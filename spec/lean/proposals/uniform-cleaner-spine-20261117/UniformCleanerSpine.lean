import ExactMUSTClosure
namespace UniformCleanerSpine
open NonEmptyPolicy NonEmptyRestriction
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h

inductive Reach where | all | below
  deriving DecidableEq, BEq, Repr

structure Region where
  path : Path
  exact : Bool := false
  holes : List Nat := []
  deriving DecidableEq, BEq, Repr

def member (r : Region) (word : Path) : Bool :=
  match dropHead r.path word with
  | none=>false
  | some suffix=>if r.exact then suffix.isEmpty else ExclusionChildCover.permits r.holes suffix

def covered (rs : List Region) (word : Path) : Bool:=rs.any (member · word)
def prepend (field : Nat) (r : Region) : Region:={r with path:=field::r.path}

/-- Relative to the incoming MUST head. A normal field hole is retained
    at the parent; only the one configured cleaner path is expanded. -/
def regions (reach : Reach) (remaining holes : Path) : List Region :=
  match remaining with
  | []=>match reach with | .all=>[] | .below=>[⟨[],true,[]⟩]
  | field::rest=>if holes.contains field then [⟨[],false,holes⟩] else
      ⟨[],false,field::holes⟩ :: (regions reach rest []).map (prepend field)

def touches (reach : Reach) (cleaned word : Path) : Bool :=
  match dropHead cleaned word with
  | none=>false
  | some suffix=>match reach with | .all=>true | .below=> !suffix.isEmpty

def retained (reach : Reach) (remaining holes word : Path) : Bool :=
  ExclusionChildCover.permits holes word && !touches reach remaining word

theorem a_prefixed_component_matches_exactly_the_corresponding_child
    (field : Nat) (r : Region) (suffix : Path) : member (prepend field r) (field::suffix)=member r suffix := by
  simp only [member,prepend,dropHead,ite_true]
  rfl

theorem a_prefixed_component_never_matches_another_child
    (field first : Nat) (r : Region) (suffix : Path) (different : field≠first) :
    member (prepend field r) (first::suffix)=false := by
  simp [member,prepend,dropHead,different]

theorem a_prefixed_component_never_matches_the_parent
    (field : Nat) (r : Region) : member (prepend field r) []=false := rfl

theorem prefixed_union_matches_exactly_the_child_union
    (field : Nat) (rs : List Region) (suffix : Path) :
    covered (rs.map (prepend field)) (field::suffix)=covered rs suffix := by
  simp only [covered,List.any_map,Function.comp_def,a_prefixed_component_matches_exactly_the_corresponding_child]

theorem prefixed_union_does_not_match_the_parent (field : Nat) (rs : List Region) :
    covered (rs.map (prepend field)) []=false := by
  induction rs with
  | nil=>rfl
  | cons r rs ih=>simpa only [List.map_cons,covered,List.any_cons,a_prefixed_component_never_matches_the_parent,Bool.false_or] using ih

theorem prefixed_union_does_not_match_a_different_child
    (field first : Nat) (rs : List Region) (suffix : Path) (different : field≠first) :
    covered (rs.map (prepend field)) (first::suffix)=false := by
  induction rs with
  | nil=>rfl
  | cons r rs ih=>
    simpa only [List.map_cons,covered,List.any_cons,
      a_prefixed_component_never_matches_another_child field first r suffix different,Bool.false_or] using ih

/-- A scalar form of the same spine, used to separate list bookkeeping
    from the spatial set-difference proof. -/
def formula (reach : Reach) (remaining holes word : Path) : Bool :=
  match remaining with
  | []=>match reach with | .all=>false | .below=>word.isEmpty
  | field::rest=>if holes.contains field then ExclusionChildCover.permits holes word else
      ExclusionChildCover.permits (field::holes) word ||
      match word with
      | []=>false
      | first::tail=>if first==field then formula reach rest [] tail else false

theorem prefixed_union_has_the_expected_word_cases
    (field : Nat) (rs : List Region) (word : Path) :
    covered (rs.map (prepend field)) word=
      match word with
      | []=>false
      | first::tail=>if first==field then covered rs tail else false := by
  cases word with
  | nil=>exact prefixed_union_does_not_match_the_parent field rs
  | cons first tail=>
    by_cases eq : first=field
    · subst first
      simpa only [beq_self_eq_true,ite_true] using prefixed_union_matches_exactly_the_child_union field rs tail
    · have neq : (first==field)=false:=beq_eq_false_iff_ne.mpr eq
      simpa only [neq,Bool.false_eq_true,ite_false] using
        prefixed_union_does_not_match_a_different_child field first rs tail (Ne.symm eq)

theorem represented_spine_is_its_scalar_formula
    (reach : Reach) (remaining holes word : Path) :
    covered (regions reach remaining holes) word=formula reach remaining holes word := by
  induction remaining generalizing holes word with
  | nil=>cases reach <;> cases word <;> rfl
  | cons field rest ih=>
    rw [regions,formula.eq_def]
    cases blocked : holes.contains field
    · simp only [blocked,Bool.false_eq_true,ite_false]
      change (ExclusionChildCover.permits (field::holes) word || covered ((regions reach rest []).map (prepend field)) word)=_
      rw [prefixed_union_has_the_expected_word_cases]
      cases word with
      | nil=>rfl
      | cons first tail=>dsimp only; rw [ih]
    · simp only [blocked,ite_true]
      change (ExclusionChildCover.permits holes word || false)=_
      exact Bool.or_false _

theorem no_holes_admit_every_suffix (word : Path) : ExclusionChildCover.permits [] word=true := by
  cases word <;> rfl

/-- Every actual marked point survives iff it is outside the cleaned
    subtree (or is the retained root of a BELOW cleaner). No widening. -/
theorem the_path_spine_is_exactly_the_uniform_residual
    (reach : Reach) (remaining holes word : Path) :
    covered (regions reach remaining holes) word=retained reach remaining holes word := by
  rw [represented_spine_is_its_scalar_formula]
  induction remaining generalizing holes word with
  | nil=>cases reach <;> cases word <;> simp [formula,retained,touches,dropHead,ExclusionChildCover.permits]
  | cons field rest ih=>
    rw [formula.eq_def]
    cases blocked : holes.contains field
    · simp only [blocked,Bool.false_eq_true,ite_false]
      cases word with
      | nil=>rfl
      | cons first tail=>
        by_cases eq : first=field
        · subst first
          simp only [List.contains_cons,beq_self_eq_true,Bool.true_or,ExclusionChildCover.permits,
            Bool.not_true,Bool.false_or,ite_true]
          rw [ih]
          simp only [retained,ExclusionChildCover.permits,blocked,Bool.not_false,Bool.true_and,
            no_holes_admit_every_suffix,touches,dropHead,ite_true]
          cases tail <;> rfl
        · have different : (first==field)=false:=beq_eq_false_iff_ne.mpr eq
          have ne : field≠first:=Ne.symm eq
          simp only [List.contains_cons,different,Bool.false_or,Bool.false_eq_true,ite_false,
            Bool.or_false,ExclusionChildCover.permits]
          simp only [retained,ExclusionChildCover.permits,touches,dropHead,ite_eq_right ne,Bool.not_false,Bool.and_true]
    · simp only [blocked,ite_true]
      cases word with
      | nil=>rfl
      | cons first tail=>
        by_cases eq : first=field
        · subst first
          simp only [retained,ExclusionChildCover.permits,blocked,Bool.not_true,Bool.false_and]
        · have ne : field≠first:=Ne.symm eq
          simp only [retained,touches,dropHead,ite_eq_right ne,Bool.not_false,Bool.and_true]

theorem the_spine_has_linear_size (reach : Reach) (remaining holes : Path) :
    (regions reach remaining holes).length≤remaining.length+1 := by
  induction remaining generalizing holes with
  | nil=>
    cases reach with
    | all=>exact Nat.zero_le 1
    | below=>exact Nat.le_refl 1
  | cons field rest ih=>
    rw [regions]
    split
    · change 1≤rest.length+1+1
      exact Nat.le_add_left 1 (rest.length+1)
    · simpa only [List.length_cons,List.length_map] using Nat.succ_le_succ (ih [])


/-- Every new head is a prefix of the one configured cleaner path.
    Repeated cleaning cannot create cross-products of unrelated paths. -/
theorem every_component_head_is_on_the_configured_path
    (reach : Reach) (remaining holes : Path) (r : Region)
    (present : r∈regions reach remaining holes) :
    ∃ suffix, remaining=r.path++suffix := by
  induction remaining generalizing holes r with
  | nil=>
    cases reach with
    | all=>cases present
    | below=>
      have same : r=⟨[],true,[]⟩:=List.mem_singleton.mp present
      subst r; exact ⟨[],rfl⟩
  | cons field rest ih=>
    rw [regions] at present
    split at present
    · have same : r=⟨[],false,holes⟩:=List.mem_singleton.mp present
      subst r; exact ⟨field::rest,rfl⟩
    · rcases List.mem_cons.mp present with same | child
      · subst r; exact ⟨field::rest,rfl⟩
      · obtain ⟨part,existsPart,equal⟩:=List.mem_map.mp child
        obtain ⟨suffix,shape⟩:=ih [] part existsPart
        subst r
        exact ⟨suffix,by simpa only [prepend,List.cons_append] using congrArg (List.cons field) shape⟩

theorem component_depth_never_exceeds_the_configured_cleaner_depth
    (reach : Reach) (remaining holes : Path) (r : Region)
    (present : r∈regions reach remaining holes) : r.path.length≤remaining.length := by
  obtain ⟨suffix,shape⟩:=every_component_head_is_on_the_configured_path reach remaining holes r present
  rw [shape,List.length_append]
  exact Nat.le_add_right _ _

theorem a_whole_subtree_cannot_keep_the_selected_root (remaining holes : Path) :
    covered (regions .all remaining holes) remaining=false := by
  rw [the_path_spine_is_exactly_the_uniform_residual]
  have own : dropHead remaining remaining=some [] := by
    simpa only [List.append_nil] using PointWriteProperties.strip_own_prefix remaining []
  simp only [retained,touches,own,Bool.not_true,Bool.and_false]

-- A local Normal MUST source and the new normal residual at x are enough
-- for the observed broad condition. The protocol proof below supplies IDs.
theorem the_nested_two_field_example_has_two_precise_regions :
    regions .all [1,2] []=[⟨[],false,[1]⟩,⟨[1],false,[2]⟩] ∧
    covered (regions .all [1,2] []) []=true ∧
    covered (regions .all [1,2] []) [1,2]=false ∧
    covered (regions .all [1,2] []) [1,1]=true := by decide

theorem a_BELOW_cleaner_also_keeps_the_normal_exact_cleaner_root :
    regions .below [1,2] []=[⟨[],false,[1]⟩,⟨[1],false,[2]⟩,⟨[1,2],true,[]⟩] ∧
    covered (regions .below [1,2] []) [1,2]=true ∧
    covered (regions .below [1,2] []) [1,2,1]=false := by decide
end UniformCleanerSpine

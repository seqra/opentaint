import AuditCleanerGetter
namespace DisjointCleaner
open NonEmptyPolicy NonEmptyRestriction
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl

inductive Reach where | exact | below | all
  deriving DecidableEq, BEq, Repr
deriving instance ReflBEq, LawfulBEq for Reach

def safeCone (head cleaned : Path) (reach : Reach) : Bool :=
  if reach == .exact then (dropHead head cleaned).isNone
  else (dropHead head cleaned).isNone && (dropHead cleaned head).isNone

def touches (cleaned : Path) (reach : Reach) (word : Path) : Bool :=
  match dropHead cleaned word with
  | none => false
  | some rest => match reach with
    | .exact => rest.isEmpty
    | .below => !rest.isEmpty
    | .all => true

theorem prefix_is_executable (head rest : Path) :
    dropHead head (head++rest)=some rest :=
  AuditIntersection.strip_common_path head rest

theorem one_common_word_forces_comparable_heads (left right a b : Path)
    (same : left++a=right++b) :
    (dropHead left right).isSome=true ∨ (dropHead right left).isSome=true := by
  rcases List.append_eq_append_iff.mp same with ⟨extra,h,_⟩ | ⟨extra,h,_⟩
  · left; rw [h];simp [prefix_is_executable]
  · right; rw [h];simp [prefix_is_executable]

theorem safe_cone_has_no_cleaned_point (head cleaned : Path) (reach : Reach)
    (safe : safeCone head cleaned reach=true) (suffix : Path) :
    touches cleaned reach (head++suffix)=false := by
  cases reach with
  | exact =>
    simp [safeCone] at safe
    cases hit : dropHead cleaned (head++suffix) with
    | none => simp [touches,hit]
    | some rest =>
      have word := DefiniteMustReplay.dropped_prefix_constructs_suffix _ _ _ hit
      cases rest with
      | nil =>
        have wrong : dropHead head cleaned=some suffix := by
          rw [show cleaned=head++suffix from by simpa using word.symm]
          exact prefix_is_executable head suffix
        simp [wrong] at safe
      | cons f more => simp [touches,hit]
  | below | all =>
    simp [safeCone] at safe
    cases hit : dropHead cleaned (head++suffix) with
    | none => simp [touches,hit]
    | some rest =>
      have word := DefiniteMustReplay.dropped_prefix_constructs_suffix _ _ _ hit
      rcases one_common_word_forces_comparable_heads head cleaned suffix rest word with wrong | wrong
      · have no := safe.1
        cases h : dropHead head cleaned <;> simp_all
      · have no := safe.2
        cases h : dropHead cleaned head <;> simp_all

-- The theorem quantifies over the whole cone, not the raw tail. In
-- particular it includes every suffix added by EXACT-to-STAR normalization.
def concreteClean (cleaned : Path) (reach : Reach) (selected mark : Nat)
    (word : Path) (present : Bool) : Bool :=
  present && !(mark==selected && touches cleaned reach word)

theorem guarded_FLOW_identity_is_valid_for_every_full_mark_and_suffix
    (head cleaned : Path) (reach : Reach) (selected mark : Nat)
    (safe : safeCone head cleaned reach=true) (suffix : Path) (present : Bool) :
    concreteClean cleaned reach selected mark (head++suffix) present=present := by
  simp [concreteClean,safe_cone_has_no_cleaned_point head cleaned reach safe suffix]

theorem the_guard_covers_normalized_EXACT_as_well_as_STAR
    (head cleaned : Path) (reach : Reach)
    (safe : safeCone head cleaned reach=true) (suffix : Path) :
    touches cleaned reach (head++suffix)=false :=
  safe_cone_has_no_cleaned_point head cleaned reach safe suffix

theorem exact_probe_at_an_ancestor_is_not_a_safe_cone (head : Path) (f : Nat) (rest : Path) :
    safeCone head (head++(f::rest)) .exact=false := by
  simp [safeCone,prefix_is_executable]

theorem same_head_selected_cleaner_stays_on_the_old_path (head : Path) (reach : Reach) :
    safeCone head head reach=false := by
  cases reach <;> simp [safeCone,show dropHead head head=some [] from by simpa using prefix_is_executable head []]

def corrected (old : Value → Value) (cleaned : Path) (reach : Reach) (v : Value) : Value :=
  if v.ap.mark.isNone && safeCone v.ap.path cleaned reach then v else old v

theorem only_a_FLOW_value_in_a_disjoint_cone_can_change
    (old : Value → Value) (cleaned : Path) (reach : Reach) (v : Value)
    (different : corrected old cleaned reach v≠old v) :
    v.ap.mark=none ∧ safeCone v.ap.path cleaned reach=true := by
  unfold corrected at different
  split at different
  · rename_i yes
    simpa only [Bool.and_eq_true,Option.isNone_iff_eq_none] using yes
  · exact False.elim (different rfl)

theorem safe_branch_keeps_every_header_and_field_limit_coordinate
    (old : Value → Value) (cleaned : Path) (reach : Reach) (v : Value)
    (flow : v.ap.mark=none) (safe : safeCone v.ap.path cleaned reach=true) :
    corrected old cleaned reach v=v := by simp [corrected,flow,safe]

theorem concrete_cleaner_rows_are_unchanged
    (old : Value → Value) (cleaned : Path) (reach : Reach) (v : Value)
    (mark : v.ap.mark≠none) : corrected old cleaned reach v=old v := by
  simp [corrected,Option.isNone_iff_eq_none,mark]

theorem full_cone_disjointness_has_no_new_path_product
    (old : Value → Value) (cleaned : Path) (reach : Reach) (v : Value) :
    corrected old cleaned reach v=v ∨ corrected old cleaned reach v=old v := by
  unfold corrected;split
  · exact Or.inl rfl
  · exact Or.inr rfl

-- Partition complete packed input paths, never route the whole packet
-- through a guard established by only one leaf.
def safePaths (cleaned : Path) (reach : Reach) (paths : List Path) :=
  paths.filter (fun head => safeCone head cleaned reach)
def otherPaths (cleaned : Path) (reach : Reach) (paths : List Path) :=
  paths.filter (fun head => !safeCone head cleaned reach)

theorem each_existing_path_is_routed_once (cleaned : Path) (reach : Reach)
    (paths : List Path) (head : Path) :
    head∈paths ↔ head∈safePaths cleaned reach paths ∨ head∈otherPaths cleaned reach paths := by
  by_cases yes : safeCone head cleaned reach=true
  · simp [safePaths,otherPaths,yes]
  · have no : safeCone head cleaned reach=false := by cases h : safeCone head cleaned reach <;> simp_all
    simp [safePaths,otherPaths,no]

theorem no_safe_path_is_also_masked (cleaned : Path) (reach : Reach)
    (paths : List Path) (head : Path) :
    ¬(head∈safePaths cleaned reach paths ∧ head∈otherPaths cleaned reach paths) := by
  simp [safePaths,otherPaths]
  intro _ yes _
  exact yes

theorem partition_does_not_enumerate_or_duplicate_paths (cleaned : Path) (reach : Reach)
    (paths : List Path) :
    (safePaths cleaned reach paths).length+(otherPaths cleaned reach paths).length=paths.length := by
  induction paths with
  | nil => rfl
  | cons head rest ih =>
    cases yes : safeCone head cleaned reach <;>
      simp [safePaths,otherPaths,yes] at * <;> omega

end DisjointCleaner

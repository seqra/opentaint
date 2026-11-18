import Alternating

/- Coverage is between already applied concrete FULL DATA at one actual
   continuation. It is not a weaker-summary-premise matching rule. -/
namespace UniformActual
open NonEmptyPolicy NonEmptyRestriction ExactSupport
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl

def sameContext (a b : Key) : Bool :=
  decide (a.frame = b.frame ∧ a.original = b.original ∧
    a.continuation = b.continuation ∧ a.h = b.h)

def regionCovers (uniform candidate : Ap) : Bool :=
  match dropHead uniform.path candidate.path with
  | none => false
  | some [] => if candidate.tail == .exact then true
      else if candidate.tail == .must then uniform.e.all candidate.e.contains
      else uniform.e.isEmpty
  | some (f :: _) => !uniform.e.contains f

def covers (n x : Item) : Bool :=
  !n.demand && x.demand && sameContext n.key x.key &&
  n.key.ap.base == x.key.ap.base && n.key.ap.mark == x.key.ap.mark &&
  n.key.ap.mark.isSome && n.key.ap.mx.isEmpty && x.key.ap.mx.isEmpty &&
  n.key.ap.tail == .must &&
  (x.key.ap.tail == .exact || x.key.ap.tail == .must || x.key.ap.tail == .may || x.key.ap.tail == .ne) &&
  (x.key.ap.tail == .must || x.key.ap.e.isEmpty) && regionCovers n.key.ap x.key.ap

/-- ready contains NORMAL DATA already owned by this same continuation or
    in this complete packet. It is not an archive or a future result. -/
def filter (backward : Bool) (ready packet : List Item) : List Item :=
  if backward then packet else packet.filter (fun x => !((ready ++ packet).any (fun n => covers n x)))

def foldValues (backward : Bool) (ready packet : List Value) : List Value :=
  (filter backward (ready.map ExactSupportCycle.wrap)
    ((DefiniteReplySupport.foldValues packet).map ExactSupportCycle.wrap)).map ExactSupportCycle.unwrap

theorem backward_is_unchanged (ready packet : List Item) : filter true ready packet = packet := rfl

theorem member (ready packet : List Item) (x : Item) :
    x ∈ filter false ready packet ↔ x ∈ packet ∧
      ∀ n ∈ ready ++ packet, covers n x = false := by
  have negated (b : Bool) : ((!b) = true) ↔ b = false := by cases b <;> decide
  simp only [filter,Bool.false_eq_true,ite_false,List.mem_filter,negated,List.any_eq_false,Bool.not_eq_true]

theorem subset (backward : Bool) (ready packet : List Item) (x : Item)
    (present : x ∈ filter backward ready packet) : x ∈ packet := by
  cases backward
  · exact ((member ready packet x).mp present).1
  · exact present

theorem normal_never_covered (n x : Item) (normal : x.demand = false) : covers n x = false := by
  simp [covers,normal]

theorem every_normal_is_retained (ready packet : List Item) (x : Item)
    (present : x ∈ packet) (normal : x.demand = false) : x ∈ filter false ready packet := by
  apply (member ready packet x).mpr
  exact ⟨present,fun _ _ => normal_never_covered _ x normal⟩

theorem coverage_has_normal_provider (n x : Item) (yes : covers n x = true) :
    n.demand = false ∧ x.demand = true := by
  cases hn : n.demand <;> cases hx : x.demand <;> simp_all [covers]

theorem deletion_has_a_retained_normal_witness (ready packet : List Item) (x : Item)
    (present : x ∈ packet) (gone : x ∉ filter false ready packet) :
    ∃ n ∈ ready ++ packet, covers n x = true ∧
      n.demand = false ∧ (n ∈ ready ∨ n ∈ filter false ready packet) := by
  have anyHit : ((ready ++ packet).any (fun n => covers n x)) = true := by
    cases hit : ((ready ++ packet).any (fun n => covers n x))
    · have keep : x ∈ filter false ready packet := List.mem_filter.mpr ⟨present,by simp [hit]⟩
      exact False.elim (gone keep)
    · rfl
  rcases List.any_eq_true.mp anyHit with ⟨n,presentN,covered⟩
  have normal := (coverage_has_normal_provider n x covered).1
  refine ⟨n,presentN,covered,normal,?_⟩
  rcases List.mem_append.mp presentN with old | fresh
  · exact Or.inl old
  · exact Or.inr (every_normal_is_retained ready packet n fresh normal)

theorem literal_context_is_preserved (n x : Item) (yes : covers n x = true) :
    n.key.frame = x.key.frame ∧ n.key.original = x.key.original ∧
    n.key.continuation = x.key.continuation ∧ n.key.h = x.key.h := by
  unfold covers at yes
  simp only [Bool.and_eq_true] at yes
  exact of_decide_eq_true yes.1.1.1.1.1.1.1.1.1.2

/-- Point semantics: a MAY leaf may select a location; MUST establishes
    the mark at every represented location. A replacement covers the WHOLE
    candidate region, not only a nonempty geometric overlap. -/
def locationIn (ap : Ap) (location : Path) : Prop :=
  ∃ rest, location = ap.path ++ rest ∧ admits ap.tail ap.e rest = true

theorem whole_region_geometry (n x : Ap) (must : n.tail = .must)
    (covered : regionCovers n x = true)
    (location : Path) (selected : locationIn x location) : locationIn n location := by
  rcases selected with ⟨rest,loc,allowed⟩
  unfold regionCovers at covered
  cases head : dropHead n.path x.path with
  | none => simp [head] at covered
  | some lead =>
      have headEq := DefiniteMustReplay.dropped_prefix_constructs_suffix n.path x.path lead head
      rw [headEq,List.append_assoc] at loc
      refine ⟨lead ++ rest,loc,?_⟩
      cases lead with
      | nil =>
          cases xt : x.tail
          <;> simp only [head,xt,beq_self_eq_true,ite_true] at covered
          case exact =>
            cases rest
            · simp [admits,must]
            · simp [admits,xt] at allowed
          case must =>
            have subs : n.e.all x.e.contains = true := covered
            cases rest with
            | nil => simp [admits,must]
            | cons f more =>
                have notX : x.e.contains f = false := by simpa [admits,xt] using allowed
                have notN : n.e.contains f = false := by
                  cases h : n.e.contains f
                  · rfl
                  · have sub := List.all_eq_true.mp subs f (List.mem_of_elem_eq_true h)
                    rw [notX] at sub
                    contradiction
                simpa [admits,must] using notN
          all_goals
            have ne : n.e = [] := by simpa using covered
            cases rest <;> simp [admits,must,ne]
      | cons f more =>
          have notExcluded : n.e.contains f = false := by simpa [head] using covered
          simpa [admits,must] using notExcluded

theorem deletion_covers_every_refinement_point (n x : Item) (yes : covers n x = true)
    (location : Path) (selected : locationIn x.key.ap location) : locationIn n.key.ap location := by
  unfold covers at yes
  simp only [Bool.and_eq_true] at yes
  have ht : n.key.ap.tail = .must := by
    simpa only [beq_iff_eq] using yes.1.1.1.2
  exact whole_region_geometry n.key.ap x.key.ap ht yes.2 location selected

theorem no_new_members_or_queries (ready packet : List Item) :
    (filter false ready packet).length ≤ packet.length := List.length_filter_le _ _

theorem membership_order_independent (ready a b : List Item)
    (same : ∀ x, x ∈ a ↔ x ∈ b) (x : Item) :
    x ∈ filter false ready a ↔ x ∈ filter false ready b := by
  simp only [member,List.mem_append,same]

theorem whole_covered_packet_is_idempotent (ready packet : List Item) (x : Item) :
    x ∈ filter false ready (filter false ready packet) ↔ x ∈ filter false ready packet := by
  constructor
  · exact subset false _ _ _
  · intro hx
    apply (member _ _ _).mpr
    refine ⟨hx,fun n hn => ?_⟩
    apply ((member ready packet x).mp hx).2 n
    rcases List.mem_append.mp hn with old | fresh
    · exact List.mem_append_left _ old
    · exact List.mem_append_right _ (subset false _ _ _ fresh)

def item (tail : Tail) (d : Bool) (path : Path := []) (e : List Nat := []) (h : Bool := false) : Item :=
  ⟨⟨0,[0],0,⟨1,path,tail,some 2,e,[]⟩,h⟩,d⟩

theorem same_root_normal_uniform_covers_may_and_ne :
    filter false [] [item .may true,item .ne true,item .must false] = [item .must false] := by decide

theorem both_arrival_orders_keep_normal :
    filter false [] [item .may true,item .must false] = [item .must false] ∧
    filter false [] [item .must false,item .may true] = [item .must false] := by decide

theorem earlier_normal_at_the_continuation_handles_a_later_packet :
    filter false [item .must false] [item .may true] = [] := by decide

theorem a_child_uniform_does_not_cover_the_parent_question :
    filter false [] [item .may true,item .must false [1]] = [item .may true,item .must false [1]] := by decide

theorem a_uniform_field_hole_blocks_whole_may_coverage :
    filter false [] [item .may true,item .must false [] [1]] =
      [item .may true,item .must false [] [1]] := by decide

theorem an_admitted_sibling_subtree_remains_covered :
    filter false [] [item .may true [2],item .must false [] [1]] =
      [item .must false [] [1]] := by decide

theorem protected_and_plain_do_not_mix :
    filter false [] [item .may true [] [] true,item .must false] =
      [item .may true [] [] true,item .must false] := by decide

theorem actual_demand_uniform_is_not_a_normal_provider :
    filter false [] [item .may true,item .must true] = [item .may true,item .must true] := by decide

theorem backward_packet_is_not_coarsened :
    filter true [] [item .may true,item .must false] = [item .may true,item .must false] := rfl

end UniformActual

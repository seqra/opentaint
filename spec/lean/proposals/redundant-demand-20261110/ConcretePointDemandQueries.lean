import EquivalentOutputSelectors

namespace ConcretePointDemandQueries

inductive Tail where
  | exact | star | may | must
  deriving DecidableEq, Repr

inductive Geometry where
  | same | strictDescendant | strictAncestor | disjoint
  deriving DecidableEq, Repr

-- The native base, literal full mark, both budgets, and legal exact initial
-- checks are common to these two entry patterns. The strict-ancestor test
-- reads the actual's exclusion on the first unmatched field.
structure Admission where
  common : Bool
  geometry : Geometry
  actualTail : Tail
  actualAdmits : Bool
  demandedStarAdmits : Bool
  deriving DecidableEq, Repr

def primary (run : Nat) (entry : Tail) (a : Admission) : Option Tail :=
  if !a.common then none else
  match entry, a.geometry with
  | .exact, .same | .star, .same => some .exact
  | .exact, .strictAncestor | .star, .strictAncestor =>
      if a.actualAdmits && (a.actualTail == .may || a.actualTail == .must)
      then some .exact else none
  | .star, .strictDescendant =>
      if run == 2 && a.demandedStarAdmits then some .star else none
  | _, _ => none

theorem primary_equal (run : Nat) (late : 3 ≤ run) (a : Admission) :
    primary run .star a = primary run .exact a := by
  have ne : run ≠ 2 := by omega
  cases a with
  | mk common geometry actualTail actualAdmits demandedStarAdmits =>
    cases geometry <;> simp [primary, ne]

theorem primary_exact (run : Nat) (a : Admission) (t : Tail)
    (h : primary run .exact a = some t) : t = .exact := by
  cases a with
  | mk common geometry actualTail actualAdmits demandedStarAdmits =>
    cases common <;> cases geometry <;> simp [primary] at h
    · exact h.symm
    · exact h.2.symm

def initialFamily (run : Nat) (entry : Tail) (a : Admission)
    (point star companion : Nat) : List Nat :=
  match primary run entry a with
  | some .exact => [point]
  | some .star => [star, companion]
  | _ => []

theorem initial_family_equal (run : Nat) (late : 3 ≤ run) (a : Admission)
    (point star companion : Nat) :
    initialFamily run .star a point star companion =
      initialFamily run .exact a point star companion := by
  simp only [initialFamily, primary_equal run late a]

-- Structural canStoreInitial after the native legality checks. The
-- normalization fallback is FLOW-only. No late concrete STAR exists here,
-- so it cannot supply a FLOW companion.
structure Stored where
  common : Bool
  samePath : Bool
  concreteSameMark : Bool
  tail : Tail
  emptyE : Bool
  deriving DecidableEq, Repr

def accepts (run : Nat) (entry : Tail) (s : Stored) : Bool :=
  s.common && s.samePath && s.concreteSameMark &&
    ((s.tail == .exact && s.emptyE) || (entry == .star && run == 2 && s.tail == .star))

theorem stored_image_equal (run : Nat) (late : 3 ≤ run) (s : Stored) :
    accepts run .star s = accepts run .exact s := by
  have ne : run ≠ 2 := by omega
  have noTwo : (run == 2) = false := by simpa using ne
  simp [accepts, noTwo]

theorem whole_original_equal (run : Nat) (late : 3 ≤ run) (members : List Stored) :
    members.any (accepts run .star) = members.any (accepts run .exact) := by
  induction members with
  | nil => rfl
  | cons head tail ih => simp only [List.any_cons, stored_image_equal run late head, ih]

def sameScopeOutput (run : Nat) (tail : Tail) (members : List Stored)
    (sameOwnerAndPort : Bool) (selectedAndCut : List Nat) : List Nat :=
  if sameOwnerAndPort && members.any (accepts run tail) then selectedAndCut else []

theorem paired_result_equal (run : Nat) (late : 3 ≤ run) (members : List Stored)
    (scope : Bool) (selectedAndCut : List Nat) :
    sameScopeOutput run .star members scope selectedAndCut =
      sameScopeOutput run .exact members scope selectedAndCut := by
  simp only [sameScopeOutput, whole_original_equal run late members]

def suppliesCursor (tail : Tail) : Bool := tail == .may

theorem no_cursor_change : suppliesCursor .star = suppliesCursor .exact := rfl

inductive ControlEntry where
  | zero | target
  deriving DecidableEq, Repr

-- The typed control entry and its physical scope are unchanged. Its DATA
-- output follows offerDataPair with ap.zero after entryAccepts succeeds.
def controlOutput {M Result : Type} (cut : Nat → EquivalentOutputSelectors.Conclusion M → List Result)
    (runLimit : Nat) (counted : Nat → Bool) (accepted : Bool)
    (raw : EquivalentOutputSelectors.Conclusion M)
    (selector : EquivalentOutputSelectors.Pattern) : List Result :=
  if accepted then
    (EquivalentOutputSelectors.restrictExit raw selector).toList.flatMap
      (cut (EquivalentOutputSelectors.budget runLimit counted selector))
  else []

theorem control_output_equal {M Result : Type}
    (cut : Nat → EquivalentOutputSelectors.Conclusion M → List Result)
    (limit : Nat) (counted : Nat → Bool) (accepted : Bool)
    (raw : EquivalentOutputSelectors.Conclusion M)
    (base : Nat) (path : List Nat) (mark : EquivalentOutputSelectors.Mark) :
    controlOutput cut limit counted accepted raw
      (EquivalentOutputSelectors.selector base path mark .star) =
    controlOutput cut limit counted accepted raw
      (EquivalentOutputSelectors.selector base path mark .may) := by
  have exits := EquivalentOutputSelectors.empty_star_and_may_exit_equal raw base path mark
  simp only [controlOutput, exits]
  rfl

-- One supplied witness per removed row, from the final retained set.
theorem retained_union {R Answer : Type} (retained removed : List R)
    (query : R → List Answer)
    (witness : ∀ r ∈ removed, { s : R // s ∈ retained ∧ query r = query s })
    (result : Answer) :
    result ∈ (retained ++ removed).flatMap query ↔ result ∈ retained.flatMap query := by
  simp only [List.flatMap_append, List.mem_append]
  constructor
  · intro found
    cases found with
    | inl yes => exact yes
    | inr lost =>
      obtain ⟨r, hr, hq⟩ := List.mem_flatMap.mp lost
      let s := witness r hr
      exact List.mem_flatMap.mpr ⟨s.val, s.property.1, s.property.2 ▸ hq⟩
  · exact Or.inl

theorem next_state_equal {State Query Answer : Type}
    (advance : (Query → Answer → Prop) → State → State)
    (left right : Query → Answer → Prop) (same : ∀ q a, left q a ↔ right q a)
    (state : State) : advance left state = advance right state := by
  have eq : left = right := funext (fun q => funext (fun a => propext (same q a)))
  rw [eq]

example : primary 2 .star ⟨true, .strictDescendant, .exact, true, true⟩ = some .star := rfl
example : primary 2 .exact ⟨true, .strictDescendant, .exact, true, true⟩ = none := rfl

#print axioms primary_equal
#print axioms primary_exact
#print axioms initial_family_equal
#print axioms stored_image_equal
#print axioms whole_original_equal
#print axioms paired_result_equal
#print axioms no_cursor_change
#print axioms control_output_equal
#print axioms retained_union
#print axioms next_state_equal

end ConcretePointDemandQueries

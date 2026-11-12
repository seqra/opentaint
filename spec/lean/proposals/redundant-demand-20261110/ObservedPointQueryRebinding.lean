import ConcretePointDemandQueries

/-! A fresh finite binding of the accepted Point law. The complete native key
codebook is q-concrete-point-query-rebinding-v3/codebook.json. No new transfer,
protection, field or control semantics is introduced here. -/
namespace ObservedPointQueryRebinding
open ConcretePointDemandQueries

structure Row where
  owner : Nat
  entryPort : Nat
  exitPort : Nat
  entryBase : Nat
  entryPath : List Nat
  fullMark : Nat
  entryTail : Tail
  entryE : List Nat
  output : EquivalentOutputSelectors.Pattern
  deriving DecidableEq, Repr

-- owner0 is the complete Map/HashMap method context and loop Block2.
-- base0=local9, base1=local3. field0=Map$Entry.Value, field1=Iterator.Element.
-- mark0 is the full Spring path source key, not the ZERO control mark.
def output : EquivalentOutputSelectors.Pattern :=
  ⟨1, [1, 0], .star, .concrete 0, []⟩
def oldSource : Row := ⟨0, 40, 40, 0, [0], 0, .exact, [], output⟩
def newSource : Row := ⟨0, 40, 40, 0, [0], 0, .exact, [], output⟩
def anchor : Row := ⟨0, 40, 40, 0, [0], 0, .star, [], output⟩
def key (row : Row) : Row := { row with entryTail := .exact, entryE := [] }

theorem old_native_coordinate_key : key oldSource = key anchor := by decide
theorem new_native_coordinate_key : key newSource = key anchor := by decide
theorem outputs_are_literal : oldSource.output = anchor.output ∧ newSource.output = anchor.output := by decide
theorem old_and_new_projected_rows_equal : oldSource = newSource := by decide

def c2 (row : Row) (run : Nat) (a : Admission) (point star companion : Nat) : List Nat :=
  initialFamily run row.entryTail a point star companion

theorem old_c2_all_later_runs (run : Nat) (late : 3 ≤ run) (a : Admission)
    (point star companion : Nat) :
    c2 oldSource run a point star companion = c2 anchor run a point star companion := by
  exact (initial_family_equal run late a point star companion).symm

theorem new_c2_all_later_runs (run : Nat) (late : 3 ≤ run) (a : Admission)
    (point star companion : Nat) :
    c2 newSource run a point star companion = c2 anchor run a point star companion := by
  exact (initial_family_equal run late a point star companion).symm

-- The full selector, relative budget, current layer and current protection stay
-- inside the same selectedAndCut function. Raw-origin flags are not query fields.
def c5 (row : Row) (run : Nat) (members : List Stored)
    (sameOwnerAndPorts : Bool) (selectedAndCut : List Nat) : List Nat :=
  sameScopeOutput run row.entryTail members sameOwnerAndPorts selectedAndCut

theorem old_c5_all_later_runs (run : Nat) (late : 3 ≤ run) (members : List Stored)
    (sameOwnerAndPorts : Bool) (selectedAndCut : List Nat) :
    c5 oldSource run members sameOwnerAndPorts selectedAndCut =
      c5 anchor run members sameOwnerAndPorts selectedAndCut := by
  exact (paired_result_equal run late members sameOwnerAndPorts selectedAndCut).symm

theorem new_c5_all_later_runs (run : Nat) (late : 3 ≤ run) (members : List Stored)
    (sameOwnerAndPorts : Bool) (selectedAndCut : List Nat) :
    c5 newSource run members sameOwnerAndPorts selectedAndCut =
      c5 anchor run members sameOwnerAndPorts selectedAndCut := by
  exact (paired_result_equal run late members sameOwnerAndPorts selectedAndCut).symm

-- Origin ranks: old0 is already retired, new1 is proposed, anchor2 is outside U.
-- Both complete native origin projections have the same explicit retained witness.
def retiredBefore : List Nat := [0]
def retiredAfter : List Nat := [0, 1]
def witnessBindings : List (Nat × Nat) := [(0, 2), (1, 2)]
def completeBindings : Bool := witnessBindings.all fun pair =>
  retiredAfter.contains pair.1 && !(retiredAfter.contains pair.2) && pair.2 == 2

theorem both_origins_have_retained_certificates : completeBindings = true := by decide

def dependenciesKept (retired dependencies : List Nat) : Bool :=
  dependencies.all fun origin => !(retired.contains origin)

theorem prior_dependency_valid_before : dependenciesKept retiredBefore [1] = true := by decide
theorem unsafe_unrebound_retirement_rejected : dependenciesKept retiredAfter [1] = false := by decide
theorem explicit_rebinding_valid_after : dependenciesKept retiredAfter [2] = true := by decide

def originsAt : Nat → List Nat | 0 => [0, 1] | 1 => [2] | _ => []
def live (retired : List Nat) (row : Nat) : Bool :=
  (originsAt row).any fun origin => !(retired.contains origin)
def queryClasses (retired : List Nat) : List Nat :=
  ([0, 1] : List Nat).filterMap fun row => if live retired row then some 0 else none

theorem canonical_query_membership_equal (query : Nat) :
    query ∈ queryClasses retiredBefore ↔ query ∈ queryClasses retiredAfter := by
  simp [queryClasses, live, originsAt, retiredBefore, retiredAfter]

theorem permanent_anchor_is_not_retired : retiredAfter.contains 2 = false := by decide

#print axioms old_native_coordinate_key
#print axioms new_native_coordinate_key
#print axioms outputs_are_literal
#print axioms old_and_new_projected_rows_equal
#print axioms old_c2_all_later_runs
#print axioms new_c2_all_later_runs
#print axioms old_c5_all_later_runs
#print axioms new_c5_all_later_runs
#print axioms both_origins_have_retained_certificates
#print axioms prior_dependency_valid_before
#print axioms unsafe_unrebound_retirement_rejected
#print axioms explicit_rebinding_valid_after
#print axioms canonical_query_membership_equal
#print axioms permanent_anchor_is_not_retired

end ObservedPointQueryRebinding

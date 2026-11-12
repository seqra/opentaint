import ConcretePointDemandQueries

namespace ObservedPointQueryFixedpoint
open ConcretePointDemandQueries

/- The accompanying encoding binds all local ranks to complete native keys.
   owner0 = List replace / LOOP block2 / reversed entry port34.
   base0 = local var(2), base1 = argument(0).
   field0 = java.util.Iterator#Element:java.lang.Object.
   mark0 = the archived full Spring path source key, not control ZERO.
   Both output ports are6. No native source/witness protection flag is erased:
   those flags remain on the raw edges and are not demand-query coordinates. -/
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

def output : EquivalentOutputSelectors.Pattern :=
  ⟨0, [0], .star, .concrete 0, []⟩
def source0 : Row := ⟨0, 34, 6, 0, [], 0, .star, [], output⟩
def witness0 : Row := ⟨0, 34, 6, 0, [], 0, .exact, [], output⟩
def source1 : Row := ⟨0, 34, 6, 1, [], 0, .star, [], output⟩
def witness1 : Row := ⟨0, 34, 6, 1, [], 0, .exact, [], output⟩

def key (row : Row) : Row :=
  { row with entryTail := .exact, entryE := [] }

theorem first_native_coordinate_key : key source0 = key witness0 := by decide
theorem second_native_coordinate_key : key source1 = key witness1 := by decide
theorem output_selectors_are_literal :
    source0.output = witness0.output ∧ source1.output = witness1.output := by decide

def c2 (row : Row) (run : Nat) (a : Admission)
    (point star companion : Nat) : List Nat :=
  initialFamily run row.entryTail a point star companion

theorem first_c2_for_all_later_runs (run : Nat) (late : 3 ≤ run) (a : Admission)
    (point star companion : Nat) :
    c2 source0 run a point star companion = c2 witness0 run a point star companion := by
  exact initial_family_equal run late a point star companion

theorem second_c2_for_all_later_runs (run : Nat) (late : 3 ≤ run) (a : Admission)
    (point star companion : Nat) :
    c2 source1 run a point star companion = c2 witness1 run a point star companion := by
  exact initial_family_equal run late a point star companion

-- selectedAndCut includes the unchanged full output selector, row budget,
-- current raw facts, layer and literal current protection membership.
def c5 (row : Row) (run : Nat) (members : List Stored)
    (sameOwnerAndPorts : Bool) (selectedAndCut : List Nat) : List Nat :=
  sameScopeOutput run row.entryTail members sameOwnerAndPorts selectedAndCut

theorem first_c5_for_all_later_runs (run : Nat) (late : 3 ≤ run)
    (members : List Stored) (sameOwnerAndPorts : Bool) (selectedAndCut : List Nat) :
    c5 source0 run members sameOwnerAndPorts selectedAndCut =
      c5 witness0 run members sameOwnerAndPorts selectedAndCut := by
  exact paired_result_equal run late members sameOwnerAndPorts selectedAndCut

theorem second_c5_for_all_later_runs (run : Nat) (late : 3 ≤ run)
    (members : List Stored) (sameOwnerAndPorts : Bool) (selectedAndCut : List Nat) :
    c5 source1 run members sameOwnerAndPorts selectedAndCut =
      c5 witness1 run members sameOwnerAndPorts selectedAndCut := by
  exact paired_result_equal run late members sameOwnerAndPorts selectedAndCut

def retainedOrigins : List Nat := [2, 3]
def removedOrigins : List Nat := [0, 1]
def witnesses : List (Nat × Nat) := [(0, 2), (1, 3)]
def originCheck : Bool := witnesses.all fun pair =>
  removedOrigins.contains pair.1 && retainedOrigins.contains pair.2 &&
    !removedOrigins.contains pair.2

theorem both_native_origins_have_retained_witnesses : originCheck = true := by decide

#print axioms first_native_coordinate_key
#print axioms second_native_coordinate_key
#print axioms output_selectors_are_literal
#print axioms first_c2_for_all_later_runs
#print axioms second_c2_for_all_later_runs
#print axioms first_c5_for_all_later_runs
#print axioms second_c5_for_all_later_runs
#print axioms both_native_origins_have_retained_witnesses

end ObservedPointQueryFixedpoint

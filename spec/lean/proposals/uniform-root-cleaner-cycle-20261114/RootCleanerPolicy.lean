import RootCleanerCycle

/- User decision after the historical counterexample: the selected
   EXACT-root cleaner cannot clean a same-head MUST. Preserve its layer.
   All other cleaner rows and existing survivor protection stay unchanged.
   This is a changed contract, not a proof of precision for the old one. -/
namespace UniformRootCleanerPolicy
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle
open UniformRootCleanerCycle

local instance : ReflBEq Nat where
  rfl := by intro a; exact Nat.beq_refl a
local instance : LawfulBEq Nat where
  eq_of_beq := by intro a b h; exact Nat.eq_of_beq_eq_true h

def revisedCleanRoot (c : Value) : Option Value :=
  if c.ap.base == x && c.ap.path.isEmpty && c.ap.tail == .must && c.ap.mark == some t then
    some {c with h := true}
  else cleanRoot c

inductive SinkTarget where
  | normal (id : Nat)
  | demand
  deriving DecidableEq, BEq, Repr

def sinkId : Nat := 100
def reportSink (c : Value) : Option SinkTarget :=
  (sinkForward c).map fun edge => if edge.demand then .demand else .normal sinkId

def newForward : List SinkTarget :=
  ((revisedCleanRoot sourceValue).bind reportSink).toList

def nextDemand (targets : List SinkTarget) : List ControlRow :=
  targets.filterMap fun target => match target with
    | .demand => some guidance
    | .normal _ => none

theorem normal_must_keeps_its_layer :
    revisedCleanRoot sourceValue = some {sourceValue with h := true} := by decide

theorem demand_must_is_not_upgraded :
    revisedCleanRoot cleanedSource = some cleanedSource := by decide

theorem no_new_layer_change_for_any_matched_must (c : Value)
    (base : c.ap.base = x) (path : c.ap.path = [])
    (must : c.ap.tail = .must) (mark : c.ap.mark = some t) :
    revisedCleanRoot c = some {c with h := true} := by
  simp [revisedCleanRoot,base,path,must,mark]

theorem non_must_cleaning_is_unchanged (c : Value)
    (notMust : c.ap.tail ≠ .must) : revisedCleanRoot c = cleanRoot c := by
  simp [revisedCleanRoot,show (c.ap.tail == .must) = false from beq_eq_false_iff_ne.mpr notMust]

theorem exact_root_still_cleans_and_may_still_has_a_demand_survivor :
    revisedCleanRoot (val (ap x [] .exact (some t))) = none ∧
    revisedCleanRoot sinkRequirement = some cleanedRequirement := by decide

theorem the_old_counterexample_has_a_normal_target_in_run1 :
    newForward = [.normal sinkId] := by decide

theorem no_refinement_or_backward_run_is_required :
    nextDemand newForward = [] ∧
    backwardRun (nextDemand newForward) true = ⟨[],false,false⟩ := by decide

/-- Concrete meaning of the original root-only cleaner on a completely
    marked source: only nonempty locations keep T. It is separate from
    the new deliberately coarser analyzer contract. -/
def concreteTAfterRootCleaner (suffix : Path) : Bool := !suffix.isEmpty

def exactRootReport (c : Value) : Option SinkTarget :=
  if c.ap.base == x && c.ap.path.isEmpty && c.ap.mark == some t &&
      (c.ap.tail == .exact || c.ap.tail == .may || c.ap.tail == .must) then
    some (if c.demand then .demand else .normal (sinkId+1)) else none

theorem a_real_child_remains_a_valid_whole_object_sink_witness :
    concreteTAfterRootCleaner [f] = true := by decide

theorem exact_root_can_now_report_normally_despite_the_actual_cleaning :
    concreteTAfterRootCleaner [] = false ∧
    (revisedCleanRoot sourceValue).bind exactRootReport = some (.normal (sinkId+1)) := by decide

end UniformRootCleanerPolicy

#print axioms UniformRootCleanerPolicy.normal_must_keeps_its_layer
#print axioms UniformRootCleanerPolicy.demand_must_is_not_upgraded
#print axioms UniformRootCleanerPolicy.no_new_layer_change_for_any_matched_must
#print axioms UniformRootCleanerPolicy.non_must_cleaning_is_unchanged
#print axioms UniformRootCleanerPolicy.exact_root_still_cleans_and_may_still_has_a_demand_survivor
#print axioms UniformRootCleanerPolicy.the_old_counterexample_has_a_normal_target_in_run1
#print axioms UniformRootCleanerPolicy.no_refinement_or_backward_run_is_required
#print axioms UniformRootCleanerPolicy.a_real_child_remains_a_valid_whole_object_sink_witness
#print axioms UniformRootCleanerPolicy.exact_root_can_now_report_normally_despite_the_actual_cleaning

import Std

/-!
Measurement design laws only. Counts of per-row selected leaf attempts are
not unique admitted facts or CPU costs. Identical summary-cut observations
can follow local path generation or inter-procedural generation. These
examples prevent attributing a timeout from compression counts alone.
-/
namespace RestrictionMeasurements
set_option autoImplicit false

inductive Decision where | rejected | uncut | cut deriving DecidableEq, Repr

structure Counts where
  attempts : Nat := 0
  rejected : Nat := 0
  uncut : Nat := 0
  cut : Nat := 0
  deriving DecidableEq, Repr

def count : List Decision → Counts
  | [] => ⟨0,0,0,0⟩
  | decision :: rest =>
    let tail := count rest
    match decision with
    | .rejected => {tail with attempts := tail.attempts + 1, rejected := tail.rejected + 1}
    | .uncut => {tail with attempts := tail.attempts + 1, uncut := tail.uncut + 1}
    | .cut => {tail with attempts := tail.attempts + 1, cut := tail.cut + 1}

theorem outcomes_partition_attempts (events : List Decision) :
    (count events).attempts = (count events).rejected + (count events).uncut + (count events).cut := by
  induction events with
  | nil => rfl
  | cons decision rest ih =>
    cases decision <;> simp only [count] <;> omega

inductive Origin where | localBody | currentDelivery | savedReplay | callStages deriving DecidableEq, Repr

structure Trace where
  origin : Origin
  decisions : List Decision
  bodySteps : Nat
  deliveryJoins : Nat
  finalMemberships : Nat
  deriving DecidableEq, Repr

def c5Observation (trace : Trace) : Counts × Nat := (count trace.decisions, trace.finalMemberships)

def localTrace : Trace := ⟨.localBody, List.replicate 16 .cut, 10000, 0, 1⟩
def deliveryTrace : Trace := ⟨.currentDelivery, List.replicate 16 .cut, 0, 10000, 1⟩

theorem identical_cut_counts_do_not_identify_the_cause :
    c5Observation localTrace = c5Observation deliveryTrace ∧
    localTrace.origin ≠ deliveryTrace.origin ∧
    localTrace.bodySteps ≠ deliveryTrace.bodySteps ∧
    localTrace.deliveryJoins ≠ deliveryTrace.deliveryJoins := by decide

def replayDuplicates : Trace := ⟨.savedReplay, List.replicate 64 .uncut, 0, 0, 1⟩

theorem summary_attempts_are_not_fresh_memberships :
    (count replayDuplicates.decisions).attempts = 64 ∧ replayDuplicates.finalMemberships = 1 := by decide

def graft (producerPrefix actualSuffix : List Nat) : List Nat := producerPrefix ++ actualSuffix

theorem bounded_summary_can_produce_a_deeper_caller_fact :
    ([1] : List Nat).length = 1 ∧ (graft [1] [2,3]).length = 3 := by decide

theorem two_producer_paths_and_two_actual_suffixes_have_four_candidates :
    ([([1] : List Nat), [2]].flatMap fun p => [[3], [4]].map (graft p)).length = 4 := by decide

end RestrictionMeasurements

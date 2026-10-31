import TargetLayers

/- Scope: an intrinsic MAY summary, e.g. p.*/FLOW -> ret.[any]/FLOW,
   stays MAY at every field limit. A new exact DEMAND hypothesis cannot
   create information absent from the submitted fact. This finite control
   disproves a general cross-iteration termination claim for the design. -/
namespace ExactDemand.IntrinsicMayCycle
open ExactDemand
set_option autoImplicit false

def demand : Demand := ⟨⟨0,[],.exact,.concrete 7,[]⟩,.demand⟩
def intrinsicActual : Actual := ⟨⟨0,[],.may,.concrete 7,[]⟩,.demand⟩

def seedAt (budgetGrowth : Nat) : Option Seed := emitExact (budgetGrowth + 1) demand intrinsicActual

def targetAt (fieldLimit : Nat) : Option Target :=
  (seedAt fieldLimit).map fun seed => sinkTarget 7 (start seed).layer

def outgoingAt (fieldLimit : Nat) : Bool :=
  (targetAt fieldLimit).any continues

def reportAt (fieldLimit : Nat) : Option Nat :=
  (targetAt fieldLimit).bind (report true)

theorem any_field_limit_has_the_same_provisional_exact (fieldLimit : Nat) :
    seedAt fieldLimit = some ⟨exactKey demand.pattern,.demand⟩ := rfl

theorem any_field_limit_keeps_demand_without_normal_report (fieldLimit : Nat) :
    targetAt fieldLimit = some .demand ∧ outgoingAt fieldLimit = true ∧
    reportAt fieldLimit = none := ⟨rfl,rfl,rfl⟩

/-- The source factory already has a persisted NORMAL ZERO producer.
    Its existing backward native read precedes any current demand lookup.
    There is no exact source guide in this example. -/
def savedSource : Summary := ⟨.zero,⟨1,[],.exact,.concrete 7,[]⟩,.normal⟩
def backwardSourceActual : Actual := ⟨⟨1,[],.star,.concrete 7,[]⟩,.demand⟩

/-- Fixed-prefix native matching slice. Geometry/full marks and offered layer
    are checked; accepted nonzero->ZERO completion keeps the caller original.
    This is existing native dispatch, not C2 or a fresh source action. -/
def backwardNativeSource (original : InitialKey) (actual : Actual) : Option TerminalSummary :=
  if actual.pattern.base == savedSource.conclusion.base &&
      actual.pattern.path == savedSource.conclusion.path &&
      markSub savedSource.conclusion.mark actual.pattern.mark && actual.layer == .demand then
    some ⟨original,.demand⟩
  else none

theorem saved_source_is_a_normal_native_candidate : nativeCandidate savedSource = some savedSource := rfl

theorem native_replay_does_not_need_a_new_source_guide :
    backwardNativeSource .zero backwardSourceActual = some ⟨.zero,.demand⟩ ∧
    sourcePermissions .none = [] := ⟨rfl,rfl⟩

structure CycleState where
  rootZeroPermission : Bool
  helperExactGuide : Demand
  deriving DecidableEq, Repr

def initialState : CycleState := ⟨true,demand⟩

/-- Compressed F/B round: existing explicit root ZERO permission runs the
    saved source plus intrinsic MAY pass; the helper emits DT, its reverse
    sink need crosses the pass, and the saved NORMAL source's backward
    native replay emits root DT under the already admitted ZERO original. Both root DT
    projections are the same complete (Target,ZERO) pair. The helper's
    reverse ZERO->p.$/T row restores its exact entry guide for the next F.
    No actual source callback is fabricated by native summary replay. -/
def nextState (budgetGrowth : Nat) (state : CycleState) : CycleState :=
  if state.rootZeroPermission then
    match emitExact (budgetGrowth + 1) state.helperExactGuide intrinsicActual,
        backwardNativeSource .zero backwardSourceActual with
    | some forwardSeed, some backwardTerminal =>
      if sinkTarget 7 (start forwardSeed).layer == .demand &&
          backwardTerminal.target == .demand then ⟨true,demand⟩
      else ⟨false,state.helperExactGuide⟩
    | _, _ => ⟨false,state.helperExactGuide⟩
  else state

theorem one_complete_forward_backward_round_repeats_frontier (budgetGrowth : Nat) :
    nextState budgetGrowth initialState = initialState := rfl

def stateAfter (limits : Nat → Nat) : Nat → CycleState
  | 0 => initialState
  | n + 1 => nextState (limits n) (stateAfter limits n)

theorem frontier_never_changes (limits : Nat → Nat) (n : Nat) :
    stateAfter limits n = initialState := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [stateAfter, ih]
    exact one_complete_forward_backward_round_repeats_frontier (limits n)

def finiteRoundJobs (fieldLimit : Nat) : List Nat :=
  match seedAt fieldLimit with | none => [] | some _ => [0,1,2]

theorem every_round_is_finite_three_jobs (fieldLimit : Nat) :
    (finiteRoundJobs fieldLimit).length = 3 := rfl

theorem arbitrary_growing_schedule_can_still_continue (limits : Nat → Nat) (n : Nat) :
    outgoingAt (limits n) = true ∧ reportAt (limits n) = none ∧
      (finiteRoundJobs (limits n)).length = 3 := ⟨rfl,rfl,rfl⟩

end ExactDemand.IntrinsicMayCycle

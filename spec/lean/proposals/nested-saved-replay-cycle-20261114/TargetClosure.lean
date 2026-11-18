import CallerClosure
import TargetZeroKernel

/- Reuse the selected ZERO/Target paired C5. No new Target constructor,
   seed, publication bypass or NORMAL+DEMAND promotion is introduced. -/
namespace NestedTargetClosure
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle
open NestedSavedReplayCycle NestedCallerClosure TargetZeroKernel

def witnessTarget (a : Offered) : Summary :=
  forwardSinkTarget 0 .zero (if a.demand then .demand else .normal) 0
def observations : List Summary := third.map witnessTarget
def rootDemand : Demand := handoffTarget 0 .zero

def producerHit : Option Summary :=
  backwardGenEventTarget .actualReverseTransfer ⟨.zero,.ap .a⟩
    (admits need.ap.tail need.ap.e [f,g] && need.ap.mark == some t) true 0 .zero

theorem forward_complete_reply_supplies_an_anonymous_demand_target :
    targetSummary 0 .zero ∈ observations := by decide

theorem ordinary_backward_calls_reach_an_actual_mark_assignment :
    deliver (deliver (deliver [need])) = [need] ∧
    producerHit = some (targetSummary 0 .zero) := by decide

theorem paired_c5_accepts_the_fresh_root_target_in_both_directions :
    c5Restrict exactEntry exactExit rootDemand (targetSummary 0 .zero) =
      some (targetSummary 0 .zero) ∧
    (producerHit.bind (c5Restrict exactEntry exactExit rootDemand)) =
      some (targetSummary 0 .zero) := by decide

theorem the_target_really_restarts_zero_and_keeps_continuation :
    emittedZero .restricted [rootDemand] 0 .zero = [.zero] ∧
    continuationRelevant (targetSummary 0 .zero) = true ∧
    selectedTargetHandoff (targetSummary 0 .zero) = some rootDemand := by decide

theorem a_retained_normal_observation_does_not_remove_that_demand :
    observations.any (fun s => s.layer == .normal) = true ∧
    (observations.filter continuationRelevant).isEmpty = false ∧
    selectedTargetHandoff (layeredTargetSummary 0 .zero .normal 0) = none := by decide

theorem uncapped_data_and_control_demand_remain (n : Nat) :
    repeatFromRun9 n = stableRows ∧
    ∃ summary ∈ observations,
      c5Restrict exactEntry exactExit rootDemand summary = some summary ∧
      selectedTargetHandoff summary = some rootDemand ∧ continuationRelevant summary = true := by
  refine ⟨uncapped_recurrence n,targetSummary 0 .zero,
    forward_complete_reply_supplies_an_anonymous_demand_target,?_,?_,?_⟩
  · exact paired_c5_accepts_the_fresh_root_target_in_both_directions.1
  · exact the_target_really_restarts_zero_and_keeps_continuation.2.2
  · exact the_target_really_restarts_zero_and_keeps_continuation.2.1

end NestedTargetClosure

#print axioms NestedTargetClosure.forward_complete_reply_supplies_an_anonymous_demand_target
#print axioms NestedTargetClosure.ordinary_backward_calls_reach_an_actual_mark_assignment
#print axioms NestedTargetClosure.paired_c5_accepts_the_fresh_root_target_in_both_directions
#print axioms NestedTargetClosure.the_target_really_restarts_zero_and_keeps_continuation
#print axioms NestedTargetClosure.a_retained_normal_observation_does_not_remove_that_demand
#print axioms NestedTargetClosure.uncapped_data_and_control_demand_remain

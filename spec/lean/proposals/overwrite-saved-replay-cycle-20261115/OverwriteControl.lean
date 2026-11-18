import OverwriteStable
import TargetZeroKernel

namespace OverwriteControl
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NormalUniformNE
open NestedSavedReplayCycle NestedColdMachine OverwriteReplay OverwriteWitnesses OverwriteStable
open TargetZeroKernel
set_option linter.unusedSimpArgs false
set_option maxRecDepth 16384
set_option maxHeartbeats 80000000

def readRecord : Edge := (point p [f,f] .star,val {point ret [] .star with e := [g]})
def writeRecord : Edge := (point p [] .star,val {point ret [f,f] .star with e := [g]})
def unresolved : Edge := (point p [] .star,val (point ret [] .may) true)
def reply (a : Offered) : List Offered := OverwriteReplay.values
  ([readRecord,writeRecord,unresolved].filterMap fun e => OverwriteReplay.apply true e a)
def deliver (actuals : List Offered) := OverwriteReplay.values (actuals.flatMap reply)
def first := deliver [NestedSavedReplayCycle.source 0]
def second := deliver first
def third := deliver second

theorem actual_forward_packets_are_precise_plus_may :
    first = OverwriteReplay.values [NestedSavedReplayCycle.source 1,need] ∧
    second = OverwriteReplay.values [NestedSavedReplayCycle.source 0,NestedSavedReplayCycle.source 2,need] ∧
    third = OverwriteReplay.values [NestedSavedReplayCycle.source 1,NestedSavedReplayCycle.source 3,need] := by decide

theorem the_proved_domain_is_the_complete_caller_domain :
    unique OverwriteReplay.valueKey ([NestedSavedReplayCycle.source 0] ++ first ++ second) =
      unique OverwriteReplay.valueKey OverwriteStable.domainF := by decide

theorem complete_saved_and_current_forward_offer_matches_this_reply :
    OverwriteStable.domainF.all (fun a => decide (reply a =
      OverwriteReplay.offer 9 8 OverwriteStable.stableRows OverwriteStable.stableSaved publications a)) = true := by decide

theorem complete_saved_and_current_backward_offer_matches_this_reply :
    reply need = OverwriteReplay.offer 10 9 OverwriteStable.stableRows OverwriteStable.stableSaved publications need := by decide

theorem uniform_paths_never_need_more_than_eight_fields :
    (OverwriteStable.domainF.flatMap reply).all (fun a => decide (a.ap.path.length ≤ 8)) = true := by decide

theorem arbitrary_later_limits_do_not_cut_a_caller_packet (n : Nat)
    (a : Offered) (ha : a ∈ OverwriteStable.domainF.flatMap reply) : cutOffer (n+8) a = a := by
  have bound : a.ap.path.length ≤ 8 :=
    of_decide_eq_true (List.all_eq_true.mp uniform_paths_never_need_more_than_eight_fields a ha)
  have within : ¬n+8 < a.ap.path.length := by omega
  cases a
  simp [cutOffer,cut,within,val]

theorem backward_reply_is_stable_and_reaches_the_producer :
    reply need = [need] ∧ deliver (deliver (deliver [need])) = [need] ∧
    admits need.ap.tail need.ap.e [f,g] = true ∧ need.ap.mark = some t := by decide

def witness (a : Offered) : Summary := forwardSinkTarget 0 .zero
  (if a.demand then .demand else .normal) 0
def observations := third.map witness
def rootDemand := handoffTarget 0 .zero
def producerHit : Option Summary := backwardGenEventTarget .actualReverseTransfer
  ⟨.zero,.ap .a⟩ (admits need.ap.tail need.ap.e [f,g] && need.ap.mark == some t) true 0 .zero

theorem forward_has_fresh_anonymous_target :
    targetSummary 0 .zero ∈ observations := by decide

theorem backward_producer_has_fresh_anonymous_target :
    producerHit = some (targetSummary 0 .zero) := by decide

theorem paired_c5_accepts_control_in_both_directions :
    c5Restrict exactEntry exactExit rootDemand (targetSummary 0 .zero) = some (targetSummary 0 .zero) ∧
    producerHit.bind (c5Restrict exactEntry exactExit rootDemand) = some (targetSummary 0 .zero) := by decide

theorem zero_is_admitted_and_fresh_target_requires_continuation :
    emittedZero .restricted [rootDemand] 0 .zero = [.zero] ∧
    continuationRelevant (targetSummary 0 .zero) = true ∧
    selectedTargetHandoff (targetSummary 0 .zero) = some rootDemand := by decide

theorem a_normal_observation_does_not_cancel_demand :
    observations.any (fun e => e.layer == .normal) = true ∧
    (observations.filter continuationRelevant).isEmpty = false := by decide

theorem nontermination_without_any_iteration_limit (n : Nat) :
    (OverwriteStable.repeatFromRun9 n).length = 4 ∧
    ∃ edge ∈ observations, c5Restrict exactEntry exactExit rootDemand edge = some edge ∧
      selectedTargetHandoff edge = some rootDemand ∧ continuationRelevant edge = true := by
  refine ⟨no_later_handoff_has_empty_demand n,targetSummary 0 .zero,
    forward_has_fresh_anonymous_target,?_,?_,?_⟩
  · exact paired_c5_accepts_control_in_both_directions.1
  · exact zero_is_admitted_and_fresh_target_requires_continuation.2.2
  · exact zero_is_admitted_and_fresh_target_requires_continuation.2.1

end OverwriteControl
#print axioms OverwriteControl.actual_forward_packets_are_precise_plus_may
#print axioms OverwriteControl.the_proved_domain_is_the_complete_caller_domain
#print axioms OverwriteControl.complete_saved_and_current_forward_offer_matches_this_reply
#print axioms OverwriteControl.complete_saved_and_current_backward_offer_matches_this_reply
#print axioms OverwriteControl.uniform_paths_never_need_more_than_eight_fields
#print axioms OverwriteControl.arbitrary_later_limits_do_not_cut_a_caller_packet
#print axioms OverwriteControl.backward_reply_is_stable_and_reaches_the_producer
#print axioms OverwriteControl.forward_has_fresh_anonymous_target
#print axioms OverwriteControl.backward_producer_has_fresh_anonymous_target
#print axioms OverwriteControl.paired_c5_accepts_control_in_both_directions
#print axioms OverwriteControl.zero_is_admitted_and_fresh_target_requires_continuation
#print axioms OverwriteControl.a_normal_observation_does_not_cancel_demand
#print axioms OverwriteControl.nontermination_without_any_iteration_limit

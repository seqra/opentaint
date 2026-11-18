import LayerProof
import CompleteRegression
import ScopedRegression
import CompleteCold
import ScopedCold
import ReplyOldExactCold
import ReplyOldMarkCold
import LayerOldFieldCold
import LayerOldExactCold
import LayerOldMarkCold
import ReplyCold
namespace LayerRegression
open NonEmptyPolicy NonEmptyRestriction CompleteRegression
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl

theorem every_old_guard_ineligible_offer_keeps_its_reply (run : Nat)
    (domains : List Offered) (current : List ReplyCore.Edge)
    (old : CompleteRegression.noGate run domains current=true)
    (a : Offered) (ha : a∈domains) (e : ReplyCore.Edge) (he : e∈current)
    (closed : List Ap) (service : List ReplyCore.Edge) (native : List Value) :
    LayerBody.suppressReply run closed service native a e=false := by
  have noA := List.all_eq_true.mp old a ha
  have noE := List.all_eq_true.mp noA e he
  have no : CompletePoint.suppress run [a.ap] a e=false := by simpa using noE
  exact LayerProof.rejected_old_input_guard_rejects_every_region run closed service native a e no

theorem old_guard_ineligible_reply_packet_is_unchanged (run : Nat) (a : Offered)
    (xs : List ReplyCore.Edge) (closed : List Ap) (service : List ReplyCore.Edge) (native : List Value)
    (old : ∀ e∈xs,CompletePoint.suppress run [a.ap] a e=false) :
    xs.filter (fun e => !LayerBody.suppressReply run closed service native a e)=xs := by
  apply List.filter_eq_self.mpr
  intro e he
  simp only [LayerProof.rejected_old_input_guard_rejects_every_region run closed service native a e (old e he),Bool.not_false]

theorem strict_MUST_actual_has_no_new_selection (run : Nat) (a : Offered)
    (closed : List Ap) (service : List ReplyCore.Edge) (native : List Value) (e : ReplyCore.Edge)
    (must : a.ap.tail=.must) : LayerBody.suppressReply run closed service native a e=false := by
  simp [LayerBody.suppressReply,LayerBody.suppress,must]

theorem old_FLOW_actual_has_no_new_selection (run : Nat) (a : Offered)
    (closed : List Ap) (service : List ReplyCore.Edge) (native : List Value) (e : ReplyCore.Edge)
    (flow : a.ap.mark=none) : LayerBody.suppressReply run closed service native a e=false := by
  simp [LayerBody.suppressReply,LayerBody.suppress,flow]

theorem old_DEMAND_actual_has_no_new_selection (run : Nat) (a : Offered)
    (closed : List Ap) (service : List ReplyCore.Edge) (native : List Value) (e : ReplyCore.Edge)
    (demand : a.demand=true) : LayerBody.suppressReply run closed service native a e=false := by
  simp [LayerBody.suppressReply,LayerBody.suppress,demand]

-- The old exhaustive noGate checks cover the complete ordinary-campaign
-- domains and published reply sets. The universal bridge above lifts them
-- for every possible new closure status, NORMAL basis and native packet.
theorem ordinary_Double_retains_guard_ineligibility :
    noGate 1 HeadOldDouble.state1.data.domains.flatten HeadOldDouble.state1.data.current.flatten=true ∧
    noGate 2 HeadOldDouble.state2.data.domains.flatten HeadOldDouble.state2.data.current.flatten=true ∧
    noGate 3 HeadOldDouble.state3.data.domains.flatten HeadOldDouble.state3.data.current.flatten=true ∧
    noGate 4 HeadOldDouble.state4.data.domains.flatten HeadOldDouble.state4.data.current.flatten=true ∧
    noGate 5 HeadOldDouble.state5.data.domains.flatten HeadOldDouble.state5.data.current.flatten=true ∧
    noGate 6 HeadOldDouble.state6.data.domains.flatten HeadOldDouble.state6.data.current.flatten=true ∧
    noGate 7 HeadOldDouble.state7.data.domains.flatten HeadOldDouble.state7.data.current.flatten=true ∧
    noGate 8 HeadOldDouble.state8.data.domains.flatten HeadOldDouble.state8.data.current.flatten=true ∧
    noGate 9 HeadOldDouble.state9.data.domains.flatten HeadOldDouble.state9.data.current.flatten=true ∧
    noGate 10 HeadOldDouble.state10.data.domains.flatten HeadOldDouble.state10.data.current.flatten=true ∧
    noGate 11 HeadOldDouble.state11.data.domains.flatten HeadOldDouble.state11.data.current.flatten=true ∧
    noGate 12 HeadOldDouble.state12.data.domains.flatten HeadOldDouble.state12.data.current.flatten=true ∧
    noGate 13 HeadOldDouble.state13.data.domains.flatten HeadOldDouble.state13.data.current.flatten=true ∧
    noGate 14 HeadOldDouble.state14.data.domains.flatten HeadOldDouble.state14.data.current.flatten=true ∧
    noGate 15 HeadOldDouble.state15.data.domains.flatten HeadOldDouble.state15.data.current.flatten=true ∧
    noGate 16 HeadOldDouble.state16.data.domains.flatten HeadOldDouble.state16.data.current.flatten=true :=
  CompleteRegression.ordinary_Double_no_current_reply_can_be_pruned

theorem ordinary_Double_retains_its_stop_and_expected_observation :
    UniformCampaign.stopped 15 HeadOldDouble.state15=true ∧
    HeadOldDouble.state15.report=HeadOldDouble.c.expected :=
  CompleteRegression.ordinary_Double_still_stops_with_the_expected_observation

theorem ordinary_Growth_retains_guard_ineligibility :
    noGate 1 HeadOldGrowth.state1.data.domains.flatten HeadOldGrowth.state1.data.current.flatten=true ∧
    noGate 2 HeadOldGrowth.state2.data.domains.flatten HeadOldGrowth.state2.data.current.flatten=true ∧
    noGate 3 HeadOldGrowth.state3.data.domains.flatten HeadOldGrowth.state3.data.current.flatten=true ∧
    noGate 4 HeadOldGrowth.state4.data.domains.flatten HeadOldGrowth.state4.data.current.flatten=true ∧
    noGate 5 HeadOldGrowth.state5.data.domains.flatten HeadOldGrowth.state5.data.current.flatten=true ∧
    noGate 6 HeadOldGrowth.state6.data.domains.flatten HeadOldGrowth.state6.data.current.flatten=true ∧
    noGate 7 HeadOldGrowth.state7.data.domains.flatten HeadOldGrowth.state7.data.current.flatten=true ∧
    noGate 8 HeadOldGrowth.state8.data.domains.flatten HeadOldGrowth.state8.data.current.flatten=true :=
  CompleteRegression.ordinary_Growth_no_current_reply_can_be_pruned

theorem ordinary_Growth_retains_its_stop_and_expected_observation :
    UniformCampaign.stopped 7 HeadOldGrowth.state7=true ∧
    HeadOldGrowth.state7.report=HeadOldGrowth.c.expected :=
  CompleteRegression.ordinary_Growth_still_stops_with_the_expected_observation

theorem ordinary_LongReader_retains_guard_ineligibility :
    noGate 1 HeadOldLongReader.state1.data.domains.flatten HeadOldLongReader.state1.data.current.flatten=true ∧
    noGate 2 HeadOldLongReader.state2.data.domains.flatten HeadOldLongReader.state2.data.current.flatten=true ∧
    noGate 3 HeadOldLongReader.state3.data.domains.flatten HeadOldLongReader.state3.data.current.flatten=true ∧
    noGate 4 HeadOldLongReader.state4.data.domains.flatten HeadOldLongReader.state4.data.current.flatten=true ∧
    noGate 5 HeadOldLongReader.state5.data.domains.flatten HeadOldLongReader.state5.data.current.flatten=true ∧
    noGate 6 HeadOldLongReader.state6.data.domains.flatten HeadOldLongReader.state6.data.current.flatten=true :=
  CompleteRegression.ordinary_LongReader_no_current_reply_can_be_pruned

theorem ordinary_LongReader_retains_its_stop_and_expected_observation :
    UniformCampaign.stopped 5 HeadOldLongReader.state5=true ∧
    HeadOldLongReader.state5.report=HeadOldLongReader.c.expected :=
  CompleteRegression.ordinary_LongReader_still_stops_with_the_expected_observation

theorem ordinary_Nested_retains_guard_ineligibility :
    noGate 1 HeadOldNested.state1.data.domains.flatten HeadOldNested.state1.data.current.flatten=true ∧
    noGate 2 HeadOldNested.state2.data.domains.flatten HeadOldNested.state2.data.current.flatten=true ∧
    noGate 3 HeadOldNested.state3.data.domains.flatten HeadOldNested.state3.data.current.flatten=true ∧
    noGate 4 HeadOldNested.state4.data.domains.flatten HeadOldNested.state4.data.current.flatten=true ∧
    noGate 5 HeadOldNested.state5.data.domains.flatten HeadOldNested.state5.data.current.flatten=true ∧
    noGate 6 HeadOldNested.state6.data.domains.flatten HeadOldNested.state6.data.current.flatten=true ∧
    noGate 7 HeadOldNested.state7.data.domains.flatten HeadOldNested.state7.data.current.flatten=true ∧
    noGate 8 HeadOldNested.state8.data.domains.flatten HeadOldNested.state8.data.current.flatten=true ∧
    noGate 9 HeadOldNested.state9.data.domains.flatten HeadOldNested.state9.data.current.flatten=true ∧
    noGate 10 HeadOldNested.state10.data.domains.flatten HeadOldNested.state10.data.current.flatten=true :=
  CompleteRegression.ordinary_Nested_no_current_reply_can_be_pruned

theorem ordinary_Nested_retains_its_stop_and_expected_observation :
    UniformCampaign.stopped 9 HeadOldNested.state9=true ∧
    HeadOldNested.state9.report=HeadOldNested.c.expected :=
  CompleteRegression.ordinary_Nested_still_stops_with_the_expected_observation

theorem ordinary_NestedDeep_retains_guard_ineligibility :
    noGate 1 HeadOldNestedDeep.state1.data.domains.flatten HeadOldNestedDeep.state1.data.current.flatten=true ∧
    noGate 2 HeadOldNestedDeep.state2.data.domains.flatten HeadOldNestedDeep.state2.data.current.flatten=true ∧
    noGate 3 HeadOldNestedDeep.state3.data.domains.flatten HeadOldNestedDeep.state3.data.current.flatten=true ∧
    noGate 4 HeadOldNestedDeep.state4.data.domains.flatten HeadOldNestedDeep.state4.data.current.flatten=true ∧
    noGate 5 HeadOldNestedDeep.state5.data.domains.flatten HeadOldNestedDeep.state5.data.current.flatten=true ∧
    noGate 6 HeadOldNestedDeep.state6.data.domains.flatten HeadOldNestedDeep.state6.data.current.flatten=true :=
  CompleteRegression.ordinary_NestedDeep_no_current_reply_can_be_pruned

theorem ordinary_NestedDeep_retains_its_stop_and_expected_observation :
    UniformCampaign.stopped 5 HeadOldNestedDeep.state5=true ∧
    HeadOldNestedDeep.state5.report=HeadOldNestedDeep.c.expected :=
  CompleteRegression.ordinary_NestedDeep_still_stops_with_the_expected_observation

theorem ordinary_NestedExact_retains_guard_ineligibility :
    noGate 1 HeadOldNestedExact.state1.data.domains.flatten HeadOldNestedExact.state1.data.current.flatten=true ∧
    noGate 2 HeadOldNestedExact.state2.data.domains.flatten HeadOldNestedExact.state2.data.current.flatten=true ∧
    noGate 3 HeadOldNestedExact.state3.data.domains.flatten HeadOldNestedExact.state3.data.current.flatten=true ∧
    noGate 4 HeadOldNestedExact.state4.data.domains.flatten HeadOldNestedExact.state4.data.current.flatten=true :=
  CompleteRegression.ordinary_NestedExact_no_current_reply_can_be_pruned

theorem ordinary_NestedExact_retains_its_stop_and_expected_observation :
    UniformCampaign.stopped 3 HeadOldNestedExact.state3=true ∧
    HeadOldNestedExact.state3.report=HeadOldNestedExact.c.expected :=
  CompleteRegression.ordinary_NestedExact_still_stops_with_the_expected_observation

theorem ordinary_NestedLarger_retains_guard_ineligibility :
    noGate 1 HeadOldNestedLarger.state1.data.domains.flatten HeadOldNestedLarger.state1.data.current.flatten=true ∧
    noGate 2 HeadOldNestedLarger.state2.data.domains.flatten HeadOldNestedLarger.state2.data.current.flatten=true ∧
    noGate 3 HeadOldNestedLarger.state3.data.domains.flatten HeadOldNestedLarger.state3.data.current.flatten=true ∧
    noGate 4 HeadOldNestedLarger.state4.data.domains.flatten HeadOldNestedLarger.state4.data.current.flatten=true ∧
    noGate 5 HeadOldNestedLarger.state5.data.domains.flatten HeadOldNestedLarger.state5.data.current.flatten=true ∧
    noGate 6 HeadOldNestedLarger.state6.data.domains.flatten HeadOldNestedLarger.state6.data.current.flatten=true ∧
    noGate 7 HeadOldNestedLarger.state7.data.domains.flatten HeadOldNestedLarger.state7.data.current.flatten=true ∧
    noGate 8 HeadOldNestedLarger.state8.data.domains.flatten HeadOldNestedLarger.state8.data.current.flatten=true ∧
    noGate 9 HeadOldNestedLarger.state9.data.domains.flatten HeadOldNestedLarger.state9.data.current.flatten=true ∧
    noGate 10 HeadOldNestedLarger.state10.data.domains.flatten HeadOldNestedLarger.state10.data.current.flatten=true ∧
    noGate 11 HeadOldNestedLarger.state11.data.domains.flatten HeadOldNestedLarger.state11.data.current.flatten=true ∧
    noGate 12 HeadOldNestedLarger.state12.data.domains.flatten HeadOldNestedLarger.state12.data.current.flatten=true :=
  CompleteRegression.ordinary_NestedLarger_no_current_reply_can_be_pruned

theorem ordinary_NestedLarger_retains_its_stop_and_expected_observation :
    UniformCampaign.stopped 11 HeadOldNestedLarger.state11=true ∧
    HeadOldNestedLarger.state11.report=HeadOldNestedLarger.c.expected :=
  CompleteRegression.ordinary_NestedLarger_still_stops_with_the_expected_observation

theorem ordinary_NestedNegative_retains_guard_ineligibility :
    noGate 1 HeadOldNestedNegative.state1.data.domains.flatten HeadOldNestedNegative.state1.data.current.flatten=true ∧
    noGate 2 HeadOldNestedNegative.state2.data.domains.flatten HeadOldNestedNegative.state2.data.current.flatten=true ∧
    noGate 3 HeadOldNestedNegative.state3.data.domains.flatten HeadOldNestedNegative.state3.data.current.flatten=true ∧
    noGate 4 HeadOldNestedNegative.state4.data.domains.flatten HeadOldNestedNegative.state4.data.current.flatten=true :=
  CompleteRegression.ordinary_NestedNegative_no_current_reply_can_be_pruned

theorem ordinary_NestedNegative_retains_its_stop_and_expected_observation :
    UniformCampaign.stopped 3 HeadOldNestedNegative.state3=true ∧
    HeadOldNestedNegative.state3.report=HeadOldNestedNegative.c.expected :=
  CompleteRegression.ordinary_NestedNegative_still_stops_with_the_expected_observation

theorem ordinary_NestedPositive_retains_guard_ineligibility :
    noGate 1 HeadOldNestedPositive.state1.data.domains.flatten HeadOldNestedPositive.state1.data.current.flatten=true ∧
    noGate 2 HeadOldNestedPositive.state2.data.domains.flatten HeadOldNestedPositive.state2.data.current.flatten=true ∧
    noGate 3 HeadOldNestedPositive.state3.data.domains.flatten HeadOldNestedPositive.state3.data.current.flatten=true ∧
    noGate 4 HeadOldNestedPositive.state4.data.domains.flatten HeadOldNestedPositive.state4.data.current.flatten=true :=
  CompleteRegression.ordinary_NestedPositive_no_current_reply_can_be_pruned

theorem ordinary_NestedPositive_retains_its_stop_and_expected_observation :
    UniformCampaign.stopped 3 HeadOldNestedPositive.state3=true ∧
    HeadOldNestedPositive.state3.report=HeadOldNestedPositive.c.expected :=
  CompleteRegression.ordinary_NestedPositive_still_stops_with_the_expected_observation

theorem ordinary_NestedSurvivor_retains_guard_ineligibility :
    noGate 1 HeadOldNestedSurvivor.state1.data.domains.flatten HeadOldNestedSurvivor.state1.data.current.flatten=true ∧
    noGate 2 HeadOldNestedSurvivor.state2.data.domains.flatten HeadOldNestedSurvivor.state2.data.current.flatten=true ∧
    noGate 3 HeadOldNestedSurvivor.state3.data.domains.flatten HeadOldNestedSurvivor.state3.data.current.flatten=true ∧
    noGate 4 HeadOldNestedSurvivor.state4.data.domains.flatten HeadOldNestedSurvivor.state4.data.current.flatten=true ∧
    noGate 5 HeadOldNestedSurvivor.state5.data.domains.flatten HeadOldNestedSurvivor.state5.data.current.flatten=true ∧
    noGate 6 HeadOldNestedSurvivor.state6.data.domains.flatten HeadOldNestedSurvivor.state6.data.current.flatten=true :=
  CompleteRegression.ordinary_NestedSurvivor_no_current_reply_can_be_pruned

theorem ordinary_NestedSurvivor_retains_its_stop_and_expected_observation :
    UniformCampaign.stopped 5 HeadOldNestedSurvivor.state5=true ∧
    HeadOldNestedSurvivor.state5.report=HeadOldNestedSurvivor.c.expected :=
  CompleteRegression.ordinary_NestedSurvivor_still_stops_with_the_expected_observation

theorem ordinary_OldBB_retains_guard_ineligibility :
    noGate 1 HeadOldOldBB.state1.data.domains.flatten HeadOldOldBB.state1.data.current.flatten=true ∧
    noGate 2 HeadOldOldBB.state2.data.domains.flatten HeadOldOldBB.state2.data.current.flatten=true ∧
    noGate 3 HeadOldOldBB.state3.data.domains.flatten HeadOldOldBB.state3.data.current.flatten=true ∧
    noGate 4 HeadOldOldBB.state4.data.domains.flatten HeadOldOldBB.state4.data.current.flatten=true ∧
    noGate 5 HeadOldOldBB.state5.data.domains.flatten HeadOldOldBB.state5.data.current.flatten=true ∧
    noGate 6 HeadOldOldBB.state6.data.domains.flatten HeadOldOldBB.state6.data.current.flatten=true :=
  CompleteRegression.ordinary_OldBB_no_current_reply_can_be_pruned

theorem ordinary_OldBB_retains_its_stop_and_expected_observation :
    UniformCampaign.stopped 5 HeadOldOldBB.state5=true ∧
    HeadOldOldBB.state5.report=HeadOldOldBB.c.expected :=
  CompleteRegression.ordinary_OldBB_still_stops_with_the_expected_observation

theorem ordinary_OldMethod_retains_guard_ineligibility :
    noGate 1 HeadOldOldMethod.state1.data.domains.flatten HeadOldOldMethod.state1.data.current.flatten=true ∧
    noGate 2 HeadOldOldMethod.state2.data.domains.flatten HeadOldOldMethod.state2.data.current.flatten=true ∧
    noGate 3 HeadOldOldMethod.state3.data.domains.flatten HeadOldOldMethod.state3.data.current.flatten=true ∧
    noGate 4 HeadOldOldMethod.state4.data.domains.flatten HeadOldOldMethod.state4.data.current.flatten=true ∧
    noGate 5 HeadOldOldMethod.state5.data.domains.flatten HeadOldOldMethod.state5.data.current.flatten=true ∧
    noGate 6 HeadOldOldMethod.state6.data.domains.flatten HeadOldOldMethod.state6.data.current.flatten=true :=
  CompleteRegression.ordinary_OldMethod_no_current_reply_can_be_pruned

theorem ordinary_OldMethod_retains_its_stop_and_expected_observation :
    UniformCampaign.stopped 5 HeadOldOldMethod.state5=true ∧
    HeadOldOldMethod.state5.report=HeadOldOldMethod.c.expected :=
  CompleteRegression.ordinary_OldMethod_still_stops_with_the_expected_observation

theorem ordinary_OrdinaryTwo_retains_guard_ineligibility :
    noGate 1 HeadOldOrdinaryTwo.state1.data.domains.flatten HeadOldOrdinaryTwo.state1.data.current.flatten=true ∧
    noGate 2 HeadOldOrdinaryTwo.state2.data.domains.flatten HeadOldOrdinaryTwo.state2.data.current.flatten=true ∧
    noGate 3 HeadOldOrdinaryTwo.state3.data.domains.flatten HeadOldOrdinaryTwo.state3.data.current.flatten=true ∧
    noGate 4 HeadOldOrdinaryTwo.state4.data.domains.flatten HeadOldOrdinaryTwo.state4.data.current.flatten=true :=
  CompleteRegression.ordinary_OrdinaryTwo_no_current_reply_can_be_pruned

theorem ordinary_OrdinaryTwo_retains_its_stop_and_expected_observation :
    UniformCampaign.stopped 3 HeadOldOrdinaryTwo.state3=true ∧
    HeadOldOrdinaryTwo.state3.report=HeadOldOrdinaryTwo.c.expected :=
  CompleteRegression.ordinary_OrdinaryTwo_still_stops_with_the_expected_observation

theorem ordinary_Overwrite_retains_guard_ineligibility :
    noGate 1 HeadOldOverwrite.state1.data.domains.flatten HeadOldOverwrite.state1.data.current.flatten=true ∧
    noGate 2 HeadOldOverwrite.state2.data.domains.flatten HeadOldOverwrite.state2.data.current.flatten=true ∧
    noGate 3 HeadOldOverwrite.state3.data.domains.flatten HeadOldOverwrite.state3.data.current.flatten=true ∧
    noGate 4 HeadOldOverwrite.state4.data.domains.flatten HeadOldOverwrite.state4.data.current.flatten=true ∧
    noGate 5 HeadOldOverwrite.state5.data.domains.flatten HeadOldOverwrite.state5.data.current.flatten=true ∧
    noGate 6 HeadOldOverwrite.state6.data.domains.flatten HeadOldOverwrite.state6.data.current.flatten=true ∧
    noGate 7 HeadOldOverwrite.state7.data.domains.flatten HeadOldOverwrite.state7.data.current.flatten=true ∧
    noGate 8 HeadOldOverwrite.state8.data.domains.flatten HeadOldOverwrite.state8.data.current.flatten=true ∧
    noGate 9 HeadOldOverwrite.state9.data.domains.flatten HeadOldOverwrite.state9.data.current.flatten=true ∧
    noGate 10 HeadOldOverwrite.state10.data.domains.flatten HeadOldOverwrite.state10.data.current.flatten=true :=
  CompleteRegression.ordinary_Overwrite_no_current_reply_can_be_pruned

theorem ordinary_Overwrite_retains_its_stop_and_expected_observation :
    UniformCampaign.stopped 9 HeadOldOverwrite.state9=true ∧
    HeadOldOverwrite.state9.report=HeadOldOverwrite.c.expected :=
  CompleteRegression.ordinary_Overwrite_still_stops_with_the_expected_observation

theorem ordinary_Postfix_retains_guard_ineligibility :
    noGate 1 HeadOldPostfix.state1.data.domains.flatten HeadOldPostfix.state1.data.current.flatten=true ∧
    noGate 2 HeadOldPostfix.state2.data.domains.flatten HeadOldPostfix.state2.data.current.flatten=true ∧
    noGate 3 HeadOldPostfix.state3.data.domains.flatten HeadOldPostfix.state3.data.current.flatten=true ∧
    noGate 4 HeadOldPostfix.state4.data.domains.flatten HeadOldPostfix.state4.data.current.flatten=true ∧
    noGate 5 HeadOldPostfix.state5.data.domains.flatten HeadOldPostfix.state5.data.current.flatten=true ∧
    noGate 6 HeadOldPostfix.state6.data.domains.flatten HeadOldPostfix.state6.data.current.flatten=true ∧
    noGate 7 HeadOldPostfix.state7.data.domains.flatten HeadOldPostfix.state7.data.current.flatten=true ∧
    noGate 8 HeadOldPostfix.state8.data.domains.flatten HeadOldPostfix.state8.data.current.flatten=true ∧
    noGate 9 HeadOldPostfix.state9.data.domains.flatten HeadOldPostfix.state9.data.current.flatten=true ∧
    noGate 10 HeadOldPostfix.state10.data.domains.flatten HeadOldPostfix.state10.data.current.flatten=true ∧
    noGate 11 HeadOldPostfix.state11.data.domains.flatten HeadOldPostfix.state11.data.current.flatten=true ∧
    noGate 12 HeadOldPostfix.state12.data.domains.flatten HeadOldPostfix.state12.data.current.flatten=true ∧
    noGate 13 HeadOldPostfix.state13.data.domains.flatten HeadOldPostfix.state13.data.current.flatten=true ∧
    noGate 14 HeadOldPostfix.state14.data.domains.flatten HeadOldPostfix.state14.data.current.flatten=true :=
  CompleteRegression.ordinary_Postfix_no_current_reply_can_be_pruned

theorem ordinary_Postfix_retains_its_stop_and_expected_observation :
    UniformCampaign.stopped 13 HeadOldPostfix.state13=true ∧
    HeadOldPostfix.state13.report=HeadOldPostfix.c.expected :=
  CompleteRegression.ordinary_Postfix_still_stops_with_the_expected_observation

theorem ordinary_Prefix_retains_guard_ineligibility :
    noGate 1 HeadOldPrefix.state1.data.domains.flatten HeadOldPrefix.state1.data.current.flatten=true ∧
    noGate 2 HeadOldPrefix.state2.data.domains.flatten HeadOldPrefix.state2.data.current.flatten=true ∧
    noGate 3 HeadOldPrefix.state3.data.domains.flatten HeadOldPrefix.state3.data.current.flatten=true ∧
    noGate 4 HeadOldPrefix.state4.data.domains.flatten HeadOldPrefix.state4.data.current.flatten=true ∧
    noGate 5 HeadOldPrefix.state5.data.domains.flatten HeadOldPrefix.state5.data.current.flatten=true ∧
    noGate 6 HeadOldPrefix.state6.data.domains.flatten HeadOldPrefix.state6.data.current.flatten=true ∧
    noGate 7 HeadOldPrefix.state7.data.domains.flatten HeadOldPrefix.state7.data.current.flatten=true ∧
    noGate 8 HeadOldPrefix.state8.data.domains.flatten HeadOldPrefix.state8.data.current.flatten=true :=
  CompleteRegression.ordinary_Prefix_no_current_reply_can_be_pruned

theorem ordinary_Prefix_retains_its_stop_and_expected_observation :
    UniformCampaign.stopped 7 HeadOldPrefix.state7=true ∧
    HeadOldPrefix.state7.report=HeadOldPrefix.c.expected :=
  CompleteRegression.ordinary_Prefix_still_stops_with_the_expected_observation

theorem ordinary_PrefixPostfix_retains_guard_ineligibility :
    noGate 1 HeadOldPrefixPostfix.state1.data.domains.flatten HeadOldPrefixPostfix.state1.data.current.flatten=true ∧
    noGate 2 HeadOldPrefixPostfix.state2.data.domains.flatten HeadOldPrefixPostfix.state2.data.current.flatten=true ∧
    noGate 3 HeadOldPrefixPostfix.state3.data.domains.flatten HeadOldPrefixPostfix.state3.data.current.flatten=true ∧
    noGate 4 HeadOldPrefixPostfix.state4.data.domains.flatten HeadOldPrefixPostfix.state4.data.current.flatten=true ∧
    noGate 5 HeadOldPrefixPostfix.state5.data.domains.flatten HeadOldPrefixPostfix.state5.data.current.flatten=true ∧
    noGate 6 HeadOldPrefixPostfix.state6.data.domains.flatten HeadOldPrefixPostfix.state6.data.current.flatten=true ∧
    noGate 7 HeadOldPrefixPostfix.state7.data.domains.flatten HeadOldPrefixPostfix.state7.data.current.flatten=true ∧
    noGate 8 HeadOldPrefixPostfix.state8.data.domains.flatten HeadOldPrefixPostfix.state8.data.current.flatten=true ∧
    noGate 9 HeadOldPrefixPostfix.state9.data.domains.flatten HeadOldPrefixPostfix.state9.data.current.flatten=true ∧
    noGate 10 HeadOldPrefixPostfix.state10.data.domains.flatten HeadOldPrefixPostfix.state10.data.current.flatten=true ∧
    noGate 11 HeadOldPrefixPostfix.state11.data.domains.flatten HeadOldPrefixPostfix.state11.data.current.flatten=true ∧
    noGate 12 HeadOldPrefixPostfix.state12.data.domains.flatten HeadOldPrefixPostfix.state12.data.current.flatten=true :=
  CompleteRegression.ordinary_PrefixPostfix_no_current_reply_can_be_pruned

theorem ordinary_PrefixPostfix_retains_its_stop_and_expected_observation :
    UniformCampaign.stopped 11 HeadOldPrefixPostfix.state11=true ∧
    HeadOldPrefixPostfix.state11.report=HeadOldPrefixPostfix.c.expected :=
  CompleteRegression.ordinary_PrefixPostfix_still_stops_with_the_expected_observation

theorem ordinary_RoundTrip_retains_guard_ineligibility :
    noGate 1 HeadOldRoundTrip.state1.data.domains.flatten HeadOldRoundTrip.state1.data.current.flatten=true ∧
    noGate 2 HeadOldRoundTrip.state2.data.domains.flatten HeadOldRoundTrip.state2.data.current.flatten=true ∧
    noGate 3 HeadOldRoundTrip.state3.data.domains.flatten HeadOldRoundTrip.state3.data.current.flatten=true ∧
    noGate 4 HeadOldRoundTrip.state4.data.domains.flatten HeadOldRoundTrip.state4.data.current.flatten=true ∧
    noGate 5 HeadOldRoundTrip.state5.data.domains.flatten HeadOldRoundTrip.state5.data.current.flatten=true ∧
    noGate 6 HeadOldRoundTrip.state6.data.domains.flatten HeadOldRoundTrip.state6.data.current.flatten=true ∧
    noGate 7 HeadOldRoundTrip.state7.data.domains.flatten HeadOldRoundTrip.state7.data.current.flatten=true ∧
    noGate 8 HeadOldRoundTrip.state8.data.domains.flatten HeadOldRoundTrip.state8.data.current.flatten=true ∧
    noGate 9 HeadOldRoundTrip.state9.data.domains.flatten HeadOldRoundTrip.state9.data.current.flatten=true ∧
    noGate 10 HeadOldRoundTrip.state10.data.domains.flatten HeadOldRoundTrip.state10.data.current.flatten=true :=
  CompleteRegression.ordinary_RoundTrip_no_current_reply_can_be_pruned

theorem ordinary_RoundTrip_retains_its_stop_and_expected_observation :
    UniformCampaign.stopped 9 HeadOldRoundTrip.state9=true ∧
    HeadOldRoundTrip.state9.report=HeadOldRoundTrip.c.expected :=
  CompleteRegression.ordinary_RoundTrip_still_stops_with_the_expected_observation

theorem HeadDeepCold_retains_guard_ineligibility :
    noGate 1 HeadDeepCold.s1.data.domains HeadDeepCold.s1.data.raw=true ∧
    noGate 2 HeadDeepCold.s2.data.domains HeadDeepCold.s2.data.raw=true ∧
    noGate 3 HeadDeepCold.s3.data.domains HeadDeepCold.s3.data.raw=true ∧
    noGate 4 HeadDeepCold.s4.data.domains HeadDeepCold.s4.data.raw=true ∧
    noGate 5 HeadDeepCold.s5.data.domains HeadDeepCold.s5.data.raw=true ∧
    noGate 6 HeadDeepCold.s6.data.domains HeadDeepCold.s6.data.raw=true :=
  CompleteRegression.HeadDeepCold_no_current_reply_can_be_pruned
theorem HeadShallowCold_retains_guard_ineligibility :
    noGate 1 HeadShallowCold.s1.data.domains HeadShallowCold.s1.data.raw=true ∧
    noGate 2 HeadShallowCold.s2.data.domains HeadShallowCold.s2.data.raw=true ∧
    noGate 3 HeadShallowCold.s3.data.domains HeadShallowCold.s3.data.raw=true ∧
    noGate 4 HeadShallowCold.s4.data.domains HeadShallowCold.s4.data.raw=true ∧
    noGate 5 HeadShallowCold.s5.data.domains HeadShallowCold.s5.data.raw=true ∧
    noGate 6 HeadShallowCold.s6.data.domains HeadShallowCold.s6.data.raw=true :=
  CompleteRegression.HeadShallowCold_no_current_reply_can_be_pruned
theorem HeadOldAlternating_retains_guard_ineligibility :
    noGate 1 HeadOldAlternating.state1.data.domains HeadOldAlternating.state1.data.raw=true ∧
    noGate 2 HeadOldAlternating.state2.data.domains HeadOldAlternating.state2.data.raw=true ∧
    noGate 3 HeadOldAlternating.state3.data.domains HeadOldAlternating.state3.data.raw=true ∧
    noGate 4 HeadOldAlternating.state4.data.domains HeadOldAlternating.state4.data.raw=true ∧
    noGate 5 HeadOldAlternating.state5.data.domains HeadOldAlternating.state5.data.raw=true ∧
    noGate 6 HeadOldAlternating.state6.data.domains HeadOldAlternating.state6.data.raw=true :=
  CompleteRegression.HeadOldAlternating_no_current_reply_can_be_pruned
def forgetField (s : LayerOldField.State) : ReplyBody.State :=
  ⟨s.rows,s.saved.map (fun n => ⟨n.edge,n.back⟩),s.complete,s.services,
    s.sourceAllowed,s.observationActive,s.report,
    ⟨s.data.domains,s.data.raw,s.data.complete,s.data.services,s.data.offers,s.data.closed⟩⟩
def forgetExact (s : LayerOldExact.State) : ReplyOldExact.State :=
  ⟨s.rows,s.saved.map (fun n => ⟨n.edge,n.back⟩),s.complete,s.services,
    s.sourceAllowed,s.observationActive,s.report,
    ⟨s.data.domains,s.data.raw,s.data.complete,s.data.services,s.data.offers,s.data.closed⟩⟩
def forgetMark (s : LayerOldMark.State) : ReplyOldMark.State :=
  ⟨s.rows,s.saved.map (fun n => ⟨n.edge,n.back⟩),s.complete,s.services,
    s.sourceAllowed,s.observationActive,s.report,
    ⟨s.data.domains,s.data.raw,s.data.complete,s.data.services,s.data.offers,s.data.closed⟩⟩

theorem old_field_complete_cold_history_is_semantically_unchanged :
    forgetField LayerOldFieldCold.s1=ReplyCold.s1 ∧
    forgetField LayerOldFieldCold.s2=ReplyCold.s2 ∧
    forgetField LayerOldFieldCold.s3=ReplyCold.s3 ∧
    forgetField LayerOldFieldCold.s4=ReplyCold.s4 ∧
    forgetField LayerOldFieldCold.s5=ReplyCold.s5 ∧
    forgetField LayerOldFieldCold.s6=ReplyCold.s6 := by decide +kernel

theorem old_exact_complete_cold_history_is_semantically_unchanged :
    forgetExact LayerOldExactCold.s1=ReplyOldExactCold.s1 ∧
    forgetExact LayerOldExactCold.s2=ReplyOldExactCold.s2 ∧
    forgetExact LayerOldExactCold.s3=ReplyOldExactCold.s3 ∧
    forgetExact LayerOldExactCold.s4=ReplyOldExactCold.s4 ∧
    forgetExact LayerOldExactCold.s5=ReplyOldExactCold.s5 ∧
    forgetExact LayerOldExactCold.s6=ReplyOldExactCold.s6 := by decide +kernel

theorem old_mark_complete_cold_history_is_semantically_unchanged :
    forgetMark LayerOldMarkCold.s1=ReplyOldMarkCold.s1 ∧
    forgetMark LayerOldMarkCold.s2=ReplyOldMarkCold.s2 ∧
    forgetMark LayerOldMarkCold.s3=ReplyOldMarkCold.s3 ∧
    forgetMark LayerOldMarkCold.s4=ReplyOldMarkCold.s4 ∧
    forgetMark LayerOldMarkCold.s5=ReplyOldMarkCold.s5 ∧
    forgetMark LayerOldMarkCold.s6=ReplyOldMarkCold.s6 := by decide +kernel

end LayerRegression

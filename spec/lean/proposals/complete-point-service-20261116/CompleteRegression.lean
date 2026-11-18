import CompleteService
import HeadDeepCold
import HeadShallowCold
import HeadOldAlternating
import HeadControls
import HeadStrictExact
import HeadStrictUniform
import HeadStrictDifferent
import HeadOldDouble
import HeadOldGrowth
import HeadOldLongReader
import HeadOldNested
import HeadOldNestedDeep
import HeadOldNestedExact
import HeadOldNestedLarger
import HeadOldNestedNegative
import HeadOldNestedPositive
import HeadOldNestedSurvivor
import HeadOldOldBB
import HeadOldOldMethod
import HeadOldOrdinaryTwo
import HeadOldOverwrite
import HeadOldPostfix
import HeadOldPrefix
import HeadOldPrefixPostfix
import HeadOldRoundTrip
namespace CompleteRegression
open NonEmptyPolicy NonEmptyRestriction
set_option maxRecDepth 65536
set_option maxHeartbeats 160000000
def noGate (run : Nat) (domains : List Offered) (current : List CompletePoint.Edge) : Bool :=
  domains.all fun a => current.all fun e => !CompletePoint.suppress run [a.ap] a e
theorem ordinary_Double_no_current_reply_can_be_pruned :
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
    noGate 16 HeadOldDouble.state16.data.domains.flatten HeadOldDouble.state16.data.current.flatten=true := by decide +kernel
theorem ordinary_Double_still_stops_with_the_expected_observation :
    UniformCampaign.stopped 15 HeadOldDouble.state15=true ∧
    HeadOldDouble.state15.report=HeadOldDouble.c.expected := HeadOldDouble.natural_stop_and_expected_observation
theorem ordinary_Growth_no_current_reply_can_be_pruned :
    noGate 1 HeadOldGrowth.state1.data.domains.flatten HeadOldGrowth.state1.data.current.flatten=true ∧
    noGate 2 HeadOldGrowth.state2.data.domains.flatten HeadOldGrowth.state2.data.current.flatten=true ∧
    noGate 3 HeadOldGrowth.state3.data.domains.flatten HeadOldGrowth.state3.data.current.flatten=true ∧
    noGate 4 HeadOldGrowth.state4.data.domains.flatten HeadOldGrowth.state4.data.current.flatten=true ∧
    noGate 5 HeadOldGrowth.state5.data.domains.flatten HeadOldGrowth.state5.data.current.flatten=true ∧
    noGate 6 HeadOldGrowth.state6.data.domains.flatten HeadOldGrowth.state6.data.current.flatten=true ∧
    noGate 7 HeadOldGrowth.state7.data.domains.flatten HeadOldGrowth.state7.data.current.flatten=true ∧
    noGate 8 HeadOldGrowth.state8.data.domains.flatten HeadOldGrowth.state8.data.current.flatten=true := by decide +kernel
theorem ordinary_Growth_still_stops_with_the_expected_observation :
    UniformCampaign.stopped 7 HeadOldGrowth.state7=true ∧
    HeadOldGrowth.state7.report=HeadOldGrowth.c.expected := HeadOldGrowth.natural_stop_and_expected_observation
theorem ordinary_LongReader_no_current_reply_can_be_pruned :
    noGate 1 HeadOldLongReader.state1.data.domains.flatten HeadOldLongReader.state1.data.current.flatten=true ∧
    noGate 2 HeadOldLongReader.state2.data.domains.flatten HeadOldLongReader.state2.data.current.flatten=true ∧
    noGate 3 HeadOldLongReader.state3.data.domains.flatten HeadOldLongReader.state3.data.current.flatten=true ∧
    noGate 4 HeadOldLongReader.state4.data.domains.flatten HeadOldLongReader.state4.data.current.flatten=true ∧
    noGate 5 HeadOldLongReader.state5.data.domains.flatten HeadOldLongReader.state5.data.current.flatten=true ∧
    noGate 6 HeadOldLongReader.state6.data.domains.flatten HeadOldLongReader.state6.data.current.flatten=true := by decide +kernel
theorem ordinary_LongReader_still_stops_with_the_expected_observation :
    UniformCampaign.stopped 5 HeadOldLongReader.state5=true ∧
    HeadOldLongReader.state5.report=HeadOldLongReader.c.expected := HeadOldLongReader.natural_stop_and_expected_observation
theorem ordinary_Nested_no_current_reply_can_be_pruned :
    noGate 1 HeadOldNested.state1.data.domains.flatten HeadOldNested.state1.data.current.flatten=true ∧
    noGate 2 HeadOldNested.state2.data.domains.flatten HeadOldNested.state2.data.current.flatten=true ∧
    noGate 3 HeadOldNested.state3.data.domains.flatten HeadOldNested.state3.data.current.flatten=true ∧
    noGate 4 HeadOldNested.state4.data.domains.flatten HeadOldNested.state4.data.current.flatten=true ∧
    noGate 5 HeadOldNested.state5.data.domains.flatten HeadOldNested.state5.data.current.flatten=true ∧
    noGate 6 HeadOldNested.state6.data.domains.flatten HeadOldNested.state6.data.current.flatten=true ∧
    noGate 7 HeadOldNested.state7.data.domains.flatten HeadOldNested.state7.data.current.flatten=true ∧
    noGate 8 HeadOldNested.state8.data.domains.flatten HeadOldNested.state8.data.current.flatten=true ∧
    noGate 9 HeadOldNested.state9.data.domains.flatten HeadOldNested.state9.data.current.flatten=true ∧
    noGate 10 HeadOldNested.state10.data.domains.flatten HeadOldNested.state10.data.current.flatten=true := by decide +kernel
theorem ordinary_Nested_still_stops_with_the_expected_observation :
    UniformCampaign.stopped 9 HeadOldNested.state9=true ∧
    HeadOldNested.state9.report=HeadOldNested.c.expected := HeadOldNested.natural_stop_and_expected_observation
theorem ordinary_NestedDeep_no_current_reply_can_be_pruned :
    noGate 1 HeadOldNestedDeep.state1.data.domains.flatten HeadOldNestedDeep.state1.data.current.flatten=true ∧
    noGate 2 HeadOldNestedDeep.state2.data.domains.flatten HeadOldNestedDeep.state2.data.current.flatten=true ∧
    noGate 3 HeadOldNestedDeep.state3.data.domains.flatten HeadOldNestedDeep.state3.data.current.flatten=true ∧
    noGate 4 HeadOldNestedDeep.state4.data.domains.flatten HeadOldNestedDeep.state4.data.current.flatten=true ∧
    noGate 5 HeadOldNestedDeep.state5.data.domains.flatten HeadOldNestedDeep.state5.data.current.flatten=true ∧
    noGate 6 HeadOldNestedDeep.state6.data.domains.flatten HeadOldNestedDeep.state6.data.current.flatten=true := by decide +kernel
theorem ordinary_NestedDeep_still_stops_with_the_expected_observation :
    UniformCampaign.stopped 5 HeadOldNestedDeep.state5=true ∧
    HeadOldNestedDeep.state5.report=HeadOldNestedDeep.c.expected := HeadOldNestedDeep.natural_stop_and_expected_observation
theorem ordinary_NestedExact_no_current_reply_can_be_pruned :
    noGate 1 HeadOldNestedExact.state1.data.domains.flatten HeadOldNestedExact.state1.data.current.flatten=true ∧
    noGate 2 HeadOldNestedExact.state2.data.domains.flatten HeadOldNestedExact.state2.data.current.flatten=true ∧
    noGate 3 HeadOldNestedExact.state3.data.domains.flatten HeadOldNestedExact.state3.data.current.flatten=true ∧
    noGate 4 HeadOldNestedExact.state4.data.domains.flatten HeadOldNestedExact.state4.data.current.flatten=true := by decide +kernel
theorem ordinary_NestedExact_still_stops_with_the_expected_observation :
    UniformCampaign.stopped 3 HeadOldNestedExact.state3=true ∧
    HeadOldNestedExact.state3.report=HeadOldNestedExact.c.expected := HeadOldNestedExact.natural_stop_and_expected_observation
theorem ordinary_NestedLarger_no_current_reply_can_be_pruned :
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
    noGate 12 HeadOldNestedLarger.state12.data.domains.flatten HeadOldNestedLarger.state12.data.current.flatten=true := by decide +kernel
theorem ordinary_NestedLarger_still_stops_with_the_expected_observation :
    UniformCampaign.stopped 11 HeadOldNestedLarger.state11=true ∧
    HeadOldNestedLarger.state11.report=HeadOldNestedLarger.c.expected := HeadOldNestedLarger.natural_stop_and_expected_observation
theorem ordinary_NestedNegative_no_current_reply_can_be_pruned :
    noGate 1 HeadOldNestedNegative.state1.data.domains.flatten HeadOldNestedNegative.state1.data.current.flatten=true ∧
    noGate 2 HeadOldNestedNegative.state2.data.domains.flatten HeadOldNestedNegative.state2.data.current.flatten=true ∧
    noGate 3 HeadOldNestedNegative.state3.data.domains.flatten HeadOldNestedNegative.state3.data.current.flatten=true ∧
    noGate 4 HeadOldNestedNegative.state4.data.domains.flatten HeadOldNestedNegative.state4.data.current.flatten=true := by decide +kernel
theorem ordinary_NestedNegative_still_stops_with_the_expected_observation :
    UniformCampaign.stopped 3 HeadOldNestedNegative.state3=true ∧
    HeadOldNestedNegative.state3.report=HeadOldNestedNegative.c.expected := HeadOldNestedNegative.natural_stop_and_expected_observation
theorem ordinary_NestedPositive_no_current_reply_can_be_pruned :
    noGate 1 HeadOldNestedPositive.state1.data.domains.flatten HeadOldNestedPositive.state1.data.current.flatten=true ∧
    noGate 2 HeadOldNestedPositive.state2.data.domains.flatten HeadOldNestedPositive.state2.data.current.flatten=true ∧
    noGate 3 HeadOldNestedPositive.state3.data.domains.flatten HeadOldNestedPositive.state3.data.current.flatten=true ∧
    noGate 4 HeadOldNestedPositive.state4.data.domains.flatten HeadOldNestedPositive.state4.data.current.flatten=true := by decide +kernel
theorem ordinary_NestedPositive_still_stops_with_the_expected_observation :
    UniformCampaign.stopped 3 HeadOldNestedPositive.state3=true ∧
    HeadOldNestedPositive.state3.report=HeadOldNestedPositive.c.expected := HeadOldNestedPositive.natural_stop_and_expected_observation
theorem ordinary_NestedSurvivor_no_current_reply_can_be_pruned :
    noGate 1 HeadOldNestedSurvivor.state1.data.domains.flatten HeadOldNestedSurvivor.state1.data.current.flatten=true ∧
    noGate 2 HeadOldNestedSurvivor.state2.data.domains.flatten HeadOldNestedSurvivor.state2.data.current.flatten=true ∧
    noGate 3 HeadOldNestedSurvivor.state3.data.domains.flatten HeadOldNestedSurvivor.state3.data.current.flatten=true ∧
    noGate 4 HeadOldNestedSurvivor.state4.data.domains.flatten HeadOldNestedSurvivor.state4.data.current.flatten=true ∧
    noGate 5 HeadOldNestedSurvivor.state5.data.domains.flatten HeadOldNestedSurvivor.state5.data.current.flatten=true ∧
    noGate 6 HeadOldNestedSurvivor.state6.data.domains.flatten HeadOldNestedSurvivor.state6.data.current.flatten=true := by decide +kernel
theorem ordinary_NestedSurvivor_still_stops_with_the_expected_observation :
    UniformCampaign.stopped 5 HeadOldNestedSurvivor.state5=true ∧
    HeadOldNestedSurvivor.state5.report=HeadOldNestedSurvivor.c.expected := HeadOldNestedSurvivor.natural_stop_and_expected_observation
theorem ordinary_OldBB_no_current_reply_can_be_pruned :
    noGate 1 HeadOldOldBB.state1.data.domains.flatten HeadOldOldBB.state1.data.current.flatten=true ∧
    noGate 2 HeadOldOldBB.state2.data.domains.flatten HeadOldOldBB.state2.data.current.flatten=true ∧
    noGate 3 HeadOldOldBB.state3.data.domains.flatten HeadOldOldBB.state3.data.current.flatten=true ∧
    noGate 4 HeadOldOldBB.state4.data.domains.flatten HeadOldOldBB.state4.data.current.flatten=true ∧
    noGate 5 HeadOldOldBB.state5.data.domains.flatten HeadOldOldBB.state5.data.current.flatten=true ∧
    noGate 6 HeadOldOldBB.state6.data.domains.flatten HeadOldOldBB.state6.data.current.flatten=true := by decide +kernel
theorem ordinary_OldBB_still_stops_with_the_expected_observation :
    UniformCampaign.stopped 5 HeadOldOldBB.state5=true ∧
    HeadOldOldBB.state5.report=HeadOldOldBB.c.expected := HeadOldOldBB.natural_stop_and_expected_observation
theorem ordinary_OldMethod_no_current_reply_can_be_pruned :
    noGate 1 HeadOldOldMethod.state1.data.domains.flatten HeadOldOldMethod.state1.data.current.flatten=true ∧
    noGate 2 HeadOldOldMethod.state2.data.domains.flatten HeadOldOldMethod.state2.data.current.flatten=true ∧
    noGate 3 HeadOldOldMethod.state3.data.domains.flatten HeadOldOldMethod.state3.data.current.flatten=true ∧
    noGate 4 HeadOldOldMethod.state4.data.domains.flatten HeadOldOldMethod.state4.data.current.flatten=true ∧
    noGate 5 HeadOldOldMethod.state5.data.domains.flatten HeadOldOldMethod.state5.data.current.flatten=true ∧
    noGate 6 HeadOldOldMethod.state6.data.domains.flatten HeadOldOldMethod.state6.data.current.flatten=true := by decide +kernel
theorem ordinary_OldMethod_still_stops_with_the_expected_observation :
    UniformCampaign.stopped 5 HeadOldOldMethod.state5=true ∧
    HeadOldOldMethod.state5.report=HeadOldOldMethod.c.expected := HeadOldOldMethod.natural_stop_and_expected_observation
theorem ordinary_OrdinaryTwo_no_current_reply_can_be_pruned :
    noGate 1 HeadOldOrdinaryTwo.state1.data.domains.flatten HeadOldOrdinaryTwo.state1.data.current.flatten=true ∧
    noGate 2 HeadOldOrdinaryTwo.state2.data.domains.flatten HeadOldOrdinaryTwo.state2.data.current.flatten=true ∧
    noGate 3 HeadOldOrdinaryTwo.state3.data.domains.flatten HeadOldOrdinaryTwo.state3.data.current.flatten=true ∧
    noGate 4 HeadOldOrdinaryTwo.state4.data.domains.flatten HeadOldOrdinaryTwo.state4.data.current.flatten=true := by decide +kernel
theorem ordinary_OrdinaryTwo_still_stops_with_the_expected_observation :
    UniformCampaign.stopped 3 HeadOldOrdinaryTwo.state3=true ∧
    HeadOldOrdinaryTwo.state3.report=HeadOldOrdinaryTwo.c.expected := HeadOldOrdinaryTwo.natural_stop_and_expected_observation
theorem ordinary_Overwrite_no_current_reply_can_be_pruned :
    noGate 1 HeadOldOverwrite.state1.data.domains.flatten HeadOldOverwrite.state1.data.current.flatten=true ∧
    noGate 2 HeadOldOverwrite.state2.data.domains.flatten HeadOldOverwrite.state2.data.current.flatten=true ∧
    noGate 3 HeadOldOverwrite.state3.data.domains.flatten HeadOldOverwrite.state3.data.current.flatten=true ∧
    noGate 4 HeadOldOverwrite.state4.data.domains.flatten HeadOldOverwrite.state4.data.current.flatten=true ∧
    noGate 5 HeadOldOverwrite.state5.data.domains.flatten HeadOldOverwrite.state5.data.current.flatten=true ∧
    noGate 6 HeadOldOverwrite.state6.data.domains.flatten HeadOldOverwrite.state6.data.current.flatten=true ∧
    noGate 7 HeadOldOverwrite.state7.data.domains.flatten HeadOldOverwrite.state7.data.current.flatten=true ∧
    noGate 8 HeadOldOverwrite.state8.data.domains.flatten HeadOldOverwrite.state8.data.current.flatten=true ∧
    noGate 9 HeadOldOverwrite.state9.data.domains.flatten HeadOldOverwrite.state9.data.current.flatten=true ∧
    noGate 10 HeadOldOverwrite.state10.data.domains.flatten HeadOldOverwrite.state10.data.current.flatten=true := by decide +kernel
theorem ordinary_Overwrite_still_stops_with_the_expected_observation :
    UniformCampaign.stopped 9 HeadOldOverwrite.state9=true ∧
    HeadOldOverwrite.state9.report=HeadOldOverwrite.c.expected := HeadOldOverwrite.natural_stop_and_expected_observation
theorem ordinary_Postfix_no_current_reply_can_be_pruned :
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
    noGate 14 HeadOldPostfix.state14.data.domains.flatten HeadOldPostfix.state14.data.current.flatten=true := by decide +kernel
theorem ordinary_Postfix_still_stops_with_the_expected_observation :
    UniformCampaign.stopped 13 HeadOldPostfix.state13=true ∧
    HeadOldPostfix.state13.report=HeadOldPostfix.c.expected := HeadOldPostfix.natural_stop_and_expected_observation
theorem ordinary_Prefix_no_current_reply_can_be_pruned :
    noGate 1 HeadOldPrefix.state1.data.domains.flatten HeadOldPrefix.state1.data.current.flatten=true ∧
    noGate 2 HeadOldPrefix.state2.data.domains.flatten HeadOldPrefix.state2.data.current.flatten=true ∧
    noGate 3 HeadOldPrefix.state3.data.domains.flatten HeadOldPrefix.state3.data.current.flatten=true ∧
    noGate 4 HeadOldPrefix.state4.data.domains.flatten HeadOldPrefix.state4.data.current.flatten=true ∧
    noGate 5 HeadOldPrefix.state5.data.domains.flatten HeadOldPrefix.state5.data.current.flatten=true ∧
    noGate 6 HeadOldPrefix.state6.data.domains.flatten HeadOldPrefix.state6.data.current.flatten=true ∧
    noGate 7 HeadOldPrefix.state7.data.domains.flatten HeadOldPrefix.state7.data.current.flatten=true ∧
    noGate 8 HeadOldPrefix.state8.data.domains.flatten HeadOldPrefix.state8.data.current.flatten=true := by decide +kernel
theorem ordinary_Prefix_still_stops_with_the_expected_observation :
    UniformCampaign.stopped 7 HeadOldPrefix.state7=true ∧
    HeadOldPrefix.state7.report=HeadOldPrefix.c.expected := HeadOldPrefix.natural_stop_and_expected_observation
theorem ordinary_PrefixPostfix_no_current_reply_can_be_pruned :
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
    noGate 12 HeadOldPrefixPostfix.state12.data.domains.flatten HeadOldPrefixPostfix.state12.data.current.flatten=true := by decide +kernel
theorem ordinary_PrefixPostfix_still_stops_with_the_expected_observation :
    UniformCampaign.stopped 11 HeadOldPrefixPostfix.state11=true ∧
    HeadOldPrefixPostfix.state11.report=HeadOldPrefixPostfix.c.expected := HeadOldPrefixPostfix.natural_stop_and_expected_observation
theorem ordinary_RoundTrip_no_current_reply_can_be_pruned :
    noGate 1 HeadOldRoundTrip.state1.data.domains.flatten HeadOldRoundTrip.state1.data.current.flatten=true ∧
    noGate 2 HeadOldRoundTrip.state2.data.domains.flatten HeadOldRoundTrip.state2.data.current.flatten=true ∧
    noGate 3 HeadOldRoundTrip.state3.data.domains.flatten HeadOldRoundTrip.state3.data.current.flatten=true ∧
    noGate 4 HeadOldRoundTrip.state4.data.domains.flatten HeadOldRoundTrip.state4.data.current.flatten=true ∧
    noGate 5 HeadOldRoundTrip.state5.data.domains.flatten HeadOldRoundTrip.state5.data.current.flatten=true ∧
    noGate 6 HeadOldRoundTrip.state6.data.domains.flatten HeadOldRoundTrip.state6.data.current.flatten=true ∧
    noGate 7 HeadOldRoundTrip.state7.data.domains.flatten HeadOldRoundTrip.state7.data.current.flatten=true ∧
    noGate 8 HeadOldRoundTrip.state8.data.domains.flatten HeadOldRoundTrip.state8.data.current.flatten=true ∧
    noGate 9 HeadOldRoundTrip.state9.data.domains.flatten HeadOldRoundTrip.state9.data.current.flatten=true ∧
    noGate 10 HeadOldRoundTrip.state10.data.domains.flatten HeadOldRoundTrip.state10.data.current.flatten=true := by decide +kernel
theorem ordinary_RoundTrip_still_stops_with_the_expected_observation :
    UniformCampaign.stopped 9 HeadOldRoundTrip.state9=true ∧
    HeadOldRoundTrip.state9.report=HeadOldRoundTrip.c.expected := HeadOldRoundTrip.natural_stop_and_expected_observation
theorem HeadDeepCold_no_current_reply_can_be_pruned :
    noGate 1 HeadDeepCold.s1.data.domains HeadDeepCold.s1.data.raw=true ∧
    noGate 2 HeadDeepCold.s2.data.domains HeadDeepCold.s2.data.raw=true ∧
    noGate 3 HeadDeepCold.s3.data.domains HeadDeepCold.s3.data.raw=true ∧
    noGate 4 HeadDeepCold.s4.data.domains HeadDeepCold.s4.data.raw=true ∧
    noGate 5 HeadDeepCold.s5.data.domains HeadDeepCold.s5.data.raw=true ∧
    noGate 6 HeadDeepCold.s6.data.domains HeadDeepCold.s6.data.raw=true := by decide +kernel
theorem HeadShallowCold_no_current_reply_can_be_pruned :
    noGate 1 HeadShallowCold.s1.data.domains HeadShallowCold.s1.data.raw=true ∧
    noGate 2 HeadShallowCold.s2.data.domains HeadShallowCold.s2.data.raw=true ∧
    noGate 3 HeadShallowCold.s3.data.domains HeadShallowCold.s3.data.raw=true ∧
    noGate 4 HeadShallowCold.s4.data.domains HeadShallowCold.s4.data.raw=true ∧
    noGate 5 HeadShallowCold.s5.data.domains HeadShallowCold.s5.data.raw=true ∧
    noGate 6 HeadShallowCold.s6.data.domains HeadShallowCold.s6.data.raw=true := by decide +kernel
theorem HeadOldAlternating_no_current_reply_can_be_pruned :
    noGate 1 HeadOldAlternating.state1.data.domains HeadOldAlternating.state1.data.raw=true ∧
    noGate 2 HeadOldAlternating.state2.data.domains HeadOldAlternating.state2.data.raw=true ∧
    noGate 3 HeadOldAlternating.state3.data.domains HeadOldAlternating.state3.data.raw=true ∧
    noGate 4 HeadOldAlternating.state4.data.domains HeadOldAlternating.state4.data.raw=true ∧
    noGate 5 HeadOldAlternating.state5.data.domains HeadOldAlternating.state5.data.raw=true ∧
    noGate 6 HeadOldAlternating.state6.data.domains HeadOldAlternating.state6.data.raw=true := by decide +kernel
theorem strict_MUST_actuals_never_use_the_new_policy (run : Nat) (ready : List Ap)
    (e : CompletePoint.Edge) :
    CompletePoint.suppress run ready ProvisionalMustCycle.rootActual e=false ∧
    CompletePoint.suppress run ready ProvisionalMustCycle.fieldActual e=false ∧
    CompletePoint.suppress run ready ProvisionalUniformCycle.rootActual e=false ∧
    CompletePoint.suppress run ready ProvisionalUniformCycle.fieldActual e=false ∧
    CompletePoint.suppress run ready DifferentUniformReply.rootActual e=false ∧
    CompletePoint.suppress run ready DifferentUniformReply.fieldActual e=false := by
  repeat' constructor
  all_goals apply CompleteService.non_exact_actual_is_unchanged
  all_goals decide +kernel

theorem exact_replay_retains_both_findings :
    (HeadStrictExact.history 5).rows=[] ∧
    (HeadStrictExact.history 5).rootDemand=false ∧
    (HeadStrictExact.history 5).reports=[0,1] := HeadStrictExact.stop_run5_and_both_observations

theorem uniform_replay_retains_both_findings :
    (HeadStrictUniform.history 5).rows=[] ∧
    (HeadStrictUniform.history 5).rootDemand=false ∧
    (HeadStrictUniform.history 5).reports=[0,1] := HeadStrictUniform.stop_run5_and_both_observations

/-- This also checks unreturned/compacted queries: every prepared key in
    these old field-flow references is abstract, so it cannot certify a
    concrete point. No new completion can be obtained from a retired row. -/
theorem all_old_field_flow_prepared_keys_are_ineligible_for_completion :
    ((List.range HeadOldDouble.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 3 2 false (HeadOldDouble.state2.rows[owner]!)
         (OverwriteReplay.views false (HeadOldDouble.state2.saved[owner]!)) (HeadOldDouble.state3.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldDouble.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 5 4 false (HeadOldDouble.state4.rows[owner]!)
         (OverwriteReplay.views false (HeadOldDouble.state4.saved[owner]!)) (HeadOldDouble.state5.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldDouble.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 7 6 false (HeadOldDouble.state6.rows[owner]!)
         (OverwriteReplay.views false (HeadOldDouble.state6.saved[owner]!)) (HeadOldDouble.state7.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldDouble.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 9 8 false (HeadOldDouble.state8.rows[owner]!)
         (OverwriteReplay.views false (HeadOldDouble.state8.saved[owner]!)) (HeadOldDouble.state9.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldDouble.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 11 10 false (HeadOldDouble.state10.rows[owner]!)
         (OverwriteReplay.views false (HeadOldDouble.state10.saved[owner]!)) (HeadOldDouble.state11.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldDouble.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 13 12 false (HeadOldDouble.state12.rows[owner]!)
         (OverwriteReplay.views false (HeadOldDouble.state12.saved[owner]!)) (HeadOldDouble.state13.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldDouble.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 15 14 false (HeadOldDouble.state14.rows[owner]!)
         (OverwriteReplay.views false (HeadOldDouble.state14.saved[owner]!)) (HeadOldDouble.state15.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldGrowth.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 3 2 false (HeadOldGrowth.state2.rows[owner]!)
         (OverwriteReplay.views false (HeadOldGrowth.state2.saved[owner]!)) (HeadOldGrowth.state3.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldGrowth.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 5 4 false (HeadOldGrowth.state4.rows[owner]!)
         (OverwriteReplay.views false (HeadOldGrowth.state4.saved[owner]!)) (HeadOldGrowth.state5.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldGrowth.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 7 6 false (HeadOldGrowth.state6.rows[owner]!)
         (OverwriteReplay.views false (HeadOldGrowth.state6.saved[owner]!)) (HeadOldGrowth.state7.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldLongReader.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 3 2 false (HeadOldLongReader.state2.rows[owner]!)
         (OverwriteReplay.views false (HeadOldLongReader.state2.saved[owner]!)) (HeadOldLongReader.state3.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldLongReader.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 5 4 false (HeadOldLongReader.state4.rows[owner]!)
         (OverwriteReplay.views false (HeadOldLongReader.state4.saved[owner]!)) (HeadOldLongReader.state5.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldNested.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 3 2 false (HeadOldNested.state2.rows[owner]!)
         (OverwriteReplay.views false (HeadOldNested.state2.saved[owner]!)) (HeadOldNested.state3.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldNested.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 5 4 false (HeadOldNested.state4.rows[owner]!)
         (OverwriteReplay.views false (HeadOldNested.state4.saved[owner]!)) (HeadOldNested.state5.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldNested.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 7 6 false (HeadOldNested.state6.rows[owner]!)
         (OverwriteReplay.views false (HeadOldNested.state6.saved[owner]!)) (HeadOldNested.state7.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldNested.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 9 8 false (HeadOldNested.state8.rows[owner]!)
         (OverwriteReplay.views false (HeadOldNested.state8.saved[owner]!)) (HeadOldNested.state9.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldNestedDeep.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 3 2 false (HeadOldNestedDeep.state2.rows[owner]!)
         (OverwriteReplay.views false (HeadOldNestedDeep.state2.saved[owner]!)) (HeadOldNestedDeep.state3.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldNestedDeep.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 5 4 false (HeadOldNestedDeep.state4.rows[owner]!)
         (OverwriteReplay.views false (HeadOldNestedDeep.state4.saved[owner]!)) (HeadOldNestedDeep.state5.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldNestedExact.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 3 2 false (HeadOldNestedExact.state2.rows[owner]!)
         (OverwriteReplay.views false (HeadOldNestedExact.state2.saved[owner]!)) (HeadOldNestedExact.state3.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldNestedLarger.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 3 2 false (HeadOldNestedLarger.state2.rows[owner]!)
         (OverwriteReplay.views false (HeadOldNestedLarger.state2.saved[owner]!)) (HeadOldNestedLarger.state3.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldNestedLarger.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 5 4 false (HeadOldNestedLarger.state4.rows[owner]!)
         (OverwriteReplay.views false (HeadOldNestedLarger.state4.saved[owner]!)) (HeadOldNestedLarger.state5.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldNestedLarger.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 7 6 false (HeadOldNestedLarger.state6.rows[owner]!)
         (OverwriteReplay.views false (HeadOldNestedLarger.state6.saved[owner]!)) (HeadOldNestedLarger.state7.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldNestedLarger.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 9 8 false (HeadOldNestedLarger.state8.rows[owner]!)
         (OverwriteReplay.views false (HeadOldNestedLarger.state8.saved[owner]!)) (HeadOldNestedLarger.state9.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldNestedLarger.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 11 10 false (HeadOldNestedLarger.state10.rows[owner]!)
         (OverwriteReplay.views false (HeadOldNestedLarger.state10.saved[owner]!)) (HeadOldNestedLarger.state11.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldNestedNegative.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 3 2 false (HeadOldNestedNegative.state2.rows[owner]!)
         (OverwriteReplay.views false (HeadOldNestedNegative.state2.saved[owner]!)) (HeadOldNestedNegative.state3.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldNestedPositive.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 3 2 false (HeadOldNestedPositive.state2.rows[owner]!)
         (OverwriteReplay.views false (HeadOldNestedPositive.state2.saved[owner]!)) (HeadOldNestedPositive.state3.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldNestedSurvivor.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 3 2 false (HeadOldNestedSurvivor.state2.rows[owner]!)
         (OverwriteReplay.views false (HeadOldNestedSurvivor.state2.saved[owner]!)) (HeadOldNestedSurvivor.state3.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldNestedSurvivor.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 5 4 false (HeadOldNestedSurvivor.state4.rows[owner]!)
         (OverwriteReplay.views false (HeadOldNestedSurvivor.state4.saved[owner]!)) (HeadOldNestedSurvivor.state5.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldOldBB.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 3 2 false (HeadOldOldBB.state2.rows[owner]!)
         (OverwriteReplay.views false (HeadOldOldBB.state2.saved[owner]!)) (HeadOldOldBB.state3.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldOldBB.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 5 4 false (HeadOldOldBB.state4.rows[owner]!)
         (OverwriteReplay.views false (HeadOldOldBB.state4.saved[owner]!)) (HeadOldOldBB.state5.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldOldMethod.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 3 2 false (HeadOldOldMethod.state2.rows[owner]!)
         (OverwriteReplay.views false (HeadOldOldMethod.state2.saved[owner]!)) (HeadOldOldMethod.state3.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldOldMethod.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 5 4 false (HeadOldOldMethod.state4.rows[owner]!)
         (OverwriteReplay.views false (HeadOldOldMethod.state4.saved[owner]!)) (HeadOldOldMethod.state5.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldOrdinaryTwo.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 3 2 false (HeadOldOrdinaryTwo.state2.rows[owner]!)
         (OverwriteReplay.views false (HeadOldOrdinaryTwo.state2.saved[owner]!)) (HeadOldOrdinaryTwo.state3.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldOverwrite.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 3 2 false (HeadOldOverwrite.state2.rows[owner]!)
         (OverwriteReplay.views false (HeadOldOverwrite.state2.saved[owner]!)) (HeadOldOverwrite.state3.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldOverwrite.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 5 4 false (HeadOldOverwrite.state4.rows[owner]!)
         (OverwriteReplay.views false (HeadOldOverwrite.state4.saved[owner]!)) (HeadOldOverwrite.state5.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldOverwrite.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 7 6 false (HeadOldOverwrite.state6.rows[owner]!)
         (OverwriteReplay.views false (HeadOldOverwrite.state6.saved[owner]!)) (HeadOldOverwrite.state7.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldOverwrite.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 9 8 false (HeadOldOverwrite.state8.rows[owner]!)
         (OverwriteReplay.views false (HeadOldOverwrite.state8.saved[owner]!)) (HeadOldOverwrite.state9.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldPostfix.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 3 2 false (HeadOldPostfix.state2.rows[owner]!)
         (OverwriteReplay.views false (HeadOldPostfix.state2.saved[owner]!)) (HeadOldPostfix.state3.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldPostfix.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 5 4 false (HeadOldPostfix.state4.rows[owner]!)
         (OverwriteReplay.views false (HeadOldPostfix.state4.saved[owner]!)) (HeadOldPostfix.state5.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldPostfix.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 7 6 false (HeadOldPostfix.state6.rows[owner]!)
         (OverwriteReplay.views false (HeadOldPostfix.state6.saved[owner]!)) (HeadOldPostfix.state7.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldPostfix.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 9 8 false (HeadOldPostfix.state8.rows[owner]!)
         (OverwriteReplay.views false (HeadOldPostfix.state8.saved[owner]!)) (HeadOldPostfix.state9.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldPostfix.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 11 10 false (HeadOldPostfix.state10.rows[owner]!)
         (OverwriteReplay.views false (HeadOldPostfix.state10.saved[owner]!)) (HeadOldPostfix.state11.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldPostfix.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 13 12 false (HeadOldPostfix.state12.rows[owner]!)
         (OverwriteReplay.views false (HeadOldPostfix.state12.saved[owner]!)) (HeadOldPostfix.state13.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldPrefix.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 3 2 false (HeadOldPrefix.state2.rows[owner]!)
         (OverwriteReplay.views false (HeadOldPrefix.state2.saved[owner]!)) (HeadOldPrefix.state3.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldPrefix.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 5 4 false (HeadOldPrefix.state4.rows[owner]!)
         (OverwriteReplay.views false (HeadOldPrefix.state4.saved[owner]!)) (HeadOldPrefix.state5.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldPrefix.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 7 6 false (HeadOldPrefix.state6.rows[owner]!)
         (OverwriteReplay.views false (HeadOldPrefix.state6.saved[owner]!)) (HeadOldPrefix.state7.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldPrefixPostfix.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 3 2 false (HeadOldPrefixPostfix.state2.rows[owner]!)
         (OverwriteReplay.views false (HeadOldPrefixPostfix.state2.saved[owner]!)) (HeadOldPrefixPostfix.state3.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldPrefixPostfix.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 5 4 false (HeadOldPrefixPostfix.state4.rows[owner]!)
         (OverwriteReplay.views false (HeadOldPrefixPostfix.state4.saved[owner]!)) (HeadOldPrefixPostfix.state5.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldPrefixPostfix.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 7 6 false (HeadOldPrefixPostfix.state6.rows[owner]!)
         (OverwriteReplay.views false (HeadOldPrefixPostfix.state6.saved[owner]!)) (HeadOldPrefixPostfix.state7.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldPrefixPostfix.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 9 8 false (HeadOldPrefixPostfix.state8.rows[owner]!)
         (OverwriteReplay.views false (HeadOldPrefixPostfix.state8.saved[owner]!)) (HeadOldPrefixPostfix.state9.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldPrefixPostfix.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 11 10 false (HeadOldPrefixPostfix.state10.rows[owner]!)
         (OverwriteReplay.views false (HeadOldPrefixPostfix.state10.saved[owner]!)) (HeadOldPrefixPostfix.state11.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldRoundTrip.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 3 2 false (HeadOldRoundTrip.state2.rows[owner]!)
         (OverwriteReplay.views false (HeadOldRoundTrip.state2.saved[owner]!)) (HeadOldRoundTrip.state3.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldRoundTrip.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 5 4 false (HeadOldRoundTrip.state4.rows[owner]!)
         (OverwriteReplay.views false (HeadOldRoundTrip.state4.saved[owner]!)) (HeadOldRoundTrip.state5.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldRoundTrip.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 7 6 false (HeadOldRoundTrip.state6.rows[owner]!)
         (OverwriteReplay.views false (HeadOldRoundTrip.state6.saved[owner]!)) (HeadOldRoundTrip.state7.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true ∧
    ((List.range HeadOldRoundTrip.c.methods.length).flatMap fun owner =>
       HeadNeutralPlan.cells 9 8 false (HeadOldRoundTrip.state8.rows[owner]!)
         (OverwriteReplay.views false (HeadOldRoundTrip.state8.saved[owner]!)) (HeadOldRoundTrip.state9.data.domains[owner]!)).all
       (fun cell => cell.2.all (fun q => q.1.ap.mark.isNone))=true := by decide +kernel

end CompleteRegression

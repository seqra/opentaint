import ClosedExactSupport
import ClosedUniformSupport
import PointCertificateDouble
import PointCertificateGrowth
import PointCertificateLongReader
import PointCertificateNested
import PointCertificateNestedDeep
import PointCertificateNestedExact
import PointCertificateNestedLarger
import PointCertificateNestedNegative
import PointCertificateNestedPositive
import PointCertificateNestedSurvivor
import PointCertificateOldBB
import PointCertificateOldMethod
import PointCertificateOrdinaryTwo
import PointCertificateOverwrite
import PointCertificatePostfix
import PointCertificatePrefix
import PointCertificatePrefixPostfix
import PointCertificateRoundTrip
import MarkedClosure

namespace DefiniteSupportPrior
open NonEmptyPolicy NonEmptyRestriction
set_option maxRecDepth 16384
set_option maxHeartbeats 80000000

def foldedOffers (xs : List Offered) : List Offered :=
  (DefiniteReplySupport.foldValues (xs.map (fun x => (⟨x.ap,x.demand,false⟩ : Value)))).map
    (fun x => (⟨x.ap,x.demand⟩ : Offered))

theorem PointDouble_every_cold_packet_unchanged :
    ([PointDouble.state1,PointDouble.state2,PointDouble.state3,PointDouble.state4,PointDouble.state5,PointDouble.state6,PointDouble.state7,PointDouble.state8,PointDouble.state9,PointDouble.state10,PointDouble.state11,PointDouble.state12,PointDouble.state13,PointDouble.state14,PointDouble.state15]).all (fun st =>
      st.offers.all (fun xs => decide (foldedOffers xs = xs))) = true := by decide

theorem PointGrowth_every_cold_packet_unchanged :
    ([PointGrowth.state1,PointGrowth.state2,PointGrowth.state3,PointGrowth.state4,PointGrowth.state5,PointGrowth.state6,PointGrowth.state7,PointGrowth.state8,PointGrowth.state9,PointGrowth.state10,PointGrowth.state11]).all (fun st =>
      st.offers.all (fun xs => decide (foldedOffers xs = xs))) = true := by decide

theorem PointLongReader_every_cold_packet_unchanged :
    ([PointLongReader.state1,PointLongReader.state2,PointLongReader.state3,PointLongReader.state4,PointLongReader.state5]).all (fun st =>
      st.offers.all (fun xs => decide (foldedOffers xs = xs))) = true := by decide

theorem PointNested_every_cold_packet_unchanged :
    ([PointNested.state1,PointNested.state2,PointNested.state3,PointNested.state4,PointNested.state5,PointNested.state6,PointNested.state7,PointNested.state8,PointNested.state9]).all (fun st =>
      st.offers.all (fun xs => decide (foldedOffers xs = xs))) = true := by decide

theorem PointNestedDeep_every_cold_packet_unchanged :
    ([PointNestedDeep.state1,PointNestedDeep.state2,PointNestedDeep.state3,PointNestedDeep.state4,PointNestedDeep.state5]).all (fun st =>
      st.offers.all (fun xs => decide (foldedOffers xs = xs))) = true := by decide

theorem PointNestedExact_every_cold_packet_unchanged :
    ([PointNestedExact.state1,PointNestedExact.state2,PointNestedExact.state3]).all (fun st =>
      st.offers.all (fun xs => decide (foldedOffers xs = xs))) = true := by decide

theorem PointNestedLarger_every_cold_packet_unchanged :
    ([PointNestedLarger.state1,PointNestedLarger.state2,PointNestedLarger.state3,PointNestedLarger.state4,PointNestedLarger.state5,PointNestedLarger.state6,PointNestedLarger.state7,PointNestedLarger.state8,PointNestedLarger.state9,PointNestedLarger.state10,PointNestedLarger.state11]).all (fun st =>
      st.offers.all (fun xs => decide (foldedOffers xs = xs))) = true := by decide

theorem PointNestedNegative_every_cold_packet_unchanged :
    ([PointNestedNegative.state1,PointNestedNegative.state2,PointNestedNegative.state3]).all (fun st =>
      st.offers.all (fun xs => decide (foldedOffers xs = xs))) = true := by decide

theorem PointNestedPositive_every_cold_packet_unchanged :
    ([PointNestedPositive.state1,PointNestedPositive.state2,PointNestedPositive.state3]).all (fun st =>
      st.offers.all (fun xs => decide (foldedOffers xs = xs))) = true := by decide

theorem PointNestedSurvivor_every_cold_packet_unchanged :
    ([PointNestedSurvivor.state1,PointNestedSurvivor.state2,PointNestedSurvivor.state3,PointNestedSurvivor.state4,PointNestedSurvivor.state5]).all (fun st =>
      st.offers.all (fun xs => decide (foldedOffers xs = xs))) = true := by decide

theorem PointOldBB_every_cold_packet_unchanged :
    ([PointOldBB.state1,PointOldBB.state2,PointOldBB.state3,PointOldBB.state4,PointOldBB.state5]).all (fun st =>
      st.offers.all (fun xs => decide (foldedOffers xs = xs))) = true := by decide

theorem PointOldMethod_every_cold_packet_unchanged :
    ([PointOldMethod.state1,PointOldMethod.state2,PointOldMethod.state3,PointOldMethod.state4,PointOldMethod.state5]).all (fun st =>
      st.offers.all (fun xs => decide (foldedOffers xs = xs))) = true := by decide

theorem PointOrdinaryTwo_every_cold_packet_unchanged :
    ([PointOrdinaryTwo.state1,PointOrdinaryTwo.state2,PointOrdinaryTwo.state3]).all (fun st =>
      st.offers.all (fun xs => decide (foldedOffers xs = xs))) = true := by decide

theorem PointOverwrite_every_cold_packet_unchanged :
    ([PointOverwrite.state1,PointOverwrite.state2,PointOverwrite.state3,PointOverwrite.state4,PointOverwrite.state5,PointOverwrite.state6,PointOverwrite.state7,PointOverwrite.state8,PointOverwrite.state9]).all (fun st =>
      st.offers.all (fun xs => decide (foldedOffers xs = xs))) = true := by decide

theorem PointPostfix_every_cold_packet_unchanged :
    ([PointPostfix.state1,PointPostfix.state2,PointPostfix.state3,PointPostfix.state4,PointPostfix.state5,PointPostfix.state6,PointPostfix.state7,PointPostfix.state8,PointPostfix.state9,PointPostfix.state10,PointPostfix.state11,PointPostfix.state12,PointPostfix.state13]).all (fun st =>
      st.offers.all (fun xs => decide (foldedOffers xs = xs))) = true := by decide

theorem PointPrefix_every_cold_packet_unchanged :
    ([PointPrefix.state1,PointPrefix.state2,PointPrefix.state3,PointPrefix.state4,PointPrefix.state5,PointPrefix.state6,PointPrefix.state7,PointPrefix.state8,PointPrefix.state9]).all (fun st =>
      st.offers.all (fun xs => decide (foldedOffers xs = xs))) = true := by decide

theorem PointPrefixPostfix_every_cold_packet_unchanged :
    ([PointPrefixPostfix.state1,PointPrefixPostfix.state2,PointPrefixPostfix.state3,PointPrefixPostfix.state4,PointPrefixPostfix.state5,PointPrefixPostfix.state6,PointPrefixPostfix.state7,PointPrefixPostfix.state8,PointPrefixPostfix.state9,PointPrefixPostfix.state10,PointPrefixPostfix.state11]).all (fun st =>
      st.offers.all (fun xs => decide (foldedOffers xs = xs))) = true := by decide

theorem PointRoundTrip_every_cold_packet_unchanged :
    ([PointRoundTrip.state1,PointRoundTrip.state2,PointRoundTrip.state3,PointRoundTrip.state4,PointRoundTrip.state5,PointRoundTrip.state6,PointRoundTrip.state7,PointRoundTrip.state8,PointRoundTrip.state9]).all (fun st =>
      st.offers.all (fun xs => decide (foldedOffers xs = xs))) = true := by decide

theorem protected_uniform_complete_replies_unchanged :
    DefiniteReplySupport.foldValues SameLaneMarkedClosure.firstReplies = SameLaneMarkedClosure.firstReplies ∧
    DefiniteReplySupport.foldValues SameLaneMarkedClosure.secondReplies = SameLaneMarkedClosure.secondReplies := by decide

end DefiniteSupportPrior

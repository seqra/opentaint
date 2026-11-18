import PacketOrder

/- The enlarged acceptance set retains each old case. Older checkers are
   dependencies; these checks also apply the new predicate to their packets.
   This does not replace old proofs by testing only the new witness. -/
namespace SameLaneAcceptance
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle
open BoundedRefinementPipeline BoundedLocalRouting BoundedOrdinaryCycle
open NormalUniformNE UniformNEClosure UniformNERegressions UniformNEVirtual
open UniformRootCleanerPolicy SameLaneMarkedClosure

theorem the_old_method_and_new_neutral_complete_packets_are_unchanged :
    SameLaneUniform.compact true oldPacket = NormalUniformNE.compact true oldPacket ∧
    SameLaneUniform.compact true newPacket = NormalUniformNE.compact true newPacket := by decide

theorem the_old_bb_frontier_and_wrapper_finding_routes_are_unchanged :
    incoming (SameLaneUniform.compact true bbPacket) = [] ∧
    incoming readBB = [] ∧
    SameLaneUniform.compact true wrapperPacket = wrapperPacket := by decide

theorem the_selected_cleaner_survivor_and_standalone_termination_are_unchanged :
    SameLaneUniform.compact true cleanerForwardPacket = cleanerForwardPacket ∧
    incoming cleanerForwardPacket = [] ∧
    nextDemand newForward = [] := by decide

theorem older_warm_views_still_remove_their_complete_cut_packet :
    (warmCandidates.filter fun e => !(warmViews.any fun n => SameLaneUniform.covers n e)) = [] := by decide

theorem neither_old_nor_new_case_needs_a_nonempty_forward_frontier :
    handoff oldBasis = [] ∧ handoff newBasis = [] ∧
    incoming SameLaneMarkedClosure.closedPacket = [] := by decide

theorem old_and_new_confirmed_findings_remain_normal :
    confirmed oldSecond = true ∧ confirmed newSecond = true ∧
    SameLaneMarkedClosure.secondReplies.any (fun c =>
      c.ap.mark == some t && c.ap.tail == .must && !c.demand) = true := by decide

end SameLaneAcceptance

#print axioms SameLaneAcceptance.the_old_method_and_new_neutral_complete_packets_are_unchanged
#print axioms SameLaneAcceptance.the_old_bb_frontier_and_wrapper_finding_routes_are_unchanged
#print axioms SameLaneAcceptance.the_selected_cleaner_survivor_and_standalone_termination_are_unchanged
#print axioms SameLaneAcceptance.older_warm_views_still_remove_their_complete_cut_packet
#print axioms SameLaneAcceptance.neither_old_nor_new_case_needs_a_nonempty_forward_frontier
#print axioms SameLaneAcceptance.old_and_new_confirmed_findings_remain_normal

import UniformSafety
import RootCleanerPolicy
import MarkedClosure

namespace UniformProtected
open NonEmptyPolicy NonEmptyRestriction
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem protected_call_packets_keep_the_complete_normal_basis :
    UniformActual.foldValues false [] SameLaneMarkedClosure.firstReplies = SameLaneMarkedClosure.firstReplies ∧
    UniformActual.foldValues false [] SameLaneMarkedClosure.secondReplies = SameLaneMarkedClosure.secondReplies := by decide

theorem the_closed_protected_frontier_still_has_no_demand :
    SameLaneMarkedClosure.incoming SameLaneMarkedClosure.closedPacket = [] ∧
    (UniformActual.foldValues false [] SameLaneMarkedClosure.secondReplies).any Value.demand = false := by decide

theorem the_selected_cleaner_image_is_unchanged :
    UniformActual.foldValues false []
      ((UniformRootCleanerPolicy.revisedCleanRoot UniformRootCleanerCycle.sourceValue).toList) =
      (UniformRootCleanerPolicy.revisedCleanRoot UniformRootCleanerCycle.sourceValue).toList := by decide

theorem the_selected_cleaner_still_finishes_at_run1 :
    UniformRootCleanerPolicy.newForward = [.normal UniformRootCleanerPolicy.sinkId] ∧
    UniformRootCleanerPolicy.nextDemand UniformRootCleanerPolicy.newForward = [] := by decide

end UniformProtected

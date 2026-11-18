import HeadSafety
import UniformProtected
namespace HeadControls
open NonEmptyPolicy NonEmptyRestriction
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem the_existing_protected_basis_and_packet_laws_remain :
    UniformActual.foldValues false [] SameLaneMarkedClosure.firstReplies = SameLaneMarkedClosure.firstReplies ∧
    UniformActual.foldValues false [] SameLaneMarkedClosure.secondReplies = SameLaneMarkedClosure.secondReplies := by
  exact UniformProtected.protected_call_packets_keep_the_complete_normal_basis

theorem the_protected_frontier_still_closes_run3 :
    SameLaneMarkedClosure.incoming SameLaneMarkedClosure.closedPacket = [] ∧
    (UniformActual.foldValues false [] SameLaneMarkedClosure.secondReplies).any Value.demand = false := by
  exact UniformProtected.the_closed_protected_frontier_still_has_no_demand

theorem the_selected_cleaner_image_is_not_changed :
    UniformActual.foldValues false []
      ((UniformRootCleanerPolicy.revisedCleanRoot UniformRootCleanerCycle.sourceValue).toList) =
      (UniformRootCleanerPolicy.revisedCleanRoot UniformRootCleanerCycle.sourceValue).toList := by
  exact UniformProtected.the_selected_cleaner_image_is_unchanged

theorem selected_cleaner_still_closes_run1 :
    UniformRootCleanerPolicy.newForward = [.normal UniformRootCleanerPolicy.sinkId] ∧
    UniformRootCleanerPolicy.nextDemand UniformRootCleanerPolicy.newForward = [] := by
  exact UniformProtected.the_selected_cleaner_still_finishes_at_run1

/-- C5 still restricts every admitted result, including NORMAL results,
    with its own paired-output-relative bound. -/
theorem C5_output_bound_is_unchanged
    (run limit : Nat) (back : Bool) (as : List Offered) (raw : Ap)
    (c : Value) (row : Row) (result : Ap × Value)
    (accepted : HeadPolicy.restrictOne run limit back as raw c row = some result) :
    result.2.ap.path.length ≤ min limit (row.exit.path.length+1) := by
  unfold HeadPolicy.restrictOne at accepted
  split at accepted
  · dsimp only at accepted
    cases selected : intersectExit (normalize raw c).2 row.exit with
    | none => simp [selected] at accepted
    | some v =>
      simp only [selected] at accepted
      have same := Option.some.inj accepted
      rw [← same]
      rw [(normalize_preserves_paths_marks_layers_protection
        (normalize raw c).1 (cut (min limit (row.exit.path.length+1)) v)).2.1]
      exact cut_respects_depth _ _
  · cases accepted
end HeadControls

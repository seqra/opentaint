import PartitionMachine
import Acceptance

/- The selected older uniform and cleaner contracts stay in force. The new
   planner does not split an admitted MUST family into point/STAR families. -/
namespace ProgressiveCompatibility
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle
open BoundedRefinementPipeline NormalUniformNE NestedSavedReplayCycle NestedColdMachine

 theorem a_dedicated_uniform_family_is_independent_of_every_partition
    (run limit : Nat) (backward : Bool) (tree : List Path) (row : Row) (a : Offered)
    (uniform : (baseFamily run limit backward row a).any (fun q => q.ap.tail == .must) = true) :
    ProgressiveMachine.cells run limit backward tree row a =
      (baseFamily run limit backward row a).map (fun q => ⟨row,row,q,[]⟩) := by
  simp [ProgressiveMachine.cells,uniform]

theorem the_selected_cleaner_forward_rows_all_use_this_unchanged_family :
    SameLaneMarkedClosure.rows3.all (fun row =>
      (baseFamily 3 2 false row SameLaneMarkedClosure.sourceOffer).any
        (fun q => q.ap.tail == .must)) = true := by decide

theorem no_partition_changes_the_cleaner_source_families
    (tree : List Path) (row : Row) (member : row ∈ SameLaneMarkedClosure.rows3) :
    ProgressiveMachine.cells 3 2 false tree row SameLaneMarkedClosure.sourceOffer =
      (baseFamily 3 2 false row SameLaneMarkedClosure.sourceOffer).map
        (fun q => ⟨row,row,q,[]⟩) := by
  apply a_dedicated_uniform_family_is_independent_of_every_partition
  exact List.all_eq_true.mp the_selected_cleaner_forward_rows_all_use_this_unchanged_family row member

/-- Fallback is attached to the native operation's supported query-correlation
    service, not to a wrapper syntax template. In particular a cleaner or an
    observation is never suppressed by finding a child field in the trie. -/
def routeOperation (supported delegated : Bool) (ordinary : Option α) : Option α :=
  if supported && delegated then none else ordinary

theorem an_unsupported_operation_keeps_its_whole_old_result
    (delegated : Bool) (ordinary : Option α) :
    routeOperation false delegated ordinary = ordinary := rfl

theorem routing_never_changes_a_surviving_result
    (supported delegated : Bool) (ordinary : Option α) (value : α)
    (emitted : routeOperation supported delegated ordinary = some value) :
    ordinary = some value := by
  unfold routeOperation at emitted
  split at emitted
  · contradiction
  · exact emitted

theorem saved_replay_with_no_current_demand_is_the_old_native_service
    (run limit : Nat) (trees : ProgressiveMachine.Trees) (saved : List (List Saved))
    (a : Offered) :
    ProgressiveMachine.offer run limit 0 trees [[],[]] saved [[],[]] a =
      NestedColdMachine.offer run limit [] (saved[0]!) [] a := by
  simp [ProgressiveMachine.offer,ProgressiveMachine.plans,NestedColdMachine.offer,executable]

theorem old_protected_and_cleaner_frontiers_keep_their_selected_coverage :
    SameLaneMarkedClosure.incoming SameLaneMarkedClosure.closedPacket = [] ∧
    UniformRootCleanerPolicy.nextDemand UniformRootCleanerPolicy.newForward = [] ∧
    SameLaneMarkedClosure.incoming UniformNERegressions.cleanerForwardPacket = [] := by
  exact ⟨SameLaneAcceptance.neither_old_nor_new_case_needs_a_nonempty_forward_frontier.2.2,
    SameLaneAcceptance.the_selected_cleaner_survivor_and_standalone_termination_are_unchanged.2.2,
    SameLaneAcceptance.the_selected_cleaner_survivor_and_standalone_termination_are_unchanged.2.1⟩

 theorem old_uniform_subsumption_is_not_replaced_by_partition_location_coverage :
    SameLaneUniform.compact true UniformNEClosure.oldPacket =
      NormalUniformNE.compact true UniformNEClosure.oldPacket ∧
    SameLaneUniform.compact true UniformNEClosure.newPacket =
      NormalUniformNE.compact true UniformNEClosure.newPacket :=
  SameLaneAcceptance.the_old_method_and_new_neutral_complete_packets_are_unchanged

end ProgressiveCompatibility

#print axioms ProgressiveCompatibility.a_dedicated_uniform_family_is_independent_of_every_partition
#print axioms ProgressiveCompatibility.the_selected_cleaner_forward_rows_all_use_this_unchanged_family
#print axioms ProgressiveCompatibility.no_partition_changes_the_cleaner_source_families
#print axioms ProgressiveCompatibility.an_unsupported_operation_keeps_its_whole_old_result
#print axioms ProgressiveCompatibility.routing_never_changes_a_surviving_result
#print axioms ProgressiveCompatibility.saved_replay_with_no_current_demand_is_the_old_native_service
#print axioms ProgressiveCompatibility.old_protected_and_cleaner_frontiers_keep_their_selected_coverage
#print axioms ProgressiveCompatibility.old_uniform_subsumption_is_not_replaced_by_partition_location_coverage

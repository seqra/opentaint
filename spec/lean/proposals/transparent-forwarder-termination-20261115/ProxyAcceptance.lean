import ProxyCertificates

/- New and old acceptance obligations in one module. The new policy is a
   guarded owner projection; rejected shapes retain all prior mechanisms. -/
namespace TransparentOwnerAcceptance
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle
open BoundedRefinementPipeline NormalUniformNE NestedSavedReplayCycle NestedColdMachine
open TransparentOwner ProxyCertificates TargetZeroKernel

/-- Known rejecting traits of the old fixtures. Exact constructor-call
    counts do not matter: field operations or rules already reject them. -/
def oldShapes : List Shape :=
  [{copiesOnly := false,calls := 0},                 -- read f.g / write f
   {copiesOnly := false,calls := 2},                 -- two BB branches
   {copiesOnly := false,calls := 0},                 -- arbitrary deeper reader
   {copiesOnly := false,calls := 0},                 -- read ff / write ff
   {copiesOnly := false,wrapperRulesEmpty := false}, -- selected cleaner/growth
   {calls := 0,wrapperRulesEmpty := false},          -- standalone selected cleaner
   {copiesOnly := false},                           -- wrapper reads h/writes k
   {calls := 0,wrapperRulesEmpty := false}]          -- exact-root survivor

theorem the_old_required_fixtures_keep_the_same_dispatch :
    oldShapes.all (fun s => !(eligible s)) = true := by decide

theorem no_rejected_fixture_changes_any_old_frontier
    (s : Shape) (ordinary proxy : α) (member : s ∈ oldShapes) :
    dispatch s ordinary proxy = ordinary := by
  have rejected : eligible s = false := by
    have yes := List.all_eq_true.mp the_old_required_fixtures_keep_the_same_dispatch s member
    cases h : eligible s <;> simp_all
  exact every_rejected_owner_keeps_ordinary_analysis s ordinary proxy rejected

theorem the_certified_new_wrapper_uses_the_direct_owner_round
    (run limit : Nat) (rows : List (List Row)) (saved : List (List Saved)) (st : State) :
    dispatch {} (NestedColdMachine.round run limit rows saved st)
      (DirectOwnerMachine.round run limit rows saved st) =
      DirectOwnerMachine.round run limit rows saved st := rfl

theorem fields_or_rules_reject_the_relay_for_any_other_shape
    (s : Shape) (ordinary proxy : α) :
    dispatch {s with copiesOnly := false} ordinary proxy = ordinary ∧
    dispatch {s with wrapperRulesEmpty := false} ordinary proxy = ordinary := by
  simp [dispatch,eligible]

theorem every_old_long_reader_keeps_its_complete_packet (rest : Path) :
    UniformNEClosure.ownerRun3 ⟨[f,g] ++ rest,[f]⟩
      UniformNEClosure.oldRows3 UniformNEClosure.fieldUniform = UniformNEClosure.oldPacket :=
  UniformNERegressions.the_complete_longer_reader_packet_is_unchanged rest

theorem old_method_bb_and_neutral_frontiers_still_close :
    SameLaneUniform.compact true UniformNEClosure.oldPacket =
      NormalUniformNE.compact true UniformNEClosure.oldPacket ∧
    SameLaneUniform.compact true UniformNEClosure.newPacket =
      NormalUniformNE.compact true UniformNEClosure.newPacket :=
  SameLaneAcceptance.the_old_method_and_new_neutral_complete_packets_are_unchanged

theorem old_inner_blocks_and_wrapper_routes_still_close :
    SameLaneMarkedClosure.incoming (SameLaneUniform.compact true UniformNERegressions.bbPacket) = [] ∧
    SameLaneMarkedClosure.incoming UniformNERegressions.readBB = [] ∧
    SameLaneUniform.compact true UniformNERegressions.wrapperPacket = UniformNERegressions.wrapperPacket :=
  SameLaneAcceptance.the_old_bb_frontier_and_wrapper_finding_routes_are_unchanged

theorem old_selected_cleaner_cases_and_their_findings_are_kept :
    SameLaneUniform.compact true UniformNERegressions.cleanerForwardPacket =
      UniformNERegressions.cleanerForwardPacket ∧
    SameLaneMarkedClosure.incoming UniformNERegressions.cleanerForwardPacket = [] ∧
    UniformRootCleanerPolicy.nextDemand UniformRootCleanerPolicy.newForward = [] :=
  SameLaneAcceptance.the_selected_cleaner_survivor_and_standalone_termination_are_unchanged

theorem old_protected_and_ordinary_complete_frontiers_are_empty :
    BoundedRefinementPipeline.handoff UniformNEClosure.oldBasis = [] ∧
    BoundedRefinementPipeline.handoff UniformNEClosure.newBasis = [] ∧
    SameLaneMarkedClosure.incoming SameLaneMarkedClosure.closedPacket = [] :=
  SameLaneAcceptance.neither_old_nor_new_case_needs_a_nonempty_forward_frontier

def terminal (a : Offered) : Summary :=
  forwardSinkTarget 0 .zero (if a.demand then .demand else .normal) 0

theorem new_run7_real_cut_still_requests_refinement :
    ((state7.offers[3]!).map terminal).any continuationRelevant = true := by decide

theorem new_run9_full_frontier_is_empty_and_the_normal_observation_remains :
    rows9 = [[],[]] ∧
    (((state9.offers[3]!).map terminal).filter continuationRelevant) = [] ∧
    collectReports [0] ((state9.offers[3]!).map terminal) = [0] := by decide

theorem no_later_iteration_is_required_after_the_complete_run9_fixed_point :
    DirectOwnerMachine.round 9 8 rows8 saved8 state9 = state9 ∧
    outputRows state9 = [[],[]] ∧
    (((state9.offers[3]!).map terminal).filter continuationRelevant) = [] := by
  exact ⟨quiescent_9,natural_completion_at_run9.1,by decide⟩

theorem the_new_tail_relay_changes_no_program_observation
    (body : α → Result α β → Prop) (a : α) (out : Result α β) :
    Executes body a out ↔ body a out := relay_has_exactly_the_callee_behavior body a out

end TransparentOwnerAcceptance

#print axioms TransparentOwnerAcceptance.the_old_required_fixtures_keep_the_same_dispatch
#print axioms TransparentOwnerAcceptance.no_rejected_fixture_changes_any_old_frontier
#print axioms TransparentOwnerAcceptance.old_method_bb_and_neutral_frontiers_still_close
#print axioms TransparentOwnerAcceptance.old_inner_blocks_and_wrapper_routes_still_close
#print axioms TransparentOwnerAcceptance.old_selected_cleaner_cases_and_their_findings_are_kept
#print axioms TransparentOwnerAcceptance.old_protected_and_ordinary_complete_frontiers_are_empty
#print axioms TransparentOwnerAcceptance.new_run7_real_cut_still_requests_refinement
#print axioms TransparentOwnerAcceptance.new_run9_full_frontier_is_empty_and_the_normal_observation_remains
#print axioms TransparentOwnerAcceptance.no_later_iteration_is_required_after_the_complete_run9_fixed_point
#print axioms TransparentOwnerAcceptance.the_new_tail_relay_changes_no_program_observation

#print axioms TransparentOwnerAcceptance.the_certified_new_wrapper_uses_the_direct_owner_round

#print axioms TransparentOwnerAcceptance.fields_or_rules_reject_the_relay_for_any_other_shape
#print axioms TransparentOwnerAcceptance.every_old_long_reader_keeps_its_complete_packet

import ChildCover

namespace PreparedReplayCompatibility
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NormalUniformNE
open NestedSavedReplayCycle NestedColdMachine PreparedChildReplay

/-- There is no new C2 implementation: process uses this old cells function
    directly. Both modes share exactly the same raw work for a fixed domain. -/
def entryWork (run limit : Nat) (rows : List Row) (saved : List Saved)
    (actuals : List Offered) : List Cell :=
  cells run limit (run % 2 == 0) rows (views (run % 2 == 0) saved) actuals

theorem entry_work_is_exactly_the_old_c2_for_every_domain
    (run limit : Nat) (rows : List Row) (saved : List Saved) (actuals : List Offered) :
    entryWork run limit rows saved actuals =
      cells run limit (run % 2 == 0) rows (views (run % 2 == 0) saved) actuals := rfl

theorem must_queries_keep_the_full_old_replay
    (q : Ap) (mask : List Nat) (e : Edge × Bool) (a : Offered) :
    route {q with tail := .must} mask e a = applyEdge e.2 e.1 a := by
  simp [route,delegated]

theorem concrete_owned_queries_keep_the_full_old_replay
    (q : Ap) (mark : Nat) (mask : List Nat) (e : Edge × Bool) (a : Offered) :
    route {q with mark := some mark} mask e a = applyEdge e.2 e.1 a := by
  simp [route,delegated]

theorem protected_records_keep_the_full_old_replay
    (q : Ap) (mask : List Nat) (e : Edge × Bool) (a : Offered) :
    route q mask ((e.1.1,{e.1.2 with h := true}),e.2) a =
      applyEdge e.2 (e.1.1,{e.1.2 with h := true}) a := by
  simp [route,delegated]

theorem current_direction_records_keep_the_full_old_replay
    (q : Ap) (mask : List Nat) (e : Edge) (a : Offered) :
    route q mask (e,false) a = applyEdge false e a := by
  simp [route,delegated]

theorem child_budget_failure_disables_routing
    (run limit : Nat) (rows : List Row) (norms : List (Edge × Bool))
    (q : Ap) (mask : List Nat) (over : limit < q.path.length+1) :
    readyMask run limit rows norms q mask = [] := by
  simp [readyMask,over]

theorem no_extra_postprocessing_outputs_for_a_fixed_native_offer
    (q : Ap) (mask : List Nat) (es : List (Edge × Bool)) (a : Offered)
    (post : Offered → List α) :
    ((es.filterMap fun e => route q mask e a).flatMap post).length ≤
      ((es.filterMap fun e => applyEdge e.2 e.1 a).flatMap post).length := by
  induction es with
  | nil => simp
  | cons e es ih =>
    cases flag : delegated q mask e.1 e.2 a <;>
      cases native : applyEdge e.2 e.1 a <;>
      simp_all [route] <;> omega

/-- Older selected-cleaner and protected coverage remain the selected laws.
    They are not replaced with any plain FLOW location-cover rule. -/
theorem all_selected_older_uniform_and_cleaner_results_remain_available :
    SameLaneMarkedClosure.incoming SameLaneMarkedClosure.closedPacket = [] ∧
    UniformRootCleanerPolicy.nextDemand UniformRootCleanerPolicy.newForward = [] ∧
    SameLaneMarkedClosure.incoming UniformNERegressions.cleanerForwardPacket = [] :=
  ⟨SameLaneAcceptance.neither_old_nor_new_case_needs_a_nonempty_forward_frontier.2.2,
    SameLaneAcceptance.the_selected_cleaner_survivor_and_standalone_termination_are_unchanged.2.2,
    SameLaneAcceptance.the_selected_cleaner_survivor_and_standalone_termination_are_unchanged.2.1⟩

end PreparedReplayCompatibility

#print axioms PreparedReplayCompatibility.entry_work_is_exactly_the_old_c2_for_every_domain
#print axioms PreparedReplayCompatibility.must_queries_keep_the_full_old_replay
#print axioms PreparedReplayCompatibility.concrete_owned_queries_keep_the_full_old_replay
#print axioms PreparedReplayCompatibility.protected_records_keep_the_full_old_replay
#print axioms PreparedReplayCompatibility.current_direction_records_keep_the_full_old_replay
#print axioms PreparedReplayCompatibility.child_budget_failure_disables_routing
#print axioms PreparedReplayCompatibility.no_extra_postprocessing_outputs_for_a_fixed_native_offer
#print axioms PreparedReplayCompatibility.all_selected_older_uniform_and_cleaner_results_remain_available

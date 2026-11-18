import ExclusionCover
import Compatibility

namespace ExclusionChildCompatibility
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NormalUniformNE NestedSavedReplayCycle NestedColdMachine
open OverwriteReplay ExclusionChildReplay
set_option linter.unusedSimpArgs false

theorem old_and_new_eligibility_are_equal_when_real_field_E_is_empty
    (q : Ap) (mask : List Nat) (e : Edge) (opposite : Bool) (a : Offered)
    (input : a.ap.e = []) (premise : e.1.e = []) (result : e.2.ap.e = []) :
    eligible q mask e opposite a = PreparedChildReplay.delegated q mask e opposite a := by
  simp [eligible,PreparedChildReplay.delegated,input,premise,result]
  rfl

theorem unsupported_raw_initial_exclusions_keep_old_replay
    (q : Ap) (mask : List Nat) (e : Edge × Bool) (a : Offered) (outside : q.e.isEmpty = false) :
    ExclusionChildReplay.route true q mask e a = ExclusionChildReplay.route false q mask e a := by
  simp [ExclusionChildReplay.route,eligible,OverwriteReplay.route,PreparedChildReplay.delegated,outside]

theorem concrete_owned_queries_keep_old_replay
    (q : Ap) (mark : Nat) (mask : List Nat) (e : Edge × Bool) (a : Offered) :
    ExclusionChildReplay.route true {q with mark := some mark} mask e a = ExclusionChildReplay.route false {q with mark := some mark} mask e a := by
  simp [ExclusionChildReplay.route,eligible,OverwriteReplay.route,PreparedChildReplay.delegated]

theorem must_owned_queries_keep_old_replay
    (q : Ap) (mask : List Nat) (e : Edge × Bool) (a : Offered) :
    ExclusionChildReplay.route true {q with tail := .must} mask e a = ExclusionChildReplay.route false {q with tail := .must} mask e a := by
  simp [ExclusionChildReplay.route,eligible,OverwriteReplay.route,PreparedChildReplay.delegated]

theorem protected_records_keep_old_replay
    (q : Ap) (mask : List Nat) (e : Edge × Bool) (a : Offered) :
    ExclusionChildReplay.route true q mask ((e.1.1,{e.1.2 with h := true}),e.2) a =
      ExclusionChildReplay.route false q mask ((e.1.1,{e.1.2 with h := true}),e.2) a := by
  simp [ExclusionChildReplay.route,eligible,OverwriteReplay.route,PreparedChildReplay.delegated]

theorem already_demand_values_keep_old_replay
    (q : Ap) (mask : List Nat) (e : Edge × Bool) (a : Offered) :
    ExclusionChildReplay.route true q mask e {a with demand := true} = ExclusionChildReplay.route false q mask e {a with demand := true} := by
  simp [ExclusionChildReplay.route,eligible,OverwriteReplay.route,PreparedChildReplay.delegated]

theorem missing_child_cover_keeps_old_replay
    (q : Ap) (e : Edge × Bool) (a : Offered) :
    ExclusionChildReplay.route true q [] e a = ExclusionChildReplay.route false q [] e a := by
  simp [ExclusionChildReplay.route,eligible,OverwriteReplay.route,PreparedChildReplay.delegated]
  split <;> simp_all

theorem selected_cleaner_and_protected_acceptance_results_remain_available :
    SameLaneMarkedClosure.incoming SameLaneMarkedClosure.closedPacket = [] ∧
    UniformRootCleanerPolicy.nextDemand UniformRootCleanerPolicy.newForward = [] ∧
    SameLaneMarkedClosure.incoming UniformNERegressions.cleanerForwardPacket = [] :=
  PreparedReplayCompatibility.all_selected_older_uniform_and_cleaner_results_remain_available
end ExclusionChildCompatibility
#print axioms ExclusionChildCompatibility.old_and_new_eligibility_are_equal_when_real_field_E_is_empty
#print axioms ExclusionChildCompatibility.unsupported_raw_initial_exclusions_keep_old_replay
#print axioms ExclusionChildCompatibility.concrete_owned_queries_keep_old_replay
#print axioms ExclusionChildCompatibility.must_owned_queries_keep_old_replay
#print axioms ExclusionChildCompatibility.protected_records_keep_old_replay
#print axioms ExclusionChildCompatibility.already_demand_values_keep_old_replay
#print axioms ExclusionChildCompatibility.missing_child_cover_keeps_old_replay
#print axioms ExclusionChildCompatibility.selected_cleaner_and_protected_acceptance_results_remain_available

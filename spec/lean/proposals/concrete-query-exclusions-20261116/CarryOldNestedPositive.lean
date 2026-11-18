import CarryCampaign
import UniformStickyColdNestedPositive
namespace CarryOldNestedPositive
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
def c := UniformStickyColdNestedPositive.c
def state0 := UniformStickyColdNestedPositive.state0
def state1 := UniformStickyColdNestedPositive.state1
def state2 := UniformStickyColdNestedPositive.state2
def state3 := UniformStickyColdNestedPositive.state3
def state4 := UniformStickyColdNestedPositive.state4
theorem cold_1 : CarryCampaign.step c 1 state0 = state1 := by
  rw [CarryCampaign.step_eq_old c 1 _ (by decide +kernel)]
  exact UniformStickyColdNestedPositive.cold_1
theorem reached_1 : CarryCampaign.history c 1 = state1 := by
  change CarryCampaign.step c 1 (CarryCampaign.history c 0) = state1
  change CarryCampaign.step c 1 state0 = state1
  exact cold_1
theorem cold_2 : CarryCampaign.step c 2 state1 = state2 := by
  rw [CarryCampaign.step_eq_old c 2 _ (by decide +kernel)]
  exact UniformStickyColdNestedPositive.cold_2
theorem reached_2 : CarryCampaign.history c 2 = state2 := by
  change CarryCampaign.step c 2 (CarryCampaign.history c 1) = state2
  rw [reached_1]
  exact cold_2
theorem cold_3 : CarryCampaign.step c 3 state2 = state3 := by
  rw [CarryCampaign.step_eq_old c 3 _ (by decide +kernel)]
  exact UniformStickyColdNestedPositive.cold_3
theorem reached_3 : CarryCampaign.history c 3 = state3 := by
  change CarryCampaign.step c 3 (CarryCampaign.history c 2) = state3
  rw [reached_2]
  exact cold_3
theorem cold_4 : CarryCampaign.step c 4 state3 = state4 := by
  rw [CarryCampaign.step_eq_old c 4 _ (by decide +kernel)]
  exact UniformStickyColdNestedPositive.cold_4
theorem reached_4 : CarryCampaign.history c 4 = state4 := by
  change CarryCampaign.step c 4 (CarryCampaign.history c 3) = state4
  rw [reached_3]
  exact cold_4
theorem natural_stop_and_expected_observation : UniformCampaign.stopped 3 state3 = true ∧ state3.report = c.expected := UniformStickyColdNestedPositive.natural_stop_and_expected_observation
theorem final_is_quiet : state4 = UniformCampaign.quiet c c.expected state4.saved := UniformStickyColdNestedPositive.final_is_quiet
theorem uncapped_no_revival (n : Nat) : CarryCampaign.history c (n+4) = state4 := by
  induction n with
  | zero => exact reached_4
  | succ n ih =>
      change CarryCampaign.step c (n+5) (CarryCampaign.history c (n+4)) = state4
      rw [ih,final_is_quiet]
      exact CarryCampaign.quiet_never_restarts c _ _ _
end CarryOldNestedPositive

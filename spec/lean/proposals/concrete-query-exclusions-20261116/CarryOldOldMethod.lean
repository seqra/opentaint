import CarryCampaign
import UniformStickyColdOldMethod
namespace CarryOldOldMethod
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
def c := UniformStickyColdOldMethod.c
def state0 := UniformStickyColdOldMethod.state0
def state1 := UniformStickyColdOldMethod.state1
def state2 := UniformStickyColdOldMethod.state2
def state3 := UniformStickyColdOldMethod.state3
def state4 := UniformStickyColdOldMethod.state4
def state5 := UniformStickyColdOldMethod.state5
def state6 := UniformStickyColdOldMethod.state6
theorem cold_1 : CarryCampaign.step c 1 state0 = state1 := by
  rw [CarryCampaign.step_eq_old c 1 _ (by decide +kernel)]
  exact UniformStickyColdOldMethod.cold_1
theorem reached_1 : CarryCampaign.history c 1 = state1 := by
  change CarryCampaign.step c 1 (CarryCampaign.history c 0) = state1
  change CarryCampaign.step c 1 state0 = state1
  exact cold_1
theorem cold_2 : CarryCampaign.step c 2 state1 = state2 := by
  rw [CarryCampaign.step_eq_old c 2 _ (by decide +kernel)]
  exact UniformStickyColdOldMethod.cold_2
theorem reached_2 : CarryCampaign.history c 2 = state2 := by
  change CarryCampaign.step c 2 (CarryCampaign.history c 1) = state2
  rw [reached_1]
  exact cold_2
theorem cold_3 : CarryCampaign.step c 3 state2 = state3 := by
  rw [CarryCampaign.step_eq_old c 3 _ (by decide +kernel)]
  exact UniformStickyColdOldMethod.cold_3
theorem reached_3 : CarryCampaign.history c 3 = state3 := by
  change CarryCampaign.step c 3 (CarryCampaign.history c 2) = state3
  rw [reached_2]
  exact cold_3
theorem cold_4 : CarryCampaign.step c 4 state3 = state4 := by
  rw [CarryCampaign.step_eq_old c 4 _ (by decide +kernel)]
  exact UniformStickyColdOldMethod.cold_4
theorem reached_4 : CarryCampaign.history c 4 = state4 := by
  change CarryCampaign.step c 4 (CarryCampaign.history c 3) = state4
  rw [reached_3]
  exact cold_4
theorem cold_5 : CarryCampaign.step c 5 state4 = state5 := by
  rw [CarryCampaign.step_eq_old c 5 _ (by decide +kernel)]
  exact UniformStickyColdOldMethod.cold_5
theorem reached_5 : CarryCampaign.history c 5 = state5 := by
  change CarryCampaign.step c 5 (CarryCampaign.history c 4) = state5
  rw [reached_4]
  exact cold_5
theorem cold_6 : CarryCampaign.step c 6 state5 = state6 := by
  rw [CarryCampaign.step_eq_old c 6 _ (by decide +kernel)]
  exact UniformStickyColdOldMethod.cold_6
theorem reached_6 : CarryCampaign.history c 6 = state6 := by
  change CarryCampaign.step c 6 (CarryCampaign.history c 5) = state6
  rw [reached_5]
  exact cold_6
theorem natural_stop_and_expected_observation : UniformCampaign.stopped 5 state5 = true ∧ state5.report = c.expected := UniformStickyColdOldMethod.natural_stop_and_expected_observation
theorem final_is_quiet : state6 = UniformCampaign.quiet c c.expected state6.saved := UniformStickyColdOldMethod.final_is_quiet
theorem uncapped_no_revival (n : Nat) : CarryCampaign.history c (n+6) = state6 := by
  induction n with
  | zero => exact reached_6
  | succ n ih =>
      change CarryCampaign.step c (n+7) (CarryCampaign.history c (n+6)) = state6
      rw [ih,final_is_quiet]
      exact CarryCampaign.quiet_never_restarts c _ _ _
end CarryOldOldMethod

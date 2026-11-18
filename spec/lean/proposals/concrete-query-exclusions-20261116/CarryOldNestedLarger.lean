import CarryCampaign
import UniformStickyColdNestedLarger
namespace CarryOldNestedLarger
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
def c := UniformStickyColdNestedLarger.c
def state0 := UniformStickyColdNestedLarger.state0
def state1 := UniformStickyColdNestedLarger.state1
def state2 := UniformStickyColdNestedLarger.state2
def state3 := UniformStickyColdNestedLarger.state3
def state4 := UniformStickyColdNestedLarger.state4
def state5 := UniformStickyColdNestedLarger.state5
def state6 := UniformStickyColdNestedLarger.state6
def state7 := UniformStickyColdNestedLarger.state7
def state8 := UniformStickyColdNestedLarger.state8
def state9 := UniformStickyColdNestedLarger.state9
def state10 := UniformStickyColdNestedLarger.state10
def state11 := UniformStickyColdNestedLarger.state11
def state12 := UniformStickyColdNestedLarger.state12
theorem cold_1 : CarryCampaign.step c 1 state0 = state1 := by
  rw [CarryCampaign.step_eq_old c 1 _ (by decide +kernel)]
  exact UniformStickyColdNestedLarger.cold_1
theorem reached_1 : CarryCampaign.history c 1 = state1 := by
  change CarryCampaign.step c 1 (CarryCampaign.history c 0) = state1
  change CarryCampaign.step c 1 state0 = state1
  exact cold_1
theorem cold_2 : CarryCampaign.step c 2 state1 = state2 := by
  rw [CarryCampaign.step_eq_old c 2 _ (by decide +kernel)]
  exact UniformStickyColdNestedLarger.cold_2
theorem reached_2 : CarryCampaign.history c 2 = state2 := by
  change CarryCampaign.step c 2 (CarryCampaign.history c 1) = state2
  rw [reached_1]
  exact cold_2
theorem cold_3 : CarryCampaign.step c 3 state2 = state3 := by
  rw [CarryCampaign.step_eq_old c 3 _ (by decide +kernel)]
  exact UniformStickyColdNestedLarger.cold_3
theorem reached_3 : CarryCampaign.history c 3 = state3 := by
  change CarryCampaign.step c 3 (CarryCampaign.history c 2) = state3
  rw [reached_2]
  exact cold_3
theorem cold_4 : CarryCampaign.step c 4 state3 = state4 := by
  rw [CarryCampaign.step_eq_old c 4 _ (by decide +kernel)]
  exact UniformStickyColdNestedLarger.cold_4
theorem reached_4 : CarryCampaign.history c 4 = state4 := by
  change CarryCampaign.step c 4 (CarryCampaign.history c 3) = state4
  rw [reached_3]
  exact cold_4
theorem cold_5 : CarryCampaign.step c 5 state4 = state5 := by
  rw [CarryCampaign.step_eq_old c 5 _ (by decide +kernel)]
  exact UniformStickyColdNestedLarger.cold_5
theorem reached_5 : CarryCampaign.history c 5 = state5 := by
  change CarryCampaign.step c 5 (CarryCampaign.history c 4) = state5
  rw [reached_4]
  exact cold_5
theorem cold_6 : CarryCampaign.step c 6 state5 = state6 := by
  rw [CarryCampaign.step_eq_old c 6 _ (by decide +kernel)]
  exact UniformStickyColdNestedLarger.cold_6
theorem reached_6 : CarryCampaign.history c 6 = state6 := by
  change CarryCampaign.step c 6 (CarryCampaign.history c 5) = state6
  rw [reached_5]
  exact cold_6
theorem cold_7 : CarryCampaign.step c 7 state6 = state7 := by
  rw [CarryCampaign.step_eq_old c 7 _ (by decide +kernel)]
  exact UniformStickyColdNestedLarger.cold_7
theorem reached_7 : CarryCampaign.history c 7 = state7 := by
  change CarryCampaign.step c 7 (CarryCampaign.history c 6) = state7
  rw [reached_6]
  exact cold_7
theorem cold_8 : CarryCampaign.step c 8 state7 = state8 := by
  rw [CarryCampaign.step_eq_old c 8 _ (by decide +kernel)]
  exact UniformStickyColdNestedLarger.cold_8
theorem reached_8 : CarryCampaign.history c 8 = state8 := by
  change CarryCampaign.step c 8 (CarryCampaign.history c 7) = state8
  rw [reached_7]
  exact cold_8
theorem cold_9 : CarryCampaign.step c 9 state8 = state9 := by
  rw [CarryCampaign.step_eq_old c 9 _ (by decide +kernel)]
  exact UniformStickyColdNestedLarger.cold_9
theorem reached_9 : CarryCampaign.history c 9 = state9 := by
  change CarryCampaign.step c 9 (CarryCampaign.history c 8) = state9
  rw [reached_8]
  exact cold_9
theorem cold_10 : CarryCampaign.step c 10 state9 = state10 := by
  rw [CarryCampaign.step_eq_old c 10 _ (by decide +kernel)]
  exact UniformStickyColdNestedLarger.cold_10
theorem reached_10 : CarryCampaign.history c 10 = state10 := by
  change CarryCampaign.step c 10 (CarryCampaign.history c 9) = state10
  rw [reached_9]
  exact cold_10
theorem cold_11 : CarryCampaign.step c 11 state10 = state11 := by
  rw [CarryCampaign.step_eq_old c 11 _ (by decide +kernel)]
  exact UniformStickyColdNestedLarger.cold_11
theorem reached_11 : CarryCampaign.history c 11 = state11 := by
  change CarryCampaign.step c 11 (CarryCampaign.history c 10) = state11
  rw [reached_10]
  exact cold_11
theorem cold_12 : CarryCampaign.step c 12 state11 = state12 := by
  rw [CarryCampaign.step_eq_old c 12 _ (by decide +kernel)]
  exact UniformStickyColdNestedLarger.cold_12
theorem reached_12 : CarryCampaign.history c 12 = state12 := by
  change CarryCampaign.step c 12 (CarryCampaign.history c 11) = state12
  rw [reached_11]
  exact cold_12
theorem natural_stop_and_expected_observation : UniformCampaign.stopped 11 state11 = true ∧ state11.report = c.expected := UniformStickyColdNestedLarger.natural_stop_and_expected_observation
theorem final_is_quiet : state12 = UniformCampaign.quiet c c.expected state12.saved := UniformStickyColdNestedLarger.final_is_quiet
theorem uncapped_no_revival (n : Nat) : CarryCampaign.history c (n+12) = state12 := by
  induction n with
  | zero => exact reached_12
  | succ n ih =>
      change CarryCampaign.step c (n+13) (CarryCampaign.history c (n+12)) = state12
      rw [ih,final_is_quiet]
      exact CarryCampaign.quiet_never_restarts c _ _ _
end CarryOldNestedLarger

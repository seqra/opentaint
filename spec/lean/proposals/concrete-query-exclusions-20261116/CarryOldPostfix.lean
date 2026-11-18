import CarryCampaign
import UniformStickyColdPostfix
namespace CarryOldPostfix
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
def c := UniformStickyColdPostfix.c
def state0 := UniformStickyColdPostfix.state0
def state1 := UniformStickyColdPostfix.state1
def state2 := UniformStickyColdPostfix.state2
def state3 := UniformStickyColdPostfix.state3
def state4 := UniformStickyColdPostfix.state4
def state5 := UniformStickyColdPostfix.state5
def state6 := UniformStickyColdPostfix.state6
def state7 := UniformStickyColdPostfix.state7
def state8 := UniformStickyColdPostfix.state8
def state9 := UniformStickyColdPostfix.state9
def state10 := UniformStickyColdPostfix.state10
def state11 := UniformStickyColdPostfix.state11
def state12 := UniformStickyColdPostfix.state12
def state13 := UniformStickyColdPostfix.state13
def state14 := UniformStickyColdPostfix.state14
theorem cold_1 : CarryCampaign.step c 1 state0 = state1 := by
  rw [CarryCampaign.step_eq_old c 1 _ (by decide +kernel)]
  exact UniformStickyColdPostfix.cold_1
theorem reached_1 : CarryCampaign.history c 1 = state1 := by
  change CarryCampaign.step c 1 (CarryCampaign.history c 0) = state1
  change CarryCampaign.step c 1 state0 = state1
  exact cold_1
theorem cold_2 : CarryCampaign.step c 2 state1 = state2 := by
  rw [CarryCampaign.step_eq_old c 2 _ (by decide +kernel)]
  exact UniformStickyColdPostfix.cold_2
theorem reached_2 : CarryCampaign.history c 2 = state2 := by
  change CarryCampaign.step c 2 (CarryCampaign.history c 1) = state2
  rw [reached_1]
  exact cold_2
theorem cold_3 : CarryCampaign.step c 3 state2 = state3 := by
  rw [CarryCampaign.step_eq_old c 3 _ (by decide +kernel)]
  exact UniformStickyColdPostfix.cold_3
theorem reached_3 : CarryCampaign.history c 3 = state3 := by
  change CarryCampaign.step c 3 (CarryCampaign.history c 2) = state3
  rw [reached_2]
  exact cold_3
theorem cold_4 : CarryCampaign.step c 4 state3 = state4 := by
  rw [CarryCampaign.step_eq_old c 4 _ (by decide +kernel)]
  exact UniformStickyColdPostfix.cold_4
theorem reached_4 : CarryCampaign.history c 4 = state4 := by
  change CarryCampaign.step c 4 (CarryCampaign.history c 3) = state4
  rw [reached_3]
  exact cold_4
theorem cold_5 : CarryCampaign.step c 5 state4 = state5 := by
  rw [CarryCampaign.step_eq_old c 5 _ (by decide +kernel)]
  exact UniformStickyColdPostfix.cold_5
theorem reached_5 : CarryCampaign.history c 5 = state5 := by
  change CarryCampaign.step c 5 (CarryCampaign.history c 4) = state5
  rw [reached_4]
  exact cold_5
theorem cold_6 : CarryCampaign.step c 6 state5 = state6 := by
  rw [CarryCampaign.step_eq_old c 6 _ (by decide +kernel)]
  exact UniformStickyColdPostfix.cold_6
theorem reached_6 : CarryCampaign.history c 6 = state6 := by
  change CarryCampaign.step c 6 (CarryCampaign.history c 5) = state6
  rw [reached_5]
  exact cold_6
theorem cold_7 : CarryCampaign.step c 7 state6 = state7 := by
  rw [CarryCampaign.step_eq_old c 7 _ (by decide +kernel)]
  exact UniformStickyColdPostfix.cold_7
theorem reached_7 : CarryCampaign.history c 7 = state7 := by
  change CarryCampaign.step c 7 (CarryCampaign.history c 6) = state7
  rw [reached_6]
  exact cold_7
theorem cold_8 : CarryCampaign.step c 8 state7 = state8 := by
  rw [CarryCampaign.step_eq_old c 8 _ (by decide +kernel)]
  exact UniformStickyColdPostfix.cold_8
theorem reached_8 : CarryCampaign.history c 8 = state8 := by
  change CarryCampaign.step c 8 (CarryCampaign.history c 7) = state8
  rw [reached_7]
  exact cold_8
theorem cold_9 : CarryCampaign.step c 9 state8 = state9 := by
  rw [CarryCampaign.step_eq_old c 9 _ (by decide +kernel)]
  exact UniformStickyColdPostfix.cold_9
theorem reached_9 : CarryCampaign.history c 9 = state9 := by
  change CarryCampaign.step c 9 (CarryCampaign.history c 8) = state9
  rw [reached_8]
  exact cold_9
theorem cold_10 : CarryCampaign.step c 10 state9 = state10 := by
  rw [CarryCampaign.step_eq_old c 10 _ (by decide +kernel)]
  exact UniformStickyColdPostfix.cold_10
theorem reached_10 : CarryCampaign.history c 10 = state10 := by
  change CarryCampaign.step c 10 (CarryCampaign.history c 9) = state10
  rw [reached_9]
  exact cold_10
theorem cold_11 : CarryCampaign.step c 11 state10 = state11 := by
  rw [CarryCampaign.step_eq_old c 11 _ (by decide +kernel)]
  exact UniformStickyColdPostfix.cold_11
theorem reached_11 : CarryCampaign.history c 11 = state11 := by
  change CarryCampaign.step c 11 (CarryCampaign.history c 10) = state11
  rw [reached_10]
  exact cold_11
theorem cold_12 : CarryCampaign.step c 12 state11 = state12 := by
  rw [CarryCampaign.step_eq_old c 12 _ (by decide +kernel)]
  exact UniformStickyColdPostfix.cold_12
theorem reached_12 : CarryCampaign.history c 12 = state12 := by
  change CarryCampaign.step c 12 (CarryCampaign.history c 11) = state12
  rw [reached_11]
  exact cold_12
theorem cold_13 : CarryCampaign.step c 13 state12 = state13 := by
  rw [CarryCampaign.step_eq_old c 13 _ (by decide +kernel)]
  exact UniformStickyColdPostfix.cold_13
theorem reached_13 : CarryCampaign.history c 13 = state13 := by
  change CarryCampaign.step c 13 (CarryCampaign.history c 12) = state13
  rw [reached_12]
  exact cold_13
theorem cold_14 : CarryCampaign.step c 14 state13 = state14 := by
  rw [CarryCampaign.step_eq_old c 14 _ (by decide +kernel)]
  exact UniformStickyColdPostfix.cold_14
theorem reached_14 : CarryCampaign.history c 14 = state14 := by
  change CarryCampaign.step c 14 (CarryCampaign.history c 13) = state14
  rw [reached_13]
  exact cold_14
theorem natural_stop_and_expected_observation : UniformCampaign.stopped 13 state13 = true ∧ state13.report = c.expected := UniformStickyColdPostfix.natural_stop_and_expected_observation
theorem final_is_quiet : state14 = UniformCampaign.quiet c c.expected state14.saved := UniformStickyColdPostfix.final_is_quiet
theorem uncapped_no_revival (n : Nat) : CarryCampaign.history c (n+14) = state14 := by
  induction n with
  | zero => exact reached_14
  | succ n ih =>
      change CarryCampaign.step c (n+15) (CarryCampaign.history c (n+14)) = state14
      rw [ih,final_is_quiet]
      exact CarryCampaign.quiet_never_restarts c _ _ _
end CarryOldPostfix

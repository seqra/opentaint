import HeadCampaign
import UniformStickyColdPostfix
namespace HeadOldPostfix
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
theorem cold_1 : HeadCampaign.step c 1 state0 = state1 := by
  rw [HeadCampaign.step_eq_old c 1 _ (by decide +kernel)]
  exact UniformStickyColdPostfix.cold_1
theorem reached_1 : HeadCampaign.history c 1 = state1 := by
  change HeadCampaign.step c 1 (HeadCampaign.history c 0) = state1
  change HeadCampaign.step c 1 state0 = state1
  exact cold_1
theorem cold_2 : HeadCampaign.step c 2 state1 = state2 := by
  rw [HeadCampaign.step_eq_old c 2 _ (by decide +kernel)]
  exact UniformStickyColdPostfix.cold_2
theorem reached_2 : HeadCampaign.history c 2 = state2 := by
  change HeadCampaign.step c 2 (HeadCampaign.history c 1) = state2
  rw [reached_1]
  exact cold_2
theorem cold_3 : HeadCampaign.step c 3 state2 = state3 := by
  rw [HeadCampaign.step_eq_old c 3 _ (by decide +kernel)]
  exact UniformStickyColdPostfix.cold_3
theorem reached_3 : HeadCampaign.history c 3 = state3 := by
  change HeadCampaign.step c 3 (HeadCampaign.history c 2) = state3
  rw [reached_2]
  exact cold_3
theorem cold_4 : HeadCampaign.step c 4 state3 = state4 := by
  rw [HeadCampaign.step_eq_old c 4 _ (by decide +kernel)]
  exact UniformStickyColdPostfix.cold_4
theorem reached_4 : HeadCampaign.history c 4 = state4 := by
  change HeadCampaign.step c 4 (HeadCampaign.history c 3) = state4
  rw [reached_3]
  exact cold_4
theorem cold_5 : HeadCampaign.step c 5 state4 = state5 := by
  rw [HeadCampaign.step_eq_old c 5 _ (by decide +kernel)]
  exact UniformStickyColdPostfix.cold_5
theorem reached_5 : HeadCampaign.history c 5 = state5 := by
  change HeadCampaign.step c 5 (HeadCampaign.history c 4) = state5
  rw [reached_4]
  exact cold_5
theorem cold_6 : HeadCampaign.step c 6 state5 = state6 := by
  rw [HeadCampaign.step_eq_old c 6 _ (by decide +kernel)]
  exact UniformStickyColdPostfix.cold_6
theorem reached_6 : HeadCampaign.history c 6 = state6 := by
  change HeadCampaign.step c 6 (HeadCampaign.history c 5) = state6
  rw [reached_5]
  exact cold_6
theorem cold_7 : HeadCampaign.step c 7 state6 = state7 := by
  rw [HeadCampaign.step_eq_old c 7 _ (by decide +kernel)]
  exact UniformStickyColdPostfix.cold_7
theorem reached_7 : HeadCampaign.history c 7 = state7 := by
  change HeadCampaign.step c 7 (HeadCampaign.history c 6) = state7
  rw [reached_6]
  exact cold_7
theorem cold_8 : HeadCampaign.step c 8 state7 = state8 := by
  rw [HeadCampaign.step_eq_old c 8 _ (by decide +kernel)]
  exact UniformStickyColdPostfix.cold_8
theorem reached_8 : HeadCampaign.history c 8 = state8 := by
  change HeadCampaign.step c 8 (HeadCampaign.history c 7) = state8
  rw [reached_7]
  exact cold_8
theorem cold_9 : HeadCampaign.step c 9 state8 = state9 := by
  rw [HeadCampaign.step_eq_old c 9 _ (by decide +kernel)]
  exact UniformStickyColdPostfix.cold_9
theorem reached_9 : HeadCampaign.history c 9 = state9 := by
  change HeadCampaign.step c 9 (HeadCampaign.history c 8) = state9
  rw [reached_8]
  exact cold_9
theorem cold_10 : HeadCampaign.step c 10 state9 = state10 := by
  rw [HeadCampaign.step_eq_old c 10 _ (by decide +kernel)]
  exact UniformStickyColdPostfix.cold_10
theorem reached_10 : HeadCampaign.history c 10 = state10 := by
  change HeadCampaign.step c 10 (HeadCampaign.history c 9) = state10
  rw [reached_9]
  exact cold_10
theorem cold_11 : HeadCampaign.step c 11 state10 = state11 := by
  rw [HeadCampaign.step_eq_old c 11 _ (by decide +kernel)]
  exact UniformStickyColdPostfix.cold_11
theorem reached_11 : HeadCampaign.history c 11 = state11 := by
  change HeadCampaign.step c 11 (HeadCampaign.history c 10) = state11
  rw [reached_10]
  exact cold_11
theorem cold_12 : HeadCampaign.step c 12 state11 = state12 := by
  rw [HeadCampaign.step_eq_old c 12 _ (by decide +kernel)]
  exact UniformStickyColdPostfix.cold_12
theorem reached_12 : HeadCampaign.history c 12 = state12 := by
  change HeadCampaign.step c 12 (HeadCampaign.history c 11) = state12
  rw [reached_11]
  exact cold_12
theorem cold_13 : HeadCampaign.step c 13 state12 = state13 := by
  rw [HeadCampaign.step_eq_old c 13 _ (by decide +kernel)]
  exact UniformStickyColdPostfix.cold_13
theorem reached_13 : HeadCampaign.history c 13 = state13 := by
  change HeadCampaign.step c 13 (HeadCampaign.history c 12) = state13
  rw [reached_12]
  exact cold_13
theorem cold_14 : HeadCampaign.step c 14 state13 = state14 := by
  rw [HeadCampaign.step_eq_old c 14 _ (by decide +kernel)]
  exact UniformStickyColdPostfix.cold_14
theorem reached_14 : HeadCampaign.history c 14 = state14 := by
  change HeadCampaign.step c 14 (HeadCampaign.history c 13) = state14
  rw [reached_13]
  exact cold_14
theorem natural_stop_and_expected_observation : UniformCampaign.stopped 13 state13 = true ∧ state13.report = c.expected := UniformStickyColdPostfix.natural_stop_and_expected_observation
theorem final_is_quiet : state14 = UniformCampaign.quiet c c.expected state14.saved := UniformStickyColdPostfix.final_is_quiet
theorem uncapped_no_revival (n : Nat) : HeadCampaign.history c (n+14) = state14 := by
  induction n with
  | zero => exact reached_14
  | succ n ih =>
      change HeadCampaign.step c (n+15) (HeadCampaign.history c (n+14)) = state14
      rw [ih,final_is_quiet]
      exact HeadCampaign.quiet_never_restarts c _ _ _
end HeadOldPostfix

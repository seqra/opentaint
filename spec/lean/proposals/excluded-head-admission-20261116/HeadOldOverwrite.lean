import HeadCampaign
import UniformStickyColdOverwrite
namespace HeadOldOverwrite
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
def c := UniformStickyColdOverwrite.c
def state0 := UniformStickyColdOverwrite.state0
def state1 := UniformStickyColdOverwrite.state1
def state2 := UniformStickyColdOverwrite.state2
def state3 := UniformStickyColdOverwrite.state3
def state4 := UniformStickyColdOverwrite.state4
def state5 := UniformStickyColdOverwrite.state5
def state6 := UniformStickyColdOverwrite.state6
def state7 := UniformStickyColdOverwrite.state7
def state8 := UniformStickyColdOverwrite.state8
def state9 := UniformStickyColdOverwrite.state9
def state10 := UniformStickyColdOverwrite.state10
theorem cold_1 : HeadCampaign.step c 1 state0 = state1 := by
  rw [HeadCampaign.step_eq_old c 1 _ (by decide +kernel)]
  exact UniformStickyColdOverwrite.cold_1
theorem reached_1 : HeadCampaign.history c 1 = state1 := by
  change HeadCampaign.step c 1 (HeadCampaign.history c 0) = state1
  change HeadCampaign.step c 1 state0 = state1
  exact cold_1
theorem cold_2 : HeadCampaign.step c 2 state1 = state2 := by
  rw [HeadCampaign.step_eq_old c 2 _ (by decide +kernel)]
  exact UniformStickyColdOverwrite.cold_2
theorem reached_2 : HeadCampaign.history c 2 = state2 := by
  change HeadCampaign.step c 2 (HeadCampaign.history c 1) = state2
  rw [reached_1]
  exact cold_2
theorem cold_3 : HeadCampaign.step c 3 state2 = state3 := by
  rw [HeadCampaign.step_eq_old c 3 _ (by decide +kernel)]
  exact UniformStickyColdOverwrite.cold_3
theorem reached_3 : HeadCampaign.history c 3 = state3 := by
  change HeadCampaign.step c 3 (HeadCampaign.history c 2) = state3
  rw [reached_2]
  exact cold_3
theorem cold_4 : HeadCampaign.step c 4 state3 = state4 := by
  rw [HeadCampaign.step_eq_old c 4 _ (by decide +kernel)]
  exact UniformStickyColdOverwrite.cold_4
theorem reached_4 : HeadCampaign.history c 4 = state4 := by
  change HeadCampaign.step c 4 (HeadCampaign.history c 3) = state4
  rw [reached_3]
  exact cold_4
theorem cold_5 : HeadCampaign.step c 5 state4 = state5 := by
  rw [HeadCampaign.step_eq_old c 5 _ (by decide +kernel)]
  exact UniformStickyColdOverwrite.cold_5
theorem reached_5 : HeadCampaign.history c 5 = state5 := by
  change HeadCampaign.step c 5 (HeadCampaign.history c 4) = state5
  rw [reached_4]
  exact cold_5
theorem cold_6 : HeadCampaign.step c 6 state5 = state6 := by
  rw [HeadCampaign.step_eq_old c 6 _ (by decide +kernel)]
  exact UniformStickyColdOverwrite.cold_6
theorem reached_6 : HeadCampaign.history c 6 = state6 := by
  change HeadCampaign.step c 6 (HeadCampaign.history c 5) = state6
  rw [reached_5]
  exact cold_6
theorem cold_7 : HeadCampaign.step c 7 state6 = state7 := by
  rw [HeadCampaign.step_eq_old c 7 _ (by decide +kernel)]
  exact UniformStickyColdOverwrite.cold_7
theorem reached_7 : HeadCampaign.history c 7 = state7 := by
  change HeadCampaign.step c 7 (HeadCampaign.history c 6) = state7
  rw [reached_6]
  exact cold_7
theorem cold_8 : HeadCampaign.step c 8 state7 = state8 := by
  rw [HeadCampaign.step_eq_old c 8 _ (by decide +kernel)]
  exact UniformStickyColdOverwrite.cold_8
theorem reached_8 : HeadCampaign.history c 8 = state8 := by
  change HeadCampaign.step c 8 (HeadCampaign.history c 7) = state8
  rw [reached_7]
  exact cold_8
theorem cold_9 : HeadCampaign.step c 9 state8 = state9 := by
  rw [HeadCampaign.step_eq_old c 9 _ (by decide +kernel)]
  exact UniformStickyColdOverwrite.cold_9
theorem reached_9 : HeadCampaign.history c 9 = state9 := by
  change HeadCampaign.step c 9 (HeadCampaign.history c 8) = state9
  rw [reached_8]
  exact cold_9
theorem cold_10 : HeadCampaign.step c 10 state9 = state10 := by
  rw [HeadCampaign.step_eq_old c 10 _ (by decide +kernel)]
  exact UniformStickyColdOverwrite.cold_10
theorem reached_10 : HeadCampaign.history c 10 = state10 := by
  change HeadCampaign.step c 10 (HeadCampaign.history c 9) = state10
  rw [reached_9]
  exact cold_10
theorem natural_stop_and_expected_observation : UniformCampaign.stopped 9 state9 = true ∧ state9.report = c.expected := UniformStickyColdOverwrite.natural_stop_and_expected_observation
theorem final_is_quiet : state10 = UniformCampaign.quiet c c.expected state10.saved := UniformStickyColdOverwrite.final_is_quiet
theorem uncapped_no_revival (n : Nat) : HeadCampaign.history c (n+10) = state10 := by
  induction n with
  | zero => exact reached_10
  | succ n ih =>
      change HeadCampaign.step c (n+11) (HeadCampaign.history c (n+10)) = state10
      rw [ih,final_is_quiet]
      exact HeadCampaign.quiet_never_restarts c _ _ _
end HeadOldOverwrite

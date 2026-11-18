import HeadCampaign
import UniformStickyColdNestedNegative
namespace HeadOldNestedNegative
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
def c := UniformStickyColdNestedNegative.c
def state0 := UniformStickyColdNestedNegative.state0
def state1 := UniformStickyColdNestedNegative.state1
def state2 := UniformStickyColdNestedNegative.state2
def state3 := UniformStickyColdNestedNegative.state3
def state4 := UniformStickyColdNestedNegative.state4
theorem cold_1 : HeadCampaign.step c 1 state0 = state1 := by
  rw [HeadCampaign.step_eq_old c 1 _ (by decide +kernel)]
  exact UniformStickyColdNestedNegative.cold_1
theorem reached_1 : HeadCampaign.history c 1 = state1 := by
  change HeadCampaign.step c 1 (HeadCampaign.history c 0) = state1
  change HeadCampaign.step c 1 state0 = state1
  exact cold_1
theorem cold_2 : HeadCampaign.step c 2 state1 = state2 := by
  rw [HeadCampaign.step_eq_old c 2 _ (by decide +kernel)]
  exact UniformStickyColdNestedNegative.cold_2
theorem reached_2 : HeadCampaign.history c 2 = state2 := by
  change HeadCampaign.step c 2 (HeadCampaign.history c 1) = state2
  rw [reached_1]
  exact cold_2
theorem cold_3 : HeadCampaign.step c 3 state2 = state3 := by
  rw [HeadCampaign.step_eq_old c 3 _ (by decide +kernel)]
  exact UniformStickyColdNestedNegative.cold_3
theorem reached_3 : HeadCampaign.history c 3 = state3 := by
  change HeadCampaign.step c 3 (HeadCampaign.history c 2) = state3
  rw [reached_2]
  exact cold_3
theorem cold_4 : HeadCampaign.step c 4 state3 = state4 := by
  rw [HeadCampaign.step_eq_old c 4 _ (by decide +kernel)]
  exact UniformStickyColdNestedNegative.cold_4
theorem reached_4 : HeadCampaign.history c 4 = state4 := by
  change HeadCampaign.step c 4 (HeadCampaign.history c 3) = state4
  rw [reached_3]
  exact cold_4
theorem natural_stop_and_expected_observation : UniformCampaign.stopped 3 state3 = true ∧ state3.report = c.expected := UniformStickyColdNestedNegative.natural_stop_and_expected_observation
theorem final_is_quiet : state4 = UniformCampaign.quiet c c.expected state4.saved := UniformStickyColdNestedNegative.final_is_quiet
theorem uncapped_no_revival (n : Nat) : HeadCampaign.history c (n+4) = state4 := by
  induction n with
  | zero => exact reached_4
  | succ n ih =>
      change HeadCampaign.step c (n+5) (HeadCampaign.history c (n+4)) = state4
      rw [ih,final_is_quiet]
      exact HeadCampaign.quiet_never_restarts c _ _ _
end HeadOldNestedNegative

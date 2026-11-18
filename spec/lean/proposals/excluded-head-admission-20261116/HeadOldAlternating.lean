import HeadAlternating
import UniformStickyColdAlternating
namespace HeadOldAlternating
open HeadAlternating
set_option maxRecDepth 32768
set_option maxHeartbeats 160000000
def state0 := initial
def state1 := UniformStickyColdAlternating.state1
def state2 := UniformStickyColdAlternating.state2
def state3 := UniformStickyColdAlternating.state3
def state4 := UniformStickyColdAlternating.state4
def state5 := UniformStickyColdAlternating.state5
def state6 := UniformStickyColdAlternating.state6
theorem cold_1 : step true 1 state0 = state1 := by decide +kernel
theorem quiescent_1 : round true 1 (limit 1) state0.rows state0.saved state1.data = state1.data := by decide +kernel
theorem reached_1 : history true 1 = state1 := by
  change step true 1 (history true 0) = state1
  change step true 1 state0 = state1
  exact cold_1
theorem cold_2 : step true 2 state1 = state2 := by decide +kernel
theorem quiescent_2 : round true 2 (limit 2) state1.rows state1.saved state2.data = state2.data := by decide +kernel
theorem reached_2 : history true 2 = state2 := by
  change step true 2 (history true 1) = state2
  rw [reached_1]
  exact cold_2
theorem cold_3 : step true 3 state2 = state3 := by decide +kernel
theorem quiescent_3 : round true 3 (limit 3) state2.rows state2.saved state3.data = state3.data := by decide +kernel
theorem reached_3 : history true 3 = state3 := by
  change step true 3 (history true 2) = state3
  rw [reached_2]
  exact cold_3
theorem cold_4 : step true 4 state3 = state4 := by decide +kernel
theorem quiescent_4 : round true 4 (limit 4) state3.rows state3.saved state4.data = state4.data := by decide +kernel
theorem reached_4 : history true 4 = state4 := by
  change step true 4 (history true 3) = state4
  rw [reached_3]
  exact cold_4
theorem cold_5 : step true 5 state4 = state5 := by decide +kernel
theorem quiescent_5 : round true 5 (limit 5) state4.rows state4.saved state5.data = state5.data := by decide +kernel
theorem reached_5 : history true 5 = state5 := by
  change step true 5 (history true 4) = state5
  rw [reached_4]
  exact cold_5
theorem cold_6 : step true 6 state5 = state6 := by decide +kernel
theorem quiescent_6 : round true 6 (limit 6) state5.rows state5.saved state6.data = state6.data := by decide +kernel
theorem reached_6 : history true 6 = state6 := by
  change step true 6 (history true 5) = state6
  rw [reached_5]
  exact cold_6
theorem stop_run5_with_the_normal_observation : stopped 5 state5 = true ∧ state3.report = true := by decide +kernel

theorem final_is_quiet : state6 = quiet true state6.saved := by decide +kernel

theorem uncapped_no_revival (n : Nat) : history true (n+6) = state6 := by
  induction n with
  | zero => exact reached_6
  | succ n ih =>
      change step true (n+7) (history true (n+6)) = state6
      rw [ih,final_is_quiet]
      exact quiet_never_restarts true _ _ _
end HeadOldAlternating

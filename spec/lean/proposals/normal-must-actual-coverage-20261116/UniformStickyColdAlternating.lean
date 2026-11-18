import UniformSticky

import UniformColdAlternating

namespace UniformStickyColdAlternating

open NonEmptyPolicy NonEmptyRestriction

set_option maxRecDepth 32768

set_option maxHeartbeats 160000000

def state0 := UniformColdAlternating.state0

def state1 := UniformColdAlternating.state1

theorem cold_1 : UniformSticky.newStep 1 state0 = state1 := by
  exact UniformSticky.from_checked_new_data_step 1 _ _ UniformColdAlternating.cold_1 (by decide)

theorem reached_1 : UniformSticky.newHistory 1 = state1 := by
  change UniformSticky.newStep 1 (UniformSticky.newHistory 0) = state1
  change UniformSticky.newStep 1 state0 = state1
  exact cold_1

def state2 := UniformColdAlternating.state2

theorem cold_2 : UniformSticky.newStep 2 state1 = state2 := by
  exact UniformSticky.from_checked_new_data_step 2 _ _ UniformColdAlternating.cold_2 (by decide)

theorem reached_2 : UniformSticky.newHistory 2 = state2 := by
  change UniformSticky.newStep 2 (UniformSticky.newHistory 1) = state2
  rw [reached_1]
  exact cold_2

def state3 := UniformColdAlternating.state3

theorem cold_3 : UniformSticky.newStep 3 state2 = state3 := by
  exact UniformSticky.from_checked_new_data_step 3 _ _ UniformColdAlternating.cold_3 (by decide)

theorem reached_3 : UniformSticky.newHistory 3 = state3 := by
  change UniformSticky.newStep 3 (UniformSticky.newHistory 2) = state3
  rw [reached_2]
  exact cold_3

def state4 := UniformColdAlternating.state4

theorem cold_4 : UniformSticky.newStep 4 state3 = state4 := by
  exact UniformSticky.from_checked_new_data_step 4 _ _ UniformColdAlternating.cold_4 (by decide)

theorem reached_4 : UniformSticky.newHistory 4 = state4 := by
  change UniformSticky.newStep 4 (UniformSticky.newHistory 3) = state4
  rw [reached_3]
  exact cold_4

def state5 := UniformColdAlternating.state5

theorem cold_5 : UniformSticky.newStep 5 state4 = state5 := by
  exact UniformSticky.from_checked_new_data_step 5 _ _ UniformColdAlternating.cold_5 (by decide)

theorem reached_5 : UniformSticky.newHistory 5 = state5 := by
  change UniformSticky.newStep 5 (UniformSticky.newHistory 4) = state5
  rw [reached_4]
  exact cold_5

def state6 := UniformColdAlternating.state6

theorem cold_6 : UniformSticky.newStep 6 state5 = state6 := by
  exact UniformSticky.from_checked_new_data_step 6 _ _ UniformColdAlternating.cold_6 (by decide)

theorem reached_6 : UniformSticky.newHistory 6 = state6 := by
  change UniformSticky.newStep 6 (UniformSticky.newHistory 5) = state6
  rw [reached_5]
  exact cold_6

theorem new_case_stops_run5_with_the_real_normal_mark :
    UniformAlternating.stopped 5 state5 = true ∧ state5.report = true ∧
    state3.data.offers.getLast!.any (fun v => v.ap.mark == some 2 && !v.demand) = true := by decide

theorem no_target_is_forgotten_in_run3 : UniformSticky.newForwardDemand 3 state2 = false := by decide

theorem final_is_quiet : state6 = UniformAlternating.quiet true state6.saved := by decide

theorem uncapped_no_revival (n : Nat) : UniformSticky.newHistory (n+6) = state6 := by
  induction n with
  | zero => exact reached_6
  | succ n ih =>
      change UniformSticky.newStep (n+7) (UniformSticky.newHistory (n+6)) = state6
      rw [ih,final_is_quiet]
      exact UniformSticky.new_quiet_still_has_no_work _ _ _

end UniformStickyColdAlternating

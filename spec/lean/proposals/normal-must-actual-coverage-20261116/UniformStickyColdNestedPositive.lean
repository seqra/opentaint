import UniformSticky

import UniformColdNestedPositive

namespace UniformStickyColdNestedPositive

open NonEmptyPolicy NonEmptyRestriction

set_option maxRecDepth 32768

set_option maxHeartbeats 160000000

def c := UniformColdNestedPositive.c

def state0 := UniformColdNestedPositive.state0

def state1 : UniformCampaign.State := UniformColdNestedPositive.state1

theorem cold_1 : UniformSticky.step c 1 state0 = state1 := by
  exact UniformSticky.from_checked_data_step c 1 _ _ UniformColdNestedPositive.cold_1 (by decide)

theorem quiescent_1 : UniformReplay.round 1 (UniformCampaign.limit 1) c.calls c.methods state0.rows state0.saved state1.data = state1.data := by
  first | exact UniformColdNestedPositive.quiescent_1 | decide

theorem reached_1 : UniformSticky.history c 1 = state1 := by
  change UniformSticky.step c 1 (UniformSticky.history c 0) = state1
  change UniformSticky.step c 1 state0 = state1
  exact cold_1

def state2 : UniformCampaign.State := UniformColdNestedPositive.state2

theorem cold_2 : UniformSticky.step c 2 state1 = state2 := by
  exact UniformSticky.from_checked_data_step c 2 _ _ UniformColdNestedPositive.cold_2 (by decide)

theorem quiescent_2 : UniformReplay.round 2 (UniformCampaign.limit 2) c.calls c.methods state1.rows state1.saved state2.data = state2.data := by
  first | exact UniformColdNestedPositive.quiescent_2 | decide

theorem reached_2 : UniformSticky.history c 2 = state2 := by
  change UniformSticky.step c 2 (UniformSticky.history c 1) = state2
  rw [reached_1]
  exact cold_2

def state3 : UniformCampaign.State := UniformColdNestedPositive.state3

theorem cold_3 : UniformSticky.step c 3 state2 = state3 := by
  exact UniformSticky.from_checked_data_step c 3 _ _ UniformColdNestedPositive.cold_3 (by decide)

theorem quiescent_3 : UniformReplay.round 3 (UniformCampaign.limit 3) c.calls c.methods state2.rows state2.saved state3.data = state3.data := by
  first | exact UniformColdNestedPositive.quiescent_3 | decide

theorem reached_3 : UniformSticky.history c 3 = state3 := by
  change UniformSticky.step c 3 (UniformSticky.history c 2) = state3
  rw [reached_2]
  exact cold_3

def state4 : UniformCampaign.State := UniformColdNestedPositive.state4

theorem cold_4 : UniformSticky.step c 4 state3 = state4 := by
  exact UniformSticky.from_checked_data_step c 4 _ _ UniformColdNestedPositive.cold_4 (by decide)

theorem quiescent_4 : UniformReplay.round 4 (UniformCampaign.limit 4) c.calls c.methods state3.rows state3.saved state4.data = state4.data := by
  first | exact UniformColdNestedPositive.quiescent_4 | decide

theorem reached_4 : UniformSticky.history c 4 = state4 := by
  change UniformSticky.step c 4 (UniformSticky.history c 3) = state4
  rw [reached_3]
  exact cold_4

theorem natural_stop_and_expected_observation : UniformCampaign.stopped 3 state3 = true ∧ state3.report = c.expected := by decide

theorem no_earlier_stop : ([(1,state1),(2,state2)].all (fun x => !(UniformCampaign.stopped x.1 x.2))) = true := by decide

theorem final_is_quiet : state4 = UniformCampaign.quiet c c.expected state4.saved := by decide

theorem uncapped_no_revival (n : Nat) : UniformSticky.history c (n+4) = state4 := by
  induction n with
  | zero => exact reached_4
  | succ n ih =>
      change UniformSticky.step c (n+5) (UniformSticky.history c (n+4)) = state4
      rw [ih,final_is_quiet]
      exact UniformSticky.quiet_still_has_no_new_work c _ _ _

end UniformStickyColdNestedPositive

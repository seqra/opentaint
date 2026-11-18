import UniformSticky

import UniformColdOverwrite

namespace UniformStickyColdOverwrite

open NonEmptyPolicy NonEmptyRestriction

set_option maxRecDepth 32768

set_option maxHeartbeats 160000000

def c := UniformColdOverwrite.c

def state0 := UniformColdOverwrite.state0

def state1 : UniformCampaign.State := UniformColdOverwrite.state1

theorem cold_1 : UniformSticky.step c 1 state0 = state1 := by
  exact UniformSticky.from_checked_data_step c 1 _ _ UniformColdOverwrite.cold_1 (by decide)

theorem quiescent_1 : UniformReplay.round 1 (UniformCampaign.limit 1) c.calls c.methods state0.rows state0.saved state1.data = state1.data := by
  exact UniformColdOverwrite.quiescent_1

theorem reached_1 : UniformSticky.history c 1 = state1 := by
  change UniformSticky.step c 1 (UniformSticky.history c 0) = state1
  change UniformSticky.step c 1 state0 = state1
  exact cold_1

def state2 : UniformCampaign.State := UniformColdOverwrite.state2

theorem cold_2 : UniformSticky.step c 2 state1 = state2 := by
  exact UniformSticky.from_checked_data_step c 2 _ _ UniformColdOverwrite.cold_2 (by decide)

theorem quiescent_2 : UniformReplay.round 2 (UniformCampaign.limit 2) c.calls c.methods state1.rows state1.saved state2.data = state2.data := by
  exact UniformColdOverwrite.quiescent_2

theorem reached_2 : UniformSticky.history c 2 = state2 := by
  change UniformSticky.step c 2 (UniformSticky.history c 1) = state2
  rw [reached_1]
  exact cold_2

def state3 : UniformCampaign.State := UniformColdOverwrite.state3

theorem cold_3 : UniformSticky.step c 3 state2 = state3 := by
  exact UniformSticky.from_checked_data_step c 3 _ _ UniformColdOverwrite.cold_3 (by decide)

theorem quiescent_3 : UniformReplay.round 3 (UniformCampaign.limit 3) c.calls c.methods state2.rows state2.saved state3.data = state3.data := by
  exact UniformColdOverwrite.quiescent_3

theorem reached_3 : UniformSticky.history c 3 = state3 := by
  change UniformSticky.step c 3 (UniformSticky.history c 2) = state3
  rw [reached_2]
  exact cold_3

def state4 : UniformCampaign.State := UniformColdOverwrite.state4

theorem cold_4 : UniformSticky.step c 4 state3 = state4 := by
  exact UniformSticky.from_checked_data_step c 4 _ _ UniformColdOverwrite.cold_4 (by decide)

theorem quiescent_4 : UniformReplay.round 4 (UniformCampaign.limit 4) c.calls c.methods state3.rows state3.saved state4.data = state4.data := by
  exact UniformColdOverwrite.quiescent_4

theorem reached_4 : UniformSticky.history c 4 = state4 := by
  change UniformSticky.step c 4 (UniformSticky.history c 3) = state4
  rw [reached_3]
  exact cold_4

def state5 : UniformCampaign.State := UniformColdOverwrite.state5

theorem cold_5 : UniformSticky.step c 5 state4 = state5 := by
  exact UniformSticky.from_checked_data_step c 5 _ _ UniformColdOverwrite.cold_5 (by decide)

theorem quiescent_5 : UniformReplay.round 5 (UniformCampaign.limit 5) c.calls c.methods state4.rows state4.saved state5.data = state5.data := by
  exact UniformColdOverwrite.quiescent_5

theorem reached_5 : UniformSticky.history c 5 = state5 := by
  change UniformSticky.step c 5 (UniformSticky.history c 4) = state5
  rw [reached_4]
  exact cold_5

def state6 : UniformCampaign.State := UniformColdOverwrite.state6

theorem cold_6 : UniformSticky.step c 6 state5 = state6 := by
  exact UniformSticky.from_checked_data_step c 6 _ _ UniformColdOverwrite.cold_6 (by decide)

theorem quiescent_6 : UniformReplay.round 6 (UniformCampaign.limit 6) c.calls c.methods state5.rows state5.saved state6.data = state6.data := by
  exact UniformColdOverwrite.quiescent_6

theorem reached_6 : UniformSticky.history c 6 = state6 := by
  change UniformSticky.step c 6 (UniformSticky.history c 5) = state6
  rw [reached_5]
  exact cold_6

def state7 : UniformCampaign.State := UniformColdOverwrite.state7

theorem cold_7 : UniformSticky.step c 7 state6 = state7 := by
  exact UniformSticky.from_checked_data_step c 7 _ _ UniformColdOverwrite.cold_7 (by decide)

theorem quiescent_7 : UniformReplay.round 7 (UniformCampaign.limit 7) c.calls c.methods state6.rows state6.saved state7.data = state7.data := by
  exact UniformColdOverwrite.quiescent_7

theorem reached_7 : UniformSticky.history c 7 = state7 := by
  change UniformSticky.step c 7 (UniformSticky.history c 6) = state7
  rw [reached_6]
  exact cold_7

def state8 : UniformCampaign.State := UniformColdOverwrite.state8

theorem cold_8 : UniformSticky.step c 8 state7 = state8 := by
  exact UniformSticky.from_checked_data_step c 8 _ _ UniformColdOverwrite.cold_8 (by decide)

theorem quiescent_8 : UniformReplay.round 8 (UniformCampaign.limit 8) c.calls c.methods state7.rows state7.saved state8.data = state8.data := by
  exact UniformColdOverwrite.quiescent_8

theorem reached_8 : UniformSticky.history c 8 = state8 := by
  change UniformSticky.step c 8 (UniformSticky.history c 7) = state8
  rw [reached_7]
  exact cold_8

def state9 : UniformCampaign.State := UniformColdOverwrite.state9

theorem cold_9 : UniformSticky.step c 9 state8 = state9 := by
  exact UniformSticky.from_checked_data_step c 9 _ _ UniformColdOverwrite.cold_9 (by decide)

theorem quiescent_9 : UniformReplay.round 9 (UniformCampaign.limit 9) c.calls c.methods state8.rows state8.saved state9.data = state9.data := by
  exact UniformColdOverwrite.quiescent_9

theorem reached_9 : UniformSticky.history c 9 = state9 := by
  change UniformSticky.step c 9 (UniformSticky.history c 8) = state9
  rw [reached_8]
  exact cold_9

def state10 : UniformCampaign.State := UniformColdOverwrite.state10

theorem cold_10 : UniformSticky.step c 10 state9 = state10 := by
  exact UniformSticky.from_checked_data_step c 10 _ _ UniformColdOverwrite.cold_10 (by decide)

theorem quiescent_10 : UniformReplay.round 10 (UniformCampaign.limit 10) c.calls c.methods state9.rows state9.saved state10.data = state10.data := by
  exact UniformColdOverwrite.quiescent_10

theorem reached_10 : UniformSticky.history c 10 = state10 := by
  change UniformSticky.step c 10 (UniformSticky.history c 9) = state10
  rw [reached_9]
  exact cold_10

theorem natural_stop_and_expected_observation : UniformCampaign.stopped 9 state9 = true ∧ state9.report = c.expected := by decide

theorem no_earlier_stop : ([(1,state1),(2,state2),(3,state3),(4,state4),(5,state5),(6,state6),(7,state7),(8,state8)].all (fun x => !(UniformCampaign.stopped x.1 x.2))) = true := by decide

theorem final_is_quiet : state10 = UniformCampaign.quiet c c.expected state10.saved := by decide

theorem uncapped_no_revival (n : Nat) : UniformSticky.history c (n+10) = state10 := by
  induction n with
  | zero => exact reached_10
  | succ n ih =>
      change UniformSticky.step c (n+11) (UniformSticky.history c (n+10)) = state10
      rw [ih,final_is_quiet]
      exact UniformSticky.quiet_still_has_no_new_work c _ _ _

end UniformStickyColdOverwrite

import UniformSticky

import UniformColdNestedLarger

namespace UniformStickyColdNestedLarger

open NonEmptyPolicy NonEmptyRestriction

set_option maxRecDepth 32768

set_option maxHeartbeats 160000000

def c := UniformColdNestedLarger.c

def state0 := UniformColdNestedLarger.state0

def state1 : UniformCampaign.State := UniformColdNestedLarger.state1

theorem cold_1 : UniformSticky.step c 1 state0 = state1 := by
  exact UniformSticky.from_checked_data_step c 1 _ _ UniformColdNestedLarger.cold_1 (by decide)

theorem quiescent_1 : UniformReplay.round 1 (UniformCampaign.limit 1) c.calls c.methods state0.rows state0.saved state1.data = state1.data := by
  first | exact UniformColdNestedLarger.quiescent_1 | decide

theorem reached_1 : UniformSticky.history c 1 = state1 := by
  change UniformSticky.step c 1 (UniformSticky.history c 0) = state1
  change UniformSticky.step c 1 state0 = state1
  exact cold_1

def state2 : UniformCampaign.State := UniformColdNestedLarger.state2

theorem cold_2 : UniformSticky.step c 2 state1 = state2 := by
  exact UniformSticky.from_checked_data_step c 2 _ _ UniformColdNestedLarger.cold_2 (by decide)

theorem quiescent_2 : UniformReplay.round 2 (UniformCampaign.limit 2) c.calls c.methods state1.rows state1.saved state2.data = state2.data := by
  first | exact UniformColdNestedLarger.quiescent_2 | decide

theorem reached_2 : UniformSticky.history c 2 = state2 := by
  change UniformSticky.step c 2 (UniformSticky.history c 1) = state2
  rw [reached_1]
  exact cold_2

def state3 : UniformCampaign.State := UniformColdNestedLarger.state3

theorem cold_3 : UniformSticky.step c 3 state2 = state3 := by
  exact UniformSticky.from_checked_data_step c 3 _ _ UniformColdNestedLarger.cold_3 (by decide)

theorem quiescent_3 : UniformReplay.round 3 (UniformCampaign.limit 3) c.calls c.methods state2.rows state2.saved state3.data = state3.data := by
  first | exact UniformColdNestedLarger.quiescent_3 | decide

theorem reached_3 : UniformSticky.history c 3 = state3 := by
  change UniformSticky.step c 3 (UniformSticky.history c 2) = state3
  rw [reached_2]
  exact cold_3

def state4 : UniformCampaign.State := UniformColdNestedLarger.state4

theorem cold_4 : UniformSticky.step c 4 state3 = state4 := by
  exact UniformSticky.from_checked_data_step c 4 _ _ UniformColdNestedLarger.cold_4 (by decide)

theorem quiescent_4 : UniformReplay.round 4 (UniformCampaign.limit 4) c.calls c.methods state3.rows state3.saved state4.data = state4.data := by
  first | exact UniformColdNestedLarger.quiescent_4 | decide

theorem reached_4 : UniformSticky.history c 4 = state4 := by
  change UniformSticky.step c 4 (UniformSticky.history c 3) = state4
  rw [reached_3]
  exact cold_4

def state5 : UniformCampaign.State := UniformColdNestedLarger.state5

theorem cold_5 : UniformSticky.step c 5 state4 = state5 := by
  exact UniformSticky.from_checked_data_step c 5 _ _ UniformColdNestedLarger.cold_5 (by decide)

theorem quiescent_5 : UniformReplay.round 5 (UniformCampaign.limit 5) c.calls c.methods state4.rows state4.saved state5.data = state5.data := by
  first | exact UniformColdNestedLarger.quiescent_5 | decide

theorem reached_5 : UniformSticky.history c 5 = state5 := by
  change UniformSticky.step c 5 (UniformSticky.history c 4) = state5
  rw [reached_4]
  exact cold_5

def state6 : UniformCampaign.State := UniformColdNestedLarger.state6

theorem cold_6 : UniformSticky.step c 6 state5 = state6 := by
  exact UniformSticky.from_checked_data_step c 6 _ _ UniformColdNestedLarger.cold_6 (by decide)

theorem quiescent_6 : UniformReplay.round 6 (UniformCampaign.limit 6) c.calls c.methods state5.rows state5.saved state6.data = state6.data := by
  first | exact UniformColdNestedLarger.quiescent_6 | decide

theorem reached_6 : UniformSticky.history c 6 = state6 := by
  change UniformSticky.step c 6 (UniformSticky.history c 5) = state6
  rw [reached_5]
  exact cold_6

def state7 : UniformCampaign.State := ⟨[[⟨⟨0,[1,1],.may,none,[],[]⟩,⟨1,[1,1],.star,none,[],[]⟩⟩]],[[⟨(⟨0,[1,1],.star,none,[],[]⟩,⟨⟨1,[],.star,none,[1],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.star,none,[],[]⟩,⟨⟨1,[1,1],.star,none,[1],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1,1,1],.star,none,[],[]⟩,⟨⟨1,[1],.star,none,[2],[]⟩,false,false⟩),true⟩,⟨(⟨0,[1],.star,none,[],[]⟩,⟨⟨1,[1,1,1],.star,none,[2],[]⟩,false,false⟩),false⟩]],true,true,true,⟨[[⟨⟨0,[],.may,some 7,[1],[]⟩,true⟩,⟨⟨0,[2],.must,some 7,[],[]⟩,false⟩,⟨⟨0,[1,1],.may,some 7,[],[]⟩,true⟩,⟨⟨0,[1,1,2],.must,some 7,[],[]⟩,false⟩,⟨⟨0,[1,1,1,1,2],.must,some 7,[],[]⟩,false⟩,⟨⟨0,[1,1,1,1,1,1],.ne,some 7,[],[]⟩,true⟩]],[[(⟨0,[1,1],.star,none,[],[]⟩,⟨⟨1,[1,1],.may,none,[],[]⟩,true,false⟩)]],[[⟨⟨0,[1,1,2],.must,some 7,[],[]⟩,false⟩],[⟨⟨0,[2],.must,some 7,[],[]⟩,false⟩,⟨⟨0,[1,1],.may,some 7,[],[]⟩,true⟩,⟨⟨0,[1,1,1,1,2],.must,some 7,[],[]⟩,false⟩],[⟨⟨0,[],.may,some 7,[1],[]⟩,true⟩,⟨⟨0,[1,1,2],.must,some 7,[],[]⟩,false⟩],[⟨⟨0,[2],.must,some 7,[],[]⟩,false⟩,⟨⟨0,[1,1,1,1,2],.must,some 7,[],[]⟩,false⟩]]⟩⟩

theorem cold_7 : UniformSticky.step c 7 state6 = state7 := by
  decide

theorem quiescent_7 : UniformReplay.round 7 (UniformCampaign.limit 7) c.calls c.methods state6.rows state6.saved state7.data = state7.data := by
  first | exact UniformColdNestedLarger.quiescent_7 | decide

theorem reached_7 : UniformSticky.history c 7 = state7 := by
  change UniformSticky.step c 7 (UniformSticky.history c 6) = state7
  rw [reached_6]
  exact cold_7

def state8 : UniformCampaign.State := ⟨[[]],[[⟨(⟨0,[1,1],.star,none,[],[]⟩,⟨⟨1,[],.star,none,[1],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.star,none,[],[]⟩,⟨⟨1,[1,1],.star,none,[1],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1,1,1],.star,none,[],[]⟩,⟨⟨1,[1],.star,none,[2],[]⟩,false,false⟩),true⟩,⟨(⟨0,[1],.star,none,[],[]⟩,⟨⟨1,[1,1,1],.star,none,[2],[]⟩,false,false⟩),false⟩]],true,false,true,⟨[[⟨⟨0,[],.may,some 7,[],[]⟩,true⟩]],[[]],[[⟨⟨0,[],.may,some 7,[],[]⟩,true⟩],[⟨⟨0,[],.may,some 7,[],[]⟩,true⟩],[⟨⟨0,[],.may,some 7,[],[]⟩,true⟩],[⟨⟨0,[],.may,some 7,[],[]⟩,true⟩]]⟩⟩

theorem cold_8 : UniformSticky.step c 8 state7 = state8 := by
  decide

theorem quiescent_8 : UniformReplay.round 8 (UniformCampaign.limit 8) c.calls c.methods state7.rows state7.saved state8.data = state8.data := by
  first | exact UniformColdNestedLarger.quiescent_8 | decide

theorem reached_8 : UniformSticky.history c 8 = state8 := by
  change UniformSticky.step c 8 (UniformSticky.history c 7) = state8
  rw [reached_7]
  exact cold_8

def state9 : UniformCampaign.State := ⟨[[]],[[⟨(⟨0,[1,1],.star,none,[],[]⟩,⟨⟨1,[],.star,none,[1],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.star,none,[],[]⟩,⟨⟨1,[1,1],.star,none,[1],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1,1,1],.star,none,[],[]⟩,⟨⟨1,[1],.star,none,[2],[]⟩,false,false⟩),true⟩,⟨(⟨0,[1],.star,none,[],[]⟩,⟨⟨1,[1,1,1],.star,none,[2],[]⟩,false,false⟩),false⟩]],true,true,true,⟨[[⟨⟨0,[2],.must,some 7,[],[]⟩,false⟩,⟨⟨0,[1,1,2],.must,some 7,[],[]⟩,false⟩,⟨⟨0,[1,1,1,1,2],.must,some 7,[],[]⟩,false⟩,⟨⟨0,[1,1,1,1,1,1,2],.must,some 7,[],[]⟩,false⟩]],[[]],[[⟨⟨0,[1,1,2],.must,some 7,[],[]⟩,false⟩],[⟨⟨0,[2],.must,some 7,[],[]⟩,false⟩,⟨⟨0,[1,1,1,1,2],.must,some 7,[],[]⟩,false⟩],[⟨⟨0,[1,1,2],.must,some 7,[],[]⟩,false⟩,⟨⟨0,[1,1,1,1,1,1,2],.must,some 7,[],[]⟩,false⟩],[⟨⟨0,[2],.must,some 7,[],[]⟩,false⟩,⟨⟨0,[1,1,1,1,2],.must,some 7,[],[]⟩,false⟩,⟨⟨0,[1,1,1,1,1,1,1,1],.ne,some 7,[],[]⟩,true⟩]]⟩⟩

theorem cold_9 : UniformSticky.step c 9 state8 = state9 := by
  decide

theorem quiescent_9 : UniformReplay.round 9 (UniformCampaign.limit 9) c.calls c.methods state8.rows state8.saved state9.data = state9.data := by
  first | exact UniformColdNestedLarger.quiescent_9 | decide

theorem reached_9 : UniformSticky.history c 9 = state9 := by
  change UniformSticky.step c 9 (UniformSticky.history c 8) = state9
  rw [reached_8]
  exact cold_9

def state10 : UniformCampaign.State := ⟨[[]],[[⟨(⟨0,[1,1],.star,none,[],[]⟩,⟨⟨1,[],.star,none,[1],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.star,none,[],[]⟩,⟨⟨1,[1,1],.star,none,[1],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1,1,1],.star,none,[],[]⟩,⟨⟨1,[1],.star,none,[2],[]⟩,false,false⟩),true⟩,⟨(⟨0,[1],.star,none,[],[]⟩,⟨⟨1,[1,1,1],.star,none,[2],[]⟩,false,false⟩),false⟩]],true,false,true,⟨[[⟨⟨0,[],.may,some 7,[],[]⟩,true⟩]],[[]],[[⟨⟨0,[],.may,some 7,[],[]⟩,true⟩],[⟨⟨0,[],.may,some 7,[],[]⟩,true⟩],[⟨⟨0,[],.may,some 7,[],[]⟩,true⟩],[⟨⟨0,[],.may,some 7,[],[]⟩,true⟩]]⟩⟩

theorem cold_10 : UniformSticky.step c 10 state9 = state10 := by
  decide

theorem quiescent_10 : UniformReplay.round 10 (UniformCampaign.limit 10) c.calls c.methods state9.rows state9.saved state10.data = state10.data := by
  first | exact UniformColdNestedLarger.quiescent_10 | decide

theorem reached_10 : UniformSticky.history c 10 = state10 := by
  change UniformSticky.step c 10 (UniformSticky.history c 9) = state10
  rw [reached_9]
  exact cold_10

def state11 : UniformCampaign.State := ⟨[[]],[[⟨(⟨0,[1,1],.star,none,[],[]⟩,⟨⟨1,[],.star,none,[1],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.star,none,[],[]⟩,⟨⟨1,[1,1],.star,none,[1],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1,1,1],.star,none,[],[]⟩,⟨⟨1,[1],.star,none,[2],[]⟩,false,false⟩),true⟩,⟨(⟨0,[1],.star,none,[],[]⟩,⟨⟨1,[1,1,1],.star,none,[2],[]⟩,false,false⟩),false⟩]],true,false,true,⟨[[⟨⟨0,[2],.must,some 7,[],[]⟩,false⟩,⟨⟨0,[1,1,2],.must,some 7,[],[]⟩,false⟩,⟨⟨0,[1,1,1,1,2],.must,some 7,[],[]⟩,false⟩,⟨⟨0,[1,1,1,1,1,1,2],.must,some 7,[],[]⟩,false⟩]],[[]],[[⟨⟨0,[1,1,2],.must,some 7,[],[]⟩,false⟩],[⟨⟨0,[2],.must,some 7,[],[]⟩,false⟩,⟨⟨0,[1,1,1,1,2],.must,some 7,[],[]⟩,false⟩],[⟨⟨0,[1,1,2],.must,some 7,[],[]⟩,false⟩,⟨⟨0,[1,1,1,1,1,1,2],.must,some 7,[],[]⟩,false⟩],[⟨⟨0,[2],.must,some 7,[],[]⟩,false⟩,⟨⟨0,[1,1,1,1,2],.must,some 7,[],[]⟩,false⟩,⟨⟨0,[1,1,1,1,1,1,1,1,2],.must,some 7,[],[]⟩,false⟩]]⟩⟩

theorem cold_11 : UniformSticky.step c 11 state10 = state11 := by
  decide

theorem quiescent_11 : UniformReplay.round 11 (UniformCampaign.limit 11) c.calls c.methods state10.rows state10.saved state11.data = state11.data := by decide

theorem reached_11 : UniformSticky.history c 11 = state11 := by
  change UniformSticky.step c 11 (UniformSticky.history c 10) = state11
  rw [reached_10]
  exact cold_11

def state12 : UniformCampaign.State := ⟨[[]],[[⟨(⟨0,[1,1],.star,none,[],[]⟩,⟨⟨1,[],.star,none,[1],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.star,none,[],[]⟩,⟨⟨1,[1,1],.star,none,[1],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1,1,1],.star,none,[],[]⟩,⟨⟨1,[1],.star,none,[2],[]⟩,false,false⟩),true⟩,⟨(⟨0,[1],.star,none,[],[]⟩,⟨⟨1,[1,1,1],.star,none,[2],[]⟩,false,false⟩),false⟩]],false,false,true,⟨[[]],[[]],[[],[],[],[]]⟩⟩

theorem cold_12 : UniformSticky.step c 12 state11 = state12 := by
  decide

theorem quiescent_12 : UniformReplay.round 12 (UniformCampaign.limit 12) c.calls c.methods state11.rows state11.saved state12.data = state12.data := by decide

theorem reached_12 : UniformSticky.history c 12 = state12 := by
  change UniformSticky.step c 12 (UniformSticky.history c 11) = state12
  rw [reached_11]
  exact cold_12

theorem natural_stop_and_expected_observation : UniformCampaign.stopped 11 state11 = true ∧ state11.report = c.expected := by decide

theorem no_earlier_stop : ([(1,state1),(2,state2),(3,state3),(4,state4),(5,state5),(6,state6),(7,state7),(8,state8),(9,state9),(10,state10)].all (fun x => !(UniformCampaign.stopped x.1 x.2))) = true := by decide

theorem final_is_quiet : state12 = UniformCampaign.quiet c c.expected state12.saved := by decide

theorem uncapped_no_revival (n : Nat) : UniformSticky.history c (n+12) = state12 := by
  induction n with
  | zero => exact reached_12
  | succ n ih =>
      change UniformSticky.step c (n+13) (UniformSticky.history c (n+12)) = state12
      rw [ih,final_is_quiet]
      exact UniformSticky.quiet_still_has_no_new_work c _ _ _

end UniformStickyColdNestedLarger

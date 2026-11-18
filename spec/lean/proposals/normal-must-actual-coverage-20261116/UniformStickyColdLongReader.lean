import UniformSticky

import UniformColdLongReader

namespace UniformStickyColdLongReader

open NonEmptyPolicy NonEmptyRestriction

set_option maxRecDepth 32768

set_option maxHeartbeats 160000000

def c := UniformColdLongReader.c

def state0 := UniformColdLongReader.state0

def state1 : UniformCampaign.State := UniformColdLongReader.state1

theorem cold_1 : UniformSticky.step c 1 state0 = state1 := by
  exact UniformSticky.from_checked_data_step c 1 _ _ UniformColdLongReader.cold_1 (by decide)

theorem quiescent_1 : UniformReplay.round 1 (UniformCampaign.limit 1) c.calls c.methods state0.rows state0.saved state1.data = state1.data := by
  first | exact UniformColdLongReader.quiescent_1 | decide

theorem reached_1 : UniformSticky.history c 1 = state1 := by
  change UniformSticky.step c 1 (UniformSticky.history c 0) = state1
  change UniformSticky.step c 1 state0 = state1
  exact cold_1

def state2 : UniformCampaign.State := UniformColdLongReader.state2

theorem cold_2 : UniformSticky.step c 2 state1 = state2 := by
  exact UniformSticky.from_checked_data_step c 2 _ _ UniformColdLongReader.cold_2 (by decide)

theorem quiescent_2 : UniformReplay.round 2 (UniformCampaign.limit 2) c.calls c.methods state1.rows state1.saved state2.data = state2.data := by
  first | exact UniformColdLongReader.quiescent_2 | decide

theorem reached_2 : UniformSticky.history c 2 = state2 := by
  change UniformSticky.step c 2 (UniformSticky.history c 1) = state2
  rw [reached_1]
  exact cold_2

def state3 : UniformCampaign.State := ⟨[[⟨⟨0,[1],.ne,none,[],[]⟩,⟨1,[1,1],.star,none,[],[]⟩⟩,⟨⟨0,[1,1],.ne,none,[],[]⟩,⟨1,[1,1],.star,none,[],[]⟩⟩]],[[⟨(⟨0,[],.star,none,[],[]⟩,⟨⟨1,[1],.star,none,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1],.must,none,[],[]⟩,⟨⟨1,[],.must,none,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1],.must,none,[],[]⟩,⟨⟨1,[1],.must,none,[],[]⟩,false,false⟩),false⟩]],true,true,true,⟨[[⟨⟨0,[],.must,some 7,[],[]⟩,false⟩,⟨⟨0,[1],.must,some 7,[],[]⟩,false⟩,⟨⟨0,[1,1],.must,some 7,[],[]⟩,false⟩]],[[(⟨0,[1],.must,none,[],[]⟩,⟨⟨1,[],.must,none,[],[]⟩,false,false⟩),(⟨0,[1],.must,none,[],[]⟩,⟨⟨1,[1],.must,none,[],[]⟩,false,false⟩),(⟨0,[1,1],.star,none,[],[]⟩,⟨⟨1,[1],.ne,none,[],[]⟩,true,false⟩),(⟨0,[1,1],.star,none,[],[]⟩,⟨⟨1,[1,1],.ne,none,[],[]⟩,true,false⟩)]],[[⟨⟨0,[1],.must,some 7,[],[]⟩,false⟩],[⟨⟨0,[],.must,some 7,[],[]⟩,false⟩],[⟨⟨0,[],.must,some 7,[],[]⟩,false⟩]]⟩⟩

theorem cold_3 : UniformSticky.step c 3 state2 = state3 := by
  decide

theorem quiescent_3 : UniformReplay.round 3 (UniformCampaign.limit 3) c.calls c.methods state2.rows state2.saved state3.data = state3.data := by
  first | exact UniformColdLongReader.quiescent_3 | decide

theorem reached_3 : UniformSticky.history c 3 = state3 := by
  change UniformSticky.step c 3 (UniformSticky.history c 2) = state3
  rw [reached_2]
  exact cold_3

def state4 : UniformCampaign.State := ⟨[[]],[[⟨(⟨0,[],.star,none,[],[]⟩,⟨⟨1,[1],.star,none,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1],.must,none,[],[]⟩,⟨⟨1,[],.must,none,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1],.must,none,[],[]⟩,⟨⟨1,[1],.must,none,[],[]⟩,false,false⟩),false⟩]],true,false,true,⟨[[⟨⟨0,[],.may,some 7,[],[]⟩,true⟩]],[[]],[[⟨⟨0,[],.may,some 7,[],[]⟩,true⟩],[⟨⟨0,[],.may,some 7,[],[]⟩,true⟩],[⟨⟨0,[],.may,some 7,[],[]⟩,true⟩]]⟩⟩

theorem cold_4 : UniformSticky.step c 4 state3 = state4 := by
  decide

theorem quiescent_4 : UniformReplay.round 4 (UniformCampaign.limit 4) c.calls c.methods state3.rows state3.saved state4.data = state4.data := by
  first | exact UniformColdLongReader.quiescent_4 | decide

theorem reached_4 : UniformSticky.history c 4 = state4 := by
  change UniformSticky.step c 4 (UniformSticky.history c 3) = state4
  rw [reached_3]
  exact cold_4

def state5 : UniformCampaign.State := ⟨[[]],[[⟨(⟨0,[],.star,none,[],[]⟩,⟨⟨1,[1],.star,none,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1],.must,none,[],[]⟩,⟨⟨1,[],.must,none,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1],.must,none,[],[]⟩,⟨⟨1,[1],.must,none,[],[]⟩,false,false⟩),false⟩]],true,false,true,⟨[[⟨⟨0,[],.must,some 7,[],[]⟩,false⟩,⟨⟨0,[1],.must,some 7,[],[]⟩,false⟩]],[[]],[[⟨⟨0,[1],.must,some 7,[],[]⟩,false⟩],[⟨⟨0,[],.must,some 7,[],[]⟩,false⟩],[⟨⟨0,[],.must,some 7,[],[]⟩,false⟩]]⟩⟩

theorem cold_5 : UniformSticky.step c 5 state4 = state5 := by
  decide

theorem quiescent_5 : UniformReplay.round 5 (UniformCampaign.limit 5) c.calls c.methods state4.rows state4.saved state5.data = state5.data := by
  first | exact UniformColdLongReader.quiescent_5 | decide

theorem reached_5 : UniformSticky.history c 5 = state5 := by
  change UniformSticky.step c 5 (UniformSticky.history c 4) = state5
  rw [reached_4]
  exact cold_5

def state6 : UniformCampaign.State := UniformColdLongReader.state6

theorem cold_6 : UniformSticky.step c 6 state5 = state6 := by
  decide

theorem quiescent_6 : UniformReplay.round 6 (UniformCampaign.limit 6) c.calls c.methods state5.rows state5.saved state6.data = state6.data := by
  first | exact UniformColdLongReader.quiescent_6 | decide

theorem reached_6 : UniformSticky.history c 6 = state6 := by
  change UniformSticky.step c 6 (UniformSticky.history c 5) = state6
  rw [reached_5]
  exact cold_6

theorem natural_stop_and_expected_observation : UniformCampaign.stopped 5 state5 = true ∧ state5.report = c.expected := by decide

theorem no_earlier_stop : ([(1,state1),(2,state2),(3,state3),(4,state4)].all (fun x => !(UniformCampaign.stopped x.1 x.2))) = true := by decide

theorem final_is_quiet : state6 = UniformCampaign.quiet c c.expected state6.saved := by decide

theorem uncapped_no_revival (n : Nat) : UniformSticky.history c (n+6) = state6 := by
  induction n with
  | zero => exact reached_6
  | succ n ih =>
      change UniformSticky.step c (n+7) (UniformSticky.history c (n+6)) = state6
      rw [ih,final_is_quiet]
      exact UniformSticky.quiet_still_has_no_new_work c _ _ _

end UniformStickyColdLongReader

import UniformCampaign

namespace UniformColdNestedLarger

open NonEmptyPolicy NonEmptyRestriction

set_option maxRecDepth 32768

set_option maxHeartbeats 160000000

def c : UniformCampaign.Case := (UniformCampaign.cases[6]!).2

def state0 := UniformCampaign.initial c

def state1 : UniformCampaign.State := ⟨[[⟨⟨0,[],.may,none,[],[]⟩,⟨1,[],.star,none,[],[]⟩⟩,⟨⟨0,[1],.ne,none,[],[]⟩,⟨1,[],.star,none,[],[]⟩⟩]],[[]],true,true,false,⟨[[⟨⟨0,[],.may,some 7,[],[]⟩,true⟩,⟨⟨0,[1],.ne,some 7,[],[]⟩,true⟩]],[[(⟨0,[],.star,none,[],[]⟩,⟨⟨1,[],.may,none,[],[]⟩,true,false⟩),(⟨0,[],.star,none,[],[]⟩,⟨⟨1,[1],.ne,none,[],[]⟩,true,false⟩)]],[[⟨⟨0,[1],.ne,some 7,[],[]⟩,true⟩],[⟨⟨0,[],.may,some 7,[],[]⟩,true⟩],[⟨⟨0,[],.may,some 7,[],[]⟩,true⟩],[⟨⟨0,[],.may,some 7,[],[]⟩,true⟩]]⟩⟩

theorem cold_1 : UniformCampaign.step c 1 state0 = state1 := by decide

theorem quiescent_1 : UniformReplay.round 1 (UniformCampaign.limit 1) c.calls c.methods state0.rows state0.saved state1.data = state1.data := by decide

theorem saved_1 : OverwriteReplay.outputSaved 1 state0.saved state1.data = state1.saved := by decide

theorem reached_1 : UniformCampaign.history c 1 = state1 := by
  change UniformCampaign.step c 1 (UniformCampaign.history c 0) = state1
  change UniformCampaign.step c 1 state0 = state1
  exact cold_1

def state2 : UniformCampaign.State := ⟨[[⟨⟨0,[],.may,none,[],[]⟩,⟨1,[1],.star,none,[],[]⟩⟩,⟨⟨0,[1],.ne,none,[],[]⟩,⟨1,[],.star,none,[],[]⟩⟩,⟨⟨0,[1],.ne,none,[],[]⟩,⟨1,[1],.star,none,[],[]⟩⟩]],[[]],true,false,false,⟨[[⟨⟨0,[],.may,some 7,[],[]⟩,true⟩]],[[(⟨0,[1],.star,none,[],[]⟩,⟨⟨1,[],.may,none,[],[]⟩,true,false⟩),(⟨0,[],.star,none,[],[]⟩,⟨⟨1,[1],.ne,none,[],[]⟩,true,false⟩),(⟨0,[1],.star,none,[],[]⟩,⟨⟨1,[1],.ne,none,[],[]⟩,true,false⟩)]],[[⟨⟨0,[],.may,some 7,[],[]⟩,true⟩],[⟨⟨0,[],.may,some 7,[],[]⟩,true⟩],[⟨⟨0,[],.may,some 7,[],[]⟩,true⟩],[⟨⟨0,[],.may,some 7,[],[]⟩,true⟩]]⟩⟩

theorem cold_2 : UniformCampaign.step c 2 state1 = state2 := by decide

theorem quiescent_2 : UniformReplay.round 2 (UniformCampaign.limit 2) c.calls c.methods state1.rows state1.saved state2.data = state2.data := by decide

theorem saved_2 : OverwriteReplay.outputSaved 2 state1.saved state2.data = state2.saved := by decide

theorem reached_2 : UniformCampaign.history c 2 = state2 := by
  change UniformCampaign.step c 2 (UniformCampaign.history c 1) = state2
  rw [reached_1]
  exact cold_2

def state3 : UniformCampaign.State := ⟨[[⟨⟨0,[],.may,none,[],[]⟩,⟨1,[1],.star,none,[],[]⟩⟩,⟨⟨0,[1],.may,none,[],[]⟩,⟨1,[1],.star,none,[],[]⟩⟩,⟨⟨0,[1],.ne,none,[],[]⟩,⟨1,[1],.star,none,[],[]⟩⟩,⟨⟨0,[1],.may,none,[],[]⟩,⟨1,[1,1],.star,none,[],[]⟩⟩,⟨⟨0,[1,1],.ne,none,[],[]⟩,⟨1,[1],.star,none,[],[]⟩⟩,⟨⟨0,[1],.ne,none,[],[]⟩,⟨1,[1,1],.star,none,[],[]⟩⟩,⟨⟨0,[1,1],.ne,none,[],[]⟩,⟨1,[1,1],.star,none,[],[]⟩⟩]],[[⟨(⟨0,[1,1],.star,none,[],[]⟩,⟨⟨1,[],.star,none,[1],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.star,none,[],[]⟩,⟨⟨1,[1,1],.star,none,[1],[]⟩,false,false⟩),false⟩]],true,true,false,⟨[[⟨⟨0,[],.may,some 7,[],[]⟩,true⟩,⟨⟨0,[],.ne,some 7,[1],[]⟩,true⟩,⟨⟨0,[1],.may,some 7,[],[]⟩,true⟩,⟨⟨0,[1,1],.ne,some 7,[],[]⟩,true⟩]],[[(⟨0,[1],.star,none,[],[]⟩,⟨⟨1,[],.may,none,[],[]⟩,true,false⟩),(⟨0,[1],.star,none,[],[]⟩,⟨⟨1,[1],.may,none,[],[]⟩,true,false⟩),(⟨0,[1],.star,none,[],[]⟩,⟨⟨1,[1],.ne,none,[],[]⟩,true,false⟩),(⟨0,[1,1],.star,none,[],[]⟩,⟨⟨1,[],.star,none,[1],[]⟩,false,false⟩),(⟨0,[],.star,none,[],[]⟩,⟨⟨1,[1,1],.star,none,[1],[]⟩,false,false⟩),(⟨0,[1,1],.star,none,[],[]⟩,⟨⟨1,[1],.may,none,[],[]⟩,true,false⟩),(⟨0,[1,1],.star,none,[],[]⟩,⟨⟨1,[1],.ne,none,[],[]⟩,true,false⟩),(⟨0,[1],.star,none,[],[]⟩,⟨⟨1,[1,1],.ne,none,[],[]⟩,true,false⟩),(⟨0,[1,1],.star,none,[],[]⟩,⟨⟨1,[1,1],.ne,none,[],[]⟩,true,false⟩)]],[[⟨⟨0,[1,1],.ne,some 7,[],[]⟩,true⟩],[⟨⟨0,[],.may,some 7,[],[]⟩,true⟩],[⟨⟨0,[],.may,some 7,[],[]⟩,true⟩],[⟨⟨0,[],.may,some 7,[],[]⟩,true⟩]]⟩⟩

theorem cold_3 : UniformCampaign.step c 3 state2 = state3 := by decide

theorem quiescent_3 : UniformReplay.round 3 (UniformCampaign.limit 3) c.calls c.methods state2.rows state2.saved state3.data = state3.data := by decide

theorem saved_3 : OverwriteReplay.outputSaved 3 state2.saved state3.data = state3.saved := by decide

theorem reached_3 : UniformCampaign.history c 3 = state3 := by
  change UniformCampaign.step c 3 (UniformCampaign.history c 2) = state3
  rw [reached_2]
  exact cold_3

def state4 : UniformCampaign.State := ⟨[[⟨⟨0,[1],.may,none,[],[]⟩,⟨1,[1],.star,none,[],[]⟩⟩,⟨⟨0,[1,1],.may,none,[],[]⟩,⟨1,[1],.star,none,[],[]⟩⟩,⟨⟨0,[1],.may,none,[],[]⟩,⟨1,[1,1],.star,none,[],[]⟩⟩,⟨⟨0,[1,1],.ne,none,[],[]⟩,⟨1,[1],.star,none,[],[]⟩⟩,⟨⟨0,[1,1],.may,none,[],[]⟩,⟨1,[1,1],.star,none,[],[]⟩⟩,⟨⟨0,[1,1],.ne,none,[],[]⟩,⟨1,[1,1],.star,none,[],[]⟩⟩,⟨⟨0,[1,1,1],.ne,none,[],[]⟩,⟨1,[1,1],.star,none,[],[]⟩⟩]],[[⟨(⟨0,[1,1],.star,none,[],[]⟩,⟨⟨1,[],.star,none,[1],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.star,none,[],[]⟩,⟨⟨1,[1,1],.star,none,[1],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1,1,1],.star,none,[],[]⟩,⟨⟨1,[1],.star,none,[2],[]⟩,false,false⟩),true⟩]],true,false,false,⟨[[⟨⟨0,[],.may,some 7,[],[]⟩,true⟩]],[[(⟨0,[1],.star,none,[],[]⟩,⟨⟨1,[1],.may,none,[],[]⟩,true,false⟩),(⟨0,[1,1],.star,none,[],[]⟩,⟨⟨1,[1],.may,none,[],[]⟩,true,false⟩),(⟨0,[1],.star,none,[],[]⟩,⟨⟨1,[1,1],.may,none,[],[]⟩,true,false⟩),(⟨0,[1],.star,none,[],[]⟩,⟨⟨1,[1,1],.ne,none,[],[]⟩,true,false⟩),(⟨0,[1,1],.star,none,[],[]⟩,⟨⟨1,[1,1],.may,none,[],[]⟩,true,false⟩),(⟨0,[1,1],.star,none,[],[]⟩,⟨⟨1,[1,1],.ne,none,[],[]⟩,true,false⟩),(⟨0,[1],.star,none,[],[]⟩,⟨⟨1,[1,1,1],.star,none,[2],[]⟩,false,false⟩),(⟨0,[1,1],.star,none,[],[]⟩,⟨⟨1,[1,1,1],.ne,none,[],[]⟩,true,false⟩)]],[[⟨⟨0,[],.may,some 7,[],[]⟩,true⟩],[⟨⟨0,[],.may,some 7,[],[]⟩,true⟩],[⟨⟨0,[],.may,some 7,[],[]⟩,true⟩],[⟨⟨0,[],.may,some 7,[],[]⟩,true⟩]]⟩⟩

theorem cold_4 : UniformCampaign.step c 4 state3 = state4 := by decide

theorem quiescent_4 : UniformReplay.round 4 (UniformCampaign.limit 4) c.calls c.methods state3.rows state3.saved state4.data = state4.data := by decide

theorem saved_4 : OverwriteReplay.outputSaved 4 state3.saved state4.data = state4.saved := by decide

theorem reached_4 : UniformCampaign.history c 4 = state4 := by
  change UniformCampaign.step c 4 (UniformCampaign.history c 3) = state4
  rw [reached_3]
  exact cold_4

def state5 : UniformCampaign.State := ⟨[[⟨⟨0,[1],.may,none,[],[]⟩,⟨1,[1,1],.star,none,[],[]⟩⟩,⟨⟨0,[1,1],.ne,none,[],[]⟩,⟨1,[1],.star,none,[],[]⟩⟩,⟨⟨0,[1,1],.may,none,[],[]⟩,⟨1,[1,1],.star,none,[],[]⟩⟩,⟨⟨0,[1,1],.ne,none,[],[]⟩,⟨1,[1,1],.star,none,[],[]⟩⟩,⟨⟨0,[1,1,1],.ne,none,[],[]⟩,⟨1,[1,1],.star,none,[],[]⟩⟩,⟨⟨0,[1,1],.ne,none,[],[]⟩,⟨1,[1,1,1],.star,none,[],[]⟩⟩,⟨⟨0,[1,1],.ne,none,[],[]⟩,⟨1,[1,1,2],.star,none,[],[]⟩⟩,⟨⟨0,[1,1,1],.ne,none,[],[]⟩,⟨1,[1,1,1],.star,none,[],[]⟩⟩,⟨⟨0,[1,1,1],.ne,none,[],[]⟩,⟨1,[1,1,2],.star,none,[],[]⟩⟩]],[[⟨(⟨0,[1,1],.star,none,[],[]⟩,⟨⟨1,[],.star,none,[1],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.star,none,[],[]⟩,⟨⟨1,[1,1],.star,none,[1],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1,1,1],.star,none,[],[]⟩,⟨⟨1,[1],.star,none,[2],[]⟩,false,false⟩),true⟩,⟨(⟨0,[1],.star,none,[],[]⟩,⟨⟨1,[1,1,1],.star,none,[2],[]⟩,false,false⟩),false⟩]],true,true,true,⟨[[⟨⟨0,[],.may,some 7,[],[]⟩,true⟩,⟨⟨0,[1],.may,some 7,[],[]⟩,true⟩,⟨⟨0,[2],.must,some 7,[],[]⟩,false⟩,⟨⟨0,[1,1,2],.must,some 7,[],[]⟩,false⟩]],[[(⟨0,[1,1],.star,none,[],[]⟩,⟨⟨1,[1],.may,none,[],[]⟩,true,false⟩),(⟨0,[1],.star,none,[],[]⟩,⟨⟨1,[1,1],.ne,none,[],[]⟩,true,false⟩),(⟨0,[1,1],.star,none,[],[]⟩,⟨⟨1,[1,1],.may,none,[],[]⟩,true,false⟩),(⟨0,[1,1],.star,none,[],[]⟩,⟨⟨1,[1,1],.ne,none,[],[]⟩,true,false⟩),(⟨0,[1],.star,none,[],[]⟩,⟨⟨1,[1,1,1],.star,none,[2],[]⟩,false,false⟩),(⟨0,[1,1,1],.star,none,[],[]⟩,⟨⟨1,[1,1],.ne,none,[],[]⟩,true,false⟩),(⟨0,[1,1],.star,none,[],[]⟩,⟨⟨1,[1,1,1],.ne,none,[],[]⟩,true,false⟩),(⟨0,[1,1,2],.star,none,[],[]⟩,⟨⟨1,[1,1],.ne,none,[],[]⟩,true,false⟩),(⟨0,[1,1,1],.star,none,[],[]⟩,⟨⟨1,[1,1,1],.ne,none,[],[]⟩,true,false⟩),(⟨0,[1,1,2],.star,none,[],[]⟩,⟨⟨1,[1,1,1],.ne,none,[],[]⟩,true,false⟩)]],[[⟨⟨0,[1,1,2],.must,some 7,[],[]⟩,false⟩],[⟨⟨0,[1],.may,some 7,[],[]⟩,true⟩,⟨⟨0,[2],.must,some 7,[],[]⟩,false⟩],[⟨⟨0,[],.may,some 7,[],[]⟩,true⟩,⟨⟨0,[1,1,2],.must,some 7,[],[]⟩,false⟩],[⟨⟨0,[],.may,some 7,[],[]⟩,true⟩,⟨⟨0,[2],.must,some 7,[],[]⟩,false⟩]]⟩⟩

theorem cold_5 : UniformCampaign.step c 5 state4 = state5 := by decide

theorem quiescent_5 : UniformReplay.round 5 (UniformCampaign.limit 5) c.calls c.methods state4.rows state4.saved state5.data = state5.data := by decide

theorem saved_5 : OverwriteReplay.outputSaved 5 state4.saved state5.data = state5.saved := by decide

theorem reached_5 : UniformCampaign.history c 5 = state5 := by
  change UniformCampaign.step c 5 (UniformCampaign.history c 4) = state5
  rw [reached_4]
  exact cold_5

def state6 : UniformCampaign.State := ⟨[[⟨⟨0,[1],.may,none,[],[]⟩,⟨1,[1,1],.star,none,[],[]⟩⟩,⟨⟨0,[1,1],.may,none,[],[]⟩,⟨1,[1,1],.star,none,[],[]⟩⟩,⟨⟨0,[1,1,1],.may,none,[],[]⟩,⟨1,[1,1],.star,none,[],[]⟩⟩,⟨⟨0,[1,1,2],.may,none,[],[]⟩,⟨1,[1,1],.star,none,[],[]⟩⟩]],[[⟨(⟨0,[1,1],.star,none,[],[]⟩,⟨⟨1,[],.star,none,[1],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.star,none,[],[]⟩,⟨⟨1,[1,1],.star,none,[1],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1,1,1],.star,none,[],[]⟩,⟨⟨1,[1],.star,none,[2],[]⟩,false,false⟩),true⟩,⟨(⟨0,[1],.star,none,[],[]⟩,⟨⟨1,[1,1,1],.star,none,[2],[]⟩,false,false⟩),false⟩]],true,false,true,⟨[[⟨⟨0,[],.may,some 7,[],[]⟩,true⟩]],[[(⟨0,[1,1],.star,none,[],[]⟩,⟨⟨1,[1],.may,none,[],[]⟩,true,false⟩),(⟨0,[1,1],.star,none,[],[]⟩,⟨⟨1,[1,1],.may,none,[],[]⟩,true,false⟩),(⟨0,[1,1],.star,none,[],[]⟩,⟨⟨1,[1,1,1],.may,none,[],[]⟩,true,false⟩),(⟨0,[1,1],.star,none,[],[]⟩,⟨⟨1,[1,1,2],.may,none,[],[]⟩,true,false⟩)]],[[⟨⟨0,[],.may,some 7,[],[]⟩,true⟩],[⟨⟨0,[],.may,some 7,[],[]⟩,true⟩],[⟨⟨0,[],.may,some 7,[],[]⟩,true⟩],[⟨⟨0,[],.may,some 7,[],[]⟩,true⟩]]⟩⟩

theorem cold_6 : UniformCampaign.step c 6 state5 = state6 := by decide

theorem quiescent_6 : UniformReplay.round 6 (UniformCampaign.limit 6) c.calls c.methods state5.rows state5.saved state6.data = state6.data := by decide

theorem saved_6 : OverwriteReplay.outputSaved 6 state5.saved state6.data = state6.saved := by decide

theorem reached_6 : UniformCampaign.history c 6 = state6 := by
  change UniformCampaign.step c 6 (UniformCampaign.history c 5) = state6
  rw [reached_5]
  exact cold_6

def state7 : UniformCampaign.State := ⟨[[⟨⟨0,[1,1],.may,none,[],[]⟩,⟨1,[1,1],.star,none,[],[]⟩⟩]],[[⟨(⟨0,[1,1],.star,none,[],[]⟩,⟨⟨1,[],.star,none,[1],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.star,none,[],[]⟩,⟨⟨1,[1,1],.star,none,[1],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1,1,1],.star,none,[],[]⟩,⟨⟨1,[1],.star,none,[2],[]⟩,false,false⟩),true⟩,⟨(⟨0,[1],.star,none,[],[]⟩,⟨⟨1,[1,1,1],.star,none,[2],[]⟩,false,false⟩),false⟩]],true,false,true,⟨[[⟨⟨0,[],.may,some 7,[1],[]⟩,true⟩,⟨⟨0,[2],.must,some 7,[],[]⟩,false⟩,⟨⟨0,[1,1],.may,some 7,[],[]⟩,true⟩,⟨⟨0,[1,1,2],.must,some 7,[],[]⟩,false⟩,⟨⟨0,[1,1,1,1,2],.must,some 7,[],[]⟩,false⟩,⟨⟨0,[1,1,1,1,1,1],.ne,some 7,[],[]⟩,true⟩]],[[(⟨0,[1,1],.star,none,[],[]⟩,⟨⟨1,[1,1],.may,none,[],[]⟩,true,false⟩)]],[[⟨⟨0,[1,1,2],.must,some 7,[],[]⟩,false⟩],[⟨⟨0,[2],.must,some 7,[],[]⟩,false⟩,⟨⟨0,[1,1],.may,some 7,[],[]⟩,true⟩,⟨⟨0,[1,1,1,1,2],.must,some 7,[],[]⟩,false⟩],[⟨⟨0,[],.may,some 7,[1],[]⟩,true⟩,⟨⟨0,[1,1,2],.must,some 7,[],[]⟩,false⟩],[⟨⟨0,[2],.must,some 7,[],[]⟩,false⟩,⟨⟨0,[1,1,1,1,2],.must,some 7,[],[]⟩,false⟩]]⟩⟩

theorem cold_7 : UniformCampaign.step c 7 state6 = state7 := by decide

theorem quiescent_7 : UniformReplay.round 7 (UniformCampaign.limit 7) c.calls c.methods state6.rows state6.saved state7.data = state7.data := by decide

theorem saved_7 : OverwriteReplay.outputSaved 7 state6.saved state7.data = state7.saved := by decide

theorem reached_7 : UniformCampaign.history c 7 = state7 := by
  change UniformCampaign.step c 7 (UniformCampaign.history c 6) = state7
  rw [reached_6]
  exact cold_7

def state8 : UniformCampaign.State := ⟨[[]],[[⟨(⟨0,[1,1],.star,none,[],[]⟩,⟨⟨1,[],.star,none,[1],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.star,none,[],[]⟩,⟨⟨1,[1,1],.star,none,[1],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1,1,1],.star,none,[],[]⟩,⟨⟨1,[1],.star,none,[2],[]⟩,false,false⟩),true⟩,⟨(⟨0,[1],.star,none,[],[]⟩,⟨⟨1,[1,1,1],.star,none,[2],[]⟩,false,false⟩),false⟩]],false,false,true,⟨[[]],[[]],[[],[],[],[]]⟩⟩

theorem cold_8 : UniformCampaign.step c 8 state7 = state8 := by decide

theorem quiescent_8 : UniformReplay.round 8 (UniformCampaign.limit 8) c.calls c.methods state7.rows state7.saved state8.data = state8.data := by decide

theorem saved_8 : OverwriteReplay.outputSaved 8 state7.saved state8.data = state8.saved := by decide

theorem reached_8 : UniformCampaign.history c 8 = state8 := by
  change UniformCampaign.step c 8 (UniformCampaign.history c 7) = state8
  rw [reached_7]
  exact cold_8

def state9 : UniformCampaign.State := ⟨[[]],[[⟨(⟨0,[1,1],.star,none,[],[]⟩,⟨⟨1,[],.star,none,[1],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.star,none,[],[]⟩,⟨⟨1,[1,1],.star,none,[1],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1,1,1],.star,none,[],[]⟩,⟨⟨1,[1],.star,none,[2],[]⟩,false,false⟩),true⟩,⟨(⟨0,[1],.star,none,[],[]⟩,⟨⟨1,[1,1,1],.star,none,[2],[]⟩,false,false⟩),false⟩]],false,false,true,⟨[[]],[[]],[[],[],[],[]]⟩⟩

theorem cold_9 : UniformCampaign.step c 9 state8 = state9 := by decide

theorem quiescent_9 : UniformReplay.round 9 (UniformCampaign.limit 9) c.calls c.methods state8.rows state8.saved state9.data = state9.data := by decide

theorem saved_9 : OverwriteReplay.outputSaved 9 state8.saved state9.data = state9.saved := by decide

theorem reached_9 : UniformCampaign.history c 9 = state9 := by
  change UniformCampaign.step c 9 (UniformCampaign.history c 8) = state9
  rw [reached_8]
  exact cold_9

def state10 : UniformCampaign.State := ⟨[[]],[[⟨(⟨0,[1,1],.star,none,[],[]⟩,⟨⟨1,[],.star,none,[1],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.star,none,[],[]⟩,⟨⟨1,[1,1],.star,none,[1],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1,1,1],.star,none,[],[]⟩,⟨⟨1,[1],.star,none,[2],[]⟩,false,false⟩),true⟩,⟨(⟨0,[1],.star,none,[],[]⟩,⟨⟨1,[1,1,1],.star,none,[2],[]⟩,false,false⟩),false⟩]],false,false,true,⟨[[]],[[]],[[],[],[],[]]⟩⟩

theorem cold_10 : UniformCampaign.step c 10 state9 = state10 := by decide

theorem quiescent_10 : UniformReplay.round 10 (UniformCampaign.limit 10) c.calls c.methods state9.rows state9.saved state10.data = state10.data := by decide

theorem saved_10 : OverwriteReplay.outputSaved 10 state9.saved state10.data = state10.saved := by decide

theorem reached_10 : UniformCampaign.history c 10 = state10 := by
  change UniformCampaign.step c 10 (UniformCampaign.history c 9) = state10
  rw [reached_9]
  exact cold_10

theorem natural_stop_and_expected_observation : UniformCampaign.stopped 9 state9 = true ∧ state9.report = c.expected := by decide

theorem no_earlier_stop : ([(1,state1),(2,state2),(3,state3),(4,state4),(5,state5),(6,state6),(7,state7),(8,state8)].all (fun x => !(UniformCampaign.stopped x.1 x.2))) = true := by decide

theorem final_is_quiet : state10 = UniformCampaign.quiet c c.expected state10.saved := by decide

theorem uncapped_no_revival (n : Nat) : UniformCampaign.history c (n+10) = state10 := by
  induction n with
  | zero => exact reached_10
  | succ n ih =>
      change UniformCampaign.step c (n+11) (UniformCampaign.history c (n+10)) = state10
      rw [ih,final_is_quiet]
      exact UniformCampaign.inactive_has_no_analysis_or_new_guidance c _ _ _

end UniformColdNestedLarger

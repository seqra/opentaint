import UniformCampaign

namespace UniformColdNestedNegative

open NonEmptyPolicy NonEmptyRestriction

set_option maxRecDepth 32768

set_option maxHeartbeats 160000000

def c : UniformCampaign.Case := (UniformCampaign.cases[7]!).2

def state0 := UniformCampaign.initial c

def state1 : UniformCampaign.State := ⟨[[⟨⟨0,[],.may,none,[],[]⟩,⟨1,[],.star,none,[],[]⟩⟩,⟨⟨0,[1],.star,none,[],[]⟩,⟨1,[],.star,none,[],[]⟩⟩,⟨⟨0,[1],.ne,none,[],[]⟩,⟨1,[],.star,none,[],[]⟩⟩]],[[]],true,true,false,⟨[[⟨⟨0,[2],.must,some 7,[],[]⟩,false⟩]],[[(⟨0,[],.star,none,[],[]⟩,⟨⟨1,[],.may,none,[],[]⟩,true,false⟩),(⟨0,[],.star,none,[],[]⟩,⟨⟨1,[1],.star,none,[],[]⟩,true,false⟩),(⟨0,[],.star,none,[],[]⟩,⟨⟨1,[1],.ne,none,[],[]⟩,true,false⟩)]],[[⟨⟨0,[2],.must,some 7,[],[]⟩,false⟩],[⟨⟨0,[],.may,some 7,[],[]⟩,true⟩]]⟩⟩

theorem cold_1 : UniformCampaign.step c 1 state0 = state1 := by decide

theorem quiescent_1 : UniformReplay.round 1 (UniformCampaign.limit 1) c.calls c.methods state0.rows state0.saved state1.data = state1.data := by decide

theorem saved_1 : OverwriteReplay.outputSaved 1 state0.saved state1.data = state1.saved := by decide

theorem reached_1 : UniformCampaign.history c 1 = state1 := by
  change UniformCampaign.step c 1 (UniformCampaign.history c 0) = state1
  change UniformCampaign.step c 1 state0 = state1
  exact cold_1

def state2 : UniformCampaign.State := ⟨[[⟨⟨0,[1],.may,none,[],[]⟩,⟨1,[1],.star,none,[],[]⟩⟩,⟨⟨0,[1],.ne,none,[],[]⟩,⟨1,[1],.star,none,[],[]⟩⟩]],[[⟨(⟨0,[1],.star,none,[],[]⟩,⟨⟨1,[],.star,none,[1,2],[]⟩,false,false⟩),true⟩,⟨(⟨0,[],.star,none,[],[]⟩,⟨⟨1,[1],.star,none,[1,2],[]⟩,false,false⟩),true⟩]],true,false,false,⟨[[⟨⟨0,[],.may,some 7,[],[]⟩,true⟩]],[[(⟨0,[1],.star,none,[],[]⟩,⟨⟨1,[],.star,none,[1,2],[]⟩,false,false⟩),(⟨0,[],.star,none,[],[]⟩,⟨⟨1,[1],.star,none,[1,2],[]⟩,false,false⟩),(⟨0,[1],.star,none,[],[]⟩,⟨⟨1,[1],.may,none,[],[]⟩,true,false⟩),(⟨0,[1],.star,none,[],[]⟩,⟨⟨1,[1],.ne,none,[],[]⟩,true,false⟩)]],[[⟨⟨0,[],.may,some 7,[],[]⟩,true⟩],[⟨⟨0,[],.may,some 7,[],[]⟩,true⟩]]⟩⟩

theorem cold_2 : UniformCampaign.step c 2 state1 = state2 := by decide

theorem quiescent_2 : UniformReplay.round 2 (UniformCampaign.limit 2) c.calls c.methods state1.rows state1.saved state2.data = state2.data := by decide

theorem saved_2 : OverwriteReplay.outputSaved 2 state1.saved state2.data = state2.saved := by decide

theorem reached_2 : UniformCampaign.history c 2 = state2 := by
  change UniformCampaign.step c 2 (UniformCampaign.history c 1) = state2
  rw [reached_1]
  exact cold_2

def state3 : UniformCampaign.State := ⟨[[]],[[⟨(⟨0,[1],.star,none,[],[]⟩,⟨⟨1,[],.star,none,[1,2],[]⟩,false,false⟩),true⟩,⟨(⟨0,[],.star,none,[],[]⟩,⟨⟨1,[1],.star,none,[1,2],[]⟩,false,false⟩),true⟩]],true,false,false,⟨[[⟨⟨0,[2],.must,some 7,[],[]⟩,false⟩]],[[]],[[⟨⟨0,[2],.must,some 7,[],[]⟩,false⟩],[]]⟩⟩

theorem cold_3 : UniformCampaign.step c 3 state2 = state3 := by decide

theorem quiescent_3 : UniformReplay.round 3 (UniformCampaign.limit 3) c.calls c.methods state2.rows state2.saved state3.data = state3.data := by decide

theorem saved_3 : OverwriteReplay.outputSaved 3 state2.saved state3.data = state3.saved := by decide

theorem reached_3 : UniformCampaign.history c 3 = state3 := by
  change UniformCampaign.step c 3 (UniformCampaign.history c 2) = state3
  rw [reached_2]
  exact cold_3

def state4 : UniformCampaign.State := ⟨[[]],[[⟨(⟨0,[1],.star,none,[],[]⟩,⟨⟨1,[],.star,none,[1,2],[]⟩,false,false⟩),true⟩,⟨(⟨0,[],.star,none,[],[]⟩,⟨⟨1,[1],.star,none,[1,2],[]⟩,false,false⟩),true⟩]],false,false,false,⟨[[]],[[]],[[],[]]⟩⟩

theorem cold_4 : UniformCampaign.step c 4 state3 = state4 := by decide

theorem quiescent_4 : UniformReplay.round 4 (UniformCampaign.limit 4) c.calls c.methods state3.rows state3.saved state4.data = state4.data := by decide

theorem saved_4 : OverwriteReplay.outputSaved 4 state3.saved state4.data = state4.saved := by decide

theorem reached_4 : UniformCampaign.history c 4 = state4 := by
  change UniformCampaign.step c 4 (UniformCampaign.history c 3) = state4
  rw [reached_3]
  exact cold_4

theorem natural_stop_and_expected_observation : UniformCampaign.stopped 3 state3 = true ∧ state3.report = c.expected := by decide

theorem no_earlier_stop : ([(1,state1),(2,state2)].all (fun x => !(UniformCampaign.stopped x.1 x.2))) = true := by decide

theorem final_is_quiet : state4 = UniformCampaign.quiet c c.expected state4.saved := by decide

theorem uncapped_no_revival (n : Nat) : UniformCampaign.history c (n+4) = state4 := by
  induction n with
  | zero => exact reached_4
  | succ n ih =>
      change UniformCampaign.step c (n+5) (UniformCampaign.history c (n+4)) = state4
      rw [ih,final_is_quiet]
      exact UniformCampaign.inactive_has_no_analysis_or_new_guidance c _ _ _

end UniformColdNestedNegative

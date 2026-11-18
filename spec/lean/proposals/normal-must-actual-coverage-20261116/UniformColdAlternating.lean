import UniformAlternating

namespace UniformColdAlternating

open NonEmptyPolicy NonEmptyRestriction

set_option maxRecDepth 32768

set_option maxHeartbeats 320000000

def state0 := UniformAlternating.initial

def state1 : UniformAlternating.State := ⟨[⟨⟨1,[],.may,some 2,[],[]⟩,⟨0,[],.star,some 1,[],[]⟩⟩,⟨⟨1,[1],.may,some 2,[],[]⟩,⟨0,[],.star,some 1,[],[]⟩⟩,⟨⟨1,[],.may,some 1,[],[]⟩,⟨0,[],.star,some 2,[],[]⟩⟩,⟨⟨1,[1],.may,some 1,[],[]⟩,⟨0,[],.star,some 2,[],[]⟩⟩],[],true,true,false,⟨[⟨⟨0,[1],.must,some 1,[],[]⟩,false⟩,⟨⟨0,[],.may,some 2,[],[]⟩,true⟩,⟨⟨0,[],.may,some 1,[],[]⟩,true⟩],[(⟨0,[],.star,some 1,[],[]⟩,⟨⟨1,[],.may,some 2,[],[]⟩,true,false⟩),(⟨0,[],.star,some 1,[],[]⟩,⟨⟨1,[1],.must,some 2,[],[]⟩,true,false⟩),(⟨0,[],.star,some 2,[],[]⟩,⟨⟨1,[],.may,some 1,[],[]⟩,true,false⟩),(⟨0,[],.star,some 2,[],[]⟩,⟨⟨1,[1],.must,some 1,[],[]⟩,true,false⟩)],[[⟨⟨0,[1],.must,some 1,[],[]⟩,false,false⟩],[⟨⟨0,[],.may,some 2,[],[]⟩,true,false⟩],[⟨⟨0,[],.may,some 1,[],[]⟩,true,false⟩],[⟨⟨0,[],.may,some 2,[],[]⟩,true,false⟩]]⟩⟩

theorem cold_1 : UniformAlternating.step true 1 state0 = state1 := by decide

theorem quiescent_1 : UniformAlternating.round true 1 (UniformAlternating.limit 1) state0.rows state0.saved state1.data = state1.data := by decide

theorem reached_1 : UniformAlternating.history true 1 = state1 := by
  change UniformAlternating.step true 1 (UniformAlternating.history true 0) = state1
  change UniformAlternating.step true 1 state0 = state1
  exact cold_1

def state2 : UniformAlternating.State := ⟨[⟨⟨0,[1],.ne,some 1,[],[]⟩,⟨1,[],.exact,some 2,[],[]⟩⟩,⟨⟨0,[1],.ne,some 1,[],[]⟩,⟨1,[],.star,some 2,[],[]⟩⟩,⟨⟨0,[],.may,some 1,[],[]⟩,⟨1,[],.star,some 2,[],[]⟩⟩,⟨⟨0,[1],.ne,some 1,[],[]⟩,⟨1,[1],.exact,some 2,[],[]⟩⟩,⟨⟨0,[],.may,some 1,[],[]⟩,⟨1,[1],.exact,some 2,[],[]⟩⟩,⟨⟨0,[1],.ne,some 1,[],[]⟩,⟨1,[1],.star,some 2,[],[]⟩⟩,⟨⟨0,[],.may,some 1,[],[]⟩,⟨1,[1],.star,some 2,[],[]⟩⟩,⟨⟨0,[1],.ne,some 2,[],[]⟩,⟨1,[],.exact,some 1,[],[]⟩⟩,⟨⟨0,[1],.ne,some 2,[],[]⟩,⟨1,[],.star,some 1,[],[]⟩⟩,⟨⟨0,[],.may,some 2,[],[]⟩,⟨1,[],.star,some 1,[],[]⟩⟩,⟨⟨0,[1],.ne,some 2,[],[]⟩,⟨1,[1],.exact,some 1,[],[]⟩⟩,⟨⟨0,[],.may,some 2,[],[]⟩,⟨1,[1],.exact,some 1,[],[]⟩⟩,⟨⟨0,[1],.ne,some 2,[],[]⟩,⟨1,[1],.star,some 1,[],[]⟩⟩,⟨⟨0,[],.may,some 2,[],[]⟩,⟨1,[1],.star,some 1,[],[]⟩⟩],[],true,false,false,⟨[⟨⟨1,[],.may,some 2,[],[]⟩,true⟩,⟨⟨1,[],.may,some 1,[],[]⟩,true⟩],[(⟨1,[],.exact,some 2,[],[]⟩,⟨⟨0,[1],.ne,some 1,[],[]⟩,true,false⟩),(⟨1,[],.star,some 2,[],[]⟩,⟨⟨0,[1],.ne,some 1,[],[]⟩,true,false⟩),(⟨1,[],.star,some 2,[],[]⟩,⟨⟨0,[],.may,some 1,[],[]⟩,true,false⟩),(⟨1,[1],.exact,some 2,[],[]⟩,⟨⟨0,[1],.ne,some 1,[],[]⟩,true,false⟩),(⟨1,[1],.exact,some 2,[],[]⟩,⟨⟨0,[],.may,some 1,[],[]⟩,true,false⟩),(⟨1,[1],.star,some 2,[],[]⟩,⟨⟨0,[1],.ne,some 1,[],[]⟩,true,false⟩),(⟨1,[1],.star,some 2,[],[]⟩,⟨⟨0,[],.may,some 1,[],[]⟩,true,false⟩),(⟨1,[],.exact,some 1,[],[]⟩,⟨⟨0,[1],.ne,some 2,[],[]⟩,true,false⟩),(⟨1,[],.star,some 1,[],[]⟩,⟨⟨0,[1],.ne,some 2,[],[]⟩,true,false⟩),(⟨1,[],.star,some 1,[],[]⟩,⟨⟨0,[],.may,some 2,[],[]⟩,true,false⟩),(⟨1,[1],.exact,some 1,[],[]⟩,⟨⟨0,[1],.ne,some 2,[],[]⟩,true,false⟩),(⟨1,[1],.exact,some 1,[],[]⟩,⟨⟨0,[],.may,some 2,[],[]⟩,true,false⟩),(⟨1,[1],.star,some 1,[],[]⟩,⟨⟨0,[1],.ne,some 2,[],[]⟩,true,false⟩),(⟨1,[1],.star,some 1,[],[]⟩,⟨⟨0,[],.may,some 2,[],[]⟩,true,false⟩)],[[⟨⟨0,[],.may,some 2,[],[]⟩,true,false⟩],[⟨⟨0,[],.may,some 1,[],[]⟩,true,false⟩],[⟨⟨0,[],.may,some 2,[],[]⟩,true,false⟩],[⟨⟨0,[],.may,some 1,[],[]⟩,true,false⟩]]⟩⟩

theorem cold_2 : UniformAlternating.step true 2 state1 = state2 := by decide

theorem quiescent_2 : UniformAlternating.round true 2 (UniformAlternating.limit 2) state1.rows state1.saved state2.data = state2.data := by decide

theorem reached_2 : UniformAlternating.history true 2 = state2 := by
  change UniformAlternating.step true 2 (UniformAlternating.history true 1) = state2
  rw [reached_1]
  exact cold_2

def state3 : UniformAlternating.State := ⟨[⟨⟨1,[],.may,some 2,[],[]⟩,⟨0,[1],.star,some 1,[],[]⟩⟩,⟨⟨1,[1],.may,some 2,[],[]⟩,⟨0,[1],.star,some 1,[],[]⟩⟩,⟨⟨1,[1],.exact,some 2,[],[]⟩,⟨0,[1],.star,some 1,[],[]⟩⟩],[⟨(⟨0,[1],.must,some 1,[],[]⟩,⟨⟨1,[],.exact,some 2,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1],.must,some 1,[],[]⟩,⟨⟨1,[],.must,some 2,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1],.must,some 1,[],[]⟩,⟨⟨1,[1],.exact,some 2,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.exact,some 2,[],[]⟩,⟨⟨1,[1],.must,some 1,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.exact,some 2,[],[]⟩,⟨⟨1,[1],.exact,some 1,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1],.must,some 2,[],[]⟩,⟨⟨1,[],.exact,some 1,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1],.must,some 2,[],[]⟩,⟨⟨1,[],.must,some 1,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.must,some 2,[],[]⟩,⟨⟨1,[],.must,some 1,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1],.must,some 2,[],[]⟩,⟨⟨1,[1],.exact,some 1,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.must,some 2,[],[]⟩,⟨⟨1,[1],.exact,some 1,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1],.exact,some 2,[],[]⟩,⟨⟨1,[1],.must,some 1,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1],.exact,some 2,[],[]⟩,⟨⟨1,[1],.exact,some 1,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.exact,some 1,[],[]⟩,⟨⟨1,[1],.must,some 2,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.exact,some 1,[],[]⟩,⟨⟨1,[1],.exact,some 2,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.must,some 1,[],[]⟩,⟨⟨1,[],.must,some 2,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.must,some 1,[],[]⟩,⟨⟨1,[1],.exact,some 2,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1],.exact,some 1,[],[]⟩,⟨⟨1,[1],.must,some 2,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1],.exact,some 1,[],[]⟩,⟨⟨1,[1],.exact,some 2,[],[]⟩,false,false⟩),false⟩],true,false,true,⟨[⟨⟨0,[1],.must,some 1,[],[]⟩,false⟩,⟨⟨0,[],.exact,some 2,[],[]⟩,false⟩,⟨⟨0,[],.must,some 2,[],[]⟩,false⟩,⟨⟨0,[1],.exact,some 2,[],[]⟩,false⟩,⟨⟨0,[],.exact,some 1,[],[]⟩,false⟩,⟨⟨0,[],.must,some 1,[],[]⟩,false⟩,⟨⟨0,[1],.exact,some 1,[],[]⟩,false⟩],[(⟨0,[1],.must,some 1,[],[]⟩,⟨⟨1,[],.exact,some 2,[],[]⟩,false,false⟩),(⟨0,[1],.must,some 1,[],[]⟩,⟨⟨1,[],.must,some 2,[],[]⟩,false,false⟩),(⟨0,[1],.must,some 1,[],[]⟩,⟨⟨1,[1],.must,some 2,[],[]⟩,false,false⟩),(⟨0,[1],.star,some 1,[],[]⟩,⟨⟨1,[],.may,some 2,[],[]⟩,true,false⟩),(⟨0,[1],.star,some 1,[],[]⟩,⟨⟨1,[1],.must,some 2,[],[]⟩,true,false⟩),(⟨0,[1],.must,some 1,[],[]⟩,⟨⟨1,[1],.exact,some 2,[],[]⟩,false,false⟩),(⟨0,[1],.star,some 1,[],[]⟩,⟨⟨1,[1],.exact,some 2,[],[]⟩,true,false⟩),(⟨0,[1],.star,some 1,[],[]⟩,⟨⟨1,[1],.may,some 2,[],[]⟩,true,false⟩),(⟨0,[],.exact,some 2,[],[]⟩,⟨⟨1,[1],.must,some 1,[],[]⟩,false,false⟩),(⟨0,[],.exact,some 2,[],[]⟩,⟨⟨1,[1],.exact,some 1,[],[]⟩,false,false⟩),(⟨0,[1],.must,some 2,[],[]⟩,⟨⟨1,[],.exact,some 1,[],[]⟩,false,false⟩),(⟨0,[1],.must,some 2,[],[]⟩,⟨⟨1,[],.must,some 1,[],[]⟩,false,false⟩),(⟨0,[1],.must,some 2,[],[]⟩,⟨⟨1,[1],.must,some 1,[],[]⟩,false,false⟩),(⟨0,[],.must,some 2,[],[]⟩,⟨⟨1,[],.must,some 1,[],[]⟩,false,false⟩),(⟨0,[],.must,some 2,[],[]⟩,⟨⟨1,[1],.must,some 1,[],[]⟩,false,false⟩),(⟨0,[1],.must,some 2,[],[]⟩,⟨⟨1,[1],.exact,some 1,[],[]⟩,false,false⟩),(⟨0,[],.must,some 2,[],[]⟩,⟨⟨1,[1],.exact,some 1,[],[]⟩,false,false⟩),(⟨0,[1],.exact,some 2,[],[]⟩,⟨⟨1,[1],.must,some 1,[],[]⟩,false,false⟩),(⟨0,[1],.exact,some 2,[],[]⟩,⟨⟨1,[1],.exact,some 1,[],[]⟩,false,false⟩),(⟨0,[],.exact,some 1,[],[]⟩,⟨⟨1,[1],.must,some 2,[],[]⟩,false,false⟩),(⟨0,[],.exact,some 1,[],[]⟩,⟨⟨1,[1],.exact,some 2,[],[]⟩,false,false⟩),(⟨0,[],.must,some 1,[],[]⟩,⟨⟨1,[],.must,some 2,[],[]⟩,false,false⟩),(⟨0,[],.must,some 1,[],[]⟩,⟨⟨1,[1],.must,some 2,[],[]⟩,false,false⟩),(⟨0,[],.must,some 1,[],[]⟩,⟨⟨1,[1],.exact,some 2,[],[]⟩,false,false⟩),(⟨0,[1],.exact,some 1,[],[]⟩,⟨⟨1,[1],.must,some 2,[],[]⟩,false,false⟩),(⟨0,[1],.exact,some 1,[],[]⟩,⟨⟨1,[1],.exact,some 2,[],[]⟩,false,false⟩)],[[⟨⟨0,[1],.must,some 1,[],[]⟩,false,false⟩],[⟨⟨0,[],.exact,some 2,[],[]⟩,false,false⟩,⟨⟨0,[],.must,some 2,[],[]⟩,false,false⟩,⟨⟨0,[1],.exact,some 2,[],[]⟩,false,false⟩],[⟨⟨0,[],.exact,some 1,[],[]⟩,false,false⟩,⟨⟨0,[],.must,some 1,[],[]⟩,false,false⟩,⟨⟨0,[1],.exact,some 1,[],[]⟩,false,false⟩],[⟨⟨0,[],.exact,some 2,[],[]⟩,false,false⟩,⟨⟨0,[],.must,some 2,[],[]⟩,false,false⟩,⟨⟨0,[1],.exact,some 2,[],[]⟩,false,false⟩]]⟩⟩

theorem cold_3 : UniformAlternating.step true 3 state2 = state3 := by decide

theorem quiescent_3 : UniformAlternating.round true 3 (UniformAlternating.limit 3) state2.rows state2.saved state3.data = state3.data := by decide

theorem reached_3 : UniformAlternating.history true 3 = state3 := by
  change UniformAlternating.step true 3 (UniformAlternating.history true 2) = state3
  rw [reached_2]
  exact cold_3

def state4 : UniformAlternating.State := ⟨[],[⟨(⟨0,[1],.must,some 1,[],[]⟩,⟨⟨1,[],.exact,some 2,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1],.must,some 1,[],[]⟩,⟨⟨1,[],.must,some 2,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1],.must,some 1,[],[]⟩,⟨⟨1,[1],.exact,some 2,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.exact,some 2,[],[]⟩,⟨⟨1,[1],.must,some 1,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.exact,some 2,[],[]⟩,⟨⟨1,[1],.exact,some 1,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1],.must,some 2,[],[]⟩,⟨⟨1,[],.exact,some 1,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1],.must,some 2,[],[]⟩,⟨⟨1,[],.must,some 1,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.must,some 2,[],[]⟩,⟨⟨1,[],.must,some 1,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1],.must,some 2,[],[]⟩,⟨⟨1,[1],.exact,some 1,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.must,some 2,[],[]⟩,⟨⟨1,[1],.exact,some 1,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1],.exact,some 2,[],[]⟩,⟨⟨1,[1],.must,some 1,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1],.exact,some 2,[],[]⟩,⟨⟨1,[1],.exact,some 1,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.exact,some 1,[],[]⟩,⟨⟨1,[1],.must,some 2,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.exact,some 1,[],[]⟩,⟨⟨1,[1],.exact,some 2,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.must,some 1,[],[]⟩,⟨⟨1,[],.must,some 2,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.must,some 1,[],[]⟩,⟨⟨1,[1],.exact,some 2,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1],.exact,some 1,[],[]⟩,⟨⟨1,[1],.must,some 2,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1],.exact,some 1,[],[]⟩,⟨⟨1,[1],.exact,some 2,[],[]⟩,false,false⟩),false⟩],false,false,true,⟨[],[],[[],[],[],[]]⟩⟩

theorem cold_4 : UniformAlternating.step true 4 state3 = state4 := by decide

theorem quiescent_4 : UniformAlternating.round true 4 (UniformAlternating.limit 4) state3.rows state3.saved state4.data = state4.data := by decide

theorem reached_4 : UniformAlternating.history true 4 = state4 := by
  change UniformAlternating.step true 4 (UniformAlternating.history true 3) = state4
  rw [reached_3]
  exact cold_4

def state5 : UniformAlternating.State := ⟨[],[⟨(⟨0,[1],.must,some 1,[],[]⟩,⟨⟨1,[],.exact,some 2,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1],.must,some 1,[],[]⟩,⟨⟨1,[],.must,some 2,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1],.must,some 1,[],[]⟩,⟨⟨1,[1],.exact,some 2,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.exact,some 2,[],[]⟩,⟨⟨1,[1],.must,some 1,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.exact,some 2,[],[]⟩,⟨⟨1,[1],.exact,some 1,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1],.must,some 2,[],[]⟩,⟨⟨1,[],.exact,some 1,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1],.must,some 2,[],[]⟩,⟨⟨1,[],.must,some 1,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.must,some 2,[],[]⟩,⟨⟨1,[],.must,some 1,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1],.must,some 2,[],[]⟩,⟨⟨1,[1],.exact,some 1,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.must,some 2,[],[]⟩,⟨⟨1,[1],.exact,some 1,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1],.exact,some 2,[],[]⟩,⟨⟨1,[1],.must,some 1,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1],.exact,some 2,[],[]⟩,⟨⟨1,[1],.exact,some 1,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.exact,some 1,[],[]⟩,⟨⟨1,[1],.must,some 2,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.exact,some 1,[],[]⟩,⟨⟨1,[1],.exact,some 2,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.must,some 1,[],[]⟩,⟨⟨1,[],.must,some 2,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.must,some 1,[],[]⟩,⟨⟨1,[1],.exact,some 2,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1],.exact,some 1,[],[]⟩,⟨⟨1,[1],.must,some 2,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1],.exact,some 1,[],[]⟩,⟨⟨1,[1],.exact,some 2,[],[]⟩,false,false⟩),false⟩],false,false,true,⟨[],[],[[],[],[],[]]⟩⟩

theorem cold_5 : UniformAlternating.step true 5 state4 = state5 := by decide

theorem quiescent_5 : UniformAlternating.round true 5 (UniformAlternating.limit 5) state4.rows state4.saved state5.data = state5.data := by decide

theorem reached_5 : UniformAlternating.history true 5 = state5 := by
  change UniformAlternating.step true 5 (UniformAlternating.history true 4) = state5
  rw [reached_4]
  exact cold_5

def state6 : UniformAlternating.State := ⟨[],[⟨(⟨0,[1],.must,some 1,[],[]⟩,⟨⟨1,[],.exact,some 2,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1],.must,some 1,[],[]⟩,⟨⟨1,[],.must,some 2,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1],.must,some 1,[],[]⟩,⟨⟨1,[1],.exact,some 2,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.exact,some 2,[],[]⟩,⟨⟨1,[1],.must,some 1,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.exact,some 2,[],[]⟩,⟨⟨1,[1],.exact,some 1,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1],.must,some 2,[],[]⟩,⟨⟨1,[],.exact,some 1,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1],.must,some 2,[],[]⟩,⟨⟨1,[],.must,some 1,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.must,some 2,[],[]⟩,⟨⟨1,[],.must,some 1,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1],.must,some 2,[],[]⟩,⟨⟨1,[1],.exact,some 1,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.must,some 2,[],[]⟩,⟨⟨1,[1],.exact,some 1,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1],.exact,some 2,[],[]⟩,⟨⟨1,[1],.must,some 1,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1],.exact,some 2,[],[]⟩,⟨⟨1,[1],.exact,some 1,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.exact,some 1,[],[]⟩,⟨⟨1,[1],.must,some 2,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.exact,some 1,[],[]⟩,⟨⟨1,[1],.exact,some 2,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.must,some 1,[],[]⟩,⟨⟨1,[],.must,some 2,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[],.must,some 1,[],[]⟩,⟨⟨1,[1],.exact,some 2,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1],.exact,some 1,[],[]⟩,⟨⟨1,[1],.must,some 2,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1],.exact,some 1,[],[]⟩,⟨⟨1,[1],.exact,some 2,[],[]⟩,false,false⟩),false⟩],false,false,true,⟨[],[],[[],[],[],[]]⟩⟩

theorem cold_6 : UniformAlternating.step true 6 state5 = state6 := by decide

theorem quiescent_6 : UniformAlternating.round true 6 (UniformAlternating.limit 6) state5.rows state5.saved state6.data = state6.data := by decide

theorem reached_6 : UniformAlternating.history true 6 = state6 := by
  change UniformAlternating.step true 6 (UniformAlternating.history true 5) = state6
  rw [reached_5]
  exact cold_6

theorem normal_observation_at_run3 : state3.report = true ∧ state3.observationActive = false := by decide

theorem run3_retains_real_callee_demand : state3.rows.length = 3 := by decide

theorem run5_naturally_stops : UniformAlternating.stopped 5 state5 = true ∧ state5.report = true ∧ state5.saved.length = 18 := by decide

theorem no_earlier_stop : ([1,2,3,4].all (fun r => !(UniformAlternating.stopped r (UniformAlternating.history true r)))) = true := by decide

theorem final_is_quiet : state6 = UniformAlternating.quiet true state6.saved := by decide

theorem uncapped_no_revival (n : Nat) : UniformAlternating.history true (n+6) = state6 := by
  induction n with
  | zero => exact reached_6
  | succ n ih =>
      change UniformAlternating.step true (n+7) (UniformAlternating.history true (n+6)) = state6
      rw [ih,final_is_quiet]
      exact UniformAlternating.quiet_never_restarts true _ _ _

end UniformColdAlternating

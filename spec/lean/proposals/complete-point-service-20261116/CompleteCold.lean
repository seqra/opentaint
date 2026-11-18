import CompletePoint
namespace CompleteCold
open CompletePoint NonEmptyPolicy NonEmptyRestriction
set_option maxRecDepth 65536
set_option maxHeartbeats 320000000
def s0 := initial
def s1 : State := ⟨[⟨⟨1,[],.may,some 2,[],[]⟩,⟨0,[],.star,some 1,[],[]⟩⟩,⟨⟨1,[3],.may,some 2,[],[]⟩,⟨0,[],.star,some 1,[],[]⟩⟩,⟨⟨1,[],.may,some 1,[],[]⟩,⟨0,[],.star,some 2,[],[]⟩⟩,⟨⟨1,[3],.may,some 1,[],[]⟩,⟨0,[],.star,some 2,[],[]⟩⟩],[],[],true,true,false,⟨[⟨⟨0,[1],.ne,some 1,[],[]⟩,true⟩,⟨⟨0,[],.may,some 2,[],[]⟩,true⟩,⟨⟨0,[],.may,some 1,[],[]⟩,true⟩],[(⟨0,[],.star,some 1,[],[]⟩,⟨⟨1,[],.may,some 2,[],[]⟩,true,false⟩),(⟨0,[],.star,some 1,[],[]⟩,⟨⟨1,[3],.must,some 2,[],[]⟩,true,false⟩),(⟨0,[],.star,some 2,[],[]⟩,⟨⟨1,[],.may,some 1,[],[]⟩,true,false⟩),(⟨0,[],.star,some 2,[],[]⟩,⟨⟨1,[3],.must,some 1,[],[]⟩,true,false⟩)],[],[[⟨⟨0,[1],.ne,some 1,[],[]⟩,true,false⟩],[⟨⟨0,[],.may,some 2,[],[]⟩,true,false⟩],[⟨⟨0,[],.may,some 1,[],[]⟩,true,false⟩],[⟨⟨0,[],.may,some 2,[],[]⟩,true,false⟩]]⟩⟩
def s2 : State := ⟨[⟨⟨0,[1],.ne,some 1,[],[]⟩,⟨1,[],.exact,some 2,[],[]⟩⟩,⟨⟨0,[1],.ne,some 1,[],[]⟩,⟨1,[],.star,some 2,[],[]⟩⟩,⟨⟨0,[],.may,some 1,[],[]⟩,⟨1,[],.star,some 2,[],[]⟩⟩,⟨⟨0,[1],.ne,some 1,[],[]⟩,⟨1,[3],.exact,some 2,[],[]⟩⟩,⟨⟨0,[],.may,some 1,[],[]⟩,⟨1,[3],.exact,some 2,[],[]⟩⟩,⟨⟨0,[1],.ne,some 1,[],[]⟩,⟨1,[3],.star,some 2,[],[]⟩⟩,⟨⟨0,[],.may,some 1,[],[]⟩,⟨1,[3],.star,some 2,[],[]⟩⟩,⟨⟨0,[1],.ne,some 2,[],[]⟩,⟨1,[],.exact,some 1,[],[]⟩⟩,⟨⟨0,[1],.ne,some 2,[],[]⟩,⟨1,[],.star,some 1,[],[]⟩⟩,⟨⟨0,[],.may,some 2,[],[]⟩,⟨1,[],.star,some 1,[],[]⟩⟩,⟨⟨0,[1],.ne,some 2,[],[]⟩,⟨1,[3],.exact,some 1,[],[]⟩⟩,⟨⟨0,[],.may,some 2,[],[]⟩,⟨1,[3],.exact,some 1,[],[]⟩⟩,⟨⟨0,[1],.ne,some 2,[],[]⟩,⟨1,[3],.star,some 1,[],[]⟩⟩,⟨⟨0,[],.may,some 2,[],[]⟩,⟨1,[3],.star,some 1,[],[]⟩⟩],[],[],true,false,false,⟨[⟨⟨1,[],.may,some 2,[],[]⟩,true⟩,⟨⟨1,[],.may,some 1,[],[]⟩,true⟩],[(⟨1,[],.exact,some 2,[],[]⟩,⟨⟨0,[1],.ne,some 1,[],[]⟩,true,false⟩),(⟨1,[],.star,some 2,[],[]⟩,⟨⟨0,[1],.ne,some 1,[],[]⟩,true,false⟩),(⟨1,[],.star,some 2,[],[]⟩,⟨⟨0,[],.may,some 1,[],[]⟩,true,false⟩),(⟨1,[3],.exact,some 2,[],[]⟩,⟨⟨0,[1],.ne,some 1,[],[]⟩,true,false⟩),(⟨1,[3],.exact,some 2,[],[]⟩,⟨⟨0,[],.may,some 1,[],[]⟩,true,false⟩),(⟨1,[3],.star,some 2,[],[]⟩,⟨⟨0,[1],.ne,some 1,[],[]⟩,true,false⟩),(⟨1,[3],.star,some 2,[],[]⟩,⟨⟨0,[],.may,some 1,[],[]⟩,true,false⟩),(⟨1,[],.exact,some 1,[],[]⟩,⟨⟨0,[1],.ne,some 2,[],[]⟩,true,false⟩),(⟨1,[],.star,some 1,[],[]⟩,⟨⟨0,[1],.ne,some 2,[],[]⟩,true,false⟩),(⟨1,[],.star,some 1,[],[]⟩,⟨⟨0,[],.may,some 2,[],[]⟩,true,false⟩),(⟨1,[3],.exact,some 1,[],[]⟩,⟨⟨0,[1],.ne,some 2,[],[]⟩,true,false⟩),(⟨1,[3],.exact,some 1,[],[]⟩,⟨⟨0,[],.may,some 2,[],[]⟩,true,false⟩),(⟨1,[3],.star,some 1,[],[]⟩,⟨⟨0,[1],.ne,some 2,[],[]⟩,true,false⟩),(⟨1,[3],.star,some 1,[],[]⟩,⟨⟨0,[],.may,some 2,[],[]⟩,true,false⟩)],[],[[⟨⟨0,[],.may,some 2,[],[]⟩,true,false⟩],[⟨⟨0,[],.may,some 1,[],[]⟩,true,false⟩],[⟨⟨0,[],.may,some 2,[],[]⟩,true,false⟩],[⟨⟨0,[],.may,some 1,[],[]⟩,true,false⟩]]⟩⟩
def s3 : State := ⟨[⟨⟨1,[],.may,some 2,[],[]⟩,⟨0,[1],.star,some 1,[],[]⟩⟩,⟨⟨1,[3],.may,some 2,[],[]⟩,⟨0,[1],.star,some 1,[],[]⟩⟩,⟨⟨1,[3],.exact,some 2,[],[]⟩,⟨0,[1],.star,some 1,[],[]⟩⟩,⟨⟨1,[3],.may,some 1,[],[]⟩,⟨0,[3],.star,some 2,[],[]⟩⟩,⟨⟨1,[3],.exact,some 1,[],[]⟩,⟨0,[3],.star,some 2,[],[]⟩⟩,⟨⟨1,[3],.may,some 2,[],[]⟩,⟨0,[3],.star,some 1,[],[]⟩⟩,⟨⟨1,[3],.exact,some 2,[],[]⟩,⟨0,[3],.star,some 1,[],[]⟩⟩],[⟨(⟨0,[1,2],.exact,some 1,[],[]⟩,⟨⟨1,[3],.must,some 2,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1,2],.exact,some 1,[],[]⟩,⟨⟨1,[3],.exact,some 2,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[3],.exact,some 2,[],[]⟩,⟨⟨1,[3],.must,some 1,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[3],.exact,some 2,[],[]⟩,⟨⟨1,[3],.exact,some 1,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[3],.exact,some 1,[],[]⟩,⟨⟨1,[3],.must,some 2,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[3],.exact,some 1,[],[]⟩,⟨⟨1,[3],.exact,some 2,[],[]⟩,false,false⟩),false⟩],[⟨0,[1,2],.exact,some 1,[],[]⟩,⟨0,[3],.exact,some 2,[],[]⟩,⟨0,[3],.exact,some 1,[],[]⟩],true,false,true,⟨[⟨⟨0,[1,2],.exact,some 1,[],[]⟩,false⟩,⟨⟨0,[3],.must,some 2,[],[]⟩,false⟩,⟨⟨0,[3],.exact,some 2,[],[]⟩,false⟩,⟨⟨0,[3],.must,some 1,[],[]⟩,false⟩,⟨⟨0,[3],.exact,some 1,[],[]⟩,false⟩],[(⟨0,[1,2],.exact,some 1,[],[]⟩,⟨⟨1,[3],.must,some 2,[],[]⟩,false,false⟩),(⟨0,[1],.star,some 1,[],[]⟩,⟨⟨1,[],.may,some 2,[],[]⟩,true,false⟩),(⟨0,[1],.star,some 1,[],[]⟩,⟨⟨1,[3],.must,some 2,[],[]⟩,true,false⟩),(⟨0,[1,2],.exact,some 1,[],[]⟩,⟨⟨1,[3],.exact,some 2,[],[]⟩,false,false⟩),(⟨0,[1],.star,some 1,[],[]⟩,⟨⟨1,[3],.exact,some 2,[],[]⟩,true,false⟩),(⟨0,[1],.star,some 1,[],[]⟩,⟨⟨1,[3],.may,some 2,[],[]⟩,true,false⟩),(⟨0,[3],.star,some 2,[],[]⟩,⟨⟨1,[3],.must,some 1,[],[]⟩,true,false⟩),(⟨0,[3],.star,some 2,[],[]⟩,⟨⟨1,[3],.exact,some 1,[],[]⟩,true,false⟩),(⟨0,[3],.exact,some 2,[],[]⟩,⟨⟨1,[3],.must,some 1,[],[]⟩,false,false⟩),(⟨0,[3],.exact,some 2,[],[]⟩,⟨⟨1,[3],.exact,some 1,[],[]⟩,false,false⟩),(⟨0,[3],.star,some 1,[],[]⟩,⟨⟨1,[3],.must,some 2,[],[]⟩,true,false⟩),(⟨0,[3],.star,some 1,[],[]⟩,⟨⟨1,[3],.exact,some 2,[],[]⟩,true,false⟩),(⟨0,[3],.exact,some 1,[],[]⟩,⟨⟨1,[3],.must,some 2,[],[]⟩,false,false⟩),(⟨0,[3],.exact,some 1,[],[]⟩,⟨⟨1,[3],.exact,some 2,[],[]⟩,false,false⟩)],[⟨0,[1,2],.exact,some 1,[],[]⟩,⟨0,[3],.exact,some 2,[],[]⟩,⟨0,[3],.exact,some 1,[],[]⟩],[[⟨⟨0,[1,2],.exact,some 1,[],[]⟩,false,false⟩],[⟨⟨0,[3],.must,some 2,[],[]⟩,false,false⟩,⟨⟨0,[3],.exact,some 2,[],[]⟩,false,false⟩],[⟨⟨0,[3],.must,some 1,[],[]⟩,false,false⟩,⟨⟨0,[3],.exact,some 1,[],[]⟩,false,false⟩],[⟨⟨0,[3],.must,some 2,[],[]⟩,false,false⟩,⟨⟨0,[3],.exact,some 2,[],[]⟩,false,false⟩]]⟩⟩
def s4 : State := ⟨[],[⟨(⟨0,[1,2],.exact,some 1,[],[]⟩,⟨⟨1,[3],.must,some 2,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1,2],.exact,some 1,[],[]⟩,⟨⟨1,[3],.exact,some 2,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[3],.exact,some 2,[],[]⟩,⟨⟨1,[3],.must,some 1,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[3],.exact,some 2,[],[]⟩,⟨⟨1,[3],.exact,some 1,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[3],.exact,some 1,[],[]⟩,⟨⟨1,[3],.must,some 2,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[3],.exact,some 1,[],[]⟩,⟨⟨1,[3],.exact,some 2,[],[]⟩,false,false⟩),false⟩],[⟨0,[1,2],.exact,some 1,[],[]⟩,⟨0,[3],.exact,some 2,[],[]⟩,⟨0,[3],.exact,some 1,[],[]⟩],false,false,true,⟨[],[],[],[[],[],[],[]]⟩⟩
def s5 : State := ⟨[],[⟨(⟨0,[1,2],.exact,some 1,[],[]⟩,⟨⟨1,[3],.must,some 2,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1,2],.exact,some 1,[],[]⟩,⟨⟨1,[3],.exact,some 2,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[3],.exact,some 2,[],[]⟩,⟨⟨1,[3],.must,some 1,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[3],.exact,some 2,[],[]⟩,⟨⟨1,[3],.exact,some 1,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[3],.exact,some 1,[],[]⟩,⟨⟨1,[3],.must,some 2,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[3],.exact,some 1,[],[]⟩,⟨⟨1,[3],.exact,some 2,[],[]⟩,false,false⟩),false⟩],[⟨0,[1,2],.exact,some 1,[],[]⟩,⟨0,[3],.exact,some 2,[],[]⟩,⟨0,[3],.exact,some 1,[],[]⟩],false,false,true,⟨[],[],[],[[],[],[],[]]⟩⟩
def s6 : State := ⟨[],[⟨(⟨0,[1,2],.exact,some 1,[],[]⟩,⟨⟨1,[3],.must,some 2,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[1,2],.exact,some 1,[],[]⟩,⟨⟨1,[3],.exact,some 2,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[3],.exact,some 2,[],[]⟩,⟨⟨1,[3],.must,some 1,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[3],.exact,some 2,[],[]⟩,⟨⟨1,[3],.exact,some 1,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[3],.exact,some 1,[],[]⟩,⟨⟨1,[3],.must,some 2,[],[]⟩,false,false⟩),false⟩,⟨(⟨0,[3],.exact,some 1,[],[]⟩,⟨⟨1,[3],.exact,some 2,[],[]⟩,false,false⟩),false⟩],[⟨0,[1,2],.exact,some 1,[],[]⟩,⟨0,[3],.exact,some 2,[],[]⟩,⟨0,[3],.exact,some 1,[],[]⟩],false,false,true,⟨[],[],[],[[],[],[],[]]⟩⟩
theorem cold_1 : step true 1 s0=s1 := by decide +kernel
theorem quiescent_1 : round true 1 (limit 1) s0.rows s0.saved s0.complete s1.data=s1.data := by decide +kernel
theorem reached_1 : history true 1=s1 := by
  change step true 1 (history true 0)=s1
  change step true 1 s0=s1
  exact cold_1
theorem cold_2 : step true 2 s1=s2 := by decide +kernel
theorem quiescent_2 : round true 2 (limit 2) s1.rows s1.saved s1.complete s2.data=s2.data := by decide +kernel
theorem reached_2 : history true 2=s2 := by
  change step true 2 (history true 1)=s2
  rw [reached_1]
  exact cold_2
theorem cold_3 : step true 3 s2=s3 := by decide +kernel
theorem quiescent_3 : round true 3 (limit 3) s2.rows s2.saved s2.complete s3.data=s3.data := by decide +kernel
theorem reached_3 : history true 3=s3 := by
  change step true 3 (history true 2)=s3
  rw [reached_2]
  exact cold_3
theorem cold_4 : step true 4 s3=s4 := by decide +kernel
theorem quiescent_4 : round true 4 (limit 4) s3.rows s3.saved s3.complete s4.data=s4.data := by decide +kernel
theorem reached_4 : history true 4=s4 := by
  change step true 4 (history true 3)=s4
  rw [reached_3]
  exact cold_4
theorem cold_5 : step true 5 s4=s5 := by decide +kernel
theorem quiescent_5 : round true 5 (limit 5) s4.rows s4.saved s4.complete s5.data=s5.data := by decide +kernel
theorem reached_5 : history true 5=s5 := by
  change step true 5 (history true 4)=s5
  rw [reached_4]
  exact cold_5
theorem cold_6 : step true 6 s5=s6 := by decide +kernel
theorem quiescent_6 : round true 6 (limit 6) s5.rows s5.saved s5.complete s6.data=s6.data := by decide +kernel
theorem reached_6 : history true 6=s6 := by
  change step true 6 (history true 5)=s6
  rw [reached_5]
  exact cold_6
theorem natural_stop : stopped 5 s5=true ∧ s5.report=true := by decide +kernel
theorem normal_observation_run3 : s3.report=true := by decide +kernel
theorem quiet_after_stop : s6=quiet true s6.saved s6.complete := by decide +kernel
theorem uncapped_no_revival (n : Nat) : history true (n+6)=s6 := by
  induction n with
  | zero => exact reached_6
  | succ n ih =>
      change step true (n+7) (history true (n+6))=s6
      rw [ih,quiet_after_stop]
      exact quiet_never_restarts true _ _ _ _
end CompleteCold

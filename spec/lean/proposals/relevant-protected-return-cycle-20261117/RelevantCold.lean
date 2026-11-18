import RelevantFrozen
namespace RelevantCold
open RelevantReturn RelevantFrozen NonEmptyPolicy NonEmptyRestriction
set_option maxRecDepth 65536
set_option maxHeartbeats 320000000
theorem cold_1 : step true 1 s0=s1 := by decide +kernel
theorem quiescent_1 : round true 1 (limit 1) s0.rows s0.saved s0.complete s0.services s1.data=s1.data := by decide +kernel
theorem reached_1 : history true 1=s1 := by
  change step true 1 (history true 0)=s1
  change step true 1 s0=s1
  exact cold_1
theorem cold_2 : step true 2 s1=s2 := by decide +kernel
theorem quiescent_2 : round true 2 (limit 2) s1.rows s1.saved s1.complete s1.services s2.data=s2.data := by decide +kernel
theorem reached_2 : history true 2=s2 := by
  change step true 2 (history true 1)=s2
  rw [reached_1]
  exact cold_2
theorem cold_3 : step true 3 s2=s3 := by decide +kernel
theorem quiescent_3 : round true 3 (limit 3) s2.rows s2.saved s2.complete s2.services s3.data=s3.data := by decide +kernel
theorem reached_3 : history true 3=s3 := by
  change step true 3 (history true 2)=s3
  rw [reached_2]
  exact cold_3
theorem cold_4 : step true 4 s3=s4 := by decide +kernel
theorem quiescent_4 : round true 4 (limit 4) s3.rows s3.saved s3.complete s3.services s4.data=s4.data := by decide +kernel
theorem reached_4 : history true 4=s4 := by
  change step true 4 (history true 3)=s4
  rw [reached_3]
  exact cold_4
theorem cold_5 : step true 5 s4=s5 := by decide +kernel
theorem quiescent_5 : round true 5 (limit 5) s4.rows s4.saved s4.complete s4.services s5.data=s5.data := by decide +kernel
theorem reached_5 : history true 5=s5 := by
  change step true 5 (history true 4)=s5
  rw [reached_4]
  exact cold_5
theorem cold_6 : step true 6 s5=s6 := by decide +kernel
theorem quiescent_6 : round true 6 (limit 6) s5.rows s5.saved s5.complete s5.services s6.data=s6.data := by decide +kernel
theorem reached_6 : history true 6=s6 := by
  change step true 6 (history true 5)=s6
  rw [reached_5]
  exact cold_6
theorem cold_7 : step true 7 s6=s7 := by decide +kernel
theorem quiescent_7 : round true 7 (limit 7) s6.rows s6.saved s6.complete s6.services s7.data=s7.data := by decide +kernel
theorem reached_7 : history true 7=s7 := by
  change step true 7 (history true 6)=s7
  rw [reached_6]
  exact cold_7
theorem cold_8 : step true 8 s7=s8 := by decide +kernel
theorem quiescent_8 : round true 8 (limit 8) s7.rows s7.saved s7.complete s7.services s8.data=s8.data := by decide +kernel
theorem reached_8 : history true 8=s8 := by
  change step true 8 (history true 7)=s8
  rw [reached_7]
  exact cold_8
theorem cold_9 : step true 9 s8=s9 := by decide +kernel
theorem quiescent_9 : round true 9 (limit 9) s8.rows s8.saved s8.complete s8.services s9.data=s9.data := by decide +kernel
theorem reached_9 : history true 9=s9 := by
  change step true 9 (history true 8)=s9
  rw [reached_8]
  exact cold_9
theorem cold_10 : step true 10 s9=s10 := by decide +kernel
theorem quiescent_10 : round true 10 (limit 10) s9.rows s9.saved s9.complete s9.services s10.data=s10.data := by decide +kernel
theorem reached_10 : history true 10=s10 := by
  change step true 10 (history true 9)=s10
  rw [reached_9]
  exact cold_10
end RelevantCold

import Steady
import Cold
import Kernel
namespace ExcludedRecurrence
open ExcludedGuardCycle ExcludedFrozen ExcludedCold ExcludedSteady
open ExcludedRounds AlternatingCondition NonEmptyPolicy NonEmptyRestriction
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
local instance : BEq Row where beq a b := decide (a = b)
local instance : LawfulBEq Row where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
set_option maxRecDepth 65536
set_option maxHeartbeats 160000000

theorem every_uncapped_later_pair (n : Nat) :
    history true (2*n+7) = s7 ∧ history true (2*n+8) = s8 := by
  induction n with
  | zero => exact ⟨reached_7,reached_8⟩
  | succ n ih =>
      have first : history true (2*n+9) = s7 := by
        change step true (2*n+9) (history true (2*n+8)) = s7
        rw [ih.2]
        exact forward_at_every_later_run n
      have second : history true (2*n+10) = s8 := by
        change step true (2*n+10) (history true (2*n+9)) = s8
        rw [first]
        exact backward_at_every_later_run n
      simpa only [show 2*(n+1)+7 = 2*n+9 by omega,
        show 2*(n+1)+8 = 2*n+10 by omega] using And.intro first second

theorem both_forward_relations_remain_in_the_refinement_view (m : Color) :
    backwardRow m ∈ s7.rows := by cases m <;> decide +kernel

theorem both_backward_relations_remain_in_the_refinement_view (m : Color) :
    forwardRow m ∈ s8.rows := by cases m <;> decide +kernel

theorem the_same_demand_returns_after_every_later_forward_run (n : Nat) (m : Color) :
    backwardRow m ∈ (history true (2*n+7)).rows := by
  rw [(every_uncapped_later_pair n).1]
  exact both_forward_relations_remain_in_the_refinement_view m

theorem the_same_demand_returns_after_every_later_backward_run (n : Nat) (m : Color) :
    forwardRow m ∈ (history true (2*n+8)).rows := by
  rw [(every_uncapped_later_pair n).2]
  exact both_backward_relations_remain_in_the_refinement_view m

theorem no_later_forward_run_can_stop (n : Nat) :
    stopped (2*n+7) (history true (2*n+7)) = false := by
  rw [(every_uncapped_later_pair n).1]
  have rows : s7.rows.isEmpty = false := by decide +kernel
  simp [stopped,rows]

theorem no_stop_was_skipped_in_the_cold_prefix :
    stopped 1 s1 = false ∧ stopped 3 s3 = false ∧ stopped 5 s5 = false := by decide +kernel

theorem a_normal_report_does_not_cancel_the_repeating_target :
    s7.report = true ∧ s7.observationActive = true ∧ s8.sourceAllowed = true := by decide +kernel

theorem stable_frontier_and_persistence_sizes :
    s7.rows.length = 52 ∧ s8.rows.length = 58 ∧
    s7.saved.length = 12 ∧ s8.saved = s7.saved := by decide +kernel

theorem forward_fixed_point_is_not_an_eight_round_timeout (n : Nat) :
    round true 5 (n+4) s8.rows s8.saved s7.data = s7.data := by
  exact roundF8 n

theorem backward_fixed_point_is_not_an_eight_round_timeout (n : Nat) :
    round true 6 (n+4) s7.rows s7.saved s8.data = s8.data := by
  exact roundB8 n
end ExcludedRecurrence

import DeeperSteady
import DeeperCold
import DeeperKernel
namespace DeeperRecurrence
open DeeperExcluded DeeperFrozen DeeperCold DeeperSteady
open DeeperRounds AlternatingCondition NonEmptyPolicy NonEmptyRestriction
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
    history true (2*n+9) = s9 ∧ history true (2*n+10) = s10 := by
  induction n with
  | zero => exact ⟨reached_9,reached_10⟩
  | succ n ih =>
      have first : history true (2*n+11) = s9 := by
        change step true (2*n+11) (history true (2*n+10)) = s9
        rw [ih.2]
        exact forward_at_every_later_run n
      have second : history true (2*n+12) = s10 := by
        change step true (2*n+12) (history true (2*n+11)) = s10
        rw [first]
        exact backward_at_every_later_run n
      simpa only [show 2*(n+1)+9 = 2*n+11 by omega,
        show 2*(n+1)+10 = 2*n+12 by omega] using And.intro first second

theorem both_forward_relations_remain_in_the_refinement_view (m : Color) :
    backwardRow m ∈ s9.rows := by cases m <;> decide +kernel

theorem both_backward_relations_remain_in_the_refinement_view (m : Color) :
    forwardRow m ∈ s10.rows := by cases m <;> decide +kernel

theorem the_same_demand_returns_after_every_later_forward_run (n : Nat) (m : Color) :
    backwardRow m ∈ (history true (2*n+9)).rows := by
  rw [(every_uncapped_later_pair n).1]
  exact both_forward_relations_remain_in_the_refinement_view m

theorem the_same_demand_returns_after_every_later_backward_run (n : Nat) (m : Color) :
    forwardRow m ∈ (history true (2*n+10)).rows := by
  rw [(every_uncapped_later_pair n).2]
  exact both_backward_relations_remain_in_the_refinement_view m

theorem no_later_forward_run_can_stop (n : Nat) :
    stopped (2*n+9) (history true (2*n+9)) = false := by
  rw [(every_uncapped_later_pair n).1]
  have rows : s9.rows.isEmpty = false := by decide +kernel
  simp [stopped,rows]

theorem no_stop_was_skipped_in_the_cold_prefix :
    stopped 1 s1 = false ∧ stopped 3 s3 = false ∧ stopped 5 s5 = false ∧ stopped 7 s7 = false := by decide +kernel

theorem a_normal_report_does_not_cancel_the_repeating_target :
    s9.report = true ∧ s9.observationActive = true ∧ s10.sourceAllowed = true := by decide +kernel

theorem stable_frontier_and_persistence_sizes :
    s9.rows.length = 73 ∧ s10.rows.length = 83 ∧
    s9.saved.length = 12 ∧ s10.saved = s9.saved := by decide +kernel

theorem forward_fixed_point_is_not_an_eight_round_timeout (n : Nat) :
    round true 5 (n+8) s10.rows s10.saved s9.data = s9.data := by
  exact roundF8 n

theorem backward_fixed_point_is_not_an_eight_round_timeout (n : Nat) :
    round true 6 (n+8) s9.rows s9.saved s10.data = s10.data := by
  exact roundB8 n
end DeeperRecurrence

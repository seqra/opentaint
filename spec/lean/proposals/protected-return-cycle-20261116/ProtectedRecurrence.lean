import ProtectedSteady
import ProtectedCold
import ProtectedKernel
import ExactKernel
namespace ProtectedRecurrence
open ProtectedReturn ProtectedFrozen ProtectedCold ProtectedSteady
open ProtectedRounds AlternatingCondition NonEmptyPolicy NonEmptyRestriction
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

def backwardRow (m : Color) : Row := ⟨fact ret [h] .may m.flip,fact p [f] .star m⟩
def forwardRow (m : Color) : Row := ⟨fact p [] .may m,fact ret [h] .star m.flip⟩

theorem every_uncapped_later_pair (n : Nat) :
    history true (2*n+11) = forward ∧ history true (2*n+12) = s12 := by
  induction n with
  | zero => exact ⟨reached_11,reached_12⟩
  | succ n ih =>
      have first : history true (2*n+13) = forward := by
        change step true (2*n+13) (history true (2*n+12)) = forward
        rw [ih.2]
        exact forward_at_every_later_run (n+1)
      have second : history true (2*n+14) = s12 := by
        change step true (2*n+14) (history true (2*n+13)) = s12
        rw [first]
        exact backward_at_every_later_run (n+1)
      simpa only [show 2*(n+1)+11 = 2*n+13 by omega,
        show 2*(n+1)+12 = 2*n+14 by omega] using And.intro first second

theorem both_forward_relations_remain_in_the_refinement_view (m : Color) :
    backwardRow m ∈ forward.rows := by cases m <;> decide +kernel

theorem both_backward_relations_remain_in_the_refinement_view (m : Color) :
    forwardRow m ∈ s12.rows := by cases m <;> decide +kernel

theorem the_same_demand_returns_after_every_later_forward_run (n : Nat) (m : Color) :
    backwardRow m ∈ (history true (2*n+11)).rows := by
  rw [(every_uncapped_later_pair n).1]
  exact both_forward_relations_remain_in_the_refinement_view m

theorem the_same_demand_returns_after_every_later_backward_run (n : Nat) (m : Color) :
    forwardRow m ∈ (history true (2*n+12)).rows := by
  rw [(every_uncapped_later_pair n).2]
  exact both_backward_relations_remain_in_the_refinement_view m

theorem no_later_forward_run_can_stop (n : Nat) :
    stopped (2*n+11) (history true (2*n+11)) = false := by
  rw [(every_uncapped_later_pair n).1]
  have rows : forward.rows.isEmpty = false := by decide +kernel
  simp [stopped,rows]

theorem no_stop_was_skipped_in_the_cold_prefix :
    stopped 1 s1 = false ∧ stopped 3 s3 = false ∧ stopped 5 s5 = false ∧ stopped 7 s7 = false ∧ stopped 9 s9=false := by decide +kernel

theorem a_normal_report_does_not_cancel_the_repeating_target :
    forward.report = true ∧ forward.observationActive = true ∧ s12.sourceAllowed = true := by decide +kernel

theorem stable_frontier_and_persistence_sizes :
    forward.rows.length = 70 ∧ s12.rows.length = 82 ∧
    forward.saved.length = 10 ∧ s12.saved = forward.saved := by decide +kernel

theorem forward_fixed_point_is_not_an_eight_round_timeout (n : Nat) :
    round true 5 (n+8) s12.rows s12.saved s12.complete s12.services forward.data = forward.data := by
  exact roundF8 n

theorem backward_fixed_point_is_not_an_eight_round_timeout (n : Nat) :
    round true 6 (n+8) forward.rows forward.saved forward.complete forward.services s12.data = s12.data := by
  exact roundB8 n

def allProtectedExclusionsEmpty (s : State) : Bool :=
  s.rows.all (fun r => r.entry.e.isEmpty && r.exit.e.isEmpty) &&
  s.saved.all (fun r => r.edge.1.e.isEmpty && r.edge.2.ap.e.isEmpty) &&
  s.data.domains.all (fun a => a.ap.e.isEmpty) &&
  s.data.raw.all (fun e => e.1.e.isEmpty && e.2.ap.e.isEmpty) &&
  s.data.offers.all (fun vs => vs.all (fun v => v.ap.e.isEmpty))

theorem no_field_exclusions_in_the_entire_cold_prefix :
    [s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s12,forward].all allProtectedExclusionsEmpty=true := by decide +kernel

theorem no_field_exclusions_in_any_later_pair (n : Nat) :
    allProtectedExclusionsEmpty (history true (2*n+11))=true ∧
    allProtectedExclusionsEmpty (history true (2*n+12))=true := by
  rw [(every_uncapped_later_pair n).1,(every_uncapped_later_pair n).2]
  decide +kernel

theorem domain_E_is_empty (s : State) (noE : allProtectedExclusionsEmpty s=true)
    (a : Offered) (inside : a ∈ s.data.domains) : a.ap.e=[] := by
  unfold allProtectedExclusionsEmpty at noE
  simp only [Bool.and_eq_true] at noE
  have yes := List.all_eq_true.mp noE.1.1.2 a inside
  cases he : a.ap.e <;> simp_all

theorem every_later_forward_offer_uses_only_the_original_entry_cap
    (n run k : Nat) (back : Bool) (d : Ap) (a : Offered) (q : Seed)
    (offered : a ∈ (history true (2*n+11)).data.domains)
    (emitted : q ∈ HeadPolicy.emit run k back d a) :
    q.ap.path.length≤k ∧ q.ap.path.length≤d.path.length+1 := by
  exact ExactKernel.all_Empty_E_offers_keep_the_original_entry_cap run k back d a q
    (domain_E_is_empty _ (no_field_exclusions_in_any_later_pair n).1 a offered) emitted

theorem every_later_backward_offer_uses_only_the_original_entry_cap
    (n run k : Nat) (back : Bool) (d : Ap) (a : Offered) (q : Seed)
    (offered : a ∈ (history true (2*n+12)).data.domains)
    (emitted : q ∈ HeadPolicy.emit run k back d a) :
    q.ap.path.length≤k ∧ q.ap.path.length≤d.path.length+1 := by
  exact ExactKernel.all_Empty_E_offers_keep_the_original_entry_cap run k back d a q
    (domain_E_is_empty _ (no_field_exclusions_in_any_later_pair n).2 a offered) emitted

def preparedWithinCaps (run k : Nat) (rows : List Row) (saved : List Saved) (d : Data) : Bool :=
  d.domains.all fun a => rows.all fun row =>
    (prepare run k (run % 2 == 0) row rows saved a).all fun q =>
      decide (q.ap.path.length≤k ∧ q.ap.path.length≤row.entry.path.length+1)

theorem complete_steady_prepared_families_keep_both_input_caps (n : Nat) :
    preparedWithinCaps 5 (n+8) s12.rows s12.saved forward.data=true ∧
    preparedWithinCaps 6 (n+8) forward.rows forward.saved s12.data=true := by kernel_decide_open
theorem every_later_forward_run_fails_all_three_completion_checks (n : Nat) :
    (history true (2*n+11)).complete=[] ∧
    (history true (2*n+11)).services=[] ∧
    (history true (2*n+11)).data.closed=[] := by
  rw [(every_uncapped_later_pair n).1]
  decide +kernel

theorem the_protected_other_return_blocks_every_later_point_check (n k : Nat) :
    bodyClosed k ProtectedKernel.point=false ∧
    ReplyCore.completeFor (history true (2*n+11)).data.raw ProtectedKernel.point
      (colors.flatMap fun m => gen m ProtectedKernel.point) ProtectedKernel.region=false := by
  exact ⟨ProtectedKernel.body_closed_rejects_every_supported_input_at_every_limit .t _ k rfl rfl,
    ProtectedKernel.reply_region_eligibility_also_rejects_the_protected_other_return .t _ _ _ rfl rfl⟩

end ProtectedRecurrence

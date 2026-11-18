import BoundFamilyBatch0
import BoundFamilyBatch1
import BoundFamilyBatch2
import BoundFamilyBatch3
import BoundFamilyBatch4
import BoundFamilyBatch5
import BoundFamilyBatch6
import BoundFamilyBatch7
import BoundFamilyBatch8
import BoundFamilyBatch9
import BoundFamilyBatch10
import BoundFamilyBatch11
import BoundFamilyBatch12
import BoundFamilyBatch13
import BoundFamilyBatch14
import BoundFamilyBatch15
import BoundFamilyBatch16
import BoundFamilyBatch17
import BoundFamilyBatch18
import BoundFamilyBatch19
import BoundFamilyBatch20
namespace BoundFamilyProof
open NonEmptyPolicy NonEmptyRestriction BoundFamily BoundFamilyCases
set_option maxRecDepth 65536
set_option maxHeartbeats 320000000
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl

def chunks : List (List Config) := [chunk 0, chunk 1, chunk 2, chunk 3, chunk 4, chunk 5, chunk 6, chunk 7, chunk 8, chunk 9, chunk 10, chunk 11, chunk 12, chunk 13, chunk 14, chunk 15, chunk 16, chunk 17, chunk 18, chunk 19, chunk 20]

theorem chunks_are_the_complete_finite_scope : chunks.flatten=cases := by decide +kernel

theorem all_finite_configurations_have_a_natural_empty_frontier : cases.all checked=true := by
  rw [←chunks_are_the_complete_finite_scope]
  simp only [List.all_flatten]
  simp only [chunks,List.all_cons,List.all_nil,
    BoundFamilyBatch0.finite_family_naturally_stops_and_keeps_observations,
    BoundFamilyBatch1.finite_family_naturally_stops_and_keeps_observations,
    BoundFamilyBatch2.finite_family_naturally_stops_and_keeps_observations,
    BoundFamilyBatch3.finite_family_naturally_stops_and_keeps_observations,
    BoundFamilyBatch4.finite_family_naturally_stops_and_keeps_observations,
    BoundFamilyBatch5.finite_family_naturally_stops_and_keeps_observations,
    BoundFamilyBatch6.finite_family_naturally_stops_and_keeps_observations,
    BoundFamilyBatch7.finite_family_naturally_stops_and_keeps_observations,
    BoundFamilyBatch8.finite_family_naturally_stops_and_keeps_observations,
    BoundFamilyBatch9.finite_family_naturally_stops_and_keeps_observations,
    BoundFamilyBatch10.finite_family_naturally_stops_and_keeps_observations,
    BoundFamilyBatch11.finite_family_naturally_stops_and_keeps_observations,
    BoundFamilyBatch12.finite_family_naturally_stops_and_keeps_observations,
    BoundFamilyBatch13.finite_family_naturally_stops_and_keeps_observations,
    BoundFamilyBatch14.finite_family_naturally_stops_and_keeps_observations,
    BoundFamilyBatch15.finite_family_naturally_stops_and_keeps_observations,
    BoundFamilyBatch16.finite_family_naturally_stops_and_keeps_observations,
    BoundFamilyBatch17.finite_family_naturally_stops_and_keeps_observations,
    BoundFamilyBatch18.finite_family_naturally_stops_and_keeps_observations,
    BoundFamilyBatch19.finite_family_naturally_stops_and_keeps_observations,
    BoundFamilyBatch20.finite_family_naturally_stops_and_keeps_observations  ]
  rfl

theorem every_finite_member_stops_without_using_a_policy_cutoff
    (cfg : Config) (inside : cfg∈cases) :
    stopped 9 (history cfg true 9)=true ∧
    (history cfg true 9).report = !(concreteOutcome cfg).isEmpty := by
  have yes := List.all_eq_true.mp all_finite_configurations_have_a_natural_empty_frontier cfg inside
  simp only [checked,Bool.and_eq_true] at yes
  exact ⟨yes.1,by simpa using yes.2⟩

theorem next_backward_state_is_quiet_after_an_empty_forward_frontier
    (cfg : Config) (state : State) (done : stopped 9 state=true) :
    step cfg true 10 state=quiet cfg state.report state.saved state.complete state.services := by
  have hs := done
  simp only [stopped,Bool.and_eq_true] at hs
  have noTarget : state.observationActive=false := by simpa using hs.2
  simp [step,stepWithLimit,noTarget]

theorem finite_member_stays_quiet_for_all_later_uncapped_runs
    (cfg : Config) (inside : cfg∈cases) (n : Nat) :
    history cfg true (n+10) = quiet cfg (history cfg true 9).report
      (history cfg true 9).saved (history cfg true 9).complete (history cfg true 9).services := by
  induction n with
  | zero =>
      change step cfg true 10 (history cfg true 9)=_
      exact next_backward_state_is_quiet_after_an_empty_forward_frontier cfg _
        (every_finite_member_stops_without_using_a_policy_cutoff cfg inside).1
  | succ n ih =>
      change step cfg true (n+11) (history cfg true (n+10))=_
      rw [ih]
      exact quiet_never_restarts cfg true _ _ _ _ _

end BoundFamilyProof

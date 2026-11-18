import DefiniteMustReplay

namespace DefiniteMustPrior
open NonEmptyPolicy NonEmptyRestriction
open NestedColdMachine OverwriteReplay
set_option maxRecDepth 32768
set_option maxHeartbeats 80000000
set_option linter.unusedSimpArgs false
local instance : LawfulBEq Tail where
  rfl := by intro a; cases a <;> rfl
  eq_of_beq := by intro a b h; cases a <;> cases b <;> first | rfl | cases h

def filteredReference (inside : Bool) (e : Ap × Value) (a : Offered) : Option Offered :=
  if e.1.tail != .must || DefiniteMustReplay.covers a.ap e.1 then apply inside e a else none

/-- The complete earlier multi-owner reference ALREADY used the definite
    MUST gate, including E. The candidate therefore changes none of its
    saved-call, current-call, opposite-view or ready-probe evaluations. -/
theorem earlier_reference_service_is_exactly_unchanged (inside : Bool) (e : Ap × Value) (a : Offered) :
    filteredReference inside e a = apply inside e a := by
  cases he : e.1.tail <;> cases ha : a.ap.tail <;>
    simp [filteredReference,DefiniteMustReplay.covers,OverwriteReplay.apply,he,ha]
  cases h : dropHead a.ap.path e.1.path with
  | none => simp [h]
  | some rest =>
      cases rest with
      | nil => cases hx : a.ap.e.all e.1.e.contains <;> simp [h,hx]
      | cons field more => cases hx : a.ap.e.contains field <;> simp [h,hx]

def finalStates : List (State × List (List Row) × Bool) := [
  (PointDouble.state15,PointDouble.rows15,true),
  (PointGrowth.state11,PointGrowth.rows11,true),
  (PointLongReader.state5,PointLongReader.rows5,true),
  (PointNested.state9,PointNested.rows9,true),
  (PointNestedDeep.state5,PointNestedDeep.rows5,true),
  (PointNestedExact.state3,PointNestedExact.rows3,true),
  (PointNestedLarger.state11,PointNestedLarger.rows11,true),
  (PointNestedNegative.state3,PointNestedNegative.rows3,false),
  (PointNestedPositive.state3,PointNestedPositive.rows3,true),
  (PointNestedSurvivor.state5,PointNestedSurvivor.rows5,true),
  (PointOldBB.state5,PointOldBB.rows5,true),
  (PointOldMethod.state5,PointOldMethod.rows5,true),
  (PointOrdinaryTwo.state3,PointOrdinaryTwo.rows3,true),
  (PointOverwrite.state9,PointOverwrite.rows9,true),
  (PointPostfix.state13,PointPostfix.rows13,true),
  (PointPrefix.state9,PointPrefix.rows9,false),
  (PointPrefixPostfix.state11,PointPrefixPostfix.rows11,true),
  (PointRoundTrip.state9,PointRoundTrip.rows9,true)]

def observation (a : Offered) : TargetZeroKernel.Summary :=
  TargetZeroKernel.forwardSinkTarget 0 .zero (if a.demand then .demand else .normal) 0

theorem all_eighteen_final_frontiers_are_empty :
    finalStates.length = 18 ∧ finalStates.all (fun x => x.2.1.all List.isEmpty &&
      !(x.1.offers.getLast!.map observation).any TargetZeroKernel.continuationRelevant) = true := by decide

theorem all_eighteen_expected_report_sets_are_preserved :
    finalStates.all (fun x => decide (TargetZeroKernel.collectReports [0]
      (x.1.offers.getLast!.map observation) = if x.2.2 then [0] else [])) = true := by decide

theorem protected_closure_native_reads_already_require_uniform_support
    (record : Ap × Value) (actual result : Value)
    (hit : SameLaneMarkedClosure.normalApply record actual = some result)
    (must : record.1.tail = .must) :
    actual.ap.tail = .must ∧ (dropHead actual.ap.path record.1.path).isSome = true := by
  unfold SameLaneMarkedClosure.normalApply at hit
  split at hit
  · contradiction
  · split at hit
    · contradiction
    · simp only [must,beq_self_eq_true,ite_true] at hit
      split at hit
      · contradiction
      · rename_i admitted
        have good : ¬ (actual.ap.tail != .must || !(dropHead actual.ap.path record.1.path).isSome) = true := admitted
        cases ht : actual.ap.tail <;> cases hp : (dropHead actual.ap.path record.1.path).isSome <;>
          simp_all

theorem protected_e_free_read_satisfies_the_candidate_gate
    (record : Ap × Value) (actual result : Value)
    (hit : SameLaneMarkedClosure.normalApply record actual = some result)
    (must : record.1.tail = .must) (emptyE : actual.ap.e = []) :
    DefiniteMustReplay.covers actual.ap record.1 = true := by
  have supported := protected_closure_native_reads_already_require_uniform_support record actual result hit must
  cases hp : dropHead actual.ap.path record.1.path with
  | none => simp [hp] at supported
  | some rest => cases rest <;> simp [DefiniteMustReplay.covers,supported.1,emptyE,hp]

theorem protected_cold_reply_geometry_is_e_free :
    SameLaneMarkedClosure.sourceOffer.ap.e = [] ∧
    (SameLaneMarkedClosure.firstReplies ++ SameLaneMarkedClosure.secondReplies).all
      (fun value => value.ap.e.isEmpty) = true := by decide

end DefiniteMustPrior

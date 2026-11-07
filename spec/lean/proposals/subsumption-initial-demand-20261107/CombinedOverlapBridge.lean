/-
Prepared bridge only. No matcher, exclusion, C2/C5 or layer definition is
changed. Maximal combined endpoint-E coverage is linked to the already
defined same-original-actual effect, in direct and generic reverse directions.
-/
import CombinedExclusionCoverage
import StarHeadOverlap

namespace CombinedOverlapBridge
open ExclusionCorrelatedInclusion
open CombinedExclusionCoverage
open StarHeadOverlap

theorem combined_criterion_preserves_every_actual_effect (short long : Row)
    (residual : List Nat) (actual : Actual) (pair : FlowAntichains.Relations.Pair Nat)
    (covered : coveringCriterion short long residual = true) (member : effect long actual pair) :
    effect short actual pair := by
  obtain ⟨mark,base,input,record⟩ := member
  exact ⟨mark,base,input,
    combined_criterion_transports_every_pair short long residual covered pair record⟩

theorem combined_exclusion_criterion_survives_reversal (short long : Row)
    (residual : List Nat) (checked : exclusionCriterion short long residual = true) :
    exclusionCriterion (inverseRow short) (inverseRow long) residual = true := by
  cases residual with
  | nil =>
    change subsetB (combinedE short) (combinedE long) = true at checked
    change subsetB (combinedE (inverseRow short)) (combinedE (inverseRow long)) = true
    apply List.all_eq_true.mpr
    intro field member
    have original : field ∈ combinedE short := by
      simpa only [combinedE,inverseRow,List.mem_append,or_comm] using member
    have included := subsetB_sound _ _ checked field original
    apply decide_eq_true
    simpa only [combinedE,inverseRow,List.mem_append,or_comm] using included
  | cons first rest =>
    have original : first ∉ combinedE short := of_decide_eq_true checked
    apply decide_eq_true
    simpa only [combinedE,inverseRow,List.mem_append,or_comm] using original

theorem combined_pair_coverage_survives_generic_reversal (short long : Row)
    (residual : List Nat) (covered : coveringCriterion short long residual = true) :
    coveringCriterion (inverseRow short) (inverseRow long) residual = true := by
  obtain ⟨geometry,marks,excluded⟩ := of_decide_eq_true covered
  apply decide_eq_true
  refine ⟨?_,marks,
    combined_exclusion_criterion_survives_reversal short long residual excluded⟩
  change FlowAntichains.Relations.specialize
    (FlowAntichains.Relations.reverseGeometry short.geometry) residual =
    FlowAntichains.Relations.reverseGeometry long.geometry
  rw [← FlowAntichains.Relations.reverse_geometry_specializes,geometry]

theorem inverse_combined_criterion_keeps_every_actual_effect (short long : Row)
    (residual : List Nat) (actual : Actual) (pair : FlowAntichains.Relations.Pair Nat)
    (covered : coveringCriterion short long residual = true)
    (member : effect (inverseRow long) actual pair) : effect (inverseRow short) actual pair :=
  combined_criterion_preserves_every_actual_effect (inverseRow short) (inverseRow long)
    residual actual pair
    (combined_pair_coverage_survives_generic_reversal short long residual covered) member

end CombinedOverlapBridge

#print axioms CombinedOverlapBridge.combined_criterion_preserves_every_actual_effect
#print axioms CombinedOverlapBridge.combined_exclusion_criterion_survives_reversal
#print axioms CombinedOverlapBridge.combined_pair_coverage_survives_generic_reversal
#print axioms CombinedOverlapBridge.inverse_combined_criterion_keeps_every_actual_effect

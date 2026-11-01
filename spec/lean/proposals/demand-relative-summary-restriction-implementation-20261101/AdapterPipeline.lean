import Integration
import Controls

/-!
Implementation-adapter laws. The scalar gate is the existing executable
Restriction/Integration gate. List leaves are a finite reference for packed
union and deltas; optimized Kotlin DAG/mark-mask adapters are not verified here.
Typed Reach has a singleton possible output, so its result set saturates after
the first admitted row. DATA collection does not use that shortcut.
-/
namespace RelativeImplementation
open RelativeRestriction
set_option autoImplicit false

def gateLeaves (context : Context) (rows : List Row) (leaves : List Integration.Summary) :
    List Integration.Summary := leaves.flatMap (Integration.gate context rows)

theorem gate_distributes_over_leaf_append (context : Context) (rows : List Row)
    (left right : List Integration.Summary) :
    gateLeaves context rows (left ++ right) =
      gateLeaves context rows left ++ gateLeaves context rows right := by
  simp only [gateLeaves, List.flatMap_append]

theorem gate_leaf_membership (context : Context) (rows : List Row)
    (leaves : List Integration.Summary) (output : Integration.Summary) :
    output ∈ gateLeaves context rows leaves ↔
      ∃ leaf, leaf ∈ leaves ∧ output ∈ Integration.gate context rows leaf := by
  exact List.mem_flatMap

/-- Post-statement fresh-leaf deltas suffice for a fixed pure gate. The
annotation adapter must expose protection/layer growth as semantic deltas. -/
theorem post_statement_delta_is_sufficient (context : Context) (rows : List Row)
    (whole old fresh : List Integration.Summary)
    (deltaLaw : ∀ leaf, leaf ∈ whole ↔ leaf ∈ old ∨ leaf ∈ fresh)
    (output : Integration.Summary) :
    output ∈ gateLeaves context rows whole ↔
      output ∈ gateLeaves context rows old ∨ output ∈ gateLeaves context rows fresh := by
  simp only [gate_leaf_membership]
  constructor
  · rintro ⟨leaf, present, selected⟩
    rcases (deltaLaw leaf).mp present with previous | added
    · exact Or.inl ⟨leaf, previous, selected⟩
    · exact Or.inr ⟨leaf, added, selected⟩
  · rintro (⟨leaf, present, selected⟩ | ⟨leaf, present, selected⟩)
    · exact ⟨leaf, (deltaLaw leaf).mpr (Or.inl present), selected⟩
    · exact ⟨leaf, (deltaLaw leaf).mpr (Or.inr present), selected⟩

theorem same_leaf_set_has_same_gate_set (context : Context) (rows : List Row)
    (left right : List Integration.Summary)
    (same : ∀ leaf, leaf ∈ left ↔ leaf ∈ right)
    (output : Integration.Summary) :
    output ∈ gateLeaves context rows left ↔ output ∈ gateLeaves context rows right := by
  simp only [gate_leaf_membership]
  constructor
  · rintro ⟨leaf, present, selected⟩
    exact ⟨leaf, (same leaf).mp present, selected⟩
  · rintro ⟨leaf, present, selected⟩
    exact ⟨leaf, (same leaf).mpr present, selected⟩

/-- Every packed-reference result retains a single actual complete row. -/
theorem packed_result_has_pair_witness (context : Context) (rows : List Row)
    (leaves : List Integration.Summary) (output : Integration.Summary)
    (present : output ∈ gateLeaves context rows leaves) :
    ∃ leaf, leaf ∈ leaves ∧ output.initial = leaf.initial ∧
      ∃ row, row ∈ rows ∧ restrictRow context row leaf.initial leaf.result = some output.result := by
  obtain ⟨leaf, inLeaves, selected⟩ := (gate_leaf_membership context rows leaves output).mp present
  obtain ⟨sameInitial, row, inRows, kept⟩ := Integration.gate_has_concrete_pair_witness context rows leaf output selected
  exact ⟨leaf, inLeaves, sameInitial, row, inRows, kept⟩

namespace Reach
open RelativeControls

theorem pair_result_is_original_reach (meet : AP → AP → Option AP) (limit : Nat)
    (original : Original) (layer : RelativeControls.Layer) (pair : Pair)
    (output : Candidate)
    (accepted : admitPair meet limit original (.reach layer) pair = some output) :
    output = .reach layer := by
  unfold admitPair at accepted
  split at accepted
  · cases exit : pair.exit with
    | zero => simpa only [exit, Option.some.injEq] using accepted.symm
    | data selector => simp only [exit] at accepted; cases accepted
  · contradiction

theorem any_result_is_original_reach (meet : AP → AP → Option AP) (limit : Nat)
    (original : Original) (layer : RelativeControls.Layer) (pairs : List Pair)
    (output : Candidate)
    (present : output ∈ admitted meet limit original (.reach layer) pairs) :
    output = .reach layer := by
  obtain ⟨pair, _, selected⟩ := List.mem_filterMap.mp present
  exact pair_result_is_original_reach meet limit original layer pair output selected

/-- Once a Reach is found, every further accepted row adds the same element.
This is semantic-set saturation, independent of callback counts or ordering. -/
theorem first_reach_saturates_result_set (meet : AP → AP → Option AP) (limit : Nat)
    (original : Original) (layer : RelativeControls.Layer) (visited remaining : List Pair)
    (found : Candidate.reach layer ∈ admitted meet limit original (.reach layer) visited)
    (output : Candidate) :
    output ∈ admitted meet limit original (.reach layer) (visited ++ remaining) ↔
      output ∈ admitted meet limit original (.reach layer) visited := by
  constructor
  · intro present
    have same := any_result_is_original_reach meet limit original layer (visited ++ remaining) output present
    simpa only [same] using found
  · intro present
    obtain ⟨pair, member, accepted⟩ := List.mem_filterMap.mp present
    exact List.mem_filterMap.mpr ⟨pair, List.mem_append_left remaining member, accepted⟩

theorem pair_reach_iff_complete_permission (meet : AP → AP → Option AP) (limit : Nat)
    (original : Original) (layer : RelativeControls.Layer) (pair : Pair) :
    admitPair meet limit original (.reach layer) pair = some (.reach layer) ↔
      targetPairAccepts original pair = true := by
  cases pair with
  | mk entry exit =>
    cases exit <;> simp [admitPair, targetPairAccepts]

/-- Same complete-row enumeration can serve Target's Boolean existence probe.
Do not replace its static traversal with a local-only control lookup. -/
theorem target_probe_iff_nonempty_reach_result (meet : AP → AP → Option AP) (limit : Nat)
    (original : Original) (layer : RelativeControls.Layer) (pairs : List Pair) :
    pairs.any (targetPairAccepts original) = true ↔
      Candidate.reach layer ∈ admitted meet limit original (.reach layer) pairs := by
  simp only [List.any_eq_true, admitted, List.mem_filterMap]
  constructor
  · rintro ⟨pair, member, permission⟩
    exact ⟨pair, member, (pair_reach_iff_complete_permission meet limit original layer pair).mpr permission⟩
  · rintro ⟨pair, member, selected⟩
    exact ⟨pair, member, (pair_reach_iff_complete_permission meet limit original layer pair).mp selected⟩

end Reach

namespace Views
open RelativeControls

structure Stored where
  original : Original
  value : Candidate
  deriving DecidableEq, Repr

def frontier (direction : Direction) (rows : List Stored) : List Stored :=
  rows.filter fun row => outgoingAP direction row.original row.value

/-- Mechanical header extraction for the Kotlin selectDemand adapter. -/
def selectedHeader (direction : Direction) (original : Original)
    (layer : RelativeControls.Layer) : Bool :=
  if layer == .demand then true else
    match original with
    | .nd _ => true
    | .zero => direction == .backward
    | .single _ => false

theorem header_selection_matches_existing_rule (direction : Direction)
    (original : Original) (value : Candidate) :
    selectedHeader direction original (candidateLayer value) = outgoingAP direction original value := by
  cases layer : candidateLayer value <;> cases original <;> cases direction <;>
    simp only [selectedHeader, outgoingAP, layer] <;> rfl

theorem frontier_is_final_admitted_view (direction : Direction) (rows : List Stored) (row : Stored) :
    row ∈ frontier direction rows ↔ row ∈ rows ∧ outgoingAP direction row.original row.value = true := by
  exact List.mem_filter

theorem ordinary_normal_singleton_is_not_guidance (direction : Direction) (key : Nat)
    (ap : AP) (normal : ap.layer = .normal) :
    outgoingAP direction (.single key) (.data ap) = false := by
  cases direction <;> simp only [outgoingAP, candidateLayer, normal]

theorem all_final_demand_rows_are_guidance (direction : Direction) (original : Original)
    (ap : AP) (demand : ap.layer = .demand) :
    outgoingAP direction original (.data ap) = true := by
  simp only [outgoingAP, candidateLayer, demand]

/-- Diagonal header selection does not depend on the decoded concrete mark or
singleton key. ND and ZERO are not diagonal scopes. -/
theorem diagonal_header_selection_is_key_independent (direction : Direction) (left right : Nat)
    (ap : AP) :
    outgoingAP direction (.single left) (.data ap) = outgoingAP direction (.single right) (.data ap) := by
  cases direction <;> cases layer : ap.layer <;> simp only [outgoingAP, candidateLayer, layer]

end Views
end RelativeImplementation

import Std
import ExclusionCorrelatedInclusion

/-!
Prepared supplement: full combined-endpoint-E criterion for correlated STAR
pair inclusion. Pair24 remains unchanged. Native overlap matching is a
separate selected semantic change and is not assumed as an equivalence axiom.
-/
namespace CombinedExclusionCoverage
open ExclusionCorrelatedInclusion
set_option autoImplicit false

def combinedE (row : Row) : List Nat := row.inputE ++ row.outputE

def exclusionCriterion (short long : Row) (residual : List Nat) : Bool :=
  match residual with
  | [] => subsetB (combinedE short) (combinedE long)
  | first :: rest => admits (combinedE short) (first :: rest)

def coveringCriterion (short long : Row) (residual : List Nat) : Bool :=
  decide (FlowAntichains.Relations.specialize short.geometry residual = long.geometry ∧
    subsetB short.excludedMarks long.excludedMarks = true ∧
    exclusionCriterion short long residual = true)

def computedWitness (short long : Row) : Option (List Nat) := do
  let residual ← FlowAntichains.Relations.coverWitness short.geometry long.geometry
  if coveringCriterion short long residual then some residual else none

theorem admits_append_iff_both (inputE outputE suffix : List Nat) :
    admits (inputE ++ outputE) suffix = true ↔
      admits inputE suffix = true ∧ admits outputE suffix = true := by
  cases suffix with
  | nil => simp [admits]
  | cons first rest => simp [admits,List.mem_append]

theorem combined_E_admits_iff_both_endpoints (row : Row) (suffix : List Nat) :
    admits (combinedE row) suffix = true ↔
      admits row.inputE suffix = true ∧ admits row.outputE suffix = true :=
  admits_append_iff_both row.inputE row.outputE suffix

theorem same_head_combined_E_subset_transports_both_exclusions
    (short long : Row) (suffix : List Nat)
    (included : subsetB (combinedE short) (combinedE long) = true)
    (inputAccepted : admits long.inputE suffix = true)
    (outputAccepted : admits long.outputE suffix = true) :
    admits short.inputE suffix = true ∧ admits short.outputE suffix = true := by
  have accepted := (combined_E_admits_iff_both_endpoints long suffix).mpr
    ⟨inputAccepted,outputAccepted⟩
  exact (combined_E_admits_iff_both_endpoints short suffix).mp
    (admits_mono _ _ _ included accepted)

theorem proper_residual_combined_E_is_exactly_both_first_field_tests
    (row : Row) (first : Nat) (rest : List Nat) :
    admits (combinedE row) (first :: rest) = true ↔
      first ∉ row.inputE ∧ first ∉ row.outputE := by
  simp [combinedE,admits,List.mem_append]

theorem exclusion_criterion_transports_both_endpoints (short long : Row)
    (residual suffix : List Nat) (checked : exclusionCriterion short long residual = true)
    (inputAccepted : admits long.inputE suffix = true)
    (outputAccepted : admits long.outputE suffix = true) :
    admits short.inputE (residual ++ suffix) = true ∧
      admits short.outputE (residual ++ suffix) = true := by
  cases residual with
  | nil =>
    exact same_head_combined_E_subset_transports_both_exclusions short long suffix
      checked inputAccepted outputAccepted
  | cons first rest =>
    have accepted : first ∉ combinedE short := of_decide_eq_true checked
    have extended := proper_residual_discharges_field_exclusions
      (combinedE short) first rest suffix accepted
    exact (combined_E_admits_iff_both_endpoints short ((first :: rest) ++ suffix)).mp extended

theorem combined_criterion_transports_every_pair (short long : Row) (residual : List Nat)
    (checked : coveringCriterion short long residual = true)
    (pair : FlowAntichains.Relations.Pair Nat) (member : denotes long pair) : denotes short pair := by
  obtain ⟨geometry,marks,exclusions⟩ := of_decide_eq_true checked
  obtain ⟨suffix,produced,inputAccepted,outputAccepted,markAccepted⟩ := member
  obtain ⟨inputAfter,outputAfter⟩ := exclusion_criterion_transports_both_endpoints
    short long residual suffix exclusions inputAccepted outputAccepted
  refine ⟨residual ++ suffix,?_,inputAfter,outputAfter,?_⟩
  · change FlowAntichains.Relations.produce short.geometry pair.mark
      (FlowAntichains.Relations.coveringSuffix residual suffix) = pair
    rw [← FlowAntichains.Relations.produced_specialization short.geometry residual suffix pair.mark,
      geometry]
    exact produced
  · exact markAdmits_mono _ _ _ marks markAccepted

theorem computed_witness_is_sound (short long : Row) (residual : List Nat)
    (found : computedWitness short long = some residual) :
    FlowAntichains.Relations.coverWitness short.geometry long.geometry = some residual ∧
      coveringCriterion short long residual = true := by
  unfold computedWitness at found
  cases located : FlowAntichains.Relations.coverWitness short.geometry long.geometry with
  | none => simp [located] at found
  | some chosen =>
    rw [located] at found
    change (if coveringCriterion short long chosen then some chosen else none) = some residual at found
    split at found
    next accepted =>
      have same : chosen = residual := Option.some.inj found
      subst residual
      exact ⟨rfl,accepted⟩
    next => cases found

theorem every_checked_residual_is_computed (short long : Row) (residual : List Nat)
    (checked : coveringCriterion short long residual = true) :
    computedWitness short long = some residual := by
  obtain ⟨geometry,_,_⟩ := of_decide_eq_true checked
  have located : FlowAntichains.Relations.coverWitness short.geometry long.geometry = some residual := by
    rw [← geometry]
    exact FlowAntichains.Relations.coverWitness_complete _ _
  simp [computedWitness,located,checked]

theorem computed_witness_iff_checked_criterion (short long : Row) (residual : List Nat) :
    computedWitness short long = some residual ↔ coveringCriterion short long residual = true :=
  ⟨fun found => (computed_witness_is_sound short long residual found).2,
    every_checked_residual_is_computed short long residual⟩

theorem computed_witness_supplies_every_pair (short long : Row) (residual : List Nat)
    (found : computedWitness short long = some residual)
    (pair : FlowAntichains.Relations.Pair Nat) (member : denotes long pair) : denotes short pair :=
  combined_criterion_transports_every_pair short long residual
    (computed_witness_is_sound short long residual found).2 pair member

def pairIncluded (short long : Row) : Prop :=
  ∀ pair, denotes long pair → denotes short pair

theorem checked_criterion_gives_pair_inclusion (short long : Row) (residual : List Nat)
    (checked : coveringCriterion short long residual = true) : pairIncluded short long :=
  combined_criterion_transports_every_pair short long residual checked

theorem pair_inclusion_is_transitive (first middle last : Row)
    (left : pairIncluded first middle) (right : pairIncluded middle last) :
    pairIncluded first last := fun pair member => left pair (right pair member)

theorem checked_rows_compose_without_an_admitted_intermediate (first middle last : Row)
    (leftResidual rightResidual : List Nat)
    (left : coveringCriterion first middle leftResidual = true)
    (right : coveringCriterion middle last rightResidual = true) : pairIncluded first last :=
  pair_inclusion_is_transitive first middle last
    (checked_criterion_gives_pair_inclusion first middle leftResidual left)
    (checked_criterion_gives_pair_inclusion middle last rightResidual right)

theorem composed_suffix_is_an_executable_geometry_witness (first middle last : Row)
    (leftResidual rightResidual suffix : List Nat) (mark : Nat)
    (left : FlowAntichains.Relations.specialize first.geometry leftResidual = middle.geometry)
    (right : FlowAntichains.Relations.specialize middle.geometry rightResidual = last.geometry) :
    FlowAntichains.Relations.produce first.geometry mark
      (FlowAntichains.Relations.coveringSuffix leftResidual
        (FlowAntichains.Relations.coveringSuffix rightResidual suffix)) =
      FlowAntichains.Relations.produce last.geometry mark suffix := by
  rw [← FlowAntichains.Relations.produced_specialization first.geometry leftResidual
    (FlowAntichains.Relations.coveringSuffix rightResidual suffix) mark,left]
  rw [← FlowAntichains.Relations.produced_specialization middle.geometry rightResidual suffix mark,right]

def redistributedShort : Row := ⟨⟨9,100,200,[10],[20]⟩,[3],[],[]⟩
def redistributedLong : Row := ⟨⟨9,100,200,[10],[20]⟩,[],[3],[]⟩

theorem redistributed_same_effective_E_is_covered :
    coveringCriterion redistributedShort redistributedLong [] = true ∧
    computedWitness redistributedShort redistributedLong = some [] := by decide

theorem redistributed_E_was_outside_pair24_componentwise_guard :
    coverAt redistributedShort redistributedLong [] = false := by decide

theorem proper_residual_keeps_pair24_general_two_endpoint_test :
    computedWitness exampleShort exampleLong = some [5] := by decide

theorem actual_exclusion_differences_are_not_erased_from_rows :
    redistributedShort.inputE = [3] ∧ redistributedShort.outputE = [] ∧
      redistributedLong.inputE = [] ∧ redistributedLong.outputE = [3] := by decide

end CombinedExclusionCoverage

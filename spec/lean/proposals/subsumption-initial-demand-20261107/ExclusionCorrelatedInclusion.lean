import Std
import Relations

/-!
Prepared only. Generalized paired STAR denotation, not a native matcher,
storage, observer or progress theorem. Bases are opaque Nat values; no
nonstatic assumption is needed by this algebra. Original Relations is copied
byte-identically. Field and mark exclusions here are finite lists.
-/
namespace ExclusionCorrelatedInclusion
set_option autoImplicit false

structure Row where
  geometry : FlowAntichains.Relations.Row Nat
  inputE : List Nat
  outputE : List Nat
  excludedMarks : List Nat
  deriving DecidableEq

def subsetB (small large : List Nat) : Bool :=
  small.all (fun field => decide (field ∈ large))

def admits (excluded suffix : List Nat) : Bool :=
  match suffix with
  | [] => true
  | field :: _ => decide (field ∉ excluded)

def markAdmits (excluded : List Nat) (mark : Nat) : Bool := decide (mark ∉ excluded)

def denotes (row : Row) (pair : FlowAntichains.Relations.Pair Nat) : Prop :=
  ∃ suffix, FlowAntichains.Relations.produce row.geometry pair.mark suffix = pair ∧
    admits row.inputE suffix = true ∧ admits row.outputE suffix = true ∧
    markAdmits row.excludedMarks pair.mark = true

/-- Empty residual uses the simple componentwise sufficient guard. This is
not claimed to be the most permissive combined-E test. A proper residual
discharges BOTH short endpoint exclusions at its first accessor. -/
def exclusionGuard (short long : Row) (residual : List Nat) : Prop :=
  match residual with
  | [] => subsetB short.inputE long.inputE = true ∧
      subsetB short.outputE long.outputE = true
  | first :: _ => first ∉ short.inputE ∧ first ∉ short.outputE

instance exclusionGuardDecidable (short long : Row) (residual : List Nat) :
    Decidable (exclusionGuard short long residual) := by
  unfold exclusionGuard
  cases residual <;> infer_instance

def coverAt (short long : Row) (residual : List Nat) : Bool :=
  decide (FlowAntichains.Relations.specialize short.geometry residual = long.geometry ∧
    subsetB short.excludedMarks long.excludedMarks = true ∧
    exclusionGuard short long residual)

def coverWitness (short long : Row) : Option (List Nat) := do
  let residual ← FlowAntichains.Relations.coverWitness short.geometry long.geometry
  if coverAt short long residual then some residual else none

theorem subsetB_sound (small large : List Nat) (checked : subsetB small large = true) :
    ∀ field, field ∈ small → field ∈ large := by
  intro field member
  exact of_decide_eq_true (List.all_eq_true.mp checked field member)

theorem subsetB_refl (fields : List Nat) : subsetB fields fields = true := by
  exact List.all_eq_true.mpr (fun field member => decide_eq_true member)

theorem admits_mono (small large suffix : List Nat)
    (included : subsetB small large = true) (accepted : admits large suffix = true) :
    admits small suffix = true := by
  cases suffix with
  | nil => rfl
  | cons first rest =>
    have absent : first ∉ large := of_decide_eq_true accepted
    apply decide_eq_true
    intro member
    exact absent (subsetB_sound small large included first member)

theorem markAdmits_mono (small large : List Nat) (mark : Nat)
    (included : subsetB small large = true) (accepted : markAdmits large mark = true) :
    markAdmits small mark = true := by
  have absent : mark ∉ large := of_decide_eq_true accepted
  apply decide_eq_true
  intro member
  exact absent (subsetB_sound small large included mark member)

theorem proper_residual_discharges_field_exclusions (excluded : List Nat)
    (first : Nat) (rest suffix : List Nat) (accepted : first ∉ excluded) :
    admits excluded ((first :: rest) ++ suffix) = true := by
  exact decide_eq_true accepted

theorem exclusion_guard_transports_both_ends (short long : Row) (residual suffix : List Nat)
    (guarded : exclusionGuard short long residual)
    (inputAccepted : admits long.inputE suffix = true)
    (outputAccepted : admits long.outputE suffix = true) :
    admits short.inputE (residual ++ suffix) = true ∧
    admits short.outputE (residual ++ suffix) = true := by
  cases residual with
  | nil =>
    exact ⟨admits_mono _ _ _ guarded.1 inputAccepted,
      admits_mono _ _ _ guarded.2 outputAccepted⟩
  | cons first rest =>
    exact ⟨proper_residual_discharges_field_exclusions _ _ _ _ guarded.1,
      proper_residual_discharges_field_exclusions _ _ _ _ guarded.2⟩

theorem generalized_cover_transports_every_pair (short long : Row) (residual : List Nat)
    (checked : coverAt short long residual = true) (pair : FlowAntichains.Relations.Pair Nat)
    (member : denotes long pair) : denotes short pair := by
  obtain ⟨geometry,marks,exclusions⟩ := of_decide_eq_true checked
  obtain ⟨suffix,produced,inputAccepted,outputAccepted,markAccepted⟩ := member
  obtain ⟨inputAfter,outputAfter⟩ :=
    exclusion_guard_transports_both_ends short long residual suffix exclusions inputAccepted outputAccepted
  refine ⟨residual ++ suffix,?_,inputAfter,outputAfter,?_⟩
  · change FlowAntichains.Relations.produce short.geometry pair.mark
      (FlowAntichains.Relations.coveringSuffix residual suffix) = pair
    rw [← FlowAntichains.Relations.produced_specialization short.geometry residual suffix pair.mark,
      geometry]
    exact produced
  · exact markAdmits_mono _ _ _ marks markAccepted

theorem executable_witness_keeps_original_geometry_check (short long : Row) (residual : List Nat)
    (found : coverWitness short long = some residual) :
    FlowAntichains.Relations.coverWitness short.geometry long.geometry = some residual ∧
    coverAt short long residual = true := by
  unfold coverWitness at found
  cases located : FlowAntichains.Relations.coverWitness short.geometry long.geometry with
  | none => simp [located] at found
  | some chosen =>
    rw [located] at found
    change (if coverAt short long chosen then some chosen else none) = some residual at found
    split at found
    next accepted =>
      have same : chosen = residual := Option.some.inj found
      subst residual
      exact ⟨rfl,accepted⟩
    next => cases found

theorem executable_witness_implies_pair_inclusion (short long : Row) (residual : List Nat)
    (found : coverWitness short long = some residual) (pair : FlowAntichains.Relations.Pair Nat)
    (member : denotes long pair) : denotes short pair :=
  generalized_cover_transports_every_pair short long residual
    (executable_witness_keeps_original_geometry_check short long residual found).2 pair member

theorem every_checked_correlated_residual_is_found (short long : Row) (residual : List Nat)
    (checked : coverAt short long residual = true) : coverWitness short long = some residual := by
  obtain ⟨geometry,_,_⟩ := of_decide_eq_true checked
  have located : FlowAntichains.Relations.coverWitness short.geometry long.geometry = some residual := by
    rw [← geometry]
    exact FlowAntichains.Relations.coverWitness_complete _ _
  simp [coverWitness,located,checked]

/-- Candidate native-safe restriction, proved here only to imply paired
denotation inclusion. It does not silently widen native matching. -/
instance restrictedExclusionGuardDecidable (short long : Row) (residual : List Nat) :
    Decidable (match residual with
      | [] => short.inputE = long.inputE ∧ subsetB short.outputE long.outputE = true
      | first :: _ => short.inputE = [] ∧ first ∉ short.outputE) := by
  cases residual <;> infer_instance

def restrictedCoverAt (short long : Row) (residual : List Nat) : Bool :=
  decide (FlowAntichains.Relations.specialize short.geometry residual = long.geometry ∧
    subsetB short.excludedMarks long.excludedMarks = true ∧
    match residual with
    | [] => short.inputE = long.inputE ∧ subsetB short.outputE long.outputE = true
    | first :: _ => short.inputE = [] ∧ first ∉ short.outputE)

theorem restricted_guard_supplies_generalized_pair_guard (short long : Row) (residual : List Nat)
    (checked : restrictedCoverAt short long residual = true) :
    coverAt short long residual = true := by
  cases residual with
  | nil =>
    obtain ⟨geometry,marks,inputSame,outputIncluded⟩ := of_decide_eq_true checked
    apply decide_eq_true
    refine ⟨geometry,marks,?_,outputIncluded⟩
    rw [inputSame]
    exact subsetB_refl _
  | cons first rest =>
    obtain ⟨geometry,marks,inputEmpty,outputAccepted⟩ := of_decide_eq_true checked
    apply decide_eq_true
    refine ⟨geometry,marks,?_,outputAccepted⟩
    rw [inputEmpty]
    simp

theorem restricted_guard_transports_every_pair (short long : Row) (residual : List Nat)
    (checked : restrictedCoverAt short long residual = true)
    (pair : FlowAntichains.Relations.Pair Nat) (member : denotes long pair) : denotes short pair :=
  generalized_cover_transports_every_pair short long residual
    (restricted_guard_supplies_generalized_pair_guard short long residual checked) pair member

/-- Exact header transcription of the existing generic STAR/STAR inverse:
reader E is empty; the result transports the shared endpoint exclusions.
The native MUST inverse is a different constructor, outside these rows. -/
def genericReverseHeaders (row : Row) : List Nat × List Nat :=
  ([], row.inputE ++ row.outputE)

theorem generic_STAR_inverse_reader_E_is_empty (row : Row) :
    (genericReverseHeaders row).1 = [] := rfl

theorem generic_STAR_inverse_result_keeps_both_endpoint_Es (row : Row) :
    (genericReverseHeaders row).2 = row.inputE ++ row.outputE := rfl

def exampleShort : Row := ⟨⟨9,100,200,[10],[20]⟩,[3],[4],[7]⟩
def exampleLong : Row := ⟨⟨9,100,200,[10,5],[20,5]⟩,[5,8],[5,11],[7,12]⟩

theorem opaque_bases_and_two_nonempty_Es_have_a_checked_cover :
    coverWitness exampleShort exampleLong = some [5] := by decide

theorem short_input_exclusion_cannot_be_ignored :
    coverAt {exampleShort with inputE := [5]} exampleLong [5] = false := by decide

theorem short_output_exclusion_cannot_be_ignored :
    coverAt {exampleShort with outputE := [5]} exampleLong [5] = false := by decide

theorem both_long_exclusions_can_change_after_an_admitted_proper_residual :
    coverAt exampleShort {exampleLong with inputE := [1,2,3,4], outputE := [5,6,7,8]} [5] = true := by decide

theorem equal_E_at_different_heads_does_not_imply_cover :
    coverAt {exampleShort with inputE := [5],outputE := [5]}
      {exampleLong with inputE := [5],outputE := [5]} [5] = false := by decide

theorem excluded_long_mark_cannot_be_reintroduced :
    coverAt exampleShort {exampleLong with excludedMarks := []} [5] = false := by decide

theorem unequal_mx_can_still_give_safe_mark_inclusion :
    exampleShort.excludedMarks ≠ exampleLong.excludedMarks ∧
    coverAt exampleShort exampleLong [5] = true := by decide

theorem unmatched_endpoint_residual_is_rejected :
    coverWitness exampleShort {exampleLong with geometry := ⟨9,100,200,[10,5],[20]⟩} = none := by decide

theorem different_owner_is_rejected :
    coverWitness exampleShort {exampleLong with geometry := ⟨99,100,200,[10,5],[20,5]⟩} = none := by decide

/-- The existing singleton same-head STAR selector uses comparable E in its
applicable/inside lanes. This is an exact local Boolean transcription only;
it does not assert that all typed rows are reachable from the selected C2. -/
def sameHeadNativeStarMatch (actualE premiseE : List Nat) : Bool :=
  subsetB premiseE actualE || subsetB actualE premiseE

theorem componentwise_E_is_pair_sufficient_not_native_inside_completeness :
    subsetB [3] [3,4] = true ∧ subsetB ([] : List Nat) [] = true ∧
    sameHeadNativeStarMatch [4] [3] = false ∧
    sameHeadNativeStarMatch [4] [3,4] = true := by decide

end ExclusionCorrelatedInclusion

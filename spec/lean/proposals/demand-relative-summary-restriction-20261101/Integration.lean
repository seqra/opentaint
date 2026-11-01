import Geometry
import Restriction
import Admission

/-!
The actual scalar paired restriction is the executable gate used by the store.
Row IDs are query witnesses only: they are stripped before semantic admission.

Scope: nonzero, empty-E concrete FULL scalar DATA, exactly as Restriction.lean.
No FLOW geometry, ND support, typed ZERO/Target, source-permission or whole-driver
completeness theorem is claimed. NORMAL-provider provenance is generic in the
flow/coverage classifier; DEMAND-to-DEMAND replacement is not prohibited here.
-/
namespace RelativeRestriction.Integration
set_option autoImplicit false

structure Summary where
  initial : Pattern
  result : Scalar
  deriving DecidableEq, Repr

def semantic (admitted : Admitted) : Summary := ⟨admitted.initial, admitted.result⟩

/-- Real scalar restriction, not an independently stipulated accepted output. -/
def gate (context : Context) (rows : List Row) (candidate : Summary) : List Summary :=
  (admitRows context rows candidate.initial candidate.result).map semantic

def storedLayer (summary : Summary) : Admission.Layer :=
  match summary.result.layer with
  | .normal => .normal
  | .demand => .demand

def empty : Admission.State Summary := ⟨[], []⟩

/-- Every final semantic row is selected with one actual complete demand row. -/
theorem gate_has_concrete_pair_witness (context : Context) (rows : List Row)
    (candidate output : Summary) (member : output ∈ gate context rows candidate) :
    output.initial = candidate.initial ∧
      ∃ row, row ∈ rows ∧
        restrictRow context row candidate.initial candidate.result = some output.result := by
  obtain ⟨admitted, inRows, same⟩ := List.mem_map.mp member
  obtain ⟨row, rowMember, accepted⟩ := List.mem_filterMap.mp inRows
  have provenance := admitted_row_provenance context row candidate.initial candidate.result admitted accepted
  cases same
  exact ⟨provenance.2.1, row, rowMember, provenance.2.2⟩

/-- Connect finite store execution provenance to the real `restrictRow` call. -/
theorem every_stored_row_has_concrete_gate_witness
    (context : Context) (rows : List Row) (history : List Summary)
    (state : Admission.State Summary)
    (trace : Admission.Trace (gate context rows) history state)
    (output : Summary) (stored : output ∈ state.rows) :
    ∃ candidate, candidate ∈ history ∧ output.initial = candidate.initial ∧
      ∃ row, row ∈ rows ∧
        restrictRow context row candidate.initial candidate.result = some output.result := by
  obtain ⟨candidate, inHistory, fromGate⟩ :=
    Admission.reachable_rows_have_gate_provenance (gate context rows) history state trace output stored
  have pair := gate_has_concrete_pair_witness context rows candidate output fromGate
  exact ⟨candidate, inHistory, pair.1, pair.2⟩

/-- Native persistence reads the admitted store and therefore uses the same
actual paired restriction. The eligibility classifier is the unchanged native
adapter; this theorem does not strengthen its shape or direction rules. -/
theorem native_row_has_concrete_gate_witness
    (context : Context) (rows : List Row) (history : List Summary)
    (eligible : Summary → Bool) (state : Admission.State Summary)
    (trace : Admission.Trace (gate context rows) history state)
    (output : Summary) (stored : output ∈ Admission.native storedLayer eligible state) :
    ∃ candidate, candidate ∈ history ∧ output.initial = candidate.initial ∧
      ∃ row, row ∈ rows ∧
        restrictRow context row candidate.initial candidate.result = some output.result :=
  every_stored_row_has_concrete_gate_witness context rows history state trace output
    (Admission.native_is_admitted storedLayer eligible state output stored)

/-- This covers NORMAL FLOW-provider provenance only. Actual FLOW coverage is
an external checked adapter, not concrete-scalar mark equality from this model. -/
theorem normal_provider_has_concrete_gate_witness
    (context : Context) (rows : List Row) (history : List Summary)
    (isFlow covers : Summary → Bool) (state : Admission.State Summary)
    (trace : Admission.Trace (gate context rows) history state)
    (output : Summary)
    (provider : output ∈ Admission.providers storedLayer isFlow covers state) :
    output.result.layer = .normal ∧
      ∃ candidate, candidate ∈ history ∧ output.initial = candidate.initial ∧
        ∃ row, row ∈ rows ∧
          restrictRow context row candidate.initial candidate.result = some output.result := by
  have admitted := Admission.provider_passed_admission storedLayer isFlow covers state output provider
  have normal : output.result.layer = .normal := by
    cases h : output.result.layer with
    | normal => rfl
    | demand => simp [storedLayer, h] at admitted
  exact ⟨normal, every_stored_row_has_concrete_gate_witness context rows history state trace output admitted.1⟩

namespace Controls

def context : Context := ⟨4, false, false⟩
def dc : Pattern := ⟨1, [], .may, 7⟩
def dp : Pattern := ⟨2, [], .may, 7⟩
def row : Row := ⟨10, dc, dp⟩
def initial : Pattern := ⟨1, [.field 11], .exact, 7⟩
def rawNormal : Summary :=
  ⟨initial, ⟨⟨2, [.field 21, .field 22, .element], .exact, 7⟩, .normal, true⟩⟩
def cutDemand : Summary :=
  ⟨initial, ⟨⟨2, [.field 21], .may, 7⟩, .demand, true⟩⟩
def admittedCut : Admission.State Summary := Admission.offer (gate context [row]) empty rawNormal

/-- Concrete scalar C5 keeps the deep N input, but its actual new limit yields D. -/
theorem real_restriction_normal_to_demand :
    existingC5 context row initial rawNormal.result = some rawNormal.result ∧
      gate context [row] rawNormal = [cutDemand] := by decide

theorem actual_cut_store_and_publication_contain_only_admitted_result :
    admittedCut.rows = [cutDemand] ∧ admittedCut.pending = [cutDemand] := by decide

theorem actual_cut_enters_frontier_and_has_no_normal_native :
    Admission.frontier storedLayer admittedCut = [cutDemand] ∧
      Admission.native storedLayer (fun _ => true) admittedCut = [] := by decide

/-- A cut can no longer supply NORMAL coverage. The unchanged law may still
use admitted DEMAND providers for DEMAND counterparts outside this model. -/
theorem actual_cut_is_not_a_normal_provider (isFlow covers : Summary → Bool) :
    Admission.providers storedLayer isFlow covers admittedCut = [] := by
  unfold Admission.providers
  rw [actual_cut_store_and_publication_contain_only_admitted_result.1]
  simp [storedLayer, cutDemand]

def exactRow : Row := {row with dp := {dp with tail := .exact}}

theorem rejected_normal_leaves_all_semantic_state_unchanged (state : Admission.State Summary) :
    Admission.offer (gate context [exactRow]) state rawNormal = state := by
  apply Admission.rejected_changes_no_state
  decide

def rawWithin : Summary :=
  ⟨initial, ⟨⟨2, [.field 21], .exact, 7⟩, .normal, true⟩⟩
def withinState : Admission.State Summary := Admission.offer (gate context [row]) empty rawWithin

/-- A concrete exact initial is eligible in this control's nonzero, backward
native lane; it is not a universal Kotlin native-record validator. -/
def nativeEligible (value : Summary) : Bool := value.initial.tail == .exact

theorem within_normal_is_persisted_from_actual_gate :
    gate context [row] rawWithin = [rawWithin] ∧
      Admission.native storedLayer nativeEligible withinState = [rawWithin] ∧
      Admission.persist [] storedLayer nativeEligible withinState = [rawWithin] ∧
      Admission.frontier storedLayer withinState = [] := by decide

/-- Both geometries and layers survive literal per-row union, with no early
exit after the first NORMAL result covers the raw point. -/
def exactDeepRow : Row := {row with id := 11, dp := rawNormal.result.toPattern}

theorem two_compatible_rows_keep_normal_and_new_demand :
    (Admission.offer (gate context [exactDeepRow, row]) empty rawNormal).rows =
      [rawNormal, cutDemand] ∧
    (Admission.offer (gate context [row, exactDeepRow]) empty rawNormal).rows =
      [cutDemand, rawNormal] := by decide

end Controls
#print axioms gate_has_concrete_pair_witness
#print axioms every_stored_row_has_concrete_gate_witness
#print axioms native_row_has_concrete_gate_witness
#print axioms normal_provider_has_concrete_gate_witness
#print axioms Controls.actual_cut_enters_frontier_and_has_no_normal_native
#print axioms Controls.rejected_normal_leaves_all_semantic_state_unchanged
#print axioms Controls.within_normal_is_persisted_from_actual_gate
#print axioms Controls.two_compatible_rows_keep_normal_and_new_demand
end RelativeRestriction.Integration

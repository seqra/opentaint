import AnnotatedC5Exit

/- The selected C5 operator can preserve STAR on DEMAND. The native handoff
must accept that existing result. This bridge checks projection format only;
it does not add a transfer, a C2 command or a refinement rule. -/
namespace FlowStarDemandHandoff
open AnnotatedC5Exit
set_option autoImplicit false

/-- The existing guidance normalization. Its input is an admitted summary view. -/
def guidance (raw : Pattern) : Pattern :=
  let located := if raw.tail = .must then {raw with tail := .may, exclusion := []} else raw
  match located.slot with
  | .full _ => located
  | .flow _ => normalizeSelector {located with slot := .flow []}

def handoff (premise : Pattern) (conclusion : Fact) : Pattern × Pattern :=
  (guidance conclusion.toPattern, guidance premise)

def flowEntry (entry : Pattern) : Prop :=
  entry.slot = .flow [] ∧ (entry.tail = .star ∨ entry.tail = .may) ∧ entry.exclusion = []

instance (entry : Pattern) : Decidable (flowEntry entry) := by
  unfold flowEntry
  infer_instance

theorem STAR_projection_preserves_base_path_tail
    (base : Nat) (path : Path) (mx : List Nat) (excluded : E) :
    guidance ⟨base,path,.star,.flow mx,excluded⟩ = ⟨base,path,.star,.flow [],[]⟩ := by
  simp [guidance,normalizeSelector]

theorem STAR_projection_is_a_legal_stored_FLOW_entry
    (base : Nat) (path : Path) (mx : List Nat) (excluded : E) :
    flowEntry (guidance ⟨base,path,.star,.flow mx,excluded⟩) := by
  rw [STAR_projection_preserves_base_path_tail]
  exact ⟨rfl,Or.inl rfl,rfl⟩

theorem MAY_projection_is_unchanged_except_mx
    (base : Nat) (path : Path) (mx : List Nat) :
    guidance ⟨base,path,.may,.flow mx,[]⟩ = ⟨base,path,.may,.flow [],[]⟩ := by
  simp [guidance,normalizeSelector]

theorem existing_MUST_projection_remains_MAY
    (base : Nat) (path : Path) (mx : List Nat) (excluded : E) :
    guidance ⟨base,path,.must,.flow mx,excluded⟩ = ⟨base,path,.may,.flow [],[]⟩ := by
  simp [guidance,normalizeSelector]

theorem handoff_keeps_the_complete_pair (premise : Pattern) (conclusion : Fact) :
    (handoff premise conclusion).1 = guidance conclusion.toPattern ∧
    (handoff premise conclusion).2 = guidance premise := ⟨rfl,rfl⟩

/-- The admission image has already authorized the FLOW companion. This is
only its paired output calculation, with a strict-descendant selector. -/
def nativeRaw : Fact := ⟨⟨2,[],.star,.flow [9],[.field 2]⟩,.demand,false⟩
def previousExit : Pattern := ⟨2,[.field 1],.may,.full 7,[]⟩
def currentPremise : Pattern := ⟨1,[],.star,.flow [],[]⟩

theorem C5_preserves_correlated_STAR_DEMAND_in_both_directions :
    restrictData true 2 nativeRaw previousExit = some nativeRaw ∧
    restrictData false 3 nativeRaw previousExit = some nativeRaw := by decide

theorem C5_result_is_not_a_field_cut :
    nativeRaw.tail = .star ∧ nativeRaw.layer = .demand ∧ nativeRaw.exclusion = [.field 2] ∧
    cut (pairBudget 2 previousExit) nativeRaw = nativeRaw := by decide

theorem old_ANY_only_assertion_rejects_the_selected_C5_result :
    nativeRaw.tail ≠ .may := by decide

theorem next_pair_keeps_STAR_and_uses_existing_selector_normalization :
    handoff currentPremise nativeRaw =
      (⟨2,[],.star,.flow [],[]⟩,⟨1,[],.star,.flow [],[]⟩) := by decide

theorem next_entry_is_legal_at_every_restricted_run :
    ∀ run : Nat, run ≥ 2 → flowEntry (handoff currentPremise nativeRaw).1 := by
  intro _ _
  exact STAR_projection_is_a_legal_stored_FLOW_entry 2 [] [9] [.field 2]

/-- Every selected pair has an executable projection; there is no filtering
by the source run number or the conclusion's STAR tail. -/
theorem every_offered_pair_has_its_own_projection
    (rows : List (Pattern × Fact)) (premise : Pattern) (conclusion : Fact)
    (member : (premise,conclusion) ∈ rows) :
    handoff premise conclusion ∈ rows.map (fun row => handoff row.1 row.2) :=
  List.mem_map.mpr ⟨(premise,conclusion),member,rfl⟩

/-- A raw MAY passes the old pre-C5 shape assertion. An exact paired selector
chooses an exact FLOW result; whole-FLOW publication normalizes it to STAR. -/
def rawMAY : Fact := ⟨⟨2,[],.may,.flow [9],[]⟩,.demand,false⟩
def exactExit : Pattern := ⟨2,[],.exact,.full 7,[]⟩
def selectedExact : Fact := ⟨⟨2,[],.exact,.flow [9],[]⟩,.demand,false⟩
def normalizedSTAR : Fact := ⟨⟨2,[],.star,.flow [9],[]⟩,.demand,false⟩

def normalizeWholeFlowConclusion (value : Fact) : Fact :=
  match value.slot,value.tail with
  | .flow _,.exact => {value with tail := .star}
  | _,_ => value

theorem paired_EXACT_selects_EXACT_FLOW_on_DEMAND :
    restrictData true 2 rawMAY exactExit = some selectedExact := by decide

theorem normalized_C5_output_is_STAR_FLOW_on_DEMAND :
    (restrictData true 2 rawMAY exactExit).map normalizeWholeFlowConclusion = some normalizedSTAR := by decide

theorem raw_ANY_assertion_does_not_imply_an_ANY_publication :
    rawMAY.tail = .may ∧ normalizedSTAR.tail ≠ .may ∧
    normalizedSTAR.layer = rawMAY.layer ∧ normalizedSTAR.slot = rawMAY.slot := by decide

theorem normalized_C5_handoff_preserves_both_STAR_endpoints :
    handoff currentPremise normalizedSTAR =
      (⟨2,[],.star,.flow [],[]⟩,⟨1,[],.star,.flow [],[]⟩) := by decide

theorem normalized_C5_entry_is_legal :
    flowEntry (handoff currentPremise normalizedSTAR).1 := by decide

#print axioms STAR_projection_preserves_base_path_tail
#print axioms STAR_projection_is_a_legal_stored_FLOW_entry
#print axioms MAY_projection_is_unchanged_except_mx
#print axioms existing_MUST_projection_remains_MAY
#print axioms handoff_keeps_the_complete_pair
#print axioms C5_preserves_correlated_STAR_DEMAND_in_both_directions
#print axioms C5_result_is_not_a_field_cut
#print axioms old_ANY_only_assertion_rejects_the_selected_C5_result
#print axioms next_pair_keeps_STAR_and_uses_existing_selector_normalization
#print axioms next_entry_is_legal_at_every_restricted_run
#print axioms every_offered_pair_has_its_own_projection
#print axioms paired_EXACT_selects_EXACT_FLOW_on_DEMAND
#print axioms normalized_C5_output_is_STAR_FLOW_on_DEMAND
#print axioms raw_ANY_assertion_does_not_imply_an_ANY_publication
#print axioms normalized_C5_handoff_preserves_both_STAR_endpoints
#print axioms normalized_C5_entry_is_legal
end FlowStarDemandHandoff

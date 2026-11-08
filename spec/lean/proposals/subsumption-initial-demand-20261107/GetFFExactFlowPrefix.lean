import ExactFlowPrefixCompanion
import GetFFC5Policy

/- E30 with the selected raw EXACT/FLOW companion. Current whole-pair
normalization and paired C5 remain unchanged. Completion is disabled.
The field-specific primary is retained and every argument/return candidate
is checked, not only the desired return. Root/native adapters remain those
of GetFFC5Policy. -/
namespace GetFFExactFlowPrefix
open PlainStarRelativeAdmission GetFFC5Policy

set_option maxRecDepth 16384
set_option maxHeartbeats 32000000

def commands (mode : Mode) (rows : List DRow) (submitted : Actual) : List Seed :=
  unique (rows.flatMap fun row =>
    match rowEntry row with
    | none => []
    | some demand => ExactFlowPrefixCompanion.emitSeeds mode demand submitted)

def infer (mode : Mode) (rows : List DRow) (submitted : Actual) : List Row :=
  authority ((commands mode rows submitted).flatMap fun seed =>
    (boundaryFacts mode (start seed)).flatMap fun raw =>
      rows.filterMap fun row => finish true mode row seed raw)

def backward2 : List Row := match reverseSink with
  | none => []
  | some offered => infer b2 b2Guides offered

def backward2SourceInputs : List Actual := match reverseSink with
  | none => []
  | some offered => applyRows 1 backward2 offered

def forward3 : List Row := match source 2 with
  | none => []
  | some offered => if backward2SourceInputs.any acceptedSource then
      infer f3 (handoff f3 backward2) offered else []

def forward3Targets : List Target := match source 2 with
  | none => []
  | some offered => (applyRows 2 (normal r1Rows ++ forward3) offered).filterMap hitSink

def backward4SourceInputs : List Actual :=
  if .demand ∈ forward3Targets then
    match reverseSink with
    | none => []
    | some offered => applyRows 3 ((normal forward3).map reverseRow) offered
  else []

def forward5Targets : List Target :=
  if backward4SourceInputs.any acceptedSource then
    match source 4 with
    | none => []
    | some offered => (applyRows 4 (normal forward3) offered).filterMap hitSink
  else []

def coarseRaw : Seed := ⟨p retBase [] .exact,.normal⟩
def coarsePublic : Row := ⟨p retBase [] .star,a (p argBase [f] .any) .demand⟩

theorem backward_emission_has_fine_primary_and_RAW_exact_companion :
    commands b2 b2Guides (a (p retBase [f] .exact T)) =
      [⟨p retBase [f] .star,.normal⟩,coarseRaw] := by decide

theorem coarse_identity_starts_EXACT_not_STAR :
    (start coarseRaw).pattern.tail = .exact := rfl

theorem exact_companion_body_is_executed_before_normalization :
    body b2 (start coarseRaw) = some (a (p argBase [f] .any) .demand) := by decide

theorem both_backward_summaries_are_derived :
    backward2 = [expectedB2,coarsePublic] := by decide

theorem backward_inputs_really_permit_the_run3_source :
    backward2SourceInputs.any acceptedSource = true := by decide

theorem next_forward_run_has_the_root_ret_output_selector :
    (handoff f3 backward2).any (fun row => decide
      (row.exit = .data (DeepGuidanceArrival.encode (p retBase [] .star)))) = true := by decide

theorem raw_forward_prefix_does_not_read_an_unrepresented_child :
    body f3 (start ⟨p argBase [f] .exact,.normal⟩) = none := by decide

theorem new_forward_commands_retain_the_descendant_primary :
    commands f3 (handoff f3 backward2) (a (p argBase [f,f] .any T) .demand) =
      [⟨p argBase [f,f] .star,.normal⟩,⟨p argBase [f] .exact,.normal⟩] := by decide

theorem proposed_STAR_rejection_accepts_the_real_NORMAL_return :
    forward3 = [expectedF3Normal] := by decide

theorem no_completion_or_argument_DEMAND_is_needed_for_this_return :
    arguments forward3 = [] ∧ demand forward3 = [] ∧ forward3Targets = [.demand] := by decide

theorem actual_source_permission_is_recovered_by_saved_opposite :
    backward4SourceInputs = [a (p argBase [f,f,f] .exact T)] ∧
    backward4SourceInputs.any acceptedSource = true := by decide

theorem raw_EXACT_companion_restores_the_run5_NORMAL_finding :
    forward5Targets = [.normal] := by decide

end GetFFExactFlowPrefix

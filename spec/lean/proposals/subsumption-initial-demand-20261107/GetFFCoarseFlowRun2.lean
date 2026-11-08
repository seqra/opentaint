import GetFFC5Policy

/- Counterfactual review of an additional coarse FLOW start in run-2.
Current C2 does NOT emit this start for the actual ret.f input. The module
does not change C2, and it does not claim a complete prefix-admission policy.
It checks whether this one additional analysis removes E30's need for the
ancestor-STAR output case or FLOW demand completion. -/
namespace GetFFCoarseFlowRun2
open PlainStarRelativeAdmission GetFFC5Policy

set_option maxRecDepth 16384
set_option maxHeartbeats 32000000

def coarse : Seed := ⟨p retBase [] .star,.normal⟩

def coarseB2 : List Row := authority (
  (boundaryFacts b2 (start coarse)).flatMap fun raw =>
    b2Guides.filterMap fun row => finish true b2 row coarse raw)

def extendedB2 : List Row := authority (b2Rows false ++ coarseB2)
def nextDemand := handoff f3 extendedB2

def forward3 : List Row :=
  match source 2 with
  | none => []
  | some offered => infer true f3 nextDemand offered

def forward3Targets : List Target :=
  match source 2 with
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

theorem actual_run2_commands_contain_only_the_field_initial :
    commands b2 b2Guides (a (p retBase [f] .exact T)) =
      [⟨p retBase [f] .star,.normal⟩] := by decide

theorem coarse_start_is_not_a_current_command_for_that_offer :
    coarse ∉ commands b2 b2Guides (a (p retBase [f] .exact T)) := by decide

theorem additional_coarse_analysis_passes_unchanged_C5 :
    coarseB2 = [⟨p retBase [] .star,a (p argBase [f] .any) .demand⟩] := by decide

theorem proposed_STAR_rejection_now_keeps_the_NORMAL_getter :
    forward3 = [expectedF3Normal] := by decide

theorem the_restored_forward3_route_has_a_DEMAND_sink :
    forward3Targets = [.demand] := by decide

theorem saved_opposite_row_reaches_the_actual_source :
    backward4SourceInputs = [a (p argBase [f,f,f] .exact T)] ∧
    backward4SourceInputs.any acceptedSource = true := by decide

theorem the_additional_run2_start_restores_the_run5_NORMAL_finding :
    forward5Targets = [.normal] := by decide

end GetFFCoarseFlowRun2

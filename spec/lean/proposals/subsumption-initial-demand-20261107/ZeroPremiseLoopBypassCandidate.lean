/-
Candidate: exempt a genuinely ZERO-premise loop DATA summary from the
extra loop output gate. Keep C5 publication, global limiting, real controls,
layers and all DATA-premise gate behavior unchanged. No production change.
The phase checks below use the existing reached repeat-component model;
they do not prove all native ports or a whole-program convergence result.
-/
import E21SavedRepeatGateDiagnosis

namespace ZeroPremiseLoopBypassCandidate
open PlainStarRelativeAdmission DeepFlowCompletion DeepGuidanceArrival E21ClosedFamilies

set_option maxRecDepth 16384
set_option maxHeartbeats 64000000

def keep (mode : Mode) (permissions : List DemandRow) (row : Edge) (actual : Actual) : List Actual :=
  if row.original = .zero then [cutAt mode.limit actual]
  else E21Run2Run3WorklistClosure.retainApplied mode permissions row actual

theorem ZERO_row_bypasses_only_the_extra_gate
    (mode : Mode) (permissions : List DemandRow) (result : End) (actual : Actual) :
    keep mode permissions ⟨.zero,result⟩ actual = [cutAt mode.limit actual] := by
  simp [keep]

theorem DATA_row_keeps_the_existing_global_bound_and_gate
    (mode : Mode) (permissions : List DemandRow) (initial : Pattern)
    (result : End) (actual : Actual) :
    keep mode permissions ⟨.data initial,result⟩ actual =
      E21Run2Run3WorklistClosure.retainApplied mode permissions ⟨.data initial,result⟩ actual := by
  simp [keep]

def round (mode : Mode) (permissions : List DemandRow) (saved : List Edge)
    (sourceAllowed : Bool) (state : E21Run2Run3WorklistClosure.State) : E21Run2Run3WorklistClosure.State :=
  let inferred := allSelected mode permissions
    ((E21Run2Run3WorklistClosure.seedCommands mode permissions state.inputs).flatMap (body mode sourceAllowed))
  let published := canonical (state.rows ++ inferred)
  let zeroResults := published.flatMap fun row => match row.original,row.result with
    | .zero,.data a => keep mode permissions row a
    | _,_ => []
  let dataResults := (saved ++ published).flatMap fun row => state.inputs.flatMap fun a =>
    (E21Run2Run3WorklistClosure.applyData row a).flatMap (keep mode permissions row)
  ⟨(state.inputs ++ zeroResults ++ dataResults).eraseDups,published⟩

def rounds (mode : Mode) (permissions : List DemandRow) (saved : List Edge)
    (sourceAllowed : Bool) : Nat → E21Run2Run3WorklistClosure.State
  | 0 => {}
  | n+1 => round mode permissions saved sourceAllowed (rounds mode permissions saved sourceAllowed n)

theorem checked_run2_still_reaches_the_same_fixed_point :
    rounds modeB2 E21Run2Run3WorklistClosure.permissions2 [] false 3 =
      E21Run2Run3WorklistClosure.closed2 ∧
    round modeB2 E21Run2Run3WorklistClosure.permissions2 [] false
      E21Run2Run3WorklistClosure.closed2 = E21Run2Run3WorklistClosure.closed2 := by decide

theorem checked_run3_still_reaches_the_same_fixed_point :
    rounds modeF3 E21Run2Run3WorklistClosure.permissions3
      E21Run2Run3WorklistClosure.saved3 E21Run2Run3WorklistClosure.sourceAllowed3 2 =
        E21Run2Run3WorklistClosure.closed3 ∧
    round modeF3 E21Run2Run3WorklistClosure.permissions3
      E21Run2Run3WorklistClosure.saved3 E21Run2Run3WorklistClosure.sourceAllowed3
      E21Run2Run3WorklistClosure.closed3 = E21Run2Run3WorklistClosure.closed3 := by decide

def sourceRow : Edge := ⟨.zero,.data rawF5⟩

theorem checked_run5_source_is_delivered_NORMAL_with_no_completion :
    keep modeF5 E21SavedRepeatGateDiagnosis.permissions sourceRow rawF5 = [rawF5] := by decide

theorem the_same_saved_reads_still_reach_the_exact_NORMAL_actor :
    ((keep modeF5 E21SavedRepeatGateDiagnosis.permissions sourceRow rawF5).flatMap
      E21SavedRepeatGateDiagnosis.executeSaved).flatMap E21SavedRepeatGateDiagnosis.executeSaved =
        [E21SavedRepeatGateDiagnosis.afterTwo] ∧
    E21SavedRepeatGateDiagnosis.exactActor ∈
      E21PrefixExactCompanion.dataCommands modeF5 E21SavedRepeatGateDiagnosis.permissions
        E21SavedRepeatGateDiagnosis.afterTwo := by decide

theorem ordinary_sink_and_Target_rules_need_no_change :
    E21SavedRepeatGateDiagnosis.normalSink ∈
      allSelected modeF5 E21SavedRepeatGateDiagnosis.permissions E21SavedRepeatGateDiagnosis.sinkRows := by decide

theorem bypass_does_not_remove_the_global_limit :
    keep modeF3 [] ⟨.zero,.data (actual [f,f,f] .exact .normal)⟩
      (actual [f,f,f] .exact .normal) = [actual [f,f] .any .demand] := by decide

theorem bypass_does_not_promote_a_DEMAND_supply :
    keep modeF5 [] sourceRow (actual [f,f,f] .exact .demand) =
      [actual [f,f,f] .exact .demand] := by decide

def growingDATA : Edge :=
  ⟨.data (p [f] .star .flow),.data (actual [f,f] .star .normal .flow)⟩

theorem a_DATA_grower_is_still_restricted_even_if_its_parent_original_is_ZERO :
    keep modeF5 [] growingDATA rawF5 = [] ∧
    (applyAtParent ⟨.zero,growingDATA.original⟩ (.data rawF5)).original = .zero := by decide

theorem repeating_the_same_ZERO_supply_is_not_new_feedback_geometry :
    ((keep modeF5 [] sourceRow rawF5) ++ (keep modeF5 [] sourceRow rawF5)).eraseDups = [rawF5] := by decide

#eval ("ZERO_BYPASS_RUN5_SUPPLY",reprStr (keep modeF5 E21SavedRepeatGateDiagnosis.permissions sourceRow rawF5))
#eval ("ZERO_BYPASS_RUN5_AFTER_SAVED_READS",reprStr
  (((keep modeF5 E21SavedRepeatGateDiagnosis.permissions sourceRow rawF5).flatMap
    E21SavedRepeatGateDiagnosis.executeSaved).flatMap E21SavedRepeatGateDiagnosis.executeSaved))

end ZeroPremiseLoopBypassCandidate

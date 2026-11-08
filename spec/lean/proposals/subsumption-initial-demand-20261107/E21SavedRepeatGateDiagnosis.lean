/-
Local diagnosis of the E21 run-5 loss. No completion is used.
The source and permissions come from the closed run-4 component, and
the saved reader comes from the closed run-3 component. This compares
the kept gate order with a bounded diagnostic route through the existing
saved repeat reader. It does not select a general loop repair or prove
the native whole-program scheduler/physical-port adapter.
-/
import E21Run2Run3WorklistClosure

namespace E21SavedRepeatGateDiagnosis
open PlainStarRelativeAdmission DeepFlowCompletion DeepGuidanceArrival E21ClosedFamilies

set_option maxRecDepth 16384
set_option maxHeartbeats 32000000

def permissions := E21Run4SavedReplayClosure.nextPermissions
def reader := E21Run2Run3WorklistClosure.flowShrinker
def afterOne := actual [f,f] .exact .normal
def afterTwo := actual [f] .exact .normal
def exactActor : Seed := ⟨p [f] .exact T,.normal⟩
def readSaved (a : Actual) := E21Run2Run3WorklistClosure.applyData reader a
def executeSaved (a : Actual) := (readSaved a).flatMap
  (E21Run2Run3WorklistClosure.retainApplied modeF5 permissions reader)
def sinkRows := body modeF5 false (.data exactActor)
def normalSink : Edge := ⟨.data (p [f] .exact T),.target .normal⟩

theorem reader_is_a_reached_NORMAL_publication :
    reader ∈ E21Run2Run3WorklistClosure.closed3.rows := by decide

theorem source_and_permission_are_derived_without_completion :
    E21Run4SavedReplayClosure.nextSourceImages = [rawF5] ∧
    sourceEnabled E21Run4SavedReplayClosure.currentRows = true := by decide

theorem current_repeat_C2_rejects_the_precise_source_image :
    E21PrefixExactCompanion.dataCommands modeF5 permissions rawF5 = [] := by decide

theorem current_gate_drops_before_saved_repeat_delivery :
    E21Run2Run3WorklistClosure.gate modeF5 permissions rawF5 = none := by decide

theorem reader_is_not_growing_even_on_the_deep_source_suffix :
    E21Run2Run3WorklistClosure.growing reader = false := by decide

theorem native_saved_application_reaches_depth_two_NORMAL :
    readSaved rawF5 = [afterOne] ∧ executeSaved rawF5 = [afterOne] := by decide

theorem native_saved_application_then_reaches_existing_exact_demand :
    readSaved afterOne = [afterTwo] ∧ executeSaved afterOne = [afterTwo] := by decide

theorem existing_exact_actor_is_admitted_NORMAL_without_completion :
    exactActor ∈ E21PrefixExactCompanion.dataCommands modeF5 permissions afterTwo := by decide

theorem current_body_emits_a_NORMAL_sink_Target :
    normalSink ∈ sinkRows := by decide

theorem existing_paired_guidance_does_not_reject_that_NORMAL_sink :
    normalSink ∈ allSelected modeF5 permissions sinkRows := by decide

theorem applying_the_same_reader_to_DEMAND_cannot_confirm_a_sink :
    readSaved (actual [f,f,f] .exact .demand) = [actual [f,f] .exact .demand] ∧
    readSaved (actual [f,f] .exact .demand) = [actual [f] .exact .demand] ∧
    (⟨.data (p [f] .exact T),.target .normal⟩ : Edge) ∉
      body modeF5 false (.data ⟨p [f] .exact T,.demand⟩) := by decide

theorem saved_read_preserves_the_parent_ZERO_origin :
    applyAtParent ⟨.zero,.data (p [f] .exact T)⟩ (.target .normal) =
      (⟨.zero,.target .normal⟩ : Edge) := rfl

theorem ZERO_and_Target_controls_do_not_admit_DATA_as_ZERO :
    entryOK modeF5 ⟨repeatPort5,.zero,.zero⟩ (.data (p [f,f,f] .exact T)) = false ∧
    entryOK modeF5 ⟨repeatPort5,.target,.zero⟩ (.data (p [f,f,f] .exact T)) = false := by decide

theorem reader_cannot_read_an_absent_concrete_field :
    readSaved (actual [] .exact .normal) = [] := by decide

#eval ("E21_NO_COMPLETION_SOURCE", reprStr E21Run4SavedReplayClosure.nextSourceImages)
#eval ("E21_NO_COMPLETION_SAVED_READER", reprStr reader)
#eval ("E21_NO_COMPLETION_GATE", reprStr (E21Run2Run3WorklistClosure.gate modeF5 permissions rawF5))
#eval ("E21_NO_COMPLETION_REPLAY", reprStr (executeSaved rawF5, executeSaved afterOne))
#eval ("E21_NO_COMPLETION_FINAL_ACTOR", reprStr (E21PrefixExactCompanion.dataCommands modeF5 permissions afterTwo))
#eval ("E21_NO_COMPLETION_NORMAL_TARGET", reprStr (allSelected modeF5 permissions sinkRows))

end E21SavedRepeatGateDiagnosis

import E21ClosedFamilies

/- Check every C5 image of the fresh ZERO source, not just its NORMAL image.
This remains the E21 scalar ownership/port/gate reference contract. -/
namespace E21AllSourceImages
open PlainStarRelativeAdmission DeepFlowCompletion DeepGuidanceArrival E21ClosedFamilies

set_option maxRecDepth 16384
set_option maxHeartbeats 32000000

def sourceCandidates : List Edge :=
  allSelected modeF5 demand5 (body modeF5 (sourceEnabled final4) .zero)

def sourceImages : List Actual := sourceCandidates.filterMap fun row =>
  match row.result with | .data a => some a | _ => none

def gateAll (rows : List DemandRow) : List Actual :=
  sourceImages.filterMap (referenceGate rows)

def savedTargets : Nat → Actual → List TargetResult
  | 0,input => (possibleSink .zero input).toList
  | n+1,input => (possibleSink .zero input).toList ++
      ((shrinkByDerived input).toList.flatMap (savedTargets n))

def targets (rows : List DemandRow) : List TargetResult :=
  (gateAll rows).flatMap (savedTargets 3)

theorem all_C5_source_images_include_the_cut_and_the_NORMAL_actual :
    sourceImages.length = 2 ∧ rawF5 ∈ sourceImages ∧ cutAt 2 rawF5 ∈ sourceImages := by decide

theorem every_admitted_source_image_fails_the_kept_gate_without_completion :
    gateAll demand5 = [] := by decide

theorem no_hidden_cut_source_image_supplies_a_Target_without_completion :
    targets demand5 = [] := by decide

theorem completion_keeps_the_real_precise_NORMAL_source_image :
    rawF5 ∈ gateAll completed5 := by decide

theorem completion_restores_the_NORMAL_Target_among_all_source_images :
    (⟨.zero,.normalReport⟩ : TargetResult) ∈ targets completed5 := by decide

#eval ("E21_ALL_ADMITTED_SOURCE_IMAGES",reprStr sourceImages)
#eval ("E21_COMPLETED_ALL_SOURCE_GATES",reprStr (gateAll completed5))
#eval ("E21_COMPLETED_TARGETS_NOT_A_STOPPING_THEOREM",reprStr (targets completed5))

end E21AllSourceImages

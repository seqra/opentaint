/-
Prepared delta to frozen ClosedFamilies38 + AllSourceImages5.
A successful ANY primary on a strictly deeper actual additionally starts an
EXACT/FLOW/NORMAL identity at the demanded prefix. All old functions/proofs
remain unchanged. This is the scalar E21 ownership/gate reference scope.
-/
import E21AllSourceImages
import ExactFlowPrefixCompanion

namespace E21PrefixExactCompanion
open PlainStarRelativeAdmission DeepFlowCompletion DeepGuidanceArrival E21ClosedFamilies

set_option maxRecDepth 16384
set_option maxHeartbeats 32000000

/- Portable adapter: use the selected generic C2 emitter directly. The
prepared external model's duplicated gate is not a second policy authority. -/
def prefixExtra (mode : Mode) (d : Demand) (a : Actual) : List Seed :=
  (ExactFlowPrefixCompanion.extra mode d a).toList

def emitSeeds (mode : Mode) (d : Demand) (a : Actual) : List Seed :=
  (ExactFlowPrefixCompanion.emitSeeds mode d a).eraseDups

def commands (mode : Mode) (rows : List DemandRow) (inputs : List Actual) : List Choice :=
  let data := rows.flatMap fun row => match row.entry with
    | .data selector => ((scalarPattern selector).bind scalarDemand).toList.flatMap fun demand =>
        inputs.flatMap fun a => (emitSeeds mode demand a).map Choice.data
    | _ => []
  let zero := if rows.any (fun row => decide (row.entry=.zero ∨ row.entry=.target)) then [Choice.zero] else []
  (zero ++ data).eraseDups

-- Whole FLOW normalization of the new prefix EXACT is already in the old
-- stored image here. ANY/full-T has its same-head STAR/T primary companion;
-- ANY/FLOW also has its old EXACT/FLOW preimage. No C5 exit is changed.
def prefixImageCheck (mode : Mode) (rows : List DemandRow) (inputs : List Actual) : Bool :=
  rows.all fun row => match row.entry with
    | .data selector => ((scalarPattern selector).bind scalarDemand).toList.all fun d =>
        inputs.all fun a => (prefixExtra mode d a).all fun seed =>
          E21OperatorLedger.stores mode d (publicInitial seed.initial)
    | _ => true

def demand2 := E21ClosedFamilies.demand2
def choices2 := commands modeB2 demand2 (actualUniverse modeB2 [1] false)
def raw2 := choices2.flatMap (body modeB2 false)
def final2 := allSelected modeB2 demand2 raw2

def demand3 := handoff .backward final2
def choices3 := commands modeF3 demand3 (actualUniverse modeF3 [0,1] true)
def raw3 := choices3.flatMap (body modeF3 (sourceEnabled final2))
def pre3 := preSelected modeF3 demand3 raw3
def final3 := canonical pre3

def demand4 := handoff .forward final3
def choices4 := commands modeB4 demand4 (actualUniverse modeB4 [0,1,2,3] false)
def raw4 := choices4.flatMap (body modeB4 false)
def pre4 := preSelected modeB4 demand4 raw4
def final4 := canonical pre4

def demand5 := handoff .backward final4
def completed5 := FlowDemandCompletion.completed demand5

def dataCommands (mode : Mode) (rows : List DemandRow) (input : Actual) : List Seed :=
  (commands mode rows [input]).filterMap fun c => match c with | .data s => some s | .zero => none

def referenceGate (rows : List DemandRow) (input : Actual) : Option Actual :=
  let baseline := dataCommands modeF5 rows input
  if baseline.isEmpty then none else
    ([1,2,3].find? fun budget => equalCommandSets baseline
      (dataCommands modeF5 rows (cutAt budget input))).map fun budget => cutAt budget input

def sourceCandidates : List Edge :=
  allSelected modeF5 demand5 (body modeF5 (sourceEnabled final4) .zero)
def sourceImages : List Actual := sourceCandidates.filterMap fun row =>
  match row.result with | .data a => some a | _ => none

def gateAll (rows : List DemandRow) : List Actual := sourceImages.filterMap (referenceGate rows)

def targets (rows : List DemandRow) : List TargetResult :=
  (gateAll rows).flatMap (E21AllSourceImages.savedTargets 3)

-- Individual new positive witnesses, using real boundary actuals, not the
-- sink's pre-read root seed as an invented boundary input.
def realB2PrefixSeeds : List Seed :=
  (E21ClosedFamilies.realSinkBoundary.toList).flatMap fun a =>
    prefixExtra modeB2 ⟨x,[],.any,.flow,[]⟩ a

def realB2PrefixRows : List Edge := allSelected modeB2 demand2
  (realB2PrefixSeeds.flatMap fun seed => body modeB2 false (.data seed))

def realB4PrefixSeeds : List Seed :=
  (E21ClosedFamilies.realB4GrowingInput.toList).flatMap fun a =>
    prefixExtra modeB4 ⟨x,[f],.any,T,[]⟩ a

def realB4PrefixRaw : List Edge := realB4PrefixSeeds.flatMap fun seed => body modeB4 false (.data seed)
def realB4PrefixAdmitted : List Edge := allSelected modeB4 demand4 realB4PrefixRaw

theorem B2_new_prefix_initial_is_genuinely_root_EXACT_FLOW :
    realB2PrefixSeeds=[⟨p [] .exact .flow,.normal⟩] := by decide

theorem B2_new_prefix_initial_builds_NORMAL_grower_through_C5 :
    realB2PrefixRows=[⟨.data (p [] .star .flow),.data (actual [f] .star .normal .flow)⟩] := by decide

theorem B2_new_grower_is_in_full_final_authority :
    (⟨.data (p [] .star .flow),.data (actual [f] .star .normal .flow)⟩ : Edge) ∈ final2 := by decide

theorem B2_new_grower_is_saved_not_a_forward_demand :
    handoff .backward realB2PrefixRows=[] := by decide

theorem B2_final_has_one_extra_NORMAL_row :
    final2.length=E21ClosedFamilies.final2.length+1 := by decide

theorem ALL_B2_prefix_public_premises_fit_the_existing_C5_image :
    prefixImageCheck modeB2 demand2 (actualUniverse modeB2 [1] false)=true := by decide

theorem ALL_B4_prefix_public_premises_fit_the_existing_C5_image :
    prefixImageCheck modeB4 demand4 (actualUniverse modeB4 [0,1,2,3] false)=true := by decide

theorem no_extra_forward_demand_is_created_by_the_B2_NORMAL_grower :
    demand3=E21ClosedFamilies.demand3 := by decide

theorem F3_all_families_are_unchanged_under_new_emitter :
    final3=E21ClosedFamilies.final3 := by decide

theorem F3_precanonical_FLOW_DATA_still_has_only_NORMAL_support :
    pre3.all (fun row => !isFlowDataD row)=true := by decide

theorem F3_precanonical_Target_origins_are_still_exact_f :
    pre3.all exactTTarget=true := by decide

theorem B4_new_prefix_initial_is_f_EXACT_FLOW :
    realB4PrefixSeeds=[⟨p [f] .exact .flow,.normal⟩] := by decide

theorem B4_new_prefix_raw_DATA_is_NORMAL_ff :
    realB4PrefixRaw=[⟨.data (p [f] .exact .flow),.data (actual [f,f] .exact .normal .flow)⟩] := by decide

theorem SAME_complete_ZERO_exit_rejects_ALL_new_B4_prefix_DATA :
    realB4PrefixAdmitted=[] := by decide

theorem B4_precanonical_no_FLOW_DATA_is_sneaked_through_another_row :
    pre4.all (fun row => !isFlowDataD row && (match row.original,row.result with
      | .data i,.data _ => decide (i.mark ≠ .flow)
      | _,_ => true))=true := by decide

theorem B4_all_admitted_families_are_unchanged :
    final4=E21ClosedFamilies.final4 := by decide

theorem F5_ALL_demand_rows_are_unchanged : demand5=E21ClosedFamilies.demand5 := by decide

theorem F5_no_completion_has_no_DATA_command_for_raw_or_cut :
    dataCommands modeF5 demand5 rawF5=[] ∧ dataCommands modeF5 demand5 (cutAt 2 rawF5)=[] := by decide

theorem ALL_admitted_SOURCE_images_include_the_NORMAL_and_cut_branches :
    sourceImages.length=2 ∧ rawF5∈sourceImages ∧ cutAt 2 rawF5∈sourceImages := by decide

theorem no_completion_kept_gate_rejects_EVERY_admitted_SOURCE_image :
    gateAll demand5=[] := by decide

theorem no_completion_has_no_public_Target_in_the_reference_source_route :
    targets demand5=[] := by decide

theorem completion_still_separates_the_fine_command_from_every_proper_cut :
    E21ClosedFamilies.fine ∈ dataCommands modeF5 completed5 rawF5 ∧
    E21ClosedFamilies.fine ∉ dataCommands modeF5 completed5 (cutAt 1 rawF5) ∧
    E21ClosedFamilies.fine ∉ dataCommands modeF5 completed5 (cutAt 2 rawF5) := by decide

theorem completion_retains_the_precise_NORMAL_source_under_the_kept_gate :
    rawF5 ∈ gateAll completed5 := by decide

theorem completion_preserves_the_real_NORMAL_Target_among_ALL_source_images :
    (⟨.zero,.normalReport⟩ : TargetResult) ∈ targets completed5 := by decide

def ALL_B4_prefix_raw : List Edge := demand4.flatMap fun row =>
  match row.entry with
  | .data selector => ((scalarPattern selector).bind scalarDemand).toList.flatMap fun d =>
      (actualUniverse modeB4 [0,1,2,3] false).flatMap fun a =>
        (prefixExtra modeB4 d a).flatMap fun seed => body modeB4 false (.data seed)
  | _ => []

theorem ALL_new_B4_prefix_bodies_fail_the_complete_paired_C5 :
    preSelected modeB4 demand4 ALL_B4_prefix_raw=[] := by decide

theorem no_completion_is_empty_for_ANY_post_gate_saved_continuation
    (savedContinuation : Actual → List TargetResult) :
    (gateAll demand5).flatMap savedContinuation=[] := by
  rw [no_completion_kept_gate_rejects_EVERY_admitted_SOURCE_image]
  rfl


#print axioms E21PrefixExactCompanion.B2_new_prefix_initial_is_genuinely_root_EXACT_FLOW
#print axioms E21PrefixExactCompanion.B2_new_prefix_initial_builds_NORMAL_grower_through_C5
#print axioms E21PrefixExactCompanion.B2_new_grower_is_in_full_final_authority
#print axioms E21PrefixExactCompanion.B2_new_grower_is_saved_not_a_forward_demand
#print axioms E21PrefixExactCompanion.B2_final_has_one_extra_NORMAL_row
#print axioms E21PrefixExactCompanion.ALL_B2_prefix_public_premises_fit_the_existing_C5_image
#print axioms E21PrefixExactCompanion.ALL_B4_prefix_public_premises_fit_the_existing_C5_image
#print axioms E21PrefixExactCompanion.no_extra_forward_demand_is_created_by_the_B2_NORMAL_grower
#print axioms E21PrefixExactCompanion.F3_all_families_are_unchanged_under_new_emitter
#print axioms E21PrefixExactCompanion.F3_precanonical_FLOW_DATA_still_has_only_NORMAL_support
#print axioms E21PrefixExactCompanion.F3_precanonical_Target_origins_are_still_exact_f
#print axioms E21PrefixExactCompanion.B4_new_prefix_initial_is_f_EXACT_FLOW
#print axioms E21PrefixExactCompanion.B4_new_prefix_raw_DATA_is_NORMAL_ff
#print axioms E21PrefixExactCompanion.SAME_complete_ZERO_exit_rejects_ALL_new_B4_prefix_DATA
#print axioms E21PrefixExactCompanion.B4_precanonical_no_FLOW_DATA_is_sneaked_through_another_row
#print axioms E21PrefixExactCompanion.B4_all_admitted_families_are_unchanged
#print axioms E21PrefixExactCompanion.F5_ALL_demand_rows_are_unchanged
#print axioms E21PrefixExactCompanion.F5_no_completion_has_no_DATA_command_for_raw_or_cut
#print axioms E21PrefixExactCompanion.ALL_admitted_SOURCE_images_include_the_NORMAL_and_cut_branches
#print axioms E21PrefixExactCompanion.no_completion_kept_gate_rejects_EVERY_admitted_SOURCE_image
#print axioms E21PrefixExactCompanion.no_completion_has_no_public_Target_in_the_reference_source_route
#print axioms E21PrefixExactCompanion.completion_still_separates_the_fine_command_from_every_proper_cut
#print axioms E21PrefixExactCompanion.completion_retains_the_precise_NORMAL_source_under_the_kept_gate
#print axioms E21PrefixExactCompanion.completion_preserves_the_real_NORMAL_Target_among_ALL_source_images
#print axioms E21PrefixExactCompanion.ALL_new_B4_prefix_bodies_fail_the_complete_paired_C5
#print axioms E21PrefixExactCompanion.no_completion_is_empty_for_ANY_post_gate_saved_continuation

#eval ("E21_PREFIX_DELTA_COUNTS",final2.length,final3.length,final4.length,demand5.length)
#eval ("E21_PREFIX_B4_RAW_REJECTED",reprStr realB4PrefixRaw,reprStr realB4PrefixAdmitted)
#eval ("E21_PREFIX_ALL_SOURCE_IMAGES",reprStr sourceImages)
#eval ("E21_PREFIX_NO_COMPLETION_TARGETS",reprStr (targets demand5))
#eval ("E21_PREFIX_COMPLETED_TARGETS_NOT_A_STOPPING_THEOREM",reprStr (targets completed5))

end E21PrefixExactCompanion

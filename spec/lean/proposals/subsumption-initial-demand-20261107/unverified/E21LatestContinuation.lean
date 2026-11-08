/-
PREPARED, NOT CHECKED. Finite continuation audit of the latest E21 operator.
Imports the frozen F1--F5 ledger and the generic EXACT/FLOW prefix emitter.
This does not assert Kotlin scheduler equivalence or native convergence.
The late B6 grammar is an upper bound; the real F7 EXACT/N grammar remains
an explicit reachable-input adapter obligation, not a consequence of it.
-/
import E21PrefixExactCompanion

namespace E21LatestContinuation
open PlainStarRelativeAdmission DeepFlowCompletion DeepGuidanceArrival E21ClosedFamilies
set_option maxRecDepth 16384
set_option maxHeartbeats 64000000

def modeB6 : Mode := ⟨6,5,.backward⟩
def modeF7 : Mode := ⟨7,6,.forward⟩

/- A typed-ZERO-only adapter. The historical raw AP kernel returns
ZERO.STAR/Universe for same-head STAR under an EXACT source premise.
Do NOT apply the old generic concrete-STAR normalizer to ordinary DATA. -/
def canonicalTypedZero (value : ApSpec.AFact) : ApSpec.AFact :=
  if value.fact.base = zeroTo.base ∧ value.fact.path = zeroTo.path ∧
      value.fact.mark = zeroTo.mark ∧ value.fact.kind = .star .univ then
    {value with fact := zeroTo}
  else value

def readTypedZero (premisePattern : Pattern) (input : Actual) : Option Layer := do
  let premise ← toAP ⟨premisePattern,intrinsic premisePattern,false⟩
  let scalar ← toAP input
  let result := ApSpec.Run1CorrelatedConcreteInitials.rawApply scalar premise.fact zeroTo
  match result.facts with
  | [raw] =>
      let kept := canonicalTypedZero raw
      if kept.fact = zeroTo then some (if kept.demand then .demand else .normal) else none
  | _ => none

def lateSourceReach (input : Actual) : Option Layer :=
  readTypedZero (p [f,f,f,f] .exact T) input

def lateBody (mode : Mode) (sourceAllowed : Bool) (choice : Choice) : List Edge :=
  if isForward mode then body mode sourceAllowed choice else
    match choice with
    | .zero => body mode sourceAllowed choice
    | .data seed =>
        let original := Original.data seed.initial
        let a := backwardReadAt mode.limit (start seed)
        [⟨original,.data a⟩] ++ (lateSourceReach a).toList.flatMap (fun layer =>
          [⟨original,.reach layer⟩,⟨original,.target .demand⟩])

def commands := E21PrefixExactCompanion.commands

def original5 := E21PrefixExactCompanion.demand5
def completed5 := E21PrefixExactCompanion.completed5

/- This transaction superset includes the DEMAND image and all legal
T/FLOW inputs up to the source's post-read depth. It is not declared an
exact native final row set. Positive real witnesses are separated below. -/
def choices5 := commands modeF5 completed5 (actualUniverse modeF5 [0,1,2,3] false)
def raw5 := choices5.flatMap (body modeF5 (sourceEnabled E21PrefixExactCompanion.final4))
def pre5 := preSelected modeF5 completed5 raw5
def upper5 := canonical pre5

def rootDemandImage : Actual := actual [] .any .demand

def shrinkTwice (input : Actual) : Option Actual := do
  let first ← shrinkByDerived input
  shrinkByDerived first

def rootFlowD : Edge :=
  ⟨.data (p [] .star .flow),.data (actual [] .any .demand .flow)⟩

def realRootFlowD : List Edge :=
  allSelected modeF5 completed5
    ((commands modeF5 completed5 [rootDemandImage]).flatMap (body modeF5 false))

-- Extra current rows are reversed only after C5 and canonical storage.
def demand6 := FlowDemandCompletion.completed (handoff .forward upper5)
def inputs6 := actualUniverse modeB6 [1,2,3,4,5] false
def choices6 := commands modeB6 demand6 inputs6
def raw6 := choices6.flatMap (lateBody modeB6 false)
def pre6 := preSelected modeB6 demand6 raw6
def upper6 := canonical pre6

def isSourceOriginAtLeastTwo (row : Edge) : Bool :=
  match row.original,row.result with
  | .data i,.reach _ | .data i,.target _ => decide (i.path.length ≥ 2)
  | _,_ => true

def localZeroDATAisNormalF (row : Edge) : Bool :=
  match row.original,row.result with
  | .zero,.data a => decide (a = actual [f] .exact .normal)
  | _,_ => true

def demand7 := FlowDemandCompletion.completed (handoff .backward upper6)

/- This is the proposed REAL-actual closure contract, not an arbitrary
abstract-start grammar. A conditional FLOW STAR start is not a real STAR/T
caller input. An external native/scheduling proof must establish it. -/
def exactNormalInputs7 : List Actual :=
  ([0,1,2,3] : List Nat).map fun n => actual (List.replicate n f) .exact .normal

def choices7 := commands modeF7 demand7 exactNormalInputs7
def raw7 := choices7.flatMap (body modeF7 (sourceEnabled upper6))
def pre7 := preSelected modeF7 demand7 raw7
def upper7 := canonical pre7

def sourceImages7 : List Actual :=
  (allSelected modeF7 demand7 (body modeF7 (sourceEnabled upper6) .zero)).filterMap fun row =>
    match row.result with | .data a => some a | _ => none

def referenceGateAt (mode : Mode) (rows : List DemandRow) (input : Actual) : Option Actual :=
  let baseline := E21PrefixExactCompanion.dataCommands mode rows input
  if baseline.isEmpty then none else
    let budgets := (List.range input.pattern.path.length).map (fun n => n+1)
    (budgets.find? fun budget => equalCommandSets baseline
      (E21PrefixExactCompanion.dataCommands mode rows (cutAt budget input)))
      |>.map (fun budget => cutAt budget input)

/- NormalTarget persistence is typed and owned. DemandTarget has no report
ID and is never suppressed by this check. Model one fixed sink identity. -/
structure OwnedNormal where
  original : Original
  reportId : Nat
  scope : Nat
deriving DecidableEq, Repr

def keepTarget (saved : List OwnedNormal) (scope reportId : Nat) (row : Edge) : Bool :=
  match row.result with
  | .target .normal => !saved.contains ⟨row.original,reportId,scope⟩
  | _ => true

def known5 : List OwnedNormal :=
  [⟨.zero,0,0⟩,⟨.data (p [f] .exact T),0,2⟩]

theorem old_readToZero_misses_the_same_head_STAR_zero_normal_form :
    sourceReach (actual [f,f,f,f] .star .demand) = none := by decide

theorem typed_ZERO_adapter_recovers_same_head_STAR_source_DEMAND :
    lateSourceReach (actual [f,f,f,f] .star .demand) = some .demand := by decide

theorem typed_ZERO_adapter_keeps_exact_source_NORMAL :
    lateSourceReach (actual [f,f,f,f] .exact .normal) = some .normal := by decide

theorem typed_ZERO_adapter_does_not_satisfy_source_with_FLOW :
    lateSourceReach (actual [f,f,f,f] .star .normal .flow) = none := by decide

theorem typed_ZERO_adapter_preserves_pre_R6_backward_source_cells :
    (actualUniverse modeB4 [0,1,2,3] false).all (fun a => decide
      (lateSourceReach (backwardReadAt 3 a) = sourceReach (backwardReadAt 3 a))) = true := by decide

theorem the_shorter_F5_SOURCE_image_reaches_a_real_root_MAY :
    shrinkTwice (cutAt 2 rawF5) = some rootDemandImage := by decide

theorem the_new_F5_FLOW_DEMAND_family_is_accepted_by_a_complete_pair :
    rootFlowD ∈ realRootFlowD := by decide

theorem the_F5_upper_bound_includes_that_FLOW_DEMAND_family :
    rootFlowD ∈ upper5 := by decide

def real6FromNormalSink : List Edge :=
  allSelected modeB6 demand6
    ((commands modeB6 demand6 [actual [f] .exact .normal]).flatMap (lateBody modeB6 false))

def flow6 : Edge :=
  ⟨.data (p [f] .star .flow),.data (actual [f] .any .demand .flow)⟩

def real6DemandActual : Option Actual := do
  let row ← real6FromNormalSink.find? fun row => decide (row=flow6)
  match row.original,row.result with
  | .data initial,.data output =>
      applyFlow ⟨iface false 5 5,.data initial,.data output⟩ (actual [f] .exact .normal)
  | _,_ => none

def real6SourceRows : List Edge := allSelected modeB6 demand6
  ((commands modeB6 demand6 real6DemandActual.toList).flatMap (lateBody modeB6 false))

theorem the_F5_FLOW_DEMAND_family_builds_a_real_B6_FLOW_DEMAND_read :
    flow6 ∈ real6FromNormalSink := by decide

theorem applying_that_read_to_the_real_sink_seed_preserves_DEMAND :
    real6DemandActual = some (actual [f] .any .demand) := by decide

theorem the_B6_DEMAND_branch_really_keeps_an_ff_STAR_source_origin :
    (⟨.data (p [f,f] .star T),.reach .demand⟩ : Edge) ∈ real6SourceRows := by decide

theorem ALL_B6_precannonical_source_origins_are_at_least_ff :
    pre6.all isSourceOriginAtLeastTwo = true := by decide

theorem ALL_B6_precannonical_ZERO_DATA_is_exact_f_NORMAL :
    pre6.all localZeroDATAisNormalF = true := by decide

theorem F7_all_source_images_have_NORMAL_support :
    sourceImages7.all (fun a => decide (a.layer = .normal)) = true := by decide

theorem F7_precise_source_image_is_present : rawF5 ∈ sourceImages7 := by decide

theorem F7_kept_gate_preserves_the_precise_source_image :
    referenceGateAt modeF7 demand7 rawF5 = some rawF5 := by decide

theorem ALL_F7_current_rows_are_NORMAL_under_the_exact_input_contract :
    pre7.all (fun row => decide (support row.result = .normal)) = true := by decide

theorem no_outgoing_F7_demand_under_the_exact_input_contract :
    handoff .forward upper7 = [] := by decide

theorem normal_target_persistence_does_not_suppress_DemandTarget :
    keepTarget known5 2 0 ⟨.data (p [f] .exact T),.target .demand⟩ = true ∧
    keepTarget known5 2 0 ⟨.data (p [f] .exact T),.target .normal⟩ = false := by decide

def allCurrentRows := [(5,pre5,upper5),(6,pre6,upper6),(7,pre7,upper7)]
#eval ("E21_LATE_UPPER_BOUND_CURRENT_ROWS_NOT_NATIVE",reprStr allCurrentRows)
#eval ("E21_LATE_DEMANDS6_7_NOT_NATIVE",reprStr demand6,reprStr demand7)
#eval ("E21_LATE_SOURCE_IMAGES7",reprStr sourceImages7)
#eval ("E21_LATE_F5_REAL_FLOW_D",reprStr realRootFlowD)
#eval ("E21_LATE_KEEP_DEMAND_TARGET",keepTarget known5 2 0 ⟨.data (p [f] .exact T),.target .demand⟩)

#print axioms E21LatestContinuation.old_readToZero_misses_the_same_head_STAR_zero_normal_form
#print axioms E21LatestContinuation.typed_ZERO_adapter_recovers_same_head_STAR_source_DEMAND
#print axioms E21LatestContinuation.typed_ZERO_adapter_keeps_exact_source_NORMAL
#print axioms E21LatestContinuation.typed_ZERO_adapter_does_not_satisfy_source_with_FLOW
#print axioms E21LatestContinuation.typed_ZERO_adapter_preserves_pre_R6_backward_source_cells
#print axioms E21LatestContinuation.the_shorter_F5_SOURCE_image_reaches_a_real_root_MAY
#print axioms E21LatestContinuation.the_new_F5_FLOW_DEMAND_family_is_accepted_by_a_complete_pair
#print axioms E21LatestContinuation.the_F5_upper_bound_includes_that_FLOW_DEMAND_family
#print axioms E21LatestContinuation.the_F5_FLOW_DEMAND_family_builds_a_real_B6_FLOW_DEMAND_read
#print axioms E21LatestContinuation.applying_that_read_to_the_real_sink_seed_preserves_DEMAND
#print axioms E21LatestContinuation.the_B6_DEMAND_branch_really_keeps_an_ff_STAR_source_origin
#print axioms E21LatestContinuation.ALL_B6_precannonical_source_origins_are_at_least_ff
#print axioms E21LatestContinuation.ALL_B6_precannonical_ZERO_DATA_is_exact_f_NORMAL
#print axioms E21LatestContinuation.F7_all_source_images_have_NORMAL_support
#print axioms E21LatestContinuation.F7_precise_source_image_is_present
#print axioms E21LatestContinuation.F7_kept_gate_preserves_the_precise_source_image
#print axioms E21LatestContinuation.ALL_F7_current_rows_are_NORMAL_under_the_exact_input_contract
#print axioms E21LatestContinuation.no_outgoing_F7_demand_under_the_exact_input_contract
#print axioms E21LatestContinuation.normal_target_persistence_does_not_suppress_DemandTarget

end E21LatestContinuation

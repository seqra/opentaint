/-
Prepared finite closed-family upper bound for the scalar E21 fragment.
All raw/current families are computed; no supplied final three-row snapshot.
The ownership and boundary grammar below are explicit reference contracts,
not a theorem that Kotlin scheduling implements this interpreter.
-/
import E21OperatorLedger

namespace E21ClosedFamilies
open PlainStarRelativeAdmission
open DeepFlowCompletion
open DeepGuidanceArrival

set_option maxRecDepth 16384
set_option maxHeartbeats 32000000

inductive End where
  | data (value : Actual)
  | reach (layer : Layer)
  | target (layer : Layer)
deriving DecidableEq, Repr
structure Edge where
  original : Original
  result : End
deriving DecidableEq, Repr
inductive Choice where | zero | data (seed : Seed)
deriving DecidableEq, Repr

-- Parent/caller bindings do not change a local summary's original.
structure Continuation where
  parent : Original
  localInitial : Original

def applyAtParent (link : Continuation) (value : End) : Edge := ⟨link.parent,value⟩
def startLocal (choice : Choice) : Original :=
  match choice with | .zero => .zero | .data seed => .data seed.initial

theorem caller_binding_stays_in_parent (link : Continuation) (value : End) :
    (applyAtParent link value).original = link.parent := rfl

theorem DATA_admission_does_not_mint_local_ZERO (seed : Seed) :
    startLocal (.data seed) ≠ .zero := by simp [startLocal]

def originFlow : Original → Bool
  | .zero => false
  | .data p => decide (p.mark = .flow)
def support : End → Layer
  | .data a => a.layer | .reach s | .target s => s

def normalize (row : Edge) : Edge :=
  let original := match row.original with | .zero => .zero | .data p => .data (publicInitial p)
  let result := match row.result with
    | .data value => .data (E21OperatorLedger.publicData (match original with | .zero => p [] .exact T | .data i => i) value)
    | other => other
  ⟨original,result⟩

def geometricSame (left right : Pattern) : Bool :=
  decide (left.base=right.base ∧ left.path=right.path ∧ left.tail=right.tail ∧ left.exclusion=right.exclusion)

def covers (left right : Edge) : Bool :=
  match left.original,left.result,right.original,right.result with
  | .data i,.data c,.data j,.data d =>
      let flow := decide (i.mark=.flow ∧ c.pattern.mark=.flow ∧ j.mark=T ∧ d.pattern.mark=T ∧
        c.hasProtection=d.hasProtection ∧ (c.layer=.normal ∨ d.layer=.demand)) &&
        geometricSame i j && geometricSame c.pattern d.pattern
      let ordinary := decide (left.original=right.original ∧ c.pattern.base=d.pattern.base ∧
        c.pattern.mark=d.pattern.mark ∧ c.layer=d.layer ∧ c.hasProtection=d.hasProtection ∧
        c.pattern.tail=.any ∧ d.pattern.tail=.any ∧
        c.pattern.path.IsPrefix d.pattern.path)
      flow || ordinary
  | .zero,.data c,.zero,.data d =>
      decide (c.pattern.base=d.pattern.base ∧ c.pattern.mark=d.pattern.mark ∧ c.layer=d.layer ∧
        c.hasProtection=d.hasProtection ∧ c.pattern.tail=.any ∧
        d.pattern.tail=.any ∧ c.pattern.path.IsPrefix d.pattern.path)
  | _,_,_,_ => false

def canonical (rows : List Edge) : List Edge :=
  let unique := rows.eraseDups
  unique.filter fun row => !(unique.any fun other => decide (other ≠ row) && covers other row)

def entryOK (mode : Mode) (row : DemandRow) (original : Original) : Bool :=
  match row.entry,original with
  | .zero,.zero | .target,.zero => true
  | .data selector,.data initial =>
      ((scalarPattern selector).bind scalarDemand).any fun demand => E21OperatorLedger.stores mode demand initial
  | _,_ => false

def intersect (mode : Mode) (permission : DemandRow) (raw : Edge) : Option Edge := do
  let row := normalize raw
  if !entryOK mode permission row.original then none else
    match row.result,permission.exit with
    | .reach layer,.zero => pure ⟨row.original,.reach layer⟩
    | .target layer,.zero => pure ⟨row.original,.target layer⟩
    | .data actual,.data selector => do
        let d ← scalarPattern selector
        let kept ← AnnotatedC5Exit.restrictData (isForward mode) mode.limit (asExitFact actual) (asExitPattern d)
        let value ← fromExit kept
        pure ⟨row.original,.data {value with pattern := publicInitial value.pattern}⟩
    | _,_ => none

def preSelected (mode : Mode) (permissions : List DemandRow) (raw : List Edge) : List Edge :=
  raw.flatMap fun row => permissions.filterMap fun permission => intersect mode permission row

def allSelected (mode : Mode) (permissions : List DemandRow) (raw : List Edge) : List Edge :=
  canonical (preSelected mode permissions raw)

def body (mode : Mode) (sourceAllowed : Bool) (choice : Choice) : List Edge :=
  match choice with
  | .zero =>
      if isForward mode then
        let gen := if sourceAllowed then (programSourceOutput mode.limit).toList else []
        [⟨.zero,.reach .normal⟩] ++ gen.flatMap fun a =>
          [⟨.zero,.data a⟩] ++
          (possibleSink .zero a).toList.map (fun t => ⟨.zero,.target (if t.kind=.normalReport then .normal else .demand)⟩)
      else [⟨.zero,.reach .normal⟩,⟨.zero,.data (backwardReadAt mode.limit (actual [] .exact .normal))⟩]
  | .data seed =>
      let original := Original.data seed.initial
      if isForward mode then
        (forwardRead (start seed)).toList.flatMap fun a =>
          [⟨original,.data a⟩] ++
          (possibleSink original a).toList.map (fun t => ⟨original,.target (if t.kind=.normalReport then .normal else .demand)⟩)
      else
        let a := backwardReadAt mode.limit (start seed)
        [⟨original,.data a⟩] ++ (sourceReach a).toList.flatMap (fun layer =>
          [⟨original,.reach layer⟩,⟨original,.target .demand⟩])

def selected (direction : Direction) (row : Edge) : Bool :=
  decide (support row.result=.demand) ||
    (decide (direction=.backward) && decide (row.original=.zero))

def handoff (direction : Direction) (rows : List Edge) : List DemandRow :=
  (rows.filter (selected direction)).map fun row =>
    ⟨iface (decide (direction=.backward)) 5 5,
      match row.result with
      | .data a => .data (encode a.pattern)
      | .reach _ => .zero
      | .target _ => .target,
      match row.original with | .zero => .zero | .data i => .data (encode i)⟩

-- The universe is a finite program grammar upper bound, not hypothetical
-- arbitrary method inputs. B2: every DATA arrives after the backward read;
-- F3: source4/cap2/read1 plus nonexpanding replay, T support stays DEMAND.
-- No field cleaner, MUST producer, other mark or field exclusion exists.
def actualUniverse (mode : Mode) (depths : List Nat) (onlyDemandT : Bool) : List Actual :=
  depths.flatMap fun n => ([Tail.exact,.star,.any]).flatMap fun tail =>
    ([T,.flow]).flatMap fun mark => ([Layer.normal,.demand]).filterMap fun layer =>
      let a := actual (List.replicate n f) tail layer mark
      if legalActual mode a ∧ (onlyDemandT=false ∨ mark=.flow ∨ layer=.demand) then some a else none

def commands (mode : Mode) (rows : List DemandRow) (inputs : List Actual) : List Choice :=
  let data := rows.flatMap fun row => match row.entry with
    | .data selector => ((scalarPattern selector).bind scalarDemand).toList.flatMap fun demand =>
        inputs.flatMap fun a => (RejectAncestorStarAdmission.emitSeeds mode demand a).map Choice.data
    | _ => []
  let zero := if rows.any (fun row => decide (row.entry=.zero ∨ row.entry=.target)) then [Choice.zero] else []
  (zero ++ data).eraseDups

def mode1 : Mode := ⟨1,1,.forward⟩
def firstChoices : List Choice := [.zero,.data ⟨p [] .star .flow,.normal⟩,.data ⟨p [] .star T,.demand⟩]
def raw1 : List Edge := firstChoices.flatMap (body mode1 true)
def final1 : List Edge := canonical (raw1.map normalize)
def demand2 := handoff .forward final1
def choices2 := commands modeB2 demand2 (actualUniverse modeB2 [1] false)
def raw2 := choices2.flatMap (body modeB2 false)
def final2 := allSelected modeB2 demand2 raw2

def sourceEnabled (rows : List Edge) : Bool := rows.any fun row =>
  match row.original,row.result with | .data i,.reach _ => decide (i.mark=T) | _,_ => false

def demand3 := handoff .backward final2
def choices3 := commands modeF3 demand3 (actualUniverse modeF3 [0,1] true)
def raw3 := choices3.flatMap (body modeF3 (sourceEnabled final2))
def final3 := allSelected modeF3 demand3 raw3

def demand4 := handoff .forward final3
def choices4 := commands modeB4 demand4 (actualUniverse modeB4 [0,1,2,3] false)
def raw4 := choices4.flatMap (body modeB4 false)
def final4 := allSelected modeB4 demand4 raw4

def demand5 := handoff .backward final4

def isFlowDataD (row : Edge) : Bool :=
  match row.original,row.result with
  | .data i,.data a => decide (i.mark=.flow ∧ a.layer=.demand)
  | _,_ => false

def exactTTarget (row : Edge) : Bool :=
  match row.original,row.result with
  | .data i,.target _ => decide (i = p [f] .exact T)
  | _,_ => true

def dataEntryExitZero (row : DemandRow) : Bool :=
  match row.entry with | .data _ => decide (row.exit=.zero) | _ => true

def exactFDataEntry (row : DemandRow) : Bool :=
  match row.entry with | .data i => decide (i=encode (p [f] .exact T)) | _ => true

def dataCommands (mode : Mode) (rows : List DemandRow) (input : Actual) : List Seed :=
  (commands mode rows [input]).filterMap fun c => match c with | .data s => some s | .zero => none

def noCompletionRaw := dataCommands modeF5 demand5 rawF5
def noCompletionCut := dataCommands modeF5 demand5 (cutAt 2 rawF5)
def completed5 := FlowDemandCompletion.completed demand5
def withCompletionRaw := dataCommands modeF5 completed5 rawF5
def withCompletionCut := dataCommands modeF5 completed5 (cutAt 2 rawF5)
def fine : Seed := ⟨p [f,f,f] .star .flow,.normal⟩

theorem every_B2_physical_DATA_body_returns_f_head (input : Actual) :
    (backwardReadAt 1 input).pattern.path=[f] := by
  cases input with
  | mk pattern layer hasH =>
    cases pattern with
    | mk base path tail mark excluded =>
      cases path with
      | nil => rfl
      | cons first rest => rfl

theorem real_F3_GEN_is_MAY_DEMAND : programSourceOutput 2=some (actual [f] .any .demand) := by decide

theorem R1_raw_has_six_families : raw1.length=6 := by decide

theorem R1_canonical_drops_requested_T_DATA :
    (⟨.data (p [] .star T),.data (actual [] .any .demand)⟩ : Edge) ∉ final1 := by decide

theorem B2_has_no_root_DATA_initial :
    choices2.all (fun c => match c with | .zero => true | .data s => decide (s.initial.path=[f]))=true := by decide

theorem F3_ALL_FLOW_DATA_is_NORMAL : final3.all (fun row => !isFlowDataD row)=true := by decide

theorem F3_ALL_nonzero_Targets_have_exact_f_original : final3.all exactTTarget=true := by decide

theorem F3_has_real_NORMAL_shrinker :
    (⟨.data (p [f] .star .flow),.data (actual [] .star .normal .flow)⟩ : Edge) ∈ final3 := by decide

theorem B4_ALL_DATA_entries_have_ZERO_exits : demand4.all dataEntryExitZero=true := by decide

theorem B4_ALL_local_ZERO_DATA_is_exact_f_NORMAL :
    final4.all (fun row => match row.original,row.result with
      | .zero,.data a => decide (a=actual [f] .exact .normal)
      | _,_ => true)=true := by decide

theorem B4_real_ff_STAR_source_Reach_is_produced :
    (⟨.data (p [f,f] .star T),.reach .demand⟩ : Edge) ∈ final4 := by decide

theorem F5_ALL_DATA_entries_are_exact_f : demand5.all exactFDataEntry=true := by decide

theorem F5_no_completion_raw_and_cut_both_have_no_DATA_command :
    noCompletionRaw=[] ∧ noCompletionCut=[] := by decide

theorem F5_completed_Reach_endpoint_supplies_fine_command :
    fine ∈ withCompletionRaw ∧ fine ∉ withCompletionCut := by decide

-- Any additional row in the classified same-owner/ports family is covered
-- by the preceding ALL predicates; no exact-three-row input is assumed.
-- Native schedule, real loop gate and root source/report adapters are open.

-- Individually produced positive witnesses. The sink DATA is inside a local
-- ZERO actor; it crosses the backward read BEFORE the next boundary C2.
def realSinkBoundary : Option Actual :=
  (sinkSeed ⟨.zero,.demandTarget⟩).map (backwardReadAt 1)
def real2AtSink : List Edge := allSelected modeB2 demand2
  ((commands modeB2 demand2 realSinkBoundary.toList).flatMap (body modeB2 false))
def real2CallerMAY : Option Actual := do
  let row ← real2AtSink.find? fun row => decide
    (row=(⟨.data (p [f] .star .flow),.data (actual [f] .any .demand .flow)⟩ : Edge))
  let input ← realSinkBoundary
  match row.original,row.result with
  | .data initial,.data output => applyFlow ⟨iface false 5 5,.data initial,.data output⟩ input
  | _,_ => none
def real2 : List Edge := allSelected modeB2 demand2
  ((commands modeB2 demand2 (realSinkBoundary.toList ++ real2CallerMAY.toList)).flatMap (body modeB2 false))
def realDemand3 := handoff .backward real2
def real3 : List Edge := allSelected modeF3 realDemand3
  ((commands modeF3 realDemand3 (programSourceOutput 2).toList).flatMap
    (body modeF3 (sourceEnabled real2)))
def realDemand4 := handoff .forward real3

def normalShrinker : Option SavedRead := do
  let row ← real3.find? fun row => decide
    (row = (⟨.data (p [f] .star .flow),.data (actual [] .star .normal .flow)⟩ : Edge))
  match row.original,row.result with
  | .data initial,.data output => pure ⟨repeatPort5,initial,output⟩
  | _,_ => none

def growFromDerived (input : Actual) : Option Actual := do
  let row ← normalShrinker
  let reversed : SavedRead := ⟨repeatPort5,row.output.pattern,⟨row.initial,.normal,false⟩⟩
  applySaved reversed input

def realB4GrowingInput : Option Actual := do
  let sink ← sinkSeed ⟨.zero,.demandTarget⟩
  let first := backwardReadAt 3 sink
  let second ← growFromDerived first
  growFromDerived second

def freshF5Source : Option Actual :=
  if sourceEnabled final4 then programSourceOutput 4 else none

def shrinkByDerived (input : Actual) : Option Actual := do
  let row ← normalShrinker
  applySaved row input

def normalRootFromFreshSource : Option Actual := do
  let a ← freshF5Source
  let b ← shrinkByDerived a
  let c ← shrinkByDerived b
  shrinkByDerived c

theorem real_R2_source_hit_enables_the_same_SOURCE : sourceEnabled final2=true := by decide

theorem B4_growing_actual_comes_from_real_sink_seed_and_derived_NORMAL_record :
    realB4GrowingInput=some (actual [f,f,f] .exact .normal) := by decide

theorem real_R4_source_hit_enables_the_same_SOURCE : sourceEnabled final4=true := by decide

theorem fresh_R5_SOURCE_is_exact_NORMAL_without_promotion :
    freshF5Source=some rawF5 := by decide

theorem completed_view_distinguishes_every_proper_scalar_cut :
    fine ∈ withCompletionRaw ∧
    fine ∉ dataCommands modeF5 completed5 (cutAt 1 rawF5) ∧ fine ∉ withCompletionCut := by decide

theorem retained_fresh_actual_and_derived_NORMAL_record_reach_root :
    normalRootFromFreshSource=some (actual [] .exact .normal) := by decide

theorem the_derived_root_witness_is_a_NORMAL_Target :
    (normalRootFromFreshSource.bind (possibleSink .zero))=
      some ⟨.zero,.normalReport⟩ := by decide


-- This is the kept loop gate after reducing E21's unreachable AL and typed
-- enclosing control to constant empty DATA components. It is not a new
-- saved-record observer. Exact command sets include initial support.
def equalCommandSets (left right : List Seed) : Bool :=
  left.all right.contains && right.all left.contains

def referenceGate (rows : List DemandRow) (input : Actual) : Option Actual :=
  let baseline := dataCommands modeF5 rows input
  if baseline.isEmpty then none else
    ([1,2,3].find? fun budget => equalCommandSets baseline
      (dataCommands modeF5 rows (cutAt budget input))).map fun budget => cutAt budget input

def F5result (rows : List DemandRow) : Option TargetResult := do
  let source ← freshF5Source
  let kept ← referenceGate rows source
  let first ← shrinkByDerived kept
  let second ← shrinkByDerived first
  let root ← shrinkByDerived second
  possibleSink .zero root

def sourceRowsFromInput (input : Actual) : List Edge :=
  allSelected modeB4 realDemand4
    (((dataCommands modeB4 realDemand4 input).map Choice.data).flatMap (body modeB4 false))

theorem real_B4_growing_input_itself_produces_ff_source_Reach :
    (⟨.data (p [f,f] .star T),.reach .demand⟩ : Edge) ∈
      sourceRowsFromInput (actual [f,f,f] .exact .normal) := by decide

theorem no_completion_kept_gate_rejects_precise_SOURCE :
    referenceGate demand5 rawF5=none := by decide

theorem completion_kept_gate_retains_precise_SOURCE_at_budget_three :
    referenceGate completed5 rawF5=some rawF5 := by decide

theorem no_completion_reference_program_has_no_NORMAL_Target :
    F5result demand5=none := by decide

theorem completion_reference_program_has_the_real_NORMAL_Target :
    F5result completed5=some ⟨.zero,.normalReport⟩ := by decide

theorem F3_precanonical_ALL_FLOW_DATA_is_NORMAL :
    (preSelected modeF3 demand3 raw3).all (fun row => !isFlowDataD row)=true := by decide

theorem F3_precanonical_ALL_T_Targets_have_exact_f_original :
    (preSelected modeF3 demand3 raw3).all exactTTarget=true := by decide

theorem B4_precanonical_ALL_local_ZERO_DATA_is_exact_f_NORMAL :
    (preSelected modeB4 demand4 raw4).all (fun row => match row.original,row.result with
      | .zero,.data a => decide (a=actual [f] .exact .normal)
      | _,_ => true)=true := by decide

theorem subset_cannot_invent_a_forbidden_precanonical_family
    (upper subset : List Edge) (allowed : Edge → Bool)
    (classified : upper.all allowed=true)
    (included : ∀ row ∈ subset, row ∈ upper) : subset.all allowed=true := by
  apply List.all_eq_true.mpr
  intro row present
  exact List.all_eq_true.mp classified row (included row present)

theorem real_sink_boundary_is_f_exact_NORMAL :
    realSinkBoundary=some (actual [f] .exact .normal) := by decide

theorem real_current_FLOW_application_is_a_parent_MAY_not_local_ZERO :
    real2CallerMAY=some (actual [f] .any .demand) := by decide

theorem real_R2_fine_FLOW_DEMAND_is_individually_produced :
    (⟨.data (p [f] .star .flow),.data (actual [f] .any .demand .flow)⟩ : Edge) ∈ real2AtSink := by decide

theorem real_R3_NORMAL_shrinker_and_exact_Target_are_individually_produced :
    (⟨.data (p [f] .star .flow),.data (actual [] .star .normal .flow)⟩ : Edge) ∈ real3 ∧
    (⟨.data (p [f] .exact T),.target .demand⟩ : Edge) ∈ real3 := by decide

def dataOnlyRowSeeds (mode : Mode) (row : DemandRow) (input : Actual) : List Seed :=
  match row.entry with
  | .data selector => ((scalarPattern selector).bind scalarDemand).toList.flatMap
      (fun demand => RejectAncestorStarAdmission.emitSeeds mode demand input)
  | .zero | .target => []

theorem arbitrary_extra_ZERO_entry_cannot_mint_DATA_command
    (mode : Mode) (owner : Interface) (exit : FlowDemandCompletion.Exit) (input : Actual) :
    dataOnlyRowSeeds mode ⟨owner,.zero,exit⟩ input=[] := rfl

theorem arbitrary_extra_Target_entry_cannot_mint_DATA_command
    (mode : Mode) (owner : Interface) (exit : FlowDemandCompletion.Exit) (input : Actual) :
    dataOnlyRowSeeds mode ⟨owner,.target,exit⟩ input=[] := rfl

#print axioms E21ClosedFamilies.caller_binding_stays_in_parent
#print axioms E21ClosedFamilies.DATA_admission_does_not_mint_local_ZERO
#print axioms E21ClosedFamilies.every_B2_physical_DATA_body_returns_f_head
#print axioms E21ClosedFamilies.real_F3_GEN_is_MAY_DEMAND
#print axioms E21ClosedFamilies.R1_raw_has_six_families
#print axioms E21ClosedFamilies.R1_canonical_drops_requested_T_DATA
#print axioms E21ClosedFamilies.B2_has_no_root_DATA_initial
#print axioms E21ClosedFamilies.F3_ALL_FLOW_DATA_is_NORMAL
#print axioms E21ClosedFamilies.F3_ALL_nonzero_Targets_have_exact_f_original
#print axioms E21ClosedFamilies.F3_has_real_NORMAL_shrinker
#print axioms E21ClosedFamilies.B4_ALL_DATA_entries_have_ZERO_exits
#print axioms E21ClosedFamilies.B4_ALL_local_ZERO_DATA_is_exact_f_NORMAL
#print axioms E21ClosedFamilies.B4_real_ff_STAR_source_Reach_is_produced
#print axioms E21ClosedFamilies.F5_ALL_DATA_entries_are_exact_f
#print axioms E21ClosedFamilies.F5_no_completion_raw_and_cut_both_have_no_DATA_command
#print axioms E21ClosedFamilies.F5_completed_Reach_endpoint_supplies_fine_command
#print axioms E21ClosedFamilies.real_R2_source_hit_enables_the_same_SOURCE
#print axioms E21ClosedFamilies.B4_growing_actual_comes_from_real_sink_seed_and_derived_NORMAL_record
#print axioms E21ClosedFamilies.real_R4_source_hit_enables_the_same_SOURCE
#print axioms E21ClosedFamilies.fresh_R5_SOURCE_is_exact_NORMAL_without_promotion
#print axioms E21ClosedFamilies.completed_view_distinguishes_every_proper_scalar_cut
#print axioms E21ClosedFamilies.retained_fresh_actual_and_derived_NORMAL_record_reach_root
#print axioms E21ClosedFamilies.the_derived_root_witness_is_a_NORMAL_Target
#print axioms E21ClosedFamilies.real_B4_growing_input_itself_produces_ff_source_Reach
#print axioms E21ClosedFamilies.no_completion_kept_gate_rejects_precise_SOURCE
#print axioms E21ClosedFamilies.completion_kept_gate_retains_precise_SOURCE_at_budget_three
#print axioms E21ClosedFamilies.no_completion_reference_program_has_no_NORMAL_Target
#print axioms E21ClosedFamilies.completion_reference_program_has_the_real_NORMAL_Target
#print axioms E21ClosedFamilies.F3_precanonical_ALL_FLOW_DATA_is_NORMAL
#print axioms E21ClosedFamilies.F3_precanonical_ALL_T_Targets_have_exact_f_original
#print axioms E21ClosedFamilies.B4_precanonical_ALL_local_ZERO_DATA_is_exact_f_NORMAL
#print axioms E21ClosedFamilies.subset_cannot_invent_a_forbidden_precanonical_family
#print axioms E21ClosedFamilies.real_sink_boundary_is_f_exact_NORMAL
#print axioms E21ClosedFamilies.real_current_FLOW_application_is_a_parent_MAY_not_local_ZERO
#print axioms E21ClosedFamilies.real_R2_fine_FLOW_DEMAND_is_individually_produced
#print axioms E21ClosedFamilies.real_R3_NORMAL_shrinker_and_exact_Target_are_individually_produced
#print axioms E21ClosedFamilies.arbitrary_extra_ZERO_entry_cannot_mint_DATA_command
#print axioms E21ClosedFamilies.arbitrary_extra_Target_entry_cannot_mint_DATA_command

#eval ("E21_FAMILY_COUNTS",raw1.length,final1.length,final2.length,final3.length,final4.length,demand5.length)
#eval ("E21_R3_ALL",reprStr final3)
#eval ("E21_R4_ALL",reprStr final4)
#eval ("E21_R5_DEMAND_ALL",reprStr demand5)
end E21ClosedFamilies

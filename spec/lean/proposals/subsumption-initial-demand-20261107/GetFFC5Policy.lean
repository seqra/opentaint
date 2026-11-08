/-
Finite FULL getter/source/sink transaction model. The physical program is:
main(){ local b = initializedFreshChain(); sourceFFF(b); r=getFF(b); sinkT(r.f); }
getFF(p){ t=p.f; return t.f; }
sourceFFF is a caller rule assigning exact T at b.f.f.f, not a source-method
summary. b and r are dead locals at root exit. The model compares three C5 /
FLOW-completion policies over all DATA commands/results for this helper.

Imported actual C2, whole FLOW normalization, C5 and correlated application
are used. No NORMAL getter record, guide or source permission is an input.
The root CFG/ZERO/Target driver, source callback and dead-local projection
remain native adapters; this is not a proof of the full Kotlin engine.
-/
import E21OperatorLedger
import WrapperRecovery
import ConcreteConverterWrapper
import Relations

namespace GetFFC5Policy
open PlainStarRelativeAdmission
open ApSpec

set_option maxRecDepth 16384
set_option maxHeartbeats 32000000

abbrev Row := PlainStarWrapperRecovery.Relation
abbrev DRow := FlowDemandCompletion.Row

def argBase : Nat := 10
def retBase : Nat := 11
def callerBase : Nat := 20
def callerRet : Nat := 21
def f : Nat := 4
def T : ScalarMark := .full 7
def p (base : Nat) (path : List Nat) (tail : Tail) (mark : ScalarMark := .flow) : Pattern :=
  ⟨base,path,tail,mark,[]⟩
def a (pattern : Pattern) (layer : Layer := .normal) : Actual := ⟨pattern,layer,false⟩

def b2 : Mode := ⟨2,1,.backward⟩
def f3 : Mode := ⟨3,2,.forward⟩
def b4 : Mode := ⟨4,3,.backward⟩
def f5 : Mode := ⟨5,4,.forward⟩

def unique [DecidableEq α] (values : List α) : List α :=
  values.foldl (fun result value => if value ∈ result then result else result ++ [value]) []

def forwardRead (limit : Nat) (input : Actual) : Option Actual :=
  (PlainStarWrapperRecovery.readForward limit f input).map fun value =>
    {value with pattern := {value.pattern with base := retBase}}
def backwardRead (limit : Nat) (input : Actual) : Actual :=
  let value := PlainStarWrapperRecovery.readBackward limit f input
  {value with pattern := {value.pattern with base := argBase}}
def body (mode : Mode) (input : Actual) : Option Actual :=
  match mode.direction with
  | .forward => (forwardRead mode.limit input).bind (forwardRead mode.limit)
  | .backward => some (backwardRead mode.limit (backwardRead mode.limit input))

def publicRow (initial : Pattern) (output : Actual) : Row :=
  let original := publicInitial initial
  ⟨original,E21OperatorLedger.publicData original output⟩

def boundaryFacts (mode : Mode) (input : Actual) : List Actual :=
  let carried := if mode.direction = .forward ∧ input.pattern.base = argBase then [input] else []
  carried ++ (body mode input).toList

def run1Analyze (initial : Pattern) : List Row :=
  (boundaryFacts ⟨3,1,.forward⟩ (start ⟨initial,intrinsic initial⟩)).map (publicRow initial)

/- The helper has no mark-check, source or cleaner rule. Its actual request
set is empty. The optional T diagonal below is an exhaustive conservative
candidate check, not a fabricated request in the program. -/
def helperMarkRequests : List ScalarMark := []
def r1Seeds : List Pattern := p argBase [] .star ::
  helperMarkRequests.map (fun mark => p argBase [] .star mark)
def r1Rows : List Row := unique (r1Seeds.flatMap run1Analyze)
def possibleRequestedT : List Row := run1Analyze (p argBase [] .star T)

def interface (mode : Mode) : FlowDemandCompletion.Interface :=
  ⟨42,decide (mode.direction = .forward),0,
    (if mode.direction = .forward then -1 else -2),
    (if mode.direction = .forward then -2 else -1)⟩

def handoff (next : Mode) (rows : List Row) : List DRow :=
  unique ((rows.filter fun row => decide (row.output.layer = .demand)).map fun row =>
    ⟨interface next,.data (DeepGuidanceArrival.encode row.output.pattern),
      .data (DeepGuidanceArrival.encode row.initial)⟩)

def demandView (completion : Bool) (rows : List DRow) : List DRow :=
  unique (if completion then FlowDemandCompletion.completed rows else rows)

def rowEntry (row : DRow) : Option Demand := do
  let pattern ← match row.entry with
    | .data value => DeepFlowCompletion.scalarPattern value
    | _ => none
  DeepFlowCompletion.scalarDemand pattern
def rowExit (row : DRow) : Option Pattern :=
  match row.exit with
  | .data value => DeepFlowCompletion.scalarPattern value
  | .zero => none

def commands (mode : Mode) (rows : List DRow) (submitted : Actual) : List Seed :=
  unique (rows.flatMap fun row =>
    match rowEntry row with
    | none => []
    | some demand => RejectAncestorStarAdmission.emitSeeds mode demand submitted)

def blocksSTAR (conclusion selector : Pattern) : Bool :=
  decide (conclusion.tail = .star ∧ conclusion.path.length < selector.path.length) &&
    (dropPrefix conclusion.path selector.path).isSome

def finish (rejectSTAR : Bool) (mode : Mode) (row : DRow) (seed : Seed)
    (raw : Actual) : Option Row := do
  let demand ← rowEntry row
  let selector ← rowExit row
  let original := publicInitial seed.initial
  let value := E21OperatorLedger.publicData original raw
  if rejectSTAR && blocksSTAR value.pattern selector then none else
    (E21OperatorLedger.finishData mode demand (some selector) seed raw).map fun result =>
      ⟨result.1,result.2⟩

def normalAlignedCovers (short long : Row) : Bool :=
  decide (short.output.layer = .normal ∧ long.output.layer = .normal ∧
    short.initial.mark = .flow ∧ long.initial.mark = .flow ∧
    short.output.pattern.mark = .flow ∧ long.output.pattern.mark = .flow ∧
    short.initial.tail = .star ∧ long.initial.tail = .star ∧
    short.output.pattern.tail = .star ∧ long.output.pattern.tail = .star ∧
    short.output.hasProtection = false ∧ long.output.hasProtection = false) &&
    (FlowAntichains.Relations.coverWitness
      (⟨42,short.initial.base,short.output.pattern.base,short.initial.path,short.output.pattern.path⟩ : FlowAntichains.Relations.Row Nat)
      (⟨42,long.initial.base,long.output.pattern.base,long.initial.path,long.output.pattern.path⟩ : FlowAntichains.Relations.Row Nat)).isSome

def authority (rows : List Row) : List Row :=
  let values := unique rows
  values.filter fun long => !(values.any fun short => decide (short ≠ long) && normalAlignedCovers short long)

def infer (rejectSTAR : Bool) (mode : Mode) (rows : List DRow) (submitted : Actual) : List Row :=
  authority ((commands mode rows submitted).flatMap fun seed =>
    (boundaryFacts mode (start seed)).flatMap fun raw =>
      rows.filterMap fun row => finish rejectSTAR mode row seed raw)

def normal (rows : List Row) : List Row := rows.filter fun row => decide (row.output.layer = .normal)
def demand (rows : List Row) : List Row := rows.filter fun row => decide (row.output.layer = .demand)
def returns (rows : List Row) : List Row := rows.filter fun row => decide (row.output.pattern.base = retBase)
def arguments (rows : List Row) : List Row := rows.filter fun row => decide (row.output.pattern.base = argBase)

/- Actual source and sink actions use the pinned correlated AP action kernel.
Call binding is only the ordinary caller-local/parameter base renaming. -/
def sourceFrom : PFact := ConcreteConverterWrapper.zero.fact
def sourceTo : PFact := ⟨callerBase,[f,f,f],.exact,.conc 7⟩
def source (limit : Nat) : Option Actual :=
  (ConcreteConverterWrapper.coreResult limit
    (Run1CorrelatedConcreteInitials.rawApply ConcreteConverterWrapper.zero sourceFrom sourceTo)).map
    fun value => {value with pattern := {value.pattern with base := argBase}}

def sinkFrom : PFact := ⟨callerRet,[f],.exact,.conc 7⟩
inductive Target where | normal | demand
deriving DecidableEq, Repr

def hitSink (input : Actual) : Option Target := do
  if input.pattern.base != retBase then none else
    pure ()
  let supplied ← ConcreteConverterWrapper.coreActual
    {input with pattern := {input.pattern with base := callerRet}}
  let result ← (Run1CorrelatedConcreteInitials.rawApply supplied sinkFrom sourceFrom).facts.head?
  pure (if result.demand then .demand else .normal)

def reverseSink : Option Actual :=
  (ConcreteConverterWrapper.coreResult 1
    (Run1CorrelatedConcreteInitials.rawApply ConcreteConverterWrapper.zero sourceFrom sinkFrom)).map
    fun value => {value with pattern := {value.pattern with base := retBase}}

def acceptedSource (input : Actual) : Bool :=
  decide (input.pattern.base = argBase) &&
  ((ConcreteConverterWrapper.coreActual
    {input with pattern := {input.pattern with base := callerBase}}).map fun supplied =>
    !(Run1CorrelatedConcreteInitials.rawApply supplied sourceTo sourceFrom).facts.isEmpty).getD false

def applyRow (limit : Nat) (row : Row) (input : Actual) : Option Actual :=
  PlainStarWrapperRecovery.applyRelation limit row input

def reverseRow (row : Row) : Row :=
  ⟨row.output.pattern,⟨row.initial,row.output.layer,row.output.hasProtection⟩⟩

def applyRows (limit : Nat) (rows : List Row) (input : Actual) : List Actual :=
  unique (rows.filterMap fun row => applyRow limit row input)

def r1Outputs : List Actual :=
  match source 1 with | none => [] | some input => applyRows 1 r1Rows input
def r1Targets : List Target := unique (r1Outputs.filterMap hitSink)
def b2Guides : List DRow := handoff b2 r1Rows

def b2Rows (completion : Bool) : List Row :=
  if .demand ∈ r1Targets then
    match reverseSink with
    | none => []
    | some offered => infer false b2 (demandView completion b2Guides) offered
  else []
def b2SourceInputs (completion : Bool) : List Actual :=
  match reverseSink with | none => [] | some offered => applyRows 1 (b2Rows completion) offered
def sourcePermissionR3 (completion : Bool) : Bool :=
  (b2SourceInputs completion).any acceptedSource

def f3Guides (completion : Bool) : List DRow := handoff f3 (b2Rows completion)
def f3Rows (rejectSTAR completion : Bool) : List Row :=
  if sourcePermissionR3 completion then
    match source 2 with
    | none => []
    | some offered => infer rejectSTAR f3 (demandView completion (f3Guides completion)) offered
  else []
def f3Outputs (rejectSTAR completion : Bool) : List Actual :=
  match source 2 with
  | none => []
  | some offered => applyRows 2 (normal r1Rows ++ (normal (b2Rows completion)).map reverseRow ++
      f3Rows rejectSTAR completion) offered
def f3Targets (rejectSTAR completion : Bool) : List Target :=
  unique ((f3Outputs rejectSTAR completion).filterMap hitSink)

def b4Guides (rejectSTAR completion : Bool) : List DRow :=
  handoff b4 (f3Rows rejectSTAR completion)
def b4Rows (rejectSTAR completion : Bool) : List Row :=
  if .demand ∈ f3Targets rejectSTAR completion then
    match reverseSink with
    | none => []
    | some offered => infer rejectSTAR b4
        (demandView completion (b4Guides rejectSTAR completion)) offered
  else []
def b4SourceInputs (rejectSTAR completion : Bool) : List Actual :=
  if .demand ∈ f3Targets rejectSTAR completion then
    match reverseSink with
    | none => []
    | some offered => applyRows 3
        ((normal r1Rows).map reverseRow ++ normal (b2Rows completion) ++
          (normal (f3Rows rejectSTAR completion)).map reverseRow ++ b4Rows rejectSTAR completion) offered
  else []
def sourcePermissionR5 (rejectSTAR completion : Bool) : Bool :=
  (b4SourceInputs rejectSTAR completion).any acceptedSource

def f5Guides (rejectSTAR completion : Bool) : List DRow := handoff f5 (b4Rows rejectSTAR completion)
def f5Rows (rejectSTAR completion : Bool) : List Row :=
  if sourcePermissionR5 rejectSTAR completion then
    match source 4 with
    | none => []
    | some offered => infer rejectSTAR f5
        (demandView completion (f5Guides rejectSTAR completion)) offered
  else []
def f5Outputs (rejectSTAR completion : Bool) : List Actual :=
  if sourcePermissionR5 rejectSTAR completion then
    match source 4 with
    | none => []
    | some offered => applyRows 4
        (normal r1Rows ++ (normal (b2Rows completion)).map reverseRow ++ normal (f3Rows rejectSTAR completion) ++
          (normal (b4Rows rejectSTAR completion)).map reverseRow ++ f5Rows rejectSTAR completion) offered
  else []
def f5Targets (rejectSTAR completion : Bool) : List Target :=
  unique ((f5Outputs rejectSTAR completion).filterMap hitSink)

def expectedR1Argument : Row := ⟨p argBase [] .star,a (p argBase [] .star)⟩
def expectedR1 : Row := ⟨p argBase [] .star,a (p retBase [] .any) .demand⟩
def expectedB2 : Row := ⟨p retBase [f] .star,a (p argBase [f] .any) .demand⟩
def expectedF3Normal : Row := ⟨p argBase [f,f] .star,a (p retBase [] .star)⟩
def expectedF3Bridge : Row := ⟨p argBase [f] .star,a (p retBase [f] .any) .demand⟩
def expectedB4Bridge : Row := ⟨p retBase [f] .star,a (p argBase [f,f] .any) .demand⟩
def expectedF5Normal : Row := ⟨p argBase [f,f,f] .star,a (p retBase [f] .star)⟩

theorem source_chain_is_derived_at_each_real_limit :
    source 1 = some (a (p argBase [f] .any T) .demand) ∧
    source 2 = some (a (p argBase [f,f] .any T) .demand) ∧
    source 4 = some (a (p argBase [f,f,f] .exact T)) := by decide

theorem run1_catalog_has_no_NORMAL_return_provider :
    r1Rows = [expectedR1Argument,expectedR1] ∧
    returns (normal r1Rows) = [] ∧ normal r1Rows = [expectedR1Argument] ∧ helperMarkRequests = [] := by decide

theorem even_optional_requested_T_only_yields_a_DEMAND_diagonal :
    possibleRequestedT = [⟨p argBase [] .star T,a (p argBase [] .star T) .demand⟩,
      ⟨p argBase [] .star T,a (p retBase [] .any T) .demand⟩] := by decide

theorem run1_sink_and_backward_offer_are_real_actions :
    r1Targets = [.demand] ∧ reverseSink = some (a (p retBase [f] .exact T)) := by decide

theorem B2_completion_changes_no_admitted_helper_family :
    b2Rows false = [expectedB2] ∧ b2Rows true = [expectedB2] ∧
    normal (b2Rows false) = [] ∧ normal (b2Rows true) = [] := by decide

theorem B2_source_permission_is_from_actual_backward_source_acceptance :
    sourcePermissionR3 false = true ∧ sourcePermissionR3 true = true := by decide

theorem old_C5_without_completion_derives_the_NORMAL_read2_provider :
    f3Rows false false = [expectedF3Normal] ∧ f3Targets false false = [.demand] := by decide

theorem proposed_C5_without_completion_has_no_helper_DATA_or_Target_at_F3 :
    f3Rows true false = [] ∧
    f3Outputs true false = [a (p argBase [f,f] .any T) .demand] ∧ f3Targets true false = [] ∧
    sourcePermissionR5 true false = false ∧ f5Targets true false = [] := by decide

theorem completion_derives_only_the_required_F3_DEMAND_bridge :
    returns (f3Rows true true) = [expectedF3Bridge] ∧ f3Targets true true = [.demand] := by decide

theorem B4_old_provider_returns_precise_source_path :
    b4Rows false false = [] ∧
    b4SourceInputs false false = [a (p argBase [f,f,f] .exact T)] ∧
    sourcePermissionR5 false false = true := by decide

theorem B4_completed_bridge_retains_a_finer_demand_and_source_permission :
    b4Rows true true = [expectedB4Bridge] ∧
    b4SourceInputs true true = [a (p argBase [f,f] .any T) .demand] ∧
    sourcePermissionR5 true true = true := by decide

theorem F5_completed_policy_derives_a_NORMAL_provider_and_finding :
    returns (f5Rows true true) = [expectedF5Normal] ∧ f5Targets true true = [.normal] := by decide

theorem F5_old_policy_uses_its_derived_saved_NORMAL_provider :
    f5Rows false false = [] ∧ f5Targets false false = [.normal] := by decide

def completeHelperLedger : List (String × String) := [
  ("R1 ACTUAL",reprStr (source 1)),("R1 ROWS",reprStr r1Rows),
  ("B2 ORIGINAL GUIDES",reprStr b2Guides),
  ("B2 COMPLETED GUIDES",reprStr (demandView true b2Guides)),
  ("B2 ROWS WITHOUT COMPLETION",reprStr (b2Rows false)),
  ("B2 ROWS WITH COMPLETION",reprStr (b2Rows true)),
  ("F3 ACTUAL",reprStr (source 2)),("F3 ORIGINAL GUIDES",reprStr (f3Guides false)),
  ("F3 COMPLETED GUIDES",reprStr (demandView true (f3Guides true))),
  ("F3 OLD ROWS",reprStr (f3Rows false false)),
  ("F3 REJECT STAR/NO COMPLETION ROWS",reprStr (f3Rows true false)),
  ("F3 REJECT STAR/COMPLETION ROWS",reprStr (f3Rows true true)),
  ("B4 COMPLETED GUIDES",reprStr (demandView true (b4Guides true true))),
  ("B4 COMPLETED ROWS",reprStr (b4Rows true true)),
  ("B4 COMPLETED SOURCE INPUTS",reprStr (b4SourceInputs true true)),
  ("F5 ACTUAL",reprStr (source 4)),
  ("F5 COMPLETED GUIDES",reprStr (demandView true (f5Guides true true))),
  ("F5 COMPLETED ROWS",reprStr (f5Rows true true)),
  ("OLD F5 TARGETS",reprStr (f5Targets false false)),
  ("REJECT/NO COMPLETION F5 TARGETS",reprStr (f5Targets true false)),
  ("REJECT/COMPLETION F5 TARGETS",reprStr (f5Targets true true))]

#eval ("GETFF_HELPER_FAMILY_LEDGER_NOT_A_NATIVE_DRIVER",completeHelperLedger)

#print axioms source_chain_is_derived_at_each_real_limit
#print axioms run1_catalog_has_no_NORMAL_return_provider
#print axioms even_optional_requested_T_only_yields_a_DEMAND_diagonal
#print axioms run1_sink_and_backward_offer_are_real_actions
#print axioms B2_completion_changes_no_admitted_helper_family
#print axioms B2_source_permission_is_from_actual_backward_source_acceptance
#print axioms old_C5_without_completion_derives_the_NORMAL_read2_provider
#print axioms proposed_C5_without_completion_has_no_helper_DATA_or_Target_at_F3
#print axioms completion_derives_only_the_required_F3_DEMAND_bridge
#print axioms B4_old_provider_returns_precise_source_path
#print axioms B4_completed_bridge_retains_a_finer_demand_and_source_permission
#print axioms F5_completed_policy_derives_a_NORMAL_provider_and_finding
#print axioms F5_old_policy_uses_its_derived_saved_NORMAL_provider

end GetFFC5Policy

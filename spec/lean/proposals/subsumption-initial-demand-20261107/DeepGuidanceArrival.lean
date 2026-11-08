/-
Prepared finite E21 producer bridge. No native-equivalence/global-driver claim.
The source and CFG are inputs; no demand row, NORMAL provider or source-hit
permission is an input. All needed rows below are computed from ordinary
operations, existing run-1 abstraction/mark requests, typed control lookup,
the checked C2/C5 components and port-preserving handoff.

Actual schedule: F1=1, B2=1, F3=2, B4=3, F5=4. The earlier Deep35 B4=2
cells remain unchanged historical local checks. This module uses B4=3.
-/
import DeepFlowCompletion
import Discovery
import ExceptionalControlDemand

namespace DeepGuidanceArrival
open PlainStarRelativeAdmission
open DeepFlowCompletion
open ApSpec
set_option maxRecDepth 8192
set_option maxHeartbeats 16000000

def modeB2 : Mode := ⟨2,1,.backward⟩
def modeF3 : Mode := ⟨3,2,.forward⟩
def modeB4 : Mode := ⟨4,3,.backward⟩
def modeF5 : Mode := ⟨5,4,.forward⟩
def isForward (mode : Mode) : Bool := decide (mode.direction = Direction.forward)

def iface (forward : Bool) (entry output : Int) : Interface := ⟨17,forward,2,entry,output⟩
def normalControlEntry (forward : Bool) : Int := if forward then -1 else -2
def terminalExit (forward : Bool) : Int := if forward then -2 else -1

inductive Role where | normal | exceptional | middle
deriving DecidableEq, Repr

def graph8 : LoopFragments.Discovery.Overlay 8 where
  raw := fun source target =>
    (source == 0 && target == 1) || (source == 1 && target == 2) ||
    (source == 2 && target == 3) || (source == 3 && target == 4) ||
    (source == 4 && target == 5) || (source == 5 && target == 2)
  normal := 6
  exceptional := 7
  distinctExits := by decide
  dead := fun node => decide (node.val < 6)
  exceptionalHasNoSuccessor := by decide
  exceptionalIsNotDead := by decide

def backwardSinkDiscovery : LoopFragments.Discovery.Path
    (LoopFragments.Discovery.backward graph8) 7 5 :=
  LoopFragments.Discovery.discoverDead graph8 5 (by decide)

def forwardFirstEntry : LoopFragments.Discovery.Path graph8.raw 0 2 :=
  .cons (middle := 1) (by decide) (.cons (middle := 2) (by decide) (.refl 2))

def forwardFeedback : LoopFragments.Discovery.Path graph8.raw 2 2 :=
  .cons (middle := 3) (by decide) (.cons (middle := 4) (by decide)
    (.cons (middle := 5) (by decide) (.cons (middle := 2) (by decide) (.refl 2))))

def backwardSourceToFeedback : LoopFragments.Discovery.Path
    (LoopFragments.Discovery.backward graph8) 3 5 :=
  .cons (middle := 2) (by decide) (.cons (middle := 5) (by decide) (.refl 5))

theorem forward_graph_has_no_normal_or_exceptional_leave :
    graph8.raw 5 6 = false ∧ graph8.raw 5 7 = false := ⟨rfl,rfl⟩

theorem discovery_reaches_the_real_sink_without_a_forward_edge :
    LoopFragments.Discovery.backward graph8 7 5 = true ∧ graph8.raw 5 7 = false := by decide

def forwardRead (input : Actual) : Option Actual :=
  match input.pattern.path with
  | [] => if input.pattern.tail = .star ∨ input.pattern.tail = .any then
      some ⟨⟨input.pattern.base,[],.any,input.pattern.mark,[]⟩,.demand,input.hasProtection⟩ else none
  | _ :: _ => readKnownHead f input

def backwardReadAt (limit : Nat) (input : Actual) : Actual := cutAt limit (reverseRead f input)

def programSourceOutput (limit : Nat) : Option Actual := forwardRead (cutAt limit sourceFFFF)

def run1StartFromArrival (input : Actual) : Seed :=
  ⟨⟨input.pattern.base,[],.star,.flow,[]⟩,.normal⟩

def run1RequestedT (flowSeed : Seed) : Seed :=
  let initial := {flowSeed.initial with mark := T}
  ⟨initial,intrinsic initial⟩

/- The existing sink mark gate, not a new concrete standing initial. -/
def requestsT (input : Actual) : Bool :=
  let mark := match input.pattern.mark with | .flow => MarkA.star | .full id => MarkA.conc id
  match markGate (.conc 1) mark with | .req id => decide (id = 1) | _ => false

def possibleSink (original : Original) (input : Actual) : Option TargetResult :=
  if input.pattern.base = x ∧ input.pattern.path = [] ∧ input.pattern.mark = T ∧
      (input.pattern.tail = .exact ∨ input.pattern.tail = .any ∨ input.pattern.tail = .star) then
    some ⟨original,if input.layer = .normal then .normalReport else .demandTarget⟩
  else none

def encode (pattern : Pattern) : FlowDemandCompletion.Pattern :=
  ⟨.local pattern.base,pattern.path.map RelativeRestriction.Accessor.field,
    match pattern.tail with | .exact => .exact | .star => .star | .any => .may | .must => .must,
    match pattern.mark with | .flow => .flow | .full id => .full id,
    pattern.exclusion.map RelativeRestriction.Accessor.field⟩

inductive Result where
  | data (value : Actual)
  | reach (layer : Layer)
deriving DecidableEq, Repr

structure Publication where
  interface : Interface
  original : Original
  result : Result
deriving DecidableEq, Repr

structure Terminal where
  interface : Interface
  original : Original
deriving DecidableEq, Repr

def projectData (row : Publication) : DemandRow :=
  ⟨reverseInterface row.interface,
    match row.result with
    | .reach _ => .zero
    | .data value => .data (encode value.pattern),
    match row.original with
    | .zero => .zero
    | .data initial => .data (encode (publicInitial initial))⟩

def projectTarget (row : Terminal) : DemandRow :=
  ⟨reverseInterface row.interface,.target,
    match row.original with
    | .zero => .zero
    | .data initial => .data (encode (publicInitial initial))⟩

def isZeroOriginal : Original → Bool
  | .zero => true | .data _ => false

def borrowNormal (forward : Bool) (role : Role) (original : Original) : Bool :=
  isZeroOriginal original &&
    decide (role = .normal ∨ (forward = false ∧ role = .exceptional))

def sameOwner (left right : Interface) : Bool :=
  decide (left.methodContext = right.methodContext ∧ left.direction = right.direction ∧
    left.scope = right.scope)

def visibleEntry (forward : Bool) (role : Role) (actual : Interface)
    (original : Original) (row : DemandRow) : Bool :=
  sameOwner actual row.interface &&
    (decide (row.interface.entryPort = actual.entryPort) ||
      (borrowNormal forward role original && decide (row.interface.entryPort = normalControlEntry forward)))

def entryAccepts (mode : Mode) (entry : FlowDemandCompletion.Entry) (original : Original) : Bool :=
  match entry,original with
  | .zero,.zero | .target,.zero => true
  | .data selector,.data initial =>
      ((scalarPattern selector).bind scalarDemand).any fun demand => canStoreInitial mode demand initial
  | _,_ => false

def fromExit (value : AnnotatedC5Exit.Fact) : Option Actual := do
  let path ← natPath value.path
  let excluded ← natPath value.exclusion
  let mark ← match value.slot with | .full id => some (.full id) | .flow [] => some .flow | _ => none
  let tail : Tail := match value.tail with | .exact => .exact | .star => .star | .may => .any | .must => .must
  let layer : Layer := match value.layer with | .normal => .normal | .demand => .demand
  pure ⟨⟨value.base,path,tail,mark,excluded⟩,layer,value.h⟩

def publish (mode : Mode) (role : Role) (location : Interface) (original : Original)
    (result : Result) (permission : DemandRow) : Option Publication := do
  if !(visibleEntry (isForward mode) role location original permission &&
      decide (permission.interface.outputPort = location.outputPort) && entryAccepts mode permission.entry original)
    then none
  else match permission.exit,result with
  | .zero,.reach layer => pure ⟨location,original,.reach layer⟩
  | .data selector,.data value => do
      let pattern ← scalarPattern selector
      let kept ← AnnotatedC5Exit.restrictData (isForward mode) mode.limit
        (asExitFact value) (asExitPattern pattern)
      let scalar ← fromExit kept
      pure ⟨location,original,.data scalar⟩
  | _,_ => none

def controlAdmission (forward : Bool) (role : Role) (location : Interface) (rows : List DemandRow) : Bool :=
  rows.any fun row => visibleEntry forward role location .zero row &&
    decide (row.entry = .zero ∨ row.entry = .target)

def normalOutputs (forward : Bool) : List Int := if forward then [5] else [1,5]

def targetPermission (mode : Mode) (role : Role) (location : Interface) (original : Original)
    (rows : List DemandRow) : Bool :=
  rows.any fun row => visibleEntry (isForward mode) role location original row &&
    decide (row.interface.outputPort ∈ location.outputPort :: normalOutputs (isForward mode)) &&
    entryAccepts mode row.entry original && decide (row.exit = .zero)

def admitFrom (mode : Mode) (row : DemandRow) (input : Actual) : Option Seed := do
  let selector ← match row.entry with | .data value => scalarPattern value | _ => none
  let demand ← scalarDemand selector
  emit mode demand input

def applyFlow (row : Publication) (input : Actual) : Option Actual :=
  match row.original,row.result with
  | .data initial,.data output =>
    if initial.base = input.pattern.base ∧ initial.tail = .star ∧ initial.mark = .flow then
      match dropPrefix initial.path input.pattern.path with
      | none => none
      | some suffix =>
        let path := if output.pattern.tail = .any then output.pattern.path else output.pattern.path ++ suffix
        let tail := if output.pattern.tail = .any then .any else input.pattern.tail
        some ⟨⟨output.pattern.base,path,tail,input.pattern.mark,output.pattern.exclusion⟩,
          joinLayer output.layer input.layer,output.hasProtection || input.hasProtection⟩
    else none
  | _,_ => none

/- Raw selected AP operation, with ordinary base x encoded as x+1 and the
typed ZERO output encoded as AP base 0. MUST is outside this program. -/
def toAP (input : Actual) : Option ApSpec.AFact := do
  let kind ← match input.pattern.tail with
    | .exact => some Kind.exact | .star => some (Kind.star (.set input.pattern.exclusion))
    | .any => some Kind.any | .must => none
  let mark := match input.pattern.mark with | .flow => MarkA.star | .full id => MarkA.conc id
  pure ⟨⟨input.pattern.base+1,input.pattern.path,kind,mark⟩,decide (input.layer = .demand)⟩

def sourceFrom : PFact := ⟨x+1,[f,f,f,f],.exact,.conc 1⟩
def zeroTo : PFact := ⟨0,[],.exact,.conc 0⟩

def readToZero (premisePattern : Pattern) (input : Actual) : Option Layer := do
  let premise ← toAP ⟨premisePattern,intrinsic premisePattern,false⟩
  let scalar ← toAP input
  let result := ApSpec.Run1CorrelatedConcreteInitials.rawApply scalar premise.fact zeroTo
  match result.facts with
  | [kept] => if kept.fact = zeroTo then some (if kept.demand then .demand else .normal) else none
  | _ => none

def sourceReach (input : Actual) : Option Layer := readToZero (p [f,f,f,f] .exact T) input

def sinkSeed (target : TargetResult) : Option Actual :=
  if target.kind = .demandTarget then some (actual [] .exact .normal) else none

def run1SourceData (entry : Int) : Option Publication :=
  (programSourceOutput 1).map fun value => ⟨iface true entry 5,.zero,.data value⟩

def run1Flow : Option Publication := do
  let arrival ← programSourceOutput 1
  let initial := run1StartFromArrival arrival
  let output ← forwardRead (start initial)
  pure ⟨iface true 5 5,.data initial.initial,.data output⟩

def run1SourceTarget : Option Terminal := do
  let output ← programSourceOutput 1
  let target ← possibleSink .zero output
  if target.kind = .demandTarget then pure ⟨iface true 5 (-2),target.original⟩ else none

def run1MarkedTarget : Option Terminal := do
  let arrival ← programSourceOutput 1
  let flowSeed := run1StartFromArrival arrival
  let symbolic ← forwardRead (start flowSeed)
  if requestsT symbolic then
    let initial := run1RequestedT flowSeed
    let output ← forwardRead (start initial)
    let target ← possibleSink (.data initial.initial) output
    if target.kind = .demandTarget then pure ⟨iface true 5 (-2),target.original⟩ else none
  else none

def b2Rows : List DemandRow :=
  [run1SourceData 1,run1SourceData 5,run1Flow].filterMap (fun row => row.map projectData) ++
  [run1SourceTarget,run1MarkedTarget].filterMap (fun row => row.map projectTarget)

def findRow (rows : List DemandRow) (test : DemandRow → Bool) : Option DemandRow := rows.find? test

def concreteZeroRow (mode : Mode) (rows : List DemandRow) (head : List Nat) (output : Int) : Option DemandRow :=
  findRow rows fun row => decide (row.interface = iface (isForward mode) 5 output ∧
    row.entry = .data (encode (p head .any T)) ∧ row.exit = .zero)

def b2FlowStep : Option Publication := do
  let terminal ← run1SourceTarget
  let _ ← if controlAdmission false .exceptional (iface false 11 5) [projectTarget terminal] then some () else none
  let target := ⟨terminal.original,.demandTarget⟩
  let seed ← sinkSeed target
  let offered := backwardReadAt 1 seed
  let permission ← findRow b2Rows fun row => decide (row.interface = iface false 5 5 ∧
    row.entry = .data (encode (p [] .any .flow)) ∧ row.exit = .data (encode (p [] .star .flow)))
  let initial ← admitFrom modeB2 permission offered
  let output := backwardReadAt 1 (start initial)
  publish modeB2 .normal (iface false 5 5) (.data initial.initial) (.data output) permission

def b2NormalZero (entry : Int) (role : Role) : Option Publication := do
  let target0 ← run1SourceTarget
  let targetT ← run1MarkedTarget
  if controlAdmission false role (iface false entry 5) [projectTarget target0,projectTarget targetT] then
    let seed ← sinkSeed ⟨target0.original,.demandTarget⟩
    let value := backwardReadAt 1 seed
    publish modeB2 role (iface false entry 5) .zero (.data value) (projectTarget targetT)
  else none

def b2ConcreteSource (output : Int) : Option Publication := do
  let symbolic ← b2FlowStep
  let target ← run1SourceTarget
  let seed ← sinkSeed ⟨target.original,.demandTarget⟩
  let offered ← applyFlow symbolic (backwardReadAt 1 seed)
  let permission ← concreteZeroRow modeB2 b2Rows [] output
  let initial ← admitFrom modeB2 permission offered
  let atSource := backwardReadAt 1 (start initial)
  let zero ← sourceReach atSource
  publish modeB2 .normal (iface false 5 output) (.data initial.initial) (.reach zero) permission

def b2SourceTarget : Option Terminal := do
  let source ← b2ConcreteSource 5
  if targetPermission modeB2 .normal (iface false 5 (-1)) source.original b2Rows then
    pure ⟨iface false 5 (-1),source.original⟩ else none

def b3Rows : List DemandRow :=
  ([b2ConcreteSource 1,b2ConcreteSource 5,b2NormalZero 11 .exceptional,b2NormalZero 5 .normal]).filterMap
    (fun row => row.map projectData) ++
  [b2SourceTarget].filterMap (fun row => row.map projectTarget)

/- Reversal of the produced NORMAL backward ZERO -> xf.EXACT row. Its
native opposite match on xf.MAY/T,D creates Reach.D; it is not a source hit. -/
def savedZeroReverse (normal : Publication) (input : Actual) : Option Layer :=
  match normal.original,normal.result with
  | .zero,.data value =>
    if normal.interface = iface false 5 5 ∧ value.layer = .normal then
      readToZero value.pattern input else none
  | _,_ => none

def targetMatches (initial : Pattern) (input : Actual) : Bool := (readToZero initial input).isSome

def rootTerminal (forward : Bool) : Terminal :=
  ⟨⟨17,forward,0,normalControlEntry forward,terminalExit forward⟩,.zero⟩

/- Root collection is modeled as nearest-boundary ZERO transport. Its
native dispatcher/store equivalence remains an explicit adapter obligation. -/
def f1RootTarget : Option Terminal := do
  let child ← run1SourceTarget
  if isZeroOriginal child.original then pure (rootTerminal true) else none

def b2RootTarget : Option Terminal := do
  let previous ← f1RootTarget
  let child ← b2SourceTarget
  let flow ← b2FlowStep
  let sinkTarget ← run1SourceTarget
  let seed ← sinkSeed ⟨sinkTarget.original,.demandTarget⟩
  let input ← applyFlow flow (backwardReadAt 1 seed)
  match child.original with
  | .zero => none
  | .data initial => if targetMatches initial input &&
      targetPermission modeB2 .normal (rootTerminal false).interface .zero [projectTarget previous]
      then pure (rootTerminal false) else none

def sourcePermission : Bool := (b2ConcreteSource 5).isSome

def f3FirstSourceData : Option Publication := do
  if (b2RootTarget.isSome && sourcePermission) && controlAdmission true .normal (iface true 1 5) b3Rows then
    let incoming ← programSourceOutput 2
    let permission ← findRow b3Rows fun row => decide (row.interface = iface true 1 5 ∧
      row.entry = .zero ∧ row.exit = .data (encode (p [f] .star T)))
    publish modeF3 .normal (iface true 1 5) .zero (.data incoming) permission
  else none

def f3RepeatSourceData : Option Publication := do
  let first ← f3FirstSourceData
  let arrived ← match first.result with | .data value => some value | _ => none
  let zeroRecord ← b2NormalZero 5 .normal
  let _ ← savedZeroReverse zeroRecord arrived
  if sourcePermission && controlAdmission true .normal (iface true 5 5) b3Rows then
    let incoming ← programSourceOutput 2
    let permission ← findRow b3Rows fun row => decide (row.interface = iface true 5 5 ∧
      row.entry = .zero ∧ row.exit = .data (encode (p [f] .star T)))
    publish modeF3 .normal (iface true 5 5) .zero (.data incoming) permission
  else none

def f3SourceData (entry : Int) : Option Publication :=
  if entry = 1 then f3FirstSourceData else if entry = 5 then f3RepeatSourceData else none

def f3PreciseTerminal : Option Terminal := do
  let source ← f3SourceData 5
  let incoming ← match source.result with | .data value => some value | _ => none
  let permission ← findRow b3Rows fun row => decide (row.interface = iface true 5 5 ∧
    row.entry = .data (encode (p [f] .exact T)) ∧ row.exit = .zero)
  let initial ← admitFrom modeF3 permission incoming
  let output ← forwardRead (start initial)
  let target ← possibleSink (.data initial.initial) output
  if target.kind = .demandTarget && targetPermission modeF3 .normal (iface true 5 (-2)) target.original b3Rows
    then pure ⟨iface true 5 (-2),target.original⟩ else none

def f3RootTarget : Option Terminal := do
  let previous ← b2RootTarget
  let child ← f3PreciseTerminal
  let source ← f3SourceData 5
  let input ← match source.result with | .data value => some value | _ => none
  match child.original with
  | .zero => none
  | .data initial => if targetMatches initial input &&
      targetPermission modeF3 .normal (rootTerminal true).interface .zero [projectTarget previous]
      then pure (rootTerminal true) else none

def f3NormalShrinker : Option Publication := do
  let source ← f3SourceData 5
  let input ← match source.result with | .data value => some value | _ => none
  let permission ← findRow (FlowDemandCompletion.completed b3Rows) fun row =>
    decide (row.interface = iface true 5 5 ∧
      row.entry = .data (encode (p [f] .any .flow)) ∧
      row.exit = .data (encode (p [f] .any .flow)))
  let initial ← admitFrom modeF3 permission input
  let output ← forwardRead (start initial)
  publish modeF3 .normal (iface true 5 5) (.data initial.initial) (.data output) permission

def b4Rows : List DemandRow :=
  [f3SourceData 1,f3SourceData 5].filterMap (fun row => row.map projectData) ++
  [f3PreciseTerminal].filterMap (fun row => row.map projectTarget)

def b4NormalZero : Option Publication := do
  let target ← f3PreciseTerminal
  if f3RootTarget.isSome && controlAdmission false .exceptional (iface false 11 5) [projectTarget target] then
    let seed ← sinkSeed ⟨target.original,.demandTarget⟩
    publish modeB4 .exceptional (iface false 11 5) .zero (.data (backwardReadAt 3 seed))
      (projectTarget target)
  else none

/- The F3 ordinary read relation is derived in DeepFlowCompletion. Its
opposite NORMAL STAR view grows the actual suffix in B4. -/
def growByDerivedNormal (input : Actual) : Option Actual := do
  let row ← f3NormalShrinker
  match row.original,row.result with
  | .data initial,.data output =>
      let reversed : SavedRead := ⟨DeepFlowCompletion.repeatPort5,output.pattern,
        ⟨initial,output.layer,false⟩⟩
      applySaved reversed input
  | _,_ => none

def b4GrowingOffer : Option Actual := do
  let target ← f3PreciseTerminal
  let seed ← sinkSeed ⟨target.original,.demandTarget⟩
  let first := backwardReadAt 3 seed
  let second ← growByDerivedNormal first
  growByDerivedNormal second

def b4SourceFrom (input : Actual) (output : Int) : Option Publication := do
  let permission ← concreteZeroRow modeB4 b4Rows [f] output
  let initial ← admitFrom modeB4 permission input
  let atSource := backwardReadAt 3 (start initial)
  let zero ← sourceReach atSource
  publish modeB4 .normal (iface false 5 output) (.data initial.initial) (.reach zero) permission

def b4ConcreteSource (output : Int) : Option Publication :=
  b4GrowingOffer.bind fun raw => b4SourceFrom raw output

def b4SourceTarget : Option Terminal := do
  let row ← b4ConcreteSource 5
  if targetPermission modeB4 .normal (iface false 5 (-1)) row.original b4Rows then
    pure ⟨iface false 5 (-1),row.original⟩ else none

def necessaryF5Rows : Option (List DemandRow) := do
  let exact ← b4NormalZero
  let data ← b4ConcreteSource 5
  let target ← b4SourceTarget
  pure [projectData exact,projectData data,projectTarget target]

theorem F1_source_produces_actual_MAY_before_block_abstraction :
    programSourceOutput 1 = some (actual [] .any .demand) := by decide

theorem F1_FLOW_hypothesis_is_derived_from_that_actual_arrival :
    run1Flow = some ⟨iface true 5 5,.data (p [] .star .flow),.data (actual [] .any .demand .flow)⟩ := by decide

theorem F1_sink_requests_T_from_real_FLOW_MAY : requestsT (actual [] .any .demand .flow) = true := rfl

theorem F1_requested_concrete_STAR_identity_is_DEMAND :
    run1RequestedT ⟨p [] .star .flow,.normal⟩ = ⟨p [] .star T,.demand⟩ := rfl

theorem F1_marked_Target_is_generated_without_a_method_local_default :
    run1MarkedTarget = some ⟨iface true 5 (-2),.data (p [] .star T)⟩ := by decide

theorem B2_real_normal_control_and_FLOW_pairs_are_generated :
    (projectData ⟨iface true 5 5,.zero,.data (actual [] .any .demand)⟩ ∈ b2Rows) ∧
    (projectData ⟨iface true 5 5,.data (p [] .star .flow),.data (actual [] .any .demand .flow)⟩ ∈ b2Rows) := by decide

theorem B2_FLOW_body_and_paired_C5_generate_MAY_result :
    b2FlowStep = some ⟨iface false 5 5,.data (p [f] .star .flow),.data (actual [f] .any .demand .flow)⟩ := by decide

theorem B2_normal_ZERO_sink_seed_keeps_exact_T_at_real_discovery_port :
    b2NormalZero 11 .exceptional = some ⟨iface false 11 5,.zero,.data (actual [f] .exact .normal)⟩ := by decide

theorem B2_normal_ZERO_feedback_seed_keeps_exact_T_at_repeat_port :
    b2NormalZero 5 .normal = some ⟨iface false 5 5,.zero,.data (actual [f] .exact .normal)⟩ := by decide

theorem B2_FLOW_result_drives_concrete_STAR_source_hit :
    b2ConcreteSource 5 = some ⟨iface false 5 5,.data (p [f] .star T),.reach .demand⟩ := by decide

theorem B2_source_hook_has_real_feedback_Target_permission :
    b2SourceTarget = some ⟨iface false 5 (-1),.data (p [f] .star T)⟩ := by decide

theorem B3_ZERO_STAR_and_precise_control_rows_arrive_with_original_ports :
    (⟨iface true 5 5,.zero,.data (encode (p [f] .star T))⟩ ∈ b3Rows) ∧
    (⟨iface true 5 5,.data (encode (p [f] .exact T)),.zero⟩ ∈ b3Rows) ∧
    (⟨iface true 5 11,.data (encode (p [f] .exact T)),.zero⟩ ∈ b3Rows) := by decide

theorem root_Target_chain_uses_previous_scoped_ZERO_permission :
    f1RootTarget = some (rootTerminal true) ∧
    b2RootTarget = some (rootTerminal false) ∧
    f3RootTarget = some (rootTerminal true) := by decide

theorem F3_saved_normal_ZERO_reverse_replay_keeps_DEMAND :
    savedZeroReverse ⟨iface false 5 5,.zero,.data (actual [f] .exact .normal)⟩
      (actual [f] .any .demand) = some .demand := by decide

theorem F3_source_MAY_is_published_in_actual_repeat_scope :
    f3SourceData 5 = some ⟨iface true 5 5,.zero,.data (actual [f] .any .demand)⟩ := by decide

theorem F3_exact_Target_original_and_permission_are_generated :
    f3PreciseTerminal = some ⟨iface true 5 (-2),.data (p [f] .exact T)⟩ := by decide

theorem B4_ANY_zero_and_exact_Target_handoff_are_computed :
    (⟨iface false 5 5,.data (encode (p [f] .any T)),.zero⟩ ∈ b4Rows) ∧
    (⟨iface false (-2) 5,.target,.data (encode (p [f] .exact T))⟩ ∈ b4Rows) := by decide

theorem actual_B4_global_limit_is_three : modeB4.limit = 3 := rfl

theorem B4_borrowed_exact_Target_accepts_real_ZERO_data_without_widening :
    b4NormalZero = some ⟨iface false 11 5,.zero,.data (actual [f] .exact .normal)⟩ := by decide

theorem B4_opposite_NORMAL_read_derives_growing_exact_actual :
    b4GrowingOffer = some (actual [f,f,f] .exact .normal) := by decide

theorem F3_NORMAL_shrinker_is_derived_from_the_generated_frontier :
    f3NormalShrinker = some ⟨iface true 5 5,.data (p [f] .star .flow),
      .data (actual [] .star .normal .flow)⟩ := by decide

def b4CompletedRows : List DemandRow := FlowDemandCompletion.completed b4Rows
def b4View : ViewScope := viewOf (iface false 5 5)
def b4Query (input : Actual) : List Key := query modeB4 b4View b4CompletedRows input
def b4Needed : Key := ⟨b4View,⟨p [f,f] .star T,.demand⟩⟩

theorem B4_whole_generated_query_has_the_needed_concrete_key :
    b4Needed ∈ b4Query (actual [f,f,f] .exact .normal) := by decide

theorem B4_depth_one_cut_loses_that_key_in_the_whole_query :
    b4Needed ∉ b4Query (cutAt 1 (actual [f,f,f] .exact .normal)) := by decide

theorem B4_depth_two_cut_preserves_that_key_in_the_whole_query :
    b4Needed ∈ b4Query (cutAt 2 (actual [f,f,f] .exact .normal)) := by decide

theorem B4_raw_and_any_possible_depth_two_trial_have_same_source_effect :
    b4SourceFrom (actual [f,f,f] .exact .normal) 5 =
      some ⟨iface false 5 5,.data (p [f,f] .star T),.reach .demand⟩ ∧
    b4SourceFrom (cutAt 2 (actual [f,f,f] .exact .normal)) 5 =
      some ⟨iface false 5 5,.data (p [f,f] .star T),.reach .demand⟩ := by decide

theorem B4_current_plain_STAR_actor_executes_physical_source :
    b4ConcreteSource 5 = some ⟨iface false 5 5,.data (p [f,f] .star T),.reach .demand⟩ := by decide

theorem B4_Target_permission_uses_complete_physical_ZERO_exit_pair :
    b4SourceTarget = some ⟨iface false 5 (-1),.data (p [f,f] .star T)⟩ := by decide

theorem actual_F5_required_three_rows_are_produced_not_supplied :
    necessaryF5Rows = some [DeepFlowCompletion.finalData,DeepFlowCompletion.finalZero,DeepFlowCompletion.finalTarget] := by decide

theorem source_reach_of_MAY_and_plain_STAR_is_a_real_AP_operation :
    sourceReach (actual [f] .any .demand) = some .demand ∧
    sourceReach (actual [f,f,f] .star .demand) = some .demand := by decide

theorem Source_FLOW_hypothesis_does_not_invent_Reach_or_Target :
    sourceReach (actual [f,f,f] .star .normal .flow) = none := by decide

theorem concrete_Target_cannot_be_admitted_by_FLOW_completion :
    entryAccepts modeB4 (.data (encode (p [f] .any .flow))) (.data (p [f,f] .star T)) = false := by decide

theorem borrowed_CONTROL_does_not_alias_nonzero_DATA_admission :
    borrowNormal false .exceptional (.data (p [f] .exact T)) = false := rfl

theorem precise_Target_row_is_never_replaced_by_MAY :
    (projectTarget ⟨iface true 5 (-2),.data (p [f] .exact T)⟩).exit =
      .data (encode (p [f] .exact T)) := rfl

#print axioms DeepGuidanceArrival.forward_graph_has_no_normal_or_exceptional_leave
#print axioms DeepGuidanceArrival.discovery_reaches_the_real_sink_without_a_forward_edge
#print axioms DeepGuidanceArrival.F1_source_produces_actual_MAY_before_block_abstraction
#print axioms DeepGuidanceArrival.F1_FLOW_hypothesis_is_derived_from_that_actual_arrival
#print axioms DeepGuidanceArrival.F1_sink_requests_T_from_real_FLOW_MAY
#print axioms DeepGuidanceArrival.F1_requested_concrete_STAR_identity_is_DEMAND
#print axioms DeepGuidanceArrival.F1_marked_Target_is_generated_without_a_method_local_default
#print axioms DeepGuidanceArrival.B2_real_normal_control_and_FLOW_pairs_are_generated
#print axioms DeepGuidanceArrival.B2_FLOW_body_and_paired_C5_generate_MAY_result
#print axioms DeepGuidanceArrival.B2_normal_ZERO_sink_seed_keeps_exact_T_at_real_discovery_port
#print axioms DeepGuidanceArrival.B2_normal_ZERO_feedback_seed_keeps_exact_T_at_repeat_port
#print axioms DeepGuidanceArrival.B2_FLOW_result_drives_concrete_STAR_source_hit
#print axioms DeepGuidanceArrival.B2_source_hook_has_real_feedback_Target_permission
#print axioms DeepGuidanceArrival.B3_ZERO_STAR_and_precise_control_rows_arrive_with_original_ports
#print axioms DeepGuidanceArrival.root_Target_chain_uses_previous_scoped_ZERO_permission
#print axioms DeepGuidanceArrival.F3_saved_normal_ZERO_reverse_replay_keeps_DEMAND
#print axioms DeepGuidanceArrival.F3_source_MAY_is_published_in_actual_repeat_scope
#print axioms DeepGuidanceArrival.F3_exact_Target_original_and_permission_are_generated
#print axioms DeepGuidanceArrival.B4_ANY_zero_and_exact_Target_handoff_are_computed
#print axioms DeepGuidanceArrival.actual_B4_global_limit_is_three
#print axioms DeepGuidanceArrival.B4_borrowed_exact_Target_accepts_real_ZERO_data_without_widening
#print axioms DeepGuidanceArrival.B4_opposite_NORMAL_read_derives_growing_exact_actual
#print axioms DeepGuidanceArrival.F3_NORMAL_shrinker_is_derived_from_the_generated_frontier
#print axioms DeepGuidanceArrival.B4_whole_generated_query_has_the_needed_concrete_key
#print axioms DeepGuidanceArrival.B4_depth_one_cut_loses_that_key_in_the_whole_query
#print axioms DeepGuidanceArrival.B4_depth_two_cut_preserves_that_key_in_the_whole_query
#print axioms DeepGuidanceArrival.B4_raw_and_any_possible_depth_two_trial_have_same_source_effect
#print axioms DeepGuidanceArrival.B4_current_plain_STAR_actor_executes_physical_source
#print axioms DeepGuidanceArrival.B4_Target_permission_uses_complete_physical_ZERO_exit_pair
#print axioms DeepGuidanceArrival.actual_F5_required_three_rows_are_produced_not_supplied
#print axioms DeepGuidanceArrival.source_reach_of_MAY_and_plain_STAR_is_a_real_AP_operation
#print axioms DeepGuidanceArrival.Source_FLOW_hypothesis_does_not_invent_Reach_or_Target
#print axioms DeepGuidanceArrival.concrete_Target_cannot_be_admitted_by_FLOW_completion
#print axioms DeepGuidanceArrival.borrowed_CONTROL_does_not_alias_nonzero_DATA_admission
#print axioms DeepGuidanceArrival.precise_Target_row_is_never_replaced_by_MAY

end DeepGuidanceArrival

import RelativeAdmission
import AnnotatedC5Exit
import FlowDemandCompletion

/-!
PREPARED ONLY. E20 finite operational witness at actual physical interfaces.
The no-write B2 header path is 10 -> 4; repeat 4 -> 4 executes write node 3.
The actual fixture is a weak static write: its reversed statement also has a
derived STATIC frame. A separate explicitly strong-touched variant removes
that frame. Do not claim the actual weak repeat cannot have NORMAL identity.
The FLOW record below is computed by C2, the ordinary header transfer and full
paired C5. It is not a structural identity default. Source permission uses a
separate marked reverse source occurrence at node 2. Native layout/actor and
static codec correspondences are source-bound adapters, not proved here.
-/
namespace TwoLoopHeaderFlow
open PlainStarRelativeAdmission
set_option maxRecDepth 4096
set_option maxHeartbeats 8000000

abbrev FC := FlowDemandCompletion.Pattern
abbrev FRow := FlowDemandCompletion.Row
abbrev FInterface := FlowDemandCompletion.Interface

/- Actual fixture CFG. Ports are enumerated by increasing physical source. -/
def successors : List (List Nat) := [[1],[2,4],[3],[1],[5,7],[6],[4],[8],[],[]]
def physicalEdges : List (Nat × Nat) :=
  (successors.zipIdx).flatMap fun item => item.1.map fun target => (item.2,target)

theorem actual_CFG_ports_and_feedback :
    physicalEdges.length = 10 ∧ physicalEdges[2]? = some (1,4) ∧
    physicalEdges[4]? = some (3,1) ∧ physicalEdges[8]? = some (6,4) := by decide

def logicalL1NormalExit : Int := 10
def L1Repeat : Int := 4
def nativeLeafOwners : List (Nat × List Nat) :=
  [(1,[0]),(2,[1,2,3]),(4,[]),(5,[4,5,6]),(6,[7,8,9])]
structure LogicalExit where
  id : Int
  loop : Nat
  target : Nat
  physicalRoutes : List Nat
  deriving DecidableEq, Repr
def L1Normal : LogicalExit := ⟨10,2,4,[2]⟩
def L2Normal : LogicalExit := ⟨11,5,7,[6]⟩
theorem logical_exit10_uses_existing_leave_edge_not_a_new_CFG_edge :
    L1Normal.physicalRoutes = [2] ∧ physicalEdges[2]? = some (1,L1Normal.target) ∧
    physicalEdges[10]? = none ∧ L1Normal.loop = 2 := by decide
theorem loop1_and_loop2_own_different_write_and_sink_nodes :
    nativeLeafOwners[1]? = some (2,[1,2,3]) ∧
    nativeLeafOwners[3]? = some (5,[4,5,6]) := by decide
def headerBackward : List Nat := [1]
def repeatBackward : List Nat := [3,2,1]
def headerForward : List Nat := [1]

theorem zero_iteration_header_does_not_execute_the_write :
    headerBackward = [1] ∧ 3 ∉ headerBackward ∧ 2 ∉ headerBackward ∧
    repeatBackward = [3,2,1] ∧ 3 ∈ repeatBackward := by decide

def b2Header : FInterface := ⟨201,false,2,10,4⟩
def b2Repeat : FInterface := ⟨201,false,2,4,4⟩
def f3Adjacent : FInterface := ⟨201,true,2,4,10⟩
def f3Repeat : FInterface := ⟨201,true,2,4,4⟩
def f3AL1 : FInterface := ⟨201,true,3,10,-2⟩
def f3Getter : FInterface := ⟨202,true,0,-1,-2⟩

def opposite (interface : FInterface) : FInterface :=
  ⟨interface.methodContext,!interface.direction,interface.scope,
    interface.outputPort,interface.entryPort⟩

theorem physical_record_reversal_is_adjacent_not_repeat :
    opposite b2Header = f3Adjacent ∧ opposite b2Header ≠ f3Repeat ∧
    opposite b2Repeat = f3Repeat := by decide

/- Class Box is the zero-counted class anchor 1; shared is field 4; g is field 0.
In the ordinary-path C2 model, class identity is encoded in the DATA base.
Field n maps to n+1; therefore F=[5], F.g=[5,1] and local g=[1]. -/
def F (tail : FlowDemandCompletion.Tail) (mark : FlowDemandCompletion.Mark := .full 1) : FC :=
  ⟨.staticRoot,[.classId 1,.field 4],tail,mark,[]⟩
def FG : FC := ⟨.staticRoot,[.classId 1,.field 4,.field 0],.exact,.full 1,[]⟩

def encodePath : FlowDemandCompletion.Path → List Nat
  | [] => []
  | .classId _ :: rest => encodePath rest
  | .field field :: rest => (field + 1) :: encodePath rest
  | .element :: rest => 0 :: encodePath rest
def encodeBase (pattern : FC) : Nat :=
  match pattern.base,pattern.path with
  | .local id,_ => 2 * id
  | .staticRoot,.classId owner :: _ => 2 * owner + 1
  | .staticRoot,_ => 1
def encodeTail : FlowDemandCompletion.Tail → Tail
  | .exact => .exact | .star => .star | .may => .any | .must => .must
def encodePattern (pattern : FC) : Option Pattern :=
  if FlowDemandCompletion.legalHead pattern.base pattern.path then
    match pattern.mark with
    | .group _ => none
    | .flow => some ⟨encodeBase pattern,encodePath pattern.path,encodeTail pattern.tail,.flow,
        encodePath pattern.exclusion⟩
    | .full mark => some ⟨encodeBase pattern,encodePath pattern.path,encodeTail pattern.tail,.full mark,
        encodePath pattern.exclusion⟩
  else none
def demandOf (pattern : Pattern) : Demand :=
  ⟨pattern.base,pattern.path,
    (match pattern.tail with | .exact => .exact | .star => .star | .any | .must => .any),
    pattern.mark,pattern.exclusion⟩
structure Pair where
  entry : Demand
  exit : Pattern
  deriving DecidableEq, Repr
def encodePair (row : FRow) : Option Pair := do
  match row.entry,row.exit with
  | .data left,.data right =>
      let input ← encodePattern left
      let output ← encodePattern right
      pure ⟨demandOf input,output⟩
  | _,_ => none

theorem class_anchor_counts_zero_and_leaf_counts_one :
    (encodePath (F .may).path).length = 1 ∧ (encodePath FG.path).length = 2 ∧
    RelativeRestriction.depth (F .may).path = 1 ∧ RelativeRestriction.depth FG.path = 2 := by decide

def toCTail : Tail → AnnotatedC5Exit.Tail
  | .exact => .exact | .star => .star | .any => .may | .must => .must
def fromCTail : AnnotatedC5Exit.Tail → Tail
  | .exact => .exact | .star => .star | .may => .any | .must => .must
def toCLayer : Layer → AnnotatedC5Exit.Layer
  | .normal => .normal | .demand => .demand
def fromCLayer : AnnotatedC5Exit.Layer → Layer
  | .normal => .normal | .demand => .demand
def toCSlot : RestrictedInitialPolicy.Mark → AnnotatedC5Exit.Slot
  | .flow => .flow [] | .full mark => .full mark
def toC (pattern : Pattern) : AnnotatedC5Exit.Pattern :=
  ⟨pattern.base,pattern.path.map RelativeRestriction.Accessor.field,toCTail pattern.tail,
    toCSlot pattern.mark,pattern.exclusion.map RelativeRestriction.Accessor.field⟩
def toCFact (actual : Actual) : AnnotatedC5Exit.Fact :=
  ⟨toC actual.pattern,toCLayer actual.layer,actual.hasProtection⟩
def fromCPath : RelativeRestriction.Path → List Nat
  | [] => [] | .field field :: rest => field :: fromCPath rest
  | .classId _ :: rest => fromCPath rest | .element :: rest => 0 :: fromCPath rest
def fromCFact (actual : AnnotatedC5Exit.Fact) : Actual :=
  ⟨⟨actual.base,fromCPath actual.path,fromCTail actual.tail,
    (match actual.slot with | .flow _ => .flow | .full mark => .full mark),
    fromCPath actual.exclusion⟩,fromCLayer actual.layer,actual.h⟩

structure Inferred where
  interface : FInterface
  initial : Pattern
  output : Actual
  deriving DecidableEq, Repr

/-- Real C2 and full annotated C5; only the finite ordinary body is supplied. -/
def infer (mode : Mode) (row : FRow) (incoming : Actual)
    (body : Actual → Option Actual) : Option Inferred := do
  let pair ← encodePair row
  let seed ← emit mode pair.entry incoming
  let raw ← body (start seed)
  if rawImage mode pair.entry seed.initial then
    let accepted ← AnnotatedC5Exit.restrictData (decide (mode.direction = .forward))
      mode.limit (toCFact raw) (toC pair.exit)
    pure ⟨row.interface,seed.initial,fromCFact accepted⟩
  else none

def b2 : Mode := ⟨2,1,.backward⟩
def f3 : Mode := ⟨3,2,.forward⟩
def FStar : Pattern := ⟨3,[5],.star,.flow,[]⟩
def FGTaint : Actual := ⟨⟨3,[5,1],.exact,.full 1,[]⟩,.normal,false⟩
def coarseF : Actual := ⟨⟨3,[5],.any,.full 1,[]⟩,.demand,false⟩

def headerFLOWRows : List FRow := FlowDemandCompletion.virtualStaticCarry true b2Header (F .may)
def repeatFLOWRows : List FRow := FlowDemandCompletion.virtualStaticCarry true b2Repeat (F .may)

theorem run2_FLOW_permission_is_query_local_and_complete :
    headerFLOWRows = [FlowDemandCompletion.selfPair b2Header (F .may) (F .may).path] := by decide

def reverseWriteShared (input : Actual) : Option Actual :=
  if input.pattern.base = 3 then
    match ApSpec.dropPrefix [5] input.pattern.path with
    | none => none
    | some suffix => some {input with pattern := {input.pattern with base := 0,path := suffix}}
  else some input

/-- Projection of the physical SOURCE at node2: matching full T records the
source occurrence; ordinary residual data cannot turn local a back into F. -/
def sourceHit2 (input : Actual) : Bool :=
  decide (input.pattern.base = 0 ∧ input.pattern.mark = .full 1) &&
    match ApSpec.dropPrefix input.pattern.path [1] with
    | none => false
    | some suffix => tailAdmits input.pattern.tail input.pattern.exclusion suffix

structure TraceState where
  data : Option Actual
  sourceHits : List Nat
  deriving DecidableEq, Repr
def backwardInstruction (node : Nat) (state : TraceState) : TraceState :=
  match node,state.data with
  | 3,some input => {state with data := reverseWriteShared input}
  | 2,some input =>
      if sourceHit2 input then {data := none,sourceHits := state.sourceHits ++ [2]}
      else state
  | _,_ => state
def executeBackward (path : List Nat) (input : Actual) : TraceState :=
  path.foldl (fun state node => backwardInstruction node state) ⟨some input,[]⟩
def headerBody (input : Actual) : Option Actual := (executeBackward headerBackward input).data
def strongRepeatBody (input : Actual) : Option Actual := (executeBackward repeatBackward input).data

/- The fixture summary's touched bases are ZERO and a, while targets include
STATIC. StatementSummary.reversed adds passOverBases(targets,touched). The
metadata code 99 denotes ZERO; no DATA/initial is seeded at that base. -/
def actualTouched : List Nat := [99,0]
def actualTargets : List Nat := [99,0,3]
def passOverBases (targets touched : List Nat) : List Nat :=
  targets.filter (fun base => !(touched.contains base))
def weakFrames : List Nat := passOverBases actualTargets actualTouched
def strongFrames : List Nat := passOverBases actualTargets (actualTouched ++ [3])
def actualFrameInstruction (frames : List Nat) (node : Nat) (input : Actual) : Option Actual :=
  match node with
  | 3 => if frames.contains input.pattern.base then some input else none
  | 2 => if input.pattern.base ≠ 0 then some input else none
  | _ => some input
def framePath (frames : List Nat) (path : List Nat) (input : Actual) : Option Actual :=
  path.foldl (fun current node => current.bind (actualFrameInstruction frames node)) (some input)
def repeatBody (input : Actual) : Option Actual := framePath weakFrames repeatBackward input
def inferredHeader : Option Inferred :=
  (headerFLOWRows.filterMap (fun row => infer b2 row coarseF headerBody)).head?
def expectedHeader : Inferred := ⟨b2Header,FStar,⟨FStar,.normal,false⟩⟩

theorem B2_HEADER_NORMAL_identity_is_inferred_from_header_transfer :
    inferredHeader = some expectedHeader := by decide
theorem B2_HEADER_does_not_grant_a_source_permission :
    executeBackward headerBackward ⟨FStar,.normal,false⟩ = ⟨some ⟨FStar,.normal,false⟩,[]⟩ := by decide
theorem B2_REPEAT_write_redirects_static_to_local_a :
    reverseWriteShared ⟨FStar,.normal,false⟩ =
      some ⟨⟨0,[],.star,.flow,[]⟩,.normal,false⟩ := by decide
theorem actual_fixture_weak_frame_is_derived_not_invented :
    weakFrames = [3] ∧ strongFrames = [] := by decide
theorem actual_weak_REPEAT_can_infer_its_separate_NORMAL_identity :
    repeatFLOWRows.filterMap (fun row => infer b2 row coarseF repeatBody) =
      [⟨b2Repeat,FStar,⟨FStar,.normal,false⟩⟩] := by decide
theorem explicit_strong_touched_REPEAT_has_no_static_NORMAL_identity :
    repeatFLOWRows.filterMap (fun row => infer b2 row coarseF strongRepeatBody) = [] ∧
      framePath strongFrames repeatBackward ⟨FStar,.normal,false⟩ = none := by decide

def markedCarry : Demand := ⟨3,[5],.any,.full 1,[]⟩
def markedSeed : Option Seed := emit b2 markedCarry coarseF
def markedReverseSource : TraceState :=
  match markedSeed with
  | none => ⟨none,[]⟩
  | some seed => executeBackward repeatBackward (start seed)
def sourcePermission : Bool := markedReverseSource.sourceHits.contains 2

theorem source_permission_comes_from_real_reverse_write_and_source2 :
    markedSeed = some ⟨⟨3,[5],.star,.full 1,[]⟩,.demand⟩ ∧
    markedReverseSource = ⟨none,[2]⟩ ∧ sourcePermission = true := by decide

def applySaved (row : Inferred) (input : Actual) : Option Actual :=
  if row.initial.base = input.pattern.base ∧ row.initial.tail = .star ∧
      row.output.pattern.tail = .star ∧
      RestrictedInitialPolicy.acceptsMark row.initial.mark input.pattern.mark = true then
    match ApSpec.dropPrefix row.initial.path input.pattern.path with
    | none => none
    | some suffix =>
      if tailAdmits .star row.initial.exclusion suffix &&
          tailAdmits .star row.output.pattern.exclusion suffix then
        some ⟨⟨row.output.pattern.base,row.output.pattern.path ++ suffix,
          input.pattern.tail,input.pattern.mark,input.pattern.exclusion⟩,
          joinLayer row.output.layer input.layer,input.hasProtection || row.output.hasProtection⟩
      else none
  else none
def replayAt (requested : FInterface) (row : Inferred) (input : Actual) : Option Actual :=
  if requested = opposite row.interface then applySaved row input else none

theorem saved_opposite_header_replays_FG_to_adjacent_exit10 :
    inferredHeader.bind (fun row => replayAt f3Adjacent row FGTaint) = some FGTaint := by decide
theorem header_record_is_not_a_repeat4_to4_record :
    inferredHeader.bind (fun row => replayAt f3Repeat row FGTaint) = none := by decide

def preciseConcreteGate : Option Seed :=
  emit f3 ⟨3,[5],.star,.full 1,[]⟩ FGTaint
theorem old_precise_concrete_STAR_gate_still_rejects_FG : preciseConcreteGate = none := by decide

def deliverSavedFirst (requested : FInterface) (input : Actual)
    (currentBody : Seed → List Actual) : List Actual :=
  let saved := match inferredHeader.bind (fun row => replayAt requested row input) with
    | some output => [output] | none => []
  let current := emit f3 ⟨3,[5],.star,.full 1,[]⟩ input
  saved ++ match current with | none => [] | some seed => currentBody seed
theorem replay_result_survives_the_empty_original_T_initial_gate
    (currentBody : Seed → List Actual) :
    preciseConcreteGate = none ∧ deliverSavedFirst f3Adjacent FGTaint currentBody = [FGTaint] := by
  constructor
  · exact old_precise_concrete_STAR_gate_still_rejects_FG
  · have noCurrent : emit f3 ⟨3,[5],.star,.full 1,[]⟩ FGTaint = none :=
      old_precise_concrete_STAR_gate_still_rejects_FG
    simp only [deliverSavedFirst,saved_opposite_header_replays_FG_to_adjacent_exit10,noCurrent,List.append_nil]

/- The AL1 T entry comes from captured B2 ZERO -> F.ANY at block3 exit10.
It is not borrowed from L1's T.STAR identity. -/
def adjacentConcreteEntry : Demand := ⟨3,[5],.any,.full 1,[]⟩
theorem AL1_actual_precise_T_starts_NORMAL :
    emit f3 adjacentConcreteEntry FGTaint =
      some ⟨⟨3,[5,1],.exact,.full 1,[]⟩,.normal⟩ := by decide

def retG : FC := ⟨.local 10,[.field 0],.star,.flow,[]⟩
def getterIncoming : FRow := ⟨f3Getter,.data (F .may .flow),.data retG⟩
def getterRows : List FRow := FlowDemandCompletion.completed [getterIncoming]
def ordinaryGetterRead (input : Actual) : Option Actual :=
  if input.pattern.base = 3 then
    match ApSpec.dropPrefix [5] input.pattern.path with
    | none => none
    | some suffix => some {input with pattern := {input.pattern with base := 20,path := suffix}}
  else none
def inferredGetter : Option Inferred :=
  (getterRows.filterMap (fun row => infer f3 row FGTaint ordinaryGetterRead)).find?
    (fun row => decide (row.initial.mark = .flow ∧ row.output.layer = .normal))
def expectedGetter : Inferred :=
  ⟨f3Getter,⟨3,[5,1],.star,.flow,[]⟩,⟨⟨20,[1],.star,.flow,[]⟩,.normal,false⟩⟩

theorem L2_getter_NORMAL_flow_is_inferred_by_actual_static_read :
    inferredGetter = some expectedGetter := by decide
def applyCurrentGetter (row : Inferred) (input : Actual) : Option Actual := applySaved row input
def bindBackToB (input : Actual) : Actual := {input with pattern := {input.pattern with base := 2}}
def sinkAt6 (input : Actual) : Bool :=
  decide (input.pattern.base = 2 ∧ input.pattern.path = [1] ∧ input.pattern.tail = .exact ∧
    input.pattern.mark = .full 1 ∧ input.layer = .normal)

def followsCFG : List Nat → Bool
  | [] | [_] => true
  | fromNode :: toNode :: rest =>
      ((successors[fromNode]?).getD []).contains toNode && followsCFG (toNode :: rest)
def existingRootControlReachesSource : Bool := followsCFG [0,1,2]
theorem configured_root_has_the_existing_control_path_to_source2 :
    existingRootControlReachesSource = true := by decide

def allowedSource2 (permission controlDelivered : Bool) : Option Actual :=
  if permission && controlDelivered then some ⟨⟨0,[1],.exact,.full 1,[]⟩,.normal,false⟩ else none
def forwardSource2 : Option Actual :=
  allowedSource2 sourcePermission existingRootControlReachesSource
theorem permission_or_control_alone_cannot_emit_the_source :
    allowedSource2 false true = none ∧ allowedSource2 true false = none := by decide
def writeSharedForward (input : Actual) : Actual :=
  {input with pattern := {input.pattern with base := 3,path := [5] ++ input.pattern.path}}
def sourceBackedStatic : Option Actual := forwardSource2.map writeSharedForward
def F3SinkInput : Option Actual := do
  let actual ← sourceBackedStatic
  let throughHeader ← inferredHeader.bind (fun row => replayAt f3Adjacent row actual)
  let _seed ← emit f3 adjacentConcreteEntry throughHeader
  let getter ← inferredGetter
  let returned ← applyCurrentGetter getter throughHeader
  pure (bindBackToB returned)

theorem F3_source_action_and_real_write_produce_the_exact_static_fact :
    sourceBackedStatic = some FGTaint := by decide
theorem E20_finite_path_reaches_physical_sink6_with_NORMAL_T :
    F3SinkInput = some ⟨⟨2,[1],.exact,.full 1,[]⟩,.normal,false⟩ ∧
      (F3SinkInput.map sinkAt6).getD false = true := by decide
theorem MAY_actual_is_not_upgraded_by_a_NORMAL_header_record :
    inferredHeader.bind (fun row => replayAt f3Adjacent row coarseF) = some coarseF := by decide
theorem wrong_mark_source_permission_is_not_granted :
    sourceHit2 ⟨⟨0,[],.star,.full 2,[]⟩,.demand,false⟩ = false := by decide
theorem header_record_never_impersonates_the_repeat_even_with_weak_write :
    inferredHeader.bind (fun row => replayAt f3Repeat row FGTaint) = none ∧
      repeatFLOWRows.filterMap (fun row => infer b2 row coarseF repeatBody) =
        [⟨b2Repeat,FStar,⟨FStar,.normal,false⟩⟩] := by decide

end TwoLoopHeaderFlow

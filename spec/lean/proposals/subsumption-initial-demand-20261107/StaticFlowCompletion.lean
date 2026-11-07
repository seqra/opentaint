/-
Prepared operational witnesses, not checked by this child.
Imports the actual completion function and the checked ordinary C2 component.
NORMAL relations are inferred by ordinary body operations and complete paired
C5, never emitted by completion itself. No independent frame mechanism.

E19: exact source C.g.h; callee writes C.f, f != g; actual run-2 same-field
MAY/T query. Completion derives a separate FLOW/ANY self-row at that field.
Its ordinary analysis infers NORMAL carry; saved-first replay carries the
actual exact h mark in run-3. Writing g instead kills that hypothesis.

The cross-base example is a complete-pair interface witness, not a claim
that native id lacked its usual R1 NORMAL FLOW record. Both self and paired
guides are computed from the actual final input row by FlowDemandCompletion.
-/
import FlowDemandCompletion
import RelativeAdmission

namespace FlowCompletionOperational
open PlainStarRelativeAdmission
open ApSpec

set_option maxRecDepth 4096
set_option maxHeartbeats 8000000

abbrev FC := FlowDemandCompletion.Pattern
abbrev FRow := FlowDemandCompletion.Row
abbrev FInterface := FlowDemandCompletion.Interface

/-- Classes remain in the static base identity; each class costs zero fields.
Local bases are even; class-specific static bases are odd. Fields and array
accessors keep distinct counted Nat codes. This is a finite-case native
adapter, not a proposed change to the native AP representation. -/
def encodePath : FlowDemandCompletion.Path → List Nat
  | [] => []
  | .classId _ :: rest => encodePath rest
  | .field value :: rest => (value + 1) :: encodePath rest
  | .element :: rest => 0 :: encodePath rest
def encodeBase (pat : FC) : Nat :=
  match pat.base, pat.path with
  | .local id, _ => 2 * id
  | .staticRoot, .classId owner :: _ => 2 * owner + 1
  | .staticRoot, _ => 1
def encodeTail : FlowDemandCompletion.Tail → Tail
  | .exact => .exact | .star => .star | .may => .any | .must => .must
def encodePattern (pat : FC) : Option Pattern :=
  if FlowDemandCompletion.legalHead pat.base pat.path then
    match pat.mark with
    | .group _ => none
    | .flow => some ⟨encodeBase pat,encodePath pat.path,encodeTail pat.tail,.flow,encodePath pat.exclusion⟩
    | .full id => some ⟨encodeBase pat,encodePath pat.path,encodeTail pat.tail,.full id,encodePath pat.exclusion⟩
  else none

theorem adapter_counts_fields_and_arrays (path : FlowDemandCompletion.Path) :
    (encodePath path).length = RelativeRestriction.depth path := by
  induction path with
  | nil => rfl
  | cons head rest ih => cases head <;> simp [encodePath,RelativeRestriction.depth,ih]

def demandOf (pat : Pattern) : Demand :=
  ⟨pat.base,pat.path,
    match pat.tail with | .exact => .exact | .star => .star | .any | .must => .any,
    pat.mark,pat.exclusion⟩
structure Pair where
  entry : Demand
  exit : Demand
  deriving DecidableEq, Repr
def encodePair (row : FRow) : Option Pair :=
  match row.entry, row.exit with
  | .data input, .data output => do
      let left ← encodePattern input
      let right ← encodePattern output
      pure ⟨demandOf left,demandOf right⟩
  | _, _ => none

def bound (limit : Nat) (input : Actual) : Actual :=
  if input.pattern.path.length > limit then
    ⟨{input.pattern with path := input.pattern.path.take limit,tail := .any,exclusion := []},
      .demand,input.hasProtection⟩
  else input
def exitAdmits (selector : Demand) (output : Pattern) : Bool :=
  decide (selector.base = output.base) &&
    RestrictedInitialPolicy.acceptsMark selector.mark output.mark &&
    match dropPrefix selector.path output.path with
    | none => false
    | some suffix => match selector.shape with
      | .exact => decide (suffix = [] ∧ output.tail = .exact)
      | .any => true
      | .star => (Excl.set selector.exclusion).admits suffix

structure Inferred where
  interface : FInterface
  initial : Pattern
  output : Actual
  deriving DecidableEq, Repr

/-- One actual C2 call supplies the seed. C5 checks that key's image, and
the paired exit/base/mark from exactly the same row; no endpoint union. -/
def analyze (mode : Mode) (row : FRow) (incoming : Actual)
    (body : Actual → Option Actual) : Option Inferred := do
  let pair ← encodePair row
  let seed ← emit mode pair.entry incoming
  let output ← body (start seed)
  if rawImage mode pair.entry seed.initial && exitAdmits pair.exit output.pattern then
    pure ⟨row.interface,seed.initial,
      bound (min mode.limit (pair.exit.path.length + 1)) output⟩
  else none
def analyzeRows (mode : Mode) (rows : List FRow) (incoming : Actual)
    (body : Actual → Option Actual) : List Inferred :=
  rows.filterMap (fun row => analyze mode row incoming body)
def normalFlow (row : Inferred) : Bool :=
  decide (row.initial.mark = .flow ∧ row.output.pattern.mark = .flow ∧ row.output.layer = .normal)

def b2 : Mode := ⟨2,1,.backward⟩
def f3 : Mode := ⟨3,2,.forward⟩
def clearInterface : FInterface := ⟨101,true,0,-2,-1⟩
def copyInterface : FInterface := ⟨102,false,0,-1,-2⟩
def q (tail : FlowDemandCompletion.Tail) (mark : FlowDemandCompletion.Mark := .full 7) : FC :=
  ⟨.staticRoot,[.classId 7,.field 8],tail,mark,[]⟩
def qh : FC := ⟨.staticRoot,[.classId 7,.field 8,.field 9],.exact,.full 7,[]⟩
def originalStaticRow : FRow := ⟨clearInterface,.data (q .may),.data (q .may)⟩
def staticFlowGuide : FRow :=
  ⟨clearInterface,.data (q .may .flow),.data (q .may .flow)⟩
def staticRows : List FRow :=
  FlowDemandCompletion.completed [originalStaticRow] ++
    FlowDemandCompletion.virtualStaticCarry true clearInterface (q .may)
def originalPureFlowRow : FRow :=
  ⟨clearInterface,.data (q .star .flow),.data (q .star .flow)⟩

def qStar : Pattern := ⟨15,[9],.star,.flow,[]⟩
def qExact : Pattern := ⟨15,[9],.exact,.full 7,[]⟩
def qhExact : Pattern := ⟨15,[9,10],.exact,.full 7,[]⟩
def preciseSource : Actual := ⟨qhExact,.normal,false⟩
def actualRun2 : Actual := bound 1 preciseSource

theorem E19_FLOW_row_is_derived_from_final_T_row :
    staticFlowGuide ∈ FlowDemandCompletion.completed [originalStaticRow] := by decide
theorem E19_query_local_FLOW_row_is_derived :
    FlowDemandCompletion.virtualStaticCarry true clearInterface (q .may) = [staticFlowGuide] := by decide
theorem remaining_pure_FLOW_DEMAND_also_gets_completion :
    staticFlowGuide ∈ FlowDemandCompletion.completed [originalPureFlowRow] := by decide
theorem E19_source_cut_is_actual_query :
    actualRun2 = ⟨⟨15,[9],.any,.full 7,[]⟩,.demand,false⟩ ∧
    encodePattern qh = some qhExact := by decide

/-- Only the same/disjoint named-field cases are used. A write of that named
field kills its whole fact. A disjoint named field preserves it. No root
summary, weak update or new field-exclusion rule is introduced. -/
def strongNamedWrite (field : Nat) (input : Actual) : Option Actual :=
  match input.pattern.path with
  | head :: _ => if head = field then none else some input
  | [] => none
def staticExpected : Inferred := ⟨clearInterface,qStar,⟨qStar,.normal,false⟩⟩
def inferredStatic : Option Inferred :=
  (analyzeRows b2 staticRows actualRun2 (strongNamedWrite 8)).find? normalFlow

theorem E19_normal_provider_is_inferred : inferredStatic = some staticExpected := by decide
theorem E19_same_field_overwrite_infers_no_NORMAL_provider :
    (analyzeRows b2 staticRows actualRun2 (strongNamedWrite 9)).find? normalFlow = none := by decide
theorem E19_concrete_selector_remains_concrete_only :
    (analyze b2 originalStaticRow actualRun2 (strongNamedWrite 8)).map
      (fun row => row.initial.mark) = some (.full 7) := by decide

/-- Saved correlated application joins the actual layer. It cannot turn a
MAY actual into NORMAL data, even when the relation was inferred NORMAL. -/
def applySaved (row : Inferred) (input : Actual) : Option Actual :=
  if row.initial.base = input.pattern.base ∧ row.initial.tail = .star ∧
      RestrictedInitialPolicy.acceptsMark row.initial.mark input.pattern.mark = true then
    match dropPrefix row.initial.path input.pattern.path with
    | none => none
    | some suffix =>
        let pat := row.output.pattern
        let result : Pattern := ⟨pat.base, pat.path ++ suffix, input.pattern.tail,
          (if pat.mark = .flow then input.pattern.mark else pat.mark), pat.exclusion⟩
        some ⟨result,joinLayer row.output.layer input.layer,
          row.output.hasProtection || input.hasProtection⟩
  else none

/-- Actual reversed exact source: MAY at Q includes the named Q.h source
point. It grants that occurrence's permission, not a NORMAL report. -/
def actualSourceHit (input : Actual) : Bool :=
  decide (input.pattern.base = 15 ∧ input.pattern.mark = .full 7) &&
    match dropPrefix input.pattern.path qhExact.path with
    | none => false
    | some rest => decide (rest = [] ∨ input.pattern.tail = .any)
def sourcePermission : Bool :=
  ((inferredStatic.bind (fun row => applySaved row actualRun2)).map actualSourceHit).getD false
def staticRun3 : Option Actual := do
  if sourcePermission then pure () else none
  let saved ← inferredStatic
  applySaved saved preciseSource
def exactSinkAt (target : Pattern) (input : Actual) : Bool :=
  decide (input.pattern.base = target.base ∧ input.pattern.path = target.path ∧
    input.pattern.tail = .exact ∧ input.pattern.mark = target.mark ∧ input.layer = .normal)

theorem E19_MAY_application_keeps_DEMAND :
    inferredStatic.bind (fun row => applySaved row actualRun2) = some actualRun2 := by decide
theorem E19_actual_source_permission_is_derived : sourcePermission = true := by decide
theorem E19_saved_first_replay_recovers_exact_finding :
    staticRun3 = some preciseSource ∧
      (staticRun3.map (exactSinkAt qhExact)).getD false = true := by decide
theorem exact_static_parent_does_not_taint_child :
    ((inferredStatic.bind (fun row => applySaved row ⟨qExact,.normal,false⟩)).map
      (exactSinkAt qhExact)).getD false = false := by decide

def copyInput : FC := ⟨.local 0,[],.star,.full 7,[]⟩
def copyOutput : FC := ⟨.local 1,[],.star,.full 7,[]⟩
def originalCopyRow : FRow := ⟨copyInterface,.data copyInput,.data copyOutput⟩
def copyActual : Actual := ⟨⟨0,[5],.exact,.full 7,[]⟩,.normal,false⟩
def copyBody (input : Actual) : Option Actual :=
  some {input with pattern := {input.pattern with base := 2}}
def copyGuide : FRow :=
  ⟨copyInterface,.data ⟨.local 0,[],.may,.flow,[]⟩,.data ⟨.local 1,[],.may,.flow,[]⟩⟩
def inferredCopy : Option Inferred :=
  (analyzeRows f3 (FlowDemandCompletion.completed [originalCopyRow]) copyActual copyBody).find? normalFlow
def copyExpected : Inferred :=
  ⟨copyInterface,⟨0,[5],.star,.flow,[]⟩,⟨⟨2,[5],.star,.flow,[]⟩,.normal,false⟩⟩

theorem paired_copy_FLOW_row_is_derived :
    copyGuide ∈ FlowDemandCompletion.pairedRow originalCopyRow := by decide
theorem self_only_completion_does_not_mix_endpoints :
    (analyzeRows f3 (originalCopyRow :: FlowDemandCompletion.prefixRows originalCopyRow)
      copyActual copyBody).find? normalFlow = none := by decide
theorem paired_copy_PROVIDER_is_inferred : inferredCopy = some copyExpected := by decide
theorem paired_copy_actual_exact_mark_is_preserved :
    inferredCopy.bind (fun row => applySaved row copyActual) =
      some ⟨⟨2,[5],.exact,.full 7,[]⟩,.normal,false⟩ := by decide
theorem copied_normal_record_keys_are_not_ANY :
    staticExpected.initial.tail ≠ .any ∧ copyExpected.initial.tail ≠ .any := by decide

/- OWASP-shaped bounded negative: after final subsumption removes a long
cross-base FLOW relation, a remaining Target/DATA endpoint can add only its
self-prefix permissions. Those rows cannot publish a cross-base return or
H-return relation under complete paired C5. This is NOT a theorem that every
real OWASP frontier has only these rows, nor a general natural-stop proof. -/
def targetToInput : FRow := ⟨copyInterface,.target,.data copyInput⟩
def onlyTargetView : List FRow := FlowDemandCompletion.completed [targetToInput]
def uniformActual : Actual := ⟨⟨0,[],.must,.full 7,[]⟩,.normal,false⟩
def inputSelfGuide : FRow := FlowDemandCompletion.selfPair copyInterface copyInput []
def uniformSeed : Seed := ⟨⟨0,[],.must,.flow,[]⟩,.normal⟩
def copyBodyAtH (input : Actual) : Option Actual :=
  some {input with pattern := {input.pattern with base := 2,path := [6] ++ input.pattern.path}}

theorem canonical_uniform_packet_admits_root_MUST_not_child_STAR :
    ((encodePair inputSelfGuide).bind
      (fun pair => emit f3 pair.entry uniformActual)) = some uniformSeed := by decide
theorem Target_self_completion_cannot_publish_crossbase_copy :
    analyzeRows f3 onlyTargetView uniformActual copyBody = [] := by decide
theorem Target_self_completion_cannot_publish_crossbase_H :
    analyzeRows f3 onlyTargetView uniformActual copyBodyAtH = [] := by decide

#eval "FLOW_COMPLETION_OPERATIONAL_STATIC_PROVIDER=" ++ toString inferredStatic.isSome
#eval "FLOW_COMPLETION_OPERATIONAL_COPY_PROVIDER=" ++ toString inferredCopy.isSome


#print axioms adapter_counts_fields_and_arrays
#print axioms E19_FLOW_row_is_derived_from_final_T_row
#print axioms E19_query_local_FLOW_row_is_derived
#print axioms remaining_pure_FLOW_DEMAND_also_gets_completion
#print axioms E19_source_cut_is_actual_query
#print axioms E19_normal_provider_is_inferred
#print axioms E19_same_field_overwrite_infers_no_NORMAL_provider
#print axioms E19_concrete_selector_remains_concrete_only
#print axioms E19_MAY_application_keeps_DEMAND
#print axioms E19_actual_source_permission_is_derived
#print axioms E19_saved_first_replay_recovers_exact_finding
#print axioms exact_static_parent_does_not_taint_child
#print axioms paired_copy_FLOW_row_is_derived
#print axioms self_only_completion_does_not_mix_endpoints
#print axioms paired_copy_PROVIDER_is_inferred
#print axioms paired_copy_actual_exact_mark_is_preserved
#print axioms copied_normal_record_keys_are_not_ANY
#print axioms canonical_uniform_packet_admits_root_MUST_not_child_STAR
#print axioms Target_self_completion_cannot_publish_crossbase_copy
#print axioms Target_self_completion_cannot_publish_crossbase_H

end FlowCompletionOperational

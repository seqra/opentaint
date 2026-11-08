/-
PREPARED, not checked by this author. Finite FULL source/helper/sink phase
catalog. Latest generic C2 (including raw EXACT/FLOW prefix) and annotated
C5 are imported. The actual baseline F75 selected cleaner and correlated
rawApply/rawSummary are used. No NORMAL helper provider, guide or source
permission is an input. Flags on concrete cleaner survivors are transported.

Native root/Target callback, precise JVM source occurrence, owner actor,
canonical packed storage and stopping correspondence remain adapters. The
finite helper catalog includes arg/return results and ZERO control; it does
not claim a whole-engine proof. No cleaner semantics are changed.
-/
import ExactFlowPrefixCompanion
import FlowDemandCompletion
import AnnotatedC5Exit
import ApSpec.BaseCleaner
import ApSpec.Run1CorrelatedConcreteInitials

namespace RootExactCleanerGap
open PlainStarRelativeAdmission
open ApSpec

set_option maxRecDepth 16384
set_option maxHeartbeats 32000000

def arg : Nat := 10
def ret : Nat := 11
def zeroBase : Nat := 999
def g : Nat := 5
def t : Nat := 7

def pat (base : Nat) (path : List Nat) (tail : Tail)
    (mark : ScalarMark := .flow) : Pattern := ⟨base,path,tail,mark,[]⟩
def b2 : Mode := ⟨2,1,.backward⟩
def f3 : Mode := ⟨3,2,.forward⟩
def cleaner : Cleaner := ⟨arg,[],.exact,some t⟩

def core (p : Pattern) : PFact :=
  ⟨p.base,p.path,
    (match p.tail with
      | .exact => .exact
      | .star => .star (.set p.exclusion)
      | .any => .any
      | .must => .any),
    (match p.mark with | .flow => .star | .full m => .conc m)⟩
def uncore (p : PFact) : Pattern :=
  ⟨p.base,p.path,
    (match p.kind with
      | .exact => .exact
      | .star _ => .star
      | .any => .any),
    (match p.mark with | .conc m => .full m | _ => .flow),
    (match p.kind with | .star (.set e) => e | _ => [])⟩

structure Value where
  data : AFact
  h : Bool := false
  deriving DecidableEq, Repr
structure Row where
  initial : Pattern
  output : Value
  deriving DecidableEq, Repr

def value (p : Pattern) (layer : Layer := .normal) (h : Bool := false) : Value :=
  ⟨⟨core p,decide (layer = .demand)⟩,h⟩
def startValue (s : Seed) : Value := value s.initial s.layer

def unique [DecidableEq α] (values : List α) : List α :=
  values.foldl (fun out v => if v ∈ out then out else out ++ [v]) []
def flowMark : MarkA → Bool | .conc _ => false | _ => true

def publicKind : Kind → Kind | .exact => .star (.set []) | k => k
/-- The existing complete FLOW pair normalization, only after body execution. -/
def publicRow (p : Pattern) (v : Value) : Row :=
  let original := publicInitial p
  let output := if p.mark = .flow ∧ flowMark v.data.fact.mark then
      {v with data := ⟨{v.data.fact with kind := publicKind v.data.fact.kind},v.data.demand⟩}
    else v
  ⟨original,output⟩

/-- ApOps.clean protects surviving concrete selected memberships; no FLOW
flag is created. Existing input H is retained through this one-value adapter. -/
def clean (v : Value) : List Value :=
  (ApSpec.BaseCleaner.cleanRes cleaner v.data).facts.map fun a =>
    ⟨a,v.h || decide (a.fact.base = arg ∧ a.fact.mark = .conc t)⟩

def starSide (base : Nat) : PFact := ⟨base,[],.star (.set []),.star⟩
def copy (fromBase toBase : Nat) (v : Value) : List Value :=
  (ApSpec.Run1CorrelatedConcreteInitials.rawApply v.data (starSide fromBase) (starSide toBase)).facts.map
    (fun a => ⟨a,v.h⟩)

/-- m(p){ RemoveMark(p,T,Exact); return p; }. All final argument and return
facts are enumerated. In backward direction the return copy is reversed. -/
def boundary (mode : Mode) (v : Value) : List Value :=
  if mode.direction = .forward then
    (clean v).flatMap fun a => [a] ++ copy arg ret a
  else (copy ret arg v).flatMap clean

def zero : AFact := ⟨⟨zeroBase,[],.exact,.conc 0⟩,false⟩
def sourceTo : PFact := ⟨arg,[g],.exact,.conc t⟩
def sinkFrom : PFact := ⟨ret,[g],.exact,.conc t⟩
def source : Value :=
  ⟨(ApSpec.Run1CorrelatedConcreteInitials.rawApply zero zero.fact sourceTo).facts.headD zero,false⟩
def sinkReverse : Value :=
  ⟨(ApSpec.Run1CorrelatedConcreteInitials.rawApply zero zero.fact sinkFrom).facts.headD zero,false⟩

def requestedMarks : List Nat :=
  (ApSpec.BaseCleaner.cleanRes cleaner (startValue ⟨pat arg [] .star,.normal⟩).data).reqs
/-- Baseline nonstatic F1 answer: exact only at the empty origin; a descendant
actual answers the existing empty-path STAR key. -/
def requestAnswer (mark : Nat) : Seed :=
  let p := uncore (answerInit (core (pat arg [] .star)) source.data.fact mark)
  ⟨p,intrinsic p⟩
def r1Seeds : List Seed := ⟨pat arg [] .star,.normal⟩ :: requestedMarks.map requestAnswer

def dataR1 : List Row := unique (r1Seeds.flatMap fun seed =>
  (boundary ⟨1,1,.forward⟩ (startValue seed)).map (publicRow seed.initial))
/-- ZERO is untouched by the cleaner and by the ordinary return statement's
untouched-base branch; it is a control record, not a DATA provider. -/
def zeroRow : Row := ⟨pat zeroBase [] .exact (.full 0),⟨zero,false⟩⟩
def r1Rows : List Row := zeroRow :: dataR1

def encode (p : Pattern) : FlowDemandCompletion.Pattern :=
  ⟨.local p.base,p.path.map RelativeRestriction.Accessor.field,
    (match p.tail with | .exact => .exact | .star => .star | .any => .may | .must => .must),
    (match p.mark with | .flow => .flow | .full m => .full m),
    p.exclusion.map RelativeRestriction.Accessor.field⟩
def ports (mode : Mode) : FlowDemandCompletion.Interface :=
  ⟨42,decide (mode.direction = .forward),0,
    (if mode.direction = .forward then -1 else -2),
    (if mode.direction = .forward then -2 else -1)⟩
def handoff (mode : Mode) (rows : List Row) : List FlowDemandCompletion.Row :=
  unique ((rows.filter (fun row => row.output.data.demand)).map fun row =>
    ⟨ports mode,.data (encode (uncore row.output.data.fact)),.data (encode row.initial)⟩)
def query (completion : Bool) (rows : List FlowDemandCompletion.Row) : List FlowDemandCompletion.Row :=
  unique (if completion then FlowDemandCompletion.completed rows else rows)

def natPath : RelativeRestriction.Path → Option (List Nat)
  | [] => some []
  | .field n :: rest => (natPath rest).map (List.cons n)
  | _ => none
def decoded (p : FlowDemandCompletion.Pattern) : Option Pattern := do
  let base ← match p.base with | .local n => some n | _ => none
  let path ← natPath p.path
  let mark ← match p.mark with | .full m => some (.full m : ScalarMark) | .flow => some .flow | _ => none
  let e ← natPath p.exclusion
  pure ⟨base,path,(match p.tail with | .exact => .exact | .star => .star | .may => .any | .must => .must),mark,e⟩
def entry (row : FlowDemandCompletion.Row) : Option Demand := do
  let p ← match row.entry with | .data p => decoded p | _ => none
  pure ⟨p.base,p.path,(match p.tail with | .exact => .exact | .star => .star | _ => .any),p.mark,p.exclusion⟩
def exit (row : FlowDemandCompletion.Row) : Option Pattern :=
  match row.exit with | .data p => decoded p | _ => none

def actual (v : Value) : Actual :=
  ⟨uncore v.data.fact,(if v.data.demand then .demand else .normal),v.h⟩
def commands (mode : Mode) (rows : List FlowDemandCompletion.Row) (v : Value) : List Seed :=
  unique (rows.flatMap fun row => match entry row with
    | none => [] | some d => ExactFlowPrefixCompanion.emitSeeds mode d (actual v))

/-- Scoped executable rendering of the selected C5 image. The EXACT-prefix
component proves its normalized public keys need no additional image branch. -/
def stores (mode : Mode) (d : Demand) (p : Pattern) : Bool :=
  canStoreInitial mode d p || match p.tail,p.mark,d.mark with
    | .star,.flow,.full m =>
        let twin := {p with mark := .full m}
        rawImage mode d twin && insideDemand d twin
    | _,_,_ => false

def toExitPattern (p : Pattern) : AnnotatedC5Exit.Pattern :=
  ⟨p.base,p.path.map RelativeRestriction.Accessor.field,
    (match p.tail with | .exact => .exact | .star => .star | .any => .may | .must => .must),
    (match p.mark with | .flow => .flow [] | .full m => .full m),
    p.exclusion.map RelativeRestriction.Accessor.field⟩
def toExit (v : Value) : AnnotatedC5Exit.Fact :=
  let p := uncore v.data.fact
  let shape := toExitPattern p
  let slot := match v.data.fact.mark with
    | .conc m => AnnotatedC5Exit.Slot.full m | .star => .flow [] | .starEx mx => .flow mx
  ⟨{shape with slot := slot},(if v.data.demand then .demand else .normal),v.h⟩
def fromExit (v : AnnotatedC5Exit.Fact) : Option Value := do
  let path ← natPath v.path
  let e ← natPath v.exclusion
  let kind ← match v.tail with
    | .exact => some Kind.exact
    | .star => some (.star (.set e))
    | .may => some .any
    | .must => none
  let mark := match v.slot with | .full m => MarkA.conc m | .flow [] => .star | .flow mx => .starEx mx
  pure ⟨⟨⟨v.base,path,kind,mark⟩,decide (v.layer = .demand)⟩,v.h⟩
def finish (mode : Mode) (row : FlowDemandCompletion.Row) (seed : Seed) (raw : Value) : Option Row := do
  let d ← entry row
  let dp ← exit row
  let published := publicRow seed.initial raw
  if !stores mode d published.initial then none else
    let kept ← AnnotatedC5Exit.restrictData (decide (mode.direction = .forward)) mode.limit
      (toExit published.output) (toExitPattern dp)
    let v ← fromExit kept
    pure (publicRow published.initial v)
def infer (mode : Mode) (rows : List FlowDemandCompletion.Row) (v : Value) : List Row :=
  unique ((commands mode rows v).flatMap fun seed =>
    (boundary mode (startValue seed)).flatMap fun raw => rows.filterMap fun row => finish mode row seed raw)

def applyRow (row : Row) (v : Value) : List Value :=
  (ApSpec.Run1CorrelatedConcreteInitials.rawSummary v.data (core row.initial) row.output.data).facts.map
    (fun a => ⟨a,v.h || row.output.h⟩)
def applyRows (rows : List Row) (v : Value) : List Value := unique (rows.flatMap (fun row => applyRow row v))
def normal (rows : List Row) : List Row := rows.filter (fun row => !row.output.data.demand)
def reverseNormal (row : Row) : Row :=
  let reversed := revEdge (core row.initial) row.output.data.fact
  ⟨uncore reversed.1,⟨⟨reversed.2,row.output.data.demand⟩,row.output.h⟩⟩

def hitSink (v : Value) : Option Bool :=
  (ApSpec.Run1CorrelatedConcreteInitials.rawApply v.data sinkFrom zero.fact).facts.head?.map
    (fun a => a.demand)
def targets (rows : List Row) : List Bool := unique ((applyRows rows source).filterMap hitSink)
def r1Targets : List Bool := targets r1Rows

def b2Rows (completion : Bool) : List Row :=
  if true ∈ r1Targets then infer b2 (query completion (handoff b2 r1Rows)) sinkReverse else []
def sourceHit (v : Value) : Bool :=
  !(ApSpec.Run1CorrelatedConcreteInitials.rawApply v.data sourceTo zero.fact).facts.isEmpty
def sourcePermission (completion : Bool) : Bool :=
  (applyRows ((normal r1Rows).map reverseNormal) sinkReverse ++ applyRows (b2Rows completion) sinkReverse).any sourceHit

def f3Rows (completion : Bool) : List Row :=
  if sourcePermission completion then infer f3 (query completion (handoff f3 (b2Rows completion))) source else []
def f3Saved (completion : Bool) : List Row := normal r1Rows ++ (normal (b2Rows completion)).map reverseNormal

def f3Targets (completion : Bool) : List Bool := targets (f3Saved completion ++ f3Rows completion)
def carriesT (row : Row) : Bool :=
  match row.output.data.fact.mark with
  | .conc m => decide (m = t)
  | .star => true
  | .starEx mx => !(memB t mx)

def expectedTArg : Row := ⟨pat arg [] .star (.full t),value (pat arg [] .star (.full t)) .demand true⟩
def expectedTRet : Row := ⟨pat arg [] .star (.full t),value (pat ret [] .star (.full t)) .demand true⟩
def flowValue (base : Nat) : Value := ⟨⟨⟨base,[],.star (.set []),.starEx [t]⟩,false⟩,false⟩
def expectedFlowArg : Row := ⟨pat arg [] .star,flowValue arg⟩
def expectedFlowRet : Row := ⟨pat arg [] .star,flowValue ret⟩
def expectedB2 : Row := ⟨pat ret [] .star (.full t),value (pat arg [] .star (.full t)) .demand true⟩

theorem exact_root_cleaner_does_not_clean_the_real_child :
    cleaner.cleansB ⟨arg,[g],t⟩ = false := by decide

theorem direct_actual_body_keeps_the_NORMAL_child :
    (boundary f3 source).filterMap hitSink = [false] := by decide

theorem real_cleaner_requests_T_from_the_F1_FLOW_probe : requestedMarks = [t] := by decide

theorem descendant_answer_is_STAR_DEMAND_not_a_precise_child :
    r1Seeds = [⟨pat arg [] .star,.normal⟩,⟨pat arg [] .star (.full t),.demand⟩] := by decide

theorem complete_R1_argument_return_and_control_catalog :
    r1Rows = [zeroRow,expectedFlowArg,expectedFlowRet,expectedTArg,expectedTRet] := by decide

theorem ALL_R1_NORMAL_DATA_rows_exclude_T_and_T_survivors_are_protected_DEMAND :
    normal r1Rows = [zeroRow,expectedFlowArg,expectedFlowRet] ∧
    r1Rows.filter (fun row => row.output.data.demand) = [expectedTArg,expectedTRet] := by decide

theorem real_R1_sink_is_provisional_and_supplies_the_backward_phase : r1Targets = [true] := by decide

theorem B2_uncompleted_commands_are_requested_STAR_and_FLOW_companion_only :
    commands b2 (query false (handoff b2 r1Rows)) sinkReverse =
      [⟨pat ret [] .star (.full t),.demand⟩,⟨pat ret [] .star,.normal⟩] := by decide

theorem complete_B2_without_completion_has_only_the_protected_T_row :
    b2Rows false = [expectedB2] := by decide

theorem B2_FLOW_body_is_rejected_by_the_original_paired_T_exit :
    ((boundary b2 (startValue ⟨pat ret [] .star,.normal⟩)).flatMap fun raw =>
      (handoff b2 r1Rows).filterMap fun row => finish b2 row ⟨pat ret [] .star,.normal⟩ raw) = [] := by decide

theorem real_source_permission_is_derived_in_both_query_variants :
    sourcePermission false = true ∧ sourcePermission true = true := by decide

theorem ANY_completion_can_add_prefix_probes_but_all_NORMAL_results_exclude_T :
    (normal (b2Rows true)).all (fun row => !(carriesT row)) = true := by decide

theorem later_precise_STAR_rejects_the_real_F3_actual_before_any_companion :
    commands f3 (query false (handoff f3 (b2Rows false))) source = [] := by decide

theorem completed_F3_query_really_uses_the_latest_EXACT_prefix_companion :
    ⟨pat arg [] .exact,.normal⟩ ∈ commands f3 (query true (handoff f3 (b2Rows true))) source := by decide

theorem ALL_saved_NORMAL_rows_cannot_deliver_T_to_the_sink (completion : Bool) :
    targets (f3Saved completion) = [] := by cases completion <;> decide

theorem ALL_new_F3_rows_are_NORMAL_FLOW_excluding_T (completion : Bool) :
    (f3Rows completion).all (fun row => !row.output.data.demand && !(carriesT row)) = true := by
  cases completion <;> decide

theorem both_current_query_variants_miss_the_NORMAL_finding :
    f3Targets false = [] ∧ f3Targets true = [] := by decide

theorem actual_source_is_in_budget_NORMAL_in_F1_and_F3 :
    source.data.fact = sourceTo ∧ source.data.demand = false ∧ sourceTo.path.length ≤ 1 := by decide

theorem ZERO_control_is_not_a_DATA_provider : applyRow zeroRow source = [] := by decide

end RootExactCleanerGap

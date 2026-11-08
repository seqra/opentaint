/-
Prepared E18 scalar operational subdomain. Actual checked C2/C5 and the
baseline correlated rawApply/rawSummary kernels are used, including concrete
T->U mark composition. No NORMAL T->U or FLOW record is supplied as an input.
Source-occurrence ownership is a separate native SOURCES-callback adapter:
the checked backward action result is nonempty and belongs to the same fixed
forward source action. This file does not redefine global source policy.
-/
import RelativeAdmission
import AnnotatedC5Exit

namespace ConcreteConverterWrapper
open PlainStarRelativeAdmission
open ApSpec
open ApSpec.Run1CorrelatedConcreteInitials

set_option maxRecDepth 4096
set_option maxHeartbeats 8000000

def T : Nat := 7
def U : Nat := 11
def f : Nat := 4
def g : Nat := 5
def zeroBase : Nat := 999
def pat (base : Nat) (path : List Nat) (tail : Tail) (mark : Nat) : Pattern :=
  ⟨base,path,tail,.full mark,[]⟩
def actual (p : Pattern) (layer : Layer) : Actual := ⟨p,layer,false⟩
def toCore (p : Pattern) : Option PFact :=
  let mark := match p.mark with | .flow => MarkA.star | .full m => .conc m
  match p.tail with
  | .exact => some ⟨p.base,p.path,.exact,mark⟩
  | .star => some ⟨p.base,p.path,.star (.set p.exclusion),mark⟩
  | .any => some ⟨p.base,p.path,.any,mark⟩
  | .must => none
def ofCore (a : AFact) : Option Actual :=
  let mark := match a.fact.mark with | .conc m => some (RestrictedInitialPolicy.Mark.full m) | .star => some .flow | .starEx _ => none
  do
    let mark ← mark
    let shape ← match a.fact.kind with
      | .exact => some (Tail.exact,[])
      | .any => some (Tail.any,[])
      | .star (.set e) => some (Tail.star,e)
      | .star .univ => none
    pure ⟨⟨a.fact.base,a.fact.path,shape.1,mark,shape.2⟩,
      (if a.demand then .demand else .normal),false⟩
def coreActual (a : Actual) : Option AFact :=
  (toCore a.pattern).map fun p => ⟨p,decide (a.layer = .demand)⟩
def coreResult (limit : Nat) (r : Res) : Option Actual :=
  r.facts.head?.bind fun a => ofCore (limitF (fun _ => true) limit a)

def sourceFrom : PFact := ⟨0,[],.any,.conc T⟩
def sourceTo : PFact := ⟨1,[f,g],.exact,.conc U⟩
def sourceAction (backward : Bool) (input : AFact) : Res :=
  if backward then rawApply input sourceTo sourceFrom else rawApply input sourceFrom sourceTo
def applySource (backward : Bool) (limit : Nat) (input : Actual) : Option Actual := do
  let raw ← coreActual input
  coreResult limit (sourceAction backward raw)

structure Row where
  initial : Pattern
  output : Actual
  deriving DecidableEq, Repr
structure Pair where
  entry : Demand
  exit : Demand
  deriving DecidableEq, Repr
def demandOf (p : Pattern) : Demand :=
  ⟨p.base,p.path,(match p.tail with | .exact => .exact | .star => .star | _ => .any),p.mark,p.exclusion⟩
def handoff (r : Row) : Pair := ⟨demandOf r.output.pattern,demandOf r.initial⟩
def toC5 (a : Actual) : AnnotatedC5Exit.Fact :=
  ⟨⟨a.pattern.base,a.pattern.path.map RelativeRestriction.Accessor.field,
      (match a.pattern.tail with | .exact => .exact | .star => .star | .any => .may | .must => .must),
      (match a.pattern.mark with | .flow => .flow [] | .full m => .full m),
      a.pattern.exclusion.map RelativeRestriction.Accessor.field⟩,
    (match a.layer with | .normal => .normal | .demand => .demand),a.hasProtection⟩
def c5Demand (d : Demand) : AnnotatedC5Exit.Pattern :=
  ⟨d.base,d.path.map RelativeRestriction.Accessor.field,
    (match d.shape with | .exact => .exact | .star => .star | .any => .may),
    (match d.mark with | .flow => .flow [] | .full m => .full m),
    d.exclusion.map RelativeRestriction.Accessor.field⟩
def ofC5 (a : AnnotatedC5Exit.Fact) : Actual :=
  ⟨⟨a.base,a.path.filterMap (fun x => match x with | .field n => some n | _ => none),
    (match a.tail with | .exact => .exact | .star => .star | .may => .any | .must => .must),
    (match a.slot with | .full m => .full m | .flow _ => .flow),
    a.exclusion.filterMap (fun x => match x with | .field n => some n | _ => none)⟩,
    (match a.layer with | .normal => .normal | .demand => .demand),a.h⟩
def publish (mode : Mode) (pair : Pair) (seed : Seed) (output : Actual) : Option Row :=
  if rawImage mode pair.entry seed.initial then
    (AnnotatedC5Exit.restrictData (decide (mode.direction = .forward)) mode.limit
      (toC5 output) (c5Demand pair.exit)).map fun result => ⟨seed.initial,ofC5 result⟩
  else none
def applyRow (limit : Nat) (row : Row) (input : Actual) : Option Actual := do
  let raw ← coreActual input
  let initial ← toCore row.initial
  let output ← coreActual row.output
  coreResult limit (rawSummary raw initial output)

inductive Phase where | run1 | run2 | run3
  deriving DecidableEq, Repr
def seed1 : Seed := ⟨pat 0 [] .star T,.demand⟩
def seed2 : Seed := ⟨pat 1 [f] .star U,.demand⟩
def seed3 : Seed := ⟨pat 0 [] .exact T,.normal⟩
def row1 : Row := ⟨seed1.initial,actual (pat 1 [f] .any U) .demand⟩
def row2 : Row := ⟨seed2.initial,actual (pat 0 [] .any T) .demand⟩
def row3 : Row := ⟨seed3.initial,actual (pat 1 [f,g] .exact U) .normal⟩
def pair2 : Pair := handoff row1
def pair3 : Pair := handoff row2
def phaseSeed : Phase → Seed | .run1 => seed1 | .run2 => seed2 | .run3 => seed3
def phaseRow : Phase → Row | .run1 => row1 | .run2 => row2 | .run3 => row3
def phaseLimit : Phase → Nat | .run1 | .run2 => 1 | .run3 => 2

/-- The actual guard produces T's run-1 request from abstract FLOW. This is
not a FLOW-to-U record. The ordinary request answer binds the offered T to
its existing correlated T/STAR initial. -/
def flowProbe : AFact := ⟨⟨0,[],.star (.set []),.star⟩,false⟩
def requestedT : Bool := memB T (sourceAction false flowProbe).reqs
def emitSeed (phase : Phase) (input : Actual) : Option Seed :=
  match phase with
  | .run1 => if requestedT && decide (input.pattern.base = 0 ∧ input.pattern.mark = .full T) then some seed1 else none
  | .run2 => emit ⟨2,1,.backward⟩ pair2.entry input
  | .run3 => emit ⟨3,2,.forward⟩ pair3.entry input
def finish (phase : Phase) (seed : Seed) (output : Actual) : Option Row :=
  match phase with
  | .run1 => some ⟨seed.initial,output⟩
  | .run2 => publish ⟨2,1,.backward⟩ pair2 seed output
  | .run3 => publish ⟨3,2,.forward⟩ pair3 seed output
def leaf (phase : Phase) (seed : Seed) : Option Row := do
  let output ← applySource (decide (phase = .run2)) (phaseLimit phase) (start seed)
  finish phase seed output
def derive (phase : Phase) : Nat → Actual → Option Row
  | 0,input => do
      let seed ← emitSeed phase input
      leaf phase seed
  | n+1,input => do
      let seed ← emitSeed phase input
      let child ← derive phase n (start seed)
      let output ← applyRow (phaseLimit phase) child (start seed)
      finish phase seed output

theorem marks_are_distinct : T ≠ U := by decide
theorem guard_requests_T_but_emits_no_FLOW_to_U :
    requestedT = true ∧ (sourceAction false flowProbe).facts = [] := by decide
theorem leaf_rows_are_actually_inferred (phase : Phase) :
    leaf phase (phaseSeed phase) = some (phaseRow phase) := by cases phase <;> decide
theorem internal_C2_admits_each_phase (phase : Phase) :
    emitSeed phase (start (phaseSeed phase)) = some (phaseSeed phase) := by cases phase <;> decide
theorem ordinary_wrapper_composition_keeps_the_inferred_row (phase : Phase) :
    ((applyRow (phaseLimit phase) (phaseRow phase) (start (phaseSeed phase))).bind
      (finish phase (phaseSeed phase))) = some (phaseRow phase) := by cases phase <;> decide
theorem arbitrary_finite_wrappers_derive_the_row (phase : Phase) (n : Nat) (input : Actual)
    (admitted : emitSeed phase input = some (phaseSeed phase)) :
    derive phase n input = some (phaseRow phase) := by
  induction n generalizing input with
  | zero => simpa [derive,admitted] using leaf_rows_are_actually_inferred phase
  | succ n ih =>
    have child := ih (start (phaseSeed phase)) (internal_C2_admits_each_phase phase)
    simpa [derive,admitted,child] using ordinary_wrapper_composition_keeps_the_inferred_row phase

def zero : AFact := ⟨⟨zeroBase,[],.exact,.conc 0⟩,false⟩
def rootSourceFrom : PFact := zero.fact
def rootSourceTo : PFact := ⟨0,[],.exact,.conc T⟩
def actualT : Actual := actual (pat 0 [] .exact T) .normal
def backwardOffer : Actual := actual (pat 1 [f] .any U) .demand
def sinkFrom : PFact := ⟨1,[f,g],.exact,.conc U⟩
def run1SinkCandidate : Option AFact := do
  let marked ← applyRow 1 row1 actualT
  let input ← coreActual marked
  (rawApply input sinkFrom rootSourceFrom).facts.head?
def reverseSinkOffer : Option Actual := do
  let reachedDemandTarget ← run1SinkCandidate
  coreResult 1 (rawApply reachedDemandTarget rootSourceFrom sinkFrom)
def acceptedConverterSource : Bool :=
  !(sourceAction true (⟨⟨1,[f],.star (.set []),.conc U⟩,true⟩ : AFact)).facts.isEmpty
def backwardTAtRoot : Option Actual := applyRow 1 row2 backwardOffer
def acceptedRootSource : Bool :=
  ((backwardTAtRoot.bind coreActual).map
    (fun input => !(rawApply input rootSourceTo rootSourceFrom).facts.isEmpty)).getD false

theorem initial_T_is_from_the_real_ZERO_source_action :
    coreResult 1 (rawApply zero rootSourceFrom rootSourceTo) = some actualT := by decide
theorem R1_sink_candidate_is_DEMAND_not_NormalTarget :
    run1SinkCandidate = some {zero with demand := true} := by decide
theorem actual_U_sink_reverse_supplies_the_coarse_offer : reverseSinkOffer = some backwardOffer := by decide
theorem R1_actual_offer_is_request_admitted : emitSeed .run1 actualT = some seed1 := by decide
theorem R2_actual_ANY_offer_is_admitted : emitSeed .run2 backwardOffer = some seed2 := by decide
theorem R3_actual_exact_T_is_admitted_NORMAL : emitSeed .run3 actualT = some seed3 := by decide
theorem accepted_backward_actions_derive_both_source_hit_preconditions :
    acceptedConverterSource = true ∧ acceptedRootSource = true ∧
      backwardTAtRoot = some (actual (pat 0 [] .any T) .demand) := by decide

def normalSinkWitness (input : Actual) (mark : Nat) : Bool :=
  decide (input.pattern.base = 1 ∧ input.pattern.path = [f,g] ∧
    input.pattern.tail = .exact ∧ input.pattern.mark = .full mark ∧ input.layer = .normal)
def finalFinding (wrappers : Nat) : Bool :=
  if acceptedConverterSource && acceptedRootSource then
    (((derive .run3 wrappers actualT).bind (fun row => applyRow 2 row actualT)).map
      (fun result => normalSinkWitness result U)).getD false
  else false
theorem arbitrary_finite_wrappers_keep_exact_U_finding (n : Nat) : finalFinding n = true := by
  have inferred := arbitrary_finite_wrappers_derive_the_row .run3 n actualT R3_actual_exact_T_is_admitted_NORMAL
  unfold finalFinding
  rw [inferred]
  decide
theorem U_result_is_not_a_T_result :
    ((applyRow 2 row3 actualT).map (fun result => normalSinkWitness result T)).getD false = false := by decide
theorem wrong_input_mark_cannot_trigger_the_source :
    emitSeed .run3 (actual (pat 0 [] .exact U) .normal) = none ∧
    applySource false 2 (actual (pat 0 [] .exact U) .normal) = none := by decide
theorem the_mark_changing_rows_have_no_ANY_original :
    row1.initial.tail ≠ .any ∧ row2.initial.tail ≠ .any ∧ row3.initial.tail ≠ .any := by decide

#print axioms marks_are_distinct
#print axioms guard_requests_T_but_emits_no_FLOW_to_U
#print axioms leaf_rows_are_actually_inferred
#print axioms internal_C2_admits_each_phase
#print axioms ordinary_wrapper_composition_keeps_the_inferred_row
#print axioms arbitrary_finite_wrappers_derive_the_row
#print axioms initial_T_is_from_the_real_ZERO_source_action
#print axioms R1_sink_candidate_is_DEMAND_not_NormalTarget
#print axioms actual_U_sink_reverse_supplies_the_coarse_offer
#print axioms R1_actual_offer_is_request_admitted
#print axioms R2_actual_ANY_offer_is_admitted
#print axioms R3_actual_exact_T_is_admitted_NORMAL
#print axioms accepted_backward_actions_derive_both_source_hit_preconditions
#print axioms arbitrary_finite_wrappers_keep_exact_U_finding
#print axioms U_result_is_not_a_T_result
#print axioms wrong_input_mark_cannot_trigger_the_source
#print axioms the_mark_changing_rows_have_no_ANY_original

end ConcreteConverterWrapper

/-
E19 interface counterexample, not a full native-engine proof or a repair.

Program (ordinary FULL marks, source/check at the exact named field):
  main() { sourceT(C.g.h); clearF(); sinkT(C.g.h); }
  clearF() { C.f = null; }      -- f != g

The model derives the actual GH input from the source and derives its coarse
G/MAY input with a genuine one-field cut. It does not enumerate an artificial
Tag universe or manufacture a C5 preimage. Only the encountered C2 cells are
modeled. The contract theorem below also states the failure for ANY C2
implementation which obeys the selected strict-descendant rejection.

Interface assumptions bound by the native no-loop/control traces:
* R2 has this concrete-only carry pair; no companion FLOW initial/provider.
* Paired C5 retains its G/STAR -> G/STAR DEMAND identity.
* Handoff retains precise STAR, and saved DATA providers are absent.
* Calls replay saved records first, then gate current replay/subscription by C2.
* This call has no other DATA bypass, writer-pool route, source or read effect.

These assumptions are deliberately visible. In particular, absence of another
DATA route is not proved here for the complete analyzer. An independent
executable witness with these interface rules disproves a claim that the
selected same-head rule alone closes every principal example.
-/
import Std

namespace PlainStarStaticCarryGap

inductive Field where | f | g | h
  deriving DecidableEq, BEq, Repr
abbrev Path := List Field

def isPrefixPath : Path → Path → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => x == y && isPrefixPath xs ys

def fPath : Path := [.f]
def gPath : Path := [.g]
def ghPath : Path := [.g, .h]

/-- Heap coordinates are exact field paths with one concrete mark T. -/
abbrev Heap := Path → Bool
def clean : Heap := fun _ => false
def sourceT (targetPath : Path) (heap : Heap) : Heap :=
  fun p => p == targetPath || heap p
def writeClean (targetPath : Path) (heap : Heap) : Heap :=
  fun p => if isPrefixPath targetPath p then false else heap p
def clearF (heap : Heap) : Heap := writeClean fPath heap
def concreteMain : Bool := (clearF (sourceT ghPath clean)) ghPath

theorem fields_are_distinct : Field.f ≠ Field.g := by decide
theorem concrete_program_reports : concreteMain = true := by decide
theorem write_removes_f_subtree : (clearF (sourceT fPath clean)) fPath = false := by decide

inductive Base where | staticRoot | arg | returned
  deriving DecidableEq, BEq, Repr
inductive Mark where | flow | t | u
  deriving DecidableEq, BEq, Repr
inductive Tail where | exact | star | may | must
  deriving DecidableEq, BEq, Repr
inductive Layer where | normal | demand
  deriving DecidableEq, BEq, Repr

structure Fact where
  base : Base
  path : Path
  tail : Tail
  mark : Mark
  deriving DecidableEq, BEq, Repr
structure Actual where
  fact : Fact
  layer : Layer
  deriving DecidableEq, BEq, Repr
structure Seed where
  initial : Fact
  start : Fact
  layer : Layer
  deriving DecidableEq, BEq, Repr
structure Config where
  run : Nat
  limit : Nat
  deriving DecidableEq, BEq, Repr

def g (tail : Tail) (mark : Mark := .t) : Fact :=
  ⟨.staticRoot, gPath, tail, mark⟩
def gh : Fact := ⟨.staticRoot, ghPath, .exact, .t⟩
def actualSource : Actual := ⟨gh, .normal⟩
def bound (limit : Nat) (a : Actual) : Actual :=
  if a.fact.path.length > limit then
    ⟨{ a.fact with path := a.fact.path.take limit, tail := .may }, .demand⟩
  else a
def coarseSource : Actual := bound 1 actualSource
def run2 : Config := ⟨2, 1⟩
def run3 : Config := ⟨3, 2⟩

def markEligible (demand actual : Mark) : Bool :=
  demand == .flow || demand == actual
def identitySeed (p : Fact) (a : Actual) : Seed :=
  ⟨p, p, if p.mark == .flow then .normal
         else if p.tail == .star then .demand else a.layer⟩

/-- The interface fragment used by this program. Same-head ANY + ANY/STAR
uses ordinary STAR identity. Precise STAR rejects strict descendants later.
No unencountered C2 table cell is claimed to be defined by this function. -/
def carryC2 (cfg : Config) (d : Fact) (a : Actual) : List Seed :=
  if decide (cfg.run < 2) || d.base != a.fact.base ||
      decide (d.path.length > cfg.limit) || decide (a.fact.path.length > cfg.limit) ||
      !markEligible d.mark a.fact.mark then []
  else if d.path != a.fact.path then []
  else match d.tail, a.fact.tail with
    | .may, .may | .may, .star =>
        [identitySeed { d with tail := .star } a]
    | .may, .exact | .star, .exact =>
        [identitySeed { d with tail := .exact } a]
    | .star, .star | .star, .may =>
        [identitySeed { d with tail := .exact } a]
    | _, _ => []

def carrySeed : Seed := ⟨g .star, g .star, .demand⟩

theorem coarse_source_is_real_cut : coarseSource = ⟨g .may, .demand⟩ := by decide
theorem selected_same_head_ANY :
    carryC2 run2 (g .may) coarseSource = [carrySeed] := by decide
theorem selected_same_head_STAR :
    carryC2 run3 (g .may) ⟨g .star, .demand⟩ = [carrySeed] := by decide
theorem same_head_FULL_mark_mismatch :
    carryC2 run3 (g .may) ⟨g .star .u, .demand⟩ = [] := by decide
theorem same_head_precise_STAR_emits_EXACT :
    carryC2 run3 (g .star) ⟨g .star, .demand⟩ =
      [⟨g .exact, g .exact, .demand⟩] := by decide
theorem source_fits_run3_field_limit : gh.path.length = run3.limit := by decide
theorem later_precise_STAR_rejects_descendant :
    carryC2 run3 (g .star) actualSource = [] := by decide

inductive Endpoint where | zero | data (fact : Fact)
  deriving DecidableEq, BEq, Repr
structure Relation where
  premise : Endpoint
  conclusion : Endpoint
  layer : Layer
  nonSubsumable : Bool := false
  deriving DecidableEq, BEq, Repr
structure DemandPair where
  entry : Fact
  exit : Fact
  deriving DecidableEq, BEq, Repr

def r2Demand : DemandPair := ⟨g .may, g .may⟩
def rawCarry : Relation := ⟨.data carrySeed.initial, .data carrySeed.start, carrySeed.layer, false⟩

/-- Finite actual witness for this pair, not a global C5 image procedure.
The actual carry fallback uses one existing MAY/MAY pair. C2(coarseSource)
witnesses the STAR entry; its STAR conclusion is kept whole under the MAY
exit selector at the same position. Entry and exit are not mixed across rows.
The cap min(limit 1, exit-depth 1 + 1) is one, so no conclusion field is cut. -/
def exitKeepsWhole (selector conclusion : Fact) : Bool :=
  selector.base == conclusion.base && selector.path == conclusion.path &&
    markEligible selector.mark conclusion.mark &&
    (selector.tail == .may || selector.tail == conclusion.tail)
def pairedCap : Nat := min run2.limit (r2Demand.exit.path.length + 1)
def c5RetainCarry : Option Relation :=
  match rawCarry.conclusion with
  | .data conclusion =>
      if (carryC2 run2 r2Demand.entry coarseSource).any
          (fun s => Endpoint.data s.initial == rawCarry.premise) &&
          exitKeepsWhole r2Demand.exit conclusion &&
          decide (conclusion.path.length ≤ pairedCap) then some rawCarry else none
  | .zero => none
theorem actual_coarse_pair_and_cap :
    r2Demand = ⟨g .may, g .may⟩ ∧ pairedCap = 1 := by decide
theorem paired_C5_has_actual_witness : c5RetainCarry = some rawCarry := by decide

def handoff (r : Relation) : Option DemandPair :=
  match r.layer, r.premise, r.conclusion with
  | .demand, .data p, .data c => some ⟨c, p⟩
  | _, _, _ => none
def r3Demand : DemandPair := ⟨g .star, g .star⟩
theorem handoff_does_not_widen_precise_STAR : handoff rawCarry = some r3Demand := by decide

def savedZero : Relation := ⟨.zero, .zero, .normal, false⟩
def saved : List Relation := [savedZero]
def current : List Relation := [rawCarry]

structure Delivery where
  endpoint : Endpoint
  layer : Layer
  deriving DecidableEq, BEq, Repr

/-- Saved control is real and replays first; it cannot transport DATA. The
fixture has no saved DATA relation, so no omitted DATA matcher is used here. -/
def replaySavedControl (offer : Endpoint) : List Delivery :=
  saved.flatMap fun r =>
    if r.layer == .normal && r.premise == offer then [⟨r.conclusion, .normal⟩] else []
theorem saved_ZERO_replay_exists : replaySavedControl .zero = [⟨.zero, .normal⟩] := by decide
theorem saved_ZERO_cannot_carry_DATA : replaySavedControl (.data gh) = [] := by decide

/-- A necessary S1 cover witness: an actually available NORMAL FLOW DATA
relation. Geometry can narrow this predicate, but cannot invent a provider. -/
def isNormalFlowProvider (r : Relation) : Bool :=
  match r.layer, r.premise, r.conclusion with
  | .normal, .data p, .data c => p.mark == .flow && c.mark == .flow
  | _, _, _ => false
def admittedProviders : List Relation := (saved ++ current).filter isNormalFlowProvider
theorem no_admitted_NORMAL_FLOW_provider : admittedProviders = [] := by decide
theorem no_S1_cover_witness :
    ¬ ∃ provider, provider ∈ saved ++ current ∧ isNormalFlowProvider provider = true := by
  intro witness
  rcases witness with ⟨provider, member, isFlow⟩
  simp [saved, current] at member
  rcases member with rfl | rfl <;>
    simp [isNormalFlowProvider, savedZero, rawCarry, carrySeed] at isFlow

def applyCurrentCarry (a : Actual) : List Delivery :=
  if a.fact.base == .staticRoot && a.fact.mark == .t && isPrefixPath gPath a.fact.path then
    [⟨.data a.fact, .demand⟩]
  else []

structure CallResult where
  savedOutputs : List Delivery
  seeds : List Seed
  subscribed : Bool
  currentOutputs : List Delivery
  deriving DecidableEq, BEq, Repr

/-- Original selected call order: saved replay; demand lookup; current
replay/subscription only when that lookup admits at least one initial. -/
def callPipelineWith (lookup : Config → Fact → Actual → List Seed)
    (a : Actual) : CallResult :=
  let savedOutputs := replaySavedControl (.data a.fact)
  let seeds := lookup run3 r3Demand.entry a
  ⟨savedOutputs, seeds, !seeds.isEmpty,
    if seeds.isEmpty then [] else applyCurrentCarry a⟩
def result : CallResult := callPipelineWith carryC2 actualSource

theorem current_relation_is_not_the_missing_piece :
    applyCurrentCarry actualSource = [⟨.data gh, .demand⟩] := by decide
theorem actual_call_has_no_DATA_output :
    result = ⟨[], [], false, []⟩ := by decide

/-- This conclusion holds for ANY complete C2 implementation with the selected
rejection on this actual input. It does not depend on omitted fragment cells. -/
theorem any_C2_with_selected_rejection_loses_this_call
    (lookup : Config → Fact → Actual → List Seed)
    (rejection : lookup run3 r3Demand.entry actualSource = []) :
    callPipelineWith lookup actualSource = ⟨[], [], false, []⟩ := by
  unfold callPipelineWith
  rw [rejection]
  change (⟨replaySavedControl (.data gh), [], false, []⟩ : CallResult) =
    (⟨[], [], false, []⟩ : CallResult)
  rw [saved_ZERO_cannot_carry_DATA]

def exactSink (outputs : List Delivery) : Bool :=
  outputs.any (fun e => e.endpoint == .data gh && e.layer == .normal)
def sourcePermission : Bool := true
def analyzedMain : Bool :=
  if sourcePermission then exactSink (result.savedOutputs ++ result.currentOutputs) else false

theorem missing_finding_even_with_source_permission :
    sourcePermission = true ∧ concreteMain = true ∧ analyzedMain = false := by decide

/- Why DEMAND + unprotected does not authorize blanket NORMAL promotion.
This is a separate concrete rule semantics witness, not a claim that this
native call generated the displayed coarse guard relation.

  API: ret is initially clean;
  Rule: CM(p.f,T) -> Pass(p,ret).
  Actual: T only at p.g; guard false; therefore ret.g has no T.

An unconditional NORMAL p.STAR/T -> ret.STAR/T would report ret.g anyway.
Protection=false (pass cannot add H) does not establish that relation.
-/
def conditionalPass (heap : Heap) : Heap := if heap fPath then heap else clean
def actualGuardInput : Heap := sourceT gPath clean
def conditionalRuleSink : Bool := (conditionalPass actualGuardInput) gPath
def promotedNormalIdentitySink : Bool := actualGuardInput gPath
theorem blanket_normal_promotion_has_concrete_counterexample :
    actualGuardInput fPath = false ∧
    conditionalRuleSink = false ∧ promotedNormalIdentitySink = true := by decide

#eval (concreteMain, analyzedMain, result)
#print axioms missing_finding_even_with_source_permission
#print axioms any_C2_with_selected_rejection_loses_this_call
#print axioms blanket_normal_promotion_has_concrete_counterexample

end PlainStarStaticCarryGap

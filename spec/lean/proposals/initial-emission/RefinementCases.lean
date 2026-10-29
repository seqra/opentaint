/-
  ANY refinement means demand/input intersection. It need not be strict.

  This model supersedes the strict-progress interpretation tested, but not
  selected, in AdmissionHistory.lean. An identity ANY intersection is valid.
  No admission cache, source/sink exception or production change is added.

  Scope: one scalar path, demand tail ANY, Empty field/mark exclusions and
  concrete full marks (plus FLOW for the abstract demand). No static, ND,
  cleaner or type-filter policy is modeled. MUST is an explicit tail flag,
  independent of an edge's NORMAL/DEMAND layer. A DEMAND MUST value must not
  be confused with MAY merely because both have a DEMAND layer.

  weakAnyMeet is the ANY-demand specialization of current Reference.commonPart,
  not F72's Reference.emit FLOW-form branch. It preserves the actual tail
  when it descends from the actual path to the demand path. Old emitM/emitX
  instead use the demand tail in that above-path branch. Thus the library's
  general legacy emitter is not silently used as the current Kotlin bridge.

  A supplied STAR is retained by intersection. This computation does not
  authorize a policy which manufactures STAR/FLOW from a supplied ANY value.
  The full admission contract, all tail kinds and whole-run coverage remain
  outside this matrix.
-/
import ApSpec.AnyTaintExDefs
import ApSpec.AbsDefs

namespace ApSpec.InitialEmissionRefinementCases
open ApSpec ApSpec.Reverse ApSpec.Handoff ApSpec.AnyTaintEx ApSpec.Abs

structure Input where
  fact : PFact
  must : Bool
deriving DecidableEq, Repr

/-- `must` distinguishes Kotlin ANY_TAINT from ANY. It is not an edge layer.
    In this scope a demand never has the ANY_TAINT tail. A submitted MUST can
    have a DEMAND edge. A fresh MUST initial's NORMAL start does not erase
    that caller-side DEMAND layer during summary application. -/
def weakAnyMeet (d : PFact) (a : Input) : Option Input :=
  if d.kind.isAny && Nat.beq d.base a.fact.base && markSubB d.mark a.fact.mark then
    match relate d.path a.fact.path with
    | .below _ => some a
    | .above r =>
      if admitsTailB a.fact.kind r then
        some ⟨{ a.fact with path := d.path }, a.must⟩
      else none
    | .apart => none
  else none

def p : Base := 1
def H : Acc := 7
def K : Acc := 8
def T : Mark := 1
def U : Mark := 2

def flowDemand (path : List Acc := []) : PFact := ⟨p, path, .any, .star⟩
def markDemand (path : List Acc := []) : PFact := ⟨p, path, .any, .conc T⟩
def may (path : List Acc := []) : Input := ⟨⟨p, path, .any, .conc T⟩, false⟩
def must (path : List Acc := []) : Input := ⟨⟨p, path, .any, .conc T⟩, true⟩
def exact (path : List Acc := []) : Input := ⟨⟨p, path, .exact, .conc T⟩, false⟩
def suppliedStar (path : List Acc := []) : Input :=
  ⟨⟨p, path, .star Excl.empty, .conc T⟩, false⟩

structure Case where
  name : String
  demand : PFact
  actual : Input
  expected : Option Input
deriving Repr

def cases : List Case := [
  ⟨"MAY identity under FLOW demand", flowDemand [], may [], some (may [])⟩,
  ⟨"MAY identity under T demand", markDemand [], may [], some (may [])⟩,
  ⟨"MUST at the same path", flowDemand [], must [], some (must [])⟩,
  ⟨"EXACT at the same path", flowDemand [], exact [], some (exact [])⟩,
  ⟨"known descendant MAY", flowDemand [], may [H], some (may [H])⟩,
  ⟨"known descendant MUST", flowDemand [], must [H], some (must [H])⟩,
  ⟨"known descendant EXACT", flowDemand [], exact [H], some (exact [H])⟩,
  ⟨"actual MAY above the demanded field", markDemand [H], may [], some (may [H])⟩,
  ⟨"actual MUST above the demanded field", markDemand [H], must [], some (must [H])⟩,
  ⟨"actual EXACT cannot descend", markDemand [H], exact [], none⟩,
  ⟨"distinct fields are disjoint", markDemand [H], may [K], none⟩,
  ⟨"distinct bases do not meet", flowDemand [], ⟨⟨2, [], .any, .conc T⟩, false⟩, none⟩,
  ⟨"distinct concrete marks do not meet", markDemand [], ⟨⟨p, [], .any, .conc U⟩, false⟩, none⟩,
  ⟨"a FLOW actual cannot supply a concrete mark", markDemand [],
    ⟨⟨p, [], .any, .star⟩, false⟩, none⟩,
  ⟨"supplied STAR at the same path", markDemand [], suppliedStar [], some (suppliedStar [])⟩,
  ⟨"known descendant supplied STAR", markDemand [], suppliedStar [H], some (suppliedStar [H])⟩,
  ⟨"supplied STAR above demand retains its tail", markDemand [H], suppliedStar [],
    some (suppliedStar [H])⟩
]

def matrixCheck : Bool := cases.all fun c => weakAnyMeet c.demand c.actual == c.expected

/-- Every successful matrix cell satisfies the existing premise satisfaction
    and inside-demand tests. This checks the listed cells, not all AP grammar. -/
def obligationsCheck : Bool := cases.all fun c =>
  match c.expected with
  | none => true
  | some j =>
    satI j.fact c.actual.fact && insideB j.fact c.demand &&
      j.fact.mark == c.actual.fact.mark && j.fact.kind == c.actual.fact.kind &&
      j.must == c.actual.must

/-- All successful listed cells use a concrete mark, so none constructs an
    abstract EXACT/MUST or a premise with a mark exclusion. -/
def representationCheck : Bool := cases.all fun c =>
  match c.expected with
  | none => true
  | some j =>
    (match j.fact.mark with | .conc _ => true | _ => false) &&
      (!j.must || j.fact.kind.isAny)

theorem complete_case_matrix : matrixCheck = true := by decide
theorem matrix_satisfaction_and_inside : obligationsCheck = true := by decide
theorem matrix_initial_representability : representationCheck = true := by decide

/-- Raw scalar identity holds for every tail and mark. This computational
    fact does not assert legal InitialAp representation for every raw mark;
    the separate matrix representability check uses only legal concrete cases. -/
theorem abstract_any_identity (b : Base) (path : List Acc) (k : Kind)
    (mark : MarkA) (am : Bool) :
    weakAnyMeet ⟨b, path, .any, .star⟩ ⟨⟨b, path, k, mark⟩, am⟩ =
      some ⟨⟨b, path, k, mark⟩, am⟩ := by
  simp [weakAnyMeet, Kind.isAny, markSubB, relate, RAux.dropPrefix_self']

/-- The earlier strict progress test is intentionally only a diagnostic.
    Its false result is not a reason to reject a valid identity intersection. -/
def strictProgress (d : PFact) (a : Input) : Bool :=
  a.must || a.fact.kind == .exact ||
    match dropPrefix d.path a.fact.path with
    | some (_ :: _) => true
    | _ => false

theorem strict_false_but_weak_valid :
    strictProgress (markDemand []) (may []) = false ∧
    weakAnyMeet (markDemand []) (may []) = some (may []) ∧
    satI (may []).fact (may []).fact = true ∧
    insideB (may []).fact (markDemand []) = true := by decide

theorem original_same_path_any_bridge :
    emitTX emitX (flowDemand []) (may []).fact false Excl.empty =
      some ((may []).fact, false, Excl.empty) ∧
    emitTX emitX (flowDemand []) (must []).fact true Excl.empty =
      some ((must []).fact, true, Excl.empty) := by decide

/-- This is the above-path difference from the older general Lean emitter.
    The current scalar meet keeps supplied STAR; it does not invent STAR. -/
theorem legacy_above_star_difference :
    emitX (markDemand [H]) (suppliedStar []).fact Excl.empty =
      some ((may [H]).fact, Excl.empty) ∧
    weakAnyMeet (markDemand [H]) (suppliedStar []) = some (suppliedStar [H]) := by decide

theorem f72_synthesized_star_is_not_weak_intersection :
    emitW (flowDemand []) (may []).fact =
      some ⟨p, [], .star Excl.empty, .star⟩ ∧
    weakAnyMeet (flowDemand []) (may []) = some (may []) := by decide

#eval matrixCheck && obligationsCheck && representationCheck
#print axioms complete_case_matrix
#print axioms matrix_satisfaction_and_inside
#print axioms matrix_initial_representability
#print axioms abstract_any_identity
#print axioms strict_false_but_weak_valid
#print axioms legacy_above_star_difference

end ApSpec.InitialEmissionRefinementCases

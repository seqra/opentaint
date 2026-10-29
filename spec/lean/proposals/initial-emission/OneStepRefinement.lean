/-
  Selected cells for one-step demand refinement.

  These cells are selected:
    demand x.p.ANY/M + actual x.p.EXACT/T   => x.p.EXACT/M
    demand x.p.ANY/FLOW + actual x.p.f.EXACT/T => x.p.f.STAR/FLOW
    demand x.p.ANY/T + actual x.p.f.EXACT/T => x.p.f.EXACT/T
  A concrete demand U rejects actual T when U differs from T.
  The first cell permits abstract EXACT as a new premise shape.
  Stop after the first new field for FLOW: actual x.p.f.g.EXACT/T gives
  x.p.f.STAR/FLOW. Interpret the concrete EXACT exception as retaining the
  complete submitted exact path, including f.g. No table for other tails is
  completed for ancestor/STAR cases in this model.
  The previous concrete-MUST-retention exception is revoked. The selected
  same-prefix MUST template below uses demand mark M; its new abstract-MUST
  representation and transfer proof are not supplied by the old library.

  This file models selected concrete-STAR coverage matching and records the
  separate abstract-EXACT gaps. It does not erase EXACT on start or change
  production. Concrete STAR starts and stays DEMAND in the checked operations.
  Scope: one scalar path, a known prefix and suffix, empty exclusions, no statics,
  ND, cleaners, aliases or type filters. All definitions are executable.
-/
import ApSpec.AnyTaintExDefs
import ApSpec.AbsDefs
import ApSpec.CorrelatedConcreteImplementation

namespace ApSpec.InitialEmissionOneStep
open ApSpec ApSpec.Reverse ApSpec.Handoff ApSpec.AnyTaintEx ApSpec.Abs

def x : Base := 1
def y : Base := 2
def F : Acc := 7
def G : Acc := 8
def T : Mark := 1

def demand (m : MarkA) : PFact := ⟨x, [], .any, m⟩
def actualRoot : PFact := ⟨x, [], .exact, .conc T⟩
def actualField : PFact := ⟨x, [F], .exact, .conc T⟩

/-- These are the chosen root and first-field results. -/
def selectedRoot (m : MarkA) : PFact := ⟨x, [], .exact, m⟩
def selectedField (m : MarkA) : PFact := ⟨x, [F], .star Excl.empty, m⟩

def xf (fact : PFact) (d : Bool := false) : XFact := ⟨⟨fact, d⟩, Excl.empty⟩

/-- Selected constructor for an EXACT actual at `prefix ++ suffix`.
    Matching the base and mark and applying the run's field limit are separate
    obligations. This constructor does not inspect beyond the first new field. -/
def selectedFlowFromExact (b : Base) (ctx suffix : List Acc) : PFact :=
  match suffix with
  | [] => ⟨b, ctx, .exact, .star⟩
  | f :: _ => ⟨b, ctx ++ [f], .star Excl.empty, .star⟩

theorem stop_after_first_new_field (b : Base) (ctx : List Acc)
    (f : Acc) (rest : List Acc) :
    selectedFlowFromExact b ctx (f :: rest) =
      ⟨b, ctx ++ [f], .star Excl.empty, .star⟩ := rfl

theorem remainder_does_not_change_initial (b : Base) (ctx : List Acc)
    (f : Acc) (r₁ r₂ : List Acc) :
    selectedFlowFromExact b ctx (f :: r₁) =
      selectedFlowFromExact b ctx (f :: r₂) := rfl

/-- Executable location witness: the complete exact actual is covered by the
    selected first-field STAR, even when its remaining suffix is nonempty. -/
theorem selected_prefix_covers_actual (b : Base) (ctx : List Acc)
    (f : Acc) (rest : List Acc) (t : Mark) :
    (selectedFlowFromExact b ctx (f :: rest)).covers
      ⟨b, ctx ++ (f :: rest), t⟩ := by
  refine ⟨rfl, ⟨rest, ?_, CoreAux.empty_admits rest⟩, True.intro⟩
  simp [selectedFlowFromExact, List.append_assoc]

theorem two_known_fields_still_select_only_one :
    selectedFlowFromExact x [] [F, G] = selectedField .star := by decide

/-- Explicit MUST tail flag, independent of any submitted edge layer. -/
structure Submitted where
  fact : PFact
  must : Bool
deriving DecidableEq, Repr

/-- This is a partial decision table. `unspecified` is not rejection and is
    not permission to emit. It records a cell which still needs a contract. -/
inductive Decision where
  | emit (initial : PFact) (must : Bool)
  | reject
  | unspecified
deriving DecidableEq, Repr

def selectedGeometry (d : PFact) (a : Submitted) : Decision :=
  if d.kind.isAny then
    match relate d.path a.fact.path with
    | .apart => .reject
    | .above _ => if a.fact.kind == .exact then .reject else .unspecified
    | .below rest =>
      if a.fact.kind == .exact then
        match d.mark with
        | .star => .emit (selectedFlowFromExact d.base d.path rest) false
        | .conc _ => .emit a.fact false
        | _ => .unspecified
      else if a.fact.kind.isAny then
        match rest with
        | [] => .emit { a.fact with mark := d.mark } a.must
        | f :: _ => .emit ⟨d.base, d.path ++ [f], .star Excl.empty, d.mark⟩ false
      else .unspecified
  else .unspecified

/-- FULL-mode equality guard runs before shape selection. A demand for U
    cannot rename a submitted T into U. Group-coverage rules are out of scope. -/
def selected (d : PFact) (a : Submitted) : Decision :=
  if d.base = a.fact.base then
    match d.mark, a.fact.mark with
    | .conc u, .conc t => if u = t then selectedGeometry d a else .reject
    | .star, .conc _ => selectedGeometry d a
    | .conc _, _ => .reject
    | _, _ => .unspecified
  else .reject

theorem concrete_mark_mismatch_always_rejects (b : Base) (dp ap : List Acc)
    (k : Kind) (am : Bool) (u t : Mark) (hne : u ≠ t) :
    selected ⟨b, dp, .any, .conc u⟩ ⟨⟨b, ap, k, .conc t⟩, am⟩ = .reject := by
  simp [selected, hne]

theorem selected_policy_cells :
    selected (demand .star) ⟨actualRoot, false⟩ = .emit (selectedRoot .star) false ∧
    selected (demand .star) ⟨actualField, false⟩ = .emit (selectedField .star) false ∧
    selected (demand .star) ⟨⟨x, [F, G], .exact, .conc T⟩, false⟩ =
      .emit (selectedField .star) false ∧
    selected (demand (.conc T)) ⟨actualField, false⟩ = .emit actualField false := by decide

theorem mismatches_in_all_requested_shapes :
    selected (demand (.conc 2)) ⟨actualRoot, false⟩ = .reject ∧
    selected (demand (.conc 2)) ⟨actualField, false⟩ = .reject ∧
    selected (demand (.conc 2)) ⟨⟨x, [], .any, .conc T⟩, false⟩ = .reject ∧
    selected (demand (.conc 2)) ⟨⟨x, [], .any, .conc T⟩, true⟩ = .reject := by decide

/-- Explicit interpretation of the concrete EXACT exception: retain the
    whole submitted exact fact, including any deeper known suffix. -/
theorem deeper_concrete_exact_keeps_whole_submitted_fact :
    selected (demand (.conc T)) ⟨⟨x, [F, G], .exact, .conc T⟩, false⟩ =
      .emit ⟨x, [F, G], .exact, .conc T⟩ false ∧
    satW ⟨x, [F, G], .exact, .conc T⟩ ⟨x, [F, G], .exact, .conc T⟩ = true := by decide

theorem selected_concrete_exact_child_matches_current :
    insideB actualField (demand (.conc T)) = true ∧
    satW actualField actualField = true := by decide

/-- Selected uniform demand mark. Its typed representation and transfer still
    require an extension; there is no concrete-MUST-retention fallback. -/
def uniformMustCandidate (m : MarkA) : Submitted := ⟨⟨x, [], .any, m⟩, true⟩

def currentMustGuard (j : Submitted) : Bool :=
  if j.must then
    j.fact.kind.isAny && (match j.fact.mark with | .conc _ => true | _ => false)
  else true

theorem uniform_abstract_must_needs_new_representation :
    (uniformMustCandidate .star).fact.mark = .star ∧
    (uniformMustCandidate .star).must = true ∧
    currentMustGuard (uniformMustCandidate .star) = false ∧
    insideB (uniformMustCandidate .star).fact (demand .star) = true ∧
    satW (uniformMustCandidate .star).fact ⟨x, [], .any, .conc T⟩ = true ∧
    selected (demand .star) ⟨⟨x, [], .any, .conc T⟩, true⟩ =
      .emit (uniformMustCandidate .star).fact true := by decide

/-- Historical matching rejects a deeper concrete MAY or MUST supplier for
    F.STAR/T. The following selected coverage extension closes this matching
    gap without making the emitted STAR initial NORMAL. -/
theorem deeper_concrete_may_must_matching_gap :
    satW (selectedField (.conc T)) ⟨x, [F, G], .any, .conc T⟩ = false ∧
    selected (demand (.conc T)) ⟨⟨x, [F, G], .any, .conc T⟩, false⟩ =
      .emit (selectedField (.conc T)) false ∧
    selected (demand (.conc T)) ⟨⟨x, [F, G], .any, .conc T⟩, true⟩ =
      .emit (selectedField (.conc T)) false := by decide

theorem unchanged_any_remains_valid :
    selected (demand .star) ⟨⟨x, [], .any, .conc T⟩, false⟩ =
      .emit ⟨x, [], .any, .star⟩ false ∧
    selected (demand (.conc T)) ⟨⟨x, [], .any, .conc T⟩, false⟩ =
      .emit ⟨x, [], .any, .conc T⟩ false := by decide

/-- Selected extension: concrete STAR premises can match by coverage too.
    Other concrete tail kinds keep their existing satisfaction test. -/
def concreteStar (j : PFact) : Bool :=
  match j.kind, j.mark with
  | .star _, .conc _ => true
  | _, _ => false

def proposedMatching (j a : PFact) : Bool :=
  satW j a || (concreteStar j && applicable j a)

def deepMustSupplier : Submitted := ⟨⟨x, [F, G], .any, .conc T⟩, true⟩

theorem coverage_matching_admits_deeper_concrete_must :
    deepMustSupplier.must = true ∧
    applicable (selectedField (.conc T)) deepMustSupplier.fact = true ∧
    proposedMatching (selectedField (.conc T)) deepMustSupplier.fact = true ∧
    proposedMatching (selectedField (.conc T)) actualField = true := by decide

theorem ordinary_concrete_matching_is_unchanged (b : Base) (path : List Acc)
    (t : Mark) (a : PFact) :
    proposedMatching ⟨b, path, .any, .conc t⟩ a = satW ⟨b, path, .any, .conc t⟩ a ∧
    proposedMatching ⟨b, path, .exact, .conc t⟩ a = satW ⟨b, path, .exact, .conc t⟩ a := by
  simp [proposedMatching, concreteStar]

/-- The MAY and MUST variants both have an ANY raw tail here. The extension
    is restricted to STAR, so neither variant starts accepting an EXACT
    supplier through an added coverage branch. -/
theorem ordinary_any_must_premise_still_rejects_exact_supplier :
    proposedMatching ⟨x, [F], .any, .conc T⟩ actualField = false ∧
    proposedMatching actualField actualField = true := by decide

/-- Current Demand.kt already starts concrete STAR as STAR/DEMAND.
    Use the correlated library's selectedStart, not legacy Basic.startFact. -/
def concreteStarStart : AFact :=
  ApSpec.Run1CorrelatedConcreteInitials.selectedStart (selectedField (.conc T))

theorem current_concrete_star_starts_demand :
    concreteStarStart = ⟨selectedField (.conc T), true⟩ ∧
    concreteStarStart.fact.kind = .star Excl.empty ∧
    concreteStarStart.demand = true := by decide

theorem selected_deeper_concrete_start_is_demand :
    selected (demand (.conc T)) deepMustSupplier =
      .emit (selectedField (.conc T)) false ∧
    concreteStarStart.fact = selectedField (.conc T) ∧
    concreteStarStart.demand = true := by decide

def concreteStarReturn : AFact := ⟨⟨y, [F], .star Excl.empty, .conc T⟩, true⟩

theorem concrete_star_identity_summary_is_demand :
    (ApSpec.Run1CorrelatedConcreteInitials.rawApply concreteStarStart
      (selectedField .star) ⟨y, [F], .star Excl.empty, .star⟩).facts = [concreteStarReturn] := by decide

/-- Any computed transfer result of this concrete STAR start remains DEMAND.
    This is layer monotonicity, not a whole-program summary-coverage theorem. -/
theorem concrete_star_start_cannot_make_normal (fr to : PFact) (r : AFact)
    (h : r ∈ (ApSpec.Run1CorrelatedConcreteInitials.rawApply concreteStarStart fr to).facts) :
    r.demand = true :=
  ApSpec.CorrelatedConcreteImplementation.raw_keeps_demand concreteStarStart fr to rfl r h

/-- A demand summary keeps application results in DEMAND even for a NORMAL
    caller. The exact/MUST tail interpretation is separate from this layer law. -/
theorem demand_summary_application_cannot_make_normal (a : AFact) (j : PFact)
    (g : AFact) (hg : g.demand = true) (r : AFact)
    (h : r ∈ (ApSpec.Run1CorrelatedConcreteInitials.rawSummary a j g).facts) :
    r.demand = true := by
  obtain ⟨before, _, hr⟩ := List.mem_map.mp h
  rw [← hr]
  simp [hg]

theorem normal_caller_gets_demand_from_concrete_star_summary :
    (ApSpec.Run1CorrelatedConcreteInitials.rawSummary ⟨⟨x, [F, G], .exact, .conc T⟩, false⟩
      (selectedField (.conc T)) concreteStarReturn).facts =
      [⟨⟨y, [F, G], .exact, .conc T⟩, true⟩] := by decide

theorem selected_flow_child_matches_current :
    insideB (selectedField .star) (demand .star) = true ∧
    applicable (selectedField .star) actualField = true ∧
    satI (selectedField .star) actualField = false ∧
    satW (selectedField .star) actualField = true := by decide

theorem rejected_concrete_star_child_matching_gap :
    insideB (selectedField (.conc T)) (demand (.conc T)) = true ∧
    applicable (selectedField (.conc T)) actualField = true ∧
    satI (selectedField (.conc T)) actualField = false ∧
    satW (selectedField (.conc T)) actualField = false := by decide

def actualTwoFields : XFact := xf ⟨x, [F, G], .exact, .conc T⟩
def identityResult : XFact := xf ⟨y, [F], .star Excl.empty, .star⟩
def selectedIdentity : MicroEdge := (selectedField .star, identityResult.af.fact)

/-- id(p) with actual p.F.G/T can use the p.F.STAR/FLOW summary. Ordinary
    application preserves the actual suffix G, exact tail, concrete T and N.
    This does not resolve the separate concrete-premise matching gap. -/
theorem first_field_flow_identity_preserves_suffix :
    satW (selectedField .star) actualTwoFields.af.fact = true ∧
    satI (selectedField .star) actualTwoFields.af.fact = false ∧
    (bindX actualTwoFields selectedIdentity).facts =
      [xf ⟨y, [F, G], .exact, .conc T⟩] ∧
    (applySummaryX actualTwoFields (selectedField .star) Excl.empty identityResult).facts =
      [xf ⟨y, [F, G], .exact, .conc T⟩] := by decide

theorem selected_exact_cells_match_mathematically :
    insideB (selectedRoot .star) (demand .star) = true ∧
    satW (selectedRoot .star) actualRoot = true ∧
    insideB (selectedRoot (.conc T)) (demand (.conc T)) = true ∧
    satW (selectedRoot (.conc T)) actualRoot = true := by decide

/-- Only the current S8 guard is modeled here, not the entire typed grammar.
    Kotlin InitialAp and initialFacts separately reject abstract EXACT. -/
def currentS8 (i : PFact) : Bool :=
  match i.kind, i.mark with
  | .exact, .conc _ => true
  | .exact, _ => false
  | _, _ => true

theorem selected_abstract_exact_is_a_grammar_change :
    currentS8 (selectedRoot .star) = false ∧
    currentS8 (selectedRoot (.conc T)) = true := by decide

/-- Keep EXACT in the raw scalar start. This is a mathematical diagnostic,
    not a claim that current typed FlowTree can encode this new shape. -/
def exactFlowStart : XFact := xf (selectedRoot .star)
def widenedFlowStart : XFact := xf ⟨x, [], .star Excl.empty, .star⟩
def readChild : MicroEdge :=
  (⟨x, [F], .star Excl.empty, .star⟩, ⟨y, [], .star Excl.empty, .star⟩)
def spuriousResult : XFact := xf ⟨y, [], .any, .star⟩ true

theorem exact_must_not_silently_start_as_star :
    (bindX exactFlowStart readChild).facts = [] ∧
    (bindX widenedFlowStart readChild).facts = [spuriousResult] := by decide

def fromRoot : Loc := ⟨x, [], T⟩
def toRoot : Loc := ⟨y, [], T⟩

/-- The widened result admits a root-to-root pair that the field read has
    no such pair. Moving this result to DEMAND does not make the pair real. -/
theorem widening_adds_a_false_pair :
    den (selectedRoot .star) spuriousResult.af.fact fromRoot toRoot ∧
    ¬ den readChild.1 readChild.2 fromRoot toRoot := by
  constructor
  · exact ⟨rfl, rfl, True.intro, rfl, True.intro, [], [], rfl, rfl, rfl, True.intro⟩
  · rintro ⟨_, _, _, _, _, s, _, hs, _, _, _⟩
    simp [fromRoot, readChild] at hs

/-- A supplied root is not required to contain a child. Thus preserving
    abstract EXACT also matters before source/sink or summary processing. -/
theorem exact_does_not_authorize_child_location :
    (selectedRoot .star).covers fromRoot ∧
    ¬ (selectedRoot .star).covers ⟨x, [F], T⟩ := by
  constructor
  · exact ⟨rfl, ⟨[], rfl, rfl⟩, True.intro⟩
  · rintro ⟨_, ⟨s, hs, ht⟩, _⟩
    have empty : s = [] := ht
    rw [empty] at hs
    simp [selectedRoot] at hs

/-! A second application gap: this one yields a false NORMAL relation after
only the existing abstract-EXACT guards are relaxed. It is different from
the earlier DEMAND overapproximation caused by silently widening a start.

Current Reference.below, target EXACT and same path, returns target EXACT
with shape.demand=false. S8 makes an abstract EXACT edge unreachable today.
The old Lean belowCase instead uses STAR/Universe on STAR + EXACT -> EXACT.
Therefore bindX cannot stand in for the current Kotlin cell in this audit.
-/

def q : Base := 3
def callerPremise : PFact := ⟨q, [], .star Excl.empty, .star⟩
def callerAtX : XFact := xf ⟨x, [], .star Excl.empty, .star⟩
def exactRecordResult : XFact := xf ⟨y, [], .exact, .star⟩

/-- Exact scalar Kotlin below-cell after S8 relaxation, with this fixed
    EXACT/FLOW -> EXACT/FLOW record. This is not a proposed repaired rule. -/
def currentExactReplayAfterS8Relaxation (c : XFact) : Option XFact :=
  if Nat.beq c.af.fact.base x && c.af.fact.path == [] then
    some (xf ⟨y, [], .exact, c.af.fact.mark⟩
      (c.af.demand || exactRecordResult.af.demand))
  else none

def legacyExactReplay : XFact := xf ⟨y, [], .star .univ, .star⟩

theorem new_exact_record_reaches_the_unprotected_current_cell :
    satW (selectedRoot .star) callerAtX.af.fact = true ∧
    currentExactReplayAfterS8Relaxation callerAtX = some exactRecordResult ∧
    exactRecordResult.af.demand = false ∧
    (applySummaryX callerAtX (selectedRoot .star) Excl.empty exactRecordResult).facts =
      [legacyExactReplay] := by decide

def callerField : Loc := ⟨q, [F], T⟩

/-- Current unchanged target-EXACT application would infer q.F/T -> y/T
    NORMAL. The actual composition through the exact identity record has no
    such pair: that record accepts x.root only. -/
theorem relaxed_current_replay_adds_a_false_normal_pair :
    den callerPremise exactRecordResult.af.fact callerField toRoot ∧
    ¬ ∃ mid, den callerPremise callerAtX.af.fact callerField mid ∧
      den (selectedRoot .star) exactRecordResult.af.fact mid toRoot := by
  constructor
  · exact ⟨rfl, rfl, True.intro, rfl, True.intro, [F], [], rfl, rfl, rfl, rfl⟩
  · rintro ⟨mid, ⟨_, _, _, _, _, s, t, hs, ht, _, hc⟩,
      ⟨_, _, _, _, _, u, _, hu, _, hi, _⟩⟩
    have hs' : s = [F] := by simpa [callerField, callerPremise] using hs.symm
    have ht' : t = [F] := hc.1.trans hs'
    have midField : mid.path = [F] := by
      rw [ht'] at ht
      simpa [callerAtX, xf] using ht
    have hu' : u = [] := hi
    have midRoot : mid.path = [] := by
      rw [hu'] at hu
      simpa [selectedRoot] using hu
    rw [midRoot] at midField
    cases midField

def check : Bool :=
  satW (selectedField .star) actualField &&
  !satW (selectedField (.conc T)) actualField &&
  satW (selectedRoot .star) actualRoot &&
  selectedFlowFromExact x [] [F, G] == selectedField .star &&
  !currentS8 (selectedRoot .star) &&
  (bindX exactFlowStart readChild).facts == [] &&
  (bindX widenedFlowStart readChild).facts == [spuriousResult]

theorem checked : check = true := by decide

#eval check
#print axioms selected_flow_child_matches_current
#print axioms concrete_mark_mismatch_always_rejects
#print axioms selected_policy_cells
#print axioms selected_concrete_exact_child_matches_current
#print axioms uniform_abstract_must_needs_new_representation
#print axioms deeper_concrete_may_must_matching_gap
#print axioms coverage_matching_admits_deeper_concrete_must
#print axioms ordinary_concrete_matching_is_unchanged
#print axioms current_concrete_star_starts_demand
#print axioms concrete_star_start_cannot_make_normal
#print axioms demand_summary_application_cannot_make_normal
#print axioms rejected_concrete_star_child_matching_gap
#print axioms selected_prefix_covers_actual
#print axioms first_field_flow_identity_preserves_suffix
#print axioms selected_abstract_exact_is_a_grammar_change
#print axioms exact_must_not_silently_start_as_star
#print axioms widening_adds_a_false_pair
#print axioms relaxed_current_replay_adds_a_false_normal_pair

end ApSpec.InitialEmissionOneStep

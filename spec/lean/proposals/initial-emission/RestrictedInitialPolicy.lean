/-
  Restricted initial policy: FULL scalar, ordinary nonstatic bases, Empty E.
  Every modeled accessor is a counted field. Static anchors, ZERO, GROUP,
  mark exclusions and field exclusions require separate adapters/proofs.

  MUST is an explicit Boolean independent of an edge layer. Demand has no
  MUST tail. FLOW metadata is accepted only by a FLOW demand; it cannot
  supply a concrete full mark. Such metadata also permits structural image
  queries without inventing a concrete caller input.

  Pinned cells: precise STAR/EXACT demand emits only EXACT at its own path;
  a proper descendant does not apply. ANY demand resolves at most one new
  field, with the terminal concrete EXACT exception. Same-prefix supplied
  STAR emits nothing. Ancestor STAR for ANY demand also emits nothing:
  this last row is the stated inferred no-ANY/no-refinement interpretation.
  Ancestor ANY/MUST descends to the ANY demand path and retains its tail.

  No application/normal-record repair or abstract-tail transfer is selected
  in this file. It defines admission and proves its structural image.
-/
import ApSpec.CorrelatedConcreteImplementation

namespace RestrictedInitialPolicy
open ApSpec

inductive Shape where
  | exact | star | any
deriving DecidableEq, Repr

inductive Mark where
  | flow | full (id : Nat)
deriving DecidableEq, Repr

def shapeEq : Shape → Shape → Bool
  | .exact, .exact | .star, .star | .any, .any => true
  | _, _ => false

structure Demand where
  base : Nat
  path : List Acc
  shape : Shape
  mark : Mark
deriving DecidableEq, Repr

structure Input where
  base : Nat
  path : List Acc
  shape : Shape
  mark : Mark
  must : Bool
deriving DecidableEq, Repr

def fullMark : Mark → Bool
  | .full _ => true
  | .flow => false

def acceptsMark (required supplied : Mark) : Bool :=
  match required, supplied with
  | .flow, _ => true
  | .full t, .full u => Nat.beq t u
  | .full _, .flow => false

def validInput (a : Input) : Bool := !a.must || shapeEq a.shape .any

inductive Template where
  | rootExact
  | rootAny (must : Bool)
  | childStar (field : Acc)
  | childExact (field : Acc)
deriving DecidableEq, Repr

def render (d : Demand) : Template → Input
  | .rootExact => ⟨d.base, d.path, .exact, d.mark, false⟩
  | .rootAny must => ⟨d.base, d.path, .any, d.mark, must⟩
  | .childStar f => ⟨d.base, d.path ++ [f], .star, d.mark, false⟩
  | .childExact f => ⟨d.base, d.path ++ [f], .exact, d.mark, false⟩

def validTemplate (d : Demand) : Template → Bool
  | .rootExact => true
  | .rootAny _ | .childStar _ => shapeEq d.shape .any
  | .childExact _ => shapeEq d.shape .any && fullMark d.mark

def rawTemplate (d : Demand) (a : Input) : Option Template :=
  if validInput a && Nat.beq d.base a.base && acceptsMark d.mark a.mark then
    match d.shape, relate d.path a.path with
    | .any, .below [] =>
      match a.shape with
      | .exact => some .rootExact
      | .any => some (.rootAny a.must)
      | .star => none
    | .any, .below (f :: rest) =>
      if fullMark d.mark && shapeEq a.shape .exact && rest.isEmpty then
        some (.childExact f)
      else some (.childStar f)
    | .any, .above _ => if shapeEq a.shape .any then some (.rootAny a.must) else none
    | .any, .apart => none
    | _, .below [] => some .rootExact
    | _, .below (_ :: _) => none
    | _, .above _ => if shapeEq a.shape .exact then none else some .rootExact
    | _, .apart => none
  else none

/-- The explicit template validity check is a finite domain check, not an
    additional matching policy. rawTemplate's selected cells render these
    canonical templates only. -/
def selectTemplate (d : Demand) (a : Input) : Option Template :=
  match rawTemplate d a with
  | none => none
  | some t => if validTemplate d t then some t else none

def emit (d : Demand) (a : Input) : Option Input :=
  match selectTemplate d a with
  | none => none
  | some t => some (render d t)

theorem mark_accepts_itself (m : Mark) : acceptsMark m m = true := by
  cases m with
  | flow => rfl
  | full t => exact Nat.beq_refl t

theorem template_is_its_own_emission (d : Demand) (t : Template)
    (valid : validTemplate d t = true) :
    emit d (render d t) = some (render d t) := by
  have self : dropPrefix d.path d.path = some [] :=
    ApSpec.Handoff.RAux.dropPrefix_self' d.path
  cases d with
  | mk base path shape mark =>
    cases t with
    | rootExact =>
      cases shape <;> cases mark <;>
        simp only [emit, selectTemplate, rawTemplate, render, validInput, acceptsMark,
          relate, self, validTemplate, Nat.beq_refl, Bool.true_and, if_true,
          shapeEq, Bool.not_false, Bool.true_or]
    | rootAny must =>
      cases shape <;> simp [validTemplate, shapeEq] at valid
      cases mark <;>
        simp only [emit, selectTemplate, rawTemplate, render, validInput, acceptsMark,
          relate, self, validTemplate, Nat.beq_refl, Bool.true_and, if_true, Bool.or_true, shapeEq]
    | childStar f =>
      have hpath : dropPrefix path (path ++ [f]) = some [f] :=
        CoreAux.dropPrefix_some.mpr rfl
      cases shape <;> simp [validTemplate, shapeEq] at valid
      cases mark <;>
        simp only [emit, selectTemplate, rawTemplate, render, validInput, acceptsMark,
          relate, hpath, validTemplate, Nat.beq_refl, Bool.true_and, if_true, fullMark,
          shapeEq, Bool.not_false, Bool.true_or, Bool.false_and, Bool.false_eq_true, if_false]
    | childExact f =>
      have hpath : dropPrefix path (path ++ [f]) = some [f] :=
        CoreAux.dropPrefix_some.mpr rfl
      cases shape <;> simp [validTemplate, shapeEq] at valid
      cases mark <;> simp [fullMark] at valid
      simp only [emit, selectTemplate, rawTemplate, render, validInput, acceptsMark,
        relate, hpath, validTemplate, fullMark, Nat.beq_refl, Bool.true_and, if_true,
        shapeEq, Bool.not_false, Bool.true_or, List.isEmpty_nil]

theorem selected_template_is_valid (d : Demand) (a : Input) (t : Template)
    (h : selectTemplate d a = some t) : validTemplate d t = true := by
  unfold selectTemplate at h
  cases hr : rawTemplate d a with
  | none => simp only [hr] at h; cases h
  | some candidate =>
    rw [hr] at h
    cases hv : validTemplate d candidate with
    | false => simp only [hv, Bool.false_eq_true, if_false] at h; cases h
    | true =>
      simp only [hv, if_true, Option.some.injEq] at h
      rw [← h]
      exact hv

/-- Projection law for every emitted initial, not just the finite examples.
    This law is established from the canonical template constructors. -/
theorem emission_is_idempotent (d : Demand) (actual initial : Input)
    (h : emit d actual = some initial) : emit d initial = some initial := by
  cases hs : selectTemplate d actual with
  | none => simp only [emit, hs] at h; cases h
  | some t =>
    simp only [emit, hs, Option.some.injEq] at h
    rw [← h]
    exact template_is_its_own_emission d t (selected_template_is_valid d actual t hs)

def CanEmit (d : Demand) (initial : Input) : Prop :=
  ∃ actual, emit d actual = some initial

theorem emittable_iff_canonical_template (d : Demand) (initial : Input) :
    CanEmit d initial ↔ ∃ t, validTemplate d t = true ∧ render d t = initial := by
  constructor
  · rintro ⟨actual, emitted⟩
    cases hs : selectTemplate d actual with
    | none => simp only [emit, hs] at emitted; cases emitted
    | some t =>
      simp only [emit, hs, Option.some.injEq] at emitted
      exact ⟨t, selected_template_is_valid d actual t hs, emitted⟩
  · rintro ⟨t, valid, same⟩
    rw [← same]
    exact ⟨render d t, template_is_its_own_emission d t valid⟩

theorem emittable_iff_self_projection (d : Demand) (initial : Input) :
    CanEmit d initial ↔ emit d initial = some initial :=
  ⟨fun ⟨actual, h⟩ => emission_is_idempotent d actual initial h,
   fun h => ⟨initial, h⟩⟩

/-- Self-projection is complete here because idempotence was proved for the
    new total policy. It was not valid for the earlier partial policy. -/
def canEmit (d : Demand) (initial : Input) : Bool :=
  if emit d initial = some initial then true else false

theorem image_classifier_sound_and_complete (d : Demand) (initial : Input) :
    canEmit d initial = true ↔ CanEmit d initial := by
  unfold canEmit
  by_cases h : emit d initial = some initial
  · rw [if_pos h]
    exact ⟨fun _ => ⟨initial, h⟩, fun _ => rfl⟩
  · rw [if_neg h]
    constructor
    · intro impossible; cases impossible
    · intro emitted
      exact False.elim (h ((emittable_iff_self_projection d initial).mp emitted))

def entryMeet (d : Demand) (initial : Input) : Option Input :=
  if canEmit d initial then some initial else none

theorem entry_intersection_exactly_matches_emitter_image (d : Demand) (initial : Input) :
    entryMeet d initial = some initial ↔ CanEmit d initial := by
  constructor
  · intro h
    cases hc : canEmit d initial with
    | false => simp only [entryMeet, hc, Bool.false_eq_true, if_false] at h; cases h
    | true => exact (image_classifier_sound_and_complete d initial).mp hc
  · intro h
    have hc := (image_classifier_sound_and_complete d initial).mpr h
    simp only [entryMeet, hc, if_true]

theorem emitted_mark_is_demand_mark (d : Demand) (actual initial : Input)
    (h : emit d actual = some initial) : initial.mark = d.mark := by
  cases hs : selectTemplate d actual with
  | none => simp only [emit, hs] at h; cases h
  | some t =>
    simp only [emit, hs, Option.some.injEq] at h
    rw [← h]
    cases t <;> rfl

theorem emitted_input_has_valid_must_flag (d : Demand) (actual initial : Input)
    (h : emit d actual = some initial) : validInput initial = true := by
  cases hs : selectTemplate d actual with
  | none => simp only [emit, hs] at h; cases h
  | some t =>
    simp only [emit, hs, Option.some.injEq] at h
    rw [← h]
    cases t <;> simp only [validInput, render, shapeEq, Bool.or_true] <;> rfl

theorem different_full_marks_never_emit (db ab u t : Nat) (dp ap : List Acc)
    (ds ashape : Shape) (certainty : Bool) (different : u ≠ t) :
    emit ⟨db, dp, ds, .full u⟩ ⟨ab, ap, ashape, .full t, certainty⟩ = none := by
  have mismatch : Nat.beq u t = false := by
    cases hb : Nat.beq u t with
    | false => rfl
    | true => exact False.elim (different (Nat.eq_of_beq_eq_true hb))
  simp only [emit, selectTemplate, rawTemplate, acceptsMark, mismatch,
    Bool.and_false, Bool.false_eq_true, if_false]

def p : Nat := 1
def f : Acc := 7
def g : Acc := 8
def T : Mark := .full 1
def anyD : Demand := ⟨p, [], .any, T⟩
def preciseD : Demand := ⟨p, [f], .star, T⟩

theorem user_pinned_cells :
    emit preciseD ⟨p, [f, g], .exact, T, false⟩ = none ∧
    emit preciseD ⟨p, [f], .exact, T, false⟩ =
      some ⟨p, [f], .exact, T, false⟩ ∧
    emit anyD ⟨p, [], .star, T, false⟩ = none ∧
    emit ⟨p, [f], .any, .flow⟩ ⟨p, [], .any, T, false⟩ =
      some ⟨p, [f], .any, .flow, false⟩ := by decide

theorem any_demand_one_step_cells :
    emit anyD ⟨p, [f], .exact, T, false⟩ =
      some ⟨p, [f], .exact, T, false⟩ ∧
    emit anyD ⟨p, [f, g], .exact, T, false⟩ =
      some ⟨p, [f], .star, T, false⟩ ∧
    emit anyD ⟨p, [f, g], .any, T, true⟩ =
      some ⟨p, [f], .star, T, false⟩ ∧
    emit anyD ⟨p, [f], .star, T, false⟩ =
      some ⟨p, [f], .star, T, false⟩ := by decide

theorem same_prefix_and_ancestor_cells :
    emit ⟨p, [], .any, .flow⟩ ⟨p, [], .exact, T, false⟩ =
      some ⟨p, [], .exact, .flow, false⟩ ∧
    emit ⟨p, [], .any, .flow⟩ ⟨p, [], .any, T, true⟩ =
      some ⟨p, [], .any, .flow, true⟩ ∧
    emit ⟨p, [f], .any, .flow⟩ ⟨p, [], .any, T, true⟩ =
      some ⟨p, [f], .any, .flow, true⟩ ∧
    emit ⟨p, [f], .any, .flow⟩ ⟨p, [], .star, T, false⟩ = none ∧
    emit ⟨p, [f], .star, .flow⟩ ⟨p, [], .star, T, false⟩ =
      some ⟨p, [f], .exact, .flow, false⟩ := by decide

theorem image_false_positives_are_rejected :
    canEmit anyD ⟨p, [], .star, T, false⟩ = false ∧
    canEmit anyD ⟨p, [f, g], .exact, T, false⟩ = false ∧
    canEmit anyD ⟨p, [f], .any, T, false⟩ = false ∧
    canEmit anyD ⟨p, [f], .any, T, true⟩ = false ∧
    canEmit preciseD ⟨p, [f], .star, T, false⟩ = false ∧
    canEmit anyD ⟨p, [f], .star, T, false⟩ = true := by decide

theorem failed_matches_do_not_emit :
    emit anyD ⟨p, [f], .exact, .full 2, false⟩ = none ∧
    emit anyD ⟨p, [f], .exact, .flow, false⟩ = none ∧
    emit anyD ⟨2, [], .any, T, false⟩ = none ∧
    emit ⟨p, [f], .any, T⟩ ⟨p, [g], .exact, T, false⟩ = none ∧
    emit ⟨p, [f], .any, T⟩ ⟨p, [], .exact, T, false⟩ = none := by decide

def toAp (initial : Input) : PFact :=
  ⟨initial.base, initial.path,
    (match initial.shape with | .exact => .exact | .star => .star Excl.empty | .any => .any),
    (match initial.mark with | .flow => .star | .full t => .conc t)⟩

theorem concrete_star_uses_current_demand_start (b : Nat) (path : List Acc) (t : Nat) :
    (ApSpec.Run1CorrelatedConcreteInitials.selectedStart
      (toAp ⟨b, path, .star, .full t, false⟩)).demand = true := rfl

def check : Bool :=
  canEmit anyD ⟨p, [f], .star, T, false⟩ &&
  !canEmit anyD ⟨p, [f, g], .exact, T, false⟩ &&
  !canEmit preciseD ⟨p, [f], .star, T, false⟩

theorem checked : check = true := by decide

#eval check
#print axioms template_is_its_own_emission
#print axioms emission_is_idempotent
#print axioms emittable_iff_canonical_template
#print axioms image_classifier_sound_and_complete
#print axioms entry_intersection_exactly_matches_emitter_image
#print axioms different_full_marks_never_emit
#print axioms emitted_mark_is_demand_mark
#print axioms concrete_star_uses_current_demand_start

end RestrictedInitialPolicy

/-
  Closed finite trace for the proposed EXACT/FLOW domain. All nonzero boundary
  inputs below come from the declared source, sink seeds, bindings or selected
  emission; the helper exact record is not assumed present.

  main: source(q.f.h); sinkAny(q.f.h); sinkExact(H(q));
        pair=W(q); sinkExact(pair.a); sinkAny(pair.b)
  H(p): return p.f
  W(q): a=H(q); b=opaqueMay(q); returnPair(a,b)
  Latest modeled iteration: run-3; field limits are 1, 1, 2.

  All calls use one shared method context per method. Fields are counted.
  E/mx are empty; there are no aliases, ND rules, type filters or statics.
  The finite principal FLOW basis is explicit. ZERO is preserved. A record
  application cell is modeled as current Kotlin would compute it after only
  S8's new abstract-EXACT guards were relaxed. It is not a current-JVM bug.
  Existing bindX is not used for that cell: its old STAR/Universe row differs.
-/
namespace RestrictedInitialPolicy.ClosedExactReplay
open ApSpec ApSpec.AnyTaintEx ApSpec.Handoff ApSpec.Abs

def mq : Base := 10
def pair : Base := 11
def probe : Base := 12
def wq : Base := 20
def wa : Base := 21
def wb : Base := 22
def wr : Base := 23
def hp : Base := 30
def hr : Base := 31
def F : Acc := 7
def H : Acc := 8
def A : Acc := 9
def B : Acc := 10
def atom : ApSpec.Mark := 1

def flow (b : Base) (path : List Acc := []) (kind : Kind := .star Excl.empty) : PFact :=
  ⟨b, path, kind, .star⟩
def marked (b : Base) (path : List Acc) (kind : Kind) : PFact := ⟨b, path, kind, .conc atom⟩
def xf (fact : PFact) (demand : Bool := false) : XFact := ⟨⟨fact, demand⟩, Excl.empty⟩
def move (src dst : Base) (fromPath toPath : List Acc := []) : MicroEdge :=
  (flow src fromPath, flow dst toPath)
def step (edge : MicroEdge) (inputs : List XFact) : List XFact :=
  inputs.flatMap fun input => (bindX input edge).facts
def limitAt (n : Nat) (inputs : List XFact) : List XFact :=
  inputs.map (limitFX (fun _ => true) n)

def asInput (fact : PFact) (must : Bool := false) : Input :=
  ⟨fact.base, fact.path,
    (match fact.kind with | .exact => .exact | .star _ => .star | .any => .any),
    (match fact.mark with | .conc t => .full t | _ => .flow), must⟩
def asDemand (fact : PFact) : Demand :=
  ⟨fact.base, fact.path,
    (match fact.kind with | .exact => .exact | .star _ => .star | .any => .any),
    (match fact.mark with | .conc t => .full t | _ => .flow)⟩
def start (initial : Input) : XFact :=
  if initial.must then xf (toAp initial) else
    ⟨ApSpec.Run1CorrelatedConcreteInitials.selectedStart (toAp initial), Excl.empty⟩
def initials (d : Demand) (inputs : List XFact) (must : Bool := false) : List XFact :=
  inputs.flatMap fun input =>
    (emit d (asInput input.af.fact must)).toList.map start

abbrev Row := PFact × XFact
def zeroRow : Row := (zeroFact, xf zeroFact)
def analyze (initials : List XFact) (body : List XFact → List XFact) : List Row :=
  initials.flatMap fun initial => (body [initial]).map fun result => (initial.af.fact, result)
def applyRows (rows : List Row) (inputs : List XFact) : List XFact :=
  inputs.flatMap fun actual => rows.flatMap fun row =>
    (applySummaryX actual row.1 Excl.empty row.2).facts
def normalNonzero (rows : List Row) : List Row :=
  rows.filter fun row => !row.2.af.demand && !(Nat.beq row.1.base zeroBase)
def nextDemand (rows : List Row) : List DemandEdge :=
  (rows.filter fun row => row.2.af.demand).map fun row => normDem ⟨row.2.af.fact, some row.1⟩
def c5 (d : DemandEdge) (row : Row) : Option Row :=
  if canEmit (asDemand d.din) (asInput row.1) then
    (restrictI row.1 row.2.af d).map fun result => (row.1, plain result)
  else none
def publish (demands : List DemandEdge) (rows : List Row) : List Row :=
  rows.flatMap fun row => demands.filterMap fun d => c5 d row
def admitted (demands : List DemandEdge) (inputs : List XFact) (must : Bool := false) : List XFact :=
  demands.flatMap fun d => initials (asDemand d.din) inputs must
def reverseRow (row : Row) : Row :=
  let edge := revEdge row.1 row.2.af.fact
  (edge.1, xf edge.2 row.2.af.demand)

def sourceEdge : MicroEdge := (zeroFact, marked mq [F, H] .any)
def sourceAll : List XFact := step sourceEdge [xf zeroFact]
def source1 : List XFact := limitAt 1 (sourceAll.map fun x => xf x.af.fact true)
def sinkSource : PFact := marked mq [F, H] .any
def sinkProbe : PFact := marked probe [] .exact
def sinkA : PFact := marked pair [A] .exact
def sinkB : PFact := marked pair [B] .any
def observed (facts : List XFact) (sink : PFact) : Bool :=
  facts.any fun fact => checkX zeroFact fact sink == .triggered

def hRead : MicroEdge := move hp hr [F] []
def hBind : MicroEdge := move mq hp [] []
def wBind : MicroEdge := move mq wq [] []
def whBind : MicroEdge := move wq hp [] []
def hBack : MicroEdge := move hr wa [] []
def probeBack : MicroEdge := move hr probe [] []
def wBack : MicroEdge := move wr pair [] []
def pairA : MicroEdge := move wa wr [] [A]
def pairB : MicroEdge := move wb wr [] [B]
def opaqueEdge : MicroEdge := (flow wq, flow wb [] .any)

/-- Repeated ZERO frames are not expanded in each principal nonzero basis.
    These declarations cannot turn ZERO into a helper/wrapper data result. -/
theorem zero_frames_do_not_add_a_hidden_return_cover :
    step (zeroFact, zeroFact) [xf zeroFact] = [xf zeroFact] ∧
    step hRead [xf zeroFact] = [] ∧
    step (revEdge hRead.1 hRead.2) [xf zeroFact] = [] ∧
    (applyEdgeXT (fun _ => false) (xf zeroFact) opaqueEdge).facts = [] ∧
    step pairA [xf zeroFact] = [] ∧ step pairB [xf zeroFact] = [] := by decide

def run1States (inputs : List XFact) : List XFact :=
  inputs.map fun input => xf (flow input.af.fact.base)
def h1Initials : List XFact := run1States (step hBind source1)
def h1Rows : List Row :=
  [zeroRow] ++ analyze h1Initials (fun xs => xs ++ step hRead xs)
def w1Initials : List XFact := run1States (step wBind source1)
def viaH1 (xs : List XFact) : List XFact :=
  step pairA (step hBack (applyRows h1Rows (step whBind xs)))
def viaOpaque (xs : List XFact) : List XFact :=
  step pairB (xs.flatMap fun x => (applyEdgeXT (fun _ => false) x opaqueEdge).facts)
def w1Rows : List Row :=
  [zeroRow] ++ analyze w1Initials (fun xs => xs ++ viaH1 xs ++ viaOpaque xs)
def mainProbe1 : List XFact := step probeBack (applyRows h1Rows (step hBind source1))
def mainPair1 : List XFact := step wBack (applyRows w1Rows (step wBind source1))
def h2Demands : List DemandEdge := nextDemand h1Rows
def w2Demands : List DemandEdge := nextDemand w1Rows

theorem run1_reports_and_frontiers_are_derived :
    source1 = [xf (marked mq [F] .any) true] ∧
    observed source1 sinkSource = true ∧
    observed mainProbe1 sinkProbe = true ∧
    observed mainPair1 sinkA = true ∧ observed mainPair1 sinkB = true ∧
    h2Demands = [⟨flow hr [] .any, some (flow hp)⟩] ∧
    w2Demands = [⟨flow wr [A] .any, some (flow wq)⟩,
      ⟨flow wr [B] .any, some (flow wq)⟩] := by decide

def backwardSeed (sink : PFact) : List XFact := limitAt 1 [xf sink true]
def sourceHits2 : List XFact := step (revEdge sourceEdge.1 sourceEdge.2) (backwardSeed sinkSource)
def sourceSelected : Bool := sourceHits2.any fun hit => Nat.beq hit.af.fact.base zeroBase
def source3 : List XFact := if sourceSelected then limitAt 2 sourceAll else []
def directProbe2 : List XFact :=
  step (revEdge probeBack.1 probeBack.2) (backwardSeed sinkProbe)
def h2Initials : List XFact := admitted h2Demands directProbe2
def h2Raw : List Row := analyze h2Initials (step (revEdge hRead.1 hRead.2))
def h2Published : List Row := publish h2Demands h2Raw
def h2Records : List Row := normalNonzero h2Raw

theorem source_and_helper_record_are_constructed :
    sourceHits2 = [xf zeroFact true] ∧ sourceSelected = true ∧
    source3 = [xf (marked mq [F, H] .any)] ∧
    directProbe2 = [xf (marked hr [] .exact) true] ∧
    h2Initials = [xf (flow hr [] .exact)] ∧
    h2Raw = [(flow hr [] .exact, xf (flow hp [F] .exact))] ∧
    h2Published = h2Raw ∧ h2Records = h2Raw := by decide

def wActualA2 : List XFact := step (revEdge wBack.1 wBack.2) (backwardSeed sinkA)
def wActualB2 : List XFact := step (revEdge wBack.1 wBack.2) (backwardSeed sinkB)
def wAInitial2 : List XFact := admitted w2Demands wActualA2
def wBInitial2 : List XFact := admitted w2Demands wActualB2
def wStandingH2 (xs : List XFact) : List XFact :=
  step (revEdge hBack.1 hBack.2) (step (revEdge pairA.1 pairA.2) xs)
def wBackwardA (xs : List XFact) : List XFact :=
  step (revEdge whBind.1 whBind.2) (applyRows h2Published (wStandingH2 xs))
def wBackwardB (xs : List XFact) : List XFact :=
  let beforeOpaque := step (revEdge opaqueEdge.1 opaqueEdge.2) (step (revEdge pairB.1 pairB.2) xs)
  step (move wq wq [] []) beforeOpaque
def w2Raw : List Row := analyze wAInitial2 wBackwardA ++ analyze wBInitial2 wBackwardB
def w2Published : List Row := publish w2Demands w2Raw
def w2Records : List Row := normalNonzero w2Raw
def h3Demands : List DemandEdge := nextDemand h2Published
def w3Demands : List DemandEdge := nextDemand w2Published
def w3Initials : List XFact := admitted w3Demands (step wBind source3) true
def h3Added : List XFact := step whBind w3Initials
def h3Initials : List XFact := admitted h3Demands h3Added

theorem wrapper_backward_and_run3_input_are_constructed :
    wAInitial2 = [xf (flow wr [A] .exact)] ∧
    wBInitial2 = [xf (flow wr [B] .any) true] ∧
    wStandingH2 wAInitial2 = [xf (flow hr [] .exact)] ∧
    w2Raw = [(flow wr [A] .exact, xf (flow wq [F] .exact)),
      (flow wr [B] .any, xf (flow wq [] .any) true)] ∧
    w2Published = w2Raw ∧
    w2Records = [(flow wr [A] .exact, xf (flow wq [F] .exact))] ∧
    h3Demands = [] ∧
    w3Demands = [⟨flow wq [] .any, some (flow wr [B] .any)⟩] ∧
    w3Initials = [xf (flow wq [F])] ∧
    h3Added = [xf (flow hp [F])] ∧ h3Initials = [] := by decide

def h3Views : List Row := h2Records.map reverseRow
def availableHelperRows3 : List Row := normalNonzero h1Rows ++ h3Views
def normalStarReturnCover (row : Row) : Bool :=
  !row.2.af.demand && row.1 == flow hp [F] && row.2.af.fact == flow hr

theorem no_covering_helper_relation_is_assumed :
    h3Views = [(flow hp [F] .exact, xf (flow hr [] .exact))] ∧
    availableHelperRows3 = [(flow hp, xf (flow hp)),
      (flow hp [F] .exact, xf (flow hr [] .exact))] ∧
    (availableHelperRows3.any normalStarReturnCover) = false ∧
    satW (flow hp [F] .exact) (flow hp [F]) = true ∧
    satW (flow wq [F] .exact) (marked wq [F, H] .any) = false := by decide

/-- Same-path target-EXACT row of current Kotlin Reference.below/compose,
    after the abstract EXACT guards alone are relaxed. The legacy Lean
    STAR/Universe row is deliberately not substituted for this current cell. -/
def currentExactReplay (actual : XFact) (record : Row) : List XFact :=
  if Nat.beq actual.af.fact.base record.1.base &&
      actual.af.fact.path == record.1.path && record.1.kind == .exact &&
      record.2.af.fact.kind == .exact then
    match markGate record.1.mark actual.af.fact.mark with
    | .ok =>
      match markComp record.2.af.fact.mark actual.af.fact.mark with
      | none => []
      | some mark => [xf ⟨record.2.af.fact.base, record.2.af.fact.path, .exact, mark⟩
          (actual.af.demand || record.2.af.demand)]
    | _ => []
  else []

def replayHelper3 (inputs : List XFact) : List XFact :=
  inputs.flatMap fun actual => h3Views.flatMap fun record =>
    if satW record.1 actual.af.fact then currentExactReplay actual record else []
def viaBadH3 (xs : List XFact) : List XFact :=
  step pairA (step hBack (replayHelper3 (step whBind xs)))
def w3Raw : List Row :=
  analyze w3Initials (fun xs => xs ++ viaBadH3 xs ++ viaOpaque xs)
def w3Published : List Row := publish w3Demands w3Raw
def w3Records : List Row := normalNonzero w3Raw
def wrongRow : Row := (flow wq [F], xf (flow wr [A] .exact))

theorem false_normal_row_is_raw_and_persisted_but_not_published :
    viaBadH3 w3Initials = [xf (flow wr [A] .exact)] ∧
    w3Raw = [(flow wq [F], xf (flow wq [F])), wrongRow,
      (flow wq [F], xf (flow wr [B] .any) true)] ∧
    w3Published = [(flow wq [F], xf (flow wr [B] .any) true)] ∧
    wrongRow ∈ w3Records ∧ wrongRow ∉ w3Published := by decide

def concreteHPath : List XFact :=
  step pairA (step hBack (step hRead (step whBind [xf (marked wq [F, H] .exact)])))
def realInput : Loc := ⟨wq, [F, H], atom⟩
def falseOutput : Loc := ⟨wr, [A], atom⟩
def realReturnRelation : PFact := flow wr [A]

theorem concrete_program_keeps_the_suffix :
    concreteHPath = [xf (marked wr [A, H] .exact)] := by decide

theorem persisted_normal_has_a_false_pair :
    den wrongRow.1 wrongRow.2.af.fact realInput falseOutput ∧
    ¬ den wrongRow.1 realReturnRelation realInput falseOutput := by
  constructor
  · exact ⟨rfl, rfl, True.intro, rfl, True.intro, [H], [], rfl, rfl, rfl, rfl⟩
  · rintro ⟨_, _, _, _, _, suffix, outSuffix, hs, ht, _, hc⟩
    have hs' : suffix = [H] := by simpa [wrongRow, flow, realInput] using hs.symm
    have ht' : outSuffix = [] := by simpa [realReturnRelation, flow, falseOutput] using ht.symm
    have same : outSuffix = suffix := hc.1
    rw [hs', ht'] at same
    cases same

/-- The other declared wrapper outputs cannot explain the false A-root pair:
    the argument frame has another base, and opaqueMay reaches B only. -/
theorem other_wrapper_paths_do_not_supply_false_a :
    ¬ den wrongRow.1 (flow wq [F]) realInput falseOutput ∧
    ¬ den wrongRow.1 (flow wr [B] .any) realInput falseOutput := by
  constructor
  · rintro ⟨_, outputBase, _⟩
    change (23 : Nat) = 20 at outputBase
    cases outputBase
  · rintro ⟨_, _, _, _, _, _, outSuffix, _, outputPath, _, _⟩
    simp [falseOutput, flow, A, B] at outputPath

theorem false_normal_pair_is_absent_from_declared_wrapper_relation :
    den wrongRow.1 wrongRow.2.af.fact realInput falseOutput ∧
    ¬ (den wrongRow.1 (flow wq [F]) realInput falseOutput ∨
      den wrongRow.1 realReturnRelation realInput falseOutput ∨
      den wrongRow.1 (flow wr [B] .any) realInput falseOutput) := by
  refine ⟨persisted_normal_has_a_false_pair.1, ?_⟩
  intro alternative
  cases alternative with
  | inl frame => exact other_wrapper_paths_do_not_supply_false_a.1 frame
  | inr returns =>
    cases returns with
    | inl helper => exact persisted_normal_has_a_false_pair.2 helper
    | inr model => exact other_wrapper_paths_do_not_supply_false_a.2 model

def check : Bool :=
  sourceSelected && observed mainProbe1 sinkProbe &&
  (h3Demands == []) && (h3Initials == []) &&
  !(availableHelperRows3.any normalStarReturnCover) &&
  w3Raw.contains wrongRow && w3Records.contains wrongRow && !w3Published.contains wrongRow

theorem checked : check = true := by decide

#eval check
#print axioms source_and_helper_record_are_constructed
#print axioms wrapper_backward_and_run3_input_are_constructed
#print axioms no_covering_helper_relation_is_assumed
#print axioms false_normal_row_is_raw_and_persisted_but_not_published
#print axioms persisted_normal_has_a_false_pair
#print axioms false_normal_pair_is_absent_from_declared_wrapper_relation

end RestrictedInitialPolicy.ClosedExactReplay

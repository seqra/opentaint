/-
  Computed backward read views for three normal, singleton forward shapes.

  Exact concrete premise -> normal must conclusion/E:
    reverse premise STAR/E with the conclusion mark; exact old premise as
    output. This is the exact annotated converse and discards input suffixes.
  Must premise -> normal must conclusion/E:
    the same reverse premise, but the old must premise becomes may ANY and
    the output is DEMAND. Its old must-input exclusion is forgotten.
  Must premise -> normal exact conclusion:
    ordinary exact-to-ANY reversal, with a DEMAND output.

  The reader rejects demand input records, nonconcrete marks, native STAR
  premises, and malformed exact annotations. It is a partial reader for these
  shapes, not a replacement for generic revEdge. Native records are not changed.
  No current annotated-closure, handoff-coverage or iteration claim follows.
-/
import ApSpec.AbsDefs
import ApSpec.AnyTaintExact
import ApSpec.AnyTaintExDefs
import ApSpec.HandoffXRestrict

namespace ApSpec.CurrentMustReverse
open ApSpec ApSpec.Reverse ApSpec.Abs ApSpec.AnyTaintEx ApSpec.Handoff

/-- The caller supplies a native R1/S14 singleton record. This carrier does
    not prove store provenance or summary cardinality. readView checks normal
    and concrete shapes; the must flag gives the forward meaning of ANY. -/
structure NativeRecord where
  premise : PFact
  premiseMust : Bool
  premiseEx : Excl
  conclusion : XFact
deriving DecidableEq, Repr

abbrev ReadView := PFact × AFact

/-- Only the listed new read shapes are accepted. Other native record shapes
    still use their existing reader. The output layer is part of the view. -/
def readView (r : NativeRecord) : Option ReadView :=
  if r.conclusion.af.demand then none else
    match r.premise.kind, r.premiseMust, r.premise.mark,
        r.conclusion.af.fact.kind, r.conclusion.af.fact.mark with
    | .exact, false, .conc _, .any, .conc _ =>
      if r.premiseEx == Excl.empty then
        some (⟨r.conclusion.af.fact.base, r.conclusion.af.fact.path,
          .star r.conclusion.ex, r.conclusion.af.fact.mark⟩, ⟨r.premise, false⟩)
      else none
    | .any, true, .conc _, .any, .conc _ =>
      some (⟨r.conclusion.af.fact.base, r.conclusion.af.fact.path,
        .star r.conclusion.ex, r.conclusion.af.fact.mark⟩, ⟨r.premise, true⟩)
    | .any, true, .conc _, .exact, .conc _ =>
      if r.conclusion.ex == Excl.empty then
        some ((revEdge r.premise r.conclusion.af.fact).1,
          ⟨(revEdge r.premise r.conclusion.af.fact).2, true⟩)
      else none
    | _, _, _, _, _ => none

/-- Additional forward reuse eligibility, decided on the raw native record.
    A successful demand read view is not sufficient to omit backward demand. -/
def omitMustDemand (r : NativeRecord) : Bool :=
  if r.conclusion.af.demand then false else
    match r.premise.kind, r.premiseMust, r.premise.mark,
        r.conclusion.af.fact.kind, r.conclusion.af.fact.mark with
    | .exact, false, .conc _, .any, .conc _ => r.premiseEx == Excl.empty
    | _, _, _, _, _ => false

/-- The corresponding explicit local native guards. Singleton provenance and
    R1/S14 remain the caller's obligations, as for readView. -/
def exactMustGuardsB (r : NativeRecord) : Bool :=
  !r.conclusion.af.demand && !r.premiseMust &&
    (r.premise.kind == .exact) && concB r.premise.mark &&
    (r.premiseEx == Excl.empty) && (r.conclusion.af.fact.kind == .any) &&
    concB r.conclusion.af.fact.mark

def normalReadB : Option ReadView → Bool
  | none => false
  | some v => !v.2.demand

theorem omit_eq_guardsB (r : NativeRecord) : omitMustDemand r = exactMustGuardsB r := by
  obtain ⟨⟨_, _, pk, pm⟩, must, jex, ⟨⟨⟨_, _, xk, xm⟩, dm⟩, ex⟩⟩ := r
  cases dm <;> cases must <;> cases pk <;> cases pm <;> cases xk <;> cases xm <;>
    simp [omitMustDemand, exactMustGuardsB, concB]

theorem omit_eq_normal_read (r : NativeRecord) :
    omitMustDemand r = normalReadB (readView r) := by
  obtain ⟨⟨_, _, pk, pm⟩, must, jex, ⟨⟨⟨_, _, xk, xm⟩, dm⟩, ex⟩⟩ := r
  cases dm <;> cases must <;> cases pk <;> cases pm <;> cases xk <;> cases xm <;>
    simp [omitMustDemand, readView, normalReadB]
  all_goals by_cases hj : jex = Excl.empty <;> by_cases hx : ex = Excl.empty <;>
    simp [hj, hx]

/-- Existing generic reuse is extended only by the new normal exact-to-must
    view. Generic Cross and generic revEdge are unchanged. -/
def RawReusable (raw : NativeRecord) : Prop :=
  Cross raw.premise raw.conclusion.af ∨ omitMustDemand raw = true

def RawDemand (raw : NativeRecord) : Prop := ¬ RawReusable raw

/-- Publication keeps this new branch's raw selection bit beside each reduced
    piece. It does not run the selector on that piece. The overall reusable
    classifier additionally includes the existing generic Cross branch. -/
def publicationPlan (raw : NativeRecord) (piece : XFact) : Bool × XFact :=
  (omitMustDemand raw, piece)

theorem publication_keeps_raw_selection (raw : NativeRecord) (piece : XFact) :
    (publicationPlan raw piece).1 = omitMustDemand raw ∧
    (publicationPlan raw piece).2 = piece := ⟨rfl, rfl⟩

theorem publication_selection_independent (raw : NativeRecord) (a b : XFact) :
    (publicationPlan raw a).1 = (publicationPlan raw b).1 := rfl

/-- The returned value is the actual computed reader result. -/
structure ViewCertificate (r : NativeRecord) where
  view : ReadView
  computed : readView r = some view

def exactNative (pb xb : Base) (pp xp : List Acc) (u t : Mark) (e : Excl) : NativeRecord :=
  ⟨⟨pb, pp, .exact, .conc u⟩, false, Excl.empty,
    ⟨⟨⟨xb, xp, .any, .conc t⟩, false⟩, e⟩⟩

/-- Selection is uniform over base, path, both concrete marks and output E. -/
theorem omit_exactNative (pb xb : Base) (pp xp : List Acc) (u t : Mark) (e : Excl) :
    omitMustDemand (exactNative pb xb pp xp u t e) = true := rfl

def exactCertificate (pb xb : Base) (pp xp : List Acc) (u t : Mark) (e : Excl) :
    ViewCertificate (exactNative pb xb pp xp u t e) :=
  ⟨(⟨xb, xp, .star e, .conc t⟩, ⟨⟨pb, pp, .exact, .conc u⟩, false⟩), rfl⟩

def mustAnyNative (pb xb : Base) (pp xp : List Acc) (u t : Mark)
    (inputEx outputEx : Excl) : NativeRecord :=
  ⟨⟨pb, pp, .any, .conc u⟩, true, inputEx,
    ⟨⟨⟨xb, xp, .any, .conc t⟩, false⟩, outputEx⟩⟩

def mustAnyCertificate (pb xb : Base) (pp xp : List Acc) (u t : Mark)
    (inputEx outputEx : Excl) :
    ViewCertificate (mustAnyNative pb xb pp xp u t inputEx outputEx) :=
  ⟨(⟨xb, xp, .star outputEx, .conc t⟩, ⟨⟨pb, pp, .any, .conc u⟩, true⟩), rfl⟩

def mustExactNative (pb xb : Base) (pp xp : List Acc) (u t : Mark)
    (inputEx : Excl) : NativeRecord :=
  ⟨⟨pb, pp, .any, .conc u⟩, true, inputEx,
    ⟨⟨⟨xb, xp, .exact, .conc t⟩, false⟩, Excl.empty⟩⟩

def mustExactCertificate (pb xb : Base) (pp xp : List Acc) (u t : Mark) (inputEx : Excl) :
    ViewCertificate (mustExactNative pb xb pp xp u t inputEx) :=
  ⟨(⟨xb, xp, .exact, .conc t⟩, ⟨⟨pb, pp, .any, .conc u⟩, true⟩), rfl⟩

/-- Exact premise: the view is exactly the annotated converse for every
    location and mark. Even a redundant old exact-premise annotation is inert. -/
theorem exact_converse {pb xb : Base} {pp xp : List Acc} {u t : Mark}
    {inputEx outputEx : Excl} {l0 l1 : Loc} :
    denX ⟨pb, pp, .exact, .conc u⟩ inputEx ⟨xb, xp, .any, .conc t⟩ outputEx l0 l1 ↔
    den ⟨xb, xp, .star outputEx, .conc t⟩ ⟨pb, pp, .exact, .conc u⟩ l1 l0 := by
  constructor
  · rintro ⟨hb0, hb1, hm0, hm1, _, σ, τ, hp0, hp1, hi, _, _, he⟩
    have hσ : σ = [] := hi
    have hu : l0.mark = u := hm0
    have ht : l1.mark = t := hm1
    refine ⟨hb1, hb0, ht, hu, trivial, τ, [], hp1, ?_, he, rfl⟩
    rw [hσ] at hp0
    exact hp0
  · rintro ⟨hb1, hb0, hm1, hm0, _, τ, σ, hp1, hp0, he, hf⟩
    have hσ : σ = [] := hf
    refine ⟨hb0, hb1, hm0, hm1, trivial, [], τ, ?_, hp1, rfl, trivial,
      CoreAux.admits_nil inputEx, he⟩
    rw [hσ] at hp0
    exact hp0

/-- The selected actual read value is an exact annotated converse. -/
theorem selected_view_converse {r : NativeRecord} {v : ReadView}
    (selected : omitMustDemand r = true) (computed : readView r = some v) (l0 l1 : Loc) :
    denX r.premise r.premiseEx r.conclusion.af.fact r.conclusion.ex l0 l1 ↔
      den v.1 v.2.fact l1 l0 := by
  obtain ⟨⟨pb, pp, pk, pm⟩, must, jex, ⟨⟨⟨xb, xp, xk, xm⟩, dm⟩, ex⟩⟩ := r
  cases dm <;> cases must <;> cases pk <;> cases pm <;> cases xk <;> cases xm <;>
    simp [omitMustDemand] at selected
  subst jex
  simp [readView] at computed
  cases computed
  exact exact_converse

structure NormalMustWitness (r : NativeRecord) where
  view : ReadView
  computed : readView r = some view
  normal : view.2.demand = false
  converse : ∀ l0 l1, denX r.premise r.premiseEx
    r.conclusion.af.fact r.conclusion.ex l0 l1 ↔ den view.1 view.2.fact l1 l0

/-- The selected view is extracted by evaluating readView, not by choosing
    a value from an existential proposition. -/
def normalMustWitness (r : NativeRecord) (selected : omitMustDemand r = true) :
    NormalMustWitness r :=
  match he : readView r with
  | some v =>
    ⟨v, he, by
      have h := (omit_eq_normal_read r).symm.trans selected
      rw [he] at h
      cases hd : v.2.demand <;> simp [normalReadB, hd] at h ⊢,
      fun _ _ => selected_view_converse selected he _ _⟩
  | none => False.elim (by
      have h := (omit_eq_normal_read r).symm.trans selected
      rw [he] at h
      cases h)

theorem omit_iff_normal_view {r : NativeRecord} :
    omitMustDemand r = true ↔ ∃ v, readView r = some v ∧ v.2.demand = false := by
  constructor
  · intro h
    let w := normalMustWitness r h
    exact ⟨w.view, w.computed, w.normal⟩
  · rintro ⟨v, hv, hn⟩
    rw [omit_eq_normal_read, hv]
    simp [normalReadB, hn]

theorem exactCertificate_converse (pb xb : Base) (pp xp : List Acc) (u t : Mark)
    (e : Excl) (l0 l1 : Loc) :
    denX (exactNative pb xb pp xp u t e).premise Excl.empty
        (exactNative pb xb pp xp u t e).conclusion.af.fact e l0 l1 ↔
      den (exactCertificate pb xb pp xp u t e).view.1
        (exactCertificate pb xb pp xp u t e).view.2.fact l1 l0 := exact_converse

/-- The computed view places the old must conclusion exclusion on its new
    premise; a normal exact output keeps the old premise, not the input suffix. -/
theorem exact_shape (pb xb : Base) (pp xp : List Acc) (u t : Mark) (e : Excl) :
    (exactCertificate pb xb pp xp u t e).view.1 = ⟨xb, xp, .star e, .conc t⟩ ∧
    (exactCertificate pb xb pp xp u t e).view.2 = ⟨⟨pb, pp, .exact, .conc u⟩, false⟩ :=
  ⟨rfl, rfl⟩

/-- Dropping a must-input annotation can enlarge the backward may result, but
    every original annotated pair is covered by the new must-output view. -/
theorem must_any_converse_covers {pb xb : Base} {pp xp : List Acc} {u t : Mark}
    {inputEx outputEx : Excl} {l0 l1 : Loc}
    (h : denX ⟨pb, pp, .any, .conc u⟩ inputEx
      ⟨xb, xp, .any, .conc t⟩ outputEx l0 l1) :
    den ⟨xb, xp, .star outputEx, .conc t⟩ ⟨pb, pp, .any, .conc u⟩ l1 l0 := by
  obtain ⟨hb0, hb1, hm0, hm1, _, σ, τ, hp0, hp1, _, _, _, he⟩ := h
  exact ⟨hb1, hb0, hm1, hm0, trivial, τ, σ, hp1, hp0, he, trivial⟩

theorem must_exact_converse_covers {pb xb : Base} {pp xp : List Acc} {u t : Mark}
    {inputEx : Excl} {l0 l1 : Loc}
    (h : denX ⟨pb, pp, .any, .conc u⟩ inputEx
      ⟨xb, xp, .exact, .conc t⟩ Excl.empty l0 l1) :
    den ⟨xb, xp, .exact, .conc t⟩ ⟨pb, pp, .any, .conc u⟩ l1 l0 := by
  obtain ⟨hb0, hb1, hm0, hm1, _, σ, τ, hp0, hp1, _, ht, _, _⟩ := h
  exact ⟨hb1, hb0, hm1, hm0, trivial, τ, σ, hp1, hp0, ht, trivial⟩

/-- An admitted exact field requirement matches and returns the old exact
    premise. The result path never incorporates the backward suffix. -/
theorem exact_transfer (pb xb : Base) (pp xp suffix : List Acc) (u t : Mark)
    (e : Excl) (admitted : e.admits suffix = true) :
    applicable ⟨xb, xp, .star e, .conc t⟩ ⟨xb, xp ++ suffix, .exact, .conc t⟩ = true ∧
    (applySummary ⟨⟨xb, xp ++ suffix, .exact, .conc t⟩, false⟩
      ⟨xb, xp, .star e, .conc t⟩ ⟨⟨pb, pp, .exact, .conc u⟩, false⟩).facts =
      [⟨⟨pb, pp, .exact, .conc u⟩, false⟩] ∧
    (applySummary ⟨⟨xb, xp ++ suffix, .exact, .conc t⟩, false⟩
      ⟨xb, xp, .star e, .conc t⟩ ⟨⟨pb, pp, .exact, .conc u⟩, false⟩).reqs = [] := by
  have hd : dropPrefix xp (xp ++ suffix) = some suffix := CoreAux.dropPrefix_some.mpr rfl
  have hrel := CoreAux.relate_below hd
  refine ⟨?_, ?_, ?_⟩
  · cases suffix with
    | nil =>
      have hs : dropPrefix xp xp = some [] :=
        CoreAux.dropPrefix_some.mpr (List.append_nil xp).symm
      simp [applicable, coversB, hs, markSubB, tailSubB, Kind.isAny]
    | cons a rest => simp [applicable, coversB, hd, markSubB, admitsTailB, admitted, Kind.isAny]
  · simp [applySummary, applyEdge, hrel, belowCase, admitsTailB, admitted,
      markGate, markComp, AFact.norm]
  · simp [applySummary, applyEdge, hrel, belowCase, admitsTailB, admitted,
      markGate, markComp, AFact.norm]

structure TransferCertificate (pb xb : Base) (pp xp suffix : List Acc) (u t : Mark) (e : Excl) where
  result : Res
  computed : result = applySummary ⟨⟨xb, xp ++ suffix, .exact, .conc t⟩, false⟩
    ⟨xb, xp, .star e, .conc t⟩ ⟨⟨pb, pp, .exact, .conc u⟩, false⟩
  applicable : ApSpec.applicable ⟨xb, xp, .star e, .conc t⟩
    ⟨xb, xp ++ suffix, .exact, .conc t⟩ = true
  facts : result.facts = [⟨⟨pb, pp, .exact, .conc u⟩, false⟩]
  requests : result.reqs = []

def transferCertificate (pb xb : Base) (pp xp suffix : List Acc) (u t : Mark)
    (e : Excl) (admitted : e.admits suffix = true) :
    TransferCertificate pb xb pp xp suffix u t e :=
  let h := exact_transfer pb xb pp xp suffix u t e admitted
  ⟨applySummary ⟨⟨xb, xp ++ suffix, .exact, .conc t⟩, false⟩
    ⟨xb, xp, .star e, .conc t⟩ ⟨⟨pb, pp, .exact, .conc u⟩, false⟩,
    rfl, h.1, h.2.1, h.2.2⟩

/-- The generic transfer certificate also applies to the actual selected
    computed read view, for every admitted concrete exact suffix. -/
theorem selected_view_transfer {r : NativeRecord} {v : ReadView}
    (selected : omitMustDemand r = true) (computed : readView r = some v)
    (suffix : List Acc) (admitted : r.conclusion.ex.admits suffix = true) :
    applicable v.1 ⟨r.conclusion.af.fact.base, r.conclusion.af.fact.path ++ suffix,
      .exact, r.conclusion.af.fact.mark⟩ = true ∧
    (applySummary ⟨⟨r.conclusion.af.fact.base, r.conclusion.af.fact.path ++ suffix,
      .exact, r.conclusion.af.fact.mark⟩, false⟩ v.1 v.2).facts = [⟨r.premise, false⟩] ∧
    (applySummary ⟨⟨r.conclusion.af.fact.base, r.conclusion.af.fact.path ++ suffix,
      .exact, r.conclusion.af.fact.mark⟩, false⟩ v.1 v.2).reqs = [] := by
  obtain ⟨⟨pb, pp, pk, pm⟩, must, jex, ⟨⟨⟨xb, xp, xk, xm⟩, dm⟩, ex⟩⟩ := r
  cases dm <;> cases must <;> cases pk <;> cases pm <;> cases xk <;> cases xm <;>
    simp [omitMustDemand] at selected
  subst jex
  simp [readView] at computed
  cases computed
  exact exact_transfer pb xb pp xp suffix _ _ ex admitted

theorem exact_transfer_rejects (pb xb : Base) (pp xp suffix : List Acc) (u t : Mark)
    (e : Excl) (excluded : e.admits suffix = false) :
    applicable ⟨xb, xp, .star e, .conc t⟩ ⟨xb, xp ++ suffix, .exact, .conc t⟩ = false ∧
    (applySummary ⟨⟨xb, xp ++ suffix, .exact, .conc t⟩, false⟩
      ⟨xb, xp, .star e, .conc t⟩ ⟨⟨pb, pp, .exact, .conc u⟩, false⟩).facts = [] := by
  have hd : dropPrefix xp (xp ++ suffix) = some suffix := CoreAux.dropPrefix_some.mpr rfl
  have hrel := CoreAux.relate_below hd
  constructor
  · cases suffix with
    | nil => rw [CoreAux.admits_nil] at excluded; cases excluded
    | cons _ _ => simp [applicable, coversB, hd, markSubB, admitsTailB, excluded, Kind.isAny]
  · simp [applySummary, applyEdge, hrel, belowCase, admitsTailB, excluded, Res.none]

/-- These wrapper contracts refer to the actual computed demand-view values.
    They are inclusion of denotation pairs, not converse program-flow proofs. -/
theorem mustAnyCertificate_covers (pb xb : Base) (pp xp : List Acc) (u t : Mark)
    (inputEx outputEx : Excl) (l0 l1 : Loc)
    (h : denX (mustAnyNative pb xb pp xp u t inputEx outputEx).premise inputEx
      (mustAnyNative pb xb pp xp u t inputEx outputEx).conclusion.af.fact outputEx l0 l1) :
    den (mustAnyCertificate pb xb pp xp u t inputEx outputEx).view.1
      (mustAnyCertificate pb xb pp xp u t inputEx outputEx).view.2.fact l1 l0 :=
  must_any_converse_covers h

theorem mustExactCertificate_covers (pb xb : Base) (pp xp : List Acc) (u t : Mark)
    (inputEx : Excl) (l0 l1 : Loc)
    (h : denX (mustExactNative pb xb pp xp u t inputEx).premise inputEx
      (mustExactNative pb xb pp xp u t inputEx).conclusion.af.fact Excl.empty l0 l1) :
    den (mustExactCertificate pb xb pp xp u t inputEx).view.1
      (mustExactCertificate pb xb pp xp u t inputEx).view.2.fact l1 l0 :=
  must_exact_converse_covers h

/-- Every successful read of a must-premise record is demand, regardless of
    whether its published conclusion is must or exact. -/
theorem must_read_demand {r : NativeRecord} {v : ReadView}
    (hm : r.premiseMust = true) (hr : readView r = some v) : v.2.demand = true := by
  obtain ⟨⟨pb, pp, pk, pm⟩, must, jex, ⟨⟨⟨xb, xp, xk, xm⟩, dm⟩, ex⟩⟩ := r
  dsimp only at hm
  subst must
  cases dm <;> cases pk <;> cases pm <;> cases xk <;> cases xm <;>
    simp only [readView, Bool.false_eq_true, ↓reduceIte] at hr
  all_goals first
    | cases hr <;> rfl
    | split at hr <;> cases hr <;> rfl

theorem must_read_not_normal {r : NativeRecord} {v : ReadView}
    (hm : r.premiseMust = true) (hr : readView r = some v) : v.2.demand ≠ false := by
  rw [must_read_demand hm hr]
  exact Bool.noConfusion

/-- Application cannot turn a demand must-view into a normal result. The
    existing demand monotonicity rules preserve this through later transfers. -/
theorem must_application_demand {r : NativeRecord} {v : ReadView} {a g : AFact}
    (hm : r.premiseMust = true) (hr : readView r = some v)
    (hg : g ∈ (applySummary a v.1 v.2).facts) : g.demand = true :=
  Invariant.applySummary_demand_monotone (Or.inr (must_read_demand hm hr)) hg

theorem omit_must_premise {r : NativeRecord} (hm : r.premiseMust = true) :
    omitMustDemand r = false := by
  unfold omitMustDemand
  rw [hm]
  cases r.conclusion.af.demand <;> cases r.premise.kind <;> rfl

theorem omit_star_premise {r : NativeRecord} {e : Excl} (hs : r.premise.kind = .star e) :
    omitMustDemand r = false := by
  unfold omitMustDemand
  rw [hs]
  cases r.conclusion.af.demand <;> rfl

theorem omit_demand_layer {r : NativeRecord} (hd : r.conclusion.af.demand = true) :
    omitMustDemand r = false := by simp [omitMustDemand, hd]

theorem omit_nonempty_premiseEx {r : NativeRecord} (he : r.premiseEx ≠ Excl.empty) :
    omitMustDemand r = false := by
  rw [omit_eq_guardsB]
  simp [exactMustGuardsB, he]

/-- A well-formed native must premise has the ANY tail. Its read view is
    demand and neither the old Cross nor the new omission selects reuse. -/
theorem must_selected_demand {r : NativeRecord} (hm : r.premiseMust = true)
    (hk : r.premise.kind = .any) : RawDemand r := by
  rintro (hc | hn)
  · unfold Cross at hc
    rw [hk] at hc
    exact hc.2.1
  · rw [omit_must_premise hm] at hn
    cases hn

/-- Concrete EXACT or ANY backward facts covering a location admitted by the
    new STAR/E reader premise can read it, even for nonempty E. Abstract facts
    are outside this contract. -/
theorem concrete_read_matches {b : Base} {p : List Acc} {e : Excl} {t u : Mark}
    {a : PFact} {l : Loc} (kind : a.kind = .exact ∨ a.kind = .any)
    (mark : a.mark = .conc u) (premise : (⟨b, p, .star e, .conc t⟩ : PFact).covers l)
    (added : a.covers l) :
    satW ⟨b, p, .star e, .conc t⟩ a || applicable ⟨b, p, .star e, .conc t⟩ a = true := by
  obtain ⟨hb, ⟨σ, hp, he⟩, hm⟩ := premise
  change e.admits σ = true at he
  obtain ⟨ha, ⟨τ, hq, ht⟩, hma⟩ := added
  have hl : l.mark = u := by rw [mark] at hma; exact hma
  have hut : u = t := hl.symm.trans hm
  have markT : a.mark = .conc t := mark.trans (congrArg MarkA.conc hut)
  have hbase : a.base = b := ha.symm.trans hb
  have hpath : p ++ σ = a.path ++ τ := hp.symm.trans hq
  have hread : satI ⟨b, p, .star e, .conc t⟩ a = true ∨
      applicable ⟨b, p, .star e, .conc t⟩ a = true := by
    rcases kind with hk | hk
    · have hτ : τ = [] := by rw [hk] at ht; exact ht
      have hpos : a.path = p ++ σ := by simpa [hτ] using hpath.symm
      have hd : dropPrefix p a.path = some σ := CoreAux.dropPrefix_some.mpr hpos
      right
      cases σ with
      | nil => simp [applicable, coversB, hbase, markT, hd, hk, markSubB, tailSubB, Kind.isAny]
      | cons _ _ => simp [applicable, coversB, hbase, markT, hd, hk, markSubB, admitsTailB, he, Kind.isAny]
    · rcases CoreAux.relate_common hpath with ⟨r, _, hpos, hσ⟩ | ⟨r, _, hpos, _, _⟩
      · cases r with
        | nil =>
          left
          have hd : dropPrefix a.path p = some [] :=
            CoreAux.dropPrefix_some.mpr (by simpa using hpos.symm)
          simp [satI, coversB, hbase, markT, hd, hk, markSubB, tailSubB]
        | cons x rest =>
          right
          have hd : dropPrefix p a.path = some (x :: rest) := CoreAux.dropPrefix_some.mpr hpos
          have hr : e.admits (x :: rest) = true := by
            rw [hσ] at he
            cases e <;> exact he
          simp [applicable, coversB, hbase, markT, hd, hk, markSubB, admitsTailB, hr, Kind.isAny]
      · left
        have hd : dropPrefix a.path p = some r := CoreAux.dropPrefix_some.mpr hpos
        cases r <;> simp [satI, coversB, hbase, markT, hd, hk, markSubB, tailSubB, admitsTailB]
  rcases hread with hs | ha
  · simp [satW, hs]
  · simp [ha]

theorem read_rejects_star {j : PFact} {mj : Bool} {jex : Excl} {g : XFact} {e : Excl}
    (hk : j.kind = .star e) : readView ⟨j, mj, jex, g⟩ = none := by
  unfold readView
  dsimp only
  rw [hk]
  cases g.af.demand <;> rfl

theorem read_rejects_demand {r : NativeRecord} (hd : r.conclusion.af.demand = true) :
    readView r = none := by simp [readView, hd]

namespace Certificate

def exact : ViewCertificate (exactNative 3 5 [] [2] 1 1 (.set [4])) :=
  exactCertificate 3 5 [] [2] 1 1 (.set [4])
def incoming : AFact := ⟨⟨5, [2, 7], .exact, .conc 1⟩, false⟩
def excluded : AFact := ⟨⟨5, [2, 4], .exact, .conc 1⟩, false⟩
def output : AFact := ⟨⟨3, [], .exact, .conc 1⟩, false⟩

def applied : Res := applySummary incoming exact.view.1 exact.view.2

/-- Normal record reading uses applicable; ordinary satisfaction alone fails. -/
theorem admitted_transfer :
    applicable exact.view.1 incoming.fact = true ∧
    satW exact.view.1 incoming.fact = false ∧ applied.facts = [output] ∧
    applied.reqs = [] := by decide

theorem excluded_rejected :
    applicable exact.view.1 excluded.fact = false ∧
    (applySummary excluded exact.view.1 exact.view.2).facts = [] := by decide

/-- This premise is a reader view, not a native initial fact. Directly starting
    it would forget the field exclusion and give an ANY demand fact. -/
theorem direct_start_demotes :
    startFact exact.view.1 = ⟨⟨5, [2], .any, .conc 1⟩, true⟩ ∧
    emitW exact.view.1 incoming.fact = some incoming.fact := by decide

def anyMust : ViewCertificate (mustAnyNative 3 5 [] [2] 1 1 (.set [8]) (.set [4])) :=
  mustAnyCertificate 3 5 [] [2] 1 1 (.set [8]) (.set [4])
def exactMust : ViewCertificate (mustExactNative 3 5 [] [2, 7] 1 1 (.set [8])) :=
  mustExactCertificate 3 5 [] [2, 7] 1 1 (.set [8])

theorem must_transfer :
    (applySummary incoming anyMust.view.1 anyMust.view.2).facts =
      [⟨⟨3, [], .any, .conc 1⟩, true⟩] ∧
    (applySummary incoming exactMust.view.1 exactMust.view.2).facts =
      [⟨⟨3, [], .any, .conc 1⟩, true⟩] := by decide

def mustAnyEndpoints : {locs : Loc × Loc //
    denX ⟨3, [], .any, .conc 1⟩ (.set [8])
      ⟨5, [2], .any, .conc 1⟩ (.set [4]) locs.1 locs.2 ∧
    den anyMust.view.1 anyMust.view.2.fact locs.2 locs.1} :=
  let h : denX ⟨3, [], .any, .conc 1⟩ (.set [8])
      ⟨5, [2], .any, .conc 1⟩ (.set [4]) ⟨3, [9], 1⟩ ⟨5, [2, 7], 1⟩ :=
    ⟨rfl, rfl, rfl, rfl, trivial, [9], [7], rfl, rfl, trivial, trivial, rfl, rfl⟩
  ⟨(⟨3, [9], 1⟩, ⟨5, [2, 7], 1⟩), h, must_any_converse_covers h⟩

def mustExactEndpoints : {locs : Loc × Loc //
    denX ⟨3, [], .any, .conc 1⟩ (.set [8])
      ⟨5, [2, 7], .exact, .conc 1⟩ Excl.empty locs.1 locs.2 ∧
    den exactMust.view.1 exactMust.view.2.fact locs.2 locs.1} :=
  let h : denX ⟨3, [], .any, .conc 1⟩ (.set [8])
      ⟨5, [2, 7], .exact, .conc 1⟩ Excl.empty ⟨3, [9], 1⟩ ⟨5, [2, 7], 1⟩ :=
    ⟨rfl, rfl, rfl, rfl, trivial, [9], [], rfl, rfl, trivial, rfl, rfl, rfl⟩
  ⟨(⟨3, [9], 1⟩, ⟨5, [2, 7], 1⟩), h, must_exact_converse_covers h⟩

def differentMarkTransfer : TransferCertificate 3 5 [] [2] [7] 9 1 (.set [4]) :=
  transferCertificate 3 5 [] [2] [7] 9 1 (.set [4]) rfl

def omittedNative : NativeRecord := exactNative 3 5 [] [2] 9 1 (.set [4])
def selectedRead : NormalMustWitness omittedNative := normalMustWitness omittedNative rfl
def reused : Res := applySummary incoming selectedRead.view.1 selectedRead.view.2
def source : MicroEdge := (zeroFact, omittedNative.premise)
def reverseSource : MicroEdge := revEdge source.1 source.2
def upstreamSourceRead : List AFact := reused.facts.flatMap
  (fun fact => (applyEdge fact reverseSource.1 reverseSource.2).facts)

/-- Local reuse returns the input's U, then the actual reversed unconditional
    source of U returns zero. This does not synthesize a source-hit store entry. -/
def upstreamSourceWitness : {facts : List AFact //
    facts = upstreamSourceRead ∧ facts = [⟨zeroFact, false⟩]} :=
  ⟨upstreamSourceRead, rfl, by decide⟩

theorem omission_reuses_distinct_mark :
    omitMustDemand omittedNative = true ∧
    reused.facts = [⟨⟨3, [], .exact, .conc 9⟩, false⟩] ∧
    reverseSource = (⟨3, [], .exact, .conc 9⟩, zeroFact) := by decide

theorem old_generic_cross_stays_false :
    ¬ Cross omittedNative.premise omittedNative.conclusion.af ∧ RawReusable omittedNative := by
  constructor
  · rintro ⟨_, _, _, hk⟩
    exact hk
  · exact Or.inr rfl

def exactPiece : XFact := ⟨incoming, Excl.empty⟩
def previousDemand : DemandEdge := ⟨omittedNative.premise, some incoming.fact⟩

/-- Actual annotated reduction publishes an exact piece. The omission choice
    still reads its raw exact-to-must record, not the narrowed piece. -/
theorem restricted_publication_keeps_selection :
    HandoffX.restrictIX omittedNative.premise omittedNative.premiseEx
      omittedNative.conclusion previousDemand = some exactPiece ∧
    (publicationPlan omittedNative exactPiece).1 = true ∧
    omitMustDemand ⟨omittedNative.premise, false, Excl.empty, exactPiece⟩ = false := by decide

theorem successful_must_view_still_demanded :
    readView (mustAnyNative 3 5 [] [2] 1 1 (.set [8]) (.set [4])) = some anyMust.view ∧
    omitMustDemand (mustAnyNative 3 5 [] [2] 1 1 (.set [8]) (.set [4])) = false ∧
    RawDemand (mustAnyNative 3 5 [] [2] 1 1 (.set [8]) (.set [4])) :=
  ⟨anyMust.computed, rfl, must_selected_demand rfl rfl⟩

theorem local_any_match_cases :
    satW exact.view.1 ⟨5, [], .any, .conc 1⟩ = true ∧
    satW exact.view.1 ⟨5, [2], .any, .conc 1⟩ = true ∧
    applicable exact.view.1 ⟨5, [2, 7], .any, .conc 1⟩ = true ∧
    (satW exact.view.1 ⟨5, [2, 4], .any, .conc 1⟩ ||
      applicable exact.view.1 ⟨5, [2, 4], .any, .conc 1⟩) = false := by decide

def starP : PFact := ⟨3, [], .star Excl.empty, .conc 1⟩
def startLoc : Loc := ⟨3, [8], 1⟩
def exitLoc : Loc := ⟨5, [2, 7], 1⟩

/-- An ANY target forgets correlation, so its converse must not correlate the
    new input suffix with an old STAR premise suffix. -/
theorem original_star_pair :
    denX starP Excl.empty ⟨5, [2], .any, .conc 1⟩ (.set [4]) startLoc exitLoc :=
  ⟨rfl, rfl, rfl, rfl, trivial, [8], [7], rfl, rfl, rfl, trivial, rfl, rfl⟩

theorem literal_star_loses_pair : ¬ den exact.view.1 starP exitLoc startLoc := by
  rintro ⟨_, _, _, _, _, σ, τ, hs, ht, _, htail⟩
  have he : σ = [7] := List.append_cancel_left (hs.symm.trans rfl)
  have hp : τ = [8] := ht.symm
  have hSame : τ = σ := htail.1
  rw [he, hp] at hSame
  cases hSame

/-- Concrete STAR input is outside the supported native normal shapes. -/
theorem star_native_rejected :
    readView ⟨starP, false, Excl.empty,
      ⟨⟨⟨5, [2], .any, .conc 1⟩, false⟩, .set [4]⟩⟩ = none := by decide

/-- Replacing the reverse premise by STAR does not make an end-exact must
    record pair-exact. The getter's false ret -> p.f pair still exists. -/
theorem normal_must_bad_pair :
    den ⟨2, [], .star Excl.empty, .conc 5⟩ ⟨1, [], .any, .conc 5⟩
      AnyTaintExact.CexRev.lRet AnyTaintExact.CexRev.lPf ∧
    ¬ Flow (Program.rev AnyTaintExact.CexApp.P) 1 AnyTaintExact.CexRev.lRet
      ((Program.rev AnyTaintExact.CexApp.P).exit 1) AnyTaintExact.CexRev.lPf :=
  ⟨⟨rfl, rfl, rfl, rfl, trivial, [], [1], rfl, rfl, rfl, trivial⟩,
    AnyTaintExact.CexRev.cex_rev.2.2.2.2.2.2.1⟩

#eval exact.view
#eval applied
#eval anyMust.view
#eval exactMust.view
#eval mustAnyEndpoints.val
#eval mustExactEndpoints.val
#eval differentMarkTransfer.result
#eval selectedRead.view
#eval upstreamSourceWitness.val
#eval publicationPlan omittedNative exactPiece

end Certificate

#print axioms readView
#print axioms omit_eq_guardsB
#print axioms omit_eq_normal_read
#print axioms omit_exactNative
#print axioms normalMustWitness
#print axioms omit_iff_normal_view
#print axioms publication_keeps_raw_selection
#print axioms exactCertificate
#print axioms mustAnyCertificate
#print axioms mustExactCertificate
#print axioms exact_converse
#print axioms must_any_converse_covers
#print axioms must_exact_converse_covers
#print axioms mustAnyCertificate_covers
#print axioms mustExactCertificate_covers
#print axioms transferCertificate
#print axioms selected_view_transfer
#print axioms exact_transfer_rejects
#print axioms must_read_demand
#print axioms must_read_not_normal
#print axioms must_application_demand
#print axioms must_selected_demand
#print axioms concrete_read_matches
#print axioms Certificate.literal_star_loses_pair
#print axioms Certificate.normal_must_bad_pair
#print axioms Certificate.mustAnyEndpoints
#print axioms Certificate.mustExactEndpoints
#print axioms Certificate.upstreamSourceWitness

end ApSpec.CurrentMustReverse

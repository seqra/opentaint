/-
  ApSpec.AnyTaintExExact — the PRECISION of the refined forward model with the EXCLUSION of the
  `[any-taint]` conclusion (decision F69, DESIGN §6, amendment A2).

  Namespace: `ApSpec.AnyTaintExExact`. The definitions are in `AnyTaintExDefs.lean` (namespace
  `ApSpec.AnyTaintEx`); this file does not change them.

  ## What this file proves

  A normal edge of the refined runs `D6X` (run 1) and `DRX` (a restricted forward run) is exact on
  its ADMITTED locations (the locations that the exclusion `E` of an `[any-taint]/E` conclusion, and
  the exclusion of a must-premise, admit):
    * an edge of a non-must premise is PAIR-EXACT: every pair of `denX` (both exclusions read) to a
      valid end location is a concrete flow from a valid start location (`EdgeOK6X`, `EdgeOKX`);
    * an edge of a must-premise is END-EXACT: every valid admitted location of the conclusion gets
      the value of SOME valid admitted location of the premise (`EndExactX`).
  A vulnerability confirmed on a normal sink edge (which can be `[any-taint]/E`: the sink pattern
  must meet an ADMITTED location, `checkX`) under a supported premise is real.

  ## Main results (all constructive; see the `#print axioms` lines)

  1. The local exactness lemmas (§1, §2):
     * `applyEdgeX_exact` (pair form) and `applyEdgeX_cov` (location form): a NORMAL result of the
       refined core operation on a normal input is a real composition on the admitted locations.
       The A2 rows are corollaries: `keep_row_exact` (the exclusion edge at `r = []`: every location
       that `E ∪ E'` admits comes from an admitted location of the input through the keep edge),
       `above_row_exact` (the case above with the edge exclusion), `below_row_exact` (the case below
       keeps `E`); each one with the NO-DEMOTION fact (the result is in the normal layer).
     * `transferX_exact`, `transferX_cov`, `limitFX_normal`, `startX_must_end` (the start of an
       annotated must-premise is END-EXACT), `applySummaryX_exact`, `applySummaryX_cov` (the
       summary application with an annotated conclusion), and its closure forms `summaryX_pair`
       (a pair-exact callee summary), `summaryX_end` (an END-EXACT callee summary of an annotated
       must-premise inside the added fact).
     * `cleanResX_exact`, `cleanResX_cov`; `below_new_fact_real` (the new `$` fact
       `(b, P.f, $, T)` of the `below` cleaner at `P.f` is real: the cleaner does not clean the
       location `P.f`, and `P.f` is an admitted location of the input).
  2. Run 1: `D6X_wf`, `D6X_NS`, `D6X_edgeOK`, `edge_exact6X`, `edge_exact_valid6X`.
  3. The restricted run: `DRX_wf`, `DRX_mustAny`, `DRX_conc`, `DRX_edgeOK`, `edge_exactX`,
     `edge_exactX_valid`, `recs_of_DRX` (the exit edges are exact records again, `RecsExactX`,
     with `RecsConcX` and `RecsWFX`).
  4. The support and the confirmation: `sup_entry6X`, `confirmed_real6X`,
     `confirmed_real_valid6X`; `sup_entryX`, `confirmed_realX`, `confirmed_realX_valid`; the spec
     instance `specX_rules`.
  5. The run sequence: `liftRecsX_exact` (run 1 records), `recsSeq_exactX`, `seq_confirmed_realX`
     (no record hypothesis left).
  6. Counterexamples (necessity): `CexAbove.cex_above` (without the exclusion check in the case
     above, a normal edge relates a location that no flow reaches: the setter `this.name = v`,
     then the read `y = this.name`); `CexExactCleaner.cex_exact_cleaner` (the `exact` cleaner at
     `P.f` can keep neither `[any-taint]/{f}`, which loses the real `P.f.g`, nor `[any-taint]/{}`,
     which claims the cleaned `P.f`: so `exact` still demotes); `CexRestrictSub.cex_restrict_sub`
     (the contract `RestrictSubX` of `AnyTaintExDefs.lean` is false for `restrictX` on a conclusion
     that is not in normal form; see the hypotheses below); `CexSideConditions.cex_htx`,
     `CexSideConditions.cex_hfx` (the side conditions of the core lemma are necessary).

  ## NEW HYPOTHESES (reported; each with the spec item that makes it true)

  * `RestrictOKX restrict` (in place of `RestrictSubX restrict`): the restriction of a conclusion
    IN NORMAL FORM (`WFX`) only removes pairs, keeps the layer, and gives a conclusion in normal
    form. `RestrictSubX` itself is FALSE for the spec instance `restrictX` (`CexRestrictSub`): on a
    `*` conclusion that (against the normal form) carries an exclusion, `normX` drops it and adds
    pairs. `restrictX` has `RestrictOKX` (`restrictX_ok`), and `RestrictSubX` with "the result is
    in normal form" implies it (`restrictOKX_of`). Spec item: A2 "a demand-layer `[any]` has NO
    exclusion" (only an `[any-taint]` conclusion carries `E`; `normX`), ap.md §6.4.
  * `RecsWFX recs`: every record conclusion is in normal form (`WFX`). A record is a persisted
    conclusion of an earlier run; the runs give it (`D6X_wf`, `DRX_wf`), and the run sequence
    discharges it (`recsSeq_exactX`). Spec item: A2 (the normal form; a TAINT tree carries one
    exclusion for its `[any-taint]` leaves).
  * `RecsConcX recs`: a normal must record has a concrete conclusion mark (as `RecsConcT` in
    `AnyTaintExact.lean`; `EndExactX` is vacuous for an abstract conclusion mark). The concrete
    runs give it (`recsConc_of_DRX`), run 1 gives no must record.
  * In the local lemma `applyEdgeX_exact` (not in the closure theorems): a premise exclusion `fex`
    of the edge needs an input that is not `*` and has a concrete mark (`hfx`), and a target
    exclusion `tex` needs the `.any` tail and a concrete target mark (`htx`). The closures give
    them: run 1 has no premise exclusion, a restricted run is concrete (`DRX_conc`), and a summary
    conclusion is in normal form (`D6X_wf`, `DRX_wf`, `RestrictOKX`, `RecsWFX`).
  The other hypotheses are those of `AnyTaintExact.DRT_edgeOK` / `confirmed_realT` with the X
  contracts: S7 (`MarkWF`), `FiltUp` or S13 (`FiltValid`, `BackOK`), `SatInsideX sat`,
  `EmitCopiesMarkX emit`, exact records (`RecsExactX`).
-/
import ApSpec.AnyTaintExDefs
import ApSpec.AnyTaintExact

namespace ApSpec.AnyTaintExExact
open ApSpec ApSpec.AnyTaint ApSpec.AnyTaintEx

/-! ## 0. Helpers -/

/-- The continuation of a location below a path is unique. -/
theorem cont_unique {p a b : List Acc} {q : List Acc} (ha : q = p ++ a) (hb : q = p ++ b) : a = b :=
  List.append_cancel_left (ha.symm.trans hb)

/-- The premise exclusion of a pair admits EVERY continuation of the start location. -/
theorem denX_iex {i f : PFact} {iex fex : Excl} {l0 l : Loc} (h : denX i iex f fex l0 l) :
    ∀ σ, l0.path = i.path ++ σ → iex.admits σ = true := by
  obtain ⟨_, _, _, _, _, σ0, _, h0p, _, _, _, hie, _⟩ := h
  intro σ hσ
  rw [cont_unique hσ h0p]
  exact hie

/-- The conclusion exclusion of a pair admits EVERY continuation of the end location. -/
theorem denX_fex {i f : PFact} {iex fex : Excl} {l0 l : Loc} (h : denX i iex f fex l0 l) :
    ∀ τ, l.path = f.path ++ τ → fex.admits τ = true := by
  obtain ⟨_, _, _, _, _, _, τ0, _, hlp, _, _, _, hfe⟩ := h
  intro τ hτ
  rw [cont_unique hτ hlp]
  exact hfe

/-- A base pair whose continuations the two exclusions admit is an annotated pair. -/
theorem denX_of_den {i f : PFact} {iex fex : Excl} {l0 l : Loc} (h : den i f l0 l)
    (hi : ∀ σ, l0.path = i.path ++ σ → iex.admits σ = true)
    (hf : ∀ τ, l.path = f.path ++ τ → fex.admits τ = true) : denX i iex f fex l0 l := by
  obtain ⟨h1, h2, h3, h4, h5, σ, τ, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, σ, τ, h6, h7, h8, h9, hi σ h6, hf τ h7⟩

/-- A larger conclusion exclusion has fewer pairs. -/
theorem denX_fex_mono {i f : PFact} {iex e1 e2 : Excl} {l0 l : Loc}
    (he : ∀ τ, e1.admits τ = true → e2.admits τ = true) (h : denX i iex f e1 l0 l) :
    denX i iex f e2 l0 l := by
  obtain ⟨h1, h2, h3, h4, h5, σ, τ, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, σ, τ, h6, h7, h8, h9, h10, he τ h11⟩

/-- The auxiliary premise `anyP` (`AnyTaintExact.anyP`): every admitted location of a concrete
    conclusion is the end of a pair of `denX anyP`. So the pair lemmas, which hold for EVERY premise,
    give the location form (END-EXACT). -/
theorem coversFX_denX {f : PFact} {fex : Excl} {l : Loc} (h : coversFX f fex l) :
    ∃ l0, denX AnyTaintExact.anyP Excl.empty f fex l0 l := by
  obtain ⟨hb, ⟨τ, hp, hI, he⟩, t, ht, hm⟩ := h
  refine ⟨⟨0, τ, l.mark⟩, rfl, hb, trivial, ?_, ?_, τ, τ, rfl, hp, trivial,
    AnyTaintExact.tailF_self hI, admits_empty τ, he⟩
  · rw [ht]; exact hm
  · rw [ht]; trivial

#print axioms coversFX_denX

/-- The end location of an annotated pair is an admitted location of a concrete conclusion. -/
theorem denX_coversFX {i f : PFact} {iex fex : Excl} {l0 l : Loc} (h : denX i iex f fex l0 l)
    (hm : ∃ t, f.mark = .conc t) : coversFX f fex l := by
  obtain ⟨_, hlb, _, hlm, _, σ, τ, _, hlp, _, hF, _, hfe⟩ := h
  obtain ⟨t, ht⟩ := hm
  refine ⟨hlb, ⟨τ, hlp, AnyTaintExact.tailF_tailI hF, hfe⟩, t, ht, ?_⟩
  rw [hlm, ht]
  rfl

#print axioms denX_coversFX

/-- An admitted conclusion location is an admitted premise location. -/
theorem coversX_of_coversFX {f : PFact} {fex : Excl} {l : Loc} (h : coversFX f fex l) :
    coversX f fex l := by
  obtain ⟨hb, hp, t, ht, hm⟩ := h
  refine ⟨hb, hp, ?_⟩
  rw [ht]
  exact hm

/-- An admitted premise location of a concrete premise is an admitted conclusion location. -/
theorem coversFX_of_coversX {f : PFact} {fex : Excl} {l : Loc} (h : coversX f fex l)
    (hm : ∃ t, f.mark = .conc t) : coversFX f fex l := by
  obtain ⟨hb, hp, ha⟩ := h
  obtain ⟨t, ht⟩ := hm
  refine ⟨hb, hp, t, ht, ?_⟩
  rw [ht] at ha
  exact ha

/-- A continuation that the union admits is admitted by both parts. -/
theorem admits_union_iff {e1 e2 : Excl} {σ : List Acc} (h : (e1.union e2).admits σ = true) :
    e1.admits σ = true ∧ e2.admits σ = true := Exact.union_admits h

/-- The tail of a non-`*` fact: `tailF` does not read the premise continuation. -/
theorem tailF_nonstar {k : Kind} (hk : k.isStar = false) {σ τ : List Acc} (h : tailI k τ) :
    tailF k σ τ := by
  cases k with
  | star e => cases hk
  | any => trivial
  | exact => exact h

theorem tailF_nonstar_nil {k : Kind} (hk : k.isStar = false) (σ : List Acc) : tailF k σ [] :=
  tailF_nonstar hk (Exact.tailI_nil k)

/-- A relative position `above` has a non-empty step. -/
theorem above_cons {p q r : List Acc} (h : relate p q = .above r) : ∃ a r', r = a :: r' := by
  cases r with
  | nil => exact absurd h (fun h' => RExact.relate_above_nil h')
  | cons a r' => exact ⟨a, r', rfl⟩

/-- A concrete target mark gives a concrete result mark. -/
theorem markComp_conc_target {t : Mark} {cm m : MarkA} (h : markComp (.conc t) cm = some m) :
    m = .conc t := by
  cases cm <;> exact (Option.some.inj h).symm

/-- A normal `.any` result with a concrete mark keeps its annotation (`normX`). -/
theorem normX_any_conc {f : PFact} {ex : Excl} (hk : f.kind = .any) (hm : ∃ t, f.mark = .conc t) :
    normX ⟨⟨f, false⟩, ex⟩ = ⟨⟨f, false⟩, ex⟩ := by
  apply normX_of_carries
  obtain ⟨t, ht⟩ := hm
  show (f.kind.isAny && !false && concB f.mark) = true
  rw [hk, ht]
  rfl

/-- A summary conclusion in normal form: its exclusion is empty, or it is `[any-taint]`. -/
theorem htx_of_wf {g : XFact} (h : WFX g) :
    g.ex = Excl.empty ∨ (g.af.fact.kind = .any ∧ ∃ t, g.af.fact.mark = .conc t) := by
  cases hc : carriesB g.af with
  | false => exact Or.inl (h hc)
  | true =>
    obtain ⟨hk, _, hm⟩ := carriesB_parts hc
    exact Or.inr ⟨hk, hm⟩

/-- A well-formed fact with a non-empty exclusion, or a non-`*` concrete fact: the input condition
    of a premise exclusion. -/
theorem keepB_of {c : XFact} (hk : c.af.fact.kind = .any) (hm : ∃ t, c.af.fact.mark = .conc t) :
    keepB c = true := by
  obtain ⟨t, ht⟩ := hm
  unfold keepB
  rw [hk, ht]
  rfl

theorem keepB_parts {c : XFact} (h : keepB c = true) :
    c.af.fact.kind = .any ∧ ∃ t, c.af.fact.mark = .conc t := by
  refine ⟨keepB_any h, ?_⟩
  have h2 : concB c.af.fact.mark = true := RExact.bool_and_right h
  cases hm : c.af.fact.mark with
  | conc t => exact ⟨t, rfl⟩
  | star => rw [hm] at h2; cases h2
  | starEx x => rw [hm] at h2; cases h2

/-- A normal well-formed fact with a non-empty exclusion is `[any-taint]`. -/
theorem carries_of_ex {c : XFact} (hw : WFX c) (h : c.ex ≠ Excl.empty) : carriesB c.af = true := by
  cases hc : carriesB c.af with
  | true => rfl
  | false => exact absurd (hw hc) h

/-! ## 1. The core operation `applyEdgeX` -/

/-- The full shape of a base result: the base of the input is the base of the edge premise, the
    geometry, the mark gate and the result mark. -/
theorem applyEdge_full {c r : AFact} {fr to : PFact} (h : r ∈ (applyEdge c fr to).facts) :
    c.fact.base = fr.base ∧ ∃ p k ap m,
      CoreAux.geo c.fact.kind fr.kind fr.path c.fact.path to.path to.kind = some (p, k, ap) ∧
      markGate fr.mark c.fact.mark = .ok ∧ markComp to.mark c.fact.mark = some m ∧
      r = AFact.norm ⟨⟨to.base, p, k, m⟩, c.demand || ap⟩ := by
  refine ⟨?_, CoreAux.mem_applyEdge_facts_inv h⟩
  unfold applyEdge at h
  cases hb : Nat.beq c.fact.base fr.base with
  | true => exact Nat.eq_of_beq_eq_true hb
  | false => rw [hb, if_neg Bool.false_ne_true] at h; exact absurd h List.not_mem_nil

/-- The mark gate of a refined result. -/
theorem applyEdgeX_gate {c x : XFact} {fr to : PFact} {fex tex : Excl}
    (hx : x ∈ (applyEdgeX c fr fex to tex).facts) : markGate fr.mark c.af.fact.mark = .ok := by
  obtain ⟨y, hy, _⟩ := applyEdgeX_base hx
  exact (Exact.applyEdge_mark hy).1

/-- A normal refined result comes from a normal input (the layer only rises). -/
theorem applyEdgeX_demand {c x : XFact} {fr to : PFact} {fex tex : Excl}
    (hx : x ∈ (applyEdgeX c fr fex to tex).facts) (hxa : x.af.demand = false) :
    c.af.demand = false := by
  unfold applyEdgeX at hx
  cases ha : annX c fr fex to tex with
  | none => rw [ha] at hx; exact absurd hx List.not_mem_nil
  | some pr =>
    obtain ⟨keep, ex⟩ := pr
    rw [ha] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    rw [normX_af] at hxa
    cases hcd : c.af.demand with
    | false => rfl
    | true =>
      have e : layerX keep c.af.demand y = y := by
        rw [hcd]; unfold layerX; cases keep <;> rfl
      rw [e] at hxa
      have h' := Exact.applyEdge_demand hy hxa
      rw [hcd] at h'
      exact h'

#print axioms applyEdgeX_demand

/-- A refined result with the `.any` target of a concrete mark (`[any-taint]` target, a summary
    conclusion `[any-taint]/E'`): its path is the target path and, in the normal layer, its exclusion
    is the target exclusion. -/
theorem applyEdgeX_tex {c x : XFact} {fr to : PFact} {fex tex : Excl}
    (hto : to.kind = .any ∧ ∃ t, to.mark = .conc t)
    (hx : x ∈ (applyEdgeX c fr fex to tex).facts) (hxa : x.af.demand = false) :
    x.af.fact.path = to.path ∧ x.ex = tex := by
  obtain ⟨htk, t, htm⟩ := hto
  unfold applyEdgeX at hx
  cases ha : annX c fr fex to tex with
  | none => rw [ha] at hx; exact absurd hx List.not_mem_nil
  | some pr =>
    obtain ⟨keep, ex⟩ := pr
    rw [ha] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    obtain ⟨_, p, k, ap, m, hg, _, hm, rfl⟩ := applyEdge_full hy
    rw [htm] at hm
    have hm' := markComp_conc_target hm
    subst hm'
    rw [htk] at hg
    have hk : k = .any := geo_any_target hg
    subst hk
    -- the geometry with an `.any` target: the target path, and not `apart`
    have hp : p = to.path ∧ ∃ r, relate fr.path c.af.fact.path = .below r ∨
        relate fr.path c.af.fact.path = .above r := by
      unfold CoreAux.geo at hg
      cases hrel : relate fr.path c.af.fact.path with
      | apart => rw [hrel] at hg; cases hg
      | below r =>
        rw [hrel] at hg
        dsimp only at hg
        unfold belowCase at hg
        cases hA : admitsTailB fr.kind r with
        | false => rw [hA, if_neg Bool.false_ne_true] at hg; cases hg
        | true => rw [hA, if_pos rfl] at hg; cases hg; exact ⟨rfl, r, Or.inl rfl⟩
      | above r =>
        rw [hrel] at hg
        dsimp only at hg
        unfold aboveCase at hg
        cases hA : admitsTailB c.af.fact.kind r with
        | false => rw [hA, if_neg Bool.false_ne_true] at hg; cases hg
        | true => rw [hA, if_pos rfl] at hg; cases hg; exact ⟨rfl, r, Or.inr rfl⟩
    obtain ⟨rfl, r, hrel⟩ := hp
    have hex : ex = tex := by
      unfold annX at ha
      rcases hrel with hrel | hrel <;> rw [hrel] at ha
      · cases r with
        | nil => rw [htk] at ha; cases ha; rfl
        | cons a r' =>
          dsimp only at ha
          split at ha
          · rw [htk] at ha; cases ha; rfl
          · cases ha
      · dsimp only at ha
        split at ha
        · rw [htk] at ha; cases ha; rfl
        · cases ha
    subst hex
    have hy' : AFact.norm ⟨⟨to.base, to.path, .any, .conc t⟩, c.af.demand || ap⟩ =
        ⟨⟨to.base, to.path, .any, .conc t⟩, c.af.demand || ap⟩ := rfl
    rw [hy'] at hxa ⊢
    have hl : layerX keep c.af.demand ⟨⟨to.base, to.path, .any, .conc t⟩, c.af.demand || ap⟩ =
        ⟨⟨to.base, to.path, .any, .conc t⟩, false⟩ := by
      rw [normX_af] at hxa
      unfold layerX at hxa ⊢
      cases hk : (keep && !c.af.demand)
      · rw [hk] at hxa; rw [if_neg Bool.false_ne_true] at hxa ⊢
        rw [show (c.af.demand || ap) = false from hxa]
      · rfl
    rw [hl, normX_any_conc rfl ⟨t, rfl⟩]
    exact ⟨rfl, rfl⟩

#print axioms applyEdgeX_tex

/-! ### The geometry of a non-`*` input -/

theorem admitsTailB_nil (k : Kind) : admitsTailB k [] = true := by
  cases k with
  | star e => exact Exact.admits_nil e
  | any => rfl
  | exact => rfl

theorem belowCase_star_cons {ck fk : Kind} {a : Acc} {r tp p : List Acc} {et : Excl} {k : Kind}
    {ap : Bool} (h : belowCase ck fk (a :: r) tp (.star et) = some (p, k, ap)) :
    admitsTailB fk (a :: r) = true ∧ et.admits (a :: r) = true ∧ p = tp ++ a :: r ∧ k = ck ∧
      ap = false := by
  unfold belowCase at h
  cases hA : admitsTailB fk (a :: r) with
  | false => rw [hA, if_neg Bool.false_ne_true] at h; cases h
  | true =>
    rw [hA, if_pos rfl] at h
    dsimp only at h
    cases hE : et.admits (a :: r) with
    | false => rw [hE, if_neg Bool.false_ne_true] at h; cases h
    | true => rw [hE, if_pos rfl] at h; cases h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem belowCase_star_nil {ck fk : Kind} {tp p : List Acc} {et : Excl} {k : Kind} {ap : Bool}
    (hck : ck.isStar = false) (h : belowCase ck fk [] tp (.star et) = some (p, k, ap)) :
    p = tp ∧ ((k = .exact ∧ ap = false) ∨
      (ck = .any ∧ k = .any ∧ ap = !((tailExcl fk).union et).isEmptyB)) := by
  unfold belowCase at h
  rw [if_pos (admitsTailB_nil fk)] at h
  dsimp only at h
  cases ck with
  | star e => cases hck
  | exact => cases h; exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
  | any =>
    cases hex : (tailExcl fk).union et with
    | univ => rw [hex] at h; cases h; exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
    | set xs => rw [hex] at h; cases h; exact ⟨rfl, Or.inr ⟨rfl, rfl, rfl⟩⟩

theorem lostCorr_nonstar {ck fk : Kind} (hck : ck.isStar = false) (r : List Acc) :
    lostCorr ck fk r = false := by
  cases ck with
  | star e => cases hck
  | any => cases r <;> rfl
  | exact => cases r <;> rfl

theorem belowCase_any_N {ck fk : Kind} {r tp p : List Acc} {k : Kind} {ap : Bool}
    (hck : ck.isStar = false) (h : belowCase ck fk r tp .any = some (p, k, ap)) :
    admitsTailB fk r = true ∧ p = tp ∧ k = .any ∧ ap = false := by
  unfold belowCase at h
  cases hA : admitsTailB fk r with
  | false => rw [hA, if_neg Bool.false_ne_true] at h; cases h
  | true =>
    rw [hA, if_pos rfl] at h
    cases h
    exact ⟨rfl, rfl, rfl, lostCorr_nonstar hck r⟩

theorem belowCase_exact_N {ck fk : Kind} {r tp p : List Acc} {k : Kind} {ap : Bool}
    (hck : ck.isStar = false) (h : belowCase ck fk r tp .exact = some (p, k, ap)) :
    admitsTailB fk r = true ∧ p = tp ∧ k = .exact ∧ ap = false := by
  unfold belowCase at h
  cases hA : admitsTailB fk r with
  | false => rw [hA, if_neg Bool.false_ne_true] at h; cases h
  | true =>
    rw [hA, if_pos rfl] at h
    cases ck with
    | star e => cases hck
    | any => cases fk <;> cases r <;> (cases h; exact ⟨rfl, rfl, rfl, rfl⟩)
    | exact => cases fk <;> cases r <;> (cases h; exact ⟨rfl, rfl, rfl, rfl⟩)

theorem aboveCase_N {ck fk tk : Kind} {r tp p : List Acc} {k : Kind} {ap : Bool}
    (hck : ck.isStar = false) (hr : ∃ a r', r = a :: r')
    (h : aboveCase ck fk r tp tk = some (p, k, ap)) :
    ck = .any ∧ p = tp ∧
      ((∃ et, tk = .star et ∧ k = .any ∧ ap = !((tailExcl fk).union et).isEmptyB) ∨
       (tk = .any ∧ k = .any ∧ ap = false) ∨ (tk = .exact ∧ k = .exact ∧ ap = false)) := by
  obtain ⟨a, r', rfl⟩ := hr
  unfold aboveCase at h
  cases ck with
  | star e => cases hck
  | exact =>
    have h0 : admitsTailB Kind.exact (a :: r') = false := rfl
    rw [h0, if_neg Bool.false_ne_true] at h; cases h
  | any =>
    have h0 : admitsTailB Kind.any (a :: r') = true := rfl
    rw [h0, if_pos rfl] at h
    refine ⟨rfl, ?_⟩
    cases tk with
    | star et => cases h; exact ⟨rfl, Or.inl ⟨et, rfl, rfl, rfl⟩⟩
    | any => cases h; exact ⟨rfl, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩
    | exact => cases h; exact ⟨rfl, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)⟩

/-! ### The annotation rows of `annX` -/

theorem annX_below_nil {c : XFact} {fr to : PFact} {fex tex : Excl} {keep : Bool} {ex : Excl}
    (hrel : relate fr.path c.af.fact.path = .below []) (h : annX c fr fex to tex = some (keep, ex)) :
    (∀ et, to.kind = .star et →
      keep = keepB c ∧ ex = ((c.ex.union (tailExcl fr.kind)).union fex).union et) ∧
    (to.kind = .any → keep = false ∧ ex = tex) := by
  unfold annX at h
  rw [hrel] at h
  dsimp only at h
  refine ⟨fun et het => ?_, fun het => ?_⟩
  · rw [het] at h; cases h; exact ⟨rfl, rfl⟩
  · rw [het] at h; cases h; exact ⟨rfl, rfl⟩

theorem annX_below_cons {c : XFact} {fr to : PFact} {fex tex : Excl} {keep : Bool} {ex : Excl}
    {a : Acc} {r : List Acc} (hrel : relate fr.path c.af.fact.path = .below (a :: r))
    (h : annX c fr fex to tex = some (keep, ex)) :
    fex.admits (a :: r) = true ∧ keep = false ∧ (∀ et, to.kind = .star et → ex = c.ex) ∧
      (to.kind = .any → ex = tex) := by
  unfold annX at h
  rw [hrel] at h
  dsimp only at h
  cases hf : fex.admits (a :: r) with
  | false => rw [hf, if_neg Bool.false_ne_true] at h; cases h
  | true =>
    rw [hf, if_pos rfl] at h
    cases hto : to.kind with
    | star et =>
      rw [hto] at h; cases h
      refine ⟨rfl, rfl, fun _ _ => rfl, ?_⟩
      intro h'; cases h'
    | any =>
      rw [hto] at h; cases h
      refine ⟨rfl, rfl, ?_, fun _ => rfl⟩
      intro et h'; cases h'
    | exact =>
      rw [hto] at h; cases h
      refine ⟨rfl, rfl, ?_, ?_⟩
      · intro et h'; cases h'
      · intro h'; cases h'

theorem annX_above {c : XFact} {fr to : PFact} {fex tex : Excl} {keep : Bool} {ex : Excl}
    {r : List Acc} (hrel : relate fr.path c.af.fact.path = .above r)
    (h : annX c fr fex to tex = some (keep, ex)) :
    c.ex.admits r = true ∧
    (∀ et, to.kind = .star et → keep = keepB c ∧ ex = ((tailExcl fr.kind).union fex).union et) ∧
    (to.kind = .any → keep = false ∧ ex = tex) := by
  unfold annX at h
  rw [hrel] at h
  dsimp only at h
  cases hf : c.ex.admits r with
  | false => rw [hf, if_neg Bool.false_ne_true] at h; cases h
  | true =>
    rw [hf, if_pos rfl] at h
    refine ⟨rfl, fun et het => ?_, fun het => ?_⟩
    · rw [het] at h; cases h; exact ⟨rfl, rfl⟩
    · rw [het] at h; cases h; exact ⟨rfl, rfl⟩

/-- An `[any-taint]` fact can take the exclusion rows. -/
theorem keepB_of_carries {c : XFact} (h : carriesB c.af = true) : keepB c = true := by
  obtain ⟨hk, _, hm⟩ := carriesB_parts h
  exact keepB_of hk hm

/-- The shape of a NORMAL refined result on a normal non-`*` input: the base geometry, the gate
    and the mark of the result; the base layer is normal, or the row is a `keep` row (DESIGN A2:
    the exclusion no longer demotes); the result is `normX` of the normal fact. -/
theorem applyEdgeX_shapeN {c x : XFact} {fr to : PFact} {fex tex : Excl}
    (hc : c.af.demand = false) (hns : c.af.fact.kind.isStar = false)
    (hx : x ∈ (applyEdgeX c fr fex to tex).facts) (hxa : x.af.demand = false) :
    ∃ keep ex p k ap m, annX c fr fex to tex = some (keep, ex) ∧ c.af.fact.base = fr.base ∧
      CoreAux.geo c.af.fact.kind fr.kind fr.path c.af.fact.path to.path to.kind = some (p, k, ap) ∧
      markGate fr.mark c.af.fact.mark = .ok ∧ markComp to.mark c.af.fact.mark = some m ∧
      (ap = false ∨ keep = true) ∧ x = normX ⟨⟨⟨to.base, p, k, m⟩, false⟩, ex⟩ := by
  unfold applyEdgeX at hx
  cases ha : annX c fr fex to tex with
  | none => rw [ha] at hx; exact absurd hx List.not_mem_nil
  | some pr =>
    obtain ⟨keep, ex⟩ := pr
    rw [ha] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hb, p, k, ap, m, hg, hgate, hm, rfl⟩ := applyEdge_full hy
    have hk : k.isStar = false := Invariant.geo_nonstar hns hg
    have hn : AFact.norm ⟨⟨to.base, p, k, m⟩, c.af.demand || ap⟩ = ⟨⟨to.base, p, k, m⟩, ap⟩ := by
      rw [Invariant.norm_id_of_nonstar (x := ⟨⟨to.base, p, k, m⟩, c.af.demand || ap⟩) hk, hc]; rfl
    rw [hn] at hxa ⊢
    rw [normX_af] at hxa
    cases keep with
    | true =>
      refine ⟨true, ex, p, k, ap, m, rfl, hb, hg, hgate, hm, Or.inr rfl, ?_⟩
      unfold layerX; rw [hc]; rfl
    | false =>
      have hap : ap = false := hxa
      refine ⟨false, ex, p, k, ap, m, rfl, hb, hg, hgate, hm, Or.inl hap, ?_⟩
      unfold layerX; rw [hap]; rfl

#print axioms applyEdgeX_shapeN

/-- The pair builder: the witness `⟨c.base, c.path ++ τ1, c.mark.out m0⟩` of a non-`*` input. -/
theorem mk_pairX {ic fr to cf : PFact} {iex cex fex tex : Excl} {l0 l2 : Loc}
    (hbase : cf.base = fr.base) (hfa : fr.mark.admits (cf.mark.out l0.mark))
    (h0b : l0.base = ic.base) (h0m : ic.mark.admits l0.mark) (hcs : cf.mark.passes l0.mark)
    (h2b : l2.base = to.base) (h2m : l2.mark = to.mark.out (cf.mark.out l0.mark))
    (hts : to.mark.passes (cf.mark.out l0.mark))
    {σ0 τ1 σ1 τ2 : List Acc} (h0p : l0.path = ic.path ++ σ0) (hI0 : tailI ic.kind σ0)
    (hie : iex.admits σ0 = true) (h1p : cf.path ++ τ1 = fr.path ++ σ1) (hF1 : tailF cf.kind σ0 τ1)
    (hce : cex.admits τ1 = true) (h2p : l2.path = to.path ++ τ2) (hI1 : tailI fr.kind σ1)
    (hF2 : tailF to.kind σ1 τ2) (hfe : fex.admits σ1 = true) (hte : tex.admits τ2 = true) :
    ∃ l1, denX ic iex cf cex l0 l1 ∧ denX fr fex to tex l1 l2 :=
  ⟨⟨cf.base, cf.path ++ τ1, cf.mark.out l0.mark⟩,
   ⟨h0b, rfl, h0m, rfl, hcs, σ0, τ1, h0p, rfl, hI0, hF1, hie, hce⟩,
   ⟨hbase, h2b, hfa, h2m, hts, σ1, τ2, h1p, h2p, hI1, hF2, hfe, hte⟩⟩

/-- `carriesB` is `keepB` in the normal layer. -/
theorem carriesB_keepB {c : XFact} (h : carriesB c.af = true) : keepB c = true :=
  keepB_of_carries h

/-- The input exclusion of a non-`[any-taint]` input is empty. -/
theorem ex_of_not_keep {c : XFact} (hw : WFX c) (h : keepB c = false) : c.ex = Excl.empty := by
  cases hc : carriesB c.af with
  | false => exact hw hc
  | true => rw [carriesB_keepB hc] at h; cases h

/-- THE CORE LEMMA FOR A NON-`*` INPUT (pair form): a normal result of `applyEdgeX` on a normal
    non-`*` input is a real composition on the admitted locations. -/
theorem applyEdgeX_exactN {ic fr to : PFact} {iex fex tex : Excl} {c x : XFact} {l0 l2 : Loc}
    (hpm : Exact.premOKB fr.mark c.af.fact.mark = true)
    (hcm : Exact.concOKB to.mark c.af.fact.mark = true)
    (hc : c.af.demand = false) (hwf : WFX c) (hns : c.af.fact.kind.isStar = false)
    (hfx : fex = Excl.empty ∨ ∃ t, c.af.fact.mark = .conc t)
    (hte : ∀ τ2, l2.path = to.path ++ τ2 → tex.admits τ2 = true)
    (hx : x ∈ (applyEdgeX c fr fex to tex).facts) (hxa : x.af.demand = false)
    (hd : denX ic iex x.af.fact x.ex l0 l2) :
    ∃ l1, denX ic iex c.af.fact c.ex l0 l1 ∧ denX fr fex to tex l1 l2 := by
  obtain ⟨keep, ex, p, k, ap, m, ha, hbase, hg, hgate, hm, hak, rfl⟩ :=
    applyEdgeX_shapeN hc hns hx hxa
  rw [normX_fact] at hd
  -- the result keeps the exclusion `ex` when it is `[any-taint]`
  have hxe : ∀ τ, k = .any → (∃ t, m = .conc t) →
      (normX ⟨⟨⟨to.base, p, k, m⟩, false⟩, ex⟩).ex.admits τ = true → ex.admits τ = true := by
    intro τ hk hmc h
    rw [normX_any_conc (f := ⟨to.base, p, k, m⟩) hk hmc] at h
    exact h
  obtain ⟨h0b, h2b, h0m, h2m, h2s, σ0, τ, h0p, h2p, hI0, hF, hie, hxex⟩ := hd
  obtain ⟨hout, hcs, hts⟩ := Exact.markComp_out hm hcm h2s
  have hfa := Exact.gate_admits hgate hpm hcs
  have h2m' : l2.mark = to.mark.out (c.af.fact.mark.out l0.mark) := by rw [h2m]; exact hout
  have key : ∀ τ1 σ1 τ2, c.af.fact.path ++ τ1 = fr.path ++ σ1 → tailF c.af.fact.kind σ0 τ1 →
      c.ex.admits τ1 = true → l2.path = to.path ++ τ2 → tailI fr.kind σ1 →
      tailF to.kind σ1 τ2 → fex.admits σ1 = true →
      ∃ l1, denX ic iex c.af.fact c.ex l0 l1 ∧ denX fr fex to tex l1 l2 :=
    fun τ1 σ1 τ2 h1 h2 h3 h4 h5 h6 h7 =>
      mk_pairX hbase hfa h0b h0m hcs h2b h2m' hts h0p hI0 hie h1 h2 h3 h4 h5 h6 h7 (hte τ2 h4)
  -- a keep row: the input is `[any-taint]`, the result keeps the exclusion `ex`
  have hkeepEx : keepB c = true → k = .any → ∀ τ', (normX ⟨⟨⟨to.base, p, k, m⟩, false⟩, ex⟩).ex.admits τ' = true →
      ex.admits τ' = true := by
    intro hkb hk τ' h
    obtain ⟨_, t, ht⟩ := keepB_parts hkb
    have hm' := hm
    rw [ht] at hm'
    exact hxe τ' hk (CoreAux.markComp_conc hm') h
  unfold CoreAux.geo at hg
  cases hrel : relate fr.path c.af.fact.path with
  | apart => rw [hrel] at hg; cases hg
  | below rr =>
    rw [hrel] at hg
    dsimp only at hg
    have hcp : c.af.fact.path = fr.path ++ rr := Exact.relate_below hrel
    cases hto : to.kind with
    | star et =>
      rw [hto] at hg
      cases rr with
      | cons a r' =>
        -- the case below with a `*` target: the result keeps `E` at its new path end
        obtain ⟨hA, hE, rfl, rfl, rfl⟩ := belowCase_star_cons hg
        obtain ⟨hfe, _, hex1, _⟩ := annX_below_cons hrel ha
        have hex : ex = c.ex := hex1 et hto
        refine key τ (a :: r' ++ τ) (a :: r' ++ τ) (by rw [hcp, List.append_assoc]) hF ?_
          (by rw [h2p, List.append_assoc]) (Exact.tailI_cons_append τ hA)
          (by rw [hto]; exact ⟨rfl, Exact.admits_cons_append τ hE⟩) (Exact.admits_cons_append τ hfe)
        cases hcar : carriesB c.af with
        | false => rw [hwf hcar]; exact admits_empty τ
        | true =>
          rw [← hex]
          exact hkeepEx (keepB_of_carries hcar) (carriesB_parts hcar).1 τ hxex
      | nil =>
        obtain ⟨rfl, hk⟩ := belowCase_star_nil hns hg
        obtain ⟨hst, _⟩ := annX_below_nil hrel ha
        obtain ⟨hkeep, hex⟩ := hst et hto
        have hcp' : c.af.fact.path ++ [] = fr.path ++ [] := by simp only [hcp, List.append_nil]
        rcases hk with ⟨rfl, rfl⟩ | ⟨hck, rfl, hap⟩
        · -- a `$` result: the position itself
          have hτ : τ = [] := hF
          subst hτ
          exact key [] [] [] hcp' (tailF_nonstar_nil hns σ0) (Exact.admits_nil _) h2p
            (Exact.tailI_nil _) (by rw [hto]; exact ⟨rfl, Exact.admits_nil et⟩) (Exact.admits_nil _)
        · -- an `.any` result: THE KEEP ROW of DESIGN A2 (`E ∪ E'`)
          have hparts : c.ex.admits τ = true ∧ tailI fr.kind τ ∧ et.admits τ = true ∧
              fex.admits τ = true := by
            cases keep with
            | true =>
              have hx' := hkeepEx hkeep.symm rfl τ hxex
              rw [hex] at hx'
              obtain ⟨h123, h4⟩ := admits_union_iff hx'
              obtain ⟨h12, h3⟩ := admits_union_iff h123
              obtain ⟨h1, h2⟩ := admits_union_iff h12
              exact ⟨h1, Exact.tailExcl_tailI h2, h4, h3⟩
            | false =>
              have hap0 : ap = false := by rcases hak with h | h; exact h; cases h
              rw [hap0] at hap
              obtain ⟨h1, h2⟩ := Exact.isEmpty_union (Exact.not_eq_false_true hap.symm)
              have hce0 : c.ex = Excl.empty := ex_of_not_keep hwf hkeep.symm
              have hfe0 : fex = Excl.empty := by
                rcases hfx with h | ⟨t, ht⟩
                · exact h
                · rw [keepB_of hck ⟨t, ht⟩] at hkeep; cases hkeep
              refine ⟨by rw [hce0]; exact admits_empty τ, Exact.tailExcl_setNil h1 τ,
                by rw [h2]; exact Exact.setNil_admits τ, by rw [hfe0]; exact admits_empty τ⟩
          obtain ⟨h1, h2, h3, h4⟩ := hparts
          have hcp'' : c.af.fact.path ++ τ = fr.path ++ τ := by
            rw [hcp, List.append_nil]
          exact key τ τ τ hcp'' (by rw [hck]; trivial) h1 h2p h2 (by rw [hto]; exact ⟨rfl, h3⟩) h4
    | any =>
      rw [hto] at hg
      obtain ⟨hA, rfl, rfl, rfl⟩ := belowCase_any_N hns hg
      have hfe : fex.admits rr = true := by
        cases rr with
        | nil => exact Exact.admits_nil _
        | cons a r' => exact (annX_below_cons hrel ha).1
      exact key [] rr τ (by rw [hcp, List.append_nil]) (tailF_nonstar_nil hns σ0)
        (Exact.admits_nil _) h2p (Exact.admitsTailB_tailI hA) (by rw [hto]; trivial) hfe
    | exact =>
      rw [hto] at hg
      obtain ⟨hA, rfl, rfl, rfl⟩ := belowCase_exact_N hns hg
      have hτ : τ = [] := hF
      subst hτ
      have hfe : fex.admits rr = true := by
        cases rr with
        | nil => exact Exact.admits_nil _
        | cons a r' => exact (annX_below_cons hrel ha).1
      exact key [] rr [] (by rw [hcp, List.append_nil]) (tailF_nonstar_nil hns σ0)
        (Exact.admits_nil _) h2p (Exact.admitsTailB_tailI hA) (by rw [hto]; rfl) hfe
  | above rr =>
    rw [hrel] at hg
    dsimp only at hg
    have hfp : fr.path = c.af.fact.path ++ rr := Exact.relate_above hrel
    obtain ⟨a, r', hrr⟩ := above_cons hrel
    obtain ⟨hcx, hst, han⟩ := annX_above hrel ha
    obtain ⟨hck, rfl, hrows⟩ := aboveCase_N hns ⟨a, r', hrr⟩ hg
    subst hrr
    rcases hrows with ⟨et, hto, rfl, hap⟩ | ⟨hto, rfl, rfl⟩ | ⟨hto, rfl, rfl⟩
    · -- a `*` target: THE CASE ABOVE WITH THE EDGE EXCLUSION (DESIGN A2)
      obtain ⟨hkeep, hex⟩ := hst et hto
      have hparts : tailI fr.kind τ ∧ et.admits τ = true ∧ fex.admits τ = true := by
        cases keep with
        | true =>
          have hx' := hkeepEx hkeep.symm rfl τ hxex
          rw [hex] at hx'
          obtain ⟨h12, h3⟩ := admits_union_iff hx'
          obtain ⟨h1, h2⟩ := admits_union_iff h12
          exact ⟨Exact.tailExcl_tailI h1, h3, h2⟩
        | false =>
          have hap0 : ap = false := by rcases hak with h | h; exact h; cases h
          rw [hap0] at hap
          obtain ⟨h1, h2⟩ := Exact.isEmpty_union (Exact.not_eq_false_true hap.symm)
          have hfe0 : fex = Excl.empty := by
            rcases hfx with h | ⟨t, ht⟩
            · exact h
            · rw [keepB_of hck ⟨t, ht⟩] at hkeep; cases hkeep
          exact ⟨Exact.tailExcl_setNil h1 τ, by rw [h2]; exact Exact.setNil_admits τ,
            by rw [hfe0]; exact admits_empty τ⟩
      obtain ⟨h1, h2, h3⟩ := hparts
      exact key (a :: r' ++ τ) τ τ (by rw [hfp, List.append_assoc]) (by rw [hck]; trivial)
        (Exact.admits_cons_append τ hcx) h2p h1 (by rw [hto]; exact ⟨rfl, h2⟩) h3
    · -- an `.any` target
      exact key (a :: r') [] τ (by rw [hfp, List.append_nil]) (by rw [hck]; trivial) hcx h2p
        (Exact.tailI_nil _) (by rw [hto]; trivial) (Exact.admits_nil _)
    · -- a `$` target
      have hτ : τ = [] := hF
      subst hτ
      exact key (a :: r') [] [] (by rw [hfp, List.append_nil]) (by rw [hck]; trivial) hcx h2p
        (Exact.tailI_nil _) (by rw [hto]; rfl) (Exact.admits_nil _)

#print axioms applyEdgeX_exactN

/-- The core lemma for a `*` input (run 1 only: a `*` fact has no exclusion, takes no `keep` row
    and meets no premise exclusion): the base lemma `Exact.applyEdge_exact`. -/
theorem applyEdgeX_exactS {ic fr to : PFact} {iex fex tex : Excl} {c x : XFact} {l0 l2 : Loc}
    (hpm : Exact.premOKB fr.mark c.af.fact.mark = true)
    (hcm : Exact.concOKB to.mark c.af.fact.mark = true)
    (hc : c.af.demand = false) (hwf : WFX c) (hst : c.af.fact.kind.isStar = true)
    (hfx : fex = Excl.empty) (hte : ∀ τ2, l2.path = to.path ++ τ2 → tex.admits τ2 = true)
    (hx : x ∈ (applyEdgeX c fr fex to tex).facts) (hxa : x.af.demand = false)
    (hd : denX ic iex x.af.fact x.ex l0 l2) :
    ∃ l1, denX ic iex c.af.fact c.ex l0 l1 ∧ denX fr fex to tex l1 l2 := by
  have hany : c.af.fact.kind.isAny = false := by
    cases hk : c.af.fact.kind with
    | star e => rfl
    | any => rw [hk] at hst; cases hst
    | exact => rw [hk] at hst; cases hst
  have hkb : keepB c = false := by unfold keepB; rw [hany]; rfl
  obtain ⟨y, hy, hxf, hl⟩ := applyEdgeX_base hx
  have hya : y.demand = false := by
    rcases hl with hl | ⟨_, _, hk, _⟩
    · rw [← hl]; exact hxa
    · rw [hkb] at hk; cases hk
  have hcex : c.ex = Excl.empty := ex_of_not_keep hwf hkb
  rw [hxf] at hd
  obtain ⟨l1, hd1, hd2⟩ := Exact.applyEdge_exact hpm hcm hc hy hya (denX_den hd)
  exact ⟨l1, denX_of_den hd1 (denX_iex hd) (fun τ _ => by rw [hcex]; exact admits_empty τ),
    denX_of_den hd2 (fun σ _ => by rw [hfx]; exact admits_empty σ) hte⟩

#print axioms applyEdgeX_exactS

/-- THE CORE LEMMA (pair form; DESIGN A2). A NORMAL result `x` of the refined core operation on a
    normal input `c` (in normal form, `WFX`) is a real composition on the ADMITTED locations: every
    pair `(l0, l2)` of `x` (its exclusion read) has a middle location `l1` that is an admitted pair
    of `c` and a pair of the edge `(fr, fex) → (to, tex)` (both edge exclusions read). The keep rows
    of A2 (the exclusion edge at `r = []`, the case above with a `*` target) are included: there the
    base demotes, the refined result stays normal and is exact. Hypotheses: the mark conditions of
    `Exact.applyEdge_exact` (`premOKB`, `concOKB`); a premise exclusion `fex` meets only a non-`*`
    concrete input (`hfx`); a target exclusion `tex` only an `[any-taint]` target (`htx`, the normal
    form of a summary conclusion). -/
theorem applyEdgeX_exact {ic fr to : PFact} {iex fex tex : Excl} {c x : XFact} {l0 l2 : Loc}
    (hpm : Exact.premOKB fr.mark c.af.fact.mark = true)
    (hcm : Exact.concOKB to.mark c.af.fact.mark = true)
    (hc : c.af.demand = false) (hwf : WFX c)
    (hfx : fex = Excl.empty ∨ (c.af.fact.kind.isStar = false ∧ ∃ t, c.af.fact.mark = .conc t))
    (htx : tex = Excl.empty ∨ (to.kind = .any ∧ ∃ t, to.mark = .conc t))
    (hx : x ∈ (applyEdgeX c fr fex to tex).facts) (hxa : x.af.demand = false)
    (hd : denX ic iex x.af.fact x.ex l0 l2) :
    ∃ l1, denX ic iex c.af.fact c.ex l0 l1 ∧ denX fr fex to tex l1 l2 := by
  have hte : ∀ τ2, l2.path = to.path ++ τ2 → tex.admits τ2 = true := by
    intro τ2 h2
    rcases htx with rfl | htx'
    · exact admits_empty τ2
    · obtain ⟨hpath, hex⟩ := applyEdgeX_tex htx' hx hxa
      have h := denX_fex hd τ2 (by rw [hpath]; exact h2)
      rw [hex] at h
      exact h
  cases hs : c.af.fact.kind.isStar with
  | false => exact applyEdgeX_exactN hpm hcm hc hwf hs (hfx.imp id (fun h => h.2)) hte hx hxa hd
  | true =>
    have hfx' : fex = Excl.empty := by
      rcases hfx with h | ⟨h, _⟩
      · exact h
      · rw [hs] at h; cases h
    exact applyEdgeX_exactS hpm hcm hc hwf hs hfx' hte hx hxa hd

#print axioms applyEdgeX_exact

/-- THE CORE LEMMA (location form, END-EXACT; DESIGN A2). Every admitted location of a normal result
    `x` of `applyEdgeX` on a normal concrete input `c` is the end of an edge pair from an admitted
    location of `c`. -/
theorem applyEdgeX_cov {fr to : PFact} {fex tex : Excl} {c x : XFact} {l : Loc}
    (hpm : Exact.premOKB fr.mark c.af.fact.mark = true)
    (hcm : Exact.concOKB to.mark c.af.fact.mark = true)
    (hc : c.af.demand = false) (hwf : WFX c)
    (hfx : fex = Excl.empty ∨ (c.af.fact.kind.isStar = false ∧ ∃ t, c.af.fact.mark = .conc t))
    (htx : tex = Excl.empty ∨ (to.kind = .any ∧ ∃ t, to.mark = .conc t))
    (hx : x ∈ (applyEdgeX c fr fex to tex).facts) (hxa : x.af.demand = false)
    (hcc : ∃ t, c.af.fact.mark = .conc t) (hl : coversFX x.af.fact x.ex l) :
    ∃ l1, coversFX c.af.fact c.ex l1 ∧ denX fr fex to tex l1 l := by
  obtain ⟨l0, hd⟩ := coversFX_denX hl
  obtain ⟨l1, hd1, hd2⟩ := applyEdgeX_exact (ic := AnyTaintExact.anyP) (iex := Excl.empty)
    hpm hcm hc hwf hfx htx hx hxa hd
  exact ⟨l1, denX_coversFX hd1 hcc, hd2⟩

#print axioms applyEdgeX_cov

/-! ### The A2 rows (corollaries of the core lemma, with the no-demotion fact) -/

/-- The layer of a refined result at a `keep` row: the layer of the input. -/
theorem applyEdgeX_keep_layer {c x : XFact} {fr to : PFact} {fex tex ex : Excl}
    (ha : annX c fr fex to tex = some (true, ex)) (hc : c.af.demand = false)
    (hx : x ∈ (applyEdgeX c fr fex to tex).facts) : x.af.demand = false := by
  unfold applyEdgeX at hx
  rw [ha] at hx
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
  rw [normX_af]
  unfold layerX
  rw [hc]
  rfl

/-- THE KEEP ROW OF DESIGN A2 (the exclusion edge at `r = []`: the keep edge of a strong write, a
    `*/E'` summary or record). On a normal `[any-taint]/E` input at the premise path and a `*/et`
    target, every result is NORMAL (the exclusion no longer demotes); an `.any` result carries
    `E ∪ tailExcl ∪ fex ∪ et`; and every location that this exclusion admits comes from an admitted
    location of the input through the edge. -/
theorem keep_row_exact {fr to : PFact} {fex tex et : Excl} {c x : XFact}
    (hpm : Exact.premOKB fr.mark c.af.fact.mark = true) (hwf : WFX c) (hcar : carriesB c.af = true)
    (hrel : relate fr.path c.af.fact.path = .below []) (hto : to.kind = .star et)
    (htex : tex = Excl.empty) (hx : x ∈ (applyEdgeX c fr fex to tex).facts) :
    x.af.demand = false ∧
    (x.af.fact.kind = .any → x.ex = ((c.ex.union (tailExcl fr.kind)).union fex).union et) ∧
    ∀ l, coversFX x.af.fact x.ex l → ∃ l1, coversFX c.af.fact c.ex l1 ∧ denX fr fex to tex l1 l := by
  obtain ⟨hk, hc, t, ht⟩ := carriesB_parts hcar
  have ha : annX c fr fex to tex = some (true, ((c.ex.union (tailExcl fr.kind)).union fex).union et) := by
    unfold annX; rw [hrel]; dsimp only; rw [hto]; dsimp only; rw [keepB_of_carries hcar]
  have hxa := applyEdgeX_keep_layer ha hc hx
  have hns : c.af.fact.kind.isStar = false := by rw [hk]; rfl
  refine ⟨hxa, fun hxk => ?_, fun l hl => ?_⟩
  · obtain ⟨keep, ex, p, k, ap, m, ha', _, _, _, hm, _, rfl⟩ := applyEdgeX_shapeN hc hns hx hxa
    rw [ha] at ha'
    cases ha'
    rw [normX_fact] at hxk
    have hm' := hm
    rw [ht] at hm'
    rw [normX_any_conc hxk (CoreAux.markComp_conc hm')]
  · exact applyEdgeX_cov hpm (AnyTaintExact.concOK_conc _ ⟨t, ht⟩) hc hwf (Or.inr ⟨hns, t, ht⟩)
      (Or.inl htex) hx hxa ⟨t, ht⟩ hl

#print axioms keep_row_exact

/-- THE CASE ABOVE WITH THE EDGE EXCLUSION (DESIGN A2): a normal `[any-taint]/E` input ABOVE the
    premise path (`fr.path = c.path ++ r`) and a `*/et` target. If `E` excludes the step `r`, there is
    NO result (no common location). Otherwise every result is NORMAL, an `.any` result carries the
    edge exclusion `tailExcl ∪ fex ∪ et` (not `E`), and every location that it admits comes from an
    admitted location of the input. -/
theorem above_row_exact {fr to : PFact} {fex tex et : Excl} {c : XFact} {r : List Acc}
    (hpm : Exact.premOKB fr.mark c.af.fact.mark = true) (hwf : WFX c) (hcar : carriesB c.af = true)
    (hrel : relate fr.path c.af.fact.path = .above r) (hto : to.kind = .star et)
    (htex : tex = Excl.empty) :
    (c.ex.admits r = false → applyEdgeX c fr fex to tex = ResX.none) ∧
    ∀ x, x ∈ (applyEdgeX c fr fex to tex).facts →
      x.af.demand = false ∧
      (x.af.fact.kind = .any → x.ex = ((tailExcl fr.kind).union fex).union et) ∧
      ∀ l, coversFX x.af.fact x.ex l → ∃ l1, coversFX c.af.fact c.ex l1 ∧ denX fr fex to tex l1 l := by
  obtain ⟨hk, hc, t, ht⟩ := carriesB_parts hcar
  refine ⟨fun hna => ?_, fun x hx => ?_⟩
  · have ha : annX c fr fex to tex = none := by
      unfold annX; rw [hrel]; dsimp only; rw [hna, if_neg Bool.false_ne_true]
    unfold applyEdgeX; rw [ha]
  · have hadm : c.ex.admits r = true := by
      cases h : c.ex.admits r with
      | true => rfl
      | false =>
        have ha : annX c fr fex to tex = none := by
          unfold annX; rw [hrel]; dsimp only; rw [h, if_neg Bool.false_ne_true]
        unfold applyEdgeX at hx; rw [ha] at hx; exact absurd hx List.not_mem_nil
    have ha : annX c fr fex to tex = some (true, ((tailExcl fr.kind).union fex).union et) := by
      unfold annX; rw [hrel]; dsimp only; rw [hadm, if_pos rfl, hto]
      rw [keepB_of_carries hcar]
    have hxa := applyEdgeX_keep_layer ha hc hx
    have hns : c.af.fact.kind.isStar = false := by rw [hk]; rfl
    refine ⟨hxa, fun hxk => ?_, fun l hl => ?_⟩
    · obtain ⟨keep, ex, p, k, ap, m, ha', _, _, _, hm, _, rfl⟩ := applyEdgeX_shapeN hc hns hx hxa
      rw [ha] at ha'
      cases ha'
      rw [normX_fact] at hxk
      have hm' := hm
      rw [ht] at hm'
      rw [normX_any_conc hxk (CoreAux.markComp_conc hm')]
    · exact applyEdgeX_cov hpm (AnyTaintExact.concOK_conc _ ⟨t, ht⟩) hc hwf (Or.inr ⟨hns, t, ht⟩)
        (Or.inl htex) hx hxa ⟨t, ht⟩ hl

#print axioms above_row_exact

/-- THE CASE BELOW KEEPS `E` (DESIGN A2): a normal `[any-taint]/E` input strictly below the premise
    path (`c.path = fr.path ++ a :: r`) and a `*/et` target. Every result is normal, at the new path
    end `to.path ++ a :: r`, with the exclusion `E` of the input; every location that `E` admits there
    comes from an admitted location of the input. -/
theorem below_row_exact {fr to : PFact} {fex tex et : Excl} {c x : XFact} {a : Acc} {r : List Acc}
    (hpm : Exact.premOKB fr.mark c.af.fact.mark = true) (hwf : WFX c) (hcar : carriesB c.af = true)
    (hrel : relate fr.path c.af.fact.path = .below (a :: r)) (hto : to.kind = .star et)
    (htex : tex = Excl.empty) (hx : x ∈ (applyEdgeX c fr fex to tex).facts) :
    x.af.demand = false ∧ x.af.fact.path = to.path ++ a :: r ∧ x.ex = c.ex ∧
    ∀ l, coversFX x.af.fact x.ex l → ∃ l1, coversFX c.af.fact c.ex l1 ∧ denX fr fex to tex l1 l := by
  obtain ⟨hk, hc, t, ht⟩ := carriesB_parts hcar
  have hns : c.af.fact.kind.isStar = false := by rw [hk]; rfl
  -- the base layer is normal: no exclusion edge at `r = []`
  have hxa : x.af.demand = false := by
    obtain ⟨y, hy, _, hl⟩ := applyEdgeX_base hx
    rcases hl with hl | ⟨hl, _⟩
    · rw [hl]
      obtain ⟨_, p, k, ap, m, hg, _, _, rfl⟩ := applyEdge_full hy
      unfold CoreAux.geo at hg; rw [hrel] at hg; dsimp only at hg; rw [hto] at hg
      obtain ⟨_, _, _, rfl, rfl⟩ := belowCase_star_cons hg
      rw [Invariant.norm_id_of_nonstar (by exact hns), hc]
      rfl
    · exact hl
  obtain ⟨keep, ex, p, k, ap, m, ha', _, hg, _, hm, _, rfl⟩ := applyEdgeX_shapeN hc hns hx hxa
  unfold CoreAux.geo at hg; rw [hrel] at hg; dsimp only at hg; rw [hto] at hg
  obtain ⟨_, _, rfl, rfl, rfl⟩ := belowCase_star_cons hg
  obtain ⟨_, _, hex1, _⟩ := annX_below_cons hrel ha'
  have hex := hex1 et hto
  subst hex
  have hm' := hm
  rw [ht] at hm'
  refine ⟨hxa, by rw [normX_fact],
    by rw [normX_any_conc (f := ⟨to.base, to.path ++ a :: r, c.af.fact.kind, m⟩) hk
      (CoreAux.markComp_conc hm')], ?_⟩
  intro l hl
  exact applyEdgeX_cov hpm (AnyTaintExact.concOK_conc _ ⟨t, ht⟩) hc hwf (Or.inr ⟨hns, t, ht⟩)
    (Or.inl htex) hx hxa ⟨t, ht⟩ hl

#print axioms below_row_exact

/-! ## 2. Bindings, statements, the field limit, the start, the summary, the cleaner -/

/-- A binding or a statement micro edge (pair form). -/
theorem bindX_exact {ic : PFact} {iex : Excl} {c x : XFact} {e : MicroEdge} {l0 l2 : Loc}
    (hmk : Exact.markEdgeB e.1.mark e.2.mark = true) (hc : c.af.demand = false) (hwf : WFX c)
    (hx : x ∈ (bindX c e).facts) (hxa : x.af.demand = false)
    (hd : denX ic iex x.af.fact x.ex l0 l2) :
    ∃ l1, denX ic iex c.af.fact c.ex l0 l1 ∧ den e.1 e.2 l1 l2 := by
  obtain ⟨hpm, hcm⟩ := Exact.markEdge_ok hmk (applyEdgeX_gate hx)
  obtain ⟨l1, hd1, hd2⟩ := applyEdgeX_exact hpm hcm hc hwf (Or.inl rfl) (Or.inl rfl) hx hxa hd
  exact ⟨l1, hd1, denX_den hd2⟩

#print axioms bindX_exact

/-- A binding or a statement micro edge (location form). -/
theorem bindX_cov {c x : XFact} {e : MicroEdge} {l : Loc}
    (hmk : Exact.markEdgeB e.1.mark e.2.mark = true) (hc : c.af.demand = false) (hwf : WFX c)
    (hx : x ∈ (bindX c e).facts) (hxa : x.af.demand = false)
    (hcc : ∃ t, c.af.fact.mark = .conc t) (hl : coversFX x.af.fact x.ex l) :
    ∃ l1, coversFX c.af.fact c.ex l1 ∧ den e.1 e.2 l1 l := by
  obtain ⟨l0, hd⟩ := coversFX_denX hl
  obtain ⟨l1, hd1, hd2⟩ := bindX_exact (ic := AnyTaintExact.anyP) hmk hc hwf hx hxa hd
  exact ⟨l1, denX_coversFX hd1 hcc, hd2⟩

#print axioms bindX_cov

/-- A normal result of the field limit is its input (no cut). -/
theorem limitFX_normal {counted : Acc → Bool} {L : Nat} {x : XFact}
    (h : (limitFX counted L x).af.demand = false) : limitFX counted L x = x := by
  unfold limitFX at h ⊢
  cases hc : cutPath counted L x.af.fact.path with
  | none => rfl
  | some p =>
    exfalso
    rw [hc] at h
    have h2 : (limitF counted L x.af).demand = false := h
    unfold limitF at h2
    rw [hc] at h2
    have h3 : true = false := h2
    cases h3

theorem limitFX_demand {counted : Acc → Bool} {L : Nat} {x : XFact} (h : x.af.demand = true) :
    (limitFX counted L x).af.demand = true := by
  rw [limitFX_af]
  exact AnyTaintExact.limitF_demand_true h

/-- A normal result of W6T is its input. -/
theorem w6tX_normal {taint : TaintEdges} {e : MicroEdge} {z : XFact}
    (h : (w6tX taint e z).af.demand = false) : w6tX taint e z = z := by
  unfold w6tX at h ⊢
  cases hc : (e.2.kind.isAny && !taint e) with
  | false => exact if_neg Bool.false_ne_true
  | true => rw [hc, if_pos rfl] at h; cases h

theorem applyAllXT_mem {taint : TaintEdges} {c x : XFact} :
    ∀ {es : List MicroEdge}, x ∈ (applyAllXT taint c es).facts →
      ∃ e, e ∈ es ∧ x ∈ (applyEdgeXT taint c e).facts
  | [], h => absurd h List.not_mem_nil
  | e :: es, h => by
    have h' : x ∈ (applyEdgeXT taint c e).facts ++ (applyAllXT taint c es).facts := h
    rcases List.mem_append.mp h' with h1 | h1
    · exact ⟨e, List.mem_cons_self .., h1⟩
    · obtain ⟨e', he', h2⟩ := applyAllXT_mem h1
      exact ⟨e', List.mem_cons_of_mem _ he', h2⟩

/-- A normal result of the refined statement transfer: a result of one micro edge (no W6T
    demotion, no cut), or the input on an untouched base. -/
theorem transferX_normal {taint : TaintEdges} {counted : Acc → Bool} {L : Nat} {s : Stmt}
    {c x : XFact} (h : x ∈ (transferX taint counted L s c).facts) (hxa : x.af.demand = false) :
    (memB c.af.fact.base s.touched = true ∧ ∃ e, e ∈ s.edges ∧ x ∈ (bindX c e).facts) ∨
    (memB c.af.fact.base s.touched = false ∧ x = c) := by
  unfold transferX at h
  cases hm : memB c.af.fact.base s.touched with
  | false =>
    rw [hm, if_neg Bool.false_ne_true] at h
    exact Or.inr ⟨rfl, List.mem_singleton.mp h⟩
  | true =>
    rw [hm, if_pos rfl] at h
    obtain ⟨z0, hz0, rfl⟩ := List.mem_map.mp h
    have e0 := limitFX_normal hxa
    have hz0a : z0.af.demand = false := by rw [← e0]; exact hxa
    rw [e0]
    obtain ⟨e, he, hz⟩ := applyAllXT_mem hz0
    obtain ⟨z, hzb, rfl⟩ := List.mem_map.mp hz
    rw [w6tX_normal hz0a]
    exact Or.inl ⟨rfl, e, he, hzb⟩

/-- A normal statement result comes from a normal input. -/
theorem transferX_demand {taint : TaintEdges} {counted : Acc → Bool} {L : Nat} {s : Stmt}
    {c x : XFact} (h : x ∈ (transferX taint counted L s c).facts) (hxa : x.af.demand = false) :
    c.af.demand = false := by
  rcases transferX_normal h hxa with ⟨_, e, _, hx⟩ | ⟨_, rfl⟩
  · exact applyEdgeX_demand hx hxa
  · exact hxa

/-- THE STATEMENT TRANSFER (pair form): a normal result of `transferX` is a real statement step
    from an admitted pair of the input. Hypothesis: the micro edges satisfy `markEdgeB` (S7). -/
theorem transferX_exact {taint : TaintEdges} {counted : Acc → Bool} {L : Nat} {s : Stmt}
    {ic : PFact} {iex : Excl} {c x : XFact} {l0 l' : Loc}
    (hmk : ∀ e, e ∈ s.edges → Exact.markEdgeB e.1.mark e.2.mark = true)
    (hc : c.af.demand = false) (hwf : WFX c) (hx : x ∈ (transferX taint counted L s c).facts)
    (hxa : x.af.demand = false) (hd : denX ic iex x.af.fact x.ex l0 l') :
    ∃ l, denX ic iex c.af.fact c.ex l0 l ∧ s.step l l' := by
  rcases transferX_normal hx hxa with ⟨_, e, he, hx'⟩ | ⟨hu, rfl⟩
  · obtain ⟨l1, hd1, hd2⟩ := bindX_exact (hmk e he) hc hwf hx' hxa hd
    exact ⟨l1, hd1, Or.inr ⟨e, he, hd2⟩⟩
  · refine ⟨l', hd, Or.inl ⟨?_, rfl⟩⟩
    rw [hd.2.1]
    exact hu

#print axioms transferX_exact

/-- THE STATEMENT TRANSFER (location form). -/
theorem transferX_cov {taint : TaintEdges} {counted : Acc → Bool} {L : Nat} {s : Stmt}
    {c x : XFact} {l' : Loc}
    (hmk : ∀ e, e ∈ s.edges → Exact.markEdgeB e.1.mark e.2.mark = true)
    (hc : c.af.demand = false) (hwf : WFX c) (hx : x ∈ (transferX taint counted L s c).facts)
    (hxa : x.af.demand = false) (hcc : ∃ t, c.af.fact.mark = .conc t)
    (hl : coversFX x.af.fact x.ex l') :
    ∃ l, coversFX c.af.fact c.ex l ∧ s.step l l' := by
  obtain ⟨l0, hd⟩ := coversFX_denX hl
  obtain ⟨l1, hd1, hs⟩ := transferX_exact (ic := AnyTaintExact.anyP) hmk hc hwf hx hxa hd
  exact ⟨l1, denX_coversFX hd1 hcc, hs⟩

#print axioms transferX_cov

/-- THE START OF AN ANNOTATED MUST-PREMISE (DESIGN A2): the start fact of `(j, [any-taint], jex, T)`
    is itself, normal, with its exclusion; it is END-EXACT at the method entry: every admitted
    location of the start fact is an admitted location of the premise. -/
theorem startX_must_end {P : Program} {ok : Loc → Prop} {M : MethodId} {j : PFact} {jex : Excl}
    (hj : j.kind = .any) :
    (startX j true jex).af.demand = false ∧
    EndExactX P ok M j jex (P.entry M) (startX j true jex).af.fact (startX j true jex).ex := by
  refine ⟨by rw [startX_af]; rfl, fun l hl hok => ⟨l, ?_, Flow.start M l, hok⟩⟩
  have hl' : coversFX (normX ⟨⟨j, false⟩, jex⟩).af.fact (normX ⟨⟨j, false⟩, jex⟩).ex l := hl
  have ⟨_, _, t, ht, _⟩ := hl'
  rw [normX_fact] at ht
  rw [normX_any_conc hj ⟨t, ht⟩] at hl'
  exact coversX_of_coversFX hl'

#print axioms startX_must_end

/-- A normal result of the refined summary application is a normal result of the core operation
    with the summary edge, and the summary edge is normal. -/
theorem applySummaryX_normal {a g r : XFact} {j : PFact} {jex : Excl}
    (hr : r ∈ (applySummaryX a j jex g).facts) (hra : r.af.demand = false) :
    r ∈ (applyEdgeX a j jex g.af.fact g.ex).facts ∧ g.af.demand = false := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
  rw [normX_af] at hra
  have hn := Exact.norm_id_of_demand hra
  rw [hn] at hra
  obtain ⟨hxa, hga⟩ := Exact.or_eq_false hra
  refine ⟨?_, hga⟩
  have e : normX ⟨AFact.norm ⟨x.af.fact, x.af.demand || g.af.demand⟩, x.ex⟩ = x := by
    rw [hn]
    have e2 : (x.af.demand || g.af.demand) = x.af.demand := by rw [hxa, hga]; rfl
    rw [e2]
    exact normX_of_wf (applyEdgeX_wf hx)
  rw [e]
  exact hx

#print axioms applySummaryX_normal

/-- THE SUMMARY APPLICATION WITH AN ANNOTATED CONCLUSION (pair form; DESIGN A2). A normal result of
    `applySummaryX a j jex g` (the summary `(j, jex) → g`, an `[any-taint]/E'` conclusion carries
    `E'`, a must-premise can carry `jex`) on an added fact `a` and a summary conclusion `g`, both in
    normal form, is a real composition: an admitted pair of `a` and an admitted pair of the summary
    edge (both its exclusions read); the added fact and the summary edge are normal. Hypotheses: the
    mark conditions of `Exact.applyEdge_exact`; a premise exclusion meets only a non-`*` concrete
    added fact (`hfx`; a restricted run is concrete). -/
theorem applySummaryX_exact {ic j : PFact} {iex jex : Excl} {a g r : XFact} {l0 l2 : Loc}
    (hpm : Exact.premOKB j.mark a.af.fact.mark = true)
    (hcm : Exact.concOKB g.af.fact.mark a.af.fact.mark = true) (haw : WFX a) (hgw : WFX g)
    (hfx : jex = Excl.empty ∨ (a.af.fact.kind.isStar = false ∧ ∃ t, a.af.fact.mark = .conc t))
    (hr : r ∈ (applySummaryX a j jex g).facts) (hra : r.af.demand = false)
    (hd : denX ic iex r.af.fact r.ex l0 l2) :
    a.af.demand = false ∧ g.af.demand = false ∧
      ∃ l1, denX ic iex a.af.fact a.ex l0 l1 ∧ denX j jex g.af.fact g.ex l1 l2 := by
  obtain ⟨hrx, hga⟩ := applySummaryX_normal hr hra
  have haa := applyEdgeX_demand hrx hra
  exact ⟨haa, hga, applyEdgeX_exact hpm hcm haa haw hfx (htx_of_wf hgw) hrx hra hd⟩

#print axioms applySummaryX_exact

/-- THE SUMMARY APPLICATION WITH AN ANNOTATED CONCLUSION (location form, END-EXACT): every admitted
    location of a normal result is the end of an admitted summary pair from an admitted location of
    the (concrete) added fact. -/
theorem applySummaryX_cov {j : PFact} {jex : Excl} {a g r : XFact} {l : Loc}
    (hpm : Exact.premOKB j.mark a.af.fact.mark = true)
    (hcm : Exact.concOKB g.af.fact.mark a.af.fact.mark = true) (haw : WFX a) (hgw : WFX g)
    (hfx : jex = Excl.empty ∨ (a.af.fact.kind.isStar = false ∧ ∃ t, a.af.fact.mark = .conc t))
    (hac : ∃ t, a.af.fact.mark = .conc t)
    (hr : r ∈ (applySummaryX a j jex g).facts) (hra : r.af.demand = false)
    (hl : coversFX r.af.fact r.ex l) :
    ∃ l1, coversFX a.af.fact a.ex l1 ∧ denX j jex g.af.fact g.ex l1 l := by
  obtain ⟨hrx, _⟩ := applySummaryX_normal hr hra
  have haa := applyEdgeX_demand hrx hra
  exact applyEdgeX_cov hpm hcm haa haw hfx (htx_of_wf hgw) hrx hra hac hl

#print axioms applySummaryX_cov

/-! ### The cleaner -/

/-- A normal cleaner result comes from a normal input. -/
theorem cleanResX_demand {cl : Cleaner} {c x : XFact} (hx : x ∈ (cleanResX cl c).facts)
    (hxa : x.af.demand = false) : c.af.demand = false := by
  unfold cleanResX at hx
  split at hx
  · rw [List.mem_singleton.mp hx] at hxa; exact hxa
  · split at hx
    · split at hx
      · exact absurd hx List.not_mem_nil
      · rw [List.mem_singleton.mp hx] at hxa; exact hxa
    · rw [List.mem_singleton.mp hx] at hxa; exact hxa
    · exact absurd hx List.not_mem_nil
  · split at hx
    · split at hx
      · unfold partX at hx
        split at hx
        · split at hx
          · rw [List.mem_singleton.mp hx] at hxa; exact hxa
          · rcases List.mem_cons.mp hx with h1 | h1
            · rw [h1] at hxa; exact hxa
            · rw [List.mem_singleton.mp h1] at hxa; exact hxa
          · rw [List.mem_singleton.mp hx] at hxa
            rcases Exact.concPart_cases cl c.af with ⟨_, _, _, he⟩ | he <;> rw [he] at hxa
            · exact hxa
            · cases hxa
        · rw [List.mem_singleton.mp hx] at hxa
          rcases Exact.concPart_cases cl c.af with ⟨_, _, _, he⟩ | he <;> rw [he] at hxa
          · exact hxa
          · cases hxa
      · rw [List.mem_singleton.mp hx] at hxa; exact hxa
    · rw [List.mem_singleton.mp hx] at hxa; exact hxa
    · rw [List.mem_singleton.mp hx] at hxa
      exact absurd (Exact.norm_true_demand c.af.fact) (by rw [hxa]; exact Bool.false_ne_true)

/-- The exclusion `{f}` excludes the step `f`. -/
theorem set_self_not_admits (f : Acc) : (Excl.set [f]).admits [f] = false := by
  show (!(Nat.beq f f || false)) = false
  rw [Nat.beq_refl]
  rfl

/-- A cleaner strictly below a fact, in a part that the exclusion `ex` excludes, cleans no admitted
    location of the fact. -/
theorem cleansB_excluded {cl : Cleaner} {f i : PFact} {iex ex : Excl} {l0 l : Loc} {r : List Acc}
    (hr : relate cl.path f.path = .above r) (hna : ex.admits r = false) (hd : denX i iex f ex l0 l) :
    cl.cleansB l = false := by
  cases hdp : dropPrefix cl.path l.path with
  | none => exact Exact.cleansB_none hdp
  | some σ =>
    exfalso
    have hl := Exact.dropPrefix_some hdp
    have hcp := Exact.relate_above hr
    obtain ⟨a, r', rfl⟩ := above_cons hr
    have h := denX_fex hd (a :: r' ++ σ) (by rw [hl, hcp, List.append_assoc])
    rw [admits_cons_append] at h
    rw [h] at hna
    cases hna

/-- A concrete mark that the cleaner does not clean: no location of the fact is cleaned. -/
theorem cleansB_markX {cl : Cleaner} {f i : PFact} {iex ex : Excl} {l0 l : Loc} {t : Mark}
    (hm : f.mark = .conc t) (hb : cl.markB t = false) (hd : denX i iex f ex l0 l) :
    cl.cleansB l = false := by
  apply Exact.cleansB_mark
  have hlm : l.mark = f.mark.out l0.mark := hd.2.2.2.1
  rw [hm] at hlm
  rw [hlm]
  exact hb

/-- The `addEx` row (an abstract mark; no exclusion on such a fact). -/
theorem addEx_rowX {cl : Cleaner} {c : XFact} {ic : PFact} {iex : Excl} {l0 l : Loc} {t : Mark}
    (hab : Exact.absB c.af.fact.mark = true) (hcm : cl.mark = some t)
    (hd : denX ic iex ⟨c.af.fact.base, c.af.fact.path, c.af.fact.kind, addEx c.af.fact.mark t⟩ c.ex
      l0 l) :
    denX ic iex c.af.fact c.ex l0 l ∧ cl.cleansB l = false := by
  obtain ⟨hd', hb⟩ := Exact.addEx_den hab (denX_den hd)
  refine ⟨denX_of_den hd' (denX_iex hd) (fun τ hτ => denX_fex hd τ hτ), Exact.cleansB_mark ?_⟩
  rw [Exact.markB_some hcm]
  exact hb

/-- The base `part` row (`concPart`, no exclusion). -/
theorem concPart_rowX {cl : Cleaner} {c : XFact} {ic : PFact} {iex : Excl} {l0 l : Loc} {t : Mark}
    (hpos : cleanPos cl c.af.fact = .part) (hm : c.af.fact.mark = .conc t) (hb : cl.markB t = true)
    (hxa : (concPart cl c.af).demand = false)
    (hd : denX ic iex (concPart cl c.af).fact Excl.empty l0 l) :
    denX ic iex c.af.fact c.ex l0 l ∧ cl.cleansB l = false := by
  have hmem : concPart cl c.af ∈ (cleanRes cl c.af).facts := by
    unfold cleanRes
    rw [hpos]
    dsimp only
    rw [hm]
    dsimp only
    rw [hb, if_pos rfl]
    exact List.mem_singleton_self _
  obtain ⟨hden, hcl⟩ := Exact.cleanRes_exact hmem hxa (denX_den hd)
  refine ⟨denX_of_den hden (denX_iex hd) ?_, hcl⟩
  intro τ' hτ'
  rcases Exact.concPart_cases cl c.af with ⟨_, _, _, he⟩ | he
  · rw [he] at hd
    obtain ⟨_, _, _, _, _, σ, τ, _, hlp, _, hF, _⟩ := hd
    have hτ : τ = [] := hF
    rw [cont_unique hτ' hlp, hτ]
    exact Exact.admits_nil _
  · rw [he] at hxa; cases hxa

/-- THE CLEANER (pair form; DESIGN A2). A normal result of `cleanResX` on an input in normal form
    denotes only admitted pairs of the input whose end location the cleaner does not clean. This
    includes the A2 rows: a cleaner in the EXCLUDED part (`disjoint`), `atAndBelow` at `P.f` (the
    result `E ∪ {f}`), and `below` at `P.f` (the result `E ∪ {f}` and the new `$` fact
    `(b, P.f, $, T)`: the `below` cleaner does not clean `P.f` itself). -/
theorem cleanResX_exact {cl : Cleaner} {c x : XFact} {ic : PFact} {iex : Excl} {l0 l : Loc}
    (hwf : WFX c) (hx : x ∈ (cleanResX cl c).facts) (hxa : x.af.demand = false)
    (hd : denX ic iex x.af.fact x.ex l0 l) :
    denX ic iex c.af.fact c.ex l0 l ∧ cl.cleansB l = false := by
  unfold cleanResX at hx
  cases hq : cleanPosX cl c with
  | disjoint =>
    rw [hq] at hx
    have hxc : x = c := List.mem_singleton.mp hx
    subst hxc
    refine ⟨hd, ?_⟩
    rcases cleanPosX_cases cl x with hp | ⟨_, r, hr, hna⟩
    · rw [hq] at hp
      exact Exact.cleanPos_disjoint hp.symm (denX_den hd)
    · exact cleansB_excluded hr hna hd
  | inside =>
    rw [hq] at hx
    have hp : cleanPos cl c.af.fact = .inside := by
      rcases cleanPosX_cases cl c with hp | ⟨hp, _⟩
      · rw [← hp, hq]
      · rw [hq] at hp; cases hp
    revert hx
    cases hm : c.af.fact.mark with
    | conc t =>
      intro hx
      dsimp only at hx
      cases hb : cl.markB t with
      | true => rw [hb, if_pos rfl] at hx; exact absurd hx List.not_mem_nil
      | false =>
        rw [hb, if_neg Bool.false_ne_true] at hx
        have hxc : x = c := List.mem_singleton.mp hx
        subst hxc
        exact ⟨hd, cleansB_markX hm hb hd⟩
    | star =>
      cases hcm : cl.mark with
      | none => intro hx; exact absurd hx List.not_mem_nil
      | some t =>
        intro hx
        have hxc := List.mem_singleton.mp hx
        subst hxc
        rw [← hm] at hd
        exact addEx_rowX (by rw [hm]; rfl) hcm hd
    | starEx xs =>
      cases hcm : cl.mark with
      | none => intro hx; exact absurd hx List.not_mem_nil
      | some t =>
        intro hx
        have hxc := List.mem_singleton.mp hx
        subst hxc
        rw [← hm] at hd
        exact addEx_rowX (by rw [hm]; rfl) hcm hd
  | part =>
    rw [hq] at hx
    have hp : cleanPos cl c.af.fact = .part := by
      rcases cleanPosX_cases cl c with hp | ⟨hp, _⟩
      · rw [← hp, hq]
      · rw [hq] at hp; cases hp
    revert hx
    cases hm : c.af.fact.mark with
    | conc t =>
      intro hx
      dsimp only at hx
      cases hb : cl.markB t with
      | false =>
        rw [hb, if_neg Bool.false_ne_true] at hx
        have hxc : x = c := List.mem_singleton.mp hx
        subst hxc
        exact ⟨hd, cleansB_markX hm hb hd⟩
      | true =>
        rw [hb, if_pos rfl] at hx
        unfold partX at hx
        cases hcar : carriesB c.af with
        | false =>
          rw [hcar, if_neg Bool.false_ne_true] at hx
          have hxc := List.mem_singleton.mp hx
          subst hxc
          exact concPart_rowX hp hm hb hxa hd
        | true =>
          rw [hcar, if_pos rfl] at hx
          obtain ⟨hk, _, _⟩ := carriesB_parts hcar
          split at hx
          · -- `atAndBelow` at `P.f`: `E ∪ {f}`
            next f hrch hrel =>
            have hxc := List.mem_singleton.mp hx
            subst hxc
            refine ⟨denX_fex_mono (fun τ h => (admits_union_iff h).1) hd, ?_⟩
            exact cleansB_excluded (f := c.af.fact) (ex := c.ex.union (.set [f])) hrel
              (by rw [CoreAux.Excl.admits_union, set_self_not_admits, Bool.and_false]) hd
          · -- `below` at `P.f`: `E ∪ {f}`, and the position itself `(b, P.f, $, T)`
            next f hrch hrel =>
            rcases List.mem_cons.mp hx with hxc | hxc
            · subst hxc
              refine ⟨denX_fex_mono (fun τ h => (admits_union_iff h).1) hd, ?_⟩
              exact cleansB_excluded (f := c.af.fact) (ex := c.ex.union (.set [f])) hrel
                (by rw [CoreAux.Excl.admits_union, set_self_not_admits, Bool.and_false]) hd
            · have hxc' := List.mem_singleton.mp hxc
              subst hxc'
              -- the step `f` is admitted (else `cleanPosX` is `disjoint`)
              have hadm : c.ex.admits [f] = true := by
                unfold cleanPosX at hq
                rw [hrel] at hq
                dsimp only at hq
                cases h : c.ex.admits [f] with
                | true => rfl
                | false => rw [h, if_neg Bool.false_ne_true] at hq; cases hq
              have hcl : cl.path = c.af.fact.path ++ [f] := Exact.relate_above hrel
              obtain ⟨h0b, hlb, h0m, hlm, hps, σ, τ, h0p, hlp, hI, hF, hie, _⟩ := hd
              have hτ : τ = [] := hF
              subst hτ
              rw [List.append_nil] at hlp
              refine ⟨⟨h0b, hlb, h0m, hlm, hps, σ, [f], h0p, hlp, hI, by rw [hk]; trivial, hie, hadm⟩, ?_⟩
              apply Exact.cleansB_some (σ := [])
              · rw [hlp, ← hcl]
                exact Exact.dropPrefix_self _
              · rw [hrch]; rfl
          · have hxc := List.mem_singleton.mp hx
            subst hxc
            exact concPart_rowX hp hm hb hxa hd
    | star =>
      cases hcm : cl.mark with
      | none =>
        intro hx
        have hxc := List.mem_singleton.mp hx
        subst hxc
        exact absurd (Exact.norm_true_demand c.af.fact) (by rw [hxa]; exact Bool.false_ne_true)
      | some t =>
        intro hx
        have hxc := List.mem_singleton.mp hx
        subst hxc
        rw [← hm] at hd
        exact addEx_rowX (by rw [hm]; rfl) hcm hd
    | starEx xs =>
      cases hcm : cl.mark with
      | none =>
        intro hx
        have hxc := List.mem_singleton.mp hx
        subst hxc
        exact absurd (Exact.norm_true_demand c.af.fact) (by rw [hxa]; exact Bool.false_ne_true)
      | some t =>
        intro hx
        have hxc := List.mem_singleton.mp hx
        subst hxc
        rw [← hm] at hd
        exact addEx_rowX (by rw [hm]; rfl) hcm hd

#print axioms cleanResX_exact

/-- THE CLEANER (location form). -/
theorem cleanResX_cov {cl : Cleaner} {c x : XFact} {l : Loc}
    (hwf : WFX c) (hx : x ∈ (cleanResX cl c).facts) (hxa : x.af.demand = false)
    (hcc : ∃ t, c.af.fact.mark = .conc t) (hl : coversFX x.af.fact x.ex l) :
    coversFX c.af.fact c.ex l ∧ cl.cleansB l = false := by
  obtain ⟨l0, hd⟩ := coversFX_denX hl
  obtain ⟨hd1, hcl⟩ := cleanResX_exact (ic := AnyTaintExact.anyP) hwf hx hxa hd
  exact ⟨denX_coversFX hd1 hcc, hcl⟩

#print axioms cleanResX_cov

/-- THE `below` CLEANER AT `P.f` ON `[any-taint]/E` (DESIGN A2). For a normal `[any-taint]/E` fact
    `(b, P, [any-taint], E, T)` and a cleaner of the mark `T` strictly below `P.f` (`f` admitted by
    `E`), the refined cleaner gives the NEW `$` fact `(b, P.f, $, T)`, in the normal layer; its
    location `(b, P.f, T)` is an admitted location of the input that the cleaner does not clean (the
    `below` cleaner cleans only strictly below `P.f`). So the new fact is real. -/
theorem below_new_fact_real {cl : Cleaner} {c : XFact} {f : Acc} {t : Mark}
    (hcar : carriesB c.af = true) (hbase : cl.base = c.af.fact.base) (hreach : cl.reach = .below)
    (hrel : relate cl.path c.af.fact.path = .above [f]) (hm : c.af.fact.mark = .conc t)
    (hb : cl.markB t = true) (hadm : c.ex.admits [f] = true) :
    (⟨⟨⟨c.af.fact.base, c.af.fact.path ++ [f], .exact, c.af.fact.mark⟩, c.af.demand⟩, Excl.empty⟩ :
      XFact) ∈ (cleanResX cl c).facts ∧ c.af.demand = false ∧
    coversFX c.af.fact c.ex ⟨c.af.fact.base, c.af.fact.path ++ [f], t⟩ ∧
    cl.cleansB ⟨c.af.fact.base, c.af.fact.path ++ [f], t⟩ = false := by
  obtain ⟨hk, hc, _⟩ := carriesB_parts hcar
  have hpos : cleanPosX cl c = .part := by
    unfold cleanPosX
    rw [hrel]
    dsimp only
    rw [hadm, if_pos rfl]
    unfold cleanPos
    rw [hbase, Nat.beq_refl, if_pos rfl, hrel]
    dsimp only
    rw [hk]
  have hcl : cl.path = c.af.fact.path ++ [f] := Exact.relate_above hrel
  refine ⟨?_, hc, ⟨rfl, ⟨[f], rfl, by rw [hk]; trivial, hadm⟩, t, hm, rfl⟩, ?_⟩
  · unfold cleanResX
    rw [hpos]
    dsimp only
    rw [hm]
    dsimp only
    rw [hb, if_pos rfl]
    unfold partX
    rw [hcar, if_pos rfl, hreach, hrel]
    dsimp only
    rw [hm]
    exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  · apply Exact.cleansB_some (σ := [])
    · show dropPrefix cl.path (c.af.fact.path ++ [f]) = some []
      rw [hcl]
      exact Exact.dropPrefix_self _
    · rw [hreach]; rfl

#print axioms below_new_fact_real

/-- THE `atAndBelow` / `below` CLEANERS AT `P.f` (DESIGN A2): on a normal `[any-taint]/E` fact the
    result `[any-taint]/(E ∪ {f})` stays normal, and every location that `E ∪ {f}` admits is an
    admitted location of the input that the cleaner does not clean. -/
theorem clean_rows_exact {cl : Cleaner} {c : XFact} {f : Acc}
    (hwf : WFX c) (hcar : carriesB c.af = true)
    (hmem : (⟨c.af, c.ex.union (.set [f])⟩ : XFact) ∈ (cleanResX cl c).facts) :
    ∀ l, coversFX c.af.fact (c.ex.union (.set [f])) l →
      coversFX c.af.fact c.ex l ∧ cl.cleansB l = false := by
  obtain ⟨_, hc, t, ht⟩ := carriesB_parts hcar
  intro l hl
  exact cleanResX_cov (x := ⟨c.af, c.ex.union (.set [f])⟩) hwf hmem hc ⟨t, ht⟩ hl

#print axioms clean_rows_exact

/-! ### Marks and tails of the refined operations -/

theorem applyEdgeX_abs {c x : XFact} {fr to : PFact} {fex tex : Excl}
    (he : Exact.markEdgeB fr.mark to.mark = true) (hc : Exact.absB c.af.fact.mark = true)
    (hx : x ∈ (applyEdgeX c fr fex to tex).facts) : Exact.absB x.af.fact.mark = true := by
  obtain ⟨y, hy, hxy, _⟩ := applyEdgeX_base hx
  rw [hxy]
  exact Exact.applyEdge_abs he hc hy

theorem applySummaryX_abs {a g r : XFact} {j : PFact} {jex : Excl}
    (hA : Exact.absB a.af.fact.mark = true)
    (hG : Exact.absB j.mark = true → Exact.absB g.af.fact.mark = true)
    (hr : r ∈ (applySummaryX a j jex g).facts) : Exact.absB r.af.fact.mark = true := by
  obtain ⟨y, hy, hry, _⟩ := applySummaryX_base hr
  obtain ⟨x, hx, hxm⟩ := Exact.applySummary_mark hy
  obtain ⟨hgx, hcx⟩ := Exact.applyEdge_mark hx
  rw [hry, hxm]
  exact Exact.comp_abs (hG (Exact.gate_abs hgx hA)) hA hcx

theorem cleanResX_abs {cl : Cleaner} {c x : XFact} (hc : Exact.absB c.af.fact.mark = true)
    (hwf : WFX c) (hx : x ∈ (cleanResX cl c).facts) : Exact.absB x.af.fact.mark = true := by
  rcases cleanResX_base hwf hx with ⟨y, hy, hxy, _⟩ | ⟨_, _, _, _, rfl⟩
  · rw [hxy]; exact Exact.cleanRes_abs hc hy
  · exact hc

theorem applyEdgeX_nonstar {c x : XFact} {fr to : PFact} {fex tex : Excl}
    (hc : c.af.fact.kind.isStar = false) (hx : x ∈ (applyEdgeX c fr fex to tex).facts) :
    x.af.fact.kind.isStar = false := by
  obtain ⟨y, hy, hxy, _⟩ := applyEdgeX_base hx
  rw [hxy]
  exact Confirmed.applyEdge_nonstar hc hy

theorem applySummaryX_nonstar {a g r : XFact} {j : PFact} {jex : Excl}
    (ha : a.af.fact.kind.isStar = false) (hr : r ∈ (applySummaryX a j jex g).facts) :
    r.af.fact.kind.isStar = false := by
  obtain ⟨y, hy, hry, _⟩ := applySummaryX_base hr
  obtain ⟨x, hx, rfl⟩ := Invariant.applySummary_shape hy
  have h2 := Confirmed.applyEdge_nonstar ha hx
  rw [hry, Confirmed.norm_nonstar (x := ⟨x.fact, x.demand || g.af.demand⟩) h2]
  exact h2

theorem transferX_nonstar {taint : TaintEdges} {counted : Acc → Bool} {L : Nat} {s : Stmt}
    {c x : XFact} (hc : c.af.fact.kind.isStar = false)
    (hx : x ∈ (transferX taint counted L s c).facts) : x.af.fact.kind.isStar = false := by
  obtain ⟨y, hy, hxy, _⟩ := transferX_base hx
  obtain ⟨y0, hy0, hle⟩ := transferT_mem hy
  rw [hxy, ← hle.fact]
  exact Confirmed.transfer_nonstar hc hy0

theorem cleanResX_nonstar {cl : Cleaner} {c x : XFact} (hwf : WFX c)
    (hc : c.af.fact.kind.isStar = false) (hx : x ∈ (cleanResX cl c).facts) :
    x.af.fact.kind.isStar = false := by
  rcases cleanResX_base hwf hx with ⟨y, hy, hxy, _⟩ | ⟨_, _, _, _, rfl⟩
  · rw [hxy]; exact Confirmed.cleanRes_nonstar hc hy
  · rfl

theorem limitFX_nonstar {counted : Acc → Bool} {L : Nat} {x : XFact}
    (h : x.af.fact.kind.isStar = false) : (limitFX counted L x).af.fact.kind.isStar = false := by
  rw [limitFX_af]
  exact Confirmed.limitF_nonstar h

/-! ## 3. Run 1 with the exclusion (`D6X`): exactness -/

/-- The well-formedness motive: every edge conclusion is in normal form. -/
def WFObj6 : XObj6 → Prop
  | .edge _ _ _ f => WFX f
  | _ => True

/-- The non-`*` motive of run 1. -/
def NSObj6 : XObj6 → Prop
  | .edge _ i _ f => i.kind.isStar = false → f.af.fact.kind.isStar = false
  | _ => True

section Run1
variable {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
  {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId}

/-- Every edge conclusion of `D6X` is in normal form (no hypothesis). -/
theorem D6X_wf {o : XObj6} (h : D6X P taint counted L α sinks roots o) : WFObj6 o := by
  induction h with
  | root => trivial
  | @start M i _ _ => exact startX_wf i false Excl.empty
  | @step M i n f n' s f' _ _ hf ih => exact transferX_wf ih hf
  | reqStmt => trivial
  | pass _ _ _ ih => exact ih
  | added => trivial
  | initA => trivial
  | @ret M i n f n' c e1 a j g r e2 r' _ _ _ _ _ _ _ _ _ hr' _ _ _ =>
    exact limitFX_wf counted L (applyEdgeX_wf hr')
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial
  | @clean M i n f n' cl f' _ _ hf ih => exact cleanResX_wf ih hf
  | reqClean => trivial
  | filt _ _ _ ih => exact ih

#print axioms D6X_wf

theorem D6X_wf_edge {M : MethodId} {i : PFact} {n : Node} {f : XFact}
    (h : D6X P taint counted L α sinks roots (.edge M i n f)) : WFX f := D6X_wf h

/-- Under a non-`*` premise every conclusion of `D6X` is non-`*` (no hypothesis). -/
theorem D6X_NS {o : XObj6} (h : D6X P taint counted L α sinks roots o) : NSObj6 o := by
  induction h with
  | root => trivial
  | @start M i _ _ =>
    intro hi
    show (startX i false Excl.empty).af.fact.kind.isStar = false
    rw [startX_af]
    exact Confirmed.startFact_nonstar hi
  | @step M i n f n' s f' _ _ hf ih => exact fun hi => transferX_nonstar (ih hi) hf
  | reqStmt => trivial
  | pass _ _ _ ih => exact ih
  | added => trivial
  | initA => trivial
  | @ret M i n f n' c e1 a j g r e2 r' _ _ _ ha _ _ _ hr _ hr' ihF _ _ =>
    intro hi
    exact limitFX_nonstar (applyEdgeX_nonstar
      (applySummaryX_nonstar (applyEdgeX_nonstar (ihF hi) ha) hr) hr')
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial
  | @clean M i n f n' cl f' hF _ hf ih => exact fun hi => cleanResX_nonstar (D6X_wf_edge hF) (ih hi) hf
  | reqClean => trivial
  | filt _ _ _ ih => exact ih

#print axioms D6X_NS

/-- THE MOTIVE ON EVERY OBJECT OF RUN 1 (`D6X`). An abstract premise mark gives an abstract
    conclusion mark, and a normal edge (also `[any-taint]/E`) is PAIR-EXACT on the admitted locations:
    every pair of `denX` (the conclusion exclusion read) to a valid end location is a concrete flow
    from a valid start location. Hypotheses: those of `AnyTaintExact.D6T_edgeOK` (S7 `MarkWF`,
    `FiltOK`, `BackOK`). -/
theorem D6X_edgeOK {ok : Loc → Prop} (hmw : Exact.MarkWF P) (hfo : Exact.FiltOK P ok)
    (hbo : Exact.BackOK P ok) {o : XObj6}
    (h : D6X P taint counted L α sinks roots o) : EdgeOK6X P ok o := by
  induction h with
  | root => trivial
  | @start M i _ _ =>
    refine ⟨fun hi => ?_, fun ha l0 l hd hok => ?_⟩
    · show Exact.absB (startX i false Excl.empty).af.fact.mark = true
      rw [startX_af, startT_mark]
      exact hi
    · have hd' : den i (startFact i).fact l0 l := denX_den hd
      have e := Exact.startFact_exact ha hd'
      subst e
      exact ⟨Flow.start M l, hok⟩
  | @step M i n f n' s f' hF hE hf ih =>
    refine ⟨fun hi => ?_, fun ha l0 l hd hok => ?_⟩
    · obtain ⟨y, hy, hfy, _⟩ := transferX_base hf
      obtain ⟨y0, hy0, hle⟩ := transferT_mem hy
      rw [hfy, ← hle.fact]
      exact Exact.transfer_abs (hmw.stmt _ _ _ _ hE) (ih.1 hi) hy0
    · have hfa := transferX_demand hf ha
      obtain ⟨l1, hd1, hs⟩ := transferX_exact (hmw.stmt _ _ _ _ hE) hfa (D6X_wf_edge hF) hf ha hd
      have hok1 : ok l1 := by
        rcases hs with ⟨-, rfl⟩ | ⟨e, he, hde⟩
        · exact hok
        · exact hbo.stmt _ _ _ _ hE e he _ _ hde hok
      obtain ⟨hfl, hok0⟩ := ih.2 hfa l0 l1 hd1 hok1
      exact ⟨Flow.step hfl hE hs, hok0⟩
  | reqStmt => trivial
  | @pass M i n f n' c _ hE hm ih =>
    refine ⟨ih.1, fun ha l0 l hd hok => ?_⟩
    obtain ⟨hfl, hok0⟩ := ih.2 ha l0 l hd hok
    refine ⟨Flow.pass hfl hE ?_, hok0⟩
    rw [hd.2.1]
    exact hm
  | added => trivial
  | initA => trivial
  | @ret M i n f n' c e1 a j g r e2 r' hF hE he1 ha _ happ hG hr he2 hr' ihF _ ihG =>
    refine ⟨fun hi => ?_, fun hla l0 l hd hok => ?_⟩
    · have hA := applyEdgeX_abs (hmw.toC _ _ _ _ hE e1 he1) (ihF.1 hi) ha
      have hR := applySummaryX_abs hA (fun hJ => ihG.1 hJ) hr
      rw [limitFX_af, Exact.limitF_mark]
      exact applyEdgeX_abs (hmw.fromC _ _ _ _ hE e2 he2) hR hr'
    · have e0 := limitFX_normal hla
      have hra' : r'.af.demand = false := by rw [← e0]; exact hla
      rw [e0] at hd
      have hra := applyEdgeX_demand hr' hra'
      -- the binding back to the caller
      obtain ⟨l2, hd2, hde2⟩ := bindX_exact (hmw.fromC _ _ _ _ hE e2 he2) hra
        (applySummaryX_wf hr) hr' hra' hd
      have hok2 : ok l2 := hbo.fromC _ _ _ _ hE e2 he2 _ _ hde2 hok
      -- the summary edge, its conclusion in normal form (`[any-taint]/E` or no exclusion)
      obtain ⟨hrx, hga⟩ := applySummaryX_normal hr hra
      have haa := applyEdgeX_demand hrx hra
      have hfa := applyEdgeX_demand ha haa
      obtain ⟨l1', hd1', hdg⟩ := applyEdgeX_exact
        (Exact.premOK_of_sub (Exact.applicable_markSub happ))
        (Exact.concOK_of (fun hA => ihG.1 (Exact.gate_abs (applyEdgeX_gate hrx) hA))) haa
        (applyEdgeX_wf ha) (Or.inl rfl) (htx_of_wf (D6X_wf_edge hG)) hrx hra hd2
      obtain ⟨hflG, hok1'⟩ := ihG.2 hga l1' l2 hdg hok2
      -- the binding into the callee
      obtain ⟨l1, hd1, hde1⟩ := bindX_exact (hmw.toC _ _ _ _ hE e1 he1) hfa (D6X_wf_edge hF) ha
        haa hd1'
      have hok1 : ok l1 := hbo.toC _ _ _ _ hE e1 he1 _ _ hde1 hok1'
      obtain ⟨hflD, hok0⟩ := ihF.2 hfa l0 l1 hd1 hok1
      exact ⟨Flow.call hflD hE he1 hde1 hflG he2 hde2, hok0⟩
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial
  | @clean M i n f n' cl f' hF hE hf ih =>
    refine ⟨fun hi => cleanResX_abs (ih.1 hi) (D6X_wf_edge hF) hf, fun ha l0 l hd hok => ?_⟩
    have hfa := cleanResX_demand hf ha
    obtain ⟨hd1, hcl⟩ := cleanResX_exact (D6X_wf_edge hF) hf ha hd
    obtain ⟨hfl, hok0⟩ := ih.2 hfa l0 l hd1 hok
    exact ⟨Flow.clean hfl hE hcl, hok0⟩
  | reqClean => trivial
  | @filt M i n f n' b may _ hE hp ih =>
    refine ⟨ih.1, fun ha l0 l hd hok => ?_⟩
    obtain ⟨hfl, hok0⟩ := ih.2 ha l0 l hd hok
    refine ⟨Flow.filt hfl hE ?_, hok0⟩
    intro hb
    obtain ⟨-, hlb, -, -, -, σ, τ, -, hlp, -, -, -, -⟩ := hd
    exact hfo _ _ _ _ _ hE f.af.fact.path τ l (hp (hlb.symm.trans hb)) hlp hok hb

#print axioms D6X_edgeOK

/-- RUN 1 IS EXACT ON THE ADMITTED LOCATIONS (`FiltUp` form). Every pair of a NORMAL edge of `D6X`
    (an `[any-taint]/E` conclusion included, its exclusion read) is a concrete flow. Hypotheses: S7
    (`MarkWF P`), `FiltUp P`. -/
theorem edge_exact6X (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P)
    {M : MethodId} {i : PFact} {n : Node} {f : XFact} {l0 l : Loc}
    (h : D6X P taint counted L α sinks roots (.edge M i n f)) (ha : f.af.demand = false)
    (hd : denX i Excl.empty f.af.fact f.ex l0 l) : Flow P M l0 n l :=
  ((D6X_edgeOK (ok := fun _ => True) hmw (Exact.filtUp_ok hup) (Exact.backOK_true P) h).2
    ha l0 l hd trivial).1

#print axioms edge_exact6X

/-- RUN 1 IS EXACT FOR VALID ADMITTED LOCATIONS (prefix-closed type filters; S7, S13): every pair
    of a normal edge of `D6X` to a valid end location is a concrete flow from a valid start
    location. -/
theorem edge_exact_valid6X {ok : Loc → Prop} (hmw : Exact.MarkWF P) (hv : Exact.FiltValid P ok)
    (hbo : Exact.BackOK P ok)
    {M : MethodId} {i : PFact} {n : Node} {f : XFact} {l0 l : Loc}
    (h : D6X P taint counted L α sinks roots (.edge M i n f)) (ha : f.af.demand = false)
    (hd : denX i Excl.empty f.af.fact f.ex l0 l) (hok : ok l) : Flow P M l0 n l ∧ ok l0 :=
  (D6X_edgeOK hmw (Exact.filtValid_ok hv) hbo h).2 ha l0 l hd hok

#print axioms edge_exact_valid6X

end Run1

/-! ## 4. The support and the confirmation of run 1 -/

/-- A triggered refined check reads the ADMITTED location set: the sink pattern overlaps it. -/
theorem checkX_overlap {i : PFact} {f : XFact} {s : PFact} (h : checkX i f s = .triggered) :
    overlapX f.af.fact f.ex s Excl.empty = true := by
  unfold checkX at h
  cases ho : overlapX f.af.fact f.ex s Excl.empty with
  | true => rfl
  | false => rw [ho, if_neg Bool.false_ne_true] at h; cases h

/-- Two overlapping location sets with exclusions have a common ADMITTED path (marks ignored). -/
theorem overlapX_common {a s : PFact} {aex sex : Excl} (h : overlapX a aex s sex = true) :
    a.base = s.base ∧ ∃ p, (∃ τ, p = a.path ++ τ ∧ tailI a.kind τ ∧ aex.admits τ = true) ∧
      (∃ σ, p = s.path ++ σ ∧ tailI s.kind σ ∧ sex.admits σ = true) := by
  unfold overlapX overlapB at h
  cases hb : Nat.beq a.base s.base with
  | false => rw [hb] at h; cases h
  | true =>
    rw [hb] at h
    refine ⟨Nat.eq_of_beq_eq_true hb, ?_⟩
    cases hrel : relate a.path s.path with
    | below r =>
      rw [hrel] at h
      have h1 : admitsTailB a.kind r = true := RExact.bool_and_left h
      have h2 : aex.admits r = true := RExact.bool_and_right h
      exact ⟨s.path, ⟨r, Exact.relate_below hrel, Exact.admitsTailB_tailI h1, h2⟩,
        [], (List.append_nil _).symm, Exact.tailI_nil _, Exact.admits_nil _⟩
    | above r =>
      rw [hrel] at h
      have h1 : admitsTailB s.kind r = true := RExact.bool_and_left h
      have h2 : sex.admits r = true := RExact.bool_and_right h
      exact ⟨a.path, ⟨[], (List.append_nil _).symm, Exact.tailI_nil _, Exact.admits_nil _⟩,
        r, Exact.relate_above hrel, Exact.admitsTailB_tailI h1, h2⟩
    | apart => rw [hrel] at h; cases h

#print axioms overlapX_common

/-- An exact premise has one continuation: `[]`. -/
theorem exact_prem_iex {i : PFact} {iex : Excl} {t0 : Mark} :
    ∀ σ, (⟨i.base, i.path, t0⟩ : Loc).path = i.path ++ σ → iex.admits σ = true := by
  intro σ hσ
  rw [cont_unique hσ (List.append_nil _).symm]
  exact Exact.admits_nil _

/-- THE SINK LOCATION (run 1). A triggered refined check under an exact premise with the concrete
    mark `t0`, on a non-`*` sink fact: an ADMITTED location of the sink fact that the sink pattern
    covers is the end of an annotated pair from the premise location. -/
theorem sink_denX {i s : PFact} {f : XFact} {t0 : Mark} {iex : Excl} (hik : i.kind = .exact)
    (him : i.mark = .conc t0) (hns : f.af.fact.kind.isStar = false)
    (hch : checkX i f s = .triggered) :
    ∃ l, denX i iex f.af.fact f.ex ⟨i.base, i.path, t0⟩ l ∧ s.covers l := by
  have hov := checkX_overlap hch
  obtain ⟨T, hsm, _, hmo, hps⟩ := Confirmed.check_triggered_passes him (checkX_triggered hch)
  obtain ⟨hb, p, ⟨τ, hpa, hτ, hτe⟩, σ, hps', hσ, _⟩ := overlapX_common hov
  have hd := AnyTaintExact.den_exact_prem hik him hns hps (l := ⟨f.af.fact.base, p, T⟩) rfl
    ⟨τ, hpa, hτ⟩ hmo.symm
  refine ⟨_, denX_of_den hd exact_prem_iex ?_, hb, ⟨σ, hps', hσ⟩, by rw [hsm]; exact rfl⟩
  intro τ' hτ'
  rw [cont_unique hτ' hpa]
  exact hτe

#print axioms sink_denX

/-- THE SINK LOCATION (a concrete sink fact): an admitted location of the sink fact that the sink
    pattern covers. -/
theorem sink_covX {i s : PFact} {f : XFact} {t0 : Mark} (him : i.mark = .conc t0)
    (hfc : ∃ t, f.af.fact.mark = .conc t) (hch : checkX i f s = .triggered) :
    ∃ l, coversFX f.af.fact f.ex l ∧ s.covers l := by
  have hov := checkX_overlap hch
  obtain ⟨T, hsm, _, hmo, _⟩ := Confirmed.check_triggered_passes him (checkX_triggered hch)
  obtain ⟨hb, p, ⟨τ, hpa, hτ, hτe⟩, σ, hps', hσ, _⟩ := overlapX_common hov
  obtain ⟨tf, htf⟩ := hfc
  have hT : tf = T := by rw [htf] at hmo; exact hmo
  refine ⟨⟨f.af.fact.base, p, T⟩, ⟨rfl, ⟨τ, hpa, hτ, hτe⟩, tf, htf, hT.symm⟩, hb, ⟨σ, hps', hσ⟩, ?_⟩
  rw [hsm]
  exact rfl

#print axioms sink_covX

section Run1Sup
variable {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
  {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId}

/-- An exact added fact has no exclusion. -/
theorem ex_of_exact {a : XFact} (hw : WFX a) (hk : a.af.fact.kind = .exact) : a.ex = Excl.empty := by
  apply hw
  unfold carriesB
  rw [hk]
  rfl

/-- THE SUPPORT OF RUN 1 (`FiltUp` form): a supported premise of `D6X` is exact with a concrete
    mark, and its one location is entry-reachable. Hypotheses: S7, `FiltUp`. -/
theorem sup_entry6X (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) {M : MethodId} {i : PFact}
    (h : Sup6X P taint counted L α sinks roots M i) :
    ∃ t, i.kind = .exact ∧ i.mark = .conc t ∧
      Confirmed.EntryReach P roots M ⟨i.base, i.path, t⟩ := by
  induction h with
  | root hM => exact ⟨zeroMark, rfl, rfl, Or.inl ⟨hM, rfl⟩⟩
  | @call M i n f n' c e a j _ hD hfd hE he ha had _ hj ih =>
    obtain ⟨t0, hik, him, hent⟩ := ih
    obtain ⟨t, hak, ham, rfl⟩ := Confirmed.sup_step (a := a.af) hj
    have hden := Confirmed.den_exact_exact (a := a.af.fact) him hak (by rw [ham]; trivial)
    rw [ham] at hden
    have hax := ex_of_exact (applyEdgeX_wf ha) hak
    have hdx : denX i Excl.empty a.af.fact a.ex ⟨i.base, i.path, t0⟩
        ⟨a.af.fact.base, a.af.fact.path, t⟩ :=
      denX_of_den hden (fun σ _ => admits_empty σ) (fun τ _ => by rw [hax]; exact admits_empty τ)
    obtain ⟨l, hd1, hd2⟩ := bindX_exact (hmw.toC _ _ _ _ hE e he) hfd (D6X_wf_edge hD) ha had hdx
    have hR := Confirmed.entry_reach P roots hent (edge_exact6X hmw hup hD hfd hd1)
    exact ⟨t, hak, ham, Or.inr ⟨M, n, l, n', c, e, hR, hE, rfl, he, hd2⟩⟩

#print axioms sup_entry6X

/-- THE SUPPORT OF RUN 1 for valid locations (S7, S13). -/
theorem sup_entry6X_valid {ok : Loc → Prop} (hmw : Exact.MarkWF P) (hv : Exact.FiltValid P ok)
    (hbo : Exact.BackOK P ok) {M : MethodId} {i : PFact}
    (h : Sup6X P taint counted L α sinks roots M i) :
    ∃ t, i.kind = .exact ∧ i.mark = .conc t ∧
      (ok ⟨i.base, i.path, t⟩ → Confirmed.EntryReach P roots M ⟨i.base, i.path, t⟩) := by
  induction h with
  | root hM => exact ⟨zeroMark, rfl, rfl, fun _ => Or.inl ⟨hM, rfl⟩⟩
  | @call M i n f n' c e a j _ hD hfd hE he ha had _ hj ih =>
    obtain ⟨t0, hik, him, hent⟩ := ih
    obtain ⟨t, hak, ham, rfl⟩ := Confirmed.sup_step (a := a.af) hj
    refine ⟨t, hak, ham, fun hokj => ?_⟩
    have hden := Confirmed.den_exact_exact (a := a.af.fact) him hak (by rw [ham]; trivial)
    rw [ham] at hden
    have hax := ex_of_exact (applyEdgeX_wf ha) hak
    have hdx : denX i Excl.empty a.af.fact a.ex ⟨i.base, i.path, t0⟩
        ⟨a.af.fact.base, a.af.fact.path, t⟩ :=
      denX_of_den hden (fun σ _ => admits_empty σ) (fun τ _ => by rw [hax]; exact admits_empty τ)
    obtain ⟨l, hd1, hd2⟩ := bindX_exact (hmw.toC _ _ _ _ hE e he) hfd (D6X_wf_edge hD) ha had hdx
    have hokl : ok l := hbo.toC _ _ _ _ hE e he _ _ hd2 hokj
    obtain ⟨hfl, hok0⟩ := edge_exact_valid6X hmw hv hbo hD hfd hd1 hokl
    exact Or.inr ⟨M, n, l, n', c, e, Confirmed.entry_reach P roots (hent hok0) hfl, hE, rfl, he, hd2⟩

#print axioms sup_entry6X_valid

/-- CONFIRMATION IN RUN 1 (`FiltUp` form). A vulnerability confirmed on a NORMAL sink edge of
    `D6X` (`Confirmed6X`: the sink fact can be `[any-taint]/E`, and the sink pattern overlaps an
    ADMITTED location of it) under a supported premise is real: a reachable location in the sink
    pattern. Hypotheses: S7, `FiltUp`. -/
theorem confirmed_real6X (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P)
    {M : MethodId} {n : Node} {s : PFact}
    (h : Confirmed6X P taint counted L α sinks roots M n s) :
    ∃ l, Reach P roots M n l ∧ s.covers l := by
  obtain ⟨i, f, hD, hS, hfd, _, hch⟩ := h
  obtain ⟨t0, hik, him, hent⟩ := sup_entry6X hmw hup hS
  have hns : f.af.fact.kind.isStar = false := D6X_NS hD (by rw [hik]; rfl)
  obtain ⟨l, hden, hcov⟩ := sink_denX (iex := Excl.empty) hik him hns hch
  exact ⟨l, Confirmed.entry_reach P roots hent (edge_exact6X hmw hup hD hfd hden), hcov⟩

#print axioms confirmed_real6X

/-- CONFIRMATION IN RUN 1 FOR VALID LOCATIONS (S7, S13): a confirmed vulnerability of `D6X` has a
    location in the sink pattern that is reached if it is valid. -/
theorem confirmed_real_valid6X_of {ok : Loc → Prop} (hmw : Exact.MarkWF P)
    (hv : Exact.FiltValid P ok) (hbo : Exact.BackOK P ok) {M : MethodId} {n : Node} {s : PFact}
    (h : Confirmed6X P taint counted L α sinks roots M n s) :
    ∃ l, s.covers l ∧ (ok l → Reach P roots M n l) := by
  obtain ⟨i, f, hD, hS, hfd, _, hch⟩ := h
  obtain ⟨t0, hik, him, hent⟩ := sup_entry6X_valid hmw hv hbo hS
  have hns : f.af.fact.kind.isStar = false := D6X_NS hD (by rw [hik]; rfl)
  obtain ⟨l, hden, hcov⟩ := sink_denX (iex := Excl.empty) hik him hns hch
  refine ⟨l, hcov, fun hok => ?_⟩
  obtain ⟨hfl, hok0⟩ := edge_exact_valid6X hmw hv hbo hD hfd hden hok
  exact Confirmed.entry_reach P roots (hent hok0) hfl

#print axioms confirmed_real_valid6X_of

/-- CONFIRMATION IN RUN 1 FOR A REAL PROGRAM (S7, S13, every location of the sink pattern valid):
    a confirmed vulnerability of `D6X` is real. -/
theorem confirmed_real_valid6X {ok : Loc → Prop} (hmw : Exact.MarkWF P)
    (hv : Exact.FiltValid P ok) (hbo : Exact.BackOK P ok) {M : MethodId} {n : Node} {s : PFact}
    (hok : ∀ l, s.covers l → ok l)
    (h : Confirmed6X P taint counted L α sinks roots M n s) :
    ∃ l, Reach P roots M n l ∧ s.covers l := by
  obtain ⟨l, hcov, hR⟩ := confirmed_real_valid6X_of hmw hv hbo h
  exact ⟨l, hR (hok l hcov), hcov⟩

#print axioms confirmed_real_valid6X

end Run1Sup

/-! ## 5. The restricted run with the exclusion (`DRX`) -/

/-- The NEW restriction hypothesis (in place of `RestrictSubX`): the restriction of a conclusion IN
    NORMAL FORM gives a conclusion in normal form, in the same layer, with fewer pairs.
    (`RestrictSubX` is false for the spec instance `restrictX`: `CexRestrictSub`.) -/
def RestrictOKX (restrict : PFact → Excl → XFact → DemandEdge → Option XFact) : Prop :=
  ∀ j jex g d g', WFX g → restrict j jex g d = some g' →
    WFX g' ∧ g'.af.demand = g.af.demand ∧
    ∀ l1 l2, denX j jex g'.af.fact g'.ex l1 l2 → denX j jex g.af.fact g.ex l1 l2

/-- `RestrictSubX` with a result in normal form gives `RestrictOKX`. -/
theorem restrictOKX_of {restrict : PFact → Excl → XFact → DemandEdge → Option XFact}
    (hs : RestrictSubX restrict)
    (hw : ∀ j jex g d g', restrict j jex g d = some g' → WFX g') : RestrictOKX restrict :=
  fun j jex g d g' _ h => ⟨hw j jex g d g' h, (hs j jex g d g' h).1, (hs j jex g d g' h).2⟩

#print axioms restrictOKX_of

/-- The NEW record hypothesis: a normal must record has a concrete conclusion mark. -/
def RecsConcX (recs : MethodId → PFact × Bool × Excl × XFact → Prop) : Prop :=
  ∀ m j jex g, recs m (j, true, jex, g) → g.af.demand = false → ∃ t, g.af.fact.mark = .conc t

/-- The NEW record hypothesis: every record conclusion is in normal form. -/
def RecsWFX (recs : MethodId → PFact × Bool × Excl × XFact → Prop) : Prop :=
  ∀ m j mj jex g, recs m (j, mj, jex, g) → WFX g

/-- The well-formedness motive of `DRX`. -/
def WFObjX : XObj → Prop
  | .edge _ _ _ _ _ f => WFX f
  | _ => True

/-- The must-premise motive: a must-premise has the `.any` tail. -/
def MustAnyX : XObj → Prop
  | .init _ j true _ => j.kind = .any
  | .edge _ j true _ _ _ => j.kind = .any
  | _ => True

/-- The concreteness motive of `DRX`: every premise, conclusion and added fact has a concrete mark,
    and no conclusion has the `*` tail. -/
def ConcObjX : XObj → Prop
  | .init _ j _ _ => ∃ t, j.mark = .conc t
  | .edge _ j _ _ _ f =>
    (∃ t, j.mark = .conc t) ∧ (∃ t, f.af.fact.mark = .conc t) ∧ f.af.fact.kind.isStar = false
  | .added _ a _ _ => ∃ t, a.mark = .conc t
  | _ => True

theorem conc_of_fact {x : XFact} {y : AFact} (h : x.af.fact = y.fact)
    (hy : ∃ t, y.fact.mark = .conc t) : ∃ t, x.af.fact.mark = .conc t := by
  rw [h]; exact hy

theorem startFact_conc_nonstar {j : PFact} (hj : ∃ t, j.mark = .conc t) :
    (startFact j).fact.kind.isStar = false := by
  obtain ⟨t, ht⟩ := hj
  obtain ⟨b, p, k, m⟩ := j
  have ht' : m = .conc t := ht
  subst ht'
  cases k <;> rfl

theorem answerInit_conc (i a : PFact) (t : Mark) : ∃ t', (answerInit i a t).mark = .conc t' := by
  unfold answerInit
  split <;> exact ⟨t, rfl⟩

section RunX
variable {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
  {demand : MethodId → DemandEdge → Prop}
  {emit : PFact → PFact → Excl → Option (PFact × Excl)}
  {sat : PFact → Excl → PFact → Excl → Bool}
  {restrict : PFact → Excl → XFact → DemandEdge → Option XFact}
  {recs : MethodId → PFact × Bool × Excl × XFact → Prop}
  {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId}

/-- Every edge conclusion of `DRX` is in normal form (no hypothesis). -/
theorem DRX_wf {o : XObj}
    (h : DRX P taint counted L demand emit sat restrict recs sinks roots o) : WFObjX o := by
  induction h with
  | root => trivial
  | @start M j mj jex _ _ => exact startX_wf j mj jex
  | @step M i mi iex n f n' s f' _ _ hf ih => exact transferX_wf ih hf
  | reqStmt => trivial
  | pass _ _ _ ih => exact ih
  | added => trivial
  | initR => trivial
  | @ret M i mi iex n f n' c e1 a j mj jex g d g' r e2 r' _ _ _ _ _ _ _ _ _ _ _ hr' _ _ _ =>
    exact limitFX_wf counted L (applyEdgeX_wf hr')
  | @retRec M i mi iex n f n' c e1 a j mj jex g r e2 r' _ _ _ _ _ _ _ _ hr' _ =>
    exact limitFX_wf counted L (recLayerX_wf _ _ (applyEdgeX_wf hr'))
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial
  | @clean M i mi iex n f n' cl f' _ _ hf ih => exact cleanResX_wf ih hf
  | reqClean => trivial
  | filt _ _ _ ih => exact ih

#print axioms DRX_wf

theorem DRX_wf_edge {M : MethodId} {i : PFact} {mi : Bool} {iex : Excl} {n : Node} {f : XFact}
    (h : DRX P taint counted L demand emit sat restrict recs sinks roots (.edge M i mi iex n f)) :
    WFX f := DRX_wf h

/-- A must-premise of `DRX` has the `.any` tail (no hypothesis). -/
theorem DRX_mustAny {o : XObj}
    (h : DRX P taint counted L demand emit sat restrict recs sinks roots o) : MustAnyX o := by
  induction h with
  | root => trivial
  | @start M j mj _ _ ih => cases mj <;> exact ih
  | @step M i mi _ _ _ _ _ _ _ _ _ ih => cases mi <;> exact ih
  | reqStmt => trivial
  | @pass M i mi _ _ _ _ _ _ _ _ ih => cases mi <;> exact ih
  | added => trivial
  | @initR m a am aex d j mj jex _ _ hj _ =>
    cases mj with
    | false => trivial
    | true =>
      unfold emitTX at hj
      cases he : emit d.din a aex with
      | none => rw [he] at hj; cases hj
      | some pr =>
        rw [he] at hj
        have hj2 : some (pr.1, am && pr.1.kind.isAny, pr.2) = some (j, true, jex) := hj
        have hj' := Option.some.inj hj2
        have h1 : pr.1 = j := congrArg Prod.fst hj'
        have h2 : (am && pr.1.kind.isAny) = true := congrArg (fun x => x.2.1) hj'
        rw [← h1]
        exact isAny_eq ((Bool.and_eq_true _ _).mp h2).2
  | @ret M i mi iex n f n' c e1 a j mj jex g d g' r e2 r' _ _ _ _ _ _ _ _ _ _ _ _ ihF _ _ =>
    cases mi <;> exact ihF
  | @retRec M i mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihF => cases mi <;> exact ihF
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial
  | @clean M i mi _ _ _ _ _ _ _ _ _ ih => cases mi <;> exact ih
  | reqClean => trivial
  | @filt M i mi _ _ _ _ _ _ _ _ _ ih => cases mi <;> exact ih

#print axioms DRX_mustAny

/-- CONCRETENESS of `DRX` (with a mark-copying emission, C3): every premise, conclusion and added
    fact has a concrete mark, and no conclusion has the `*` tail. -/
theorem DRX_conc (hem : EmitCopiesMarkX emit) {o : XObj}
    (h : DRX P taint counted L demand emit sat restrict recs sinks roots o) : ConcObjX o := by
  induction h with
  | root => exact ⟨zeroMark, rfl⟩
  | @start M j mj jex hJ ih =>
    refine ⟨ih, ?_, ?_⟩
    · rw [startX_af, startT_mark]; exact ih
    · cases mj with
      | false =>
        show (startX j false jex).af.fact.kind.isStar = false
        rw [startX_af]
        exact startFact_conc_nonstar ih
      | true =>
        show (startX j true jex).af.fact.kind.isStar = false
        rw [startX_af]
        show j.kind.isStar = false
        rw [(DRX_mustAny hJ : j.kind = .any)]
        rfl
  | @step M i mi iex n f n' s f' _ _ hf ih =>
    obtain ⟨hi, ⟨tf, htf⟩, hfns⟩ := ih
    obtain ⟨y, hy, hfy, _⟩ := transferX_base hf
    obtain ⟨y0, hy0, hle⟩ := transferT_mem hy
    obtain ⟨t', ht'⟩ := transfer_mark_conc htf hy0
    exact ⟨hi, ⟨t', by rw [hfy, ← hle.fact]; exact ht'⟩, transferX_nonstar hfns hf⟩
  | reqStmt => trivial
  | pass _ _ _ ih => exact ih
  | @added M i mi iex n f n' c e a _ _ _ ha ih =>
    obtain ⟨_, ⟨tf, htf⟩, _⟩ := ih
    obtain ⟨y, hy, hay, _⟩ := applyEdgeX_base ha
    exact conc_of_fact hay (applyEdge_mark_conc htf hy)
  | @initR m a am aex d j mj jex _ _ hj ih =>
    unfold emitTX at hj
    cases he : emit d.din a aex with
    | none => rw [he] at hj; cases hj
    | some pr =>
      rw [he] at hj
      have hj2 : some (pr.1, am && pr.1.kind.isAny, pr.2) = some (j, mj, jex) := hj
      have h1 : pr.1 = j := congrArg Prod.fst (Option.some.inj hj2)
      have hm := hem d.din a aex pr.1 pr.2 he
      show ∃ t, j.mark = .conc t
      rw [← h1, hm]
      exact ih
  | @ret M i mi iex n f n' c e1 a j mj jex g d g' r e2 r' _ _ _ ha _ _ _ _ _ hr _ hr' ihF _ _ =>
    obtain ⟨hi, ⟨tf, htf⟩, hfns⟩ := ihF
    obtain ⟨ya, hya, hay, _⟩ := applyEdgeX_base ha
    obtain ⟨ta, hta⟩ := conc_of_fact hay (applyEdge_mark_conc htf hya)
    obtain ⟨yr, hyr, hry, _⟩ := applySummaryX_base hr
    obtain ⟨tr, htr⟩ := conc_of_fact hry (applySummary_mark_conc hta hyr)
    obtain ⟨yr', hyr', hry', _⟩ := applyEdgeX_base hr'
    obtain ⟨t3, ht3⟩ := conc_of_fact hry' (applyEdge_mark_conc htr hyr')
    refine ⟨hi, ⟨t3, by rw [limitFX_af, Exact.limitF_mark]; exact ht3⟩, ?_⟩
    exact limitFX_nonstar (applyEdgeX_nonstar
      (applySummaryX_nonstar (applyEdgeX_nonstar hfns ha) hr) hr')
  | @retRec M i mi iex n f n' c e1 a j mj jex g r e2 r' _ _ _ ha _ _ hr _ hr' ihF =>
    obtain ⟨hi, ⟨tf, htf⟩, hfns⟩ := ihF
    obtain ⟨ya, hya, hay, _⟩ := applyEdgeX_base ha
    obtain ⟨ta, hta⟩ := conc_of_fact hay (applyEdge_mark_conc htf hya)
    obtain ⟨yr, hyr, hry, _⟩ := applySummaryX_base hr
    obtain ⟨tr, htr⟩ := conc_of_fact hry (applySummary_mark_conc hta hyr)
    obtain ⟨yr', hyr', hry', _⟩ := applyEdgeX_base hr'
    obtain ⟨t3, ht3⟩ := conc_of_fact hry' (applyEdge_mark_conc htr hyr')
    refine ⟨hi, ⟨t3, ?_⟩, ?_⟩
    · rw [limitFX_af, Exact.limitF_mark, recLayerX_af, recLayer_fact]; exact ht3
    · apply limitFX_nonstar
      rw [recLayerX_af, recLayer_fact]
      exact applyEdgeX_nonstar (applySummaryX_nonstar (applyEdgeX_nonstar hfns ha) hr) hr'
  | reqSink => trivial
  | @answer M i t a am aex _ _ _ _ _ _ => exact answerInit_conc i a t
  | reqUp => trivial
  | vuln => trivial
  | @clean M i mi iex n f n' cl f' hF _ hf ih =>
    obtain ⟨hi, ⟨tf, htf⟩, hfns⟩ := ih
    rcases cleanResX_base (DRX_wf_edge hF) hf with ⟨y, hy, hxy, _⟩ | ⟨_, _, _, _, rfl⟩
    · exact ⟨hi, conc_of_fact hxy (cleanRes_mark_conc htf hy),
        cleanResX_nonstar (DRX_wf_edge hF) hfns hf⟩
    · exact ⟨hi, ⟨tf, htf⟩, rfl⟩
  | reqClean => trivial
  | filt _ _ _ ih => exact ih

#print axioms DRX_conc

end RunX

/-- An abstract premise mark of a concrete premise: vacuous. -/
theorem absX_vac {i : PFact} {m : MarkA} (hic : ∃ t, i.mark = .conc t) :
    Exact.absB i.mark = true → Exact.absB m = true :=
  fun hi => absurd hi (by rw [AnyTaintExact.absB_conc hic]; exact Bool.false_ne_true)

/-- A demand edge satisfies the motive (it says nothing about such an edge). -/
theorem edgeOKX_of_demand {P : Program} {ok : Loc → Prop} {M : MethodId} {i : PFact} {mi : Bool}
    {iex : Excl} {n : Node} {f : XFact} (h : f.af.demand = true) :
    EdgeOKX P ok (.edge M i mi iex n f) := by
  cases mi with
  | false => intro hd; rw [h] at hd; cases hd
  | true => intro hd; rw [h] at hd; cases hd

/-- A premise inside the added fact (with the exclusions, `SatInsideX`), with a concrete mark: every
    admitted location of the premise is an admitted location of the added fact. -/
theorem coversFX_of_insideX {a j : PFact} {aex jex : Excl} {l : Loc}
    (hin : ∀ l, coversX j jex l → coversX ⟨a.base, a.path, a.kind, .star⟩ aex l)
    (hsm : markSubB j.mark a.mark = true) (hjc : ∃ t, j.mark = .conc t) (hl : coversX j jex l) :
    coversFX a aex l := by
  obtain ⟨hb, hp, _⟩ := hin l hl
  obtain ⟨t, ht⟩ := hjc
  have ham : a.mark = j.mark := AnyTaintExact.markSub_conc ⟨t, ht⟩ hsm
  have hlm : l.mark = t := by
    have h := hl.2.2
    rw [ht] at h
    exact h
  exact ⟨hb, hp, t, by rw [ham, ht], hlm⟩

/-- An uncorrelated (non-`*`) fact: with the start location of one pair, every admitted location
    of the fact is the end of a pair (`AnyTaintExact.den_swap` with the exclusions). -/
theorem den_swapX {i a : PFact} {iex aex : Excl} {l0 l1 l1' : Loc} (hns : a.kind.isStar = false)
    (hd : denX i iex a aex l0 l1) (hl : coversFX a aex l1') : denX i iex a aex l0 l1' := by
  obtain ⟨h0b, _, h0m, _, hps, σ, _, h0p, _, hI, _, hie, _⟩ := hd
  obtain ⟨hb, ⟨τ, hp, hτ, he⟩, t, ht, hm⟩ := hl
  refine ⟨h0b, hb, h0m, ?_, hps, σ, τ, h0p, hp, hI, tailF_nonstar hns hτ, hie, he⟩
  rw [ht, hm]
  rfl

section RunX2
variable {P : Program} {counted : Acc → Bool} {L : Nat}

/-- The normal result of a summary application goes back to a normal summary edge and a normal
    caller edge. -/
theorem summaryX_back {f a g r r' : XFact} {j : PFact} {jex : Excl} {e1 e2 : MicroEdge}
    (ha : a ∈ (bindX f e1).facts) (hr : r ∈ (applySummaryX a j jex g).facts)
    (hr' : r' ∈ (bindX r e2).facts) (hla : (limitFX counted L r').af.demand = false) :
    r'.af.demand = false ∧ limitFX counted L r' = r' ∧ r.af.demand = false ∧
      r ∈ (applyEdgeX a j jex g.af.fact g.ex).facts ∧ g.af.demand = false ∧
      a.af.demand = false ∧ f.af.demand = false := by
  have e0 := limitFX_normal hla
  have hra' : r'.af.demand = false := by rw [← e0]; exact hla
  have hra := applyEdgeX_demand hr' hra'
  obtain ⟨hrx, hga⟩ := applySummaryX_normal hr hra
  have haa := applyEdgeX_demand hrx hra
  exact ⟨hra', e0, hra, hrx, hga, haa, applyEdgeX_demand ha haa⟩

/-- THE SUMMARY APPLICATION WITH A PAIR-EXACT CALLEE SUMMARY (a non-must callee premise; the
    summary conclusion may be `[any-taint]/E'`, its exclusion read): the result satisfies the motive
    for a pair caller and for a must caller (concrete run). -/
theorem summaryX_pair {ok : Loc → Prop} (hmw : Exact.MarkWF P) (hbo : Exact.BackOK P ok)
    {M : MethodId} {i j : PFact} {mi : Bool} {iex jex : Excl} {n n' : Node} {c : Call}
    {f a g r r' : XFact} {e1 e2 : MicroEdge}
    (hE : (M, n, Instr.call c, n') ∈ P.edges) (he1 : e1 ∈ c.toCallee)
    (ha : a ∈ (bindX f e1).facts) (hsm : markSubB j.mark a.af.fact.mark = true)
    (hr : r ∈ (applySummaryX a j jex g).facts) (he2 : e2 ∈ c.fromCallee)
    (hr' : r' ∈ (bindX r e2).facts)
    (hic : ∃ t, i.mark = .conc t) (hfc : ∃ t, f.af.fact.mark = .conc t)
    (hfns : f.af.fact.kind.isStar = false) (hfw : WFX f) (hgw : WFX g)
    (ihD : EdgeOKX P ok (.edge M i mi iex n f))
    (ihG : g.af.demand = false → ∀ l1 l2, denX j jex g.af.fact g.ex l1 l2 → ok l2 →
      Flow P c.callee l1 (P.exit c.callee) l2 ∧ ok l1) :
    EdgeOKX P ok (.edge M i mi iex n' (limitFX counted L r')) := by
  have hac : ∃ t, a.af.fact.mark = .conc t := by
    obtain ⟨y, hy, hay, _⟩ := applyEdgeX_base ha
    obtain ⟨tf, htf⟩ := hfc
    exact conc_of_fact hay (applyEdge_mark_conc htf hy)
  have hrc : ∃ t, r.af.fact.mark = .conc t := by
    obtain ⟨y, hy, hry, _⟩ := applySummaryX_base hr
    obtain ⟨ta, hta⟩ := hac
    exact conc_of_fact hry (applySummary_mark_conc hta hy)
  have hans := applyEdgeX_nonstar hfns ha
  have hawf : WFX a := applyEdgeX_wf ha
  have hrwf : WFX r := applySummaryX_wf hr
  have hpm := Exact.premOK_of_sub hsm
  have hcm := AnyTaintExact.concOK_conc g.af.fact.mark hac
  cases mi with
  | false =>
    intro hla
    obtain ⟨hra', e0, hra, hrx, hga, haa, hfa⟩ := summaryX_back ha hr hr' hla
    refine ⟨absX_vac hic, fun l0 l hd hok => ?_⟩
    rw [e0] at hd
    obtain ⟨l2, hd2, hde2⟩ := bindX_exact (hmw.fromC _ _ _ _ hE e2 he2) hra hrwf hr' hra' hd
    have hok2 : ok l2 := hbo.fromC _ _ _ _ hE e2 he2 _ _ hde2 hok
    obtain ⟨l1', hd1', hdg⟩ := applyEdgeX_exact hpm hcm haa hawf (Or.inr ⟨hans, hac⟩)
      (htx_of_wf hgw) hrx hra hd2
    obtain ⟨hflG, hok1'⟩ := ihG hga l1' l2 hdg hok2
    obtain ⟨l1, hd1, hde1⟩ := bindX_exact (hmw.toC _ _ _ _ hE e1 he1) hfa hfw ha haa hd1'
    have hok1 : ok l1 := hbo.toC _ _ _ _ hE e1 he1 _ _ hde1 hok1'
    obtain ⟨hflD, hok0⟩ := (ihD hfa).2 l0 l1 hd1 hok1
    exact ⟨Flow.call hflD hE he1 hde1 hflG he2 hde2, hok0⟩
  | true =>
    intro hla
    obtain ⟨hra', e0, hra, hrx, hga, haa, hfa⟩ := summaryX_back ha hr hr' hla
    refine ⟨absX_vac hic, fun l hl hok => ?_⟩
    rw [e0] at hl
    obtain ⟨l2, hl2, hde2⟩ := bindX_cov (hmw.fromC _ _ _ _ hE e2 he2) hra hrwf hr' hra' hrc hl
    have hok2 : ok l2 := hbo.fromC _ _ _ _ hE e2 he2 _ _ hde2 hok
    obtain ⟨l1', hl1', hdg⟩ := applyEdgeX_cov hpm hcm haa hawf (Or.inr ⟨hans, hac⟩)
      (htx_of_wf hgw) hrx hra hac hl2
    obtain ⟨hflG, hok1'⟩ := ihG hga l1' l2 hdg hok2
    obtain ⟨l1, hl1, hde1⟩ := bindX_cov (hmw.toC _ _ _ _ hE e1 he1) hfa hfw ha haa hfc hl1'
    have hok1 : ok l1 := hbo.toC _ _ _ _ hE e1 he1 _ _ hde1 hok1'
    obtain ⟨l0, hi0, hflD, hok0⟩ := (ihD hfa).2 l1 hl1 hok1
    exact ⟨l0, hi0, Flow.call hflD hE he1 hde1 hflG he2 hde2, hok0⟩

#print axioms summaryX_pair

/-- THE SUMMARY APPLICATION WITH AN END-EXACT CALLEE SUMMARY (an annotated must-premise
    `(j, [any-taint], jex)` that lies INSIDE the added fact `(a, a.ex)`, `SatInsideX`): every admitted
    location of the premise is an admitted location of the added fact, so the result satisfies the
    motive for a pair caller (`den_swapX`) and for a must caller. -/
theorem summaryX_end {ok : Loc → Prop} (hmw : Exact.MarkWF P) (hbo : Exact.BackOK P ok)
    {M : MethodId} {i j : PFact} {mi : Bool} {iex jex : Excl} {n n' : Node} {c : Call}
    {f a g r r' : XFact} {e1 e2 : MicroEdge}
    (hE : (M, n, Instr.call c, n') ∈ P.edges) (he1 : e1 ∈ c.toCallee)
    (ha : a ∈ (bindX f e1).facts)
    (hin : ∀ l, coversX j jex l → coversX ⟨a.af.fact.base, a.af.fact.path, a.af.fact.kind, .star⟩
      a.ex l)
    (hsm : markSubB j.mark a.af.fact.mark = true)
    (hjc : g.af.demand = false → ∃ t, j.mark = .conc t)
    (hr : r ∈ (applySummaryX a j jex g).facts) (he2 : e2 ∈ c.fromCallee)
    (hr' : r' ∈ (bindX r e2).facts)
    (hic : ∃ t, i.mark = .conc t) (hfc : ∃ t, f.af.fact.mark = .conc t)
    (hfns : f.af.fact.kind.isStar = false) (hfw : WFX f) (hgw : WFX g)
    (ihD : EdgeOKX P ok (.edge M i mi iex n f))
    (hG : g.af.demand = false → ∀ l1 l2, denX j jex g.af.fact g.ex l1 l2 → ok l2 →
      ∃ l0, coversX j jex l0 ∧ Flow P c.callee l0 (P.exit c.callee) l2 ∧ ok l0) :
    EdgeOKX P ok (.edge M i mi iex n' (limitFX counted L r')) := by
  have hac : ∃ t, a.af.fact.mark = .conc t := by
    obtain ⟨y, hy, hay, _⟩ := applyEdgeX_base ha
    obtain ⟨tf, htf⟩ := hfc
    exact conc_of_fact hay (applyEdge_mark_conc htf hy)
  have hrc : ∃ t, r.af.fact.mark = .conc t := by
    obtain ⟨y, hy, hry, _⟩ := applySummaryX_base hr
    obtain ⟨ta, hta⟩ := hac
    exact conc_of_fact hry (applySummary_mark_conc hta hy)
  have hans := applyEdgeX_nonstar hfns ha
  have hawf : WFX a := applyEdgeX_wf ha
  have hrwf : WFX r := applySummaryX_wf hr
  have hpm := Exact.premOK_of_sub hsm
  have hcm := AnyTaintExact.concOK_conc g.af.fact.mark hac
  cases mi with
  | false =>
    intro hla
    obtain ⟨hra', e0, hra, hrx, hga, haa, hfa⟩ := summaryX_back ha hr hr' hla
    refine ⟨absX_vac hic, fun l0 l hd hok => ?_⟩
    rw [e0] at hd
    obtain ⟨l2, hd2, hde2⟩ := bindX_exact (hmw.fromC _ _ _ _ hE e2 he2) hra hrwf hr' hra' hd
    have hok2 : ok l2 := hbo.fromC _ _ _ _ hE e2 he2 _ _ hde2 hok
    obtain ⟨l1', hd1', hdg⟩ := applyEdgeX_exact hpm hcm haa hawf (Or.inr ⟨hans, hac⟩)
      (htx_of_wf hgw) hrx hra hd2
    obtain ⟨l1'', hj1, hflG, hok1''⟩ := hG hga l1' l2 hdg hok2
    have hd1'' := den_swapX hans hd1' (coversFX_of_insideX hin hsm (hjc hga) hj1)
    obtain ⟨l1, hd1, hde1⟩ := bindX_exact (hmw.toC _ _ _ _ hE e1 he1) hfa hfw ha haa hd1''
    have hok1 : ok l1 := hbo.toC _ _ _ _ hE e1 he1 _ _ hde1 hok1''
    obtain ⟨hflD, hok0⟩ := (ihD hfa).2 l0 l1 hd1 hok1
    exact ⟨Flow.call hflD hE he1 hde1 hflG he2 hde2, hok0⟩
  | true =>
    intro hla
    obtain ⟨hra', e0, hra, hrx, hga, haa, hfa⟩ := summaryX_back ha hr hr' hla
    refine ⟨absX_vac hic, fun l hl hok => ?_⟩
    rw [e0] at hl
    obtain ⟨l2, hl2, hde2⟩ := bindX_cov (hmw.fromC _ _ _ _ hE e2 he2) hra hrwf hr' hra' hrc hl
    have hok2 : ok l2 := hbo.fromC _ _ _ _ hE e2 he2 _ _ hde2 hok
    obtain ⟨l1', _, hdg⟩ := applyEdgeX_cov hpm hcm haa hawf (Or.inr ⟨hans, hac⟩)
      (htx_of_wf hgw) hrx hra hac hl2
    obtain ⟨l1'', hj1, hflG, hok1''⟩ := hG hga l1' l2 hdg hok2
    have hca := coversFX_of_insideX hin hsm (hjc hga) hj1
    obtain ⟨l1, hl1, hde1⟩ := bindX_cov (hmw.toC _ _ _ _ hE e1 he1) hfa hfw ha haa hfc hca
    have hok1 : ok l1 := hbo.toC _ _ _ _ hE e1 he1 _ _ hde1 hok1''
    obtain ⟨l0, hi0, hflD, hok0⟩ := (ihD hfa).2 l1 hl1 hok1
    exact ⟨l0, hi0, Flow.call hflD hE he1 hde1 hflG he2 hde2, hok0⟩

#print axioms summaryX_end

end RunX2

section RunX3
variable {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
  {demand : MethodId → DemandEdge → Prop}
  {emit : PFact → PFact → Excl → Option (PFact × Excl)}
  {sat : PFact → Excl → PFact → Excl → Bool}
  {restrict : PFact → Excl → XFact → DemandEdge → Option XFact}
  {recs : MethodId → PFact × Bool × Excl × XFact → Prop}
  {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId}

/-- THE MOTIVE ON EVERY OBJECT OF THE RESTRICTED RUN WITH THE EXCLUSION (`DRX`). A normal edge of a
    non-must premise is PAIR-EXACT on the admitted locations (`denX` with the premise exclusion and
    the conclusion exclusion); a normal edge of an (annotated) must-premise is END-EXACT on the
    admitted locations (`EndExactX`); an abstract premise mark gives an abstract conclusion mark
    (vacuous: the run is concrete). Hypotheses: those of `AnyTaintExact.DRT_edgeOK` with the X
    contracts: S7 (`MarkWF`), `FiltOK`/`BackOK` for the validity `ok` (S13), `SatInsideX sat`,
    `EmitCopiesMarkX emit`, the records exact (`RecsExactX`) with concrete must records
    (`RecsConcX`); and the NEW normal-form hypotheses `RestrictOKX restrict` (in place of
    `RestrictSubX`) and `RecsWFX recs`. A must record that applies by `applicable` only gives a
    demand result (`recLayerX`), so it needs no exactness. -/
theorem DRX_edgeOK {ok : Loc → Prop} (hmw : Exact.MarkWF P) (hfo : Exact.FiltOK P ok)
    (hbo : Exact.BackOK P ok) (hin : SatInsideX sat) (hsub : RestrictOKX restrict)
    (hem : EmitCopiesMarkX emit) (hrecs : RecsExactX P ok recs) (hrc : RecsConcX recs)
    (hrw : RecsWFX recs) {o : XObj}
    (h : DRX P taint counted L demand emit sat restrict recs sinks roots o) : EdgeOKX P ok o := by
  induction h with
  | root => trivial
  | @start M j mj jex hJ _ =>
    cases mj with
    | false =>
      intro ha
      refine ⟨fun hi => ?_, fun l0 l hd hok => ?_⟩
      · show Exact.absB (startX j false jex).af.fact.mark = true
        rw [startX_af, startT_mark]
        exact hi
      · have hd' : den j (startFact j).fact l0 l := denX_den hd
        have e := Exact.startFact_exact ha hd'
        subst e
        exact ⟨Flow.start M l, hok⟩
    | true =>
      intro _
      refine ⟨fun hi => ?_, (startX_must_end (DRX_mustAny hJ)).2⟩
      show Exact.absB (startX j true jex).af.fact.mark = true
      rw [startX_af, startT_mark]
      exact hi
  | @step M i mi iex n f n' s f' hF hE hf ih =>
    have hfw := DRX_wf_edge hF
    have hcx := DRX_conc hem hF
    cases mi with
    | false =>
      intro ha
      have hfa := transferX_demand hf ha
      obtain ⟨_, ih2⟩ := ih hfa
      refine ⟨absX_vac hcx.1, fun l0 l hd hok => ?_⟩
      obtain ⟨l1, hd1, hs⟩ := transferX_exact (hmw.stmt _ _ _ _ hE) hfa hfw hf ha hd
      have hok1 : ok l1 := by
        rcases hs with ⟨-, rfl⟩ | ⟨e, he, hde⟩
        · exact hok
        · exact hbo.stmt _ _ _ _ hE e he _ _ hde hok
      obtain ⟨hfl, hok0⟩ := ih2 l0 l1 hd1 hok1
      exact ⟨Flow.step hfl hE hs, hok0⟩
    | true =>
      intro ha
      have hfa := transferX_demand hf ha
      obtain ⟨_, ih2⟩ := ih hfa
      refine ⟨absX_vac hcx.1, fun l hl hok => ?_⟩
      obtain ⟨l1, hl1, hs⟩ := transferX_cov (hmw.stmt _ _ _ _ hE) hfa hfw hf ha hcx.2.1 hl
      have hok1 : ok l1 := by
        rcases hs with ⟨-, rfl⟩ | ⟨e, he, hde⟩
        · exact hok
        · exact hbo.stmt _ _ _ _ hE e he _ _ hde hok
      obtain ⟨l0, hi0, hfl, hok0⟩ := ih2 l1 hl1 hok1
      exact ⟨l0, hi0, Flow.step hfl hE hs, hok0⟩
  | reqStmt => trivial
  | @pass M i mi iex n f n' c _ hE hm ih =>
    cases mi with
    | false =>
      intro ha
      obtain ⟨ih1, ih2⟩ := ih ha
      refine ⟨ih1, fun l0 l hd hok => ?_⟩
      obtain ⟨hfl, hok0⟩ := ih2 l0 l hd hok
      refine ⟨Flow.pass hfl hE ?_, hok0⟩
      rw [hd.2.1]
      exact hm
    | true =>
      intro ha
      obtain ⟨ih1, ih2⟩ := ih ha
      refine ⟨ih1, fun l hl hok => ?_⟩
      obtain ⟨l0, hi0, hfl, hok0⟩ := ih2 l hl hok
      refine ⟨l0, hi0, Flow.pass hfl hE ?_, hok0⟩
      rw [hl.1]
      exact hm
  | added => trivial
  | initR => trivial
  | @ret M i mi iex n f n' c e1 a j mj jex g d g' r e2 r' hF hE he1 ha hJ hG _ hres hs hr he2 hr'
      ihF _ ihG =>
    have hgw := DRX_wf_edge hG
    obtain ⟨hgw', hgd, hgsub⟩ := hsub j jex g d g' hgw hres
    obtain ⟨hcov, hsm⟩ := hin j jex a.af.fact a.ex hs
    have hcx := DRX_conc hem hF
    cases mj with
    | false =>
      -- a non-must callee premise: the callee summary is pair-exact
      have ihG' : g'.af.demand = false → ∀ l1 l2, denX j jex g'.af.fact g'.ex l1 l2 → ok l2 →
          Flow P c.callee l1 (P.exit c.callee) l2 ∧ ok l1 := by
        intro hg' l1 l2 hd' hok
        exact (ihG (hgd.symm.trans hg')).2 l1 l2 (hgsub l1 l2 hd') hok
      exact summaryX_pair hmw hbo hE he1 ha hsm hr he2 hr' hcx.1 hcx.2.1 hcx.2.2 (DRX_wf_edge hF)
        hgw' ihF ihG'
    | true =>
      -- an annotated must callee premise inside the added fact: END-EXACT of the callee summary
      have hjc : ∃ t, j.mark = .conc t := DRX_conc hem hJ
      have hgc := (DRX_conc hem hG).2.1
      have hG' : g'.af.demand = false → ∀ l1 l2, denX j jex g'.af.fact g'.ex l1 l2 → ok l2 →
          ∃ l0, coversX j jex l0 ∧ Flow P c.callee l0 (P.exit c.callee) l2 ∧ ok l0 := by
        intro hg' l1 l2 hd' hok
        exact (ihG (hgd.symm.trans hg')).2 l2 (denX_coversFX (hgsub l1 l2 hd') hgc) hok
      exact summaryX_end hmw hbo hE he1 ha hcov hsm (fun _ => hjc) hr he2 hr' hcx.1 hcx.2.1
        hcx.2.2 (DRX_wf_edge hF) hgw' ihF hG'
  | @retRec M i mi iex n f n' c e1 a j mj jex g r e2 r' hF hE he1 ha hrec hs hr he2 hr' ihF =>
    have hG := hrecs c.callee j mj jex g hrec
    have hgw := hrw c.callee j mj jex g hrec
    have hcx := DRX_conc hem hF
    cases mj with
    | false =>
      -- a non-must record, by `sat` or by `applicable`: pair-exact (`RecsExactX`)
      have hsm : markSubB j.mark a.af.fact.mark = true := by
        rcases hs with hs | hs
        · exact (hin j jex a.af.fact a.ex hs).2
        · exact Exact.applicable_markSub hs
      have e : recLayerX false (sat j jex a.af.fact a.ex) r' = r' := rfl
      rw [e]
      exact summaryX_pair hmw hbo hE he1 ha hsm hr he2 hr' hcx.1 hcx.2.1 hcx.2.2 (DRX_wf_edge hF)
        hgw ihF (fun hg => (hG hg).2)
    | true =>
      cases hsj : sat j jex a.af.fact a.ex with
      | false =>
        -- a must record by `applicable` only: the result is in the demand layer
        apply edgeOKX_of_demand
        apply limitFX_demand
        rfl
      | true =>
        -- a must record by `sat`: the premise lies inside the added fact
        obtain ⟨hcov, hsm⟩ := hin j jex a.af.fact a.ex hsj
        have hjc : g.af.demand = false → ∃ t, j.mark = .conc t := fun hg =>
          AnyTaintExact.conc_of_absImp (hG hg).1 (hrc c.callee j jex g hrec hg)
        have e : recLayerX true true r' = r' := rfl
        rw [e]
        exact summaryX_end hmw hbo hE he1 ha hcov hsm hjc hr he2 hr' hcx.1 hcx.2.1 hcx.2.2
          (DRX_wf_edge hF) hgw ihF
          (fun hg l1 l2 hd' hok => (hG hg).2 l2 (denX_coversFX hd' (hrc c.callee j jex g hrec hg)) hok)
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial
  | @clean M i mi iex n f n' cl f' hF hE hf ih =>
    have hfw := DRX_wf_edge hF
    have hcx := DRX_conc hem hF
    cases mi with
    | false =>
      intro ha
      have hfa := cleanResX_demand hf ha
      obtain ⟨_, ih2⟩ := ih hfa
      refine ⟨absX_vac hcx.1, fun l0 l hd hok => ?_⟩
      obtain ⟨hd1, hcl⟩ := cleanResX_exact hfw hf ha hd
      obtain ⟨hfl, hok0⟩ := ih2 l0 l hd1 hok
      exact ⟨Flow.clean hfl hE hcl, hok0⟩
    | true =>
      intro ha
      have hfa := cleanResX_demand hf ha
      obtain ⟨_, ih2⟩ := ih hfa
      refine ⟨absX_vac hcx.1, fun l hl hok => ?_⟩
      obtain ⟨hl1, hcl⟩ := cleanResX_cov hfw hf ha hcx.2.1 hl
      obtain ⟨l0, hi0, hfl, hok0⟩ := ih2 l hl1 hok
      exact ⟨l0, hi0, Flow.clean hfl hE hcl, hok0⟩
  | reqClean => trivial
  | @filt M i mi iex n f n' b may _ hE hp ih =>
    cases mi with
    | false =>
      intro ha
      obtain ⟨ih1, ih2⟩ := ih ha
      refine ⟨ih1, fun l0 l hd hok => ?_⟩
      obtain ⟨hfl, hok0⟩ := ih2 l0 l hd hok
      refine ⟨Flow.filt hfl hE ?_, hok0⟩
      intro hb
      obtain ⟨-, hlb, -, -, -, σ, τ, -, hlp, -, -, -, -⟩ := hd
      exact hfo _ _ _ _ _ hE f.af.fact.path τ l (hp (hlb.symm.trans hb)) hlp hok hb
    | true =>
      intro ha
      obtain ⟨ih1, ih2⟩ := ih ha
      refine ⟨ih1, fun l hl hok => ?_⟩
      obtain ⟨l0, hi0, hfl, hok0⟩ := ih2 l hl hok
      refine ⟨l0, hi0, Flow.filt hfl hE ?_, hok0⟩
      intro hb
      obtain ⟨hlb, ⟨τ, hlp, _⟩, _⟩ := hl
      exact hfo _ _ _ _ _ hE f.af.fact.path τ l (hp (hlb.symm.trans hb)) hlp hok hb

#print axioms DRX_edgeOK

/-- The two exactness forms of a normal edge of `DRX`, for a validity `ok` with `FiltOK`, `BackOK`. -/
theorem edge_exactX_gen {ok : Loc → Prop} (hmw : Exact.MarkWF P) (hfo : Exact.FiltOK P ok)
    (hbo : Exact.BackOK P ok) (hin : SatInsideX sat) (hsub : RestrictOKX restrict)
    (hem : EmitCopiesMarkX emit) (hrecs : RecsExactX P ok recs) (hrc : RecsConcX recs)
    (hrw : RecsWFX recs)
    {M : MethodId} {i : PFact} {mi : Bool} {iex : Excl} {n : Node} {f : XFact}
    (h : DRX P taint counted L demand emit sat restrict recs sinks roots (.edge M i mi iex n f))
    (ha : f.af.demand = false) :
    (mi = false → ∀ l0 l, denX i iex f.af.fact f.ex l0 l → ok l → Flow P M l0 n l ∧ ok l0) ∧
    (mi = true → EndExactX P ok M i iex n f.af.fact f.ex) := by
  have hm := DRX_edgeOK hmw hfo hbo hin hsub hem hrecs hrc hrw h
  cases mi with
  | false => exact ⟨fun _ => (hm ha).2, fun h' => (by cases h')⟩
  | true => exact ⟨fun h' => (by cases h'), fun _ => (hm ha).2⟩

#print axioms edge_exactX_gen

/-- THE EXACTNESS THEOREM OF A RESTRICTED RUN WITH THE EXCLUSION (`FiltUp` form). A normal edge
    `(i, mi, iex) → f` of `DRX`:
    * of a non-must premise is PAIR-EXACT on the admitted locations: every pair of `denX` (the
      premise exclusion and the exclusion of an `[any-taint]/E` conclusion read) is a concrete flow;
    * of an (annotated) must-premise is END-EXACT on the admitted locations: every admitted location
      of the conclusion is reached by a concrete flow from SOME admitted location of the premise.
    Hypotheses: S7, `FiltUp`, `SatInsideX sat`, `RestrictOKX restrict`, `EmitCopiesMarkX emit`, the
    records exact (`RecsExactX`), concrete (`RecsConcX`) and in normal form (`RecsWFX`). -/
theorem edge_exactX (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hin : SatInsideX sat)
    (hsub : RestrictOKX restrict) (hem : EmitCopiesMarkX emit)
    (hrecs : RecsExactX P (fun _ => True) recs) (hrc : RecsConcX recs) (hrw : RecsWFX recs)
    {M : MethodId} {i : PFact} {mi : Bool} {iex : Excl} {n : Node} {f : XFact}
    (h : DRX P taint counted L demand emit sat restrict recs sinks roots (.edge M i mi iex n f))
    (ha : f.af.demand = false) :
    (mi = false → ∀ l0 l, denX i iex f.af.fact f.ex l0 l → Flow P M l0 n l) ∧
    (mi = true → ∀ l, coversFX f.af.fact f.ex l → ∃ l0, coversX i iex l0 ∧ Flow P M l0 n l) := by
  obtain ⟨h1, h2⟩ := edge_exactX_gen hmw (Exact.filtUp_ok hup) (Exact.backOK_true P) hin hsub hem
    hrecs hrc hrw h ha
  refine ⟨fun hm l0 l hd => (h1 hm l0 l hd trivial).1, fun hm l hl => ?_⟩
  obtain ⟨l0, hi0, hfl, _⟩ := h2 hm l hl trivial
  exact ⟨l0, hi0, hfl⟩

#print axioms edge_exactX

/-- THE EXACTNESS THEOREM FOR VALID ADMITTED LOCATIONS (S13 `FiltValid`, `BackOK`; the other
    hypotheses of `edge_exactX`, the records exact for `ok`). -/
theorem edge_exactX_valid {ok : Loc → Prop} (hmw : Exact.MarkWF P) (hv : Exact.FiltValid P ok)
    (hbo : Exact.BackOK P ok) (hin : SatInsideX sat) (hsub : RestrictOKX restrict)
    (hem : EmitCopiesMarkX emit) (hrecs : RecsExactX P ok recs) (hrc : RecsConcX recs)
    (hrw : RecsWFX recs)
    {M : MethodId} {i : PFact} {mi : Bool} {iex : Excl} {n : Node} {f : XFact}
    (h : DRX P taint counted L demand emit sat restrict recs sinks roots (.edge M i mi iex n f))
    (ha : f.af.demand = false) :
    (mi = false → ∀ l0 l, denX i iex f.af.fact f.ex l0 l → ok l → Flow P M l0 n l ∧ ok l0) ∧
    (mi = true → EndExactX P ok M i iex n f.af.fact f.ex) :=
  edge_exactX_gen hmw (Exact.filtValid_ok hv) hbo hin hsub hem hrecs hrc hrw h ha

#print axioms edge_exactX_valid

/-- The exit edges of a run with the exclusion, as an annotated record set. -/
def exitRecsX (P : Program) (R : XObj → Prop) (m : MethodId) (x : PFact × Bool × Excl × XFact) :
    Prop :=
  R (.edge m x.1 x.2.1 x.2.2.1 (P.exit m) x.2.2.2)

/-- The exit edges of a `DRX` run are exact records again (general validity). -/
theorem recs_of_DRX_gen {ok : Loc → Prop} (hmw : Exact.MarkWF P) (hfo : Exact.FiltOK P ok)
    (hbo : Exact.BackOK P ok) (hin : SatInsideX sat) (hsub : RestrictOKX restrict)
    (hem : EmitCopiesMarkX emit) (hrecs : RecsExactX P ok recs) (hrc : RecsConcX recs)
    (hrw : RecsWFX recs) :
    RecsExactX P ok
      (exitRecsX P (DRX P taint counted L demand emit sat restrict recs sinks roots)) :=
  fun _ _ _ _ _ hr => DRX_edgeOK hmw hfo hbo hin hsub hem hrecs hrc hrw hr

#print axioms recs_of_DRX_gen

/-- THE RECORDS OF A RESTRICTED RUN (`FiltUp` form): the exit edges of a `DRX` run, with their must
    flags and premise exclusions, are exact records (`RecsExactX`): pair-exact for a non-must premise,
    END-EXACT for a must-premise, on the admitted locations. -/
theorem recs_of_DRX (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hin : SatInsideX sat)
    (hsub : RestrictOKX restrict) (hem : EmitCopiesMarkX emit)
    (hrecs : RecsExactX P (fun _ => True) recs) (hrc : RecsConcX recs) (hrw : RecsWFX recs) :
    RecsExactX P (fun _ => True)
      (exitRecsX P (DRX P taint counted L demand emit sat restrict recs sinks roots)) :=
  recs_of_DRX_gen hmw (Exact.filtUp_ok hup) (Exact.backOK_true P) hin hsub hem hrecs hrc hrw

#print axioms recs_of_DRX

/-- The records of a restricted run for valid locations (S13). -/
theorem recs_of_DRX_valid {ok : Loc → Prop} (hmw : Exact.MarkWF P) (hv : Exact.FiltValid P ok)
    (hbo : Exact.BackOK P ok) (hin : SatInsideX sat) (hsub : RestrictOKX restrict)
    (hem : EmitCopiesMarkX emit) (hrecs : RecsExactX P ok recs) (hrc : RecsConcX recs)
    (hrw : RecsWFX recs) :
    RecsExactX P ok
      (exitRecsX P (DRX P taint counted L demand emit sat restrict recs sinks roots)) :=
  recs_of_DRX_gen hmw (Exact.filtValid_ok hv) hbo hin hsub hem hrecs hrc hrw

#print axioms recs_of_DRX_valid

/-- The exit edges of a concrete run satisfy `RecsConcX`. -/
theorem recsConc_of_DRX (hem : EmitCopiesMarkX emit) :
    RecsConcX (exitRecsX P (DRX P taint counted L demand emit sat restrict recs sinks roots)) :=
  fun _ _ _ _ hr _ => (DRX_conc hem hr).2.1

#print axioms recsConc_of_DRX

/-- The exit edges of a run are in normal form (`RecsWFX`). -/
theorem recsWF_of_DRX :
    RecsWFX (exitRecsX P (DRX P taint counted L demand emit sat restrict recs sinks roots)) :=
  fun _ _ _ _ _ hr => DRX_wf_edge hr

#print axioms recsWF_of_DRX

end RunX3

/-! ## 6. The support and the confirmation of the restricted run -/

/-- An exact fact: every exclusion admits its one continuation. -/
theorem coversFX_exact_ex {f : PFact} {e1 e2 : Excl} {l : Loc} (hk : f.kind = .exact)
    (h : coversFX f e1 l) : coversFX f e2 l := by
  obtain ⟨hb, ⟨τ, hp, hτ, _⟩, hm⟩ := h
  rw [hk] at hτ
  have hτ' : τ = [] := hτ
  subst hτ'
  exact ⟨hb, ⟨[], hp, by rw [hk]; rfl, Exact.admits_nil _⟩, hm⟩

theorem coversFX_zero {ex : Excl} {l : Loc} (h : coversFX zeroFact ex l) : l = zeroLoc :=
  AnyTaintExact.coversF_zero (coversFX_coversF h)

theorem coversFX_self_exact {i : PFact} {iex : Excl} {t0 : Mark} (hik : i.kind = .exact)
    (him : i.mark = .conc t0) : coversFX i iex ⟨i.base, i.path, t0⟩ :=
  ⟨rfl, ⟨[], (List.append_nil _).symm, by rw [hik]; rfl, Exact.admits_nil _⟩, t0, him, rfl⟩

theorem coversFX_fex {f : PFact} {fex : Excl} {l : Loc} (h : coversFX f fex l) :
    ∀ τ, l.path = f.path ++ τ → fex.admits τ = true := by
  obtain ⟨_, ⟨τ0, hp, _, he⟩, _⟩ := h
  intro τ hτ
  rw [cont_unique hτ hp]
  exact he

/-- The pair from the one location of an exact concrete premise to an admitted location of a
    non-`*` fact. -/
theorem denX_exact_prem {i a : PFact} {iex aex : Excl} {t0 : Mark} {l : Loc}
    (hik : i.kind = .exact) (him : i.mark = .conc t0) (hns : a.kind.isStar = false)
    (hl : coversFX a aex l) : denX i iex a aex ⟨i.base, i.path, t0⟩ l :=
  denX_of_den (AnyTaintExact.den_exact_prem_cov hik him hns (coversFX_coversF hl)) exact_prem_iex
    (coversFX_fex hl)

section RunXSup
variable {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
  {demand : MethodId → DemandEdge → Prop}
  {emit : PFact → PFact → Excl → Option (PFact × Excl)}
  {sat : PFact → Excl → PFact → Excl → Bool}
  {restrict : PFact → Excl → XFact → DemandEdge → Option XFact}
  {recs : MethodId → PFact × Bool × Excl × XFact → Prop}
  {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId}

/-- THE SUPPORT (general validity). A supported premise `(i, mi, iex)` of `DRX` (`SupX`) is
    concrete, a non-must one is exact, and every valid ADMITTED location of it is entry-reachable:
    for an annotated must-premise ALL its admitted locations (it lies inside an `[any-taint]/aex`
    added fact with its mark and exclusion, `satX`), for an exact premise its one location. -/
theorem sup_entryX_gen {ok : Loc → Prop} (hmw : Exact.MarkWF P) (hfo : Exact.FiltOK P ok)
    (hbo : Exact.BackOK P ok) (hin : SatInsideX sat) (hsub : RestrictOKX restrict)
    (hem : EmitCopiesMarkX emit) (hrecs : RecsExactX P ok recs) (hrc : RecsConcX recs)
    (hrw : RecsWFX recs) {M : MethodId} {i : PFact} {mi : Bool} {iex : Excl}
    (h : SupX P taint counted L demand emit sat restrict recs sinks roots M i mi iex) :
    (∃ t, i.mark = .conc t) ∧ (mi = false → i.kind = .exact) ∧
      ∀ l, coversFX i iex l → ok l → Confirmed.EntryReach P roots M l := by
  induction h with
  | root hM =>
    exact ⟨⟨zeroMark, rfl⟩, fun _ => rfl, fun l hl _ => Or.inl ⟨hM, coversFX_zero hl⟩⟩
  | @call M i mi iex n f n' c e a j mj jex _ hD hfd hE he ha had _ hlink ih =>
    obtain ⟨⟨t0, him⟩, hik, hent⟩ := ih
    -- the link: `j` is concrete, and every admitted location of `j` is one of `a`
    have hlinkF : (∃ t, j.mark = .conc t) ∧ (mj = false → j.kind = .exact) ∧
        ∀ l, coversFX j jex l → coversFX a.af.fact a.ex l := by
      rcases hlink with ⟨rfl, hz⟩ | ⟨hak, hac, rfl, _⟩ | ⟨_, hac, hjm, hsat, hk⟩
      · refine ⟨⟨zeroMark, rfl⟩, fun _ => rfl, fun l hl => ?_⟩
        rw [hz]
        exact coversFX_exact_ex rfl hl
      · exact ⟨hac, fun _ => hak, fun l hl => coversFX_exact_ex hak hl⟩
      · have hjc : ∃ t, j.mark = .conc t := by rw [hjm]; exact hac
        refine ⟨hjc, fun hm => ?_, fun l hl => ?_⟩
        · rcases hk with ⟨hk1, _⟩ | ⟨_, hm'⟩
          · exact hk1
          · rw [hm] at hm'; cases hm'
        · obtain ⟨hin', hsm⟩ := satX_inside j jex a.af.fact a.ex hsat
          exact coversFX_of_insideX hin' hsm hjc (coversX_of_coversFX hl)
    obtain ⟨hjc, hjk, hja⟩ := hlinkF
    refine ⟨hjc, hjk, fun l hl hok => ?_⟩
    have hla := hja l hl
    have hm := DRX_edgeOK hmw hfo hbo hin hsub hem hrecs hrc hrw hD
    have hcx := DRX_conc hem hD
    have hfw := DRX_wf_edge hD
    cases mi with
    | false =>
      -- a pair caller with an exact premise: the pair from its one location
      have hdx := denX_exact_prem (iex := iex) (hik rfl) him (applyEdgeX_nonstar hcx.2.2 ha) hla
      obtain ⟨l', hd1, hd2⟩ := bindX_exact (hmw.toC _ _ _ _ hE e he) hfd hfw ha had hdx
      have hokl' : ok l' := hbo.toC _ _ _ _ hE e he _ _ hd2 hok
      obtain ⟨hfl, hok0⟩ := (hm hfd).2 _ _ hd1 hokl'
      have hR := Confirmed.entry_reach P roots
        (hent _ (coversFX_self_exact (hik rfl) him) hok0) hfl
      exact Or.inr ⟨M, n, l', n', c, e, hR, hE, rfl, he, hd2⟩
    | true =>
      -- a must caller: END-EXACT of the caller edge
      obtain ⟨l', hl', hd2⟩ := bindX_cov (hmw.toC _ _ _ _ hE e he) hfd hfw ha had hcx.2.1 hla
      have hokl' : ok l' := hbo.toC _ _ _ _ hE e he _ _ hd2 hok
      obtain ⟨l0, hi0, hfl, hok0⟩ := (hm hfd).2 l' hl' hokl'
      have hR := Confirmed.entry_reach P roots
        (hent l0 (coversFX_of_coversX hi0 ⟨t0, him⟩) hok0) hfl
      exact Or.inr ⟨M, n, l', n', c, e, hR, hE, rfl, he, hd2⟩

#print axioms sup_entryX_gen

/-- THE SUPPORT (`FiltUp` form): every admitted location of a supported premise is
    entry-reachable (all admitted locations of an annotated must-premise, the one location of an
    exact premise). -/
theorem sup_entryX (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hin : SatInsideX sat)
    (hsub : RestrictOKX restrict) (hem : EmitCopiesMarkX emit)
    (hrecs : RecsExactX P (fun _ => True) recs) (hrc : RecsConcX recs) (hrw : RecsWFX recs)
    {M : MethodId} {i : PFact} {mi : Bool} {iex : Excl}
    (h : SupX P taint counted L demand emit sat restrict recs sinks roots M i mi iex) :
    (∃ t, i.mark = .conc t) ∧ (mi = false → i.kind = .exact) ∧
      ∀ l, coversFX i iex l → Confirmed.EntryReach P roots M l := by
  obtain ⟨h1, h2, h3⟩ := sup_entryX_gen hmw (Exact.filtUp_ok hup) (Exact.backOK_true P) hin hsub
    hem hrecs hrc hrw h
  exact ⟨h1, h2, fun l hl => h3 l hl trivial⟩

#print axioms sup_entryX

/-- The confirmation, general validity: a confirmed vulnerability of `DRX` has a location in the
    sink pattern that is reached if it is valid. -/
theorem confirmed_realX_gen {ok : Loc → Prop} (hmw : Exact.MarkWF P) (hfo : Exact.FiltOK P ok)
    (hbo : Exact.BackOK P ok) (hin : SatInsideX sat) (hsub : RestrictOKX restrict)
    (hem : EmitCopiesMarkX emit) (hrecs : RecsExactX P ok recs) (hrc : RecsConcX recs)
    (hrw : RecsWFX recs) {M : MethodId} {n : Node} {s : PFact}
    (h : ConfirmedX P taint counted L demand emit sat restrict recs sinks roots M n s) :
    ∃ l, s.covers l ∧ (ok l → Reach P roots M n l) := by
  obtain ⟨i, mi, iex, f, hD, hS, hfd, _, hch⟩ := h
  obtain ⟨⟨t0, him⟩, hik, hent⟩ := sup_entryX_gen hmw hfo hbo hin hsub hem hrecs hrc hrw hS
  have hm := DRX_edgeOK hmw hfo hbo hin hsub hem hrecs hrc hrw hD
  have hcx := DRX_conc hem hD
  obtain ⟨l, hlf, hls⟩ := sink_covX him hcx.2.1 hch
  refine ⟨l, hls, fun hok => ?_⟩
  cases mi with
  | false =>
    -- an exact supported premise: the pair from its one location to the sink location
    have hdx := denX_exact_prem (iex := iex) (hik rfl) him hcx.2.2 hlf
    obtain ⟨hfl, hok0⟩ := (hm hfd).2 _ _ hdx hok
    exact Confirmed.entry_reach P roots (hent _ (coversFX_self_exact (hik rfl) him) hok0) hfl
  | true =>
    -- a supported annotated must-premise: END-EXACT, and every admitted location is
    -- entry-reachable
    obtain ⟨l0, hi0, hfl, hok0⟩ := (hm hfd).2 l hlf hok
    exact Confirmed.entry_reach P roots (hent l0 (coversFX_of_coversX hi0 ⟨t0, him⟩) hok0) hfl

#print axioms confirmed_realX_gen

/-- THE CONFIRMATION THEOREM OF A RESTRICTED RUN WITH THE EXCLUSION (`FiltUp` form). A
    vulnerability confirmed on a NORMAL sink edge of `DRX` (`ConfirmedX`: the sink fact can be
    `[any-taint]/E`, and the sink pattern overlaps an ADMITTED location of it) under a supported
    premise (`SupX`: a supported annotated must-premise has every admitted location
    entry-reachable) is a real concrete vulnerability. Hypotheses: those of `edge_exactX`. -/
theorem confirmed_realX (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hin : SatInsideX sat)
    (hsub : RestrictOKX restrict) (hem : EmitCopiesMarkX emit)
    (hrecs : RecsExactX P (fun _ => True) recs) (hrc : RecsConcX recs) (hrw : RecsWFX recs)
    {M : MethodId} {n : Node} {s : PFact}
    (h : ConfirmedX P taint counted L demand emit sat restrict recs sinks roots M n s) :
    ∃ l, Reach P roots M n l ∧ s.covers l := by
  obtain ⟨l, hls, hR⟩ := confirmed_realX_gen hmw (Exact.filtUp_ok hup) (Exact.backOK_true P) hin
    hsub hem hrecs hrc hrw h
  exact ⟨l, hR trivial, hls⟩

#print axioms confirmed_realX

/-- THE CONFIRMATION FOR VALID LOCATIONS (S13): a confirmed vulnerability of `DRX` has a location
    in the sink pattern that is reached if it is valid. -/
theorem confirmed_realX_valid_of {ok : Loc → Prop} (hmw : Exact.MarkWF P)
    (hv : Exact.FiltValid P ok) (hbo : Exact.BackOK P ok) (hin : SatInsideX sat)
    (hsub : RestrictOKX restrict) (hem : EmitCopiesMarkX emit) (hrecs : RecsExactX P ok recs)
    (hrc : RecsConcX recs) (hrw : RecsWFX recs) {M : MethodId} {n : Node} {s : PFact}
    (h : ConfirmedX P taint counted L demand emit sat restrict recs sinks roots M n s) :
    ∃ l, s.covers l ∧ (ok l → Reach P roots M n l) :=
  confirmed_realX_gen hmw (Exact.filtValid_ok hv) hbo hin hsub hem hrecs hrc hrw h

#print axioms confirmed_realX_valid_of

/-- THE CONFIRMATION FOR A REAL PROGRAM (S13, every location of the sink pattern valid): a
    confirmed vulnerability of `DRX` is real. -/
theorem confirmed_realX_valid {ok : Loc → Prop} (hmw : Exact.MarkWF P)
    (hv : Exact.FiltValid P ok) (hbo : Exact.BackOK P ok) (hin : SatInsideX sat)
    (hsub : RestrictOKX restrict) (hem : EmitCopiesMarkX emit) (hrecs : RecsExactX P ok recs)
    (hrc : RecsConcX recs) (hrw : RecsWFX recs) {M : MethodId} {n : Node} {s : PFact}
    (hok : ∀ l, s.covers l → ok l)
    (h : ConfirmedX P taint counted L demand emit sat restrict recs sinks roots M n s) :
    ∃ l, Reach P roots M n l ∧ s.covers l := by
  obtain ⟨l, hls, hR⟩ := confirmed_realX_valid_of hmw hv hbo hin hsub hem hrecs hrc hrw h
  exact ⟨l, hR (hok l hls), hls⟩

#print axioms confirmed_realX_valid

end RunXSup

/-! ### The spec instance: `emitX`, `satX`, `restrictX` -/

/-- THE SPEC RESTRICTION HAS THE NEW CONTRACT: `restrictX` maps a conclusion in normal form to a
    conclusion in normal form, in the same layer, with fewer pairs (a `D-p` at or below the
    conclusion keeps it; a `D-p` below an `[any-taint]/E` conclusion, on an admitted step, gives the
    chain `D-p` with no exclusion). -/
theorem restrictX_ok : RestrictOKX restrictX := by
  intro j jex g d g' hgw h
  unfold restrictX at h
  cases hd : d.dout with
  | none => rw [hd] at h; cases h
  | some p =>
    rw [hd] at h
    dsimp only at h
    cases ho : overlapX j jex d.din Excl.empty with
    | false => rw [ho, if_neg Bool.false_ne_true] at h; cases h
    | true =>
      rw [ho, if_pos rfl] at h
      unfold restrictConcX at h
      cases hr : restrictConcU g.af p with
      | none => rw [hr] at h; cases h
      | some g0 =>
        rw [hr] at h
        dsimp only at h
        unfold restrictConcU at hr
        cases hb : Nat.beq g.af.fact.base p.base with
        | false => rw [hb, if_neg Bool.false_ne_true] at hr; cases hr
        | true =>
          rw [hb, if_pos rfl] at hr
          cases hrel : relate p.path g.af.fact.path with
          | apart => rw [hrel] at hr; cases hr
          | below r =>
            rw [hrel] at hr h
            dsimp only at hr h
            cases hA : admitsTailB p.kind r with
            | false => rw [hA, if_neg Bool.false_ne_true] at hr; cases hr
            | true =>
              rw [hA, if_pos rfl] at hr
              cases hr
              cases h
              have e : normX ⟨g.af, g.ex⟩ = g := normX_of_wf hgw
              rw [e]
              exact ⟨hgw, rfl, fun _ _ h => h⟩
          | above r =>
            obtain ⟨a, r', rfl⟩ := above_cons hrel
            have hpp : p.path = g.af.fact.path ++ a :: r' := Exact.relate_above hrel
            rw [hrel] at hr h
            dsimp only at hr h
            cases hk : g.af.fact.kind with
            | star e => rw [hk] at hr; cases hr
            | exact => rw [hk] at hr; cases hr
            | any =>
              rw [hk] at hr
              cases hr
              cases hadm : g.ex.admits (a :: r') with
              | false => rw [hadm, if_neg Bool.false_ne_true] at h; cases h
              | true =>
                rw [hadm, if_pos rfl] at h
                cases h
                refine ⟨wf_empty _, rfl, fun l1 l2 hd' => ?_⟩
                obtain ⟨h0b, h2b, h0m, h2m, hps, σ, τ, h0p, h2p, hI, _, hie, _⟩ := hd'
                refine ⟨h0b, h2b, h0m, h2m, hps, σ, a :: r' ++ τ, h0p, ?_, hI,
                  by rw [hk]; trivial, hie, Exact.admits_cons_append τ hadm⟩
                rw [h2p, hpp, List.append_assoc]

#print axioms restrictX_ok

/-- The spec instance satisfies the rule hypotheses: `emitX` copies the mark (C3), `satX` reads the
    premise inside the added fact with the exclusions, `restrictX` has `RestrictOKX`. -/
theorem specX_rules : EmitCopiesMarkX emitX ∧ SatInsideX satX ∧ RestrictOKX restrictX :=
  ⟨emitX_copies, satX_inside, restrictX_ok⟩

#print axioms specX_rules

/-- THE CONFIRMATION THEOREM FOR THE SPEC INSTANCE `DRXs` (`emitX`, `satX`, `restrictX`; `FiltUp`
    form): only S7, `FiltUp` and the record hypotheses remain. -/
theorem confirmed_realXs {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop} {recs : MethodId → PFact × Bool × Excl × XFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P)
    (hrecs : RecsExactX P (fun _ => True) recs) (hrc : RecsConcX recs) (hrw : RecsWFX recs)
    {M : MethodId} {n : Node} {s : PFact}
    (h : ConfirmedX P taint counted L demand emitX satX restrictX recs sinks roots M n s) :
    ∃ l, Reach P roots M n l ∧ s.covers l :=
  confirmed_realX hmw hup satX_inside restrictX_ok emitX_copies hrecs hrc hrw h

#print axioms confirmed_realXs

/-! ## 7. The run sequence: the records stay exact -/

/-- The restricted run `k + 1` of the sequence: `DRX` with the field limit `Ls k`, the demand
    `dem k` and the records `recs k`. -/
def runX (P : Program) (taint : TaintEdges) (counted : Acc → Bool) (Ls : Nat → Nat)
    (dem : Nat → MethodId → DemandEdge → Prop)
    (emit : PFact → PFact → Excl → Option (PFact × Excl))
    (sat : PFact → Excl → PFact → Excl → Bool)
    (restrict : PFact → Excl → XFact → DemandEdge → Option XFact)
    (recs : Nat → MethodId → PFact × Bool × Excl × XFact → Prop)
    (sinks : List (MethodId × Node × PFact)) (roots : List MethodId) (k : Nat) : XObj → Prop :=
  DRX P taint counted (Ls k) (dem k) emit sat restrict (recs k) sinks roots

/-- The exit edges of run 1, lifted: non-must, no premise exclusion. -/
def liftRecsX (P : Program) (R0 : XObj6 → Prop) (m : MethodId) (x : PFact × Bool × Excl × XFact) :
    Prop :=
  x.2.1 = false ∧ x.2.2.1 = Excl.empty ∧ R0 (.edge m x.1 (P.exit m) x.2.2.2)

/-- The records `recs k` of the restricted run `k + 1` are exit edges of run 1 (lifted) or of an
    earlier restricted run `k' < k`. -/
def RecsFromRunsX (P : Program) (R0 : XObj6 → Prop) (R : Nat → XObj → Prop)
    (recs : Nat → MethodId → PFact × Bool × Excl × XFact → Prop) : Prop :=
  ∀ k m x, recs k m x → liftRecsX P R0 m x ∨ ∃ k', k' < k ∧ exitRecsX P (R k') m x

section Seq
variable {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L0 : Nat}
  {α : MethodId → PFact → PFact} {Ls : Nat → Nat}
  {dem : Nat → MethodId → DemandEdge → Prop}
  {emit : PFact → PFact → Excl → Option (PFact × Excl)}
  {sat : PFact → Excl → PFact → Excl → Bool}
  {restrict : PFact → Excl → XFact → DemandEdge → Option XFact}
  {recs : Nat → MethodId → PFact × Bool × Excl × XFact → Prop}
  {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId}

theorem liftRecsX_exact {ok : Loc → Prop} (hmw : Exact.MarkWF P) (hfo : Exact.FiltOK P ok)
    (hbo : Exact.BackOK P ok) :
    RecsExactX P ok (liftRecsX P (D6X P taint counted L0 α sinks roots)) := by
  intro m j mj jex g hr
  obtain ⟨hmj, hjex, hD⟩ := hr
  have hmj' : mj = false := hmj
  have hjex' : jex = Excl.empty := hjex
  subst hmj' hjex'
  intro hg
  have h6 := D6X_edgeOK hmw hfo hbo hD
  exact ⟨h6.1, h6.2 hg⟩

theorem liftRecsX_conc (R0 : XObj6 → Prop) : RecsConcX (liftRecsX P R0) := by
  intro _ _ _ _ hr _
  have h1 : true = false := hr.1
  cases h1

theorem liftRecsX_wf : RecsWFX (liftRecsX P (D6X P taint counted L0 α sinks roots)) :=
  fun _ _ _ _ _ hr => D6X_wf_edge hr.2.2

#print axioms liftRecsX_exact
#print axioms liftRecsX_conc
#print axioms liftRecsX_wf

/-- RECORD EXACTNESS OVER THE RUN SEQUENCE (general validity). If the records of every restricted
    run are exit edges of run 1 (`D6X`) or of earlier restricted runs (`DRX`), every record set of the
    sequence is exact (`RecsExactX`), with concrete must records (`RecsConcX`) in normal form
    (`RecsWFX`). Hypotheses: those of `DRX_edgeOK` without the record hypotheses. -/
theorem recsSeq_exactX_gen {ok : Loc → Prop} (hmw : Exact.MarkWF P) (hfo : Exact.FiltOK P ok)
    (hbo : Exact.BackOK P ok) (hin : SatInsideX sat) (hsub : RestrictOKX restrict)
    (hem : EmitCopiesMarkX emit)
    (hfrom : RecsFromRunsX P (D6X P taint counted L0 α sinks roots)
      (runX P taint counted Ls dem emit sat restrict recs sinks roots) recs) :
    ∀ k, RecsExactX P ok (recs k) ∧ RecsConcX (recs k) ∧ RecsWFX (recs k) := by
  have h0 := liftRecsX_exact (taint := taint) (counted := counted) (L0 := L0) (α := α)
    (sinks := sinks) (roots := roots) hmw hfo hbo
  have hw0 := liftRecsX_wf (P := P) (taint := taint) (counted := counted) (L0 := L0) (α := α)
    (sinks := sinks) (roots := roots)
  have key : ∀ k j, j ≤ k → RecsExactX P ok (recs j) ∧ RecsConcX (recs j) ∧ RecsWFX (recs j) := by
    intro k
    induction k with
    | zero =>
      intro j hj
      refine ⟨fun m jj mj jex g hr => ?_, fun m jj jex g hr => ?_, fun m jj mj jex g hr => ?_⟩
      · rcases hfrom j m (jj, mj, jex, g) hr with hl | ⟨k', hk', _⟩
        · exact h0 m jj mj jex g hl
        · exact absurd hk' (by omega)
      · rcases hfrom j m (jj, true, jex, g) hr with hl | ⟨k', hk', _⟩
        · exact liftRecsX_conc _ m jj jex g hl
        · exact absurd hk' (by omega)
      · rcases hfrom j m (jj, mj, jex, g) hr with hl | ⟨k', hk', _⟩
        · exact hw0 m jj mj jex g hl
        · exact absurd hk' (by omega)
    | succ k ih =>
      intro j hj
      refine ⟨fun m jj mj jex g hr => ?_, fun m jj jex g hr => ?_, fun m jj mj jex g hr => ?_⟩
      · rcases hfrom j m (jj, mj, jex, g) hr with hl | ⟨k', hk', hx⟩
        · exact h0 m jj mj jex g hl
        · obtain ⟨hE', hC', hW'⟩ := ih k' (by omega)
          exact recs_of_DRX_gen hmw hfo hbo hin hsub hem hE' hC' hW' m jj mj jex g hx
      · rcases hfrom j m (jj, true, jex, g) hr with hl | ⟨k', _, hx⟩
        · exact liftRecsX_conc _ m jj jex g hl
        · exact recsConc_of_DRX hem m jj jex g hx
      · rcases hfrom j m (jj, mj, jex, g) hr with hl | ⟨k', _, hx⟩
        · exact hw0 m jj mj jex g hl
        · exact recsWF_of_DRX m jj mj jex g hx
  exact fun k => key k k (Nat.le_refl k)

#print axioms recsSeq_exactX_gen

/-- RECORD EXACTNESS OVER THE RUN SEQUENCE (`FiltUp` form). -/
theorem recsSeq_exactX (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hin : SatInsideX sat)
    (hsub : RestrictOKX restrict) (hem : EmitCopiesMarkX emit)
    (hfrom : RecsFromRunsX P (D6X P taint counted L0 α sinks roots)
      (runX P taint counted Ls dem emit sat restrict recs sinks roots) recs) :
    ∀ k, RecsExactX P (fun _ => True) (recs k) ∧ RecsConcX (recs k) ∧ RecsWFX (recs k) :=
  recsSeq_exactX_gen hmw (Exact.filtUp_ok hup) (Exact.backOK_true P) hin hsub hem hfrom

#print axioms recsSeq_exactX

/-- RECORD EXACTNESS OVER THE RUN SEQUENCE for valid locations (S13). -/
theorem recsSeq_exactX_valid {ok : Loc → Prop} (hmw : Exact.MarkWF P) (hv : Exact.FiltValid P ok)
    (hbo : Exact.BackOK P ok) (hin : SatInsideX sat) (hsub : RestrictOKX restrict)
    (hem : EmitCopiesMarkX emit)
    (hfrom : RecsFromRunsX P (D6X P taint counted L0 α sinks roots)
      (runX P taint counted Ls dem emit sat restrict recs sinks roots) recs) :
    ∀ k, RecsExactX P ok (recs k) ∧ RecsConcX (recs k) ∧ RecsWFX (recs k) :=
  recsSeq_exactX_gen hmw (Exact.filtValid_ok hv) hbo hin hsub hem hfrom

#print axioms recsSeq_exactX_valid

/-- EVERY CONFIRMED VULNERABILITY OF EVERY RESTRICTED RUN OF THE SEQUENCE IS REAL (`FiltUp` form);
    no record hypothesis remains. -/
theorem seq_confirmed_realX (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hin : SatInsideX sat)
    (hsub : RestrictOKX restrict) (hem : EmitCopiesMarkX emit)
    (hfrom : RecsFromRunsX P (D6X P taint counted L0 α sinks roots)
      (runX P taint counted Ls dem emit sat restrict recs sinks roots) recs)
    (k : Nat) {M : MethodId} {n : Node} {s : PFact}
    (h : ConfirmedX P taint counted (Ls k) (dem k) emit sat restrict (recs k) sinks roots M n s) :
    ∃ l, Reach P roots M n l ∧ s.covers l :=
  let hr := recsSeq_exactX hmw hup hin hsub hem hfrom k
  confirmed_realX hmw hup hin hsub hem hr.1 hr.2.1 hr.2.2 h

#print axioms seq_confirmed_realX

/-- EVERY CONFIRMED VULNERABILITY OF EVERY RESTRICTED RUN OF THE SEQUENCE IS REAL, for a real
    program (S13, every location of the sink pattern valid); no record hypothesis remains. -/
theorem seq_confirmed_realX_valid {ok : Loc → Prop} (hmw : Exact.MarkWF P)
    (hv : Exact.FiltValid P ok) (hbo : Exact.BackOK P ok) (hin : SatInsideX sat)
    (hsub : RestrictOKX restrict) (hem : EmitCopiesMarkX emit)
    (hfrom : RecsFromRunsX P (D6X P taint counted L0 α sinks roots)
      (runX P taint counted Ls dem emit sat restrict recs sinks roots) recs)
    (k : Nat) {M : MethodId} {n : Node} {s : PFact} (hok : ∀ l, s.covers l → ok l)
    (h : ConfirmedX P taint counted (Ls k) (dem k) emit sat restrict (recs k) sinks roots M n s) :
    ∃ l, Reach P roots M n l ∧ s.covers l :=
  let hr := recsSeq_exactX_valid hmw hv hbo hin hsub hem hfrom k
  confirmed_realX_valid hmw hv hbo hin hsub hem hr.1 hr.2.1 hr.2.2 hok h

#print axioms seq_confirmed_realX_valid

end Seq

/-! ## 8. Counterexamples (necessity) -/

namespace CexAbove

/-! ### (a) The exclusion check in the case above is necessary

  The program (bases `1 = this`, `2 = v`, `4 = y`; accessor `3 = name`; mark `5`), one method `0`:
  * node `0 → 1`: `this = srcAny()` (the taint source `zero → (this, [], [any], 5)`);
  * node `1 → 2`: the setter `this.name = v` (the keep edge `this.* →_{name} this.*`, the write
    edge `v.* → this.name.*`; `v` carries nothing);
  * node `2 → 3`: the read `y = this.name`.
  By DESIGN A2 the setter gives the NORMAL `(this, [], [any-taint], {name}, 5)` (no demotion). The
  read is the case above (`this.name.*` below the fact path `this`), its step `name` is EXCLUDED: the
  model gives nothing (`read_nothing`). Without the check (`annXnc`) the read gives the normal
  `(y, [], [any-taint], {}, 5)`, whose location `y` no flow reaches (`this.name` holds `v`). -/

def src : MicroEdge := (zeroFact, ⟨1, [], .any, .conc 5⟩)
def s1 : Stmt := ⟨[zeroBase], [src]⟩
def keep : MicroEdge := (⟨1, [], .star (.set []), .star⟩, ⟨1, [], .star (.set [3]), .star⟩)
def write : MicroEdge := (⟨2, [], .star (.set []), .star⟩, ⟨1, [3], .star (.set []), .star⟩)
def setter : Stmt := ⟨[1], [keep, write]⟩
def rd : MicroEdge := (⟨1, [3], .star (.set []), .star⟩, ⟨4, [], .star (.set []), .star⟩)
def s3 : Stmt := ⟨[1], [rd]⟩
def P : Program := ⟨fun _ => 0, fun _ => 3,
  [(0, 0, .stmt s1, 1), (0, 1, .stmt setter, 2), (0, 2, .stmt s3, 3)]⟩
/-- The source is the only taint edge (decision 3). -/
def taint : TaintEdges := fun e => decide (e = src)
def cnt : Acc → Bool := fun _ => true

/-- After the source: `(this, [], [any-taint], {}, 5)`. -/
def c1 : XFact := ⟨⟨⟨1, [], .any, .conc 5⟩, false⟩, Excl.empty⟩
/-- After the setter: `(this, [], [any-taint], {name}, 5)`, normal (DESIGN A2). -/
def c2 : XFact := ⟨⟨⟨1, [], .any, .conc 5⟩, false⟩, .set [3]⟩
/-- The read without the check: `(y, [], [any-taint], {}, 5)`, normal. -/
def xbad : XFact := ⟨⟨⟨4, [], .any, .conc 5⟩, false⟩, Excl.empty⟩

theorem mem_s1 : ((0 : MethodId), (0 : Node), Instr.stmt s1, (1 : Node)) ∈ P.edges :=
  List.Mem.head _
theorem mem_setter : ((0 : MethodId), (1 : Node), Instr.stmt setter, (2 : Node)) ∈ P.edges :=
  List.Mem.tail _ (List.Mem.head _)
theorem mem_s3 : ((0 : MethodId), (2 : Node), Instr.stmt s3, (3 : Node)) ∈ P.edges :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

abbrev R := D6X P taint cnt 3 policy1 [] [0]

theorem d1 : R (.edge 0 zeroFact 1 c1) :=
  D6X.step (D6X.start (D6X.root (List.mem_singleton.mpr rfl))) mem_s1 (by decide)

/-- The setter result is a normal `[any-taint]/{name}` edge of run 1 (DESIGN A2). -/
theorem d2 : R (.edge 0 zeroFact 2 c2) := D6X.step d1 mem_setter (by decide)

#print axioms d2

/-- (The base model demotes at the setter: there the read is harmless.) -/
theorem base_setter_demand :
    (transferT taint cnt 3 setter c1.af).facts = [⟨⟨1, [], .any, .conc 5⟩, true⟩] := by decide

/-- The model reads the exclusion: the read through the excluded `name` gives NOTHING. -/
theorem read_nothing : (transferX taint cnt 3 s3 c2).facts = [] := by decide

/-- `annX` WITHOUT the exclusion check in the case above (the rule that DESIGN A2 forbids): an
    input above the premise path reads through every first accessor, also an excluded one. -/
def annXnc (c : XFact) (fr : PFact) (fex : Excl) (to : PFact) (tex : Excl) : Option (Bool × Excl) :=
  match relate fr.path c.af.fact.path with
  | .above _ =>
    match to.kind with
    | .star et => some (keepB c, ((tailExcl fr.kind).union fex).union et)
    | .any     => some (false, tex)
    | .exact   => some (false, Excl.empty)
  | _ => annX c fr fex to tex

/-- `applyEdgeX` with `annXnc`. -/
def applyEdgeXnc (c : XFact) (fr : PFact) (fex : Excl) (to : PFact) (tex : Excl) : ResX :=
  match annXnc c fr fex to tex with
  | none => ResX.none
  | some (keep, ex) =>
    ⟨(applyEdge c.af fr to).facts.map (fun y => normX ⟨layerX keep c.af.demand y, ex⟩),
     (applyEdge c.af fr to).reqs⟩

def applyAllXTnc (taint : TaintEdges) (c : XFact) : List MicroEdge → ResX
  | []      => ResX.none
  | e :: es =>
    (⟨(applyEdgeXnc c e.1 Excl.empty e.2 Excl.empty).facts.map (w6tX taint e),
      (applyEdgeXnc c e.1 Excl.empty e.2 Excl.empty).reqs⟩ : ResX).append
      (applyAllXTnc taint c es)

/-- `transferX` with `annXnc`. -/
def transferXnc (taint : TaintEdges) (counted : Acc → Bool) (L : Nat) (s : Stmt) (c : XFact) :
    ResX :=
  if memB c.af.fact.base s.touched then
    let r := applyAllXTnc taint c s.edges
    ⟨r.facts.map (limitFX counted L), r.reqs⟩
  else ⟨[c], []⟩

/-- Without the check the read gives the normal `(y, [], [any-taint], {}, 5)`. -/
theorem read_without_check : (transferXnc taint cnt 3 s3 c2).facts = [xbad] := by decide

theorem markWF : Exact.MarkWF P where
  stmt := by
    intro M n s n' hE e he
    cases hE with
    | head =>
      cases he with
      | head => rfl
      | tail _ h => cases h
    | tail _ h =>
      cases h with
      | head =>
        cases he with
        | head => rfl
        | tail _ h =>
          cases h with
          | head => rfl
          | tail _ h => cases h
      | tail _ h =>
        cases h with
        | head =>
          cases he with
          | head => rfl
          | tail _ h => cases h
        | tail _ h => cases h
  toC := by
    intro M n c n' hE
    cases hE with
    | tail _ h => cases h with
      | tail _ h => cases h with
        | tail _ h => cases h
  fromC := by
    intro M n c n' hE
    cases hE with
    | tail _ h => cases h with
      | tail _ h => cases h with
        | tail _ h => cases h

theorem filtUp : Exact.FiltUp P := by
  intro M n b may n' hE
  cases hE with
  | tail _ h => cases h with
    | tail _ h => cases h with
      | tail _ h => cases h

theorem taintConc : TaintConc P taint := by
  intro M n s n' hE e he ht
  cases hE with
  | head =>
    cases he with
    | head => exact ⟨rfl, ⟨5, rfl⟩, ⟨0, rfl⟩⟩
    | tail _ h => cases h
  | tail _ h =>
    cases h with
    | head =>
      cases he with
      | head => exact absurd ht (by decide)
      | tail _ h =>
        cases h with
        | head => exact absurd ht (by decide)
        | tail _ h => cases h
    | tail _ h =>
      cases h with
      | head =>
        cases he with
        | head => exact absurd ht (by decide)
        | tail _ h => cases h
      | tail _ h => cases h

/-- The concrete flows from the zero location: the zero location at node `0`, a location of `this`
    at node `1`, a location of `this` NOT below `this.name` at node `2`, and nothing at node `3`. -/
theorem flow_inv : ∀ {M l0 n l}, Flow P M l0 n l → l0 = zeroLoc →
    (n = 0 ∧ l = zeroLoc) ∨ (n = 1 ∧ l.base = 1) ∨
      (n = 2 ∧ l.base = 1 ∧ ∀ τ, l.path ≠ 3 :: τ) := by
  intro M l0 n l h
  induction h with
  | start M l0 => intro hl; exact Or.inl ⟨rfl, hl⟩
  | @step M l0 n l n' l' s _ hE hs ih =>
    intro hl0
    have ih' := ih hl0
    cases hE with
    | head =>
      rcases ih' with ⟨_, rfl⟩ | ⟨hn, _⟩ | ⟨hn, _⟩
      · rcases hs with ⟨hm, _⟩ | ⟨e, he, hde⟩
        · exact absurd hm (by decide)
        · cases he with
          | head => exact Or.inr (Or.inl ⟨rfl, hde.2.1⟩)
          | tail _ h => cases h
      · exact absurd hn (by decide)
      · exact absurd hn (by decide)
    | tail _ h =>
      cases h with
      | head =>
        rcases ih' with ⟨hn, _⟩ | ⟨_, hb⟩ | ⟨hn, _⟩
        · exact absurd hn (by decide)
        · rcases hs with ⟨hm, _⟩ | ⟨e, he, hde⟩
          · rw [hb] at hm; exact absurd hm (by decide)
          · cases he with
            | head =>
              obtain ⟨_, hb', _, _, _, σ, τ, _, hp, _, ⟨hτ, hadm⟩⟩ := hde
              refine Or.inr (Or.inr ⟨rfl, hb', fun τ' hτ' => ?_⟩)
              have h1 : σ = 3 :: τ' := by rw [← hτ]; exact hp.symm.trans hτ'
              rw [h1] at hadm
              have h2 : (Excl.set [3]).admits (3 :: τ') = false := rfl
              rw [h2] at hadm
              cases hadm
            | tail _ h =>
              cases h with
              | head =>
                have hb2 : l.base = 2 := hde.1
                rw [hb] at hb2
                exact absurd hb2 (by decide)
              | tail _ h => cases h
        · exact absurd hn (by decide)
      | tail _ h =>
        cases h with
        | head =>
          exfalso
          rcases ih' with ⟨hn, _⟩ | ⟨hn, _⟩ | ⟨_, hb, hnp⟩
          · exact absurd hn (by decide)
          · exact absurd hn (by decide)
          · rcases hs with ⟨hm, _⟩ | ⟨e, he, hde⟩
            · rw [hb] at hm; exact absurd hm (by decide)
            · cases he with
              | head =>
                obtain ⟨_, _, _, _, _, σ, _, hσ, _⟩ := hde
                exact hnp σ hσ
              | tail _ h => cases h
        | tail _ h => cases h
  | pass _ hE _ _ =>
    cases hE with
    | tail _ h => cases h with
      | tail _ h => cases h with
        | tail _ h => cases h
  | call _ hE _ _ _ _ _ _ _ =>
    cases hE with
    | tail _ h => cases h with
      | tail _ h => cases h with
        | tail _ h => cases h
  | clean _ hE _ _ =>
    cases hE with
    | tail _ h => cases h with
      | tail _ h => cases h with
        | tail _ h => cases h
  | filt _ hE _ _ =>
    cases hE with
    | tail _ h => cases h with
      | tail _ h => cases h with
        | tail _ h => cases h

#print axioms flow_inv

/-- No flow from the zero location reaches node `3`. -/
theorem no_flow (l : Loc) : ¬ Flow P 0 zeroLoc 3 l := by
  intro h
  rcases flow_inv h rfl with ⟨hn, _⟩ | ⟨hn, _⟩ | ⟨hn, _⟩ <;> exact absurd hn (by decide)

/-- `CexAbove`: THE EXCLUSION CHECK IN THE CASE ABOVE IS NECESSARY (DESIGN A2: "case above `r`: only
    if `E` admits `r`"). The hypotheses of `D6X_edgeOK` hold (S7, `FiltUp`, `TaintConc`). Run 1
    derives the NORMAL setter result `(this, [], [any-taint], {name}, 5)` (A2: no demotion; the base
    model demotes, `base_setter_demand`). The read `y = this.name` is the case above with the
    EXCLUDED step `name`: the model gives nothing. Without the check the read gives the NORMAL
    `(y, [], [any-taint], {}, 5)`: its pair `(zero, y)` is not a concrete flow (`this.name` holds the
    untainted `v`), so the edge would break the exactness motive `EdgeOK6X`. -/
theorem cex_above :
    Exact.MarkWF P ∧ Exact.FiltUp P ∧ TaintConc P taint ∧
    R (.edge 0 zeroFact 2 c2) ∧ c2.af.demand = false ∧ c2.ex = .set [3] ∧
    (transferX taint cnt 3 s3 c2).facts = [] ∧
    (transferXnc taint cnt 3 s3 c2).facts = [xbad] ∧ xbad.af.demand = false ∧
    denX zeroFact Excl.empty xbad.af.fact xbad.ex zeroLoc ⟨4, [], 5⟩ ∧
    ¬ Flow P 0 zeroLoc 3 ⟨4, [], 5⟩ ∧
    ¬ EdgeOK6X P (fun _ => True) (.edge 0 zeroFact 3 xbad) := by
  have hd : denX zeroFact Excl.empty xbad.af.fact xbad.ex zeroLoc ⟨4, [], 5⟩ :=
    ⟨rfl, rfl, rfl, rfl, trivial, [], [], rfl, rfl, rfl, trivial, rfl, rfl⟩
  refine ⟨markWF, filtUp, taintConc, d2, rfl, rfl, read_nothing, read_without_check, rfl, hd,
    no_flow _, fun h => no_flow _ ((h.2 rfl) zeroLoc ⟨4, [], 5⟩ hd trivial).1⟩

#print axioms cex_above

end CexAbove

namespace CexExactCleaner
open CexAbove (src s1 taint cnt)

/-! ### (b') The `exact` cleaner at `P.f` still demotes

  The program (base `1 = x`; accessors `4 = f`, `6 = g`; mark `5`), one method `0`:
  * node `0 → 1`: `x = srcAny()` (the source `zero → (x, [], [any], 5)`): `[any-taint]` at `P = []`;
  * node `1 → 2`: a cleaner of the mark `5` at EXACTLY `x.f`.
  After the cleaner every location below `x` but `x.f` carries `5`. No `[any-taint]/E` shape holds
  this set: `[any-taint]/{f}` loses the real `x.f.g`, `[any-taint]/{}` claims the cleaned `x.f`. The
  model gives the demand `[any]` (`model_demotes`), which covers `x.f.g`. -/

def clE : Cleaner := ⟨1, [4], .exact, some 5⟩
def Q : Program := ⟨fun _ => 0, fun _ => 2, [(0, 0, .stmt s1, 1), (0, 1, .clean clE, 2)]⟩
def c1 : XFact := ⟨⟨⟨1, [], .any, .conc 5⟩, false⟩, Excl.empty⟩

theorem mem_s1 : ((0 : MethodId), (0 : Node), Instr.stmt s1, (1 : Node)) ∈ Q.edges :=
  List.Mem.head _
theorem mem_cl : ((0 : MethodId), (1 : Node), Instr.clean clE, (2 : Node)) ∈ Q.edges :=
  List.Mem.tail _ (List.Mem.head _)

theorem d1 : D6X Q taint cnt 3 policy1 [] [0] (.edge 0 zeroFact 1 c1) :=
  D6X.step (D6X.start (D6X.root (List.mem_singleton.mpr rfl))) mem_s1 (by decide)

/-- The model demotes: the `exact` cleaner at `x.f` gives the demand `[any]`. -/
theorem model_demotes :
    cleanResX clE c1 = ⟨[⟨⟨⟨1, [], .any, .conc 5⟩, true⟩, Excl.empty⟩], []⟩ := by decide

/-- The location `x.f.g` is real after the cleaner. -/
theorem real_pfg : Flow Q 0 zeroLoc 2 ⟨1, [4, 6], 5⟩ :=
  Flow.clean (Flow.step (Flow.start 0 zeroLoc) mem_s1
    (Or.inr ⟨src, List.Mem.head _, rfl, rfl, rfl, rfl, trivial, [], [4, 6], rfl, rfl, rfl, trivial⟩))
    mem_cl (by decide)

theorem markWF : Exact.MarkWF Q where
  stmt := by
    intro M n s n' hE e he
    cases hE with
    | head =>
      cases he with
      | head => rfl
      | tail _ h => cases h
    | tail _ h => cases h with
      | tail _ h => cases h
  toC := by
    intro M n c n' hE
    cases hE with
    | tail _ h => cases h with
      | tail _ h => cases h
  fromC := by
    intro M n c n' hE
    cases hE with
    | tail _ h => cases h with
      | tail _ h => cases h

theorem filtUp : Exact.FiltUp Q := by
  intro M n b may n' hE
  cases hE with
  | tail _ h => cases h with
    | tail _ h => cases h

/-- The concrete flows from the zero location: at node `2` only locations that the cleaner does not
    clean. -/
theorem flow_invQ : ∀ {M l0 n l}, Flow Q M l0 n l → l0 = zeroLoc →
    (n = 0 ∧ l = zeroLoc) ∨ n = 1 ∨ (n = 2 ∧ clE.cleansB l = false) := by
  intro M l0 n l h
  induction h with
  | start M l0 => intro hl; exact Or.inl ⟨rfl, hl⟩
  | step _ hE _ _ =>
    intro _
    cases hE with
    | head => exact Or.inr (Or.inl rfl)
    | tail _ h => cases h with
      | tail _ h => cases h
  | pass _ hE _ _ =>
    cases hE with
    | tail _ h => cases h with
      | tail _ h => cases h
  | call _ hE _ _ _ _ _ _ _ =>
    cases hE with
    | tail _ h => cases h with
      | tail _ h => cases h
  | @clean M l0 n l n' cl _ hE hcl _ =>
    intro _
    cases hE with
    | tail _ h =>
      cases h with
      | head => exact Or.inr (Or.inr ⟨rfl, hcl⟩)
      | tail _ h => cases h
  | filt _ hE _ _ =>
    cases hE with
    | tail _ h => cases h with
      | tail _ h => cases h

/-- The cleaned location `x.f` is not real after the cleaner. -/
theorem no_flow_pf : ¬ Flow Q 0 zeroLoc 2 ⟨1, [4], 5⟩ := by
  intro h
  rcases flow_invQ h rfl with ⟨hn, _⟩ | hn | ⟨_, hcl⟩
  · exact absurd hn (by decide)
  · exact absurd hn (by decide)
  · exact absurd hcl (by decide)

/-- `CexExactCleaner`: THE `exact` CLEANER AT `P.f` CANNOT KEEP AN `[any-taint]/E` FACT (DESIGN A2:
    "`exact` at `P.f` still demotes"). On the normal `(x, [], [any-taint], {}, 5)` of run 1 and the
    cleaner of `5` at exactly `x.f`:
    (1) `[any-taint]/{f}` would LOSE the real location `x.f.g` (a flow reaches it after the cleaner,
        the cleaner does not clean it, `{f}` excludes it): the analysis would miss a real flow;
    (2) `[any-taint]/{}` in the normal layer would CLAIM the cleaned `x.f` (no flow reaches it): the
        edge would break the exactness motive `EdgeOK6X`.
    The model gives the demand `[any]` (`model_demotes`), which covers `x.f.g`. -/
theorem cex_exact_cleaner :
    Exact.MarkWF Q ∧ Exact.FiltUp Q ∧
    D6X Q taint cnt 3 policy1 [] [0] (.edge 0 zeroFact 1 c1) ∧ carriesB c1.af = true ∧
    cleanResX clE c1 = ⟨[⟨⟨⟨1, [], .any, .conc 5⟩, true⟩, Excl.empty⟩], []⟩ ∧
    Flow Q 0 zeroLoc 2 ⟨1, [4, 6], 5⟩ ∧ clE.cleansB ⟨1, [4, 6], 5⟩ = false ∧
    ¬ coversFX c1.af.fact (.set [4]) ⟨1, [4, 6], 5⟩ ∧
    coversF ⟨1, [], .any, .conc 5⟩ ⟨1, [4, 6], 5⟩ ∧
    clE.cleansB ⟨1, [4], 5⟩ = true ∧ ¬ Flow Q 0 zeroLoc 2 ⟨1, [4], 5⟩ ∧
    ¬ EdgeOK6X Q (fun _ => True) (.edge 0 zeroFact 2 c1) := by
  have hd : denX zeroFact Excl.empty c1.af.fact c1.ex zeroLoc ⟨1, [4], 5⟩ :=
    ⟨rfl, rfl, rfl, rfl, trivial, [], [4], rfl, rfl, rfl, trivial, rfl, rfl⟩
  refine ⟨markWF, filtUp, d1, rfl, model_demotes, real_pfg, by decide, ?_,
    ⟨rfl, ⟨[4, 6], rfl, trivial⟩, 5, rfl, rfl⟩, by decide, no_flow_pf,
    fun h => no_flow_pf ((h.2 rfl) zeroLoc ⟨1, [4], 5⟩ hd trivial).1⟩
  intro hc
  obtain ⟨_, ⟨τ, hp, _, ha⟩, _⟩ := hc
  have hτ : τ = [4, 6] := hp.symm
  rw [hτ] at ha
  exact absurd ha (by decide)

#print axioms cex_exact_cleaner

end CexExactCleaner

namespace CexRestrictSub

/-! ### The contract `RestrictSubX` is false for `restrictX`

  A `*` conclusion that (against the normal form) carries the exclusion `{3}`: the restriction keeps
  it at the same path and `normX` drops the exclusion, so the restricted edge has the pair
  `(x.3, y.3)`, which the input edge excludes. So the closure theorems read `RestrictOKX` (the input
  in normal form), which `restrictX` has (`restrictX_ok`). -/

def j : PFact := ⟨1, [], .star (.set []), .star⟩
def g : XFact := ⟨⟨⟨2, [], .star (.set []), .star⟩, false⟩, .set [3]⟩
def d : DemandEdge := ⟨⟨1, [], .star (.set []), .star⟩, some ⟨2, [], .star (.set []), .star⟩⟩
def g' : XFact := ⟨g.af, Excl.empty⟩

theorem restrict_eq : restrictX j Excl.empty g d = some g' := by decide

/-- `CexRestrictSub`: the input `g` is NOT in normal form, `restrictX` gives `g'` with more pairs, so
    `RestrictSubX restrictX` is false. -/
theorem cex_restrict_sub : ¬ WFX g ∧ restrictX j Excl.empty g d = some g' ∧
    ¬ RestrictSubX restrictX := by
  refine ⟨fun h => ?_, restrict_eq, fun h => ?_⟩
  · have h1 : g.ex = Excl.empty := h rfl
    cases h1
  · obtain ⟨_, hsub⟩ := h j Excl.empty g d g' restrict_eq
    have hd : denX j Excl.empty g'.af.fact g'.ex ⟨1, [3], 0⟩ ⟨2, [3], 0⟩ :=
      ⟨rfl, rfl, trivial, rfl, trivial, [3], [3], rfl, rfl, rfl, ⟨rfl, rfl⟩, rfl, rfl⟩
    obtain ⟨_, _, _, _, _, σ, τ, _, hp, _, _, _, he⟩ := hsub _ _ hd
    have hτ : τ = [3] := hp.symm
    rw [hτ] at he
    exact absurd he (by decide)

#print axioms cex_restrict_sub

end CexRestrictSub

namespace CexSideConditions

/-! ### The side conditions `htx`, `hfx` of the core lemma are necessary

  `htx` is what the normal form of a summary conclusion gives (`WFX`; so the closures need
  `RecsWFX` and the output part of `RestrictOKX`); `hfx` is what run 1 (no premise exclusion) and a
  concrete restricted run (no `*` fact) give. -/

def a : XFact := ⟨⟨⟨1, [], .any, .conc 5⟩, false⟩, Excl.empty⟩
def j : PFact := ⟨1, [], .star (.set []), .star⟩
def g : XFact := ⟨⟨⟨2, [], .star (.set []), .star⟩, false⟩, .set [3]⟩
def r : XFact := ⟨⟨⟨2, [], .any, .conc 5⟩, false⟩, Excl.empty⟩

/-- `htx` IS NECESSARY (the summary conclusion in normal form). A `*` summary conclusion that
    carries the exclusion `{3}` (not in normal form): the result on the `[any-taint]` added fact
    `(x, [], [any-taint], {}, 5)` is the normal `(y, [], [any-taint], {}, 5)`; it admits `y.3`, but
    no admitted summary pair ends at `y.3`. -/
theorem cex_htx : ¬ WFX g ∧ (applySummaryX a j Excl.empty g).facts = [r] ∧
    coversFX r.af.fact r.ex ⟨2, [3], 5⟩ ∧
    ¬ ∃ l1, coversFX a.af.fact a.ex l1 ∧ denX j Excl.empty g.af.fact g.ex l1 ⟨2, [3], 5⟩ := by
  refine ⟨fun h => ?_, by decide, ⟨rfl, ⟨[3], rfl, trivial, rfl⟩, 5, rfl, rfl⟩, ?_⟩
  · have h1 : g.ex = Excl.empty := h rfl
    cases h1
  · intro ⟨l1, _, hd⟩
    have h := denX_fex hd [3] rfl
    exact absurd h (by decide)

#print axioms cex_htx

def c : XFact := ⟨⟨⟨1, [], .star (.set []), .star⟩, false⟩, Excl.empty⟩
def fr : PFact := ⟨1, [], .star (.set []), .star⟩
def to : PFact := ⟨2, [], .star (.set []), .star⟩
def rs : XFact := ⟨⟨⟨2, [], .star (.set []), .star⟩, false⟩, Excl.empty⟩
def ic : PFact := ⟨0, [], .star (.set []), .star⟩

/-- `hfx` IS NECESSARY (a premise exclusion meets only a non-`*` concrete input). The edge
    `(x, [], */{}) /{3} → (y, [], */{})` on the `*` fact `(x, [], */{}, *)` gives the normal
    correlated `(y, [], */{}, *)` (a `*` result cannot carry the exclusion `{3}`); its pair
    `(i.3, y.3)` has no middle location that the premise exclusion `{3}` admits. -/
theorem cex_hfx : (applyEdgeX c fr (.set [3]) to Excl.empty).facts = [rs] ∧
    denX ic Excl.empty rs.af.fact rs.ex ⟨0, [3], 7⟩ ⟨2, [3], 7⟩ ∧
    ¬ ∃ l1, denX ic Excl.empty c.af.fact c.ex ⟨0, [3], 7⟩ l1 ∧
      denX fr (.set [3]) to Excl.empty l1 ⟨2, [3], 7⟩ := by
  refine ⟨by decide, ⟨rfl, rfl, trivial, rfl, trivial, [3], [3], rfl, rfl, rfl, ⟨rfl, rfl⟩, rfl, rfl⟩,
    ?_⟩
  intro ⟨l1, hd1, hd2⟩
  obtain ⟨_, _, _, _, _, σ0, τ1, h0p, h1p, _, ⟨hτ, _⟩, _, _⟩ := hd1
  have hσ : σ0 = [3] := (cont_unique h0p (show (⟨0, [3], 7⟩ : Loc).path = ic.path ++ [3] from rfl))
  have h1 : l1.path = fr.path ++ [3] := by rw [h1p, hτ, hσ]; rfl
  have h := denX_iex hd2 [3] h1
  exact absurd h (by decide)

#print axioms cex_hfx

end CexSideConditions

end ApSpec.AnyTaintExExact

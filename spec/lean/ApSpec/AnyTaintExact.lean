/-
  ApSpec.AnyTaintExact — the PRECISION side of the `[any-taint]` tail kind (decision F69).

  Namespace: `ApSpec.AnyTaintExact` (the definitions are in `ApSpec.AnyTaint`, file
  `AnyTaintDefs.lean`; this file does not change them).

  `Exact.lean` and `RestrictedExact.lean` prove that a normal edge of `D` and of `DR` is PAIR-EXACT:
  every pair `(l0, l)` of its denotation `den i f` (to a valid end location) is a concrete flow. This
  file proves the same for the two new closures of `AnyTaintDefs.lean`:
    * run 1 with the rule W6T, `D6T`: its normal edges are pair-exact (an `.any` normal sink
      edge, an `[any-taint]`, included), and a vulnerability confirmed on a NORMAL sink edge
      (`ConfirmedT6`) is real;
    * the restricted forward run with must-premises, `DRT`: a normal edge of a non-must premise is
      pair-exact; a normal edge of a MUST-PREMISE (spec premise `[any-taint]`, `must = true`) is
      END-EXACT; a vulnerability confirmed on a normal sink edge under a supported premise
      (`ConfirmedT`, `SupT`) is real.

  END-EXACT (`AnyTaint.EndExact`, DESIGN §1). An edge `(j, must) → f` of a must-premise holds when
  EVERY location of `j` carries the mark. It is END-EXACT if every valid location `l` of the
  conclusion `f` (`coversF f l`: the base, a path `f.path ++ τ` that the tail admits, the concrete
  mark) is reached by a concrete flow from SOME valid location `l0` of the premise (`j.covers l0`).
  It is not exact pair by pair: the start fact of a must-premise is the premise itself, and its
  `den` relates every `σ` to every `τ` (`CexApp.record_not_pair_exact`). So:
    * a must record must be applied only to an added fact that covers its premise (`satI`): every
      location of the premise is then a location of the added fact, so it is reached; an
      application by `applicable` (the added fact inside the premise) must give a DEMAND result
      (`recLayer`; `CexApp.cex_app` shows that a normal result is false);
    * a must record must not be reversed: its reversal is not a converse-flow edge
      (`CexRev.cex_rev`).

  Main results (all constructive; see the `#print axioms` lines):
    0. Helpers read on LOCATIONS: `applyEdge_cov`, `transfer_cov`, `cleanRes_cov` (a location of a
       normal result has a middle location in the input: the pair lemmas of `Exact.lean` hold for
       every premise, so the premise `anyP` gives them), `den_swap` (an uncorrelated fact: every
       location is the end of a pair from a given start), `coversF_of_inside`, `sink_den`,
       `sink_cov` (a common location of the sink fact and the sink pattern).
    1. Run 1: `D6T_edgeOK`, `edge_exact6T`, `edge_exact_valid6T`, `recs_of_D6T(_valid, _gen)`,
       `D6T_NS`, `sup_entry6T(_valid)`, `confirmed_real6T`, `confirmed_real_valid6T(_of)`.
    2. The restricted run, invariants: `DRT_concrete`, `DRT_mustAny`, `DRT_legal`, `DRT_nonstar`.
    3. The restricted run, exactness: `summaryT_pair`, `summaryT_end` (the four cases of a summary
       application), `DRT_edgeOK` (the motive `EdgeOKT` on every object).
    4. `edge_exactT`, `edge_exactT_valid`, `recs_of_DRT(_valid, _gen)`, `recsConc_of_DRT`,
       `recsT_union`, `recsT_mono`, `recsConcT_union`, `recsConcT_lift`; the support and the
       confirmation: `sup_entryT(_valid)`, `confirmed_realT`, `confirmed_realT_valid(_of)`;
       `spec_rules` (`emitM`, `satI`, `restrictU` satisfy the rule hypotheses).
    5. The run sequence: `recsSeq_exactT(_valid)`, `seq_confirmed_realT(_valid)`: run 1 (`D6T`)
       and the restricted runs (`DRT`) keep the records exact; no record hypothesis remains.
    6. Counterexamples: `CexApp.cex_app` (the demotion `recLayer` is necessary),
       `CexRecConc.cex_rec_conc` (the new record hypothesis `RecsConcT` is necessary),
       `CexRev.cex_rev` (a must record must not be reversed), `CexSupMark.cex_sup_mark` (the mark
       equality of `SupLink`).

  NEW HYPOTHESES (reported; each one with the spec item that makes it true):
    * `SatInside sat` (in place of `RExact.SatMark`, which it implies): a must callee premise is
      END-EXACT, so its summary is exact only for an added fact that covers the premise. `satI`
      has it (`satI_inside`; ap.md §4.3). `CexApp` is the same application through a record; for
      the rule `ret` the necessity is argued, not proved (it needs a second call site).
    * `EmitCopiesMark emit`: the run is concrete (`DRT_concrete`). END-EXACT reads the locations
      `coversF`, which exist only for a concrete mark. `emitM` has it (§6.3 C3).
    * `RecsConcT recs`: a normal must record has a concrete conclusion mark. `EndExact` is VACUOUS
      for an abstract conclusion mark (`coversF` is empty), so without it a must record says
      nothing (`CexRecConc.cex_rec_conc`). The premise mark is then concrete by the mark part of
      `RecsExactT` (`conc_of_absImp`). The records of a concrete run have it (`recsConc_of_DRT`),
      run 1 gives no must record (`recsConcT_lift`), so the run sequence discharges it
      (`recsSeq_exactT`).
  The other hypotheses are those of `RExact.DR_edgeOK`/`confirmed_realM_gen`: S7 (`MarkWF`),
  `FiltUp` or S13 (`FiltValid`, `BackOK`), `RestrictSub restrict`, exact records (`RecsExactT`).
-/
import ApSpec.AnyTaintDefs
import ApSpec.BackwardExact

namespace ApSpec.AnyTaintExact
open ApSpec ApSpec.AnyTaint

/-! ## 0. Helpers: locations of a conclusion, and the pair lemmas read on locations -/

theorem tailF_tailI {k : Kind} {σ τ : List Acc} (h : tailF k σ τ) : tailI k τ := by
  cases k with
  | star e =>
    obtain ⟨h1, h2⟩ := h
    rw [h1]; exact h2
  | any => trivial
  | exact => exact h

theorem tailF_self {k : Kind} {τ : List Acc} (h : tailI k τ) : tailF k τ τ := by
  cases k with
  | star e => exact ⟨rfl, h⟩
  | any => trivial
  | exact => exact h

theorem absB_conc {m : MarkA} (h : ∃ t, m = .conc t) : Exact.absB m = false := by
  obtain ⟨t, rfl⟩ := h
  rfl

theorem concOK_conc (tm : MarkA) {cm : MarkA} (h : ∃ t, cm = .conc t) :
    Exact.concOKB tm cm = true := by
  obtain ⟨t, rfl⟩ := h
  cases tm <;> rfl

/-- The end location of a pair of `den` is a location of the conclusion (concrete mark). -/
theorem den_coversF {i f : PFact} {l0 l : Loc} (hd : den i f l0 l) (hm : ∃ t, f.mark = .conc t) :
    coversF f l := by
  obtain ⟨_, hlb, _, hlm, _, σ, τ, _, hlp, _, hF⟩ := hd
  obtain ⟨t, ht⟩ := hm
  refine ⟨hlb, ⟨τ, hlp, tailF_tailI hF⟩, t, ht, ?_⟩
  rw [hlm, ht]
  rfl

/-- The auxiliary premise: the `[any]` tail and the mark `*`. Every location of a conclusion is
    the end of a pair of `den anyP` (`coversF_den`), so the pair lemmas (`applyEdge_exact`,
    `transfer_exact`, `cleanRes_exact`), which hold for EVERY premise, give the middle location of
    a location. -/
def anyP : PFact := ⟨0, [], .any, .star⟩

theorem coversF_den {f : PFact} {l : Loc} (h : coversF f l) : ∃ l0, den anyP f l0 l := by
  obtain ⟨hb, ⟨τ, hp, hI⟩, t, ht, hm⟩ := h
  refine ⟨⟨0, τ, l.mark⟩, rfl, hb, trivial, ?_, ?_, τ, τ, rfl, hp, trivial, tailF_self hI⟩
  · rw [ht]; exact hm
  · rw [ht]; trivial

/-- A location of a micro-edge or summary result has a middle location in the input fact. -/
theorem applyEdge_cov {c r : AFact} {fr to : PFact} {l : Loc}
    (hpm : Exact.premOKB fr.mark c.fact.mark = true) (hcm : Exact.concOKB to.mark c.fact.mark = true)
    (hc : c.demand = false) (hr : r ∈ (applyEdge c fr to).facts) (hra : r.demand = false)
    (hcc : ∃ t, c.fact.mark = .conc t) (hl : coversF r.fact l) :
    ∃ l1, coversF c.fact l1 ∧ den fr to l1 l := by
  obtain ⟨l0, hd⟩ := coversF_den hl
  obtain ⟨l1, hd1, hd2⟩ := Exact.applyEdge_exact hpm hcm hc hr hra hd
  exact ⟨l1, den_coversF hd1 hcc, hd2⟩

#print axioms applyEdge_cov

/-- A location of a statement result has a source location in the input fact. -/
theorem transfer_cov {counted : Acc → Bool} {L : Nat} {s : Stmt} {c r : AFact} {l : Loc}
    (hmk : ∀ e, e ∈ s.edges → Exact.markEdgeB e.1.mark e.2.mark = true)
    (hc : c.demand = false) (hr : r ∈ (transfer counted L s c).facts) (hra : r.demand = false)
    (hcc : ∃ t, c.fact.mark = .conc t) (hl : coversF r.fact l) :
    ∃ l1, coversF c.fact l1 ∧ s.step l1 l := by
  obtain ⟨l0, hd⟩ := coversF_den hl
  obtain ⟨l1, hd1, hs⟩ := Exact.transfer_exact hmk hc hr hra hd
  exact ⟨l1, den_coversF hd1 hcc, hs⟩

#print axioms transfer_cov

/-- A location of a normal cleaner result is a location of the input that the cleaner keeps. -/
theorem cleanRes_cov {cl : Cleaner} {c r : AFact} {l : Loc}
    (hr : r ∈ (cleanRes cl c).facts) (hra : r.demand = false)
    (hcc : ∃ t, c.fact.mark = .conc t) (hl : coversF r.fact l) :
    coversF c.fact l ∧ cl.cleansB l = false := by
  obtain ⟨l0, hd⟩ := coversF_den hl
  obtain ⟨hd1, hcl⟩ := Exact.cleanRes_exact hr hra hd
  exact ⟨den_coversF hd1 hcc, hcl⟩

#print axioms cleanRes_cov

/-- A fact without the `*` tail is UNCORRELATED: with a start location `l0` of one pair, every
    location of the fact is the end of a pair from `l0`. -/
theorem den_swap {i a : PFact} {l0 l1 l1' : Loc} (hns : a.kind.isStar = false)
    (hd : den i a l0 l1) (hl : coversF a l1') : den i a l0 l1' := by
  obtain ⟨h0b, _, h0m, _, hps, σ, _, h0p, _, hI, _⟩ := hd
  obtain ⟨hb, ⟨τ, hp, hτ⟩, t, ht, hm⟩ := hl
  refine ⟨h0b, hb, h0m, ?_, hps, σ, τ, h0p, hp, hI, ?_⟩
  · rw [ht, hm]; rfl
  · cases hk : a.kind with
    | star e => rw [hk] at hns; cases hns
    | any => trivial
    | exact => rw [hk] at hτ; exact hτ

#print axioms den_swap

/-- An exact premise with a concrete mark: its one location is the start of a pair to every
    location of a fact without the `*` tail whose mark lets the premise mark pass. -/
theorem den_exact_prem {i a : PFact} {t0 : Mark} {l : Loc} (hik : i.kind = .exact)
    (him : i.mark = .conc t0) (hns : a.kind.isStar = false) (hps : a.mark.passes t0)
    (hb : l.base = a.base) (hp : ∃ τ, l.path = a.path ++ τ ∧ tailI a.kind τ)
    (hm : l.mark = a.mark.out t0) :
    den i a ⟨i.base, i.path, t0⟩ l := by
  obtain ⟨τ, hlp, hτ⟩ := hp
  refine ⟨rfl, hb, ?_, hm, hps, [], τ, (List.append_nil _).symm, hlp, ?_, ?_⟩
  · rw [him]; exact rfl
  · rw [hik]; exact rfl
  · cases hk : a.kind with
    | star e => rw [hk] at hns; cases hns
    | any => trivial
    | exact => rw [hk] at hτ; exact hτ

#print axioms den_exact_prem

/-- A premise inside the location part of a fact (`satI`), with the same concrete mark: every
    location of the premise is a location of the fact. -/
theorem coversF_of_inside {a j : PFact} {l : Loc}
    (hin : coversB ⟨a.base, a.path, a.kind, .star⟩ j = true) (hsm : markSubB j.mark a.mark = true)
    (hjc : ∃ t, j.mark = .conc t) (hl : j.covers l) : coversF a l := by
  obtain ⟨hb, hp, -⟩ := coversB_sound hin hl
  obtain ⟨t, ht⟩ := hjc
  have hlm : l.mark = t := by
    have h := hl.2.2
    rw [ht] at h
    exact h
  rw [ht] at hsm
  cases ham : a.mark with
  | conc t' =>
    rw [ham] at hsm
    have e : t = t' := Nat.eq_of_beq_eq_true hsm
    exact ⟨hb, hp, t', ham, hlm.trans e⟩
  | star => rw [ham] at hsm; cases hsm
  | starEx x => rw [ham] at hsm; cases hsm

#print axioms coversF_of_inside

/-- A concrete premise mark that is a sub-mark of the fact mark: the fact mark is the same. -/
theorem markSub_conc {jm am : MarkA} (hjc : ∃ t, jm = .conc t) (hsm : markSubB jm am = true) :
    am = jm := by
  obtain ⟨t, rfl⟩ := hjc
  cases am with
  | conc t' =>
    have e : t = t' := Nat.eq_of_beq_eq_true hsm
    rw [e]
  | star => cases hsm
  | starEx x => cases hsm

/-- A result of `applyEdge` with a concrete mark has no `*` tail (W2, in any layer). -/
theorem applyEdge_conc_nonstar {c r : AFact} {fr to : PFact} (hr : r ∈ (applyEdge c fr to).facts)
    (hc : ∃ t, r.fact.mark = .conc t) : r.fact.kind.isStar = false := by
  cases hk : r.fact.kind with
  | star e =>
    obtain ⟨t, ht⟩ := hc
    exact absurd ht ((Invariant.applyEdge_legal hr hk).1.not_conc t)
  | any => rfl
  | exact => rfl

/-- Two overlapping facts have a common path (marks ignored). -/
theorem overlap_common {a s : PFact} (h : overlapB a s = true) :
    a.base = s.base ∧ ∃ p, (∃ τ, p = a.path ++ τ ∧ tailI a.kind τ) ∧
      (∃ σ, p = s.path ++ σ ∧ tailI s.kind σ) := by
  unfold overlapB at h
  cases hb : Nat.beq a.base s.base with
  | false => rw [hb] at h; cases h
  | true =>
    rw [hb] at h
    refine ⟨Nat.eq_of_beq_eq_true hb, ?_⟩
    cases hrel : relate a.path s.path with
    | below r =>
      rw [hrel] at h
      have hr : admitsTailB a.kind r = true := h
      exact ⟨s.path, ⟨r, Exact.relate_below hrel, Exact.admitsTailB_tailI hr⟩,
        [], (List.append_nil _).symm, Exact.tailI_nil _⟩
    | above r =>
      rw [hrel] at h
      have hr : admitsTailB s.kind r = true := h
      exact ⟨a.path, ⟨[], (List.append_nil _).symm, Exact.tailI_nil _⟩,
        r, Exact.relate_above hrel, Exact.admitsTailB_tailI hr⟩
    | apart => rw [hrel] at h; cases h

#print axioms overlap_common

/-- THE SINK LOCATION. A triggered check under an exact premise with the concrete mark `t0`, on a
    sink fact without the `*` tail: a COMMON location of the sink fact and the sink pattern is the
    end of a pair from the premise location, and the sink pattern covers it. For an `.any` sink
    fact (`[any-taint]`) this is every common location (`tailF .any`). -/
theorem sink_den {i s : PFact} {f : AFact} {t0 : Mark} (hik : i.kind = .exact)
    (him : i.mark = .conc t0) (hns : f.fact.kind.isStar = false) (hch : check i f s = .triggered) :
    ∃ l, den i f.fact ⟨i.base, i.path, t0⟩ l ∧ s.covers l := by
  obtain ⟨T, hsm, ho, hmo, hps⟩ := Confirmed.check_triggered_passes him hch
  obtain ⟨hb, p, ⟨τ, hpa, hτ⟩, σ, hps', hσ⟩ := overlap_common ho
  refine ⟨⟨f.fact.base, p, T⟩, den_exact_prem hik him hns hps rfl ⟨τ, hpa, hτ⟩ hmo.symm,
    hb, ⟨σ, hps', hσ⟩, ?_⟩
  rw [hsm]
  exact rfl

#print axioms sink_den

/-- The sink location for a concrete sink fact: a common location of the sink fact and of the
    sink pattern, with the mark of the sink. -/
theorem sink_cov {i s : PFact} {f : AFact} {t0 : Mark} (him : i.mark = .conc t0)
    (hfc : ∃ t, f.fact.mark = .conc t) (hch : check i f s = .triggered) :
    ∃ l, coversF f.fact l ∧ s.covers l := by
  obtain ⟨T, hsm, ho, hmo, _⟩ := Confirmed.check_triggered_passes him hch
  obtain ⟨hb, p, ⟨τ, hpa, hτ⟩, σ, hps', hσ⟩ := overlap_common ho
  obtain ⟨tf, htf⟩ := hfc
  have hT : tf = T := by rw [htf] at hmo; exact hmo
  refine ⟨⟨f.fact.base, p, T⟩, ⟨rfl, ⟨τ, hpa, hτ⟩, tf, htf, hT.symm⟩, hb, ⟨σ, hps', hσ⟩, ?_⟩
  rw [hsm]
  exact rfl

#print axioms sink_cov

/-- A location of a concrete premise is a location of the premise read as a conclusion. -/
theorem coversF_of_covers {i : PFact} {l : Loc} (hic : ∃ t, i.mark = .conc t) (h : i.covers l) :
    coversF i l :=
  (coversF_iff i l).mpr ⟨h, hic⟩

/-! ## 1. Run 1 with W6T (`D6T`): exactness and confirmation

  W6T only raises the layer of a statement result (`transferT_mem`: the same fact, `W6.LE`). A
  NORMAL result of `transferT` is a normal result of `transfer` (`W6.LE.eq_of_normal`), so the
  proof of `Exact.D_edgeOK` carries over rule by rule; only the case `step` changes. -/

section Run1
variable {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
  {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId}

/-- The motive `Exact.EdgeOK` holds on every object of `D6T` (the hypotheses of
    `Exact.D_edgeOK`: S7 `MarkWF`, the filter condition `FiltOK` and `BackOK` for the valid
    locations `ok`). -/
theorem D6T_edgeOK {ok : Loc → Prop} (hmw : Exact.MarkWF P) (hfo : Exact.FiltOK P ok)
    (hbo : Exact.BackOK P ok) {o : Obj}
    (h : D6T P taint counted L α sinks roots o) : Exact.EdgeOK P ok o := by
  induction h with
  | root => trivial
  | @start M i _ _ =>
    refine ⟨fun hi => by rw [startFact_mark]; exact hi, ?_⟩
    intro ha l0 l hd hok
    have e := Exact.startFact_exact ha hd
    subst e
    exact ⟨Flow.start M l, hok⟩
  | @step M i n f n' s f' _ hE hf ih =>
    obtain ⟨f0, hf0, hle⟩ := transferT_mem hf
    refine ⟨fun hi => ?_, ?_⟩
    · rw [← hle.fact]
      exact Exact.transfer_abs (hmw.stmt _ _ _ _ hE) (ih.1 hi) hf0
    · intro ha l0 l hd hok
      have e := hle.eq_of_normal ha
      subst e
      have hfa := Exact.transfer_demand hf0 ha
      obtain ⟨l1, hd1, hs⟩ := Exact.transfer_exact (hmw.stmt _ _ _ _ hE) hfa hf0 ha hd
      have hok1 : ok l1 := by
        rcases hs with ⟨-, rfl⟩ | ⟨e, he, hde⟩
        · exact hok
        · exact hbo.stmt _ _ _ _ hE e he _ _ hde hok
      obtain ⟨hfl, hok0⟩ := ih.2 hfa l0 l1 hd1 hok1
      exact ⟨Flow.step hfl hE hs, hok0⟩
  | reqStmt => trivial
  | @pass M i n f n' c _ hE hm ih =>
    refine ⟨ih.1, ?_⟩
    intro ha l0 l hd hok
    obtain ⟨hfl, hok0⟩ := ih.2 ha l0 l hd hok
    refine ⟨Flow.pass hfl hE ?_, hok0⟩
    rw [hd.2.1]
    exact hm
  | added => trivial
  | initA => trivial
  | @ret M i n f n' c e1 a j g r e2 r' _ hE he1 ha _ happ _ hr he2 hr' ihD _ ihG =>
    refine ⟨fun hi => ?_, ?_⟩
    · have hA := Exact.applyEdge_abs (hmw.toC _ _ _ _ hE e1 he1) (ihD.1 hi) ha
      obtain ⟨x, hx, hxm⟩ := Exact.applySummary_mark hr
      obtain ⟨hgx, hcx⟩ := Exact.applyEdge_mark hx
      have hG := ihG.1 (Exact.gate_abs hgx hA)
      have hR : Exact.absB r.fact.mark = true := by rw [hxm]; exact Exact.comp_abs hG hA hcx
      rw [limitF_mark]
      exact Exact.applyEdge_abs (hmw.fromC _ _ _ _ hE e2 he2) hR hr'
    · intro hla l0 l hd hok
      have e := Exact.limitF_exact hla
      rw [e] at hd hla
      have hra := Exact.applyEdge_demand hr' hla
      obtain ⟨hp3, hc3⟩ := Exact.markEdge_ok (hmw.fromC _ _ _ _ hE e2 he2)
        (Exact.applyEdge_mark hr').1
      obtain ⟨l2, hd2, hde2⟩ := Exact.applyEdge_exact hp3 hc3 hra hr' hla hd
      have hok2 : ok l2 := hbo.fromC _ _ _ _ hE e2 he2 _ _ hde2 hok
      obtain ⟨x, hx, rfl⟩ := Exact.applySummary_mem hr hra
      obtain ⟨hxa, hga⟩ := Exact.or_eq_false hra
      have haa := Exact.applyEdge_demand hx hxa
      have hfa := Exact.applyEdge_demand ha haa
      have hp2 : Exact.premOKB j.mark a.fact.mark = true :=
        Exact.premOK_of_sub (Exact.applicable_markSub happ)
      have hc2 : Exact.concOKB g.fact.mark a.fact.mark = true :=
        Exact.concOK_of (fun hA => ihG.1 (Exact.gate_abs (Exact.applyEdge_mark hx).1 hA))
      obtain ⟨l1', hd1', hdg⟩ := Exact.applyEdge_exact hp2 hc2 haa hx hxa hd2
      obtain ⟨hflG, hok1'⟩ := ihG.2 hga l1' l2 hdg hok2
      obtain ⟨hp1, hc1⟩ := Exact.markEdge_ok (hmw.toC _ _ _ _ hE e1 he1)
        (Exact.applyEdge_mark ha).1
      obtain ⟨l1, hd1, hde1⟩ := Exact.applyEdge_exact hp1 hc1 hfa ha haa hd1'
      have hok1 : ok l1 := hbo.toC _ _ _ _ hE e1 he1 _ _ hde1 hok1'
      obtain ⟨hflD, hok0⟩ := ihD.2 hfa l0 l1 hd1 hok1
      exact ⟨Flow.call hflD hE he1 hde1 hflG he2 hde2, hok0⟩
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial
  | @clean M i n f n' cl f' _ hE hf ih =>
    refine ⟨fun hi => Exact.cleanRes_abs (ih.1 hi) hf, ?_⟩
    intro ha l0 l hd hok
    have hfa := Exact.cleanRes_demand hf ha
    obtain ⟨hd1, hcl⟩ := Exact.cleanRes_exact hf ha hd
    obtain ⟨hfl, hok0⟩ := ih.2 hfa l0 l hd1 hok
    exact ⟨Flow.clean hfl hE hcl, hok0⟩
  | reqClean => trivial
  | @filt M i n f n' b may _ hE hp ih =>
    refine ⟨ih.1, ?_⟩
    intro ha l0 l hd hok
    obtain ⟨hfl, hok0⟩ := ih.2 ha l0 l hd hok
    refine ⟨Flow.filt hfl hE ?_, hok0⟩
    intro hb
    obtain ⟨-, hlb, -, -, -, σ, τ, -, hlp, -, -⟩ := hd
    exact hfo _ _ _ _ _ hE f.fact.path τ l (hp (hlb.symm.trans hb)) hlp hok hb

#print axioms D6T_edgeOK

/-- RUN 1 IS EXACT (`FiltUp` form). Every pair of a NORMAL edge of `D6T` is a concrete flow. The
    edge can have the `.any` tail (a normal `[any-taint]`: the result of a taint source). Hypotheses:
    S7 (`MarkWF P`) and `FiltUp P`, as `Exact.edge_exact`. -/
theorem edge_exact6T (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P)
    {M : MethodId} {i : PFact} {n : Node} {f : AFact} {l0 l : Loc}
    (h : D6T P taint counted L α sinks roots (.edge M i n f)) (ha : f.demand = false)
    (hd : den i f.fact l0 l) : Flow P M l0 n l :=
  ((D6T_edgeOK (ok := fun _ => True) hmw (Exact.filtUp_ok hup) (Exact.backOK_true P) h).2
    ha l0 l hd trivial).1

#print axioms edge_exact6T

/-- RUN 1 IS EXACT FOR VALID LOCATIONS (prefix-closed type filters; S7, S13). Every pair of a
    normal edge of `D6T` to a valid end location is a concrete flow from a valid start location. -/
theorem edge_exact_valid6T {ok : Loc → Prop} (hmw : Exact.MarkWF P) (hv : Exact.FiltValid P ok)
    (hbo : Exact.BackOK P ok)
    {M : MethodId} {i : PFact} {n : Node} {f : AFact} {l0 l : Loc}
    (h : D6T P taint counted L α sinks roots (.edge M i n f)) (ha : f.demand = false)
    (hd : den i f.fact l0 l) (hok : ok l) : Flow P M l0 n l ∧ ok l0 :=
  (D6T_edgeOK hmw (Exact.filtValid_ok hv) hbo h).2 ha l0 l hd hok

#print axioms edge_exact_valid6T

/-- The exit edges of run 1 (`D6T`) are exact records for valid locations (`RExact.RecsExactV`). -/
theorem recs_of_D6T_valid {ok : Loc → Prop} (hmw : Exact.MarkWF P) (hv : Exact.FiltValid P ok)
    (hbo : Exact.BackOK P ok) :
    RExact.RecsExactV P ok (RExact.exitRecs P (D6T P taint counted L α sinks roots)) :=
  fun _ _ _ hr hg =>
    let h := D6T_edgeOK hmw (Exact.filtValid_ok hv) hbo hr
    ⟨h.1, h.2 hg⟩

#print axioms recs_of_D6T_valid

/-- The exit edges of run 1 (`D6T`) are exact records (`FiltUp` form, `RExact.RecsExact`). -/
theorem recs_of_D6T (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) :
    RExact.RecsExact P (RExact.exitRecs P (D6T P taint counted L α sinks roots)) :=
  fun _ _ _ hr hg _ _ hd => edge_exact6T hmw hup hr hg hd

#print axioms recs_of_D6T

/-- The general form: the exit edges of run 1 are exact records for every validity `ok` with
    `FiltOK` and `BackOK`. -/
theorem recs_of_D6T_gen {ok : Loc → Prop} (hmw : Exact.MarkWF P) (hfo : Exact.FiltOK P ok)
    (hbo : Exact.BackOK P ok) :
    RExact.RecsExactV P ok (RExact.exitRecs P (D6T P taint counted L α sinks roots)) :=
  fun _ _ _ hr hg =>
    let h := D6T_edgeOK hmw hfo hbo hr
    ⟨h.1, h.2 hg⟩

#print axioms recs_of_D6T_gen

/-- Under a non-`*` premise every final fact of `D6T` is non-`*` (`Confirmed.D_NS` for `D6T`). -/
theorem D6T_NS {o : Obj} (h : D6T P taint counted L α sinks roots o) : Confirmed.NS o := by
  induction h with
  | root => trivial
  | @start M i _ _ => exact fun hi => Confirmed.startFact_nonstar hi
  | @step M i n f n' s f' _ _ hf ih =>
    intro hi
    obtain ⟨f0, hf0, hle⟩ := transferT_mem hf
    rw [← hle.fact]
    exact Confirmed.transfer_nonstar (ih hi) hf0
  | reqStmt => trivial
  | pass _ _ _ ih => exact ih
  | added => trivial
  | initA => trivial
  | @ret M i n f n' c e1 a j g r e2 r' _ _ _ ha _ _ _ hr _ hr' ihF _ _ =>
    intro hi
    have h1 := Confirmed.applyEdge_nonstar (ihF hi) ha
    obtain ⟨x, hx, rfl⟩ := Invariant.applySummary_shape hr
    have h2 := Confirmed.applyEdge_nonstar h1 hx
    have h3 : (AFact.norm ⟨x.fact, x.demand || g.demand⟩).fact.kind.isStar = false := by
      rw [Confirmed.norm_nonstar (x := ⟨x.fact, x.demand || g.demand⟩) h2]
      exact h2
    exact Confirmed.limitF_nonstar (Confirmed.applyEdge_nonstar h3 hr')
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial
  | @clean M i n f n' cl f' _ _ hf' ih => exact fun hi => Confirmed.cleanRes_nonstar (ih hi) hf'
  | reqClean => trivial
  | filt _ _ _ ih => exact ih

#print axioms D6T_NS

/-- A supported premise of run 1 (`Sup6T`) is exact with a concrete mark, and its one location is
    entry-reachable (`Confirmed.sup_entry` for `D6T`; S7, `FiltUp`). -/
theorem sup_entry6T (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) {M : MethodId} {i : PFact}
    (h : Sup6T P taint counted L α sinks roots M i) :
    ∃ t, i.kind = .exact ∧ i.mark = .conc t ∧
      Confirmed.EntryReach P roots M ⟨i.base, i.path, t⟩ := by
  induction h with
  | root hM => exact ⟨zeroMark, rfl, rfl, Or.inl ⟨hM, rfl⟩⟩
  | @call M i n f n' c e a j _ hD hfd hE he ha had _ hj ih =>
    obtain ⟨t0, hik, him, hent⟩ := ih
    obtain ⟨t, hak, ham, rfl⟩ := Confirmed.sup_step hj
    have hden := Confirmed.den_exact_exact (a := a.fact) him hak (by rw [ham]; trivial)
    rw [ham] at hden
    obtain ⟨hp1, hc1⟩ := Exact.markEdge_ok (hmw.toC _ _ _ _ hE e he) (Exact.applyEdge_mark ha).1
    obtain ⟨l, hd1, hd2⟩ := Exact.applyEdge_exact hp1 hc1 hfd ha had hden
    have hR := Confirmed.entry_reach P roots hent (edge_exact6T hmw hup hD hfd hd1)
    exact ⟨t, hak, ham, Or.inr ⟨M, n, l, n', c, e, hR, hE, rfl, he, hd2⟩⟩

#print axioms sup_entry6T

/-- The valid form of `sup_entry6T` (S7, S13): the one location of a supported premise is
    entry-reachable if it is valid. -/
theorem sup_entry6T_valid {ok : Loc → Prop} (hmw : Exact.MarkWF P) (hv : Exact.FiltValid P ok)
    (hbo : Exact.BackOK P ok) {M : MethodId} {i : PFact}
    (h : Sup6T P taint counted L α sinks roots M i) :
    ∃ t, i.kind = .exact ∧ i.mark = .conc t ∧
      (ok ⟨i.base, i.path, t⟩ → Confirmed.EntryReach P roots M ⟨i.base, i.path, t⟩) := by
  induction h with
  | root hM => exact ⟨zeroMark, rfl, rfl, fun _ => Or.inl ⟨hM, rfl⟩⟩
  | @call M i n f n' c e a j _ hD hfd hE he ha had _ hj ih =>
    obtain ⟨t0, hik, him, hent⟩ := ih
    obtain ⟨t, hak, ham, rfl⟩ := Confirmed.sup_step hj
    refine ⟨t, hak, ham, fun hokj => ?_⟩
    have hden := Confirmed.den_exact_exact (a := a.fact) him hak (by rw [ham]; trivial)
    rw [ham] at hden
    obtain ⟨hp1, hc1⟩ := Exact.markEdge_ok (hmw.toC _ _ _ _ hE e he) (Exact.applyEdge_mark ha).1
    obtain ⟨l, hd1, hd2⟩ := Exact.applyEdge_exact hp1 hc1 hfd ha had hden
    have hokl : ok l := hbo.toC _ _ _ _ hE e he _ _ hd2 hokj
    obtain ⟨hfl, hok0⟩ := edge_exact_valid6T hmw hv hbo hD hfd hd1 hokl
    exact Or.inr ⟨M, n, l, n', c, e, Confirmed.entry_reach P roots (hent hok0) hfl, hE, rfl, he, hd2⟩

#print axioms sup_entry6T_valid

/-- CONFIRMATION IN RUN 1 (`FiltUp` form). A vulnerability confirmed on a NORMAL sink edge of
    `D6T` under a supported premise (`ConfirmedT6`; the sink fact can be a normal `.any`, an
    `[any-taint]`) is a real concrete vulnerability: a reachable location in the sink pattern. The
    sink location is a common location of the sink fact and the sink pattern; for a normal `.any`
    sink fact every such location is the end of a pair from the premise location. Hypotheses: S7,
    `FiltUp` (those of `Confirmed.confirmed_real`). -/
theorem confirmed_real6T (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P)
    {M : MethodId} {n : Node} {s : PFact}
    (h : ConfirmedT6 P taint counted L α sinks roots M n s) :
    ∃ l, Reach P roots M n l ∧ s.covers l := by
  obtain ⟨i, f, hD, hS, hfd, _, hch⟩ := h
  obtain ⟨t0, hik, him, hent⟩ := sup_entry6T hmw hup hS
  have hns : f.fact.kind.isStar = false := D6T_NS hD (by rw [hik]; rfl)
  obtain ⟨l, hden, hcov⟩ := sink_den hik him hns hch
  exact ⟨l, Confirmed.entry_reach P roots hent (edge_exact6T hmw hup hD hfd hden), hcov⟩

#print axioms confirmed_real6T

/-- CONFIRMATION IN RUN 1 FOR VALID LOCATIONS (S7, S13): a confirmed vulnerability of `D6T` has a
    location in the sink pattern that is reached if it is valid. -/
theorem confirmed_real_valid6T_of {ok : Loc → Prop} (hmw : Exact.MarkWF P)
    (hv : Exact.FiltValid P ok) (hbo : Exact.BackOK P ok) {M : MethodId} {n : Node} {s : PFact}
    (h : ConfirmedT6 P taint counted L α sinks roots M n s) :
    ∃ l, s.covers l ∧ (ok l → Reach P roots M n l) := by
  obtain ⟨i, f, hD, hS, hfd, _, hch⟩ := h
  obtain ⟨t0, hik, him, hent⟩ := sup_entry6T_valid hmw hv hbo hS
  have hns : f.fact.kind.isStar = false := D6T_NS hD (by rw [hik]; rfl)
  obtain ⟨l, hden, hcov⟩ := sink_den hik him hns hch
  refine ⟨l, hcov, fun hok => ?_⟩
  obtain ⟨hfl, hok0⟩ := edge_exact_valid6T hmw hv hbo hD hfd hden hok
  exact Confirmed.entry_reach P roots (hent hok0) hfl

#print axioms confirmed_real_valid6T_of

/-- CONFIRMATION IN RUN 1 FOR A REAL PROGRAM (S7, S13, every location of the sink pattern
    valid): a confirmed vulnerability of `D6T` is a real concrete vulnerability. -/
theorem confirmed_real_valid6T {ok : Loc → Prop} (hmw : Exact.MarkWF P)
    (hv : Exact.FiltValid P ok) (hbo : Exact.BackOK P ok) {M : MethodId} {n : Node} {s : PFact}
    (hok : ∀ l, s.covers l → ok l)
    (h : ConfirmedT6 P taint counted L α sinks roots M n s) :
    ∃ l, Reach P roots M n l ∧ s.covers l := by
  obtain ⟨l, hcov, hR⟩ := confirmed_real_valid6T_of hmw hv hbo h
  exact ⟨l, hR (hok l hcov), hcov⟩

#print axioms confirmed_real_valid6T

end Run1

/-! ## 2. The restricted run with must-premises (`DRT`): the invariants -/

/-- The record hypothesis on the marks (NEW): a normal must record has a concrete conclusion
    mark. `EndExact` reads the locations `coversF` of the conclusion, which exist only for a
    concrete mark, so a must record with an abstract conclusion mark is END-EXACT for every program
    (`CexRecConc.cex_rec_conc`). (The premise mark is then concrete too: the mark part of
    `RecsExactT` gives an abstract conclusion mark to an abstract premise mark, `conc_of_absImp`.)
    The exit edges of a concrete run have it (`recsConc_of_DRT`); run 1 gives no must record. -/
def RecsConcT (recs : MethodId → PFact × Bool × AFact → Prop) : Prop :=
  ∀ m j g, recs m (j, true, g) → g.demand = false → ∃ t, g.fact.mark = .conc t

/-- A mark that gives an abstract conclusion mark when it is abstract, with a concrete conclusion
    mark, is concrete. -/
theorem conc_of_absImp {jm gm : MarkA} (h : Exact.absB jm = true → Exact.absB gm = true)
    (hg : ∃ t, gm = .conc t) : ∃ t, jm = .conc t := by
  cases jm with
  | conc t => exact ⟨t, rfl⟩
  | star => exact absurd (h rfl) (by rw [absB_conc hg]; exact Bool.false_ne_true)
  | starEx x => exact absurd (h rfl) (by rw [absB_conc hg]; exact Bool.false_ne_true)

/-- The mark part of W2 on the edges of `DRT`: a `*` conclusion has an abstract mark. -/
def LegalT : TObj → Prop
  | .edge _ _ _ _ f => Invariant.LegalM f
  | _ => True

section RunT
variable {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
  {demand : MethodId → DemandEdge → Prop}
  {emit : PFact → PFact → Option PFact}
  {sat : PFact → PFact → Bool}
  {restrict : PFact → AFact → DemandEdge → Option AFact}
  {recs : MethodId → PFact × Bool × AFact → Prop}
  {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId}

/-- CONCRETENESS of a restricted run with must-premises (`RExact.DR_concrete` for `DRT`): with a
    mark-copying emission, every premise, conclusion and added fact has a concrete mark, and the
    run has no request. -/
theorem DRT_concrete (hem : EmitCopiesMark emit) {o : TObj}
    (h : DRT P taint counted L demand emit sat restrict recs sinks roots o) : ConcObjT o := by
  induction h with
  | root => exact ⟨zeroMark, rfl⟩
  | @start M j mj _ ih =>
    obtain ⟨t, ht⟩ := ih
    exact ⟨⟨t, ht⟩, t, by rw [startT_mark, ht]⟩
  | @step M i mi n f n' s f' _ _ hf ih =>
    obtain ⟨hi, t, ht⟩ := ih
    obtain ⟨f0, hf0, hle⟩ := transferT_mem hf
    obtain ⟨t', ht'⟩ := transfer_mark_conc ht hf0
    exact ⟨hi, t', by rw [← hle.fact]; exact ht'⟩
  | @reqStmt M i mi n f n' s t _ _ ht ih =>
    obtain ⟨_, t0, h0⟩ := ih
    rw [transferT_reqs, transfer_reqs_of_conc h0] at ht
    cases ht
  | pass _ _ _ ih => exact ih
  | @added M i mi n f n' c e a _ _ _ ha ih =>
    obtain ⟨_, t, ht⟩ := ih
    exact applyEdge_mark_conc ht ha
  | @initR m a am d j mj _ _ hj ih =>
    obtain ⟨t, ht⟩ := ih
    exact ⟨t, by rw [hem _ _ _ (emitTWith_some hj).1, ht]⟩
  | @ret M i mi n f n' c e1 a j mj g d g' r e2 r' _ _ _ ha _ _ _ _ _ hr _ hr' ihF _ _ =>
    obtain ⟨hi, t, ht⟩ := ihF
    obtain ⟨t1, h1⟩ := applyEdge_mark_conc ht ha
    obtain ⟨t2, h2⟩ := applySummary_mark_conc h1 hr
    obtain ⟨t3, h3⟩ := applyEdge_mark_conc h2 hr'
    exact ⟨hi, t3, by rw [limitF_mark, h3]⟩
  | @retRec M i mi n f n' c e1 a j mj g r e2 r' _ _ _ ha _ _ hr _ hr' ihF =>
    obtain ⟨hi, t, ht⟩ := ihF
    obtain ⟨t1, h1⟩ := applyEdge_mark_conc ht ha
    obtain ⟨t2, h2⟩ := applySummary_mark_conc h1 hr
    obtain ⟨t3, h3⟩ := applyEdge_mark_conc h2 hr'
    exact ⟨hi, t3, by rw [limitF_mark, recLayer_fact, h3]⟩
  | @reqSink M i mi n f s t _ _ hc ih =>
    obtain ⟨⟨t0, h0⟩, _⟩ := ih
    exact check_request_star hc t0 h0
  | answer _ _ _ _ ihR _ => exact ihR.elim
  | reqUp _ _ _ _ _ _ _ _ ihR _ => exact ihR.elim
  | vuln => trivial
  | @clean M i mi n f n' cl f' _ _ hf ih =>
    obtain ⟨hi, t, ht⟩ := ih
    exact ⟨hi, cleanRes_mark_conc ht hf⟩
  | @reqClean M i mi n f n' cl t _ _ ht ih =>
    obtain ⟨_, t0, h0⟩ := ih
    exact (cleanRes_reqs_abstract ht).1 t0 h0
  | filt _ _ _ ih => exact ih

#print axioms DRT_concrete

/-- The edges of a restricted run are concrete (premise and conclusion). -/
theorem DRT_edge_conc (hem : EmitCopiesMark emit) {M : MethodId} {i : PFact} {mi : Bool}
    {n : Node} {f : AFact}
    (h : DRT P taint counted L demand emit sat restrict recs sinks roots (.edge M i mi n f)) :
    (∃ t, i.mark = .conc t) ∧ ∃ t, f.fact.mark = .conc t :=
  DRT_concrete hem h

/-- The initial facts of a restricted run are concrete. -/
theorem DRT_init_conc (hem : EmitCopiesMark emit) {M : MethodId} {j : PFact} {mj : Bool}
    (h : DRT P taint counted L demand emit sat restrict recs sinks roots (.init M j mj)) :
    ∃ t, j.mark = .conc t :=
  DRT_concrete hem h

/-- A must-premise of `DRT` has the `.any` tail (decision 6: the premise `[any-taint]`). No
    hypothesis: the emission gives the must flag only to an `.any` premise. -/
theorem DRT_mustAny {o : TObj}
    (h : DRT P taint counted L demand emit sat restrict recs sinks roots o) : MustAnyT o := by
  induction h with
  | root => trivial
  | @start M j mj _ ih => cases mj <;> exact ih
  | @step M i mi _ _ _ _ _ _ _ _ ih => cases mi <;> exact ih
  | reqStmt => trivial
  | @pass M i mi _ _ _ _ _ _ _ ih => cases mi <;> exact ih
  | added => trivial
  | @initR m a am d j mj _ _ hj _ =>
    cases mj with
    | false => trivial
    | true => exact emitTWith_must_any hj
  | @ret M i mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihF _ _ =>
    cases mi <;> exact ihF
  | @retRec M i mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihF => cases mi <;> exact ihF
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial
  | @clean M i mi _ _ _ _ _ _ _ _ ih => cases mi <;> exact ih
  | reqClean => trivial
  | @filt M i mi _ _ _ _ _ _ _ _ ih => cases mi <;> exact ih

#print axioms DRT_mustAny

/-- W2 on `DRT` (the mark part): a conclusion with the `*` tail has an abstract mark. No
    hypothesis. -/
theorem DRT_legal {o : TObj}
    (h : DRT P taint counted L demand emit sat restrict recs sinks roots o) : LegalT o := by
  induction h with
  | root => trivial
  | @start M j mj hJ _ =>
    cases mj with
    | false => exact fun e hk => (Invariant.startFact_legal hk).1
    | true =>
      intro e hk
      have hm : j.kind = .any := DRT_mustAny hJ
      have hk' : j.kind = .star e := hk
      rw [hm] at hk'
      cases hk'
  | @step M i mi n f n' s f' _ _ hf ih =>
    intro e hk
    obtain ⟨f0, hf0, hle⟩ := transferT_mem hf
    rw [← hle.fact] at hk ⊢
    rcases Invariant.transfer_mem hf0 with rfl | ⟨x, e', _, hx, rfl⟩
    · exact ih e hk
    · exact (Invariant.limitF_legal (fun e2 h2 => Invariant.applyEdge_legal hx h2) hk).1
  | reqStmt => trivial
  | pass _ _ _ ih => exact ih
  | added => trivial
  | initR => trivial
  | @ret M i mi n f n' c e1 a j mj g d g' r e2 r' _ _ _ _ _ _ _ _ _ _ _ hr' _ _ _ =>
    intro e hk
    exact (Invariant.limitF_legal (fun e2 h2 => Invariant.applyEdge_legal hr' h2) hk).1
  | @retRec M i mi n f n' c e1 a j mj g r e2 r' _ _ _ _ _ _ _ _ hr' _ =>
    intro e hk
    rw [limitF_recLayer_fact] at hk ⊢
    exact (Invariant.limitF_legal (fun e2 h2 => Invariant.applyEdge_legal hr' h2) hk).1
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial
  | clean _ _ hf ih => exact Invariant.cleanRes_LegalM ih hf
  | reqClean => trivial
  | filt _ _ _ ih => exact ih

#print axioms DRT_legal

/-- In a concrete run no conclusion has the `*` tail. -/
theorem DRT_nonstar (hem : EmitCopiesMark emit) {M : MethodId} {i : PFact} {mi : Bool}
    {n : Node} {f : AFact}
    (h : DRT P taint counted L demand emit sat restrict recs sinks roots (.edge M i mi n f)) :
    f.fact.kind.isStar = false := by
  cases hk : f.fact.kind with
  | star e =>
    obtain ⟨_, t, ht⟩ := DRT_edge_conc hem h
    have hl : Invariant.LegalM f := DRT_legal h
    exact absurd ht ((hl e hk).not_conc t)
  | any => rfl
  | exact => rfl

#print axioms DRT_nonstar

end RunT

/-! ## 3. The exactness of `DRT`

  The motive is `AnyTaint.EdgeOKT`: pair-exact for a normal edge of a non-must premise (as
  `RExact.EdgeOKR`), END-EXACT for a normal edge of a must-premise. The local lemmas read on
  LOCATIONS (`applyEdge_cov`, `transfer_cov`, `cleanRes_cov`) move END-EXACT through every step.
  At a summary application there are four cases (caller premise × callee premise):
    * pair caller, pair callee: `RExact.summary_ok`;
    * must caller, pair callee: the location of the result goes back through the bindings and
      the summary pairs to a location of the caller conclusion, which END-EXACT reaches;
    * pair or must caller, MUST callee: the callee summary is END-EXACT; the premise of the callee
      lies inside the added fact (`SatInside`), so the premise location that the callee reads is a
      location of the added fact. The added fact is uncorrelated (no `*` tail: it is concrete), so
      for a pair caller it is the end of a pair from the same start location (`den_swap`). -/

/-- END-EXACT in the pair form: the form that a summary application reads. Every pair of `den j g`
    to a valid end location has the end location reached from SOME valid premise location. -/
def EndExactD (P : Program) (ok : Loc → Prop) (m : MethodId) (j : PFact) (n : Node) (g : PFact) :
    Prop :=
  ∀ l1 l2, den j g l1 l2 → ok l2 → ∃ l0, j.covers l0 ∧ Flow P m l0 n l2 ∧ ok l0

/-- END-EXACT gives its pair form for a concrete conclusion. -/
theorem endD_of_end {P : Program} {ok : Loc → Prop} {m : MethodId} {j : PFact} {n : Node}
    {g : PFact} (hg : ∃ t, g.mark = .conc t) (h : EndExact P ok m j n g) :
    EndExactD P ok m j n g :=
  fun _ l2 hd hok => h l2 (den_coversF hd hg) hok

theorem limitF_demand_true {counted : Acc → Bool} {L : Nat} {f : AFact} (h : f.demand = true) :
    (limitF counted L f).demand = true := by
  unfold limitF
  cases cutPath counted L f.fact.path with
  | none => exact h
  | some p => rfl

/-- A demand-layer edge satisfies the motive (it says nothing about such an edge). -/
theorem edgeOKT_of_demand {P : Program} {ok : Loc → Prop} {M : MethodId} {i : PFact} {mi : Bool}
    {n : Node} {f : AFact} (h : f.demand = true) : EdgeOKT P ok (.edge M i mi n f) := by
  cases mi with
  | false => intro hd; rw [h] at hd; cases hd
  | true => intro hd; rw [h] at hd; cases hd

section RunT2
variable {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
  {demand : MethodId → DemandEdge → Prop}
  {emit : PFact → PFact → Option PFact}
  {sat : PFact → PFact → Bool}
  {restrict : PFact → AFact → DemandEdge → Option AFact}
  {recs : MethodId → PFact × Bool × AFact → Prop}
  {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId}

/-- A summary application with a PAIR-EXACT callee summary (a non-must premise): the result
    satisfies the motive for a pair caller (`RExact.summary_ok`) and for a must caller. -/
theorem summaryT_pair {ok : Loc → Prop} (hmw : Exact.MarkWF P) (hbo : Exact.BackOK P ok)
    {M : MethodId} {i j : PFact} {mi : Bool} {n n' : Node} {c : Call} {f a g r r' : AFact}
    {e1 e2 : MicroEdge}
    (hE : (M, n, Instr.call c, n') ∈ P.edges) (he1 : e1 ∈ c.toCallee)
    (ha : a ∈ (applyEdge f e1.1 e1.2).facts) (hsm : markSubB j.mark a.fact.mark = true)
    (hr : r ∈ (applySummary a j g).facts) (he2 : e2 ∈ c.fromCallee)
    (hr' : r' ∈ (applyEdge r e2.1 e2.2).facts) (hfc : ∃ t, f.fact.mark = .conc t)
    (ihD : EdgeOKT P ok (.edge M i mi n f))
    (ihG : RExact.EdgeOKR P ok (.edge c.callee j (P.exit c.callee) g)) :
    EdgeOKT P ok (.edge M i mi n' (limitF counted L r')) := by
  cases mi with
  | false => exact RExact.summary_ok hmw hbo hE he1 ha hsm hr he2 hr' ihD ihG
  | true =>
    intro hla
    have e := Exact.limitF_exact hla
    rw [e] at hla ⊢
    have hra := Exact.applyEdge_demand hr' hla
    obtain ⟨x, hx, rfl⟩ := Exact.applySummary_mem hr hra
    obtain ⟨hxa, hga⟩ := Exact.or_eq_false hra
    have haa := Exact.applyEdge_demand hx hxa
    have hfa := Exact.applyEdge_demand ha haa
    obtain ⟨ihD1, ihD2⟩ := ihD hfa
    obtain ⟨_, ihG2⟩ := ihG hga
    obtain ⟨tf, htf⟩ := hfc
    obtain ⟨ta, hta⟩ := applyEdge_mark_conc htf ha
    have hxc := applyEdge_mark_conc hta hx
    refine ⟨fun hi => absurd (ihD1 hi) (by rw [absB_conc ⟨tf, htf⟩]; exact Bool.false_ne_true),
      fun l hl hok => ?_⟩
    -- the binding back to the caller
    obtain ⟨hp3, hc3⟩ := Exact.markEdge_ok (hmw.fromC _ _ _ _ hE e2 he2)
      (Exact.applyEdge_mark hr').1
    obtain ⟨l2, hl2, hde2⟩ := applyEdge_cov hp3 hc3 hra hr' hla hxc hl
    have hok2 : ok l2 := hbo.fromC _ _ _ _ hE e2 he2 _ _ hde2 hok
    -- the summary edge: its pairs are real flows
    obtain ⟨l1', hl1', hdg⟩ := applyEdge_cov (Exact.premOK_of_sub hsm) (concOK_conc _ ⟨ta, hta⟩)
      haa hx hxa ⟨ta, hta⟩ hl2
    obtain ⟨hflG, hok1'⟩ := ihG2 l1' l2 hdg hok2
    -- the binding into the callee
    obtain ⟨hp1, hc1⟩ := Exact.markEdge_ok (hmw.toC _ _ _ _ hE e1 he1) (Exact.applyEdge_mark ha).1
    obtain ⟨l1, hl1, hde1⟩ := applyEdge_cov hp1 hc1 hfa ha haa ⟨tf, htf⟩ hl1'
    have hok1 : ok l1 := hbo.toC _ _ _ _ hE e1 he1 _ _ hde1 hok1'
    -- the caller conclusion is END-EXACT
    obtain ⟨l0, hi0, hflD, hok0⟩ := ihD2 l1 hl1 hok1
    exact ⟨l0, hi0, Flow.call hflD hE he1 hde1 hflG he2 hde2, hok0⟩

#print axioms summaryT_pair

/-- A summary application with an END-EXACT callee summary (a MUST callee premise `j`) to an added
    fact `a` that covers `j` (`hin`, the satisfaction `satI`): every location of `j` is a location
    of `a` (`coversF_of_inside`). The result satisfies the motive for a pair caller (every location
    of the uncorrelated `a` is the end of a pair from the start location, `den_swap`) and for a
    must caller (END-EXACT goes back through the bindings). -/
theorem summaryT_end {ok : Loc → Prop} (hmw : Exact.MarkWF P) (hbo : Exact.BackOK P ok)
    {M : MethodId} {i j : PFact} {mi : Bool} {n n' : Node} {c : Call} {f a g r r' : AFact}
    {e1 e2 : MicroEdge}
    (hE : (M, n, Instr.call c, n') ∈ P.edges) (he1 : e1 ∈ c.toCallee)
    (ha : a ∈ (applyEdge f e1.1 e1.2).facts) (hsm : markSubB j.mark a.fact.mark = true)
    (hin : coversB ⟨a.fact.base, a.fact.path, a.fact.kind, .star⟩ j = true)
    (hjc : g.demand = false → ∃ t, j.mark = .conc t)
    (hr : r ∈ (applySummary a j g).facts) (he2 : e2 ∈ c.fromCallee)
    (hr' : r' ∈ (applyEdge r e2.1 e2.2).facts) (hfc : ∃ t, f.fact.mark = .conc t)
    (ihD : EdgeOKT P ok (.edge M i mi n f))
    (hG : g.demand = false → EndExactD P ok c.callee j (P.exit c.callee) g.fact) :
    EdgeOKT P ok (.edge M i mi n' (limitF counted L r')) := by
  obtain ⟨tf, htf⟩ := hfc
  have hac : ∃ t, a.fact.mark = .conc t := applyEdge_mark_conc htf ha
  have hans : a.fact.kind.isStar = false := applyEdge_conc_nonstar ha hac
  cases mi with
  | false =>
    intro hla
    have e := Exact.limitF_exact hla
    rw [e] at hla ⊢
    have hra := Exact.applyEdge_demand hr' hla
    obtain ⟨x, hx, rfl⟩ := Exact.applySummary_mem hr hra
    obtain ⟨hxa, hga⟩ := Exact.or_eq_false hra
    have haa := Exact.applyEdge_demand hx hxa
    have hfa := Exact.applyEdge_demand ha haa
    obtain ⟨ihD1, ihD2⟩ := ihD hfa
    refine ⟨fun hi => absurd (ihD1 hi) (by rw [absB_conc ⟨tf, htf⟩]; exact Bool.false_ne_true),
      fun l0 l hd hok => ?_⟩
    -- the binding back to the caller
    obtain ⟨hp3, hc3⟩ := Exact.markEdge_ok (hmw.fromC _ _ _ _ hE e2 he2)
      (Exact.applyEdge_mark hr').1
    obtain ⟨l2, hd2, hde2⟩ := Exact.applyEdge_exact hp3 hc3 hra hr' hla hd
    have hok2 : ok l2 := hbo.fromC _ _ _ _ hE e2 he2 _ _ hde2 hok
    -- the summary edge: END-EXACT gives a premise location of the callee
    obtain ⟨l1', hd1', hdg⟩ := Exact.applyEdge_exact (Exact.premOK_of_sub hsm)
      (concOK_conc _ hac) haa hx hxa hd2
    obtain ⟨l1'', hj1, hflG, hok1''⟩ := hG hga l1' l2 hdg hok2
    -- that location is a location of the added fact, the end of a pair from `l0`
    have hd1'' := den_swap hans hd1' (coversF_of_inside hin hsm (hjc hga) hj1)
    -- the binding into the callee
    obtain ⟨hp1, hc1⟩ := Exact.markEdge_ok (hmw.toC _ _ _ _ hE e1 he1) (Exact.applyEdge_mark ha).1
    obtain ⟨l1, hd1, hde1⟩ := Exact.applyEdge_exact hp1 hc1 hfa ha haa hd1''
    have hok1 : ok l1 := hbo.toC _ _ _ _ hE e1 he1 _ _ hde1 hok1''
    obtain ⟨hflD, hok0⟩ := ihD2 l0 l1 hd1 hok1
    exact ⟨Flow.call hflD hE he1 hde1 hflG he2 hde2, hok0⟩
  | true =>
    intro hla
    have e := Exact.limitF_exact hla
    rw [e] at hla ⊢
    have hra := Exact.applyEdge_demand hr' hla
    obtain ⟨x, hx, rfl⟩ := Exact.applySummary_mem hr hra
    obtain ⟨hxa, hga⟩ := Exact.or_eq_false hra
    have haa := Exact.applyEdge_demand hx hxa
    have hfa := Exact.applyEdge_demand ha haa
    obtain ⟨ihD1, ihD2⟩ := ihD hfa
    obtain ⟨ta, hta⟩ := hac
    have hxc := applyEdge_mark_conc hta hx
    refine ⟨fun hi => absurd (ihD1 hi) (by rw [absB_conc ⟨tf, htf⟩]; exact Bool.false_ne_true),
      fun l hl hok => ?_⟩
    -- the binding back to the caller
    obtain ⟨hp3, hc3⟩ := Exact.markEdge_ok (hmw.fromC _ _ _ _ hE e2 he2)
      (Exact.applyEdge_mark hr').1
    obtain ⟨l2, hl2, hde2⟩ := applyEdge_cov hp3 hc3 hra hr' hla hxc hl
    have hok2 : ok l2 := hbo.fromC _ _ _ _ hE e2 he2 _ _ hde2 hok
    -- the summary edge: END-EXACT gives a premise location of the callee
    obtain ⟨l1', _, hdg⟩ := applyEdge_cov (Exact.premOK_of_sub hsm) (concOK_conc _ ⟨ta, hta⟩)
      haa hx hxa ⟨ta, hta⟩ hl2
    obtain ⟨l1'', hj1, hflG, hok1''⟩ := hG hga l1' l2 hdg hok2
    -- that location is a location of the added fact
    have hca := coversF_of_inside hin hsm (hjc hga) hj1
    -- the binding into the callee
    obtain ⟨hp1, hc1⟩ := Exact.markEdge_ok (hmw.toC _ _ _ _ hE e1 he1) (Exact.applyEdge_mark ha).1
    obtain ⟨l1, hl1, hde1⟩ := applyEdge_cov hp1 hc1 hfa ha haa ⟨tf, htf⟩ hca
    have hok1 : ok l1 := hbo.toC _ _ _ _ hE e1 he1 _ _ hde1 hok1''
    -- the caller conclusion is END-EXACT
    obtain ⟨l0, hi0, hflD, hok0⟩ := ihD2 l1 hl1 hok1
    exact ⟨l0, hi0, Flow.call hflD hE he1 hde1 hflG he2 hde2, hok0⟩

#print axioms summaryT_end

/-- THE MOTIVE ON EVERY OBJECT OF `DRT`. A normal edge of a non-must premise is pair-exact; a
    normal edge of a must-premise is END-EXACT (every valid location of its conclusion is reached
    from some valid location of its premise); in both cases an abstract premise mark gives an
    abstract conclusion mark. Hypotheses: S7 (`MarkWF`), `FiltOK`/`BackOK` for the validity `ok`
    (S13), `SatInside sat` (the satisfaction reads the premise INSIDE the added fact; `satI`), the
    restriction only removes pairs (`RestrictSub`), the emission copies the mark (`EmitCopiesMark`:
    the run is concrete), and the records: exact (`RecsExactT`) with concrete must records
    (`RecsConcT`). A must record that applies by `applicable` only gives a demand result
    (`recLayer`), so it needs no exactness. -/
theorem DRT_edgeOK {ok : Loc → Prop} (hmw : Exact.MarkWF P) (hfo : Exact.FiltOK P ok)
    (hbo : Exact.BackOK P ok) (hin : SatInside sat) (hsub : RestrictSub restrict)
    (hem : EmitCopiesMark emit) (hrecs : RecsExactT P ok recs) (hrc : RecsConcT recs) {o : TObj}
    (h : DRT P taint counted L demand emit sat restrict recs sinks roots o) : EdgeOKT P ok o := by
  induction h with
  | root => trivial
  | @start M j mj _ _ =>
    cases mj with
    | false =>
      intro ha
      refine ⟨fun hi => by rw [startT_mark]; exact hi, fun l0 l hd hok => ?_⟩
      have e := Exact.startFact_exact ha hd
      subst e
      exact ⟨Flow.start M l, hok⟩
    | true =>
      -- the start of a must-premise: every end location is its own premise location
      intro _
      exact ⟨fun hi => hi, fun l hl hok => ⟨l, ((coversF_iff j l).mp hl).1, Flow.start M l, hok⟩⟩
  | @step M i mi n f n' s f' hF hE hf ih =>
    obtain ⟨f0, hf0, hle⟩ := transferT_mem hf
    cases mi with
    | false =>
      intro ha
      have e := hle.eq_of_normal ha
      subst e
      have hfa := Exact.transfer_demand hf0 ha
      obtain ⟨ih1, ih2⟩ := ih hfa
      refine ⟨fun hi => Exact.transfer_abs (hmw.stmt _ _ _ _ hE) (ih1 hi) hf0,
        fun l0 l hd hok => ?_⟩
      obtain ⟨l1, hd1, hs⟩ := Exact.transfer_exact (hmw.stmt _ _ _ _ hE) hfa hf0 ha hd
      have hok1 : ok l1 := by
        rcases hs with ⟨-, rfl⟩ | ⟨e, he, hde⟩
        · exact hok
        · exact hbo.stmt _ _ _ _ hE e he _ _ hde hok
      obtain ⟨hfl, hok0⟩ := ih2 l0 l1 hd1 hok1
      exact ⟨Flow.step hfl hE hs, hok0⟩
    | true =>
      intro ha
      have e := hle.eq_of_normal ha
      subst e
      have hfa := Exact.transfer_demand hf0 ha
      obtain ⟨ih1, ih2⟩ := ih hfa
      refine ⟨fun hi => Exact.transfer_abs (hmw.stmt _ _ _ _ hE) (ih1 hi) hf0,
        fun l hl hok => ?_⟩
      obtain ⟨l1, hl1, hs⟩ := transfer_cov (hmw.stmt _ _ _ _ hE) hfa hf0 ha
        (DRT_edge_conc hem hF).2 hl
      have hok1 : ok l1 := by
        rcases hs with ⟨-, rfl⟩ | ⟨e, he, hde⟩
        · exact hok
        · exact hbo.stmt _ _ _ _ hE e he _ _ hde hok
      obtain ⟨l0, hi0, hfl, hok0⟩ := ih2 l1 hl1 hok1
      exact ⟨l0, hi0, Flow.step hfl hE hs, hok0⟩
  | reqStmt => trivial
  | @pass M i mi n f n' c _ hE hm ih =>
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
  | @ret M i mi n f n' c e1 a j mj g d g' r e2 r' hF hE he1 ha _ hG _ hres hs hr he2 hr' ihF _
      ihG =>
    have hfc := (DRT_edge_conc hem hF).2
    obtain ⟨hgd, hgsub⟩ := hsub j g d g' hres
    obtain ⟨hcov, hsm⟩ := hin j a.fact hs
    cases mj with
    | false =>
      -- a non-must callee premise: as `RExact.DR_edgeOK`
      have ihG' : RExact.EdgeOKR P ok (.edge c.callee j (P.exit c.callee) g') := by
        intro hg'
        obtain ⟨h1, h2⟩ := ihG (hgd.symm.trans hg')
        exact ⟨fun hJ' => RExact.abs_of_sub hJ' (h1 hJ') hgsub,
          fun l1 l2 hd hok => h2 l1 l2 (hgsub l1 l2 hd) hok⟩
      exact summaryT_pair hmw hbo hE he1 ha hsm hr he2 hr' hfc ihF ihG'
    | true =>
      -- a must callee premise inside the added fact: END-EXACT of the callee summary
      obtain ⟨hjc, hgc⟩ := DRT_edge_conc hem hG
      have hG' : g'.demand = false → EndExactD P ok c.callee j (P.exit c.callee) g'.fact := by
        intro hg'
        have hEnd := endD_of_end hgc (ihG (hgd.symm.trans hg')).2
        exact fun l1 l2 hd hok => hEnd l1 l2 (hgsub l1 l2 hd) hok
      exact summaryT_end hmw hbo hE he1 ha hsm hcov (fun _ => hjc) hr he2 hr' hfc ihF hG'
  | @retRec M i mi n f n' c e1 a j mj g r e2 r' hF hE he1 ha hrec hs hr he2 hr' ihF =>
    have hfc := (DRT_edge_conc hem hF).2
    have hG := hrecs c.callee j mj g hrec
    cases mj with
    | false =>
      -- a non-must record, by `sat` or by `applicable`: pair-exact (`RecsExactT`)
      have hsm : markSubB j.mark a.fact.mark = true :=
        RExact.recApp_markSub (fun j' a' h' => (hin j' a' h').2) hs
      rw [show recLayer false (sat j a.fact) r' = r' from recLayer_keep (Or.inl rfl) r']
      exact summaryT_pair hmw hbo hE he1 ha hsm hr he2 hr' hfc ihF hG
    | true =>
      cases hsj : sat j a.fact with
      | false =>
        -- a must record by `applicable` only: the result is in the demand layer
        exact edgeOKT_of_demand (limitF_demand_true rfl)
      | true =>
        -- a must record by `sat`: the premise lies inside the added fact
        obtain ⟨hcov, hsm⟩ := hin j a.fact hsj
        -- the record conclusion is concrete (`RecsConcT`), so its premise is (`RecsExactT`)
        have hjc : g.demand = false → ∃ t, j.mark = .conc t := fun hg =>
          conc_of_absImp (hG hg).1 (hrc c.callee j g hrec hg)
        rw [show recLayer true true r' = r' from recLayer_keep (Or.inr rfl) r']
        exact summaryT_end hmw hbo hE he1 ha hsm hcov hjc hr he2 hr' hfc ihF
          (fun hg => endD_of_end (hrc c.callee j g hrec hg) (hG hg).2)
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial
  | @clean M i mi n f n' cl f' hF hE hf ih =>
    cases mi with
    | false =>
      intro ha
      have hfa := Exact.cleanRes_demand hf ha
      obtain ⟨ih1, ih2⟩ := ih hfa
      refine ⟨fun hi => Exact.cleanRes_abs (ih1 hi) hf, fun l0 l hd hok => ?_⟩
      obtain ⟨hd1, hcl⟩ := Exact.cleanRes_exact hf ha hd
      obtain ⟨hfl, hok0⟩ := ih2 l0 l hd1 hok
      exact ⟨Flow.clean hfl hE hcl, hok0⟩
    | true =>
      intro ha
      have hfa := Exact.cleanRes_demand hf ha
      obtain ⟨ih1, ih2⟩ := ih hfa
      refine ⟨fun hi => Exact.cleanRes_abs (ih1 hi) hf, fun l hl hok => ?_⟩
      obtain ⟨hl1, hcl⟩ := cleanRes_cov hf ha (DRT_edge_conc hem hF).2 hl
      obtain ⟨l0, hi0, hfl, hok0⟩ := ih2 l hl1 hok
      exact ⟨l0, hi0, Flow.clean hfl hE hcl, hok0⟩
  | reqClean => trivial
  | @filt M i mi n f n' b may _ hE hp ih =>
    cases mi with
    | false =>
      intro ha
      obtain ⟨ih1, ih2⟩ := ih ha
      refine ⟨ih1, fun l0 l hd hok => ?_⟩
      obtain ⟨hfl, hok0⟩ := ih2 l0 l hd hok
      refine ⟨Flow.filt hfl hE ?_, hok0⟩
      intro hb
      obtain ⟨-, hlb, -, -, -, σ, τ, -, hlp, -, -⟩ := hd
      exact hfo _ _ _ _ _ hE f.fact.path τ l (hp (hlb.symm.trans hb)) hlp hok hb
    | true =>
      intro ha
      obtain ⟨ih1, ih2⟩ := ih ha
      refine ⟨ih1, fun l hl hok => ?_⟩
      obtain ⟨l0, hi0, hfl, hok0⟩ := ih2 l hl hok
      refine ⟨l0, hi0, Flow.filt hfl hE ?_, hok0⟩
      intro hb
      obtain ⟨hlb, ⟨τ, hlp, _⟩, _⟩ := hl
      exact hfo _ _ _ _ _ hE f.fact.path τ l (hp (hlb.symm.trans hb)) hlp hok hb

#print axioms DRT_edgeOK

end RunT2

/-! ## 4. Exactness, records, support and confirmation of `DRT` -/

/-- The union of two exact record sets with must flags is exact. -/
theorem recsT_union {P : Program} {ok : Loc → Prop} {recs1 recs2 : MethodId → PFact × Bool × AFact → Prop}
    (h1 : RecsExactT P ok recs1) (h2 : RecsExactT P ok recs2) :
    RecsExactT P ok (fun m x => recs1 m x ∨ recs2 m x) :=
  fun m j mj g hr => hr.elim (h1 m j mj g) (h2 m j mj g)

#print axioms recsT_union

/-- A subset of an exact record set is exact. -/
theorem recsT_mono {P : Program} {ok : Loc → Prop} {recs recs' : MethodId → PFact × Bool × AFact → Prop}
    (hsub : ∀ m x, recs' m x → recs m x) (h : RecsExactT P ok recs) : RecsExactT P ok recs' :=
  fun m j mj g hr => h m j mj g (hsub m _ hr)

#print axioms recsT_mono

/-- The empty record set is exact. -/
theorem recsT_empty (P : Program) (ok : Loc → Prop) : RecsExactT P ok (fun _ _ => False) :=
  fun _ _ _ _ hr => hr.elim

theorem recsConcT_union {recs1 recs2 : MethodId → PFact × Bool × AFact → Prop}
    (h1 : RecsConcT recs1) (h2 : RecsConcT recs2) : RecsConcT (fun m x => recs1 m x ∨ recs2 m x) :=
  fun m j g hr => hr.elim (h1 m j g) (h2 m j g)

theorem recsConcT_mono {recs recs' : MethodId → PFact × Bool × AFact → Prop}
    (hsub : ∀ m x, recs' m x → recs m x) (h : RecsConcT recs) : RecsConcT recs' :=
  fun m j g hr => h m j g (hsub m _ hr)

theorem recsConcT_empty : RecsConcT (fun _ _ => False) := fun _ _ _ hr => hr.elim

/-- The records of run 1 (lifted, no must flag) have no must record. -/
theorem recsConcT_lift (recs : MethodId → PFact × AFact → Prop) : RecsConcT (liftRecs recs) :=
  fun _ _ _ hr _ => by have h1 : true = false := hr.1; cases h1

#print axioms recsConcT_union
#print axioms recsConcT_lift

/-- The one location of an exact concrete premise, read as a conclusion location. -/
theorem coversF_self {i : PFact} {t0 : Mark} (him : i.mark = .conc t0) :
    coversF i ⟨i.base, i.path, t0⟩ :=
  ⟨rfl, ⟨[], (List.append_nil _).symm, Exact.tailI_nil _⟩, t0, him, rfl⟩

/-- `den_exact_prem` for a location of a concrete fact. -/
theorem den_exact_prem_cov {i a : PFact} {t0 : Mark} {l : Loc} (hik : i.kind = .exact)
    (him : i.mark = .conc t0) (hns : a.kind.isStar = false) (hl : coversF a l) :
    den i a ⟨i.base, i.path, t0⟩ l := by
  obtain ⟨hb, hp, ta, hta, hlm⟩ := hl
  exact den_exact_prem hik him hns (by rw [hta]; trivial) hb hp (by rw [hta]; exact hlm)

/-- The location `zeroLoc` is the only location of the zero fact. -/
theorem coversF_zero {l : Loc} (h : coversF zeroFact l) : l = zeroLoc := by
  obtain ⟨hb, ⟨τ, hp, hτ⟩, t, ht, hm⟩ := h
  have hτ' : τ = [] := hτ
  have ht' : zeroMark = t := MarkA.conc.inj ht
  exact Exact.loc_ext hb (by rw [hp, hτ']; rfl) (hm.trans ht'.symm)

section RunT3
variable {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
  {demand : MethodId → DemandEdge → Prop}
  {emit : PFact → PFact → Option PFact}
  {sat : PFact → PFact → Bool}
  {restrict : PFact → AFact → DemandEdge → Option AFact}
  {recs : MethodId → PFact × Bool × AFact → Prop}
  {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId}

/-- The two exactness forms of a normal edge of `DRT`, for a validity `ok` with `FiltOK` and
    `BackOK`. -/
theorem edge_exactT_gen {ok : Loc → Prop} (hmw : Exact.MarkWF P) (hfo : Exact.FiltOK P ok)
    (hbo : Exact.BackOK P ok) (hin : SatInside sat) (hsub : RestrictSub restrict)
    (hem : EmitCopiesMark emit) (hrecs : RecsExactT P ok recs) (hrc : RecsConcT recs)
    {M : MethodId} {i : PFact} {mi : Bool} {n : Node} {f : AFact}
    (h : DRT P taint counted L demand emit sat restrict recs sinks roots (.edge M i mi n f))
    (ha : f.demand = false) :
    (mi = false → ∀ l0 l, den i f.fact l0 l → ok l → Flow P M l0 n l ∧ ok l0) ∧
    (mi = true → EndExact P ok M i n f.fact) := by
  have hm := DRT_edgeOK hmw hfo hbo hin hsub hem hrecs hrc h
  cases mi with
  | false => exact ⟨fun _ => (hm ha).2, fun h' => (by cases h')⟩
  | true => exact ⟨fun h' => (by cases h'), fun _ => (hm ha).2⟩

#print axioms edge_exactT_gen

/-- THE EXACTNESS THEOREM OF A RESTRICTED RUN WITH MUST-PREMISES (`FiltUp` form). A normal edge
    `(i, mi) → f` of `DRT`:
    * of a non-must premise (`mi = false`) is PAIR-EXACT: every pair of `den i f` is a concrete flow;
    * of a must-premise (`mi = true`, the premise `[any-taint]`) is END-EXACT: every location of
      the conclusion is reached by a concrete flow from SOME location of the premise.
    Hypotheses: S7, `FiltUp`, `SatInside sat`, `RestrictSub restrict`, `EmitCopiesMark emit`, the
    records exact (`RecsExactT`) with concrete must records (`RecsConcT`). -/
theorem edge_exactT (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hin : SatInside sat)
    (hsub : RestrictSub restrict) (hem : EmitCopiesMark emit)
    (hrecs : RecsExactT P (fun _ => True) recs) (hrc : RecsConcT recs)
    {M : MethodId} {i : PFact} {mi : Bool} {n : Node} {f : AFact}
    (h : DRT P taint counted L demand emit sat restrict recs sinks roots (.edge M i mi n f))
    (ha : f.demand = false) :
    (mi = false → ∀ l0 l, den i f.fact l0 l → Flow P M l0 n l) ∧
    (mi = true → ∀ l, coversF f.fact l → ∃ l0, i.covers l0 ∧ Flow P M l0 n l) := by
  obtain ⟨h1, h2⟩ := edge_exactT_gen hmw (Exact.filtUp_ok hup) (Exact.backOK_true P) hin hsub hem
    hrecs hrc h ha
  refine ⟨fun hm l0 l hd => (h1 hm l0 l hd trivial).1, fun hm l hl => ?_⟩
  obtain ⟨l0, hi0, hfl, _⟩ := h2 hm l hl trivial
  exact ⟨l0, hi0, hfl⟩

#print axioms edge_exactT

/-- THE EXACTNESS THEOREM FOR VALID LOCATIONS (prefix-closed type filters: S13 `FiltValid`,
    `BackOK`; the other hypotheses of `edge_exactT`, the records exact for `ok`). A normal edge of
    a non-must premise: every pair to a valid end location is a concrete flow from a valid start
    location. A normal edge of a must-premise: every valid location of the conclusion is reached
    from some valid location of the premise. -/
theorem edge_exactT_valid {ok : Loc → Prop} (hmw : Exact.MarkWF P) (hv : Exact.FiltValid P ok)
    (hbo : Exact.BackOK P ok) (hin : SatInside sat) (hsub : RestrictSub restrict)
    (hem : EmitCopiesMark emit) (hrecs : RecsExactT P ok recs) (hrc : RecsConcT recs)
    {M : MethodId} {i : PFact} {mi : Bool} {n : Node} {f : AFact}
    (h : DRT P taint counted L demand emit sat restrict recs sinks roots (.edge M i mi n f))
    (ha : f.demand = false) :
    (mi = false → ∀ l0 l, den i f.fact l0 l → ok l → Flow P M l0 n l ∧ ok l0) ∧
    (mi = true → EndExact P ok M i n f.fact) :=
  edge_exactT_gen hmw (Exact.filtValid_ok hv) hbo hin hsub hem hrecs hrc h ha

#print axioms edge_exactT_valid

/-- The exit edges of a `DRT` run are exact records again (general validity). -/
theorem recs_of_DRT_gen {ok : Loc → Prop} (hmw : Exact.MarkWF P) (hfo : Exact.FiltOK P ok)
    (hbo : Exact.BackOK P ok) (hin : SatInside sat) (hsub : RestrictSub restrict)
    (hem : EmitCopiesMark emit) (hrecs : RecsExactT P ok recs) (hrc : RecsConcT recs) :
    RecsExactT P ok (exitRecsT P (DRT P taint counted L demand emit sat restrict recs sinks roots)) :=
  fun _ _ _ _ hr => DRT_edgeOK hmw hfo hbo hin hsub hem hrecs hrc hr

#print axioms recs_of_DRT_gen

/-- THE RECORDS OF A RESTRICTED RUN (`FiltUp` form): the exit edges of a `DRT` run, with their
    must flags, are exact records (`RecsExactT`): pair-exact for a non-must premise, END-EXACT for
    a must-premise. So a later run can reuse them. -/
theorem recs_of_DRT (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hin : SatInside sat)
    (hsub : RestrictSub restrict) (hem : EmitCopiesMark emit)
    (hrecs : RecsExactT P (fun _ => True) recs) (hrc : RecsConcT recs) :
    RecsExactT P (fun _ => True)
      (exitRecsT P (DRT P taint counted L demand emit sat restrict recs sinks roots)) :=
  recs_of_DRT_gen hmw (Exact.filtUp_ok hup) (Exact.backOK_true P) hin hsub hem hrecs hrc

#print axioms recs_of_DRT

/-- The records of a restricted run for valid locations (S13). -/
theorem recs_of_DRT_valid {ok : Loc → Prop} (hmw : Exact.MarkWF P) (hv : Exact.FiltValid P ok)
    (hbo : Exact.BackOK P ok) (hin : SatInside sat) (hsub : RestrictSub restrict)
    (hem : EmitCopiesMark emit) (hrecs : RecsExactT P ok recs) (hrc : RecsConcT recs) :
    RecsExactT P ok (exitRecsT P (DRT P taint counted L demand emit sat restrict recs sinks roots)) :=
  recs_of_DRT_gen hmw (Exact.filtValid_ok hv) hbo hin hsub hem hrecs hrc

#print axioms recs_of_DRT_valid

/-- The exit edges of a concrete run satisfy the new record hypothesis `RecsConcT`. -/
theorem recsConc_of_DRT (hem : EmitCopiesMark emit) :
    RecsConcT (exitRecsT P (DRT P taint counted L demand emit sat restrict recs sinks roots)) :=
  fun _ _ _ hr _ => (DRT_edge_conc hem hr).2

#print axioms recsConc_of_DRT

/-- THE SUPPORT (general validity). Every valid location of a supported premise (`SupT`) is
    entry-reachable: for a must-premise ALL its locations (it lies inside a normal `[any-taint]`
    added fact with its mark), for an exact premise its one location. A supported premise is
    concrete, and a non-must one is exact. -/
theorem sup_entryT_gen {ok : Loc → Prop} (hmw : Exact.MarkWF P) (hfo : Exact.FiltOK P ok)
    (hbo : Exact.BackOK P ok) (hin : SatInside sat) (hsub : RestrictSub restrict)
    (hem : EmitCopiesMark emit) (hrecs : RecsExactT P ok recs) (hrc : RecsConcT recs)
    {M : MethodId} {i : PFact} {mi : Bool}
    (h : SupT P taint counted L demand emit sat restrict recs sinks roots M i mi) :
    (∃ t, i.mark = .conc t) ∧ (mi = false → i.kind = .exact) ∧
      ∀ l, coversF i l → ok l → Confirmed.EntryReach P roots M l := by
  induction h with
  | root hM => exact ⟨⟨zeroMark, rfl⟩, fun _ => rfl, fun l hl _ => Or.inl ⟨hM, coversF_zero hl⟩⟩
  | @call M i mi n f n' c e a j mj _ hD hfd hE he ha had _ hlink ih =>
    obtain ⟨⟨t0, him⟩, hik, hent⟩ := ih
    -- the link: `j` is concrete, and every location of `j` is a location of `a`
    have hlinkF : (∃ t, j.mark = .conc t) ∧ (mj = false → j.kind = .exact) ∧
        ∀ l, coversF j l → coversF a.fact l := by
      rcases hlink with ⟨rfl, hz⟩ | ⟨hak, hac, rfl, _⟩ | ⟨_, hac, hjm, hsat, hk⟩
      · exact ⟨⟨zeroMark, rfl⟩, fun _ => rfl, fun l hl => by rw [hz]; exact hl⟩
      · exact ⟨hac, fun _ => hak, fun l hl => hl⟩
      · have hjc : ∃ t, j.mark = .conc t := by rw [hjm]; exact hac
        refine ⟨hjc, fun hm => ?_, fun l hl => ?_⟩
        · rcases hk with ⟨hk1, _⟩ | ⟨_, hm'⟩
          · exact hk1
          · rw [hm] at hm'; cases hm'
        · exact coversF_of_inside (RExact.bool_and_left hsat) (RExact.bool_and_right hsat) hjc
            ((coversF_iff j l).mp hl).1
    obtain ⟨hjc, hjk, hja⟩ := hlinkF
    refine ⟨hjc, hjk, fun l hl hok => ?_⟩
    have hla := hja l hl
    have hac : ∃ t, a.fact.mark = .conc t := by
      obtain ⟨_, _, t, ht, _⟩ := hla
      exact ⟨t, ht⟩
    have hm := DRT_edgeOK hmw hfo hbo hin hsub hem hrecs hrc hD
    obtain ⟨hp1, hc1⟩ := Exact.markEdge_ok (hmw.toC _ _ _ _ hE e he) (Exact.applyEdge_mark ha).1
    have hfc := (DRT_edge_conc hem hD).2
    cases mi with
    | false =>
      -- a pair caller with an exact premise: the pair from its one location
      have hd0 := den_exact_prem_cov (hik rfl) him (applyEdge_conc_nonstar ha hac) hla
      obtain ⟨l', hd1, hd2⟩ := Exact.applyEdge_exact hp1 hc1 hfd ha had hd0
      have hokl' : ok l' := hbo.toC _ _ _ _ hE e he _ _ hd2 hok
      obtain ⟨hfl, hok0⟩ := (hm hfd).2 _ _ hd1 hokl'
      have hR := Confirmed.entry_reach P roots (hent _ (coversF_self him) hok0) hfl
      exact Or.inr ⟨M, n, l', n', c, e, hR, hE, rfl, he, hd2⟩
    | true =>
      -- a must caller: END-EXACT of the caller edge
      obtain ⟨l', hl', hd2⟩ := applyEdge_cov hp1 hc1 hfd ha had hfc hla
      have hokl' : ok l' := hbo.toC _ _ _ _ hE e he _ _ hd2 hok
      obtain ⟨l0, hi0, hfl, hok0⟩ := (hm hfd).2 l' hl' hokl'
      have hR := Confirmed.entry_reach P roots (hent l0 (coversF_of_covers ⟨t0, him⟩ hi0) hok0) hfl
      exact Or.inr ⟨M, n, l', n', c, e, hR, hE, rfl, he, hd2⟩

#print axioms sup_entryT_gen

/-- THE SUPPORT (`FiltUp` form): every location of a supported premise is entry-reachable (all
    locations of a must-premise, the one location of an exact premise). -/
theorem sup_entryT (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hin : SatInside sat)
    (hsub : RestrictSub restrict) (hem : EmitCopiesMark emit)
    (hrecs : RecsExactT P (fun _ => True) recs) (hrc : RecsConcT recs)
    {M : MethodId} {i : PFact} {mi : Bool}
    (h : SupT P taint counted L demand emit sat restrict recs sinks roots M i mi) :
    (∃ t, i.mark = .conc t) ∧ (mi = false → i.kind = .exact) ∧
      ∀ l, coversF i l → Confirmed.EntryReach P roots M l := by
  obtain ⟨h1, h2, h3⟩ := sup_entryT_gen hmw (Exact.filtUp_ok hup) (Exact.backOK_true P) hin hsub
    hem hrecs hrc h
  exact ⟨h1, h2, fun l hl => h3 l hl trivial⟩

#print axioms sup_entryT

/-- THE SUPPORT FOR VALID LOCATIONS (S13): every valid location of a supported premise is
    entry-reachable. -/
theorem sup_entryT_valid {ok : Loc → Prop} (hmw : Exact.MarkWF P) (hv : Exact.FiltValid P ok)
    (hbo : Exact.BackOK P ok) (hin : SatInside sat) (hsub : RestrictSub restrict)
    (hem : EmitCopiesMark emit) (hrecs : RecsExactT P ok recs) (hrc : RecsConcT recs)
    {M : MethodId} {i : PFact} {mi : Bool}
    (h : SupT P taint counted L demand emit sat restrict recs sinks roots M i mi) :
    (∃ t, i.mark = .conc t) ∧ (mi = false → i.kind = .exact) ∧
      ∀ l, coversF i l → ok l → Confirmed.EntryReach P roots M l :=
  sup_entryT_gen hmw (Exact.filtValid_ok hv) hbo hin hsub hem hrecs hrc h

#print axioms sup_entryT_valid

/-- The confirmation, general validity: a confirmed vulnerability of `DRT` has a location in the
    sink pattern that is reached if it is valid. -/
theorem confirmed_realT_gen {ok : Loc → Prop} (hmw : Exact.MarkWF P) (hfo : Exact.FiltOK P ok)
    (hbo : Exact.BackOK P ok) (hin : SatInside sat) (hsub : RestrictSub restrict)
    (hem : EmitCopiesMark emit) (hrecs : RecsExactT P ok recs) (hrc : RecsConcT recs)
    {M : MethodId} {n : Node} {s : PFact}
    (h : ConfirmedT P taint counted L demand emit sat restrict recs sinks roots M n s) :
    ∃ l, s.covers l ∧ (ok l → Reach P roots M n l) := by
  obtain ⟨i, mi, f, hD, hS, hfd, _, hch⟩ := h
  obtain ⟨⟨t0, him⟩, hik, hent⟩ := sup_entryT_gen hmw hfo hbo hin hsub hem hrecs hrc hS
  have hm := DRT_edgeOK hmw hfo hbo hin hsub hem hrecs hrc hD
  obtain ⟨l, hlf, hls⟩ := sink_cov him (DRT_edge_conc hem hD).2 hch
  refine ⟨l, hls, fun hok => ?_⟩
  cases mi with
  | false =>
    -- an exact supported premise: the pair from its one location to the sink location
    have hd := den_exact_prem_cov (hik rfl) him (DRT_nonstar hem hD) hlf
    obtain ⟨hfl, hok0⟩ := (hm hfd).2 _ _ hd hok
    exact Confirmed.entry_reach P roots (hent _ (coversF_self him) hok0) hfl
  | true =>
    -- a supported must-premise: END-EXACT, and every location of the premise is entry-reachable
    obtain ⟨l0, hi0, hfl, hok0⟩ := (hm hfd).2 l hlf hok
    exact Confirmed.entry_reach P roots (hent l0 (coversF_of_covers ⟨t0, him⟩ hi0) hok0) hfl

#print axioms confirmed_realT_gen

/-- THE CONFIRMATION THEOREM OF A RESTRICTED RUN WITH MUST-PREMISES (`FiltUp` form). A vulnerability
    confirmed on a NORMAL sink edge of `DRT` (the sink fact can be `[any-taint]`) under a supported
    premise (`ConfirmedT`) is a real concrete vulnerability: a reachable location in the sink
    pattern. Hypotheses: those of `RExact.confirmed_realM_gen` (S7, `FiltUp`, the satisfaction
    reads the marks, `RestrictSub`, exact records), with `SatInside sat` in place of `SatMark sat`,
    plus `EmitCopiesMark emit` and the records with must flags (`RecsExactT`, `RecsConcT`). -/
theorem confirmed_realT (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hin : SatInside sat)
    (hsub : RestrictSub restrict) (hem : EmitCopiesMark emit)
    (hrecs : RecsExactT P (fun _ => True) recs) (hrc : RecsConcT recs)
    {M : MethodId} {n : Node} {s : PFact}
    (h : ConfirmedT P taint counted L demand emit sat restrict recs sinks roots M n s) :
    ∃ l, Reach P roots M n l ∧ s.covers l := by
  obtain ⟨l, hls, hR⟩ := confirmed_realT_gen hmw (Exact.filtUp_ok hup) (Exact.backOK_true P) hin
    hsub hem hrecs hrc h
  exact ⟨l, hR trivial, hls⟩

#print axioms confirmed_realT

/-- THE CONFIRMATION FOR VALID LOCATIONS (S13): a confirmed vulnerability of `DRT` has a location
    in the sink pattern that is reached if it is valid. -/
theorem confirmed_realT_valid_of {ok : Loc → Prop} (hmw : Exact.MarkWF P)
    (hv : Exact.FiltValid P ok) (hbo : Exact.BackOK P ok) (hin : SatInside sat)
    (hsub : RestrictSub restrict) (hem : EmitCopiesMark emit) (hrecs : RecsExactT P ok recs)
    (hrc : RecsConcT recs) {M : MethodId} {n : Node} {s : PFact}
    (h : ConfirmedT P taint counted L demand emit sat restrict recs sinks roots M n s) :
    ∃ l, s.covers l ∧ (ok l → Reach P roots M n l) :=
  confirmed_realT_gen hmw (Exact.filtValid_ok hv) hbo hin hsub hem hrecs hrc h

#print axioms confirmed_realT_valid_of

/-- THE CONFIRMATION FOR A REAL PROGRAM (S13, every location of the sink pattern valid): a
    confirmed vulnerability of `DRT` is a real concrete vulnerability. -/
theorem confirmed_realT_valid {ok : Loc → Prop} (hmw : Exact.MarkWF P)
    (hv : Exact.FiltValid P ok) (hbo : Exact.BackOK P ok) (hin : SatInside sat)
    (hsub : RestrictSub restrict) (hem : EmitCopiesMark emit) (hrecs : RecsExactT P ok recs)
    (hrc : RecsConcT recs) {M : MethodId} {n : Node} {s : PFact} (hok : ∀ l, s.covers l → ok l)
    (h : ConfirmedT P taint counted L demand emit sat restrict recs sinks roots M n s) :
    ∃ l, Reach P roots M n l ∧ s.covers l := by
  obtain ⟨l, hls, hR⟩ := confirmed_realT_valid_of hmw hv hbo hin hsub hem hrecs hrc h
  exact ⟨l, hR (hok l hls), hls⟩

#print axioms confirmed_realT_valid

end RunT3

/-- The spec instance of the rules: `emitM` copies the mark, `satI` reads the premise inside the
    fact, `restrictU` only removes pairs. -/
theorem spec_rules : EmitCopiesMark emitM ∧ SatInside satI ∧ RestrictSub restrictU :=
  ⟨RExact.emitM_copies, satI_inside, RExact.restrictU_sub⟩

#print axioms spec_rules

/-! ## 5. The run sequence: the records stay exact

  The forward runs of the iteration are run 1 (`D6T`, no must-premise) and the restricted runs
  (`DRT`). The run `k + 1` reads the records `recs k`. Each record of `recs k` is an exit edge of
  run 1 (lifted with the flag `false`, `liftRecs`) or of an earlier restricted run (with its must
  flag). By induction over the runs every record set is exact (`RecsExactT`) and its must records
  are concrete (`RecsConcT`): the record hypotheses of §3, §4 are discharged for the whole
  iteration. (`BExact.recsSeq_exact` for `D` and `DR`.) -/

/-- The restricted run `k + 1` of the sequence: `DRT` with the field limit `Ls k`, the demand
    `dem k` and the records `recs k`. -/
def runT (P : Program) (taint : TaintEdges) (counted : Acc → Bool) (Ls : Nat → Nat)
    (dem : Nat → MethodId → DemandEdge → Prop) (emit : PFact → PFact → Option PFact)
    (sat : PFact → PFact → Bool) (restrict : PFact → AFact → DemandEdge → Option AFact)
    (recs : Nat → MethodId → PFact × Bool × AFact → Prop)
    (sinks : List (MethodId × Node × PFact)) (roots : List MethodId) (k : Nat) : TObj → Prop :=
  DRT P taint counted (Ls k) (dem k) emit sat restrict (recs k) sinks roots

/-- The records `recs k` of the restricted run `k + 1` are exit edges of run 1 (`R0`, lifted) or of
    an earlier restricted run `R k'` (`k' < k`). Any subset is allowed (all exit edges, the
    complete ones, the union over the runs). -/
def RecsFromRunsT (P : Program) (R0 : Obj → Prop) (R : Nat → TObj → Prop)
    (recs : Nat → MethodId → PFact × Bool × AFact → Prop) : Prop :=
  ∀ k m x, recs k m x →
    liftRecs (RExact.exitRecs P R0) m x ∨ ∃ k', k' < k ∧ exitRecsT P (R k') m x

section Seq
variable {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L0 : Nat}
  {α : MethodId → PFact → PFact} {Ls : Nat → Nat}
  {dem : Nat → MethodId → DemandEdge → Prop}
  {emit : PFact → PFact → Option PFact}
  {sat : PFact → PFact → Bool}
  {restrict : PFact → AFact → DemandEdge → Option AFact}
  {recs : Nat → MethodId → PFact × Bool × AFact → Prop}
  {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId}

/-- RECORD EXACTNESS OVER THE RUN SEQUENCE (general validity). If the records of every restricted
    run are exit edges of run 1 or of earlier restricted runs, every record set of the sequence is
    exact with concrete must records. Hypotheses: those of `DRT_edgeOK` without the record
    hypotheses. -/
theorem recsSeq_exactT_gen {ok : Loc → Prop} (hmw : Exact.MarkWF P) (hfo : Exact.FiltOK P ok)
    (hbo : Exact.BackOK P ok) (hin : SatInside sat) (hsub : RestrictSub restrict)
    (hem : EmitCopiesMark emit)
    (hfrom : RecsFromRunsT P (D6T P taint counted L0 α sinks roots)
      (runT P taint counted Ls dem emit sat restrict recs sinks roots) recs) :
    ∀ k, RecsExactT P ok (recs k) ∧ RecsConcT (recs k) := by
  have h0 : RecsExactT P ok (liftRecs (RExact.exitRecs P (D6T P taint counted L0 α sinks roots))) :=
    liftRecs_exactT (recs_of_D6T_gen hmw hfo hbo)
  have key : ∀ k j, j ≤ k → RecsExactT P ok (recs j) ∧ RecsConcT (recs j) := by
    intro k
    induction k with
    | zero =>
      intro j hj
      refine ⟨fun m jj mj g hr => ?_, fun m jj g hr => ?_⟩
      · rcases hfrom j m (jj, mj, g) hr with hl | ⟨k', hk', _⟩
        · exact h0 m jj mj g hl
        · exact absurd hk' (by omega)
      · rcases hfrom j m (jj, true, g) hr with hl | ⟨k', hk', _⟩
        · have h1 : true = false := hl.1
          exact absurd h1 Bool.noConfusion
        · exact absurd hk' (by omega)
    | succ k ih =>
      intro j hj
      refine ⟨fun m jj mj g hr => ?_, fun m jj g hr => ?_⟩
      · rcases hfrom j m (jj, mj, g) hr with hl | ⟨k', hk', hx⟩
        · exact h0 m jj mj g hl
        · obtain ⟨hE', hC'⟩ := ih k' (by omega)
          exact recs_of_DRT_gen hmw hfo hbo hin hsub hem hE' hC' m jj mj g hx
      · rcases hfrom j m (jj, true, g) hr with hl | ⟨k', _, hx⟩
        · have h1 : true = false := hl.1
          exact absurd h1 Bool.noConfusion
        · exact recsConc_of_DRT hem m jj g hx
  exact fun k => key k k (Nat.le_refl k)

#print axioms recsSeq_exactT_gen

/-- RECORD EXACTNESS OVER THE RUN SEQUENCE (`FiltUp` form). -/
theorem recsSeq_exactT (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hin : SatInside sat)
    (hsub : RestrictSub restrict) (hem : EmitCopiesMark emit)
    (hfrom : RecsFromRunsT P (D6T P taint counted L0 α sinks roots)
      (runT P taint counted Ls dem emit sat restrict recs sinks roots) recs) :
    ∀ k, RecsExactT P (fun _ => True) (recs k) ∧ RecsConcT (recs k) :=
  recsSeq_exactT_gen hmw (Exact.filtUp_ok hup) (Exact.backOK_true P) hin hsub hem hfrom

#print axioms recsSeq_exactT

/-- RECORD EXACTNESS OVER THE RUN SEQUENCE for valid locations (S13). -/
theorem recsSeq_exactT_valid {ok : Loc → Prop} (hmw : Exact.MarkWF P) (hv : Exact.FiltValid P ok)
    (hbo : Exact.BackOK P ok) (hin : SatInside sat) (hsub : RestrictSub restrict)
    (hem : EmitCopiesMark emit)
    (hfrom : RecsFromRunsT P (D6T P taint counted L0 α sinks roots)
      (runT P taint counted Ls dem emit sat restrict recs sinks roots) recs) :
    ∀ k, RecsExactT P ok (recs k) ∧ RecsConcT (recs k) :=
  recsSeq_exactT_gen hmw (Exact.filtValid_ok hv) hbo hin hsub hem hfrom

#print axioms recsSeq_exactT_valid

/-- EVERY CONFIRMED VULNERABILITY OF EVERY RESTRICTED RUN OF THE SEQUENCE IS REAL (`FiltUp` form);
    no record hypothesis remains. -/
theorem seq_confirmed_realT (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hin : SatInside sat)
    (hsub : RestrictSub restrict) (hem : EmitCopiesMark emit)
    (hfrom : RecsFromRunsT P (D6T P taint counted L0 α sinks roots)
      (runT P taint counted Ls dem emit sat restrict recs sinks roots) recs)
    (k : Nat) {M : MethodId} {n : Node} {s : PFact}
    (h : ConfirmedT P taint counted (Ls k) (dem k) emit sat restrict (recs k) sinks roots M n s) :
    ∃ l, Reach P roots M n l ∧ s.covers l :=
  let hr := recsSeq_exactT hmw hup hin hsub hem hfrom k
  confirmed_realT hmw hup hin hsub hem hr.1 hr.2 h

#print axioms seq_confirmed_realT

/-- EVERY CONFIRMED VULNERABILITY OF EVERY RESTRICTED RUN OF THE SEQUENCE IS REAL, for a real
    program (S13, every location of the sink pattern valid); no record hypothesis remains. -/
theorem seq_confirmed_realT_valid {ok : Loc → Prop} (hmw : Exact.MarkWF P)
    (hv : Exact.FiltValid P ok) (hbo : Exact.BackOK P ok) (hin : SatInside sat)
    (hsub : RestrictSub restrict) (hem : EmitCopiesMark emit)
    (hfrom : RecsFromRunsT P (D6T P taint counted L0 α sinks roots)
      (runT P taint counted Ls dem emit sat restrict recs sinks roots) recs)
    (k : Nat) {M : MethodId} {n : Node} {s : PFact} (hok : ∀ l, s.covers l → ok l)
    (h : ConfirmedT P taint counted (Ls k) (dem k) emit sat restrict (recs k) sinks roots M n s) :
    ∃ l, Reach P roots M n l ∧ s.covers l :=
  let hr := recsSeq_exactT_valid hmw hv hbo hin hsub hem hfrom k
  confirmed_realT_valid hmw hv hbo hin hsub hem hr.1 hr.2 hok h

#print axioms seq_confirmed_realT_valid

end Seq

/-! ## 6. Counterexamples (necessity)

  One program for `CexApp`, `CexRecConc` and `CexRev` (accessors `f = 1`, `g = 2`; mark `5`):
  * method `0` (a root; bases `1 = dto`, `3 = x`): `dto.f = srcAny()` (the taint source
    `zero → (1, [f], [any], 5)`, its result is `[any-taint]`), then `x = get(dto)`;
  * method `1` (`get`; bases `1 = p`, `2 = ret`): `ret = p.g` (the micro edge
    `(1, [g], *) → (2, [], *)`).
  The must record of `get` is `(p, [], [any-taint], 5) → (ret, [], [any-taint], 5)`: if every
  location below `p` carries `5`, every location below `ret` does. It is END-EXACT, not pair-exact
  (`record_not_pair_exact`). In the caller only `dto.f…` carries `5`, so `dto.g`, and `x`, carry
  nothing: no flow reaches the node `2` of the caller (`no_flow_caller`). -/

namespace CexApp

def src : MicroEdge := (zeroFact, ⟨1, [1], .any, .conc 5⟩)
def s1 : Stmt := ⟨[zeroBase], [src]⟩
def bind : MicroEdge := (⟨1, [], .star (.set []), .star⟩, ⟨1, [], .star (.set []), .star⟩)
def back : MicroEdge := (⟨2, [], .star (.set []), .star⟩, ⟨3, [], .star (.set []), .star⟩)
def cc : Call := ⟨1, [1, 3], [bind], [back]⟩
def get : MicroEdge := (⟨1, [2], .star (.set []), .star⟩, ⟨2, [], .star (.set []), .star⟩)
def s2 : Stmt := ⟨[1], [get]⟩
def P : Program := ⟨fun m => if m = 0 then 0 else 10, fun m => if m = 0 then 2 else 11,
  [(0, 0, .stmt s1, 1), (0, 1, .call cc, 2), (1, 10, .stmt s2, 11)]⟩
/-- The source is the only taint edge (decision 3). -/
def taint : TaintEdges := fun e => decide (e = src)
def cnt : Acc → Bool := fun _ => true
def dem : MethodId → DemandEdge → Prop := fun _ _ => False

/-- The must-premise `(p, [], [any-taint], 5)` of `get` and its conclusion
    `(ret, [], [any-taint], 5)`. -/
def j : PFact := ⟨1, [], .any, .conc 5⟩
def g : AFact := ⟨⟨2, [], .any, .conc 5⟩, false⟩
/-- The persisted must record. -/
def recs : MethodId → PFact × Bool × AFact → Prop := fun m x => m = 1 ∧ x = (j, true, g)

/-- The added fact `(p, [f], [any-taint], 5)` (normal on the link), inside the premise `j`. -/
def a : AFact := ⟨⟨1, [1], .any, .conc 5⟩, false⟩
def r : AFact := ⟨⟨2, [], .any, .conc 5⟩, false⟩
def r' : AFact := ⟨⟨3, [], .any, .conc 5⟩, false⟩

abbrev R := DRT P taint cnt 3 dem emitM satI restrictU recs [] [0]

theorem mem_s1 : ((0 : MethodId), (0 : Node), Instr.stmt s1, (1 : Node)) ∈ P.edges :=
  List.Mem.head _
theorem mem_cc : ((0 : MethodId), (1 : Node), Instr.call cc, (2 : Node)) ∈ P.edges :=
  List.Mem.tail _ (List.Mem.head _)
theorem mem_s2 : ((1 : MethodId), (10 : Node), Instr.stmt s2, (11 : Node)) ∈ P.edges :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

theorem wf : P.WF where
  stmtTouched := by
    intro M n s n' hE e he
    cases hE with
    | head =>
      cases he with
      | head => rfl
      | tail _ h => cases h
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | head =>
          cases he with
          | head => rfl
          | tail _ h => cases h
        | tail _ h => cases h
  toStar := by
    intro M n c n' hE e he
    cases hE with
    | tail _ h =>
      cases h with
      | head =>
        cases he with
        | head => rfl
        | tail _ h => cases h
      | tail _ h =>
        cases h with
        | tail _ h => cases h
  fromStar := by
    intro M n c n' hE e he
    cases hE with
    | tail _ h =>
      cases h with
      | head =>
        cases he with
        | head => rfl
        | tail _ h => cases h
      | tail _ h =>
        cases h with
        | tail _ h => cases h
  filtPrefix := by
    intro M n b may n' hE
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h => cases h

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
      | tail _ h =>
        cases h with
        | head =>
          cases he with
          | head => rfl
          | tail _ h => cases h
        | tail _ h => cases h
  toC := by
    intro M n c n' hE e he
    cases hE with
    | tail _ h =>
      cases h with
      | head =>
        cases he with
        | head => rfl
        | tail _ h => cases h
      | tail _ h =>
        cases h with
        | tail _ h => cases h
  fromC := by
    intro M n c n' hE e he
    cases hE with
    | tail _ h =>
      cases h with
      | head =>
        cases he with
        | head => rfl
        | tail _ h => cases h
      | tail _ h =>
        cases h with
        | tail _ h => cases h

theorem filtUp : Exact.FiltUp P := by
  intro M n b may n' hE
  cases hE with
  | tail _ h =>
    cases h with
    | tail _ h =>
      cases h with
      | tail _ h => cases h

/-- The source is a taint edge with the `.any` target and concrete marks (`TaintConc`). -/
theorem taintConc : TaintConc P taint := by
  intro M n s n' hE e he ht
  cases hE with
  | head =>
    cases he with
    | head => exact ⟨rfl, ⟨5, rfl⟩, ⟨0, rfl⟩⟩
    | tail _ h => cases h
  | tail _ h =>
    cases h with
    | tail _ h =>
      cases h with
      | head =>
        cases he with
        | head => exact absurd ht (by decide)
        | tail _ h => cases h
      | tail _ h => cases h

/-- In `get`, a location below `p.f` reaches nothing at the exit: `ret = p.g` reads only `p.g…`. -/
theorem flow_callee : ∀ {M l1 n l}, Flow P M l1 n l → M = 1 → l1.base = 1 →
    (∃ τ, l1.path = 1 :: τ) → n = 10 ∧ l = l1 := by
  intro M l1 n l h
  induction h with
  | start M l0 => intro hM _ _; subst hM; exact ⟨rfl, rfl⟩
  | @step M l0 n l n' l' s _ hE hs ih =>
    intro hM hb hp
    obtain ⟨_, hl⟩ := ih hM hb hp
    cases hE with
    | head => exact absurd hM (by decide)
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | head =>
          exfalso
          obtain ⟨τ, hτ⟩ := hp
          rcases hs with ⟨hm, _⟩ | ⟨e, he, hde⟩
          · rw [hl, hb] at hm
            exact absurd hm (by decide)
          · cases he with
            | head =>
              obtain ⟨_, _, _, _, _, σ, _, hσ, _⟩ := hde
              rw [hl, hτ] at hσ
              have h2 : (1 : Nat) :: τ = 2 :: σ := hσ
              exact absurd (List.head_eq_of_cons_eq h2) (by decide)
            | tail _ h => cases h
        | tail _ h => cases h
  | pass _ hE _ _ =>
    intro hM
    cases hE with
    | tail _ h =>
      cases h with
      | head => exact absurd hM (by decide)
      | tail _ h =>
        cases h with
        | tail _ h => cases h
  | call _ hE _ _ _ _ _ _ _ =>
    intro hM
    cases hE with
    | tail _ h =>
      cases h with
      | head => exact absurd hM (by decide)
      | tail _ h =>
        cases h with
        | tail _ h => cases h
  | clean _ hE _ _ =>
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h => cases h
  | filt _ hE _ _ =>
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h => cases h

#print axioms flow_callee

/-- In the caller, from the zero location: the zero location at the node `0`, a location below
    `dto.f` at the node `1`, and nothing at the node `2`. -/
theorem flow_caller : ∀ {M l0 n l}, Flow P M l0 n l → M = 0 → l0 = zeroLoc →
    (n = 0 ∧ l = zeroLoc) ∨ (n = 1 ∧ l.base = 1 ∧ ∃ τ, l.path = 1 :: τ) := by
  intro M l0 n l h
  induction h with
  | start M l0 => intro hM hl; subst hM; exact Or.inl ⟨rfl, hl⟩
  | @step M l0 n l n' l' s _ hE hs ih =>
    intro hM hl0
    have ih' := ih hM hl0
    cases hE with
    | head =>
      rcases ih' with ⟨_, rfl⟩ | ⟨hn, _⟩
      · rcases hs with ⟨hm, _⟩ | ⟨e, he, hde⟩
        · exact absurd hm (by decide)
        · cases he with
          | head =>
            obtain ⟨_, hb, _, _, _, σ, τ, _, hp, _⟩ := hde
            exact Or.inr ⟨rfl, hb, τ, hp⟩
          | tail _ h => cases h
      · exact absurd hn (by decide)
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | head => exact absurd hM (by decide)
        | tail _ h => cases h
  | @pass M l0 n l n' c _ hE hm ih =>
    intro hM hl0
    have ih' := ih hM hl0
    cases hE with
    | tail _ h =>
      cases h with
      | head =>
        rcases ih' with ⟨hn, _⟩ | ⟨_, hb, _⟩
        · exact absurd hn (by decide)
        · rw [hb] at hm
          exact absurd hm (by decide)
      | tail _ h =>
        cases h with
        | tail _ h => cases h
  | @call M l0 n l n' c e1 e2 l1 l2 l3 _ hE he1 hd1 hfl2 _ _ ih1 _ =>
    intro hM hl0
    have ih' := ih1 hM hl0
    cases hE with
    | tail _ h =>
      cases h with
      | head =>
        rcases ih' with ⟨hn, _⟩ | ⟨_, _, τ, hp⟩
        · exact absurd hn (by decide)
        · cases he1 with
          | head =>
            obtain ⟨_, hb1, _, _, _, σ, τ', hσ, hτ', _, hF⟩ := hd1
            have e1' : l1.path = l.path := by rw [hτ', hσ, hF.1]; rfl
            exact absurd (flow_callee hfl2 rfl hb1 ⟨τ, e1'.trans hp⟩).1 (by decide)
          | tail _ h => cases h
      | tail _ h =>
        cases h with
        | tail _ h => cases h
  | clean _ hE _ _ =>
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h => cases h
  | filt _ hE _ _ =>
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h => cases h

#print axioms flow_caller

/-- No flow from the zero location reaches the node `2` of the caller (`x = get(dto)` reads
    `dto.g`, which carries nothing). -/
theorem no_flow_caller (l : Loc) : ¬ Flow P 0 zeroLoc 2 l := by
  intro h
  rcases flow_caller h rfl rfl with ⟨hn, _⟩ | ⟨hn, _⟩
  · exact absurd hn (by decide)
  · exact absurd hn (by decide)

/-- The must record is END-EXACT for the program (and its must records are concrete). -/
theorem recsExact : RecsExactT P (fun _ => True) recs := by
  intro m j' mj g' hr
  obtain ⟨rfl, hx⟩ := hr
  cases hx
  intro _
  refine ⟨fun h => absurd h (by decide), fun l hl _ => ?_⟩
  obtain ⟨hb, ⟨τ, hp, _⟩, t, ht, hm⟩ := hl
  have ht' : (5 : Nat) = t := MarkA.conc.inj ht
  refine ⟨⟨1, 2 :: τ, 5⟩, ⟨rfl, ⟨2 :: τ, rfl, trivial⟩, rfl⟩, ?_, trivial⟩
  have hd : den get.1 get.2 ⟨1, 2 :: τ, 5⟩ l :=
    ⟨rfl, hb, trivial, hm.trans ht'.symm, trivial, τ, τ, rfl, hp, Exact.setNil_admits τ,
      rfl, Exact.setNil_admits τ⟩
  exact Flow.step (Flow.start 1 _) mem_s2 (Or.inr ⟨get, List.Mem.head _, hd⟩)

#print axioms recsExact

theorem recsConc : RecsConcT recs := by
  intro m j' g' hr _
  obtain ⟨rfl, hx⟩ := hr
  cases hx
  exact ⟨5, rfl⟩

/-- The pair `(p.f, ret)` of the must record is not a concrete flow: the record is END-EXACT, but
    not pair-exact (so a must record read as a non-must record is false). -/
theorem record_not_pair_exact : ¬ RExact.EdgeOKR P (fun _ => True) (.edge 1 j (P.exit 1) g) := by
  intro h
  have hd : den j g.fact ⟨1, [1], 5⟩ ⟨2, [], 5⟩ :=
    ⟨rfl, rfl, rfl, rfl, trivial, [1], [], rfl, rfl, trivial, trivial⟩
  have hfl := ((h rfl).2 _ _ hd trivial).1
  exact absurd (flow_callee hfl rfl rfl ⟨[], rfl⟩).1 (by decide)

#print axioms record_not_pair_exact

/-- The caller edge before the call: the source result `(dto, [f], [any-taint], 5)`, normal. -/
theorem drt_a : R (.edge 0 zeroFact false 1 a) :=
  DRT.step (DRT.start (DRT.root (List.Mem.head _))) mem_s1 (by decide)

/-- The must record applies by `applicable` only; `DRT` demotes the result (`recLayer`). -/
theorem drt_rec : R (.edge 0 zeroFact false 2 (limitF cnt 3 (recLayer true (satI j a.fact) r'))) :=
  DRT.retRec (mj := true) drt_a mem_cc (List.Mem.head _)
    (by decide : a ∈ (applyEdge a bind.1 bind.2).facts) ⟨rfl, rfl⟩ (Or.inr (by decide))
    (by decide : r ∈ (applySummary a j g).facts) (List.Mem.head _)
    (by decide : r' ∈ (applyEdge r back.1 back.2).facts)

#print axioms drt_rec

/-- The normal result `(x, [], [any-taint], 5)` at the node `2` denotes a pair that is not a flow. -/
theorem not_edgeOK : ¬ EdgeOKT P (fun _ => True) (.edge 0 zeroFact false 2 (limitF cnt 3 r')) := by
  rw [show limitF cnt 3 r' = r' from by decide]
  intro h
  have hd : den zeroFact r'.fact zeroLoc ⟨3, [], 5⟩ :=
    ⟨rfl, rfl, rfl, rfl, trivial, [], [], rfl, rfl, rfl, trivial⟩
  exact no_flow_caller _ ((h rfl).2 _ _ hd trivial).1

/-- `CexApp`: THE DEMOTION OF A MUST RECORD APPLIED BY `applicable` IS NECESSARY. Every hypothesis
    of `DRT_edgeOK` holds (S7, `FiltUp`, the spec rules `emitM`, `satI`, `restrictU`, an END-EXACT
    concrete must record). The must record `(p, [], [any-taint], 5) → (ret, [], [any-taint], 5)` of
    `ret = p.g` applies to the added fact `(p, [f], [any-taint], 5)` by `applicable` only (the
    added fact lies inside the premise). `DRT` gives the result in the demand layer (`recLayer`).
    The same result in the normal layer, `(x, [], [any-taint], 5)`, would break the exactness: its
    location `x` with the mark `5` is reached by no flow from the caller premise (`p.g`, and so
    `x`, carries nothing). -/
theorem cex_app :
    P.WF ∧ Exact.MarkWF P ∧ Exact.FiltUp P ∧ TaintConc P taint ∧
    RecsExactT P (fun _ => True) recs ∧ RecsConcT recs ∧
    applicable j a.fact = true ∧ satI j a.fact = false ∧
    R (.edge 0 zeroFact false 2 (limitF cnt 3 (recLayer true (satI j a.fact) r'))) ∧
    (limitF cnt 3 (recLayer true (satI j a.fact) r')).demand = true ∧
    (limitF cnt 3 r').fact = (limitF cnt 3 (recLayer true (satI j a.fact) r')).fact ∧
    (limitF cnt 3 r').demand = false ∧
    den zeroFact (limitF cnt 3 r').fact zeroLoc ⟨3, [], 5⟩ ∧ ¬ Flow P 0 zeroLoc 2 ⟨3, [], 5⟩ ∧
    ¬ EdgeOKT P (fun _ => True) (.edge 0 zeroFact false 2 (limitF cnt 3 r')) :=
  ⟨wf, markWF, filtUp, taintConc, recsExact, recsConc, by decide, by decide, drt_rec, by decide,
    by decide, by decide, ⟨rfl, rfl, rfl, rfl, trivial, [], [], rfl, rfl, rfl, trivial⟩,
    no_flow_caller _, not_edgeOK⟩

#print axioms cex_app

end CexApp

namespace CexRecConc
open CexApp

/-- A must record with an ABSTRACT conclusion mark: `(dto, [f], [any-taint], 5) → (ret, [], $, *)`.
    Its premise is the added fact itself, so it applies by `satI`. -/
def j0 : PFact := ⟨1, [1], .any, .conc 5⟩
def g0 : AFact := ⟨⟨2, [], .exact, .star⟩, false⟩
def recs0 : MethodId → PFact × Bool × AFact → Prop := fun m x => m = 1 ∧ x = (j0, true, g0)
def r0 : AFact := ⟨⟨2, [], .exact, .conc 5⟩, false⟩
def r0' : AFact := ⟨⟨3, [], .exact, .conc 5⟩, false⟩
def res : AFact := limitF cnt 3 (recLayer true (satI j0 a.fact) r0')

/-- `EndExact` reads the locations `coversF`, which are empty for an abstract conclusion mark: the
    record is END-EXACT for every program. -/
theorem recsExact0 : RecsExactT P (fun _ => True) recs0 := by
  intro m j' mj g' hr
  obtain ⟨rfl, hx⟩ := hr
  cases hx
  intro _
  refine ⟨fun h => absurd h (by decide), fun l hl _ => ?_⟩
  obtain ⟨_, _, t, ht, _⟩ := hl
  cases ht

theorem not_recsConc0 : ¬ RecsConcT recs0 := by
  intro h
  obtain ⟨t, ht⟩ := h 1 j0 g0 ⟨rfl, rfl⟩ rfl
  cases ht

theorem drt_res : DRT P taint cnt 3 dem emitM satI restrictU recs0 [] [0] (.edge 0 zeroFact false 2 res) :=
  DRT.retRec (mj := true) (DRT.step (DRT.start (DRT.root (List.Mem.head _))) mem_s1 (by decide))
    mem_cc (List.Mem.head _) (by decide : a ∈ (applyEdge a bind.1 bind.2).facts) ⟨rfl, rfl⟩
    (Or.inl (by decide)) (by decide : r0 ∈ (applySummary a j0 g0).facts) (List.Mem.head _)
    (by decide : r0' ∈ (applyEdge r0 back.1 back.2).facts)

/-- `CexRecConc`: THE NEW RECORD HYPOTHESIS `RecsConcT` IS NECESSARY. Every other hypothesis of
    `DRT_edgeOK` holds; the must record `(dto, [f], [any-taint], 5) → (ret, [], $, *)` is END-EXACT
    (vacuously: an abstract conclusion mark has no location `coversF`), it applies by `satI`, and
    `DRT` derives the NORMAL edge `(x, [], $, 5)` at the node `2`, which no flow reaches. -/
theorem cex_rec_conc :
    Exact.MarkWF P ∧ Exact.FiltUp P ∧ RecsExactT P (fun _ => True) recs0 ∧ ¬ RecsConcT recs0 ∧
    DRT P taint cnt 3 dem emitM satI restrictU recs0 [] [0] (.edge 0 zeroFact false 2 res) ∧
    res.demand = false ∧ ¬ EdgeOKT P (fun _ => True) (.edge 0 zeroFact false 2 res) := by
  refine ⟨markWF, filtUp, recsExact0, not_recsConc0, drt_res, by decide, ?_⟩
  rw [show res = r0' from by decide]
  intro h
  have hd : den zeroFact r0'.fact zeroLoc ⟨3, [], 5⟩ :=
    ⟨rfl, rfl, rfl, rfl, trivial, [], [], rfl, rfl, rfl, rfl⟩
  exact no_flow_caller _ ((h rfl).2 _ _ hd trivial).1

#print axioms cex_rec_conc

end CexRecConc

namespace CexRev
open CexApp

/-- `ret` at the exit of `get`, `p.f` at its entry. -/
def lRet : Loc := ⟨2, [], 5⟩
def lPf : Loc := ⟨1, [1], 5⟩
/-- The reversal of the must record, as a backward record (normal layer). -/
def revRec : MethodId → PFact × AFact → Prop :=
  fun m x => m = 1 ∧ x = ((revEdge j g.fact).1, ⟨(revEdge j g.fact).2, false⟩)

theorem rev_eq : revEdge j g.fact = (⟨2, [], .any, .conc 5⟩, ⟨1, [], .any, .conc 5⟩) := by decide

theorem revStmts : Reverse.RevStmts P := by
  intro M n s n' hE e he
  cases hE with
  | head =>
    cases he with
    | head => exact ⟨trivial, Or.inr ⟨0, rfl⟩⟩
    | tail _ h => cases h
  | tail _ h =>
    cases h with
    | tail _ h =>
      cases h with
      | head =>
        cases he with
        | head => exact ⟨trivial, Or.inl (Or.inl rfl)⟩
        | tail _ h => cases h
      | tail _ h => cases h

theorem revCalls : Reverse.RevCalls P := by
  intro M n c n' hE
  cases hE with
  | tail _ h =>
    cases h with
    | head =>
      refine ⟨fun e he => ?_, fun e he => ?_⟩
      · cases he with
        | head => exact ⟨trivial, Or.inl (Or.inl rfl)⟩
        | tail _ h => cases h
      · cases he with
        | head => exact ⟨trivial, Or.inl (Or.inl rfl)⟩
        | tail _ h => cases h
    | tail _ h =>
      cases h with
      | tail _ h => cases h

/-- `CexRev`: A MUST RECORD MUST NOT BE REVERSED. The must record of `get` is END-EXACT (a
    persisted record of the forward run), and the program reverses exactly (`RevStmts`,
    `RevCalls`: every converse flow of `P` is a flow of `Program.rev P` and back). Its reversal
    `revEdge j g = ((ret, [], [any], 5), (p, [], [any], 5))` relates `ret` to `p.f`, but `p.f`
    does not flow to `ret`: the reversed pair is not a flow of the reversed program, so the
    reversed record breaks the record hypothesis of the backward run (`BExact.RecsExactNZ`). The
    reversal would claim a must requirement ("every location below `p` leads to the sink") that
    only `p.g` satisfies. -/
theorem cex_rev :
    RecsExactT P (fun _ => True) recs ∧ recs 1 (j, true, g) ∧
    Reverse.RevStmts P ∧ Reverse.RevCalls P ∧
    den (revEdge j g.fact).1 (revEdge j g.fact).2 lRet lPf ∧
    ¬ Flow P 1 lPf (P.exit 1) lRet ∧
    ¬ Flow (Reverse.Program.rev P) 1 lRet ((Reverse.Program.rev P).exit 1) lPf ∧
    ¬ BExact.RecsExactNZ (Reverse.Program.rev P) revRec := by
  have hd : den (revEdge j g.fact).1 (revEdge j g.fact).2 lRet lPf := by
    rw [rev_eq]
    exact ⟨rfl, rfl, rfl, rfl, trivial, [], [1], rfl, rfl, trivial, trivial⟩
  have hnf : ¬ Flow P 1 lPf (P.exit 1) lRet := fun h =>
    absurd (flow_callee h rfl rfl ⟨[], rfl⟩).1 (by decide)
  have hnr : ¬ Flow (Reverse.Program.rev P) 1 lRet ((Reverse.Program.rev P).exit 1) lPf := fun h =>
    hnf ((Reverse.flow_rev_iff_calls revStmts revCalls).mpr h)
  refine ⟨recsExact, ⟨rfl, rfl⟩, revStmts, revCalls, hd, hnf, hnr, fun h => hnr ?_⟩
  exact h 1 _ _ ⟨rfl, rfl⟩ (by decide) rfl lRet lPf hd

#print axioms cex_rev

end CexRev

namespace CexSupMark

def a : PFact := ⟨1, [], .any, .conc 5⟩
def j : PFact := ⟨1, [], .any, .star⟩
def l : Loc := ⟨1, [], 6⟩

/-- `CexSupMark`: THE MARK EQUALITY `j.mark = a.mark` OF `SupLink` (the `[any-taint]` link). For the
    premise `j = (x, [], [any], *)` inside the `[any-taint]` added fact `a = (x, [], [any], 5)`,
    every other condition of the link holds (`a` is `.any` with a concrete mark, `satI j a`, `j`
    has the `.any` tail), but `j` covers the location `x` with the mark `6`, which `a` does not
    carry, so the call does not supply it. Without the equality, a must-premise `j` would be
    "supported" although its locations with other marks are not entry-reachable. In a concrete run
    (`EmitCopiesMark`) every premise mark is concrete, and then `satI` alone gives the equality
    (`markSub_conc`). -/
theorem cex_sup_mark :
    a.kind = .any ∧ (∃ t, a.mark = .conc t) ∧ satI j a = true ∧ j.kind = .any ∧
    j.covers l ∧ ¬ a.covers l ∧ ¬ SupLink a j true := by
  refine ⟨rfl, ⟨5, rfl⟩, by decide, rfl, ⟨rfl, ⟨[], rfl, trivial⟩, trivial⟩, ?_, ?_⟩
  · intro h
    have h1 : (6 : Nat) = 5 := h.2.2
    exact absurd h1 (by decide)
  · intro h
    rcases h with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, _, h3, _⟩
    · exact absurd h1 (by decide)
    · exact absurd h1 (by decide)
    · exact absurd h3 (by decide)

#print axioms cex_sup_mark

end CexSupMark

end ApSpec.AnyTaintExact

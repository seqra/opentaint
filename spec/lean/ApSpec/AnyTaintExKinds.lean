/-
  ApSpec.AnyTaintExKinds — the KINDS INVARIANT of the refined run 1 (`AnyTaintEx.D6X`), the
  PREMISES of a normal edge of the refined restricted run (`AnyTaintEx.DRX`, `DRXs`), and the
  SIMULATIONS of the refined runs by the base runs (`AnyTaintEx.Sim6X`, `AnyTaintEx.SimRX`), with
  the EXCLUSION of the forward `[any-taint]` conclusion (decision F69, DESIGN §6, amendment A2).

  Namespace: `ApSpec.AnyTaintExKinds`. The definitions are in `AnyTaintExDefs.lean` (namespace
  `ApSpec.AnyTaintEx`); this file does not change them.

  ## Main results (all constructive; see the `#print axioms` lines)

  1. THE KINDS INVARIANT OF `D6X` (§2), by a direct induction on `D6X` with the per-operation lemmas
     (`applyEdgeX_anyConc`, `transferX_anyConc`, `applySummaryX_anyConc`, `cleanResX_anyConc`,
     `cleanResX_cases`), not through a simulation:
     * `D6X_any_conc`: a NORMAL `.any` conclusion (`[any-taint]/E`) has a concrete mark
       (hypotheses `TaintConc`, `BindNoAny`, as `AnyTaintSim.D6T_any_conc`; every abstraction);
     * `D6X_flow_no_any_taint`: a `*` premise (FLOW) has no normal `.any` conclusion (S7
       `MarkWF`, `TaintConc`, `BindNoAny`; NO `W6.SummaryStar`, which
       `AnyTaintSim.D6T_flow_no_any_taint` needs for its simulation); `D6X_flow_no_excl`: a FLOW
       conclusion carries no exclusion;
     * `kinds_D6X` (`policy1`), `kinds_D6X_gen` (every `InitK` abstraction): the six claims of
       `AnyTaintSim.kinds_D6T` for `D6X`, under the hypotheses of `kinds_D6T` (S7, S8 `PremConc`
       and `NoUnivE`, `ExactTargetConc`, `TaintConc`, `BindNoAny`). The motives: `AnyConcObj6`,
       `KInvObj6` (the FLOW motive of `Kinds.kInv_all`), `ConcObj6` (`Coverage.EdgeInv`),
       `LegalObj6` (W2). The `below` cleaner's new position `(b, P.f, $, T)` (a fact the base does
       not have) has the concrete mark of an `[any-taint]` fact, so it never lies under a `*`
       premise and touches no claim.
  2. THE PREMISES OF A NORMAL `DRX` EDGE (§3): `DRX_normal_premise` (the form of
     `RExact.complete_premise_exact` for `DRX`): a normal edge has a `$` premise that is not must,
     or a must-premise, which is `.any` with a concrete mark (hypothesis `EmitCopiesMarkX emit`);
     `DRX_must_premise` (every must-premise is `[any-taint]`); the spec instance
     `DRXs_normal_premise`, `DRXs_must_premise` (no hypothesis). The motive `PremLayerX`
     (`DRX_premLayer`, no hypothesis): a normal edge has a `$`, an abstract or a must premise.
  3. THE SIMULATIONS (§4, §5), the statements of `AnyTaintExDefs.lean` with exactly the expected
     hypotheses:
     * `sim6X` (`Sim6X`, only `NoBelowCleaner P`), `sim6XIn`; `D6X_abs_same`: an abstract-mark
       edge of `D6X` is a `D6T` edge with the same annotated fact;
     * `simRX` (`SimRX`, `NoBelowCleaner P` and `RecsRefine P recsX recs`), `simRXIn`.
     The per-fact relation is `RelA` (`W6.LE` of the base facts, an annotated refined fact is a base
     demand fact, an abstract-mark refined fact IS its base fact); the restricted run adds the
     premise condition of `RefinesR` (`SimObjR`). The key local lemma is `applyEdgeX_LE` with
     `annX_geo_ex`: a non-empty result exclusion comes from a base demotion (a `keep` row with a
     non-empty edge exclusion) or from an exclusion of the input, the premise or the target. The
     abstract-mark component removes the `W6.SummaryStar`-style hypothesis of
     `W6.applySummary_LL` (a `*` result of a summary application has an abstract mark, so the two
     summary edges are the same). The record demotion: a refined demotion `mj ∧ ¬satX` is a base
     demotion, or the base record is demand (`mj` only in the refined run), or the added fact
     carries an exclusion (`sat_inside_ex`).

  ## Hypotheses

  No new program hypothesis: the kinds theorems use those of `AnyTaintSim.kinds_D6T` (and
  `D6X_flow_no_any_taint` drops its `W6.SummaryStar`); `DRX_normal_premise` uses C3
  (`EmitCopiesMarkX`, true for `emitX`); the simulations use the hypotheses that
  `AnyTaintExDefs.lean` names (`NoBelowCleaner`, `RecsRefine`).
-/
import ApSpec.AnyTaintExExact
import ApSpec.AnyTaintSim

namespace ApSpec.AnyTaintExKinds
open ApSpec ApSpec.AnyTaint ApSpec.AnyTaintEx

/-! ## 1. Local lemmas -/

/-- The refined `part` row: the input fact (with an exclusion), the base `concPart`, or the new
    position `$` of the `below` row. -/
theorem partX_cases {cl : Cleaner} {c x : XFact} (h : x ∈ partX cl c) :
    x.af = c.af ∨ x.af = concPart cl c.af ∨
    (x.af.fact.kind = .exact ∧ x.af.fact.mark = c.af.fact.mark ∧ x.af.demand = c.af.demand) := by
  unfold partX at h
  split at h
  · split at h
    · rw [List.mem_singleton.mp h]; exact Or.inl rfl
    · rcases List.mem_cons.mp h with h1 | h1
      · rw [h1]; exact Or.inl rfl
      · rw [List.mem_singleton.mp h1]; exact Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)
    · rw [List.mem_singleton.mp h]; exact Or.inr (Or.inl rfl)
  · rw [List.mem_singleton.mp h]; exact Or.inr (Or.inl rfl)

#print axioms partX_cases

/-- THE REFINED CLEANER, case by case: every result is the input fact (with its exclusion, possibly
    enlarged), a result of the base cleaner `cleanRes` on the base fact, or the new position
    `(b, P.f, $, T)` of the `below` row (a `$` fact with the concrete mark and the layer of the
    input). -/
theorem cleanResX_cases {cl : Cleaner} {c x : XFact} (h : x ∈ (cleanResX cl c).facts) :
    x.af = c.af ∨ x.af ∈ (cleanRes cl c.af).facts ∨
    ((∃ t, c.af.fact.mark = .conc t) ∧ x.af.fact.kind = .exact ∧
      x.af.fact.mark = c.af.fact.mark ∧ x.af.demand = c.af.demand) := by
  unfold cleanResX at h
  rcases cleanPosX_cases cl c with hp | ⟨hp, _⟩
  · unfold cleanRes
    rw [← hp]
    cases hq : cleanPosX cl c with
    | disjoint => rw [hq] at h; exact Or.inl (by rw [List.mem_singleton.mp h])
    | inside =>
      rw [hq] at h
      dsimp only at h ⊢
      revert h
      cases hm : c.af.fact.mark with
      | conc t =>
        intro h
        dsimp only at h ⊢
        cases hb : cl.markB t with
        | true => rw [hb, if_pos rfl] at h; exact absurd h List.not_mem_nil
        | false =>
          rw [hb, if_neg Bool.false_ne_true] at h
          exact Or.inl (by rw [List.mem_singleton.mp h])
      | star =>
        cases hcm : cl.mark with
        | none => intro h; exact absurd h List.not_mem_nil
        | some t =>
          intro h
          right; left
          rw [List.mem_singleton.mp h]
          exact List.mem_singleton.mpr rfl
      | starEx xs =>
        cases hcm : cl.mark with
        | none => intro h; exact absurd h List.not_mem_nil
        | some t =>
          intro h
          right; left
          rw [List.mem_singleton.mp h]
          exact List.mem_singleton.mpr rfl
    | part =>
      rw [hq] at h
      dsimp only at h ⊢
      revert h
      cases hm : c.af.fact.mark with
      | conc t =>
        intro h
        dsimp only at h ⊢
        cases hb : cl.markB t with
        | true =>
          rw [hb, if_pos rfl] at h
          rw [if_pos rfl]
          rcases partX_cases h with h1 | h1 | ⟨h1, h2, h3⟩
          · exact Or.inl h1
          · exact Or.inr (Or.inl (by rw [h1]; exact List.mem_singleton.mpr rfl))
          · exact Or.inr (Or.inr ⟨⟨t, rfl⟩, h1, h2.trans hm, h3⟩)
        | false =>
          rw [hb, if_neg Bool.false_ne_true] at h
          exact Or.inl (by rw [List.mem_singleton.mp h])
      | star =>
        cases hcm : cl.mark with
        | none =>
          intro h
          right; left
          rw [List.mem_singleton.mp h]
          exact List.mem_singleton.mpr rfl
        | some t =>
          intro h
          right; left
          rw [List.mem_singleton.mp h]
          exact List.mem_singleton.mpr rfl
      | starEx xs =>
        cases hcm : cl.mark with
        | none =>
          intro h
          right; left
          rw [List.mem_singleton.mp h]
          exact List.mem_singleton.mpr rfl
        | some t =>
          intro h
          right; left
          rw [List.mem_singleton.mp h]
          exact List.mem_singleton.mpr rfl
  · rw [hp] at h
    exact Or.inl (by rw [List.mem_singleton.mp h])

#print axioms cleanResX_cases

/-! ### The `[any-taint]` motive (`AnyTaintSim.AnyConc`) through the refined operations -/

/-- THE LOCAL STEP of the kinds invariant. A result of the refined core operation keeps
    `AnyConc` (a normal `.any` fact has a concrete mark) if an `.any` target has a concrete mark.
    A result in the layer of the base result is the base case (`AnyTaintSim.applyEdge_anyConc`); a
    result kept normal by an exclusion row (`annX` `keep`) comes from an `.any` input with a
    CONCRETE mark, so its mark is concrete. -/
theorem applyEdgeX_anyConc {c x : XFact} {fr to : PFact} {fex tex : Excl}
    (hc : AnyTaintSim.AnyConc c.af) (hto : to.kind = .any → ∃ t, to.mark = .conc t)
    (hx : x ∈ (applyEdgeX c fr fex to tex).facts) : AnyTaintSim.AnyConc x.af := by
  obtain ⟨y, hy, hxy, hl⟩ := applyEdgeX_base hx
  rcases hl with hl | ⟨_, _, hk, _⟩
  · intro hk' hd'
    have hy' := AnyTaintSim.applyEdge_anyConc hc hto hy
    rw [hxy]
    exact hy' (by rw [← hxy]; exact hk') (by rw [← hl]; exact hd')
  · intro _ _
    obtain ⟨_, t, ht⟩ := AnyTaintExExact.keepB_parts hk
    rw [hxy]
    exact applyEdge_mark_conc ht hy

#print axioms applyEdgeX_anyConc

/-- The refined statement transfer keeps `AnyConc` if every taint edge with an `.any` target has a
    concrete target mark (`TaintConc`); a non-taint `.any` target is demoted by W6T. -/
theorem transferX_anyConc {taint : TaintEdges} {counted : Acc → Bool} {L : Nat} {s : Stmt}
    {c x : XFact}
    (hs : ∀ e, e ∈ s.edges → taint e = true → e.2.kind = .any → ∃ t, e.2.mark = .conc t)
    (hc : AnyTaintSim.AnyConc c.af) (hx : x ∈ (transferX taint counted L s c).facts) :
    AnyTaintSim.AnyConc x.af := by
  unfold transferX at hx
  cases hm : memB c.af.fact.base s.touched with
  | false =>
    rw [hm, if_neg Bool.false_ne_true] at hx
    rw [List.mem_singleton.mp hx]; exact hc
  | true =>
    rw [hm, if_pos rfl] at hx
    obtain ⟨z0, hz0, rfl⟩ := List.mem_map.mp hx
    rw [limitFX_af]
    apply AnyTaintSim.limitF_anyConc
    obtain ⟨e, he, hz⟩ := AnyTaintExExact.applyAllXT_mem hz0
    obtain ⟨z, hzb, rfl⟩ := List.mem_map.mp hz
    rw [w6tX_af]
    unfold w6t
    cases hb : (e.2.kind.isAny && !taint e) with
    | true => rw [if_pos rfl]; exact AnyTaintSim.raise_anyConc z.af
    | false =>
      rw [if_neg Bool.false_ne_true]
      refine applyEdgeX_anyConc hc (fun hk => ?_) hzb
      have ht : taint e = true := by
        rw [hk] at hb
        cases h2 : taint e with
        | true => rfl
        | false => rw [h2] at hb; cases hb
      exact hs e he ht hk

#print axioms transferX_anyConc

/-- The refined summary application keeps `AnyConc` if the summary edge has it. -/
theorem applySummaryX_anyConc {a g r : XFact} {j : PFact} {jex : Excl}
    (ha : AnyTaintSim.AnyConc a.af) (hg : AnyTaintSim.AnyConc g.af)
    (hr : r ∈ (applySummaryX a j jex g).facts) : AnyTaintSim.AnyConc r.af := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
  rw [normX_af]
  cases hgd : g.af.demand with
  | true =>
    intro _ hd
    rw [AnyTaintSim.norm_demand (y := ⟨x.af.fact, x.af.demand || true⟩) (Bool.or_true _)] at hd
    cases hd
  | false =>
    have hxa : AnyTaintSim.AnyConc x.af := applyEdgeX_anyConc ha (fun hk => hg hk hgd) hx
    apply AnyTaintSim.norm_anyConc
    intro hk hd
    exact hxa hk (by rw [Bool.or_false] at hd; exact hd)

#print axioms applySummaryX_anyConc

/-- The refined cleaner keeps `AnyConc` (the new position of the `below` row is a `$` fact). -/
theorem cleanResX_anyConc {cl : Cleaner} {c x : XFact} (hc : AnyTaintSim.AnyConc c.af)
    (hx : x ∈ (cleanResX cl c).facts) : AnyTaintSim.AnyConc x.af := by
  rcases cleanResX_cases hx with h1 | h1 | ⟨_, h1, _⟩
  · rw [h1]; exact hc
  · exact AnyTaintSim.cleanRes_anyConc hc h1
  · intro hk; rw [h1] at hk; cases hk

#print axioms cleanResX_anyConc

/-! ### The FLOW motive (`Kinds.FlowF`), the concrete marks and W2 (`Invariant.Legal`) -/

/-- `FlowF` reads only the fact. -/
theorem flowF_of_fact {x y : AFact} (h : x.fact = y.fact) (hy : Kinds.FlowF y) : Kinds.FlowF x := by
  unfold Kinds.FlowF; rw [h]; exact hy

/-- W2 of a refined result from W2 of a base result with the same fact in the same or a higher
    layer. -/
theorem legal_of_base {x y : AFact} (hf : x.fact = y.fact) (hd : x.demand = true → y.demand = true)
    (hy : Invariant.Legal y) : Invariant.Legal x := by
  intro e hk
  rw [hf] at hk
  obtain ⟨h1, h2⟩ := hy e hk
  refine ⟨by rw [hf]; exact h1, ?_⟩
  cases hx : x.demand with
  | false => rfl
  | true => rw [hd hx] at h2; cases h2

#print axioms legal_of_base

/-- A refined statement result has the fact of a base `transfer` result. -/
theorem transferX_fact {taint : TaintEdges} {counted : Acc → Bool} {L : Nat} {s : Stmt}
    {c x : XFact} (h : x ∈ (transferX taint counted L s c).facts) :
    ∃ y, y ∈ (transfer counted L s c.af).facts ∧ x.af.fact = y.fact := by
  obtain ⟨y, hy, hfy, _⟩ := transferX_base h
  obtain ⟨y0, hy0, hle⟩ := transferT_mem hy
  exact ⟨y0, hy0, hfy.trans hle.fact.symm⟩

#print axioms transferX_fact

/-- W2 of the base statement transfer with W6T. -/
theorem transferT_legal {taint : TaintEdges} {counted : Acc → Bool} {L : Nat} {s : Stmt}
    {c y : AFact} (hc : Invariant.Legal c) (h : y ∈ (transferT taint counted L s c).facts) :
    Invariant.Legal y := by
  rcases AnyTaintSim.transferT_mem_inv h with ⟨_, rfl⟩ | ⟨e, x, _, hx, rfl⟩
  · exact hc
  · apply Invariant.limitF_Legal
    rcases w6t_cases taint e x with e1 | ⟨hk, _, e1⟩
    · rw [e1]; exact Invariant.applyEdge_Legal hx
    · rw [e1]
      intro e' hk'
      have hxk : x.fact.kind = .any := applyEdge_any_target hk hx
      have hk'' : x.fact.kind = .star e' := hk'
      rw [hxk] at hk''
      cases hk''

#print axioms transferT_legal

/-- W2 of a refined statement result. -/
theorem transferX_legal {taint : TaintEdges} {counted : Acc → Bool} {L : Nat} {s : Stmt}
    {c x : XFact} (hc : Invariant.Legal c.af) (h : x ∈ (transferX taint counted L s c).facts) :
    Invariant.Legal x.af := by
  obtain ⟨y, hy, hfy, hd⟩ := transferX_base h
  exact legal_of_base hfy hd (transferT_legal hc hy)

#print axioms transferX_legal

/-! ## 2. Run 1 with the exclusion (`D6X`): the kinds invariant -/

/-- The `[any-taint]` motive on the objects of run 1: a normal `.any` conclusion has a concrete
    mark. -/
def AnyConcObj6 : XObj6 → Prop
  | .edge _ _ _ f => AnyTaintSim.AnyConc f.af
  | _ => True

/-- The FLOW motive (`Kinds.KInv` on the refined run): every premise satisfies `InitK`, an edge with
    an abstract premise has a FLOW conclusion (an abstract mark, the tail `.any` or `*/E` with `E`
    not Universe). -/
def KInvObj6 : XObj6 → Prop
  | .init _ i => Kinds.InitK i
  | .edge _ i _ f => Kinds.InitK i ∧ (Exact.absB i.mark = true → Kinds.FlowF f.af)
  | _ => True

/-- The TAINT motive (`Coverage.EdgeInv` on the refined run): a concrete premise mark gives a
    concrete conclusion mark. -/
def ConcObj6 : XObj6 → Prop
  | .edge _ i _ f => ∀ t, i.mark = .conc t → ∃ t', f.af.fact.mark = .conc t'
  | _ => True

/-- The W2 motive (`Invariant.InvL` on the refined run): a `*` conclusion has an abstract mark and
    is normal. -/
def LegalObj6 : XObj6 → Prop
  | .edge _ _ _ f => Invariant.Legal f.af
  | _ => True

section Run1
variable {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
  {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId}

/-- The `[any-taint]` motive on every object of `D6X` (one induction). Hypotheses: `TaintConc`,
    `BindNoAny` (as `AnyTaintSim.D6T_anyConc_all`). -/
theorem D6X_anyConc_all (htc : TaintConc P taint) (hbn : BindNoAny P) {o : XObj6}
    (h : D6X P taint counted L α sinks roots o) : AnyConcObj6 o := by
  induction h with
  | @start M i _ _ =>
    show AnyTaintSim.AnyConc (startX i false Excl.empty).af
    rw [startX_af]; exact AnyTaintSim.startFact_anyConc i
  | @step M i n f n' s f' _ hE hf ih =>
    exact transferX_anyConc (fun e he ht _ => (htc _ _ _ _ hE e he ht).2.1) ih hf
  | pass _ _ _ ih => exact ih
  | @ret M i n f n' c e1 a j g r e2 r' _ hE he1 ha _ _ _ hr he2 hr' ihF _ ihG =>
    have hno : ∀ e : MicroEdge, e.2.kind.isAny = false → e.2.kind = .any →
        ∃ t, e.2.mark = .conc t :=
      fun e h1 h2 => by rw [h2] at h1; cases h1
    have hA := applyEdgeX_anyConc ihF (hno e1 ((hbn _ _ _ _ hE).1 e1 he1)) ha
    have hR := applySummaryX_anyConc hA ihG hr
    show AnyTaintSim.AnyConc (limitFX counted L r').af
    rw [limitFX_af]
    exact AnyTaintSim.limitF_anyConc
      (applyEdgeX_anyConc hR (hno e2 ((hbn _ _ _ _ hE).2 e2 he2)) hr')
  | clean _ _ hf ih => exact cleanResX_anyConc ih hf
  | filt _ _ _ ih => exact ih
  | root => trivial
  | reqStmt => trivial
  | added => trivial
  | initA => trivial
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial
  | reqClean => trivial

#print axioms D6X_anyConc_all

/-- The FLOW motive on every object of `D6X` (one induction, `Kinds.kInv_all` on the refined run).
    Hypotheses: those of `Kinds.kInv_all` (S7 `MarkWF`, S8 `PremConc` and `NoUnivE`,
    `ExactTargetConc`, `InitK` for the abstraction). The new position `$` of the `below` row comes
    from an `[any-taint]` fact, which has a concrete mark, so it never meets an abstract premise. -/
theorem D6X_kInv_all (hmw : Exact.MarkWF P) (het : Kinds.ExactTargetConc P)
    (hA : Invariant.AllEdges P Invariant.PremConc) (hB : Invariant.AllEdges P Invariant.NoUnivE)
    (hα : ∀ m a, Kinds.InitK (α m a)) {o : XObj6}
    (h : D6X P taint counted L α sinks roots o) : KInvObj6 o := by
  induction h with
  | root => exact Kinds.initK_conc (t := zeroMark) rfl
  | @start M i _ ih =>
    refine ⟨ih, fun ha => ?_⟩
    show Kinds.FlowF (startX i false Excl.empty).af
    rw [startX_af]
    exact Kinds.startFact_flow ih ha
  | @step M i n f n' s f' _ hE hf ih =>
    refine ⟨ih.1, fun ha => ?_⟩
    obtain ⟨y, hy, hfy⟩ := transferX_fact hf
    refine flowF_of_fact hfy (Kinds.transfer_flow (fun e he => ?_) (ih.2 ha) hy)
    exact ⟨hmw.stmt _ _ _ _ hE e he, hA.1 _ _ _ _ hE e he, hB.1 _ _ _ _ hE e he,
      het.1 _ _ _ _ hE e he⟩
  | reqStmt => trivial
  | pass _ _ _ ih => exact ih
  | added => trivial
  | initA => exact hα _ _
  | @ret M i n f n' c e1 a j g r e2 r' _ hE he1 ha1 _ _ _ hr he2 hr' ihF ihJ ihG =>
    refine ⟨ihF.1, fun ha => ?_⟩
    show Kinds.FlowF (limitFX counted L r').af
    rw [limitFX_af]
    apply Kinds.limitF_flow
    obtain ⟨ya, hya, hfa, _⟩ := bindX_base ha1
    have hA1 : Kinds.FlowF a.af := flowF_of_fact hfa
      (Kinds.micro_flow (hmw.toC _ _ _ _ hE e1 he1) (hA.2.1 _ _ _ _ hE e1 he1)
        (hB.2.1 _ _ _ _ hE e1 he1) (het.2.1 _ _ _ _ hE e1 he1) (ihF.2 ha) hya)
    obtain ⟨yr, hyr, hfr, _⟩ := applySummaryX_base hr
    have hR : Kinds.FlowF r.af :=
      flowF_of_fact hfr (Kinds.applySummary_flow hA1 ihJ.2 ihG.2 hyr)
    obtain ⟨yr', hyr', hfr', _⟩ := bindX_base hr'
    exact flowF_of_fact hfr'
      (Kinds.micro_flow (hmw.fromC _ _ _ _ hE e2 he2) (hA.2.2 _ _ _ _ hE e2 he2)
        (hB.2.2 _ _ _ _ hE e2 he2) (het.2.2 _ _ _ _ hE e2 he2) hR hyr')
  | reqSink => trivial
  | @answer M i t a _ _ _ _ _ _ => exact Kinds.initK_conc (W6.answerInit_mark i a t)
  | reqUp => trivial
  | vuln => trivial
  | @clean M i n f n' cl f' _ _ hf ih =>
    refine ⟨ih.1, fun ha => ?_⟩
    have hc := ih.2 ha
    rcases cleanResX_cases hf with h1 | h1 | ⟨⟨t, ht⟩, _⟩
    · rw [h1]; exact hc
    · exact Kinds.cleanRes_flow hc h1
    · exact (Kinds.not_abs_of_conc ht hc.1).elim
  | reqClean => trivial
  | filt _ _ _ ih => exact ih

#print axioms D6X_kInv_all

/-- The TAINT motive on every object of `D6X` (no hypothesis): a concrete premise mark gives a
    concrete conclusion mark (`Coverage.edgeInv_all` on the refined run). -/
theorem D6X_conc_all {o : XObj6} (h : D6X P taint counted L α sinks roots o) : ConcObj6 o := by
  induction h with
  | @start M i _ _ =>
    intro t ht
    exact ⟨t, by rw [startX_af, startT_mark]; exact ht⟩
  | @step M i n f n' s f' _ _ hf ih =>
    intro t ht
    obtain ⟨t1, h1⟩ := ih t ht
    obtain ⟨y, hy, hfy⟩ := transferX_fact hf
    obtain ⟨t2, h2⟩ := transfer_mark_conc h1 hy
    exact ⟨t2, by rw [hfy]; exact h2⟩
  | pass _ _ _ ih => exact ih
  | @ret M i n f n' c e1 a j g r e2 r' _ _ _ ha _ _ _ hr _ hr' ihF _ _ =>
    intro t ht
    obtain ⟨tf, htf⟩ := ihF t ht
    obtain ⟨ya, hya, hay, _⟩ := applyEdgeX_base ha
    obtain ⟨ta, hta⟩ := AnyTaintExExact.conc_of_fact hay (applyEdge_mark_conc htf hya)
    obtain ⟨yr, hyr, hry, _⟩ := applySummaryX_base hr
    obtain ⟨tr, htr⟩ := AnyTaintExExact.conc_of_fact hry (applySummary_mark_conc hta hyr)
    obtain ⟨yr', hyr', hry', _⟩ := applyEdgeX_base hr'
    obtain ⟨t3, ht3⟩ := AnyTaintExExact.conc_of_fact hry' (applyEdge_mark_conc htr hyr')
    exact ⟨t3, by rw [limitFX_af, Exact.limitF_mark]; exact ht3⟩
  | @clean M i n f n' cl f' _ _ hf ih =>
    intro t ht
    obtain ⟨t1, h1⟩ := ih t ht
    rcases cleanResX_cases hf with e1 | e1 | ⟨_, _, e2, _⟩
    · exact ⟨t1, by rw [e1]; exact h1⟩
    · exact cleanRes_mark_conc h1 e1
    · exact ⟨t1, by rw [e2]; exact h1⟩
  | filt _ _ _ ih => exact ih
  | root => trivial
  | reqStmt => trivial
  | added => trivial
  | initA => trivial
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial
  | reqClean => trivial

#print axioms D6X_conc_all

/-- W2 on every edge of `D6X` (no hypothesis): a `*` conclusion has an abstract mark and is
    normal (`Invariant.D_legal` on the refined run). -/
theorem D6X_legal_all {o : XObj6} (h : D6X P taint counted L α sinks roots o) : LegalObj6 o := by
  induction h with
  | @start M i _ _ =>
    show Invariant.Legal (startX i false Excl.empty).af
    rw [startX_af, startT_false]
    exact fun e hk => Invariant.startFact_legal hk
  | @step M i n f n' s f' _ _ hf ih => exact transferX_legal ih hf
  | pass _ _ _ ih => exact ih
  | @ret M i n f n' c e1 a j g r e2 r' _ _ _ _ _ _ _ _ _ hr' _ _ _ =>
    show Invariant.Legal (limitFX counted L r').af
    rw [limitFX_af]
    apply Invariant.limitF_Legal
    obtain ⟨y, hy, hfy, hd⟩ := bindX_base hr'
    exact legal_of_base hfy hd (Invariant.applyEdge_Legal hy)
  | @clean M i n f n' cl f' _ _ hf ih =>
    show Invariant.Legal f'.af
    rcases cleanResX_cases hf with e1 | e1 | ⟨_, hk, _⟩
    · rw [e1]; exact ih
    · exact Invariant.cleanRes_Legal ih e1
    · intro e he; rw [hk] at he; cases he
  | filt _ _ _ ih => exact ih
  | root => trivial
  | reqStmt => trivial
  | added => trivial
  | initA => trivial
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial
  | reqClean => trivial

#print axioms D6X_legal_all

/-- THE KINDS INVARIANT OF THE REFINED RUN 1 (ap.md §7.2 with F69 decision 2, DESIGN §6 A2): every
    NORMAL edge of `D6X` whose conclusion has the `.any` tail (a spec `[any-taint]/E` conclusion,
    with or without an exclusion) has a CONCRETE mark. Hypotheses: `TaintConc` and `BindNoAny`, as
    `AnyTaintSim.D6T_any_conc`; every abstraction `α`. The exclusion rows of A2 (`annX` `keep`)
    keep a result normal only on an `.any` input with a concrete mark, so their result mark is
    concrete; the `below` cleaner's new position is a `$` fact. -/
theorem D6X_any_conc (htc : TaintConc P taint) (hbn : BindNoAny P)
    {M : MethodId} {i : PFact} {n : Node} {f : XFact}
    (h : D6X P taint counted L α sinks roots (.edge M i n f)) (hk : f.af.fact.kind = .any)
    (hd : f.af.demand = false) : ∃ t, f.af.fact.mark = .conc t :=
  D6X_anyConc_all htc hbn h hk hd

#print axioms D6X_any_conc

/-- A FLOW EDGE OF THE REFINED RUN 1 HAS NO `[any-taint]` LEAF: an edge of `D6X` whose premise has
    the mark `*` has no normal `.any` conclusion (its mark is abstract, the mark part of
    `AnyTaintExExact.D6X_edgeOK`, and a normal `.any` conclusion has a concrete mark,
    `D6X_any_conc`). Hypotheses: S7 (`Exact.MarkWF`), `TaintConc`, `BindNoAny`. (No `W6.SummaryStar`:
    unlike `AnyTaintSim.D6T_flow_no_any_taint` the proof does not go through a simulation.) -/
theorem D6X_flow_no_any_taint (hmw : Exact.MarkWF P) (htc : TaintConc P taint)
    (hbn : BindNoAny P) {M : MethodId} {i : PFact} {n : Node} {f : XFact}
    (h : D6X P taint counted L α sinks roots (.edge M i n f)) (hi : i.mark = .star) :
    ¬ (f.af.fact.kind = .any ∧ f.af.demand = false) := by
  rintro ⟨hk, hd⟩
  obtain ⟨t, ht⟩ := D6X_any_conc htc hbn h hk hd
  have habs := (AnyTaintExExact.D6X_edgeOK hmw (Kinds.filtOK_false P) (Kinds.backOK_false P) h).1
    (by rw [hi]; rfl)
  rw [ht] at habs
  cases habs

#print axioms D6X_flow_no_any_taint

/-- A FLOW EDGE CARRIES NO EXCLUSION: under a `*` premise every conclusion of `D6X` has the empty
    exclusion (an exclusion is carried only by an `[any-taint]` conclusion, `D6X_wf`, and a FLOW edge
    has none, `D6X_flow_no_any_taint`). So a FLOW tree has no `[any-taint]/E` leaf at all.
    Hypotheses: those of `D6X_flow_no_any_taint`. -/
theorem D6X_flow_no_excl (hmw : Exact.MarkWF P) (htc : TaintConc P taint)
    (hbn : BindNoAny P) {M : MethodId} {i : PFact} {n : Node} {f : XFact}
    (h : D6X P taint counted L α sinks roots (.edge M i n f)) (hi : i.mark = .star) :
    f.ex = Excl.empty := by
  cases hc : carriesB f.af with
  | false => exact AnyTaintExExact.D6X_wf_edge h hc
  | true =>
    obtain ⟨hk, hd, _⟩ := carriesB_parts hc
    exact (D6X_flow_no_any_taint hmw htc hbn h hi ⟨hk, hd⟩).elim

#print axioms D6X_flow_no_excl

/-- THE PARTITION OF THE REFINED RUN 1, for every abstraction with `Kinds.InitK` (ap.md §7.2 with
    F69, DESIGN §6 A2). For every edge of `D6X`: the four claims of `Kinds.kinds_D` (the premise mark
    is `*` or concrete; a `*` premise gives an abstract conclusion mark and no `$` tail; a concrete
    premise gives a concrete conclusion mark and no `*` tail; a `*` tail has an abstract mark and is
    normal), and the two claims of F69: a normal `.any` conclusion (`[any-taint]/E`) has a concrete
    mark, so a `*` premise (FLOW) has no `[any-taint]` conclusion. Hypotheses: those of
    `Kinds.kinds_D` (S7 `MarkWF`, S8 `PremConc` and `NoUnivE`, `ExactTargetConc`), `InitK` for the
    abstraction, and `TaintConc`, `BindNoAny` (as `AnyTaintSim.kinds_D6T`). -/
theorem kinds_D6X_gen (hmw : Exact.MarkWF P) (het : Kinds.ExactTargetConc P)
    (hA : Invariant.AllEdges P Invariant.PremConc) (hB : Invariant.AllEdges P Invariant.NoUnivE)
    (hα : ∀ m a, Kinds.InitK (α m a)) (htc : TaintConc P taint) (hbn : BindNoAny P)
    {M : MethodId} {i : PFact} {n : Node} {f : XFact}
    (h : D6X P taint counted L α sinks roots (.edge M i n f)) :
    (i.mark = .star ∨ ∃ t, i.mark = .conc t) ∧
    (i.mark = .star → Invariant.AbsMark f.af.fact.mark ∧ f.af.fact.kind ≠ .exact) ∧
    (∀ t, i.mark = .conc t → (∃ t', f.af.fact.mark = .conc t') ∧ f.af.fact.kind.isStar = false) ∧
    (∀ e, f.af.fact.kind = .star e → Invariant.AbsMark f.af.fact.mark ∧ f.af.demand = false) ∧
    (f.af.fact.kind = .any → f.af.demand = false → ∃ t, f.af.fact.mark = .conc t) ∧
    (i.mark = .star → ¬ (f.af.fact.kind = .any ∧ f.af.demand = false)) := by
  have hK : KInvObj6 (.edge M i n f) := D6X_kInv_all hmw het hA hB hα h
  have hC : ConcObj6 (.edge M i n f) := D6X_conc_all h
  have hL : LegalObj6 (.edge M i n f) := D6X_legal_all h
  refine ⟨hK.1.1, fun hi => ?_, fun t ht => ?_, hL, D6X_any_conc htc hbn h,
    fun hi => D6X_flow_no_any_taint hmw htc hbn h hi⟩
  · have hf := hK.2 (by rw [hi]; rfl)
    exact ⟨Kinds.absB_iff.mp hf.1, (Kinds.flowKind_ne hf.2).1⟩
  · obtain ⟨t', ht'⟩ := hC t ht
    refine ⟨⟨t', ht'⟩, ?_⟩
    cases hk : f.af.fact.kind with
    | star e => exact absurd ht' ((hL e hk).1.not_conc t')
    | any => rfl
    | exact => rfl

#print axioms kinds_D6X_gen

end Run1

/-- THE PARTITION OF THE REFINED RUN 1 (`D6X` with `policy1`; ap.md §7.2 with F69, DESIGN §6 A2):
    the six claims of `AnyTaintSim.kinds_D6T` for `D6X`: the premise mark is `*` or concrete; a `*`
    premise gives an abstract conclusion mark and no `$` tail; a concrete premise gives a concrete
    conclusion mark and no `*` tail; a `*` tail has an abstract mark and is normal; a normal `.any`
    conclusion (`[any-taint]/E`) has a concrete mark; a `*` premise (FLOW) has no `[any-taint]`
    conclusion. Hypotheses: those of `AnyTaintSim.kinds_D6T` (S7 `MarkWF`, S8 `PremConc` and
    `NoUnivE`, `ExactTargetConc`, `TaintConc`, `BindNoAny`). The `below` cleaner's new position
    `(b, P.f, $, T)` (a fact the base does not have) has the concrete mark of an `[any-taint]` fact,
    so it lies under a concrete premise and touches no claim. -/
theorem kinds_D6X {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    (hmw : Exact.MarkWF P) (het : Kinds.ExactTargetConc P)
    (hA : Invariant.AllEdges P Invariant.PremConc) (hB : Invariant.AllEdges P Invariant.NoUnivE)
    (htc : TaintConc P taint) (hbn : BindNoAny P)
    {M : MethodId} {i : PFact} {n : Node} {f : XFact}
    (h : D6X P taint counted L policy1 sinks roots (.edge M i n f)) :
    (i.mark = .star ∨ ∃ t, i.mark = .conc t) ∧
    (i.mark = .star → Invariant.AbsMark f.af.fact.mark ∧ f.af.fact.kind ≠ .exact) ∧
    (∀ t, i.mark = .conc t → (∃ t', f.af.fact.mark = .conc t') ∧ f.af.fact.kind.isStar = false) ∧
    (∀ e, f.af.fact.kind = .star e → Invariant.AbsMark f.af.fact.mark ∧ f.af.demand = false) ∧
    (f.af.fact.kind = .any → f.af.demand = false → ∃ t, f.af.fact.mark = .conc t) ∧
    (i.mark = .star → ¬ (f.af.fact.kind = .any ∧ f.af.demand = false)) :=
  kinds_D6X_gen hmw het hA hB Kinds.policy1_initK htc hbn h

#print axioms kinds_D6X

/-! ## 3. The restricted run with the exclusion (`DRX`): the premises of a normal edge -/

/-- The premise-layer motive (`RExact.PremLayer` with must-premises): a normal edge has a `$`
    premise, an abstract premise, or a must-premise. -/
def PremLayerX : XObj → Prop
  | .edge _ i mi _ _ f => f.af.demand = false →
      i.kind = .exact ∨ Exact.absB i.mark = true ∨ mi = true
  | _ => True

/-- A normal result of the record demotion is its normal input. -/
theorem recLayerX_normal {mj s : Bool} {x : XFact} (h : (recLayerX mj s x).af.demand = false) :
    x.af.demand = false := by
  unfold recLayerX at h
  cases hb : (mj && !s) with
  | true => rw [hb, if_pos rfl] at h; cases h
  | false => rw [hb, if_neg Bool.false_ne_true] at h; exact h

#print axioms recLayerX_normal

section RunX
variable {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
  {demand : MethodId → DemandEdge → Prop}
  {emit : PFact → PFact → Excl → Option (PFact × Excl)}
  {sat : PFact → Excl → PFact → Excl → Bool}
  {restrict : PFact → Excl → XFact → DemandEdge → Option XFact}
  {recs : MethodId → PFact × Bool × Excl × XFact → Prop}
  {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId}

/-- The premise-layer motive on every object of `DRX` (no hypothesis; every emission, satisfaction,
    restriction and record set). The layer only rises along an edge (`transferX_demand`,
    `applyEdgeX_demand`, `applySummaryX_normal`, `cleanResX_demand`, `limitFX_normal`,
    `recLayerX_normal`), and a normal start fact is a must-premise (`startX`), a `$` premise, or an
    abstract `*` premise (`startFact`). -/
theorem DRX_premLayer {o : XObj}
    (h : DRX P taint counted L demand emit sat restrict recs sinks roots o) : PremLayerX o := by
  induction h with
  | root => trivial
  | @start M j mj jex _ _ =>
    intro hd
    cases mj with
    | true => exact Or.inr (Or.inr rfl)
    | false =>
      have hd' : (startFact j).demand = false := hd
      obtain ⟨ib, ip, ik, im⟩ := j
      cases ik with
      | exact => exact Or.inl rfl
      | any => cases im <;> cases hd'
      | star e =>
        cases im with
        | star => exact Or.inr (Or.inl rfl)
        | starEx x => exact Or.inr (Or.inl rfl)
        | conc t => cases hd'
  | step _ _ hf ih => exact fun hd => ih (AnyTaintExExact.transferX_demand hf hd)
  | reqStmt => trivial
  | pass _ _ _ ih => exact ih
  | added => trivial
  | initR => trivial
  | @ret M i mi iex n f n' c e1 a j mj jex g d g' r e2 r' _ _ _ ha _ _ _ _ _ hr _ hr' ihF _ _ =>
    intro hla
    have e0 := AnyTaintExExact.limitFX_normal hla
    have hra' : r'.af.demand = false := by rw [← e0]; exact hla
    have hra := AnyTaintExExact.applyEdgeX_demand hr' hra'
    obtain ⟨hrx, _⟩ := AnyTaintExExact.applySummaryX_normal hr hra
    exact ihF (AnyTaintExExact.applyEdgeX_demand ha (AnyTaintExExact.applyEdgeX_demand hrx hra))
  | @retRec M i mi iex n f n' c e1 a j mj jex g r e2 r' _ _ _ ha _ _ hr _ hr' ihF =>
    intro hla
    have e0 := AnyTaintExExact.limitFX_normal hla
    have hz : (recLayerX mj (sat j jex a.af.fact a.ex) r').af.demand = false := by
      rw [← e0]; exact hla
    have hra := AnyTaintExExact.applyEdgeX_demand hr' (recLayerX_normal hz)
    obtain ⟨hrx, _⟩ := AnyTaintExExact.applySummaryX_normal hr hra
    exact ihF (AnyTaintExExact.applyEdgeX_demand ha (AnyTaintExExact.applyEdgeX_demand hrx hra))
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial
  | clean _ _ hf ih => exact fun hd => ih (AnyTaintExExact.cleanResX_demand hf hd)
  | reqClean => trivial
  | filt _ _ _ ih => exact ih

#print axioms DRX_premLayer

/-- EVERY MUST-PREMISE OF A RESTRICTED RUN IS `[any-taint]`: it has the `.any` tail
    (`AnyTaintExExact.DRX_mustAny`, no hypothesis) and a concrete mark (`DRX_conc`). Hypothesis: the
    emission copies the mark of the added fact (`EmitCopiesMarkX`, C3; `emitX` has it). -/
theorem DRX_must_premise (hem : EmitCopiesMarkX emit) {M : MethodId} {j : PFact} {jex : Excl}
    (h : DRX P taint counted L demand emit sat restrict recs sinks roots (.init M j true jex)) :
    j.kind = .any ∧ ∃ t, j.mark = .conc t :=
  ⟨AnyTaintExExact.DRX_mustAny h, AnyTaintExExact.DRX_conc hem h⟩

#print axioms DRX_must_premise

/-- THE PREMISE OF A NORMAL EDGE OF A RESTRICTED RUN (`RExact.complete_premise_exact` for `DRX`;
    ap.md §6.5 with F69, DESIGN §6 A2): a NORMAL edge of `DRX` has either a `$` premise (not must),
    or a MUST-PREMISE, which has the `.any` tail and a concrete mark (`[any-taint]`, possibly with an
    exclusion). In particular a normal edge never has a non-must `.any` premise or a `*` premise.
    Hypothesis: `EmitCopiesMarkX emit` (C3; the run is concrete, `DRX_conc`). The layer only rises
    along an edge, and a normal start fact is a must-premise or a `$` premise (`startFact` of a
    concrete `.any` or `*` premise is demand). -/
theorem DRX_normal_premise (hem : EmitCopiesMarkX emit) {M : MethodId} {i : PFact} {mi : Bool}
    {iex : Excl} {n : Node} {f : XFact}
    (h : DRX P taint counted L demand emit sat restrict recs sinks roots (.edge M i mi iex n f))
    (hd : f.af.demand = false) :
    (i.kind = .exact ∧ mi = false) ∨ (mi = true ∧ i.kind = .any ∧ ∃ t, i.mark = .conc t) := by
  have hc0 : AnyTaintExExact.ConcObjX (.edge M i mi iex n f) := AnyTaintExExact.DRX_conc hem h
  obtain ⟨hc, _, _⟩ := hc0
  cases mi with
  | true => exact Or.inr ⟨rfl, AnyTaintExExact.DRX_mustAny h, hc⟩
  | false =>
    rcases DRX_premLayer h hd with hk | ha | hm
    · exact Or.inl ⟨hk, rfl⟩
    · rw [AnyTaintExact.absB_conc hc] at ha; cases ha
    · cases hm

#print axioms DRX_normal_premise

end RunX

/-- `DRX_normal_premise` for the spec instance `DRXs` (`emitX`, `satX`, `restrictX`): no
    hypothesis. -/
theorem DRXs_normal_premise {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop} {recs : MethodId → PFact × Bool × Excl × XFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    {M : MethodId} {i : PFact} {mi : Bool} {iex : Excl} {n : Node} {f : XFact}
    (h : DRXs P taint counted L demand recs sinks roots (.edge M i mi iex n f))
    (hd : f.af.demand = false) :
    (i.kind = .exact ∧ mi = false) ∨ (mi = true ∧ i.kind = .any ∧ ∃ t, i.mark = .conc t) :=
  DRX_normal_premise emitX_copies h hd

#print axioms DRXs_normal_premise

/-- `DRX_must_premise` for the spec instance `DRXs`: no hypothesis. -/
theorem DRXs_must_premise {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop} {recs : MethodId → PFact × Bool × Excl × XFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    {M : MethodId} {j : PFact} {jex : Excl}
    (h : DRXs P taint counted L demand recs sinks roots (.init M j true jex)) :
    j.kind = .any ∧ ∃ t, j.mark = .conc t :=
  DRX_must_premise emitX_copies h

#print axioms DRXs_must_premise

/-! ## 4. The simulation of run 1 (`Sim6X`, under `NoBelowCleaner`)

  Every object of `D6X` has a `D6T` object with the same base fact (`Refines6`). The proof is one
  induction on `D6X` with the per-fact relation `RelX x f`: `W6.LE x.af f` (the same fact, the base
  layer the same or raised, a `*` fact in the same layer) and "an annotated conclusion is a base
  demand conclusion". The local lemmas follow the base operations through `W6.applyEdge_LL`,
  `W6.transfer_LL`, `W6.cleanRes_LL`; the new part is the EXCLUSION side: a result exclusion is
  non-empty only where the base demotes (a `keep` row with a non-empty edge exclusion) or where an
  input exclusion is non-empty (the input, the premise or the conclusion of the edge), and those are
  base demand facts. -/

/-- The emptiness of a union. -/
theorem isEmptyB_union (a b : Excl) : (a.union b).isEmptyB = (a.isEmptyB && b.isEmptyB) := by
  cases a with
  | univ => rfl
  | set xs =>
    cases b with
    | univ => cases xs <;> rfl
    | set ys => cases xs <;> cases ys <;> rfl

#print axioms isEmptyB_union

theorem layerX_fact (keep cd : Bool) (y : AFact) : (layerX keep cd y).fact = y.fact := by
  unfold layerX; cases keep && !cd <;> rfl

/-- A normal `.any` result of the normal form is a normal `.any` fact before it. -/
theorem norm_any_normal {b : Base} {p : List Acc} {k : Kind} {m : MarkA} {d : Bool}
    (hk : (AFact.norm ⟨⟨b, p, k, m⟩, d⟩).fact.kind = .any)
    (hd : (AFact.norm ⟨⟨b, p, k, m⟩, d⟩).demand = false) : k = .any ∧ d = false := by
  cases k with
  | exact => cases hk
  | any => exact ⟨rfl, hd⟩
  | star e =>
    cases e <;> cases m <;> cases d <;> first | (cases hk; done) | (cases hd; done)

#print axioms norm_any_normal

/-- The case below at the premise with a `*` target gives a NORMAL `.any` result only if the edge
    exclusion is empty. -/
theorem belowCase_nil_star_any {ck fk : Kind} {tp p : List Acc} {et : Excl}
    (h : belowCase ck fk [] tp (.star et) = some (p, .any, false)) :
    ((tailExcl fk).union et).isEmptyB = true := by
  unfold belowCase at h
  rw [if_pos (AnyTaintExExact.admitsTailB_nil fk)] at h
  dsimp only at h
  cases ck with
  | exact => cases h
  | star ec => cases h
  | any =>
    cases hex : (tailExcl fk).union et with
    | univ => rw [hex] at h; cases h
    | set xs =>
      rw [hex] at h
      cases xs with
      | nil => rfl
      | cons a xs =>
        have h2 := congrArg (fun x => x.2.2) (Option.some.inj h)
        cases h2

#print axioms belowCase_nil_star_any

/-- The case above with a `*` target gives a NORMAL result only if the edge exclusion is empty. -/
theorem aboveCase_star_any {ck fk : Kind} {r tp p : List Acc} {et : Excl}
    (h : aboveCase ck fk r tp (.star et) = some (p, .any, false)) :
    ((tailExcl fk).union et).isEmptyB = true := by
  unfold aboveCase at h
  cases hA : admitsTailB ck r with
  | false => rw [hA, if_neg Bool.false_ne_true] at h; cases h
  | true =>
    rw [hA, if_pos rfl] at h
    dsimp only at h
    have h2 : (!(ck.isAny && ((tailExcl fk).union et).isEmptyB)) = false :=
      congrArg (fun x => x.2.2) (Option.some.inj h)
    cases hb : ((tailExcl fk).union et).isEmptyB with
    | true => rfl
    | false => rw [hb, Bool.and_false] at h2; cases h2

#print axioms aboveCase_star_any

/-- THE EXCLUSION ROWS AGAINST THE BASE GEOMETRY: if the base geometry gives a NORMAL `.any`
    result (`ap = false`) and the input, the premise and the target carry no exclusion, then the
    result exclusion of `annX` is empty. (So a non-empty result exclusion comes from an input
    exclusion or from an edge exclusion that the base reads as a demotion.) -/
theorem annX_geo_ex {c : XFact} {fr to : PFact} {fex tex : Excl} {keep : Bool} {ex : Excl}
    {p : List Acc} {ap : Bool}
    (ha : annX c fr fex to tex = some (keep, ex))
    (hg : CoreAux.geo c.af.fact.kind fr.kind fr.path c.af.fact.path to.path to.kind =
      some (p, .any, ap))
    (hce : c.ex.isEmptyB = true) (hfe : fex.isEmptyB = true) (hte : tex.isEmptyB = true)
    (hap : ap = false) : ex.isEmptyB = true := by
  subst hap
  unfold CoreAux.geo at hg
  unfold annX at ha
  cases hrel : relate fr.path c.af.fact.path with
  | apart => rw [hrel] at hg; cases hg
  | below r =>
    rw [hrel] at hg ha
    dsimp only at hg ha
    cases r with
    | nil =>
      dsimp only at ha
      cases hto : to.kind with
      | star et =>
        rw [hto] at ha hg
        cases ha
        have h1 := belowCase_nil_star_any hg
        rw [isEmptyB_union] at h1
        rw [isEmptyB_union, isEmptyB_union, isEmptyB_union, hce, hfe]
        cases h3 : (tailExcl fr.kind).isEmptyB <;> cases h4 : et.isEmptyB <;>
          rw [h3, h4] at h1 <;> first | rfl | cases h1
      | any => rw [hto] at ha; cases ha; exact hte
      | exact => rw [hto] at ha; cases ha; rfl
    | cons a r' =>
      dsimp only at ha
      cases hf : fex.admits (a :: r') with
      | false => rw [hf, if_neg Bool.false_ne_true] at ha; cases ha
      | true =>
        rw [hf, if_pos rfl] at ha
        cases hto : to.kind with
        | star et => rw [hto] at ha; cases ha; exact hce
        | any => rw [hto] at ha; cases ha; exact hte
        | exact => rw [hto] at ha; cases ha; rfl
  | above r =>
    rw [hrel] at hg ha
    dsimp only at hg ha
    cases hf : c.ex.admits r with
    | false => rw [hf, if_neg Bool.false_ne_true] at ha; cases ha
    | true =>
      rw [hf, if_pos rfl] at ha
      cases hto : to.kind with
      | star et =>
        rw [hto] at ha hg
        cases ha
        have h1 := aboveCase_star_any hg
        rw [isEmptyB_union] at h1
        rw [isEmptyB_union, isEmptyB_union, hfe]
        cases h3 : (tailExcl fr.kind).isEmptyB <;> cases h4 : et.isEmptyB <;>
          rw [h3, h4] at h1 <;> first | rfl | cases h1
      | any => rw [hto] at ha; cases ha; exact hte
      | exact => rw [hto] at ha; cases ha; rfl

#print axioms annX_geo_ex

/-- THE PER-OPERATION RELATION of the core operation, with the exclusion: a refined result lies in
    `W6.LE` below the base result on the base input, and a non-empty result exclusion comes from a
    base DEMAND result or from an exclusion of the input, of the premise or of the target. -/
theorem applyEdgeX_LE {c x : XFact} {fr to : PFact} {fex tex : Excl}
    (hx : x ∈ (applyEdgeX c fr fex to tex).facts) :
    ∃ y, y ∈ (applyEdge c.af fr to).facts ∧ W6.LE x.af y ∧
      (x.ex.isEmptyB = false → y.demand = true ∨ c.ex.isEmptyB = false ∨
        fex.isEmptyB = false ∨ tex.isEmptyB = false) ∧
      (Exact.absB x.af.fact.mark = true → x.af = y) := by
  unfold applyEdgeX at hx
  cases ha : annX c fr fex to tex with
  | none => rw [ha] at hx; exact absurd hx List.not_mem_nil
  | some pr =>
    obtain ⟨keep, ex⟩ := pr
    rw [ha] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    refine ⟨y, hy, ?_, ?_, ?_⟩
    · rw [normX_af]
      unfold layerX
      cases hk : (keep && !c.af.demand) with
      | false => rw [if_neg Bool.false_ne_true]; exact W6.LE.refl y
      | true =>
        rw [if_pos rfl]
        have hkeep : keep = true := ((Bool.and_eq_true _ _).mp hk).1
        subst hkeep
        have hns := applyEdge_any_nonstar (keepB_any (annX_keep ha)) hy
        refine W6.LE.of_nonstar rfl hns (fun h => ?_)
        cases h
    · intro hex
      have hz : carriesB (layerX keep c.af.demand y) = true ∧ ex.isEmptyB = false := by
        cases hc : carriesB (layerX keep c.af.demand y) with
        | true =>
          rw [normX_of_carries (x := ⟨layerX keep c.af.demand y, ex⟩) hc] at hex
          exact ⟨rfl, hex⟩
        | false =>
          rw [normX_of_not (x := ⟨layerX keep c.af.demand y, ex⟩) hc] at hex
          cases hex
      obtain ⟨hk, _, _⟩ := carriesB_parts hz.1
      rw [layerX_fact] at hk
      cases hyd : y.demand with
      | true => exact Or.inl rfl
      | false =>
        right
        cases hce : c.ex.isEmptyB with
        | false => exact Or.inl rfl
        | true =>
          cases hfe : fex.isEmptyB with
          | false => exact Or.inr (Or.inl rfl)
          | true =>
            cases hte : tex.isEmptyB with
            | false => exact Or.inr (Or.inr rfl)
            | true =>
              exfalso
              obtain ⟨_, p, k, ap, m, hg, _, _, hyeq⟩ := AnyTaintExExact.applyEdge_full hy
              rw [hyeq] at hk hyd
              obtain ⟨hk', hd'⟩ := norm_any_normal hk hyd
              subst hk'
              have hap : ap = false := (Exact.or_eq_false hd').2
              have h1 := annX_geo_ex ha hg hce hfe hte hap
              rw [hz.2] at h1
              cases h1
    · intro habs
      rw [normX_af] at habs ⊢
      unfold layerX at habs ⊢
      cases hk : (keep && !c.af.demand) with
      | false => rw [if_neg Bool.false_ne_true]
      | true =>
        exfalso
        rw [hk, if_pos rfl] at habs
        have hkeep : keep = true := ((Bool.and_eq_true _ _).mp hk).1
        subst hkeep
        obtain ⟨_, t, ht⟩ := AnyTaintExExact.keepB_parts (annX_keep ha)
        obtain ⟨t', ht'⟩ := applyEdge_mark_conc ht hy
        have h2 : Exact.absB y.fact.mark = true := habs
        rw [ht'] at h2
        cases h2

#print axioms applyEdgeX_LE

/-- THE PER-FACT RELATION of the simulation: the base fact is the refined fact in the same or a
    raised layer (a `*` fact in the same layer, `W6.LE`), and an annotated refined fact is a base
    DEMAND fact. -/
def RelX (x : XFact) (f : AFact) : Prop :=
  W6.LE x.af f ∧ (x.ex.isEmptyB = false → f.demand = true)

/-- The core operation under `RelX`: the base result on the related base input. -/
theorem applyEdgeX_rel {c x : XFact} {c' : AFact} {fr to : PFact} {fex tex : Excl}
    (hc : RelX c c') (hx : x ∈ (applyEdgeX c fr fex to tex).facts) :
    ∃ y', y' ∈ (applyEdge c' fr to).facts ∧ W6.LE x.af y' ∧
      (x.ex.isEmptyB = false → y'.demand = true ∨ fex.isEmptyB = false ∨
        tex.isEmptyB = false) := by
  obtain ⟨y, hy, hle, hex, _⟩ := applyEdgeX_LE hx
  obtain ⟨y', hy', hle'⟩ := (W6.applyEdge_LL hc.1).1.fwd hy
  refine ⟨y', hy', AnyTaintSim.LE_trans hle hle', fun he => ?_⟩
  rcases hex he with h1 | h1 | h1 | h1
  · exact Or.inl (hle'.dem h1)
  · exact Or.inl (Invariant.applyEdge_demand_monotone (hc.2 h1) hy')
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h1)

#print axioms applyEdgeX_rel

/-- A call binding or a statement micro edge under `RelX`. -/
theorem bindX_rel {c x : XFact} {c' : AFact} {e : MicroEdge} (hc : RelX c c')
    (hx : x ∈ (bindX c e).facts) : ∃ y', y' ∈ (applyEdge c' e.1 e.2).facts ∧ RelX x y' := by
  obtain ⟨y', hy', hle, hex⟩ := applyEdgeX_rel hc hx
  refine ⟨y', hy', hle, fun he => ?_⟩
  rcases hex he with h | h | h
  · exact h
  · cases h
  · cases h

#print axioms bindX_rel

/-- A result of one micro edge with W6T is a result of `applyAllT`. -/
theorem applyAllT_mem_of {taint : TaintEdges} {c y : AFact} :
    ∀ {es : List MicroEdge} {e : MicroEdge}, e ∈ es → y ∈ (applyEdge c e.1 e.2).facts →
      w6t taint e y ∈ (applyAllT taint c es).facts
  | [], _, he, _ => absurd he List.not_mem_nil
  | e0 :: es, e, he, hy => by
    show w6t taint e y ∈ (applyEdge c e0.1 e0.2).facts.map (w6t taint e0) ++
      (applyAllT taint c es).facts
    rcases List.mem_cons.mp he with rfl | he'
    · exact List.mem_append_left _ (List.mem_map_of_mem (f := w6t taint e) hy)
    · exact List.mem_append_right _ (applyAllT_mem_of he' hy)

#print axioms applyAllT_mem_of

/-- W6T under `RelX` (the same micro edge on both sides). -/
theorem w6tX_rel {taint : TaintEdges} {e : MicroEdge} {z : XFact} {y : AFact} (h : RelX z y) :
    RelX (w6tX taint e z) (w6t taint e y) := by
  unfold w6tX w6t
  cases hb : (e.2.kind.isAny && !taint e) with
  | true =>
    rw [if_pos rfl, if_pos rfl]
    have hf : y.fact = z.af.fact := h.1.fact.symm
    refine ⟨?_, fun he => by cases he⟩
    show W6.LE ⟨z.af.fact, true⟩ ⟨y.fact, true⟩
    rw [hf]; exact W6.LE.refl _
  | false => rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]; exact h

#print axioms w6tX_rel

/-- The field limit under `RelX`. -/
theorem limitFX_rel {counted : Acc → Bool} {L : Nat} {z : XFact} {y : AFact} (h : RelX z y) :
    RelX (limitFX counted L z) (limitF counted L y) := by
  refine ⟨by rw [limitFX_af]; exact W6.limitF_LE h.1, fun he => ?_⟩
  have hf : y.fact = z.af.fact := h.1.fact.symm
  unfold limitFX at he
  cases hc : cutPath counted L z.af.fact.path with
  | none =>
    rw [hc] at he
    have hy : limitF counted L y = y := by unfold limitF; rw [hf, hc]
    rw [hy]; exact h.2 he
  | some p => rw [hc] at he; cases he

#print axioms limitFX_rel

/-- The refined cleaner without the `below` row, case by case for the simulation: a result of the
    base cleaner on the base fact with the input exclusion or none; or the input itself in the
    excluded part (`cleanPosX` disjoint, the input exclusion non-empty); or the `atAndBelow` row
    one accessor below an `[any-taint]` fact (the base gives `concPart`). -/
theorem cleanResX_cases_rel {cl : Cleaner} {c x : XFact} (hnb : cl.reach ≠ .below)
    (h : x ∈ (cleanResX cl c).facts) :
    (x.af ∈ (cleanRes cl c.af).facts ∧ (x.ex = c.ex ∨ x.ex = Excl.empty)) ∨
    (x.af = c.af ∧ x.ex = c.ex ∧ ∃ r, relate cl.path c.af.fact.path = .above r ∧
      c.ex.admits r = false) ∨
    (x.af = c.af ∧ carriesB c.af = true ∧ cl.reach = .atAndBelow ∧
      cleanPos cl c.af.fact = .part ∧ ∃ t, c.af.fact.mark = .conc t ∧ cl.markB t = true) := by
  unfold cleanResX at h
  rcases cleanPosX_cases cl c with hp | ⟨hp, r, hr, hadm⟩
  · unfold cleanRes
    rw [← hp]
    cases hq : cleanPosX cl c with
    | disjoint =>
      rw [hq] at h
      rw [List.mem_singleton.mp h]
      exact Or.inl ⟨List.mem_singleton.mpr rfl, Or.inl rfl⟩
    | inside =>
      rw [hq] at h
      dsimp only at h ⊢
      revert h
      cases hm : c.af.fact.mark with
      | conc t =>
        intro h
        dsimp only at h ⊢
        cases hb : cl.markB t with
        | true => rw [hb, if_pos rfl] at h; exact absurd h List.not_mem_nil
        | false =>
          rw [hb, if_neg Bool.false_ne_true] at h
          rw [if_neg Bool.false_ne_true, List.mem_singleton.mp h]
          exact Or.inl ⟨List.mem_singleton.mpr rfl, Or.inl rfl⟩
      | star =>
        cases hcm : cl.mark with
        | none => intro h; exact absurd h List.not_mem_nil
        | some t =>
          intro h
          rw [List.mem_singleton.mp h]
          exact Or.inl ⟨List.mem_singleton.mpr rfl, Or.inl rfl⟩
      | starEx xs =>
        cases hcm : cl.mark with
        | none => intro h; exact absurd h List.not_mem_nil
        | some t =>
          intro h
          rw [List.mem_singleton.mp h]
          exact Or.inl ⟨List.mem_singleton.mpr rfl, Or.inl rfl⟩
    | part =>
      rw [hq] at h
      dsimp only at h ⊢
      revert h
      cases hm : c.af.fact.mark with
      | conc t =>
        intro h
        dsimp only at h ⊢
        cases hb : cl.markB t with
        | true =>
          rw [hb, if_pos rfl] at h
          rw [if_pos rfl]
          have hbase : x = ⟨concPart cl c.af, Excl.empty⟩ →
              (x.af ∈ [concPart cl c.af] ∧ (x.ex = c.ex ∨ x.ex = Excl.empty)) := by
            intro e; rw [e]; exact ⟨List.mem_singleton.mpr rfl, Or.inr rfl⟩
          unfold partX at h
          cases hcar : carriesB c.af with
          | false =>
            rw [hcar, if_neg Bool.false_ne_true] at h
            exact Or.inl (hbase (List.mem_singleton.mp h))
          | true =>
            rw [hcar, if_pos rfl] at h
            revert h
            cases hrch : cl.reach with
            | below => exact absurd hrch hnb
            | exact => intro h; exact Or.inl (hbase (List.mem_singleton.mp h))
            | atAndBelow =>
              cases hrl : relate cl.path c.af.fact.path with
              | above r =>
                cases r with
                | nil => intro h; exact Or.inl (hbase (List.mem_singleton.mp h))
                | cons f r' =>
                  cases r' with
                  | nil =>
                    intro h
                    rw [List.mem_singleton.mp h]
                    exact Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl, t, rfl, hb⟩)
                  | cons g r'' => intro h; exact Or.inl (hbase (List.mem_singleton.mp h))
              | below r => intro h; exact Or.inl (hbase (List.mem_singleton.mp h))
              | apart => intro h; exact Or.inl (hbase (List.mem_singleton.mp h))
        | false =>
          rw [hb, if_neg Bool.false_ne_true] at h
          rw [if_neg Bool.false_ne_true, List.mem_singleton.mp h]
          exact Or.inl ⟨List.mem_singleton.mpr rfl, Or.inl rfl⟩
      | star =>
        cases hcm : cl.mark with
        | none =>
          intro h
          rw [List.mem_singleton.mp h]
          exact Or.inl ⟨List.mem_singleton.mpr rfl, Or.inr rfl⟩
        | some t =>
          intro h
          rw [List.mem_singleton.mp h]
          exact Or.inl ⟨List.mem_singleton.mpr rfl, Or.inl rfl⟩
      | starEx xs =>
        cases hcm : cl.mark with
        | none =>
          intro h
          rw [List.mem_singleton.mp h]
          exact Or.inl ⟨List.mem_singleton.mpr rfl, Or.inr rfl⟩
        | some t =>
          intro h
          rw [List.mem_singleton.mp h]
          exact Or.inl ⟨List.mem_singleton.mpr rfl, Or.inl rfl⟩
  · rw [hp] at h
    rw [List.mem_singleton.mp h]
    exact Or.inr (Or.inl ⟨rfl, rfl, r, hr, hadm⟩)

#print axioms cleanResX_cases_rel

/-- An empty exclusion admits every continuation. -/
theorem admits_of_isEmptyB {e : Excl} (h : e.isEmptyB = true) (r : List Acc) : e.admits r = true := by
  cases e with
  | univ => cases h
  | set xs =>
    cases xs with
    | nil => exact admits_empty r
    | cons a xs => cases h

/-- The refined cleaner (no `below` row) under `RelX`. -/
theorem cleanResX_rel {cl : Cleaner} {c x : XFact} {c' : AFact} (hc : RelX c c') (hw : WFX c)
    (hnb : cl.reach ≠ .below) (hx : x ∈ (cleanResX cl c).facts) :
    ∃ y', y' ∈ (cleanRes cl c').facts ∧ RelX x y' := by
  have hf : c'.fact = c.af.fact := hc.1.fact.symm
  rcases cleanResX_cases_rel hnb hx with
    ⟨h1, h2⟩ | ⟨h1, _, r, hr, hadm⟩ | ⟨h1, hcar, hrch, hpos, t, hm, hb⟩
  · obtain ⟨y', hy', hle⟩ := (W6.cleanRes_LL hc.1).1.fwd h1
    refine ⟨y', hy', hle, fun he => ?_⟩
    rcases h2 with h2 | h2
    · rw [h2] at he
      exact Invariant.cleanRes_demand_monotone (hc.2 he) hy'
    · rw [h2] at he; cases he
  · have hcar := carriesB_of_ex hw hadm
    obtain ⟨hk, _, _⟩ := carriesB_parts hcar
    have hce : c.ex.isEmptyB = false := by
      cases hce : c.ex.isEmptyB with
      | false => rfl
      | true => rw [admits_of_isEmptyB hce r] at hadm; cases hadm
    have hcd : c'.demand = true := hc.2 hce
    obtain ⟨y, hy, hfy, _⟩ := cleanRes_above_any hcar hr
    obtain ⟨y', hy', hle⟩ := (W6.cleanRes_LL hc.1).1.fwd hy
    have hyd : y'.demand = true := Invariant.cleanRes_demand_monotone hcd hy'
    refine ⟨y', hy', ⟨?_, fun _ => hyd⟩⟩
    rw [h1]
    refine W6.LE.of_nonstar (hfy.trans hle.fact) (by rw [hk]; rfl) (fun _ => hyd)
  · obtain ⟨hk, _, _⟩ := carriesB_parts hcar
    have hmem : concPart cl c' ∈ (cleanRes cl c').facts := by
      unfold cleanRes
      rw [hf, hpos]
      dsimp only
      rw [hm]
      dsimp only
      rw [hb, if_pos rfl]
      exact List.mem_singleton.mpr rfl
    have hcp : concPart cl c' = ⟨c'.fact, true⟩ := by
      unfold concPart
      rw [hf, hk, hrch]
    refine ⟨concPart cl c', hmem, ⟨?_, fun _ => by rw [hcp]⟩⟩
    rw [hcp, h1, hf]
    exact W6.LE.raise (by rw [hk]; rfl)

#print axioms cleanResX_rel

/-- The requests of the refined cleaner are base requests. -/
theorem cleanResX_reqs {cl : Cleaner} {c : XFact} {t : Mark} (h : t ∈ (cleanResX cl c).reqs) :
    t ∈ (cleanRes cl c.af).reqs := by
  unfold cleanResX at h
  rcases cleanPosX_cases cl c with hp | ⟨hp, _⟩
  · unfold cleanRes
    rw [← hp]
    cases hq : cleanPosX cl c with
    | disjoint => rw [hq] at h; exact absurd h List.not_mem_nil
    | inside =>
      rw [hq] at h
      dsimp only at h ⊢
      revert h
      cases hm : c.af.fact.mark with
      | conc t0 =>
        intro h
        dsimp only at h
        cases hb : cl.markB t0 with
        | true => rw [hb, if_pos rfl] at h; exact absurd h List.not_mem_nil
        | false => rw [hb, if_neg Bool.false_ne_true] at h; exact absurd h List.not_mem_nil
      | star =>
        cases hcm : cl.mark with
        | none => intro h; exact absurd h List.not_mem_nil
        | some t0 => intro h; exact absurd h List.not_mem_nil
      | starEx xs =>
        cases hcm : cl.mark with
        | none => intro h; exact absurd h List.not_mem_nil
        | some t0 => intro h; exact absurd h List.not_mem_nil
    | part =>
      rw [hq] at h
      dsimp only at h ⊢
      revert h
      cases hm : c.af.fact.mark with
      | conc t0 =>
        intro h
        dsimp only at h
        cases hb : cl.markB t0 with
        | true => rw [hb, if_pos rfl] at h; exact absurd h List.not_mem_nil
        | false => rw [hb, if_neg Bool.false_ne_true] at h; exact absurd h List.not_mem_nil
      | star =>
        cases hcm : cl.mark with
        | none => intro h; exact absurd h List.not_mem_nil
        | some t0 => intro h; exact h
      | starEx xs =>
        cases hcm : cl.mark with
        | none => intro h; exact absurd h List.not_mem_nil
        | some t0 => intro h; exact h
  · rw [hp] at h; exact absurd h List.not_mem_nil

#print axioms cleanResX_reqs

/-! ### The strengthened relation: an abstract-mark fact has the SAME layer in both runs

  The refined layer differs from the base layer only below an `[any-taint]` fact (a `keep` row of
  `annX`, a `partX` row), which has a concrete mark, and every result of a concrete-mark fact has
  a concrete mark. So an abstract-mark refined fact IS its base fact (`RelA`). This removes the
  hypothesis of `W6.applySummary_LL` (a `*` result of a summary application has an abstract mark,
  so its summary edge has an abstract mark, so the two summary edges are the same). -/

/-- An abstract mark is not concrete. -/
theorem conc_of_absB_false {m : MarkA} (h : Exact.absB m = false) : ∃ t, m = .conc t := by
  cases m with
  | conc t => exact ⟨t, rfl⟩
  | star => cases h
  | starEx xs => cases h

/-- An abstract-mark result of the core operation has an abstract-mark input and target. -/
theorem applyEdge_abs_inv {c r : AFact} {fr to : PFact} (hr : r ∈ (applyEdge c fr to).facts)
    (h : Exact.absB r.fact.mark = true) :
    Exact.absB c.fact.mark = true ∧ Exact.absB to.mark = true := by
  refine ⟨?_, ?_⟩
  · cases hc : Exact.absB c.fact.mark with
    | true => rfl
    | false =>
      obtain ⟨t, ht⟩ := conc_of_absB_false hc
      obtain ⟨t', ht'⟩ := applyEdge_mark_conc ht hr
      rw [ht'] at h; cases h
  · cases ht : Exact.absB to.mark with
    | true => rfl
    | false =>
      obtain ⟨t, ht⟩ := conc_of_absB_false ht
      obtain ⟨_, p, k, ap, m, _, _, hm, rfl⟩ := AnyTaintExExact.applyEdge_full hr
      rw [ht] at hm
      have e := AnyTaintExExact.markComp_conc_target hm
      rw [CoreAux.norm_mark] at h
      rw [show (⟨⟨to.base, p, k, m⟩, c.demand || ap⟩ : AFact).fact.mark = m from rfl, e] at h
      cases h

#print axioms applyEdge_abs_inv

/-- The strengthened relation: `RelX`, and an abstract-mark refined fact is its base fact. -/
def RelA (x : XFact) (f : AFact) : Prop :=
  RelX x f ∧ (Exact.absB x.af.fact.mark = true → x.af = f)

/-- The core operation under `RelA`. -/
theorem applyEdgeX_relA {c x : XFact} {c' : AFact} {fr to : PFact} {fex tex : Excl}
    (hc : RelA c c') (hx : x ∈ (applyEdgeX c fr fex to tex).facts) :
    ∃ y', y' ∈ (applyEdge c' fr to).facts ∧ W6.LE x.af y' ∧
      (x.ex.isEmptyB = false → y'.demand = true ∨ fex.isEmptyB = false ∨
        tex.isEmptyB = false) ∧
      (Exact.absB x.af.fact.mark = true → x.af = y') := by
  cases habs : Exact.absB c.af.fact.mark with
  | true =>
    have e : c.af = c' := hc.2 habs
    obtain ⟨y, hy, hle, hex, hab⟩ := applyEdgeX_LE hx
    refine ⟨y, by rw [← e]; exact hy, hle, fun he => ?_, hab⟩
    rcases hex he with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · have hcd : c'.demand = true := hc.1.2 h1
      rw [← e] at hcd
      exact Or.inl (Invariant.applyEdge_demand_monotone hcd hy)
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)
  | false =>
    obtain ⟨y', hy', hle, hex⟩ := applyEdgeX_rel hc.1 hx
    refine ⟨y', hy', hle, hex, fun hxa => ?_⟩
    exfalso
    obtain ⟨y, hy, hxy, _⟩ := applyEdgeX_base hx
    rw [hxy] at hxa
    have h2 := (applyEdge_abs_inv hy hxa).1
    rw [habs] at h2
    cases h2

#print axioms applyEdgeX_relA

/-- A call binding or a statement micro edge under `RelA`. -/
theorem bindX_relA {c x : XFact} {c' : AFact} {e : MicroEdge} (hc : RelA c c')
    (hx : x ∈ (bindX c e).facts) : ∃ y', y' ∈ (applyEdge c' e.1 e.2).facts ∧ RelA x y' := by
  obtain ⟨y', hy', hle, hex, hab⟩ := applyEdgeX_relA hc hx
  refine ⟨y', hy', ⟨hle, fun he => ?_⟩, hab⟩
  rcases hex he with h | h | h
  · exact h
  · cases h
  · cases h

#print axioms bindX_relA

theorem w6tX_relA {taint : TaintEdges} {e : MicroEdge} {z : XFact} {y : AFact} (h : RelA z y) :
    RelA (w6tX taint e z) (w6t taint e y) := by
  refine ⟨w6tX_rel h.1, fun habs => ?_⟩
  rw [w6tX_af] at habs ⊢
  rw [w6t_fact] at habs
  rw [h.2 habs]

#print axioms w6tX_relA

theorem limitFX_relA {counted : Acc → Bool} {L : Nat} {z : XFact} {y : AFact} (h : RelA z y) :
    RelA (limitFX counted L z) (limitF counted L y) := by
  refine ⟨limitFX_rel h.1, fun habs => ?_⟩
  rw [limitFX_af] at habs ⊢
  rw [Exact.limitF_mark] at habs
  rw [h.2 habs]

#print axioms limitFX_relA

/-- The refined statement transfer under `RelA`. -/
theorem transferX_relA {taint : TaintEdges} {counted : Acc → Bool} {L : Nat} {s : Stmt}
    {c x : XFact} {c' : AFact} (hc : RelA c c') (hx : x ∈ (transferX taint counted L s c).facts) :
    ∃ y', y' ∈ (transferT taint counted L s c').facts ∧ RelA x y' := by
  have hf : c'.fact = c.af.fact := hc.1.1.fact.symm
  unfold transferX at hx
  unfold transferT
  rw [hf]
  cases hm : memB c.af.fact.base s.touched with
  | false =>
    rw [hm, if_neg Bool.false_ne_true] at hx
    rw [if_neg Bool.false_ne_true]
    rw [List.mem_singleton.mp hx]
    exact ⟨c', List.mem_singleton.mpr rfl, hc⟩
  | true =>
    rw [hm, if_pos rfl] at hx
    rw [if_pos rfl]
    obtain ⟨z0, hz0, rfl⟩ := List.mem_map.mp hx
    obtain ⟨e, he, hz⟩ := AnyTaintExExact.applyAllXT_mem hz0
    obtain ⟨z, hzb, rfl⟩ := List.mem_map.mp hz
    obtain ⟨y', hy', hr⟩ := bindX_relA hc hzb
    exact ⟨limitF counted L (w6t taint e y'),
      List.mem_map_of_mem (f := limitF counted L) (applyAllT_mem_of he hy'),
      limitFX_relA (w6tX_relA hr)⟩

#print axioms transferX_relA

/-- The refined summary application of run 1 (no premise exclusion) under `RelA`, with no
    hypothesis: a `*` result has an abstract mark, so the summary edge has an abstract mark and is
    the same on both sides. -/
theorem applySummaryX_relA {a g x : XFact} {a' g' : AFact} {j : PFact}
    (ha : RelA a a') (hg : RelA g g') (hx : x ∈ (applySummaryX a j Excl.empty g).facts) :
    ∃ y', y' ∈ (applySummary a' j g').facts ∧ RelA x y' := by
  have hgf : g'.fact = g.af.fact := hg.1.1.fact.symm
  obtain ⟨x0, hx0, rfl⟩ := List.mem_map.mp hx
  obtain ⟨y0, hy0, hle, hex, hab⟩ := applyEdgeX_relA ha hx0
  have hy0' : y0 ∈ (applyEdge a' j g'.fact).facts := by rw [hgf]; exact hy0
  -- an abstract-mark `x0` has an abstract-mark summary conclusion, the same on both sides
  have hgabs : Exact.absB x0.af.fact.mark = true → g.af = g' := by
    intro h0
    obtain ⟨yb, hyb, hxyb, _⟩ := applyEdgeX_base hx0
    rw [hxyb] at h0
    exact hg.2 (applyEdge_abs_inv hyb h0).2
  -- a `*` refined result has an abstract mark (W2 of the base result with its fact)
  have hsabs : x0.af.fact.kind.isStar = true → Exact.absB x0.af.fact.mark = true := by
    intro hs
    obtain ⟨yb, hyb, hxyb, _⟩ := applyEdgeX_base hx0
    obtain ⟨e, he⟩ : ∃ e, x0.af.fact.kind = .star e := by
      cases hk : x0.af.fact.kind with
      | star e => exact ⟨e, rfl⟩
      | any => rw [hk] at hs; cases hs
      | exact => rw [hk] at hs; cases hs
    rw [hxyb] at he ⊢
    exact Kinds.absB_iff.mpr (Invariant.applyEdge_Legal hyb e he).1
  refine ⟨AFact.norm ⟨y0.fact, y0.demand || g'.demand⟩,
    List.mem_map_of_mem (f := fun x : AFact => AFact.norm (⟨x.fact, x.demand || g'.demand⟩ : AFact))
      hy0', ⟨?_, ?_⟩, ?_⟩
  · rw [normX_af]
    show W6.LE (AFact.norm ⟨x0.af.fact, x0.af.demand || g.af.demand⟩)
      (AFact.norm ⟨y0.fact, y0.demand || g'.demand⟩)
    cases hs : x0.af.fact.kind.isStar with
    | true =>
      have e1 : y0 = x0.af := hle.star_eq hs
      have e2 : g.af = g' := hgabs (hsabs hs)
      rw [e1, ← e2]; exact W6.LE.refl _
    | false =>
      have hys : y0.fact.kind.isStar = false := by rw [← hle.fact]; exact hs
      rw [Invariant.norm_id_of_nonstar (x := ⟨x0.af.fact, x0.af.demand || g.af.demand⟩) hs,
        Invariant.norm_id_of_nonstar (x := ⟨y0.fact, y0.demand || g'.demand⟩) hys]
      exact W6.LE.of_nonstar hle.fact hs (W6.bor_mono hle.dem hg.1.1.dem)
  · intro he
    have hx0e : x0.ex.isEmptyB = false := by
      unfold normX at he
      split at he
      · exact he
      · cases he
    rcases hex hx0e with h1 | h1 | h1
    · apply AnyTaintSim.norm_demand
      show (y0.demand || g'.demand) = true
      rw [h1]; rfl
    · cases h1
    · apply AnyTaintSim.norm_demand
      show (y0.demand || g'.demand) = true
      rw [hg.1.2 h1]; cases y0.demand <;> rfl
  · intro habs
    rw [normX_af] at habs ⊢
    rw [CoreAux.norm_mark] at habs
    have h0 : Exact.absB x0.af.fact.mark = true := habs
    have e1 : x0.af = y0 := hab h0
    have e2 : g.af = g' := hgabs h0
    show AFact.norm ⟨x0.af.fact, x0.af.demand || g.af.demand⟩ =
      AFact.norm ⟨y0.fact, y0.demand || g'.demand⟩
    rw [e1, e2]

#print axioms applySummaryX_relA

/-- The marks of the refined cleaner: a concrete input gives concrete results. -/
theorem cleanResX_conc {cl : Cleaner} {c x : XFact} {t : Mark} (hc : c.af.fact.mark = .conc t)
    (hx : x ∈ (cleanResX cl c).facts) : ∃ t', x.af.fact.mark = .conc t' := by
  rcases cleanResX_cases hx with e1 | e1 | ⟨_, _, e2, _⟩
  · exact ⟨t, by rw [e1]; exact hc⟩
  · exact cleanRes_mark_conc hc e1
  · exact ⟨t, by rw [e2]; exact hc⟩

#print axioms cleanResX_conc

/-- The refined cleaner (no `below` row) under `RelA`. -/
theorem cleanResX_relA {cl : Cleaner} {c x : XFact} {c' : AFact} (hc : RelA c c') (hw : WFX c)
    (hnb : cl.reach ≠ .below) (hx : x ∈ (cleanResX cl c).facts) :
    ∃ y', y' ∈ (cleanRes cl c').facts ∧ RelA x y' := by
  cases habs : Exact.absB c.af.fact.mark with
  | true =>
    have e : c.af = c' := hc.2 habs
    have hnc : ∀ t, c.af.fact.mark = .conc t → False := fun t ht => by rw [ht] at habs; cases habs
    have hce : c.ex = Excl.empty := hw (carriesB_of_mark hnc)
    rcases cleanResX_cases_rel hnb hx with ⟨h1, h2⟩ | ⟨_, _, r, _, hadm⟩ | ⟨_, hcar, _⟩
    · refine ⟨x.af, by rw [← e]; exact h1, ⟨W6.LE.refl _, fun he => ?_⟩, fun _ => rfl⟩
      rcases h2 with h2 | h2
      · rw [h2, hce] at he; cases he
      · rw [h2] at he; cases he
    · rw [hce, admits_empty] at hadm; cases hadm
    · obtain ⟨_, _, t, ht⟩ := carriesB_parts hcar
      exact (hnc t ht).elim
  | false =>
    obtain ⟨y', hy', hr⟩ := cleanResX_rel hc.1 hw hnb hx
    refine ⟨y', hy', hr, fun hxa => ?_⟩
    exfalso
    obtain ⟨t, ht⟩ := conc_of_absB_false habs
    obtain ⟨t', ht'⟩ := cleanResX_conc ht hx
    rw [ht'] at hxa
    cases hxa

#print axioms cleanResX_relA

/-- The motive of the simulation of run 1: the base run `R` has the object, an edge with a related
    base fact (`RelA`), a vulnerability in the same or a higher base layer. -/
def SimObj6 (R : Obj → Prop) : XObj6 → Prop
  | .init M i => R (.init M i)
  | .edge M i n x => ∃ f, R (.edge M i n f) ∧ RelA x f
  | .added M a => R (.added M a)
  | .req M i t => R (.req M i t)
  | .vuln M n s d => ∃ d', R (.vuln M n s d') ∧ (d = true → d' = true)

section Sim6
variable {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
  {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId}

/-- THE SIMULATION INVARIANT (one induction on `D6X`). Hypothesis: `NoBelowCleaner P` (the one
    rule whose result is not a base fact). Every abstraction, every taint edge set. -/
theorem D6X_sim (hnb : NoBelowCleaner P) {o : XObj6}
    (h : D6X P taint counted L α sinks roots o) :
    SimObj6 (D6T P taint counted L α sinks roots) o := by
  induction h with
  | root hM => exact D6T.root hM
  | @start M i _ ih =>
    exact ⟨startFact i, D6T.start ih, ⟨W6.LE.refl _, fun he => by cases he⟩, fun _ => rfl⟩
  | @step M i n f n' s f' _ hE hf ih =>
    obtain ⟨g, hg, hr⟩ := ih
    obtain ⟨g', hg', hr'⟩ := transferX_relA hr hf
    exact ⟨g', D6T.step hg hE hg', hr'⟩
  | @reqStmt M i n f n' s t _ hE ht ih =>
    obtain ⟨g, hg, hr⟩ := ih
    refine D6T.reqStmt hg hE ?_
    rw [transferT_reqs, ← (W6.transfer_LL hr.1.1).2, ← transferT_reqs taint]
    exact transferX_reqs ht
  | @pass M i n f n' c _ hE hm ih =>
    obtain ⟨g, hg, hr⟩ := ih
    exact ⟨g, D6T.pass hg hE (by rw [← hr.1.1.fact]; exact hm), hr⟩
  | @added M i n f n' c e a _ hE he ha ih =>
    obtain ⟨g, hg, hr⟩ := ih
    obtain ⟨a', ha', hra⟩ := bindX_relA hr ha
    show D6T P taint counted L α sinks roots (.added c.callee a.af.fact)
    rw [hra.1.1.fact]
    exact D6T.added hg hE he ha'
  | initA _ ih => exact D6T.initA ih
  | @ret M i n f n' c e1 a j g r e2 r' _ hE he1 ha _ happ _ hr he2 hr' ihF ihJ ihG =>
    obtain ⟨f6, hf6, hrf⟩ := ihF
    obtain ⟨g6, hg6, hrg⟩ := ihG
    obtain ⟨a6, ha6, hra⟩ := bindX_relA hrf ha
    obtain ⟨r6, hr6, hrr⟩ := applySummaryX_relA hra hrg hr
    obtain ⟨r6', hr6', hrr'⟩ := bindX_relA hrr hr'
    exact ⟨_, D6T.ret hf6 hE he1 ha6 ihJ (by rw [← hra.1.1.fact]; exact happ) hg6 hr6 he2 hr6',
      limitFX_relA hrr'⟩
  | @reqSink M i n f s t _ hs hc ih =>
    obtain ⟨g, hg, hr⟩ := ih
    exact D6T.reqSink hg hs (by rw [← W6.check_LE i s hr.1.1]; exact checkX_request hc)
  | answer _ _ hm ho ihR ihA => exact D6T.answer ihR ihA hm ho
  | @reqUp m j t M ic n f n' c e a _ _ hE hc he ha hcl ho ihR ihF =>
    obtain ⟨g, hg, hr⟩ := ihF
    obtain ⟨a', ha', hra⟩ := bindX_relA hr ha
    exact D6T.reqUp ihR hg hE hc he ha' (by rw [← hra.1.1.fact]; exact hcl)
      (by rw [← hra.1.1.fact]; exact overlapX_overlapB ho)
  | @vuln M i n f s _ hs hc ih =>
    obtain ⟨g, hg, hr⟩ := ih
    exact ⟨g.demand,
      D6T.vuln hg hs (by rw [← W6.check_LE i s hr.1.1]; exact checkX_triggered hc), hr.1.1.dem⟩
  | @clean M i n f n' cl f' hF hE hf ih =>
    obtain ⟨g, hg, hr⟩ := ih
    obtain ⟨g', hg', hr'⟩ :=
      cleanResX_relA hr (AnyTaintExExact.D6X_wf_edge hF) (hnb _ _ _ _ hE) hf
    exact ⟨g', D6T.clean hg hE hg', hr'⟩
  | @reqClean M i n f n' cl t _ hE ht ih =>
    obtain ⟨g, hg, hr⟩ := ih
    exact D6T.reqClean hg hE (by rw [← (W6.cleanRes_LL hr.1.1).2]; exact cleanResX_reqs ht)
  | @filt M i n f n' b may _ hE hp ih =>
    obtain ⟨g, hg, hr⟩ := ih
    exact ⟨g, D6T.filt hg hE (by rw [← hr.1.1.fact]; exact hp), hr⟩

#print axioms D6X_sim

/-- THE SIMULATION OF RUN 1 (`AnyTaintEx.Sim6X`): every object of `D6X` has a `D6T` object with the
    same base fact (`Refines6`: the same object up to the exclusion and the layer; a refined demand
    edge is a base demand edge; an annotated edge, `ex ≠ {}`, is a base demand edge; a refined demand
    vulnerability is a base demand vulnerability). Only hypothesis: `NoBelowCleaner P` (the `below`
    cleaner's new position is not a base fact, `Vec.below_new_fact`); every abstraction, every taint
    edge set. -/
theorem sim6X (hnb : NoBelowCleaner P) : Sim6X P taint counted L α sinks roots := by
  intro o h
  have hs := D6X_sim hnb h
  cases o with
  | init M i => exact ⟨.init M i, hs, rfl, rfl⟩
  | edge M i n x =>
    obtain ⟨f, hf, hr⟩ := hs
    exact ⟨.edge M i n f, hf, rfl, rfl, rfl, hr.1.1.fact, hr.1.1.dem, hr.1.2⟩
  | added M a => exact ⟨.added M a, hs, rfl, rfl⟩
  | req M i t => exact ⟨.req M i t, hs, rfl, rfl, rfl⟩
  | vuln M n s d =>
    obtain ⟨d', hd, hdd⟩ := hs
    exact ⟨.vuln M n s d', hd, rfl, rfl, rfl, hdd⟩

#print axioms sim6X

/-- The location-inclusion form (`AnyTaintEx.Sim6XIn`) under the same hypothesis. -/
theorem sim6XIn (hnb : NoBelowCleaner P) : Sim6XIn P taint counted L α sinks roots :=
  sim6X_in (sim6X hnb)

#print axioms sim6XIn

/-- An abstract-mark edge of `D6X` is a `D6T` edge with the SAME annotated fact (no exclusion, the
    same layer): the refinement changes only edges below an `[any-taint]` fact. Hypothesis:
    `NoBelowCleaner P`. -/
theorem D6X_abs_same (hnb : NoBelowCleaner P) {M : MethodId} {i : PFact} {n : Node} {x : XFact}
    (h : D6X P taint counted L α sinks roots (.edge M i n x))
    (ha : Exact.absB x.af.fact.mark = true) :
    D6T P taint counted L α sinks roots (.edge M i n x.af) ∧ x.ex = Excl.empty := by
  obtain ⟨f, hf, hr⟩ := D6X_sim hnb h
  refine ⟨by rw [hr.2 ha]; exact hf, AnyTaintExExact.D6X_wf_edge h (carriesB_of_mark ?_)⟩
  intro t ht
  rw [ht] at ha
  cases ha

#print axioms D6X_abs_same

end Sim6

/-! ## 5. The simulation of the restricted run (`SimRX`, under `NoBelowCleaner` and `RecsRefine`)

  Every object of the spec instance `DRXs` has an object of the spec instance of `DRT` (`emitM`,
  `satI`, `restrictU`) with the same base fact (`RefinesR`). One induction on `DRXs`; an edge is
  related by `RelA` and by the premise condition "an edge of a premise with an exclusion, or of a
  refined must-premise that is a base non-must premise, is a base demand edge" (the base start fact
  of such a premise, `startFact` of a concrete `.any` or `*` premise, is demand, and the base layer
  never falls). The new parts: the start of a must-premise (`startX_relR`), the emission with the
  must flags (`emitTX_parts`), the restriction (`restrictX_relR`), the summary with a premise
  exclusion (`applySummaryX_relR`), and the record demotion (`recLayerX_relA`: a refined demotion
  `mj ∧ ¬satX` is a base demotion, or the base record is demand, or the added fact carries an
  exclusion, `sat_inside_ex`). -/

/-- The base layer never falls along a statement. -/
theorem transferT_demand_mono {taint : TaintEdges} {counted : Acc → Bool} {L : Nat} {s : Stmt}
    {c y : AFact} (hc : c.demand = true) (h : y ∈ (transferT taint counted L s c).facts) :
    y.demand = true := by
  rcases AnyTaintSim.transferT_mem_inv h with ⟨_, rfl⟩ | ⟨e, x, _, hx, rfl⟩
  · exact hc
  · apply AnyTaintExact.limitF_demand_true
    rcases w6t_cases taint e x with e1 | ⟨_, _, e1⟩
    · rw [e1]; exact Invariant.applyEdge_demand_monotone hc hx
    · rw [e1]

#print axioms transferT_demand_mono

/-- A summary application gives a demand result on a demand added fact or a demand summary edge. -/
theorem applySummary_demand_mono {a g y : AFact} {j : PFact}
    (hd : a.demand = true ∨ g.demand = true) (h : y ∈ (applySummary a j g).facts) :
    y.demand = true := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  apply AnyTaintSim.norm_demand
  show (x.demand || g.demand) = true
  rcases hd with hd | hd
  · rw [Invariant.applyEdge_demand_monotone hd hx]; rfl
  · rw [hd]; cases x.demand <;> rfl

#print axioms applySummary_demand_mono

theorem recLayer_demand_mono {mj s : Bool} {x : AFact} (h : x.demand = true) :
    (recLayer mj s x).demand = true := by
  unfold recLayer
  cases mj && !s
  · exact h
  · rfl

/-- `normX` keeps at most the exclusion it is given. -/
theorem normX_ex_ne {x : XFact} (h : (normX x).ex.isEmptyB = false) : x.ex.isEmptyB = false := by
  unfold normX at h
  split at h
  · exact h
  · cases h

theorem eq_empty_of_isEmptyB {e : Excl} (h : e.isEmptyB = true) : e = Excl.empty := by
  cases e with
  | univ => cases h
  | set xs =>
    cases xs with
    | nil => rfl
    | cons a xs => cases h

theorem subB_empty (e : Excl) : Excl.empty.subB e = true := by
  cases e <;> rfl

/-- `satI` reads the premise at or below the added fact. -/
theorem satI_below {j a : PFact} (h : satI j a = true) : ∃ r, relate a.path j.path = .below r := by
  unfold satI coversB at h
  have h1 := RExact.bool_and_right (RExact.bool_and_left h)
  dsimp only at h1
  cases hd : dropPrefix a.path j.path with
  | none => rw [hd] at h1; cases h1
  | some r => exact ⟨r, by unfold relate; rw [hd]⟩

#print axioms satI_below

/-- THE SATISFACTION GAP: a premise without exclusion that `satI` accepts but `satX` rejects meets an
    added fact WITH an exclusion. -/
theorem sat_inside_ex {j a : PFact} {aex : Excl} (hs : satI j a = true)
    (hx : satX j Excl.empty a aex = false) : aex.isEmptyB = false := by
  unfold satX at hx
  rw [hs, Bool.true_and] at hx
  obtain ⟨r, hr⟩ := satI_below hs
  unfold insideExB at hx
  rw [hr] at hx
  cases he : aex.isEmptyB with
  | false => rfl
  | true =>
    exfalso
    have e := eq_empty_of_isEmptyB he
    subst e
    cases r with
    | nil => dsimp only at hx; rw [subB_empty] at hx; cases hx
    | cons x r' => dsimp only at hx; rw [admits_empty] at hx; cases hx

#print axioms sat_inside_ex

/-- The start fact of a concrete non-`$` premise is demand. -/
theorem startFact_demand_of {j : PFact} (hk : j.kind ≠ .exact) (hc : ∃ t, j.mark = .conc t) :
    (startFact j).demand = true := by
  obtain ⟨t, ht⟩ := hc
  obtain ⟨b, p, k, m⟩ := j
  have ht' : m = .conc t := ht
  subst ht'
  cases k with
  | exact => exact absurd rfl hk
  | any => rfl
  | star e => rfl

/-- THE START OF A REFINED PREMISE against the base start of the same premise with a base flag
    (a base must flag is a refined must flag; an exclusion means a base non-must premise). -/
theorem startX_relR {j : PFact} {mj mj' : Bool} {jex : Excl}
    (hmm : mj' = true → mj = true) (hjx : jex.isEmptyB = false → mj' = false)
    (hjc : ∃ t, j.mark = .conc t) (hmust : mj = true → j.kind = .any)
    (hjex : jex.isEmptyB = false → j.kind ≠ .exact) :
    RelA (startX j mj jex) (startT j mj') ∧
    ((jex.isEmptyB = false ∨ (mj = true ∧ mj' = false)) → (startT j mj').demand = true) := by
  have hnabs : Exact.absB j.mark = false := by obtain ⟨t, ht⟩ := hjc; rw [ht]; rfl
  cases mj with
  | false =>
    cases mj' with
    | true => exact absurd (hmm rfl) Bool.false_ne_true
    | false =>
      refine ⟨⟨⟨W6.LE.refl _, fun he => by cases he⟩, fun _ => rfl⟩, ?_⟩
      rintro (he | ⟨h1, _⟩)
      · exact startFact_demand_of (hjex he) hjc
      · cases h1
  | true =>
    cases mj' with
    | true =>
      refine ⟨⟨⟨?_, fun he => ?_⟩, fun _ => ?_⟩, ?_⟩
      · show W6.LE (normX ⟨⟨j, false⟩, jex⟩).af ⟨j, false⟩
        rw [normX_af]; exact W6.LE.refl _
      · have h2 := hjx (normX_ex_ne he)
        cases h2
      · show (normX ⟨⟨j, false⟩, jex⟩).af = ⟨j, false⟩
        rw [normX_af]
      · rintro (he | ⟨_, h2⟩)
        · have h2 := hjx he
          cases h2
        · cases h2
    | false =>
      have hk := hmust rfl
      obtain ⟨b, p, k, m⟩ := j
      have hk' : k = .any := hk
      subst hk'
      have hst : startT ⟨b, p, .any, m⟩ false = ⟨⟨b, p, .any, m⟩, true⟩ := by
        show startFact ⟨b, p, .any, m⟩ = _
        rfl
      rw [hst]
      refine ⟨⟨⟨?_, fun _ => rfl⟩, fun ha => ?_⟩, fun _ => rfl⟩
      · show W6.LE (normX ⟨⟨⟨b, p, .any, m⟩, false⟩, jex⟩).af ⟨⟨b, p, .any, m⟩, true⟩
        rw [normX_af]
        exact W6.LE.raise rfl
      · exfalso
        rw [startX_af] at ha
        have ha' : Exact.absB m = true := ha
        have hn : Exact.absB m = false := hnabs
        rw [ha'] at hn
        cases hn

#print axioms startX_relR

/-- The refined emission with the must flag: the base premise, the flag rule, and an exclusion of
    the emitted premise comes from an exclusion of the added fact and is never on a `$` premise. -/
theorem emitTX_parts {d a j : PFact} {am mj : Bool} {aex jex : Excl}
    (h : emitTX emitX d a am aex = some (j, mj, jex)) :
    emitM d a = some j ∧ mj = (am && j.kind.isAny) ∧
      (jex.isEmptyB = false → aex.isEmptyB = false ∧ j.kind ≠ .exact) := by
  unfold emitTX at h
  cases he : emitX d a aex with
  | none => rw [he] at h; cases h
  | some pr =>
    obtain ⟨j0, jex0⟩ := pr
    rw [he] at h
    cases h
    have hj := emitX_base he
    refine ⟨hj, rfl, fun hne => ?_⟩
    unfold emitX at he
    rw [hj] at he
    dsimp only at he
    split at he
    · split at he
      · cases he; cases hne
      · cases he
    · cases he
      unfold normJ at hne
      cases hk : j0.kind with
      | exact => rw [hk] at hne; cases hne
      | any => rw [hk] at hne; exact ⟨hne, fun h' => by cases h'⟩
      | star e => rw [hk] at hne; exact ⟨hne, fun h' => by cases h'⟩

#print axioms emitTX_parts

/-- A premise of `DRXs` with an exclusion is not a `$` premise. -/
theorem DRXs_init_excl {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop} {recs : MethodId → PFact × Bool × Excl × XFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    {M : MethodId} {j : PFact} {mj : Bool} {jex : Excl}
    (h : DRXs P taint counted L demand recs sinks roots (.init M j mj jex))
    (he : jex.isEmptyB = false) : j.kind ≠ .exact := by
  cases h with
  | root _ => cases he
  | initR _ _ hj => exact ((emitTX_parts hj).2.2 he).2
  | answer _ _ _ _ => cases he

#print axioms DRXs_init_excl

/-- The base restriction keeps the layer. -/
theorem restrictU_demand {j : PFact} {g g' : AFact} {d : DemandEdge}
    (h : restrictU j g d = some g') : g'.demand = g.demand := by
  unfold restrictU restrictWith at h
  cases hd : d.dout with
  | none => rw [hd] at h; cases h
  | some p =>
    rw [hd] at h
    dsimp only at h
    cases ho : overlapB j d.din with
    | false => rw [ho, if_neg Bool.false_ne_true] at h; cases h
    | true =>
      rw [ho, if_pos rfl] at h
      unfold restrictConcU at h
      cases hb : Nat.beq g.fact.base p.base with
      | false => rw [hb, if_neg Bool.false_ne_true] at h; cases h
      | true =>
        rw [hb, if_pos rfl] at h
        cases hr : relate p.path g.fact.path with
        | below r =>
          rw [hr] at h
          dsimp only at h
          cases ha : admitsTailB p.kind r with
          | false => rw [ha, if_neg Bool.false_ne_true] at h; cases h
          | true => rw [ha, if_pos rfl] at h; cases h; rfl
        | above r =>
          rw [hr] at h
          dsimp only at h
          cases hk : g.fact.kind with
          | any => rw [hk] at h; cases h; rfl
          | star e => rw [hk] at h; cases h
          | exact => rw [hk] at h; cases h
        | apart => rw [hr] at h; cases h

#print axioms restrictU_demand

/-- An exclusion of a refined restricted conclusion comes from the conclusion. -/
theorem restrictX_ex {sp : PFact} {spex : Excl} {sc g' : XFact} {d : DemandEdge}
    (h : restrictX sp spex sc d = some g') (he : g'.ex.isEmptyB = false) :
    sc.ex.isEmptyB = false := by
  unfold restrictX at h
  cases hd : d.dout with
  | none => rw [hd] at h; cases h
  | some p =>
    rw [hd] at h
    dsimp only at h
    cases ho : overlapX sp spex d.din Excl.empty with
    | false => rw [ho, if_neg Bool.false_ne_true] at h; cases h
    | true =>
      rw [ho, if_pos rfl] at h
      unfold restrictConcX at h
      cases hr : restrictConcU sc.af p with
      | none => rw [hr] at h; cases h
      | some g0 =>
        rw [hr] at h
        dsimp only at h
        split at h
        · split at h
          · cases h; cases he
          · cases h
        · cases h
          exact normX_ex_ne (x := ⟨g0, sc.ex⟩) he

#print axioms restrictX_ex

/-- The relation of a summary edge (a restricted exit edge or a record): the same fact, a refined
    demand edge is a base demand edge, an annotated edge is a base demand edge. -/
def RelS (g : XFact) (f : AFact) : Prop :=
  g.af.fact = f.fact ∧ (g.af.demand = true → f.demand = true) ∧
    (g.ex.isEmptyB = false → f.demand = true)

/-- The refined restriction under `RelA`: the base restriction of the related base exit edge. -/
theorem restrictX_relR {j : PFact} {jex : Excl} {g g'' : XFact} {gb : AFact} {d : DemandEdge}
    (hg : RelA g gb) (h : restrictX j jex g d = some g'') :
    ∃ gb'', restrictU j gb d = some gb'' ∧ RelS g'' gb'' := by
  have h0 := restrictX_base h
  have hf := restrictU_fact j g.af gb d hg.1.1.fact
  rw [h0] at hf
  cases hb : restrictU j gb d with
  | none => rw [hb] at hf; cases hf
  | some gb'' =>
    rw [hb] at hf
    have hff : g''.af.fact = gb''.fact := Option.some.inj hf
    refine ⟨gb'', rfl, hff, fun hd => ?_, fun he => ?_⟩
    · rw [restrictU_demand hb]
      rw [restrictU_demand h0] at hd
      exact hg.1.1.dem hd
    · rw [restrictU_demand hb]
      exact hg.1.2 (restrictX_ex h he)

#print axioms restrictX_relR

/-- The refined summary application of a restricted run (a premise exclusion `jex`, a concrete
    non-`*` added fact) under `RelA` / `RelS`. Hypothesis: a premise exclusion means a base demand
    summary edge (`hjx`). -/
theorem applySummaryX_relR {a g x : XFact} {a' g' : AFact} {j : PFact} {jex : Excl}
    (ha : RelA a a') (hans : a.af.fact.kind.isStar = false) (hac : ∃ t, a.af.fact.mark = .conc t)
    (hg : RelS g g') (hjx : jex.isEmptyB = false → g'.demand = true)
    (hx : x ∈ (applySummaryX a j jex g).facts) :
    ∃ y', y' ∈ (applySummary a' j g').facts ∧ RelA x y' := by
  obtain ⟨x0, hx0, rfl⟩ := List.mem_map.mp hx
  obtain ⟨y0, hy0, hle, hex, _⟩ := applyEdgeX_relA ha hx0
  have hy0' : y0 ∈ (applyEdge a' j g'.fact).facts := by rw [← hg.1]; exact hy0
  have hs : x0.af.fact.kind.isStar = false := AnyTaintExExact.applyEdgeX_nonstar hans hx0
  have hys : y0.fact.kind.isStar = false := by rw [← hle.fact]; exact hs
  have hxc : ∃ t, x0.af.fact.mark = .conc t := by
    obtain ⟨yb, hyb, hxyb, _⟩ := applyEdgeX_base hx0
    obtain ⟨t, ht⟩ := hac
    rw [hxyb]; exact applyEdge_mark_conc ht hyb
  refine ⟨AFact.norm ⟨y0.fact, y0.demand || g'.demand⟩,
    List.mem_map_of_mem (f := fun x : AFact => AFact.norm (⟨x.fact, x.demand || g'.demand⟩ : AFact))
      hy0', ⟨?_, ?_⟩, ?_⟩
  · rw [normX_af]
    show W6.LE (AFact.norm ⟨x0.af.fact, x0.af.demand || g.af.demand⟩)
      (AFact.norm ⟨y0.fact, y0.demand || g'.demand⟩)
    rw [Invariant.norm_id_of_nonstar (x := ⟨x0.af.fact, x0.af.demand || g.af.demand⟩) hs,
      Invariant.norm_id_of_nonstar (x := ⟨y0.fact, y0.demand || g'.demand⟩) hys]
    exact W6.LE.of_nonstar hle.fact hs (W6.bor_mono hle.dem hg.2.1)
  · intro he
    have hx0e := normX_ex_ne he
    apply AnyTaintSim.norm_demand
    show (y0.demand || g'.demand) = true
    rcases hex hx0e with h1 | h1 | h1
    · rw [h1]; rfl
    · rw [hjx h1]; cases y0.demand <;> rfl
    · rw [hg.2.2 h1]; cases y0.demand <;> rfl
  · intro habs
    exfalso
    rw [normX_af, CoreAux.norm_mark] at habs
    obtain ⟨t, ht⟩ := hxc
    have h2 : Exact.absB x0.af.fact.mark = true := habs
    rw [ht] at h2
    cases h2

#print axioms applySummaryX_relR

/-- The record demotion under `RelA` (a concrete non-`*` result): the refined demotion needs a base
    demand result (`hdem`). -/
theorem recLayerX_relA {mj sx mj' si : Bool} {r : XFact} {y : AFact} (h : RelA r y)
    (hns : r.af.fact.kind.isStar = false) (hc : ∃ t, r.af.fact.mark = .conc t)
    (hdem : (mj && !sx) = true → (recLayer mj' si y).demand = true) :
    RelA (recLayerX mj sx r) (recLayer mj' si y) := by
  have hf : (recLayer mj' si y).fact = r.af.fact := by
    rw [recLayer_fact]; exact h.1.1.fact.symm
  have hnabs : Exact.absB r.af.fact.mark = false := by obtain ⟨t, ht⟩ := hc; rw [ht]; rfl
  unfold recLayerX
  cases hb : (mj && !sx) with
  | true =>
    rw [if_pos rfl]
    have hd := hdem hb
    refine ⟨⟨W6.LE.of_nonstar hf.symm hns (fun _ => hd), fun he => by cases he⟩, fun ha => ?_⟩
    have ha' : Exact.absB r.af.fact.mark = true := ha
    rw [ha'] at hnabs; cases hnabs
  | false =>
    rw [if_neg Bool.false_ne_true]
    refine ⟨⟨W6.LE.of_nonstar hf.symm hns (fun hd => recLayer_demand_mono (h.1.1.dem hd)),
      fun he => recLayer_demand_mono (h.1.2 he)⟩, fun ha => ?_⟩
    rw [ha] at hnabs; cases hnabs

#print axioms recLayerX_relA

/-- The motive of the simulation of the restricted run: a base object with a base flag that implies
    the refined flag (and is not must if there is an exclusion); an edge with a related base fact
    (`RelA`) that is a base demand edge if its premise carries an exclusion or is must only in the
    refined run. -/
def SimObjR (R : TObj → Prop) : XObj → Prop
  | .init M j mj jex => ∃ mj', R (.init M j mj') ∧ (mj' = true → mj = true) ∧
      (jex.isEmptyB = false → mj' = false)
  | .edge M j mj jex n x => ∃ mj' f, R (.edge M j mj' n f) ∧ (mj' = true → mj = true) ∧
      (jex.isEmptyB = false → mj' = false) ∧ RelA x f ∧
      ((jex.isEmptyB = false ∨ (mj = true ∧ mj' = false)) → f.demand = true)
  | .added M a am aex => ∃ am', R (.added M a am') ∧ (am' = true → am = true) ∧
      (aex.isEmptyB = false → am' = false)
  | .req M j t => R (.req M j t)
  | .vuln M n s d => ∃ d', R (.vuln M n s d') ∧ (d = true → d' = true)

section SimR
variable {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
  {demand : MethodId → DemandEdge → Prop}
  {recsX : MethodId → PFact × Bool × Excl × XFact → Prop}
  {recs : MethodId → PFact × Bool × AFact → Prop}
  {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}

/-- THE SIMULATION INVARIANT OF THE RESTRICTED RUN (one induction on `DRXs`). Hypotheses:
    `NoBelowCleaner P`, `RecsRefine P recsX recs`. -/
theorem DRXs_sim (hnb : NoBelowCleaner P) (hrr : RecsRefine P recsX recs) {o : XObj}
    (h : DRXs P taint counted L demand recsX sinks roots o) :
    SimObjR (DRT P taint counted L demand emitM satI restrictU recs sinks roots) o := by
  induction h with
  | root hM => exact ⟨false, DRT.root hM, fun h => h, fun _ => rfl⟩
  | @start M j mj jex hJ ih =>
    obtain ⟨mj', hj', hmm, hjx⟩ := ih
    obtain ⟨hr, hc⟩ := startX_relR hmm hjx (AnyTaintExExact.DRX_conc emitX_copies hJ)
      (fun hm => by subst hm; exact AnyTaintExExact.DRX_mustAny hJ)
      (DRXs_init_excl hJ)
    exact ⟨mj', startT j mj', DRT.start hj', hmm, hjx, hr, hc⟩
  | @step M i mi iex n f n' s f' _ hE hf ih =>
    obtain ⟨mi', g, hg, hmm, hix, hr, hcd⟩ := ih
    obtain ⟨g', hg', hr'⟩ := transferX_relA hr hf
    exact ⟨mi', g', DRT.step hg hE hg', hmm, hix, hr', fun hc => transferT_demand_mono (hcd hc) hg'⟩
  | @reqStmt M i mi iex n f n' s t _ hE ht ih =>
    obtain ⟨mi', g, hg, _, _, hr, _⟩ := ih
    refine DRT.reqStmt hg hE ?_
    rw [transferT_reqs, ← (W6.transfer_LL hr.1.1).2, ← transferT_reqs taint]
    exact transferX_reqs ht
  | @pass M i mi iex n f n' c _ hE hm ih =>
    obtain ⟨mi', g, hg, hmm, hix, hr, hcd⟩ := ih
    exact ⟨mi', g, DRT.pass hg hE (by rw [← hr.1.1.fact]; exact hm), hmm, hix, hr, hcd⟩
  | @added M i mi iex n f n' c e a _ hE he ha ih =>
    obtain ⟨mi', g, hg, _, _, hr, _⟩ := ih
    obtain ⟨a', ha', hra⟩ := bindX_relA hr ha
    refine ⟨a'.fact.kind.isAny && !a'.demand, ?_, fun hm => ?_, fun hx => ?_⟩
    · rw [hra.1.1.fact]; exact DRT.added hg hE he ha'
    · rw [hra.1.1.fact]
      have h1 := RExact.bool_and_left hm
      have h2 : a'.demand = false := by
        have h0 := RExact.bool_and_right hm
        cases hd : a'.demand with
        | false => rfl
        | true => rw [hd] at h0; cases h0
      have h3 : a.af.demand = false := by
        cases hd : a.af.demand with
        | false => rfl
        | true => rw [hra.1.1.dem hd] at h2; cases h2
      rw [h1, h3]; rfl
    · rw [hra.1.2 hx]; cases a'.fact.kind.isAny <;> rfl
  | @initR m a am aex d j mj jex _ hd hj ih =>
    obtain ⟨am', hA', hmm, hax⟩ := ih
    obtain ⟨hem, hmj, hjx⟩ := emitTX_parts hj
    refine ⟨am' && j.kind.isAny, DRT.initR hA' hd (emitTWith_of hem am'), fun hm => ?_,
      fun he => ?_⟩
    · rw [hmj, hmm (RExact.bool_and_left hm), RExact.bool_and_right hm]; rfl
    · rw [hax (hjx he).1]; rfl
  | @ret M i mi iex n f n' c e1 a j mj jex g d g'' r e2 r' hF hE he1 ha _ _ hd hres hsat hr he2
      hr' ihF _ ihG =>
    obtain ⟨mi', f6, hf6, hmm, hix, hrf, hcf⟩ := ihF
    obtain ⟨mj'', gb, hgb, _, _, hrg, hcg⟩ := ihG
    obtain ⟨a6, ha6, hra⟩ := bindX_relA hrf ha
    obtain ⟨gb'', hres', hrs⟩ := restrictX_relR hrg hres
    have hcF : AnyTaintExExact.ConcObjX (.edge M i mi iex n f) :=
      AnyTaintExExact.DRX_conc emitX_copies hF
    obtain ⟨_, ⟨tf, htf⟩, hfns⟩ := hcF
    have hans := AnyTaintExExact.applyEdgeX_nonstar hfns ha
    have hac : ∃ t, a.af.fact.mark = .conc t := by
      obtain ⟨y, hy, hay, _⟩ := applyEdgeX_base ha
      rw [hay]; exact applyEdge_mark_conc htf hy
    have hjx' : jex.isEmptyB = false → gb''.demand = true := fun he => by
      rw [restrictU_demand hres']; exact hcg (Or.inl he)
    obtain ⟨r6, hr6, hrr⟩ := applySummaryX_relR hra hans hac hrs hjx' hr
    obtain ⟨r6', hr6', hrr'⟩ := bindX_relA hrr hr'
    refine ⟨mi', _, DRT.ret hf6 hE he1 ha6 (AnyTaintSim.DRT_edge_init hgb) hgb hd hres'
      (by rw [← hra.1.1.fact]; exact satX_satI hsat) hr6 he2 hr6', hmm, hix, limitFX_relA hrr',
      fun hc => ?_⟩
    have h1 := Invariant.applyEdge_demand_monotone (hcf hc) ha6
    have h2 := applySummary_demand_mono (Or.inl h1) hr6
    exact AnyTaintExact.limitF_demand_true (Invariant.applyEdge_demand_monotone h2 hr6')
  | @retRec M i mi iex n f n' c e1 a j mj jex g r e2 r' hF hE he1 ha hrec hsat hr he2 hr' ihF =>
    obtain ⟨mi', f6, hf6, hmm, hix, hrf, hcf⟩ := ihF
    obtain ⟨a6, ha6, hra⟩ := bindX_relA hrf ha
    obtain ⟨mj', g', hrec', hR⟩ := hrr _ _ _ _ _ hrec
    obtain ⟨_, _, _, hgf, _, hjx, hgd, hgc⟩ := hR
    have hcF : AnyTaintExExact.ConcObjX (.edge M i mi iex n f) :=
      AnyTaintExExact.DRX_conc emitX_copies hF
    obtain ⟨_, ⟨tf, htf⟩, hfns⟩ := hcF
    have hans := AnyTaintExExact.applyEdgeX_nonstar hfns ha
    have hac : ∃ t, a.af.fact.mark = .conc t := by
      obtain ⟨y, hy, hay, _⟩ := applyEdgeX_base ha
      rw [hay]; exact applyEdge_mark_conc htf hy
    have hrs : RelS g g' := ⟨hgf, hgd, fun he => hgc (Or.inl he)⟩
    obtain ⟨r6, hr6, hrr⟩ :=
      applySummaryX_relR hra hans hac hrs (fun he => hgc (Or.inr (Or.inl he))) hr
    obtain ⟨r6', hr6', hrr'⟩ := bindX_relA hrr hr'
    have hsat' : satI j a6.fact = true ∨ applicable j a6.fact = true := by
      rw [← hra.1.1.fact]
      rcases hsat with h1 | h1
      · exact Or.inl (satX_satI h1)
      · exact Or.inr h1
    have hrns : r.af.fact.kind.isStar = false := AnyTaintExExact.applySummaryX_nonstar hans hr
    have hr'ns : r'.af.fact.kind.isStar = false := AnyTaintExExact.applyEdgeX_nonstar hrns hr'
    have hr'c : ∃ t, r'.af.fact.mark = .conc t := by
      obtain ⟨ta, hta⟩ := hac
      obtain ⟨yr, hyr, hry, _⟩ := applySummaryX_base hr
      obtain ⟨tr, htr⟩ := AnyTaintExExact.conc_of_fact hry (applySummary_mark_conc hta hyr)
      obtain ⟨yr', hyr', hry', _⟩ := applyEdgeX_base hr'
      exact AnyTaintExExact.conc_of_fact hry' (applyEdge_mark_conc htr hyr')
    refine ⟨mi', _, DRT.retRec hf6 hE he1 ha6 hrec' hsat' hr6 he2 hr6', hmm, hix,
      limitFX_relA (recLayerX_relA hrr' hr'ns hr'c ?_), fun hc => ?_⟩
    · intro hb
      have hmj : mj = true := RExact.bool_and_left hb
      have hsx : satX j jex a.af.fact a.ex = false := by
        have h2 := RExact.bool_and_right hb
        cases hs : satX j jex a.af.fact a.ex with
        | false => rfl
        | true => rw [hs] at h2; cases h2
      cases hmj' : mj' with
      | false =>
        apply recLayer_demand_mono
        have hgd' : g'.demand = true := hgc (Or.inr (Or.inr ⟨hmj, hmj'⟩))
        exact Invariant.applyEdge_demand_monotone (applySummary_demand_mono (Or.inr hgd') hr6) hr6'
      | true =>
        cases hsi : satI j a6.fact with
        | false => exact rfl
        | true =>
          apply recLayer_demand_mono
          have hje : jex = Excl.empty := by
            cases he : jex.isEmptyB with
            | true => exact eq_empty_of_isEmptyB he
            | false => rw [hjx he] at hmj'; cases hmj'
          rw [hje] at hsx
          have hsi' : satI j a.af.fact = true := by rw [hra.1.1.fact]; exact hsi
          have hae := sat_inside_ex hsi' hsx
          have h1 := hra.1.2 hae
          exact Invariant.applyEdge_demand_monotone (applySummary_demand_mono (Or.inl h1) hr6) hr6'
    · have h1 := Invariant.applyEdge_demand_monotone (hcf hc) ha6
      have h2 := applySummary_demand_mono (Or.inl h1) hr6
      exact AnyTaintExact.limitF_demand_true
        (recLayer_demand_mono (Invariant.applyEdge_demand_monotone h2 hr6'))
  | @reqSink M i mi iex n f s t _ hs hc ih =>
    obtain ⟨mi', g, hg, _, _, hr, _⟩ := ih
    exact DRT.reqSink hg hs (by rw [← W6.check_LE i s hr.1.1]; exact checkX_request hc)
  | @answer M i t a am aex _ _ hm ho ihR ihA =>
    obtain ⟨am', hA', _, _⟩ := ihA
    exact ⟨false, DRT.answer ihR hA' hm (overlapX_overlapB ho), fun h => h, fun _ => rfl⟩
  | @reqUp m j t M ic mc icx n f n' c e a _ _ hE hc he ha hcl ho ihR ihF =>
    obtain ⟨mc', g, hg, _, _, hr, _⟩ := ihF
    obtain ⟨a', ha', hra⟩ := bindX_relA hr ha
    exact DRT.reqUp ihR hg hE hc he ha' (by rw [← hra.1.1.fact]; exact hcl)
      (by rw [← hra.1.1.fact]; exact overlapX_overlapB ho)
  | @vuln M i mi iex n f s _ hs hc ih =>
    obtain ⟨mi', g, hg, _, _, hr, _⟩ := ih
    exact ⟨g.demand,
      DRT.vuln hg hs (by rw [← W6.check_LE i s hr.1.1]; exact checkX_triggered hc), hr.1.1.dem⟩
  | @clean M i mi iex n f n' cl f' hF hE hf ih =>
    obtain ⟨mi', g, hg, hmm, hix, hr, hcd⟩ := ih
    obtain ⟨g', hg', hr'⟩ :=
      cleanResX_relA hr (AnyTaintExExact.DRX_wf_edge hF) (hnb _ _ _ _ hE) hf
    exact ⟨mi', g', DRT.clean hg hE hg', hmm, hix, hr',
      fun hc => Invariant.cleanRes_demand_monotone (hcd hc) hg'⟩
  | @reqClean M i mi iex n f n' cl t _ hE ht ih =>
    obtain ⟨mi', g, hg, _, _, hr, _⟩ := ih
    exact DRT.reqClean hg hE (by rw [← (W6.cleanRes_LL hr.1.1).2]; exact cleanResX_reqs ht)
  | @filt M i mi iex n f n' b may _ hE hp ih =>
    obtain ⟨mi', g, hg, hmm, hix, hr, hcd⟩ := ih
    exact ⟨mi', g, DRT.filt hg hE (by rw [← hr.1.1.fact]; exact hp), hmm, hix, hr, hcd⟩

#print axioms DRXs_sim

/-- THE SIMULATION OF THE RESTRICTED RUN (`AnyTaintEx.SimRX`): every object of the spec instance
    `DRXs` (`emitX`, `satX`, `restrictX`) has an object of the spec instance of `DRT` (`emitM`,
    `satI`, `restrictU`) with the same base fact (`RefinesR`: a base must flag is a refined must
    flag; a premise or added fact with an exclusion is not must in the base; a refined demand edge,
    an annotated edge, an edge of a premise with an exclusion and an edge of a premise that is must
    only in the refined run are base demand edges). Hypotheses: `NoBelowCleaner P`,
    `RecsRefine P recsX recs` (the expected ones). -/
theorem simRX (hnb : NoBelowCleaner P) (hrr : RecsRefine P recsX recs) :
    SimRX P taint counted L demand recsX recs sinks roots := by
  intro o h
  have hs := DRXs_sim hnb hrr h
  cases o with
  | init M j mj jex =>
    obtain ⟨mj', h1, h2, h3⟩ := hs
    exact ⟨.init M j mj', h1, rfl, rfl, h2, h3⟩
  | edge M j mj jex n x =>
    obtain ⟨mj', f, h1, h2, h3, hr, h4⟩ := hs
    refine ⟨.edge M j mj' n f, h1, rfl, rfl, rfl, hr.1.1.fact, h2, h3, hr.1.1.dem, fun hc => ?_⟩
    rcases hc with hc | hc | hc
    · exact hr.1.2 hc
    · exact h4 (Or.inl hc)
    · exact h4 (Or.inr hc)
  | added M a am aex =>
    obtain ⟨am', h1, h2, h3⟩ := hs
    exact ⟨.added M a am', h1, rfl, rfl, h2, h3⟩
  | req M j t => exact ⟨.req M j t, hs, rfl, rfl, rfl⟩
  | vuln M n s d =>
    obtain ⟨d', h1, h2⟩ := hs
    exact ⟨.vuln M n s d', h1, rfl, rfl, rfl, h2⟩

#print axioms simRX

/-- The location-inclusion form (`AnyTaintEx.SimRXIn`) under the same hypotheses. -/
theorem simRXIn (hnb : NoBelowCleaner P) (hrr : RecsRefine P recsX recs) :
    SimRXIn P taint counted L demand recsX recs sinks roots :=
  simRX_in (simRX hnb hrr)

#print axioms simRXIn

end SimR

end ApSpec.AnyTaintExKinds

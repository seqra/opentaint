/-
  ApSpec.RestrictedCoverage — the soundness of the runs that strictly follow the demand.

  Contents:
    * the mark invariants of the restricted closure `DR` (`edge_concR`, `req_initial_starR`);
    * the coverage theorem of `DR` (`coverageR`): a DEMANDED flow (`FlowR`) is covered by an
      edge, or the run raises the mark request on the initial fact. The covered flow is also
      demanded by the summaries of the run itself (`summaryDemand`): this is the input of the
      next run;
    * the vulnerability theorem of `DR` (`reach_strongR`, `vuln_foundR`);
    * run 1 (the closure `D`) gives the first demanded witness (`coverageD`, `reach_to_reachR`);
    * monotonicity and forgetting of the demand (`flowR_mono`, `reachR_mono`, `flowR_flow`,
      `reachR_reach`);
    * the iteration (`runSeq`, `iteration_sound`): every run of the sequence reports every
      concrete vulnerability, if each backward step satisfies `BackwardContract`.

  The emission, satisfaction and restriction functions are variables. The proofs use only
  the contracts `EmitContractOn (DR …) emit sat` (the emission contract for the added facts of
  the run itself), `SatContract sat` and `RestrictContract restrict`.

  Version 4: the demand entry pattern covers the entry location WITH its mark (`FlowR.call`,
  `ReachR.down`). Two paths give the per-run emission contract:
    * version 3: the full contract `EmitContract emit sat` (`EmitContract.on`);
    * version 4 (`emitM`): the contract for concrete added facts `EmitContractConc emit sat`,
      and a mark-copying emission `EmitCopiesMark emit`. Then every object of the run is
      concrete (`concInvR_all`), so the contract holds on the run (`emitOn_of_conc`).
-/
import ApSpec.Restricted
import ApSpec.Coverage

namespace ApSpec.RCov
open ApSpec ApSpec.Coverage

/-! ## 0. Small lemmas -/

/-- A fact that covers a location covers it as a location (the mark is ignored). -/
theorem covers_loc {i : PFact} {l : Loc} (h : i.covers l) : i.coversLoc l := ⟨h.1, h.2.1⟩

/-- A satisfied premise raises no request: its mark admits the mark of the added fact. -/
theorem sat_step {sat : PFact → PFact → Bool} (hS : SatContract sat) {i j : PFact} {a g : AFact}
    {l0 l1 l2 : Loc}
    (hsat : sat j a.fact = true) (hda : den i a.fact l0 l1) (hdg : den j g.fact l1 l2) :
    ∃ r, r ∈ (applySummary a j g).facts ∧ den i r.fact l0 l2 := by
  rcases applySummary_sound hda hdg with h | ⟨hst, hq⟩
  · exact h
  · exfalso
    have hm := hS.1 j a.fact hsat
    rcases mark_cases j.mark with hj | ⟨t, hj⟩
    · rw [applySummary_reqs, applyEdge_reqs_of_star hj] at hq
      cases hq
    · rw [hj, hst] at hm
      exact Bool.noConfusion hm

/-- The version-4 emission copies the mark of the added fact. -/
theorem emitM_copies : EmitCopiesMark emitM := by
  intro d a j h
  unfold emitM at h
  split at h
  · split at h
    · cases h
      rfl
    · split at h
      · cases h
        rfl
      · cases h
    · split at h
      · cases h
        rfl
      · cases h
    · cases h
  · cases h

#print axioms emitM_copies

/-! ## 1. Monotonicity and forgetting of the demand -/

/-- A larger demand keeps a demanded flow. -/
theorem flowR_mono {P : Program} {d1 d2 : MethodId → DemandEdge → Prop}
    (h : ∀ m e, d1 m e → d2 m e) {M : MethodId} {l0 : Loc} {n : Node} {l : Loc}
    (hf : FlowR P d1 M l0 n l) : FlowR P d2 M l0 n l := by
  induction hf with
  | start M l0 => exact FlowR.start M l0
  | step _ he hs ih => exact FlowR.step ih he hs
  | pass _ he hm ih => exact FlowR.pass ih he hm
  | call _ he he1 hd1 _ hdem hdin hdout hp he2 hd2 ih ihc =>
    exact FlowR.call ih he he1 hd1 ihc (h _ _ hdem) hdin hdout hp he2 hd2

#print axioms flowR_mono

/-- A larger demand keeps a demanded vulnerability witness. -/
theorem reachR_mono {P : Program} {roots : List MethodId} {d1 d2 : MethodId → DemandEdge → Prop}
    (h : ∀ m e, d1 m e → d2 m e) {M : MethodId} {n : Node} {l : Loc}
    (hr : ReachR P d1 roots M n l) : ReachR P d2 roots M n l := by
  induction hr with
  | root hM hfl => exact ReachR.root hM (flowR_mono h hfl)
  | down _ he he1 hd1 hdem hdin hfc ih =>
    exact ReachR.down ih he he1 hd1 (h _ _ hdem) hdin (flowR_mono h hfc)

#print axioms reachR_mono

/-- A demanded flow is a flow. -/
theorem flowR_flow {P : Program} {demand : MethodId → DemandEdge → Prop}
    {M : MethodId} {l0 : Loc} {n : Node} {l : Loc}
    (hf : FlowR P demand M l0 n l) : Flow P M l0 n l := by
  induction hf with
  | start M l0 => exact Flow.start M l0
  | step _ he hs ih => exact Flow.step ih he hs
  | pass _ he hm ih => exact Flow.pass ih he hm
  | call _ he he1 hd1 _ _ _ _ _ he2 hd2 ih ihc => exact Flow.call ih he he1 hd1 ihc he2 hd2

#print axioms flowR_flow

/-- A demanded vulnerability witness is a vulnerability witness. -/
theorem reachR_reach {P : Program} {roots : List MethodId} {demand : MethodId → DemandEdge → Prop}
    {M : MethodId} {n : Node} {l : Loc}
    (hr : ReachR P demand roots M n l) : Reach P roots M n l := by
  induction hr with
  | root hM hfl => exact Reach.root hM (flowR_flow hfl)
  | down _ he he1 hd1 _ _ hfc ih => exact Reach.down ih he he1 hd1 (flowR_flow hfc)

#print axioms reachR_reach

/-! ## 2. The restricted closure `DR` -/

section Restricted
variable (P : Program) (counted : Acc → Bool) (L : Nat)
  (demand : MethodId → DemandEdge → Prop)
  (emit : PFact → PFact → Option PFact)
  (sat : PFact → PFact → Bool)
  (restrict : PFact → AFact → DemandEdge → Option AFact)
  (recs : MethodId → (PFact × AFact) → Prop)
  (sinks : List (MethodId × Node × PFact))
  (roots : List MethodId)

local notation "DRr" => DR P counted L demand emit sat restrict recs sinks roots

/-! ### 2.1 Mark invariants -/

theorem edgeInvR_all {o : Obj} (h : DRr o) : EdgeInv o := by
  induction h with
  | start _ =>
    intro t ht
    exact ⟨t, by rw [startFact_mark]; exact ht⟩
  | step _ _ hf' ih =>
    intro t ht
    obtain ⟨t1, h1⟩ := ih t ht
    exact transfer_mark_conc h1 hf'
  | pass _ _ _ ih => exact ih
  | ret _ _ _ ha _ _ _ _ _ hr _ hr' ih _ _ =>
    intro t ht
    obtain ⟨t1, h1⟩ := ih t ht
    obtain ⟨t2, h2⟩ := applyEdge_mark_conc h1 ha
    obtain ⟨t3, h3⟩ := applySummary_mark_conc h2 hr
    obtain ⟨t4, h4⟩ := applyEdge_mark_conc h3 hr'
    exact ⟨t4, by rw [limitF_mark]; exact h4⟩
  | retRec _ _ _ ha _ _ hr _ hr' ih =>
    intro t ht
    obtain ⟨t1, h1⟩ := ih t ht
    obtain ⟨t2, h2⟩ := applyEdge_mark_conc h1 ha
    obtain ⟨t3, h3⟩ := applySummary_mark_conc h2 hr
    obtain ⟨t4, h4⟩ := applyEdge_mark_conc h3 hr'
    exact ⟨t4, by rw [limitF_mark]; exact h4⟩
  | root _ => trivial
  | reqStmt _ _ _ _ => trivial
  | added _ _ _ _ _ => trivial
  | initR _ _ _ _ => trivial
  | reqSink _ _ _ _ => trivial
  | answer _ _ _ _ _ _ => trivial
  | reqUp _ _ _ _ _ _ _ _ _ _ => trivial
  | vuln _ _ _ _ => trivial

/-- Invariant (b) of `DR`: an edge of a concrete-mark initial fact has a concrete-mark
    final fact. -/
theorem edge_concR {M : MethodId} {i : PFact} {n : Node} {f : AFact} {t : Mark}
    (h : DRr (.edge M i n f)) (ht : i.mark = .conc t) :
    ∃ t', f.fact.mark = .conc t' :=
  edgeInvR_all P counted L demand emit sat restrict recs sinks roots h t ht

#print axioms edge_concR

theorem reqInvR_all {o : Obj} (h : DRr o) : ReqInv o := by
  induction h with
  | @reqStmt _ i _ _ _ _ _ hf _ hq _ =>
    rcases mark_cases i.mark with hm | ⟨t0, hm⟩
    · exact hm
    · exfalso
      obtain ⟨t1, h1⟩ := edge_concR P counted L demand emit sat restrict recs sinks roots hf hm
      rw [transfer_reqs_of_conc h1] at hq
      cases hq
  | reqSink _ _ hc _ => exact check_request_star hc
  | @reqUp _ _ _ _ ic _ _ _ _ _ _ _ hf _ _ _ ha ham _ _ _ =>
    rcases mark_cases ic.mark with hm | ⟨t0, hm⟩
    · exact hm
    · exfalso
      obtain ⟨t1, h1⟩ := edge_concR P counted L demand emit sat restrict recs sinks roots hf hm
      obtain ⟨t2, h2⟩ := applyEdge_mark_conc h1 ha
      rw [ham] at h2
      cases h2
  | root _ => trivial
  | start _ _ => trivial
  | step _ _ _ _ => trivial
  | pass _ _ _ _ => trivial
  | added _ _ _ _ _ => trivial
  | initR _ _ _ _ => trivial
  | ret _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial
  | retRec _ _ _ _ _ _ _ _ _ _ => trivial
  | answer _ _ _ _ _ _ => trivial
  | vuln _ _ _ _ => trivial

/-- Invariant (a) of `DR`: every request is on a mark-abstract initial fact. -/
theorem req_initial_starR {M : MethodId} {i : PFact} {t : Mark}
    (h : DRr (.req M i t)) : i.mark = .star :=
  reqInvR_all P counted L demand emit sat restrict recs sinks roots h

#print axioms req_initial_starR

/-- The concreteness invariant of a run with a mark-copying emission: every initial fact, every
    edge and every added fact has a concrete mark, and the run has no request. -/
def ConcInv : Obj → Prop
  | .init _ i     => ∃ t, i.mark = .conc t
  | .edge _ i _ f => (∃ t, i.mark = .conc t) ∧ ∃ t, f.fact.mark = .conc t
  | .added _ a    => ∃ t, a.mark = .conc t
  | .req _ _ _    => False
  | .vuln _ _ _ _ => True

/-- Version 4: a run with a mark-copying emission (`emitM`) is fully concrete. The run starts
    from the zero fact (concrete), the emission copies the mark of a concrete added fact, and a
    concrete fact raises no request. The records and the restriction do not matter. -/
theorem concInvR_all (hcm : EmitCopiesMark emit) {o : Obj} (h : DRr o) : ConcInv o := by
  induction h with
  | root _ => exact ⟨zeroMark, rfl⟩
  | start _ ih => exact ⟨ih, by rw [startFact_mark]; exact ih⟩
  | step _ _ hf' ih =>
    obtain ⟨hi, ⟨t1, h1⟩⟩ := ih
    exact ⟨hi, transfer_mark_conc h1 hf'⟩
  | reqStmt _ _ hq ih =>
    obtain ⟨_, ⟨t1, h1⟩⟩ := ih
    rw [transfer_reqs_of_conc h1] at hq
    cases hq
  | pass _ _ _ ih => exact ih
  | added _ _ _ ha ih =>
    obtain ⟨_, ⟨t1, h1⟩⟩ := ih
    exact applyEdge_mark_conc h1 ha
  | initR _ _ hemit ih =>
    obtain ⟨t, ht⟩ := ih
    exact ⟨t, by rw [hcm _ _ _ hemit]; exact ht⟩
  | ret _ _ _ ha _ _ _ _ _ hr _ hr' ih _ _ =>
    obtain ⟨hi, ⟨t1, h1⟩⟩ := ih
    obtain ⟨t2, h2⟩ := applyEdge_mark_conc h1 ha
    obtain ⟨t3, h3⟩ := applySummary_mark_conc h2 hr
    obtain ⟨t4, h4⟩ := applyEdge_mark_conc h3 hr'
    exact ⟨hi, t4, by rw [limitF_mark]; exact h4⟩
  | retRec _ _ _ ha _ _ hr _ hr' ih =>
    obtain ⟨hi, ⟨t1, h1⟩⟩ := ih
    obtain ⟨t2, h2⟩ := applyEdge_mark_conc h1 ha
    obtain ⟨t3, h3⟩ := applySummary_mark_conc h2 hr
    obtain ⟨t4, h4⟩ := applyEdge_mark_conc h3 hr'
    exact ⟨hi, t4, by rw [limitF_mark]; exact h4⟩
  | reqSink _ _ hc ih =>
    obtain ⟨⟨t, ht⟩, _⟩ := ih
    have hst := check_request_star hc
    rw [ht] at hst
    cases hst
  | answer _ _ _ _ ih _ => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih _ => exact ih.elim
  | vuln _ _ _ _ => trivial

/-- Every added fact of a run with a mark-copying emission is concrete. -/
theorem added_concR (hcm : EmitCopiesMark emit) {m : MethodId} {a : PFact}
    (h : DRr (.added m a)) : ∃ t, a.mark = .conc t :=
  concInvR_all P counted L demand emit sat restrict recs sinks roots hcm h

#print axioms added_concR

/-- A run with a mark-copying emission has no request. -/
theorem no_reqR (hcm : EmitCopiesMark emit) {M : MethodId} {i : PFact} {t : Mark} :
    ¬ DRr (.req M i t) :=
  fun h => concInvR_all P counted L demand emit sat restrict recs sinks roots hcm h

#print axioms no_reqR

/-- Version 4: the contract for concrete added facts and a mark-copying emission give the
    emission contract on the run. -/
theorem emitOn_of_conc (hE : EmitContractConc emit sat) (hcm : EmitCopiesMark emit) :
    EmitContractOn DRr emit sat :=
  EmitContractConc.on hE (fun _ _ h => added_concR P counted L demand emit sat restrict recs
    sinks roots hcm h)

#print axioms emitOn_of_conc

/-! ### 2.2 The return step of a call -/

/-- A demanded callee pair: the restriction keeps it, the satisfied premise applies it
    without a request, and the binding back gives a caller edge. -/
theorem ret_stepR (hwf : P.WF) (hS : SatContract sat) (hR : RestrictContract restrict)
    {M : MethodId} {i : PFact} {n n' : Node} {f : AFact}
    {c : Call} {e1 e2 : MicroEdge} {a g : AFact} {j : PFact} {l0 l1 l2 l3 : Loc}
    {d : DemandEdge} {p : PFact}
    (hf : DRr (.edge M i n f))
    (he : (M, n, Instr.call c, n') ∈ P.edges)
    (he1 : e1 ∈ c.toCallee) (ha : a ∈ (applyEdge f e1.1 e1.2).facts)
    (hda : den i a.fact l0 l1)
    (hj : DRr (.init c.callee j))
    (hsat : sat j a.fact = true)
    (hg : DRr (.edge c.callee j (P.exit c.callee) g))
    (hdg : den j g.fact l1 l2)
    (hdem : demand c.callee d) (hdin : d.din.coversLoc l1) (hdout : d.dout = some p)
    (hp : p.coversLoc l2)
    (he2 : e2 ∈ c.fromCallee) (hd2 : den e2.1 e2.2 l2 l3) :
    ∃ f', DRr (.edge M i n' f') ∧ den i f'.fact l0 l3 := by
  obtain ⟨g', hres, hdg', _⟩ := hR j g d p l1 l2 hdg hdin hdout hp
  obtain ⟨r, hr, hdr⟩ := sat_step hS hsat hda hdg'
  obtain ⟨r', hr', hdr'⟩ := bind_out hwf he he2 hdr hd2
  exact ⟨_, DR.ret hf he he1 ha hj hg hdem hres hsat hr he2 hr', limitF_sound hdr'⟩

#print axioms ret_stepR

/-! ### 2.3 The coverage theorem of `DR` -/

/-- THE COVERAGE THEOREM OF A RESTRICTED RUN. If the initial fact `i` of `M` is in `DR` and
    covers the entry location `l0`, and the value at `l0` flows to `l` at node `n` along a
    flow that the demand of the previous run demands, then an edge of `i` at `n` covers the
    pair, or `DR` has the request for the entry mark on `i`. The covered flow is also
    demanded by the summaries of this run (the input of the next run). -/
theorem coverageR (hwf : P.WF) (hE : EmitContractOn DRr emit sat) (hS : SatContract sat)
    (hR : RestrictContract restrict)
    {M : MethodId} {l0 : Loc} {n : Node} {l : Loc} (hfl : FlowR P demand M l0 n l) :
    ∀ i, DRr (.init M i) → i.covers l0 →
      (∃ f, DRr (.edge M i n f) ∧ den i f.fact l0 l ∧
        FlowR P (summaryDemand P DRr) M l0 n l) ∨
      DRr (.req M i l0.mark) := by
  induction hfl with
  | start M l0 =>
    intro i hi hc
    exact .inl ⟨_, DR.start hi, startFact_sound hc, FlowR.start M l0⟩
  | step _ he hs ih =>
    intro i hi hc
    rcases ih i hi hc with ⟨f, hf, hd, hfr⟩ | hr
    · rcases transfer_sound (hwf.stmtTouched _ _ _ _ he) hd hs with ⟨r, hr, hdr⟩ | ⟨_, hq⟩
      · exact .inl ⟨r, DR.step hf he hr, hdr, FlowR.step hfr he hs⟩
      · exact .inr (DR.reqStmt hf he hq)
    · exact .inr hr
  | @pass M l0 n l n' c _ he hm ih =>
    intro i hi hc
    rcases ih i hi hc with ⟨f, hf, hd, hfr⟩ | hr
    · have hb : memB f.fact.base c.touched = false := by
        rw [← hd.2.1]
        exact hm
      exact .inl ⟨f, DR.pass hf he hb, hd, FlowR.pass hfr he hm⟩
    · exact .inr hr
  | @call M l0 n l n' c e1 e2 l1 l2 l3 d p _ he he1 hd1 _ hdem hdin hdout hp he2 hd2 ih ihc =>
    intro i hi hc
    rcases ih i hi hc with ⟨f, hf, hd, hfr⟩ | hr
    · -- The caller fact reaches the call. Bind it into the callee.
      obtain ⟨a, ha, hda⟩ := bind_in hwf he he1 hd hd1
      have hadd := DR.added hf he he1 ha
      have hac : a.fact.covers l1 := den_covers_final hda
      -- The demand edge of the callee covers `l1`: the emission gives the initial fact `j`.
      obtain ⟨j, hemit, hjc, hsat⟩ := hE c.callee d.din a.fact l1 hadd hdin hac
      have hj := DR.initR hadd hdem hemit
      have hov : overlapB a.fact j = true := overlapB_of_common hac hjc
      -- A covered callee exit pair of a satisfied initial fact gives the caller edge.
      have fin : ∀ j', DRr (.init c.callee j') → j'.covers l1 → sat j' a.fact = true →
          ∀ g, DRr (.edge c.callee j' (P.exit c.callee) g) → den j' g.fact l1 l2 →
          FlowR P (summaryDemand P DRr) c.callee l1 (P.exit c.callee) l2 →
          ∃ f', DRr (.edge M i n' f') ∧ den i f'.fact l0 l3 ∧
            FlowR P (summaryDemand P DRr) M l0 n' l3 := by
        intro j' hj' hjc' hsat' g hg hdg hfc'
        obtain ⟨f', hf', hd'⟩ := ret_stepR P counted L demand emit sat restrict recs sinks roots
          hwf hS hR hf he he1 ha hda hj' hsat' hg hdg hdem (covers_loc hdin) hdout hp he2 hd2
        -- The next demand edge is the run's own initial fact `j'`: it covers `l1` with its mark.
        exact ⟨f', hf', hd', FlowR.call (d := ⟨j', some g.fact⟩) (p := g.fact) hfr he he1 hd1
          hfc' ⟨hj', .inr ⟨g, hg, rfl⟩⟩ hjc' rfl
          (covers_loc (den_covers_final hdg)) he2 hd2⟩
      rcases ihc j hj hjc with ⟨g, hg, hdg, hfc'⟩ | hreq
      · -- The callee summary covers the pair.
        exact .inl (fin j hj hjc hsat g hg hdg hfc')
      · -- The callee raises the request on its initial fact.
        rcases mark_cases a.fact.mark with ham | ⟨t', ham⟩
        · -- The added fact is mark-abstract: the request climbs to the caller.
          have hup := DR.reqUp hreq hf he rfl he1 ha ham hov
          rw [den_mark_star hda ham] at hup
          exact .inr hup
        · -- The added fact is concrete: it answers the request.
          have hmk := den_mark_conc hda ham
          have hans := DR.answer hreq hadd hmk hov
          have hsat' := hS.2 j a.fact l1.mark hsat hmk
          have hc' := answerInit_covers (t := l1.mark) hjc hac rfl
          rcases ihc _ hans hc' with ⟨g, hg, hdg, hfc'⟩ | hreq'
          · exact .inl (fin _ hans hc' hsat' g hg hdg hfc')
          · exfalso
            have hst := req_initial_starR P counted L demand emit sat restrict recs sinks roots hreq'
            rw [answerInit_mark] at hst
            cases hst
    · exact .inr hr

#print axioms coverageR

/-- Coverage of `DR` for a concrete-mark initial fact: it has no request. -/
theorem coverage_concR (hwf : P.WF) (hE : EmitContractOn DRr emit sat) (hS : SatContract sat)
    (hR : RestrictContract restrict)
    {M : MethodId} {l0 : Loc} {n : Node} {l : Loc} (hfl : FlowR P demand M l0 n l)
    {i : PFact} {t : Mark}
    (hi : DRr (.init M i)) (hc : i.covers l0) (ht : i.mark = .conc t) :
    ∃ f, DRr (.edge M i n f) ∧ den i f.fact l0 l ∧ FlowR P (summaryDemand P DRr) M l0 n l := by
  rcases coverageR P counted L demand emit sat restrict recs sinks roots hwf hE hS hR hfl i hi hc
    with h | hr
  · exact h
  · exfalso
    have hst := req_initial_starR P counted L demand emit sat restrict recs sinks roots hr
    rw [ht] at hst
    cases hst

#print axioms coverage_concR

/-! ### 2.4 The vulnerability theorem of `DR` -/

/-- The strengthened reach statement of `DR` (as `Coverage.reach_strong`). The demanded
    witness is also demanded by the summaries of this run. -/
theorem reach_strongR (hwf : P.WF) (hE : EmitContractOn DRr emit sat) (hS : SatContract sat)
    (hR : RestrictContract restrict)
    {M : MethodId} {n : Node} {l : Loc} (hRe : ReachR P demand roots M n l) :
    ReachR P (summaryDemand P DRr) roots M n l ∧
    ∃ l0 i f, DRr (.edge M i n f) ∧ den i f.fact l0 l ∧
      ((∃ t, i.mark = .conc t) ∨
       (i.mark = .star ∧ (DRr (.req M i l0.mark) →
          ∃ i' f', DRr (.edge M i' n f') ∧ den i' f'.fact l0 l ∧
            ∃ t, i'.mark = .conc t))) := by
  induction hRe with
  | root hM hfl =>
    obtain ⟨f, hf, hd, hfr⟩ := coverage_concR P counted L demand emit sat restrict recs sinks roots
      hwf hE hS hR hfl (t := zeroMark) (DR.root hM) zeroFact_covers rfl
    exact ⟨ReachR.root hM hfr, zeroLoc, zeroFact, f, hf, hd, .inl ⟨zeroMark, rfl⟩⟩
  | @down M n l n' c e l1 n2 l2 d _ he he1 hd1 hdem hdin hfc ih =>
    obtain ⟨hRR, l0, i, f, hf, hd, hdisj⟩ := ih
    -- Bind the caller fact into the callee.
    obtain ⟨a, ha, hda⟩ := bind_in hwf he he1 hd hd1
    have hadd := DR.added hf he he1 ha
    have hac : a.fact.covers l1 := den_covers_final hda
    -- The demand edge of the callee covers `l1`: the emission gives the initial fact `j`.
    obtain ⟨j, hemit, hjc, _⟩ := hE c.callee d.din a.fact l1 hadd hdin hac
    have hj := DR.initR hadd hdem hemit
    -- A request on `j` gets a concrete-mark answer that covers `l1`.
    have key : DRr (.req c.callee j l1.mark) →
        ∃ j', DRr (.init c.callee j') ∧ j'.covers l1 ∧ ∃ t, j'.mark = .conc t := by
      intro hreq
      have hconc : ∃ a', DRr (.added c.callee a') ∧ a'.covers l1 ∧ a'.mark = .conc l1.mark := by
        rcases mark_cases a.fact.mark with ham | ⟨t', ham⟩
        · -- The request climbs to the caller. The caller gives a concrete-mark edge, and
          -- its binding is a concrete added fact.
          have hup := DR.reqUp hreq hf he rfl he1 ha ham (overlapB_of_common hac hjc)
          rw [den_mark_star hda ham] at hup
          rcases hdisj with ⟨t, ht⟩ | ⟨_, himp⟩
          · exfalso
            have hst := req_initial_starR P counted L demand emit sat restrict recs sinks roots hup
            rw [ht] at hst
            cases hst
          · obtain ⟨i', f', hf', hd', t, ht⟩ := himp hup
            obtain ⟨a', ha', hda'⟩ := bind_in hwf he he1 hd' hd1
            obtain ⟨t1, h1⟩ := edge_concR P counted L demand emit sat restrict recs sinks roots hf' ht
            obtain ⟨t2, h2⟩ := applyEdge_mark_conc h1 ha'
            exact ⟨a'.fact, DR.added hf' he he1 ha', den_covers_final hda', den_mark_conc hda' h2⟩
        · exact ⟨a.fact, hadd, hac, den_mark_conc hda ham⟩
      obtain ⟨a', hadd', hac', hm'⟩ := hconc
      have hans := DR.answer hreq hadd' hm' (overlapB_of_common hac' hjc)
      exact ⟨_, hans, answerInit_covers hjc hac' rfl, l1.mark, answerInit_mark⟩
    -- The summary demand of this run demands the call down: its initial fact `j'` covers `l1`.
    have mk : ∀ j', DRr (.init c.callee j') → j'.covers l1 →
        FlowR P (summaryDemand P DRr) c.callee l1 n2 l2 →
        ReachR P (summaryDemand P DRr) roots c.callee n2 l2 :=
      fun j' hj' hjc' hfr =>
        ReachR.down (d := ⟨j', none⟩) hRR he he1 hd1 ⟨hj', .inl rfl⟩ hjc' hfr
    rcases coverageR P counted L demand emit sat restrict recs sinks roots hwf hE hS hR hfc _ hj hjc
      with ⟨g, hg, hdg, hfr⟩ | hreq
    · refine ⟨mk j hj hjc hfr, l1, _, g, hg, hdg, ?_⟩
      rcases mark_cases j.mark with hjm | ⟨t, hjm⟩
      · refine .inr ⟨hjm, fun hreq => ?_⟩
        obtain ⟨j', hj', hjc', t, ht⟩ := key hreq
        obtain ⟨g', hg', hdg', _⟩ := coverage_concR P counted L demand emit sat restrict recs sinks
          roots hwf hE hS hR hfc hj' hjc' ht
        exact ⟨j', g', hg', hdg', t, ht⟩
      · exact .inl ⟨t, hjm⟩
    · obtain ⟨j', hj', hjc', t, ht⟩ := key hreq
      obtain ⟨g', hg', hdg', hfr⟩ := coverage_concR P counted L demand emit sat restrict recs sinks
        roots hwf hE hS hR hfc hj' hjc' ht
      exact ⟨mk j' hj' hjc' hfr, l1, j', g', hg', hdg', .inl ⟨t, ht⟩⟩

#print axioms reach_strongR

/-- THE VULNERABILITY THEOREM OF A RESTRICTED RUN. A demanded concrete source-to-sink
    witness gives a `vuln` object. The witness is also demanded by the summaries of this run. -/
theorem vuln_foundR (hwf : P.WF) (hE : EmitContractOn DRr emit sat) (hS : SatContract sat)
    (hR : RestrictContract restrict)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : ReachR P demand roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    (∃ b, DRr (.vuln M n s b)) ∧ ReachR P (summaryDemand P DRr) roots M n l := by
  obtain ⟨hRR, l0, i, f, hf, hd, hdisj⟩ :=
    reach_strongR P counted L demand emit sat restrict recs sinks roots hwf hE hS hR hRe
  refine ⟨?_, hRR⟩
  rcases check_sound hT hd hsc with htr | ⟨hrq, hist⟩
  · exact ⟨_, DR.vuln hf hs htr⟩
  · have hreq := DR.reqSink hf hs hrq
    rcases hdisj with ⟨t, ht⟩ | ⟨_, himp⟩
    · exfalso
      rw [ht] at hist
      cases hist
    · obtain ⟨i', f', hf', hd', t, ht⟩ := himp hreq
      rcases check_sound hT hd' hsc with htr' | ⟨_, hist'⟩
      · exact ⟨_, DR.vuln hf' hs htr'⟩
      · exfalso
        rw [ht] at hist'
        cases hist'

#print axioms vuln_foundR

end Restricted

/-! ## 3. Run 1: the unrestricted closure `D` -/

section Run1
variable (P : Program) (counted : Acc → Bool) (L : Nat) (α : MethodId → PFact → PFact)
  (sinks : List (MethodId × Node × PFact)) (roots : List MethodId)

local notation "Dr" => D P counted L α sinks roots

/-- The coverage theorem of run 1 (as `Coverage.coverage`). The covered flow is demanded by
    the summaries of run 1 (the input of run 2). -/
theorem coverageD (hwf : P.WF) (hα : ∀ m a, applicable (α m a) a = true)
    {M : MethodId} {l0 : Loc} {n : Node} {l : Loc} (hfl : Flow P M l0 n l) :
    ∀ i, Dr (.init M i) → i.covers l0 →
      (∃ f, Dr (.edge M i n f) ∧ den i f.fact l0 l ∧ FlowR P (summaryDemand P Dr) M l0 n l) ∨
      Dr (.req M i l0.mark) := by
  induction hfl with
  | start M l0 =>
    intro i hi hc
    exact .inl ⟨_, D.start hi, startFact_sound hc, FlowR.start M l0⟩
  | step _ he hs ih =>
    intro i hi hc
    rcases ih i hi hc with ⟨f, hf, hd, hfr⟩ | hr
    · rcases transfer_sound (hwf.stmtTouched _ _ _ _ he) hd hs with ⟨r, hr, hdr⟩ | ⟨_, hq⟩
      · exact .inl ⟨r, D.step hf he hr, hdr, FlowR.step hfr he hs⟩
      · exact .inr (D.reqStmt hf he hq)
    · exact .inr hr
  | @pass M l0 n l n' c _ he hm ih =>
    intro i hi hc
    rcases ih i hi hc with ⟨f, hf, hd, hfr⟩ | hr
    · have hb : memB f.fact.base c.touched = false := by
        rw [← hd.2.1]
        exact hm
      exact .inl ⟨f, D.pass hf he hb, hd, FlowR.pass hfr he hm⟩
    · exact .inr hr
  | @call M l0 n l n' c e1 e2 l1 l2 l3 _ he he1 hd1 _ he2 hd2 ih ihc =>
    intro i hi hc
    rcases ih i hi hc with ⟨f, hf, hd, hfr⟩ | hr
    · -- The caller fact reaches the call. Bind it into the callee.
      obtain ⟨a, ha, hda⟩ := bind_in hwf he he1 hd hd1
      have hadd := D.added hf he he1 ha
      have hac : a.fact.covers l1 := den_covers_final hda
      have hapj := hα c.callee a.fact
      have hjc : (α c.callee a.fact).covers l1 := applicable_sound hapj hac
      have hov : overlapB a.fact (α c.callee a.fact) = true := overlapB_of_common hac hjc
      -- A covered callee exit pair of an applicable initial fact gives the caller edge.
      have fin : ∀ j, Dr (.init c.callee j) → j.covers l1 → applicable j a.fact = true →
          ∀ g, Dr (.edge c.callee j (P.exit c.callee) g) → den j g.fact l1 l2 →
          FlowR P (summaryDemand P Dr) c.callee l1 (P.exit c.callee) l2 →
          ∃ f', Dr (.edge M i n' f') ∧ den i f'.fact l0 l3 ∧
            FlowR P (summaryDemand P Dr) M l0 n' l3 := by
        intro j hj hjc' hap g hg hdg hfc'
        obtain ⟨f', hf', hd'⟩ := ret_step P counted L α sinks roots hwf hf he he1 ha hda hj hap
          hg hdg he2 hd2
        -- The next demand edge is the run's own initial fact `j`: it covers `l1` with its mark.
        exact ⟨f', hf', hd', FlowR.call (d := ⟨j, some g.fact⟩) (p := g.fact) hfr he he1 hd1
          hfc' ⟨hj, .inr ⟨g, hg, rfl⟩⟩ hjc' rfl
          (covers_loc (den_covers_final hdg)) he2 hd2⟩
      rcases ihc _ (D.initA hadd) hjc with ⟨g, hg, hdg, hfc'⟩ | hreq
      · exact .inl (fin _ (D.initA hadd) hjc hapj g hg hdg hfc')
      · rcases mark_cases a.fact.mark with ham | ⟨t', ham⟩
        · -- The added fact is mark-abstract: the request climbs to the caller.
          have hup := D.reqUp hreq hf he rfl he1 ha ham hov
          rw [den_mark_star hda ham] at hup
          exact .inr hup
        · -- The added fact is concrete: it answers the request.
          have hmk := den_mark_conc hda ham
          have hans := D.answer hreq hadd hmk hov
          have hap' := answerInit_applicable hapj hmk
          have hc' := answerInit_covers (t := l1.mark) hjc hac rfl
          rcases ihc _ hans hc' with ⟨g, hg, hdg, hfc'⟩ | hreq'
          · exact .inl (fin _ hans hc' hap' g hg hdg hfc')
          · exfalso
            have hst := req_initial_star P counted L α sinks roots hreq'
            rw [answerInit_mark] at hst
            cases hst
    · exact .inr hr

#print axioms coverageD

/-- Coverage of run 1 for a concrete-mark initial fact: it has no request. -/
theorem coverage_concD (hwf : P.WF) (hα : ∀ m a, applicable (α m a) a = true)
    {M : MethodId} {l0 : Loc} {n : Node} {l : Loc} (hfl : Flow P M l0 n l)
    {i : PFact} {t : Mark}
    (hi : Dr (.init M i)) (hc : i.covers l0) (ht : i.mark = .conc t) :
    ∃ f, Dr (.edge M i n f) ∧ den i f.fact l0 l ∧ FlowR P (summaryDemand P Dr) M l0 n l := by
  rcases coverageD P counted L α sinks roots hwf hα hfl i hi hc with h | hr
  · exact h
  · exfalso
    have hst := req_initial_star P counted L α sinks roots hr
    rw [ht] at hst
    cases hst

#print axioms coverage_concD

/-- The strengthened reach statement of run 1 (as `Coverage.reach_strong`). The concrete
    witness is demanded by the summaries of run 1. -/
theorem reach_strongD (hwf : P.WF) (hα : ∀ m a, applicable (α m a) a = true)
    {M : MethodId} {n : Node} {l : Loc} (hRe : Reach P roots M n l) :
    ReachR P (summaryDemand P Dr) roots M n l ∧
    ∃ l0 i f, Dr (.edge M i n f) ∧ den i f.fact l0 l ∧
      ((∃ t, i.mark = .conc t) ∨
       (i.mark = .star ∧ (Dr (.req M i l0.mark) →
          ∃ i' f', Dr (.edge M i' n f') ∧ den i' f'.fact l0 l ∧ ∃ t, i'.mark = .conc t))) := by
  induction hRe with
  | root hM hfl =>
    obtain ⟨f, hf, hd, hfr⟩ := coverage_concD P counted L α sinks roots hwf hα hfl
      (t := zeroMark) (D.root hM) zeroFact_covers rfl
    exact ⟨ReachR.root hM hfr, zeroLoc, zeroFact, f, hf, hd, .inl ⟨zeroMark, rfl⟩⟩
  | @down M n l n' c e l1 n2 l2 _ he he1 hd1 hfc ih =>
    obtain ⟨hRR, l0, i, f, hf, hd, hdisj⟩ := ih
    -- Bind the caller fact into the callee.
    obtain ⟨a, ha, hda⟩ := bind_in hwf he he1 hd hd1
    have hadd := D.added hf he he1 ha
    have hac : a.fact.covers l1 := den_covers_final hda
    have hapj := hα c.callee a.fact
    have hjc : (α c.callee a.fact).covers l1 := applicable_sound hapj hac
    -- A request on the callee initial fact gets a concrete-mark answer that covers `l1`.
    have key : Dr (.req c.callee (α c.callee a.fact) l1.mark) →
        ∃ j', Dr (.init c.callee j') ∧ j'.covers l1 ∧ ∃ t, j'.mark = .conc t := by
      intro hreq
      have hconc : ∃ a', Dr (.added c.callee a') ∧ a'.covers l1 ∧ a'.mark = .conc l1.mark := by
        rcases mark_cases a.fact.mark with ham | ⟨t', ham⟩
        · have hup := D.reqUp hreq hf he rfl he1 ha ham (overlapB_of_common hac hjc)
          rw [den_mark_star hda ham] at hup
          rcases hdisj with ⟨t, ht⟩ | ⟨_, himp⟩
          · exfalso
            have hst := req_initial_star P counted L α sinks roots hup
            rw [ht] at hst
            cases hst
          · obtain ⟨i', f', hf', hd', t, ht⟩ := himp hup
            obtain ⟨a', ha', hda'⟩ := bind_in hwf he he1 hd' hd1
            obtain ⟨t1, h1⟩ := edge_conc P counted L α sinks roots hf' ht
            obtain ⟨t2, h2⟩ := applyEdge_mark_conc h1 ha'
            exact ⟨a'.fact, D.added hf' he he1 ha', den_covers_final hda', den_mark_conc hda' h2⟩
        · exact ⟨a.fact, hadd, hac, den_mark_conc hda ham⟩
      obtain ⟨a', hadd', hac', hm'⟩ := hconc
      have hans := D.answer hreq hadd' hm' (overlapB_of_common hac' hjc)
      exact ⟨_, hans, answerInit_covers hjc hac' rfl, l1.mark, answerInit_mark⟩
    have mk : ∀ j', Dr (.init c.callee j') → j'.covers l1 →
        FlowR P (summaryDemand P Dr) c.callee l1 n2 l2 →
        ReachR P (summaryDemand P Dr) roots c.callee n2 l2 :=
      fun j' hj' hjc' hfr =>
        ReachR.down (d := ⟨j', none⟩) hRR he he1 hd1 ⟨hj', .inl rfl⟩ hjc' hfr
    rcases coverageD P counted L α sinks roots hwf hα hfc _ (D.initA hadd) hjc with
      ⟨g, hg, hdg, hfr⟩ | hreq
    · refine ⟨mk _ (D.initA hadd) hjc hfr, l1, _, g, hg, hdg, ?_⟩
      rcases mark_cases (α c.callee a.fact).mark with hjm | ⟨t, hjm⟩
      · refine .inr ⟨hjm, fun hreq => ?_⟩
        obtain ⟨j', hj', hjc', t, ht⟩ := key hreq
        obtain ⟨g', hg', hdg', _⟩ :=
          coverage_concD P counted L α sinks roots hwf hα hfc hj' hjc' ht
        exact ⟨j', g', hg', hdg', t, ht⟩
      · exact .inl ⟨t, hjm⟩
    · obtain ⟨j', hj', hjc', t, ht⟩ := key hreq
      obtain ⟨g', hg', hdg', hfr⟩ := coverage_concD P counted L α sinks roots hwf hα hfc hj' hjc' ht
      exact ⟨mk j' hj' hjc' hfr, l1, j', g', hg', hdg', .inl ⟨t, ht⟩⟩

#print axioms reach_strongD

/-- Run 1 makes every concrete witness a demanded witness of its own summary demand. -/
theorem reach_to_reachR (hwf : P.WF) (hα : ∀ m a, applicable (α m a) a = true)
    {M : MethodId} {n : Node} {l : Loc} (hRe : Reach P roots M n l) :
    ReachR P (summaryDemand P Dr) roots M n l :=
  (reach_strongD P counted L α sinks roots hwf hα hRe).1

#print axioms reach_to_reachR

/-- The vulnerability theorem of run 1, with the demanded witness for run 2. -/
theorem vuln_foundD (hwf : P.WF) (hα : ∀ m a, applicable (α m a) a = true)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    (∃ b, Dr (.vuln M n s b)) ∧ ReachR P (summaryDemand P Dr) roots M n l :=
  ⟨vuln_found P counted L α sinks roots hwf hα hRe hs hT hsc,
   reach_to_reachR P counted L α sinks roots hwf hα hRe⟩

#print axioms vuln_foundD

end Run1

/-! ## 4. The iteration -/

/-- The run sequence. Run 0 is the closure `D` with the most abstract fact (`policy1`).
    Run `k + 1` is the restricted closure with the demand `dem k` that the backward run
    after run `k` gives, the field limit `Ls (k + 1)` and the records `recs k`. -/
def runSeq (P : Program) (counted : Acc → Bool) (Ls : Nat → Nat)
    (dem : Nat → MethodId → DemandEdge → Prop) (emit : PFact → PFact → Option PFact)
    (sat : PFact → PFact → Bool) (restrict : PFact → AFact → DemandEdge → Option AFact)
    (recs : Nat → MethodId → PFact × AFact → Prop) (sinks : List (MethodId × Node × PFact))
    (roots : List MethodId) : Nat → Obj → Prop
  | 0     => D P counted (Ls 0) policy1 sinks roots
  | k + 1 => DR P counted (Ls (k + 1)) (dem k) emit sat restrict (recs k) sinks roots

/-- The identity backward step satisfies the backward contract. -/
theorem backward_identity (P : Program) (roots : List MethodId)
    (sinks : List (MethodId × Node × PFact)) (R : Obj → Prop) :
    BackwardContract P roots sinks R (summaryDemand P R) :=
  fun _ _ _ _ _ _ _ _ h => h

#print axioms backward_identity

/-- A backward step that passes on at least the summary demand satisfies the contract. -/
theorem backward_of_superset (P : Program) (roots : List MethodId)
    (sinks : List (MethodId × Node × PFact)) (R : Obj → Prop)
    (dnext : MethodId → DemandEdge → Prop) (h : ∀ m d, summaryDemand P R m d → dnext m d) :
    BackwardContract P roots sinks R dnext :=
  fun _ _ _ _ _ _ _ _ hr => reachR_mono h hr

#print axioms backward_of_superset

section Iteration
variable {P : Program} {counted : Acc → Bool} {Ls : Nat → Nat}
  {dem : Nat → MethodId → DemandEdge → Prop} {emit : PFact → PFact → Option PFact}
  {sat : PFact → PFact → Bool} {restrict : PFact → AFact → DemandEdge → Option AFact}
  {recs : Nat → MethodId → PFact × AFact → Prop} {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId}

/-- The invariant of the iteration: every run keeps the concrete witness demanded by its
    own summaries. -/
theorem iteration_invariant (hwf : P.WF)
    (hE : ∀ k, EmitContractOn (runSeq P counted Ls dem emit sat restrict recs sinks roots (k + 1))
      emit sat)
    (hS : SatContract sat) (hR : RestrictContract restrict)
    (hB : ∀ k, BackwardContract P roots sinks
      (runSeq P counted Ls dem emit sat restrict recs sinks roots k) (dem k))
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, ReachR P (summaryDemand P (runSeq P counted Ls dem emit sat restrict recs sinks roots k))
      roots M n l := by
  intro k
  induction k with
  | zero =>
    exact reach_to_reachR P counted (Ls 0) policy1 sinks roots hwf
      (policy_applicable (fun _ => [])) hRe
  | succ k ih =>
    obtain ⟨hRR, _⟩ := reach_strongR P counted (Ls (k + 1)) (dem k) emit sat restrict (recs k)
      sinks roots hwf (hE k) hS hR (hB k M n l s T hs hT hsc ih)
    exact hRR

#print axioms iteration_invariant

/-- THE ITERATION THEOREM. If each backward step keeps the witnesses that the summaries of
    the previous run carry, then every run of the sequence reports every concrete
    source-to-sink flow. The field limits and the records of the runs are arbitrary. -/
theorem iteration_sound (hwf : P.WF)
    (hE : ∀ k, EmitContractOn (runSeq P counted Ls dem emit sat restrict recs sinks roots (k + 1))
      emit sat)
    (hS : SatContract sat) (hR : RestrictContract restrict)
    (hB : ∀ k, BackwardContract P roots sinks
      (runSeq P counted Ls dem emit sat restrict recs sinks roots k) (dem k))
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, ∃ b, runSeq P counted Ls dem emit sat restrict recs sinks roots k (.vuln M n s b) := by
  intro k
  cases k with
  | zero =>
    exact vuln_found P counted (Ls 0) policy1 sinks roots hwf
      (policy_applicable (fun _ => [])) hRe hs hT hsc
  | succ k =>
    have inv := iteration_invariant (counted := counted) (Ls := Ls) (emit := emit)
      (recs := recs) (sinks := sinks) hwf hE hS hR hB hRe hs hT hsc k
    exact (vuln_foundR P counted (Ls (k + 1)) (dem k) emit sat restrict (recs k) sinks roots
      hwf (hE k) hS hR (hB k M n l s T hs hT hsc inv) hs hT hsc).1

#print axioms iteration_sound

/-- The iteration theorem for version 3: the full emission contract holds on every run. -/
theorem iteration_sound_full (hwf : P.WF) (hE : EmitContract emit sat) (hS : SatContract sat)
    (hR : RestrictContract restrict)
    (hB : ∀ k, BackwardContract P roots sinks
      (runSeq P counted Ls dem emit sat restrict recs sinks roots k) (dem k))
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, ∃ b, runSeq P counted Ls dem emit sat restrict recs sinks roots k (.vuln M n s b) :=
  iteration_sound hwf (fun _ => hE.on _) hS hR hB hRe hs hT hsc

#print axioms iteration_sound_full

/-- The iteration theorem for version 4 (`emitM`): the contract for concrete added facts and a
    mark-copying emission. Every restricted run is concrete, so the contract holds on it. -/
theorem iteration_sound_conc (hwf : P.WF) (hE : EmitContractConc emit sat)
    (hcm : EmitCopiesMark emit) (hS : SatContract sat) (hR : RestrictContract restrict)
    (hB : ∀ k, BackwardContract P roots sinks
      (runSeq P counted Ls dem emit sat restrict recs sinks roots k) (dem k))
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, ∃ b, runSeq P counted Ls dem emit sat restrict recs sinks roots k (.vuln M n s b) :=
  iteration_sound hwf
    (fun k => emitOn_of_conc P counted (Ls (k + 1)) (dem k) emit sat restrict (recs k) sinks roots
      hE hcm)
    hS hR hB hRe hs hT hsc

#print axioms iteration_sound_conc

end Iteration

/-- The run sequence with the identity backward step: run `k + 1` follows the summary
    demand of run `k`. -/
def runSeqId (P : Program) (counted : Acc → Bool) (Ls : Nat → Nat)
    (emit : PFact → PFact → Option PFact) (sat : PFact → PFact → Bool)
    (restrict : PFact → AFact → DemandEdge → Option AFact)
    (recs : Nat → MethodId → PFact × AFact → Prop) (sinks : List (MethodId × Node × PFact))
    (roots : List MethodId) : Nat → Obj → Prop
  | 0     => D P counted (Ls 0) policy1 sinks roots
  | k + 1 => DR P counted (Ls (k + 1))
      (summaryDemand P (runSeqId P counted Ls emit sat restrict recs sinks roots k))
      emit sat restrict (recs k) sinks roots

/-- `runSeqId` is `runSeq` with the demand of the identity backward step. -/
theorem runSeqId_eq (P : Program) (counted : Acc → Bool) (Ls : Nat → Nat)
    (emit : PFact → PFact → Option PFact) (sat : PFact → PFact → Bool)
    (restrict : PFact → AFact → DemandEdge → Option AFact)
    (recs : Nat → MethodId → PFact × AFact → Prop) (sinks : List (MethodId × Node × PFact))
    (roots : List MethodId) (k : Nat) :
    runSeqId P counted Ls emit sat restrict recs sinks roots k =
      runSeq P counted Ls
        (fun k => summaryDemand P (runSeqId P counted Ls emit sat restrict recs sinks roots k))
        emit sat restrict recs sinks roots k := by
  cases k <;> rfl

#print axioms runSeqId_eq

/-- The iteration theorem for the identity backward step: no backward contract is needed. -/
theorem iteration_sound_identity {P : Program} {counted : Acc → Bool} {Ls : Nat → Nat}
    {emit : PFact → PFact → Option PFact} {sat : PFact → PFact → Bool}
    {restrict : PFact → AFact → DemandEdge → Option AFact}
    {recs : Nat → MethodId → PFact × AFact → Prop} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId}
    (hwf : P.WF)
    (hE : ∀ k, EmitContractOn (runSeqId P counted Ls emit sat restrict recs sinks roots (k + 1))
      emit sat)
    (hS : SatContract sat) (hR : RestrictContract restrict)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, ∃ b, runSeqId P counted Ls emit sat restrict recs sinks roots k (.vuln M n s b) := by
  intro k
  rw [runSeqId_eq]
  refine iteration_sound hwf (fun k' => ?_) hS hR ?_ hRe hs hT hsc k
  · rw [← runSeqId_eq]
    exact hE k'
  intro k'
  show BackwardContract P roots sinks _
    (summaryDemand P (runSeqId P counted Ls emit sat restrict recs sinks roots k'))
  rw [runSeqId_eq P counted Ls emit sat restrict recs sinks roots k']
  exact backward_identity P roots sinks _

#print axioms iteration_sound_identity

end ApSpec.RCov

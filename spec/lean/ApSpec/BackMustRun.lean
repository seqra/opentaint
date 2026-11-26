/-
  ApSpec.BackMustRun — the BACKWARD RUN WITH MUST-PREMISES: the backward `[any-taint]` seed (B1),
  the MAY-class demotion of the reversed statement edges (B1), and the backward MUST added facts,
  must-premises and MUST records (B2); their PRECISION on the reversed program and, through the
  reversal, on the forward program.

  Namespace: `ApSpec.BackMust`. The forward refined model (`AnyTaintExDefs.lean`,
  `AnyTaintExExact.lean`), the base backward closure (`Backward.lean`, `BackwardExact.lean`) and the
  reversal bridge (`Reverse.lean`) are used unchanged.

  ## What this file models

  The backward run is `DBX`: the rules of the forward refined restricted run `AnyTaintEx.DRX` on the
  reversed program `Pb` (annotated facts `XFact`, must-premises, premise exclusions, `startX`,
  `emitTX`, `bindX`, `applySummaryX`, `recLayerX`, `limitFX`, `cleanResX`, `checkX`), plus the zero
  rules of `Backward.DB` (the user's design, `zbind = true`) in the `XObj` form: `zpass`, `zin`
  (`.init c.callee zeroFact false {}`), `seed`, `zret`.
    * B1, the seed: a seed is `(M, n, s, must)`; it gives `limitFX counted L ((s, demand = !must), {})`:
      a MUST seed (a single-literal sink with an `[any]` pattern) is a NORMAL requirement (the
      backward `[any-taint]`, empty exclusion), an ND seed (`must = false`) a DEMAND one.
    * B1, the statement transfer `transferXB bmay`: `transferX` with `taint := fun _ => true` (no W6T
      demotion in the backward run), then `w6bX bmay e` per micro edge: an edge of the MAY class
      (`bmay e = true`: the reversal of a forward pass-rule `AnyField` target or of an ND conjunction
      literal) demotes its results to DEMAND (no exclusion); every other edge, including an edge with
      an `.any` TARGET in `Pb` (the reversed single `[any]` condition literal), keeps the layer.
    * B2: the rule `added` makes a normal `.any` added fact a MUST added fact (`am`); `initR` emits a
      must-premise from it (`emitTX`); its start (`startX`) is NORMAL; its normal exit edges with a
      non-zero premise are the backward MUST records (`exitRecsNZ`).

  ## Main results (all constructive; see the `#print axioms` lines)

  1. `transferXB_normal`: a NORMAL result of `transferXB` is a result of `transferX (fun _ => true)`
     with the same `XFact` (so `transferX_exact`, `transferX_cov` apply); `transferXB_cases`,
     `transferXB_wf`, `transferXB_reqs`.
  2. The closure `DBX` and its invariants `DBX_wf`, `DBX_mustAny`, `DBX_conc`.
  3. MAIN: `DBX_edgeOK_nz`: every edge of `DBX` whose premise is not the zero fact satisfies
     `EdgeOKX Pb ok` (a normal edge of a non-must premise is PAIR-EXACT, of a must-premise
     END-EXACT, on the admitted locations). A full mirror of `DRX_edgeOK`, no open case. Corollary
     `edge_exactBX_gen`.
  4. `recsB_exact`: the exit edges with a non-zero premise (`exitRecsNZ`) satisfy `RecsExactX Pb ok`
     (`recsB_must_end`: a backward MUST record is END-EXACT; `recsB_pair`: a non-must one
     PAIR-EXACT); `recsB_next`, `recsBSeq_ok`: over a sequence of backward runs the records satisfy
     the record hypotheses again (no record hypothesis left).
  5. `must_seed_normal` (a must `.any` concrete seed gives a NORMAL `.any` edge, `carriesB`),
     `must_added`, `bindX_star_any`, `must_seed_bound` (bound into a callee by `b.* → b'.*`: a MUST
     added fact, `am = true`), `must_premise_normal` (the emission gives a must-premise, its start is
     NORMAL), `must_premise_endExact`; the contrast `demand_seed_contrast`, `demand_premise_start`
     (a demand seed: `am = false`, a non-must premise, a DEMAND start).
  6. `backMust_forward`: for `Pb = Program.rev P`, a normal backward MUST record `jb (must, jex) → gb`
     at the backward exit: every admitted location `l` of `gb` at the forward entry flows in `P` to
     SOME admitted location `l0` of `jb` at the forward exit (`Flow P M l (P.exit M) l0`);
     `backPair_forward` (the pair form of a non-must premise), `backMust_forward_valid` (S13),
     `backMust_forward_seq` (the spec rules over the backward sequence: no record hypothesis).
  7. Counterexample `CexMustPair.cex_must_pair` (executable, all hypotheses of `recsB_exact` hold):
     the B1/B2 chain derives a backward MUST record that is END-EXACT but NOT PAIR-EXACT (so a MUST
     record must be read END-EXACT), and a NORMAL zero-premise `[any-taint]` exit edge (the must
     seed) that is not exact (so the motive and `exitRecsNZ` must exclude the zero premise).

  ## NEW HYPOTHESES (each with the spec item that makes it true)

  The hypotheses of `DRX_edgeOK` on `Pb` (S7 `MarkWF`, `FiltOK`/`BackOK` (S13 or `FiltUp`),
  `SatInsideX sat`, `RestrictOKX restrict`, `EmitCopiesMarkX emit`; the spec rules have them,
  `specX_rules`), and:
    * `NoZeroIn Pb`: no reversed call binds into the callee's zero base. For `Pb = Program.rev P` it
      is `Backward.NoZeroBack P` (`noZeroIn_rev`), the hypothesis of `Backward.B_general`: the zero
      fact enters a callee only by `zin`. Necessity: `BExact.CexZeroBack` (base backward run).
    * `SeedsConcB seeds`: every seed has a concrete mark (a seed is a sink pattern `(b, P, k, T)`,
      `BExact.SeedsConc`). Necessity: `BExact.CexSeed` (a `*` seed gives a request). No hypothesis
      on the tail of a seed: the concreteness motive `ConcObjB` excludes the `*` tail only on edges
      of a non-zero premise.
    * The record hypotheses are WEAKER than those of `DRX_edgeOK`: `RecsExactXNZ`, `RecsConcXNZ`,
      `RecsWFXNZ` ask exactness, concreteness and normal form only of the records whose premise is
      OFF THE ZERO BASE (a record with a zero-based premise never applies under `NoZeroIn`,
      `no_zero_summaryX`). So the hypothesis "every record premise is not `zeroFact`" is NOT needed.
      B2 (the persisted records are the non-zero-premise exit edges of earlier backward runs)
      discharges them: `recsBSeq_ok`.
  No hypothesis on `bmay`, the demand, the sinks, the roots or the must flags of the seeds.
  Item 6 adds `RevStmts P`, `RevCalls P` (`Reverse.flow_rev_iff_calls`) and transports `MarkWF P`,
  `FiltUp P` (or `FiltValid P ok`), `NoZeroBack P` by `markWF_rev`, `filtUp_rev`, `filtValid_rev`,
  `noZeroIn_rev`.

  ## Differences between the model and production

    * THE MAY CLASS IS INVISIBLE TO THE MODEL. `bmay` is a free parameter and every theorem holds
      for every `bmay`, also `fun _ => false`: the model's statement semantics is the denotation of
      the micro edges (`Stmt.step`), and a forward `AnyField` target `x.* → y.[any]` relates each
      `x.σ` to EVERY `y.τ` (uncorrelated `.any`), so its reversal `y.[any] → x.[any]` is exact in the
      model (`RevStmts`). In production the target is a MAY (`x.σ` reaches ONE unknown `y.τ`), so
      (informally) the reversed edge is a MUST only on an input requirement that covers its whole
      premise. The demotion of B1 is a production fact that the model neither justifies nor
      refutes.
    * The must flag of a seed is an input (`seeds`); the model does not decide which sinks are
      single-literal `[any]` sinks. A must seed with a `$` pattern is a normal `$` seed (in
      `Backward.DB` every seed is normal).
    * `zbind` is fixed to `true` (the user's design); the plain reversal is not modeled.
    * The persisted records are ALL non-zero-premise exit edges (`exitRecsNZ`, `recsBSeq`); a
      production policy that persists a subset satisfies the same record hypotheses.
    * The backward run uses the forward refined operations unchanged (bindings, summaries, records,
      cleaners, the field limit `LB k` per run). The rules `reqSink`, `answer`, `reqUp`, `vuln` are
      kept for the mirror of `DRX` (in use the backward run is given no forward sink; for the base
      run, concrete seeds give no request, `BExact.DB_no_request`; not re-proved for `DBX`).
-/
import ApSpec.AnyTaintExExact
import ApSpec.BackwardExact

namespace ApSpec.BackMust
open ApSpec ApSpec.AnyTaint ApSpec.AnyTaintEx ApSpec.AnyTaintExExact ApSpec.Reverse
  ApSpec.Backward ApSpec.BExact

/-! ## 1. The backward statement transfer (B1) -/

/-- The MAY class of the reversed statement micro edges (B1): `bmay e = true` for the reversal of a
    forward pass-rule `AnyField` target and of an ND conjunction literal. -/
abbrev BMay := MicroEdge → Bool

/-- The backward demotion (B1): a result of a MAY-class micro edge goes to the DEMAND layer and drops
    its exclusion (the normal form of `w6tX`, `recLayerX`). Every other micro edge keeps the layer,
    including an edge with an `.any` TARGET in `Pb` (the reversed single `[any]` condition literal). -/
def w6bX (bmay : BMay) (e : MicroEdge) (x : XFact) : XFact :=
  if bmay e then ⟨⟨x.af.fact, true⟩, Excl.empty⟩ else x

/-- One reversed statement micro edge: `applyEdgeXT` with `taint := fun _ => true` (no W6T demotion
    in the backward run), then `w6bX`. -/
def applyEdgeXB (bmay : BMay) (c : XFact) (e : MicroEdge) : ResX :=
  ⟨(applyEdgeXT (fun _ => true) c e).facts.map (w6bX bmay e), (applyEdgeXT (fun _ => true) c e).reqs⟩

/-- `applyEdgeXB` on each micro edge of a statement. -/
def applyAllXB (bmay : BMay) (c : XFact) : List MicroEdge → ResX
  | []      => ResX.none
  | e :: es => (applyEdgeXB bmay c e).append (applyAllXB bmay c es)

/-- THE BACKWARD STATEMENT TRANSFER (B1): `transferX` with `taint := fun _ => true`, then `w6bX`
    per micro edge, then the field limit `limitFX`. -/
def transferXB (bmay : BMay) (counted : Acc → Bool) (L : Nat) (s : Stmt) (c : XFact) : ResX :=
  if memB c.af.fact.base s.touched then
    let r := applyAllXB bmay c s.edges
    ⟨r.facts.map (limitFX counted L), r.reqs⟩
  else ⟨[c], []⟩

/-- The zero fact as an annotated normal fact (the start fact of the zero premise). -/
def zeroX : XFact := ⟨zeroAF, Excl.empty⟩

theorem startX_zero : startX zeroFact false Excl.empty = zeroX := rfl

/-- A normal result of `w6bX` is its input. -/
theorem w6bX_normal {bmay : BMay} {e : MicroEdge} {z : XFact}
    (h : (w6bX bmay e z).af.demand = false) : w6bX bmay e z = z := by
  unfold w6bX at h ⊢
  cases hb : bmay e with
  | false => exact if_neg Bool.false_ne_true
  | true => rw [hb, if_pos rfl] at h; cases h

theorem applyAllXB_mem {bmay : BMay} {c x : XFact} :
    ∀ {es : List MicroEdge}, x ∈ (applyAllXB bmay c es).facts →
      ∃ e, e ∈ es ∧ ∃ z, z ∈ (applyEdgeXT (fun _ => true) c e).facts ∧ x = w6bX bmay e z
  | [], h => absurd h List.not_mem_nil
  | e :: es, h => by
    have h' : x ∈ (applyEdgeXB bmay c e).facts ++ (applyAllXB bmay c es).facts := h
    rcases List.mem_append.mp h' with h1 | h1
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp h1
      exact ⟨e, List.mem_cons_self .., z, hz, rfl⟩
    · obtain ⟨e', he', z, hz, hx⟩ := applyAllXB_mem h1
      exact ⟨e', List.mem_cons_of_mem _ he', z, hz, hx⟩

theorem applyAllXT_of_mem {taint : TaintEdges} {c z : XFact} :
    ∀ {es : List MicroEdge} {e : MicroEdge}, e ∈ es → z ∈ (applyEdgeXT taint c e).facts →
      z ∈ (applyAllXT taint c es).facts
  | [], _, he, _ => absurd he List.not_mem_nil
  | e' :: es, e, he, hz => by
    show z ∈ (applyEdgeXT taint c e').facts ++ (applyAllXT taint c es).facts
    rcases List.mem_cons.mp he with rfl | he'
    · exact List.mem_append_left _ hz
    · exact List.mem_append_right _ (applyAllXT_of_mem he' hz)

/-- 1a. A NORMAL result of the backward transfer is a result of the forward refined transfer with
    `taint := fun _ => true`, with the same annotated fact (so `transferX_exact`, `transferX_cov`
    apply to it). -/
theorem transferXB_normal {bmay : BMay} {counted : Acc → Bool} {L : Nat} {s : Stmt} {c x : XFact}
    (h : x ∈ (transferXB bmay counted L s c).facts) (hxa : x.af.demand = false) :
    x ∈ (transferX (fun _ => true) counted L s c).facts := by
  unfold transferXB at h
  unfold transferX
  cases hm : memB c.af.fact.base s.touched with
  | false =>
    rw [hm, if_neg Bool.false_ne_true] at h
    rw [if_neg Bool.false_ne_true]
    exact h
  | true =>
    rw [hm, if_pos rfl] at h
    rw [if_pos rfl]
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp h
    have e0 := limitFX_normal hxa
    have hya : y.af.demand = false := by rw [← e0]; exact hxa
    obtain ⟨e, he, z, hz, rfl⟩ := applyAllXB_mem hy
    rw [w6bX_normal hya]
    exact List.mem_map.mpr ⟨z, applyAllXT_of_mem he hz, rfl⟩

#print axioms transferXB_normal

/-- The backward transfer has the requests of the forward refined transfer. -/
theorem applyAllXB_reqs (bmay : BMay) (c : XFact) :
    ∀ (es : List MicroEdge), (applyAllXB bmay c es).reqs = (applyAllXT (fun _ => true) c es).reqs
  | [] => rfl
  | e :: es => by
    show (applyEdgeXT (fun _ => true) c e).reqs ++ (applyAllXB bmay c es).reqs =
      (applyEdgeXT (fun _ => true) c e).reqs ++ (applyAllXT (fun _ => true) c es).reqs
    rw [applyAllXB_reqs bmay c es]

theorem transferXB_reqs (bmay : BMay) (counted : Acc → Bool) (L : Nat) (s : Stmt) (c : XFact) :
    (transferXB bmay counted L s c).reqs = (transferX (fun _ => true) counted L s c).reqs := by
  unfold transferXB transferX
  cases memB c.af.fact.base s.touched
  · rfl
  · exact applyAllXB_reqs bmay c s.edges

#print axioms transferXB_reqs

theorem limitFX_ex_empty {counted : Acc → Bool} {L : Nat} {x : XFact} (h : x.ex = Excl.empty) :
    (limitFX counted L x).ex = Excl.empty := by
  unfold limitFX
  cases cutPath counted L x.af.fact.path
  · exact h
  · rfl

/-- 1b. Every result of the backward transfer has the fact of a result of the forward refined
    transfer; it is that result, or it carries no exclusion (a demoted result). -/
theorem transferXB_cases {bmay : BMay} {counted : Acc → Bool} {L : Nat} {s : Stmt} {c x : XFact}
    (h : x ∈ (transferXB bmay counted L s c).facts) :
    ∃ y, y ∈ (transferX (fun _ => true) counted L s c).facts ∧ x.af.fact = y.af.fact ∧
      (x = y ∨ x.ex = Excl.empty) := by
  unfold transferXB at h
  unfold transferX
  cases hm : memB c.af.fact.base s.touched with
  | false =>
    rw [hm, if_neg Bool.false_ne_true] at h
    rw [if_neg Bool.false_ne_true]
    exact ⟨x, h, rfl, Or.inl rfl⟩
  | true =>
    rw [hm, if_pos rfl] at h
    rw [if_pos rfl]
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp h
    obtain ⟨e, he, z, hz, rfl⟩ := applyAllXB_mem hy
    refine ⟨limitFX counted L z, List.mem_map.mpr ⟨z, applyAllXT_of_mem he hz, rfl⟩, ?_⟩
    unfold w6bX
    cases bmay e with
    | false => exact ⟨rfl, Or.inl rfl⟩
    | true =>
      refine ⟨?_, Or.inr (limitFX_ex_empty rfl)⟩
      rw [limitFX_af, limitFX_af]
      exact limitF_fact_eq rfl

#print axioms transferXB_cases

/-- The backward transfer keeps the normal form. -/
theorem transferXB_wf {bmay : BMay} {counted : Acc → Bool} {L : Nat} {s : Stmt} {c x : XFact}
    (hc : WFX c) (h : x ∈ (transferXB bmay counted L s c).facts) : WFX x := by
  obtain ⟨y, hy, _, hxy⟩ := transferXB_cases h
  rcases hxy with rfl | he
  · exact transferX_wf hc hy
  · exact fun _ => he

#print axioms transferXB_wf

/-- A normal backward statement result comes from a normal input. -/
theorem transferXB_demand {bmay : BMay} {counted : Acc → Bool} {L : Nat} {s : Stmt} {c x : XFact}
    (h : x ∈ (transferXB bmay counted L s c).facts) (hxa : x.af.demand = false) :
    c.af.demand = false :=
  transferX_demand (transferXB_normal h hxa) hxa

theorem transferXB_nonstar {bmay : BMay} {counted : Acc → Bool} {L : Nat} {s : Stmt} {c x : XFact}
    (hc : c.af.fact.kind.isStar = false) (h : x ∈ (transferXB bmay counted L s c).facts) :
    x.af.fact.kind.isStar = false := by
  obtain ⟨y, hy, hxy, _⟩ := transferXB_cases h
  rw [hxy]
  exact transferX_nonstar hc hy

theorem transferXB_conc {bmay : BMay} {counted : Acc → Bool} {L : Nat} {s : Stmt} {c x : XFact}
    {t : Mark} (hc : c.af.fact.mark = .conc t) (h : x ∈ (transferXB bmay counted L s c).facts) :
    ∃ t', x.af.fact.mark = .conc t' := by
  obtain ⟨y, hy, hxy, _⟩ := transferXB_cases h
  obtain ⟨y1, hy1, hfy, _⟩ := transferX_base hy
  obtain ⟨y0, hy0, hle⟩ := transferT_mem hy1
  obtain ⟨t', ht'⟩ := transfer_mark_conc hc hy0
  exact ⟨t', by rw [hxy, hfy, ← hle.fact]; exact ht'⟩


/-! ## 2. The backward closure with must-premises (B1, B2) -/

section ClosureB
variable (Pb : Program) (bmay : BMay) (counted : Acc → Bool) (L : Nat)
  (demand : MethodId → DemandEdge → Prop)
  (emit : PFact → PFact → Excl → Option (PFact × Excl))
  (sat : PFact → Excl → PFact → Excl → Bool)
  (restrict : PFact → Excl → XFact → DemandEdge → Option XFact)
  (recs : MethodId → PFact × Bool × Excl × XFact → Prop)
  (sinks : List (MethodId × Node × PFact))
  (roots : List MethodId)
  (seeds : List (MethodId × Node × PFact × Bool))

/-- THE BACKWARD RUN WITH MUST-PREMISES (B1, B2): the rules of `AnyTaintEx.DRX` on the reversed
    program `Pb` (with `transferXB` for `step`, `reqStmt`), and the zero rules of `Backward.DB` (the
    user's design, `zbind = true`) in the `XObj` form. A seed `(M, n, s, must)`: `must = true` is a
    single-literal sink with an `[any]` pattern, its requirement is NORMAL (the backward
    `[any-taint]`, empty exclusion); `must = false` (an ND seed) stays DEMAND. The rule `added`
    makes a normal `.any` added fact a MUST added fact (`am`), and `initR` emits a must-premise
    from it (B2). -/
inductive DBX : XObj → Prop where
  | root {M} : M ∈ roots → DBX (.init M zeroFact false Excl.empty)
  | start {M j mj jex} :
      DBX (.init M j mj jex) → DBX (.edge M j mj jex (Pb.entry M) (startX j mj jex))
  | step {M i mi iex n f n' s f'} :
      DBX (.edge M i mi iex n f) → (M, n, Instr.stmt s, n') ∈ Pb.edges →
      f' ∈ (transferXB bmay counted L s f).facts → DBX (.edge M i mi iex n' f')
  | reqStmt {M i mi iex n f n' s t} :
      DBX (.edge M i mi iex n f) → (M, n, Instr.stmt s, n') ∈ Pb.edges →
      t ∈ (transferXB bmay counted L s f).reqs → DBX (.req M i t)
  | pass {M i mi iex n f n' c} :
      DBX (.edge M i mi iex n f) → (M, n, Instr.call c, n') ∈ Pb.edges →
      memB f.af.fact.base c.touched = false → DBX (.edge M i mi iex n' f)
  | added {M i mi iex n f n' c e a} :
      DBX (.edge M i mi iex n f) → (M, n, Instr.call c, n') ∈ Pb.edges →
      e ∈ c.toCallee → a ∈ (bindX f e).facts →
      DBX (.added c.callee a.af.fact (a.af.fact.kind.isAny && !a.af.demand) a.ex)
  | initR {m a am aex d j mj jex} :
      DBX (.added m a am aex) → demand m d → emitTX emit d.din a am aex = some (j, mj, jex) →
      DBX (.init m j mj jex)
  | ret {M i mi iex n f n' c e1 a j mj jex g d g' r e2 r'} :
      DBX (.edge M i mi iex n f) → (M, n, Instr.call c, n') ∈ Pb.edges →
      e1 ∈ c.toCallee → a ∈ (bindX f e1).facts →
      DBX (.init c.callee j mj jex) →
      DBX (.edge c.callee j mj jex (Pb.exit c.callee) g) →
      demand c.callee d → restrict j jex g d = some g' →
      sat j jex a.af.fact a.ex = true →
      r ∈ (applySummaryX a j jex g').facts →
      e2 ∈ c.fromCallee → r' ∈ (bindX r e2).facts →
      DBX (.edge M i mi iex n' (limitFX counted L r'))
  | retRec {M i mi iex n f n' c e1 a j mj jex g r e2 r'} :
      DBX (.edge M i mi iex n f) → (M, n, Instr.call c, n') ∈ Pb.edges →
      e1 ∈ c.toCallee → a ∈ (bindX f e1).facts →
      recs c.callee (j, mj, jex, g) →
      (sat j jex a.af.fact a.ex = true ∨ applicable j a.af.fact = true) →
      r ∈ (applySummaryX a j jex g).facts →
      e2 ∈ c.fromCallee → r' ∈ (bindX r e2).facts →
      DBX (.edge M i mi iex n' (limitFX counted L (recLayerX mj (sat j jex a.af.fact a.ex) r')))
  | reqSink {M i mi iex n f s t} :
      DBX (.edge M i mi iex n f) → (M, n, s) ∈ sinks → checkX i f s = .request t →
      DBX (.req M i t)
  | answer {M i t a am aex} :
      DBX (.req M i t) → DBX (.added M a am aex) → a.mark = .conc t →
      overlapX a aex i Excl.empty = true → DBX (.init M (answerInit i a t) false Excl.empty)
  | reqUp {m j t M ic mc icx n f n' c e a} :
      DBX (.req m j t) → DBX (.edge M ic mc icx n f) → (M, n, Instr.call c, n') ∈ Pb.edges →
      c.callee = m → e ∈ c.toCallee → a ∈ (bindX f e).facts →
      climbsB a.af.fact.mark t = true → overlapX a.af.fact a.ex j Excl.empty = true →
      DBX (.req M ic t)
  | vuln {M i mi iex n f s} :
      DBX (.edge M i mi iex n f) → (M, n, s) ∈ sinks → checkX i f s = .triggered →
      DBX (.vuln M n s f.af.demand)
  | clean {M i mi iex n f n' cl f'} :
      DBX (.edge M i mi iex n f) → (M, n, Instr.clean cl, n') ∈ Pb.edges →
      f' ∈ (cleanResX cl f).facts → DBX (.edge M i mi iex n' f')
  | reqClean {M i mi iex n f n' cl t} :
      DBX (.edge M i mi iex n f) → (M, n, Instr.clean cl, n') ∈ Pb.edges →
      t ∈ (cleanResX cl f).reqs → DBX (.req M i t)
  | filt {M i mi iex n f n' b may} :
      DBX (.edge M i mi iex n f) → (M, n, Instr.filt b may, n') ∈ Pb.edges →
      (f.af.fact.base = b → may f.af.fact.path = true) → DBX (.edge M i mi iex n' f)
  -- the zero fact passes over every call
  | zpass {M n n' c} :
      DBX (.edge M zeroFact false Excl.empty n zeroX) → (M, n, Instr.call c, n') ∈ Pb.edges →
      DBX (.edge M zeroFact false Excl.empty n' zeroX)
  -- the zero fact enters every callee through its own binding (at the callee's backward entry)
  | zin {M n n' c} :
      DBX (.edge M zeroFact false Excl.empty n zeroX) → (M, n, Instr.call c, n') ∈ Pb.edges →
      DBX (.init c.callee zeroFact false Excl.empty)
  -- the sink rule (B1): a must seed is a NORMAL requirement, an ND seed a DEMAND one
  | seed {M n s must} : (M, n, s, must) ∈ seeds →
      DBX (.edge M zeroFact false Excl.empty n zeroX) →
      DBX (.edge M zeroFact false Excl.empty n (limitFX counted L ⟨⟨s, !must⟩, Excl.empty⟩))
  -- the balanced return of a zero-premise callee summary
  | zret {M n n' c g r e2 r'} :
      DBX (.edge M zeroFact false Excl.empty n zeroX) → (M, n, Instr.call c, n') ∈ Pb.edges →
      DBX (.edge c.callee zeroFact false Excl.empty (Pb.exit c.callee) g) →
      r ∈ (applySummaryX zeroX zeroFact Excl.empty g).facts →
      e2 ∈ c.fromCallee → r' ∈ (bindX r e2).facts →
      DBX (.edge M zeroFact false Excl.empty n' (limitFX counted L r'))

end ClosureB

/-! ## 3. Invariants of `DBX`: normal form, must-premises, concreteness -/

/-- The seeds have concrete marks (a seed is a sink pattern `s.mark = .conc T`; `BExact.SeedsConc`
    in the 4-tuple form). -/
def SeedsConcB (seeds : List (MethodId × Node × PFact × Bool)) : Prop :=
  ∀ M n s must, (M, n, s, must) ∈ seeds → ∃ t, s.mark = .conc t

/-- The concreteness motive of `DBX` (`AnyTaintExExact.ConcObjX` with the `*` tail excluded only on
    the edges of a NON-ZERO premise: a seed may have any tail). -/
def ConcObjB : XObj → Prop
  | .init _ j _ _ => ∃ t, j.mark = .conc t
  | .edge _ j _ _ _ f =>
    (∃ t, j.mark = .conc t) ∧ (∃ t, f.af.fact.mark = .conc t) ∧
      (j ≠ zeroFact → f.af.fact.kind.isStar = false)
  | .added _ a _ _ => ∃ t, a.mark = .conc t
  | _ => True

section Inv
variable {Pb : Program} {bmay : BMay} {counted : Acc → Bool} {L : Nat}
  {demand : MethodId → DemandEdge → Prop}
  {emit : PFact → PFact → Excl → Option (PFact × Excl)}
  {sat : PFact → Excl → PFact → Excl → Bool}
  {restrict : PFact → Excl → XFact → DemandEdge → Option XFact}
  {recs : MethodId → PFact × Bool × Excl × XFact → Prop}
  {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId}
  {seeds : List (MethodId × Node × PFact × Bool)}

/-- Every edge conclusion of `DBX` is in normal form (no hypothesis). -/
theorem DBX_wf {o : XObj}
    (h : DBX Pb bmay counted L demand emit sat restrict recs sinks roots seeds o) : WFObjX o := by
  induction h with
  | root => trivial
  | @start M j mj jex _ _ => exact startX_wf j mj jex
  | @step M i mi iex n f n' s f' _ _ hf ih => exact transferXB_wf ih hf
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
  | zpass => exact wf_empty _
  | zin => trivial
  | seed => exact limitFX_wf counted L (wf_empty _)
  | @zret M n n' c g r e2 r' _ _ _ _ _ hr' _ _ => exact limitFX_wf counted L (applyEdgeX_wf hr')

#print axioms DBX_wf

theorem DBX_wf_edge {M : MethodId} {i : PFact} {mi : Bool} {iex : Excl} {n : Node} {f : XFact}
    (h : DBX Pb bmay counted L demand emit sat restrict recs sinks roots seeds
      (.edge M i mi iex n f)) : WFX f := DBX_wf h

/-- A must-premise of `DBX` has the `.any` tail (no hypothesis). -/
theorem DBX_mustAny {o : XObj}
    (h : DBX Pb bmay counted L demand emit sat restrict recs sinks roots seeds o) : MustAnyX o := by
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
  | zpass => trivial
  | zin => trivial
  | seed => trivial
  | zret => trivial

#print axioms DBX_mustAny

/-- CONCRETENESS of `DBX` (a mark-copying emission and concrete seeds): every premise, conclusion
    and added fact has a concrete mark; no conclusion of a non-zero premise has the `*` tail. -/
theorem DBX_conc (hem : EmitCopiesMarkX emit) (hsd : SeedsConcB seeds) {o : XObj}
    (h : DBX Pb bmay counted L demand emit sat restrict recs sinks roots seeds o) :
    ConcObjB o := by
  induction h with
  | root => exact ⟨zeroMark, rfl⟩
  | @start M j mj jex hJ ih =>
    refine ⟨ih, ?_, fun _ => ?_⟩
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
        rw [(DBX_mustAny hJ : j.kind = .any)]
        rfl
  | @step M i mi iex n f n' s f' _ _ hf ih =>
    obtain ⟨hi, ⟨tf, htf⟩, hfns⟩ := ih
    exact ⟨hi, transferXB_conc htf hf, fun hz => transferXB_nonstar (hfns hz) hf⟩
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
    refine ⟨hi, ⟨t3, by rw [limitFX_af, Exact.limitF_mark]; exact ht3⟩, fun hz => ?_⟩
    exact limitFX_nonstar (applyEdgeX_nonstar
      (applySummaryX_nonstar (applyEdgeX_nonstar (hfns hz) ha) hr) hr')
  | @retRec M i mi iex n f n' c e1 a j mj jex g r e2 r' _ _ _ ha _ _ hr _ hr' ihF =>
    obtain ⟨hi, ⟨tf, htf⟩, hfns⟩ := ihF
    obtain ⟨ya, hya, hay, _⟩ := applyEdgeX_base ha
    obtain ⟨ta, hta⟩ := conc_of_fact hay (applyEdge_mark_conc htf hya)
    obtain ⟨yr, hyr, hry, _⟩ := applySummaryX_base hr
    obtain ⟨tr, htr⟩ := conc_of_fact hry (applySummary_mark_conc hta hyr)
    obtain ⟨yr', hyr', hry', _⟩ := applyEdgeX_base hr'
    obtain ⟨t3, ht3⟩ := conc_of_fact hry' (applyEdge_mark_conc htr hyr')
    refine ⟨hi, ⟨t3, ?_⟩, fun hz => ?_⟩
    · rw [limitFX_af, Exact.limitF_mark, recLayerX_af, recLayer_fact]; exact ht3
    · apply limitFX_nonstar
      rw [recLayerX_af, recLayer_fact]
      exact applyEdgeX_nonstar (applySummaryX_nonstar (applyEdgeX_nonstar (hfns hz) ha) hr) hr'
  | reqSink => trivial
  | @answer M i t a am aex _ _ _ _ _ _ => exact answerInit_conc i a t
  | reqUp => trivial
  | vuln => trivial
  | @clean M i mi iex n f n' cl f' hF _ hf ih =>
    obtain ⟨hi, ⟨tf, htf⟩, hfns⟩ := ih
    rcases cleanResX_base (DBX_wf_edge hF) hf with ⟨y, hy, hxy, _⟩ | ⟨_, _, _, _, rfl⟩
    · exact ⟨hi, conc_of_fact hxy (cleanRes_mark_conc htf hy),
        fun hz => cleanResX_nonstar (DBX_wf_edge hF) (hfns hz) hf⟩
    · exact ⟨hi, ⟨tf, htf⟩, fun _ => rfl⟩
  | reqClean => trivial
  | filt _ _ _ ih => exact ih
  | zpass => exact ⟨⟨zeroMark, rfl⟩, ⟨zeroMark, rfl⟩, fun hz => absurd rfl hz⟩
  | zin => exact ⟨zeroMark, rfl⟩
  | @seed M n s must hs _ _ =>
    obtain ⟨t, ht⟩ := hsd M n s must hs
    exact ⟨⟨zeroMark, rfl⟩, ⟨t, by rw [limitFX_af, Exact.limitF_mark]; exact ht⟩,
      fun hz => absurd rfl hz⟩
  | @zret M n n' c g r e2 r' _ _ _ hr _ hr' _ _ =>
    obtain ⟨yr, hyr, hry, _⟩ := applySummaryX_base hr
    obtain ⟨tr, htr⟩ := conc_of_fact hry
      (applySummary_mark_conc (a := zeroAF) (t := zeroMark) rfl hyr)
    obtain ⟨yr', hyr', hry', _⟩ := applyEdgeX_base hr'
    obtain ⟨t3, ht3⟩ := conc_of_fact hry' (applyEdge_mark_conc htr hyr')
    exact ⟨⟨zeroMark, rfl⟩, ⟨t3, by rw [limitFX_af, Exact.limitF_mark]; exact ht3⟩,
      fun hz => absurd rfl hz⟩

#print axioms DBX_conc

end Inv

/-! ## 4. Exactness of the backward edges with a non-zero premise (the main theorem) -/

/-- A summary application reads only a premise on the base of the caller's added fact. -/
theorem applySummaryX_base_eq {a g r : XFact} {j : PFact} {jex : Excl}
    (h : r ∈ (applySummaryX a j jex g).facts) : a.af.fact.base = j.base := by
  obtain ⟨x, hx, _⟩ := List.mem_map.mp h
  obtain ⟨y, hy, _⟩ := applyEdgeX_base hx
  exact Statics.applyEdge_base_eq hy

/-- Under `NoZeroIn`, a summary or a record applied at a call (rules `ret`, `retRec`) has a premise
    off the zero base: a zero-premise backward summary never applies to a non-zero-based added fact
    (`BExact.no_zero_summary` with the annotated operations). -/
theorem no_zero_summaryX {Pb : Program} (hnz : NoZeroIn Pb) {M : MethodId} {n n' : Node} {c : Call}
    {e1 : MicroEdge} {f a g r : XFact} {j : PFact} {jex : Excl}
    (hE : (M, n, Instr.call c, n') ∈ Pb.edges) (he1 : e1 ∈ c.toCallee)
    (ha : a ∈ (bindX f e1).facts) (hr : r ∈ (applySummaryX a j jex g).facts) :
    j.base ≠ zeroBase := by
  intro hj
  have h1 := applySummaryX_base_eq hr
  obtain ⟨y, hy, hay, _⟩ := applyEdgeX_base ha
  have h2 : y.fact.base = e1.2.base := Statics.applyEdge_base hy
  exact hnz _ _ _ _ hE e1 he1 (by rw [← h2, ← hay, h1, hj])

#print axioms no_zero_summaryX

/-- The motive: `EdgeOKX` on the edges with a non-zero premise. -/
def EdgeOKNZX (Pb : Program) (ok : Loc → Prop) : XObj → Prop
  | .edge M i mi iex n f => i ≠ zeroFact → EdgeOKX Pb ok (.edge M i mi iex n f)
  | _ => True

/-- The persisted backward records are exact (`RecsExactX`) on the premises OFF the zero base: a
    record with a zero-based premise never applies under `NoZeroIn` (so it may be a zero-premise
    exit edge of an earlier backward run). -/
def RecsExactXNZ (Pb : Program) (ok : Loc → Prop)
    (recs : MethodId → PFact × Bool × Excl × XFact → Prop) : Prop :=
  ∀ m j mj jex g, recs m (j, mj, jex, g) → j.base ≠ zeroBase →
    EdgeOKX Pb ok (.edge m j mj jex (Pb.exit m) g)

/-- `RecsConcX` off the zero base: a normal must record has a concrete conclusion mark. -/
def RecsConcXNZ (recs : MethodId → PFact × Bool × Excl × XFact → Prop) : Prop :=
  ∀ m j jex g, recs m (j, true, jex, g) → j.base ≠ zeroBase → g.af.demand = false →
    ∃ t, g.af.fact.mark = .conc t

/-- `RecsWFX` off the zero base: a record conclusion is in normal form. -/
def RecsWFXNZ (recs : MethodId → PFact × Bool × Excl × XFact → Prop) : Prop :=
  ∀ m j mj jex g, recs m (j, mj, jex, g) → j.base ≠ zeroBase → WFX g

theorem recsExactXNZ_of {Pb : Program} {ok : Loc → Prop}
    {recs : MethodId → PFact × Bool × Excl × XFact → Prop} (h : RecsExactX Pb ok recs) :
    RecsExactXNZ Pb ok recs := fun m j mj jex g hr _ => h m j mj jex g hr

theorem recsConcXNZ_of {recs : MethodId → PFact × Bool × Excl × XFact → Prop}
    (h : RecsConcX recs) : RecsConcXNZ recs := fun m j jex g hr _ hg => h m j jex g hr hg

theorem recsWFXNZ_of {recs : MethodId → PFact × Bool × Excl × XFact → Prop}
    (h : RecsWFX recs) : RecsWFXNZ recs := fun m j mj jex g hr _ => h m j mj jex g hr

section Main
variable {Pb : Program} {bmay : BMay} {counted : Acc → Bool} {L : Nat}
  {demand : MethodId → DemandEdge → Prop}
  {emit : PFact → PFact → Excl → Option (PFact × Excl)}
  {sat : PFact → Excl → PFact → Excl → Bool}
  {restrict : PFact → Excl → XFact → DemandEdge → Option XFact}
  {recs : MethodId → PFact × Bool × Excl × XFact → Prop}
  {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId}
  {seeds : List (MethodId × Node × PFact × Bool)}

/-- 3. THE MAIN THEOREM: every object of `DBX` satisfies the motive "an edge whose premise is not
    the zero fact satisfies `EdgeOKX Pb ok`": a normal edge of a non-must premise is PAIR-EXACT on
    the admitted locations, a normal edge of a must-premise END-EXACT, on the reversed program `Pb`.
    The proof mirrors `AnyTaintExExact.DRX_edgeOK` case by case; the statement step goes through
    `transferXB_normal` (a normal result of the backward transfer is a result of `transferX`); the
    zero rules give zero-premise edges (vacuous); `ret`/`retRec` read a callee premise off the zero
    base (`no_zero_summaryX`), so the zero-premise edges never enter a non-zero premise.
    Hypotheses: those of `DRX_edgeOK` (`MarkWF`, `FiltOK`, `BackOK` of `Pb`, `SatInsideX sat`,
    `RestrictOKX restrict`, `EmitCopiesMarkX emit`, the records exact, concrete and in normal form,
    here only OFF THE ZERO BASE), `NoZeroIn Pb`, and concrete seeds (`SeedsConcB`). No hypothesis on
    `bmay`, the demand, the sinks, the roots or the must flags of the seeds. -/
theorem DBX_edgeOK_nz {ok : Loc → Prop} (hmw : Exact.MarkWF Pb) (hfo : Exact.FiltOK Pb ok)
    (hbo : Exact.BackOK Pb ok) (hin : SatInsideX sat) (hsub : RestrictOKX restrict)
    (hem : EmitCopiesMarkX emit) (hsd : SeedsConcB seeds) (hnz : NoZeroIn Pb)
    (hrecs : RecsExactXNZ Pb ok recs) (hrc : RecsConcXNZ recs) (hrw : RecsWFXNZ recs) {o : XObj}
    (h : DBX Pb bmay counted L demand emit sat restrict recs sinks roots seeds o) :
    EdgeOKNZX Pb ok o := by
  induction h with
  | root => trivial
  | @start M j mj jex hJ _ =>
    intro _
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
      refine ⟨fun hi => ?_, (startX_must_end (DBX_mustAny hJ)).2⟩
      show Exact.absB (startX j true jex).af.fact.mark = true
      rw [startX_af, startT_mark]
      exact hi
  | @step M i mi iex n f n' s f' hF hE hf ih =>
    intro hz
    have hfw := DBX_wf_edge hF
    have hcx := DBX_conc hem hsd hF
    cases mi with
    | false =>
      intro ha
      have hf' := transferXB_normal hf ha
      have hfa := transferX_demand hf' ha
      obtain ⟨_, ih2⟩ := ih hz hfa
      refine ⟨absX_vac hcx.1, fun l0 l hd hok => ?_⟩
      obtain ⟨l1, hd1, hs⟩ := transferX_exact (hmw.stmt _ _ _ _ hE) hfa hfw hf' ha hd
      have hok1 : ok l1 := by
        rcases hs with ⟨-, rfl⟩ | ⟨e, he, hde⟩
        · exact hok
        · exact hbo.stmt _ _ _ _ hE e he _ _ hde hok
      obtain ⟨hfl, hok0⟩ := ih2 l0 l1 hd1 hok1
      exact ⟨Flow.step hfl hE hs, hok0⟩
    | true =>
      intro ha
      have hf' := transferXB_normal hf ha
      have hfa := transferX_demand hf' ha
      obtain ⟨_, ih2⟩ := ih hz hfa
      refine ⟨absX_vac hcx.1, fun l hl hok => ?_⟩
      obtain ⟨l1, hl1, hs⟩ := transferX_cov (hmw.stmt _ _ _ _ hE) hfa hfw hf' ha hcx.2.1 hl
      have hok1 : ok l1 := by
        rcases hs with ⟨-, rfl⟩ | ⟨e, he, hde⟩
        · exact hok
        · exact hbo.stmt _ _ _ _ hE e he _ _ hde hok
      obtain ⟨l0, hi0, hfl, hok0⟩ := ih2 l1 hl1 hok1
      exact ⟨l0, hi0, Flow.step hfl hE hs, hok0⟩
  | reqStmt => trivial
  | @pass M i mi iex n f n' c _ hE hm ih =>
    intro hz
    cases mi with
    | false =>
      intro ha
      obtain ⟨ih1, ih2⟩ := ih hz ha
      refine ⟨ih1, fun l0 l hd hok => ?_⟩
      obtain ⟨hfl, hok0⟩ := ih2 l0 l hd hok
      refine ⟨Flow.pass hfl hE ?_, hok0⟩
      rw [hd.2.1]
      exact hm
    | true =>
      intro ha
      obtain ⟨ih1, ih2⟩ := ih hz ha
      refine ⟨ih1, fun l hl hok => ?_⟩
      obtain ⟨l0, hi0, hfl, hok0⟩ := ih2 l hl hok
      refine ⟨l0, hi0, Flow.pass hfl hE ?_, hok0⟩
      rw [hl.1]
      exact hm
  | added => trivial
  | initR => trivial
  | @ret M i mi iex n f n' c e1 a j mj jex g d g' r e2 r' hF hE he1 ha hJ hG _ hres hs hr he2 hr'
      ihF _ ihG =>
    intro hz
    -- the callee premise is off the zero base: its edges have a non-zero premise
    have hjb : j.base ≠ zeroBase := no_zero_summaryX hnz hE he1 ha hr
    have hjz : j ≠ zeroFact := ne_zero_of_base hjb
    have hgw := DBX_wf_edge hG
    obtain ⟨hgw', hgd, hgsub⟩ := hsub j jex g d g' hgw hres
    obtain ⟨hcov, hsm⟩ := hin j jex a.af.fact a.ex hs
    have hcx := DBX_conc hem hsd hF
    cases mj with
    | false =>
      -- a non-must callee premise: the callee summary is pair-exact
      have ihG' : g'.af.demand = false → ∀ l1 l2, denX j jex g'.af.fact g'.ex l1 l2 → ok l2 →
          Flow Pb c.callee l1 (Pb.exit c.callee) l2 ∧ ok l1 := by
        intro hg' l1 l2 hd' hok
        exact (ihG hjz (hgd.symm.trans hg')).2 l1 l2 (hgsub l1 l2 hd') hok
      exact summaryX_pair hmw hbo hE he1 ha hsm hr he2 hr' hcx.1 hcx.2.1 (hcx.2.2 hz)
        (DBX_wf_edge hF) hgw' (ihF hz) ihG'
    | true =>
      -- a must callee premise inside the added fact: END-EXACT of the callee summary
      have hjc : ∃ t, j.mark = .conc t := DBX_conc hem hsd hJ
      have hgc := (DBX_conc hem hsd hG).2.1
      have hG' : g'.af.demand = false → ∀ l1 l2, denX j jex g'.af.fact g'.ex l1 l2 → ok l2 →
          ∃ l0, coversX j jex l0 ∧ Flow Pb c.callee l0 (Pb.exit c.callee) l2 ∧ ok l0 := by
        intro hg' l1 l2 hd' hok
        exact (ihG hjz (hgd.symm.trans hg')).2 l2 (denX_coversFX (hgsub l1 l2 hd') hgc) hok
      exact summaryX_end hmw hbo hE he1 ha hcov hsm (fun _ => hjc) hr he2 hr' hcx.1 hcx.2.1
        (hcx.2.2 hz) (DBX_wf_edge hF) hgw' (ihF hz) hG'
  | @retRec M i mi iex n f n' c e1 a j mj jex g r e2 r' hF hE he1 ha hrec hs hr he2 hr' ihF =>
    intro hz
    have hjb : j.base ≠ zeroBase := no_zero_summaryX hnz hE he1 ha hr
    have hG := hrecs c.callee j mj jex g hrec hjb
    have hgw := hrw c.callee j mj jex g hrec hjb
    have hcx := DBX_conc hem hsd hF
    cases mj with
    | false =>
      -- a non-must record, by `sat` or by `applicable`: pair-exact
      have hsm : markSubB j.mark a.af.fact.mark = true := by
        rcases hs with hs | hs
        · exact (hin j jex a.af.fact a.ex hs).2
        · exact Exact.applicable_markSub hs
      have e : recLayerX false (sat j jex a.af.fact a.ex) r' = r' := rfl
      rw [e]
      exact summaryX_pair hmw hbo hE he1 ha hsm hr he2 hr' hcx.1 hcx.2.1 (hcx.2.2 hz)
        (DBX_wf_edge hF) hgw (ihF hz) (fun hg => (hG hg).2)
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
          AnyTaintExact.conc_of_absImp (hG hg).1 (hrc c.callee j jex g hrec hjb hg)
        have e : recLayerX true true r' = r' := rfl
        rw [e]
        exact summaryX_end hmw hbo hE he1 ha hcov hsm hjc hr he2 hr' hcx.1 hcx.2.1 (hcx.2.2 hz)
          (DBX_wf_edge hF) hgw (ihF hz)
          (fun hg l1 l2 hd' hok =>
            (hG hg).2 l2 (denX_coversFX hd' (hrc c.callee j jex g hrec hjb hg)) hok)
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial
  | @clean M i mi iex n f n' cl f' hF hE hf ih =>
    intro hz
    have hfw := DBX_wf_edge hF
    have hcx := DBX_conc hem hsd hF
    cases mi with
    | false =>
      intro ha
      have hfa := cleanResX_demand hf ha
      obtain ⟨_, ih2⟩ := ih hz hfa
      refine ⟨absX_vac hcx.1, fun l0 l hd hok => ?_⟩
      obtain ⟨hd1, hcl⟩ := cleanResX_exact hfw hf ha hd
      obtain ⟨hfl, hok0⟩ := ih2 l0 l hd1 hok
      exact ⟨Flow.clean hfl hE hcl, hok0⟩
    | true =>
      intro ha
      have hfa := cleanResX_demand hf ha
      obtain ⟨_, ih2⟩ := ih hz hfa
      refine ⟨absX_vac hcx.1, fun l hl hok => ?_⟩
      obtain ⟨hl1, hcl⟩ := cleanResX_cov hfw hf ha hcx.2.1 hl
      obtain ⟨l0, hi0, hfl, hok0⟩ := ih2 l hl1 hok
      exact ⟨l0, hi0, Flow.clean hfl hE hcl, hok0⟩
  | reqClean => trivial
  | @filt M i mi iex n f n' b may _ hE hp ih =>
    intro hz
    cases mi with
    | false =>
      intro ha
      obtain ⟨ih1, ih2⟩ := ih hz ha
      refine ⟨ih1, fun l0 l hd hok => ?_⟩
      obtain ⟨hfl, hok0⟩ := ih2 l0 l hd hok
      refine ⟨Flow.filt hfl hE ?_, hok0⟩
      intro hb
      obtain ⟨-, hlb, -, -, -, σ, τ, -, hlp, -, -, -, -⟩ := hd
      exact hfo _ _ _ _ _ hE f.af.fact.path τ l (hp (hlb.symm.trans hb)) hlp hok hb
    | true =>
      intro ha
      obtain ⟨ih1, ih2⟩ := ih hz ha
      refine ⟨ih1, fun l hl hok => ?_⟩
      obtain ⟨l0, hi0, hfl, hok0⟩ := ih2 l hl hok
      refine ⟨l0, hi0, Flow.filt hfl hE ?_, hok0⟩
      intro hb
      obtain ⟨hlb, ⟨τ, hlp, _⟩, _⟩ := hl
      exact hfo _ _ _ _ _ hE f.af.fact.path τ l (hp (hlb.symm.trans hb)) hlp hok hb
  -- the zero rules make edges of the zero premise only
  | zpass => exact fun hz => absurd rfl hz
  | zin => trivial
  | seed => exact fun hz => absurd rfl hz
  | zret => exact fun hz => absurd rfl hz

#print axioms DBX_edgeOK_nz

/-- 3'. The two exactness forms of a normal backward edge with a non-zero premise. -/
theorem edge_exactBX_gen {ok : Loc → Prop} (hmw : Exact.MarkWF Pb) (hfo : Exact.FiltOK Pb ok)
    (hbo : Exact.BackOK Pb ok) (hin : SatInsideX sat) (hsub : RestrictOKX restrict)
    (hem : EmitCopiesMarkX emit) (hsd : SeedsConcB seeds) (hnz : NoZeroIn Pb)
    (hrecs : RecsExactXNZ Pb ok recs) (hrc : RecsConcXNZ recs) (hrw : RecsWFXNZ recs)
    {M : MethodId} {i : PFact} {mi : Bool} {iex : Excl} {n : Node} {f : XFact}
    (h : DBX Pb bmay counted L demand emit sat restrict recs sinks roots seeds
      (.edge M i mi iex n f))
    (hi : i ≠ zeroFact) (ha : f.af.demand = false) :
    (mi = false → ∀ l0 l, denX i iex f.af.fact f.ex l0 l → ok l → Flow Pb M l0 n l ∧ ok l0) ∧
    (mi = true → EndExactX Pb ok M i iex n f.af.fact f.ex) := by
  have hm := DBX_edgeOK_nz hmw hfo hbo hin hsub hem hsd hnz hrecs hrc hrw h hi
  cases mi with
  | false => exact ⟨fun _ => (hm ha).2, fun h' => (by cases h')⟩
  | true => exact ⟨fun h' => (by cases h'), fun _ => (hm ha).2⟩

#print axioms edge_exactBX_gen

/-! ## 5. The backward records (item 4) -/

/-- The exit edges of a backward run with a NON-ZERO premise, as annotated records (with their
    must flags and premise exclusions): the persisted backward records (B2). -/
def exitRecsNZ (Pb : Program) (R : XObj → Prop) (m : MethodId)
    (x : PFact × Bool × Excl × XFact) : Prop :=
  x.1 ≠ zeroFact ∧ R (.edge m x.1 x.2.1 x.2.2.1 (Pb.exit m) x.2.2.2)

/-- 4. THE BACKWARD RECORDS ARE EXACT (`RecsExactX Pb ok`): a backward MUST record is END-EXACT on
    the admitted locations, every other backward record PAIR-EXACT, on `Pb`. -/
theorem recsB_exact {ok : Loc → Prop} (hmw : Exact.MarkWF Pb) (hfo : Exact.FiltOK Pb ok)
    (hbo : Exact.BackOK Pb ok) (hin : SatInsideX sat) (hsub : RestrictOKX restrict)
    (hem : EmitCopiesMarkX emit) (hsd : SeedsConcB seeds) (hnz : NoZeroIn Pb)
    (hrecs : RecsExactXNZ Pb ok recs) (hrc : RecsConcXNZ recs) (hrw : RecsWFXNZ recs) :
    RecsExactX Pb ok
      (exitRecsNZ Pb (DBX Pb bmay counted L demand emit sat restrict recs sinks roots seeds)) :=
  fun _ _ _ _ _ hr => DBX_edgeOK_nz hmw hfo hbo hin hsub hem hsd hnz hrecs hrc hrw hr.2 hr.1

#print axioms recsB_exact

/-- 4m. A normal backward MUST record is END-EXACT on `Pb`. -/
theorem recsB_must_end {ok : Loc → Prop} (hmw : Exact.MarkWF Pb) (hfo : Exact.FiltOK Pb ok)
    (hbo : Exact.BackOK Pb ok) (hin : SatInsideX sat) (hsub : RestrictOKX restrict)
    (hem : EmitCopiesMarkX emit) (hsd : SeedsConcB seeds) (hnz : NoZeroIn Pb)
    (hrecs : RecsExactXNZ Pb ok recs) (hrc : RecsConcXNZ recs) (hrw : RecsWFXNZ recs)
    {m : MethodId} {j : PFact} {jex : Excl} {g : XFact}
    (hr : exitRecsNZ Pb (DBX Pb bmay counted L demand emit sat restrict recs sinks roots seeds) m
      (j, true, jex, g)) (hg : g.af.demand = false) :
    EndExactX Pb ok m j jex (Pb.exit m) g.af.fact g.ex :=
  (recsB_exact hmw hfo hbo hin hsub hem hsd hnz hrecs hrc hrw m j true jex g hr hg).2

#print axioms recsB_must_end

/-- 4p. A normal backward non-must record is PAIR-EXACT on `Pb`. -/
theorem recsB_pair {ok : Loc → Prop} (hmw : Exact.MarkWF Pb) (hfo : Exact.FiltOK Pb ok)
    (hbo : Exact.BackOK Pb ok) (hin : SatInsideX sat) (hsub : RestrictOKX restrict)
    (hem : EmitCopiesMarkX emit) (hsd : SeedsConcB seeds) (hnz : NoZeroIn Pb)
    (hrecs : RecsExactXNZ Pb ok recs) (hrc : RecsConcXNZ recs) (hrw : RecsWFXNZ recs)
    {m : MethodId} {j : PFact} {jex : Excl} {g : XFact}
    (hr : exitRecsNZ Pb (DBX Pb bmay counted L demand emit sat restrict recs sinks roots seeds) m
      (j, false, jex, g)) (hg : g.af.demand = false) :
    ∀ l0 l, denX j jex g.af.fact g.ex l0 l → ok l → Flow Pb m l0 (Pb.exit m) l ∧ ok l0 :=
  (recsB_exact hmw hfo hbo hin hsub hem hsd hnz hrecs hrc hrw m j false jex g hr hg).2

#print axioms recsB_pair

/-- 4'. THE NEXT BACKWARD RUN: the records of a backward run together with its exit edges of a
    non-zero premise satisfy the three record hypotheses of the main theorem again. -/
theorem recsB_next {ok : Loc → Prop} (hmw : Exact.MarkWF Pb) (hfo : Exact.FiltOK Pb ok)
    (hbo : Exact.BackOK Pb ok) (hin : SatInsideX sat) (hsub : RestrictOKX restrict)
    (hem : EmitCopiesMarkX emit) (hsd : SeedsConcB seeds) (hnz : NoZeroIn Pb)
    (hrecs : RecsExactXNZ Pb ok recs) (hrc : RecsConcXNZ recs) (hrw : RecsWFXNZ recs) :
    let recs' := fun m x => recs m x ∨
      exitRecsNZ Pb (DBX Pb bmay counted L demand emit sat restrict recs sinks roots seeds) m x
    RecsExactXNZ Pb ok recs' ∧ RecsConcXNZ recs' ∧ RecsWFXNZ recs' := by
  refine ⟨fun m j mj jex g hr hjb => ?_, fun m j jex g hr hjb hg => ?_,
    fun m j mj jex g hr hjb => ?_⟩
  · rcases hr with hr | hr
    · exact hrecs m j mj jex g hr hjb
    · exact recsB_exact hmw hfo hbo hin hsub hem hsd hnz hrecs hrc hrw m j mj jex g hr
  · rcases hr with hr | hr
    · exact hrc m j jex g hr hjb hg
    · exact (DBX_conc hem hsd hr.2).2.1
  · rcases hr with hr | hr
    · exact hrw m j mj jex g hr hjb
    · exact DBX_wf_edge hr.2

#print axioms recsB_next

end Main

/-! ## 6. Must seeds and must-premises (item 5) -/

section MustSeed
variable {Pb : Program} {bmay : BMay} {counted : Acc → Bool} {L : Nat}
  {demand : MethodId → DemandEdge → Prop}
  {emit : PFact → PFact → Excl → Option (PFact × Excl)}
  {sat : PFact → Excl → PFact → Excl → Bool}
  {restrict : PFact → Excl → XFact → DemandEdge → Option XFact}
  {recs : MethodId → PFact × Bool × Excl × XFact → Prop}
  {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId}
  {seeds : List (MethodId × Node × PFact × Bool)}

theorem limitFX_of_none {x : XFact} (h : cutPath counted L x.af.fact.path = none) :
    limitFX counted L x = x := by
  unfold limitFX; rw [h]

/-- 5a. A MUST seed with an `.any` concrete pattern (within the backward field limit) gives a NORMAL
    `.any` edge with an empty exclusion: the backward `[any-taint]` (`carriesB`). -/
theorem must_seed_normal {M : MethodId} {n : Node} {s : PFact} {t : Mark}
    (hs : (M, n, s, true) ∈ seeds) (hk : s.kind = .any) (hm : s.mark = .conc t)
    (hL : cutPath counted L s.path = none)
    (hZ : DBX Pb bmay counted L demand emit sat restrict recs sinks roots seeds
      (.edge M zeroFact false Excl.empty n zeroX)) :
    DBX Pb bmay counted L demand emit sat restrict recs sinks roots seeds
      (.edge M zeroFact false Excl.empty n ⟨⟨s, false⟩, Excl.empty⟩) ∧
    carriesB ⟨s, false⟩ = true := by
  refine ⟨?_, ?_⟩
  · have h := DBX.seed hs hZ
    rw [limitFX_of_none hL] at h
    exact h
  · unfold carriesB
    show (s.kind.isAny && !false && concB s.mark) = true
    rw [hk, hm]
    rfl

#print axioms must_seed_normal

/-- 5b. Binding a NORMAL `.any` fact into a callee gives a MUST added fact (`am = true`, B2). -/
theorem must_added {M : MethodId} {i : PFact} {mi : Bool} {iex : Excl} {n n' : Node} {c : Call}
    {f a : XFact} {e : MicroEdge}
    (hF : DBX Pb bmay counted L demand emit sat restrict recs sinks roots seeds
      (.edge M i mi iex n f))
    (hE : (M, n, Instr.call c, n') ∈ Pb.edges) (he : e ∈ c.toCallee) (ha : a ∈ (bindX f e).facts)
    (hd : a.af.demand = false) (hk : a.af.fact.kind = .any) :
    DBX Pb bmay counted L demand emit sat restrict recs sinks roots seeds
      (.added c.callee a.af.fact true a.ex) := by
  have h := DBX.added hF hE he ha
  rw [hk, hd] at h
  exact h

#print axioms must_added

/-- The standard binding `b.* → b'.*` moves a normal `.any` concrete fact to the callee base, normal,
    with no exclusion. -/
theorem bindX_star_any (b b' : Base) (p : List Acc) (t : Mark) :
    bindX ⟨⟨⟨b, p, .any, .conc t⟩, false⟩, Excl.empty⟩
      (⟨b, [], .star Excl.empty, .star⟩, ⟨b', [], .star Excl.empty, .star⟩) =
    ⟨[⟨⟨⟨b', p, .any, .conc t⟩, false⟩, Excl.empty⟩], []⟩ := by
  cases p with
  | nil =>
    simp [bindX, applyEdgeX, annX, applyEdge, relate, dropPrefix, belowCase, markGate, markComp,
      normX, layerX, carriesB, keepB, concB, tailExcl, Excl.union, Excl.empty, admitsTailB,
      Excl.admits, Excl.isEmptyB, AFact.norm, Kind.isAny]
  | cons x r =>
    simp [bindX, applyEdgeX, annX, applyEdge, relate, dropPrefix, belowCase, markGate, markComp,
      normX, layerX, carriesB, concB, Excl.empty, admitsTailB, Excl.admits, AFact.norm,
      Kind.isAny, memB]

#print axioms bindX_star_any

/-- 5c. A must seed `(b, p, [any], T)` bound into a callee by the standard binding `b.* → b'.*`
    gives the MUST added fact `(b', p, [any], T)` with no exclusion. -/
theorem must_seed_bound {M : MethodId} {n n' : Node} {c : Call} {b b' : Base} {p : List Acc}
    {t : Mark} (hs : (M, n, (⟨b, p, .any, .conc t⟩ : PFact), true) ∈ seeds)
    (hL : cutPath counted L p = none)
    (hZ : DBX Pb bmay counted L demand emit sat restrict recs sinks roots seeds
      (.edge M zeroFact false Excl.empty n zeroX))
    (hE : (M, n, Instr.call c, n') ∈ Pb.edges)
    (he : ((⟨b, [], .star Excl.empty, .star⟩ : PFact), (⟨b', [], .star Excl.empty, .star⟩ : PFact))
      ∈ c.toCallee) :
    DBX Pb bmay counted L demand emit sat restrict recs sinks roots seeds
      (.added c.callee ⟨b', p, .any, .conc t⟩ true Excl.empty) := by
  have hS := (must_seed_normal hs rfl rfl hL hZ).1
  have ha : (⟨⟨⟨b', p, .any, .conc t⟩, false⟩, Excl.empty⟩ : XFact) ∈
      (bindX ⟨⟨⟨b, p, .any, .conc t⟩, false⟩, Excl.empty⟩
        (⟨b, [], .star Excl.empty, .star⟩, ⟨b', [], .star Excl.empty, .star⟩)).facts := by
    rw [bindX_star_any]
    exact List.mem_singleton.mpr rfl
  exact must_added hS hE he ha rfl rfl

#print axioms must_seed_bound

/-- 5d. THE MUST-PREMISE (B2): the emission from a must added fact of an `.any` premise gives a
    MUST premise; its start fact is NORMAL (and END-EXACT at the entry, `startX_must_end`). -/
theorem must_premise_normal {m : MethodId} {a : PFact} {aex : Excl} {d : DemandEdge} {j : PFact}
    {jex : Excl}
    (hA : DBX Pb bmay counted L demand emit sat restrict recs sinks roots seeds
      (.added m a true aex))
    (hd : demand m d) (hem : emit d.din a aex = some (j, jex)) (hj : j.kind = .any) :
    DBX Pb bmay counted L demand emit sat restrict recs sinks roots seeds (.init m j true jex) ∧
    DBX Pb bmay counted L demand emit sat restrict recs sinks roots seeds
      (.edge m j true jex (Pb.entry m) (startX j true jex)) ∧
    (startX j true jex).af.demand = false ∧ j ≠ zeroFact := by
  have he : emitTX emit d.din a true aex = some (j, true, jex) := by
    show (emit d.din a aex).map (fun p => (p.1, true && p.1.kind.isAny, p.2)) = some (j, true, jex)
    rw [hem]
    show some (j, true && j.kind.isAny, jex) = some (j, true, jex)
    rw [hj]
    rfl
  have hI := DBX.initR hA hd he
  refine ⟨hI, DBX.start hI, (startX_must_end (P := Pb) (ok := fun _ => True) (M := m) hj).1, ?_⟩
  intro hz
  rw [hz] at hj
  cases hj

#print axioms must_premise_normal

/-- 5e. The edges of such a must-premise are END-EXACT on `Pb` (the main theorem applies: the premise
    is not the zero fact). -/
theorem must_premise_endExact {ok : Loc → Prop} (hmw : Exact.MarkWF Pb) (hfo : Exact.FiltOK Pb ok)
    (hbo : Exact.BackOK Pb ok) (hin : SatInsideX sat) (hsub : RestrictOKX restrict)
    (hemc : EmitCopiesMarkX emit) (hsd : SeedsConcB seeds) (hnz : NoZeroIn Pb)
    (hrecs : RecsExactXNZ Pb ok recs) (hrc : RecsConcXNZ recs) (hrw : RecsWFXNZ recs)
    {m : MethodId} {a : PFact} {aex : Excl} {d : DemandEdge} {j : PFact} {jex : Excl}
    {n : Node} {f : XFact}
    (hA : DBX Pb bmay counted L demand emit sat restrict recs sinks roots seeds
      (.added m a true aex))
    (hd : demand m d) (hem : emit d.din a aex = some (j, jex)) (hj : j.kind = .any)
    (hF : DBX Pb bmay counted L demand emit sat restrict recs sinks roots seeds
      (.edge m j true jex n f)) (hf : f.af.demand = false) :
    EndExactX Pb ok m j jex n f.af.fact f.ex :=
  ((edge_exactBX_gen hmw hfo hbo hin hsub hemc hsd hnz hrecs hrc hrw hF
    (must_premise_normal hA hd hem hj).2.2.2 hf).2 rfl)

#print axioms must_premise_endExact

/-- A binding of a DEMAND fact gives only demand results. -/
theorem bindX_demand {f x : XFact} {e : MicroEdge} (hf : f.af.demand = true)
    (hx : x ∈ (bindX f e).facts) : x.af.demand = true := by
  cases hxa : x.af.demand with
  | true => rfl
  | false =>
    have := applyEdgeX_demand hx hxa
    rw [hf] at this
    cases this

/-- 5f. CONTRAST (the status quo, an ND seed or a seed with `must = false`): the seed edge is DEMAND,
    every fact that it binds into a callee is a NON-must added fact (`am = false`), the emission
    gives a non-must premise, and the start of an `.any` premise is DEMAND. -/
theorem demand_seed_contrast {M : MethodId} {n n' : Node} {s : PFact} {c : Call} {e : MicroEdge}
    {a : XFact} (hs : (M, n, s, false) ∈ seeds)
    (hZ : DBX Pb bmay counted L demand emit sat restrict recs sinks roots seeds
      (.edge M zeroFact false Excl.empty n zeroX))
    (hE : (M, n, Instr.call c, n') ∈ Pb.edges) (he : e ∈ c.toCallee)
    (ha : a ∈ (bindX (limitFX counted L ⟨⟨s, true⟩, Excl.empty⟩) e).facts) :
    DBX Pb bmay counted L demand emit sat restrict recs sinks roots seeds
      (.edge M zeroFact false Excl.empty n (limitFX counted L ⟨⟨s, true⟩, Excl.empty⟩)) ∧
    (limitFX counted L ⟨⟨s, true⟩, Excl.empty⟩).af.demand = true ∧
    DBX Pb bmay counted L demand emit sat restrict recs sinks roots seeds
      (.added c.callee a.af.fact false a.ex) := by
  have hS := DBX.seed (Pb := Pb) (bmay := bmay) (demand := demand) (emit := emit) (sat := sat)
    (restrict := restrict) (recs := recs) (sinks := sinks) (roots := roots) hs hZ
  have hsd : (limitFX counted L ⟨⟨s, true⟩, Excl.empty⟩).af.demand = true :=
    limitFX_demand (x := ⟨⟨s, true⟩, Excl.empty⟩) rfl
  refine ⟨hS, hsd, ?_⟩
  have h := DBX.added hS hE he ha
  rw [bindX_demand hsd ha, Bool.not_true, Bool.and_false] at h
  exact h

#print axioms demand_seed_contrast

/-- 5g. CONTRAST (the emission): a non-must added fact gives a non-must premise, and the start of an
    `.any` premise is DEMAND (`startFact`). -/
theorem demand_premise_start {d a : PFact} {aex : Excl} {j : PFact} {mj : Bool} {jex : Excl}
    (hem : emitTX emit d a false aex = some (j, mj, jex)) (hj : j.kind = .any) :
    mj = false ∧ (startX j mj jex).af.demand = true := by
  have hmj : mj = false := by
    unfold emitTX at hem
    cases he : emit d a aex with
    | none => rw [he] at hem; cases hem
    | some pr =>
      rw [he] at hem
      have h2 : some (pr.1, false && pr.1.kind.isAny, pr.2) = some (j, mj, jex) := hem
      exact (congrArg (fun x => x.2.1) (Option.some.inj h2)).symm
  refine ⟨hmj, ?_⟩
  subst hmj
  obtain ⟨jb, jp, jk, jm⟩ := j
  have hk : jk = .any := hj
  subst hk
  rfl

#print axioms demand_premise_start

end MustSeed

/-! ## 7. The backward run sequence (no record hypothesis left) -/

/-- The record sets of a sequence of backward runs on `Pb`: run `k` is `run k recs`; run `0` has no
    record; the records of run `k + 1` are those of run `k` and the exit edges of run `k` with a
    non-zero premise (`exitRecsNZ`). -/
def recsBSeq (Pb : Program)
    (run : Nat → (MethodId → PFact × Bool × Excl × XFact → Prop) → XObj → Prop) :
    Nat → MethodId → PFact × Bool × Excl × XFact → Prop
  | 0     => fun _ _ => False
  | k + 1 => fun m x => recsBSeq Pb run k m x ∨ exitRecsNZ Pb (run k (recsBSeq Pb run k)) m x

/-- The `k`-th backward run of a sequence (its own `bmay`, field limit, demand and seeds). -/
abbrev runB (Pb : Program) (bmayB : Nat → BMay) (counted : Acc → Bool) (LB : Nat → Nat)
    (demB : Nat → MethodId → DemandEdge → Prop)
    (emit : PFact → PFact → Excl → Option (PFact × Excl))
    (sat : PFact → Excl → PFact → Excl → Bool)
    (restrict : PFact → Excl → XFact → DemandEdge → Option XFact)
    (sinks : List (MethodId × Node × PFact)) (roots : List MethodId)
    (seedsB : Nat → List (MethodId × Node × PFact × Bool)) (k : Nat)
    (recs : MethodId → PFact × Bool × Excl × XFact → Prop) : XObj → Prop :=
  DBX Pb (bmayB k) counted (LB k) (demB k) emit sat restrict recs sinks roots (seedsB k)

section Seq
variable {Pb : Program} {bmayB : Nat → BMay} {counted : Acc → Bool} {LB : Nat → Nat}
  {demB : Nat → MethodId → DemandEdge → Prop}
  {emit : PFact → PFact → Excl → Option (PFact × Excl)}
  {sat : PFact → Excl → PFact → Excl → Bool}
  {restrict : PFact → Excl → XFact → DemandEdge → Option XFact}
  {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
  {seedsB : Nat → List (MethodId × Node × PFact × Bool)}

/-- 4s. THE BACKWARD RECORDS OVER THE SEQUENCE: the records of every backward run of the sequence
    satisfy the three record hypotheses of the main theorem (by `recsB_next`). -/
theorem recsBSeq_ok {ok : Loc → Prop} (hmw : Exact.MarkWF Pb) (hfo : Exact.FiltOK Pb ok)
    (hbo : Exact.BackOK Pb ok) (hin : SatInsideX sat) (hsub : RestrictOKX restrict)
    (hem : EmitCopiesMarkX emit) (hsd : ∀ k, SeedsConcB (seedsB k)) (hnz : NoZeroIn Pb) :
    ∀ k, RecsExactXNZ Pb ok
        (recsBSeq Pb (runB Pb bmayB counted LB demB emit sat restrict sinks roots seedsB) k) ∧
      RecsConcXNZ
        (recsBSeq Pb (runB Pb bmayB counted LB demB emit sat restrict sinks roots seedsB) k) ∧
      RecsWFXNZ
        (recsBSeq Pb (runB Pb bmayB counted LB demB emit sat restrict sinks roots seedsB) k)
  | 0 => ⟨fun _ _ _ _ _ h => h.elim, fun _ _ _ _ h => h.elim, fun _ _ _ _ _ h => h.elim⟩
  | k + 1 => by
    obtain ⟨h1, h2, h3⟩ := recsBSeq_ok hmw hfo hbo hin hsub hem hsd hnz k
    exact recsB_next hmw hfo hbo hin hsub hem (hsd k) hnz h1 h2 h3

#print axioms recsBSeq_ok

end Seq

/-! ## 8. Back to the forward program (item 6) -/

section Forward
variable {P : Program} {bmay : BMay} {counted : Acc → Bool} {L : Nat}
  {demand : MethodId → DemandEdge → Prop}
  {emit : PFact → PFact → Excl → Option (PFact × Excl)}
  {sat : PFact → Excl → PFact → Excl → Bool}
  {restrict : PFact → Excl → XFact → DemandEdge → Option XFact}
  {recs : MethodId → PFact × Bool × Excl × XFact → Prop}
  {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId}
  {seeds : List (MethodId × Node × PFact × Bool)}

/-- The forward hypotheses transported to the reversed program, in the form of the main theorem. -/
theorem rev_hyps (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hNZB : NoZeroBack P) :
    Exact.MarkWF (Program.rev P) ∧ Exact.FiltOK (Program.rev P) (fun _ => True) ∧
      Exact.BackOK (Program.rev P) (fun _ => True) ∧ NoZeroIn (Program.rev P) :=
  ⟨markWF_rev hmw, Exact.filtUp_ok (filtUp_rev hup), Exact.backOK_true _, noZeroIn_rev hNZB⟩

/-- 6. A NORMAL BACKWARD MUST RECORD IS A FORWARD END-EXACT FACT: for `Pb = Program.rev P`, a normal
    backward MUST edge `(jb, must, jex) → gb` at the backward exit (the forward entry) with a
    non-zero premise means: every admitted location `l` of `gb` at the forward entry flows in `P` to
    SOME admitted location `l0` of `jb` at the forward exit. Hypotheses on the FORWARD program:
    `MarkWF P`, `FiltUp P`, `NoZeroBack P` (transported by `markWF_rev`, `filtUp_rev`,
    `noZeroIn_rev`), `RevStmts P`, `RevCalls P` (`Reverse.flow_rev_iff_calls`); the rule contracts
    and the backward records as in `DBX_edgeOK_nz`. -/
theorem backMust_forward (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hNZB : NoZeroBack P)
    (hR : RevStmts P) (hC : RevCalls P) (hin : SatInsideX sat) (hsub : RestrictOKX restrict)
    (hem : EmitCopiesMarkX emit) (hsd : SeedsConcB seeds)
    (hrecs : RecsExactXNZ (Program.rev P) (fun _ => True) recs) (hrc : RecsConcXNZ recs)
    (hrw : RecsWFXNZ recs)
    {M : MethodId} {jb : PFact} {jex : Excl} {gb : XFact}
    (h : DBX (Program.rev P) bmay counted L demand emit sat restrict recs sinks roots seeds
      (.edge M jb true jex ((Program.rev P).exit M) gb))
    (hjb : jb ≠ zeroFact) (hg : gb.af.demand = false) :
    ∀ l, coversFX gb.af.fact gb.ex l → ∃ l0, coversX jb jex l0 ∧ Flow P M l (P.exit M) l0 := by
  obtain ⟨h1, h2, h3, h4⟩ := rev_hyps hmw hup hNZB
  have hm := (edge_exactBX_gen h1 h2 h3 hin hsub hem hsd h4 hrecs hrc hrw h hjb hg).2 rfl
  intro l hl
  obtain ⟨l0, hl0, hfl, _⟩ := hm l hl trivial
  exact ⟨l0, hl0, (flow_rev_iff_calls hR hC).mpr hfl⟩

#print axioms backMust_forward

/-- 6p. The pair form for a NON-must premise: every admitted pair `(l0, l)` of a normal backward
    edge `(jb, jex) → gb` at the backward exit is a forward flow from `l` (forward entry) to `l0`
    (forward exit). -/
theorem backPair_forward (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hNZB : NoZeroBack P)
    (hR : RevStmts P) (hC : RevCalls P) (hin : SatInsideX sat) (hsub : RestrictOKX restrict)
    (hem : EmitCopiesMarkX emit) (hsd : SeedsConcB seeds)
    (hrecs : RecsExactXNZ (Program.rev P) (fun _ => True) recs) (hrc : RecsConcXNZ recs)
    (hrw : RecsWFXNZ recs)
    {M : MethodId} {jb : PFact} {jex : Excl} {gb : XFact}
    (h : DBX (Program.rev P) bmay counted L demand emit sat restrict recs sinks roots seeds
      (.edge M jb false jex ((Program.rev P).exit M) gb))
    (hjb : jb ≠ zeroFact) (hg : gb.af.demand = false) :
    ∀ l0 l, denX jb jex gb.af.fact gb.ex l0 l → Flow P M l (P.exit M) l0 := by
  obtain ⟨h1, h2, h3, h4⟩ := rev_hyps hmw hup hNZB
  have hm := (edge_exactBX_gen h1 h2 h3 hin hsub hem hsd h4 hrecs hrc hrw h hjb hg).1 rfl
  intro l0 l hd
  exact (flow_rev_iff_calls hR hC).mpr (hm l0 l hd trivial).1

#print axioms backPair_forward

/-- 6v. The valid-location form of `backMust_forward` (S13: `FiltValid P ok`, `BackOK` of the
    reversed program for `ok`; the records exact for `ok`). -/
theorem backMust_forward_valid {ok : Loc → Prop} (hmw : Exact.MarkWF P)
    (hv : Exact.FiltValid P ok) (hbo : Exact.BackOK (Program.rev P) ok) (hNZB : NoZeroBack P)
    (hR : RevStmts P) (hC : RevCalls P) (hin : SatInsideX sat) (hsub : RestrictOKX restrict)
    (hem : EmitCopiesMarkX emit) (hsd : SeedsConcB seeds)
    (hrecs : RecsExactXNZ (Program.rev P) ok recs) (hrc : RecsConcXNZ recs)
    (hrw : RecsWFXNZ recs)
    {M : MethodId} {jb : PFact} {jex : Excl} {gb : XFact}
    (h : DBX (Program.rev P) bmay counted L demand emit sat restrict recs sinks roots seeds
      (.edge M jb true jex ((Program.rev P).exit M) gb))
    (hjb : jb ≠ zeroFact) (hg : gb.af.demand = false) :
    ∀ l, coversFX gb.af.fact gb.ex l → ok l →
      ∃ l0, coversX jb jex l0 ∧ Flow P M l (P.exit M) l0 ∧ ok l0 := by
  have hm := (edge_exactBX_gen (markWF_rev hmw) (Exact.filtValid_ok (filtValid_rev hv)) hbo hin
    hsub hem hsd (noZeroIn_rev hNZB) hrecs hrc hrw h hjb hg).2 rfl
  intro l hl hok
  obtain ⟨l0, hl0, hfl, hok0⟩ := hm l hl hok
  exact ⟨l0, hl0, (flow_rev_iff_calls hR hC).mpr hfl, hok0⟩

#print axioms backMust_forward_valid

end Forward

/-- 6s. THE SPEC INSTANCE OVER THE BACKWARD SEQUENCE (no record hypothesis): with the spec rules
    `emitX`, `satX`, `restrictX` and the records of the sequence (`recsBSeq`), a normal backward MUST
    record of run `k` with a non-zero premise is a forward END-EXACT fact of `P`. Hypotheses:
    `MarkWF P`, `FiltUp P`, `NoZeroBack P`, `RevStmts P`, `RevCalls P`, concrete seeds. -/
theorem backMust_forward_seq {P : Program} {bmayB : Nat → BMay} {counted : Acc → Bool}
    {LB : Nat → Nat} {demB : Nat → MethodId → DemandEdge → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    {seedsB : Nat → List (MethodId × Node × PFact × Bool)}
    (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hNZB : NoZeroBack P)
    (hR : RevStmts P) (hC : RevCalls P) (hsd : ∀ k, SeedsConcB (seedsB k)) (k : Nat)
    {M : MethodId} {jb : PFact} {jex : Excl} {gb : XFact}
    (h : runB (Program.rev P) bmayB counted LB demB emitX satX restrictX sinks roots seedsB k
      (recsBSeq (Program.rev P)
        (runB (Program.rev P) bmayB counted LB demB emitX satX restrictX sinks roots seedsB) k)
      (.edge M jb true jex ((Program.rev P).exit M) gb))
    (hjb : jb ≠ zeroFact) (hg : gb.af.demand = false) :
    ∀ l, coversFX gb.af.fact gb.ex l → ∃ l0, coversX jb jex l0 ∧ Flow P M l (P.exit M) l0 := by
  obtain ⟨h1, h2, h3, h4⟩ := rev_hyps hmw hup hNZB
  obtain ⟨hr1, hr2, hr3⟩ := recsBSeq_ok h1 h2 h3 satX_inside restrictX_ok emitX_copies hsd h4 k
  exact backMust_forward hmw hup hNZB hR hC satX_inside restrictX_ok emitX_copies (hsd k) hr1 hr2
    hr3 h hjb hg

#print axioms backMust_forward_seq

/-! ## 9. Counterexample: the two restrictions of the record theorem are necessary

`CexMustPair`: one backward program `Pb` (method `0`: the call node `0`, the exit `1`; the callee `1`:
one node, its entry is its exit) with the standard binding `1.* → 2.*`, the must seed
`(1, [], [any], 5)` at node `0`, the demand `(2, [], [any], 5)` of the callee, the spec rules and no
record. The hypotheses of `recsB_exact` hold. The run derives:
  * a MUST record `(2,[],[any],5) (must, {}) → (2,[],[any],5)` of the callee (the chain of B1/B2:
    the must seed, the must added fact, the must-premise, its normal start); it is END-EXACT
    (`recsB_exact`) but NOT PAIR-EXACT: the pair `(2.[3], 2.[4])` of its `denX` is no flow. So a
    backward MUST record must be read END-EXACT (`backMust_forward`), never as pairs;
  * a NORMAL zero-premise exit edge `zero → (1,[],[any-taint],5)` of method `0` (the must seed passed
    over the call). It is not exact (no flow from the zero location reaches `1.[]` with the mark `5`):
    the restriction to non-zero premises in the motive and in `exitRecsNZ` is necessary. -/
namespace CexMustPair

def bind : MicroEdge := (⟨1, [], .star Excl.empty, .star⟩, ⟨2, [], .star Excl.empty, .star⟩)
def c : Call := ⟨1, [], [bind], []⟩
def Pb : Program := ⟨fun _ => 0, fun m => if m = 0 then 1 else 0, [(0, 0, .call c, 1)]⟩
def s : PFact := ⟨1, [], .any, .conc 5⟩
def seeds : List (MethodId × Node × PFact × Bool) := [(0, 0, s, true)]
def a : PFact := ⟨2, [], .any, .conc 5⟩
def dd : DemandEdge := ⟨a, none⟩
def dem : MethodId → DemandEdge → Prop := fun m d => m = 1 ∧ d = dd
def noRecs : MethodId → PFact × Bool × Excl × XFact → Prop := fun _ _ => False
def cnt : Acc → Bool := fun _ => true
def sX : XFact := ⟨⟨s, false⟩, Excl.empty⟩
def gX : XFact := ⟨⟨a, false⟩, Excl.empty⟩

abbrev R : XObj → Prop :=
  DBX Pb (fun _ => false) cnt 3 dem emitX satX restrictX noRecs [] [0] seeds

theorem hE : ((0 : MethodId), (0 : Node), Instr.call c, (1 : Node)) ∈ Pb.edges := List.Mem.head _

theorem d0 : R (.init 0 zeroFact false Excl.empty) := DBX.root (List.Mem.head _)
theorem d1 : R (.edge 0 zeroFact false Excl.empty 0 zeroX) := DBX.start d0
/-- The must seed: a NORMAL `[any-taint]` requirement (B1). -/
theorem d2 : R (.edge 0 zeroFact false Excl.empty 0 sX) := DBX.seed (List.Mem.head _) d1
/-- It passes over the call to the exit of method `0`. -/
theorem d3 : R (.edge 0 zeroFact false Excl.empty 1 sX) := DBX.pass d2 hE rfl
/-- The binding into the callee gives a MUST added fact (B2). -/
theorem d4 : R (.added 1 a true Excl.empty) :=
  DBX.added (a := gX) d2 hE (List.Mem.head _) (by decide)
/-- The emission gives a MUST premise. -/
theorem d5 : R (.init 1 a true Excl.empty) := DBX.initR (d := dd) d4 ⟨rfl, rfl⟩ (by decide)
/-- Its start fact is NORMAL; the callee entry is the callee exit: a backward MUST record. -/
theorem d6 : R (.edge 1 a true Excl.empty 0 gX) := DBX.start d5

theorem markWF : Exact.MarkWF Pb where
  stmt := by
    intro M n s n' hE
    cases hE with
    | tail _ h => cases h
  toC := by
    intro M n c' n' hE e he
    cases hE with
    | head =>
      cases he with
      | head => rfl
      | tail _ h => cases h
    | tail _ h => cases h
  fromC := by
    intro M n c' n' hE e he
    cases hE with
    | head => cases he
    | tail _ h => cases h

theorem filtUp : Exact.FiltUp Pb := by
  intro M n b may n' hE
  cases hE with
  | tail _ h => cases h

theorem noZeroIn : NoZeroIn Pb := by
  intro M n c' n' hE e he
  cases hE with
  | head =>
    cases he with
    | head => decide
    | tail _ h => cases h
  | tail _ h => cases h

theorem seedsConc : SeedsConcB seeds := by
  intro M n s' must h
  cases h with
  | head => exact ⟨5, rfl⟩
  | tail _ h => cases h

/-- In the callee every flow keeps its location. -/
theorem flow1 : ∀ {M l0 n l}, Flow Pb M l0 n l → M = 1 → l = l0 := by
  intro M l0 n l h
  induction h with
  | start => intro _; rfl
  | step _ hE _ _ => cases hE with | tail _ h => cases h
  | pass _ hE _ ih =>
    intro hM
    cases hE with
    | head => exact absurd hM (by decide)
    | tail _ h => cases h
  | call _ hE _ _ _ _ _ _ _ =>
    intro hM
    cases hE with
    | head => exact absurd hM (by decide)
    | tail _ h => cases h
  | clean _ hE _ _ => cases hE with | tail _ h => cases h
  | filt _ hE _ _ => cases hE with | tail _ h => cases h

/-- In method `0` the zero location stays the zero location. -/
theorem flow0 : ∀ {M l0 n l}, Flow Pb M l0 n l → M = 0 → l0 = zeroLoc → l = zeroLoc := by
  intro M l0 n l h
  induction h with
  | start => intro _ h; exact h
  | step _ hE _ _ => cases hE with | tail _ h => cases h
  | pass _ _ _ ih => exact ih
  | call _ hE _ _ _ he2 _ _ _ =>
    cases hE with
    | head => cases he2
    | tail _ h => cases h
  | clean _ hE _ _ => cases hE with | tail _ h => cases h
  | filt _ hE _ _ => cases hE with | tail _ h => cases h

/-- `CexMustPair.cex_must_pair`: the hypotheses of `recsB_exact` hold; the backward MUST record
    `(a, must, {}) → a` of the callee is END-EXACT but NOT PAIR-EXACT; the normal zero-premise exit
    edge `zero → (1,[],[any-taint],5)` of method `0` is not exact (so `exitRecsNZ` and the motive
    must exclude the zero premise). -/
theorem cex_must_pair :
    Exact.MarkWF Pb ∧ Exact.FiltUp Pb ∧ NoZeroIn Pb ∧ SeedsConcB seeds ∧
    exitRecsNZ Pb R 1 (a, true, Excl.empty, gX) ∧ gX.af.demand = false ∧
    EndExactX Pb (fun _ => True) 1 a Excl.empty (Pb.exit 1) gX.af.fact gX.ex ∧
    denX a Excl.empty gX.af.fact gX.ex ⟨2, [3], 5⟩ ⟨2, [4], 5⟩ ∧
    ¬ Flow Pb 1 ⟨2, [3], 5⟩ (Pb.exit 1) ⟨2, [4], 5⟩ ∧
    R (.edge 0 zeroFact false Excl.empty (Pb.exit 0) sX) ∧ sX.af.demand = false ∧
    carriesB sX.af = true ∧
    ¬ EdgeOKX Pb (fun _ => True) (.edge 0 zeroFact false Excl.empty (Pb.exit 0) sX) := by
  have hrec : exitRecsNZ Pb R 1 (a, true, Excl.empty, gX) := ⟨by decide, d6⟩
  have hend := recsB_must_end markWF (Exact.filtUp_ok filtUp) (Exact.backOK_true Pb) satX_inside
    restrictX_ok emitX_copies seedsConc noZeroIn (fun _ _ _ _ _ h => h.elim)
    (fun _ _ _ _ h => h.elim) (fun _ _ _ _ _ h => h.elim) hrec rfl
  have hd0 : denX zeroFact Excl.empty sX.af.fact sX.ex zeroLoc ⟨1, [], 5⟩ :=
    ⟨rfl, rfl, rfl, rfl, trivial, [], [], rfl, rfl, rfl, trivial, rfl, rfl⟩
  have hnf0 : ¬ Flow Pb 0 zeroLoc (Pb.exit 0) ⟨1, [], 5⟩ := fun hf => by
    have := flow0 hf rfl rfl
    cases this
  refine ⟨markWF, filtUp, noZeroIn, seedsConc, hrec, rfl, hend,
    ⟨rfl, rfl, rfl, rfl, trivial, [3], [4], rfl, rfl, trivial, trivial, rfl, rfl⟩,
    fun hf => ?_, d3, rfl, rfl, fun h => hnf0 ((h rfl).2 zeroLoc ⟨1, [], 5⟩ hd0 trivial).1⟩
  have := flow1 hf rfl
  cases this

#print axioms cex_must_pair

end CexMustPair

end ApSpec.BackMust

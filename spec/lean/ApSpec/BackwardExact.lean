/-
  ApSpec.BackwardExact — precision and the static invariant of the BACKWARD run `Backward.DB`,
  and record exactness over the forward run sequence.

  Part 1. `DB` HAS NO REQUEST AND IS CONCRETE (`DB_concrete`, `DB_no_request`): with a
    mark-copying emission (`EmitCopiesMark`, `emitM`) and seeds with concrete marks (`SeedsConc`;
    a seed is a sink pattern `s.mark = .conc T`). The seed hypothesis is necessary
    (`CexSeed.cex_seed`: a seed with the mark `*` gives a request).
  Part 2. EXACTNESS OF BACKWARD EDGES WITH A NON-ZERO PREMISE (`DB_edgeOK`, `edge_exactB`,
    `edge_exactB_valid`, `edge_exactB_rev`): a normal-layer edge of `DB` whose premise is not the
    zero fact denotes only real flows of the reversed program, if no reversed call binds into the
    callee's zero base (`NoZeroIn`; for `Program.rev P` it is `Backward.NoZeroBack P`,
    `noZeroIn_rev`). The zero-premise edges (`seed`) are not converse flows; under `NoZeroIn` no
    caller fact meets a zero-based premise, so they are never applied in a non-zero context. The
    persisted records need exactness only on premises off the zero base (`RecsExactNZ`).
    Conclusion (`summary_rev_flow`, `rev_record_exact`, `revRecs_exact`): a normal backward
    summary with a non-zero premise is a correct reversed record of `P` (a forward flow from the
    forward entry to the forward exit), and, with a mark-copying emission and concrete seeds, its
    reversal `revEdge jb gb` is an exact forward record (`RecsExact P`).
    Without `NoZeroBack` it is FALSE (`CexZeroBack`): a program that satisfies every other
    hypothesis of `Backward.B_general` and whose call binds the callee's zero back; the backward run
    (demand = a reversed summary of forward run 1, seeds = the sinks forward run 1 reports, one
    persisted record = a zero-premise exit edge of a backward run) derives a COMPLETE
    non-zero-premise backward summary whose reversal is not a forward flow (`cex_rec`); with no
    record and one more demand edge the rule `ret` derives it too (`cex_ret`, against the direct
    analogue of `RExact.edge_exactR` with the full `RecsExact`).
    The backward records over the backward runs: `recsB_step`, `recsBSeq_exact`.
  Part 3. RECORD EXACTNESS OVER THE RUN SEQUENCE (`recsSeq_exact`, `recsSeq_exactV`): if the
    records `recs k` that run `k + 1` of `RCov.runSeq` reuses are exit edges of runs `0 .. k`
    (`RecsFromRuns`; any subset, e.g. the complete ones), they satisfy `RecsExact` (`RecsExactV`).
    The accumulation `accRecs` (the union over the runs of the exit edges a policy `keep`
    persists) is an instance (`accRecs_from`, `accRecs_exact`, `accRecs_exactV`,
    `accRecs_exactM`); consequences: every normal-layer edge of every run is exact
    (`seq_edge_exact`) and every confirmed vulnerability of every restricted run is real
    (`seq_confirmed_real`), with no record hypothesis.
  Part 4. THE STATIC INVARIANT FOR `DB` (`binv_all`, `no_any_above_B`, `static_step_below_B`,
    `recOK_of_DB`): the analogue of `StaticsIter.rinv_all` for the backward run, under `SWFR` of the
    program it runs on and seeds that keep the invariant (`SeedsOK`); with it
    `no_static_rule_backward` (every backward run of the iteration satisfies the static invariant
    and has no request).

  All proofs are constructive (`propext`, `Quot.sound` only).
-/
import ApSpec.StaticsIter

namespace ApSpec.BExact
open ApSpec ApSpec.Reverse ApSpec.Backward

/-! ## Part 1. `DB` is concrete and has no request -/

/-- Every seed has a concrete mark (a seed is a sink pattern, `s.mark = .conc T`). -/
def SeedsConc (seeds : List (MethodId × Node × PFact)) : Prop :=
  ∀ M n s, (M, n, s) ∈ seeds → ∃ t, s.mark = .conc t

section Part1
variable {Pb : Program} {counted : Acc → Bool} {L : Nat}
  {demand : MethodId → DemandEdge → Prop}
  {emit : PFact → PFact → Option PFact}
  {sat : PFact → PFact → Bool}
  {restrict : PFact → AFact → DemandEdge → Option AFact}
  {recs : MethodId → PFact × AFact → Prop}
  {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId}
  {seeds : List (MethodId × Node × PFact)}
  {zbind : Bool}

/-- 1. CONCRETENESS OF THE BACKWARD RUN. With a mark-copying emission and concrete seeds, every
    initial fact, every edge (premise and final fact) and every added fact of `DB` has a concrete
    mark, and `DB` has no request object (any program, demand, satisfaction, restriction, records,
    sinks, roots and `zbind`). The zero rules keep the zero fact (`zpass`, `zin`), the sink rule
    gives the concrete seed (`seed`), the balanced return applies a summary to the concrete zero
    fact (`zret`). -/
theorem DB_concrete (hem : EmitCopiesMark emit) (hsd : SeedsConc seeds) {o : Obj}
    (h : DB Pb counted L demand emit sat restrict recs sinks roots seeds zbind o) :
    RExact.ConcObj o := by
  induction h with
  | root => exact ⟨zeroMark, rfl⟩
  | @start M i _ ih =>
    obtain ⟨t, ht⟩ := ih
    exact ⟨⟨t, ht⟩, t, by rw [startFact_mark, ht]⟩
  | @step M i n f n' s f' _ _ hf ih =>
    obtain ⟨hi, t, ht⟩ := ih
    exact ⟨hi, transfer_mark_conc ht hf⟩
  | @reqStmt M i n f n' s t _ _ ht ih =>
    obtain ⟨_, t0, h0⟩ := ih
    rw [transfer_reqs_of_conc h0] at ht
    cases ht
  | pass _ _ _ ih => exact ih
  | @added M i n f n' c e a _ _ _ ha ih =>
    obtain ⟨_, t, ht⟩ := ih
    exact applyEdge_mark_conc ht ha
  | @initR m a d j _ _ hj ih =>
    obtain ⟨t, ht⟩ := ih
    exact ⟨t, by rw [hem _ _ _ hj, ht]⟩
  | @ret M i n f n' c e1 a j g d g' r e2 r' _ _ _ ha _ _ _ _ _ hr _ hr' ihF _ _ =>
    obtain ⟨hi, t, ht⟩ := ihF
    obtain ⟨t1, h1⟩ := applyEdge_mark_conc ht ha
    obtain ⟨t2, h2⟩ := applySummary_mark_conc h1 hr
    obtain ⟨t3, h3⟩ := applyEdge_mark_conc h2 hr'
    exact ⟨hi, t3, by rw [limitF_mark, h3]⟩
  | @retRec M i n f n' c e1 a j g r e2 r' _ _ _ ha _ _ hr _ hr' ihF =>
    obtain ⟨hi, t, ht⟩ := ihF
    obtain ⟨t1, h1⟩ := applyEdge_mark_conc ht ha
    obtain ⟨t2, h2⟩ := applySummary_mark_conc h1 hr
    obtain ⟨t3, h3⟩ := applyEdge_mark_conc h2 hr'
    exact ⟨hi, t3, by rw [limitF_mark, h3]⟩
  | @reqSink M i n f s t _ _ hc ih =>
    obtain ⟨⟨t0, h0⟩, _⟩ := ih
    exact check_request_star hc t0 h0
  | answer _ _ _ _ ihR _ => exact ihR.elim
  | reqUp _ _ _ _ _ _ _ _ ihR _ => exact ihR.elim
  | vuln => trivial
  | @clean M i n f n' cl f' _ _ hf ih =>
    obtain ⟨hi, t, ht⟩ := ih
    exact ⟨hi, cleanRes_mark_conc ht hf⟩
  | @reqClean M i n f n' cl t _ _ ht ih =>
    obtain ⟨_, t0, h0⟩ := ih
    exact (cleanRes_reqs_abstract ht).1 t0 h0
  | filt _ _ _ ih => exact ih
  | zpass => exact ⟨⟨zeroMark, rfl⟩, zeroMark, rfl⟩
  | zin => exact ⟨zeroMark, rfl⟩
  | @seed M n s hs _ _ =>
    obtain ⟨t, ht⟩ := hsd M n s hs
    exact ⟨⟨zeroMark, rfl⟩, t, by rw [limitF_mark]; exact ht⟩
  | @zret M n n' c g r e2 r' _ _ _ _ hr _ hr' _ _ =>
    obtain ⟨t2, h2⟩ := applySummary_mark_conc (a := zeroAF) (t := zeroMark) rfl hr
    obtain ⟨t3, h3⟩ := applyEdge_mark_conc h2 hr'
    exact ⟨⟨zeroMark, rfl⟩, t3, by rw [limitF_mark, h3]⟩

#print axioms DB_concrete

/-- 1'. NO REQUEST IN A BACKWARD RUN: with a mark-copying emission and concrete seeds, `DB`
    contains no request object (so the rules `answer` and `reqUp` never fire). -/
theorem DB_no_request (hem : EmitCopiesMark emit) (hsd : SeedsConc seeds) :
    ∀ M i t, ¬ DB Pb counted L demand emit sat restrict recs sinks roots seeds zbind (.req M i t) :=
  fun _ _ _ h => DB_concrete hem hsd h

#print axioms DB_no_request

/-- Every added fact of the backward run is concrete. -/
theorem DB_added_concrete (hem : EmitCopiesMark emit) (hsd : SeedsConc seeds) :
    ∀ m a, DB Pb counted L demand emit sat restrict recs sinks roots seeds zbind (.added m a) →
      ∃ t, a.mark = .conc t :=
  fun _ _ h => DB_concrete hem hsd h

#print axioms DB_added_concrete

/-- Every edge of the backward run is concrete (premise and final fact). -/
theorem DB_edge_concrete (hem : EmitCopiesMark emit) (hsd : SeedsConc seeds) {M : MethodId}
    {i : PFact} {n : Node} {f : AFact}
    (h : DB Pb counted L demand emit sat restrict recs sinks roots seeds zbind (.edge M i n f)) :
    (∃ t, i.mark = .conc t) ∧ ∃ t, f.fact.mark = .conc t :=
  DB_concrete hem hsd h

#print axioms DB_edge_concrete

/-- With a mark-copying emission and concrete seeds, the contract for concrete added facts gives
    the contract for the backward run. -/
theorem DB_emitContractOn (hem : EmitCopiesMark emit) (hsd : SeedsConc seeds)
    (hc : EmitContractConc emit sat) :
    EmitContractOn (DB Pb counted L demand emit sat restrict recs sinks roots seeds zbind) emit sat :=
  EmitContractConc.on hc (DB_added_concrete hem hsd)

#print axioms DB_emitContractOn

/-- Every initial fact of a backward run with a mark-copying emission and concrete seeds is a
    root zero fact, the zero fact entering a callee (`zin`), or an emission; never an answer. -/
theorem DB_no_answer_init (hem : EmitCopiesMark emit) (hsd : SeedsConc seeds) {m : MethodId}
    {j : PFact} (h : DB Pb counted L demand emit sat restrict recs sinks roots seeds zbind (.init m j)) :
    j = zeroFact ∨
    ∃ d a, demand m d ∧ DB Pb counted L demand emit sat restrict recs sinks roots seeds zbind
      (.added m a) ∧ emit d.din a = some j := by
  cases h with
  | root _ => exact Or.inl rfl
  | initR ha hd hj => exact Or.inr ⟨_, _, hd, ha, hj⟩
  | answer hR _ _ _ => exact (DB_no_request hem hsd _ _ _ hR).elim
  | zin _ _ _ => exact Or.inl rfl

#print axioms DB_no_answer_init

/-- The premise-layer motive (`RExact.PremLayer`) holds on every object of `DB` (no hypothesis):
    the zero rules make edges of the exact zero premise. -/
theorem DB_premLayer {o : Obj}
    (h : DB Pb counted L demand emit sat restrict recs sinks roots seeds zbind o) :
    RExact.PremLayer o := by
  induction h with
  | root => trivial
  | @start M i _ _ =>
    intro hd
    obtain ⟨ib, ip, ik, im⟩ := i
    cases ik with
    | exact => exact Or.inl rfl
    | any => cases im <;> cases hd
    | star e =>
      cases im with
      | star => exact Or.inr rfl
      | starEx x => exact Or.inr rfl
      | conc t => cases hd
  | step _ _ hf ih => exact fun hd => ih (Exact.transfer_demand hf hd)
  | reqStmt => trivial
  | pass _ _ _ ih => exact ih
  | added => trivial
  | initR => trivial
  | @ret M i n f n' c e1 a j g d g' r e2 r' _ _ _ ha _ _ _ _ _ hr _ hr' ihF _ _ =>
    intro hla
    have e := Exact.limitF_exact hla
    rw [e] at hla
    have hra := Exact.applyEdge_demand hr' hla
    obtain ⟨x, hx, rfl⟩ := Exact.applySummary_mem hr hra
    obtain ⟨hxa, _⟩ := Exact.or_eq_false hra
    exact ihF (Exact.applyEdge_demand ha (Exact.applyEdge_demand hx hxa))
  | @retRec M i n f n' c e1 a j g r e2 r' _ _ _ ha _ _ hr _ hr' ihF =>
    intro hla
    have e := Exact.limitF_exact hla
    rw [e] at hla
    have hra := Exact.applyEdge_demand hr' hla
    obtain ⟨x, hx, rfl⟩ := Exact.applySummary_mem hr hra
    obtain ⟨hxa, _⟩ := Exact.or_eq_false hra
    exact ihF (Exact.applyEdge_demand ha (Exact.applyEdge_demand hx hxa))
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial
  | clean _ _ hf ih => exact fun hd => ih (Exact.cleanRes_demand hf hd)
  | reqClean => trivial
  | filt _ _ _ ih => exact ih
  | zpass => exact fun _ => Or.inl rfl
  | zin => trivial
  | seed => exact fun _ => Or.inl rfl
  | zret => exact fun _ => Or.inl rfl

#print axioms DB_premLayer

/-- A normal-layer edge of a concrete backward run has an EXACT premise. -/
theorem DB_premise_exact (hem : EmitCopiesMark emit) (hsd : SeedsConc seeds) {M : MethodId}
    {i : PFact} {n : Node} {f : AFact}
    (h : DB Pb counted L demand emit sat restrict recs sinks roots seeds zbind (.edge M i n f))
    (hd : f.demand = false) : i.kind = .exact := by
  rcases DB_premLayer h hd with hk | hm
  · exact hk
  · obtain ⟨⟨t, ht⟩, _⟩ := DB_concrete hem hsd h
    rw [ht] at hm
    cases hm

#print axioms DB_premise_exact

end Part1

/-- The spec rules: a backward run with `emitM` and sink seeds (concrete marks) has no request,
    for every satisfaction, restriction, demand and record set. -/
theorem DB_no_requestM {Pb : Program} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop} {sat : PFact → PFact → Bool}
    {restrict : PFact → AFact → DemandEdge → Option AFact}
    {recs : MethodId → PFact × AFact → Prop} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {seeds : List (MethodId × Node × PFact)} {zbind : Bool}
    (hsd : SeedsConc seeds) :
    ∀ M i t, ¬ DB Pb counted L demand emitM sat restrict recs sinks roots seeds zbind (.req M i t) :=
  DB_no_request RExact.emitM_copies hsd

#print axioms DB_no_requestM

/-! ### The seed hypothesis is necessary

One method, one statement `y := x` whose micro edge reads the concrete mark 5. A seed at its node
with the mark `*` gives the backward edge `0 → (1, ., $, *)`; the statement raises the mark
request 5. -/

namespace CexSeed

def sx : Stmt := ⟨[1], [(⟨1, [], .exact, .conc 5⟩, ⟨2, [], .exact, .conc 5⟩)]⟩
def Pb : Program := ⟨fun _ => 0, fun _ => 1, [(0, 0, .stmt sx, 1)]⟩
def sStar : PFact := ⟨1, [], .exact, .star⟩
def seeds : List (MethodId × Node × PFact) := [(0, 0, sStar)]

theorem cex_seed :
    ¬ SeedsConc seeds ∧
    DB Pb (fun _ => true) 2 (fun _ _ => False) emitM satI restrictU (fun _ _ => False) [] [0]
      seeds true (.req 0 zeroFact 5) := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨t, ht⟩ := h 0 0 sStar (List.Mem.head _)
    cases ht
  · have h0 : DB Pb (fun _ => true) 2 (fun _ _ => False) emitM satI restrictU (fun _ _ => False)
        [] [0] seeds true (.edge 0 zeroFact 0 zeroAF) := DB.start (DB.root (List.Mem.head _))
    have h1 := DB.seed (List.Mem.head _) h0
    exact DB.reqStmt (s := sx) (n' := 1) h1 (List.Mem.head _) (by decide)

#print axioms cex_seed

end CexSeed

/-! ## Part 2. Exactness of backward edges with a non-zero premise

The zero-premise edges of `DB` are not converse flows (`seed` puts a sink pattern on the zero
premise: `Backward.seed_den`). An edge with a non-zero premise is built from its initial fact by
the rules of `DR` only; it reads a zero-premise edge only through a summary application (`ret`,
`retRec`) whose premise is the zero fact. If no reversed call binds into the callee's zero base
(`NoZeroIn`, which is `NoZeroBack` of the forward program), the added fact of a call is never on
the zero base, so a summary with a zero-based premise gives nothing: the zero-premise edges never
enter a non-zero premise. -/

/-- No call binds INTO the callee's zero base. -/
def NoZeroIn (Pb : Program) : Prop :=
  ∀ M n c n', (M, n, Instr.call c, n') ∈ Pb.edges → ∀ e, e ∈ c.toCallee → e.2.base ≠ zeroBase

/-- The reversed program binds into the callee's zero base iff the forward program binds the
    callee's zero base back: `NoZeroBack P` gives `NoZeroIn (Program.rev P)`. -/
theorem noZeroIn_rev {P : Program} (h : NoZeroBack P) : NoZeroIn (Program.rev P) := by
  intro M n c' n' hE e he
  obtain ⟨c, hm, rfl⟩ := rev_call_inv hE
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
  show e0.1.base ≠ zeroBase
  exact h _ _ _ _ hm e0 he0

#print axioms noZeroIn_rev

/-- A summary application reads only a premise on the base of the caller's added fact. -/
theorem applySummary_base {a r g : AFact} {j : PFact} (h : r ∈ (applySummary a j g).facts) :
    a.fact.base = j.base := by
  obtain ⟨x, hx, _⟩ := List.mem_map.mp h
  exact Statics.applyEdge_base_eq hx

/-- Under `NoZeroIn`, a summary applied at a call (rules `ret`, `retRec`) has a premise off the
    zero base. -/
theorem no_zero_summary {Pb : Program} (hnz : NoZeroIn Pb) {M : MethodId} {n n' : Node} {c : Call}
    {e1 : MicroEdge} {f a g r : AFact} {j : PFact}
    (hE : (M, n, Instr.call c, n') ∈ Pb.edges) (he1 : e1 ∈ c.toCallee)
    (ha : a ∈ (applyEdge f e1.1 e1.2).facts) (hr : r ∈ (applySummary a j g).facts) :
    j.base ≠ zeroBase := by
  intro hj
  have h1 := applySummary_base hr
  have h2 := Statics.applyEdge_base ha
  exact hnz _ _ _ _ hE e1 he1 (h2.symm.trans (h1.trans hj))

#print axioms no_zero_summary

theorem ne_zero_of_base {j : PFact} (h : j.base ≠ zeroBase) : j ≠ zeroFact :=
  fun e => h (by rw [e]; rfl)

/-- The motive: `RExact.EdgeOKR` on the edges with a non-zero premise. -/
def EdgeOKNZ (Pb : Program) (ok : Loc → Prop) : Obj → Prop
  | .edge M i n f => i ≠ zeroFact → RExact.EdgeOKR Pb ok (.edge M i n f)
  | _ => True

/-- The persisted records of a backward run are exact (valid form) on the premises OFF the zero
    base (a record with a zero-based premise never applies under `NoZeroIn`, so it may be a
    zero-premise backward summary). -/
def RecsExactVNZ (Pb : Program) (ok : Loc → Prop) (recs : MethodId → PFact × AFact → Prop) : Prop :=
  ∀ m j g, recs m (j, g) → j.base ≠ zeroBase → RExact.EdgeOKR Pb ok (.edge m j (Pb.exit m) g)

/-- The persisted records are exact on the premises off the zero base. -/
def RecsExactNZ (Pb : Program) (recs : MethodId → PFact × AFact → Prop) : Prop :=
  ∀ m j g, recs m (j, g) → j.base ≠ zeroBase → g.demand = false → ∀ l1 l2, den j g.fact l1 l2 →
    Flow Pb m l1 (Pb.exit m) l2

theorem RecsExact.toNZ {Pb : Program} {recs : MethodId → PFact × AFact → Prop}
    (h : RExact.RecsExact Pb recs) : RecsExactNZ Pb recs :=
  fun m j g hr _ hg l1 l2 hd => h m j g hr hg l1 l2 hd

/-- An exact record (off the zero base) with an abstract premise mark has an abstract conclusion
    mark (as `RExact.recs_abs`). -/
theorem recs_absNZ {Pb : Program} {recs : MethodId → PFact × AFact → Prop}
    (hmw : Exact.MarkWF Pb) (hrecs : RecsExactNZ Pb recs) {m : MethodId} {j : PFact} {g : AFact}
    (hr : recs m (j, g)) (hjb : j.base ≠ zeroBase) (hg : g.demand = false)
    (hj : Exact.absB j.mark = true) : Exact.absB g.fact.mark = true := by
  cases hm : g.fact.mark with
  | star => rfl
  | starEx x => rfl
  | conc t =>
    exfalso
    obtain ⟨m0, hjm, hmt, hfr⟩ := RExact.fresh_mark hj t (RExact.progMarks Pb.edges)
    have hfl := hrecs m j g hr hjb hg _ _ (RExact.den_nil j g.fact hjm (by rw [hm]; trivial))
    have hk : g.fact.mark.out m0 = m0 := RExact.flow_keep hmw hfl hfr
    rw [hm] at hk
    exact hmt hk.symm

#print axioms recs_absNZ

theorem RecsExactNZ.toV {Pb : Program} {recs : MethodId → PFact × AFact → Prop}
    (hmw : Exact.MarkWF Pb) (h : RecsExactNZ Pb recs) : RecsExactVNZ Pb (fun _ => True) recs :=
  fun _ j g hr hjb hg => ⟨recs_absNZ hmw h hr hjb hg,
    fun l1 l2 hd _ => ⟨h _ j g hr hjb hg l1 l2 hd, trivial⟩⟩

#print axioms RecsExactNZ.toV

section Part2
variable {Pb : Program} {counted : Acc → Bool} {L : Nat}
  {demand : MethodId → DemandEdge → Prop}
  {emit : PFact → PFact → Option PFact}
  {sat : PFact → PFact → Bool}
  {restrict : PFact → AFact → DemandEdge → Option AFact}
  {recs : MethodId → PFact × AFact → Prop}
  {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId}
  {seeds : List (MethodId × Node × PFact)}
  {zbind : Bool}

/-- 2. THE MOTIVE ON THE BACKWARD RUN: `EdgeOKR` holds on every edge of `DB` with a non-zero
    premise. Hypotheses: those of `RExact.DR_edgeOK` (`MarkWF`, `FiltOK`, `BackOK` of the program
    the run runs on, `SatMark sat`, `RestrictSub restrict`, valid records, here only off the zero
    base), and `NoZeroIn`. No hypothesis on the demand, the emission, the seeds, the sinks, the
    roots or `zbind`. -/
theorem DB_edgeOK {ok : Loc → Prop} (hmw : Exact.MarkWF Pb) (hfo : Exact.FiltOK Pb ok)
    (hbo : Exact.BackOK Pb ok) (hsat : RExact.SatMark sat) (hsub : RestrictSub restrict)
    (hnz : NoZeroIn Pb) (hrecs : RecsExactVNZ Pb ok recs) {o : Obj}
    (h : DB Pb counted L demand emit sat restrict recs sinks roots seeds zbind o) :
    EdgeOKNZ Pb ok o := by
  induction h with
  | root => trivial
  | @start M i _ _ =>
    intro _ ha
    refine ⟨fun hi => by rw [startFact_mark]; exact hi, fun l0 l hd hok => ?_⟩
    have e := Exact.startFact_exact ha hd
    subst e
    exact ⟨Flow.start M l, hok⟩
  | @step M i n f n' s f' _ hE hf ih =>
    intro hz ha
    have hfa := Exact.transfer_demand hf ha
    obtain ⟨ih1, ih2⟩ := ih hz hfa
    refine ⟨fun hi => Exact.transfer_abs (hmw.stmt _ _ _ _ hE) (ih1 hi) hf, fun l0 l hd hok => ?_⟩
    obtain ⟨l1, hd1, hs⟩ := Exact.transfer_exact (hmw.stmt _ _ _ _ hE) hfa hf ha hd
    have hok1 : ok l1 := by
      rcases hs with ⟨-, rfl⟩ | ⟨e, he, hde⟩
      · exact hok
      · exact hbo.stmt _ _ _ _ hE e he _ _ hde hok
    obtain ⟨hfl, hok0⟩ := ih2 l0 l1 hd1 hok1
    exact ⟨Flow.step hfl hE hs, hok0⟩
  | reqStmt => trivial
  | @pass M i n f n' c _ hE hm ih =>
    intro hz ha
    obtain ⟨ih1, ih2⟩ := ih hz ha
    refine ⟨ih1, fun l0 l hd hok => ?_⟩
    obtain ⟨hfl, hok0⟩ := ih2 l0 l hd hok
    refine ⟨Flow.pass hfl hE ?_, hok0⟩
    rw [hd.2.1]
    exact hm
  | added => trivial
  | initR => trivial
  | @ret M i n f n' c e1 a j g d g' r e2 r' _ hE he1 ha _ _ _ hres hs hr he2 hr' ihD _ ihG =>
    intro hz
    -- the callee premise is off the zero base: its edges have a non-zero premise
    have hjz : j ≠ zeroFact := ne_zero_of_base (no_zero_summary hnz hE he1 ha hr)
    obtain ⟨hgd, hgsub⟩ := hsub j g d g' hres
    have ihG' : RExact.EdgeOKR Pb ok (.edge c.callee j (Pb.exit c.callee) g') := by
      intro hg'
      obtain ⟨h1, h2⟩ := ihG hjz (hgd.symm.trans hg')
      exact ⟨fun hJ => RExact.abs_of_sub hJ (h1 hJ) hgsub,
        fun l1 l2 hd hok => h2 l1 l2 (hgsub l1 l2 hd) hok⟩
    exact RExact.summary_ok hmw hbo hE he1 ha (hsat j a.fact hs) hr he2 hr' (ihD hz) ihG'
  | @retRec M i n f n' c e1 a j g r e2 r' _ hE he1 ha hrec hs hr he2 hr' ihD =>
    intro hz
    exact RExact.summary_ok hmw hbo hE he1 ha (RExact.recApp_markSub hsat hs) hr he2 hr' (ihD hz)
      (hrecs c.callee j g hrec (no_zero_summary hnz hE he1 ha hr))
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial
  | @clean M i n f n' cl f' _ hE hf ih =>
    intro hz ha
    have hfa := Exact.cleanRes_demand hf ha
    obtain ⟨ih1, ih2⟩ := ih hz hfa
    refine ⟨fun hi => Exact.cleanRes_abs (ih1 hi) hf, fun l0 l hd hok => ?_⟩
    obtain ⟨hd1, hcl⟩ := Exact.cleanRes_exact hf ha hd
    obtain ⟨hfl, hok0⟩ := ih2 l0 l hd1 hok
    exact ⟨Flow.clean hfl hE hcl, hok0⟩
  | reqClean => trivial
  | @filt M i n f n' b may _ hE hp ih =>
    intro hz ha
    obtain ⟨ih1, ih2⟩ := ih hz ha
    refine ⟨ih1, fun l0 l hd hok => ?_⟩
    obtain ⟨hfl, hok0⟩ := ih2 l0 l hd hok
    refine ⟨Flow.filt hfl hE ?_, hok0⟩
    intro hb
    obtain ⟨-, hlb, -, -, -, σ, τ, -, hlp, -, -⟩ := hd
    exact hfo _ _ _ _ _ hE f.fact.path τ l (hp (hlb.symm.trans hb)) hlp hok hb
  -- the zero rules make edges of the zero premise only
  | zpass => exact fun hz => absurd rfl hz
  | zin => trivial
  | seed => exact fun hz => absurd rfl hz
  | zret => exact fun hz => absurd rfl hz

#print axioms DB_edgeOK

/-- 2'. THE EXACTNESS THEOREM FOR THE BACKWARD RUN. A normal-layer edge of `DB` whose premise is
    not the zero fact denotes only real flows of the program it runs on. Hypotheses: those of
    `RExact.edge_exactR`, the records exact off the zero base, and `NoZeroIn`. -/
theorem edge_exactB (hmw : Exact.MarkWF Pb) (hup : Exact.FiltUp Pb) (hsat : RExact.SatMark sat)
    (hsub : RestrictSub restrict) (hnz : NoZeroIn Pb) (hrecs : RecsExactNZ Pb recs)
    {M : MethodId} {i : PFact} {n : Node} {f : AFact} {l0 l : Loc}
    (h : DB Pb counted L demand emit sat restrict recs sinks roots seeds zbind (.edge M i n f))
    (hi : i ≠ zeroFact) (ha : f.demand = false) (hd : den i f.fact l0 l) : Flow Pb M l0 n l :=
  ((DB_edgeOK hmw (Exact.filtUp_ok hup) (Exact.backOK_true Pb) hsat hsub hnz (hrecs.toV hmw) h hi
    ha).2 l0 l hd trivial).1

#print axioms edge_exactB

/-- 2v. The valid form (prefix-closed type filters, no `FiltUp`). -/
theorem edge_exactB_valid {ok : Loc → Prop} (hmw : Exact.MarkWF Pb) (hv : Exact.FiltValid Pb ok)
    (hbo : Exact.BackOK Pb ok) (hsat : RExact.SatMark sat) (hsub : RestrictSub restrict)
    (hnz : NoZeroIn Pb) (hrecs : RecsExactVNZ Pb ok recs)
    {M : MethodId} {i : PFact} {n : Node} {f : AFact} {l0 l : Loc}
    (h : DB Pb counted L demand emit sat restrict recs sinks roots seeds zbind (.edge M i n f))
    (hi : i ≠ zeroFact) (ha : f.demand = false) (hd : den i f.fact l0 l) (hok : ok l) :
    Flow Pb M l0 n l ∧ ok l0 :=
  (DB_edgeOK hmw (Exact.filtValid_ok hv) hbo hsat hsub hnz hrecs h hi ha).2 l0 l hd hok

#print axioms edge_exactB_valid

/-- The exit edges of a backward run with a non-zero premise are exact records: the records of
    the backward run together with its exit edges are exact off the zero base (a later backward
    run can reuse them). -/
theorem recsB_step (hmw : Exact.MarkWF Pb) (hup : Exact.FiltUp Pb) (hsat : RExact.SatMark sat)
    (hsub : RestrictSub restrict) (hnz : NoZeroIn Pb) (hrecs : RecsExactNZ Pb recs) :
    RecsExactNZ Pb (fun m jg => recs m jg ∨
      RExact.exitRecs Pb (DB Pb counted L demand emit sat restrict recs sinks roots seeds zbind) m jg) := by
  intro m j g hr hjb hg l1 l2 hd
  rcases hr with hr | hr
  · exact hrecs m j g hr hjb hg l1 l2 hd
  · exact edge_exactB hmw hup hsat hsub hnz hrecs hr (ne_zero_of_base hjb) hg hd

#print axioms recsB_step

end Part2

/-! ### The reversed program -/

/-- `revEdge` keeps `markEdgeB`. -/
theorem markEdge_rev {i f : PFact} (h : Exact.markEdgeB i.mark f.mark = true) :
    Exact.markEdgeB (revEdge i f).1.mark (revEdge i f).2.mark = true := by
  obtain ⟨ib, ip, ik, im⟩ := i
  obtain ⟨fb, fp, fk, fm⟩ := f
  cases im <;> cases fm <;> first | rfl | (exfalso; exact Bool.false_ne_true h)

/-- The reversed program keeps `MarkWF`. -/
theorem markWF_rev {P : Program} (h : Exact.MarkWF P) : Exact.MarkWF (Program.rev P) where
  stmt := by
    intro M n s' n' hE e he
    obtain ⟨s, hm, rfl⟩ := rev_stmt_inv hE
    rcases List.mem_append.mp he with h1 | h2
    · obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp h1
      exact markEdge_rev (h.stmt _ _ _ _ hm e0 he0)
    · obtain ⟨b, _, rfl⟩ := List.mem_map.mp h2
      rfl
  toC := by
    intro M n c' n' hE e he
    obtain ⟨c, hm, rfl⟩ := rev_call_inv hE
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
    exact markEdge_rev (h.fromC _ _ _ _ hm e0 he0)
  fromC := by
    intro M n c' n' hE e he
    obtain ⟨c, hm, rfl⟩ := rev_call_inv hE
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
    exact markEdge_rev (h.toC _ _ _ _ hm e0 he0)

#print axioms markWF_rev

/-- The reversed program keeps `FiltUp` (its filters are the filters of `P`). -/
theorem filtUp_rev {P : Program} (h : Exact.FiltUp P) : Exact.FiltUp (Program.rev P) := by
  intro M n b may n' hE p q hp
  exact h _ _ _ _ _ (rev_filt_inv hE) p q hp

/-- The reversed program keeps `FiltValid`. -/
theorem filtValid_rev {P : Program} {ok : Loc → Prop} (h : Exact.FiltValid P ok) :
    Exact.FiltValid (Program.rev P) ok := by
  intro M n b may n' hE l hok hb
  exact h _ _ _ _ _ (rev_filt_inv hE) l hok hb

#print axioms filtUp_rev
#print axioms filtValid_rev

section Part2rev
variable {P : Program} {counted : Acc → Bool} {L : Nat}
  {demand : MethodId → DemandEdge → Prop}
  {emit : PFact → PFact → Option PFact}
  {sat : PFact → PFact → Bool}
  {restrict : PFact → AFact → DemandEdge → Option AFact}
  {recs : MethodId → PFact × AFact → Prop}
  {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId}
  {seeds : List (MethodId × Node × PFact)}
  {zbind : Bool}

/-- 2r. THE EXACTNESS THEOREM FOR THE BACKWARD RUN OF THE DESIGN (on `Program.rev P`). Hypotheses
    on the FORWARD program: `MarkWF P`, `FiltUp P` and `NoZeroBack P` (the hypothesis of
    `Backward.B_general`); `SatMark sat`, `RestrictSub restrict`, the backward records exact off the
    zero base. A normal-layer backward edge with a non-zero premise denotes only real flows of the
    reversed program. -/
theorem edge_exactB_rev (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hNZB : NoZeroBack P)
    (hsat : RExact.SatMark sat) (hsub : RestrictSub restrict)
    (hrecs : RecsExactNZ (Program.rev P) recs)
    {M : MethodId} {i : PFact} {n : Node} {f : AFact} {l0 l : Loc}
    (h : DB (Program.rev P) counted L demand emit sat restrict recs sinks roots seeds zbind
      (.edge M i n f))
    (hi : i ≠ zeroFact) (ha : f.demand = false) (hd : den i f.fact l0 l) :
    Flow (Program.rev P) M l0 n l :=
  edge_exactB (markWF_rev hmw) (filtUp_rev hup) hsat hsub (noZeroIn_rev hNZB) hrecs h hi ha hd

#print axioms edge_exactB_rev

/-- 2s. A NORMAL BACKWARD SUMMARY WITH A NON-ZERO PREMISE IS A CORRECT REVERSED RECORD: an edge
    `jb → gb` at the backward exit (the forward entry) relates `l0` (forward exit) to `l` (forward
    entry) only if the value at `l` on the forward entry flows to `l0` at the forward exit of `P`.
    Added hypotheses: `RevStmts P`, `RevCalls P` (those of `Reverse.flow_rev_iff_calls`). -/
theorem summary_rev_flow (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hNZB : NoZeroBack P)
    (hR : RevStmts P) (hC : RevCalls P)
    (hsat : RExact.SatMark sat) (hsub : RestrictSub restrict)
    (hrecs : RecsExactNZ (Program.rev P) recs)
    {M : MethodId} {jb : PFact} {gb : AFact} {l0 l : Loc}
    (h : DB (Program.rev P) counted L demand emit sat restrict recs sinks roots seeds zbind
      (.edge M jb ((Program.rev P).exit M) gb))
    (hjb : jb ≠ zeroFact) (hg : gb.demand = false) (hd : den jb gb.fact l0 l) :
    Flow P M l (P.exit M) l0 :=
  (flow_rev_iff_calls hR hC).mpr (edge_exactB_rev hmw hup hNZB hsat hsub hrecs h hjb hg hd)

#print axioms summary_rev_flow

/-- 2s'. With a mark-copying emission and concrete seeds, the reversal `revEdge jb gb` of a normal
    backward summary with a non-zero premise is an exact FORWARD record of `P` (its premise is exact
    and concrete, so the reversal is exact: `Reverse.rev_exact_of_empty_premise`). -/
theorem rev_record_exact (hem : EmitCopiesMark emit) (hsd : SeedsConc seeds)
    (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hNZB : NoZeroBack P)
    (hR : RevStmts P) (hC : RevCalls P)
    (hsat : RExact.SatMark sat) (hsub : RestrictSub restrict)
    (hrecs : RecsExactNZ (Program.rev P) recs)
    {M : MethodId} {jb : PFact} {gb : AFact}
    (h : DB (Program.rev P) counted L demand emit sat restrict recs sinks roots seeds zbind
      (.edge M jb ((Program.rev P).exit M) gb))
    (hjb : jb ≠ zeroFact) (hg : gb.demand = false) {l l0 : Loc}
    (hd : den (revEdge jb gb.fact).1 (revEdge jb gb.fact).2 l l0) :
    Flow P M l (P.exit M) l0 := by
  have hk : jb.kind = .exact := DB_premise_exact hem hsd h hg
  have hpe : PremEmpty jb.kind := by rw [hk]; exact True.intro
  have hmr : MarkRev jb gb.fact := Or.inr (DB_edge_concrete hem hsd h).1
  exact summary_rev_flow hmw hup hNZB hR hC hsat hsub hrecs h hjb hg
    ((rev_exact_of_empty_premise hpe hmr).mpr hd)

#print axioms rev_record_exact

end Part2rev

/-- The reversed normal backward summaries with a non-zero premise, as FORWARD records of `P`. -/
def revRecs (P : Program) (RB : Obj → Prop) (m : MethodId) (jg : PFact × AFact) : Prop :=
  ∃ jb gb, RB (.edge m jb ((Program.rev P).exit m) gb) ∧ jb ≠ zeroFact ∧ gb.demand = false ∧
    jg = ((revEdge jb gb.fact).1, ⟨(revEdge jb gb.fact).2, false⟩)

/-- 2t. THE REVERSED BACKWARD SUMMARIES ARE EXACT FORWARD RECORDS (`RecsExact P`): a forward run
    can persist and reuse them (`DR.retRec`). -/
theorem revRecs_exact {P : Program} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop} {emit : PFact → PFact → Option PFact}
    {sat : PFact → PFact → Bool} {restrict : PFact → AFact → DemandEdge → Option AFact}
    {recs : MethodId → PFact × AFact → Prop} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {seeds : List (MethodId × Node × PFact)} {zbind : Bool}
    (hem : EmitCopiesMark emit) (hsd : SeedsConc seeds)
    (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hNZB : NoZeroBack P)
    (hR : RevStmts P) (hC : RevCalls P)
    (hsat : RExact.SatMark sat) (hsub : RestrictSub restrict)
    (hrecs : RecsExactNZ (Program.rev P) recs) :
    RExact.RecsExact P (revRecs P
      (DB (Program.rev P) counted L demand emit sat restrict recs sinks roots seeds zbind)) := by
  intro m j g hr _ l1 l2 hd
  obtain ⟨jb, gb, h, hjb, hg, e⟩ := hr
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact rev_record_exact hem hsd hmw hup hNZB hR hC hsat hsub hrecs h hjb hg hd

#print axioms revRecs_exact

/-- The spec rules (`emitM`, `satI`, `restrictU`) with sink seeds: the reversed backward summaries
    are exact forward records. -/
theorem revRecs_exactM {P : Program} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop}
    {recs : MethodId → PFact × AFact → Prop} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {seeds : List (MethodId × Node × PFact)} {zbind : Bool}
    (hsd : SeedsConc seeds) (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hNZB : NoZeroBack P)
    (hR : RevStmts P) (hC : RevCalls P) (hrecs : RecsExactNZ (Program.rev P) recs) :
    RExact.RecsExact P (revRecs P
      (DB (Program.rev P) counted L demand emitM satI restrictU recs sinks roots seeds zbind)) :=
  revRecs_exact RExact.emitM_copies hsd hmw hup hNZB hR hC RExact.satI_mark RExact.restrictU_sub hrecs

#print axioms revRecs_exactM

/-! ### Without `NoZeroBack` the exactness is false

The program (forward orientation; base `0` is the zero base, every binding is `b.* → b'.*`):
  * root `0`: `v5 = source(); m2(v5); r1 = m1(); sink(r1)` — node 3 → 2 → 1 → 0;
  * method `1`: `m2(a4); v2 = source(); return v2` — node 2 → 1 → 0; the call `m2(a4)` binds
    `a4 → p3` into the callee and binds the CALLEE'S ZERO BACK (`zero.* → zero.*`), which
    `NoZeroBack` forbids;
  * method `2`: `sink(p3)` at its single node 0.
Both sinks are real and forward run 1 reports both (`reported`), so seeding them is the design.
Forward run 1 has the summary `zero → (2, ., $, 1)` of method 1, whose reversal is the backward
demand `((2,.,$,1), zero)` of method 1 (`dem_reversed`). The backward run on the reversed program:
  * the root's seed `(1,.,$,1)` enters method 1 through the reversed binding `1 → 2` and the
    emission gives the NON-ZERO premise `jb = (2,.,$,1)`;
  * the reversed source statement of `v2` turns it into the zero fact (a real reversed flow);
  * the reversed call into method 2 binds this zero fact into the callee's zero (the reversed
    binding back), and the callee's ZERO-PREMISE summary `zero → (3,.,$,1)` (the seed of the sink
    in method 2, a persisted exit edge of a backward run, `record_of_run`) applies; the reversed
    argument binding `3 → 4` takes it back to the caller.
The result is the COMPLETE backward summary `(2,.,$,1) → (4,.,$,1)` of method 1. It claims that `a4`
on the entry of method 1 flows to `v2` at its exit; no such flow exists (`flow1`). The zero fact
under a non-zero premise means "the requirement is met by a source"; the callee's zero-premise
summary means "a sink of the callee is reached"; their composition is not a flow. -/

namespace CexZeroBack

def st (b : Base) : PFact := ⟨b, [], .star Excl.empty, .star⟩
def zb : MicroEdge := (st 0, st 0)
def x2 : PFact := ⟨2, [], .exact, .conc 1⟩
def x5 : PFact := ⟨5, [], .exact, .conc 1⟩
def src2 : Stmt := ⟨[0], [(zeroFact, zeroFact), (zeroFact, x2)]⟩
def src5 : Stmt := ⟨[0], [(zeroFact, zeroFact), (zeroFact, x5)]⟩
/-- `r1 = m1()`: the zero enters the callee, the callee's `2` comes back to `1`. -/
def c0 : Call := ⟨1, [1], [zb], [(st 2, st 1)]⟩
/-- `m2(v5)`. -/
def c02 : Call := ⟨2, [5], [(st 5, st 3)], []⟩
/-- `m2(a4)`, and the callee's zero binds back (the binding that `NoZeroBack` forbids). -/
def c1 : Call := ⟨2, [4], [(st 4, st 3)], [zb]⟩
def P : Program :=
  { entry := fun m => match m with
      | 0 => 3
      | 1 => 2
      | _ => 0,
    exit := fun _ => 0,
    edges := [(0, 3, .stmt src5, 2), (0, 2, .call c02, 1), (0, 1, .call c0, 0),
              (1, 2, .call c1, 1), (1, 1, .stmt src2, 0)] }
def s1 : PFact := ⟨1, [], .exact, .conc 1⟩
def s3 : PFact := ⟨3, [], .exact, .conc 1⟩
def sinks : List (MethodId × Node × PFact) := [(0, 0, s1), (2, 0, s3)]
def cnt : Acc → Bool := fun _ => true
/-- Forward run 1. -/
abbrev R1 : Obj → Prop := D P cnt 2 policy1 sinks [0]
/-- The backward demand of method 1: the reversed forward summary `zero → (2,.,$,1)`. -/
def dem1 : DemandEdge := ⟨x2, some zeroFact⟩
def demR : MethodId → DemandEdge → Prop := fun m d => m = 1 ∧ d = dem1
/-- The persisted zero-premise backward record of method 2 (the seed of its sink). -/
def g3 : AFact := ⟨s3, false⟩
def recR : MethodId → PFact × AFact → Prop := fun m jg => m = 2 ∧ jg = (zeroFact, g3)
/-- The spurious backward summary of method 1. -/
def g4 : AFact := ⟨⟨4, [], .exact, .conc 1⟩, false⟩
def lA : Loc := ⟨2, [], 1⟩
def lB : Loc := ⟨4, [], 1⟩

theorem hE0 : (0, 3, Instr.stmt src5, 2) ∈ P.edges := List.Mem.head _
theorem hE1 : (0, 2, Instr.call c02, 1) ∈ P.edges := List.Mem.tail _ (List.Mem.head _)
theorem hE2 : (0, 1, Instr.call c0, 0) ∈ P.edges := List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
theorem hE3 : (1, 2, Instr.call c1, 1) ∈ P.edges :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
theorem hE4 : (1, 1, Instr.stmt src2, 0) ∈ P.edges :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem edge_inv {M n n' : Node} {ins : Instr} (h : (M, n, ins, n') ∈ P.edges) :
    (M = 0 ∧ n = 3 ∧ ins = .stmt src5 ∧ n' = 2) ∨ (M = 0 ∧ n = 2 ∧ ins = .call c02 ∧ n' = 1) ∨
    (M = 0 ∧ n = 1 ∧ ins = .call c0 ∧ n' = 0) ∨ (M = 1 ∧ n = 2 ∧ ins = .call c1 ∧ n' = 1) ∨
    (M = 1 ∧ n = 1 ∧ ins = .stmt src2 ∧ n' = 0) := by
  cases h with
  | head => exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
  | tail _ h => cases h with
    | head => exact Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)
    | tail _ h => cases h with
      | head => exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩))
      | tail _ h => cases h with
        | head => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)))
        | tail _ h => cases h with
          | head => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩)))
          | tail _ h => cases h

/-! #### The program satisfies every hypothesis of `Backward.B_general` but `NoZeroBack` -/

theorem wf : P.WF where
  stmtTouched := by
    intro M n s n' hE
    rcases edge_inv hE with ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ |
      ⟨-, -, h3, -⟩ <;> (cases h3 <;> decide)
  toStar := by
    intro M n c n' hE
    rcases edge_inv hE with ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ |
      ⟨-, -, h3, -⟩ <;> (cases h3 <;> decide)
  fromStar := by
    intro M n c n' hE
    rcases edge_inv hE with ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ |
      ⟨-, -, h3, -⟩ <;> (cases h3 <;> decide)
  filtPrefix := by
    intro M n b may n' hE
    rcases edge_inv hE with ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ |
      ⟨-, -, h3, -⟩ <;> cases h3

theorem markWF : Exact.MarkWF P where
  stmt := by
    intro M n s n' hE
    rcases edge_inv hE with ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ |
      ⟨-, -, h3, -⟩ <;> (cases h3 <;> decide)
  toC := by
    intro M n c n' hE
    rcases edge_inv hE with ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ |
      ⟨-, -, h3, -⟩ <;> (cases h3 <;> decide)
  fromC := by
    intro M n c n' hE
    rcases edge_inv hE with ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ |
      ⟨-, -, h3, -⟩ <;> (cases h3 <;> decide)

theorem filtUp : Exact.FiltUp P := by
  intro M n b may n' hE
  rcases edge_inv hE with ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ |
    ⟨-, -, h3, -⟩ <;> cases h3

theorem bindStar : BindTargetsStar P := by
  intro M n c n' hE
  rcases edge_inv hE with ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ |
    ⟨-, -, h3, -⟩ <;> (cases h3 <;> decide)

/-- The statement micro edges all read the zero fact with the exact tail. -/
theorem stmt_zero {M n n' : Node} {s : Stmt} (hE : (M, n, Instr.stmt s, n') ∈ P.edges) :
    ∀ e, e ∈ s.edges → e.1 = zeroFact := by
  rcases edge_inv hE with ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ |
    ⟨-, -, h3, -⟩ <;> (cases h3 <;> decide)

theorem markRev : StmtsMarkRev P :=
  fun _ _ _ _ hE e he => Or.inr ⟨0, by rw [stmt_zero hE e he]; rfl⟩

theorem revStmts : RevStmts P := by
  intro M n s n' hE e he
  refine ⟨?_, Or.inr ⟨0, by rw [stmt_zero hE e he]; rfl⟩⟩
  rw [stmt_zero hE e he]
  exact True.intro

/-- Every binding is `b.* → b'.*` with the empty exclusions and the mark `*`. -/
theorem bind_st {M n n' : Node} {c : Call} (hE : (M, n, Instr.call c, n') ∈ P.edges) :
    (∀ e, e ∈ c.toCallee → e.1.kind = .star Excl.empty ∧ e.2.kind = .star Excl.empty ∧
      e.2.mark = .star) ∧
    (∀ e, e ∈ c.fromCallee → e.1.kind = .star Excl.empty ∧ e.2.kind = .star Excl.empty ∧
      e.2.mark = .star) := by
  rcases edge_inv hE with ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ |
    ⟨-, -, h3, -⟩ <;> (cases h3 <;> decide)

theorem revCalls : RevCalls P := by
  intro M n c n' hE
  refine ⟨fun e he => ?_, fun e he => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := (bind_st hE).1 e he
    exact bindRev_of_star h1 h2 h3
  · obtain ⟨h1, h2, h3⟩ := (bind_st hE).2 e he
    exact bindRev_of_star h1 h2 h3

theorem zeroKept : ZeroKept P where
  stmt := by
    intro M n s n' hE _
    rcases edge_inv hE with ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ |
      ⟨-, -, h3, -⟩ <;> (cases h3 <;> decide)
  clean := by
    intro M n cl n' hE
    rcases edge_inv hE with ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ |
      ⟨-, -, h3, -⟩ <;> cases h3
  filt := by
    intro M n b may n' hE
    rcases edge_inv hE with ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ |
      ⟨-, -, h3, -⟩ <;> cases h3

/-- Every node of a method reaches the exit of its method (every edge goes down to node 0). -/
theorem exitReach : ExitReach P [0] := by
  intro M n _ hp
  show CfgPath P M n 0
  cases hp with
  | refl =>
    rcases M with _ | _ | M
    · exact CfgPath.step (CfgPath.step (CfgPath.step CfgPath.refl hE0) hE1) hE2
    · exact CfgPath.step (CfgPath.step CfgPath.refl hE3) hE4
    · exact CfgPath.refl
  | step _ he =>
    rcases edge_inv he with ⟨rfl, -, -, rfl⟩ | ⟨rfl, -, -, rfl⟩ | ⟨rfl, -, -, rfl⟩ |
      ⟨rfl, -, -, rfl⟩ | ⟨rfl, -, -, rfl⟩
    · exact CfgPath.step (CfgPath.step CfgPath.refl hE1) hE2
    · exact CfgPath.step CfgPath.refl hE2
    · exact CfgPath.refl
    · exact CfgPath.step CfgPath.refl hE4
    · exact CfgPath.refl

#print axioms exitReach

theorem sinkKinds : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any := by
  intro M n s h
  cases h with
  | head => exact Or.inl rfl
  | tail _ h => cases h with
    | head => exact Or.inl rfl
    | tail _ h => cases h

/-- The call `m2(a4)` binds the callee's zero back. -/
theorem not_noZeroBack : ¬ NoZeroBack P :=
  fun h => h 1 2 c1 1 hE3 zb (List.Mem.head _) rfl

theorem seedsConc : SeedsConc sinks := by
  intro M n s h
  cases h with
  | head => exact ⟨1, rfl⟩
  | tail _ h => cases h with
    | head => exact ⟨1, rfl⟩
    | tail _ h => cases h

/-! #### Forward run 1: the demand is a reversed summary, the seeds are the reported sinks -/

theorem den_st {a b : Base} {l : Loc} (hl : l.base = a) (hp : l.path = []) :
    den (st a) (st b) l ⟨b, [], l.mark⟩ :=
  ⟨hl, rfl, trivial, rfl, trivial, [], [], by rw [hp]; rfl, rfl, rfl, rfl, rfl⟩

theorem den_src {x : PFact} (hx : x = ⟨x.base, [], .exact, .conc 1⟩) :
    den zeroFact x zeroLoc ⟨x.base, [], 1⟩ := by
  rw [hx]
  exact ⟨rfl, rfl, rfl, rfl, trivial, [], [], rfl, rfl, rfl, rfl⟩

theorem flow_m1 : Flow P 1 zeroLoc 0 lA := by
  have h0 : Flow P 1 zeroLoc 2 zeroLoc := Flow.start 1 zeroLoc
  have h1 : Flow P 1 zeroLoc 1 zeroLoc := Flow.pass h0 hE3 (by decide)
  exact Flow.step h1 hE4 (Or.inr ⟨(zeroFact, x2), by decide, den_src rfl⟩)

theorem reach_s1 : Reach P [0] 0 0 ⟨1, [], 1⟩ := by
  have h0 : Flow P 0 zeroLoc 3 zeroLoc := Flow.start 0 zeroLoc
  have h1 : Flow P 0 zeroLoc 2 zeroLoc :=
    Flow.step h0 hE0 (Or.inr ⟨(zeroFact, zeroFact), by decide, Backward.den_zero⟩)
  have h2 : Flow P 0 zeroLoc 1 zeroLoc := Flow.pass h1 hE1 (by decide)
  exact Reach.root (List.Mem.head _) (Flow.call (e1 := zb) (e2 := (st 2, st 1)) h2 hE2
    (by decide) (den_st rfl rfl) flow_m1 (by decide) (den_st rfl rfl))

theorem reach_s3 : Reach P [0] 2 0 ⟨3, [], 1⟩ := by
  have h0 : Flow P 0 zeroLoc 3 zeroLoc := Flow.start 0 zeroLoc
  have h1 : Flow P 0 zeroLoc 2 ⟨5, [], 1⟩ :=
    Flow.step h0 hE0 (Or.inr ⟨(zeroFact, x5), by decide, den_src rfl⟩)
  exact Reach.down (e := (st 5, st 3)) (Reach.root (List.Mem.head _) h1) hE1 (by decide)
    (den_st rfl rfl) (Flow.start 2 _)

/-- Forward run 1 reports both sinks: the seeds of the backward run are the reported sinks. -/
theorem reported : ∀ M n s, (M, n, s) ∈ sinks → ∃ b, R1 (.vuln M n s b) := by
  intro M n s h
  cases h with
  | head =>
    exact Coverage.vuln_found_policy P cnt 2 sinks [0] wf (fun _ => []) reach_s1
      (List.Mem.head _) rfl ⟨rfl, ⟨[], rfl, rfl⟩, rfl⟩
  | tail _ h => cases h with
    | head =>
      exact Coverage.vuln_found_policy P cnt 2 sinks [0] wf (fun _ => []) reach_s3
        (List.Mem.tail _ (List.Mem.head _)) rfl ⟨rfl, ⟨[], rfl, rfl⟩, rfl⟩
    | tail _ h => cases h

theorem policy1_zero : policy1 1 zeroFact = zeroFact := by decide

/-- The backward demand of method 1 is the reversed summary `zero → (2,.,$,1)` of forward run 1
    (the hand-off `revSummaryDemand` of the design). -/
theorem dem_reversed : ∀ m d, demR m d → revSummaryDemand P R1 m d := by
  intro m d ⟨hm, hd⟩
  subst hm hd
  have f0 : R1 (.init 0 zeroFact) := D.root (List.Mem.head _)
  have f1 : R1 (.edge 0 zeroFact 3 zeroAF) := D.start f0
  have f2 : R1 (.edge 0 zeroFact 2 zeroAF) := D.step f1 hE0 (by decide)
  have f3 : R1 (.edge 0 zeroFact 1 zeroAF) := D.pass f2 hE1 (by decide)
  have f4 : R1 (.added 1 zeroFact) := D.added (c := c0) (e := zb) (a := zeroAF) f3 hE2 (by decide)
    (by decide)
  have f5 : R1 (.init 1 zeroFact) := by
    have h := D.initA (α := policy1) f4
    rw [policy1_zero] at h
    exact h
  have f6 : R1 (.edge 1 zeroFact 2 zeroAF) := D.start f5
  have f7 : R1 (.edge 1 zeroFact 1 zeroAF) := D.pass f6 hE3 (by decide)
  have f8 : R1 (.edge 1 zeroFact 0 ⟨x2, false⟩) := D.step f7 hE4 (by decide)
  exact ⟨zeroFact, x2, ⟨f5, Or.inr ⟨⟨x2, false⟩, f8, rfl⟩⟩, rfl⟩

/-! #### The backward runs -/

abbrev BRun (demand : MethodId → DemandEdge → Prop) (recs : MethodId → PFact × AFact → Prop) :
    Obj → Prop :=
  DB (Program.rev P) cnt 2 demand emitM satI restrictU recs [] [0] sinks true

theorem hb_c0 : (0, 0, Instr.call (Call.rev c0), 1) ∈ (Program.rev P).edges := mem_rev_call hE2
theorem hb_c1 : (1, 1, Instr.call (Call.rev c1), 2) ∈ (Program.rev P).edges := mem_rev_call hE3
theorem hb_src2 : (1, 0, Instr.stmt (Stmt.rev src2), 1) ∈ (Program.rev P).edges := mem_rev_stmt hE4

/-- Every backward run (any demand, any records) has the zero-premise summary `zero → (3,.,$,1)`
    of method 2 at its backward exit: the zero enters method 1 and method 2 (`zin`), the seed of the
    sink of method 2 gives the requirement (`seed`). -/
theorem zero_summary_m2 (demand : MethodId → DemandEdge → Prop)
    (recs : MethodId → PFact × AFact → Prop) :
    BRun demand recs (.init 2 zeroFact) ∧
    BRun demand recs (.edge 2 zeroFact ((Program.rev P).exit 2) g3) := by
  have r0 : BRun demand recs (.init 0 zeroFact) := DB.root (List.Mem.head _)
  have r1 : BRun demand recs (.edge 0 zeroFact 0 zeroAF) := DB.start r0
  have r2 : BRun demand recs (.init 1 zeroFact) := DB.zin (c := Call.rev c0) rfl r1 hb_c0
  have r3 : BRun demand recs (.edge 1 zeroFact 0 zeroAF) := DB.start r2
  have r4 : BRun demand recs (.edge 1 zeroFact 1 zeroAF) := DB.step r3 hb_src2 (by decide)
  have r5 : BRun demand recs (.init 2 zeroFact) := DB.zin (c := Call.rev c1) rfl r4 hb_c1
  have r6 : BRun demand recs (.edge 2 zeroFact 0 zeroAF) := DB.start r5
  exact ⟨r5, DB.seed (List.Mem.tail _ (List.Mem.head _)) r6⟩

/-- The persisted record is an exit edge of a backward run (no record, the demand `demR`). -/
theorem record_of_run :
    ∀ m jg, recR m jg → RExact.exitRecs (Program.rev P) (BRun demR (fun _ _ => False)) m jg := by
  intro m jg ⟨hm, hjg⟩
  subst hm hjg
  exact (zero_summary_m2 demR (fun _ _ => False)).2

/-- The record is exact off the zero base (its premise is the zero fact). -/
theorem recR_NZ : RecsExactNZ (Program.rev P) recR := by
  intro m j g ⟨_, hjg⟩ hjb
  simp only [Prod.mk.injEq] at hjg
  obtain ⟨rfl, -⟩ := hjg
  exact absurd rfl hjb

/-- The common prefix: the non-zero premise `(2,.,$,1)` of method 1 and its zero fact. -/
theorem prefix_m1 (demand : MethodId → DemandEdge → Prop) (recs : MethodId → PFact × AFact → Prop)
    (hd : demand 1 dem1) : BRun demand recs (.edge 1 x2 1 zeroAF) := by
  have b0 : BRun demand recs (.init 0 zeroFact) := DB.root (List.Mem.head _)
  have b1 : BRun demand recs (.edge 0 zeroFact 0 zeroAF) := DB.start b0
  have b2 : BRun demand recs (.edge 0 zeroFact 0 ⟨s1, false⟩) := DB.seed (List.Mem.head _) b1
  have b3 : BRun demand recs (.added 1 x2) :=
    DB.added (c := Call.rev c0) (e := revEdge (st 2) (st 1)) (a := ⟨x2, false⟩) b2 hb_c0
      (by decide) (by decide)
  have b4 : BRun demand recs (.init 1 x2) := DB.initR (d := dem1) b3 hd (by decide)
  have b5 : BRun demand recs (.edge 1 x2 0 ⟨x2, false⟩) := DB.start b4
  exact DB.step b5 hb_src2 (by decide)

/-- The callee flow of method 2 stays at its entry location. -/
theorem flow2 : ∀ {M l0 n l}, Flow P M l0 n l → M = 2 → n = 0 ∧ l = l0 := by
  intro M l0 n l h
  induction h with
  | start M l0 => intro hM; subst hM; exact ⟨rfl, rfl⟩
  | step _ hE _ _ =>
    intro hM
    rcases edge_inv hE with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;>
      exact absurd (h1.symm.trans hM) (by decide)
  | pass _ hE _ _ =>
    intro hM
    rcases edge_inv hE with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;>
      exact absurd (h1.symm.trans hM) (by decide)
  | call _ hE _ _ _ _ _ _ _ =>
    intro hM
    rcases edge_inv hE with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;>
      exact absurd (h1.symm.trans hM) (by decide)
  | clean _ hE _ _ =>
    intro hM
    rcases edge_inv hE with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;>
      exact absurd (h1.symm.trans hM) (by decide)
  | filt _ hE _ _ =>
    intro hM
    rcases edge_inv hE with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;>
      exact absurd (h1.symm.trans hM) (by decide)

/-- In method 1, `a4` on the entry flows nowhere: the call passes it into method 2 as `p3`, and
    only the callee's zero comes back. -/
theorem flow1 : ∀ {M l0 n l}, Flow P M l0 n l → M = 1 → l0 = lB → n = 2 ∧ l = l0 := by
  intro M l0 n l h
  induction h with
  | start M l0 => intro hM _; subst hM; exact ⟨rfl, rfl⟩
  | @step M l0 n l n' l' s _ hE _ ih =>
    intro hM hl
    obtain ⟨hn, _⟩ := ih hM hl
    rcases edge_inv hE with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, -, h3, -⟩ | ⟨-, h2, -, -⟩
    · exact absurd (h1.symm.trans hM) (by decide)
    · exact absurd (h1.symm.trans hM) (by decide)
    · exact absurd (h1.symm.trans hM) (by decide)
    · cases h3
    · exact absurd (h2.symm.trans hn) (by decide)
  | @pass M l0 n l n' c _ hE hb ih =>
    intro hM hl
    obtain ⟨_, hll⟩ := ih hM hl
    rcases edge_inv hE with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩
    · exact absurd (h1.symm.trans hM) (by decide)
    · exact absurd (h1.symm.trans hM) (by decide)
    · exact absurd (h1.symm.trans hM) (by decide)
    · injection h3 with h3
      subst h3
      rw [hll, hl] at hb
      exact absurd hb (by decide)
    · cases h3
  | @call M l0 n l n' c e1 e2 l1 l2 l3 _ hE he1 hd1 hfc he2 hd2 _ _ =>
    intro hM _
    rcases edge_inv hE with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩
    · exact absurd (h1.symm.trans hM) (by decide)
    · exact absurd (h1.symm.trans hM) (by decide)
    · exact absurd (h1.symm.trans hM) (by decide)
    · injection h3 with h3
      subst h3
      have he1' : e1 = (st 4, st 3) := List.mem_singleton.mp he1
      have he2' : e2 = zb := List.mem_singleton.mp he2
      subst he1' he2'
      have hb1 : l1.base = 3 := hd1.2.1
      have hb2 : l2.base = 0 := hd2.1
      have hl21 : l2 = l1 := (flow2 hfc rfl).2
      rw [hl21, hb1] at hb2
      exact absurd hb2 (by decide)
    · cases h3
  | clean _ hE _ _ =>
    rcases edge_inv hE with ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ |
      ⟨-, -, h3, -⟩ <;> cases h3
  | filt _ hE _ _ =>
    rcases edge_inv hE with ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ |
      ⟨-, -, h3, -⟩ <;> cases h3

theorem no_fwd_flow : ¬ Flow P 1 lB (P.exit 1) lA := fun h => absurd (flow1 h rfl rfl).1 (by decide)

theorem no_rev_flow : ¬ Flow (Program.rev P) 1 lA ((Program.rev P).exit 1) lB :=
  fun h => no_fwd_flow ((flow_rev_iff_calls revStmts revCalls).mpr h)

theorem den_spurious : den x2 g4.fact lA lB := ⟨rfl, rfl, rfl, rfl, trivial, [], [], rfl, rfl, rfl, rfl⟩

theorem x2_ne : x2 ≠ zeroFact := by decide

/-- THE COUNTEREXAMPLE, ROUTE `retRec` (the natural one). Every hypothesis of `revRecs_exactM`,
    `summary_rev_flow` and `Backward.B_general` but `NoZeroBack` holds: the program is
    well-formed, mark-agnostic in its bindings, mark-reversible, keeps the zero, every node reaches
    its exit, the sinks have the tail `$`, `MarkWF`, `FiltUp`, `RevStmts`, `RevCalls`; the backward
    demand is a reversed summary of forward run 1; the seeds are the sinks forward run 1 reports;
    the one persisted record is an exit edge of a backward run and is exact off the zero base. The
    backward run derives the COMPLETE summary `(2,.,$,1) → (4,.,$,1)` of method 1 with a non-zero
    premise; its pair `(lA, lB)` is not a reversed flow, its reversal is not a forward flow, and
    the reversed backward summaries are NOT exact forward records. -/
theorem cex_rec :
    P.WF ∧ BindTargetsStar P ∧ StmtsMarkRev P ∧ ZeroKept P ∧ ExitReach P [0] ∧
    (∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any) ∧
    Exact.MarkWF P ∧ Exact.FiltUp P ∧ RevStmts P ∧ RevCalls P ∧ ¬ NoZeroBack P ∧ SeedsConc sinks ∧
    (∀ m d, demR m d → revSummaryDemand P R1 m d) ∧
    (∀ M n s, (M, n, s) ∈ sinks → ∃ b, R1 (.vuln M n s b)) ∧
    (∀ m jg, recR m jg → RExact.exitRecs (Program.rev P) (BRun demR (fun _ _ => False)) m jg) ∧
    RecsExactNZ (Program.rev P) recR ∧
    BRun demR recR (.edge 1 x2 ((Program.rev P).exit 1) g4) ∧ x2 ≠ zeroFact ∧
    g4.complete = true ∧ den x2 g4.fact lA lB ∧
    ¬ Flow (Program.rev P) 1 lA ((Program.rev P).exit 1) lB ∧ ¬ Flow P 1 lB (P.exit 1) lA ∧
    ¬ RExact.RecsExact P (revRecs P (BRun demR recR)) := by
  have hpre := prefix_m1 demR recR ⟨rfl, rfl⟩
  have hedge : BRun demR recR (.edge 1 x2 ((Program.rev P).exit 1) g4) :=
    DB.retRec (c := Call.rev c1) (e1 := revEdge zb.1 zb.2) (a := zeroAF) (j := zeroFact) (g := g3)
      (r := g3) (e2 := revEdge (st 4) (st 3)) (r' := g4) hpre hb_c1 (by decide) (by decide)
      ⟨rfl, rfl⟩ (Or.inl (by decide)) (by decide) (by decide) (by decide)
  refine ⟨wf, bindStar, markRev, zeroKept, exitReach, sinkKinds, markWF, filtUp, revStmts,
    revCalls, not_noZeroBack,
    seedsConc, dem_reversed, reported, record_of_run, recR_NZ, hedge, x2_ne, rfl, den_spurious,
    no_rev_flow, no_fwd_flow, fun h => ?_⟩
  have hd : den (revEdge x2 g4.fact).1 (revEdge x2 g4.fact).2 lB lA :=
    revEdge_sound (Or.inr ⟨1, rfl⟩) den_spurious
  exact no_fwd_flow (h 1 _ _ ⟨x2, g4, hedge, x2_ne, rfl, rfl⟩ rfl lB lA hd)

#print axioms cex_rec

/-- The demand of route `ret`: `demR` and one more demand edge of method 2 that lets the
    zero-premise summary through the restriction. -/
def dem2 : DemandEdge := ⟨zeroFact, some ⟨3, [], .exact, .star⟩⟩
def demT : MethodId → DemandEdge → Prop := fun m d => (m = 1 ∧ d = dem1) ∨ (m = 2 ∧ d = dem2)

/-- THE COUNTEREXAMPLE, ROUTE `ret`, against the direct analogue of `RExact.edge_exactR` (whose
    record hypothesis is the full `RecsExact`): no record at all (`recs_empty`), every hypothesis
    of `edge_exactR` on the reversed program holds (`MarkWF`, `FiltUp`, `SatMark satI`,
    `RestrictSub restrictU`, `RecsExact`), only `NoZeroIn` fails; the run applies the callee's
    zero-premise summary through `ret` and derives the same non-real normal edge. -/
theorem cex_ret :
    Exact.MarkWF (Program.rev P) ∧ Exact.FiltUp (Program.rev P) ∧ RExact.SatMark satI ∧
    RestrictSub restrictU ∧ RExact.RecsExact (Program.rev P) (fun _ _ => False) ∧
    ¬ NoZeroIn (Program.rev P) ∧
    BRun demT (fun _ _ => False) (.edge 1 x2 ((Program.rev P).exit 1) g4) ∧ x2 ≠ zeroFact ∧
    g4.demand = false ∧ den x2 g4.fact lA lB ∧
    ¬ Flow (Program.rev P) 1 lA ((Program.rev P).exit 1) lB := by
  have hpre := prefix_m1 demT (fun _ _ => False) (Or.inl ⟨rfl, rfl⟩)
  obtain ⟨hj, hg⟩ := zero_summary_m2 demT (fun _ _ => False)
  have hedge : BRun demT (fun _ _ => False) (.edge 1 x2 ((Program.rev P).exit 1) g4) :=
    DB.ret (c := Call.rev c1) (e1 := revEdge zb.1 zb.2) (a := zeroAF) (j := zeroFact) (g := g3)
      (d := dem2) (g' := g3) (r := g3) (e2 := revEdge (st 4) (st 3)) (r' := g4) hpre hb_c1
      (by decide) (by decide) hj hg (Or.inr ⟨rfl, rfl⟩) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  refine ⟨markWF_rev markWF, filtUp_rev filtUp, RExact.satI_mark, RExact.restrictU_sub,
    RExact.recs_empty _, fun h => ?_, hedge, x2_ne, rfl, den_spurious, no_rev_flow⟩
  exact h 1 1 (Call.rev c1) 2 hb_c1 (revEdge zb.1 zb.2) (List.Mem.head _) rfl

#print axioms cex_ret

end CexZeroBack

/-! ## Part 3. Record exactness over the run sequence

The restricted-run theorems take `RExact.RecsExact P recs` as a hypothesis. The records that run
`k + 1` of `RCov.runSeq` reuses (`recs k`) are exit edges of the runs before it: run 1 (`D`, index
0) and the restricted runs `1 .. k`. The modelled accumulation (`RecsFromRuns`): every record of
`recs k` is an exit edge of a run with index `≤ k` (any subset: all exit edges, the complete ones,
the union over the runs). Then every `recs k` is exact, by induction over the runs: the exit edges
of run 0 are exact (`recs_of_D`), and the exit edges of run `j + 1` are exact because its records
`recs j` are (`recs_of_DR`). -/

/-- The records of run `k + 1` (`recs k`) are exit edges of the runs `0 .. k` of the sequence
    `R`. -/
def RecsFromRuns (P : Program) (R : Nat → Obj → Prop) (recs : Nat → MethodId → PFact × AFact → Prop) :
    Prop :=
  ∀ k m jg, recs k m jg → ∃ k', k' ≤ k ∧ RExact.exitRecs P (R k') m jg

section Part3
variable {P : Program} {counted : Acc → Bool} {Ls : Nat → Nat}
  {dem : Nat → MethodId → DemandEdge → Prop}
  {emit : PFact → PFact → Option PFact}
  {sat : PFact → PFact → Bool}
  {restrict : PFact → AFact → DemandEdge → Option AFact}
  {recs : Nat → MethodId → PFact × AFact → Prop}
  {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId}

/-- 3. RECORD EXACTNESS OVER THE RUN SEQUENCE. If the records of every run are exit edges of
    earlier runs (or of run 1), every record set of the sequence is exact. Hypotheses: those of
    `RExact.recs_of_DR` except the record hypothesis (`MarkWF P`, `FiltUp P`, `SatMark sat`,
    `RestrictSub restrict`). -/
theorem recsSeq_exact (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hsat : RExact.SatMark sat)
    (hsub : RestrictSub restrict)
    (hfrom : RecsFromRuns P (RCov.runSeq P counted Ls dem emit sat restrict recs sinks roots) recs) :
    ∀ k, RExact.RecsExact P (recs k) := by
  have key : ∀ k j, j ≤ k → RExact.RecsExact P (recs j) := by
    intro k
    induction k with
    | zero =>
      intro j hj m jj g hr hg l1 l2 hd
      obtain ⟨k', hk', hx⟩ := hfrom j m (jj, g) hr
      cases k' with
      | zero => exact RExact.recs_of_D hmw hup m jj g hx hg l1 l2 hd
      | succ i => exact absurd (Nat.le_trans hk' hj) (by omega)
    | succ k ih =>
      intro j hj m jj g hr hg l1 l2 hd
      obtain ⟨k', hk', hx⟩ := hfrom j m (jj, g) hr
      cases k' with
      | zero => exact RExact.recs_of_D hmw hup m jj g hx hg l1 l2 hd
      | succ i =>
        exact RExact.recs_of_DR hmw hup hsat hsub (ih i (by omega)) m jj g hx hg l1 l2 hd
  exact fun k => key k k (Nat.le_refl k)

#print axioms recsSeq_exact

/-- 3v. The valid form (`RecsExactV`; prefix-closed type filters). -/
theorem recsSeq_exactV {ok : Loc → Prop} (hmw : Exact.MarkWF P) (hv : Exact.FiltValid P ok)
    (hbo : Exact.BackOK P ok) (hsat : RExact.SatMark sat) (hsub : RestrictSub restrict)
    (hfrom : RecsFromRuns P (RCov.runSeq P counted Ls dem emit sat restrict recs sinks roots) recs) :
    ∀ k, RExact.RecsExactV P ok (recs k) := by
  have key : ∀ k j, j ≤ k → RExact.RecsExactV P ok (recs j) := by
    intro k
    induction k with
    | zero =>
      intro j hj m jj g hr
      obtain ⟨k', hk', hx⟩ := hfrom j m (jj, g) hr
      cases k' with
      | zero => exact RExact.recs_of_D_valid hmw hv hbo m jj g hx
      | succ i => exact absurd (Nat.le_trans hk' hj) (by omega)
    | succ k ih =>
      intro j hj m jj g hr
      obtain ⟨k', hk', hx⟩ := hfrom j m (jj, g) hr
      cases k' with
      | zero => exact RExact.recs_of_D_valid hmw hv hbo m jj g hx
      | succ i =>
        exact RExact.recs_of_DR_valid hmw hv hbo hsat hsub (ih i (by omega)) m jj g hx
  exact fun k => key k k (Nat.le_refl k)

#print axioms recsSeq_exactV

/-- 3'. Every normal-layer edge of every run of the sequence is exact: no record hypothesis. -/
theorem seq_edge_exact (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hsat : RExact.SatMark sat)
    (hsub : RestrictSub restrict)
    (hfrom : RecsFromRuns P (RCov.runSeq P counted Ls dem emit sat restrict recs sinks roots) recs)
    (k : Nat) {M : MethodId} {i : PFact} {n : Node} {f : AFact} {l0 l : Loc}
    (h : RCov.runSeq P counted Ls dem emit sat restrict recs sinks roots k (.edge M i n f))
    (ha : f.demand = false) (hd : den i f.fact l0 l) : Flow P M l0 n l := by
  cases k with
  | zero => exact Exact.edge_exact hmw hup h ha hd
  | succ k =>
    exact RExact.edge_exactR hmw hup hsat hsub (recsSeq_exact hmw hup hsat hsub hfrom k) h ha hd

#print axioms seq_edge_exact

end Part3

/-- 3''. Every confirmed vulnerability of every restricted run of the sequence (spec rules
    `emitM`, `satI`, `restrictU`) is a real vulnerability: no record hypothesis. -/
theorem seq_confirmed_real {P : Program} {counted : Acc → Bool} {Ls : Nat → Nat}
    {dem : Nat → MethodId → DemandEdge → Prop} {recs : Nat → MethodId → PFact × AFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P)
    (hfrom : RecsFromRuns P (RCov.runSeq P counted Ls dem emitM satI restrictU recs sinks roots) recs)
    (k : Nat) {M : MethodId} {n : Node} {s : PFact}
    (h : RExact.ConfirmedM P counted (Ls (k + 1)) (dem k) emitM satI restrictU (recs k) sinks roots
      M n s) :
    ∃ l, Reach P roots M n l ∧ s.covers l :=
  RExact.confirmed_realM_gen hmw hup RExact.satI_mark RExact.restrictU_sub
    (recsSeq_exact hmw hup RExact.satI_mark RExact.restrictU_sub hfrom k) h

#print axioms seq_confirmed_real

/-- THE ACCUMULATION: the records after run `k` are the exit edges of runs `0 .. k` that the
    policy `keep` persists (`keep := fun _ jg => jg.2.complete = true` for the complete exit
    edges, `fun _ _ => True` for all). Run `k + 1` of the sequence uses `accRecs … k`. -/
def accRecs (P : Program) (counted : Acc → Bool) (Ls : Nat → Nat)
    (dem : Nat → MethodId → DemandEdge → Prop) (emit : PFact → PFact → Option PFact)
    (sat : PFact → PFact → Bool) (restrict : PFact → AFact → DemandEdge → Option AFact)
    (sinks : List (MethodId × Node × PFact)) (roots : List MethodId)
    (keep : MethodId → PFact × AFact → Prop) : Nat → MethodId → PFact × AFact → Prop
  | 0 => fun m jg => RExact.exitRecs P (D P counted (Ls 0) policy1 sinks roots) m jg ∧ keep m jg
  | k + 1 => fun m jg =>
      accRecs P counted Ls dem emit sat restrict sinks roots keep k m jg ∨
      (RExact.exitRecs P (DR P counted (Ls (k + 1)) (dem k) emit sat restrict
        (accRecs P counted Ls dem emit sat restrict sinks roots keep k) sinks roots) m jg ∧ keep m jg)

/-- The accumulated records come from the runs of the sequence that uses them. -/
theorem accRecs_from {P : Program} {counted : Acc → Bool} {Ls : Nat → Nat}
    {dem : Nat → MethodId → DemandEdge → Prop} {emit : PFact → PFact → Option PFact}
    {sat : PFact → PFact → Bool} {restrict : PFact → AFact → DemandEdge → Option AFact}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    {keep : MethodId → PFact × AFact → Prop} :
    RecsFromRuns P (RCov.runSeq P counted Ls dem emit sat restrict
      (accRecs P counted Ls dem emit sat restrict sinks roots keep) sinks roots)
      (accRecs P counted Ls dem emit sat restrict sinks roots keep) := by
  intro k
  induction k with
  | zero => intro m jg h; exact ⟨0, Nat.le_refl 0, h.1⟩
  | succ k ih =>
    intro m jg h
    rcases h with h | h
    · obtain ⟨k', hk', hx⟩ := ih m jg h
      exact ⟨k', Nat.le_succ_of_le hk', hx⟩
    · exact ⟨k + 1, Nat.le_refl _, h.1⟩

#print axioms accRecs_from

/-- 3a. THE ACCUMULATED RECORDS ARE EXACT, for every persistence policy `keep`. -/
theorem accRecs_exact {P : Program} {counted : Acc → Bool} {Ls : Nat → Nat}
    {dem : Nat → MethodId → DemandEdge → Prop} {emit : PFact → PFact → Option PFact}
    {sat : PFact → PFact → Bool} {restrict : PFact → AFact → DemandEdge → Option AFact}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    {keep : MethodId → PFact × AFact → Prop}
    (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hsat : RExact.SatMark sat)
    (hsub : RestrictSub restrict) :
    ∀ k, RExact.RecsExact P (accRecs P counted Ls dem emit sat restrict sinks roots keep k) :=
  recsSeq_exact hmw hup hsat hsub accRecs_from

#print axioms accRecs_exact

/-- 3av. The valid form. -/
theorem accRecs_exactV {P : Program} {counted : Acc → Bool} {Ls : Nat → Nat}
    {dem : Nat → MethodId → DemandEdge → Prop} {emit : PFact → PFact → Option PFact}
    {sat : PFact → PFact → Bool} {restrict : PFact → AFact → DemandEdge → Option AFact}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    {keep : MethodId → PFact × AFact → Prop} {ok : Loc → Prop}
    (hmw : Exact.MarkWF P) (hv : Exact.FiltValid P ok) (hbo : Exact.BackOK P ok)
    (hsat : RExact.SatMark sat) (hsub : RestrictSub restrict) :
    ∀ k, RExact.RecsExactV P ok (accRecs P counted Ls dem emit sat restrict sinks roots keep k) :=
  recsSeq_exactV hmw hv hbo hsat hsub accRecs_from

#print axioms accRecs_exactV

/-- The spec rules: the accumulated records of the sequence with `emitM`, `satI`, `restrictU`
    are exact. -/
theorem accRecs_exactM {P : Program} {counted : Acc → Bool} {Ls : Nat → Nat}
    {dem : Nat → MethodId → DemandEdge → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    {keep : MethodId → PFact × AFact → Prop}
    (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) :
    ∀ k, RExact.RecsExact P (accRecs P counted Ls dem emitM satI restrictU sinks roots keep k) :=
  accRecs_exact hmw hup RExact.satI_mark RExact.restrictU_sub

#print axioms accRecs_exactM

/-! ### The backward records over the backward runs

The same induction for the records that the backward runs persist and reuse: if the records of
backward run `k` are exit edges of backward runs `j < k`, they are exact off the zero base (under
`NoZeroIn`), so every backward run satisfies the record hypothesis of `edge_exactB`. -/

theorem recsBSeq_exact {Pb : Program} {counted : Acc → Bool} {LB : Nat → Nat}
    {demB : Nat → MethodId → DemandEdge → Prop} {emit : PFact → PFact → Option PFact}
    {sat : PFact → PFact → Bool} {restrict : PFact → AFact → DemandEdge → Option AFact}
    {recsB : Nat → MethodId → PFact × AFact → Prop} {sinksB : List (MethodId × Node × PFact)}
    {rootsB : List MethodId} {seeds : Nat → List (MethodId × Node × PFact)} {zbind : Bool}
    (hmw : Exact.MarkWF Pb) (hup : Exact.FiltUp Pb) (hsat : RExact.SatMark sat)
    (hsub : RestrictSub restrict) (hnz : NoZeroIn Pb)
    (hfrom : ∀ k m jg, recsB k m jg → ∃ j, j < k ∧ RExact.exitRecs Pb
      (DB Pb counted (LB j) (demB j) emit sat restrict (recsB j) sinksB rootsB (seeds j) zbind) m jg) :
    ∀ k, RecsExactNZ Pb (recsB k) := by
  have key : ∀ k j, j < k → RecsExactNZ Pb (recsB j) := by
    intro k
    induction k with
    | zero => intro j hj; exact absurd hj (Nat.not_lt_zero j)
    | succ k ih =>
      intro j hj m jj g hr hjb hg l1 l2 hd
      obtain ⟨i, hi, hx⟩ := hfrom j m (jj, g) hr
      exact edge_exactB hmw hup hsat hsub hnz (ih i (by omega)) hx (ne_zero_of_base hjb) hg hd
  exact fun k => key (k + 1) k (Nat.lt_succ_self k)

#print axioms recsBSeq_exact

/-! ## Part 4. The static invariant of the backward run

`StaticsIter.rinv_all` proves the static invariant (`RInv`: no static fact with a `*` or `[any]`
tail strictly above a static position; W2 on edges) for every restricted forward run. The backward
run `DB` has the same rules and four zero rules. The zero fact is exact (`zpass`, `zin`); a seed
keeps the invariant if the sink pattern does (`SeedsOK`); the balanced return applies a callee
summary (which keeps the invariant by induction, so it is a good record, `recOK_of`) to the exact
concrete zero fact and binds back by `S.* → S.*` only (`zret`, as `ret`). The program of the
context `X` is the program the run runs on: for a backward run, `Program.rev P` with the backward
field limit, whose construction rules `SWFR` are a hypothesis (the positions of the reversed
program are the forward write targets and the sinks, so `SWFR` of the reversed program is not a
consequence of `Statics.SWF` of the forward one). -/

section Part4
open ApSpec.Statics ApSpec.StaticsIter

/-- The seeds keep the static invariant: a sink pattern has the tail `$` or `[any]`, and none
    with the tail `[any]` lies strictly above a static position. -/
def SeedsOK (X : SCtx) (seeds : List (MethodId × Node × PFact)) : Prop :=
  ∀ M n s, (M, n, s) ∈ seeds → (s.kind = .exact ∨ s.kind = .any) ∧ ¬ AboveNE X s

/-- 4. THE STATIC INVARIANT OF A BACKWARD RUN (the analogue of `StaticsIter.rinv_all`). In `DB` with
    the spec rules (`emitM`, `satI`, `restrictU`), under the construction rules `SWFR X` of the
    program it runs on, for EVERY demand, every record set that keeps the run-1 invariant
    (`RecOK`), concrete seeds that keep the invariant, any sinks, roots and `zbind`: no static fact
    with a `*` or `[any]` tail lies strictly above a static position (initial facts, edges, added
    facts), and every edge fact is W2. -/
theorem binv_all {X : SCtx} (hs : SWFR X) {demand : MethodId → DemandEdge → Prop}
    {recs : MethodId → PFact × AFact → Prop} (hrecs : ∀ m j g, recs m (j, g) → RecOK X j g)
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    {seeds : List (MethodId × Node × PFact)} {zbind : Bool}
    (hsd : SeedsConc seeds) (hso : SeedsOK X seeds) {o : Obj}
    (h : DB X.P X.counted X.FL demand emitM satI restrictU recs sinks roots seeds zbind o) :
    RInv X o := by
  induction h with
  | root _ => exact fun hab => hab.2.2 rfl
  | start _ ih => exact ⟨startFact_w2 _, fun hab => ih (aboveNE_start hab)⟩
  | step _ hE hf ih => exact rinv_step hs hE ih.1 ih.2 hf
  | reqStmt => trivial
  | pass _ _ _ ih => exact ih
  | @added M i n f n' c e a _ hE he ha ih => exact rinv_bind (hs.toC _ _ _ _ hE e he) ih.2 ha
  | initR _ _ hemit ih => exact rinv_emit ih hemit
  | @ret M i n f n' c e1 a j g d g' r e2 r' hf hE he1 ha _ _ _ hres _ hr he2 hr' ihf _ ihg =>
    obtain ⟨-, t, ht⟩ := DB_concrete RExact.emitM_copies hsd hf
    obtain ⟨ta, hta⟩ := applyEdge_mark_conc ht ha
    have han := rinv_bind (hs.toC _ _ _ _ hE e1 he1) ihf.2 ha
    obtain ⟨hgw', hgn'⟩ := rinv_restrict ihg.1 ihg.2 hres
    have hrn := rinv_summary (recOK_of hgw' hgn') han (applyEdge_w2 ha) hta hr
    have hr'n := rinv_bind (hs.fromC _ _ _ _ hE e2 he2) hrn hr'
    refine ⟨limitF_w2 (applyEdge_w2 hr'), fun hab => ?_⟩
    have hab0 : AbovePos X (limitF X.counted X.FL r').fact.path := hab.2.1
    rw [limitF_keepR hs hab0] at hab
    exact hr'n hab
  | @retRec M i n f n' c e1 a j g r e2 r' hf hE he1 ha hrec _ hr he2 hr' ihf =>
    obtain ⟨-, t, ht⟩ := DB_concrete RExact.emitM_copies hsd hf
    obtain ⟨ta, hta⟩ := applyEdge_mark_conc ht ha
    have han := rinv_bind (hs.toC _ _ _ _ hE e1 he1) ihf.2 ha
    have hrn := rinv_summary (hrecs _ _ _ hrec) han (applyEdge_w2 ha) hta hr
    have hr'n := rinv_bind (hs.fromC _ _ _ _ hE e2 he2) hrn hr'
    refine ⟨limitF_w2 (applyEdge_w2 hr'), fun hab => ?_⟩
    have hab0 : AbovePos X (limitF X.counted X.FL r').fact.path := hab.2.1
    rw [limitF_keepR hs hab0] at hab
    exact hr'n hab
  | reqSink => trivial
  | answer hreq _ _ _ _ _ => exact (DB_no_requestM hsd _ _ _ hreq).elim
  | reqUp => trivial
  | vuln => trivial
  | @clean M i n f n' cl f' _ hE hf ih =>
    refine ⟨cleanRes_w2 ih.1 hf, fun hab => ?_⟩
    rcases cleanRes_cases hf with rfl | ⟨-, t, ha, -, rfl⟩ | ⟨t, hct, rfl⟩ | ⟨-, -, rfl⟩
    · exact ih.2 hab
    · exact ih.2 ⟨hab.1, hab.2.1, hab.2.2⟩
    · rcases Exact.concPart_cases cl f with ⟨-, -, -, hcp⟩ | hcp
      · rw [hcp] at hab
        exact hab.2.2 rfl
      · rw [hcp] at hab
        exact ih.2 hab
    · exact ih.2 (aboveNE_norm (x := ⟨f.fact, true⟩) hab)
  | reqClean => trivial
  | filt _ _ _ ih => exact ih
  -- the zero rules
  | zpass =>
    show W2A zeroAF ∧ ¬ AboveNE X zeroAF.fact
    exact ⟨fun E hE => (by cases hE), fun hab => hab.2.2 rfl⟩
  | zin => exact fun hab => hab.2.2 rfl
  | @seed M n s hsm _ _ =>
    obtain ⟨hk, hna⟩ := hso M n s hsm
    have hw : W2A ⟨s, false⟩ := by
      intro E hE
      rcases hk with hk | hk
      · have h' : s.kind = .star E := hE
        rw [hk] at h'
        cases h'
      · have h' : s.kind = .star E := hE
        rw [hk] at h'
        cases h'
    refine ⟨limitF_w2 hw, fun hab => ?_⟩
    have hab0 : AbovePos X (limitF X.counted X.FL ⟨s, false⟩).fact.path := hab.2.1
    rw [limitF_keepR hs hab0] at hab
    exact hna hab
  | @zret M n n' c g r e2 r' _ _ hE _ hr he2 hr' _ ihg =>
    have hrn := rinv_summary (a := zeroAF) (j := zeroFact) (recOK_of ihg.1 ihg.2)
      (fun hab => hab.2.2 rfl) (fun E hE => by cases hE) (t := zeroMark) rfl hr
    have hr'n := rinv_bind (hs.fromC _ _ _ _ hE e2 he2) hrn hr'
    refine ⟨limitF_w2 (applyEdge_w2 hr'), fun hab => ?_⟩
    have hab0 : AbovePos X (limitF X.counted X.FL r').fact.path := hab.2.1
    rw [limitF_keepR hs hab0] at hab
    exact hr'n hab

#print axioms binv_all

/-- The edge form: no static edge fact of a backward run with a `*` or `[any]` tail strictly above
    a position. -/
theorem no_any_above_B {X : SCtx} (hs : SWFR X) {demand : MethodId → DemandEdge → Prop}
    {recs : MethodId → PFact × AFact → Prop} (hrecs : ∀ m j g, recs m (j, g) → RecOK X j g)
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    {seeds : List (MethodId × Node × PFact)} {zbind : Bool}
    (hsd : SeedsConc seeds) (hso : SeedsOK X seeds)
    {M : MethodId} {i : PFact} {n : Node} {f : AFact}
    (h : DB X.P X.counted X.FL demand emitM satI restrictU recs sinks roots seeds zbind
      (.edge M i n f))
    (hb : f.fact.base = X.sB) (hp : AbovePos X f.fact.path) : f.fact.kind = .exact := by
  cases hk : f.fact.kind with
  | exact => rfl
  | any => exact absurd ⟨hb, hp, by rw [hk]; intro h; cases h⟩ (binv_all hs hrecs hsd hso h).2
  | star e => exact absurd ⟨hb, hp, by rw [hk]; intro h; cases h⟩ (binv_all hs hrecs hsd hso h).2

#print axioms no_any_above_B

/-- Every static read, write keep edge or copy of the program the backward run runs on, whose
    premise is at most a static field and that gives a fact, is the case at or below (the
    analogue of `StaticsIter.static_step_below`). -/
theorem static_step_below_B {X : SCtx} (hs : SWFR X) {demand : MethodId → DemandEdge → Prop}
    {recs : MethodId → PFact × AFact → Prop} (hrecs : ∀ m j g, recs m (j, g) → RecOK X j g)
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    {seeds : List (MethodId × Node × PFact)} {zbind : Bool}
    (hsd : SeedsConc seeds) (hso : SeedsOK X seeds)
    {M : MethodId} {i : PFact} {n n' : Node} {f : AFact} {s : Stmt} {e : MicroEdge} {y : AFact}
    (h : DB X.P X.counted X.FL demand emitM satI restrictU recs sinks roots seeds zbind
      (.edge M i n f))
    (hE : (M, n, Instr.stmt s, n') ∈ X.P.edges) (he : e ∈ s.edges) (heb : e.1.base = X.sB)
    (hlen : e.1.path.length ≤ 2)
    (hy : y ∈ (applyEdge f e.1 e.2).facts) : ∃ rr, f.fact.path = e.1.path ++ rr := by
  obtain ⟨p, k, ap, m, hfb, -, -, -, hgeo⟩ := apply_shape hy
  rcases hgeo with ⟨rr, hrr, -⟩ | ⟨rr, hq, hne, ha⟩
  · exact ⟨rr, hrr⟩
  · exfalso
    obtain ⟨-, hadm, -, -⟩ := above_tk ha
    have hpos : PosIn X e.1.path := .inl ⟨M, n, s, n', e, hE, he, heb, List.take_of_length_le hlen⟩
    exact (binv_all hs hrecs hsd hso h).2 ⟨hfb.trans heb, ⟨_, rr, hpos, hne, hq⟩,
      admits_ne_exact hne hadm⟩

#print axioms static_step_below_B

/-- The exit edges of a backward run are good records (`RecOK`), so a later backward run can reuse
    them under `binv_all`. -/
theorem recOK_of_DB {X : SCtx} (hs : SWFR X) {demand : MethodId → DemandEdge → Prop}
    {recs : MethodId → PFact × AFact → Prop} (hrecs : ∀ m j g, recs m (j, g) → RecOK X j g)
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    {seeds : List (MethodId × Node × PFact)} {zbind : Bool}
    (hsd : SeedsConc seeds) (hso : SeedsOK X seeds)
    {M : MethodId} {j : PFact} {n : Node} {g : AFact}
    (h : DB X.P X.counted X.FL demand emitM satI restrictU recs sinks roots seeds zbind
      (.edge M j n g)) : RecOK X j g :=
  recOK_of (binv_all hs hrecs hsd hso h).1 (binv_all hs hrecs hsd hso h).2

#print axioms recOK_of_DB

/-- 4'. NO STATIC RULE IN ANY BACKWARD RUN of the iteration (the backward half of
    `StaticsIter.no_static_rule_after_run1`). Backward run `k` is `DB` on `Program.rev X.P` with the
    field limit `LB k`, any demand `demB k`, records `recsB k` and seeds `seeds k` (the user's
    design, `zbind = true`, roots `X.roots`, no forward sinks). If the reversed program with that
    field limit satisfies the construction rules (`SWFR`), the records keep the run-1 invariant
    (they do when they are exit edges of `DS`, of `DR` or of `DB`: `recOK_of_DS`, `recOK_of_DR`,
    `recOK_of_DB`) and the seeds are sink patterns that keep it, then every backward run
    satisfies the static invariant and raises no request. -/
theorem no_static_rule_backward {X : SCtx} {LB : Nat → Nat}
    (hsb : ∀ k, SWFR { X with P := Program.rev X.P, FL := LB k })
    {demB : Nat → MethodId → DemandEdge → Prop} {recsB : Nat → MethodId → PFact × AFact → Prop}
    {seeds : Nat → List (MethodId × Node × PFact)}
    (hrecs : ∀ k m j g, recsB k m (j, g) → RecOK { X with P := Program.rev X.P, FL := LB k } j g)
    (hsd : ∀ k, SeedsConc (seeds k))
    (hso : ∀ k, SeedsOK { X with P := Program.rev X.P, FL := LB k } (seeds k)) (k : Nat) :
    (∀ o, DB (Program.rev X.P) X.counted (LB k) (demB k) emitM satI restrictU (recsB k) [] X.roots
        (seeds k) true o → RInv { X with P := Program.rev X.P, FL := LB k } o) ∧
    (∀ M i t, ¬ DB (Program.rev X.P) X.counted (LB k) (demB k) emitM satI restrictU (recsB k) []
        X.roots (seeds k) true (.req M i t)) :=
  ⟨fun _ h => binv_all (X := { X with P := Program.rev X.P, FL := LB k }) (hsb k)
      (fun m j g h => hrecs k m j g h) (hsd k) (hso k) h,
   DB_no_requestM (hsd k)⟩

#print axioms no_static_rule_backward

end Part4

end ApSpec.BExact

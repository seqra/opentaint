/-
  ApSpec.PipelineAnyTaintDriver — the iteration driver over the pipeline with the tail kind
  `[any-taint]` (decision F69; analyzer-core.md §7, §12; `ap.md` §8.11, §9.2).

  As `PipelineDriver.driver_iteration` and `PipelineSeeds.driver_iteration_src`, for the run
  sequence of F69: run 1 is the encoded closure `AnyTaint.D6T` (run 1 with the rule W6T,
  `PipelineAnyTaint.sysD6T`), every backward run is the encoded closure `Backward.DB` of the
  reversed program (`PipelineAP.sysDB`, no new closure), and every forward restricted run is the
  encoded closure `AnyTaint.DRT` with must-premises (`PipelineAnyTaint.sysDRT`, the spec instance
  `emitM`, `satI`, `restrictU`).

  The objects of run 1 (`PO`) and of a restricted run (`TPObj`, with must flags) have different
  types. So the driver holds two kinds of final states: `st1` for run 1 and `stR k` for forward
  restricted run `k + 1` (the spec's run `2k + 3`); `stB k` is the backward run after forward run
  `k` (the spec's run `2k + 2`). The driver reads a restricted run with its must flags forgotten
  (`AnyTaintSim.forgetRun`): the backward demand (`DemandEdge`) has no must flag, so a pattern
  tail `[any-taint]` is a LABEL (DESIGN §1; `handoff_sameT`: the driver hands on the same
  backward demand as from the base run `DR`).

  Main theorems:
    * `resultSeq_runSeqT`, `resultSeq_runSeqSrcT`: what the driver reads from the complete
      forward runs is the run sequence `AnyTaintSim.runSeqT` (`runSeqSrcT` with forward seeds)
      (`PipelineAnyTaint.result_D6T`, `result_DRT`).
    * `handoff_sameT`: the backward demand that the driver computes from a complete restricted
      run is the reversed summary demand of the base restricted run `DR`
      (`AnyTaintSim.revSummaryDemandT_iff`).
    * `driver_iterationT`: if every run of the driver is complete and the driver computes the
      hand-offs of analyzer-core.md §7.3, §7.4 from the final states, then every forward run of
      the driver reports every real vulnerability, in some layer
      (`AnyTaintSim.iteration_reportsT`).
    * `driver_iteration_uptoT`: the same for a finite run sequence (the driver stops after
      forward run `2K + 1`).
    * `driver_iteration_srcT`: the same with forward seeds (forward restricted run `k + 1` analyses
      `FSeeds.keepSources P (σ k)`; `AnyTaintSim.iteration_srcT`).

  No new hypothesis: the hypotheses are those of `PipelineDriver.driver_iteration` (resp.
  `PipelineSeeds.driver_iteration_src`), with the systems `sysD6T`, `sysDRT` in place of `sysD`,
  `sysDR`; no hypothesis on the taint edges and on the records (with must flags) of the forward
  restricted runs.

  All proofs are constructive (`propext`, `Quot.sound` only; see the `#print axioms` lines).
-/
import ApSpec.PipelineAnyTaint
import ApSpec.AnyTaintSim
import ApSpec.PipelineDriver

namespace ApSpec.PipelineAnyTaintDriver
open ApSpec ApSpec.Reverse ApSpec.Pipeline ApSpec.PipelineAP ApSpec.Backward ApSpec.PipelineDriver
  ApSpec.AnyTaint ApSpec.AnyTaintSim ApSpec.PipelineAnyTaint

/-! ## 1. What the driver reads from the forward runs -/

/-- What the driver reads from forward run `k` of the sequence, as objects without must flags:
    forward run 1 (`k = 0`) from the final state `st1` of `sysD6T`; forward restricted run
    `k + 1` from the final state `stR k` of `sysDRT`, with the must flags forgotten
    (`forgetRun`). The backward demand and the seeds of the next backward run are computed from
    it. -/
def resultSeq (st1 : St PO MethodId MethodId) (stR : Nat → St TPObj MethodId MethodId) :
    Nat → Obj → Prop
  | 0     => result st1
  | k + 1 => forgetRun (resultT (stR k))

theorem resultSeq_zero (st1 : St PO MethodId MethodId) (stR : Nat → St TPObj MethodId MethodId) :
    resultSeq st1 stR 0 = result st1 := rfl

theorem resultSeq_succ (st1 : St PO MethodId MethodId) (stR : Nat → St TPObj MethodId MethodId)
    (k : Nat) : resultSeq st1 stR (k + 1) = forgetRun (resultT (stR k)) := rfl

/-- A vulnerability that the driver reads from forward restricted run `k + 1` (the flags
    forgotten) is a vulnerability object of its final state, and back. -/
theorem resultSeq_vuln_succ {st1 : St PO MethodId MethodId}
    {stR : Nat → St TPObj MethodId MethodId} {k : Nat} {M : MethodId} {n : Node} {s : PFact}
    {b : Bool} :
    resultSeq st1 stR (k + 1) (.vuln M n s b) ↔ TPObj.base (.vuln M n s b) ∈ (stR k).known :=
  ⟨fun h => forgetRun_vuln h, fun h => ⟨_, h, rfl⟩⟩

#print axioms resultSeq_vuln_succ

/-- COMPLETE FORWARD RUNS GIVE THE RUN SEQUENCE WITH `[any-taint]`: if run 1 is a complete run of
    `sysD6T` (reachable and quiescent) and every forward restricted run `k + 1` is a complete run
    of `sysDRT` (the demand `dem k`, the records `recs k`), then what the driver reads from
    forward run `k` is run `k` of `AnyTaintSim.runSeqT` (`result_D6T`, `result_DRT`). -/
theorem resultSeq_runSeqT {P : Program} {taint : TaintEdges} {counted : Acc → Bool}
    {Ls : Nat → Nat} {dem : Nat → MethodId → DemandEdge → Prop}
    {recs : Nat → MethodId → PFact × Bool × AFact → Prop} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {st1 : St PO MethodId MethodId}
    {stR : Nat → St TPObj MethodId MethodId}
    (hF0 : Pipeline.Reach (sysD6T P taint counted (Ls 0) policy1 sinks roots) st1)
    (hQF0 : st1.Quiescent) {k : Nat}
    (hF : ∀ i, i + 1 ≤ k → Pipeline.Reach
      (sysDRT P taint counted (Ls (i + 1)) (dem i) emitM satI restrictU (recs i) sinks roots)
      (stR i))
    (hQF : ∀ i, i + 1 ≤ k → (stR i).Quiescent) :
    resultSeq st1 stR k = runSeqT P taint counted Ls dem emitM satI restrictU recs sinks roots k := by
  cases k with
  | zero => exact result_D6T hF0 hQF0
  | succ i =>
    show forgetRun (resultT (stR i)) =
      forgetRun (DRT P taint counted (Ls (i + 1)) (dem i) emitM satI restrictU (recs i) sinks roots)
    rw [result_DRT (hF i (Nat.le_refl _)) (hQF i (Nat.le_refl _))]

#print axioms resultSeq_runSeqT

/-- With forward seeds: if run 1 is a complete run of `sysD6T` on `P` and forward restricted run
    `k + 1` is a complete run of `sysDRT` on `FSeeds.keepSources P (σ k)`, then what the driver
    reads from forward run `k` is run `k` of `AnyTaintSim.runSeqSrcT`. -/
theorem resultSeq_runSeqSrcT {P : Program} {taint : TaintEdges} {counted : Acc → Bool}
    {Ls : Nat → Nat} {σ : Nat → MethodId → Node → MicroEdge → Bool}
    {dem : Nat → MethodId → DemandEdge → Prop}
    {recs : Nat → MethodId → PFact × Bool × AFact → Prop} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {st1 : St PO MethodId MethodId}
    {stR : Nat → St TPObj MethodId MethodId}
    (hF0 : Pipeline.Reach (sysD6T P taint counted (Ls 0) policy1 sinks roots) st1)
    (hQF0 : st1.Quiescent) {k : Nat}
    (hF : ∀ i, i + 1 ≤ k → Pipeline.Reach
      (sysDRT (FSeeds.keepSources P (σ i)) taint counted (Ls (i + 1)) (dem i) emitM satI restrictU
        (recs i) sinks roots) (stR i))
    (hQF : ∀ i, i + 1 ≤ k → (stR i).Quiescent) :
    resultSeq st1 stR k =
      runSeqSrcT P taint counted Ls σ dem emitM satI restrictU recs sinks roots k := by
  cases k with
  | zero => exact result_D6T hF0 hQF0
  | succ i =>
    show forgetRun (resultT (stR i)) =
      forgetRun (DRT (FSeeds.keepSources P (σ i)) taint counted (Ls (i + 1)) (dem i) emitM satI
        restrictU (recs i) sinks roots)
    rw [result_DRT (hF i (Nat.le_refl _)) (hQF i (Nat.le_refl _))]

#print axioms resultSeq_runSeqSrcT

/-- THE HAND-OFF OF A RESTRICTED RUN IS THAT OF THE BASE RUN: the backward demand that the driver
    computes from the final state of a complete run of `sysDRT` (the reversed summary demand, the
    must flags forgotten) is the reversed summary demand of the base restricted run `DR` with the
    records `recsDR recs` (`revSummaryDemandT_iff`). So the must flags and the layers of `DRT` are
    not visible to the backward run: the pattern tail `[any-taint]` is a label. -/
theorem handoff_sameT {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop} {recs : MethodId → PFact × Bool × AFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    {st : St TPObj MethodId MethodId}
    (hR : Pipeline.Reach
      (sysDRT P taint counted L demand emitM satI restrictU recs sinks roots) st)
    (hQ : st.Quiescent) :
    revSummaryDemand P (forgetRun (resultT st)) =
      revSummaryDemand P (DR P counted L demand emitM satI restrictU (recsDR recs) sinks roots) := by
  rw [result_DRT hR hQ]
  exact backward_reads_sameT RExact.emitM_copies restrictU_fact

#print axioms handoff_sameT

/-! ## 2. The driver theorem -/

/-- THE DRIVER THEOREM WITH `[any-taint]`. `st1` is the final state of forward run 1 (a run of
    `sysD6T`), `stR k` the final state of forward restricted run `k + 1` (the spec's run `2k + 3`,
    a run of `sysDRT` with the demand `dem k` and the records `recs k`), `stB k` the final state of
    the backward run after forward run `k` (a run of `sysDB` of the reversed program). Every run
    is complete (reachable and quiescent). The driver computes the hand-offs from the final
    states: the backward demand contains the reversed summaries of the forward run before it, read
    with the must flags forgotten (`resultSeq`; §7.3), the seeds contain its vulnerabilities
    (§7.3), and the forward demand contains the hand-off `demOf` of the backward run before it
    (§7.4). Then every forward run of the driver reports every real vulnerability, in some layer:
    run 1 and every forward restricted run.
    Hypotheses: those of `PipelineDriver.driver_iteration` (S10, `BindTargetsStar`,
    `StmtsMarkRev`, `NoZeroBack`, `ZeroKept`, `ExitReach`; the sinks have the tail `$` or `[any]`;
    any field limits, backward records and forward records); no hypothesis on the taint edges. -/
theorem driver_iterationT {P : Program} (hW : P.WF) (hT : BindTargetsStar P)
    (hmr : StmtsMarkRev P) (hNZB : NoZeroBack P) (hZ : ZeroKept P) {roots : List MethodId}
    (hX : ExitReach P roots) {sinks : List (MethodId × Node × PFact)}
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    {taint : TaintEdges} {counted : Acc → Bool} {Ls : Nat → Nat}
    {dem : Nat → MethodId → DemandEdge → Prop}
    {recs : Nat → MethodId → PFact × Bool × AFact → Prop}
    (LB : Nat → Nat) (demB : Nat → MethodId → DemandEdge → Prop)
    (recsB : Nat → MethodId → PFact × AFact → Prop) (seeds : Nat → List (MethodId × Node × PFact))
    (st1 : St PO MethodId MethodId) (stR : Nat → St TPObj MethodId MethodId)
    (stB : Nat → St PO MethodId MethodId)
    (hF0 : Pipeline.Reach (sysD6T P taint counted (Ls 0) policy1 sinks roots) st1)
    (hQF0 : st1.Quiescent)
    (hF : ∀ k, Pipeline.Reach
      (sysDRT P taint counted (Ls (k + 1)) (dem k) emitM satI restrictU (recs k) sinks roots)
      (stR k))
    (hQF : ∀ k, (stR k).Quiescent)
    (hB : ∀ k, Pipeline.Reach (sysDB (Program.rev P) counted (LB k) (demB k) emitM satI restrictU
      (recsB k) [] roots (seeds k) true) (stB k))
    (hQB : ∀ k, (stB k).Quiescent)
    (hdemB : ∀ k m d, revSummaryDemand P (resultSeq st1 stR k) m d → demB k m d)
    (hseeds : ∀ k M n s b, resultSeq st1 stR k (.vuln M n s b) → (M, n, s) ∈ seeds k)
    (hdem : ∀ k m d, demOf (Program.rev P) (result (stB k)) m d → dem k m d)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : ApSpec.Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    (∃ b, PObj.base (.vuln M n s b) ∈ st1.known) ∧
      ∀ k, ∃ b, TPObj.base (.vuln M n s b) ∈ (stR k).known := by
  have hres : ∀ k, resultSeq st1 stR k =
      runSeqT P taint counted Ls dem emitM satI restrictU recs sinks roots k :=
    fun _ => resultSeq_runSeqT hF0 hQF0 (fun i _ => hF i) (fun i _ => hQF i)
  have hresB : ∀ k, result (stB k) = DB (Program.rev P) counted (LB k) (demB k) emitM satI
      restrictU (recsB k) [] roots (seeds k) true := fun k => result_DB (hB k) (hQB k)
  obtain ⟨h1, hR⟩ := iteration_reportsT hW hT hmr hNZB hZ hX hk LB demB recsB seeds
    (fun k m d h => hdemB k m d (by rw [hres k]; exact h))
    (fun k M' n' s' b h => hseeds k M' n' s' b (by rw [hres k]; exact h))
    (fun k m d h => hdem k m d (by rw [hresB k]; exact h))
    hRe hs hT' hsc
  refine ⟨?_, fun k => ?_⟩
  · obtain ⟨b, hb⟩ := h1
    refine ⟨b, ?_⟩
    have : result st1 (.vuln M n s b) := by rw [result_D6T hF0 hQF0]; exact hb
    exact this
  · obtain ⟨b, hb⟩ := hR k
    refine ⟨b, ?_⟩
    have : resultT (stR k) (.vuln M n s b) := by rw [result_DRT (hF k) (hQF k)]; exact hb
    exact this

#print axioms driver_iterationT

/-! ## 3. The driver stops: a finite run sequence -/

/-- Only the sink rule makes a vulnerability (run 1 with W6T). -/
theorem vuln_sink_D6T {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
    {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {M : MethodId} {n : Node} {s : PFact} {b : Bool}
    (h : D6T P taint counted L α sinks roots (.vuln M n s b)) : (M, n, s) ∈ sinks := by
  cases h with
  | vuln _ hs _ => exact hs

/-- Only the sink rule makes a vulnerability (a restricted run with must-premises). -/
theorem vuln_sink_DRT {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop} {emit : PFact → PFact → Option PFact}
    {sat : PFact → PFact → Bool} {restrict : PFact → AFact → DemandEdge → Option AFact}
    {recs : MethodId → PFact × Bool × AFact → Prop} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {M : MethodId} {n : Node} {s : PFact} {b : Bool}
    (h : DRT P taint counted L demand emit sat restrict recs sinks roots (.vuln M n s b)) :
    (M, n, s) ∈ sinks := by
  cases h with
  | vuln _ hs _ => exact hs

/-- Only the sink rule makes a vulnerability (any run of the sequence `runSeqT`). -/
theorem vuln_sink_runSeqT {P : Program} {taint : TaintEdges} {counted : Acc → Bool}
    {Ls : Nat → Nat} {dem : Nat → MethodId → DemandEdge → Prop}
    {emit : PFact → PFact → Option PFact} {sat : PFact → PFact → Bool}
    {restrict : PFact → AFact → DemandEdge → Option AFact}
    {recs : Nat → MethodId → PFact × Bool × AFact → Prop} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {k : Nat} {M : MethodId} {n : Node} {s : PFact} {b : Bool}
    (h : runSeqT P taint counted Ls dem emit sat restrict recs sinks roots k (.vuln M n s b)) :
    (M, n, s) ∈ sinks := by
  cases k with
  | zero => exact vuln_sink_D6T h
  | succ k => exact vuln_sink_DRT (forgetRun_vuln h)

/-- The run sequence with `[any-taint]` up to run `k` reads only the demands before `k`. -/
theorem runSeqT_congr {P : Program} {taint : TaintEdges} {counted : Acc → Bool}
    {Ls : Nat → Nat} {dem dem' : Nat → MethodId → DemandEdge → Prop}
    {recs : Nat → MethodId → PFact × Bool × AFact → Prop} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {k : Nat} (h : ∀ i, i + 1 ≤ k → dem' i = dem i) :
    runSeqT P taint counted Ls dem' emitM satI restrictU recs sinks roots k =
      runSeqT P taint counted Ls dem emitM satI restrictU recs sinks roots k := by
  cases k with
  | zero => rfl
  | succ i =>
    show forgetRun (DRT P taint counted (Ls (i + 1)) (dem' i) emitM satI restrictU (recs i) sinks
        roots) =
      forgetRun (DRT P taint counted (Ls (i + 1)) (dem i) emitM satI restrictU (recs i) sinks roots)
    rw [h i (Nat.le_refl _)]

/-- THE DRIVER THEOREM WITH `[any-taint]` FOR A FINITE SEQUENCE. The driver stops after forward
    run `2K + 1`. Let the runs up to it be complete: forward run 1 `st1` (a run of `sysD6T`),
    forward restricted runs `stR 0` to `stR (K - 1)` (runs of `sysDRT`) and backward runs `stB 0`
    to `stB (K - 1)` (runs of `sysDB`), with the hand-offs of analyzer-core.md §7.3 and §7.4
    between them (as in `driver_iterationT`). Then each of these forward runs reports every real
    vulnerability, in some layer. (The proof extends the sequence after `K` with the full demand
    and every sink as a seed, so `iteration_generalT` applies.) Hypotheses: those of
    `driver_iterationT`, for the runs up to `K`. -/
theorem driver_iteration_uptoT {P : Program} (hW : P.WF) (hT : BindTargetsStar P)
    (hmr : StmtsMarkRev P) (hNZB : NoZeroBack P) (hZ : ZeroKept P) {roots : List MethodId}
    (hX : ExitReach P roots) {sinks : List (MethodId × Node × PFact)}
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    {taint : TaintEdges} {counted : Acc → Bool} {Ls : Nat → Nat}
    {dem : Nat → MethodId → DemandEdge → Prop}
    {recs : Nat → MethodId → PFact × Bool × AFact → Prop}
    (LB : Nat → Nat) (demB : Nat → MethodId → DemandEdge → Prop)
    (recsB : Nat → MethodId → PFact × AFact → Prop) (seeds : Nat → List (MethodId × Node × PFact))
    (K : Nat) (st1 : St PO MethodId MethodId) (stR : Nat → St TPObj MethodId MethodId)
    (stB : Nat → St PO MethodId MethodId)
    (hF0 : Pipeline.Reach (sysD6T P taint counted (Ls 0) policy1 sinks roots) st1)
    (hQF0 : st1.Quiescent)
    (hF : ∀ k, k + 1 ≤ K → Pipeline.Reach
      (sysDRT P taint counted (Ls (k + 1)) (dem k) emitM satI restrictU (recs k) sinks roots)
      (stR k))
    (hQF : ∀ k, k + 1 ≤ K → (stR k).Quiescent)
    (hB : ∀ k, k < K → Pipeline.Reach (sysDB (Program.rev P) counted (LB k) (demB k) emitM satI
      restrictU (recsB k) [] roots (seeds k) true) (stB k))
    (hQB : ∀ k, k < K → (stB k).Quiescent)
    (hdemB : ∀ k, k < K → ∀ m d, revSummaryDemand P (resultSeq st1 stR k) m d → demB k m d)
    (hseeds : ∀ k, k < K → ∀ M n s b, resultSeq st1 stR k (.vuln M n s b) → (M, n, s) ∈ seeds k)
    (hdem : ∀ k, k < K → ∀ m d, demOf (Program.rev P) (result (stB k)) m d → dem k m d)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : ApSpec.Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    (∃ b, PObj.base (.vuln M n s b) ∈ st1.known) ∧
      ∀ k, k + 1 ≤ K → ∃ b, TPObj.base (.vuln M n s b) ∈ (stR k).known := by
  -- the sequence after `K`: the full demand and every sink as a seed
  let dem' : Nat → MethodId → DemandEdge → Prop := fun k => if k < K then dem k else fun _ _ => True
  let demB' : Nat → MethodId → DemandEdge → Prop :=
    fun k => if k < K then demB k else fun _ _ => True
  let seeds' : Nat → List (MethodId × Node × PFact) := fun k => if k < K then seeds k else sinks
  have hdem'_eq : ∀ k, k < K → dem' k = dem k := fun k h => by simp only [dem', if_pos h]
  have hdemB'_eq : ∀ k, k < K → demB' k = demB k := fun k h => by simp only [demB', if_pos h]
  have hseeds'_eq : ∀ k, k < K → seeds' k = seeds k := fun k h => by simp only [seeds', if_pos h]
  -- the forward runs up to `K` are the runs of the extended sequence
  have hres : ∀ k, k ≤ K → resultSeq st1 stR k =
      runSeqT P taint counted Ls dem' emitM satI restrictU recs sinks roots k := by
    intro k hkK
    rw [runSeqT_congr (dem := dem) (fun i hi => hdem'_eq i (Nat.lt_of_lt_of_le hi hkK))]
    exact resultSeq_runSeqT hF0 hQF0 (fun i hi => hF i (Nat.le_trans hi hkK))
      (fun i hi => hQF i (Nat.le_trans hi hkK))
  have hresB : ∀ k, k < K → result (stB k) = DB (Program.rev P) counted (LB k) (demB' k) emitM
      satI restrictU (recsB k) [] roots (seeds' k) true := by
    intro k hkK
    rw [hdemB'_eq k hkK, hseeds'_eq k hkK]
    exact result_DB (hB k hkK) (hQB k hkK)
  have hit := iteration_generalT (taint := taint) (dem := dem') (recs := recs) hW hT hmr hNZB hZ
    hX hk LB demB' recsB seeds'
    (fun k m d h => by
      by_cases hkK : k < K
      · rw [hdemB'_eq k hkK]
        exact hdemB k hkK m d (by rw [hres k (Nat.le_of_lt hkK)]; exact h)
      · simp only [demB', if_neg hkK])
    (fun k M' n' s' b h => by
      by_cases hkK : k < K
      · rw [hseeds'_eq k hkK]
        exact hseeds k hkK M' n' s' b (by rw [hres k (Nat.le_of_lt hkK)]; exact h)
      · simp only [seeds', if_neg hkK]
        exact vuln_sink_runSeqT h)
    (fun k m d h => by
      by_cases hkK : k < K
      · rw [hdem'_eq k hkK]
        exact hdem k hkK m d (by rw [hresB k hkK]; exact h)
      · simp only [dem', if_neg hkK])
    hRe hs hT' hsc
  refine ⟨?_, fun k hkK => ?_⟩
  · obtain ⟨b, hb⟩ := hit 0
    refine ⟨b, ?_⟩
    have : resultSeq st1 stR 0 (.vuln M n s b) := by rw [hres 0 (Nat.zero_le _)]; exact hb
    exact this
  · obtain ⟨b, hb⟩ := hit (k + 1)
    refine ⟨b, ?_⟩
    have : resultSeq st1 stR (k + 1) (.vuln M n s b) := by rw [hres (k + 1) hkK]; exact hb
    exact resultSeq_vuln_succ.1 this

#print axioms driver_iteration_uptoT

/-! ## 4. The driver with forward seeds -/

/-- THE DRIVER THEOREM WITH `[any-taint]` AND FORWARD SEEDS. `st1` is the final state of forward
    run 1 (a run of `sysD6T` on the full program), `stR k` the final state of forward restricted
    run `k + 1` (a run of `sysDRT` on `FSeeds.keepSources P (σ k)`: only the seeded unconditional
    sources fire), `stB k` the final state of the backward run after forward run `k` (a run of
    `sysDB` of the full reversed program `Program.rev P`). Every run is complete (reachable and
    quiescent). The driver computes the hand-offs from the final states: the backward demand
    contains the reversed summaries of the forward run (computed on its own program
    `FSeeds.progSrc P σ k`, read with the must flags forgotten), the sink seeds contain its
    vulnerabilities, the forward demand contains the hand-off `demOf` of the backward run, and the
    source seeds `σ k` contain the source hits of backward run `k`. Then every forward run of the
    driver reports every real vulnerability of `P`, in some layer.
    Hypotheses: those of `PipelineSeeds.driver_iteration_src`; no hypothesis on the taint edges. -/
theorem driver_iteration_srcT {P : Program} (hW : P.WF) (hT : BindTargetsStar P)
    (hmr : StmtsMarkRev P) (hNZB : NoZeroBack P) (hZ : ZeroKept P) {roots : List MethodId}
    (hX : ExitReach P roots) {sinks : List (MethodId × Node × PFact)}
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    {taint : TaintEdges} {counted : Acc → Bool} {Ls : Nat → Nat}
    {dem : Nat → MethodId → DemandEdge → Prop}
    {recs : Nat → MethodId → PFact × Bool × AFact → Prop}
    (σ : Nat → MethodId → Node → MicroEdge → Bool)
    (LB : Nat → Nat) (demB : Nat → MethodId → DemandEdge → Prop)
    (recsB : Nat → MethodId → PFact × AFact → Prop) (seeds : Nat → List (MethodId × Node × PFact))
    (st1 : St PO MethodId MethodId) (stR : Nat → St TPObj MethodId MethodId)
    (stB : Nat → St PO MethodId MethodId)
    (hF0 : Pipeline.Reach (sysD6T P taint counted (Ls 0) policy1 sinks roots) st1)
    (hQF0 : st1.Quiescent)
    (hF : ∀ k, Pipeline.Reach
      (sysDRT (FSeeds.keepSources P (σ k)) taint counted (Ls (k + 1)) (dem k) emitM satI restrictU
        (recs k) sinks roots) (stR k))
    (hQF : ∀ k, (stR k).Quiescent)
    (hB : ∀ k, Pipeline.Reach (sysDB (Program.rev P) counted (LB k) (demB k) emitM satI restrictU
      (recsB k) [] roots (seeds k) true) (stB k))
    (hQB : ∀ k, (stB k).Quiescent)
    (hdemB : ∀ k m d, revSummaryDemand (FSeeds.progSrc P σ k) (resultSeq st1 stR k) m d →
      demB k m d)
    (hseeds : ∀ k M n s b, resultSeq st1 stR k (.vuln M n s b) → (M, n, s) ∈ seeds k)
    (hdem : ∀ k m d, demOf (Program.rev P) (result (stB k)) m d → dem k m d)
    (hσ : ∀ k M n e, FSeeds.srcHit P (result (stB k)) M n e → σ k M n e = true)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : ApSpec.Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    (∃ b, PObj.base (.vuln M n s b) ∈ st1.known) ∧
      ∀ k, ∃ b, TPObj.base (.vuln M n s b) ∈ (stR k).known := by
  have hres : ∀ k, resultSeq st1 stR k =
      runSeqSrcT P taint counted Ls σ dem emitM satI restrictU recs sinks roots k :=
    fun _ => resultSeq_runSeqSrcT hF0 hQF0 (fun i _ => hF i) (fun i _ => hQF i)
  have hresB : ∀ k, result (stB k) = DB (Program.rev P) counted (LB k) (demB k) emitM satI
      restrictU (recsB k) [] roots (seeds k) true := fun k => result_DB (hB k) (hQB k)
  obtain ⟨h1, hR⟩ := iteration_srcT hW hT hmr hNZB hZ hX hk σ LB demB recsB seeds
    (fun k m d h => hdemB k m d (by rw [hres k]; exact h))
    (fun k M' n' s' b h => hseeds k M' n' s' b (by rw [hres k]; exact h))
    (fun k m d h => hdem k m d (by rw [hresB k]; exact h))
    (fun k M' n' e h => hσ k M' n' e (by rw [hresB k]; exact h))
    hRe hs hT' hsc
  refine ⟨?_, fun k => ?_⟩
  · obtain ⟨b, hb⟩ := h1
    refine ⟨b, ?_⟩
    have : result st1 (.vuln M n s b) := by rw [result_D6T hF0 hQF0]; exact hb
    exact this
  · obtain ⟨b, hb⟩ := hR k
    refine ⟨b, ?_⟩
    have : resultT (stR k) (.vuln M n s b) := by rw [result_DRT (hF k) (hQF k)]; exact hb
    exact this

#print axioms driver_iteration_srcT

end ApSpec.PipelineAnyTaintDriver

/-
  ApSpec.PipelineAnyTaintExDriver — the iteration driver over the pipeline with the `[any-taint]`
  conclusion WITH AN EXCLUSION (decision F69, DESIGN §6 amendment A2; analyzer-core.md §7, §12;
  `ap.md` §8.11, §9.2).

  As `PipelineAnyTaintDriver.driver_iterationT` (and `PipelineDriver.driver_iteration`,
  `PipelineSeeds.driver_iteration_src`), for the refined run sequence of A2: run 1 is the encoded
  closure `AnyTaintEx.D6X` (`PipelineAnyTaintEx.sysD6X`, the policy `policy1`), every backward run
  is the encoded closure `Backward.DB` of the reversed program (`PipelineAP.sysDB`, no new closure),
  and every forward restricted run is the encoded closure `AnyTaintEx.DRX` with the spec rules
  (`PipelineAnyTaintEx.sysDRX` with `emitX`, `satX`, `restrictX`: the closure `DRXs`).

  The objects of run 1 (`XPObj6`, over `XObj6`) and of a restricted run (`XPObj`, over `XObj`, with
  must flags and exclusions) have different types. So the driver holds two kinds of final states:
  `st1` for run 1 and `stR k` for forward restricted run `k + 1` (the spec's run `2k + 3`); `stB k`
  is the backward run after forward run `k` (the spec's run `2k + 2`). The driver reads a forward run
  with its exclusions (and must flags) DROPPED (`AnyTaintExCov.forget6`, `forgetX`): the backward
  demand (`DemandEdge`) reads plain `PFact` patterns (A2: "the hand-off MAY drop `E`; the model
  drops it"). Unlike `PipelineAnyTaintDriver.handoff_sameT`, this hand-off is NOT that of the base
  run on the same demand (`AnyTaintExCov.CexRoute.route_a_false`: the exclusion removes summaries),
  so the driver theorem goes through the direct iteration `AnyTaintExCov.iteration_reportsX`, not
  through `AnyTaintSim.iteration_generalT`.

  Main theorems:
    * `resultSeqX_runSeqX`, `resultSeqX_runSeqSrcX`: what the driver reads from the complete forward
      runs (the exclusions dropped) is the run sequence `AnyTaintExCov.runSeqX` (`runSeqSrcX` with
      forward seeds) (`PipelineAnyTaintEx.result_D6X`, `result_DRXs`).
    * `driver_iterationX`: if every run of the driver is complete and the driver computes the
      hand-offs of analyzer-core.md §7.3, §7.4 from the final states (the forward runs read with the
      exclusions dropped), then every forward run of the driver reports every real vulnerability,
      in some layer (`AnyTaintExCov.iteration_reportsX`).
    * `driver_iteration_uptoX`: the same for a finite run sequence (the driver stops after forward
      run `2K + 1`; `AnyTaintExCov.iteration_generalX`).
    * `driver_iteration_srcX`: the same with forward seeds (forward restricted run `k + 1` analyses
      `FSeeds.keepSources P (σ k)`; `AnyTaintExCov.iteration_srcX`).

  No new hypothesis: the hypotheses are those of `PipelineAnyTaintDriver.driver_iterationT` (resp.
  `driver_iteration_uptoT`, `driver_iteration_srcT`), with the systems `sysD6X`, `sysDRX` (spec
  rules) in place of `sysD6T`, `sysDRT`; no hypothesis on the taint edges and on the records (with
  must flags and exclusions) of the forward restricted runs.

  All proofs are constructive (`propext`, `Quot.sound` only; see the `#print axioms` lines).
-/
import ApSpec.PipelineAnyTaintEx
import ApSpec.AnyTaintExCov
import ApSpec.PipelineDriver

namespace ApSpec.PipelineAnyTaintExDriver
open ApSpec ApSpec.Reverse ApSpec.Pipeline ApSpec.PipelineAP ApSpec.Backward ApSpec.PipelineDriver
  ApSpec.AnyTaint ApSpec.AnyTaintEx ApSpec.PipelineAnyTaintEx
open ApSpec.AnyTaintExCov (forget6 forgetX forget6_vuln forgetX_vuln runSeqX runSeqSrcX
  iteration_reportsX iteration_generalX iteration_srcX)

/-! ## 1. What the driver reads from the forward runs -/

/-- What the driver reads from forward run `k` of the sequence, as base objects (the exclusions and
    the must flags dropped): forward run 1 (`k = 0`) from the final state `st1` of `sysD6X`
    (`forget6`); forward restricted run `k + 1` from the final state `stR k` of `sysDRX`
    (`forgetX`). The backward demand and the seeds of the next backward run are computed from it. -/
def resultSeqX (st1 : St XPObj6 MethodId MethodId) (stR : Nat → St XPObj MethodId MethodId) :
    Nat → Obj → Prop
  | 0     => forget6 (resultX6 st1)
  | k + 1 => forgetX (resultX (stR k))

theorem resultSeqX_zero (st1 : St XPObj6 MethodId MethodId)
    (stR : Nat → St XPObj MethodId MethodId) :
    resultSeqX st1 stR 0 = forget6 (resultX6 st1) := rfl

theorem resultSeqX_succ (st1 : St XPObj6 MethodId MethodId)
    (stR : Nat → St XPObj MethodId MethodId) (k : Nat) :
    resultSeqX st1 stR (k + 1) = forgetX (resultX (stR k)) := rfl

/-- A vulnerability that the driver reads from forward run 1 (the exclusions dropped) is a
    vulnerability object of its final state, and back. -/
theorem resultSeqX_vuln_zero {st1 : St XPObj6 MethodId MethodId}
    {stR : Nat → St XPObj MethodId MethodId} {M : MethodId} {n : Node} {s : PFact} {b : Bool} :
    resultSeqX st1 stR 0 (.vuln M n s b) ↔ XPObj6.base (.vuln M n s b) ∈ st1.known :=
  ⟨fun h => forget6_vuln h, fun h => ⟨_, h, rfl⟩⟩

#print axioms resultSeqX_vuln_zero

/-- A vulnerability that the driver reads from forward restricted run `k + 1` (the exclusions and
    the must flags dropped) is a vulnerability object of its final state, and back. -/
theorem resultSeqX_vuln_succ {st1 : St XPObj6 MethodId MethodId}
    {stR : Nat → St XPObj MethodId MethodId} {k : Nat} {M : MethodId} {n : Node} {s : PFact}
    {b : Bool} :
    resultSeqX st1 stR (k + 1) (.vuln M n s b) ↔ XPObj.base (.vuln M n s b) ∈ (stR k).known :=
  ⟨fun h => forgetX_vuln h, fun h => ⟨_, h, rfl⟩⟩

#print axioms resultSeqX_vuln_succ

/-- COMPLETE FORWARD RUNS GIVE THE RUN SEQUENCE WITH THE EXCLUSION: if run 1 is a complete run of
    `sysD6X` (reachable and quiescent) and every forward restricted run `k + 1` is a complete run of
    `sysDRX` with the spec rules (the demand `dem k`, the records `recs k`), then what the driver
    reads from forward run `k` is run `k` of `AnyTaintExCov.runSeqX` (`result_D6X`,
    `result_DRXs`). -/
theorem resultSeqX_runSeqX {P : Program} {taint : TaintEdges} {counted : Acc → Bool}
    {Ls : Nat → Nat} {dem : Nat → MethodId → DemandEdge → Prop}
    {recs : Nat → MethodId → PFact × Bool × Excl × XFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    {st1 : St XPObj6 MethodId MethodId} {stR : Nat → St XPObj MethodId MethodId}
    (hF0 : Pipeline.Reach (sysD6X P taint counted (Ls 0) policy1 sinks roots) st1)
    (hQF0 : st1.Quiescent) {k : Nat}
    (hF : ∀ i, i + 1 ≤ k → Pipeline.Reach
      (sysDRX P taint counted (Ls (i + 1)) (dem i) emitX satX restrictX (recs i) sinks roots)
      (stR i))
    (hQF : ∀ i, i + 1 ≤ k → (stR i).Quiescent) :
    resultSeqX st1 stR k = runSeqX P taint counted Ls dem recs sinks roots k := by
  cases k with
  | zero =>
    show forget6 (resultX6 st1) = forget6 (D6X P taint counted (Ls 0) policy1 sinks roots)
    rw [result_D6X hF0 hQF0]
  | succ i =>
    show forgetX (resultX (stR i)) =
      forgetX (DRXs P taint counted (Ls (i + 1)) (dem i) (recs i) sinks roots)
    rw [result_DRXs (hF i (Nat.le_refl _)) (hQF i (Nat.le_refl _))]

#print axioms resultSeqX_runSeqX

/-- With forward seeds: if run 1 is a complete run of `sysD6X` on `P` and forward restricted run
    `k + 1` is a complete run of `sysDRX` (spec rules) on `FSeeds.keepSources P (σ k)`, then what
    the driver reads from forward run `k` is run `k` of `AnyTaintExCov.runSeqSrcX`. -/
theorem resultSeqX_runSeqSrcX {P : Program} {taint : TaintEdges} {counted : Acc → Bool}
    {Ls : Nat → Nat} {σ : Nat → MethodId → Node → MicroEdge → Bool}
    {dem : Nat → MethodId → DemandEdge → Prop}
    {recs : Nat → MethodId → PFact × Bool × Excl × XFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    {st1 : St XPObj6 MethodId MethodId} {stR : Nat → St XPObj MethodId MethodId}
    (hF0 : Pipeline.Reach (sysD6X P taint counted (Ls 0) policy1 sinks roots) st1)
    (hQF0 : st1.Quiescent) {k : Nat}
    (hF : ∀ i, i + 1 ≤ k → Pipeline.Reach
      (sysDRX (FSeeds.keepSources P (σ i)) taint counted (Ls (i + 1)) (dem i) emitX satX restrictX
        (recs i) sinks roots) (stR i))
    (hQF : ∀ i, i + 1 ≤ k → (stR i).Quiescent) :
    resultSeqX st1 stR k = runSeqSrcX P taint counted Ls σ dem recs sinks roots k := by
  cases k with
  | zero =>
    show forget6 (resultX6 st1) = forget6 (D6X P taint counted (Ls 0) policy1 sinks roots)
    rw [result_D6X hF0 hQF0]
  | succ i =>
    show forgetX (resultX (stR i)) =
      forgetX (DRXs (FSeeds.keepSources P (σ i)) taint counted (Ls (i + 1)) (dem i) (recs i) sinks
        roots)
    rw [result_DRXs (hF i (Nat.le_refl _)) (hQF i (Nat.le_refl _))]

#print axioms resultSeqX_runSeqSrcX

/-! ## 2. The driver theorem -/

/-- THE DRIVER THEOREM WITH THE EXCLUSION OF `[any-taint]`. `st1` is the final state of forward run
    1 (a run of `sysD6X`), `stR k` the final state of forward restricted run `k + 1` (the spec's run
    `2k + 3`, a run of `sysDRX` with the spec rules `emitX`, `satX`, `restrictX`, the demand `dem k`
    and the records `recs k`), `stB k` the final state of the backward run after forward run `k` (a
    run of `sysDB` of the reversed program). Every run is complete (reachable and quiescent). The
    driver computes the hand-offs from the final states: the backward demand contains the reversed
    summaries of the forward run before it, read with the exclusions and the must flags dropped
    (`resultSeqX`: `forget6`, `forgetX`; §7.3, A2), the seeds contain its vulnerabilities (§7.3),
    and the forward demand contains the hand-off `demOf` of the backward run before it (§7.4). Then
    every forward run of the driver reports every real vulnerability, in some layer: run 1 and
    every forward restricted run.
    Hypotheses: those of `PipelineAnyTaintDriver.driver_iterationT` (S10, `BindTargetsStar`,
    `StmtsMarkRev`, `NoZeroBack`, `ZeroKept`, `ExitReach`; the sinks have the tail `$` or `[any]`;
    any field limits, backward records and forward records); no hypothesis on the taint edges. -/
theorem driver_iterationX {P : Program} (hW : P.WF) (hT : BindTargetsStar P)
    (hmr : StmtsMarkRev P) (hNZB : NoZeroBack P) (hZ : ZeroKept P) {roots : List MethodId}
    (hX : ExitReach P roots) {sinks : List (MethodId × Node × PFact)}
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    {taint : TaintEdges} {counted : Acc → Bool} {Ls : Nat → Nat}
    {dem : Nat → MethodId → DemandEdge → Prop}
    {recs : Nat → MethodId → PFact × Bool × Excl × XFact → Prop}
    (LB : Nat → Nat) (demB : Nat → MethodId → DemandEdge → Prop)
    (recsB : Nat → MethodId → PFact × AFact → Prop) (seeds : Nat → List (MethodId × Node × PFact))
    (st1 : St XPObj6 MethodId MethodId) (stR : Nat → St XPObj MethodId MethodId)
    (stB : Nat → St PO MethodId MethodId)
    (hF0 : Pipeline.Reach (sysD6X P taint counted (Ls 0) policy1 sinks roots) st1)
    (hQF0 : st1.Quiescent)
    (hF : ∀ k, Pipeline.Reach
      (sysDRX P taint counted (Ls (k + 1)) (dem k) emitX satX restrictX (recs k) sinks roots)
      (stR k))
    (hQF : ∀ k, (stR k).Quiescent)
    (hB : ∀ k, Pipeline.Reach (sysDB (Program.rev P) counted (LB k) (demB k) emitM satI restrictU
      (recsB k) [] roots (seeds k) true) (stB k))
    (hQB : ∀ k, (stB k).Quiescent)
    (hdemB : ∀ k m d, revSummaryDemand P (resultSeqX st1 stR k) m d → demB k m d)
    (hseeds : ∀ k M n s b, resultSeqX st1 stR k (.vuln M n s b) → (M, n, s) ∈ seeds k)
    (hdem : ∀ k m d, demOf (Program.rev P) (result (stB k)) m d → dem k m d)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : ApSpec.Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    (∃ b, XPObj6.base (.vuln M n s b) ∈ st1.known) ∧
      ∀ k, ∃ b, XPObj.base (.vuln M n s b) ∈ (stR k).known := by
  have hres : ∀ k, resultSeqX st1 stR k = runSeqX P taint counted Ls dem recs sinks roots k :=
    fun _ => resultSeqX_runSeqX hF0 hQF0 (fun i _ => hF i) (fun i _ => hQF i)
  have hresB : ∀ k, result (stB k) = DB (Program.rev P) counted (LB k) (demB k) emitM satI
      restrictU (recsB k) [] roots (seeds k) true := fun k => result_DB (hB k) (hQB k)
  obtain ⟨h1, hR⟩ := iteration_reportsX (taint := taint) (counted := counted) (Ls := Ls)
    (dem := dem) (recs := recs) hW hT hmr hNZB hZ hX hk LB demB recsB seeds
    (fun k m d h => hdemB k m d (by rw [hres k]; exact h))
    (fun k M' n' s' b h => hseeds k M' n' s' b (by rw [hres k]; exact h))
    (fun k m d h => hdem k m d (by rw [hresB k]; exact h))
    hRe hs hT' hsc
  refine ⟨?_, fun k => ?_⟩
  · obtain ⟨b, hb⟩ := h1
    refine ⟨b, ?_⟩
    have : resultX6 st1 (.vuln M n s b) := by rw [result_D6X hF0 hQF0]; exact hb
    exact this
  · obtain ⟨b, hb⟩ := hR k
    refine ⟨b, ?_⟩
    have : resultX (stR k) (.vuln M n s b) := by rw [result_DRXs (hF k) (hQF k)]; exact hb
    exact this

#print axioms driver_iterationX

/-! ## 3. The driver stops: a finite run sequence -/

/-- Only the sink rule makes a vulnerability (run 1 with the exclusion). -/
theorem vuln_sink_D6X {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
    {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {M : MethodId} {n : Node} {s : PFact} {b : Bool}
    (h : D6X P taint counted L α sinks roots (.vuln M n s b)) : (M, n, s) ∈ sinks := by
  cases h with
  | vuln _ hs _ => exact hs

/-- Only the sink rule makes a vulnerability (a restricted run with must-premises and
    exclusions, any rules). -/
theorem vuln_sink_DRX {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop}
    {emit : PFact → PFact → Excl → Option (PFact × Excl)}
    {sat : PFact → Excl → PFact → Excl → Bool}
    {restrict : PFact → Excl → XFact → DemandEdge → Option XFact}
    {recs : MethodId → PFact × Bool × Excl × XFact → Prop} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {M : MethodId} {n : Node} {s : PFact} {b : Bool}
    (h : DRX P taint counted L demand emit sat restrict recs sinks roots (.vuln M n s b)) :
    (M, n, s) ∈ sinks := by
  cases h with
  | vuln _ hs _ => exact hs

/-- Only the sink rule makes a vulnerability (any run of the sequence `runSeqX`). -/
theorem vuln_sink_runSeqX {P : Program} {taint : TaintEdges} {counted : Acc → Bool}
    {Ls : Nat → Nat} {dem : Nat → MethodId → DemandEdge → Prop}
    {recs : Nat → MethodId → PFact × Bool × Excl × XFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId} {k : Nat} {M : MethodId}
    {n : Node} {s : PFact} {b : Bool}
    (h : runSeqX P taint counted Ls dem recs sinks roots k (.vuln M n s b)) :
    (M, n, s) ∈ sinks := by
  cases k with
  | zero => exact vuln_sink_D6X (forget6_vuln h)
  | succ k => exact vuln_sink_DRX (forgetX_vuln h)

/-- The run sequence with the exclusion up to run `k` reads only the demands before `k`. -/
theorem runSeqX_congr {P : Program} {taint : TaintEdges} {counted : Acc → Bool}
    {Ls : Nat → Nat} {dem dem' : Nat → MethodId → DemandEdge → Prop}
    {recs : Nat → MethodId → PFact × Bool × Excl × XFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId} {k : Nat}
    (h : ∀ i, i + 1 ≤ k → dem' i = dem i) :
    runSeqX P taint counted Ls dem' recs sinks roots k =
      runSeqX P taint counted Ls dem recs sinks roots k := by
  cases k with
  | zero => rfl
  | succ i =>
    show forgetX (DRXs P taint counted (Ls (i + 1)) (dem' i) (recs i) sinks roots) =
      forgetX (DRXs P taint counted (Ls (i + 1)) (dem i) (recs i) sinks roots)
    rw [h i (Nat.le_refl _)]

/-- THE DRIVER THEOREM WITH THE EXCLUSION FOR A FINITE SEQUENCE. The driver stops after forward run
    `2K + 1`. Let the runs up to it be complete: forward run 1 `st1` (a run of `sysD6X`), forward
    restricted runs `stR 0` to `stR (K - 1)` (runs of `sysDRX` with the spec rules) and backward
    runs `stB 0` to `stB (K - 1)` (runs of `sysDB`), with the hand-offs of analyzer-core.md §7.3
    and §7.4 between them (as in `driver_iterationX`: the forward runs read with the exclusions
    dropped). Then each of these forward runs reports every real vulnerability, in some layer.
    (The proof extends the sequence after `K` with the full demand and every sink as a seed, so
    `AnyTaintExCov.iteration_generalX` applies.) Hypotheses: those of `driver_iterationX`, for the
    runs up to `K`. -/
theorem driver_iteration_uptoX {P : Program} (hW : P.WF) (hT : BindTargetsStar P)
    (hmr : StmtsMarkRev P) (hNZB : NoZeroBack P) (hZ : ZeroKept P) {roots : List MethodId}
    (hX : ExitReach P roots) {sinks : List (MethodId × Node × PFact)}
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    {taint : TaintEdges} {counted : Acc → Bool} {Ls : Nat → Nat}
    {dem : Nat → MethodId → DemandEdge → Prop}
    {recs : Nat → MethodId → PFact × Bool × Excl × XFact → Prop}
    (LB : Nat → Nat) (demB : Nat → MethodId → DemandEdge → Prop)
    (recsB : Nat → MethodId → PFact × AFact → Prop) (seeds : Nat → List (MethodId × Node × PFact))
    (K : Nat) (st1 : St XPObj6 MethodId MethodId) (stR : Nat → St XPObj MethodId MethodId)
    (stB : Nat → St PO MethodId MethodId)
    (hF0 : Pipeline.Reach (sysD6X P taint counted (Ls 0) policy1 sinks roots) st1)
    (hQF0 : st1.Quiescent)
    (hF : ∀ k, k + 1 ≤ K → Pipeline.Reach
      (sysDRX P taint counted (Ls (k + 1)) (dem k) emitX satX restrictX (recs k) sinks roots)
      (stR k))
    (hQF : ∀ k, k + 1 ≤ K → (stR k).Quiescent)
    (hB : ∀ k, k < K → Pipeline.Reach (sysDB (Program.rev P) counted (LB k) (demB k) emitM satI
      restrictU (recsB k) [] roots (seeds k) true) (stB k))
    (hQB : ∀ k, k < K → (stB k).Quiescent)
    (hdemB : ∀ k, k < K → ∀ m d, revSummaryDemand P (resultSeqX st1 stR k) m d → demB k m d)
    (hseeds : ∀ k, k < K → ∀ M n s b, resultSeqX st1 stR k (.vuln M n s b) → (M, n, s) ∈ seeds k)
    (hdem : ∀ k, k < K → ∀ m d, demOf (Program.rev P) (result (stB k)) m d → dem k m d)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : ApSpec.Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    (∃ b, XPObj6.base (.vuln M n s b) ∈ st1.known) ∧
      ∀ k, k + 1 ≤ K → ∃ b, XPObj.base (.vuln M n s b) ∈ (stR k).known := by
  -- the sequence after `K`: the full demand and every sink as a seed
  let dem' : Nat → MethodId → DemandEdge → Prop := fun k => if k < K then dem k else fun _ _ => True
  let demB' : Nat → MethodId → DemandEdge → Prop :=
    fun k => if k < K then demB k else fun _ _ => True
  let seeds' : Nat → List (MethodId × Node × PFact) := fun k => if k < K then seeds k else sinks
  have hdem'_eq : ∀ k, k < K → dem' k = dem k := fun k h => by simp only [dem', if_pos h]
  have hdemB'_eq : ∀ k, k < K → demB' k = demB k := fun k h => by simp only [demB', if_pos h]
  have hseeds'_eq : ∀ k, k < K → seeds' k = seeds k := fun k h => by simp only [seeds', if_pos h]
  -- the forward runs up to `K` are the runs of the extended sequence
  have hres : ∀ k, k ≤ K → resultSeqX st1 stR k =
      runSeqX P taint counted Ls dem' recs sinks roots k := by
    intro k hkK
    rw [runSeqX_congr (dem := dem) (fun i hi => hdem'_eq i (Nat.lt_of_lt_of_le hi hkK))]
    exact resultSeqX_runSeqX hF0 hQF0 (fun i hi => hF i (Nat.le_trans hi hkK))
      (fun i hi => hQF i (Nat.le_trans hi hkK))
  have hresB : ∀ k, k < K → result (stB k) = DB (Program.rev P) counted (LB k) (demB' k) emitM
      satI restrictU (recsB k) [] roots (seeds' k) true := by
    intro k hkK
    rw [hdemB'_eq k hkK, hseeds'_eq k hkK]
    exact result_DB (hB k hkK) (hQB k hkK)
  have hit := iteration_generalX (taint := taint) (counted := counted) (Ls := Ls) (dem := dem')
    (recs := recs) hW hT hmr hNZB hZ hX hk LB demB' recsB seeds'
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
        exact vuln_sink_runSeqX h)
    (fun k m d h => by
      by_cases hkK : k < K
      · rw [hdem'_eq k hkK]
        exact hdem k hkK m d (by rw [hresB k hkK]; exact h)
      · simp only [dem', if_neg hkK])
    hRe hs hT' hsc
  refine ⟨?_, fun k hkK => ?_⟩
  · obtain ⟨b, hb⟩ := hit 0
    refine ⟨b, ?_⟩
    have : resultSeqX st1 stR 0 (.vuln M n s b) := by rw [hres 0 (Nat.zero_le _)]; exact hb
    exact resultSeqX_vuln_zero.1 this
  · obtain ⟨b, hb⟩ := hit (k + 1)
    refine ⟨b, ?_⟩
    have : resultSeqX st1 stR (k + 1) (.vuln M n s b) := by rw [hres (k + 1) hkK]; exact hb
    exact resultSeqX_vuln_succ.1 this

#print axioms driver_iteration_uptoX

/-! ## 4. The driver with forward seeds -/

/-- THE DRIVER THEOREM WITH THE EXCLUSION AND FORWARD SEEDS. `st1` is the final state of forward
    run 1 (a run of `sysD6X` on the full program), `stR k` the final state of forward restricted
    run `k + 1` (a run of `sysDRX` with the spec rules on `FSeeds.keepSources P (σ k)`: only the
    seeded unconditional sources fire), `stB k` the final state of the backward run after forward
    run `k` (a run of `sysDB` of the full reversed program `Program.rev P`). Every run is complete
    (reachable and quiescent). The driver computes the hand-offs from the final states: the
    backward demand contains the reversed summaries of the forward run (computed on its own program
    `FSeeds.progSrc P σ k`, read with the exclusions and the must flags dropped), the sink seeds
    contain its vulnerabilities, the forward demand contains the hand-off `demOf` of the backward
    run, and the source seeds `σ k` contain the source hits of backward run `k`. Then every forward
    run of the driver reports every real vulnerability of `P`, in some layer.
    Hypotheses: those of `PipelineAnyTaintDriver.driver_iteration_srcT`; no hypothesis on the taint
    edges. -/
theorem driver_iteration_srcX {P : Program} (hW : P.WF) (hT : BindTargetsStar P)
    (hmr : StmtsMarkRev P) (hNZB : NoZeroBack P) (hZ : ZeroKept P) {roots : List MethodId}
    (hX : ExitReach P roots) {sinks : List (MethodId × Node × PFact)}
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    {taint : TaintEdges} {counted : Acc → Bool} {Ls : Nat → Nat}
    {dem : Nat → MethodId → DemandEdge → Prop}
    {recs : Nat → MethodId → PFact × Bool × Excl × XFact → Prop}
    (σ : Nat → MethodId → Node → MicroEdge → Bool)
    (LB : Nat → Nat) (demB : Nat → MethodId → DemandEdge → Prop)
    (recsB : Nat → MethodId → PFact × AFact → Prop) (seeds : Nat → List (MethodId × Node × PFact))
    (st1 : St XPObj6 MethodId MethodId) (stR : Nat → St XPObj MethodId MethodId)
    (stB : Nat → St PO MethodId MethodId)
    (hF0 : Pipeline.Reach (sysD6X P taint counted (Ls 0) policy1 sinks roots) st1)
    (hQF0 : st1.Quiescent)
    (hF : ∀ k, Pipeline.Reach
      (sysDRX (FSeeds.keepSources P (σ k)) taint counted (Ls (k + 1)) (dem k) emitX satX restrictX
        (recs k) sinks roots) (stR k))
    (hQF : ∀ k, (stR k).Quiescent)
    (hB : ∀ k, Pipeline.Reach (sysDB (Program.rev P) counted (LB k) (demB k) emitM satI restrictU
      (recsB k) [] roots (seeds k) true) (stB k))
    (hQB : ∀ k, (stB k).Quiescent)
    (hdemB : ∀ k m d, revSummaryDemand (FSeeds.progSrc P σ k) (resultSeqX st1 stR k) m d →
      demB k m d)
    (hseeds : ∀ k M n s b, resultSeqX st1 stR k (.vuln M n s b) → (M, n, s) ∈ seeds k)
    (hdem : ∀ k m d, demOf (Program.rev P) (result (stB k)) m d → dem k m d)
    (hσ : ∀ k M n e, FSeeds.srcHit P (result (stB k)) M n e → σ k M n e = true)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : ApSpec.Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    (∃ b, XPObj6.base (.vuln M n s b) ∈ st1.known) ∧
      ∀ k, ∃ b, XPObj.base (.vuln M n s b) ∈ (stR k).known := by
  have hres : ∀ k, resultSeqX st1 stR k =
      runSeqSrcX P taint counted Ls σ dem recs sinks roots k :=
    fun _ => resultSeqX_runSeqSrcX hF0 hQF0 (fun i _ => hF i) (fun i _ => hQF i)
  have hresB : ∀ k, result (stB k) = DB (Program.rev P) counted (LB k) (demB k) emitM satI
      restrictU (recsB k) [] roots (seeds k) true := fun k => result_DB (hB k) (hQB k)
  obtain ⟨h1, hR⟩ := iteration_srcX (taint := taint) (counted := counted) (Ls := Ls) (dem := dem)
    (recs := recs) hW hT hmr hNZB hZ hX hk σ LB demB recsB seeds
    (fun k m d h => hdemB k m d (by rw [hres k]; exact h))
    (fun k M' n' s' b h => hseeds k M' n' s' b (by rw [hres k]; exact h))
    (fun k m d h => hdem k m d (by rw [hresB k]; exact h))
    (fun k M' n' e h => hσ k M' n' e (by rw [hresB k]; exact h))
    hRe hs hT' hsc
  refine ⟨?_, fun k => ?_⟩
  · obtain ⟨b, hb⟩ := h1
    refine ⟨b, ?_⟩
    have : resultX6 st1 (.vuln M n s b) := by rw [result_D6X hF0 hQF0]; exact hb
    exact this
  · obtain ⟨b, hb⟩ := hR k
    refine ⟨b, ?_⟩
    have : resultX (stR k) (.vuln M n s b) := by rw [result_DRXs (hF k) (hQF k)]; exact hb
    exact this

#print axioms driver_iteration_srcX

end ApSpec.PipelineAnyTaintExDriver

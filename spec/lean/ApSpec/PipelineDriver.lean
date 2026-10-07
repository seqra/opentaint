/-
  ApSpec.PipelineDriver — the iteration driver over the pipeline (analyzer-core.md §7).

  The driver runs forward run 1, backward run 2, forward run 3, and so on. Each run is a fresh
  pipeline (`Pipeline.Sys`, the encodings of `PipelineAP`). The driver waits until a run is
  quiescent (the barrier), reads the objects that the final state holds, and computes the
  hand-off of the next run from them.

  Main theorems:
    * `result_D`, `result_DR`, `result_DB`: the objects that a reachable quiescent state of an
      encoded run holds are exactly the AP closure of that run (`Pipeline.quiescent_exact` with
      `PipelineAP.clD_iff`, `clDR_iff`, `clDB_iff`).
    * `driver_iteration`: if every run of the driver is complete and the driver computes the
      hand-offs of analyzer-core.md §7.3, §7.4 from the final states, then every forward run of
      the driver reports every real vulnerability (`Backward.iteration_general`).

  All proofs are constructive (`propext`, `Quot.sound` only).
-/
import ApSpec.PipelineProofs
import ApSpec.PipelineAP

namespace ApSpec.PipelineDriver
open ApSpec ApSpec.Reverse ApSpec.Pipeline ApSpec.PipelineAP ApSpec.Backward

/-- What the driver reads from the final state of a run: the closure objects that it holds. -/
def result (st : St PO MethodId MethodId) : Obj → Prop := fun o => PObj.base o ∈ st.known

/-- A complete run 1: the driver reads exactly `D`. -/
theorem result_D {P : Program} {counted : Acc → Bool} {L : Nat} {α : MethodId → PFact → PFact}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId} {st : St PO MethodId MethodId}
    (hR : Pipeline.Reach (sysD P counted L α sinks roots) st) (hQ : st.Quiescent) :
    result st = D P counted L α sinks roots := by
  funext o
  exact propext ((quiescent_exact sysD_wf hR hQ).trans clD_iff)

#print axioms result_D

/-- A complete restricted run: the driver reads exactly `DR`. -/
theorem result_DR {P : Program} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop} {emit : PFact → PFact → Option PFact}
    {sat : PFact → PFact → Bool} {restrict : PFact → AFact → DemandEdge → Option AFact}
    {recs : MethodId → (PFact × AFact) → Prop} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {st : St PO MethodId MethodId}
    (hR : Pipeline.Reach (sysDR P counted L demand emit sat restrict recs sinks roots) st)
    (hQ : st.Quiescent) :
    result st = DR P counted L demand emit sat restrict recs sinks roots := by
  funext o
  exact propext ((quiescent_exact sysDR_wf hR hQ).trans clDR_iff)

#print axioms result_DR

/-- A complete backward run: the driver reads exactly `DB`. -/
theorem result_DB {Pb : Program} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop} {emit : PFact → PFact → Option PFact}
    {sat : PFact → PFact → Bool} {restrict : PFact → AFact → DemandEdge → Option AFact}
    {recs : MethodId → (PFact × AFact) → Prop} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {seeds : List (MethodId × Node × PFact)} {zbind : Bool}
    {st : St PO MethodId MethodId}
    (hR : Pipeline.Reach
      (sysDB Pb counted L demand emit sat restrict recs sinks roots seeds zbind) st)
    (hQ : st.Quiescent) :
    result st = DB Pb counted L demand emit sat restrict recs sinks roots seeds zbind := by
  funext o
  exact propext ((quiescent_exact sysDB_wf hR hQ).trans clDB_iff)

#print axioms result_DB

/-- THE DRIVER THEOREM. `stF k` is the final state of forward run `2k + 1` (`stF 0` is run 1),
    `stB k` the final state of the backward run after it. Every run is complete (reachable and
    quiescent). The driver computes the hand-offs from the final states: the backward demand
    contains the reversed summaries of the forward run (§7.3), the seeds contain its
    vulnerabilities (§7.3), and the forward demand contains the hand-off `demOf` of the backward
    run (§7.4). Then every forward run of the driver reports every real vulnerability. -/
theorem driver_iteration {P : Program} (hW : P.WF) (hT : BindTargetsStar P)
    (hmr : StmtsMarkRev P) (hNZB : NoZeroBack P) (hZ : ZeroKept P) {roots : List MethodId}
    (hX : ExitReach P roots) {sinks : List (MethodId × Node × PFact)}
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    {counted : Acc → Bool} {Ls : Nat → Nat}
    {dem : Nat → MethodId → DemandEdge → Prop} {recs : Nat → MethodId → PFact × AFact → Prop}
    (LB : Nat → Nat) (demB : Nat → MethodId → DemandEdge → Prop)
    (recsB : Nat → MethodId → PFact × AFact → Prop) (seeds : Nat → List (MethodId × Node × PFact))
    (stF stB : Nat → St PO MethodId MethodId)
    (hF0 : Pipeline.Reach (sysD P counted (Ls 0) policy1 sinks roots) (stF 0))
    (hQF0 : (stF 0).Quiescent)
    (hF : ∀ k, Pipeline.Reach
      (sysDR P counted (Ls (k + 1)) (dem k) emitM satI restrictU (recs k) sinks roots) (stF (k + 1)))
    (hQF : ∀ k, (stF (k + 1)).Quiescent)
    (hB : ∀ k, Pipeline.Reach (sysDB (Program.rev P) counted (LB k) (demB k) emitM satI restrictU
      (recsB k) [] roots (seeds k) true) (stB k))
    (hQB : ∀ k, (stB k).Quiescent)
    (hdemB : ∀ k m d, revSummaryDemand P (result (stF k)) m d → demB k m d)
    (hseeds : ∀ k M n s b, result (stF k) (.vuln M n s b) → (M, n, s) ∈ seeds k)
    (hdem : ∀ k m d, demOf (Program.rev P) (result (stB k)) m d → dem k m d)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : ApSpec.Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, ∃ b, PObj.base (.vuln M n s b) ∈ (stF k).known := by
  have hres : ∀ k, result (stF k) =
      RCov.runSeq P counted Ls dem emitM satI restrictU recs sinks roots k := by
    intro k
    cases k with
    | zero => exact result_D hF0 hQF0
    | succ k => exact result_DR (hF k) (hQF k)
  have hresB : ∀ k, result (stB k) = DB (Program.rev P) counted (LB k) (demB k) emitM satI
      restrictU (recsB k) [] roots (seeds k) true := fun k => result_DB (hB k) (hQB k)
  have hit := iteration_general hW hT hmr hNZB hZ hX hk LB demB recsB seeds
    (fun k m d h => hdemB k m d (by rw [hres k]; exact h))
    (fun k M' n' s' b h => hseeds k M' n' s' b (by rw [hres k]; exact h))
    (fun k m d h => hdem k m d (by rw [hresB k]; exact h))
    hRe hs hT' hsc
  intro k
  obtain ⟨b, hb⟩ := hit k
  refine ⟨b, ?_⟩
  have : result (stF k) (.vuln M n s b) := by rw [hres k]; exact hb
  exact this

#print axioms driver_iteration

/-! ## The driver stops: a finite run sequence -/

/-- Only the sink rule makes a vulnerability (run 1). -/
theorem vuln_sink_D {P : Program} {counted : Acc → Bool} {L : Nat} {α : MethodId → PFact → PFact}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId} {M : MethodId} {n : Node}
    {s : PFact} {b : Bool} (h : D P counted L α sinks roots (.vuln M n s b)) : (M, n, s) ∈ sinks := by
  cases h with
  | vuln _ hs _ => exact hs

/-- Only the sink rule makes a vulnerability (a restricted run). -/
theorem vuln_sink_DR {P : Program} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop} {emit : PFact → PFact → Option PFact}
    {sat : PFact → PFact → Bool} {restrict : PFact → AFact → DemandEdge → Option AFact}
    {recs : MethodId → (PFact × AFact) → Prop} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {M : MethodId} {n : Node} {s : PFact} {b : Bool}
    (h : DR P counted L demand emit sat restrict recs sinks roots (.vuln M n s b)) :
    (M, n, s) ∈ sinks := by
  cases h with
  | vuln _ hs _ => exact hs

/-- The run sequence up to run `k` reads only the demands before `k`. -/
theorem runSeq_congr {P : Program} {counted : Acc → Bool} {Ls : Nat → Nat}
    {dem dem' : Nat → MethodId → DemandEdge → Prop} {recs : Nat → MethodId → PFact × AFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId} {k : Nat}
    (h : ∀ i, i + 1 ≤ k → dem' i = dem i) :
    RCov.runSeq P counted Ls dem' emitM satI restrictU recs sinks roots k =
      RCov.runSeq P counted Ls dem emitM satI restrictU recs sinks roots k := by
  cases k with
  | zero => rfl
  | succ i =>
    show DR P counted (Ls (i + 1)) (dem' i) emitM satI restrictU (recs i) sinks roots =
      DR P counted (Ls (i + 1)) (dem i) emitM satI restrictU (recs i) sinks roots
    rw [h i (Nat.le_refl _)]

/-- THE DRIVER THEOREM FOR A FINITE SEQUENCE. The driver stops after forward run `2K + 1`. Let the
    runs up to it be complete: forward runs `stF 0` to `stF K` and backward runs `stB 0` to
    `stB (K - 1)`, with the hand-offs of analyzer-core.md §7.3 and §7.4 between them. Then each of
    these forward runs reports every real vulnerability. (The proof extends the sequence after `K`
    with the full demand, so `iteration_general` applies.) -/
theorem driver_iteration_upto {P : Program} (hW : P.WF) (hT : BindTargetsStar P)
    (hmr : StmtsMarkRev P) (hNZB : NoZeroBack P) (hZ : ZeroKept P) {roots : List MethodId}
    (hX : ExitReach P roots) {sinks : List (MethodId × Node × PFact)}
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    {counted : Acc → Bool} {Ls : Nat → Nat}
    {dem : Nat → MethodId → DemandEdge → Prop} {recs : Nat → MethodId → PFact × AFact → Prop}
    (LB : Nat → Nat) (demB : Nat → MethodId → DemandEdge → Prop)
    (recsB : Nat → MethodId → PFact × AFact → Prop) (seeds : Nat → List (MethodId × Node × PFact))
    (K : Nat) (stF stB : Nat → St PO MethodId MethodId)
    (hF0 : Pipeline.Reach (sysD P counted (Ls 0) policy1 sinks roots) (stF 0))
    (hQF0 : (stF 0).Quiescent)
    (hF : ∀ k, k + 1 ≤ K → Pipeline.Reach
      (sysDR P counted (Ls (k + 1)) (dem k) emitM satI restrictU (recs k) sinks roots) (stF (k + 1)))
    (hQF : ∀ k, k + 1 ≤ K → (stF (k + 1)).Quiescent)
    (hB : ∀ k, k < K → Pipeline.Reach (sysDB (Program.rev P) counted (LB k) (demB k) emitM satI
      restrictU (recsB k) [] roots (seeds k) true) (stB k))
    (hQB : ∀ k, k < K → (stB k).Quiescent)
    (hdemB : ∀ k, k < K → ∀ m d, revSummaryDemand P (result (stF k)) m d → demB k m d)
    (hseeds : ∀ k, k < K → ∀ M n s b, result (stF k) (.vuln M n s b) → (M, n, s) ∈ seeds k)
    (hdem : ∀ k, k < K → ∀ m d, demOf (Program.rev P) (result (stB k)) m d → dem k m d)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : ApSpec.Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, k ≤ K → ∃ b, PObj.base (.vuln M n s b) ∈ (stF k).known := by
  -- the sequence after `K`: the full demand and every sink as a seed
  let dem' : Nat → MethodId → DemandEdge → Prop := fun k => if k < K then dem k else fun _ _ => True
  let demB' : Nat → MethodId → DemandEdge → Prop :=
    fun k => if k < K then demB k else fun _ _ => True
  let seeds' : Nat → List (MethodId × Node × PFact) := fun k => if k < K then seeds k else sinks
  have hdem'_eq : ∀ k, k < K → dem' k = dem k := fun k h => by simp only [dem', if_pos h]
  have hdemB'_eq : ∀ k, k < K → demB' k = demB k := fun k h => by simp only [demB', if_pos h]
  have hseeds'_eq : ∀ k, k < K → seeds' k = seeds k := fun k h => by simp only [seeds', if_pos h]
  -- the forward runs up to `K` are the closures of the extended sequence
  have hres : ∀ k, k ≤ K → result (stF k) =
      RCov.runSeq P counted Ls dem' emitM satI restrictU recs sinks roots k := by
    intro k hkK
    rw [runSeq_congr (dem := dem) (fun i hi => hdem'_eq i (Nat.lt_of_lt_of_le hi hkK))]
    cases k with
    | zero => exact result_D hF0 hQF0
    | succ k => exact result_DR (hF k hkK) (hQF k hkK)
  have hresB : ∀ k, k < K → result (stB k) = DB (Program.rev P) counted (LB k) (demB' k) emitM
      satI restrictU (recsB k) [] roots (seeds' k) true := by
    intro k hkK
    rw [hdemB'_eq k hkK, hseeds'_eq k hkK]
    exact result_DB (hB k hkK) (hQB k hkK)
  have hit := iteration_general (dem := dem') (recs := recs) hW hT hmr hNZB hZ hX hk LB demB' recsB
    seeds'
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
        cases k with
        | zero => exact vuln_sink_D h
        | succ k => exact vuln_sink_DR h)
    (fun k m d h => by
      by_cases hkK : k < K
      · rw [hdem'_eq k hkK]
        exact hdem k hkK m d (by rw [hresB k hkK]; exact h)
      · simp only [dem', if_neg hkK])
    hRe hs hT' hsc
  intro k hkK
  obtain ⟨b, hb⟩ := hit k
  refine ⟨b, ?_⟩
  have : result (stF k) (.vuln M n s b) := by rw [hres k hkK]; exact hb
  exact this

#print axioms driver_iteration_upto

end ApSpec.PipelineDriver

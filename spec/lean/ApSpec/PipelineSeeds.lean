/-
  ApSpec.PipelineSeeds — the iteration driver over the pipeline with FORWARD SEEDS
  (analyzer-core.md §4.7, §7.4; `ap.md` §8.11).

  As `PipelineDriver.driver_iteration`, but a forward restricted run fires only the unconditional
  sources that the backward run before it reached: forward run `2k + 3` is the encoded restricted
  system of the program `FSeeds.keepSources P (σ k)`, and the driver computes the source seeds
  `σ k` from the final state of the backward run `stB k` (its source hits, `FSeeds.srcHit`). Run 1
  is the encoded closure `D` of the full program, and every backward run is the encoded closure
  `DB` of the full reversed program `Program.rev P`.

  Main theorem:
    * `driver_iteration_src`: if every run of the driver is complete and the driver computes the
      hand-offs (the backward demand, the sink seeds, the forward demand and the SOURCE SEEDS) from
      the final states, then every forward run of the driver reports every real vulnerability
      (`FSeeds.iteration_src`, with `PipelineDriver.result_D`, `result_DR`, `result_DB`).

  All proofs are constructive (`propext`, `Quot.sound` only).
-/
import ApSpec.PipelineDriver
import ApSpec.ForwardSeeds

namespace ApSpec.PipelineSeeds
open ApSpec ApSpec.Reverse ApSpec.Pipeline ApSpec.PipelineAP ApSpec.Backward ApSpec.PipelineDriver

/-- THE DRIVER THEOREM WITH FORWARD SEEDS. `stF k` is the final state of forward run `2k + 1`
    (`stF 0` is run 1, on the full program), `stB k` the final state of the backward run after it.
    Every run is complete (reachable and quiescent). Forward run `k + 1` analyses
    `keepSources P (σ k)`. The driver computes the hand-offs from the final states: the backward
    demand contains the reversed summaries of the forward run (computed on its own program), the
    sink seeds contain its vulnerabilities, the forward demand contains the hand-off `demOf` of the
    backward run, and the source seeds `σ k` contain the source hits of backward run `k`. Then every
    forward run of the driver reports every real vulnerability. -/
theorem driver_iteration_src {P : Program} (hW : P.WF) (hT : BindTargetsStar P)
    (hmr : StmtsMarkRev P) (hNZB : NoZeroBack P) (hZ : ZeroKept P) {roots : List MethodId}
    (hX : ExitReach P roots) {sinks : List (MethodId × Node × PFact)}
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    {counted : Acc → Bool} {Ls : Nat → Nat}
    {dem : Nat → MethodId → DemandEdge → Prop} {recs : Nat → MethodId → PFact × AFact → Prop}
    (σ : Nat → MethodId → Node → MicroEdge → Bool)
    (LB : Nat → Nat) (demB : Nat → MethodId → DemandEdge → Prop)
    (recsB : Nat → MethodId → PFact × AFact → Prop) (seeds : Nat → List (MethodId × Node × PFact))
    (stF stB : Nat → St PO MethodId MethodId)
    (hF0 : Pipeline.Reach (sysD P counted (Ls 0) policy1 sinks roots) (stF 0))
    (hQF0 : (stF 0).Quiescent)
    (hF : ∀ k, Pipeline.Reach
      (sysDR (FSeeds.keepSources P (σ k)) counted (Ls (k + 1)) (dem k) emitM satI restrictU (recs k)
        sinks roots) (stF (k + 1)))
    (hQF : ∀ k, (stF (k + 1)).Quiescent)
    (hB : ∀ k, Pipeline.Reach (sysDB (Program.rev P) counted (LB k) (demB k) emitM satI restrictU
      (recsB k) [] roots (seeds k) true) (stB k))
    (hQB : ∀ k, (stB k).Quiescent)
    (hdemB : ∀ k m d, revSummaryDemand (FSeeds.progSrc P σ k) (result (stF k)) m d → demB k m d)
    (hseeds : ∀ k M n s b, result (stF k) (.vuln M n s b) → (M, n, s) ∈ seeds k)
    (hdem : ∀ k m d, demOf (Program.rev P) (result (stB k)) m d → dem k m d)
    (hσ : ∀ k M n e, FSeeds.srcHit P (result (stB k)) M n e → σ k M n e = true)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : ApSpec.Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, ∃ b, PObj.base (.vuln M n s b) ∈ (stF k).known := by
  have hres : ∀ k, result (stF k) =
      FSeeds.runSeqSrc P counted Ls σ dem emitM satI restrictU recs sinks roots k := by
    intro k
    cases k with
    | zero => exact result_D hF0 hQF0
    | succ k => exact result_DR (hF k) (hQF k)
  have hresB : ∀ k, result (stB k) = DB (Program.rev P) counted (LB k) (demB k) emitM satI
      restrictU (recsB k) [] roots (seeds k) true := fun k => result_DB (hB k) (hQB k)
  have hit := FSeeds.iteration_src hW hT hmr hNZB hZ hX hk σ LB demB recsB seeds
    (fun k m d h => hdemB k m d (by rw [hres k]; exact h))
    (fun k M' n' s' b h => hseeds k M' n' s' b (by rw [hres k]; exact h))
    (fun k m d h => hdem k m d (by rw [hresB k]; exact h))
    (fun k M' n' e h => hσ k M' n' e (by rw [hresB k]; exact h))
    hRe hs hT' hsc
  intro k
  obtain ⟨b, hb⟩ := hit k
  refine ⟨b, ?_⟩
  have : result (stF k) (.vuln M n s b) := by rw [hres k]; exact hb
  exact this

#print axioms driver_iteration_src

end ApSpec.PipelineSeeds

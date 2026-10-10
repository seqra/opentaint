/-
  ApSpec.PipelineHandoffDriver — the iteration driver over the pipeline with the hand-off of the
  DEMAND EDGES only (decision F70) and the `[any-taint]` exclusion (decision F69).

  As `PipelineAnyTaintExDriver.driver_iterationX`, with the new hand-off: run 1 is the encoded
  closure `AnyTaintEx.D6X` (`PipelineAnyTaintEx.sysD6X`, the policy `policy1`); every backward run
  is the encoded closure `Backward.DB` of the reversed program with the INTERSECTION restriction
  `restrictI` (`PipelineAP.sysDB` is generic in the restriction, so no new system); every forward
  restricted run is the encoded closure `AnyTaintEx.DRX` with `emitX`, `satX` and the
  INTERSECTION restriction with the exclusion `restrictIX` (`PipelineAnyTaintEx.sysDRX` is generic
  in the rules). The driver reads a forward run with its exclusions and must flags DROPPED
  (`PipelineAnyTaintExDriver.resultSeqX`: `forget6`, `forgetX`) and its publication from the final
  state (`pubSeqXst`: `pubD` for run 1, `pubRX` for a restricted run).

  Main theorems:
    * `resultSeqX_runSeqNX`, `pubSeqXst_pubSeqNX`: what the driver reads from the complete forward
      runs is the run sequence `HandoffXIter.runSeqNX` with its publications `pubSeqNX`
      (`result_D6X`, `result_DRX`).
    * `driver_iterationNX`: if every run of the driver is complete and the driver computes the new
      hand-offs from the final states (the backward demand contains `handF`, the backward records
      the reversed crossable records, the forward demand contains `demOfN`, the forward base records
      contain `rcNextOf` and the X records embed them), then every forward run of the driver reports
      every real vulnerability, in some layer (`HandoffXIter.iteration_reportsNX`).

  All proofs are constructive (`propext`, `Quot.sound` only; see the `#print axioms` lines).
-/
import ApSpec.HandoffXIter
import ApSpec.PipelineAnyTaintExDriver

namespace ApSpec.PipelineHandoffDriver
open ApSpec ApSpec.Reverse ApSpec.Pipeline ApSpec.PipelineAP ApSpec.Backward ApSpec.PipelineDriver
  ApSpec.AnyTaint ApSpec.AnyTaintEx ApSpec.PipelineAnyTaintEx ApSpec.PipelineAnyTaintExDriver
  ApSpec.Handoff ApSpec.HandoffBackward ApSpec.HandoffX ApSpec.HandoffXIter
open ApSpec.AnyTaintExCov (forget6 forgetX)

/-! ## 1. What the driver reads from the forward runs -/

/-- The publication that the driver reads from forward run `k`: run 1 publishes each exit edge as
    it is (`pubD`); forward restricted run `k + 1` publishes the `restrictIX` pieces of the exit
    edges of its final state, read without the exclusions (`pubRX`). -/
def pubSeqXst (P : Program) (stR : Nat → St XPObj MethodId MethodId)
    (dem : Nat → MethodId → DemandEdge → Prop) : Nat → Pub
  | 0     => pubD
  | k + 1 => pubRX P (resultX (stR k)) (dem k)

/-- COMPLETE FORWARD RUNS GIVE THE RUN SEQUENCE OF THE NEW HAND-OFF: if run 1 is a complete run of
    `sysD6X` and every forward restricted run `k + 1` is a complete run of `sysDRX` with `emitX`,
    `satX`, `restrictIX` (the demand `dem k`, the X records `recsX k`), then what the driver reads
    from forward run `k` is run `k` of `HandoffXIter.runSeqNX`. -/
theorem resultSeqX_runSeqNX {P : Program} {taint : TaintEdges} {counted : Acc → Bool}
    {Ls : Nat → Nat} {dem : Nat → MethodId → DemandEdge → Prop}
    {recsX : Nat → MethodId → PFact × Bool × Excl × XFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    {st1 : St XPObj6 MethodId MethodId} {stR : Nat → St XPObj MethodId MethodId}
    (hF0 : Pipeline.Reach (sysD6X P taint counted (Ls 0) policy1 sinks roots) st1)
    (hQF0 : st1.Quiescent) {k : Nat}
    (hF : ∀ i, i + 1 ≤ k → Pipeline.Reach
      (sysDRX P taint counted (Ls (i + 1)) (dem i) emitX satX restrictIX (recsX i) sinks roots)
      (stR i))
    (hQF : ∀ i, i + 1 ≤ k → (stR i).Quiescent) :
    resultSeqX st1 stR k = runSeqNX P taint counted Ls dem recsX sinks roots k := by
  cases k with
  | zero =>
    show forget6 (resultX6 st1) = forget6 (D6X P taint counted (Ls 0) policy1 sinks roots)
    rw [result_D6X hF0 hQF0]
  | succ i =>
    show forgetX (resultX (stR i)) =
      forgetX (DRX P taint counted (Ls (i + 1)) (dem i) emitX satX restrictIX (recsX i) sinks roots)
    rw [result_DRX (hF i (Nat.le_refl _)) (hQF i (Nat.le_refl _))]

#print axioms resultSeqX_runSeqNX

/-- The publications that the driver reads are those of `HandoffXIter.pubSeqNX`. -/
theorem pubSeqXst_pubSeqNX {P : Program} {taint : TaintEdges} {counted : Acc → Bool}
    {Ls : Nat → Nat} {dem : Nat → MethodId → DemandEdge → Prop}
    {recsX : Nat → MethodId → PFact × Bool × Excl × XFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    {stR : Nat → St XPObj MethodId MethodId} {k : Nat}
    (hF : ∀ i, i + 1 ≤ k → Pipeline.Reach
      (sysDRX P taint counted (Ls (i + 1)) (dem i) emitX satX restrictIX (recsX i) sinks roots)
      (stR i))
    (hQF : ∀ i, i + 1 ≤ k → (stR i).Quiescent) :
    pubSeqXst P stR dem k = pubSeqNX P taint counted Ls dem recsX sinks roots k := by
  cases k with
  | zero => rfl
  | succ i =>
    show pubRX P (resultX (stR i)) (dem i) =
      pubRX P (DRX P taint counted (Ls (i + 1)) (dem i) emitX satX restrictIX (recsX i) sinks
        roots) (dem i)
    rw [result_DRX (hF i (Nat.le_refl _)) (hQF i (Nat.le_refl _))]

#print axioms pubSeqXst_pubSeqNX

/-! ## 2. The driver theorem -/

/-- THE DRIVER THEOREM OF THE NEW HAND-OFF WITH THE EXCLUSION OF `[any-taint]`. `st1` is the final
    state of forward run 1 (a run of `sysD6X`), `stR k` the final state of forward restricted run
    `k + 1` (a run of `sysDRX` with `emitX`, `satX`, `restrictIX`, the demand `dem k` and the X
    records `recsX k`), `stB k` the final state of the backward run after forward run `k` (a run of
    `sysDB` of the reversed program with `emitM`, `satI`, `restrictI`). Every run is complete
    (reachable and quiescent). The driver computes the new hand-offs from the final states (the
    forward runs read with the exclusions and the must flags dropped): the backward demand contains
    `handF` of the forward run before it, with the publication of that run (`pubSeqXst`); the
    backward records contain the reversed crossable records of that run (records it read, or its
    exit edges); the base records `rc (k + 1)` of the next forward run contain `rcNextOf`
    (`NextRecs`), and its X records embed them (`RecsEmbed`); the forward demand contains the
    hand-off `demOfN` of the backward run before it; the seeds contain every vulnerability of the
    forward run. Then every forward run of the driver reports every real vulnerability, in some
    layer. Hypotheses: those of `PipelineAnyTaintExDriver.driver_iterationX` (S10,
    `BindTargetsStar`, `StmtsMarkRev`, `NoZeroBack`, `ZeroKept`, `ExitReach`; the sinks have the tail
    `$` or `[any]`), with the new hand-offs in place of `revSummaryDemand` and `demOf`. -/
theorem driver_iterationNX {P : Program} (hW : P.WF) (hT : BindTargetsStar P)
    (hmr : StmtsMarkRev P) (hNZB : NoZeroBack P) (hZ : ZeroKept P) {roots : List MethodId}
    (hX : ExitReach P roots) {sinks : List (MethodId × Node × PFact)}
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    {taint : TaintEdges} {counted : Acc → Bool} {Ls : Nat → Nat}
    {dem : Nat → MethodId → DemandEdge → Prop}
    {recsX : Nat → MethodId → PFact × Bool × Excl × XFact → Prop}
    (LB : Nat → Nat) (demB : Nat → MethodId → DemandEdge → Prop)
    (recsB : Nat → MethodId → PFact × AFact → Prop) (rc : Nat → Recs)
    (seeds : Nat → List (MethodId × Node × PFact))
    (st1 : St XPObj6 MethodId MethodId) (stR : Nat → St XPObj MethodId MethodId)
    (stB : Nat → St PO MethodId MethodId)
    (hF0 : Pipeline.Reach (sysD6X P taint counted (Ls 0) policy1 sinks roots) st1)
    (hQF0 : st1.Quiescent)
    (hF : ∀ k, Pipeline.Reach
      (sysDRX P taint counted (Ls (k + 1)) (dem k) emitX satX restrictIX (recsX k) sinks roots)
      (stR k))
    (hQF : ∀ k, (stR k).Quiescent)
    (hB : ∀ k, Pipeline.Reach (sysDB (Program.rev P) counted (LB k) (demB k) emitM satI restrictI
      (recsB k) [] roots (seeds k) true) (stB k))
    (hQB : ∀ k, (stB k).Quiescent)
    (hdemB : ∀ k m d, handF P (resultSeqX st1 stR k) (pubSeqXst P stR dem k) m d → demB k m d)
    (hrecB : ∀ k m x, (rc k m x ∨ (resultSeqX st1 stR k (.init m x.1) ∧
        resultSeqX st1 stR k (.edge m x.1 (P.exit m) x.2))) →
      Cross x.1 x.2 → recsB k m (revRec x))
    (hrcN : ∀ k, NextRecs P (resultSeqX st1 stR k) (rc k) (result (stB k)) (rc (k + 1)))
    (hdem : ∀ k m d, demOfN (Program.rev P) (result (stB k)) (pubR (demB k)) m d → dem k m d)
    (hrecX : ∀ k, RecsEmbed (rc (k + 1)) (recsX k))
    (hseeds : ∀ k M n s b, resultSeqX st1 stR k (.vuln M n s b) → (M, n, s) ∈ seeds k)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : ApSpec.Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    (∃ b, XPObj6.base (.vuln M n s b) ∈ st1.known) ∧
      ∀ k, ∃ b, XPObj.base (.vuln M n s b) ∈ (stR k).known := by
  have hres : ∀ k, resultSeqX st1 stR k = runSeqNX P taint counted Ls dem recsX sinks roots k :=
    fun _ => resultSeqX_runSeqNX hF0 hQF0 (fun i _ => hF i) (fun i _ => hQF i)
  have hpub : ∀ k, pubSeqXst P stR dem k = pubSeqNX P taint counted Ls dem recsX sinks roots k :=
    fun _ => pubSeqXst_pubSeqNX (fun i _ => hF i) (fun i _ => hQF i)
  have hresB : ∀ k, result (stB k) = DB (Program.rev P) counted (LB k) (demB k) emitM satI
      restrictI (recsB k) [] roots (seeds k) true := fun k => result_DB (hB k) (hQB k)
  obtain ⟨h1, hR⟩ := iteration_reportsNX (taint := taint) (counted := counted) (Ls := Ls)
    (LB := LB) (dem := dem) (demB := demB) (rc := rc) (recsB := recsB) (recsX := recsX)
    (seeds := seeds) hW hT hmr hNZB hZ hX hk
    (fun k m d h => hdemB k m d (by rw [hres k, hpub k]; exact h))
    (fun k m x h hc => hrecB k m x (by rw [hres k]; exact h) hc)
    (fun k => by have h := hrcN k; rw [hres k, hresB k] at h; exact h)
    (fun k m d h => hdem k m d (by rw [hresB k]; exact h))
    hrecX
    (fun k M' n' s' b h => hseeds k M' n' s' b (by rw [hres k]; exact h))
    hRe hs hT' hsc
  refine ⟨?_, fun k => ?_⟩
  · obtain ⟨b, hb⟩ := h1
    refine ⟨b, ?_⟩
    have : resultX6 st1 (.vuln M n s b) := by rw [result_D6X hF0 hQF0]; exact hb
    exact this
  · obtain ⟨b, hb⟩ := hR k
    refine ⟨b, ?_⟩
    have : resultX (stR k) (.vuln M n s b) := by rw [result_DRX (hF k) (hQF k)]; exact hb
    exact this

#print axioms driver_iterationNX

end ApSpec.PipelineHandoffDriver

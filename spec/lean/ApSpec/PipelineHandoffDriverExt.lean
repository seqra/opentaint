/-
  ApSpec.PipelineHandoffDriverExt — the driver of `analyzer-core.md` §7.1 over the pipeline with the
  hand-off of the DEMAND EDGES only (decision F70) and the `[any-taint]` exclusion (decision F69):
  the three forms that `PipelineHandoffDriver.driver_iterationNX` does not give.

  1. THE DEMAND-ONLY SEEDS (`driver_iterationNX_demand`). The backward run after forward run `k`
     seeds only the vulnerabilities that are not CONFIRMED: every vulnerability that the driver
     reads from forward run `k` is confirmed (`C k`, any predicate; the driver uses "confirmed by
     some forward run up to `k`") or seeded. Then every real vulnerability is, at every forward run
     `k` of the driver, reported by run `k` or confirmed by an earlier run. With `C` = "a forward
     run up to `k` reports it in the normal layer": `driver_iterationNX_confirmed`. The forms on
     the final states: `driver_iterationNX_demand_known` (and the general conversions
     `known_of_resultSeqX`, `known_of_resultSeqX_upto`).
  2. THE FINITE FORM (`driver_iterationNX_upto`). The driver stops after forward run `K`: only
     forward run 1, the forward restricted runs `stR 0` to `stR (K - 1)` and the backward runs
     `stB 0` to `stB (K - 1)` must be complete, and the hand-offs hold between them. Then every
     forward run `k ≤ K` reports every real vulnerability, or an earlier run confirmed it
     (`HandoffUpto.iteration_generalNX_upto`; no extension of the sequence after `K`).
  3. THE SOURCE SEEDS (`driver_iteration_srcNX`, finite form `driver_iteration_srcNX_upto`):
     forward restricted run `k + 1` is a run of `sysDRX` on `FSeeds.keepSources P (σ k)`, and `σ k`
     contains the source hits of backward run `k` (`HandoffSrc.iteration_srcNX`).

  All proofs are constructive (`propext`, `Quot.sound` only).
-/
import ApSpec.PipelineHandoffDriver
import ApSpec.HandoffSrc

namespace ApSpec.PipelineHandoffDriverExt
open ApSpec ApSpec.Reverse ApSpec.Pipeline ApSpec.PipelineAP ApSpec.Backward ApSpec.PipelineDriver
  ApSpec.AnyTaint ApSpec.AnyTaintEx ApSpec.PipelineAnyTaintEx ApSpec.PipelineAnyTaintExDriver
  ApSpec.Handoff ApSpec.HandoffBackward ApSpec.HandoffX ApSpec.PipelineHandoffDriver
open ApSpec.AnyTaintExCov (forget6 forgetX)
open ApSpec.HandoffXIter (runSeqNX pubSeqNX iteration_generalNX_incl)

/-! ## 0. From the driver's read of a forward run to the final states -/

/-- The conclusion on what the driver reads (`resultSeqX`) gives the conclusion on the final
    states: forward run 1 reports the vulnerability (no run is before it), and forward restricted
    run `k + 1` reports it or a run up to `k` confirmed it. -/
theorem known_of_resultSeqX {st1 : St XPObj6 MethodId MethodId}
    {stR : Nat → St XPObj MethodId MethodId} {C : Nat → MethodId → Node → PFact → Prop}
    {M : MethodId} {n : Node} {s : PFact}
    (h : ∀ k, (∃ k', k' < k ∧ C k' M n s) ∨ ∃ b, resultSeqX st1 stR k (.vuln M n s b)) :
    (∃ b, XPObj6.base (.vuln M n s b) ∈ st1.known) ∧
    ∀ k, (∃ k', k' ≤ k ∧ C k' M n s) ∨ ∃ b, XPObj.base (.vuln M n s b) ∈ (stR k).known := by
  refine ⟨?_, fun k => ?_⟩
  · rcases h 0 with ⟨_, hk', _⟩ | ⟨b, hb⟩
    · exact absurd hk' (Nat.not_lt_zero _)
    · exact ⟨b, resultSeqX_vuln_zero.1 hb⟩
  · rcases h (k + 1) with ⟨k', hk', hC⟩ | ⟨b, hb⟩
    · exact Or.inl ⟨k', Nat.le_of_lt_succ hk', hC⟩
    · exact Or.inr ⟨b, resultSeqX_vuln_succ.1 hb⟩

#print axioms known_of_resultSeqX

/-- The same for a finite sequence (forward runs up to `K`). -/
theorem known_of_resultSeqX_upto {st1 : St XPObj6 MethodId MethodId}
    {stR : Nat → St XPObj MethodId MethodId} {C : Nat → MethodId → Node → PFact → Prop}
    {M : MethodId} {n : Node} {s : PFact} {K : Nat}
    (h : ∀ k, k ≤ K → (∃ k', k' < k ∧ C k' M n s) ∨ ∃ b, resultSeqX st1 stR k (.vuln M n s b)) :
    (∃ b, XPObj6.base (.vuln M n s b) ∈ st1.known) ∧
    ∀ k, k + 1 ≤ K →
      (∃ k', k' ≤ k ∧ C k' M n s) ∨ ∃ b, XPObj.base (.vuln M n s b) ∈ (stR k).known := by
  refine ⟨?_, fun k hk => ?_⟩
  · rcases h 0 (Nat.zero_le _) with ⟨_, hk', _⟩ | ⟨b, hb⟩
    · exact absurd hk' (Nat.not_lt_zero _)
    · exact ⟨b, resultSeqX_vuln_zero.1 hb⟩
  · rcases h (k + 1) hk with ⟨k', hk', hC⟩ | ⟨b, hb⟩
    · exact Or.inl ⟨k', Nat.le_of_lt_succ hk', hC⟩
    · exact Or.inr ⟨b, resultSeqX_vuln_succ.1 hb⟩

#print axioms known_of_resultSeqX_upto

/-! ## 1. The demand-only seeds -/

/-- THE DRIVER THEOREM OF THE NEW HAND-OFF WITH THE DEMAND-ONLY SEEDS. The runs and the hand-offs
    as `PipelineHandoffDriver.driver_iterationNX` (every run complete; the backward demand contains
    `handF`, the backward records the reversed crossable records, the forward demand `demOfN`, the
    forward base records `rcNextOf` (`NextRecs`), the X records embed them), but the seeds of the
    backward run after forward run `k` need only contain the vulnerabilities that are not
    confirmed: every vulnerability that the driver reads from forward run `k` is confirmed
    (`C k`) or seeded. Then every real vulnerability is, at every forward run `k` of the driver
    (`resultSeqX st1 stR k`), reported by run `k` or confirmed by an earlier run. -/
theorem driver_iterationNX_demand {P : Program} (hW : P.WF) (hT : BindTargetsStar P)
    (hmr : StmtsMarkRev P) (hNZB : NoZeroBack P) (hZ : ZeroKept P) {roots : List MethodId}
    (hX : ExitReach P roots) {sinks : List (MethodId × Node × PFact)}
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    {taint : TaintEdges} {counted : Acc → Bool} {Ls : Nat → Nat}
    {dem : Nat → MethodId → DemandEdge → Prop}
    {recsX : Nat → MethodId → PFact × Bool × Excl × XFact → Prop}
    (LB : Nat → Nat) (demB : Nat → MethodId → DemandEdge → Prop)
    (recsB : Nat → MethodId → PFact × AFact → Prop) (rc : Nat → Recs)
    (seeds : Nat → List (MethodId × Node × PFact)) {C : Nat → MethodId → Node → PFact → Prop}
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
    (hseeds : ∀ k M n s b, resultSeqX st1 stR k (.vuln M n s b) →
      C k M n s ∨ (M, n, s) ∈ seeds k)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : ApSpec.Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, (∃ k', k' < k ∧ C k' M n s) ∨ ∃ b, resultSeqX st1 stR k (.vuln M n s b) := by
  have hres : ∀ k, resultSeqX st1 stR k = runSeqNX P taint counted Ls dem recsX sinks roots k :=
    fun _ => resultSeqX_runSeqNX hF0 hQF0 (fun i _ => hF i) (fun i _ => hQF i)
  have hpub : ∀ k, pubSeqXst P stR dem k = pubSeqNX P taint counted Ls dem recsX sinks roots k :=
    fun _ => pubSeqXst_pubSeqNX (fun i _ => hF i) (fun i _ => hQF i)
  have hresB : ∀ k, result (stB k) = DB (Program.rev P) counted (LB k) (demB k) emitM satI
      restrictI (recsB k) [] roots (seeds k) true := fun k => result_DB (hB k) (hQB k)
  intro k
  have h := iteration_generalNX_incl (taint := taint) (counted := counted) (Ls := Ls) (LB := LB)
    (dem := dem) (demB := demB) (rc := rc) (recsB := recsB) (recsX := recsX) (seeds := seeds)
    (C := C) hW hT hmr hNZB hZ hX hk
    (fun k m d h => hdemB k m d (by rw [hres k, hpub k]; exact h))
    (fun k m x h hc => hrecB k m x (by rw [hres k]; exact h) hc)
    (fun k => by have h := hrcN k; rw [hres k, hresB k] at h; exact h)
    (fun k m d h => hdem k m d (by rw [hresB k]; exact h))
    hrecX
    (fun k M' n' s' b h => hseeds k M' n' s' b (by rw [hres k]; exact h))
    hRe hs hT' hsc k
  rw [hres k]
  exact h

#print axioms driver_iterationNX_demand

/-- THE DRIVER THEOREM WITH THE DEMAND-ONLY SEEDS, ON THE FINAL STATES: forward run 1 reports every
    real vulnerability, and every forward restricted run `stR k` reports it or a forward run up to
    `k` confirmed it. Hypotheses: those of `driver_iterationNX_demand`. -/
theorem driver_iterationNX_demand_known {P : Program} (hW : P.WF) (hT : BindTargetsStar P)
    (hmr : StmtsMarkRev P) (hNZB : NoZeroBack P) (hZ : ZeroKept P) {roots : List MethodId}
    (hX : ExitReach P roots) {sinks : List (MethodId × Node × PFact)}
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    {taint : TaintEdges} {counted : Acc → Bool} {Ls : Nat → Nat}
    {dem : Nat → MethodId → DemandEdge → Prop}
    {recsX : Nat → MethodId → PFact × Bool × Excl × XFact → Prop}
    (LB : Nat → Nat) (demB : Nat → MethodId → DemandEdge → Prop)
    (recsB : Nat → MethodId → PFact × AFact → Prop) (rc : Nat → Recs)
    (seeds : Nat → List (MethodId × Node × PFact)) {C : Nat → MethodId → Node → PFact → Prop}
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
    (hseeds : ∀ k M n s b, resultSeqX st1 stR k (.vuln M n s b) →
      C k M n s ∨ (M, n, s) ∈ seeds k)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : ApSpec.Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    (∃ b, XPObj6.base (.vuln M n s b) ∈ st1.known) ∧
    ∀ k, (∃ k', k' ≤ k ∧ C k' M n s) ∨ ∃ b, XPObj.base (.vuln M n s b) ∈ (stR k).known :=
  known_of_resultSeqX (driver_iterationNX_demand hW hT hmr hNZB hZ hX hk LB demB recsB rc seeds
    st1 stR stB hF0 hQF0 hF hQF hB hQB hdemB hrecB hrcN hdem hrecX hseeds hRe hs hT' hsc)

#print axioms driver_iterationNX_demand_known

/-- THE DRIVER THEOREM WITH THE SEEDS OF THE DEMAND VULNERABILITIES (`analyzer-core.md` §7.3: the
    report state DEMAND). `C k` is "a forward run up to `k` reports the vulnerability in the normal
    layer" (CONFIRMED is final). If every vulnerability that the driver reads from forward run `k`
    is confirmed by a forward run up to `k` or seeded, then every real vulnerability is, at every
    forward run `k`, reported by run `k` or reported in the normal layer by an earlier run.
    Hypotheses: those of `driver_iterationNX_demand`. -/
theorem driver_iterationNX_confirmed {P : Program} (hW : P.WF) (hT : BindTargetsStar P)
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
    (hseeds : ∀ k M n s b, resultSeqX st1 stR k (.vuln M n s b) →
      (∃ k', k' ≤ k ∧ resultSeqX st1 stR k' (.vuln M n s false)) ∨ (M, n, s) ∈ seeds k)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : ApSpec.Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, (∃ k', k' < k ∧ resultSeqX st1 stR k' (.vuln M n s false)) ∨
      ∃ b, resultSeqX st1 stR k (.vuln M n s b) := by
  intro k
  rcases driver_iterationNX_demand
      (C := fun k M n s => ∃ k', k' ≤ k ∧ resultSeqX st1 stR k' (.vuln M n s false))
      hW hT hmr hNZB hZ hX hk LB demB recsB rc seeds st1 stR stB hF0 hQF0 hF hQF hB hQB hdemB hrecB
      hrcN hdem hrecX hseeds hRe hs hT' hsc k with ⟨k', hk', k'', hk'', hc⟩ | h
  · exact Or.inl ⟨k'', Nat.lt_of_le_of_lt hk'' hk', hc⟩
  · exact Or.inr h

#print axioms driver_iterationNX_confirmed

/-! ## 2. The finite form: the driver stops after forward run `K` -/

/-- THE DRIVER THEOREM OF THE NEW HAND-OFF FOR A FINITE SEQUENCE. The driver stops after forward
    run `K`. Let the runs up to it be complete: forward run 1 `st1`, the forward restricted runs
    `stR 0` to `stR (K - 1)`, the backward runs `stB 0` to `stB (K - 1)`, with the hand-offs of
    `driver_iterationNX_demand` between them (and the demand-only seeds). Then every real
    vulnerability is, at every forward run `k ≤ K` of the driver, reported by run `k` or confirmed
    by an earlier run. The final states after `K` are not read. -/
theorem driver_iterationNX_upto {P : Program} (hW : P.WF) (hT : BindTargetsStar P)
    (hmr : StmtsMarkRev P) (hNZB : NoZeroBack P) (hZ : ZeroKept P) {roots : List MethodId}
    (hX : ExitReach P roots) {sinks : List (MethodId × Node × PFact)}
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    {taint : TaintEdges} {counted : Acc → Bool} {Ls : Nat → Nat}
    {dem : Nat → MethodId → DemandEdge → Prop}
    {recsX : Nat → MethodId → PFact × Bool × Excl × XFact → Prop}
    (LB : Nat → Nat) (demB : Nat → MethodId → DemandEdge → Prop)
    (recsB : Nat → MethodId → PFact × AFact → Prop) (rc : Nat → Recs)
    (seeds : Nat → List (MethodId × Node × PFact)) {C : Nat → MethodId → Node → PFact → Prop}
    (K : Nat) (st1 : St XPObj6 MethodId MethodId) (stR : Nat → St XPObj MethodId MethodId)
    (stB : Nat → St PO MethodId MethodId)
    (hF0 : Pipeline.Reach (sysD6X P taint counted (Ls 0) policy1 sinks roots) st1)
    (hQF0 : st1.Quiescent)
    (hF : ∀ k, k + 1 ≤ K → Pipeline.Reach
      (sysDRX P taint counted (Ls (k + 1)) (dem k) emitX satX restrictIX (recsX k) sinks roots)
      (stR k))
    (hQF : ∀ k, k + 1 ≤ K → (stR k).Quiescent)
    (hB : ∀ k, k < K → Pipeline.Reach (sysDB (Program.rev P) counted (LB k) (demB k) emitM satI
      restrictI (recsB k) [] roots (seeds k) true) (stB k))
    (hQB : ∀ k, k < K → (stB k).Quiescent)
    (hdemB : ∀ k, k < K → ∀ m d,
      handF P (resultSeqX st1 stR k) (pubSeqXst P stR dem k) m d → demB k m d)
    (hrecB : ∀ k, k < K → ∀ m x, (rc k m x ∨ (resultSeqX st1 stR k (.init m x.1) ∧
        resultSeqX st1 stR k (.edge m x.1 (P.exit m) x.2))) →
      Cross x.1 x.2 → recsB k m (revRec x))
    (hrcN : ∀ k, k < K → NextRecs P (resultSeqX st1 stR k) (rc k) (result (stB k)) (rc (k + 1)))
    (hdem : ∀ k, k < K → ∀ m d,
      demOfN (Program.rev P) (result (stB k)) (pubR (demB k)) m d → dem k m d)
    (hrecX : ∀ k, k < K → RecsEmbed (rc (k + 1)) (recsX k))
    (hseeds : ∀ k, k < K → ∀ M n s b, resultSeqX st1 stR k (.vuln M n s b) →
      C k M n s ∨ (M, n, s) ∈ seeds k)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : ApSpec.Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, k ≤ K → (∃ k', k' < k ∧ C k' M n s) ∨ ∃ b, resultSeqX st1 stR k (.vuln M n s b) := by
  have hres : ∀ k, k ≤ K →
      resultSeqX st1 stR k = runSeqNX P taint counted Ls dem recsX sinks roots k :=
    fun _ hkK => resultSeqX_runSeqNX hF0 hQF0 (fun i hi => hF i (Nat.le_trans hi hkK))
      (fun i hi => hQF i (Nat.le_trans hi hkK))
  have hpub : ∀ k, k ≤ K →
      pubSeqXst P stR dem k = pubSeqNX P taint counted Ls dem recsX sinks roots k :=
    fun _ hkK => pubSeqXst_pubSeqNX (fun i hi => hF i (Nat.le_trans hi hkK))
      (fun i hi => hQF i (Nat.le_trans hi hkK))
  have hresB : ∀ k, k < K → result (stB k) = DB (Program.rev P) counted (LB k) (demB k) emitM
      satI restrictI (recsB k) [] roots (seeds k) true :=
    fun k hkK => result_DB (hB k hkK) (hQB k hkK)
  intro k hkK
  have h := HandoffUpto.iteration_generalNX_upto (taint := taint) (counted := counted) (Ls := Ls)
    (LB := LB) (dem := dem) (demB := demB) (rc := rc) (recsB := recsB) (recsX := recsX)
    (seeds := seeds) (C := C) hW hT hmr hNZB hZ hX hk K
    (fun k hk m d h => hdemB k hk m d
      (by rw [hres k (Nat.le_of_lt hk), hpub k (Nat.le_of_lt hk)]; exact h))
    (fun k hk m x h hc => hrecB k hk m x (by rw [hres k (Nat.le_of_lt hk)]; exact h) hc)
    (fun k hk => by
      have h := hrcN k hk
      rw [hres k (Nat.le_of_lt hk), hresB k hk] at h
      exact h)
    (fun k hk m d h => hdem k hk m d (by rw [hresB k hk]; exact h))
    hrecX
    (fun k hk M' n' s' b h => hseeds k hk M' n' s' b (by rw [hres k (Nat.le_of_lt hk)]; exact h))
    hRe hs hT' hsc k hkK
  rw [hres k hkK]
  exact h

#print axioms driver_iterationNX_upto

/-! ## 3. The source seeds -/

/-- COMPLETE FORWARD RUNS WITH SOURCE SEEDS GIVE THE SEQUENCE `HandoffSrc.runSeqSrcNX`: forward run
    1 is a complete run of `sysD6X` on `P`, forward restricted run `k + 1` a complete run of
    `sysDRX` on `keepSources P (σ k)` with `emitX`, `satX`, `restrictIX`. -/
theorem resultSeqX_runSeqSrcNX {P : Program} {taint : TaintEdges} {counted : Acc → Bool}
    {Ls : Nat → Nat} {σ : Nat → MethodId → Node → MicroEdge → Bool}
    {dem : Nat → MethodId → DemandEdge → Prop}
    {recsX : Nat → MethodId → PFact × Bool × Excl × XFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    {st1 : St XPObj6 MethodId MethodId} {stR : Nat → St XPObj MethodId MethodId}
    (hF0 : Pipeline.Reach (sysD6X P taint counted (Ls 0) policy1 sinks roots) st1)
    (hQF0 : st1.Quiescent) {k : Nat}
    (hF : ∀ i, i + 1 ≤ k → Pipeline.Reach
      (sysDRX (FSeeds.keepSources P (σ i)) taint counted (Ls (i + 1)) (dem i) emitX satX restrictIX
        (recsX i) sinks roots) (stR i))
    (hQF : ∀ i, i + 1 ≤ k → (stR i).Quiescent) :
    resultSeqX st1 stR k = HandoffSrc.runSeqSrcNX P taint counted Ls σ dem recsX sinks roots k := by
  cases k with
  | zero =>
    show forget6 (resultX6 st1) = forget6 (D6X P taint counted (Ls 0) policy1 sinks roots)
    rw [result_D6X hF0 hQF0]
  | succ i =>
    show forgetX (resultX (stR i)) =
      forgetX (DRX (FSeeds.keepSources P (σ i)) taint counted (Ls (i + 1)) (dem i) emitX satX
        restrictIX (recsX i) sinks roots)
    rw [result_DRX (hF i (Nat.le_refl _)) (hQF i (Nat.le_refl _))]

#print axioms resultSeqX_runSeqSrcNX

/-- The publications that the driver reads are those of `HandoffSrc.pubSeqSrcNX`. -/
theorem pubSeqXst_pubSeqSrcNX {P : Program} {taint : TaintEdges} {counted : Acc → Bool}
    {Ls : Nat → Nat} {σ : Nat → MethodId → Node → MicroEdge → Bool}
    {dem : Nat → MethodId → DemandEdge → Prop}
    {recsX : Nat → MethodId → PFact × Bool × Excl × XFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    {stR : Nat → St XPObj MethodId MethodId} {k : Nat}
    (hF : ∀ i, i + 1 ≤ k → Pipeline.Reach
      (sysDRX (FSeeds.keepSources P (σ i)) taint counted (Ls (i + 1)) (dem i) emitX satX restrictIX
        (recsX i) sinks roots) (stR i))
    (hQF : ∀ i, i + 1 ≤ k → (stR i).Quiescent) :
    pubSeqXst P stR dem k = HandoffSrc.pubSeqSrcNX P taint counted Ls σ dem recsX sinks roots k := by
  cases k with
  | zero => rfl
  | succ i =>
    show pubRX P (resultX (stR i)) (dem i) =
      pubRX P (DRX (FSeeds.keepSources P (σ i)) taint counted (Ls (i + 1)) (dem i) emitX satX
        restrictIX (recsX i) sinks roots) (dem i)
    rw [result_DRX (hF i (Nat.le_refl _)) (hQF i (Nat.le_refl _))]

#print axioms pubSeqXst_pubSeqSrcNX

/-- THE DRIVER THEOREM OF THE NEW HAND-OFF WITH THE SOURCE SEEDS (and the demand-only sink seeds).
    `st1` is forward run 1 (`sysD6X` on the full program), `stR k` forward restricted run `k + 1`
    (`sysDRX` with the spec rules on `FSeeds.keepSources P (σ k)`: only the seeded unconditional
    sources fire), `stB k` the backward run after forward run `k` (`sysDB` on the full reversed
    program). Every run is complete. The driver computes the new hand-offs from the final states
    (as `driver_iterationNX_demand`), and the source seeds `σ k` contain the source hits of
    backward run `k`. Then every real vulnerability of `P` is, at every forward run `k` of the
    driver, reported by run `k` or confirmed by an earlier run (`HandoffSrc.iteration_srcNX`). -/
theorem driver_iteration_srcNX {P : Program} (hW : P.WF) (hT : BindTargetsStar P)
    (hmr : StmtsMarkRev P) (hNZB : NoZeroBack P) (hZ : ZeroKept P) {roots : List MethodId}
    (hX : ExitReach P roots) {sinks : List (MethodId × Node × PFact)}
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    {taint : TaintEdges} {counted : Acc → Bool} {Ls : Nat → Nat}
    {dem : Nat → MethodId → DemandEdge → Prop}
    {recsX : Nat → MethodId → PFact × Bool × Excl × XFact → Prop}
    (σ : Nat → MethodId → Node → MicroEdge → Bool)
    (LB : Nat → Nat) (demB : Nat → MethodId → DemandEdge → Prop)
    (recsB : Nat → MethodId → PFact × AFact → Prop) (rc : Nat → Recs)
    (seeds : Nat → List (MethodId × Node × PFact)) {C : Nat → MethodId → Node → PFact → Prop}
    (st1 : St XPObj6 MethodId MethodId) (stR : Nat → St XPObj MethodId MethodId)
    (stB : Nat → St PO MethodId MethodId)
    (hF0 : Pipeline.Reach (sysD6X P taint counted (Ls 0) policy1 sinks roots) st1)
    (hQF0 : st1.Quiescent)
    (hF : ∀ k, Pipeline.Reach
      (sysDRX (FSeeds.keepSources P (σ k)) taint counted (Ls (k + 1)) (dem k) emitX satX
        restrictIX (recsX k) sinks roots) (stR k))
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
    (hσ : ∀ k M n e, FSeeds.srcHit P (result (stB k)) M n e → σ k M n e = true)
    (hseeds : ∀ k M n s b, resultSeqX st1 stR k (.vuln M n s b) →
      C k M n s ∨ (M, n, s) ∈ seeds k)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : ApSpec.Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, (∃ k', k' < k ∧ C k' M n s) ∨ ∃ b, resultSeqX st1 stR k (.vuln M n s b) := by
  have hres : ∀ k, resultSeqX st1 stR k =
      HandoffSrc.runSeqSrcNX P taint counted Ls σ dem recsX sinks roots k :=
    fun _ => resultSeqX_runSeqSrcNX hF0 hQF0 (fun i _ => hF i) (fun i _ => hQF i)
  have hpub : ∀ k, pubSeqXst P stR dem k =
      HandoffSrc.pubSeqSrcNX P taint counted Ls σ dem recsX sinks roots k :=
    fun _ => pubSeqXst_pubSeqSrcNX (fun i _ => hF i) (fun i _ => hQF i)
  have hresB : ∀ k, result (stB k) = DB (Program.rev P) counted (LB k) (demB k) emitM satI
      restrictI (recsB k) [] roots (seeds k) true := fun k => result_DB (hB k) (hQB k)
  intro k
  have h := HandoffSrc.iteration_srcNX (taint := taint) (counted := counted) (Ls := Ls) (LB := LB)
    (σ := σ) (dem := dem) (demB := demB) (rc := rc) (recsB := recsB) (recsX := recsX)
    (seeds := seeds) (C := C) hW hT hmr hNZB hZ hX hk
    (fun k m d h => hdemB k m d (by rw [hres k, hpub k]; exact h))
    (fun k m x h hc => hrecB k m x (by rw [hres k]; exact h) hc)
    (fun k => by have h := hrcN k; rw [hres k, hresB k] at h; exact h)
    (fun k m d h => hdem k m d (by rw [hresB k]; exact h))
    hrecX
    (fun k M' n' e h => hσ k M' n' e (by rw [hresB k]; exact h))
    (fun k M' n' s' b h => hseeds k M' n' s' b (by rw [hres k]; exact h))
    hRe hs hT' hsc k
  rw [hres k]
  exact h

#print axioms driver_iteration_srcNX

/-- THE DRIVER THEOREM WITH THE SOURCE SEEDS, FINITE FORM: the driver stops after forward run `K`;
    only the runs up to it are complete and the hand-offs and the source seeds hold between them.
    Then every real vulnerability of `P` is, at every forward run `k ≤ K` of the driver, reported
    by run `k` or confirmed by an earlier run (`HandoffSrc.iteration_srcNX_upto`). -/
theorem driver_iteration_srcNX_upto {P : Program} (hW : P.WF) (hT : BindTargetsStar P)
    (hmr : StmtsMarkRev P) (hNZB : NoZeroBack P) (hZ : ZeroKept P) {roots : List MethodId}
    (hX : ExitReach P roots) {sinks : List (MethodId × Node × PFact)}
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    {taint : TaintEdges} {counted : Acc → Bool} {Ls : Nat → Nat}
    {dem : Nat → MethodId → DemandEdge → Prop}
    {recsX : Nat → MethodId → PFact × Bool × Excl × XFact → Prop}
    (σ : Nat → MethodId → Node → MicroEdge → Bool)
    (LB : Nat → Nat) (demB : Nat → MethodId → DemandEdge → Prop)
    (recsB : Nat → MethodId → PFact × AFact → Prop) (rc : Nat → Recs)
    (seeds : Nat → List (MethodId × Node × PFact)) {C : Nat → MethodId → Node → PFact → Prop}
    (K : Nat) (st1 : St XPObj6 MethodId MethodId) (stR : Nat → St XPObj MethodId MethodId)
    (stB : Nat → St PO MethodId MethodId)
    (hF0 : Pipeline.Reach (sysD6X P taint counted (Ls 0) policy1 sinks roots) st1)
    (hQF0 : st1.Quiescent)
    (hF : ∀ k, k + 1 ≤ K → Pipeline.Reach
      (sysDRX (FSeeds.keepSources P (σ k)) taint counted (Ls (k + 1)) (dem k) emitX satX
        restrictIX (recsX k) sinks roots) (stR k))
    (hQF : ∀ k, k + 1 ≤ K → (stR k).Quiescent)
    (hB : ∀ k, k < K → Pipeline.Reach (sysDB (Program.rev P) counted (LB k) (demB k) emitM satI
      restrictI (recsB k) [] roots (seeds k) true) (stB k))
    (hQB : ∀ k, k < K → (stB k).Quiescent)
    (hdemB : ∀ k, k < K → ∀ m d,
      handF P (resultSeqX st1 stR k) (pubSeqXst P stR dem k) m d → demB k m d)
    (hrecB : ∀ k, k < K → ∀ m x, (rc k m x ∨ (resultSeqX st1 stR k (.init m x.1) ∧
        resultSeqX st1 stR k (.edge m x.1 (P.exit m) x.2))) →
      Cross x.1 x.2 → recsB k m (revRec x))
    (hrcN : ∀ k, k < K → NextRecs P (resultSeqX st1 stR k) (rc k) (result (stB k)) (rc (k + 1)))
    (hdem : ∀ k, k < K → ∀ m d,
      demOfN (Program.rev P) (result (stB k)) (pubR (demB k)) m d → dem k m d)
    (hrecX : ∀ k, k < K → RecsEmbed (rc (k + 1)) (recsX k))
    (hσ : ∀ k, k < K → ∀ M n e, FSeeds.srcHit P (result (stB k)) M n e → σ k M n e = true)
    (hseeds : ∀ k, k < K → ∀ M n s b, resultSeqX st1 stR k (.vuln M n s b) →
      C k M n s ∨ (M, n, s) ∈ seeds k)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : ApSpec.Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, k ≤ K → (∃ k', k' < k ∧ C k' M n s) ∨ ∃ b, resultSeqX st1 stR k (.vuln M n s b) := by
  have hres : ∀ k, k ≤ K → resultSeqX st1 stR k =
      HandoffSrc.runSeqSrcNX P taint counted Ls σ dem recsX sinks roots k :=
    fun _ hkK => resultSeqX_runSeqSrcNX hF0 hQF0 (fun i hi => hF i (Nat.le_trans hi hkK))
      (fun i hi => hQF i (Nat.le_trans hi hkK))
  have hpub : ∀ k, k ≤ K → pubSeqXst P stR dem k =
      HandoffSrc.pubSeqSrcNX P taint counted Ls σ dem recsX sinks roots k :=
    fun _ hkK => pubSeqXst_pubSeqSrcNX (fun i hi => hF i (Nat.le_trans hi hkK))
      (fun i hi => hQF i (Nat.le_trans hi hkK))
  have hresB : ∀ k, k < K → result (stB k) = DB (Program.rev P) counted (LB k) (demB k) emitM
      satI restrictI (recsB k) [] roots (seeds k) true :=
    fun k hkK => result_DB (hB k hkK) (hQB k hkK)
  intro k hkK
  have h := HandoffSrc.iteration_srcNX_upto (taint := taint) (counted := counted) (Ls := Ls)
    (LB := LB) (σ := σ) (dem := dem) (demB := demB) (rc := rc) (recsB := recsB) (recsX := recsX)
    (seeds := seeds) (C := C) hW hT hmr hNZB hZ hX hk K
    (fun k hk m d h => hdemB k hk m d
      (by rw [hres k (Nat.le_of_lt hk), hpub k (Nat.le_of_lt hk)]; exact h))
    (fun k hk m x h hc => hrecB k hk m x (by rw [hres k (Nat.le_of_lt hk)]; exact h) hc)
    (fun k hk => by
      have h := hrcN k hk
      rw [hres k (Nat.le_of_lt hk), hresB k hk] at h
      exact h)
    (fun k hk m d h => hdem k hk m d (by rw [hresB k hk]; exact h))
    hrecX
    (fun k hk M' n' e h => hσ k hk M' n' e (by rw [hresB k hk]; exact h))
    (fun k hk M' n' s' b h => hseeds k hk M' n' s' b (by rw [hres k (Nat.le_of_lt hk)]; exact h))
    hRe hs hT' hsc k hkK
  rw [hres k hkK]
  exact h

#print axioms driver_iteration_srcNX_upto

end ApSpec.PipelineHandoffDriverExt

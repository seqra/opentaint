/-
  ApSpec.HandoffXIter — the iteration of the hand-off of the DEMAND EDGES only (decision F70) on the
  spec closures WITH THE `[any-taint]` EXCLUSION (decision F69).

  Part 1. THE CANONICAL X RUN SEQUENCE (`canonStateX`), by recursion over the state of a forward run
    (its result read on the forgotten view, its publication, its base record set):
      * run 0: `forget6 (D6X P taint counted (Ls 0) policy1 sinks roots)`, the publication `pubD`, no
        record;
      * the backward run after forward run `k` (`backOfX`, the base model of agent B):
          `DB (Program.rev P) counted (LB k) (handF P (R k) (pub k)) emitM satI restrictI
             (recsBOf P (R k) (rc k)) [] roots (seeds k) true`;
      * the demand of run `k + 1` (`demOfX`): `demOfN (Program.rev P) DBk (pubR (handF …))`;
      * the base records of run `k + 1` (`rcOfX`): `rcNextOf P (R k) (rc k) DBk`, read by the X run as
        the X records `embedRecs` (`(j, false, Excl.empty, ⟨g, Excl.empty⟩)`);
      * run `k + 1`: `forgetX (DRX P taint counted (Ls (k + 1)) (dem k) emitX satX restrictIX
        (embedRecs (rc (k + 1))) sinks roots)`, the publication `pubRX P DRX… (dem k)`.
    The seeds `seeds k` are a parameter: every vulnerability that run `k` reports is confirmed (a
    predicate `C k`) or seeded.
  Part 2. THE ITERATION (`iteration_generalNX`), from `HandoffIter.iteration_abstract_or`,
    `HandoffBackward.B_generalN_canon` (generic in the forward run and its publication) and the X
    coverage (`HandoffXCoverage.coversN_DRXI`, `run0X_contract`): every real vulnerability (a sink
    pattern with a concrete mark and the tail `$` or `[any]`) is, at every forward run `k`, reported
    by run `k` or confirmed by an earlier run. `iteration_generalNX_all`, `iteration_reportsNX_canon`:
    with every reported vulnerability seeded, every forward run reports every real vulnerability.
  Part 3. THE INCLUSION FORM (`iteration_generalNX_incl`, the cited form `iteration_reportsNX`):
    hypotheses as `AnyTaintExCov.iteration_reportsX`: the driver may hand off MORE demand edges and
    MORE records than the canonical sets.

  All proofs are constructive (`propext`, `Quot.sound` only).
-/
import ApSpec.HandoffXCoverage
import ApSpec.HandoffBackward
import ApSpec.HandoffIter

namespace ApSpec.HandoffXIter
open ApSpec ApSpec.Reverse ApSpec.Backward ApSpec.Handoff ApSpec.HandoffBackward ApSpec.HandoffIter
  ApSpec.HandoffX ApSpec.AnyTaint ApSpec.AnyTaintEx
open ApSpec.AnyTaintExCov (forgetX forget6)

/-! ## 0. Monotonicity (copies of the lemmas of `HandoffMain.lean`, under other names) -/

/-- A larger demand and more records keep a demanded-or-recorded flow. -/
theorem flowRR_monoX {P : Program} {d1 d2 : MethodId → DemandEdge → Prop} {rc1 rc2 : Recs}
    (h : ∀ m e, d1 m e → d2 m e) (hr : ∀ m x, rc1 m x → rc2 m x)
    {M : MethodId} {l0 : Loc} {n : Node} {l : Loc}
    (hf : FlowRR P d1 rc1 M l0 n l) : FlowRR P d2 rc2 M l0 n l := by
  induction hf with
  | start M l0 => exact FlowRR.start M l0
  | step _ he hs ih => exact FlowRR.step ih he hs
  | pass _ he hm ih => exact FlowRR.pass ih he hm
  | call _ he he1 hd1 _ hdem hdin hdout hp he2 hd2 ih ihc =>
    exact FlowRR.call ih he he1 hd1 ihc (h _ _ hdem) hdin hdout hp he2 hd2
  | rcall _ he he1 hd1 hrc hcr hjc hdg he2 hd2 ih =>
    exact FlowRR.rcall ih he he1 hd1 (hr _ _ hrc) hcr hjc hdg he2 hd2
  | clean _ he hcl ih => exact FlowRR.clean ih he hcl
  | filt _ he hl ih => exact FlowRR.filt ih he hl

/-- A larger demand and more records keep a demanded-or-recorded vulnerability witness. -/
theorem reachRR_monoX {P : Program} {roots : List MethodId} {d1 d2 : MethodId → DemandEdge → Prop}
    {rc1 rc2 : Recs} (h : ∀ m e, d1 m e → d2 m e) (hr : ∀ m x, rc1 m x → rc2 m x)
    {M : MethodId} {n : Node} {l : Loc}
    (hw : ReachRR P d1 rc1 roots M n l) : ReachRR P d2 rc2 roots M n l := by
  induction hw with
  | root hM hfl => exact ReachRR.root hM (flowRR_monoX h hr hfl)
  | down _ he he1 hd1 hdem hdin hfc ih =>
    exact ReachRR.down ih he he1 hd1 (h _ _ hdem) hdin (flowRR_monoX h hr hfc)

/-- More records keep a justified flow. -/
theorem flowRDN_mono_rcX {P : Program} {R : Obj → Prop} {pub : Pub} {rc1 rc2 : Recs}
    (h : ∀ m x, rc1 m x → rc2 m x) {M : MethodId} {l0 : Loc} {n : Node} {l : Loc}
    (hf : FlowRDN P R pub rc1 M l0 n l) : FlowRDN P R pub rc2 M l0 n l := by
  induction hf with
  | start M l0 => exact FlowRDN.start M l0
  | step _ he hs ih => exact FlowRDN.step ih he hs
  | pass _ he hm ih => exact FlowRDN.pass ih he hm
  | call _ he he1 hd1 _ hj hg hpub hjc hdg he2 hd2 ih ihc =>
    exact FlowRDN.call ih he he1 hd1 ihc hj hg hpub hjc hdg he2 hd2
  | rcall _ he he1 hd1 hrc hcr hjc hdg he2 hd2 ih =>
    exact FlowRDN.rcall ih he he1 hd1 (h _ _ hrc) hcr hjc hdg he2 hd2
  | clean _ he hcl ih => exact FlowRDN.clean ih he hcl
  | filt _ he hl ih => exact FlowRDN.filt ih he hl

/-- More records keep a justified vulnerability witness. -/
theorem reachRDN_mono_rcX {P : Program} {R : Obj → Prop} {pub : Pub} {rc1 rc2 : Recs}
    {roots : List MethodId} (h : ∀ m x, rc1 m x → rc2 m x) {M : MethodId} {n : Node} {l : Loc}
    (hw : ReachRDN P R pub rc1 roots M n l) : ReachRDN P R pub rc2 roots M n l := by
  induction hw with
  | root hM hfl => exact ReachRDN.root hM (flowRDN_mono_rcX h hfl)
  | down _ he he1 hd1 hj hjc hfc ih =>
    exact ReachRDN.down ih he he1 hd1 hj hjc (flowRDN_mono_rcX h hfc)

#print axioms flowRR_monoX
#print axioms reachRR_monoX
#print axioms flowRDN_mono_rcX
#print axioms reachRDN_mono_rcX

/-! ## Part 1. The canonical X run sequence -/

/-- The state of a forward run: its result on the forgotten view, its publication and the base
    records it read. -/
structure RunStateX where
  R : Obj → Prop
  pub : Pub
  rc : Recs

/-- THE RECORD EMBEDDING: the crossable base records of `rc` as X records (not must, no
    exclusion). -/
def embedRecs (rc : Recs) : MethodId → PFact × Bool × Excl × XFact → Prop :=
  fun m y => ∃ j g, rc m (j, g) ∧ Cross j g ∧ y = (j, false, Excl.empty, ⟨g, Excl.empty⟩)

theorem embedRecs_spec (rc : Recs) : RecsEmbed rc (embedRecs rc) :=
  fun _ j g h hc => ⟨j, g, h, hc, rfl⟩

#print axioms embedRecs_spec

/-- The backward run after the forward run `s` (field limit `LB`, seeds `seeds`): demand `handF`,
    records `recsBOf`, no backward sink, started at the forward roots, the zero rules on (the base
    model of agent B, `HandoffBackward.lean`). -/
abbrev backOfX (P : Program) (counted : Acc → Bool) (LB : Nat) (roots : List MethodId)
    (seeds : List (MethodId × Node × PFact)) (s : RunStateX) : Obj → Prop :=
  DB (Program.rev P) counted LB (handF P s.R s.pub) emitM satI restrictI (recsBOf P s.R s.rc) []
    roots seeds true

/-- The demand that the backward run after `s` hands off to the next forward run. -/
abbrev demOfX (P : Program) (counted : Acc → Bool) (LB : Nat) (roots : List MethodId)
    (seeds : List (MethodId × Node × PFact)) (s : RunStateX) : MethodId → DemandEdge → Prop :=
  demOfN (Program.rev P) (backOfX P counted LB roots seeds s) (pubR (handF P s.R s.pub))

/-- The base records of the next forward run. -/
abbrev rcOfX (P : Program) (counted : Acc → Bool) (LB : Nat) (roots : List MethodId)
    (seeds : List (MethodId × Node × PFact)) (s : RunStateX) : Recs :=
  rcNextOf P s.R s.rc (backOfX P counted LB roots seeds s)

/-- The restricted forward run with the exclusion (before the forgotten view): the spec rules
    `emitX`, `satX`, `restrictIX`, the base records embedded as X records. -/
abbrev runX (P : Program) (taint : TaintEdges) (counted : Acc → Bool) (L : Nat)
    (dem : MethodId → DemandEdge → Prop) (rc : Recs) (sinks : List (MethodId × Node × PFact))
    (roots : List MethodId) : XObj → Prop :=
  DRX P taint counted L dem emitX satX restrictIX (embedRecs rc) sinks roots

/-- One round: from forward run `k` (state `s`) to forward run `k + 1`. -/
def stepStateX (P : Program) (taint : TaintEdges) (counted : Acc → Bool) (Ls LB : Nat → Nat)
    (sinks : List (MethodId × Node × PFact)) (roots : List MethodId)
    (seeds : Nat → List (MethodId × Node × PFact)) (k : Nat) (s : RunStateX) : RunStateX where
  R := forgetX (runX P taint counted (Ls (k + 1)) (demOfX P counted (LB k) roots (seeds k) s)
    (rcOfX P counted (LB k) roots (seeds k) s) sinks roots)
  pub := pubRX P (runX P taint counted (Ls (k + 1)) (demOfX P counted (LB k) roots (seeds k) s)
    (rcOfX P counted (LB k) roots (seeds k) s) sinks roots) (demOfX P counted (LB k) roots (seeds k) s)
  rc := rcOfX P counted (LB k) roots (seeds k) s

/-- Run 0: `D6X … policy1 …` read by `forget6`, the publication `pubD`, no record. -/
def state0X (P : Program) (taint : TaintEdges) (counted : Acc → Bool) (L0 : Nat)
    (sinks : List (MethodId × Node × PFact)) (roots : List MethodId) : RunStateX where
  R := forget6 (D6X P taint counted L0 policy1 sinks roots)
  pub := pubD
  rc := fun _ _ => False

/-- THE CANONICAL X RUN SEQUENCE of the spec rules with the exclusion. -/
def canonStateX (P : Program) (taint : TaintEdges) (counted : Acc → Bool) (Ls LB : Nat → Nat)
    (sinks : List (MethodId × Node × PFact)) (roots : List MethodId)
    (seeds : Nat → List (MethodId × Node × PFact)) : Nat → RunStateX
  | 0 => state0X P taint counted (Ls 0) sinks roots
  | k + 1 => stepStateX P taint counted Ls LB sinks roots seeds k
      (canonStateX P taint counted Ls LB sinks roots seeds k)

section Canon
variable {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {Ls LB : Nat → Nat}
  {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
  {seeds : Nat → List (MethodId × Node × PFact)}

local notation "CS" => canonStateX P taint counted Ls LB sinks roots seeds
local notation "DEMk" k => demOfX P counted (LB k) roots (seeds k) (CS k)

theorem canonX_zero : CS 0 = state0X P taint counted (Ls 0) sinks roots := rfl

theorem canonX_succ (k : Nat) :
    CS (k + 1) = stepStateX P taint counted Ls LB sinks roots seeds k (CS k) := rfl

/-- Forward run `k + 1` of the sequence is the forgotten view of the X run. -/
theorem canonX_run (k : Nat) :
    (CS (k + 1)).R = forgetX (runX P taint counted (Ls (k + 1)) (DEMk k) (CS (k + 1)).rc sinks
      roots) := rfl

#print axioms canonX_zero
#print axioms canonX_succ
#print axioms canonX_run

/-- Every publication of the sequence only removes pairs (the hypothesis `hpubSub` of the
    backward contract): `pubD`, and `pubRX` (`HandoffXRestrict.pubRX_sub`). -/
theorem canonX_pubSub (k : Nat) :
    ∀ m j g g', (CS k).pub m j g g' → ∀ l1 l2, den j g'.fact l1 l2 → den j g.fact l1 l2 := by
  cases k with
  | zero => exact pubD_sub
  | succ k => exact pubRX_sub P _ _

#print axioms canonX_pubSub

/-- Run 0 (`D6X`) justifies every real witness and reports it. -/
theorem canonX_run0 (hW : P.WF) :
    Run0Contract P roots sinks (CS 0).R (CS 0).pub (CS 0).rc :=
  run0X_contract hW

/-- The forward contract of every restricted X run of the sequence. -/
theorem canonX_covers (hW : P.WF) (k : Nat) :
    CoversN P roots sinks (DEMk k) (CS (k + 1)).rc (CS (k + 1)).R (CS (k + 1)).pub :=
  coversN_DRXI hW (embedRecs_spec _)

/-- The backward contract of every backward run of the sequence (agent B's
    `B_generalN_canon`, generic in the forward run and its publication). -/
theorem canonX_backward (hW : P.WF) (hT : BindTargetsStar P) (hmr : StmtsMarkRev P)
    (hNZB : NoZeroBack P) (hZ : ZeroKept P) (hX : ExitReach P roots)
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any) (k : Nat) :
    BackwardContractN P roots sinks (seeds k) (CS k).R (CS k).pub (CS k).rc (DEMk k)
      (CS (k + 1)).rc :=
  B_generalN_canon (counted := counted) (L := LB k) (sinksB := []) hW hT hmr hNZB hZ hX hk
    (canonX_pubSub k)

#print axioms canonX_run0
#print axioms canonX_covers
#print axioms canonX_backward

/-! ## Part 2. The iteration -/

/-- THE GENERAL ITERATION THEOREM OF THE NEW HAND-OFF WITH THE `[any-taint]` EXCLUSION. On the
    canonical X run sequence, every real vulnerability (a sink pattern with a concrete mark) is, at
    every forward run `k`, reported by run `k` or confirmed by an earlier run, if every reported
    vulnerability of a run is confirmed (`C`) or seeded. Program hypotheses as
    `AnyTaintExCov.iteration_reportsX`: well-formed, mark-agnostic binding targets,
    mark-reversible statements, no zero binding back, the zero kept by every instruction, every
    node of a method reaches its exit; the sinks have the tail `$` or `[any]`. -/
theorem iteration_generalNX (hW : P.WF) (hT : BindTargetsStar P) (hmr : StmtsMarkRev P)
    (hNZB : NoZeroBack P) (hZ : ZeroKept P) (hX : ExitReach P roots)
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    {C : Nat → MethodId → Node → PFact → Prop}
    (hseeds : ∀ k M n s b, (CS k).R (.vuln M n s b) → C k M n s ∨ (M, n, s) ∈ seeds k)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, (∃ k', k' < k ∧ C k' M n s) ∨ ∃ b, (CS k).R (.vuln M n s b) :=
  iteration_abstract_or (R := fun k => (CS k).R) (pub := fun k => (CS k).pub)
    (rc := fun k => (CS k).rc) (dem := fun k => DEMk k) (seeds := seeds)
    (canonX_run0 hW) (canonX_covers hW) (canonX_backward hW hT hmr hNZB hZ hX hk) hseeds
    hRe hs hT' hsc

#print axioms iteration_generalNX

/-- THE COROLLARY: if the backward run after each forward run seeds every reported vulnerability,
    every forward run of the canonical X sequence reports every real vulnerability. -/
theorem iteration_generalNX_all (hW : P.WF) (hT : BindTargetsStar P) (hmr : StmtsMarkRev P)
    (hNZB : NoZeroBack P) (hZ : ZeroKept P) (hX : ExitReach P roots)
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    (hseeds : ∀ k M n s b, (CS k).R (.vuln M n s b) → (M, n, s) ∈ seeds k)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, ∃ b, (CS k).R (.vuln M n s b) :=
  iteration_all_seeded (R := fun k => (CS k).R) (pub := fun k => (CS k).pub)
    (rc := fun k => (CS k).rc) (dem := fun k => DEMk k) (seeds := seeds)
    (canonX_run0 hW) (canonX_covers hW) (canonX_backward hW hT hmr hNZB hZ hX hk) hseeds
    hRe hs hT' hsc

#print axioms iteration_generalNX_all

/-- THE CITED FORM ON THE CANONICAL SEQUENCE (as `AnyTaintExCov.iteration_reportsX`): run 1 `D6X`
    reports every real vulnerability, and every restricted X run `k + 1`
    (`DRX … emitX satX restrictIX …`) reports it, in some layer. -/
theorem iteration_reportsNX_canon (hW : P.WF) (hT : BindTargetsStar P) (hmr : StmtsMarkRev P)
    (hNZB : NoZeroBack P) (hZ : ZeroKept P) (hX : ExitReach P roots)
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    (hseeds : ∀ k M n s b, (CS k).R (.vuln M n s b) → (M, n, s) ∈ seeds k)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    (∃ b, D6X P taint counted (Ls 0) policy1 sinks roots (.vuln M n s b)) ∧
    ∀ k, ∃ b, runX P taint counted (Ls (k + 1)) (DEMk k) (CS (k + 1)).rc sinks roots
      (.vuln M n s b) := by
  have h := iteration_generalNX_all hW hT hmr hNZB hZ hX hk hseeds hRe hs hT' hsc
  refine ⟨?_, fun k => ?_⟩
  · obtain ⟨b, hb⟩ := h 0
    exact ⟨b, AnyTaintExCov.forget6_vuln hb⟩
  · obtain ⟨b, hb⟩ := h (k + 1)
    exact ⟨b, AnyTaintExCov.forgetX_vuln hb⟩

#print axioms iteration_reportsNX_canon

end Canon

/-! ## Part 3. The inclusion form: the driver may hand off more -/

/-- A run sequence with given demands and X records: run 0 is `D6X … policy1 …` read by `forget6`,
    run `k + 1` is `DRX … (dem k) emitX satX restrictIX (recsX k) …` read by `forgetX`. -/
def runSeqNX (P : Program) (taint : TaintEdges) (counted : Acc → Bool) (Ls : Nat → Nat)
    (dem : Nat → MethodId → DemandEdge → Prop)
    (recsX : Nat → MethodId → PFact × Bool × Excl × XFact → Prop)
    (sinks : List (MethodId × Node × PFact)) (roots : List MethodId) : Nat → Obj → Prop
  | 0 => forget6 (D6X P taint counted (Ls 0) policy1 sinks roots)
  | k + 1 => forgetX (DRX P taint counted (Ls (k + 1)) (dem k) emitX satX restrictIX (recsX k)
      sinks roots)

/-- The publications of `runSeqNX`. -/
def pubSeqNX (P : Program) (taint : TaintEdges) (counted : Acc → Bool) (Ls : Nat → Nat)
    (dem : Nat → MethodId → DemandEdge → Prop)
    (recsX : Nat → MethodId → PFact × Bool × Excl × XFact → Prop)
    (sinks : List (MethodId × Node × PFact)) (roots : List MethodId) : Nat → Pub
  | 0 => pubD
  | k + 1 => pubRX P (DRX P taint counted (Ls (k + 1)) (dem k) emitX satX restrictIX (recsX k)
      sinks roots) (dem k)

theorem pubSeqNX_sub {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {Ls : Nat → Nat}
    {dem : Nat → MethodId → DemandEdge → Prop}
    {recsX : Nat → MethodId → PFact × Bool × Excl × XFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId} (k : Nat) :
    ∀ m j g g', pubSeqNX P taint counted Ls dem recsX sinks roots k m j g g' →
      ∀ l1 l2, den j g'.fact l1 l2 → den j g.fact l1 l2 := by
  cases k with
  | zero => exact pubD_sub
  | succ k => exact pubRX_sub P _ _

#print axioms pubSeqNX_sub

section Incl
variable {P : Program} {roots : List MethodId} {sinks : List (MethodId × Node × PFact)}
  {taint : TaintEdges} {counted : Acc → Bool} {Ls LB : Nat → Nat}
  {dem demB : Nat → MethodId → DemandEdge → Prop} {rc recsB : Nat → Recs}
  {recsX : Nat → MethodId → PFact × Bool × Excl × XFact → Prop}
  {seeds : Nat → List (MethodId × Node × PFact)}

local notation "RS" => runSeqNX P taint counted Ls dem recsX sinks roots
local notation "PS" => pubSeqNX P taint counted Ls dem recsX sinks roots
local notation "DBk" k => DB (Program.rev P) counted (LB k) (demB k) emitM satI restrictI (recsB k)
  [] roots (seeds k) true

/-- THE GENERAL ITERATION THEOREM WITH THE EXCLUSION, INCLUSION FORM (hypotheses as
    `AnyTaintExCov.iteration_reportsX`). The backward demand `demB k` contains `handF` of run `k`
    (read on the forgotten view, publication `pubSeqNX`), the backward records `recsB k` contain
    the reversed crossable records of run `k`, the demand `dem k` of run `k + 1` contains the
    hand-off `demOfN` of the backward run, the base records `rc (k + 1)` contain `rcNextOf`
    (`NextRecs`), and the X records `recsX k` of run `k + 1` embed them (`RecsEmbed`). Then every
    real vulnerability is, at every forward run `k`, reported by run `k` or confirmed by an earlier
    run. -/
theorem iteration_generalNX_incl (hW : P.WF) (hT : BindTargetsStar P) (hmr : StmtsMarkRev P)
    (hNZB : NoZeroBack P) (hZ : ZeroKept P) (hX : ExitReach P roots)
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    {C : Nat → MethodId → Node → PFact → Prop}
    (hdemB : ∀ k m d, handF P (RS k) (PS k) m d → demB k m d)
    (hrecB : ∀ k m x, (rc k m x ∨ (RS k (.init m x.1) ∧ RS k (.edge m x.1 (P.exit m) x.2))) →
      Cross x.1 x.2 → recsB k m (revRec x))
    (hrcN : ∀ k, NextRecs P (RS k) (rc k) (DBk k) (rc (k + 1)))
    (hdem : ∀ k m d, demOfN (Program.rev P) (DBk k) (pubR (demB k)) m d → dem k m d)
    (hrecX : ∀ k, RecsEmbed (rc (k + 1)) (recsX k))
    (hseeds : ∀ k M n s b, RS k (.vuln M n s b) → C k M n s ∨ (M, n, s) ∈ seeds k)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, (∃ k', k' < k ∧ C k' M n s) ∨ ∃ b, RS k (.vuln M n s b) := by
  have h0 : Run0Contract P roots sinks (RS 0) (PS 0) (rc 0) := by
    intro M1 n1 l1 s1 T1 hs1 hT1 hsc1 hRe1
    obtain ⟨hRD, hv⟩ := run0X_contract (taint := taint) (counted := counted) (L := Ls 0) hW M1 n1 l1
      s1 T1 hs1 hT1 hsc1 hRe1
    exact ⟨reachRDN_mono_rcX (fun _ _ h => h.elim) hRD, hv⟩
  have hF : ∀ k, CoversN P roots sinks (dem k) (rc (k + 1)) (RS (k + 1)) (PS (k + 1)) :=
    fun k => coversN_DRXI hW (hrecX k)
  have hB : ∀ k, BackwardContractN P roots sinks (seeds k) (RS k) (PS k) (rc k) (dem k)
      (rc (k + 1)) := by
    intro k M1 n1 l1 s1 T1 hs1 hT1 hsc1 hRR1 hsd1
    exact reachRR_monoX (hdem k) (fun _ _ h => h)
      (B_generalN (counted := counted) (L := LB k) (sinksB := []) hW hT hmr hNZB hZ hX hk
        (hdemB k) (hrecB k) (pubSeqNX_sub k) (hrcN k) M1 n1 l1 s1 T1 hs1 hT1 hsc1 hRR1 hsd1)
  exact iteration_abstract_or (R := RS) (pub := PS) (rc := rc) (dem := dem) (seeds := seeds)
    h0 hF hB hseeds hRe hs hT' hsc

#print axioms iteration_generalNX_incl

/-- THE CITED FORM, INCLUSION FORM (as `AnyTaintExCov.iteration_reportsX`): with every reported
    vulnerability seeded, run 1 `D6X` reports every real vulnerability, and every restricted X run
    `k + 1` (`DRX … (dem k) emitX satX restrictIX (recsX k) …`) reports it, in some layer. -/
theorem iteration_reportsNX (hW : P.WF) (hT : BindTargetsStar P) (hmr : StmtsMarkRev P)
    (hNZB : NoZeroBack P) (hZ : ZeroKept P) (hX : ExitReach P roots)
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    (hdemB : ∀ k m d, handF P (RS k) (PS k) m d → demB k m d)
    (hrecB : ∀ k m x, (rc k m x ∨ (RS k (.init m x.1) ∧ RS k (.edge m x.1 (P.exit m) x.2))) →
      Cross x.1 x.2 → recsB k m (revRec x))
    (hrcN : ∀ k, NextRecs P (RS k) (rc k) (DBk k) (rc (k + 1)))
    (hdem : ∀ k m d, demOfN (Program.rev P) (DBk k) (pubR (demB k)) m d → dem k m d)
    (hrecX : ∀ k, RecsEmbed (rc (k + 1)) (recsX k))
    (hseeds : ∀ k M n s b, RS k (.vuln M n s b) → (M, n, s) ∈ seeds k)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    (∃ b, D6X P taint counted (Ls 0) policy1 sinks roots (.vuln M n s b)) ∧
    ∀ k, ∃ b, DRX P taint counted (Ls (k + 1)) (dem k) emitX satX restrictIX (recsX k) sinks roots
      (.vuln M n s b) := by
  have h : ∀ k, ∃ b, RS k (.vuln M n s b) := by
    intro k
    rcases iteration_generalNX_incl (C := fun _ _ _ _ => False) hW hT hmr hNZB hZ hX hk hdemB
      hrecB hrcN hdem hrecX (fun k M n s b hv => Or.inr (hseeds k M n s b hv)) hRe hs hT' hsc k
      with ⟨_, _, hF⟩ | hv
    · exact hF.elim
    · exact hv
  refine ⟨?_, fun k => ?_⟩
  · obtain ⟨b, hb⟩ := h 0
    exact ⟨b, AnyTaintExCov.forget6_vuln hb⟩
  · obtain ⟨b, hb⟩ := h (k + 1)
    exact ⟨b, AnyTaintExCov.forgetX_vuln hb⟩

#print axioms iteration_reportsNX

end Incl

end ApSpec.HandoffXIter

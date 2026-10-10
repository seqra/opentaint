/-
  ApSpec.HandoffUpto — the iteration of the hand-off of the DEMAND EDGES only (decision F70) when
  the driver STOPS: a finite run sequence (`analyzer-core.md` §7.1, the stop rules).

  The driver stops after forward run `K` (a stop rule, or the budget). Only the runs up to it are
  complete, so only the hand-offs between them are known. This file proves the iteration for such
  a finite sequence: the hypotheses hold only for `k < K`, the conclusion holds for every forward
  run `k ≤ K`. The proof does not extend the sequence after `K` (the technique of
  `PipelineDriver.driver_iteration_upto`): the induction of `HandoffIter.iteration_invariantN`
  stops at `K` itself.

  Part 1. THE ABSTRACT CORE (`iteration_invariant_upto`): a run sequence with ONE PROGRAM PER RUN
    (`Pr k`: forward run `k` analyses `Pr k`; with forward source seeds a later forward run analyses
    a restricted program, `HandoffSrc.lean`), the two contracts for `k < K` (`CoversN` of forward
    run `k + 1` in its program, `BackwardContractNIn` from forward run `k` in its program to forward
    run `k + 1` in its program), and seeds "confirmed or seeded" for `k < K`. Then every forward run
    `k ≤ K` reports the vulnerability, or a run before `k` confirmed it. The infinite forms
    (`iteration_invariant_prog`, `iteration_prog_or`) follow with `K = k`.
  Part 2. THE BASE SEQUENCE (`HandoffMain.runSeqN`): `iteration_generalN_upto` (the inclusion form
    of `HandoffMain.iteration_generalN_incl`, its hypotheses only for `k < K`) and the canonical
    sequence `iteration_generalN_canon_upto`.
  Part 3. THE SPEC CLOSURES WITH THE `[any-taint]` EXCLUSION (`HandoffXIter.runSeqNX`):
    `iteration_generalNX_upto` (the inclusion form of `HandoffXIter.iteration_generalNX_incl`) and
    `iteration_generalNX_canon_upto`.

  All proofs are constructive (`propext`, `Quot.sound` only).
-/
import ApSpec.HandoffMain
import ApSpec.HandoffXIter

namespace ApSpec.HandoffUpto
open ApSpec ApSpec.Reverse ApSpec.Backward ApSpec.Handoff ApSpec.HandoffBackward ApSpec.HandoffIter

/-! ## Part 1. The abstract core: a program per run, a stop index -/

/-- THE BACKWARD CONTRACT BETWEEN TWO PROGRAMS: every witness that forward run `Rk` justifies in
    its program `Pk` (with its publication and its records), of a sink that the backward run SEEDS,
    is demanded or recorded in the next forward run, in the program `Pn` of that run (its demand
    `dnext`, its records `rcnext`). With `Pk = Pn = P` it is `Handoff.BackwardContractN`. -/
def BackwardContractNIn (Pk Pn : Program) (roots : List MethodId)
    (sinks : List (MethodId × Node × PFact)) (seeds : List (MethodId × Node × PFact))
    (Rk : Obj → Prop) (pub : Pub) (rc : Recs)
    (dnext : MethodId → DemandEdge → Prop) (rcnext : Recs) : Prop :=
  ∀ M n l s T, (M, n, s) ∈ sinks → s.mark = .conc T → s.covers l →
    ReachRDN Pk Rk pub rc roots M n l → (M, n, s) ∈ seeds →
    ReachRR Pn dnext rcnext roots M n l

/-- With one program, the contract is `BackwardContractN`. -/
theorem backwardContractNIn_iff {P : Program} {roots : List MethodId}
    {sinks seeds : List (MethodId × Node × PFact)} {Rk : Obj → Prop} {pub : Pub} {rc : Recs}
    {dnext : MethodId → DemandEdge → Prop} {rcnext : Recs} :
    BackwardContractNIn P P roots sinks seeds Rk pub rc dnext rcnext ↔
      BackwardContractN P roots sinks seeds Rk pub rc dnext rcnext := Iff.rfl

#print axioms backwardContractNIn_iff

section Core
variable {Pr : Nat → Program} {roots : List MethodId} {sinks : List (MethodId × Node × PFact)}
  {R : Nat → Obj → Prop} {pub : Nat → Pub} {rc : Nat → Recs}
  {dem : Nat → MethodId → DemandEdge → Prop} {seeds : Nat → List (MethodId × Node × PFact)}
  {C : Nat → MethodId → Node → PFact → Prop}

/-- THE STRENGTHENED INVARIANT OF A FINITE SEQUENCE. The contracts and the seed hypothesis hold
    for the rounds `k < K`. If forward run 0 justifies the witness in its program and reports it,
    then every forward run `k ≤ K` justifies it in its program and reports it, or a run before `k`
    confirmed it. -/
theorem iteration_invariant_upto (K : Nat)
    (hF : ∀ k, k < K →
      CoversN (Pr (k + 1)) roots sinks (dem k) (rc (k + 1)) (R (k + 1)) (pub (k + 1)))
    (hB : ∀ k, k < K → BackwardContractNIn (Pr k) (Pr (k + 1)) roots sinks (seeds k) (R k) (pub k)
      (rc k) (dem k) (rc (k + 1)))
    (hseeds : ∀ k, k < K → ∀ M n s b, R k (.vuln M n s b) → C k M n s ∨ (M, n, s) ∈ seeds k)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T) (hsc : s.covers l)
    (h0 : ReachRDN (Pr 0) (R 0) (pub 0) (rc 0) roots M n l) (h0v : ∃ b, R 0 (.vuln M n s b)) :
    ∀ k, k ≤ K → (∃ k', k' < k ∧ C k' M n s) ∨
      (ReachRDN (Pr k) (R k) (pub k) (rc k) roots M n l ∧ ∃ b, R k (.vuln M n s b)) := by
  intro k
  induction k with
  | zero => exact fun _ => Or.inr ⟨h0, h0v⟩
  | succ k ih =>
    intro hk
    have hkK : k < K := Nat.lt_of_succ_le hk
    rcases ih (Nat.le_of_lt hkK) with ⟨k', hk', hC⟩ | ⟨hRk, b, hv⟩
    · exact Or.inl ⟨k', Nat.lt_succ_of_lt hk', hC⟩
    · rcases hseeds k hkK M n s b hv with hC | hsd
      · exact Or.inl ⟨k, Nat.lt_succ_self k, hC⟩
      · exact Or.inr (hF k hkK M n l s T hs hT hsc (hB k hkK M n l s T hs hT hsc hRk hsd))

#print axioms iteration_invariant_upto

/-- THE STRENGTHENED INVARIANT, INFINITE FORM (a program per run). -/
theorem iteration_invariant_prog
    (hF : ∀ k, CoversN (Pr (k + 1)) roots sinks (dem k) (rc (k + 1)) (R (k + 1)) (pub (k + 1)))
    (hB : ∀ k, BackwardContractNIn (Pr k) (Pr (k + 1)) roots sinks (seeds k) (R k) (pub k)
      (rc k) (dem k) (rc (k + 1)))
    (hseeds : ∀ k M n s b, R k (.vuln M n s b) → C k M n s ∨ (M, n, s) ∈ seeds k)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T) (hsc : s.covers l)
    (h0 : ReachRDN (Pr 0) (R 0) (pub 0) (rc 0) roots M n l) (h0v : ∃ b, R 0 (.vuln M n s b)) :
    ∀ k, (∃ k', k' < k ∧ C k' M n s) ∨
      (ReachRDN (Pr k) (R k) (pub k) (rc k) roots M n l ∧ ∃ b, R k (.vuln M n s b)) :=
  fun k => iteration_invariant_upto (C := C) k (fun i _ => hF i) (fun i _ => hB i)
    (fun i _ => hseeds i) hs hT hsc h0 h0v k (Nat.le_refl k)

#print axioms iteration_invariant_prog

/-- THE ABSTRACT ITERATION OF A FINITE SEQUENCE (a program per run): for a real witness (in the
    program of run 0) of a sink pattern with a concrete mark, every forward run `k ≤ K` reports the
    vulnerability, or a run before `k` confirmed it. -/
theorem iteration_prog_upto (K : Nat)
    (h0 : Run0Contract (Pr 0) roots sinks (R 0) (pub 0) (rc 0))
    (hF : ∀ k, k < K →
      CoversN (Pr (k + 1)) roots sinks (dem k) (rc (k + 1)) (R (k + 1)) (pub (k + 1)))
    (hB : ∀ k, k < K → BackwardContractNIn (Pr k) (Pr (k + 1)) roots sinks (seeds k) (R k) (pub k)
      (rc k) (dem k) (rc (k + 1)))
    (hseeds : ∀ k, k < K → ∀ M n s b, R k (.vuln M n s b) → C k M n s ∨ (M, n, s) ∈ seeds k)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach (Pr 0) roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, k ≤ K → (∃ k', k' < k ∧ C k' M n s) ∨ ∃ b, R k (.vuln M n s b) := by
  intro k hk
  obtain ⟨hRD, hv⟩ := h0 M n l s T hs hT hsc hRe
  rcases iteration_invariant_upto K hF hB hseeds hs hT hsc hRD hv k hk with h | ⟨_, hv'⟩
  · exact Or.inl h
  · exact Or.inr hv'

#print axioms iteration_prog_upto

/-- THE ABSTRACT ITERATION, INFINITE FORM (a program per run). -/
theorem iteration_prog_or
    (h0 : Run0Contract (Pr 0) roots sinks (R 0) (pub 0) (rc 0))
    (hF : ∀ k, CoversN (Pr (k + 1)) roots sinks (dem k) (rc (k + 1)) (R (k + 1)) (pub (k + 1)))
    (hB : ∀ k, BackwardContractNIn (Pr k) (Pr (k + 1)) roots sinks (seeds k) (R k) (pub k)
      (rc k) (dem k) (rc (k + 1)))
    (hseeds : ∀ k M n s b, R k (.vuln M n s b) → C k M n s ∨ (M, n, s) ∈ seeds k)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach (Pr 0) roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, (∃ k', k' < k ∧ C k' M n s) ∨ ∃ b, R k (.vuln M n s b) :=
  fun k => iteration_prog_upto (C := C) k h0 (fun i _ => hF i) (fun i _ => hB i)
    (fun i _ => hseeds i) hRe hs hT hsc k (Nat.le_refl k)

#print axioms iteration_prog_or

end Core

/-- THE ABSTRACT ITERATION OF A FINITE SEQUENCE, ONE PROGRAM (`HandoffIter.iteration_abstract_or`
    for the rounds `k < K`): every forward run `k ≤ K` reports the vulnerability, or a run before `k`
    confirmed it. -/
theorem iteration_abstract_upto {P : Program} {roots : List MethodId}
    {sinks : List (MethodId × Node × PFact)} {R : Nat → Obj → Prop} {pub : Nat → Pub}
    {rc : Nat → Recs} {dem : Nat → MethodId → DemandEdge → Prop}
    {seeds : Nat → List (MethodId × Node × PFact)} {C : Nat → MethodId → Node → PFact → Prop}
    (K : Nat)
    (h0 : Run0Contract P roots sinks (R 0) (pub 0) (rc 0))
    (hF : ∀ k, k < K → CoversN P roots sinks (dem k) (rc (k + 1)) (R (k + 1)) (pub (k + 1)))
    (hB : ∀ k, k < K → BackwardContractN P roots sinks (seeds k) (R k) (pub k) (rc k) (dem k)
      (rc (k + 1)))
    (hseeds : ∀ k, k < K → ∀ M n s b, R k (.vuln M n s b) → C k M n s ∨ (M, n, s) ∈ seeds k)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, k ≤ K → (∃ k', k' < k ∧ C k' M n s) ∨ ∃ b, R k (.vuln M n s b) :=
  iteration_prog_upto (Pr := fun _ => P) K h0 hF (fun k hk => backwardContractNIn_iff.mpr (hB k hk))
    hseeds hRe hs hT hsc

#print axioms iteration_abstract_upto

/-! ## Part 2. The base sequence -/

section Base
open ApSpec.HandoffMain (runSeqN pubSeqN pubSeqN_sub reachRR_mono reachRDN_mono_rc)

/-- THE GENERAL ITERATION THEOREM OF THE NEW HAND-OFF FOR A FINITE SEQUENCE (inclusion form,
    `HandoffMain.iteration_generalN_incl` for the rounds `k < K`). The driver stops after forward
    run `K`; the hand-offs between the runs up to it hold: the backward demand `demB k` contains
    `handF` of run `k`, the backward records `recsB k` contain the reversed crossable records of
    run `k`, the demand `dem k` of run `k + 1` contains the hand-off `demOfN` of the backward run,
    the records `rc (k + 1)` contain `rcNextOf` (`NextRecs`), and every reported vulnerability of
    run `k` is confirmed (`C k`) or seeded. Then every real vulnerability is, at every forward run
    `k ≤ K`, reported by run `k` or confirmed by an earlier run. Program hypotheses as
    `HandoffMain.iteration_generalN`. -/
theorem iteration_generalN_upto {P : Program} (hW : P.WF) (hT : BindTargetsStar P)
    (hmr : StmtsMarkRev P) (hNZB : NoZeroBack P) (hZ : ZeroKept P) {roots : List MethodId}
    (hX : ExitReach P roots) {sinks : List (MethodId × Node × PFact)}
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    {counted : Acc → Bool} {Ls LB : Nat → Nat}
    {dem demB : Nat → MethodId → DemandEdge → Prop} {rc recsB : Nat → Recs}
    {seeds : Nat → List (MethodId × Node × PFact)} {C : Nat → MethodId → Node → PFact → Prop}
    (K : Nat)
    (hdemB : ∀ k, k < K → ∀ m d,
      handF P (runSeqN P counted Ls dem rc sinks roots k) (pubSeqN dem k) m d → demB k m d)
    (hrecB : ∀ k, k < K → ∀ m x, (rc k m x ∨ (runSeqN P counted Ls dem rc sinks roots k
        (.init m x.1) ∧ runSeqN P counted Ls dem rc sinks roots k (.edge m x.1 (P.exit m) x.2))) →
      Cross x.1 x.2 → recsB k m (revRec x))
    (hdem : ∀ k, k < K → ∀ m d, demOfN (Program.rev P)
        (DB (Program.rev P) counted (LB k) (demB k) emitM satI restrictI (recsB k) [] roots
          (seeds k) true) (pubR (demB k)) m d → dem k m d)
    (hrc : ∀ k, k < K → NextRecs P (runSeqN P counted Ls dem rc sinks roots k) (rc k)
      (DB (Program.rev P) counted (LB k) (demB k) emitM satI restrictI (recsB k) [] roots
        (seeds k) true) (rc (k + 1)))
    (hseeds : ∀ k, k < K → ∀ M n s b, runSeqN P counted Ls dem rc sinks roots k (.vuln M n s b) →
      C k M n s ∨ (M, n, s) ∈ seeds k)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, k ≤ K → (∃ k', k' < k ∧ C k' M n s) ∨
      ∃ b, runSeqN P counted Ls dem rc sinks roots k (.vuln M n s b) := by
  refine iteration_abstract_upto (R := runSeqN P counted Ls dem rc sinks roots)
    (pub := pubSeqN dem) (rc := rc) (dem := dem) (seeds := seeds) K ?_ ?_ ?_ hseeds hRe hs hT' hsc
  · intro M' n' l' s' T' hs' hT'' hc' hRe'
    obtain ⟨hR, hv⟩ := run1_justifies P counted (Ls 0) sinks roots hW M' n' l' s' T' hs' hT'' hc'
      hRe'
    exact ⟨reachRDN_mono_rc (fun _ _ h => h.elim) hR, hv⟩
  · intro k _
    exact coversN_DR P counted (Ls (k + 1)) (dem k) (rc (k + 1)) sinks roots hW
  · intro k hkK M' n' l' s' T' hs' hT'' hc' hRR hsd
    exact reachRR_mono (hdem k hkK)
      (B_generalN (counted := counted) (L := LB k) (sinksB := []) hW hT hmr hNZB hZ hX hk
        (hdemB k hkK) (hrecB k hkK) (pubSeqN_sub dem k) (hrc k hkK) M' n' l' s' T' hs' hT'' hc'
        hRR hsd)

#print axioms iteration_generalN_upto

end Base

section BaseCanon
open ApSpec.HandoffMain (canonState canon_run0 canon_covers canon_backward)
variable {P : Program} {counted : Acc → Bool} {Ls LB : Nat → Nat}
  {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
  {seeds : Nat → List (MethodId × Node × PFact)}

local notation "CS" => canonState P counted Ls LB sinks roots seeds

/-- THE CANONICAL SEQUENCE, FINITE FORM (`HandoffMain.iteration_generalN` with the seed hypothesis
    only for the rounds `k < K`): every real vulnerability is, at every forward run `k ≤ K` of the
    canonical sequence, reported by run `k` or confirmed by an earlier run. -/
theorem iteration_generalN_canon_upto (hW : P.WF) (hT : BindTargetsStar P) (hmr : StmtsMarkRev P)
    (hNZB : NoZeroBack P) (hZ : ZeroKept P) (hX : ExitReach P roots)
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    {C : Nat → MethodId → Node → PFact → Prop} (K : Nat)
    (hseeds : ∀ k, k < K → ∀ M n s b, (CS k).R (.vuln M n s b) → C k M n s ∨ (M, n, s) ∈ seeds k)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, k ≤ K → (∃ k', k' < k ∧ C k' M n s) ∨ ∃ b, (CS k).R (.vuln M n s b) :=
  iteration_abstract_upto (R := fun k => (CS k).R) (pub := fun k => (CS k).pub)
    (rc := fun k => (CS k).rc)
    (dem := fun k => HandoffMain.demOf P counted (LB k) roots (seeds k) (CS k)) (seeds := seeds) K
    (canon_run0 hW) (fun k _ => canon_covers hW k)
    (fun k _ => canon_backward hW hT hmr hNZB hZ hX hk k) hseeds hRe hs hT' hsc

#print axioms iteration_generalN_canon_upto

end BaseCanon

/-! ## Part 3. The spec closures with the `[any-taint]` exclusion -/

section X
open ApSpec.HandoffX ApSpec.AnyTaint ApSpec.AnyTaintEx
open ApSpec.AnyTaintExCov (forgetX forget6)
open ApSpec.HandoffXIter (runSeqNX pubSeqNX pubSeqNX_sub reachRR_monoX reachRDN_mono_rcX)

variable {P : Program} {roots : List MethodId} {sinks : List (MethodId × Node × PFact)}
  {taint : TaintEdges} {counted : Acc → Bool} {Ls LB : Nat → Nat}
  {dem demB : Nat → MethodId → DemandEdge → Prop} {rc recsB : Nat → Recs}
  {recsX : Nat → MethodId → PFact × Bool × Excl × XFact → Prop}
  {seeds : Nat → List (MethodId × Node × PFact)}

local notation "RS" => runSeqNX P taint counted Ls dem recsX sinks roots
local notation "PS" => pubSeqNX P taint counted Ls dem recsX sinks roots
local notation "DBk" k => DB (Program.rev P) counted (LB k) (demB k) emitM satI restrictI (recsB k)
  [] roots (seeds k) true

/-- THE GENERAL ITERATION THEOREM WITH THE EXCLUSION FOR A FINITE SEQUENCE (inclusion form,
    `HandoffXIter.iteration_generalNX_incl` for the rounds `k < K`): with the hand-offs between the
    runs up to forward run `K` (hypotheses as there, for `k < K`), every real vulnerability is, at
    every forward run `k ≤ K`, reported by run `k` or confirmed by an earlier run. -/
theorem iteration_generalNX_upto (hW : P.WF) (hT : BindTargetsStar P) (hmr : StmtsMarkRev P)
    (hNZB : NoZeroBack P) (hZ : ZeroKept P) (hX : ExitReach P roots)
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    {C : Nat → MethodId → Node → PFact → Prop} (K : Nat)
    (hdemB : ∀ k, k < K → ∀ m d, handF P (RS k) (PS k) m d → demB k m d)
    (hrecB : ∀ k, k < K → ∀ m x, (rc k m x ∨ (RS k (.init m x.1) ∧
        RS k (.edge m x.1 (P.exit m) x.2))) → Cross x.1 x.2 → recsB k m (revRec x))
    (hrcN : ∀ k, k < K → NextRecs P (RS k) (rc k) (DBk k) (rc (k + 1)))
    (hdem : ∀ k, k < K → ∀ m d, demOfN (Program.rev P) (DBk k) (pubR (demB k)) m d → dem k m d)
    (hrecX : ∀ k, k < K → RecsEmbed (rc (k + 1)) (recsX k))
    (hseeds : ∀ k, k < K → ∀ M n s b, RS k (.vuln M n s b) → C k M n s ∨ (M, n, s) ∈ seeds k)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, k ≤ K → (∃ k', k' < k ∧ C k' M n s) ∨ ∃ b, RS k (.vuln M n s b) := by
  have h0 : Run0Contract P roots sinks (RS 0) (PS 0) (rc 0) := by
    intro M1 n1 l1 s1 T1 hs1 hT1 hsc1 hRe1
    obtain ⟨hRD, hv⟩ := run0X_contract (taint := taint) (counted := counted) (L := Ls 0) hW M1 n1 l1
      s1 T1 hs1 hT1 hsc1 hRe1
    exact ⟨reachRDN_mono_rcX (fun _ _ h => h.elim) hRD, hv⟩
  have hF : ∀ k, k < K → CoversN P roots sinks (dem k) (rc (k + 1)) (RS (k + 1)) (PS (k + 1)) :=
    fun k hkK => coversN_DRXI hW (hrecX k hkK)
  have hB : ∀ k, k < K → BackwardContractN P roots sinks (seeds k) (RS k) (PS k) (rc k) (dem k)
      (rc (k + 1)) := by
    intro k hkK M1 n1 l1 s1 T1 hs1 hT1 hsc1 hRR1 hsd1
    exact reachRR_monoX (hdem k hkK) (fun _ _ h => h)
      (B_generalN (counted := counted) (L := LB k) (sinksB := []) hW hT hmr hNZB hZ hX hk
        (hdemB k hkK) (hrecB k hkK) (pubSeqNX_sub k) (hrcN k hkK) M1 n1 l1 s1 T1 hs1 hT1 hsc1 hRR1
        hsd1)
  exact iteration_abstract_upto (R := RS) (pub := PS) (rc := rc) (dem := dem) (seeds := seeds) K
    h0 hF hB hseeds hRe hs hT' hsc

#print axioms iteration_generalNX_upto

end X

section XCanon
open ApSpec.HandoffXIter (canonStateX canonX_run0 canonX_covers canonX_backward demOfX)
variable {P : Program} {taint : AnyTaint.TaintEdges} {counted : Acc → Bool} {Ls LB : Nat → Nat}
  {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
  {seeds : Nat → List (MethodId × Node × PFact)}

local notation "CSX" => canonStateX P taint counted Ls LB sinks roots seeds

/-- THE CANONICAL X SEQUENCE, FINITE FORM (`HandoffXIter.iteration_generalNX` with the seed
    hypothesis only for the rounds `k < K`). -/
theorem iteration_generalNX_canon_upto (hW : P.WF) (hT : BindTargetsStar P)
    (hmr : StmtsMarkRev P) (hNZB : NoZeroBack P) (hZ : ZeroKept P) (hX : ExitReach P roots)
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    {C : Nat → MethodId → Node → PFact → Prop} (K : Nat)
    (hseeds : ∀ k, k < K → ∀ M n s b, (CSX k).R (.vuln M n s b) → C k M n s ∨ (M, n, s) ∈ seeds k)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, k ≤ K → (∃ k', k' < k ∧ C k' M n s) ∨ ∃ b, (CSX k).R (.vuln M n s b) :=
  iteration_abstract_upto (R := fun k => (CSX k).R) (pub := fun k => (CSX k).pub)
    (rc := fun k => (CSX k).rc)
    (dem := fun k => demOfX P counted (LB k) roots (seeds k) (CSX k)) (seeds := seeds) K
    (canonX_run0 hW) (fun k _ => canonX_covers hW k)
    (fun k _ => canonX_backward hW hT hmr hNZB hZ hX hk k) hseeds hRe hs hT' hsc

#print axioms iteration_generalNX_canon_upto

end XCanon

end ApSpec.HandoffUpto

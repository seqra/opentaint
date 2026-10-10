/-
  ApSpec.HandoffIter — the iteration of the hand-off of the DEMAND EDGES only (decision F70), in
  abstract form.

  A run sequence: forward runs `R k` with the publications `pub k` and the record sets `rc k`
  (the records that run `k` reads; run 0 reads none), the demand `dem k` of forward run `k + 1`,
  the seeds `seeds k` of the backward run after forward run `k`, and a CONFIRMED predicate `C`
  (any predicate: `C k M n s` says that run `k` confirmed the vulnerability of the sink
  `(M, n, s)`; the backward run does not seed a confirmed vulnerability, because it is final).

  The theorem composes the two contracts of `HandoffDefs.lean`:
    * `CoversN` for every restricted forward run `k + 1` (input `ReachRR` with the demand `dem k`
      and the records `rc (k + 1)`, output `ReachRDN` and a reported vulnerability);
    * `BackwardContractN` for every backward step `k` (output `ReachRDN` of run `k` with a SEEDED
      sink, input `ReachRR` of run `k + 1`);
  with run 0 that justifies every real witness and reports it, and seeds that contain every
  reported vulnerability that is not confirmed.

  Main results:
    * `iteration_invariantN`: the strengthened induction (the witness stays justified).
    * `iteration_abstract_or`: for a real witness of a sink pattern with a concrete mark, every
      run `k` reports the vulnerability, or an earlier run confirmed it. The seed hypothesis is in
      the constructive form "confirmed or seeded".
    * `iteration_abstract`: the same with the seed hypothesis of the brief ("not confirmed ⇒
      seeded") and a decidable `C` (constructive logic needs the case split on `C`).
    * `iteration_invariant_neg`, `iteration_abstract_neg`: the seed hypothesis of the brief with
      no decidable `C`, and the conclusion in its constructive form: if no run before `k`
      confirmed the vulnerability, run `k` reports it.
    * `iteration_all_seeded`: the corollary with `C = False` (every reported vulnerability
      seeded): every forward run reports every real vulnerability.

  The end-to-end theorem with the spec rules (`HandoffMain.lean`) joins this file with the
  coverage theorem of the restricted forward run and `HandoffBackward.B_generalN`.

  All proofs are constructive (`propext`, `Quot.sound` only).
-/
import ApSpec.HandoffDefs

namespace ApSpec.HandoffIter
open ApSpec ApSpec.Handoff

/-- Run 0 justifies every real witness of a sink pattern with a concrete mark, and reports its
    vulnerability. -/
def Run0Contract (P : Program) (roots : List MethodId) (sinks : List (MethodId × Node × PFact))
    (R0 : Obj → Prop) (pub0 : Pub) (rc0 : Recs) : Prop :=
  ∀ M n l s T, (M, n, s) ∈ sinks → s.mark = .conc T → s.covers l → Reach P roots M n l →
    ReachRDN P R0 pub0 rc0 roots M n l ∧ ∃ b, R0 (.vuln M n s b)

section Abstract
variable {P : Program} {roots : List MethodId} {sinks : List (MethodId × Node × PFact)}
  {R : Nat → Obj → Prop} {pub : Nat → Pub} {rc : Nat → Recs}
  {dem : Nat → MethodId → DemandEdge → Prop} {seeds : Nat → List (MethodId × Node × PFact)}
  {C : Nat → MethodId → Node → PFact → Prop}

/-- THE STRENGTHENED INVARIANT. If run 0 justifies the witness and reports it, then every run
    `k` justifies it and reports it, or an earlier run confirmed it. -/
theorem iteration_invariantN
    (hF : ∀ k, CoversN P roots sinks (dem k) (rc (k + 1)) (R (k + 1)) (pub (k + 1)))
    (hB : ∀ k, BackwardContractN P roots sinks (seeds k) (R k) (pub k) (rc k) (dem k) (rc (k + 1)))
    (hseeds : ∀ k M n s b, R k (.vuln M n s b) → C k M n s ∨ (M, n, s) ∈ seeds k)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T) (hsc : s.covers l)
    (h0 : ReachRDN P (R 0) (pub 0) (rc 0) roots M n l) (h0v : ∃ b, R 0 (.vuln M n s b)) :
    ∀ k, (∃ k', k' < k ∧ C k' M n s) ∨
      (ReachRDN P (R k) (pub k) (rc k) roots M n l ∧ ∃ b, R k (.vuln M n s b)) := by
  intro k
  induction k with
  | zero => exact Or.inr ⟨h0, h0v⟩
  | succ k ih =>
    rcases ih with ⟨k', hk', hC⟩ | ⟨hRk, b, hv⟩
    · exact Or.inl ⟨k', Nat.lt_succ_of_lt hk', hC⟩
    · rcases hseeds k M n s b hv with hC | hsd
      · exact Or.inl ⟨k, Nat.lt_succ_self k, hC⟩
      · exact Or.inr (hF k M n l s T hs hT hsc (hB k M n l s T hs hT hsc hRk hsd))

#print axioms iteration_invariantN

/-- THE ABSTRACT ITERATION THEOREM (seed hypothesis: confirmed or seeded). For a real witness of
    a sink pattern with a concrete mark, every forward run `k` reports the vulnerability, or a run
    before `k` confirmed it. -/
theorem iteration_abstract_or
    (h0 : Run0Contract P roots sinks (R 0) (pub 0) (rc 0))
    (hF : ∀ k, CoversN P roots sinks (dem k) (rc (k + 1)) (R (k + 1)) (pub (k + 1)))
    (hB : ∀ k, BackwardContractN P roots sinks (seeds k) (R k) (pub k) (rc k) (dem k) (rc (k + 1)))
    (hseeds : ∀ k M n s b, R k (.vuln M n s b) → C k M n s ∨ (M, n, s) ∈ seeds k)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, (∃ k', k' < k ∧ C k' M n s) ∨ ∃ b, R k (.vuln M n s b) := by
  intro k
  obtain ⟨hRD, hv⟩ := h0 M n l s T hs hT hsc hRe
  rcases iteration_invariantN hF hB hseeds hs hT hsc hRD hv k with h | ⟨_, hv'⟩
  · exact Or.inl h
  · exact Or.inr hv'

#print axioms iteration_abstract_or

/-- THE ABSTRACT ITERATION THEOREM in the form of the brief: the seeds contain every reported
    vulnerability that `C` does not confirm. The case split on `C` needs `C` decidable
    (`hCd`); with the seed hypothesis in the form "confirmed or seeded" no such hypothesis is
    necessary (`iteration_abstract_or`). -/
theorem iteration_abstract
    (h0 : Run0Contract P roots sinks (R 0) (pub 0) (rc 0))
    (hF : ∀ k, CoversN P roots sinks (dem k) (rc (k + 1)) (R (k + 1)) (pub (k + 1)))
    (hB : ∀ k, BackwardContractN P roots sinks (seeds k) (R k) (pub k) (rc k) (dem k) (rc (k + 1)))
    (hCd : ∀ k M n s, C k M n s ∨ ¬ C k M n s)
    (hseeds : ∀ k M n s b, R k (.vuln M n s b) → ¬ C k M n s → (M, n, s) ∈ seeds k)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, (∃ k', k' < k ∧ C k' M n s) ∨ ∃ b, R k (.vuln M n s b) :=
  iteration_abstract_or h0 hF hB
    (fun k M n s b hv => (hCd k M n s).elim Or.inl (fun hnC => Or.inr (hseeds k M n s b hv hnC)))
    hRe hs hT hsc

#print axioms iteration_abstract

/-- THE INVARIANT WITH THE SEED HYPOTHESIS OF THE BRIEF, constructive form: if no run before `k`
    confirmed the vulnerability, run `k` justifies the witness and reports it. No case split on
    `C` is necessary. -/
theorem iteration_invariant_neg
    (hF : ∀ k, CoversN P roots sinks (dem k) (rc (k + 1)) (R (k + 1)) (pub (k + 1)))
    (hB : ∀ k, BackwardContractN P roots sinks (seeds k) (R k) (pub k) (rc k) (dem k) (rc (k + 1)))
    (hseeds : ∀ k M n s b, R k (.vuln M n s b) → ¬ C k M n s → (M, n, s) ∈ seeds k)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T) (hsc : s.covers l)
    (h0 : ReachRDN P (R 0) (pub 0) (rc 0) roots M n l) (h0v : ∃ b, R 0 (.vuln M n s b)) :
    ∀ k, (∀ k', k' < k → ¬ C k' M n s) →
      ReachRDN P (R k) (pub k) (rc k) roots M n l ∧ ∃ b, R k (.vuln M n s b) := by
  intro k
  induction k with
  | zero => exact fun _ => ⟨h0, h0v⟩
  | succ k ih =>
    intro hnC
    obtain ⟨hRk, b, hv⟩ := ih (fun k' hk' => hnC k' (Nat.lt_succ_of_lt hk'))
    have hsd := hseeds k M n s b hv (hnC k (Nat.lt_succ_self k))
    exact hF k M n l s T hs hT hsc (hB k M n l s T hs hT hsc hRk hsd)

#print axioms iteration_invariant_neg

/-- THE ABSTRACT ITERATION THEOREM with the seed hypothesis of the brief, in the constructive
    form of its conclusion: if no run before `k` confirmed the vulnerability, run `k` reports it.
    (Classically this is the conclusion of the brief; constructively it needs no decidable `C`.) -/
theorem iteration_abstract_neg
    (h0 : Run0Contract P roots sinks (R 0) (pub 0) (rc 0))
    (hF : ∀ k, CoversN P roots sinks (dem k) (rc (k + 1)) (R (k + 1)) (pub (k + 1)))
    (hB : ∀ k, BackwardContractN P roots sinks (seeds k) (R k) (pub k) (rc k) (dem k) (rc (k + 1)))
    (hseeds : ∀ k M n s b, R k (.vuln M n s b) → ¬ C k M n s → (M, n, s) ∈ seeds k)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, (∀ k', k' < k → ¬ C k' M n s) → ∃ b, R k (.vuln M n s b) := by
  intro k hnC
  obtain ⟨hRD, hv⟩ := h0 M n l s T hs hT hsc hRe
  exact (iteration_invariant_neg hF hB hseeds hs hT hsc hRD hv k hnC).2

#print axioms iteration_abstract_neg

end Abstract

/-- THE COROLLARY WITH `C = False`: if the backward run after each forward run seeds every
    reported vulnerability, every forward run reports every real vulnerability. -/
theorem iteration_all_seeded {P : Program} {roots : List MethodId}
    {sinks : List (MethodId × Node × PFact)} {R : Nat → Obj → Prop} {pub : Nat → Pub}
    {rc : Nat → Recs} {dem : Nat → MethodId → DemandEdge → Prop}
    {seeds : Nat → List (MethodId × Node × PFact)}
    (h0 : Run0Contract P roots sinks (R 0) (pub 0) (rc 0))
    (hF : ∀ k, CoversN P roots sinks (dem k) (rc (k + 1)) (R (k + 1)) (pub (k + 1)))
    (hB : ∀ k, BackwardContractN P roots sinks (seeds k) (R k) (pub k) (rc k) (dem k) (rc (k + 1)))
    (hseeds : ∀ k M n s b, R k (.vuln M n s b) → (M, n, s) ∈ seeds k)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, ∃ b, R k (.vuln M n s b) := by
  intro k
  rcases iteration_abstract_or (C := fun _ _ _ _ => False) h0 hF hB
    (fun k M n s b hv => Or.inr (hseeds k M n s b hv)) hRe hs hT hsc k with ⟨_, _, hF'⟩ | hv
  · exact hF'.elim
  · exact hv

#print axioms iteration_all_seeded

end ApSpec.HandoffIter

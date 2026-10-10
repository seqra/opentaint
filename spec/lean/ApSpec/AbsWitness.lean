/-
  Executable witnesses for the local emission contract of F72.

  The witness is computed by emitW. The existence theorem is used only to prove properties
  of that computed value. No witness is extracted from Prop or selected by an axiom.
  Global coverage and iteration still need separate data-producing witness models.
-/
import ApSpec.AbsDefs
import ApSpec.HandoffNoStar

namespace ApSpec.Abs
open ApSpec ApSpec.Handoff

/-- Actual patterns from run 1 satisfy the tail condition of L6. Later hand-offs need their
    own run invariant; this statement does not assume it for the full sequence. -/
theorem handFA_run1_PatTail {P : Program} {counted : Acc → Bool} {L : Nat}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    {M : MethodId} {d : DemandEdge}
    (h : handFA P (D P counted L policy1 sinks roots) pubD M d) :
    PatTailB d.din.kind = true := by
  obtain ⟨d0, h0, rfl⟩ := h
  have hk := (HandoffNoStar.handF_run1_nonstar h0).1
  change PatTailB d0.din.kind = true
  cases he : d0.din.kind with
  | exact => rfl
  | any => rfl
  | star e => exact False.elim (hk e he)

#print axioms handFA_run1_PatTail

/-- L6 as data: a premise computed by emitW, with its coverage and satisfaction proofs. -/
def emitWitness (d a : PFact) (l : Loc)
    (hk : d.mark = .star → PatTailB d.kind = true)
    (hc : d.mark ≠ .star → ∃ t, a.mark = .conc t)
    (hd : d.covers l) (ha : a.covers l) :
    {j : PFact // emitW d a = some j ∧ j.covers l ∧ satW j a = true} :=
  match he : emitW d a with
  | some j => ⟨j, rfl, by
      obtain ⟨j0, h0, hcov, hsat⟩ := emitW_contract hk hc hd ha
      rw [he] at h0
      cases h0
      exact ⟨hcov, hsat⟩⟩
  | none => False.elim (by
      obtain ⟨j, hj, _, _⟩ := emitW_contract hk hc hd ha
      rw [he] at hj
      cases hj)

#print axioms emitWitness

/-- Computation of the certified witness uses the same operation as the analyzer. -/
theorem emitWitness_eq (d a : PFact) (l : Loc)
    (hk : d.mark = .star → PatTailB d.kind = true)
    (hc : d.mark ≠ .star → ∃ t, a.mark = .conc t)
    (hd : d.covers l) (ha : a.covers l) :
    emitW d a = some (emitWitness d a l hk hc hd ha).val :=
  (emitWitness d a l hk hc hd ha).property.1

#print axioms emitWitness_eq

/-- A finite executable sharing vector: both concrete marks compute the same FLOW premise. -/
def witnessVector (t : Mark) : PFact :=
  (emitWitness ⟨3, [], .any, .star⟩ ⟨3, [4], .exact, .conc t⟩ ⟨3, [4], t⟩
    (fun _ => rfl)
    (fun h => False.elim (h rfl))
    ⟨rfl, ⟨[4], rfl, trivial⟩, trivial⟩
    ⟨rfl, ⟨[], rfl, rfl⟩, rfl⟩).val

theorem witnessVector_shared (t u : Mark) : witnessVector t = witnessVector u := by
  rfl

#print axioms witnessVector
#print axioms witnessVector_shared

-- Kernel computation also checks that the witness can be reduced as ordinary data.
example : witnessVector 1 = ⟨3, [], .star Excl.empty, .star⟩ := by decide

end ApSpec.Abs

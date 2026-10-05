/-
  ApSpec.SharedExcl — one exclusion per edge.

  In the design, a correlated edge `(x, p, *) → (y, q, *)` has ONE exclusion `E`, shared
  by the premise and the conclusion. The model stores a `*/E` kind on both sides of a
  micro edge. This file proves that only the union matters: the edge
  `(x, p, */Ef) → (y, q, */Et)` gives the same result as `(x, p, */{}) → (y, q, */(Ef ∪ Et))`
  for every fact. So the spec states every table with the one edge exclusion `E`.
-/
import ApSpec.Core

namespace ApSpec.SharedExcl
open ApSpec

theorem empty_union (e : Excl) : Excl.empty.union e = e := by
  cases e <;> rfl

theorem below_shared (ck : Kind) (Ef Et : Excl) (r tp : List Acc) :
    belowCase ck (.star Ef) r tp (.star Et) =
      belowCase ck (.star Excl.empty) r tp (.star (Ef.union Et)) := by
  cases r with
  | nil =>
    have h1 : admitsTailB (.star Ef) [] = true := CoreAux.admits_nil Ef
    have h2 : admitsTailB (.star Excl.empty) [] = true := CoreAux.admits_nil Excl.empty
    unfold belowCase
    rw [h1, h2]
    cases ck <;> cases Ef <;> cases Et <;> rfl
  | cons a rs =>
    have h2 : admitsTailB (.star Excl.empty) (a :: rs) = true := CoreAux.empty_admits (a :: rs)
    unfold belowCase
    rw [h2]
    show (if Ef.admits (a :: rs) = true then
            (if Et.admits (a :: rs) = true then some (tp ++ a :: rs, ck, false) else none)
          else none) =
         (if (Ef.union Et).admits (a :: rs) = true then some (tp ++ a :: rs, ck, false) else none)
    rw [CoreAux.Excl.admits_union]
    cases Ef.admits (a :: rs) <;> cases Et.admits (a :: rs) <;> rfl

theorem above_shared (ck : Kind) (Ef Et : Excl) (r tp : List Acc) :
    aboveCase ck (.star Ef) r tp (.star Et) =
      aboveCase ck (.star Excl.empty) r tp (.star (Ef.union Et)) := by
  unfold aboveCase
  cases Ef <;> cases Et <;> rfl

/-- ONE EXCLUSION PER EDGE. A correlated micro edge gives the same result whether its
    exclusion is stored on the premise, on the conclusion, or split between them. -/
theorem applyEdge_shared_excl (c : AFact) (b b' : Base) (p q : List Acc) (Ef Et : Excl)
    (m m' : MarkA) :
    applyEdge c ⟨b, p, .star Ef, m⟩ ⟨b', q, .star Et, m'⟩ =
      applyEdge c ⟨b, p, .star Excl.empty, m⟩ ⟨b', q, .star (Ef.union Et), m'⟩ := by
  unfold applyEdge
  cases relate p c.fact.path with
  | below r => dsimp only; rw [below_shared]
  | above r => dsimp only; rw [above_shared]
  | apart => rfl

#print axioms applyEdge_shared_excl

/-- The same on the premise side: the exclusion may also be stored on the premise. -/
theorem applyEdge_shared_excl_premise (c : AFact) (b b' : Base) (p q : List Acc) (Ef Et : Excl)
    (m m' : MarkA) :
    applyEdge c ⟨b, p, .star Ef, m⟩ ⟨b', q, .star Et, m'⟩ =
      applyEdge c ⟨b, p, .star Excl.empty, m⟩ ⟨b', q, .star (Excl.empty.union (Ef.union Et)), m'⟩ := by
  rw [empty_union]
  exact applyEdge_shared_excl c b b' p q Ef Et m m'

/-- The pair relation of a correlated edge depends on the union only. -/
theorem den_shared_excl (b b' : Base) (p q : List Acc) (Ef Et : Excl) (m m' : MarkA)
    (l0 l1 : Loc) :
    den ⟨b, p, .star Ef, m⟩ ⟨b', q, .star Et, m'⟩ l0 l1 ↔
      den ⟨b, p, .star Excl.empty, m⟩ ⟨b', q, .star (Ef.union Et), m'⟩ l0 l1 := by
  unfold den
  constructor
  · rintro ⟨h1, h2, h3, h4, hp, σ, τ, h5, h6, h7, h8, h9⟩
    refine ⟨h1, h2, h3, h4, hp, σ, τ, h5, h6, CoreAux.empty_admits σ, h8, ?_⟩
    show (Ef.union Et).admits σ = true
    rw [CoreAux.Excl.admits_union]
    have h7' : Ef.admits σ = true := h7
    rw [h7', h9]
    rfl
  · rintro ⟨h1, h2, h3, h4, hp, σ, τ, h5, h6, _, h8, h9⟩
    have h9' : (Ef.union Et).admits σ = true := h9
    rw [CoreAux.Excl.admits_union] at h9'
    have hEf : Ef.admits σ = true := by
      cases hx : Ef.admits σ
      · rw [hx] at h9'; exact Bool.noConfusion h9'
      · rfl
    have hEt : Et.admits σ = true := by
      cases hx : Et.admits σ
      · rw [hx, Bool.and_false] at h9'; exact Bool.noConfusion h9'
      · rfl
    exact ⟨h1, h2, h3, h4, hp, σ, τ, h5, h6, hEf, h8, hEt⟩

#print axioms den_shared_excl

end ApSpec.SharedExcl

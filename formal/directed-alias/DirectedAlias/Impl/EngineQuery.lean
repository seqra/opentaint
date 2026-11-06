import DirectedAlias.Impl.EngineState

/-!
# The query holders by rule (obligation 5)

The backward query steps from an origin `o` to its holders: the cells `(p, c)` whose content
has `o`. In the engine state the holders are the written entries that contain `o`, and the
DEFAULT PARENTS of `o`: the cells that are not written and whose cell name is `o`.

* `holders_iff`: the holders of `o` in the denotation are exactly these cells (everywhere, so
  also on the universe: `holders_on`).
* `dfltParent_sym`: a symbolic origin `⟨b.q.c⟩` has exactly one default parent, the cell `c` of
  `⟨b.q⟩` (the engine computes it from the path, without a scan).
-/

namespace DirectedAlias.Impl.Engine

open DirectedAlias DirectedAlias.Opt
open DirectedAlias.Sound.CellNamed DirectedAlias.Sound.ValueSem

/-- The written holders of `o`: the written keys whose content has `o`. -/
def holdersW (K : Nat) (E : EState) (o : Origin) : List (Origin × ACell) :=
  (keys E.heap).filter (fun k => decide (o ∈ getH K E k))

/-- THE HOLDERS BY RULE: a cell holds `o` in the denotation if and only if it is a written holder,
or it is not written and its cell name is `o`. -/
theorem holders_iff (K : Nat) (E : EState) (o p : Origin) (c : ACell) :
    o ∈ (den K E).heap p c ↔
      (p, c) ∈ holdersW K E o ∨ ((p, c) ∉ keys E.heap ∧ o = childCN K p c) := by
  show o ∈ getH K E (p, c) ↔ _
  unfold holdersW
  rw [List.mem_filter]
  by_cases hw : (p, c) ∈ keys E.heap
  · constructor
    · intro h; exact Or.inl ⟨hw, decide_eq_true h⟩
    · rintro (⟨_, h⟩ | ⟨h, _⟩)
      · exact of_decide_eq_true h
      · exact absurd hw h
  · have e : getH K E (p, c) = [childCN K p c] := by
      unfold getH; rw [look_none_of hw]; rfl
    rw [e]
    constructor
    · intro h; exact Or.inr ⟨hw, List.mem_singleton.mp h⟩
    · rintro (⟨h, _⟩ | ⟨_, h⟩)
      · exact absurd h hw
      · exact List.mem_singleton.mpr h

/-- The holders by rule on the universe: the universe cells that hold `o` are the written
holders and the unwritten universe cells with cell name `o`. -/
theorem holders_on (ctx : Ctx) (E : EState) (o : Origin) :
    ∀ p ∈ ctx.origins, ∀ c ∈ ctx.cells,
      (o ∈ (den ctx.K E).heap p c ↔
        (p, c) ∈ holdersW ctx.K E o ∨ ((p, c) ∉ keys E.heap ∧ o = childCN ctx.K p c)) :=
  fun p _ c _ => holders_iff ctx.K E o p c

/-- THE DEFAULT PARENT OF A SYMBOLIC ORIGIN: if the cell name of `(a, c)` is `⟨b.q⟩`, then `a` is
`⟨b.q'⟩` with `q = q' ++ [c]`: the parent is the path without its last cell. -/
theorem dfltParent_sym {K : Nat} {a : Origin} {c : ACell} {b : ABase} {q : List ACell}
    (h : childCN K a c = .sym b q) : a = .sym b q.dropLast ∧ q.getLast? = some c := by
  obtain ⟨q0, rfl, rfl⟩ := childCN_sym_inv h
  exact ⟨by rw [List.dropLast_concat], List.getLast?_concat⟩

end DirectedAlias.Impl.Engine

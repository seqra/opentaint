import ApSpec.BackNDRefine
import ApSpec.BackCondRules

/-!
# Principal examples of `spec/backward-condition-progress.md`

Each example of the spec is a closed computation of the executable model, checked by `decide`.
The names `ex_*` are the example ids of the spec.

Names: bases `x ret arg0 va vb`, accessors `f g h k`, marks `T U`.
-/

namespace ApSpec.BackCondEx

open ApSpec ApSpec.AnyTaintEx

abbrev x : Base := 1
abbrev ret : Base := 4
abbrev arg0 : Base := 5
abbrev va : Base := 6
abbrev vb : Base := 7
abbrev f : Acc := 1
abbrev g : Acc := 2
abbrev h : Acc := 3
abbrev k : Acc := 4
abbrev tT : Mark := 7
abbrev tU : Mark := 8
abbrev T : MarkA := .conc tT
abbrev U : MarkA := .conc tU

def pf (b : Base) (p : List Acc) (κ : Kind) (μ : MarkA) : PFact := ⟨b, p, κ, μ⟩
abbrev s0 : Kind := .star Excl.empty

/-! ## §N.2 Rule conditions -/

/-- Unary `ContainsMarkOnAnyField(ret, T)`: one location below `ret` fires it. -/
theorem ex_c1 : BackCond.fires [[pf ret [] .any T]] [⟨ret, [f], tT⟩] = true := by decide
/-- ND `a.$(T) ∧ b.[any](U)`: `b.f(U)` alone does not fire it. -/
theorem ex_c2 : BackCond.fires [[pf va [] .exact T, pf vb [] .any U]] [⟨vb, [f], tU⟩] = false := by
  decide
/-- ND: with `a(T)` it fires. -/
theorem ex_c3 :
    BackCond.fires [[pf va [] .exact T, pf vb [] .any U]] [⟨va, [], tT⟩, ⟨vb, [f], tU⟩] = true := by
  decide

/-! ## §II.2 The seed layer: `(pattern, demand)` -/

/-- Unary `$`: NORMAL. -/
theorem ex_k1 : BackCond.reqs [[pf ret [] .exact T]] = [⟨pf ret [] .exact T, false⟩] := by decide
/-- Unary `[any]`: DEMAND (W6; the backward run has no `[any-taint]`). -/
theorem ex_k2 : BackCond.reqs [[pf ret [] .any T]] = [⟨pf ret [] .any T, true⟩] := by decide
/-- ND: DEMAND, also the `$` literal. -/
theorem ex_k3 : BackCond.reqs [[pf va [] .exact T, pf vb [] .any U]] =
    [⟨pf va [] .exact T, true⟩, ⟨pf vb [] .any U, true⟩] := by decide

/-! ## §II.4 The meet of a literal with a captured input: `(pattern, exclusion)` -/

/-- Input below the literal: the input. -/
theorem ex_m1 : BackND.meetLit (pf ret [] .any T) (pf ret [f] .exact T) Excl.empty =
    some (pf ret [f] .exact T, Excl.empty) := by decide
/-- Input `[any]` below the literal: the input. -/
theorem ex_m2 : BackND.meetLit (pf ret [] .any T) (pf ret [f] .any T) Excl.empty =
    some (pf ret [f] .any T, Excl.empty) := by decide
/-- Input above the literal: the literal path. -/
theorem ex_m3 : BackND.meetLit (pf ret [f] .any T) (pf ret [] .any T) Excl.empty =
    some (pf ret [f] .any T, Excl.empty) := by decide
/-- The marks differ: no meet. -/
theorem ex_m4 : BackND.meetLit (pf ret [] .any T) (pf ret [f] .exact U) Excl.empty = none := by
  decide

/-! ## The ND literals of c2: `0 = va.$(T)`, `1 = vb.[any](U)` -/

def lits : List PFact := [pf va [] .exact T, pf vb [] .any U]

/-! ## §II.5 Progress: the unary literal `x.[any](T)` of `use(x)` over rounds -/

def litX : List PFact := [pf x [] .any T]

/-- The seeds of a round from the stored leaves of the forward run before it. -/
def seeds (ls : List PFact) (cap : BackND.Cap) : List BackND.Leaf :=
  BackND.treeSeeds ls (BackND.capMeets ls cap)

/-- CURRENT (and the fallback): the seed is the literal in every round. -/
theorem ex_p0 : seeds litX [] = [(0, pf x [] .any T)] := by decide
/-- Forward run 1 cut the fact one field deep: the seed keeps the field. -/
theorem ex_p1 : seeds litX [(0, pf x [f] .any T, Excl.empty)] = [(0, pf x [f] .any T)] := by decide
/-- A forward run cut it one field deeper. -/
theorem ex_p2 : seeds litX [(0, pf x [f, g] .any T, Excl.empty)] = [(0, pf x [f, g] .any T)] := by
  decide
/-- A `$` input (DEMAND by another cause) gives a `$` leaf: no `[any]` entry, no C2 cut. -/
theorem ex_p3 : seeds litX [(0, pf x [f, g, h] .exact T, Excl.empty)] =
    [(0, pf x [f, g, h] .exact T)] := by decide
/-- Two completed combinations: one tree with two leaves. -/
theorem ex_p4 : seeds litX [(0, pf x [f] .any T, Excl.empty), (0, pf x [g] .exact T, Excl.empty)] =
    [(0, pf x [f] .any T), (0, pf x [g] .exact T)] := by decide
/-- A reversed conditional source literal `arg0.[any](U)` with the captured input `arg0.h.$(U)`. -/
theorem ex_s1 : seeds [pf arg0 [] .any U] [(0, pf arg0 [h] .exact U, Excl.empty)] =
    [(0, pf arg0 [h] .exact U)] := by decide

/-! ## §I.3 The capture tree: stored leaves `(literal, pattern)` and the merged tree -/

/-- Meet first: a `$` input below the literal is a `$` leaf; an `[any-taint]/{g}` input (model:
    kind `any` with an exclusion) is an `[any]` leaf, exclusion dropped. -/
theorem ex_t1 : BackND.capMeets litX [(0, pf x [f, g] .exact T, Excl.empty), (0, pf x [h] .any T, .set [g])] =
    [(0, pf x [f, g] .exact T), (0, pf x [h] .any T)] := by decide
/-- An input above the literal: the leaf is at the literal path. -/
theorem ex_t2 : BackND.capMeets [pf x [f] .any T] [(0, pf x [] .any T, Excl.empty)] =
    [(0, pf x [f] .any T)] := by decide
/-- One tree: `x.f.[any]` subsumes `x.f.g.$`; `x.h.$` stays. -/
theorem ex_t3 : BackND.mergeLeaves [(0, pf x [f] .any T), (0, pf x [f, g] .exact T), (0, pf x [h] .exact T)] =
    [(0, pf x [f] .any T), (0, pf x [h] .exact T)] := by decide
/-- One tree: a repeated `$` leaf is kept once. -/
theorem ex_t4 : BackND.mergeLeaves [(0, pf x [g] .exact T), (0, pf x [g] .exact T)] =
    [(0, pf x [g] .exact T)] := by decide
/-- The ND literals of c2: literal 0 (`$`, not captured) keeps its seed; literal 1 gets its tree. -/
theorem ex_t5 : BackND.treeSeeds lits (BackND.capMeets lits
      [(1, pf vb [f] .exact U, Excl.empty), (1, pf vb [g, h] .exact U, Excl.empty)]) =
    [(0, pf va [] .exact T), (1, pf vb [f] .exact U), (1, pf vb [g, h] .exact U)] := by decide
/-- An input with the abstract mark gives no leaf (no meet), so literal 1 keeps its seed: the
    normal form (the matched concrete mark) is needed for progress, not for soundness. -/
theorem ex_t6 : BackND.treeSeeds lits (BackND.capMeets lits [(1, pf vb [f] s0 .star, Excl.empty)]) =
    [(0, pf va [] .exact T), (1, pf vb [] .any U)] := by decide

end ApSpec.BackCondEx

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

/-! ## §II.4 Refinement: literals `0 = va.$(T)`, `1 = vb.[any](U)` (ND) -/

def lits : List PFact := [pf va [] .exact T, pf vb [] .any U]

theorem ex_n1 : BackND.refine lits [(0, pf va [] .exact T, Excl.empty), (1, pf vb [f] .exact U, Excl.empty),
    (1, pf vb [g, h] .exact U, Excl.empty)] =
    [(0, pf va [] .exact T, Excl.empty), (1, pf vb [f] .exact U, Excl.empty),
     (1, pf vb [g, h] .exact U, Excl.empty)] := by decide
theorem ex_n2 : BackND.refine lits [(1, pf vb [g] .any U, .set [k])] =
    [(0, pf va [] .exact T, Excl.empty), (1, pf vb [g] .any U, .set [k])] := by decide
theorem ex_n3 : BackND.refine lits [] =
    [(0, pf va [] .exact T, Excl.empty), (1, pf vb [] .any U, Excl.empty)] := by decide
/-- A capture with the abstract mark: literal 1 gets no seed (the normal form prevents it). -/
theorem ex_n4 : BackND.refine lits [(1, pf vb [f] s0 .star, Excl.empty)] =
    [(0, pf va [] .exact T, Excl.empty)] := by decide

/-! ## §II.5 Progress: the unary literal `x.[any](T)` of `use(x)` over rounds -/

def litX : List PFact := [pf x [] .any T]

/-- CURRENT (and the fallback): the seed is the literal in every round. -/
theorem ex_p0 : BackND.refine litX [] = [(0, pf x [] .any T, Excl.empty)] := by decide
/-- Forward run 1 cut the fact one field deep: the seed keeps the field. -/
theorem ex_p1 : BackND.refine litX [(0, pf x [f] .any T, Excl.empty)] =
    [(0, pf x [f] .any T, Excl.empty)] := by decide
/-- Forward run 3 cut it one field deeper. -/
theorem ex_p2 : BackND.refine litX [(0, pf x [f, g] .any T, Excl.empty)] =
    [(0, pf x [f, g] .any T, Excl.empty)] := by decide
/-- A `$` capture (DEMAND by another cause) gives a `$` seed: no `[any]` entry. -/
theorem ex_p3 : BackND.refine litX [(0, pf x [f, g, h] .exact T, Excl.empty)] =
    [(0, pf x [f, g, h] .exact T, Excl.empty)] := by decide
/-- Two completed combinations: two seeds. -/
theorem ex_p4 : BackND.refine litX [(0, pf x [f] .any T, Excl.empty), (0, pf x [g] .exact T, Excl.empty)] =
    [(0, pf x [f] .any T, Excl.empty), (0, pf x [g] .exact T, Excl.empty)] := by decide
/-- A reversed conditional source literal `arg0.[any](U)` with the captured input `arg0.h.$(U)`. -/
theorem ex_s1 : BackND.refine [pf arg0 [] .any U] [(0, pf arg0 [h] .exact U, Excl.empty)] =
    [(0, pf arg0 [h] .exact U, Excl.empty)] := by decide

end ApSpec.BackCondEx

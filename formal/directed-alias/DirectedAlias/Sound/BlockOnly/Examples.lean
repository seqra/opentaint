import DirectedAlias.Sound.BlockOnly.Soundness
import DirectedAlias.Sound.CellNamed.Examples

/-!
# Examples of design BO

* Both cases of `HavocNeed` answer true (the empty cell case needs the empty-cell fix).
* The spread of the shared havoc origin on `pHv` is gone; the dead-end case aliases.
* The gain of narrow reach: after `touch()` the store through `t = this.box` stays strong.
* Trace C: `t = x.f; m(x); t.g = null; u = x.f; a = u.g; b = u.g` answers `a ~ b` true, and the
  alias is real (the store after the call is weak because `x.f` is below `Etree`).
* The `Eval` case: `z = new; z.g = e; x.f = z; m(x); t = x.f; t.g = v` keeps `z.g ~ e`, and the
  alias is real. Without the `Eval` rule the store is strong and the alias is lost.
* The losses of design CN: L2 and L3 are gone (BO answers false, which is exact), L1 stays.
* The new loss L4: `u = b.value; this.box = b; touch(this); b.value = v`: `b` is in `Eval`, so
  the store is weak and `b.value ~ u` stays; no execution has this alias.
* The join example, the field example and `loop_bf_x` keep their answers.

The checks use `decide +kernel` with small `K`; the soundness theorem holds for each `K`.
-/

namespace DirectedAlias.Sound.BlockOnly.Examples

open DirectedAlias DirectedAlias.Sound DirectedAlias.Sound.Havoc DirectedAlias.Sound.HavocRecency
open DirectedAlias.Sound.CellNamed DirectedAlias.Sound.BlockOnly DirectedAlias.Sound.Recency

/-! ## Why an unresolved call needs a havoc origin (`HavocNeed`) -/

section need

open DirectedAlias.HavocNeed

/-- Design BO answers true in both cases of `HavocNeed`: after the call, the store through
`t = x.f` is weak, and the loads of a cell of a new object alias. -/
theorem need_answersBO :
    mayProgBO true 0 [] fr pStrong vw [.fld fg] ve [] = true ∧
      mayProgBO true 1 [] fr pStrong vw [.fld fg] ve [] = true ∧
      mayProgBO true 0 [] fr pEmpty va [] vb [] = true ∧
      mayProgBO true 1 [] fr pEmpty va [] vb [] = true ∧
      mayProgBO false 0 [] fr pEmpty va [] vb [] = true := by decide +kernel

end need

/-! ## The shared havoc spread is gone -/

section spread

open DirectedAlias.Examples DirectedAlias.Sound.Havoc.Examples

/-- On `pHv = m(x); a = x.f; b = y.g`, design BO answers false for `a ~ b`, `a ~ z.f` and
`a ~ w.g`, and true for `a ~ x.f` (both policies). -/
theorem spread_goneBO :
    mayProgBO true 0 [] fr pHv va [] vb [] = false ∧
      mayProgBO true 0 [] fr pHv va [] vz [.fld ff] = false ∧
      mayProgBO true 0 [] fr pHv va [] vw [.fld fg] = false ∧
      mayProgBO true 0 [] fr pHv va [] vx [.fld ff] = true ∧
      mayProgBO false 0 [] fr pHv va [] vb [] = false ∧
      mayProgBO true 1 [] fr pHv va [] vb [] = false := by decide +kernel

/-- Under strict narrow A2, no execution of `pHv` aliases `a` and `b` (by design BO). -/
theorem spread_ab_noneBO (src : Nat → Obj × Cell) : ¬ CAliasN src [] fr pHv va [] vb [] :=
  no_alias_of_mayProgBO src [] true 0 fr pHv va [] vb [] spread_goneBO.1

end spread

/-! ## The other examples keep their answers -/

section other

open DirectedAlias.Examples

/-- The join example, the field example, the strong-update example, the call example and
`loop_bf_x` keep their answers in design BO. -/
theorem other_answersBO :
    mayProgBO true 2 [] fr pJoin va [] vx [] = true ∧
      mayProgBO true 2 [] fr pJoin va [] vy [] = true ∧
      mayProgBO true 2 [] fr pJoin vx [] vy [] = false ∧
      mayProgBO true 1 [] fr pField vx [.fld ff] vz [] = true ∧
      mayProgBO true 1 [] fr pField vy [.fld ff] vz [] = true ∧
      mayProgBO true 1 [] fr pField vx [] vy [] = false ∧
      mayProgBO true 1 [] fr pField va [] vx [] = false ∧
      mayProgBO true 1 [] fr pField va [] vw [] = true ∧
      mayProgBO true 1 [] fr pStrong vb [.fld ff] vx [] = false ∧
      mayProgBO true 1 [] fr pStrong vb [.fld ff] vy [] = true ∧
      mayProgBO true 1 [] fr pCall vw [] vx [.fld ff] = true := by decide +kernel

/-- `loop_bf_x` stays fixed in design BO: after the loop, `b.f` does not alias `x` (both
policies), and `b.f` may alias `y`. -/
theorem loop_bf_x_BO :
    mayProgBO true 1 [] fr pLoop vb [.fld ff] vx [] = false ∧
      mayProgBO false 1 [] fr pLoop vb [.fld ff] vx [] = false ∧
      mayProgBO true 1 [] fr pLoop vb [.fld ff] vy [] = true := by decide +kernel

end other

/-! ## Examples with the variables of design CN -/

open DirectedAlias.Sound.CellNamed.Examples

/-- In the dead-end case, design BO answers `b ~ d` true (the alias is real: `dead_realN`). -/
theorem dead_answerBO :
    mayProgBO true 0 [] frN pDead vb [] vd [] = true ∧
      mayProgBO true 1 [] frN pDead vb [] vd [] = true := by decide +kernel

/-- NARROW REACH GAIN: `touch()` does not expose `this`, so the store `t.value = z` is strong.
With `touch(this)`, or with `this` as a static root, the store is weak. An unrelated static
root does not change the answer. -/
theorem gain_answersBO :
    mayProgBO true 1 [] frN (pGain []) vt [.fld fg] vu [] = false ∧
      mayProgBO true 1 [5] frN (pGain []) vt [.fld fg] vu [] = false ∧
      mayProgBO true 1 [] frN (pGain [vx]) vt [.fld fg] vu [] = true ∧
      mayProgBO true 1 [0] frN (pGain []) vt [.fld fg] vu [] = true := by decide +kernel

/-- Under strict narrow A2, after `touch()` no execution aliases `t.value` and the old content
`u` (by design BO). -/
theorem gain_noneBO (src : Nat → Obj × Cell) :
    ¬ CAliasN src [] frN (pGain []) vt [.fld fg] vu [] :=
  no_alias_of_mayProgBO src [] true 1 frN (pGain []) vt [.fld fg] vu [] gain_answersBO.1

/-! ## Trace C -/

/-- Trace C: `t = x.f; m(x)@9; n = null; t.g = n; u = x.f; a = u.g; b = u.g`. -/
def pC : Prog :=
  .seq (.stmt (.load vt vx ff)) <| .seq (.stmt (.call none 9 [vx])) <|
  .seq (.stmt (.null vn)) <| .seq (.stmt (.store vt fg vn)) <|
  .seq (.stmt (.load vu vx ff)) <| .seq (.stmt (.load va vu fg)) (.stmt (.load vb vu fg))

/-- TRACE C: design BO answers `a ~ b` true. The store `t.g = null` after the call is weak,
because `t` has the origin `x.f`, which is below the reached `x`. -/
theorem traceC_answerBO :
    mayProgBO true 0 [] frN pC va [] vb [] = true ∧
      mayProgBO true 1 [] frN pC va [] vb [] = true ∧
      mayProgBO true 2 [] frN pC va [] vb [] = true := by decide +kernel

/-- The alias of trace C is real: the callee writes a new object into `x.f`; then `u` is that
object, and `a` and `b` are its child at `g`. -/
theorem traceC_realN : CAliasN (srcL [(.sym (.root 0) [], .fld ff)]) [] frN pC va [] vb [] :=
  runAliasBN_sound (cs := [.havoc [⟨.arg vx, [], .fld ff, 0⟩]]) (by decide)

/-! ## The `Eval` case -/

/-- The `Eval` case: `n = new@5; n.g = y; x.f = n; m(x)@9; t = x.f; t.g = z`. The query is
`n.g ~ y`. -/
def pE : Prog :=
  .seq (.stmt (.new vn 5)) <| .seq (.stmt (.store vn fg vy)) <|
  .seq (.stmt (.store vx ff vn)) <| .seq (.stmt (.call none 9 [vx])) <|
  .seq (.stmt (.load vt vx ff)) (.stmt (.store vt fg vz))

/-- THE `Eval` CASE: design BO keeps `n.g ~ y`. The origin `new(5)` was the content of the
reached cell `x.f`, so it is in `Eval`, and the store `t.g = z` is weak. -/
theorem eval_answerBO :
    mayProgBO true 0 [] frN pE vn [.fld fg] vy [] = true ∧
      mayProgBO true 1 [] frN pE vn [.fld fg] vy [] = true ∧
      mayProgBO false 1 [] frN pE vn [.fld fg] vy [] = true := by decide +kernel

/-- The alias of the `Eval` case is real: the callee writes a new object into `x.f`, so `t` is
that object, and `n.g` stays `y`. -/
theorem eval_realN : CAliasN (srcL [(.sym (.root 0) [], .fld ff)]) [] frN pE vn [.fld fg] vy [] :=
  runAliasBN_sound (cs := [.havoc [⟨.arg vx, [], .fld ff, 0⟩]]) (by decide)

/-- Design BO without the `Eval` rule: the store tests only the recency rule and the prefix
rule of `Etree`. -/
def storeNoV (cb : CtxB) (X : AState) (x : Var) (c : ACell) (S : List Origin) : AState :=
  match single? (X.env x) with
  | some o =>
    if uniqueCN cb.cn.ctx.once cb.cn.ctx.entryUnique (X.env cb.cn.xe) o then X.setCell o c S
    else X.weakStore (X.env x) c S
  | none => X.weakStore (X.env x) c S

/-- The transfer of design BO without the `Eval` rule. -/
def astepNoV (cb : CtxB) : Stmt → AState → AState
  | .store x f y, X => storeNoV cb X x (.fld f) (X.env y)
  | st, X => astepBO cb st X

/-- The analysis of design BO without the `Eval` rule. -/
def analyzeNoV (cb : CtxB) : Prog → AState → AState
  | .skip, X => X
  | .stmt s, X => astepNoV cb s X
  | .seq p q, X => analyzeNoV cb q (analyzeNoV cb p X)
  | .choice p q, X => join (analyzeNoV cb p X) (analyzeNoV cb q X)
  | .loop p, X => loopIter cb.cn.ctx (analyzeNoV cb p) cb.cn.ctx.fuel X

/-- May-alias of design BO without the `Eval` rule. -/
def mayProgNoV (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (x : Var) (px : List ACell) (y : Var) (py : List ACell) : Bool :=
  may (analyzeNoV (ctxBO eu K statics fr p (afields px ++ afields py)) p (ainit K fr)) x px y py

/-- Without the `Eval` rule, design BO answers `n.g ~ y` false. -/
theorem noV_answer : mayProgNoV true 1 [] frN pE vn [.fld fg] vy [] = false := by decide +kernel

/-- THE `Eval` RULE IS NECESSARY: without it, the store `t.g = z` is strong, and the real
alias `n.g ~ y` is lost. -/
theorem eval_needed :
    mayProgNoV true 1 [] frN pE vn [.fld fg] vy [] = false ∧
      CAliasN (srcL [(.sym (.root 0) [], .fld ff)]) [] frN pE vn [.fld fg] vy [] :=
  ⟨noV_answer, eval_realN⟩

/-! ## The losses of design CN -/

/-- L2 AND L3 ARE GONE: design BO answers false for `t ~ w` in L2 and for `a ~ c` in L3 (the
callee object is named by the old content `y` or `z`, not by the entry name). L1 STAYS: the
store `t.g = z` is weak, because `t` has the origin `x.f` below the reached `x`. -/
theorem losses_BO :
    mayProgBO true 1 [] frN pL1 vt [.fld fg] vu [] = true ∧
      mayProgBO true 0 [] frN pL2 vt [] vw [] = false ∧
      mayProgBO true 1 [] frN pL2 vt [] vw [] = false ∧
      mayProgBO true 0 [] frN pL3 va [] vc [] = false ∧
      mayProgBO true 1 [] frN pL3 va [] vc [] = false := by decide +kernel

/-- The false answers of L2 and L3 are exact: no strict narrow execution aliases the paths
(`loss2_noneN`, `loss3_noneN`), and design BO agrees with that. -/
theorem losses_exactBO (src : Nat → Obj × Cell) :
    ¬ CAliasN src [] frN pL2 vt [] vw [] ∧ ¬ CAliasN src [] frN pL3 va [] vc [] :=
  ⟨no_alias_of_mayProgBO src [] true 0 frN pL2 vt [] vw [] losses_BO.2.1,
    no_alias_of_mayProgBO src [] true 0 frN pL3 va [] vc [] losses_BO.2.2.2.1⟩

/-! ## The new loss L4 -/

/-- L4: `u = b.value; this.box = b; touch(this)@9; b.value = v` (`this` is `x`, `b` is `y`,
`v` is `z`; `box` is `f`, `value` is `g`). -/
def pL4 : Prog :=
  .seq (.stmt (.load vu vy fg)) <| .seq (.stmt (.store vx ff vy)) <|
  .seq (.stmt (.call none 9 [vx])) (.stmt (.store vy fg vz))

/-- THE NEW LOSS L4: design BO answers `b.value ~ u` true. The origin of `b` was the content of
the reached cell `this.box`, so it is in `Eval`, and the store `b.value = v` is weak; the old
content `u` stays in `b.value`. Design CN answers false (the store is strong). -/
theorem loss4_BO :
    mayProgBO true 0 [] frN pL4 vy [.fld fg] vu [] = true ∧
      mayProgBO true 1 [] frN pL4 vy [.fld fg] vu [] = true ∧
      mayProgCN true 1 [] frN pL4 vy [.fld fg] vu [] = false := by decide +kernel

/-- L4 has no execution: under strict narrow A2, `b.value` is `v` after the store, and no
execution aliases `b.value` and `u` (by the soundness of design CN). -/
theorem loss4_noneN (src : Nat → Obj × Cell) : ¬ CAliasN src [] frN pL4 vy [.fld fg] vu [] :=
  no_alias_of_mayProgCN src [] true 1 frN pL4 vy [.fld fg] vu [] loss4_BO.2.2

end DirectedAlias.Sound.BlockOnly.Examples

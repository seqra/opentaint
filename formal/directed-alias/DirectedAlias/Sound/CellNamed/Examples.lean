import DirectedAlias.Sound.CellNamed.Soundness
import DirectedAlias.Sound.CellNamed.Run
import DirectedAlias.Sound.HavocRecency.Examples
import DirectedAlias.HavocNeed

/-!
# Examples of design CN

* Both cases of `HavocNeed` answer true, and both aliases are real under strict narrow A2.
* The spread of the shared havoc origin on `pHv` is gone.
* The dead-end case: `n = new; m(n); a = n.f; if (*) { b = a; d = a } else { b = y; d = z }`
  answers `b ~ d` true, and the alias is real.
* The gain of narrow reach: after `touch()` the store through `t = this.box` stays strong.
* The three accepted losses L1, L2, L3: design CN answers true, the per-cell reference
  (`mayProgHR`, sound for strict A2) answers false, so no strict narrow execution aliases
  the two paths.
* The join example, the field example and `loop_bf_x` keep their answers.

The checks use `decide +kernel` with small `K`; the soundness theorem holds for each `K`.
-/

namespace DirectedAlias.Sound.CellNamed.Examples

open DirectedAlias DirectedAlias.Sound DirectedAlias.Sound.Havoc DirectedAlias.Sound.HavocRecency
open DirectedAlias.Sound.CellNamed

/-! ## Why an unresolved call needs a havoc origin (`HavocNeed`) -/

section need

open DirectedAlias.HavocNeed

/-- Design CN answers true in both cases of `HavocNeed`: after the call, the store through
`t = x.f` is weak, and the loads of a cell of a new object alias. -/
theorem need_answersCN :
    mayProgCN true 0 [] fr pStrong vw [.fld fg] ve [] = true ∧
      mayProgCN true 1 [] fr pStrong vw [.fld fg] ve [] = true ∧
      mayProgCN true 0 [] fr pEmpty va [] vb [] = true ∧
      mayProgCN true 1 [] fr pEmpty va [] vb [] = true := by decide +kernel

/-- The first alias is real under strict narrow A2: the callee writes a new object into `x.f`. -/
theorem strong_after_call_realN :
    CAliasN (srcL [(.sym (.root 0) [], .fld ff)]) [] fr pStrong vw [.fld fg] ve [] :=
  runAliasBN_sound (cs := [.havoc [⟨.arg vx, [], .fld ff, 0⟩]]) (by decide)

/-- The second alias is real under strict narrow A2: the callee writes a new object into
`n.f`. -/
theorem empty_cell_realN :
    CAliasN (srcL [(.alloc 5 0, .fld ff)]) [] fr pEmpty va [] vb [] :=
  runAliasBN_sound (cs := [.havoc [⟨.arg vn, [], .fld ff, 0⟩]]) (by decide)

end need

/-! ## The shared havoc spread is gone -/

section spread

open DirectedAlias.Examples DirectedAlias.Sound.Havoc.Examples

/-- On `pHv = m(x); a = x.f; b = y.g`, design CN answers false for `a ~ b`, `a ~ z.f` and
`a ~ w.g`, and true for `a ~ x.f` (both policies). -/
theorem spread_goneCN :
    mayProgCN true 0 [] fr pHv va [] vb [] = false ∧
      mayProgCN true 0 [] fr pHv va [] vz [.fld ff] = false ∧
      mayProgCN true 0 [] fr pHv va [] vw [.fld fg] = false ∧
      mayProgCN true 0 [] fr pHv va [] vx [.fld ff] = true ∧
      mayProgCN false 0 [] fr pHv va [] vb [] = false ∧
      mayProgCN true 1 [] fr pHv va [] vb [] = false := by decide +kernel

/-- Under strict narrow A2, no execution of `pHv` aliases `a` and `b`. -/
theorem spread_ab_noneN (src : Nat → Obj × Cell) : ¬ CAliasN src [] fr pHv va [] vb [] :=
  no_alias_of_mayProgCN src [] true 0 fr pHv va [] vb [] spread_goneCN.1

/-- The answer `a ~ x.f` is realized: the callee keeps `x.f`. -/
theorem spread_axf_keepN : CAliasN (srcL []) [] fr pHv va [] vx [.fld ff] :=
  runAliasBN_sound (cs := [.havoc []]) (by decide)

end spread

/-! ## The other examples keep their answers -/

section other

open DirectedAlias.Examples

/-- The join example, the field example, the strong-update example, the call example and
`loop_bf_x` keep their answers in design CN. -/
theorem other_answersCN :
    mayProgCN true 2 [] fr pJoin va [] vx [] = true ∧
      mayProgCN true 2 [] fr pJoin va [] vy [] = true ∧
      mayProgCN true 2 [] fr pJoin vx [] vy [] = false ∧
      mayProgCN true 1 [] fr pField vx [.fld ff] vz [] = true ∧
      mayProgCN true 1 [] fr pField vy [.fld ff] vz [] = true ∧
      mayProgCN true 1 [] fr pField vx [] vy [] = false ∧
      mayProgCN true 1 [] fr pField va [] vx [] = false ∧
      mayProgCN true 1 [] fr pField va [] vw [] = true ∧
      mayProgCN true 1 [] fr pStrong vb [.fld ff] vx [] = false ∧
      mayProgCN true 1 [] fr pStrong vb [.fld ff] vy [] = true ∧
      mayProgCN true 1 [] fr pCall vw [] vx [.fld ff] = true := by decide +kernel

/-- `loop_bf_x` stays fixed in design CN: after the loop, `b.f` does not alias `x` (both
policies), and `b.f` may alias `y`. -/
theorem loop_bf_x_CN :
    mayProgCN true 1 [] fr pLoop vb [.fld ff] vx [] = false ∧
      mayProgCN false 1 [] fr pLoop vb [.fld ff] vx [] = false ∧
      mayProgCN true 1 [] fr pLoop vb [.fld ff] vy [] = true := by decide +kernel

end other

/-! ## Variables of the new examples -/

/-- Variable `x` (root 0, `this` in the narrow-reach example). -/
abbrev vx : Var := 0
/-- Variable `y` (root 1). -/
abbrev vy : Var := 1
/-- Variable `z` (root 2). -/
abbrev vz : Var := 2
/-- Variable `t`. -/
abbrev vt : Var := 3
/-- Variable `u`. -/
abbrev vu : Var := 4
/-- Variable `a`. -/
abbrev va : Var := 5
/-- Variable `b`. -/
abbrev vb : Var := 6
/-- Variable `c`. -/
abbrev vc : Var := 7
/-- Variable `d`. -/
abbrev vd : Var := 8
/-- Variable `n`. -/
abbrev vn : Var := 9
/-- Variable `w`. -/
abbrev vw : Var := 10
/-- Field `f` (`box` in the narrow-reach example). -/
abbrev ff : Field := 0
/-- Field `g` (`value` in the narrow-reach example). -/
abbrev fg : Field := 1

/-- The frame: `x`, `y`, `z` hold the distinct roots 0, 1, 2. -/
def frN : Frame := ⟨[(vx, 0), (vy, 1), (vz, 2)]⟩

/-! ## The dead-end case -/

/-- `n = new@5; m(n); a = n.f; if (*) { b = a; d = a } else { b = y; d = z }`. -/
def pDead : Prog :=
  .seq (.stmt (.new vn 5)) <| .seq (.stmt (.call none 9 [vn])) <| .seq (.stmt (.load va vn ff)) <|
  .choice (.seq (.stmt (.copy vb va)) (.stmt (.copy vd va)))
    (.seq (.stmt (.copy vb vy)) (.stmt (.copy vd vz)))

/-- In the dead-end case, design CN answers `b ~ d` true. -/
theorem dead_answerCN :
    mayProgCN true 0 [] frN pDead vb [] vd [] = true ∧
      mayProgCN true 1 [] frN pDead vb [] vd [] = true := by decide +kernel

/-- The alias `b ~ d` is real: the callee writes a new object into `n.f`, and the left branch
runs. -/
theorem dead_realN : CAliasN (srcL [(.alloc 5 0, .fld ff)]) [] frN pDead vb [] vd [] :=
  runAliasBN_sound (cs := [.havoc [⟨.arg vn, [], .fld ff, 0⟩], .left]) (by decide)

/-! ## The gain of narrow reach -/

/-- `t = this.box; u = t.value; touch(args); t.value = z`. -/
def pGain (args : List Var) : Prog :=
  .seq (.stmt (.load vt vx ff)) <| .seq (.stmt (.load vu vt fg)) <|
  .seq (.stmt (.call none 9 args)) (.stmt (.store vt fg vz))

/-- NARROW REACH GAIN: `touch()` without arguments and without statics does not expose
`this`, so the store `t.value = z` is strong and the old content `u` is removed. With
`touch(this)`, or with `this` as a static root, the store is weak. An unrelated static root
does not change the answer. -/
theorem gain_answersCN :
    mayProgCN true 1 [] frN (pGain []) vt [.fld fg] vu [] = false ∧
      mayProgCN true 1 [5] frN (pGain []) vt [.fld fg] vu [] = false ∧
      mayProgCN true 1 [] frN (pGain [vx]) vt [.fld fg] vu [] = true ∧
      mayProgCN true 1 [0] frN (pGain []) vt [.fld fg] vu [] = true := by decide +kernel

/-- Under strict narrow A2, after `touch()` no execution aliases `t.value` and the old content
`u`. -/
theorem gain_noneN (src : Nat → Obj × Cell) : ¬ CAliasN src [] frN (pGain []) vt [.fld fg] vu [] :=
  no_alias_of_mayProgCN src [] true 1 frN (pGain []) vt [.fld fg] vu [] gain_answersCN.1

/-! ## The accepted losses -/

/-- L1: `t = x.f; u = t.g; m(x); t.g = z` (this is `pGain [x]`). -/
def pL1 : Prog := pGain [vx]

/-- L2: `w = x.f; x.f = y; m(x); t = x.f`. -/
def pL2 : Prog :=
  .seq (.stmt (.load vw vx ff)) <| .seq (.stmt (.store vx ff vy)) <|
  .seq (.stmt (.call none 9 [vx])) (.stmt (.load vt vx ff))

/-- L3: `x.f = y; m(x); a = x.f; x.f = z; m'(x); c = x.f`. -/
def pL3 : Prog :=
  .seq (.stmt (.store vx ff vy)) <| .seq (.stmt (.call none 9 [vx])) <|
  .seq (.stmt (.load va vx ff)) <| .seq (.stmt (.store vx ff vz)) <|
  .seq (.stmt (.call none 8 [vx])) (.stmt (.load vc vx ff))

/-- THE THREE LOSSES: design CN answers true. L1: the store `t.g = z` is weak, because `x` is
exposed and `t` has the cell name `x.f`; the old alias `t.g ~ u` survives. L2: the callee
object in `x.f` has the entry name of `x.f`, so `t ~ w`. L3: the callee objects of the two
calls have the same name, so `a ~ c`. -/
theorem losses_CN :
    mayProgCN true 1 [] frN pL1 vt [.fld fg] vu [] = true ∧
      mayProgCN true 0 [] frN pL2 vt [] vw [] = true ∧
      mayProgCN true 1 [] frN pL2 vt [] vw [] = true ∧
      mayProgCN true 0 [] frN pL3 va [] vc [] = true ∧
      mayProgCN true 1 [] frN pL3 va [] vc [] = true := by decide +kernel

/-- The per-cell reference (recency with per-cell havoc, generous reach) answers false for the
three losses. -/
theorem losses_HR :
    mayProgHR true 1 frN pL1 vt [.fld fg] vu [] = false ∧
      mayProgHR true 0 frN pL2 vt [] vw [] = false ∧
      mayProgHR true 0 frN pL3 va [] vc [] = false := by decide +kernel

/-- L1 has no execution: under strict narrow A2, no execution aliases `t.g` and `u`. -/
theorem loss1_noneN (src : Nat → Obj × Cell) (statics : List Root) :
    ¬ CAliasN src statics frN pL1 vt [.fld fg] vu [] := fun h =>
  no_alias_of_mayProgHR src true 1 frN pL1 vt [.fld fg] vu [] losses_HR.1 h.toCAliasS

/-- L2 has no execution: under strict narrow A2, no execution aliases `t` and `w`. -/
theorem loss2_noneN (src : Nat → Obj × Cell) (statics : List Root) :
    ¬ CAliasN src statics frN pL2 vt [] vw [] := fun h =>
  no_alias_of_mayProgHR src true 0 frN pL2 vt [] vw [] losses_HR.2.1 h.toCAliasS

/-- L3 has no execution: under strict narrow A2, no execution aliases `a` and `c`. -/
theorem loss3_noneN (src : Nat → Obj × Cell) (statics : List Root) :
    ¬ CAliasN src statics frN pL3 va [] vc [] := fun h =>
  no_alias_of_mayProgHR src true 0 frN pL3 va [] vc [] losses_HR.2.2 h.toCAliasS

end DirectedAlias.Sound.CellNamed.Examples

import DirectedAlias.Sound.ValueSem.Run
import DirectedAlias.Sound.BlockOnly.Examples
import DirectedAlias.Sound.BlockOnly.Unsound

/-!
# Examples of design VS

* THE USER'S RULE: `x = new; a = x.f` gives `a ~ x.f` without a call, and the alias is real:
  `a` and `x.f` are the same null instance (the default null of the cell). Object semantics
  (design CN) answers false, and no execution aliases them as objects: the value relation is
  wider only by null instances.
* `n = new; m(n); a = n.f; b = n.f`, the join case and the loop case of `Unsound.lean`, and
  the null-store case `x.f = null; m(x); a = x.f; b = x.f` all answer true, and all are real
  (with and without a callee write).
* Distinct null sites do not alias (`a = null; b = null`), and two unwritten fields of
  objects of different sites do not alias. Both false answers are exact (`csoundVS`).
* The examples of design BO keep their answers: `HavocNeed`, `pHv`, the dead-end case, the gain,
  trace C, the `Eval` case, L1 to L4, the join and field examples, `loop_bf_x`.
* DEFINITE ASSIGNMENT IS NEEDED: if an unassigned variable held a siteless null (the IR frame
  semantics), its store would make an EMPTY cell, and a later callee write into that cell
  would be invisible (`siteless_unsound`). With a null site the alias is kept.

The checks use `decide +kernel` with small `K`; the soundness theorem holds for each `K`.
-/

namespace DirectedAlias.Sound.ValueSem.Examples

open DirectedAlias DirectedAlias.Sound DirectedAlias.Sound.Havoc DirectedAlias.Sound.HavocRecency
open DirectedAlias.Sound.CellNamed DirectedAlias.Sound.BlockOnly DirectedAlias.Sound.ValueSem

/-! ## Variables -/

namespace U

/-- Variable `x`. -/
abbrev vx : Var := 0
/-- Variable `a`. -/
abbrev va : Var := 1
/-- Variable `y`. -/
abbrev vy : Var := 2
/-- Variable `b`. -/
abbrev vb : Var := 3
/-- Variable `n`. -/
abbrev vn : Var := 4
/-- Variable `u` (unbound in the frames). -/
abbrev vu : Var := 5
/-- Field `f`. -/
abbrev ff : Field := 0

/-- The empty frame. -/
def frE : Frame := ⟨[]⟩

/-- The frame where `x` holds root 0. -/
def frX : Frame := ⟨[(vx, 0)]⟩

/-- The callee writes one new object into `x.f` (tag 0). -/
def wxf : HavocW := ⟨.arg vx, [], .fld ff, 0⟩

end U

section user

open U

/-! ## The user's rule -/

/-- `x = new@5; a = x.f`. -/
def pUser : Prog := .seq (.stmt (.new vx 5)) (.stmt (.load va vx ff))

/-- `x = new@5; m(x)@9; a = x.f`. -/
def pUserCall : Prog :=
  .seq (.stmt (.new vx 5)) (.seq (.stmt (.call none 9 [vx])) (.stmt (.load va vx ff)))

/-- THE USER'S RULE: design VS answers `a ~ x.f` true after `x = new; a = x.f`, with and without
a call. Design CN and design BO answer false without the call (object semantics). -/
theorem user_answers :
    mayProgVS true 0 [] frE pUser va [] vx [.fld ff] = true ∧
      mayProgVS true 1 [] frE pUser va [] vx [.fld ff] = true ∧
      mayProgVS false 1 [] frE pUser va [] vx [.fld ff] = true ∧
      mayProgVS true 1 [] frE pUserCall va [] vx [.fld ff] = true ∧
      mayProgCN true 1 [] frE pUser va [] vx [.fld ff] = false ∧
      mayProgBO true 1 [] frE pUser va [] vx [.fld ff] = false := by decide +kernel

/-- The alias of the user's rule is real: `a` and `x.f` are the same null instance. -/
theorem user_real : CAliasV (srcL []) [] frE pUser va [] vx [.fld ff] :=
  runAliasV_sound (cs := []) (by decide)

/-- With the call, the alias is real both when the callee keeps the cell (the same null
instance) and when it writes a new object into it (the same object). -/
theorem user_call_real :
    CAliasV (srcL []) [] frE pUserCall va [] vx [.fld ff] ∧
      CAliasV (srcL [(.alloc 5 0, .fld ff)]) [] frE pUserCall va [] vx [.fld ff] :=
  ⟨runAliasV_sound (cs := [.havoc []]) (by decide),
    runAliasV_sound (cs := [.havoc [wxf]]) (by decide)⟩

/-- THE VALUE RELATION IS WIDER ONLY BY NULL INSTANCES: in the user's rule no execution aliases
`a` and `x.f` as objects (by design CN), but they are the same null instance. -/
theorem user_wider (src : Nat → Obj × Cell) :
    ¬ CAliasN src [] frE pUser va [] vx [.fld ff] ∧ CAliasV (srcL []) [] frE pUser va [] vx [.fld ff] :=
  ⟨no_alias_of_mayProgCN src [] true 1 frE pUser va [] vx [.fld ff] user_answers.2.2.2.2.1,
    user_real⟩

end user

/-! ## Reads after calls, joins and loops -/

section need

open DirectedAlias.HavocNeed

/-- `n = new; m(n); a = n.f; b = n.f` (`pEmpty`): design VS answers `a ~ b` true (both
policies). -/
theorem empty_answersVS :
    mayProgVS true 0 [] fr pEmpty va [] vb [] = true ∧
      mayProgVS true 1 [] fr pEmpty va [] vb [] = true ∧
      mayProgVS false 1 [] fr pEmpty va [] vb [] = true := by decide +kernel

/-- The alias of `pEmpty` is real: the same null instance if the callee keeps `n.f`, the same
object if it writes `n.f`. -/
theorem empty_realV :
    CAliasV (srcL []) [] fr pEmpty va [] vb [] ∧
      CAliasV (srcL [(.alloc 5 0, .fld ff)]) [] fr pEmpty va [] vb [] :=
  ⟨runAliasV_sound (cs := [.havoc []]) (by decide),
    runAliasV_sound (cs := [.havoc [⟨.arg vn, [], .fld ff, 0⟩]]) (by decide)⟩

/-- `HavocNeed` strong-after-call: the store after the call is weak and `w.g ~ e` stays. -/
theorem strong_answersVS :
    mayProgVS true 0 [] fr pStrong vw [.fld fg] ve [] = true ∧
      mayProgVS true 1 [] fr pStrong vw [.fld fg] ve [] = true := by decide +kernel

/-- The alias `w.g ~ e` of `HavocNeed` is a real value alias. -/
theorem strong_realV :
    CAliasV (srcL [(.sym (.root 0) [], .fld ff)]) [] fr pStrong vw [.fld fg] ve [] :=
  runAliasV_sound (cs := [.havoc [⟨.arg vx, [], .fld ff, 0⟩]]) (by decide)

end need

section unsound

open DirectedAlias.Sound.BlockOnly.Unsound

/-- THE JOIN AND LOOP CASES OF `Unsound.lean`: design VS answers `t ~ x.f` true (both policies);
the heap was not written at the call, but the cell already holds its name. -/
theorem bo0_cases_VS :
    mayProgVS true 0 [] frU pJoinBug vt [] vx [.fld ff] = true ∧
      mayProgVS true 1 [] frU pJoinBug vt [] vx [.fld ff] = true ∧
      mayProgVS false 0 [] frU pJoinBug vt [] vx [.fld ff] = true ∧
      mayProgVS true 0 [] frU pLoopBug vt [] vx [.fld ff] = true ∧
      mayProgVS true 1 [] frU pLoopBug vt [] vx [.fld ff] = true ∧
      mayProgVS false 0 [] frU pLoopBug vt [] vx [.fld ff] = true ∧
      mayProgVS true 1 [] frS pSymBug vt [] vx [.fld ff] = true := by decide +kernel

/-- The join and loop cases are real value aliases, with a callee write (the same object) and
without one (the same null instance). -/
theorem bo0_cases_realV :
    CAliasV (srcL [(.alloc 5 0, .fld ff)]) [] frU pJoinBug vt [] vx [.fld ff] ∧
      CAliasV (srcL []) [] frU pJoinBug vt [] vx [.fld ff] ∧
      CAliasV (srcL [(.alloc 5 0, .fld ff)]) [] frU pLoopBug vt [] vx [.fld ff] ∧
      CAliasV (srcL []) [] frU pLoopBug vt [] vx [.fld ff] ∧
      CAliasV (srcL [(.sym (.root 1) [], .fld ff)]) [] frS pSymBug vt [] vx [.fld ff] :=
  ⟨runAliasV_sound (cs := [.left, .havoc [⟨.arg vx, [], .fld ff, 0⟩]]) (by decide),
    runAliasV_sound (cs := [.left, .havoc []]) (by decide),
    runAliasV_sound (cs := [.havoc [⟨.arg vx, [], .fld ff, 0⟩], .iter 0]) (by decide),
    runAliasV_sound (cs := [.havoc [], .iter 0]) (by decide),
    runAliasV_sound (cs := [.left, .havoc [⟨.arg vx, [], .fld ff, 0⟩]]) (by decide)⟩

end unsound

section nulls

open U

/-- The null-store case: `n = null; x.f = n; m(x)@9; a = x.f; b = x.f` with `x` an entry root. -/
def pNullStore : Prog :=
  .seq (.stmt (.null vn)) <| .seq (.stmt (.store vx ff vn)) <| .seq (.stmt (.call none 9 [vx])) <|
  .seq (.stmt (.load va vx ff)) (.stmt (.load vb vx ff))

/-- THE NULL-STORE CASE: design VS answers `a ~ b` true (both policies). -/
theorem nullStore_answers :
    mayProgVS true 0 [] frX pNullStore va [] vb [] = true ∧
      mayProgVS true 1 [] frX pNullStore va [] vb [] = true ∧
      mayProgVS false 1 [] frX pNullStore va [] vb [] = true := by decide +kernel

/-- The null-store case is real: the same null instance of site 0 if the callee keeps `x.f`, the
same object if it writes `x.f`. -/
theorem nullStore_real :
    CAliasV (srcL []) [] frX pNullStore va [] vb [] ∧
      CAliasV (srcL [(.sym (.root 0) [], .fld ff)]) [] frX pNullStore va [] vb [] :=
  ⟨runAliasV_sound (cs := [.havoc []]) (by decide),
    runAliasV_sound (cs := [.havoc [wxf]]) (by decide)⟩

/-! ## Distinct null sites -/

/-- `a = null; b = null`: two null sites. -/
def pTwoNull : Prog := .seq (.stmt (.null va)) (.stmt (.null vb))

/-- `a = null; b = a`: one null site. -/
def pOneNull : Prog := .seq (.stmt (.null va)) (.stmt (.copy vb va))

/-- `x = new@5; y = new@6; a = x.f; b = y.f`: unwritten fields of objects of two sites. -/
def pTwoNew : Prog :=
  .seq (.stmt (.new vx 5)) <| .seq (.stmt (.new vy 6)) <|
  .seq (.stmt (.load va vx ff)) (.stmt (.load vb vy ff))

/-- DISTINCT NULL SITES DO NOT ALIAS: `a ~ b` is false after `a = null; b = null`, and after two
reads of unwritten fields of objects of two sites; it is true after `a = null; b = a`. -/
theorem nulls_answers :
    mayProgVS true 1 [] frE pTwoNull va [] vb [] = false ∧
      mayProgVS true 1 [] frE pTwoNew va [] vb [] = false ∧
      mayProgVS true 1 [] frE pOneNull va [] vb [] = true := by decide +kernel

/-- The false answers are exact (no instrumented execution gives the same value), and the true
answer is real (the same null instance). -/
theorem nulls_exact (src : Nat → Obj × Cell) (statics : List Root) :
    ¬ CAliasV src statics frE pTwoNull va [] vb [] ∧ ¬ CAliasV src statics frE pTwoNew va [] vb [] ∧
      CAliasV (srcL []) [] frE pOneNull va [] vb [] := by
  refine ⟨fun h => ?_, fun h => ?_, runAliasV_sound (cs := []) (by decide)⟩
  · have := csoundVS src statics true 1 frE pTwoNull va [] vb [] h
    revert this
    have e : mayProgVS true 1 statics frE pTwoNull va [] vb [] =
        mayProgVS true 1 [] frE pTwoNull va [] vb [] := rfl
    rw [show ([] : List Cell).map Cell.abs = [] from rfl, e, nulls_answers.1]
    exact Bool.false_ne_true
  · have := csoundVS src statics true 1 frE pTwoNew va [] vb [] h
    revert this
    have e : mayProgVS true 1 statics frE pTwoNew va [] vb [] =
        mayProgVS true 1 [] frE pTwoNew va [] vb [] := rfl
    rw [show ([] : List Cell).map Cell.abs = [] from rfl, e, nulls_answers.2.1]
    exact Bool.false_ne_true

end nulls

/-! ## The examples of design BO -/

section spread

open DirectedAlias.Examples DirectedAlias.Sound.Havoc.Examples

/-- On `pHv = m(x); a = x.f; b = y.g`, design VS answers false for `a ~ b`, `a ~ z.f`, `a ~ w.g`
(no spread) and true for `a ~ x.f`. -/
theorem spread_goneVS :
    mayProgVS true 0 [] fr pHv va [] vb [] = false ∧
      mayProgVS true 0 [] fr pHv va [] vz [.fld ff] = false ∧
      mayProgVS true 0 [] fr pHv va [] vw [.fld fg] = false ∧
      mayProgVS true 0 [] fr pHv va [] vx [.fld ff] = true ∧
      mayProgVS false 0 [] fr pHv va [] vb [] = false ∧
      mayProgVS true 1 [] fr pHv va [] vb [] = false := by decide +kernel

/-- No instrumented execution of `pHv` gives `a` and `b` the same value. -/
theorem spread_ab_noneV (src : Nat → Obj × Cell) : ¬ CAliasV src [] fr pHv va [] vb [] :=
  no_alias_of_mayProgVS src [] true 0 fr pHv va [] vb [] spread_goneVS.1

/-- The join example, the field example, the strong-update example, the call example and
`loop_bf_x` keep their answers in design VS. -/
theorem other_answersVS :
    mayProgVS true 2 [] fr pJoin va [] vx [] = true ∧
      mayProgVS true 2 [] fr pJoin va [] vy [] = true ∧
      mayProgVS true 2 [] fr pJoin vx [] vy [] = false ∧
      mayProgVS true 1 [] fr pField vx [.fld ff] vz [] = true ∧
      mayProgVS true 1 [] fr pField vy [.fld ff] vz [] = true ∧
      mayProgVS true 1 [] fr pField vx [] vy [] = false ∧
      mayProgVS true 1 [] fr pField va [] vx [] = false ∧
      mayProgVS true 1 [] fr pField va [] vw [] = true ∧
      mayProgVS true 1 [] fr pStrong vb [.fld ff] vx [] = false ∧
      mayProgVS true 1 [] fr pStrong vb [.fld ff] vy [] = true ∧
      mayProgVS true 1 [] fr pCall vw [] vx [.fld ff] = true := by decide +kernel

/-- `loop_bf_x` stays fixed in design VS: after the loop, `b.f` does not alias `x` (both
policies), and `b.f` may alias `y`. -/
theorem loop_bf_x_VS :
    mayProgVS true 1 [] fr pLoop vb [.fld ff] vx [] = false ∧
      mayProgVS false 1 [] fr pLoop vb [.fld ff] vx [] = false ∧
      mayProgVS true 1 [] fr pLoop vb [.fld ff] vy [] = true := by decide +kernel

end spread

section cn

open DirectedAlias.Sound.CellNamed.Examples DirectedAlias.Sound.BlockOnly.Examples

/-- In the dead-end case, design VS answers `b ~ d` true. -/
theorem dead_answerVS :
    mayProgVS true 0 [] frN pDead vb [] vd [] = true ∧
      mayProgVS true 1 [] frN pDead vb [] vd [] = true := by decide +kernel

/-- The dead-end alias is real (a callee write), and also real without a callee write (the same
null instance of `n.f`). -/
theorem dead_realV :
    CAliasV (srcL [(.alloc 5 0, .fld ff)]) [] frN pDead vb [] vd [] ∧
      CAliasV (srcL []) [] frN pDead vb [] vd [] :=
  ⟨runAliasV_sound (cs := [.havoc [⟨.arg vn, [], .fld ff, 0⟩], .left]) (by decide),
    runAliasV_sound (cs := [.havoc [], .left]) (by decide)⟩

/-- NARROW REACH GAIN: after `touch()` the store `t.value = z` is strong; with `touch(this)` or
`this` static it is weak; an unrelated static changes nothing. -/
theorem gain_answersVS :
    mayProgVS true 1 [] frN (pGain []) vt [.fld fg] vu [] = false ∧
      mayProgVS true 1 [5] frN (pGain []) vt [.fld fg] vu [] = false ∧
      mayProgVS true 1 [] frN (pGain [vx]) vt [.fld fg] vu [] = true ∧
      mayProgVS true 1 [0] frN (pGain []) vt [.fld fg] vu [] = true := by decide +kernel

/-- The false answer of the gain is exact. -/
theorem gain_noneV (src : Nat → Obj × Cell) : ¬ CAliasV src [] frN (pGain []) vt [.fld fg] vu [] :=
  no_alias_of_mayProgVS src [] true 1 frN (pGain []) vt [.fld fg] vu [] gain_answersVS.1

/-- TRACE C: design VS answers `a ~ b` true. -/
theorem traceC_answerVS :
    mayProgVS true 0 [] frN pC va [] vb [] = true ∧
      mayProgVS true 1 [] frN pC va [] vb [] = true ∧
      mayProgVS true 2 [] frN pC va [] vb [] = true := by decide +kernel

/-- The alias of trace C is a real value alias. -/
theorem traceC_realV : CAliasV (srcL [(.sym (.root 0) [], .fld ff)]) [] frN pC va [] vb [] :=
  runAliasV_sound (cs := [.havoc [⟨.arg vx, [], .fld ff, 0⟩]]) (by decide)

/-- THE `Eval` CASE: design VS keeps `n.g ~ y`. -/
theorem eval_answerVS :
    mayProgVS true 0 [] frN pE vn [.fld fg] vy [] = true ∧
      mayProgVS true 1 [] frN pE vn [.fld fg] vy [] = true ∧
      mayProgVS false 1 [] frN pE vn [.fld fg] vy [] = true := by decide +kernel

/-- The alias of the `Eval` case is a real value alias. -/
theorem eval_realV : CAliasV (srcL [(.sym (.root 0) [], .fld ff)]) [] frN pE vn [.fld fg] vy [] :=
  runAliasV_sound (cs := [.havoc [⟨.arg vx, [], .fld ff, 0⟩]]) (by decide)

/-- L1 TO L4: design VS gives the answers of design BO: L1 true, L2 false, L3 false, L4 true. -/
theorem losses_VS :
    mayProgVS true 1 [] frN pL1 vt [.fld fg] vu [] = true ∧
      mayProgVS true 0 [] frN pL2 vt [] vw [] = false ∧
      mayProgVS true 1 [] frN pL2 vt [] vw [] = false ∧
      mayProgVS true 0 [] frN pL3 va [] vc [] = false ∧
      mayProgVS true 1 [] frN pL3 va [] vc [] = false ∧
      mayProgVS true 0 [] frN pL4 vy [.fld fg] vu [] = true ∧
      mayProgVS true 1 [] frN pL4 vy [.fld fg] vu [] = true := by decide +kernel

/-- L2 and L3 are exact: no instrumented execution gives the two paths the same value. -/
theorem losses_exactV (src : Nat → Obj × Cell) :
    ¬ CAliasV src [] frN pL2 vt [] vw [] ∧ ¬ CAliasV src [] frN pL3 va [] vc [] :=
  ⟨no_alias_of_mayProgVS src [] true 0 frN pL2 vt [] vw [] losses_VS.2.1,
    no_alias_of_mayProgVS src [] true 0 frN pL3 va [] vc [] losses_VS.2.2.2.1⟩

/-- L1 and L4 are losses: the programs have no `null` and no `new`, so a value alias is an
object alias, and no strict narrow execution has one (`loss1_noneN`, `loss4_noneN`). -/
theorem losses_noneV (src : Nat → Obj × Cell) :
    ¬ CAliasV src [] frN pL1 vt [.fld fg] vu [] ∧ ¬ CAliasV src [] frN pL4 vy [.fld fg] vu [] :=
  ⟨not_CAliasV_of_nullFree (nullFree_of (by decide)) (loss1_noneN src []),
    not_CAliasV_of_nullFree (nullFree_of (by decide)) (loss4_noneN src)⟩

end cn

/-! ## Definite assignment -/

section siteless

open U

/-- `x = new@5; x.f = u; m(x)@9; a = x.f; b = x.f` with `u` unassigned (unbound in the frame). -/
def pSiteless : Prog :=
  .seq (.stmt (.new vx 5)) <| .seq (.stmt (.store vx ff vu)) <|
  .seq (.stmt (.call none 9 [vx])) <| .seq (.stmt (.load va vx ff)) (.stmt (.load vb vx ff))

/-- The same program with a null site: `u = null; x = new@5; x.f = u; m(x)@9; a = x.f; b = x.f`. -/
def pSited : Prog := .seq (.stmt (.null vu)) pSiteless

/-- A SITELESS NULL BREAKS DESIGN VS: under the foundation frame semantics (an unbound variable
holds null) the store `x.f = u` empties the cell, the callee writes one object into it, and
`a ~ b` is real; design VS answers false (design BO answers true by its empty-cell write).
Under the instrumented semantics an unassigned variable has no value and the store blocks
(definite assignment), and with a null site design VS answers true. -/
theorem siteless_unsound :
    mayProgVS true 1 [] frE pSiteless va [] vb [] = false ∧
      CAliasN (srcL [(.alloc 5 0, .fld ff)]) [] frE pSiteless va [] vb [] ∧
      mayProgBO true 1 [] frE pSiteless va [] vb [] = true ∧
      mayProgVS true 1 [] frE pSited va [] vb [] = true ∧
      CAliasV (srcL [(.alloc 5 0, .fld ff)]) [] frE pSited va [] vb [] ∧
      CAliasV (srcL []) [] frE pSited va [] vb [] :=
  ⟨by decide +kernel, runAliasBN_sound (cs := [.havoc [wxf]]) (by decide), by decide +kernel,
    by decide +kernel, runAliasV_sound (cs := [.havoc [wxf]]) (by decide),
    runAliasV_sound (cs := [.havoc []]) (by decide)⟩

end siteless

end DirectedAlias.Sound.ValueSem.Examples

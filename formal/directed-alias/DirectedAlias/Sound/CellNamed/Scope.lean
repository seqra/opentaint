import DirectedAlias.Sound.CellNamed.Reference

/-!
# The scope of design CN, and the precision order

* SCOPE. Design CN is sound for strict narrow A2 (`csoundCN`). Both restrictions are
  load-bearing:
  - with the generous reach of `HavocS` (a callee can reach each symbolic object), the strong
    update after a call without arguments is unsound (`generous_reach_breaks_CN`);
  - with the generous havoc of `Havoc` (one object into two cells), the cell names are
    unsound (`generous_havoc_breaks_CN`).
* PRECISION ORDER. The order "each answer true of the per-cell reference is true in design CN"
  is FALSE in general (`precision_order_fails`): the per-cell origins key a callee object
  below a callee object by its call site only, so two such objects below different arguments
  share one origin; design CN names them by their cells and keeps them apart. The three losses
  (`losses_CN`, `losses_HR`) show the other direction. So the two designs are incomparable.
-/

namespace DirectedAlias.Sound.CellNamed

open DirectedAlias DirectedAlias.Sound DirectedAlias.Sound.Havoc DirectedAlias.Sound.HavocRecency

/-! ## Narrow reach is load-bearing -/

section reach

open DirectedAlias.HavocNeed

/-- `w = x.f; e = w.g; touch(); t = x.f; t.g = z`: the call has no argument. -/
def pTouch : Prog :=
  .seq (.stmt (.load vw vx ff)) <| .seq (.stmt (.load ve vw fg)) <|
  .seq (.stmt (.call none 9 [])) <| .seq (.stmt (.load vt vx ff)) (.stmt (.store vt fg vz))

/-- A naming that decodes each tag to the cell `f` of the root object of `x`. -/
def srcX : Nat → Obj × Cell := fun _ => (.sym (.root 0) [], .fld ff)

/-- The heap after a generous callee writes a new object into `x.f`. -/
def hTouch : Heap :=
  fupd2 (CState.init fr).heap (.sym (.root 0) []) (.fld ff) (some (.sym (.havoc 9 0 0) []))

/-- Under the generous reach of `HavocS`, a call without arguments can write into `x.f`. -/
theorem havocS_touch (st : CState) (hst : st.heap = (CState.init fr).heap) :
    HavocS srcX st [] 9 0 hTouch := by
  intro o c
  by_cases e : o = .sym (.root 0) [] ∧ c = .fld ff
  · obtain ⟨rfl, rfl⟩ := e
    exact Or.inr ⟨Reach.outer, 0, rfl, fupd2_same _ _ _ _⟩
  · left; rw [hst]; exact fupd2_ne _ _ e

/-- NARROW REACH IS LOAD-BEARING: design CN answers false for `w.g ~ e` (after `touch()`, the
store `t.g = z` is strong), but a strict execution with generous reach aliases them. -/
theorem generous_reach_breaks_CN :
    mayProgCN true 1 [] fr pTouch vw [.fld fg] ve [] = false ∧
      CAliasS srcX fr pTouch vw [.fld fg] ve [] := by
  refine ⟨by decide +kernel, ?_⟩
  refine ⟨_, .seq (.stmt (.load rfl)) (.seq (.stmt (.load rfl)) (.seq (.stmt (.call
    (havocS_touch _ rfl))) (.seq (.stmt (.load rfl)) (.stmt (.store rfl))))), ?_⟩
  exact aliasInB_iff.mp (by decide)

/-- Under strict narrow A2, no execution of `pTouch` aliases `w.g` and `e`. -/
theorem touch_noneN (src : Nat → Obj × Cell) : ¬ CAliasN src [] fr pTouch vw [.fld fg] ve [] :=
  no_alias_of_mayProgCN src [] true 1 fr pTouch vw [.fld fg] ve [] generous_reach_breaks_CN.1

end reach

/-! ## Strict havoc is load-bearing -/

section havoc

open DirectedAlias.Examples DirectedAlias.Sound.Havoc.Examples

/-- STRICT HAVOC IS LOAD-BEARING: on `pHv = m(x); a = x.f; b = y.g`, design CN answers false
for `a ~ b`, but a generous callee writes one object into `x.f` and `y.g`. -/
theorem generous_havoc_breaks_CN :
    mayProgCN true 0 [] fr pHv va [] vb [] = false ∧ CAlias fr pHv va [] vb [] :=
  ⟨Examples.spread_goneCN.1, spread_real_ab⟩

end havoc

/-! ## The precision order fails -/

section precision

open DirectedAlias.Sound.CellNamed.Examples

/-- `m(x, y); m'(x, y); t = x.f; a = t.g; u = y.f; b = u.g`. -/
def pNest : Prog :=
  .seq (.stmt (.call none 9 [vx, vy])) <| .seq (.stmt (.call none 8 [vx, vy])) <|
  .seq (.stmt (.load vt vx ff)) <| .seq (.stmt (.load va vt fg)) <|
  .seq (.stmt (.load vu vy ff)) (.stmt (.load vb vu fg))

/-- THE PRECISION ORDER FAILS: the per-cell reference (narrow reach) and the sound per-cell
analysis (generous reach) answer `a ~ b` true: the second call writes into `x.f.g` and `y.f.g`
objects with the one origin `hsym 8 (havoc 9) g []`. Design CN answers false: the names are
`x.f.g` and `y.f.g`. -/
theorem precision_order_fails :
    mayProgHRN true 0 [] frN pNest va [] vb [] = true ∧
      mayProgHR true 0 frN pNest va [] vb [] = true ∧
      mayProgCN true 0 [] frN pNest va [] vb [] = false := by decide +kernel

/-- The answer true of the per-cell analyses on `pNest` is spurious: under strict narrow A2 no
execution aliases `a` and `b`. -/
theorem nest_noneN (src : Nat → Obj × Cell) :
    ¬ CAliasN src [] frN pNest va [] vb [] :=
  no_alias_of_mayProgCN src [] true 0 frN pNest va [] vb [] precision_order_fails.2.2

end precision

end DirectedAlias.Sound.CellNamed

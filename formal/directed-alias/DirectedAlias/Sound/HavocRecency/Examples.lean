import DirectedAlias.Sound.HavocRecency.Soundness
import DirectedAlias.Sound.Havoc.Examples
import DirectedAlias.Sound.Recency.Examples

/-!
# Examples of recency with per-cell havoc

* The recency fix stays: `loop_bf_x` is false and exact (`loop_bf_x_fixedHR`).
* The per-cell havoc fix stays: the spread on `pHv` is gone (`strict_answersHR`).
* The other examples keep their answers.
* Only the combination answers both questions of `pBoth` correctly (`both_answers`).
* The precision cost of the key `rOld s` for both recency origins: `pCost` (`cost_answers`,
  `cost_none`). Recency alone and per-cell havoc alone give the same spurious answer there.

The checks use `decide +kernel` with small `K` (the soundness theorem holds for each `K`).
-/

namespace DirectedAlias.Sound.HavocRecency.Examples

open DirectedAlias DirectedAlias.Examples DirectedAlias.Sound DirectedAlias.Sound.Havoc
open DirectedAlias.Sound.Havoc.Examples DirectedAlias.Sound.Recency DirectedAlias.Sound.HavocRecency

/-! ## The recency fix stays -/

/-- With recency and per-cell havoc, `b.f` does not alias `x` after the loop (both policies),
and `b.f` may alias `y`. -/
theorem loop_bf_x_fixedHR :
    mayProgHR true 1 fr pLoop vb [.fld ff] vx [] = false ∧
      mayProgHR false 1 fr pLoop vb [.fld ff] vx [] = false ∧
      mayProgHR true 1 fr pLoop vb [.fld ff] vy [] = true := by decide +kernel

/-- The answer for `b.f` and `x` is exact: no two executions alias them. -/
theorem loop_bf_x_exactHR :
    mayProgHR true 1 fr pLoop vb [.fld ff] vx [] = false ∧
      Boundary.NoCrossAlias fr pLoop vb [.fld ff] vx [] :=
  ⟨loop_bf_x_fixedHR.1, Boundary.loop_none⟩

/-! ## The per-cell havoc fix stays -/

/-- The spread on `pHv` is gone: `a ~ b`, `a ~ z.f`, `a ~ w.g` are false, `a ~ x.f` is true
(both policies). -/
theorem strict_answersHR :
    mayProgHR true 0 fr pHv va [] vb [] = false ∧
      mayProgHR true 0 fr pHv va [] vz [.fld ff] = false ∧
      mayProgHR true 0 fr pHv va [] vw [.fld fg] = false ∧
      mayProgHR true 0 fr pHv va [] vx [.fld ff] = true ∧
      mayProgHR false 0 fr pHv va [] vb [] = false ∧
      mayProgHR false 0 fr pHv va [] vx [.fld ff] = true := by decide +kernel

/-- Recency with the shared havoc keeps the spread on `pHv`. -/
theorem spread_with_recency_only : mayProgR true 0 fr pHv va [] vb [] = true := by decide +kernel

/-- The cells of an argument allocation: `a ~ z` is false, `a ~ b.f` is true. -/
theorem new_answersHR :
    mayProgHR true 0 frE pNew va [] vz [] = false ∧
      mayProgHR true 0 frE pNew va [] vb [.fld ff] = true := by decide +kernel

/-- The loop with a call: `a ~ b` is false, `a ~ x.f` is true. -/
theorem loop_answersHR :
    mayProgHR true 0 fr pLoopHv va [] vb [] = false ∧
      mayProgHR true 0 fr pLoopHv va [] vx [.fld ff] = true := by decide +kernel

/-! ## The other examples keep their answers -/

/-- The task example, the field example, the strong-update example and the call example keep
their answers. -/
theorem other_answersHR :
    mayProgHR true 2 fr pJoin va [] vx [] = true ∧ mayProgHR true 2 fr pJoin va [] vy [] = true ∧
      mayProgHR true 2 fr pJoin vx [] vy [] = false ∧
      mayProgHR true 1 fr pField vx [.fld ff] vz [] = true ∧
      mayProgHR true 1 fr pField vy [.fld ff] vz [] = true ∧
      mayProgHR true 1 fr pField vx [] vy [] = false ∧
      mayProgHR true 1 fr pField va [] vw [] = true ∧
      mayProgHR true 1 fr pStrong vb [.fld ff] vx [] = false ∧
      mayProgHR true 1 fr pStrong vb [.fld ff] vy [] = true ∧
      mayProgHR true 1 fr pCall vw [] vx [.fld ff] = true := by decide +kernel

/-- The list loop keeps its answer: the next node of the head may alias the head. -/
theorem list_mayHR : mayProgHR true 2 Recency.Examples.frL Recency.Examples.pList vb [.fld ff] vb [] = true := by
  decide +kernel

/-! ## Both refinements are necessary -/

/-- `loop { b = new@7; b.f = x; b.f = y }; m(x); a = x.f; c = y.g` (with `c` = variable `z`). -/
def pBoth : Prog :=
  .seq pLoop (.seq (.stmt (.call none 9 [vx])) (.seq (.stmt (.load va vx ff)) (.stmt (.load vz vy fg))))

/-- The frame of `pBoth`: `x` and `y` are roots. -/
def frB : Frame := ⟨[(vx, 0), (vy, 1)]⟩

/-- Only the combination answers false for both `b.f ~ x` and `a ~ c`. Per-cell havoc alone
answers true for `b.f ~ x`; recency alone answers true for `a ~ c`. -/
theorem both_answers :
    mayProgHR true 0 frB pBoth vb [.fld ff] vx [] = false ∧
      mayProgHR true 0 frB pBoth va [] vz [] = false ∧
      mayProgH true 0 frB pBoth vb [.fld ff] vx [] = true ∧
      mayProgR true 0 frB pBoth va [] vz [] = true := by decide +kernel

/-- Under strict A2, no execution of `pBoth` aliases `b.f` and `x`. -/
theorem both_bf_x_none (src : Nat → Obj × Cell) : ¬ CAliasS src frB pBoth vb [.fld ff] vx [] :=
  no_alias_of_mayProgHR src true 0 frB pBoth vb [.fld ff] vx [] both_answers.1

/-- Under strict A2, no execution of `pBoth` aliases `a` and `c`. -/
theorem both_a_c_none (src : Nat → Obj × Cell) : ¬ CAliasS src frB pBoth va [] vz [] :=
  no_alias_of_mayProgHR src true 0 frB pBoth va [] vz [] both_answers.2.1

/-! ## The precision cost of the shared key -/

/-- `o = new@7; b = new@7; m(b, o); t = b.f; u = o.f` (`o` = `x`, `t` = `a`, `u` = `z`).
`b` holds the most recent object of site 7 and `o` an older one. -/
def pCost : Prog :=
  .seq (.stmt (.new vx 7)) (.seq (.stmt (.new vb 7)) (.seq (.stmt (.call none 9 [vb, vx]))
    (.seq (.stmt (.load va vb ff)) (.stmt (.load vz vx ff)))))

/-- THE COST: the key `rOld 7` of both recency origins gives `t ~ u` true. Recency alone and
per-cell havoc alone also answer true. `t ~ b.f` stays true. -/
theorem cost_answers :
    mayProgHR true 0 frE pCost va [] vz [] = true ∧
      mayProgHR true 0 frE pCost va [] vb [.fld ff] = true ∧
      mayProgH true 0 frE pCost va [] vz [] = true ∧
      mayProgR true 0 frE pCost va [] vz [] = true := by decide +kernel

/-- A strict havoc never writes one object into the same cell of two different objects whose
cells were null before the call. -/
theorem havocS_distinct {src : Nat → Obj × Cell} {st : CState} {args : List Var} {s n : Nat}
    {h' : Heap} (hh : HavocS src st args s n h') {o1 o2 : Obj} {c : Cell} (hne : o1 ≠ o2)
    (h1 : st.heap o1 c = none) (h2 : st.heap o2 c = none) (v : Obj)
    (e1 : h' o1 c = some v) (e2 : h' o2 c = some v) : False := by
  rcases hh o1 c with a1 | ⟨_, k1, hk1, a1⟩
  · rw [a1, h1] at e1; cases e1
  rcases hh o2 c with a2 | ⟨_, k2, hk2, a2⟩
  · rw [a2, h2] at e2; cases e2
  rw [a1] at e1; rw [a2] at e2
  cases e1
  exact hne (HavocS.inj hk1 hk2 (Option.some.inj e2).symm).1

/-- The answer `t ~ u` of `cost_answers` is spurious: no strict execution aliases `t` and `u`. -/
theorem cost_none (src : Nat → Obj × Cell) : ¬ CAliasS src frE pCost va [] vz [] := by
  rintro ⟨st, hx, o, h1, h2⟩
  cases hx with | seq hA hB =>
  cases hA with | stmt hA =>
  cases hA
  cases hB with | seq hA hB =>
  cases hA with | stmt hA =>
  cases hA
  cases hB with | seq hA hB =>
  cases hA with | stmt hA =>
  cases hA with | call hh =>
  cases hB with | seq hA hB =>
  cases hA with | stmt hA =>
  cases hA with | load he1 =>
  cases hB with | stmt hA =>
  cases hA with | load he2 =>
  rename_i h' o1 o2
  change some (Obj.alloc 7 1) = some o1 at he1
  change some (Obj.alloc 7 0) = some o2 at he2
  cases he1; cases he2
  change (h' (.alloc 7 1) (.fld ff)).bind (fun o => readPath _ o []) = some o at h1
  change (h' (.alloc 7 0) (.fld ff)).bind (fun o => readPath _ o []) = some o at h2
  cases e1 : h' (.alloc 7 1) (.fld ff) with
  | none => rw [e1] at h1; cases h1
  | some v1 =>
    cases e2 : h' (.alloc 7 0) (.fld ff) with
    | none => rw [e2] at h2; cases h2
    | some v2 =>
      rw [e1] at h1; rw [e2] at h2
      cases h1; cases h2
      exact havocS_distinct hh (by decide) rfl rfl _ e1 e2

end DirectedAlias.Sound.HavocRecency.Examples

import DirectedAlias.Sound.StoreScope
import DirectedAlias.Sound.Boundary

/-!
# Examples of the store certificate

Programs in the certified scope (exact by `ccomplete_store`), and the counterexamples
B4, B5, B6, which the certificate rejects.
-/

namespace DirectedAlias.Sound.StoreExamples

open DirectedAlias DirectedAlias.Sound
open DirectedAlias.Sound.Boundary (vx vy vz va vt ff fg fr3 pCorr pStrongTwo pStrongTwoG pWeak)

/-- The initialization pattern: `if (*) { a = new@7; a.f = x } else { a = y }; t = a.f`. -/
def pInit : Prog :=
  .seq (.choice (.seq (.stmt (.new va 7)) (.stmt (.store va ff vx))) (.stmt (.copy va vy)))
    (.stmt (.load vt va ff))

/-- The initialization pattern is in the certified scope. -/
theorem init_in_scope : storeScopeB 2 fr3 pInit [] [] = true := by decide

/-- In the initialization pattern, `t` may alias `x` (new object) and `y.f` (old object). -/
theorem init_answers :
    mayProg 2 fr3 pInit vt [] vx [] = true ∧ mayProg 2 fr3 pInit vt [] vy [.fld ff] = true ∧
      mayProg 2 fr3 pInit vt [] vy [] = false := by decide

/-- Each answer of the initialization pattern has two executions (exactness). -/
theorem init_exact (x y : Var) (h : mayProg 2 fr3 pInit x [] y [] = true) :
    ∃ cx cy, cx.map Cell.abs = [] ∧ cy.map Cell.abs = [] ∧ CAliasX fr3 pInit x cx y cy :=
  ccomplete_store 2 _ _ x [] y [] init_in_scope h

/-- A field initialization before the branch: `x.f = z; if (*) a = x else a = y; t = a.f`. -/
def pPre : Prog :=
  .seq (.stmt (.store vx ff vz))
    (.seq (.choice (.stmt (.copy va vx)) (.stmt (.copy va vy))) (.stmt (.load vt va ff)))

/-- The field initialization before the branch is in the certified scope. -/
theorem pre_in_scope : storeScopeB 2 fr3 pPre [] [.fld ff] = true := by decide

/-- After the field initialization, `t` may alias `z` and `y.f`, and not `x`. -/
theorem pre_answers :
    mayProg 2 fr3 pPre vt [] vz [] = true ∧ mayProg 2 fr3 pPre vt [] vy [.fld ff] = true ∧
      mayProg 2 fr3 pPre vt [] vx [] = false := by decide

/-- The certificate rejects B4 (a store in one branch on a cell that the other branch keeps). -/
theorem corr_rejected : storeScopeB 2 fr3 pCorr [] [] = false := by decide

/-- The certificate rejects B5 (a stored value with two origins). -/
theorem strongTwo_rejected : storeScopeB 2 fr3 pStrongTwo [.fld ff, .fld ff] [] = false := by
  decide

/-- The certificate rejects B5 without a cycle. -/
theorem strongTwoG_rejected : storeScopeB 2 fr3 pStrongTwoG [.fld ff, .fld fg] [] = false := by
  decide

/-- The certificate rejects B6 (a weak store). -/
theorem weak_rejected : storeScopeB 2 fr3 pWeak [.fld ff, .fld ff] [] = false := by decide

/-- The certificate rejects the user's field example (a weak store through `a`). -/
theorem field_rejected : storeScopeB 2 Examples.fr Examples.pField [.fld Examples.ff] [] = false := by
  decide

end DirectedAlias.Sound.StoreExamples

import DirectedAlias.Sound.BlockOnly.Examples

/-!
# Precision of design BO and design CN

On each example query, both designs give the same answer, except:
* L2 and L3: design BO answers false (exact), design CN answers true;
* L4: design BO answers true (a loss: no execution has the alias), design CN answers false.

So the two designs are incomparable in precision (`bo_cn_incomparable`); both false answers
are exact (the designs are sound).
-/

namespace DirectedAlias.Sound.BlockOnly.Precision

open DirectedAlias DirectedAlias.Sound DirectedAlias.Sound.CellNamed DirectedAlias.Sound.BlockOnly

/-- One query: design BO and design CN with the same arguments. -/
def both (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog) (x : Var)
    (px : List ACell) (y : Var) (py : List ACell) : Bool × Bool :=
  (mayProgBO eu K statics fr p x px y py, mayProgCN eu K statics fr p x px y py)

section cnvars

open DirectedAlias.Sound.CellNamed.Examples DirectedAlias.Sound.BlockOnly.Examples

/-- THE PRECISION TABLE on the examples with the variables of design CN, as pairs
(design BO, design CN). Only L2, L3 and L4 differ. -/
theorem precision_tableN :
    both true 1 [] frN (pGain []) vt [.fld fg] vu [] = (false, false) ∧
      both true 1 [] frN (pGain [vx]) vt [.fld fg] vu [] = (true, true) ∧
      both true 1 [0] frN (pGain []) vt [.fld fg] vu [] = (true, true) ∧
      both true 1 [] frN pL1 vt [.fld fg] vu [] = (true, true) ∧
      both true 0 [] frN pL2 vt [] vw [] = (false, true) ∧
      both true 0 [] frN pL3 va [] vc [] = (false, true) ∧
      both true 1 [] frN pL4 vy [.fld fg] vu [] = (true, false) ∧
      both true 1 [] frN pC va [] vb [] = (true, true) ∧
      both true 1 [] frN pE vn [.fld fg] vy [] = (true, true) ∧
      both true 0 [] frN pDead vb [] vd [] = (true, true) := by decide +kernel

end cnvars

section need

open DirectedAlias.HavocNeed

/-- The precision table on the two cases of `HavocNeed` (both designs answer true). -/
theorem precision_tableNeed :
    both true 0 [] fr pStrong vw [.fld fg] ve [] = (true, true) ∧
      both true 0 [] fr pEmpty va [] vb [] = (true, true) := by decide +kernel

end need

section other

open DirectedAlias.Examples DirectedAlias.Sound.Havoc.Examples

/-- The precision table on `pHv` and on the join, field, strong-update, call and loop examples
(both designs give the same answers). -/
theorem precision_tableOld :
    both true 0 [] fr pHv va [] vb [] = (false, false) ∧
      both true 0 [] fr pHv va [] vx [.fld ff] = (true, true) ∧
      both true 2 [] fr pJoin vx [] vy [] = (false, false) ∧
      both true 1 [] fr pField vx [.fld ff] vz [] = (true, true) ∧
      both true 1 [] fr pField va [] vx [] = (false, false) ∧
      both true 1 [] fr pStrong vb [.fld ff] vx [] = (false, false) ∧
      both true 1 [] fr pCall vw [] vx [.fld ff] = (true, true) ∧
      both true 1 [] fr pLoop vb [.fld ff] vx [] = (false, false) := by decide +kernel

end other

section cnvars2

open DirectedAlias.Sound.CellNamed.Examples DirectedAlias.Sound.BlockOnly.Examples

/-- INCOMPARABLE PRECISION: there is a query where design BO answers true and design CN false
(L4), and a query where design BO answers false and design CN true (L2). Both false answers
are exact. -/
theorem bo_cn_incomparable :
    (mayProgBO true 1 [] frN pL4 vy [.fld fg] vu [] = true ∧
      mayProgCN true 1 [] frN pL4 vy [.fld fg] vu [] = false ∧
      ∀ src, ¬ CAliasN src [] frN pL4 vy [.fld fg] vu []) ∧
    (mayProgBO true 0 [] frN pL2 vt [] vw [] = false ∧
      mayProgCN true 0 [] frN pL2 vt [] vw [] = true ∧
      ∀ src, ¬ CAliasN src [] frN pL2 vt [] vw []) :=
  ⟨⟨loss4_BO.2.1, loss4_BO.2.2, loss4_noneN⟩,
    ⟨losses_BO.2.1, losses_CN.2.1, fun src => (losses_exactBO src).1⟩⟩

end cnvars2

end DirectedAlias.Sound.BlockOnly.Precision

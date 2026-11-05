import DirectedAlias.Opt.ValueSem
import DirectedAlias.Sound.ValueSem.Statics

/-!
# The optimized machine of design VSS

Design VSS is design VS on the program without its static writes (`mayProgVSS_eq`). So the O
machine of design VS on the stripped program (`mayProgVSO`) is the O machine of design VSS:
it gives the answers of the concept (`mayProgVSSO_eq`), and it is sound under A5
(`csoundVSSO`).
-/

namespace DirectedAlias.Opt.ValueSem

open DirectedAlias DirectedAlias.Sound DirectedAlias.Sound.CellNamed DirectedAlias.Sound.ValueSem

/-- O may-alias of design VSS: the O machine of design VS on the stripped program. -/
def mayProgVSSO (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (x : Var) (px : List ACell) (y : Var) (py : List ACell) : Bool :=
  mayProgVSO eu K statics fr (stripStatic (shB statics fr) p) x px y py

/-- O EQUIVALENCE OF DESIGN VSS: on variables of the stripped program and of the frame, O and
the concept of design VSS give the same may-alias answer. -/
theorem mayProgVSSO_eq (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (x : Var) (px : List ACell) (y : Var) (py : List ACell)
    (hx : x ∈ (stripStatic (shB statics fr) p).vars ++ fr.vars)
    (hy : y ∈ (stripStatic (shB statics fr) p).vars ++ fr.vars) :
    mayProgVSSO eu K statics fr p x px y py = mayProgVSS eu K statics fr p x px y py := by
  rw [mayProgVSS_eq]
  exact mayProgVSO_eq eu K statics fr _ x px y py hx hy

/-- O of design VSS is sound under A5: each A5 value alias of program variables is a
may-alias of `mayProgVSSO`. -/
theorem csoundVSSO (src : Nat → Obj × Cell) (statics : List Root) (eu : Bool) (K : Nat)
    (fr : Frame) (p : Prog) (x : Var) (px : List Cell) (y : Var) (py : List Cell)
    (hx : x ∈ (stripStatic (shB statics fr) p).vars ++ fr.vars)
    (hy : y ∈ (stripStatic (shB statics fr) p).vars ++ fr.vars)
    (h : CAliasA5 src statics fr p x px y py) :
    mayProgVSSO eu K statics fr p x (px.map Cell.abs) y (py.map Cell.abs) = true := by
  rw [mayProgVSSO_eq eu K statics fr p x _ y _ hx hy]
  exact csoundVSS src statics eu K fr p x px y py h

end DirectedAlias.Opt.ValueSem

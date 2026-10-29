import DirectedAlias.Sound.CellNamed.Examples

/-!
# The per-cell reference with narrow reach (for the precision comparison)

`mayProgHRN` is recency with per-cell havoc origins (`Sound/HavocRecency`) and the narrow
reach of design CN: a call adds `hsym s (keyOfR o) c []` to each universe cell of each origin
`o` that the closure `closeN` covers. It has no exposed set: its uniqueness test is the
recency test. This file uses it only as a REFERENCE for the precision of design CN. The model
does not prove it sound (the sound per-cell analysis is `mayProgHR`, with generous reach).

The general precision order "each answer true of the reference is true in design CN" is OPEN.
`precision_examples` checks it on each query of the examples.
-/

namespace DirectedAlias.Sound.CellNamed

open DirectedAlias DirectedAlias.Sound DirectedAlias.Sound.Recency DirectedAlias.Sound.Havoc
open DirectedAlias.Sound.HavocRecency

/-- The per-cell havoc with narrow reach: each universe cell of each covered origin gets the
per-cell havoc origin of the call site. -/
def havocHRN (cn : CtxN) (X : AState) (args : List Var) (s : Site) : AState :=
  match closeN cn X (cn.ctx.origins.length + 1) (callRoots cn X args) with
  | some R =>
    { X with heap := fun o c => if c ∈ cn.ctx.cells ∧ coveredB R o = true
        then uni [.hsym s (keyOfR o) c []] (X.heap o c) else X.heap o c }
  | none =>
    { X with heap := fun o c => if c ∈ cn.ctx.cells
        then uni [.hsym s (keyOfR o) c []] (X.heap o c) else X.heap o c }

/-- The transfer of the reference: `astepHR` with the narrow per-cell havoc. -/
def astepHRN (cn : CtxN) : Stmt → AState → AState
  | .call ret s args, X => (retire s (havocHRN cn X args s)).setRet ret [.sym (.fresh s) []]
  | st, X => astepHR cn.ctx st X

/-- The analysis of the reference. -/
def analyzeHRN (cn : CtxN) : Prog → AState → AState
  | .skip, X => X
  | .stmt s, X => astepHRN cn s X
  | .seq p q, X => analyzeHRN cn q (analyzeHRN cn p X)
  | .choice p q, X => join (analyzeHRN cn p X) (analyzeHRN cn q X)
  | .loop p, X => loopIter cn.ctx (analyzeHRN cn p) cn.ctx.fuel X

/-- The keys of the reference universe: the symbolic origins of the bases, the old recency
origin of each allocation site, and the site origin of each call site. -/
def keysHRN (K : Nat) (fr : Frame) (statics : List Root) (p : Prog) (cells : List ACell) :
    List Origin :=
  (basesCN fr statics p).flatMap (fun b => (pathsUpTo cells K).map (Origin.sym b) ++ [Origin.deep b]) ++
    p.newSites.map rOld ++ p.callSites.map Origin.havoc

/-- The universe of the reference. -/
def originsHRN (K : Nat) (fr : Frame) (statics : List Root) (p : Prog) (cells : List ACell) :
    List Origin :=
  (basesCN fr statics p).flatMap (fun b => (pathsUpTo cells K).map (Origin.sym b) ++ [Origin.deep b]) ++
    p.newSites.flatMap (fun s => [rNew s, rOld s]) ++
    havocCells K (keysHRN K fr statics p cells) cells p.callSites

/-- The context of the reference. -/
def ctxHRN (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog) (qf : List Field) :
    CtxN :=
  let c0 := (ctxCN eu K statics fr p qf).ctx
  let origins := originsHRN K fr statics p c0.cells
  { ctx := { K := c0.K, once := c0.once, cells := c0.cells, vars := c0.vars, origins := origins,
             fuel := (c0.vars.length + origins.length * c0.cells.length) * origins.length + 1,
             entryUnique := c0.entryUnique }
    statics := statics
    xe := (ctxCN eu K statics fr p qf).xe }

/-- May-alias at the end of `p` in the reference. -/
def mayProgHRN (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (x : Var) (px : List ACell) (y : Var) (py : List ACell) : Bool :=
  may (analyzeHRN (ctxHRN eu K statics fr p (afields px ++ afields py)) p (ainit K fr)) x px y py

/-- The precision check of one query: if the reference answers true, design CN answers true. -/
def precB (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (x : Var) (px : List ACell) (y : Var) (py : List ACell) : Bool :=
  !(mayProgHRN eu K statics fr p x px y py) || mayProgCN eu K statics fr p x px y py

/-! ## The precision check on the examples -/

section precision

/-- The precision order holds on the `HavocNeed` queries. -/
theorem precision_need :
    precB true 0 [] HavocNeed.fr HavocNeed.pStrong HavocNeed.vw [.fld HavocNeed.fg] HavocNeed.ve [] ∧
      precB true 1 [] HavocNeed.fr HavocNeed.pStrong HavocNeed.vw [.fld HavocNeed.fg]
        HavocNeed.ve [] ∧
      precB true 0 [] HavocNeed.fr HavocNeed.pEmpty HavocNeed.va [] HavocNeed.vb [] ∧
      precB true 1 [] HavocNeed.fr HavocNeed.pEmpty HavocNeed.va [] HavocNeed.vb [] := by
  decide +kernel

open DirectedAlias.Examples DirectedAlias.Sound.Havoc.Examples in
/-- The precision order holds on the queries of `pHv` and of the older examples. -/
theorem precision_old :
    precB true 0 [] fr pHv va [] vb [] ∧ precB true 0 [] fr pHv va [] vz [.fld ff] ∧
      precB true 0 [] fr pHv va [] vw [.fld fg] ∧ precB true 0 [] fr pHv va [] vx [.fld ff] ∧
      precB false 0 [] fr pHv va [] vb [] ∧
      precB true 2 [] fr pJoin va [] vx [] ∧ precB true 2 [] fr pJoin va [] vy [] ∧
      precB true 2 [] fr pJoin vx [] vy [] ∧
      precB true 1 [] fr pField vx [.fld ff] vz [] ∧ precB true 1 [] fr pField vy [.fld ff] vz [] ∧
      precB true 1 [] fr pField vx [] vy [] ∧ precB true 1 [] fr pField va [] vx [] ∧
      precB true 1 [] fr pField va [] vw [] ∧
      precB true 1 [] fr pStrong vb [.fld ff] vx [] ∧ precB true 1 [] fr pStrong vb [.fld ff] vy [] ∧
      precB true 1 [] fr pCall vw [] vx [.fld ff] ∧
      precB true 1 [] fr pLoop vb [.fld ff] vx [] ∧ precB false 1 [] fr pLoop vb [.fld ff] vx [] ∧
      precB true 1 [] fr pLoop vb [.fld ff] vy [] := by decide +kernel

open DirectedAlias.Sound.CellNamed.Examples in
/-- The precision order holds on the new queries. The reference answers false on the three
losses, where design CN answers true. -/
theorem precision_new :
    precB true 0 [] frN pDead vb [] vd [] ∧ precB true 1 [] frN pDead vb [] vd [] ∧
      precB true 1 [] frN (pGain []) vt [.fld fg] vu [] ∧
      precB true 1 [0] frN (pGain []) vt [.fld fg] vu [] ∧
      precB true 1 [] frN pL1 vt [.fld fg] vu [] ∧ precB true 0 [] frN pL2 vt [] vw [] ∧
      precB true 1 [] frN pL2 vt [] vw [] ∧ precB true 0 [] frN pL3 va [] vc [] ∧
      precB true 1 [] frN pL3 va [] vc [] ∧
      mayProgHRN true 1 [] frN pL1 vt [.fld fg] vu [] = false ∧
      mayProgHRN true 1 [] frN pL2 vt [] vw [] = false ∧
      mayProgHRN true 1 [] frN pL3 va [] vc [] = false := by decide +kernel

end precision

end DirectedAlias.Sound.CellNamed

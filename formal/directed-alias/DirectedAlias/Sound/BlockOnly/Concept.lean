import DirectedAlias.Sound.CellNamed.Soundness

/-!
# The call only blocks strong updates (design BO, with the empty-cell fix)

Design BO keeps the recency state of design CN, but a call does not add cell names to the
cells that it reaches. It keeps two origin sets in two reserved variables:

* `Etree` (key `xe`): the origins that a call reached (the closure `R`);
* `Eval` (key `xv`): the contents of the universe cells of the covered origins at a call.

An origin is unique if the recency rule holds, no proper prefix of it is in `Etree`, and it is
not in `Eval` (`uniqueBO`). A callee object in the cell `(O, c)` is named by the old content
of the cell. The old content is now in `Eval`, so it gets no strong update.

THE FIX (see `Unsound.lean`). The design as first stated named the callee object in an EMPTY
covered cell by a read rule: a read of an empty covered cell gives the cell name. That rule is
unsound: a later join or weak store makes the cell non-empty, and then the read loses the cell
name. The fixed call WRITES the cell name into each covered universe cell whose content is
empty, and there is no read rule. A non-empty cell is not changed. So the call changes the
heap only at covered empty cells (for example the null fields of a reached new object).

The fallback (the closure fails): every origin is covered, and both sets get every universe
origin.
-/

namespace DirectedAlias.Sound.BlockOnly

open DirectedAlias DirectedAlias.Sound DirectedAlias.Sound.Recency DirectedAlias.Sound.Havoc
open DirectedAlias.Sound.HavocRecency DirectedAlias.Sound.CellNamed

/-- The context of design BO: the context of design CN (its reserved variable `xe` holds
`Etree`), and a second reserved variable `xv` that holds `Eval`. -/
structure CtxB where
  cn : CtxN
  xv : Var

/-- Uniqueness of design BO: the recency test, no proper prefix in `E` (the `Etree` set), and
the origin is not in `V` (the `Eval` set). -/
def uniqueBO (once : Site → Bool) (eu : Bool) (E V : List Origin) (o : Origin) : Bool :=
  uniqueCN once eu E o && !(decide (o ∈ V))

/-- The store of design BO: strong if the target has one origin and it is unique. -/
def storeBO (cb : CtxB) (X : AState) (x : Var) (c : ACell) (S : List Origin) : AState :=
  match single? (X.env x) with
  | some o =>
    if uniqueBO cb.cn.ctx.once cb.cn.ctx.entryUnique (X.env cb.cn.xe) (X.env cb.xv) o then
      X.setCell o c S
    else X.weakStore (X.env x) c S
  | none => X.weakStore (X.env x) c S

/-- The call with closure `E`, contents `V` and coverage `cov`: `Etree` gets `E`, `Eval` gets
`V`, and each covered cell of the universe cells whose content is empty gets its cell name.
Every other cell keeps its content. -/
def callWith (cb : CtxB) (X : AState) (E V : List Origin) (cov : Origin → Bool) : AState where
  env := fupd (fupd X.env cb.cn.xe (uni E (X.env cb.cn.xe))) cb.xv (uni V (X.env cb.xv))
  heap := fun o c => if c ∈ cb.cn.ctx.cells ∧ cov o = true ∧ (X.heap o c).isEmpty = true
    then [childCN cb.cn.ctx.K o c] else X.heap o c

/-- The call of design BO: the closure `R` of design CN, then `callWith` with `R`, the
contents of the covered cells, and the descendants of `R`. If the closure fails, every origin
is covered and both sets get every universe origin. -/
def callBO (cb : CtxB) (X : AState) (args : List Var) : AState :=
  match closeN cb.cn X (cb.cn.ctx.origins.length + 1) (callRoots cb.cn X args) with
  | some R => callWith cb X R (succsN cb.cn X R) (coveredB R)
  | none => callWith cb X cb.cn.ctx.origins cb.cn.ctx.origins (fun _ => true)

/-- The abstract transfer of design BO. -/
def astepBO (cb : CtxB) : Stmt → AState → AState
  | .new x s, X => (retire s X).setVar x [rNew s]
  | .unknown x s, X => (retire s X).setVar x [.sym (.fresh s) []]
  | .call ret s args, X => (retire s (callBO cb X args)).setRet ret [.sym (.fresh s) []]
  | .store x f y, X => storeBO cb X x (.fld f) (X.env y)
  | st, X => astep cb.cn.ctx st X

/-- The abstract analysis of design BO. -/
def analyzeBO (cb : CtxB) : Prog → AState → AState
  | .skip, X => X
  | .stmt s, X => astepBO cb s X
  | .seq p q, X => analyzeBO cb q (analyzeBO cb p X)
  | .choice p q, X => join (analyzeBO cb p X) (analyzeBO cb q X)
  | .loop p, X => loopIter cb.cn.ctx (analyzeBO cb p) cb.cn.ctx.fuel X

/-- The variables of a program and its frame, without repetition. -/
def progVars (fr : Frame) (p : Prog) : List Var := (p.vars ++ fr.vars).eraseDups

/-- The context of a program in design BO: the universe of design CN, and the two reserved
variables `xe = freshVar` and `xv = xe + 1` in the variable universe, so the loop check
covers both sets. -/
def ctxBO (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog) (qf : List Field) :
    CtxB :=
  let c0 := (ctxCN eu K statics fr p qf).ctx
  let xe := freshVar (progVars fr p)
  let vars := xe :: (xe + 1) :: progVars fr p
  let fuel := (vars.length + c0.origins.length * c0.cells.length) * c0.origins.length + 1
  let ctx : Ctx := { c0 with vars := vars, fuel := fuel }
  ⟨⟨ctx, statics, xe⟩, xe + 1⟩

/-- The final abstract state of program `p` in design BO. -/
def analyzeProgBO (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (qf : List Field) : AState :=
  analyzeBO (ctxBO eu K statics fr p qf) p (ainit K fr)

/-- May-alias at the end of `p` in design BO. -/
def mayProgBO (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (x : Var) (px : List ACell) (y : Var) (py : List ACell) : Bool :=
  may (analyzeProgBO eu K statics fr p (afields px ++ afields py)) x px y py

end DirectedAlias.Sound.BlockOnly

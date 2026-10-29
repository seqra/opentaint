import DirectedAlias.Sound.HavocRecency.Soundness

/-!
# Cell-named havoc with narrow reachability (design CN)

The per-cell havoc of `Sound/HavocRecency` adds a new origin to each cell of each reachable
origin at each call, and the reach is generous (every symbolic object). This file states a
cheaper design:

* NARROW REACH. A callee reaches only the closure of its argument values and of the static
  roots, through cells (`ReachN`). The strict call relation `HavocN` is `HavocS` with this
  reach. `ExecN` executions are `ExecS` executions (`ExecN.toExecS`).
* CELL NAMES. The object that a call writes into the cell `(O, c)` has the NAME OF THE CELL:
  `childCN (alpha O) c`. For a symbolic origin this is the origin of the default content.
  For an allocation origin it is a heap child `hsym 0 (rOld s) c []` (both recency origins of
  a site give the same child). Objects below a callee object extend the path. So no origin
  belongs to one call.
* EXPOSED SET. The abstract state keeps the set `exposed` in a reserved variable `xe`.
  A call adds its reachable closure `R` to it. A symbolic origin `sym b q` is not unique if
  `exposed` holds `sym b p` for a proper prefix `p` of `q` (`uniqueCN`).
* THE CALL. `R` is the closure of the argument origins and the static roots: the contents of
  each universe cell of each COVERED origin are added. An origin is covered if it is a
  descendant of an origin in `R` (`descB`). Each universe cell of each covered origin gets
  its own name `childCN o c`. If the closure fails, every origin is covered and every
  universe origin is exposed.

The concrete objects that a call writes are abstracted through a ghost naming `N` in the
soundness proof (`Soundness.lean`); the analysis does not need it.
-/

namespace DirectedAlias.Sound.CellNamed

open DirectedAlias DirectedAlias.Sound DirectedAlias.Sound.Recency DirectedAlias.Sound.Havoc
open DirectedAlias.Sound.HavocRecency

/-! ## Narrow concrete semantics -/

/-- Narrow reach of a call: the values of the arguments, the entry objects of the static
roots, and each object that a cell of a reachable object holds. -/
inductive ReachN (st : CState) (statics : List Root) (args : List Var) : Obj → Prop where
  | arg {x : Var} {o : Obj} : x ∈ args → st.env x = some o → ReachN st statics args o
  | static {r : Root} : r ∈ statics → ReachN st statics args (.sym (.root r) [])
  | step {o o' : Obj} {c : Cell} : ReachN st statics args o → st.heap o c = some o' →
      ReachN st statics args o'

/-- Strict narrow havoc of the `n`-th execution of call site `s`: each cell keeps its value, or
a cell of a narrow-reachable object gets a new object whose tag decodes to that cell. -/
def HavocN (src : Nat → Obj × Cell) (statics : List Root) (st : CState) (args : List Var)
    (s n : Nat) (h' : Heap) : Prop :=
  ∀ o c, h' o c = st.heap o c ∨
    (ReachN st statics args o ∧ ∃ k, src k = (o, c) ∧ h' o c = some (.sym (.havoc s n k) []))

/-- One statement step with the strict narrow call semantics. -/
inductive SStepN (src : Nat → Obj × Cell) (statics : List Root) : Stmt → CState → CState → Prop where
  | new {x s st} :
      SStepN src statics (.new x s) st ((st.setVar x (some (.alloc s (st.cnt s)))).bump s)
  | null {x st} : SStepN src statics (.null x) st (st.setVar x none)
  | copy {x y st} : SStepN src statics (.copy x y) st (st.setVar x (st.env y))
  | load {x y f st o} : st.env y = some o →
      SStepN src statics (.load x y f) st (st.setVar x (st.heap o (.fld f)))
  | store {x f y st o} : st.env x = some o →
      SStepN src statics (.store x f y) st (st.setCell o (.fld f) (st.env y))
  | aload {x y st o} (i : Nat) : st.env y = some o →
      SStepN src statics (.aload x y) st (st.setVar x (st.heap o (.elem i)))
  | astore {x y st o} (i : Nat) : st.env x = some o →
      SStepN src statics (.astore x y) st (st.setCell o (.elem i) (st.env y))
  | unknown {x s st} :
      SStepN src statics (.unknown x s) st
        ((st.setVar x (some (.sym (.fresh s (st.cnt s)) []))).bump s)
  | call {ret s args st h'} : HavocN src statics st args s (st.cnt s) h' →
      SStepN src statics (.call ret s args) st
        (({ st with heap := h' }.setRet ret (some (.sym (.fresh s (st.cnt s)) []))).bump s)

/-- Big-step execution with the strict narrow call semantics. -/
inductive ExecN (src : Nat → Obj × Cell) (statics : List Root) : Prog → CState → CState → Prop where
  | skip {s} : ExecN src statics .skip s s
  | stmt {st s s'} : SStepN src statics st s s' → ExecN src statics (.stmt st) s s'
  | seq {p q s t u} : ExecN src statics p s t → ExecN src statics q t u →
      ExecN src statics (.seq p q) s u
  | choiceL {p q s t} : ExecN src statics p s t → ExecN src statics (.choice p q) s t
  | choiceR {p q s t} : ExecN src statics q s t → ExecN src statics (.choice p q) s t
  | loopZero {p s} : ExecN src statics (.loop p) s s
  | loopMore {p s t u} : ExecN src statics p s t → ExecN src statics (.loop p) t u →
      ExecN src statics (.loop p) s u

/-- One-execution alias under the strict narrow call semantics. -/
def CAliasN (src : Nat → Obj × Cell) (statics : List Root) (fr : Frame) (p : Prog)
    (x : Var) (px : List Cell) (y : Var) (py : List Cell) : Prop :=
  ∃ st, ExecN src statics p (CState.init fr) st ∧ AliasIn st x px y py

/-- A narrow-reachable object is reachable in the generous sense. -/
theorem ReachN.toReach {st : CState} {statics : List Root} {args : List Var} {o : Obj}
    (h : ReachN st statics args o) : Reach st args o := by
  induction h with
  | arg hx he => exact Reach.arg hx he
  | static _ => exact Reach.outer
  | step _ hh ih => exact Reach.step ih hh

/-- A strict narrow havoc is a strict havoc. -/
theorem HavocN.toHavocS {src : Nat → Obj × Cell} {statics : List Root} {st : CState}
    {args : List Var} {s n : Nat} {h' : Heap} (h : HavocN src statics st args s n h') :
    HavocS src st args s n h' := by
  intro o c
  rcases h o c with e | ⟨hr, k, hk, e⟩
  · exact Or.inl e
  · exact Or.inr ⟨hr.toReach, k, hk, e⟩

/-- A narrow step is a strict step. -/
theorem SStepN.toSStepS {src : Nat → Obj × Cell} {statics : List Root} {st : Stmt}
    {s s' : CState} (h : SStepN src statics st s s') : SStepS src st s s' := by
  cases h with
  | new => exact .new
  | null => exact .null
  | copy => exact .copy
  | load he => exact .load he
  | store he => exact .store he
  | aload i he => exact .aload i he
  | astore i he => exact .astore i he
  | unknown => exact .unknown
  | call hh => exact .call hh.toHavocS

/-- A narrow execution is a strict execution. -/
theorem ExecN.toExecS {src : Nat → Obj × Cell} {statics : List Root} {p : Prog} {s s' : CState}
    (h : ExecN src statics p s s') : ExecS src p s s' := by
  induction h with
  | skip => exact .skip
  | stmt hs => exact .stmt hs.toSStepS
  | seq _ _ ih1 ih2 => exact .seq ih1 ih2
  | choiceL _ ih => exact .choiceL ih
  | choiceR _ ih => exact .choiceR ih
  | loopZero => exact .loopZero
  | loopMore _ _ ih1 ih2 => exact .loopMore ih1 ih2

/-- A narrow execution is an execution of the foundation semantics. -/
theorem ExecN.toExec {src : Nat → Obj × Cell} {statics : List Root} {p : Prog} {s s' : CState}
    (h : ExecN src statics p s s') : Exec p s s' :=
  h.toExecS.toExec

/-- A narrow one-execution alias is a strict one-execution alias. -/
theorem CAliasN.toCAliasS {src : Nat → Obj × Cell} {statics : List Root} {fr : Frame}
    {p : Prog} {x y : Var} {px py : List Cell} (h : CAliasN src statics fr p x px y py) :
    CAliasS src fr p x px y py := by
  obtain ⟨st, hx, ha⟩ := h
  exact ⟨st, hx.toExecS, ha⟩

/-! ## Cell names -/

/-- The name of the cell `c` of an origin: the origin of the object that a call writes into it.
For a symbolic origin it is the default child; for an allocation origin it is the heap child
of the site (key `rOld s` for both recency origins). -/
def childCN (K : Nat) : Origin → ACell → Origin
  | .sym b q, c => symOrDeep K b (q ++ [c])
  | .deep b, _ => .deep b
  | .alloc a, c => .hsym 0 (keyOfR (.alloc a)) c []
  | .havoc s, _ => .havoc s
  | .hsym s k c q, c' => if (q ++ [c']).length ≤ K then .hsym s k c (q ++ [c']) else .hdeep s k c
  | .hdeep s k c, _ => .hdeep s k c

/-- The name at path `q` below an origin. -/
def extendCN (K : Nat) : Origin → List ACell → Origin
  | a, [] => a
  | a, c :: cs => extendCN K (childCN K a c) cs

/-- `p` is a prefix of `q`. -/
def preB (p q : List ACell) : Bool := decide (q.take p.length = p)

/-- The origin `u` is a proper descendant of the origin `a` in the tree of cell names: a
symbolic, or heap-child, path extension, or the deep summary of the same family. -/
def descM : Origin → Origin → Bool
  | .sym b p, .sym b' q => decide (b = b') && preB p q
  | .sym b _, .deep b' => decide (b = b')
  | .alloc x, .hsym s k _ _ => decide (s = 0) && decide (k = keyOfR (.alloc x))
  | .alloc x, .hdeep s k _ => decide (s = 0) && decide (k = keyOfR (.alloc x))
  | .hsym s k c p, .hsym s' k' c' q =>
      decide (s = s') && decide (k = k') && decide (c = c') && preB p q
  | .hsym s k c _, .hdeep s' k' c' => decide (s = s') && decide (k = k') && decide (c = c')
  | _, _ => false

/-- The origin `u` is a descendant of the origin `a` (or `a` itself): it is in the subtree of
cell names below `a`. Deep summaries are descendants of each origin of their family. -/
def descB (a u : Origin) : Bool :=
  decide (a = u) || descM a u

/-- The origin `u` is covered by `R`: it is a descendant of an origin in `R`. -/
def coveredB (R : List Origin) (u : Origin) : Bool :=
  R.any (fun a => descB a u)

/-- The origin is below an exposed origin: it is `sym b q`, and `E` holds `sym b p` for a
proper prefix `p` of `q`. -/
def expB (E : List Origin) : Origin → Bool
  | .sym b q => E.any (fun e => match e with
      | .sym b' p => decide (b' = b) && decide (p.length < q.length) && preB p q
      | _ => false)
  | _ => false

/-- Uniqueness with recency and the exposed set: the recency test, and the origin is not
below an exposed origin. -/
def uniqueCN (once : Site → Bool) (eu : Bool) (E : List Origin) (o : Origin) : Bool :=
  uniqueR once eu o && !(expB E o)

/-! ## The abstract analysis -/

/-- The context of design CN: the analysis context, the static roots, and the reserved
variable `xe` that holds the exposed set. -/
structure CtxN where
  ctx : Ctx
  statics : List Root
  xe : Var

/-- The store with the uniqueness test of design CN. -/
def storeCN (cn : CtxN) (X : AState) (x : Var) (c : ACell) (S : List Origin) : AState :=
  match single? (X.env x) with
  | some o =>
    if uniqueCN cn.ctx.once cn.ctx.entryUnique (X.env cn.xe) o then X.setCell o c S
    else X.weakStore (X.env x) c S
  | none => X.weakStore (X.env x) c S

/-- The start set of a call: the origins of the arguments and of the static roots. -/
def callRoots (cn : CtxN) (X : AState) (args : List Var) : List Origin :=
  uni (uniMap X.env args) (cn.statics.map (fun r => Origin.sym (.root r) []))

/-- The contents of the universe cells of the covered universe origins. -/
def succsN (cn : CtxN) (X : AState) (R : List Origin) : List Origin :=
  uniMap (fun u => uniMap (X.heap u) cn.ctx.cells) (cn.ctx.origins.filter (coveredB R))

/-- Close `R` under `succsN`. The result is `none` if the fuel runs out. -/
def closeN (cn : CtxN) (X : AState) : Nat → List Origin → Option (List Origin)
  | 0, _ => none
  | n + 1, R => if subB (succsN cn X R) R then some R else closeN cn X n (uni (succsN cn X R) R)

/-- The cell-named havoc with exposed set `E` and coverage test `cov`: each universe cell of
each covered origin gets its own name, and `E` is added to the exposed set. -/
def havocWith (cn : CtxN) (X : AState) (E : List Origin) (cov : Origin → Bool) : AState where
  env := fupd X.env cn.xe (uni E (X.env cn.xe))
  heap := fun o c => if c ∈ cn.ctx.cells ∧ cov o = true
    then uni [childCN cn.ctx.K o c] (X.heap o c) else X.heap o c

/-- The cell-named havoc of a call: the closure `R` is exposed, and the descendants of `R` are
covered. If the closure fails, all origins are covered and all universe origins are exposed. -/
def havocCN (cn : CtxN) (X : AState) (args : List Var) : AState :=
  match closeN cn X (cn.ctx.origins.length + 1) (callRoots cn X args) with
  | some R => havocWith cn X R (coveredB R)
  | none => havocWith cn X cn.ctx.origins (fun _ => true)

/-- The abstract transfer of design CN (recency, cell names, exposed set). -/
def astepCN (cn : CtxN) : Stmt → AState → AState
  | .new x s, X => (retire s X).setVar x [rNew s]
  | .unknown x s, X => (retire s X).setVar x [.sym (.fresh s) []]
  | .call ret s args, X => (retire s (havocCN cn X args)).setRet ret [.sym (.fresh s) []]
  | .store x f y, X => storeCN cn X x (.fld f) (X.env y)
  | st, X => astep cn.ctx st X

/-- The abstract analysis of design CN. -/
def analyzeCN (cn : CtxN) : Prog → AState → AState
  | .skip, X => X
  | .stmt s, X => astepCN cn s X
  | .seq p q, X => analyzeCN cn q (analyzeCN cn p X)
  | .choice p q, X => join (analyzeCN cn p X) (analyzeCN cn q X)
  | .loop p, X => loopIter cn.ctx (analyzeCN cn p) cn.ctx.fuel X

/-! ## The universe of a program -/

/-- The symbolic bases of a program: the frame roots, the static roots and the fresh sites. -/
def basesCN (fr : Frame) (statics : List Root) (p : Prog) : List ABase :=
  (fr.roots ++ statics).map ABase.root ++ p.freshSites.map ABase.fresh

/-- The heap children of the allocation sites: for each site and cell, the paths up to `K`
and the deep summary. -/
def heapKids (K : Nat) (sites : List Site) (cells : List ACell) : List Origin :=
  sites.flatMap (fun s => cells.flatMap (fun c =>
    (pathsUpTo cells K).map (Origin.hsym 0 (rOld s) c) ++ [Origin.hdeep 0 (rOld s) c]))

/-- The origin universe of design CN: symbolic paths and deep summaries of each base, both
recency origins of each allocation site, and the heap children. -/
def originsCN (K : Nat) (fr : Frame) (statics : List Root) (p : Prog) (cells : List ACell) :
    List Origin :=
  (basesCN fr statics p).flatMap (fun b => (pathsUpTo cells K).map (Origin.sym b) ++ [Origin.deep b]) ++
    p.newSites.flatMap (fun s => [rNew s, rOld s]) ++ heapKids K p.newSites cells

/-- A variable that is larger than each variable of the list. -/
def freshVar (l : List Var) : Var := l.foldr max 0 + 1

/-- The context of a program in design CN with policy `eu`, depth limit `K`, static roots
`statics` and query fields `qf`. The reserved variable is in the variable universe, so the
loop check covers the exposed set. -/
def ctxCN (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog) (qf : List Field) :
    CtxN :=
  let cells := cellsOf (p.fields ++ qf)
  let pv := (p.vars ++ fr.vars).eraseDups
  let xe := freshVar pv
  let vars := xe :: pv
  let origins := originsCN K fr statics p cells
  { ctx := { K := K, once := p.onceB, cells := cells, vars := vars, origins := origins,
             fuel := (vars.length + origins.length * cells.length) * origins.length + 1,
             entryUnique := eu }
    statics := statics
    xe := xe }

/-- The final abstract state of program `p` in design CN. -/
def analyzeProgCN (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (qf : List Field) : AState :=
  analyzeCN (ctxCN eu K statics fr p qf) p (ainit K fr)

/-- May-alias at the end of `p` in design CN. -/
def mayProgCN (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (x : Var) (px : List ACell) (y : Var) (py : List ACell) : Bool :=
  may (analyzeProgCN eu K statics fr p (afields px ++ afields py)) x px y py

end DirectedAlias.Sound.CellNamed

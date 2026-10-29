import DirectedAlias.Sound.Soundness

/-!
# Recency refinement of concept C (CEGAR step for `loop_bf_x`)

Each allocation site `s` has two origins:
* `rNew s` (encoded as `Origin.alloc (2 * s)`): the most recent object of the site;
* `rOld s` (encoded as `Origin.alloc (2 * s + 1)`): all older objects of the site.
In each concrete state, at most one object has the origin `rNew s`. So `rNew s` is unique,
also in a loop, and a store through it is strong.
When a site runs again, the old most recent object becomes old: `retire s` renames `rNew s`
to `rOld s` in every value and moves the cells of `rNew s` into the cells of `rOld s`.
The abstraction depends on the state: it reads the counter of the site.
Everything else (loads, joins, loops, calls, queries) is the same as in concept C.
-/

namespace DirectedAlias.Sound.Recency

open DirectedAlias DirectedAlias.Sound

/-- The origin of the most recent object of site `s`. -/
def rNew (s : Site) : Origin := .alloc (2 * s)

/-- The origin of the older objects of site `s`. -/
def rOld (s : Site) : Origin := .alloc (2 * s + 1)

/-- The recency abstraction of an object in a state. -/
def alphaR (K : Nat) (st : CState) : Obj → Origin
  | .alloc s n => if n + 1 = st.cnt s then rNew s else rOld s
  | o => alpha K o

/-- Rename the most recent origin of site `s` to the old origin. -/
def renameO (s : Site) (o : Origin) : Origin :=
  if o = rNew s then rOld s else o

/-- Rename the most recent origin of site `s` in a set. -/
def renameL (s : Site) (l : List Origin) : List Origin :=
  l.map (renameO s)

/-- The most recent object of site `s` becomes old. -/
def retire (s : Site) (X : AState) : AState where
  env x := renameL s (X.env x)
  heap o c :=
    if o = rNew s then []
    else if o = rOld s then renameL s (uni (X.heap (rNew s) c) (X.heap (rOld s) c))
    else renameL s (X.heap o c)

/-- Uniqueness with recency: `rNew s` is unique for each site. -/
def uniqueR (once : Site → Bool) (eu : Bool) : Origin → Bool
  | .alloc a => a % 2 == 0
  | o => o.uniqueB once eu

/-- The store with the recency uniqueness test. -/
def storeR (ctx : Ctx) (X : AState) (x : Var) (c : ACell) (S : List Origin) : AState :=
  match single? (X.env x) with
  | some o => if uniqueR ctx.once ctx.entryUnique o then X.setCell o c S else X.weakStore (X.env x) c S
  | none => X.weakStore (X.env x) c S

/-- The abstract transfer with recency. A site that runs makes its old most recent object old. -/
def astepR (ctx : Ctx) : Stmt → AState → AState
  | .new x s, X => (retire s X).setVar x [rNew s]
  | .unknown x s, X => (retire s X).setVar x [.sym (.fresh s) []]
  | .call ret s args, X => (retire s (X.havoc ctx args s)).setRet ret [.sym (.fresh s) []]
  | .store x f y, X => storeR ctx X x (.fld f) (X.env y)
  | st, X => astep ctx st X

/-- The abstract analysis with recency. -/
def analyzeR (ctx : Ctx) : Prog → AState → AState
  | .skip, X => X
  | .stmt s, X => astepR ctx s X
  | .seq p q, X => analyzeR ctx q (analyzeR ctx p X)
  | .choice p q, X => join (analyzeR ctx p X) (analyzeR ctx q X)
  | .loop p, X => loopIter ctx (analyzeR ctx p) ctx.fuel X

/-- The origin universe with recency: both origins of each allocation site. -/
def originsR (K : Nat) (fr : Frame) (p : Prog) (cells : List ACell) : List Origin :=
  let bases := fr.roots.map ABase.root ++ p.freshSites.map ABase.fresh
  bases.flatMap (fun b => (pathsUpTo cells K).map (Origin.sym b) ++ [Origin.deep b]) ++
    p.newSites.flatMap (fun s => [rNew s, rOld s]) ++ p.callSites.map Origin.havoc

/-- The context of a program with recency. -/
def ctxR (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) : Ctx :=
  let cells := cellsOf (p.fields ++ qf)
  let vars := (p.vars ++ fr.vars).eraseDups
  let origins := originsR K fr p cells
  { K := K, once := p.onceB, cells := cells, vars := vars, origins := origins,
    fuel := (vars.length + origins.length * cells.length) * origins.length + 1,
    entryUnique := eu }

/-- May-alias at the end of `p`, with recency. -/
def mayProgR (eu : Bool) (K : Nat) (fr : Frame) (p : Prog)
    (x : Var) (px : List ACell) (y : Var) (py : List ACell) : Bool :=
  may (analyzeR (ctxR eu K fr p (afields px ++ afields py)) p (ainit K fr)) x px y py

end DirectedAlias.Sound.Recency

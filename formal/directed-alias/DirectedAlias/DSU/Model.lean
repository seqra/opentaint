import DirectedAlias.Concept

/-!
# Model of today's JVM DSU alias analysis

This file models `DSUAliasAnalysis` (opentaint-jvm-dataflow) and `State` / `IntDisjointSets`
(opentaint-dataflow) at the level of the partition.

A state is a graph. A node is one alias group. A base atom (`Atom`) is a non-heap element
(`SimpleLoc`, `Alloc`, `CallReturn`, `Unknown`). A heap element `HeapAlias(instance, acc)` is an
edge `(g, acc) ↦ t`: the element is in group `t`, and its instance is group `g`.
The edges are functional. This is the congruence invariant that `restoreHeapInvariant` keeps.
The members of a group are its atoms and its incoming edges.

Node ids have no meaning. After each statement, `canon` gives the nodes canonical ids
(breadth-first from the atoms, in the order of the atom universe). It also removes the nodes
that no atom reaches. Thus two states are the same partition exactly when they are equal.
-/

namespace DirectedAlias.DSU

open DirectedAlias

/-- A base element of the DSU. -/
inductive Atom where
  /-- `SimpleLoc(Local v)`. -/
  | loc (v : Var)
  /-- `SimpleLoc(Arg r)` (or `This`, `Static`): the entry root `r`. -/
  | root (r : Root)
  /-- `Alloc(stmt)` of a `new` statement at site `s`. -/
  | alloc (s : Site)
  /-- `Alloc(stmt)` of a `null` constant at statement position `pos`. -/
  | nul (pos : Nat)
  /-- `CallReturn(stmt)` of the call at site `s`. -/
  | ret (s : Site)
  /-- `Unknown(stmt)` of the unknown expression at site `s`. -/
  | unk (s : Site)
  deriving DecidableEq, Repr

/-- A heap accessor: a field, or the array element. -/
abbrev Acc := ACell
/-- A node id (one alias group). -/
abbrev Node := Nat

/-- A DSU state: the group of each atom, the heap edges, and the next fresh node id. -/
structure DState where
  atoms : List (Atom × Node)
  edges : List ((Node × Acc) × Node)
  next : Nat
  deriving DecidableEq, Repr

/-- The empty state. -/
def DState.empty : DState := ⟨[], [], 0⟩

/-- Lookup in an association list. The first entry wins. -/
def lk {α β : Type} [DecidableEq α] (a : α) : List (α × β) → Option β
  | [] => none
  | (k, v) :: l => if a = k then some v else lk a l

/-- The group of an atom. -/
def nodeOf (D : DState) (a : Atom) : Option Node := lk a D.atoms

/-- The target group of the heap element `(n, c)`. -/
def edgeOf (D : DState) (n : Node) (c : Acc) : Option Node := lk (n, c) D.edges

/-- The configuration of the model: constructor roots, static holders, the representative quirk. -/
structure DCfg where
  /-- Roots that are `This(isOuter = false)` (`this` in a constructor). -/
  inner : List Root := []
  /-- Variables that hold the class of static fields. A store through them is `WriteStatic`. -/
  statics : List Var := []
  /-- Model the representative choice of `DsuMergeStrategy` in a load (see `load`). -/
  quirk : Bool := true

/-- The analysis context: the configuration, the atom universe, the accessor universe, the loop fuel. -/
structure DCtx where
  cfg : DCfg
  U : List Atom
  accs : List Acc
  fuel : Nat

/-! ## Primitive operations -/

/-- Remove atom `a` from the state. -/
def delAtom (D : DState) (a : Atom) : DState :=
  { D with atoms := D.atoms.filter (fun p => !decide (p.1 = a)) }

/-- Put atom `a` into group `n`. -/
def addAtom (D : DState) (a : Atom) (n : Node) : DState :=
  { D with atoms := (a, n) :: D.atoms }

/-- Remove the heap element `(n, c)`. -/
def delEdge (D : DState) (n : Node) (c : Acc) : DState :=
  { D with edges := D.edges.filter (fun p => !decide (p.1 = (n, c))) }

/-- Add the heap element `(n, c)` into group `t`. -/
def addEdge (D : DState) (n : Node) (c : Acc) (t : Node) : DState :=
  { D with edges := ((n, c), t) :: D.edges }

/-- A fresh node id. -/
def freshNode (D : DState) : Node × DState := (D.next, { D with next := D.next + 1 })

/-- Rename node `m` to `n`. -/
def renN (m n k : Node) : Node := if k = m then n else k

/-- Rename node `m` to `n` in the whole state. This unites the two groups. -/
def ren (D : DState) (m n : Node) : DState where
  atoms := D.atoms.map (fun p => (p.1, renN m n p.2))
  edges := D.edges.map (fun p => ((renN m n p.1.1, p.1.2), renN m n p.2))
  next := D.next

/-- The first key with two different values, as the pair of the two values. -/
def conflictL {α : Type} [DecidableEq α] : List (α × Node) → Option (Node × Node)
  | [] => none
  | (a, n) :: rest =>
    match lk a rest with
    | some m => if m = n then conflictL rest else some (n, m)
    | none => conflictL rest

/-- The first conflict of a state: an atom in two groups, or a heap element in two groups. -/
def conflict (D : DState) : Option (Node × Node) :=
  match conflictL D.atoms with
  | some p => some p
  | none => conflictL D.edges

/-- Congruence closure: unite the groups of each conflict until no conflict is left.
The result is `none` if the fuel runs out. -/
def normalize : Nat → DState → Option DState
  | 0, D =>
    match conflict D with
    | none => some D
    | some _ => none
  | k + 1, D =>
    match conflict D with
    | none => some D
    | some (n, m) => normalize k (ren D m n)

/-- The fuel of `normalize`: each union removes one node id. -/
def nfuel (D : DState) : Nat := D.atoms.length + 2 * D.edges.length + 1

/-- Unite group `m` into group `n`, then close under congruence. -/
def unite (D : DState) (m n : Node) : Option DState :=
  normalize (nfuel (ren D m n)) (ren D m n)

/-! ## Canonical form and garbage removal -/

/-- Remove repeated nodes. The first occurrence stays. -/
def dedupN : List Node → List Node → List Node
  | [], acc => acc
  | n :: l, acc => if acc.contains n then dedupN l acc else dedupN l (acc ++ [n])

/-- Breadth-first search over the heap edges. -/
def bfs (D : DState) (accs : List Acc) : Nat → List Node → List Node → List Node
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | k + 1, n :: q, seen =>
    let nw := (dedupN (accs.filterMap (edgeOf D n)) []).filter (fun t => !seen.contains t)
    bfs D accs k (q ++ nw) (seen ++ nw)

/-- The position of a node in a list. -/
def idxIn : List Node → Node → Nat
  | [], _ => 0
  | m :: l, n => if m = n then 0 else idxIn l n + 1

/-- The canonical edges of the nodes in `l`, with new ids from position `i`. -/
def canonEdges (D : DState) (accs : List Acc) (σ : Node → Nat) :
    Nat → List Node → List ((Node × Acc) × Node)
  | _, [] => []
  | i, n :: l =>
    accs.filterMap (fun c => (edgeOf D n c).map (fun t => ((i, c), σ t))) ++
      canonEdges D accs σ (i + 1) l

/-- The canonical renaming of a state. It drops each group that no atom reaches (garbage). -/
def canonMap (cx : DCtx) (D : DState) : List Node :=
  let seen0 := dedupN (cx.U.filterMap (nodeOf D)) []
  bfs D cx.accs (D.atoms.length + D.edges.length + 1) seen0 seen0

/-- The canonical form of a state. -/
def canon (cx : DCtx) (D : DState) : DState :=
  let seen := canonMap cx D
  { atoms := cx.U.filterMap (fun a => (nodeOf D a).map (fun n => (a, idxIn seen n))),
    edges := canonEdges D cx.accs (idxIn seen) 0 seen,
    next := seen.length }

/-! ## Group members -/

/-- The atoms of group `n`. -/
def atomsAt (D : DState) (n : Node) : List Atom :=
  (D.atoms.filter (fun p => decide (p.2 = n))).map Prod.fst

/-- The heap elements in group `n` (incoming edges). -/
def inEdges (D : DState) (n : Node) : List (Node × Acc) :=
  (D.edges.filter (fun p => decide (p.2 = n))).map Prod.fst

/-- The number of members of group `n`. -/
def members (D : DState) (n : Node) : Nat := (atomsAt D n).length + (inEdges D n).length

/-- A group with at least two members is in the parent map of `IntDisjointSets`.
Only these groups occur in `allAliasSets()`. -/
def inMap (D : DState) (n : Node) : Bool := decide (2 ≤ members D n)

/-- An outer atom (`aliasInfoIsSimpleOuter`): `Arg`/`Static`/outer `This`, `CallReturn`, `Unknown`. -/
def Atom.outer (cfg : DCfg) : Atom → Bool
  | .root r => !cfg.inner.contains r
  | .ret _ => true
  | .unk _ => true
  | _ => false

/-- A concrete atom: `Alloc` (also of a `null` constant). -/
def Atom.concrete : Atom → Bool
  | .alloc _ => true
  | .nul _ => true
  | _ => false

/-- `containsMultipleConcreteOrOuterLocations`: an outer member, a member on the recursion stack,
an instance group that is multiple, or more than one concrete member (`Alloc` and `HeapAlias`). -/
def multi (cfg : DCfg) (D : DState) : Nat → List Node → Node → Bool
  | 0, _, _ => true
  | k + 1, stack, n =>
    stack.contains n ||
    (atomsAt D n).any (Atom.outer cfg) ||
    (inEdges D n).any (fun e => multi cfg D k (n :: stack) e.1) ||
    decide (1 < (atomsAt D n).countP Atom.concrete + (inEdges D n).length)

/-- The fuel of `multi`. -/
def mfuel (D : DState) : Nat := D.atoms.length + D.edges.length + 2

/-! ## Unions -/

/-- `mergeAliasSets({a, b})` for two atoms. If `a = b`, the set has one element: no change. -/
def unionAtoms (D : DState) (a b : Atom) : Option DState :=
  if a = b then some D else
  match nodeOf D a, nodeOf D b with
  | some n, some m => unite D m n
  | some n, none => some (addAtom D b n)
  | none, some m => some (addAtom D a m)
  | none, none => let p := freshNode D; some (addAtom (addAtom p.2 a p.1) b p.1)

/-- `mergeWith(a, HeapAlias(g, c))`: unite the group of atom `a` with the heap element `(g, c)`. -/
def unionHeap (D : DState) (a : Atom) (g : Node) (c : Acc) : Option DState :=
  match edgeOf D g c, nodeOf D a with
  | some t, some k => unite D k t
  | some t, none => some (addAtom D a t)
  | none, some k => some (addEdge D g c k)
  | none, none => let p := freshNode D; some (addEdge (addAtom p.2 a p.1) g c p.1)

/-- The group of atom `a`. A new singleton group if `a` has no group. -/
def nodeOrFresh (D : DState) (a : Atom) : Node × DState :=
  match nodeOf D a with
  | some n => (n, D)
  | none => let p := freshNode D; (p.1, addAtom p.2 a p.1)

/-- `removeOldAndMergeWith(x, b)`: remove `x`, then unite `x` with atom `b`. -/
def assign (D : DState) (x : Var) (b : Atom) : Option DState :=
  unionAtoms (delAtom D (.loc x)) (.loc x) b

/-- `loc x` is the representative of group `g` (the minimum of `DsuMergeStrategy`):
`Alloc` (kind 0) < `CallReturn` (1) < `SimpleLoc` (2; `Local` < `Arg` < `This` < `Static`) <
`Unknown` (3) < `HeapAlias` (4). -/
def isRepr (D : DState) (g : Node) (x : Var) : Bool :=
  let as := atomsAt D g
  as.contains (.loc x) &&
    !(as.any (fun a => match a with
      | .alloc _ => true | .nul _ => true | .ret _ => true
      | .loc v => decide (v < x) | _ => false))

/-! ## Transfer functions -/

/-- `x := y.c` (`evalHeapLoad`, then `removeOldAndMergeWith`). The instance is the representative
of the group of `y`. If that representative is `loc x`, the removal of `x` leaves the new element
`HeapAlias(x, c)` with the instance `x`, so `x` gets a self loop (with `quirk`). -/
def load (cfg : DCfg) (D : DState) (x y : Var) (c : Acc) : Option DState :=
  let p := nodeOrFresh D (.loc y)
  if cfg.quirk && isRepr p.2 p.1 x then
    let q := freshNode (delAtom p.2 (.loc x))
    some (addEdge (addAtom q.2 (.loc x) q.1) q.1 c q.1)
  else
    unionHeap (delAtom p.2 (.loc x)) (.loc x) p.1 c

/-- `x.c := y` (`evalHeapStore`). A field store is strong if the group of `x` is not `multi`.
An array store is always weak. -/
def store (cfg : DCfg) (D : DState) (x : Var) (c : Acc) (y : Var) (strongOk : Bool) :
    Option DState :=
  let p := nodeOrFresh D (.loc x)
  let D2 := if strongOk && !multi cfg p.2 (mfuel p.2) [] p.1 then delEdge p.2 p.1 c else p.2
  unionHeap D2 (.loc y) p.1 c

/-- One pass of `invalidateOuterHeapAliases`: remove each heap element whose instance group is
invalid, if the element is in a group of `allAliasSets()`. That group is then invalid. -/
def invStep (D : DState) (st : List Node × List (Node × Acc)) : List Node × List (Node × Acc) :=
  D.edges.foldl (fun st e =>
    if st.2.contains e.1 then st
    else if st.1.contains e.1.1 && inMap D e.2 then (e.2 :: st.1, e.1 :: st.2) else st) st

/-- Iterate `invStep` until no new heap element is removed. -/
def invIter (D : DState) : Nat → List Node × List (Node × Acc) → List (Node × Acc)
  | 0, st => st.2
  | k + 1, st =>
    let st' := invStep D st
    if st'.2.length = st.2.length then st.2 else invIter D k st'

/-- `invalidateOuterHeapAliases`: the start groups are the groups of the arguments and the groups
of `allAliasSets()` with an outer atom. All fields are mutable in the IR. -/
def invalidate (cfg : DCfg) (D : DState) (args : List Var) : DState :=
  let start := args.filterMap (fun v => nodeOf D (.loc v)) ++
    D.atoms.filterMap (fun p => if p.1.outer cfg && inMap D p.2 then some p.2 else none)
  let rm := invIter D (D.edges.length + 1) (start, [])
  { D with edges := D.edges.filter (fun e => !rm.contains e.1) }

/-- The DSU transfer of one statement at position `pos`, before the canonical form. -/
def stepRaw (cx : DCtx) (pos : Nat) : Stmt → DState → Option DState
  | .new x s, D => assign D x (.alloc s)
  | .null x, D => assign D x (.nul pos)
  | .copy x y, D => assign D x (.loc y)
  | .load x y f, D => load cx.cfg D x y (.fld f)
  | .store x f y, D =>
    if cx.cfg.statics.contains x then some D else store cx.cfg D x (.fld f) y true
  | .aload x y, D => load cx.cfg D x y .elem
  | .astore x y, D => store cx.cfg D x .elem y false
  | .unknown x s, D => assign D x (.unk s)
  | .call ret s args, D => do
    let D1 ← match ret with
      | some x => assign D x (.ret s)
      | none => some D
    some (invalidate cx.cfg (canon cx D1) args)

/-- The DSU transfer of one statement, in canonical form. -/
def stepD (cx : DCtx) (pos : Nat) (st : Stmt) (D : DState) : Option DState :=
  (stepRaw cx pos st D).map (canon cx)

/-- Shift all node ids by `k`. -/
def shift (k : Nat) (D : DState) : DState where
  atoms := D.atoms.map (fun p => (p.1, p.2 + k))
  edges := D.edges.map (fun p => ((p.1.1 + k, p.1.2), p.2 + k))
  next := D.next + k

/-- `State.merge`: the union of all relations of both states, closed under congruence. -/
def joinD (cx : DCtx) (A B : DState) : Option DState :=
  let B' := shift A.next B
  let C : DState := ⟨A.atoms ++ B'.atoms, A.edges ++ B'.edges, B'.next⟩
  (normalize (nfuel C) C).map (canon cx)

/-- The loop head: iterate `head := merge(entry, body(head))` until the head does not change. -/
def loopD (cx : DCtx) (body : DState → Option DState) (X : DState) :
    Nat → DState → Option DState
  | 0, _ => none
  | k + 1, Y => do
    let B ← body Y
    let J ← joinD cx X B
    if J = Y then some Y else loopD cx body X k J

/-- The DSU analysis of a program whose first statement is at position `pos`. -/
def analyzeD (cx : DCtx) : Nat → Prog → DState → Option DState
  | _, .skip, D => some D
  | pos, .stmt st, D => stepD cx pos st D
  | pos, .seq p q, D => do
    let D1 ← analyzeD cx pos p D
    analyzeD cx (pos + p.stmts.length) q D1
  | pos, .choice p q, D => do
    let A ← analyzeD cx pos p D
    let B ← analyzeD cx (pos + p.stmts.length) q D
    joinD cx A B
  | pos, .loop p, D => loopD cx (analyzeD cx pos p) D cx.fuel D

/-! ## Entry state, universe, query -/

/-- The entry state: each bound variable is in the group of its root (`x = arg` at entry). -/
def initAux (fr : Frame) : List Var → DState → Option DState
  | [], D => some D
  | x :: xs, D =>
    match fr.root? x with
    | some r => (unionAtoms D (.loc x) (.root r)).bind (initAux fr xs)
    | none => initAux fr xs D

/-- The atom universe of a program, in a fixed order. -/
def univ (fr : Frame) (p : Prog) : List Atom :=
  (p.vars ++ fr.vars).eraseDups.map Atom.loc ++ fr.roots.eraseDups.map Atom.root ++
    p.newSites.eraseDups.map Atom.alloc ++ (List.range p.stmts.length).map Atom.nul ++
    p.callSites.eraseDups.map Atom.ret ++ p.freshSites.eraseDups.map Atom.unk

/-- The context of a program. -/
def DCtx.ofProg (cfg : DCfg) (fr : Frame) (p : Prog) : DCtx where
  cfg := cfg
  U := univ fr p
  accs := cellsOf p.fields
  fuel := 64

/-- The DSU state at the end of program `p`. -/
def dsuProg (cfg : DCfg) (fr : Frame) (p : Prog) : Option DState :=
  let cx := DCtx.ofProg cfg fr p
  (initAux fr fr.vars.eraseDups DState.empty).bind (fun D => analyzeD cx 0 p (canon cx D))

/-- The group of access path `x.p`: the group of `x`, then the heap elements along `p`.
The result is `none` if a heap element does not exist. -/
def follow (D : DState) : Node → List Acc → Option Node
  | n, [] => some n
  | n, c :: cs => (edgeOf D n c).bind (fun t => follow D t cs)

/-- The group of access path `x.p`, if it exists. -/
def matD (D : DState) (x : Var) (p : List Acc) : Option Node :=
  (nodeOf D (.loc x)).bind (fun n => follow D n p)

/-- The two paths have the same group. -/
def sameB (D : DState) (x : Var) (px : List Acc) (y : Var) (py : List Acc) : Bool :=
  match matD D x px, matD D y py with
  | some n, some m => decide (n = m)
  | _, _ => false

/-- The query on reversed paths: the two paths have the same group, or they end with the same
accessor and the prefixes are aliases. -/
def mayRev (D : DState) (x y : Var) : List Acc → List Acc → Bool
  | rx, ry =>
    sameB D x rx.reverse y ry.reverse ||
    match rx, ry with
    | c :: rx', d :: ry' => decide (c = d) && mayRev D x y rx' ry'
    | _, _ => false

/-- The DSU alias answer for `x.px` and `y.py` (`findAlias` and `forEachHeapAlias`): a prefix of each
path has the same group, and the rest of the two paths is the same suffix. The client appends the
suffix to the alias (`applyAlias`). A path whose heap element does not exist has no alias through
that element. -/
def dsuMayD (D : DState) (x : Var) (px : List Acc) (y : Var) (py : List Acc) : Bool :=
  mayRev D x y px.reverse py.reverse

/-- The DSU alias answer at the end of program `p`. -/
def dsuMay (cfg : DCfg) (fr : Frame) (p : Prog)
    (x : Var) (px : List Acc) (y : Var) (py : List Acc) : Bool :=
  match dsuProg cfg fr p with
  | some D => dsuMayD D x px y py
  | none => false

/-- The faithful configuration: no constructor roots, no statics, the representative quirk on. -/
def kotlin : DCfg := {}

end DirectedAlias.DSU

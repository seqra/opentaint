import DirectedAlias.Sound.ValueSem.Soundness

/-!
# The CFG model of the engine (design VS on a control flow graph)

The Kotlin engine runs a worklist over the JIR control flow graph, with exceptional edges.
This file gives the CFG model, its instrumented concrete semantics, the abstract transfer of
one node (design VS with a store guard), and the POST-FIXPOINT CERTIFICATE `PostFix`.
`Impl/CfgSound.lean` proves that each post-fixpoint is sound (`csoundCfg`), so the iteration
strategy of the engine is irrelevant for soundness.

## The model

* A node has an instruction, normal successors, exceptional successors (handlers), and a list
  of KILLS: variables that become unassigned at the node entry, before the instruction. A kill
  node of the brief (`kill x`) is a node `nop` with the kill list `[x]`. A kill is a node prefix,
  so no kill sits between a `throw` and its `catch` (the pending exception survives).
* Instructions: an IR statement (no static writes: A5), `nop`, `throw y` (`thr`), `catch x s`
  (`cat`, the handler entry), and `const x s` (`cnst`, a constant read with the shared site `s`
  of its key).
* The null site of a null statement is the number of null statements in the nodes before it.
* A configuration is a node, an instrumented state, and a pending exception (an object or none).
* Normal step: the kills, then the instruction, then a normal successor; the pending exception
  becomes none. Exceptional step: the kills, then no effect (or, for a call, the callee effect
  without the result; for `throw y`, the object of `y` is pending), then a handler.
* `catch x s`: `x` gets the pending object, or else a fresh object of site `s`.
* `const x s`: `x` gets a fresh object of site `s` or an object that site `s` made before (REUSE).
-/

namespace DirectedAlias.Impl.Cfg

open DirectedAlias DirectedAlias.Sound DirectedAlias.Sound.Recency DirectedAlias.Sound.Havoc
open DirectedAlias.Sound.HavocRecency DirectedAlias.Sound.CellNamed DirectedAlias.Sound.BlockOnly
open DirectedAlias.Sound.ValueSem DirectedAlias.Opt

/-! ## Syntax -/

/-- An instruction of a CFG node. -/
inductive Instr where
  /-- An IR statement. -/
  | stmt (st : Stmt)
  /-- No operation. -/
  | nop
  /-- `throw y`. -/
  | thr (y : Var)
  /-- `x = catch` at site `s` (the handler entry). -/
  | cat (x : Var) (s : Site)
  /-- `x = const` with the shared site `s` of the constant key. -/
  | cnst (x : Var) (s : Site)
  deriving DecidableEq, Repr

/-- A CFG node: an instruction, the normal successors, the exceptional successors, and the
variables that the node kills at its entry. -/
structure Node where
  instr : Instr
  succ : List Nat
  exc : List Nat
  kills : List Var := []
  deriving DecidableEq, Repr

/-- A control flow graph: the nodes (node `v` is at index `v`) and the entry node. -/
structure Cfg where
  nodes : List Node
  entry : Nat
  deriving DecidableEq, Repr

/-- The site of an instruction, if it has one. -/
def Instr.site? : Instr → Option Site
  | .stmt st => st.site?
  | .cat _ s => some s
  | .cnst _ s => some s
  | _ => none

/-- The number of null statements of an instruction. -/
def Instr.nullN : Instr → Nat
  | .stmt st => st.nullN
  | _ => 0

/-- The site of node `v`, if it has one. -/
def Cfg.siteAt (g : Cfg) (v : Nat) : Option Site :=
  (g.nodes[v]?).bind (fun nd => nd.instr.site?)

/-- The null site of node `v`: the number of null statements in the nodes before `v`. -/
def Cfg.nullSite (g : Cfg) (v : Nat) : Nat :=
  ((g.nodes.take v).map (fun nd => nd.instr.nullN)).sum

/-! ## Graph reachability and the once test -/

/-- The successors of node `v` over normal and exceptional edges. -/
def Cfg.outs (g : Cfg) (v : Nat) : List Nat :=
  match g.nodes[v]? with
  | some nd => nd.succ ++ nd.exc
  | none => []

/-- An edge (normal or exceptional) from `a` to `b`. -/
def Cfg.Edge (g : Cfg) (a b : Nat) : Prop := b ∈ g.outs a

/-- Reflexive and transitive reachability over the edges. -/
inductive GReach (g : Cfg) : Nat → Nat → Prop where
  | refl {a : Nat} : GReach g a a
  | step {a b c : Nat} : g.Edge a b → GReach g b c → GReach g a c

/-- Close `R` under the successors. The result is `none` if the fuel runs out. -/
def Cfg.closeG (g : Cfg) : Nat → List Nat → Option (List Nat)
  | 0, _ => none
  | k + 1, R => if subB (uniMap g.outs R) R then some R else g.closeG k (uni (uniMap g.outs R) R)

/-- The fuel of the closure: the number of nodes and edges, plus two. -/
def Cfg.fuelG (g : Cfg) : Nat :=
  g.nodes.length + (g.nodes.map (fun nd => nd.succ.length + nd.exc.length)).sum + 2

/-- Node `u` is on a cycle (conservative: true if the closure fails). -/
def Cfg.onCycleB (g : Cfg) (u : Nat) : Bool :=
  match g.closeG g.fuelG (g.outs u) with
  | some R => decide (u ∈ R)
  | none => true

/-- Site `t` is once: exactly one node has site `t`, and that node is on no cycle. -/
def Cfg.onceB (g : Cfg) (t : Site) : Bool :=
  match (List.range g.nodes.length).filter (fun v => decide (g.siteAt v = some t)) with
  | [u] => !(g.onCycleB u)
  | _ => false

/-! ## The universe -/

/-- The structured program of an instruction, for the universe: `throw y` mentions `y`, and
`catch`/`const` are unknown expressions of their site. -/
def Instr.prog : Instr → Prog
  | .stmt st => .stmt st
  | .nop => .skip
  | .thr y => .stmt (.copy y y)
  | .cat x s => .stmt (.unknown x s)
  | .cnst x s => .stmt (.unknown x s)

/-- The structured program of the kills of a node, for the universe. -/
def killProg (xs : List Var) : Prog :=
  xs.foldr (fun x p => .seq (.stmt (.copy x x)) p) .skip

/-- The structured program of a node, for the universe. -/
def Node.prog (nd : Node) : Prog := .seq (killProg nd.kills) nd.instr.prog

/-- The structured program of a CFG, for the universe: the sequence of its node programs. -/
def Cfg.prog (g : Cfg) : Prog := g.nodes.foldr (fun nd p => .seq nd.prog p) .skip

/-- The context of a CFG: the context of design VS of the CFG program, with the once test of
the CFG. -/
def cfgCtx (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (g : Cfg) (qf : List Field) :
    CtxB :=
  let cb := ctxVS eu K statics fr g.prog qf
  ⟨⟨{ cb.cn.ctx with once := g.onceB }, cb.cn.statics, cb.cn.xe⟩, cb.xv⟩

/-! ## Abstract transfer -/

/-- Give each empty cell its cell name. The states of the engine have no empty cell, so this is
the identity on them; it makes the check sound for each certificate. -/
def pad (K : Nat) (X : AState) : AState where
  env := X.env
  heap := fun o c => match X.heap o c with
    | [] => [childCN K o c]
    | a :: l => a :: l

/-- The abstract kill: each variable of `xs` gets the empty set. -/
def killS (xs : List Var) (X : AState) : AState := xs.foldl (fun Y x => Y.setVar x []) X

/-- The state at the node entry: the padded state, after the kills of the node. -/
def entryS (cb : CtxB) (nd : Node) (X : AState) : AState := killS nd.kills (pad cb.cn.ctx.K X)

/-- The guarded store: strong only if the store of design BO is strong and the guard accepts
the target origin. -/
def storeG (cb : CtxB) (guard : Origin → Bool) (X : AState) (x : Var) (c : ACell)
    (S : List Origin) : AState :=
  match single? (X.env x) with
  | some o => if guard o = true then storeBO cb X x c S else X.weakStore (X.env x) c S
  | none => storeBO cb X x c S

/-- The abstract transfer of an instruction at node `v` with null site `i`. `T v` holds the
thrown values for the handler `v`. -/
def itrans (cb : CtxB) (guard : Origin → Bool) (T : Nat → List Origin) (i v : Nat) :
    Instr → AState → AState
  | .stmt (.store x f y), X => storeG cb guard X x (.fld f) (X.env y)
  | .stmt st, X => astepVS cb i st X
  | .nop, X => X
  | .thr _, X => X
  | .cat x s, X => join (astepVS cb i (.unknown x s) X) (X.setVar x (T v))
  | .cnst x s, X => join (astepVS cb i (.unknown x s) X) (X.setVar x [.sym (.fresh s) []])

/-- The abstract transfer of node `v`. -/
def trans (cb : CtxB) (guard : Origin → Bool) (T : Nat → List Origin) (g : Cfg) (v : Nat)
    (nd : Node) (X : AState) : AState :=
  itrans cb guard T (g.nullSite v) v nd.instr (entryS cb nd X)

/-- The partial call of a call node: the passive call sets and the counter, without the result
assignment (the callee throws). -/
def partialS (cb : CtxB) (nd : Node) (s : Site) (args : List Var) (X : AState) : AState :=
  astepVS cb 0 (.call none s args) (entryS cb nd X)

/-! ## The post-fixpoint certificate -/

/-- A POST-FIXPOINT of the transfer of design VS on the CFG: `Sb v` is the state before node
`v`, `Sa v` the state after it, and `T h` the thrown values for handler `h`. -/
structure PostFix (cb : CtxB) (guard : Origin → Bool) (g : Cfg) (fr : Frame)
    (Sb Sa : Nat → AState) (T : Nat → List Origin) : Prop where
  /-- The state before each node holds only universe origins. -/
  supp : ∀ v nd, g.nodes[v]? = some nd → Supp cb.cn.ctx (Sb v)
  /-- The entry state is below the state before the entry node. -/
  entry : leOn cb.cn.ctx (ainitV cb.cn.ctx.K fr) (Sb g.entry) = true
  /-- The transfer of each node is below the state after it. -/
  node : ∀ v nd, g.nodes[v]? = some nd → leOn cb.cn.ctx (trans cb guard T g v nd (Sb v)) (Sa v) = true
  /-- A normal edge: the state after the node is below the state before the successor. -/
  succ : ∀ v nd w, g.nodes[v]? = some nd → w ∈ nd.succ → leOn cb.cn.ctx (Sa v) (Sb w) = true
  /-- An exceptional edge: the entry state of the node is below the state before the handler. -/
  exc : ∀ v nd h, g.nodes[v]? = some nd → h ∈ nd.exc →
    leOn cb.cn.ctx (entryS cb nd (Sb v)) (Sb h) = true
  /-- An exceptional edge of a call: the partial call is below the state before the handler. -/
  excCall : ∀ v nd h ret s args, g.nodes[v]? = some nd → h ∈ nd.exc →
    nd.instr = .stmt (.call ret s args) →
    leOn cb.cn.ctx (partialS cb nd s args (Sb v)) (Sb h) = true
  /-- An exceptional edge of a throw: the thrown values are in `T h`. -/
  excThrow : ∀ v nd h y, g.nodes[v]? = some nd → h ∈ nd.exc → nd.instr = .thr y →
    (entryS cb nd (Sb v)).env y ⊆ T h

/-! ## Concrete semantics -/

/-- Kill variable `x`: it becomes unassigned. -/
def killV (vs : VState) (x : Var) : VState :=
  { vs with cs := vs.cs.setVar x none, nv := fupd vs.nv x none }

/-- Kill each variable of `xs`. -/
def killAllV (xs : List Var) (vs : VState) : VState := xs.foldl killV vs

/-- A normal step of an instruction with null site `i` and pending exception `e`. -/
inductive IStep (src : Nat → Obj × Cell) (statics : List Root) (i : Nat) :
    Instr → Option Obj → VState → VState → Prop where
  | stmt {st e vs vs'} : SStepV src statics i st vs vs' → IStep src statics i (.stmt st) e vs vs'
  | nop {e vs} : IStep src statics i .nop e vs vs
  | thr {y e vs} : IStep src statics i (.thr y) e vs vs
  | catP {x s o vs} : IStep src statics i (.cat x s) (some o) vs (vs.setVarV x (.obj o))
  | catF {x s vs vs'} : SStepV src statics i (.unknown x s) vs vs' →
      IStep src statics i (.cat x s) none vs vs'
  | cnstF {x s e vs vs'} : SStepV src statics i (.unknown x s) vs vs' →
      IStep src statics i (.cnst x s) e vs vs'
  | cnstR {x s e vs n} : n < vs.cs.cnt s →
      IStep src statics i (.cnst x s) e vs (vs.setVarV x (.obj (.sym (.fresh s n) [])))

/-- An exceptional step of an instruction: no effect and an unknown exception; or the object of
`y` for `throw y`; or the callee effect without the result for a call. -/
inductive XStep (src : Nat → Obj × Cell) (statics : List Root) :
    Instr → VState → VState → Option Obj → Prop where
  | none {ins vs} : XStep src statics ins vs vs none
  | thr {y vs o} : vs.cs.env y = some o → XStep src statics (.thr y) vs vs (some o)
  | call {ret s args vs vs'} : SStepV src statics 0 (.call none s args) vs vs' →
      XStep src statics (.stmt (.call ret s args)) vs vs' none

/-- A configuration: the node, the instrumented state before the node, and the pending
exception. -/
structure Conf where
  node : Nat
  vs : VState
  exc : Option Obj

/-- One step of the CFG. -/
inductive Step (src : Nat → Obj × Cell) (statics : List Root) (g : Cfg) : Conf → Conf → Prop where
  | norm {v nd w vs vs' e} : g.nodes[v]? = some nd → w ∈ nd.succ →
      IStep src statics (g.nullSite v) nd.instr e (killAllV nd.kills vs) vs' →
      Step src statics g ⟨v, vs, e⟩ ⟨w, vs', none⟩
  | exc {v nd h vs vs' e e'} : g.nodes[v]? = some nd → h ∈ nd.exc →
      XStep src statics nd.instr (killAllV nd.kills vs) vs' e' →
      Step src statics g ⟨v, vs, e⟩ ⟨h, vs', e'⟩

/-- The reachable configurations of a CFG from the frame entry. -/
inductive Reach (src : Nat → Obj × Cell) (statics : List Root) (g : Cfg) (fr : Frame) :
    Conf → Prop where
  | init : Reach src statics g fr ⟨g.entry, VState.init fr, none⟩
  | step {c c' : Conf} : Reach src statics g fr c → Step src statics g c c' →
      Reach src statics g fr c'

/-! ## Liveness -/

/-- The variables that a statement reads. -/
def _root_.DirectedAlias.Stmt.uses : Stmt → List Var
  | .new _ _ => []
  | .null _ => []
  | .copy _ y => [y]
  | .load _ y _ => [y]
  | .store x _ y => [x, y]
  | .aload _ y => [y]
  | .astore x y => [x, y]
  | .unknown _ _ => []
  | .call _ _ args => args

/-- The variables that a statement writes. -/
def _root_.DirectedAlias.Stmt.defs : Stmt → List Var
  | .new x _ => [x]
  | .null x => [x]
  | .copy x _ => [x]
  | .load x _ _ => [x]
  | .store _ _ _ => []
  | .aload x _ => [x]
  | .astore _ _ => []
  | .unknown x _ => [x]
  | .call ret _ _ => ret.toList

/-- The variables that an instruction reads. -/
def Instr.uses : Instr → List Var
  | .stmt st => st.uses
  | .thr y => [y]
  | _ => []

/-- The variables that an instruction writes. -/
def Instr.defs : Instr → List Var
  | .stmt st => st.defs
  | .cat x _ => [x]
  | .cnst x _ => [x]
  | _ => []

/-- A LIVENESS CERTIFICATE (the fixed rule): `live v` holds the uses of `v`, the live variables
of each normal successor that `v` does not write, and ALL live variables of each handler (an
exception happens before the write). -/
def LiveOK (g : Cfg) (live : Nat → List Var) : Prop :=
  ∀ v nd, g.nodes[v]? = some nd →
    (∀ x ∈ nd.instr.uses, x ∈ live v) ∧
    (∀ w ∈ nd.succ, ∀ x ∈ live w, x ∉ nd.instr.defs → x ∈ live v) ∧
    (∀ h ∈ nd.exc, ∀ x ∈ live h, x ∈ live v)

/-- The liveness rule of the brief: `live_in v = use v ∪ (live_out v \ def v)`, where
`live_out v` joins the normal AND the exceptional successors. -/
def LiveOKSpec (g : Cfg) (live : Nat → List Var) : Prop :=
  ∀ v nd, g.nodes[v]? = some nd →
    (∀ x ∈ nd.instr.uses, x ∈ live v) ∧
    (∀ w ∈ nd.succ ++ nd.exc, ∀ x ∈ live w, x ∉ nd.instr.defs → x ∈ live v)

/-- The Boolean check of the fixed liveness rule. -/
def liveOKB (g : Cfg) (live : Nat → List Var) : Bool :=
  (List.range g.nodes.length).all (fun v => match g.nodes[v]? with
    | some nd => subB nd.instr.uses (live v) &&
        nd.succ.all (fun w => (live w).all (fun x => decide (x ∈ nd.instr.defs) || decide (x ∈ live v))) &&
        nd.exc.all (fun h => subB (live h) (live v))
    | none => true)

/-- The Boolean check of the liveness rule of the brief. -/
def liveOKSpecB (g : Cfg) (live : Nat → List Var) : Bool :=
  (List.range g.nodes.length).all (fun v => match g.nodes[v]? with
    | some nd => subB nd.instr.uses (live v) &&
        (nd.succ ++ nd.exc).all (fun w =>
          (live w).all (fun x => decide (x ∈ nd.instr.defs) || decide (x ∈ live v)))
    | none => true)

/-- A node without its kills. -/
def Node.strip (nd : Node) : Node := { nd with kills := [] }

/-- `g'` is `g` with kills: the same nodes up to the kills, the same entry, and `g` has no
kills. -/
structure KillExt (g g' : Cfg) : Prop where
  entry : g'.entry = g.entry
  strip : g'.nodes.map Node.strip = g.nodes.map Node.strip
  noKill : ∀ (v : Nat) (nd : Node), g.nodes[v]? = some nd → nd.kills = []

/-- Each kill of `g'` at node `v` removes a variable that is not live at `v`. -/
def KillOK (g' : Cfg) (live : Nat → List Var) : Prop :=
  ∀ (v : Nat) (nd : Node), g'.nodes[v]? = some nd → ∀ x ∈ nd.kills, x ∉ live v

end DirectedAlias.Impl.Cfg

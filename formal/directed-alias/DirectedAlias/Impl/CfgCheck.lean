import DirectedAlias.Impl.CfgSound

/-!
# An executable post-fixpoint checker and a small CFG solver

* `postFixB` checks the conditions of `PostFix` on the universe; `postFixB_sound` proves that
  a true answer gives `PostFix`. The engine can run the same check in tests.
* `solveCfg` is a small solver: a round-robin (Jacobi) iteration over the nodes, with an
  ACCUMULATING JOIN at the given head nodes and an overwrite at the other nodes, and fuel.
  It returns a certificate only if `postFixB` accepts it (`solveCfg_sound`), so each answer of
  the solver is sound by `csoundCfg`, whatever the head nodes and the iteration order.
* The flag `chkT` of the checker and the flag `useT` of the solver switch off the throw condition
  and the thrown values. With both off, the solver computes the COMPACT-SPEC rule for a catch
  (`T h = []`: a catch variable is only the result origin `⟨s⟩`); see `Impl/CfgExamples.lean`.
-/

namespace DirectedAlias.Impl.Cfg

open DirectedAlias DirectedAlias.Sound DirectedAlias.Sound.Recency DirectedAlias.Sound.Havoc
open DirectedAlias.Sound.HavocRecency DirectedAlias.Sound.CellNamed DirectedAlias.Sound.BlockOnly
open DirectedAlias.Sound.ValueSem DirectedAlias.Opt

/-! ## The checker -/

/-- Boolean support test: each universe key holds only universe origins. -/
def suppB (ctx : Ctx) (X : AState) : Bool :=
  (ukeys ctx).all (fun k => subB (cval X k) ctx.origins)

/-- `suppB` gives support. -/
theorem suppB_sound {ctx : Ctx} {X : AState} (h : suppB ctx X = true) : Supp ctx X := by
  intro k hk
  exact subB_iff.mp (List.all_eq_true.mp h k (mem_ukeys.mpr hk))

/-- The call condition of an exceptional edge (true for a node that is not a call). -/
def callCondB (cb : CtxB) (nd : Node) (Xv Xh : AState) : Bool :=
  match nd.instr with
  | .stmt (.call _ s args) => leOn cb.cn.ctx (partialS cb nd s args Xv) Xh
  | _ => true

/-- The throw condition of an exceptional edge (true for a node that is not a throw). -/
def throwCondB (cb : CtxB) (nd : Node) (Xv : AState) (P : List Origin) : Bool :=
  match nd.instr with
  | .thr y => subB ((entryS cb nd Xv).env y) P
  | _ => true

/-- The conditions of one node; `chkT` switches the throw condition on. -/
def nodeB (cb : CtxB) (guard : Origin → Bool) (g : Cfg) (Sb Sa : Nat → AState)
    (T : Nat → List Origin) (chkT : Bool) (v : Nat) (nd : Node) : Bool :=
  suppB cb.cn.ctx (Sb v) && leOn cb.cn.ctx (trans cb guard T g v nd (Sb v)) (Sa v) &&
    nd.succ.all (fun w => leOn cb.cn.ctx (Sa v) (Sb w)) &&
    nd.exc.all (fun h => leOn cb.cn.ctx (entryS cb nd (Sb v)) (Sb h) &&
      callCondB cb nd (Sb v) (Sb h) && (!chkT || throwCondB cb nd (Sb v) (T h)))

/-- THE EXECUTABLE POST-FIXPOINT CHECK; `chkT` switches the throw condition on. -/
def postFixB (cb : CtxB) (guard : Origin → Bool) (g : Cfg) (fr : Frame) (Sb Sa : Nat → AState)
    (T : Nat → List Origin) (chkT : Bool := true) : Bool :=
  leOn cb.cn.ctx (ainitV cb.cn.ctx.K fr) (Sb g.entry) &&
    (List.range g.nodes.length).all (fun v => match g.nodes[v]? with
      | some nd => nodeB cb guard g Sb Sa T chkT v nd
      | none => true)

/-- A node of the graph is in the index range. -/
theorem lt_of_getElem? {g : Cfg} {v : Nat} {nd : Node} (hn : g.nodes[v]? = some nd) :
    v < g.nodes.length := by
  by_cases hlt : v < g.nodes.length
  · exact hlt
  · rw [List.getElem?_eq_none (Nat.le_of_not_lt hlt)] at hn; cases hn

/-- The check gives the conditions of each node. -/
theorem postFixB_node {cb : CtxB} {guard : Origin → Bool} {g : Cfg} {fr : Frame}
    {Sb Sa : Nat → AState} {T : Nat → List Origin} {chkT : Bool}
    (h : postFixB cb guard g fr Sb Sa T chkT = true) {v : Nat} {nd : Node}
    (hn : g.nodes[v]? = some nd) : nodeB cb guard g Sb Sa T chkT v nd = true := by
  unfold postFixB at h
  rw [Bool.and_eq_true] at h
  have := List.all_eq_true.mp h.2 v (List.mem_range.mpr (lt_of_getElem? hn))
  rw [hn] at this
  exact this

/-- SOUNDNESS OF THE CHECKER: a true answer of `postFixB` (with the throw condition) gives the
post-fixpoint certificate. -/
theorem postFixB_sound {cb : CtxB} {guard : Origin → Bool} {g : Cfg} {fr : Frame}
    {Sb Sa : Nat → AState} {T : Nat → List Origin}
    (h : postFixB cb guard g fr Sb Sa T true = true) : PostFix cb guard g fr Sb Sa T := by
  have hN := fun {v} {nd} (hn : g.nodes[v]? = some nd) => postFixB_node h hn
  have parts : ∀ {v nd}, g.nodes[v]? = some nd →
      suppB cb.cn.ctx (Sb v) = true ∧ leOn cb.cn.ctx (trans cb guard T g v nd (Sb v)) (Sa v) = true ∧
      (∀ w ∈ nd.succ, leOn cb.cn.ctx (Sa v) (Sb w) = true) ∧
      (∀ h ∈ nd.exc, leOn cb.cn.ctx (entryS cb nd (Sb v)) (Sb h) = true ∧
        callCondB cb nd (Sb v) (Sb h) = true ∧ throwCondB cb nd (Sb v) (T h) = true) := by
    intro v nd hn
    have h1 := hN hn
    unfold nodeB at h1
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_true, Bool.false_or] at h1
    obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := h1
    exact ⟨a, b, c, fun h hh => ⟨(d h hh).1.1, (d h hh).1.2, (d h hh).2⟩⟩
  unfold postFixB at h
  rw [Bool.and_eq_true] at h
  exact {
    supp := fun v nd hn => suppB_sound (parts hn).1
    entry := h.1
    node := fun v nd hn => (parts hn).2.1
    succ := fun v nd w hn hw => (parts hn).2.2.1 w hw
    exc := fun v nd hh hn he => ((parts hn).2.2.2 hh he).1
    excCall := fun v nd hh ret s args hn he hins => by
      have := ((parts hn).2.2.2 hh he).2.1
      unfold callCondB at this; rw [hins] at this; exact this
    excThrow := fun v nd hh y hn he hins => by
      have := ((parts hn).2.2.2 hh he).2.2
      unfold throwCondB at this; rw [hins] at this; exact subB_iff.mp this }

/-! ## The solver -/

/-- A certificate: the states before and after each node, and the thrown values of each
handler. -/
structure Cert where
  sb : Nat → AState
  sa : Nat → AState
  tt : Nat → List Origin

/-- The empty state. -/
def botS : AState := ⟨fun _ => [], fun _ _ => []⟩

/-- Tabulate a state on the universe (a materialized state); outside the universe a cell holds
its cell name. -/
def matS (ctx : Ctx) (X : AState) : AState :=
  let et := ctx.vars.map (fun x => (x, X.env x))
  let ht := ctx.origins.map (fun o => (o, ctx.cells.map (fun c => (c, X.heap o c))))
  { env := fun x => (et.lookup x).getD []
    heap := fun o c => match ht.lookup o with
      | some l => (l.lookup c).getD [childCN ctx.K o c]
      | none => [childCN ctx.K o c] }

/-- The states after the nodes for the states before them. -/
def afterS (cb : CtxB) (guard : Origin → Bool) (g : Cfg) (sb : Nat → AState)
    (tt : Nat → List Origin) (v : Nat) : AState :=
  match g.nodes[v]? with
  | some nd => trans cb guard tt g v nd (sb v)
  | none => sb v

/-- The contributions of node `v` to the state before node `w`. -/
def contrib (cb : CtxB) (g : Cfg) (sb sa : Nat → AState) (w v : Nat) : List AState :=
  match g.nodes[v]? with
  | some nd =>
    (if w ∈ nd.succ then [sa v] else []) ++
    (if w ∈ nd.exc then
      entryS cb nd (sb v) :: (match nd.instr with
        | .stmt (.call _ s args) => [partialS cb nd s args (sb v)]
        | _ => [])
    else [])
  | none => []

/-- The thrown values that node `v` gives to handler `h`. -/
def thrown (cb : CtxB) (g : Cfg) (sb : Nat → AState) (h v : Nat) : List Origin :=
  match g.nodes[v]? with
  | some nd => if h ∈ nd.exc then
      (match nd.instr with
        | .thr y => (entryS cb nd (sb v)).env y
        | _ => [])
    else []
  | none => []

/-- One round of the solver: each state before a node is the join of its contributions (and the
entry state at the entry); a head node also keeps its old state (accumulating join). -/
def round (cb : CtxB) (guard : Origin → Bool) (g : Cfg) (fr : Frame) (heads : List Nat)
    (useT : Bool) (sb : Nat → AState) (tt : Nat → List Origin) :
    (Nat → AState) × (Nat → List Origin) :=
  let sa := afterS cb guard g sb tt
  let n := g.nodes.length
  let tbl := (List.range n).map (fun w =>
    matS cb.cn.ctx (((List.range n).flatMap (contrib cb g sb sa w)).foldl join
      (join (if w ∈ heads then sb w else botS)
        (if w = g.entry then ainitV cb.cn.ctx.K fr else botS))))
  let ttl := (List.range n).map (fun h =>
    if useT then uni (tt h) (uniMap (thrown cb g sb h) (List.range n)) else [])
  (fun w => tbl.getD w botS, fun h => ttl.getD h [])

/-- The solver loop: stop at the first round whose certificate passes the check. -/
def solveIter (cb : CtxB) (guard : Origin → Bool) (g : Cfg) (fr : Frame) (heads : List Nat)
    (useT chkT : Bool) : Nat → (Nat → AState) → (Nat → List Origin) → Option Cert
  | 0, _, _ => none
  | k + 1, sb, tt =>
    if postFixB cb guard g fr sb (afterS cb guard g sb tt) tt chkT then
      some ⟨sb, afterS cb guard g sb tt, tt⟩
    else
      let r := round cb guard g fr heads useT sb tt
      solveIter cb guard g fr heads useT chkT k r.1 r.2

/-- THE SOLVER: start from the empty states, iterate with fuel, and return a certificate only if
the check accepts it. -/
def solveCfg (cb : CtxB) (guard : Origin → Bool) (g : Cfg) (fr : Frame) (heads : List Nat)
    (fuel : Nat) (useT chkT : Bool := true) : Option Cert :=
  solveIter cb guard g fr heads useT chkT fuel (fun _ => botS) (fun _ => [])

/-- Each certificate of the solver loop passes the check. -/
theorem solveIter_check {cb : CtxB} {guard : Origin → Bool} {g : Cfg} {fr : Frame}
    {heads : List Nat} {useT chkT : Bool} :
    ∀ {k : Nat} {sb : Nat → AState} {tt : Nat → List Origin} {C : Cert},
      solveIter cb guard g fr heads useT chkT k sb tt = some C →
      postFixB cb guard g fr C.sb C.sa C.tt chkT = true
  | 0, _, _, _, h => by cases h
  | k + 1, sb, tt, C, h => by
    simp only [solveIter] at h
    split at h
    · rename_i hp; cases h; exact hp
    · exact solveIter_check h

/-- SOUNDNESS OF THE SOLVER: each certificate of `solveCfg` (with the throw condition) is a
post-fixpoint, so each of its answers is sound by `csoundCfg`. -/
theorem solveCfg_sound {cb : CtxB} {guard : Origin → Bool} {g : Cfg} {fr : Frame}
    {heads : List Nat} {fuel : Nat} {useT : Bool} {C : Cert}
    (h : solveCfg cb guard g fr heads fuel useT true = some C) : PostFix cb guard g fr C.sb C.sa C.tt :=
  postFixB_sound (solveIter_check h)

/-- The may-alias answer of the solver at node `v` (before the node), or false if the solver
fails. -/
def solveMay (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (g : Cfg)
    (guard : Origin → Bool) (heads : List Nat) (fuel : Nat) (v : Nat)
    (x : Var) (px : List ACell) (y : Var) (py : List ACell) (useT chkT : Bool := true) : Bool :=
  match solveCfg (cfgCtx eu K statics fr g (afields px ++ afields py)) guard g fr heads fuel
      useT chkT with
  | some C => may (C.sb v) x px y py
  | none => false

/-- THE SOLVER ANSWER IS SOUND: if the solver answers false at node `v`, no reachable
configuration at `v` has the value alias (for each naming and each guard). -/
theorem solveMay_sound (src : Nat → Obj × Cell) (statics : List Root) (eu : Bool) (K : Nat)
    (fr : Frame) (g : Cfg) (guard : Origin → Bool) (heads : List Nat) (fuel : Nat) (v : Nat)
    (x : Var) (px : List Cell) (y : Var) (py : List Cell) (useT : Bool)
    (hs : (solveCfg (cfgCtx eu K statics fr g (afields (px.map Cell.abs) ++ afields (py.map Cell.abs)))
      guard g fr heads fuel useT true).isSome = true)
    {vs : VState} {e : Option Obj} (hr : Reach src statics g fr ⟨v, vs, e⟩)
    (ha : AliasInV vs x px y py) :
    solveMay eu K statics fr g guard heads fuel v x (px.map Cell.abs) y (py.map Cell.abs) useT true
      = true := by
  unfold solveMay
  cases hC : solveCfg (cfgCtx eu K statics fr g (afields (px.map Cell.abs) ++
      afields (py.map Cell.abs))) guard g fr heads fuel useT true with
  | none => rw [hC] at hs; cases hs
  | some C =>
    exact csoundCfgQ src statics eu K fr g guard C.sb C.sa C.tt x px y py (solveCfg_sound hC) hr ha

end DirectedAlias.Impl.Cfg

import DirectedAlias.Impl.CfgSound
import DirectedAlias.Impl.EngineRun

/-!
# The A6 corollary and the engine glue for the CFG certificate

* A6 (exceptions, user decision 2026-11-06: the catch rule stays `{⟨s⟩}`). The A6 CFG `g.a6`
  is `g` with each `throw y` replaced by `nop`; the nodes, the edges, the kills and the entry do
  not change. So a thrown value reaches its handler as an UNKNOWN exception (a fresh object of
  the catch site). Each A6 execution is an execution of `g` (`reach_a6`), and a post-fixpoint
  of `g.a6` with no thrown values (`T = []`) is sound for the A6 semantics (`csoundCfgA6`).
* ENGINE GLUE. `transE` is the engine transfer of a node on the engine state `EState`
  (`astepE` for the statements, the guarded engine store `storeGE`, the kills remove env
  entries, catch and const are the engine join of the unknown step and the set assignment).
  `EPostFix` is an engine post-fixpoint: the engine order is the change test of the engine
  (`ELe F E`: `E` is NF and `mapEqB (joinE E F) E`). `ePostFix_postFix` proves that the
  completed denotation `comp (den (S v))` of an engine post-fixpoint is a post-fixpoint of the
  CFG (`PostFix`, with `T = []`) for a CFG without throw. `csoundEngineCfg`: an engine
  post-fixpoint of the A6 CFG is sound for the A6 semantics, and the answer is the answer of
  `den (S v)` itself (`may_comp`).
-/

namespace DirectedAlias.Impl.Cfg

open DirectedAlias DirectedAlias.Sound DirectedAlias.Sound.Recency DirectedAlias.Sound.Havoc
open DirectedAlias.Sound.HavocRecency DirectedAlias.Sound.CellNamed DirectedAlias.Sound.BlockOnly
open DirectedAlias.Sound.ValueSem DirectedAlias.Opt DirectedAlias.Impl.Engine

/-! ## T1: the A6 CFG -/

/-- The A6 instruction: a `throw` becomes `nop`. -/
def Instr.a6 : Instr → Instr
  | .thr _ => .nop
  | i => i

/-- The A6 node: the instruction is the A6 instruction; the edges and the kills do not change. -/
def Node.a6 (nd : Node) : Node := { nd with instr := nd.instr.a6 }

/-- The A6 CFG: each `throw y` is `nop`; the nodes, the edges and the entry do not change. -/
def Cfg.a6 (g : Cfg) : Cfg := { g with nodes := g.nodes.map Node.a6 }

/-- No node of the CFG is a `throw`. -/
def NoThr (g : Cfg) : Prop := ∀ (v : Nat) (nd : Node) (y : Var), g.nodes[v]? = some nd → nd.instr ≠ .thr y

/-- A node of `g` gives the A6 node of `g.a6` at the same index. -/
theorem a6_node {g : Cfg} {v : Nat} {nd : Node} (h : g.nodes[v]? = some nd) :
    g.a6.nodes[v]? = some nd.a6 := by
  show (g.nodes.map Node.a6)[v]? = _
  rw [List.getElem?_map, h]; rfl

/-- Each node of `g.a6` is the A6 node of the node of `g` at the same index. -/
theorem a6_node_inv {g : Cfg} {v : Nat} {nd' : Node} (h : g.a6.nodes[v]? = some nd') :
    ∃ nd, g.nodes[v]? = some nd ∧ nd' = nd.a6 := by
  change (g.nodes.map Node.a6)[v]? = some nd' at h
  rw [List.getElem?_map] at h
  cases e : g.nodes[v]? with
  | none => rw [e] at h; cases h
  | some nd => rw [e] at h; exact ⟨nd, rfl, (Option.some.inj h).symm⟩

/-- The A6 CFG has no throw. -/
theorem a6_noThr (g : Cfg) : NoThr g.a6 := by
  intro v nd y h
  obtain ⟨nd0, _, rfl⟩ := a6_node_inv h
  show nd0.instr.a6 ≠ _
  cases nd0.instr <;> exact fun e => nomatch e

/-- The A6 instruction has the null statements of the instruction. -/
theorem Instr.a6_nullN (i : Instr) : i.a6.nullN = i.nullN := by
  cases i <;> rfl

/-- The A6 CFG has the null sites of the CFG. -/
theorem a6_nullSite (g : Cfg) (v : Nat) : g.a6.nullSite v = g.nullSite v := by
  unfold Cfg.nullSite
  show (((g.nodes.map Node.a6).take v).map (fun nd => nd.instr.nullN)).sum = _
  rw [← List.map_take, List.map_map]
  congr 1
  apply List.map_congr_left
  intro nd _
  exact Instr.a6_nullN nd.instr

/-- A normal step of an A6 instruction is a normal step of the instruction. -/
theorem istep_of_a6 {src : Nat → Obj × Cell} {statics : List Root} {i : Nat} {ins : Instr}
    {e : Option Obj} {vs vs' : VState} (h : IStep src statics i ins.a6 e vs vs') :
    IStep src statics i ins e vs vs' := by
  cases ins with
  | thr y => cases h; exact .thr
  | _ => exact h

/-- An exceptional step of an A6 instruction is an exceptional step of the instruction (a
`throw` gives an unknown exception). -/
theorem xstep_of_a6 {src : Nat → Obj × Cell} {statics : List Root} {ins : Instr}
    {e : Option Obj} {vs vs' : VState} (h : XStep src statics ins.a6 vs vs' e) :
    XStep src statics ins vs vs' e := by
  cases ins with
  | thr y => cases h; exact .none
  | _ => exact h

/-- EACH A6 EXECUTION IS AN EXECUTION OF THE CFG: the A6 semantics is the semantics of `g` where
each thrown value reaches its handler as an unknown exception. -/
theorem reach_a6 {src : Nat → Obj × Cell} {statics : List Root} {g : Cfg} {fr : Frame}
    {c : Conf} (h : Reach src statics g.a6 fr c) : Reach src statics g fr c := by
  induction h with
  | init => exact .init
  | step _ hs ih =>
    cases hs with
    | norm hn hw hi =>
      obtain ⟨nd, hn0, rfl⟩ := a6_node_inv hn
      rw [a6_nullSite] at hi
      exact .step ih (.norm hn0 hw (istep_of_a6 hi))
    | exc hn hh hx =>
      obtain ⟨nd, hn0, rfl⟩ := a6_node_inv hn
      exact .step ih (.exc hn0 hh (xstep_of_a6 hx))

/-- A post-fixpoint of a CFG without throw needs no throw condition: the conditions without
it give `PostFix` with no thrown values. -/
theorem PostFix.ofNoThr {cb : CtxB} {guard : Origin → Bool} {g : Cfg} {fr : Frame}
    {Sb Sa : Nat → AState} (hnt : NoThr g)
    (supp : ∀ v nd, g.nodes[v]? = some nd → Supp cb.cn.ctx (Sb v))
    (entry : leOn cb.cn.ctx (ainitV cb.cn.ctx.K fr) (Sb g.entry) = true)
    (node : ∀ v nd, g.nodes[v]? = some nd →
      leOn cb.cn.ctx (trans cb guard (fun _ => []) g v nd (Sb v)) (Sa v) = true)
    (succ : ∀ v nd w, g.nodes[v]? = some nd → w ∈ nd.succ → leOn cb.cn.ctx (Sa v) (Sb w) = true)
    (exc : ∀ v nd h, g.nodes[v]? = some nd → h ∈ nd.exc →
      leOn cb.cn.ctx (entryS cb nd (Sb v)) (Sb h) = true)
    (excCall : ∀ v nd h ret s args, g.nodes[v]? = some nd → h ∈ nd.exc →
      nd.instr = .stmt (.call ret s args) →
      leOn cb.cn.ctx (partialS cb nd s args (Sb v)) (Sb h) = true) :
    PostFix cb guard g fr Sb Sa (fun _ => []) :=
  ⟨supp, entry, node, succ, exc, excCall, fun v nd _ y hn _ hi => absurd hi (hnt v nd y hn)⟩

/-- THE A6 COROLLARY (`csoundCfgA6`): a post-fixpoint of the A6 CFG with no thrown values is
sound for the A6 semantics: each reachable configuration has the invariant of design VS. -/
theorem csoundCfgA6 {src : Nat → Obj × Cell} {cb : CtxB} {g : Cfg} {fr : Frame}
    {guard : Origin → Bool} {Sb Sa : Nat → AState} (hok : CfgOK cb g.a6)
    (hpf : PostFix cb guard g.a6 fr Sb Sa (fun _ => [])) (hfr : FrameOK cb.cn.ctx fr)
    {v : Nat} {vs : VState} {e : Option Obj} (hr : Reach src cb.cn.statics g.a6 fr ⟨v, vs, e⟩) :
    InvVS cb vs (Sb v) :=
  csoundCfg hok hpf hfr hr

/-- The query form of the A6 corollary: each value alias of an A6 execution at node `v` is a
may-alias of `Sb v`. -/
theorem csoundCfgA6_may {src : Nat → Obj × Cell} {cb : CtxB} {g : Cfg} {fr : Frame}
    {guard : Origin → Bool} {Sb Sa : Nat → AState} (hok : CfgOK cb g.a6)
    (hpf : PostFix cb guard g.a6 fr Sb Sa (fun _ => [])) (hfr : FrameOK cb.cn.ctx fr)
    {v : Nat} {vs : VState} {e : Option Obj} (hr : Reach src cb.cn.statics g.a6 fr ⟨v, vs, e⟩)
    {x y : Var} {px py : List Cell} (hcx : ∀ c ∈ px, c.abs ∈ cb.cn.ctx.cells)
    (hcy : ∀ c ∈ py, c.abs ∈ cb.cn.ctx.cells) (ha : AliasInV vs x px y py) :
    may (Sb v) x (px.map Cell.abs) y (py.map Cell.abs) = true :=
  csoundCfg_may hok hpf hfr hr hcx hcy ha

/-! ## T2: the engine transfer of a node -/

/-- The engine kills: each variable of `xs` loses its env entry. -/
def killE (xs : List Var) (E : EState) : EState := xs.foldl (fun E x => putV E x []) E

/-- The guarded engine store: strong only if the guard accepts the single target origin and
the engine store is strong. -/
def storeGE (cb : CtxB) (guard : Origin → Bool) (E : EState) (x : Var) (c : ACell)
    (S : List Origin) : EState :=
  match single? (getE E x) with
  | some o => if guard o = true then storeE cb E x c S else weakE cb.cn.ctx.K c S E (getE E x)
  | none => storeE cb E x c S

/-- The engine transfer of an instruction (no thrown values: a catch gives only `⟨s⟩`). -/
def itransE (cb : CtxB) (B : Nat) (guard : Origin → Bool) (i : Nat) : Instr → EState → EState
  | .stmt (.store x f y), E => storeGE cb guard E x (.fld f) (getE E y)
  | .stmt st, E => astepE cb B i st E
  | .nop, E => E
  | .thr _, E => E
  | .cat x s, E => joinE cb.cn.ctx.K (astepE cb B i (.unknown x s) E) (putV E x [])
  | .cnst x s, E =>
    joinE cb.cn.ctx.K (astepE cb B i (.unknown x s) E) (putV E x [.sym (.fresh s) []])

/-- The engine transfer of node `v`: the kills, then the instruction. -/
def transE (cb : CtxB) (B : Nat) (guard : Origin → Bool) (g : Cfg) (v : Nat) (nd : Node)
    (E : EState) : EState :=
  itransE cb B guard (g.nullSite v) nd.instr (killE nd.kills E)

/-- The engine order (the change test of the engine): `F` is below `E` if `E` is NF and the
engine join of `E` with `F` has the map of `E`. -/
def ELe (K : Nat) (F E : EState) : Prop := NF K E ∧ mapEqB (joinE K E F) E = true

/-- No heap entry of the engine state is empty. -/
def NEH (E : EState) : Prop := ∀ p ∈ E.heap, p.2 ≠ []

/-- AN ENGINE POST-FIXPOINT of a CFG with budget `B` and guard `guard`. -/
structure EPostFix (cb : CtxB) (B : Nat) (guard : Origin → Bool) (g : Cfg) (fr : Frame)
    (Sb Sa : Nat → EState) : Prop where
  /-- The state before each node has support, universe heap keys, and no empty heap entry. -/
  ok : ∀ v nd, g.nodes[v]? = some nd →
    Supp cb.cn.ctx (den cb.cn.ctx.K (Sb v)) ∧ HK cb (Sb v) ∧ NEH (Sb v)
  /-- The engine entry state is below the state before the entry node. -/
  entry : ELe cb.cn.ctx.K (initE fr) (Sb g.entry)
  /-- The engine transfer of each node is below the state after it. -/
  node : ∀ v nd, g.nodes[v]? = some nd → ELe cb.cn.ctx.K (transE cb B guard g v nd (Sb v)) (Sa v)
  /-- A normal edge. -/
  succ : ∀ v nd w, g.nodes[v]? = some nd → w ∈ nd.succ → ELe cb.cn.ctx.K (Sa v) (Sb w)
  /-- An exceptional edge: the state after the kills is below the handler state. -/
  exc : ∀ v nd h, g.nodes[v]? = some nd → h ∈ nd.exc →
    ELe cb.cn.ctx.K (killE nd.kills (Sb v)) (Sb h)
  /-- An exceptional edge of a call: the engine partial call is below the handler state. -/
  excCall : ∀ v nd h ret s args, g.nodes[v]? = some nd → h ∈ nd.exc →
    nd.instr = .stmt (.call ret s args) →
    ELe cb.cn.ctx.K (astepE cb B 0 (.call none s args) (killE nd.kills (Sb v))) (Sb h)

/-! ## Lemmas -/

section glue

variable {cb : CtxB}

/-- Two abstract states with the same env and heap are equal. -/
theorem AState.ext' {A B : AState} (h1 : A.env = B.env) (h2 : A.heap = B.heap) : A = B := by
  cases A; cases B; cases h1; cases h2; rfl

/-- The engine order gives inclusion of the denotations. -/
theorem ELe.sub {K : Nat} {F E : EState} (h : ELe K F E) : (den K F).Sub (den K E) :=
  fix_of_mapEqB h.1 h.2

/-- Inclusion gives inclusion on the universe. -/
theorem leOn_of_sub {ctx : Ctx} {X Y : AState} (h : X.Sub Y) : leOn ctx X Y = true :=
  leOn_iff.mpr ⟨fun x _ => h.1 x, fun o _ c _ => h.2 o c⟩

/-- The engine order gives inclusion of the completed denotations on the universe. -/
theorem ELe.leOn (hc : CtxBOK cb) {F E : EState} (h : ELe cb.cn.ctx.K F E) :
    leOn cb.cn.ctx (comp cb (den cb.cn.ctx.K F)) (comp cb (den cb.cn.ctx.K E)) = true :=
  leOn_of_sub (comp_mono hc.xvNe h.sub)

/-- `putV` is `setVar` on the denotation (equality). -/
theorem den_putV_eq (K : Nat) (E : EState) (x : Var) (S : List Origin) :
    den K (putV E x S) = (den K E).setVar x S := by
  refine AState.ext' (funext fun y => ?_) rfl
  show getE (putV E x S) y = fupd (getE E) x S y
  by_cases hy : y = x
  · subst hy; rw [getE_putV_same, fupd_same]
  · rw [getE_putV_ne _ _ hy, fupd_ne _ _ hy]

/-- The engine kills are the abstract kills on the denotation. -/
theorem den_killE (K : Nat) : ∀ (xs : List Var) (E : EState), den K (killE xs E) = killS xs (den K E)
  | [], _ => rfl
  | x :: xs, E => by
    show den K (killE xs (putV E x [])) = killS xs ((den K E).setVar x [])
    rw [den_killE K xs, den_putV_eq]

/-- The engine kills keep the heap. -/
theorem killE_heap : ∀ (xs : List Var) (E : EState), (killE xs E).heap = E.heap
  | [], _ => rfl
  | x :: xs, E => killE_heap xs (putV E x [])

/-- The completion commutes with `setVar` of a variable that is not reserved (equality). -/
theorem comp_setVar_eq (hx : cb.xv ≠ cb.cn.xe) (X : AState) {x : Var} (h1 : x ≠ cb.cn.xe)
    (h2 : x ≠ cb.xv) (S : List Origin) : (comp cb X).setVar x S = comp cb (X.setVar x S) := by
  refine AState.ext' (funext fun y => ?_) rfl
  have hxe : (X.setVar x S).env cb.cn.xe = X.env cb.cn.xe := fupd_ne _ _ (fun e => h1 e.symm)
  have hxv : (X.setVar x S).env cb.xv = X.env cb.xv := fupd_ne _ _ (fun e => h2 e.symm)
  show fupd (comp cb X).env x S y = (comp cb (X.setVar x S)).env y
  by_cases e1 : y = cb.cn.xe
  · subst e1
    rw [fupd_ne _ _ (fun e => h1 e.symm), comp_xe hx, comp_xe hx, hxe]
  · by_cases e2 : y = cb.xv
    · subst e2
      rw [fupd_ne _ _ (fun e => h2 e.symm), comp_xv, comp_xv, hxe, hxv]
    · rw [comp_ne _ e1 e2]
      by_cases e : y = x
      · subst e; rw [fupd_same]; show S = fupd X.env y S y; rw [fupd_same]
      · rw [fupd_ne _ _ e, comp_ne _ e1 e2]; show X.env y = fupd X.env x S y; rw [fupd_ne _ _ e]

/-- The abstract kills of variables that are not reserved commute with the completion. -/
theorem killS_comp (hx : cb.xv ≠ cb.cn.xe) : ∀ (xs : List Var) (X : AState),
    (∀ x ∈ xs, x ≠ cb.cn.xe ∧ x ≠ cb.xv) → killS xs (comp cb X) = comp cb (killS xs X)
  | [], _, _ => rfl
  | x :: xs, X, h => by
    show killS xs ((comp cb X).setVar x []) = comp cb (killS xs (X.setVar x []))
    rw [comp_setVar_eq hx X (h x List.mem_cons_self).1 (h x List.mem_cons_self).2,
      killS_comp hx xs _ (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- Padding is the identity on a state without empty cells. -/
theorem pad_id (K : Nat) {X : AState} (h : NE X) : pad K X = X := by
  refine AState.ext' rfl (funext fun o => funext fun c => ?_)
  show (match X.heap o c with | [] => [childCN K o c] | a :: l => a :: l) = X.heap o c
  cases e : X.heap o c with
  | nil => exact absurd e (h o c)
  | cons a l => rfl

/-- The completed denotation of an engine state without empty heap entries has no empty cell. -/
theorem NE_comp_den (K : Nat) {E : EState} (h : NEH E) : NE (comp cb (den K E)) := by
  intro o c
  show (look E.heap (o, c)).getD (adefaultV K o c) ≠ []
  cases e : look E.heap (o, c) with
  | none => exact fun e => nomatch e
  | some S => exact h _ (look_mem e)

/-- The completion keeps support. -/
theorem supp_comp (hx : cb.xv ≠ cb.cn.xe) {X : AState} (hs : Supp cb.cn.ctx X) :
    Supp cb.cn.ctx (comp cb X) := by
  intro k hk
  cases k with
  | h o c => exact hs (.h o c) hk
  | v x =>
    have hf : ∀ (p : Origin → Bool), cb.cn.ctx.origins.filter p ⊆ cb.cn.ctx.origins :=
      fun _ a ha => (List.mem_filter.mp ha).1
    show (comp cb X).env x ⊆ _
    by_cases e1 : x = cb.xv
    · subst e1; rw [comp_xv]; exact uni_sub (hf _) (hs.env hk)
    · by_cases e2 : x = cb.cn.xe
      · subst e2; rw [comp_xe hx]; exact uni_sub (hf _) (hs.env hk)
      · rw [comp_ne X e2 e1]; exact hs.env hk

/-- The completion commutes with a weak store (equality). -/
theorem comp_weakStore (X : AState) (os : List Origin) (c : ACell) (S : List Origin) :
    (comp cb X).weakStore os c S = comp cb (X.weakStore os c S) := rfl

/-- The engine transfer of a statement other than a store. -/
theorem itransE_stmt {B : Nat} {guard : Origin → Bool} {i : Nat} {st : Stmt}
    (h : ∀ x f y, st ≠ .store x f y) (E : EState) :
    itransE cb B guard i (.stmt st) E = astepE cb B i st E := by
  cases st with
  | store x f y => exact absurd rfl (h x f y)
  | _ => rfl

/-- THE INSTRUCTION BRIDGE: the model transfer of an instruction (no thrown values) on the
completed denotation is `Le` the completion of the engine transfer. -/
theorem itrans_bridge (hc : CtxBOK cb) (B : Nat) (guard : Origin → Bool) (i v : Nat) {E : EState}
    (hs : Supp cb.cn.ctx (den cb.cn.ctx.K E)) (hk : HK cb E) (ins : Instr)
    (hv : ∀ st ∈ ins.prog.stmts, ∀ x ∈ st.vars, x ∈ cb.cn.ctx.vars ∧ x ≠ cb.cn.xe ∧ x ≠ cb.xv) :
    Le cb (itrans cb guard (fun _ => []) i v ins (comp cb (den cb.cn.ctx.K E)))
      (comp cb (den cb.cn.ctx.K (itransE cb B guard i ins E))) := by
  have hx := hc.xvNe
  cases ins with
  | stmt st =>
    have hv1 := hv st List.mem_cons_self
    rcases stmt_store_or st with ⟨x, f, y, rfl⟩ | hne
    · have hx1 := hv1 x List.mem_cons_self
      have hy1 := hv1 y (List.mem_cons_of_mem _ List.mem_cons_self)
      have hS : (comp cb (den cb.cn.ctx.K E)).env y = getE E y := comp_ne _ hy1.2.1 hy1.2.2
      have hX : (comp cb (den cb.cn.ctx.K E)).env x = getE E x := comp_ne _ hx1.2.1 hx1.2.2
      show Le cb (storeG cb guard (comp cb (den cb.cn.ctx.K E)) x (.fld f)
          ((comp cb (den cb.cn.ctx.K E)).env y))
        (comp cb (den cb.cn.ctx.K (storeGE cb guard E x (.fld f) (getE E y))))
      rw [hS]
      have hBO : Le cb (storeBO cb (comp cb (den cb.cn.ctx.K E)) x (.fld f) (getE E y))
          (comp cb (den cb.cn.ctx.K (storeE cb E x (.fld f) (getE E y)))) := by
        rw [comp_storeBO hx _ hx1.2.1 hx1.2.2]
        exact Le.of_deq ((den_storeE cb E x _ _).comp hx).symm
      have hW : Le cb ((comp cb (den cb.cn.ctx.K E)).weakStore (getE E x) (.fld f) (getE E y))
          (comp cb (den cb.cn.ctx.K (weakE cb.cn.ctx.K (.fld f) (getE E y) E (getE E x)))) := by
        rw [comp_weakStore]
        exact Le.of_deq ((den_weakE _ _ _ E _).comp hx).symm
      unfold storeG storeGE
      rw [hX]
      cases single? (getE E x) with
      | none => exact hBO
      | some o =>
        dsimp only
        split
        · exact hBO
        · exact hW
    · rw [itrans_stmt hne, itransE_stmt hne]
      exact bridge hc B i hs hk st hv1
  | nop => exact Le.refl _
  | thr y => exact Le.refl _
  | cat x s =>
    have hx1 := hv (.unknown x s) List.mem_cons_self x List.mem_cons_self
    have h1 := bridge hc B i hs hk (.unknown x s) (hv (.unknown x s) List.mem_cons_self)
    have h2 : Le cb ((comp cb (den cb.cn.ctx.K E)).setVar x [])
        (comp cb (den cb.cn.ctx.K (putV E x []))) := by
      rw [comp_setVar_eq hx _ hx1.2.1 hx1.2.2, den_putV_eq]; exact Le.refl _
    exact (Le.join h1 h2).trans (join_bridge_le hc _ _)
  | cnst x s =>
    have hx1 := hv (.unknown x s) List.mem_cons_self x List.mem_cons_self
    have h1 := bridge hc B i hs hk (.unknown x s) (hv (.unknown x s) List.mem_cons_self)
    have h2 : Le cb ((comp cb (den cb.cn.ctx.K E)).setVar x [.sym (.fresh s) []])
        (comp cb (den cb.cn.ctx.K (putV E x [.sym (.fresh s) []]))) := by
      rw [comp_setVar_eq hx _ hx1.2.1 hx1.2.2, den_putV_eq]; exact Le.refl _
    exact (Le.join h1 h2).trans (join_bridge_le hc _ _)

/-- The variables of the statements of a node that fits are universe variables and are not
reserved. -/
theorem NodeOK.vars {g : Cfg} {v : Nat} {nd : Node} (h : NodeOK cb g v nd) :
    ∀ st ∈ nd.instr.prog.stmts, ∀ x ∈ st.vars, x ∈ cb.cn.ctx.vars ∧ x ≠ cb.cn.xe ∧ x ≠ cb.xv :=
  fun st hs x hx => ⟨(h.instr st hs).vars x hx, (h.instr st hs).noXe x hx, (h.instr st hs).noXv x hx⟩

/-- The entry state of a node on the completed denotation is the completed denotation of the
engine state after the kills. -/
theorem entryS_comp {g : Cfg} {v : Nat} {nd : Node} (hc : CtxBOK cb) (hok : NodeOK cb g v nd)
    {E : EState} (hne : NEH E) :
    entryS cb nd (comp cb (den cb.cn.ctx.K E)) = comp cb (den cb.cn.ctx.K (killE nd.kills E)) := by
  unfold entryS
  rw [pad_id _ (NE_comp_den _ hne), den_killE,
    killS_comp hc.xvNe _ _ (fun x hx => ⟨(hok.kills x hx).2.1, (hok.kills x hx).2.2⟩)]

/-- THE ENGINE POST-FIXPOINT IS A POST-FIXPOINT: for a CFG without throw, the completed
denotations of an engine post-fixpoint form a post-fixpoint of the CFG with no thrown values. -/
theorem ePostFix_postFix {B : Nat} {guard : Origin → Bool} {g : Cfg} {fr : Frame}
    {Sb Sa : Nat → EState} (hok : CfgOK cb g) (hnt : NoThr g)
    (h : EPostFix cb B guard g fr Sb Sa) :
    PostFix cb guard g fr (fun v => comp cb (den cb.cn.ctx.K (Sb v)))
      (fun v => comp cb (den cb.cn.ctx.K (Sa v))) (fun _ => []) := by
  have hc := hok.ctx
  have hx := hc.xvNe
  have hkE : ∀ v nd, g.nodes[v]? = some nd →
      Supp cb.cn.ctx (den cb.cn.ctx.K (killE nd.kills (Sb v))) ∧ HK cb (killE nd.kills (Sb v)) := by
    intro v nd hn
    obtain ⟨h1, h2, _⟩ := h.ok v nd hn
    refine ⟨?_, ?_⟩
    · rw [den_killE]; exact supp_killS _ h1
    · intro k hk; rw [killE_heap] at hk; exact h2 k hk
  refine PostFix.ofNoThr hnt ?_ ?_ ?_ ?_ ?_ ?_
  · intro v nd hn; exact supp_comp hx (h.ok v nd hn).1
  · have h1 := h.entry.sub
    have h0 := den_initE cb.cn.ctx.K fr
    refine leOn_of_sub ⟨fun x a ha => ?_, fun o c a ha => ?_⟩
    · exact (le_comp hx _).sub.1 x (h1.1 x ((h0.1 x a).mpr ha))
    · exact (le_comp hx _).sub.2 o c (h1.2 o c ((h0.2 o c a).mpr ha))
  · intro v nd hn
    have nok := hok.nodes v nd hn
    show leOn cb.cn.ctx (itrans cb guard (fun _ => []) (g.nullSite v) v nd.instr
      (entryS cb nd (comp cb (den cb.cn.ctx.K (Sb v))))) _ = true
    rw [entryS_comp hc nok (h.ok v nd hn).2.2]
    have hb := itrans_bridge hc B guard (g.nullSite v) v (hkE v nd hn).1 (hkE v nd hn).2 nd.instr
      nok.vars
    exact leOn_of_sub (hb.sub.trans (comp_mono hx (h.node v nd hn).sub))
  · intro v nd w hn hw; exact (h.succ v nd w hn hw).leOn hc
  · intro v nd hh hn he
    rw [entryS_comp hc (hok.nodes v nd hn) (h.ok v nd hn).2.2]
    exact (h.exc v nd hh hn he).leOn hc
  · intro v nd hh ret s args hn he hins
    have nok := hok.nodes v nd hn
    unfold partialS
    rw [entryS_comp hc nok (h.ok v nd hn).2.2]
    have hv := nok.vars
    rw [hins] at hv
    have hb := bridge hc B 0 (hkE v nd hn).1 (hkE v nd hn).2 (.call none s args)
      (fun x hx' => hv _ List.mem_cons_self x (List.mem_append_right _ hx'))
    exact leOn_of_sub (hb.sub.trans (comp_mono hx (h.excCall v nd hh ret s args hn he hins).sub))

/-- An engine post-fixpoint of a CFG is an engine post-fixpoint of its A6 CFG (a `throw` and a
`nop` have the same engine transfer). -/
theorem EPostFix.a6 {B : Nat} {guard : Origin → Bool} {g : Cfg} {fr : Frame}
    {Sb Sa : Nat → EState} (h : EPostFix cb B guard g fr Sb Sa) :
    EPostFix cb B guard g.a6 fr Sb Sa := by
  have ht : ∀ v nd E, transE cb B guard g.a6 v nd.a6 E = transE cb B guard g v nd E := by
    intro v nd E
    unfold transE
    rw [a6_nullSite]
    show itransE cb B guard (g.nullSite v) nd.instr.a6 _ = _
    cases nd.instr <;> rfl
  refine ⟨fun v nd' hn => ?_, h.entry, fun v nd' hn => ?_, fun v nd' w hn hw => ?_,
    fun v nd' hh hn he => ?_, fun v nd' hh ret s args hn he hins => ?_⟩
  · obtain ⟨nd, hn0, rfl⟩ := a6_node_inv hn; exact h.ok v nd hn0
  · obtain ⟨nd, hn0, rfl⟩ := a6_node_inv hn; rw [ht]; exact h.node v nd hn0
  · obtain ⟨nd, hn0, rfl⟩ := a6_node_inv hn; exact h.succ v nd w hn0 hw
  · obtain ⟨nd, hn0, rfl⟩ := a6_node_inv hn; exact h.exc v nd hh hn0 he
  · obtain ⟨nd, hn0, rfl⟩ := a6_node_inv hn
    have hins' : nd.instr = .stmt (.call ret s args) := by
      have : nd.instr.a6 = .stmt (.call ret s args) := hins
      revert this; cases nd.instr <;> intro e <;> first | exact e | cases e
    exact h.excCall v nd hh ret s args hn0 he hins'

/-- THE ENGINE CERTIFICATE IS SOUND (`csoundEngineCfg`): for an engine post-fixpoint of the A6
CFG, each value alias of two variables that are not reserved, at a node of an A6 execution, is a
may-alias of the engine state `den (Sb v)` before the node. -/
theorem csoundEngineCfg {src : Nat → Obj × Cell} {B : Nat} {guard : Origin → Bool} {g : Cfg}
    {fr : Frame} {Sb Sa : Nat → EState} (hok : CfgOK cb g.a6)
    (h : EPostFix cb B guard g.a6 fr Sb Sa) (hfr : FrameOK cb.cn.ctx fr)
    {v : Nat} {vs : VState} {e : Option Obj} (hr : Reach src cb.cn.statics g.a6 fr ⟨v, vs, e⟩)
    {x y : Var} {px py : List Cell} (hx1 : x ≠ cb.cn.xe) (hx2 : x ≠ cb.xv) (hy1 : y ≠ cb.cn.xe)
    (hy2 : y ≠ cb.xv) (hcx : ∀ c ∈ px, c.abs ∈ cb.cn.ctx.cells)
    (hcy : ∀ c ∈ py, c.abs ∈ cb.cn.ctx.cells) (ha : AliasInV vs x px y py) :
    may (den cb.cn.ctx.K (Sb v)) x (px.map Cell.abs) y (py.map Cell.abs) = true := by
  have hpf := ePostFix_postFix hok (a6_noThr g) h
  have := csoundCfg_may hok hpf hfr hr hcx hcy ha
  rw [may_comp hok.ctx.xvNe _ hx1 hx2 hy1 hy2] at this
  exact this

/-- The engine certificate of a CFG (with throws) is sound for the A6 semantics of the CFG. -/
theorem csoundEngineCfg' {src : Nat → Obj × Cell} {B : Nat} {guard : Origin → Bool} {g : Cfg}
    {fr : Frame} {Sb Sa : Nat → EState} (hok : CfgOK cb g.a6)
    (h : EPostFix cb B guard g fr Sb Sa) (hfr : FrameOK cb.cn.ctx fr)
    {v : Nat} {vs : VState} {e : Option Obj} (hr : Reach src cb.cn.statics g.a6 fr ⟨v, vs, e⟩)
    {x y : Var} {px py : List Cell} (hx1 : x ≠ cb.cn.xe) (hx2 : x ≠ cb.xv) (hy1 : y ≠ cb.cn.xe)
    (hy2 : y ≠ cb.xv) (hcx : ∀ c ∈ px, c.abs ∈ cb.cn.ctx.cells)
    (hcy : ∀ c ∈ py, c.abs ∈ cb.cn.ctx.cells) (ha : AliasInV vs x px y py) :
    may (den cb.cn.ctx.K (Sb v)) x (px.map Cell.abs) y (py.map Cell.abs) = true :=
  csoundEngineCfg hok h.a6 hfr hr hx1 hx2 hy1 hy2 hcx hcy ha

end glue

end DirectedAlias.Impl.Cfg

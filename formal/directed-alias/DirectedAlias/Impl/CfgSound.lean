import DirectedAlias.Impl.Cfg

/-!
# Post-fixpoint soundness of design VS on a CFG (the engine certificate)

The main theorem is `csoundCfg`: if `(Sb, Sa, T)` is a post-fixpoint of the transfer of design VS
on the CFG (`PostFix`), then each reachable configuration `(v, vs)` has `InvVS cb vs (Sb v)`.
So each value alias at node `v` is a may-alias of `Sb v` (`csoundCfg_may`), and each value alias
after a normal step of `v` is a may-alias of `Sa v` (`csoundCfg_after`). The iteration strategy
that gives the post-fixpoint (worklist, weak topological order, irreducible graphs, inlining) is
irrelevant.

The proof reuses the LOCAL soundness of one statement of design VS (`step_soundVS`). The new
parts are:
* the once budget of a CFG (`CntInv`): a site of exactly one node that is on no cycle runs at
  most once in each execution, and not before its node;
* the padding (no empty cell) and the kills;
* the guarded weak store, `catch` with a pending object, and `const` with reuse;
* the pending exception: the object that a `throw` gives keeps its origin until the `catch`.
-/

namespace DirectedAlias.Impl.Cfg

open DirectedAlias DirectedAlias.Sound DirectedAlias.Sound.Recency DirectedAlias.Sound.Havoc
open DirectedAlias.Sound.HavocRecency DirectedAlias.Sound.CellNamed DirectedAlias.Sound.BlockOnly
open DirectedAlias.Sound.ValueSem DirectedAlias.Opt

variable {src : Nat → Obj × Cell} {cb : CtxB}

/-! ## Graph reachability -/

/-- Reachability is transitive. -/
theorem GReach.trans {g : Cfg} {a b c : Nat} (h1 : GReach g a b) (h2 : GReach g b c) :
    GReach g a c := by
  induction h1 with
  | refl => exact h2
  | step e _ ih => exact .step e (ih h2)

/-- A result of `closeG` contains the start set and is closed under the successors. -/
theorem closeG_spec {g : Cfg} : ∀ {k : Nat} {R0 R : List Nat}, g.closeG k R0 = some R →
    (∀ a ∈ R0, a ∈ R) ∧ ∀ a ∈ R, ∀ b ∈ g.outs a, b ∈ R
  | 0, _, _, h => by cases h
  | k + 1, R0, R, h => by
    simp only [Cfg.closeG] at h
    split at h
    · rename_i hs
      cases h
      exact ⟨fun _ h => h, fun a ha b hb => subB_iff.mp hs b (mem_uniMap.mpr ⟨a, ha, hb⟩)⟩
    · obtain ⟨h1, h2⟩ := closeG_spec h
      exact ⟨fun a ha => h1 a (mem_uni.mpr (Or.inr ha)), h2⟩

/-- A set that is closed under the successors contains each node that its elements reach. -/
theorem closed_reach {g : Cfg} {R : List Nat} (hR : ∀ a ∈ R, ∀ b ∈ g.outs a, b ∈ R)
    {a b : Nat} (h : GReach g a b) (ha : a ∈ R) : b ∈ R := by
  induction h with
  | refl => exact ha
  | step e _ ih => exact ih (hR _ ha _ e)

/-- If the cycle test is false, no successor of the node reaches the node. -/
theorem not_onCycle {g : Cfg} {u : Nat} (h : g.onCycleB u = false) :
    ∀ w, g.Edge u w → ¬ GReach g w u := by
  intro w hw hr
  unfold Cfg.onCycleB at h
  split at h
  · rename_i R hR
    have hu : u ∉ R := of_decide_eq_false h
    obtain ⟨h1, h2⟩ := closeG_spec hR
    exact hu (closed_reach h2 hr (h1 w hw))
  · cases h

/-- A node with a site is a node of the graph. -/
theorem lt_of_siteAt {g : Cfg} {u : Nat} {t : Site} (h : g.siteAt u = some t) :
    u < g.nodes.length := by
  by_cases hlt : u < g.nodes.length
  · exact hlt
  · unfold Cfg.siteAt at h
    rw [List.getElem?_eq_none (Nat.le_of_not_lt hlt)] at h
    cases h

/-- THE ONCE TEST: a once site has exactly one node, and that node is on no cycle. -/
theorem onceB_spec {g : Cfg} {t : Site} (h : g.onceB t = true) :
    ∃ u, g.siteAt u = some t ∧ (∀ u', g.siteAt u' = some t → u' = u) ∧ g.onCycleB u = false := by
  unfold Cfg.onceB at h
  cases hf : (List.range g.nodes.length).filter (fun v => decide (g.siteAt v = some t)) with
  | nil => rw [hf] at h; cases h
  | cons u l =>
    cases l with
    | cons _ _ => rw [hf] at h; cases h
    | nil =>
      rw [hf] at h
      have hu : u ∈ (List.range g.nodes.length).filter (fun v => decide (g.siteAt v = some t)) := by
        rw [hf]; exact List.mem_cons_self
      refine ⟨u, of_decide_eq_true (List.mem_filter.mp hu).2, ?_, ?_⟩
      · intro u' hu'
        have hm : u' ∈ (List.range g.nodes.length).filter (fun v => decide (g.siteAt v = some t)) :=
          List.mem_filter.mpr ⟨List.mem_range.mpr (lt_of_siteAt hu'), decide_eq_true hu'⟩
        rw [hf] at hm
        exact List.mem_singleton.mp hm
      · have h' : (!g.onCycleB u) = true := h
        cases e : g.onCycleB u with
        | false => rfl
        | true => rw [e] at h'; cases h'

/-! ## Counters -/

/-- `setRet` does not change the counters. -/
theorem setRet_cnt (st : CState) (r : Option Var) (v : Val) : (st.setRet r v).cnt = st.cnt := by
  cases r <;> rfl

/-- One instrumented statement step adds one to the counter of its site, or keeps the counter. -/
theorem sstep_cnt {statics : List Root} {i : Nat} {st : Stmt} {vs vs' : VState}
    (h : SStepV src statics i st vs vs') :
    ∀ t, vs'.cs.cnt t = vs.cs.cnt t ∨ (st.site? = some t ∧ vs'.cs.cnt t = vs.cs.cnt t + 1) := by
  have bump : ∀ (c : CState) (s : Site) (t : Site), c.cnt = vs.cs.cnt →
      (c.bump s).cnt t = vs.cs.cnt t ∨ (some s = some t ∧ (c.bump s).cnt t = vs.cs.cnt t + 1) := by
    intro c s t hc
    show fupd c.cnt s (c.cnt s + 1) t = _ ∨ (_ ∧ fupd c.cnt s (c.cnt s + 1) t = _)
    rw [hc]
    by_cases e : t = s
    · subst e; exact Or.inr ⟨rfl, fupd_same _ _ _⟩
    · exact Or.inl (fupd_ne _ _ e)
  intro t
  cases h with
  | new => exact bump _ _ t rfl
  | null => exact Or.inl rfl
  | copy _ => left; rw [setVarV_cs]; rfl
  | load _ => left; rw [setVarV_cs]; rfl
  | store _ _ => left; rw [setCellV_cs]; rfl
  | aload _ _ => left; rw [setVarV_cs]; rfl
  | astore _ _ _ => left; rw [setCellV_cs]; rfl
  | unknown => exact bump _ _ t rfl
  | call _ => exact bump _ _ t (setRet_cnt _ _ _)

/-- The foundation part of a kill. -/
theorem killV_cs (vs : VState) (x : Var) : (killV vs x).cs = vs.cs.setVar x none := rfl

/-- The kills keep the heap, the counters and the null tags of the cells. -/
theorem killAllV_keep : ∀ (xs : List Var) (vs : VState),
    (killAllV xs vs).cs.heap = vs.cs.heap ∧ (killAllV xs vs).cs.cnt = vs.cs.cnt ∧
      (killAllV xs vs).nh = vs.nh ∧ (killAllV xs vs).nc = vs.nc
  | [], _ => ⟨rfl, rfl, rfl, rfl⟩
  | x :: xs, vs => killAllV_keep xs (killV vs x)

/-- The kills keep the counters. -/
theorem killAllV_cnt (xs : List Var) (vs : VState) : (killAllV xs vs).cs.cnt = vs.cs.cnt :=
  (killAllV_keep xs vs).2.1

/-- One normal instruction step adds one to the counter of its site, or keeps the counter. -/
theorem istep_cnt {statics : List Root} {i : Nat} {ins : Instr} {e : Option Obj}
    {vs vs' : VState} (h : IStep src statics i ins e vs vs') :
    ∀ t, vs'.cs.cnt t = vs.cs.cnt t ∨ (ins.site? = some t ∧ vs'.cs.cnt t = vs.cs.cnt t + 1) := by
  intro t
  cases h with
  | stmt h => exact sstep_cnt h t
  | nop => exact Or.inl rfl
  | thr => exact Or.inl rfl
  | catP => exact Or.inl rfl
  | catF h => exact sstep_cnt h t
  | cnstF h => exact sstep_cnt h t
  | cnstR _ => exact Or.inl rfl

/-- One exceptional instruction step adds one to the counter of its site, or keeps the counter. -/
theorem xstep_cnt {statics : List Root} {ins : Instr} {vs vs' : VState} {e : Option Obj}
    (h : XStep src statics ins vs vs' e) :
    ∀ t, vs'.cs.cnt t = vs.cs.cnt t ∨ (ins.site? = some t ∧ vs'.cs.cnt t = vs.cs.cnt t + 1) := by
  intro t
  cases h with
  | none => exact Or.inl rfl
  | thr _ => exact Or.inl rfl
  | call h => exact sstep_cnt h t

/-- The site of a node is the site of its instruction. -/
theorem siteAt_of {g : Cfg} {v : Nat} {nd : Node} (hn : g.nodes[v]? = some nd) :
    g.siteAt v = nd.instr.site? := by
  unfold Cfg.siteAt; rw [hn]; rfl

/-- A node has an edge to each of its normal successors. -/
theorem edge_succ {g : Cfg} {v w : Nat} {nd : Node} (hn : g.nodes[v]? = some nd)
    (hw : w ∈ nd.succ) : g.Edge v w := by
  unfold Cfg.Edge Cfg.outs; rw [hn]; exact List.mem_append.mpr (Or.inl hw)

/-- A node has an edge to each of its handlers. -/
theorem edge_exc {g : Cfg} {v w : Nat} {nd : Node} (hn : g.nodes[v]? = some nd)
    (hw : w ∈ nd.exc) : g.Edge v w := by
  unfold Cfg.Edge Cfg.outs; rw [hn]; exact List.mem_append.mpr (Or.inr hw)

/-- One CFG step follows an edge, and adds one to the counter of the site of the node or keeps
the counter. -/
theorem step_cnt {statics : List Root} {g : Cfg} {c c' : Conf} (h : Step src statics g c c') :
    g.Edge c.node c'.node ∧ ∀ t, c'.vs.cs.cnt t = c.vs.cs.cnt t ∨
      (g.siteAt c.node = some t ∧ c'.vs.cs.cnt t = c.vs.cs.cnt t + 1) := by
  cases h with
  | norm hn hw hi =>
    refine ⟨edge_succ hn hw, fun t => ?_⟩
    rw [siteAt_of hn]
    have := istep_cnt hi t
    rw [killAllV_cnt] at this
    exact this
  | exc hn hw hx =>
    refine ⟨edge_exc hn hw, fun t => ?_⟩
    rw [siteAt_of hn]
    have := xstep_cnt hx t
    rw [killAllV_cnt] at this
    exact this

/-- THE COUNTER INVARIANT: the counter of a once site is at most one, and if it is one, the
configuration does not reach the node of the site. -/
def CntInv (g : Cfg) (c : Conf) : Prop :=
  ∀ t, g.onceB t = true → c.vs.cs.cnt t ≤ 1 ∧
    (c.vs.cs.cnt t = 1 → ∀ u, g.siteAt u = some t → ¬ GReach g c.node u)

/-- The counter invariant holds at the entry. -/
theorem CntInv.init (g : Cfg) (fr : Frame) : CntInv g ⟨g.entry, VState.init fr, none⟩ :=
  fun _ _ => ⟨Nat.zero_le _, fun h => absurd h Nat.zero_ne_one⟩

/-- One CFG step keeps the counter invariant. -/
theorem CntInv.step {statics : List Root} {g : Cfg} {c c' : Conf} (hI : CntInv g c)
    (hs : Step src statics g c c') : CntInv g c' := by
  obtain ⟨hedge, hc⟩ := step_cnt hs
  intro t ht
  obtain ⟨u, _, huniq, hcyc⟩ := onceB_spec ht
  obtain ⟨h1, h2⟩ := hI t ht
  rcases hc t with e | ⟨hsite, e⟩
  · rw [e]; exact ⟨h1, fun h1' u' hu' hr => h2 h1' u' hu' (GReach.step hedge hr)⟩
  · have hv : c.node = u := huniq _ hsite
    have h0 : c.vs.cs.cnt t = 0 := by
      have : ¬ c.vs.cs.cnt t = 1 := fun h => h2 h c.node hsite .refl
      omega
    rw [e, h0]
    refine ⟨Nat.le_refl _, fun _ u' hu' hr => ?_⟩
    have hu'' : u' = u := huniq u' hu'
    rw [hu''] at hr
    rw [hv] at hedge
    exact not_onCycle hcyc _ hedge hr

/-- THE ONCE BUDGET: at a configuration of the counter invariant, a statement whose site is the
site of the node has the budget of design VS. -/
theorem budget_of {g : Cfg} {c : Conf} {st : Stmt} (hon : cb.cn.ctx.once = g.onceB)
    (hI : CntInv g c) (hst : ∀ t, st.site? = some t → g.siteAt c.node = some t)
    {vs : VState} (hcnt : vs.cs.cnt = c.vs.cs.cnt) : Budget cb.cn.ctx (.stmt st) vs.cs := by
  intro t ht
  rw [hon] at ht
  obtain ⟨h1, h2⟩ := hI t ht
  rw [hcnt]
  refine ⟨?_, fun h => nomatch h⟩
  rw [sites_stmt]
  cases hs : st.site? with
  | none => show c.vs.cs.cnt t + List.count t [] ≤ 1; rw [List.count_nil]; exact h1
  | some t' =>
    show c.vs.cs.cnt t + List.count t [t'] ≤ 1
    by_cases e : t' = t
    · subst e
      have hsite := hst t' hs
      have : ¬ c.vs.cs.cnt t' = 1 := fun h => h2 h c.node hsite .refl
      rw [List.count_singleton_self]
      omega
    · have : List.count t [t'] = 0 := by
        rw [List.count_cons, List.count_nil]
        have hb : (t' == t) = false := by
          cases hb : (t' == t) with
          | false => rfl
          | true => exact absurd (beq_iff_eq.mp hb) e
        rw [hb]; rfl
      rw [this]; exact h1

/-! ## Padding and kills -/

/-- The padded state includes the state. -/
theorem sub_pad (K : Nat) (X : AState) : X.Sub (pad K X) := by
  refine ⟨fun _ _ h => h, fun o c a h => ?_⟩
  show a ∈ (match X.heap o c with | [] => [childCN K o c] | b :: l => b :: l)
  cases e : X.heap o c with
  | nil => rw [e] at h; cases h
  | cons b l => rw [e] at h; exact h

/-- The padded state has no empty cell. -/
theorem NE_pad (K : Nat) (X : AState) : NE (pad K X) := by
  intro o c
  show (match X.heap o c with | [] => [childCN K o c] | b :: l => b :: l) ≠ []
  cases X.heap o c with
  | nil => exact fun e => by cases e
  | cons b l => exact fun e => by cases e

/-- Padding keeps support. -/
theorem supp_pad (hc : CtxBOK cb) {X : AState} (hs : Supp cb.cn.ctx X) :
    Supp cb.cn.ctx (pad cb.cn.ctx.K X) := by
  intro k hk
  cases k with
  | v x => exact hs (.v x) hk
  | h o c =>
    have h0 : X.heap o c ⊆ cb.cn.ctx.origins := hs (.h o c) hk
    show (match X.heap o c with | [] => [childCN cb.cn.ctx.K o c] | b :: l => b :: l) ⊆ _
    cases e : X.heap o c with
    | nil =>
      intro a ha
      rw [List.mem_singleton.mp ha]
      exact hc.cn.childIn o hk.1 c hk.2
    | cons b l => rw [e] at h0; exact h0

/-- The abstract kills keep the heap. -/
theorem killS_heap : ∀ (xs : List Var) (X : AState), (killS xs X).heap = X.heap
  | [], _ => rfl
  | x :: xs, X => killS_heap xs (X.setVar x [])

/-- The abstract kills keep no empty cell. -/
theorem NE_killS {X : AState} (h : NE X) (xs : List Var) : NE (killS xs X) := by
  intro o c; rw [killS_heap]; exact h o c

/-- The abstract kills keep support. -/
theorem supp_killS {ctx : Ctx} : ∀ (xs : List Var) {X : AState}, Supp ctx X → Supp ctx (killS xs X)
  | [], _, h => h
  | x :: xs, _, h => supp_killS xs (h.setVar x (fun _ h => nomatch h))

/-- The entry state of a node has no empty cell. -/
theorem NE_entryS (cb : CtxB) (nd : Node) (X : AState) : NE (entryS cb nd X) :=
  NE_killS (NE_pad _ X) _

/-- The entry state of a node has support. -/
theorem supp_entryS (hc : CtxBOK cb) (nd : Node) {X : AState} (hs : Supp cb.cn.ctx X) :
    Supp cb.cn.ctx (entryS cb nd X) :=
  supp_killS _ (supp_pad hc hs)

/-! ## The invariant with a pending exception -/

/-- The pending object has a live universe origin in `P` (the thrown values of the handler). -/
def PendOK (cb : CtxB) (G : GNames) (vs : VState) (P : List Origin) (e : Option Obj) : Prop :=
  ∀ o, e = some o → ¬ Dead cb.cn.ctx.once o ∧ alphaBO cb G vs.cs.cnt o ∈ cb.cn.ctx.origins ∧
    alphaBO cb G vs.cs.cnt o ∈ P ∧ ∀ a n, o = .alloc a n → n < vs.cs.cnt a

/-- The invariant of design VS with the pending exception, for one ghost naming. -/
def InvP (cb : CtxB) (vs : VState) (X : AState) (P : List Origin) (e : Option Obj) : Prop :=
  ∃ G, InvG cb.cn.ctx (alphaBO cb G) vs.cs X ∧ InvXB cb G vs.cs X ∧ CntOKB G vs.cs.cnt ∧
    InvN cb G vs X ∧ PendOK cb G vs P e

/-- The invariant with a pending exception gives the invariant of design VS. -/
theorem InvP.toVS {vs : VState} {X : AState} {P : List Origin} {e : Option Obj}
    (h : InvP cb vs X P e) : InvVS cb vs X :=
  let ⟨G, hg, hx, hn, hN, _⟩ := h
  ⟨G, hg, hx, hn, hN⟩

/-- The invariant of design VS gives the invariant without a pending exception. -/
theorem InvVS.toP {vs : VState} {X : AState} (h : InvVS cb vs X) (P : List Origin) :
    InvP cb vs X P none :=
  let ⟨G, hg, hx, hn, hN⟩ := h
  ⟨G, hg, hx, hn, hN, fun _ e => nomatch e⟩

/-- The invariant with a pending exception is closed upward under state inclusion. -/
theorem InvP.mono {vs : VState} {X Y : AState} {P : List Origin} {e : Option Obj}
    (h : InvP cb vs X P e) (hs : X.Sub Y) : InvP cb vs Y P e :=
  let ⟨G, hg, hx, hn, hN, hp⟩ := h
  ⟨G, hg.mono hs, hx.mono (fun _ ha => hs.1 _ ha) (fun _ ha => hs.1 _ ha), hn, hN.mono hs, hp⟩

/-- The invariant with a pending exception is closed upward under inclusion on the universe. -/
theorem InvP.mono_leOn (hc : CtxBOK cb) {vs : VState} {X Y : AState} {P Q : List Origin}
    {e : Option Obj} (h : InvP cb vs X P e) (hs : leOn cb.cn.ctx X Y = true) (hPQ : P ⊆ Q) :
    InvP cb vs Y Q e :=
  let ⟨G, hg, hx, hn, hN, hp⟩ := h
  ⟨G, hg.mono_leOn hs, hx.mono_leOn hc hs, hn, hN.mono_leOn hs,
    fun o eo => let ⟨a, b, c, d⟩ := hp o eo; ⟨a, b, hPQ c, d⟩⟩

/-- A kill keeps the null facts. -/
theorem InvN.kill {G : GNames} {vs : VState} {X : AState} (h : InvN cb G vs X) (x : Var) :
    InvN cb G (killV vs x) (X.setVar x []) where
  nout y hy := by
    show fupd vs.nv x none y = none
    by_cases e : y = x
    · subst e; exact fupd_same _ _ _
    · rw [fupd_ne _ _ e]; exact h.nout y hy
  nenv y hy he t ht := by
    change fupd vs.cs.env x none y = none at he
    change fupd vs.nv x none y = some t at ht
    show _ ∈ fupd X.env x [] y
    by_cases e : y = x
    · subst e; rw [fupd_same] at ht; cases ht
    · rw [fupd_ne _ _ e] at he ht ⊢; exact h.nenv y hy he t ht
  nenvIn y t he ht := by
    change fupd vs.cs.env x none y = none at he
    change fupd vs.nv x none y = some t at ht
    by_cases e : y = x
    · subst e; rw [fupd_same] at ht; cases ht
    · rw [fupd_ne _ _ e] at he ht; exact h.nenvIn y t he ht
  nheap := h.nheap
  nheapIn := h.nheapIn
  nfresh := h.nfresh

/-- A kill of a universe variable that is not reserved keeps the invariant. -/
theorem InvP.kill {vs : VState} {X : AState} {P : List Origin} {e : Option Obj}
    (h : InvP cb vs X P e) {x : Var} (hx : x ∈ cb.cn.ctx.vars) (hxe : x ≠ cb.cn.xe)
    (hxv : x ≠ cb.xv) : InvP cb (killV vs x) (X.setVar x []) P e :=
  let ⟨G, hg, hx', hn, hN, hp⟩ := h
  ⟨G, InvG.setVar (v := none) hg hx (fun _ e => nomatch e) (fun _ _ e => nomatch e),
    hx'.setVar hxe hxv, hn, InvN.kill hN x, hp⟩

/-- The kills of universe variables that are not reserved keep the invariant. -/
theorem InvP.killAll : ∀ (xs : List Var) {vs : VState} {X : AState} {P : List Origin}
    {e : Option Obj}, (∀ x ∈ xs, x ∈ cb.cn.ctx.vars ∧ x ≠ cb.cn.xe ∧ x ≠ cb.xv) →
    InvP cb vs X P e → InvP cb (killAllV xs vs) (killS xs X) P e
  | [], _, _, _, _, _, h => h
  | x :: xs, _, _, _, _, hx, h =>
    InvP.killAll xs (fun y hy => hx y (List.mem_cons_of_mem _ hy))
      (h.kill (hx x List.mem_cons_self).1 (hx x List.mem_cons_self).2.1
        (hx x List.mem_cons_self).2.2)

/-! ## Instruction steps -/

/-- Setting a universe variable to an object with a live universe origin in `S` keeps the
invariant. -/
theorem setVarObj_sound {G : GNames} {vs : VState} {X : AState} {x : Var} {o : Obj}
    {S : List Origin} (hg : InvG cb.cn.ctx (alphaBO cb G) vs.cs X) (hx : InvXB cb G vs.cs X)
    (hn : CntOKB G vs.cs.cnt) (hN : InvN cb G vs X) (hxv : x ∈ cb.cn.ctx.vars)
    (hxe : x ≠ cb.cn.xe) (hxv' : x ≠ cb.xv)
    (ho : ¬ Dead cb.cn.ctx.once o ∧ alphaBO cb G vs.cs.cnt o ∈ cb.cn.ctx.origins ∧
      alphaBO cb G vs.cs.cnt o ∈ S)
    (hcr : ∀ a n, o = .alloc a n → n < vs.cs.cnt a) :
    InvVS cb (vs.setVarV x (.obj o)) (X.setVar x S) :=
  ⟨G, InvG.setVar hg hxv (fun o' e => by cases e; exact ho) (fun a n e => by cases e; exact hcr a n rfl),
    hx.setVar hxe hxv', hn, hN.setVarV hxv (fun _ e => nomatch e)⟩

/-- THE GUARDED WEAK STORE: a weak store is sound for each store step. -/
theorem weak_soundVS (hc : CtxBOK cb) {i : Nat} {x y : Var} {f : Field} {s s' : VState}
    {X : AState} (hok : StmtOKB cb (.store x f y)) (h : InvVS cb s X)
    (hst : SStepV src cb.cn.statics i (.store x f y) s s') :
    InvVS cb s' (X.weakStore (X.env x) (.fld f) (X.env y)) := by
  obtain ⟨G, hg, hx, hn, hN⟩ := h
  cases hst with
  | @store _ _ _ _ o v he hv =>
    have hyv := hok.vars y (by simp [Stmt.vars])
    have hxv := hok.vars x (by simp [Stmt.vars])
    have e : (s.setCellV o (.fld f) v).cs = s.cs.setCell o (.fld f) (s.cs.env y) := by
      rw [setCellV_cs, val_toVal hv]
    have hd := hg.envOk x o he
    have hxo := hg.env x hxv o he
    have hf : ACell.fld f ∈ cb.cn.ctx.cells := hok.fields f (by simp [Stmt.fields])
    have hocr : ∀ a n, o = .alloc a n → n < s.cs.cnt a := fun a n e => hg.envCr x a n (e ▸ he)
    have hv' : ∀ o', s.cs.env y = some o' → ¬ Dead cb.cn.ctx.once o' ∧
        alphaBO cb G s.cs.cnt o' ∈ cb.cn.ctx.origins ∧ alphaBO cb G s.cs.cnt o' ∈ X.env y :=
      fun o' e => ⟨(hg.envOk y o' e).1, (hg.envOk y o' e).2, hg.env y hyv o' e⟩
    have hvcr : ∀ a n, s.cs.env y = some (.alloc a n) → n < s.cs.cnt a :=
      fun a n e => hg.envCr y a n e
    have hvN : ∀ t, v = .nul t → alphaN cb.cn.ctx.K t ∈ X.env y ∧
        alphaN cb.cn.ctx.K t ∈ cb.cn.ctx.origins := by
      intro t et
      subst et
      obtain ⟨h1, h2⟩ := val_nul hv
      exact ⟨hN.nenv y hyv h1 t h2, hN.nenvIn y t h1 h2⟩
    refine ⟨G, ?_, ?_, ?_, hN.weak (c := .fld f) hxo hvN hocr⟩
    · rw [e]; exact InvG.weak (c := .fld f) hg hd hocr hf hxo hv' hvcr
    · rw [e]; exact InvXB.write (c := .fld f) (v := s.cs.env y) hc hx hd hf rfl rfl
    · rw [e]; exact hn

/-- The statement of an instruction fits the universe. -/
theorem stmt_mem_prog (st : Stmt) : st ∈ (Instr.stmt st).prog.stmts := List.mem_cons_self

/-- A statement other than a store: the transfer of the instruction is the transfer of design VS. -/
theorem itrans_stmt {guard : Origin → Bool} {T : Nat → List Origin} {i v : Nat} {st : Stmt}
    (h : ∀ x f y, st ≠ .store x f y) (X : AState) :
    itrans cb guard T i v (.stmt st) X = astepVS cb i st X := by
  cases st with
  | store x f y => exact absurd rfl (h x f y)
  | _ => rfl

/-- A statement is a store, or it is not a store (a constructive case split). -/
theorem stmt_store_or (st : Stmt) :
    (∃ x f y, st = .store x f y) ∨ ∀ x f y, st ≠ .store x f y := by
  cases st with
  | store x f y => exact Or.inl ⟨x, f, y, rfl⟩
  | _ => exact Or.inr (fun _ _ _ e => nomatch e)

/-- LOCAL SOUNDNESS OF ONE INSTRUCTION: a normal instruction step keeps the invariant of design VS,
for each guard. -/
theorem itrans_sound (hc : CtxBOK cb) {guard : Origin → Bool} {T : Nat → List Origin}
    {i v : Nat} {ins : Instr} {e : Option Obj} {vs vs' : VState} {X : AState}
    (hok : ∀ st ∈ ins.prog.stmts, StmtOKB cb st)
    (hnull : ins.nullN = 1 → nullO i ∈ cb.cn.ctx.origins)
    (hb : ∀ st : Stmt, (∀ t, st.site? = some t → ins.site? = some t) →
      Budget cb.cn.ctx (.stmt st) vs.cs)
    (hs : Supp cb.cn.ctx X) (hne : NE X) (h : InvP cb vs X (T v) e)
    (hst : IStep src cb.cn.statics i ins e vs vs') :
    InvVS cb vs' (itrans cb guard T i v ins X) := by
  cases hst with
  | @stmt st _ _ _ hss =>
    have hok1 := hok st (stmt_mem_prog st)
    have hb1 := hb st (fun t ht => ht)
    rcases stmt_store_or st with ⟨x, f, y, rfl⟩ | hne'
    · show InvVS cb vs' (storeG cb guard X x (.fld f) (X.env y))
      unfold storeG
      split
      · split
        · exact (step_soundVS hc hok1 hnull hb1 hs hne h.toVS hss).2
        · exact weak_soundVS hc hok1 h.toVS hss
      · exact (step_soundVS hc hok1 hnull hb1 hs hne h.toVS hss).2
    · rw [itrans_stmt hne']
      exact (step_soundVS hc hok1 hnull hb1 hs hne h.toVS hss).2
  | nop => exact h.toVS
  | thr => exact h.toVS
  | @catP x s o _ =>
    obtain ⟨G, hg, hx, hn, hN, hp⟩ := h
    have hok1 := hok (.unknown x s) List.mem_cons_self
    have hxv := hok1.vars x (by simp [Stmt.vars])
    obtain ⟨h1, h2, h3, h4⟩ := hp o rfl
    exact (setVarObj_sound hg hx hn hN hxv (hok1.noXe x (by simp [Stmt.vars]))
      (hok1.noXv x (by simp [Stmt.vars])) ⟨h1, h2, h3⟩ h4).mono (sub_join_right _ _)
  | @catF x s _ _ hss =>
    have hok1 := hok (.unknown x s) List.mem_cons_self
    exact (step_soundVS hc hok1 (fun e => absurd e Nat.zero_ne_one) (hb _ (fun t ht => ht)) hs hne
      h.toVS hss).2.mono (sub_join_left _ _)
  | @cnstF x s _ _ _ hss =>
    have hok1 := hok (.unknown x s) List.mem_cons_self
    exact (step_soundVS hc hok1 (fun e => absurd e Nat.zero_ne_one) (hb _ (fun t ht => ht)) hs hne
      h.toVS hss).2.mono (sub_join_left _ _)
  | @cnstR x s _ _ n hn =>
    obtain ⟨G, hg, hx, hn', hN, _⟩ := h
    have hok1 := hok (.unknown x s) List.mem_cons_self
    have hxv := hok1.vars x (by simp [Stmt.vars])
    have hb1 := hb (.unknown x s) (fun t ht => ht)
    have hnd : ¬ Dead cb.cn.ctx.once (.sym (.fresh s n) []) := by
      rintro ⟨ho, _⟩
      have := Budget.stmt_site hb1 rfl ho
      omega
    refine (setVarObj_sound hg hx hn' hN hxv (hok1.noXe x (by simp [Stmt.vars]))
      (hok1.noXv x (by simp [Stmt.vars])) ⟨hnd, ?_, ?_⟩ (fun _ _ e => nomatch e)).mono
      (sub_join_right _ _)
    · rw [alphaBO_fresh]; exact hok1.freshS s rfl
    · rw [alphaBO_fresh]; exact List.mem_singleton.mpr rfl

/-! ## The CFG fits the context -/

/-- A node fits the context: its statements fit the universe, and its null site is a universe
null site. -/
structure NodeOK (cb : CtxB) (g : Cfg) (v : Nat) (nd : Node) : Prop where
  stmts : ∀ st ∈ nd.prog.stmts, StmtOKB cb st
  null : nd.instr.nullN = 1 → nullO (g.nullSite v) ∈ cb.cn.ctx.origins

/-- A CFG fits the context: the context is closed, its once test is the once test of the CFG,
and each node fits. -/
structure CfgOK (cb : CtxB) (g : Cfg) : Prop where
  ctx : CtxBOK cb
  once : cb.cn.ctx.once = g.onceB
  nodes : ∀ v nd, g.nodes[v]? = some nd → NodeOK cb g v nd

/-- The statements of the kills. -/
theorem mem_killProg {x : Var} : ∀ {xs : List Var}, x ∈ xs → Stmt.copy x x ∈ (killProg xs).stmts
  | y :: ys, h => by
    show _ ∈ (Prog.stmt (.copy y y)).stmts ++ (killProg ys).stmts
    rcases List.mem_cons.mp h with e | h
    · subst e; exact List.mem_append.mpr (Or.inl List.mem_cons_self)
    · exact List.mem_append.mpr (Or.inr (mem_killProg h))

/-- The killed variables of a node are universe variables that are not reserved. -/
theorem NodeOK.kills {g : Cfg} {v : Nat} {nd : Node} (h : NodeOK cb g v nd) :
    ∀ x ∈ nd.kills, x ∈ cb.cn.ctx.vars ∧ x ≠ cb.cn.xe ∧ x ≠ cb.xv := by
  intro x hx
  have h1 := h.stmts _ (List.mem_append.mpr (Or.inl (mem_killProg hx)))
  exact ⟨h1.vars x (by simp [Stmt.vars]), h1.noXe x (by simp [Stmt.vars]),
    h1.noXv x (by simp [Stmt.vars])⟩

/-- The statements of the instruction of a node fit the universe. -/
theorem NodeOK.instr {g : Cfg} {v : Nat} {nd : Node} (h : NodeOK cb g v nd) :
    ∀ st ∈ nd.instr.prog.stmts, StmtOKB cb st :=
  fun st hs => h.stmts st (List.mem_append.mpr (Or.inr hs))

/-- The call without its result fits the universe if the call fits. -/
theorem StmtOKB.callNone {ret : Option Var} {s : Site} {args : List Var}
    (h : StmtOKB cb (.call ret s args)) : StmtOKB cb (.call none s args) :=
  ⟨fun v hv => h.vars v (List.mem_append.mpr (Or.inr hv)),
    fun v hv => h.noXe v (List.mem_append.mpr (Or.inr hv)),
    fun v hv => h.noXv v (List.mem_append.mpr (Or.inr hv)), h.fields, h.newS, h.freshS⟩

/-! ## The main theorem -/

/-- The invariant at the entry of a node: the padded state after the kills. -/
theorem inv_entry {g : Cfg} {v : Nat} {nd : Node} (hok : NodeOK cb g v nd)
    {vs : VState} {X : AState} {P : List Origin} {e : Option Obj} (h : InvP cb vs X P e) :
    InvP cb (killAllV nd.kills vs) (entryS cb nd X) P e :=
  (h.mono (sub_pad cb.cn.ctx.K X)).killAll _ hok.kills

/-- THE INVARIANT OF A REACHABLE CONFIGURATION: the invariant of design VS for the state before
the node, with the pending exception in the thrown values of the node, and the counter
invariant. -/
theorem csoundCfg_inv {g : Cfg} {fr : Frame} {guard : Origin → Bool} {Sb Sa : Nat → AState}
    {T : Nat → List Origin} (hok : CfgOK cb g) (hpf : PostFix cb guard g fr Sb Sa T)
    (hfr : FrameOK cb.cn.ctx fr) {c : Conf} (hr : Reach src cb.cn.statics g fr c) :
    InvP cb c.vs (Sb c.node) (T c.node) c.exc ∧ CntInv g c := by
  have hc := hok.ctx
  induction hr with
  | init =>
    exact ⟨InvVS.toP ((inv_initVS hc hfr).mono_leOn hc hpf.entry) _, CntInv.init g fr⟩
  | @step c c' _ hs ih =>
    obtain ⟨hI, hC⟩ := ih
    refine ⟨?_, hC.step hs⟩
    cases hs with
    | @norm v nd w vs vs' e hn hw hi =>
      have nok := hok.nodes v nd hn
      have hsk := supp_entryS hc nd (hpf.supp v nd hn)
      have hIk := inv_entry nok hI
      have hb : ∀ st : Stmt, (∀ t, st.site? = some t → nd.instr.site? = some t) →
          Budget cb.cn.ctx (.stmt st) (killAllV nd.kills vs).cs := by
        intro st hst
        exact budget_of (c := ⟨v, vs, e⟩) hok.once hC
          (fun t ht => by rw [siteAt_of hn]; exact hst t ht) (killAllV_cnt _ _)
      have h1 := itrans_sound (guard := guard) hc nok.instr nok.null hb hsk (NE_entryS cb nd _)
        hIk hi
      exact InvVS.toP ((h1.mono_leOn hc (hpf.node v nd hn)).mono_leOn hc (hpf.succ v nd w hn hw)) _
    | @exc v nd h vs vs' e e' hn hh hx =>
      have nok := hok.nodes v nd hn
      have hsk := supp_entryS hc nd (hpf.supp v nd hn)
      have hIk := inv_entry nok hI
      generalize hins : nd.instr = ins at hx
      cases hx with
      | none => exact InvVS.toP (hIk.toVS.mono_leOn hc (hpf.exc v nd h hn hh)) _
      | @thr y _ o hy =>
        obtain ⟨G, hg, hx, hn', hN, _⟩ := hIk
        have hyv : y ∈ cb.cn.ctx.vars := by
          by_cases hyv : y ∈ cb.cn.ctx.vars
          · exact hyv
          · rw [hg.outside y hyv] at hy; cases hy
        have hT := hpf.excThrow v nd h y hn hh hins
        refine ⟨G, hg.mono_leOn (hpf.exc v nd h hn hh), hx.mono_leOn hc (hpf.exc v nd h hn hh), hn',
          hN.mono_leOn (hpf.exc v nd h hn hh), fun o' eo => ?_⟩
        cases eo
        exact ⟨(hg.envOk y o hy).1, (hg.envOk y o hy).2, hT (hg.env y hyv o hy),
          fun a n e => hg.envCr y a n (e ▸ hy)⟩
      | @call ret s args _ _ hss =>
        have hokc : StmtOKB cb (.call ret s args) := by
          have := nok.instr; rw [hins] at this; exact this _ List.mem_cons_self
        have hb : Budget cb.cn.ctx (.stmt (.call none s args)) (killAllV nd.kills vs).cs :=
          budget_of (c := ⟨v, vs, e⟩) hok.once hC
            (fun t ht => by rw [siteAt_of hn, hins]; exact ht) (killAllV_cnt _ _)
        have h1 := (step_soundVS hc (StmtOKB.callNone hokc) (fun e => absurd e Nat.zero_ne_one) hb hsk
          (NE_entryS cb nd _) hIk.toVS hss).2
        exact InvVS.toP (h1.mono_leOn hc (hpf.excCall v nd h ret s args hn hh hins)) _

/-- SOUNDNESS OF A POST-FIXPOINT (`csoundCfg`): each reachable configuration `(v, vs)` has the
invariant of design VS for the state `Sb v`. -/
theorem csoundCfg {g : Cfg} {fr : Frame} {guard : Origin → Bool} {Sb Sa : Nat → AState}
    {T : Nat → List Origin} (hok : CfgOK cb g) (hpf : PostFix cb guard g fr Sb Sa T)
    (hfr : FrameOK cb.cn.ctx fr) {v : Nat} {vs : VState} {e : Option Obj}
    (hr : Reach src cb.cn.statics g fr ⟨v, vs, e⟩) : InvVS cb vs (Sb v) :=
  (csoundCfg_inv hok hpf hfr hr).1.toVS

/-- Each value alias at a reachable node, on universe cells, is a may-alias of the state
before the node. -/
theorem csoundCfg_may {g : Cfg} {fr : Frame} {guard : Origin → Bool} {Sb Sa : Nat → AState}
    {T : Nat → List Origin} (hok : CfgOK cb g) (hpf : PostFix cb guard g fr Sb Sa T)
    (hfr : FrameOK cb.cn.ctx fr) {v : Nat} {vs : VState} {e : Option Obj}
    (hr : Reach src cb.cn.statics g fr ⟨v, vs, e⟩) {x y : Var} {px py : List Cell}
    (hcx : ∀ c ∈ px, c.abs ∈ cb.cn.ctx.cells) (hcy : ∀ c ∈ py, c.abs ∈ cb.cn.ctx.cells)
    (ha : AliasInV vs x px y py) : may (Sb v) x (px.map Cell.abs) y (py.map Cell.abs) = true :=
  (csoundCfg hok hpf hfr hr).may_of_alias hcx hcy ha

/-- After a normal step of a reachable node, the state has the invariant of design VS for the
state `Sa v` after the node. -/
theorem csoundCfg_after {g : Cfg} {fr : Frame} {guard : Origin → Bool} {Sb Sa : Nat → AState}
    {T : Nat → List Origin} (hok : CfgOK cb g) (hpf : PostFix cb guard g fr Sb Sa T)
    (hfr : FrameOK cb.cn.ctx fr) {v : Nat} {vs vs' : VState} {e : Option Obj} {nd : Node}
    (hr : Reach src cb.cn.statics g fr ⟨v, vs, e⟩) (hn : g.nodes[v]? = some nd)
    (hi : IStep src cb.cn.statics (g.nullSite v) nd.instr e (killAllV nd.kills vs) vs') :
    InvVS cb vs' (Sa v) := by
  have hc := hok.ctx
  obtain ⟨hI, hC⟩ := csoundCfg_inv hok hpf hfr hr
  have nok := hok.nodes v nd hn
  have hb : ∀ st : Stmt, (∀ t, st.site? = some t → nd.instr.site? = some t) →
      Budget cb.cn.ctx (.stmt st) (killAllV nd.kills vs).cs := by
    intro st hst
    exact budget_of (c := ⟨v, vs, e⟩) hok.once hC
      (fun t ht => by rw [siteAt_of hn]; exact hst t ht) (killAllV_cnt _ _)
  have h1 := itrans_sound (guard := guard) hc nok.instr nok.null hb
    (supp_entryS hc nd (hpf.supp v nd hn)) (NE_entryS cb nd _) (inv_entry nok hI) hi
  exact h1.mono_leOn hc (hpf.node v nd hn)

/-- Each value alias after a normal step of a reachable node, on universe cells, is a may-alias
of the state after the node. -/
theorem csoundCfg_may_after {g : Cfg} {fr : Frame} {guard : Origin → Bool}
    {Sb Sa : Nat → AState} {T : Nat → List Origin} (hok : CfgOK cb g)
    (hpf : PostFix cb guard g fr Sb Sa T) (hfr : FrameOK cb.cn.ctx fr) {v : Nat}
    {vs vs' : VState} {e : Option Obj} {nd : Node}
    (hr : Reach src cb.cn.statics g fr ⟨v, vs, e⟩) (hn : g.nodes[v]? = some nd)
    (hi : IStep src cb.cn.statics (g.nullSite v) nd.instr e (killAllV nd.kills vs) vs')
    {x y : Var} {px py : List Cell}
    (hcx : ∀ c ∈ px, c.abs ∈ cb.cn.ctx.cells) (hcy : ∀ c ∈ py, c.abs ∈ cb.cn.ctx.cells)
    (ha : AliasInV vs' x px y py) : may (Sa v) x (px.map Cell.abs) y (py.map Cell.abs) = true :=
  (csoundCfg_after hok hpf hfr hr hn hi).may_of_alias hcx hcy ha

/-! ## The context of a CFG -/

/-- The kills program has no null statement. -/
theorem killProg_nulls : ∀ xs : List Var, (killProg xs).nulls = 0
  | [] => rfl
  | _ :: xs => by
    show 0 + (killProg xs).nulls = 0
    rw [killProg_nulls xs]

/-- The null statements of the program of an instruction. -/
theorem Instr.prog_nulls (ins : Instr) : ins.prog.nulls = ins.nullN := by
  cases ins <;> rfl

/-- The null statements of the program of a node are the null statements of its instruction. -/
theorem Node.prog_nulls (nd : Node) : nd.prog.nulls = nd.instr.nullN := by
  show (killProg nd.kills).nulls + nd.instr.prog.nulls = _
  rw [killProg_nulls, Instr.prog_nulls, Nat.zero_add]

/-- The null statements of the program of a node list. -/
theorem foldr_prog_nulls : ∀ l : List Node,
    (l.foldr (fun nd p => Prog.seq nd.prog p) .skip).nulls = (l.map (fun nd => nd.instr.nullN)).sum
  | [] => rfl
  | nd :: l => by
    show nd.prog.nulls + (l.foldr (fun nd p => Prog.seq nd.prog p) .skip).nulls = _
    rw [foldr_prog_nulls l, Node.prog_nulls, List.map_cons, List.sum_cons]

/-- The statements of a node are statements of the program of a node list that contains it. -/
theorem foldr_prog_stmts {nd : Node} {st : Stmt} (hst : st ∈ nd.prog.stmts) :
    ∀ l : List Node, nd ∈ l → st ∈ (l.foldr (fun nd p => Prog.seq nd.prog p) .skip).stmts
  | a :: l, h => by
    show st ∈ a.prog.stmts ++ (l.foldr (fun nd p => Prog.seq nd.prog p) .skip).stmts
    rcases List.mem_cons.mp h with e | h
    · subst e; exact List.mem_append.mpr (Or.inl hst)
    · exact List.mem_append.mpr (Or.inr (foldr_prog_stmts hst l h))

/-- The sum before an element and the element are at most the sum of the list. -/
theorem take_sum_le {f : Node → Nat} : ∀ (l : List Node) (v : Nat) {nd : Node},
    l[v]? = some nd → ((l.take v).map f).sum + f nd ≤ (l.map f).sum
  | a :: l, 0, nd, h => by
    have : a = nd := by simpa using h
    subst this
    simp
  | a :: l, v + 1, nd, h => by
    have h' : l[v]? = some nd := by simpa using h
    have := take_sum_le (f := f) l v h'
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
    omega

/-- The context of a CFG fits the CFG. -/
theorem cfgCtx_ok (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (g : Cfg)
    (qf : List Field) : CfgOK (cfgCtx eu K statics fr g qf) g where
  ctx := by
    obtain ⟨⟨⟨⟨el, df⟩, no, on⟩, nj, ci, pr, ri, xe⟩, xvIn, xvNe, st⟩ :=
      ctxVS_ok eu K statics fr g.prog qf
    exact ⟨⟨⟨⟨el, df⟩, no, on⟩, nj, ci, pr, ri, xe⟩, xvIn, xvNe, st⟩
  once := rfl
  nodes v nd hn := {
    stmts := fun st hst =>
      let h := ctxVS_stmts eu K statics fr g.prog qf st
        (foldr_prog_stmts hst _ (List.mem_of_getElem? hn))
      ⟨h.vars, h.noXe, h.noXv, h.fields, h.newS, h.freshS⟩
    null := fun h1 => by
      apply ctxVS_nulls eu K statics fr g.prog qf
      have := take_sum_le (f := fun nd => nd.instr.nullN) g.nodes v hn
      show g.nullSite v < g.prog.nulls
      unfold Cfg.prog Cfg.nullSite
      rw [foldr_prog_nulls]
      omega }

/-- The frame fits the context of a CFG. -/
theorem cfgCtx_frame (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (g : Cfg)
    (qf : List Field) : FrameOK (cfgCtx eu K statics fr g qf).cn.ctx fr :=
  let h := ctxVS_frame eu K statics fr g.prog qf
  ⟨h.vars, h.roots⟩

/-- THE CFG SOUNDNESS THEOREM FOR THE QUERY CONTEXT: for each naming, static roots, policy,
depth limit and guard, if `(Sb, Sa, T)` is a post-fixpoint for the context with the query
fields, each value alias at a reachable node `v` is a may-alias of `Sb v`. -/
theorem csoundCfgQ (src : Nat → Obj × Cell) (statics : List Root) (eu : Bool) (K : Nat)
    (fr : Frame) (g : Cfg) (guard : Origin → Bool) (Sb Sa : Nat → AState) (T : Nat → List Origin)
    (x : Var) (px : List Cell) (y : Var) (py : List Cell)
    (hpf : PostFix (cfgCtx eu K statics fr g (afields (px.map Cell.abs) ++ afields (py.map Cell.abs)))
      guard g fr Sb Sa T)
    {v : Nat} {vs : VState} {e : Option Obj} (hr : Reach src statics g fr ⟨v, vs, e⟩)
    (ha : AliasInV vs x px y py) : may (Sb v) x (px.map Cell.abs) y (py.map Cell.abs) = true := by
  let qf := afields (px.map Cell.abs) ++ afields (py.map Cell.abs)
  exact csoundCfg_may (cb := cfgCtx eu K statics fr g qf) (cfgCtx_ok eu K statics fr g qf) hpf
    (cfgCtx_frame eu K statics fr g qf) hr
    (query_cells (cells := g.prog.fields) qf (fun a ha => List.mem_append.mpr (Or.inl ha)))
    (query_cells (cells := g.prog.fields) qf (fun a ha => List.mem_append.mpr (Or.inr ha))) ha

/-- No reachable configuration has a value alias that a post-fixpoint answers false. -/
theorem no_alias_of_postFix (src : Nat → Obj × Cell) (statics : List Root) (eu : Bool) (K : Nat)
    (fr : Frame) (g : Cfg) (guard : Origin → Bool) (Sb Sa : Nat → AState) (T : Nat → List Origin)
    (x : Var) (px : List Cell) (y : Var) (py : List Cell)
    (hpf : PostFix (cfgCtx eu K statics fr g (afields (px.map Cell.abs) ++ afields (py.map Cell.abs)))
      guard g fr Sb Sa T)
    {v : Nat} (hf : may (Sb v) x (px.map Cell.abs) y (py.map Cell.abs) = false) :
    ¬ ∃ vs e, Reach src statics g fr ⟨v, vs, e⟩ ∧ AliasInV vs x px y py := by
  rintro ⟨vs, e, hr, ha⟩
  have := csoundCfgQ src statics eu K fr g guard Sb Sa T x px y py hpf hr ha
  rw [hf] at this; cases this

/-! ## The compact-spec rule for handlers -/

/-- Inclusion on the universe is transitive. -/
theorem leOn_trans {ctx : Ctx} {X Y Z : AState} (h1 : leOn ctx X Y = true)
    (h2 : leOn ctx Y Z = true) : leOn ctx X Z = true := by
  obtain ⟨a1, b1⟩ := leOn_iff.mp h1
  obtain ⟨a2, b2⟩ := leOn_iff.mp h2
  exact leOn_iff.mpr ⟨fun x hx _ h => a2 x hx (a1 x hx h),
    fun o ho c hc _ h => b2 o ho c hc (b1 o ho c hc h)⟩

/-- A state is below its join on the universe. -/
theorem leOn_join_left (ctx : Ctx) (X Y : AState) : leOn ctx X (join X Y) = true :=
  leOn_iff.mpr ⟨fun _ _ _ h => mem_uni.mpr (Or.inl h), fun _ _ _ _ _ h => mem_uni.mpr (Or.inl h)⟩

/-- The renaming of `retire` keeps a set without the most recent origin of the site. -/
theorem renameL_id {s : Site} : ∀ {L : List Origin}, (∀ a ∈ L, a ≠ rNew s) → renameL s L = L
  | [], _ => rfl
  | a :: L, h => by
    show renameO s a :: renameL s L = a :: L
    rw [renameL_id (fun b hb => h b (List.mem_cons_of_mem _ hb))]
    unfold renameO
    rw [ite_eq_right (h a List.mem_cons_self)]

/-- The passive call keeps each variable that is not reserved. -/
theorem callVS_env_ne (cb : CtxB) (X : AState) (args : List Var) {z : Var} (h1 : z ≠ cb.cn.xe)
    (h2 : z ≠ cb.xv) : (callVS cb X args).env z = X.env z := by
  unfold callVS
  split <;>
  · show fupd (fupd X.env cb.cn.xe _) cb.xv _ z = _
    rw [fupd_ne _ _ h2, fupd_ne _ _ h1]

/-- THE COMPACT-SPEC HANDLER RULE GIVES THE CALL CONDITION: if the handler state includes the
join of the entry state and the state after a call node, it includes the partial call, provided
the call site is not an allocation site of the universe. -/
theorem compact_rule_call {guard : Origin → Bool} {T : Nat → List Origin} {g : Cfg} {v : Nat}
    {nd : Node} {ret : Option Var} {s : Site} {args : List Var} {X Y Z : AState}
    (hcall : nd.instr = .stmt (.call ret s args)) (hok : StmtOKB cb (.call ret s args))
    (hs : Supp cb.cn.ctx (entryS cb nd X)) (hnew : rNew s ∉ cb.cn.ctx.origins)
    (hnode : leOn cb.cn.ctx (trans cb guard T g v nd X) Y = true)
    (hjoin : leOn cb.cn.ctx (join (entryS cb nd X) Y) Z = true) :
    leOn cb.cn.ctx (partialS cb nd s args X) Z = true := by
  refine leOn_trans ?_ hjoin
  have ht : trans cb guard T g v nd X =
      (retireV cb.cn.ctx.K s (callVS cb (entryS cb nd X) args)).setRet ret [.sym (.fresh s) []] := by
    unfold trans; rw [hcall, itrans_stmt (st := .call ret s args) (fun _ _ _ e => nomatch e)]; rfl
  rw [ht] at hnode
  obtain ⟨h1, h2⟩ := leOn_iff.mp hnode
  refine leOn_iff.mpr ⟨fun z hz a ha => ?_, fun o ho c hc a ha => ?_⟩
  · change a ∈ (retireV cb.cn.ctx.K s (callVS cb (entryS cb nd X) args)).env z at ha
    cases ret with
    | none => exact mem_uni.mpr (Or.inr (h1 z hz ha))
    | some r =>
      by_cases e : z = r
      · subst e
        have hz1 : z ∈ (Stmt.call (some z) s args).vars := List.mem_cons_self
        change a ∈ renameL s ((callVS cb (entryS cb nd X) args).env z) at ha
        rw [callVS_env_ne cb _ args (hok.noXe z hz1) (hok.noXv z hz1),
          renameL_id (fun b hb eb => hnew (eb ▸ hs.env hz hb))] at ha
        exact mem_uni.mpr (Or.inl ha)
      · have := h1 z hz (a := a)
        change a ∈ fupd (retireV cb.cn.ctx.K s (callVS cb (entryS cb nd X) args)).env r _ z → _ at this
        rw [fupd_ne _ _ e] at this
        exact mem_uni.mpr (Or.inr (this ha))
  · have := h2 o ho c hc (a := a)
    have e : ((retireV cb.cn.ctx.K s (callVS cb (entryS cb nd X) args)).setRet ret
        [.sym (.fresh s) []]).heap = (retireV cb.cn.ctx.K s (callVS cb (entryS cb nd X) args)).heap := by
      cases ret <;> rfl
    rw [e] at this
    exact mem_uni.mpr (Or.inr (this ha))

/-- THE COMPACT-SPEC HANDLER RULE GIVES THE PLAIN EXCEPTIONAL CONDITION: if the handler state
includes the join of the entry state and the state after the node, it includes the entry state. -/
theorem compact_rule_exc {X Y Z : AState} {nd : Node}
    (hjoin : leOn cb.cn.ctx (join (entryS cb nd X) Y) Z = true) :
    leOn cb.cn.ctx (entryS cb nd X) Z = true :=
  leOn_trans (leOn_join_left _ _ _) hjoin

end DirectedAlias.Impl.Cfg

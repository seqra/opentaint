import DirectedAlias.Sound.BlockOnly.Call

/-!
# Soundness of design BO under strict narrow A2

The main theorem is `csoundBO`: for each naming `src`, each list of static roots, each depth
limit and both strong-update policies, each strict narrow one-execution alias is a may-alias
of `mayProgBO` (with recency, `Etree`, `Eval`, and the empty-cell fix of the call).

The proof carries the support invariant `Supp` of the abstract state (each universe key holds
only universe origins) beside the simulation invariant. The call needs it: the name of a
callee object is the first origin of an abstract cell, and that origin must be in the
universe.
-/

namespace DirectedAlias.Sound.BlockOnly

open DirectedAlias DirectedAlias.Sound DirectedAlias.Sound.Recency DirectedAlias.Sound.Havoc
open DirectedAlias.Sound.HavocRecency DirectedAlias.Sound.CellNamed DirectedAlias.Opt
open DirectedAlias.Opt.Rec

variable {src : Nat → Obj × Cell} {cb : CtxB}

/-! ## The call -/

/-- The start set of a call is in the universe. -/
theorem callRoots_sub (hc : CtxBOK cb) {X : AState} (hs : Supp cb.cn.ctx X) {args : List Var}
    (hargs : ∀ a ∈ args, a ∈ cb.cn.ctx.vars) : callRoots cb.cn X args ⊆ cb.cn.ctx.origins := by
  refine uni_sub ?_ ?_
  · intro o ho
    obtain ⟨x, hx, h⟩ := mem_uniMap.mp ho
    exact hs (.v x) (hargs x hx) h
  · intro o ho
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ho
    exact hc.statics r hr

/-- LOCAL SOUNDNESS OF THE CALL OF DESIGN BO: the abstract call `callBO` keeps the generic
invariant and the extra facts for the new ghost naming, for each strict narrow havoc. -/
theorem callBO_sound (hc : CtxBOK cb) {G : GNames} {st : CState} {X : AState}
    {args : List Var} {s : Site} {h' : Heap}
    (hg : InvG cb.cn.ctx (alphaBO cb G) st X) (hx : InvXB cb G st X)
    (hcnt : CntOKB G st.cnt) (hargs : ∀ a ∈ args, a ∈ cb.cn.ctx.vars)
    (hh : HavocN src cb.cn.statics st args s (st.cnt s) h') (hs : Supp cb.cn.ctx X) :
    InvG cb.cn.ctx (alphaBO cb (ghostsAfter cb G src st.cnt h' (callBO cb X args) s (st.cnt s)))
      { st with heap := h' } (callBO cb X args) ∧
    InvXB cb (ghostsAfter cb G src st.cnt h' (callBO cb X args) s (st.cnt s))
      { st with heap := h' } (callBO cb X args) := by
  have hroots := callRoots_sub hc hs hargs
  unfold callBO
  split
  · rename_i R hR
    obtain ⟨h0, hcl⟩ := closeN_spec hR
    have hRU : R ⊆ cb.cn.ctx.origins := Opt.CellNamed.closeN_sub hs hroots hR
    have hVU := Opt.CellNamed.succsN_sub hs R
    have hcov := fun o (hr : ReachN st cb.cn.statics args o) =>
      reach_coverB hc hg hx hargs h0 hcl hr
    have hcovc : ∀ u c, coveredB R u = true → coveredB R (childCN cb.cn.ctx.K u c) = true := by
      intro u c h
      obtain ⟨a, ha, hd⟩ := coveredB_iff.mp h
      exact coveredB_iff.mpr ⟨a, ha, descB_child _ _ hd⟩
    have hVc : ∀ u ∈ cb.cn.ctx.origins, coveredB R u = true → ∀ c ∈ cb.cn.ctx.cells,
        ∀ v ∈ X.heap u c, v ∈ succsN cb.cn X R :=
      fun u hu hcu c hc1 v hv => mem_succsN.mpr ⟨u, hu, hcu, c, hc1, hv⟩
    have hcovS : ∀ u ∈ cb.cn.ctx.origins, coveredB R u = true → ∀ c ∈ cb.cn.ctx.cells,
        ∀ v ∈ X.heap u c, coveredB R v = true :=
      fun u hu hcu c hc1 v hv =>
        coveredB_iff.mpr ⟨v, hcl v (hVc u hu hcu c hc1 v hv), descB_refl v⟩
    have hEc : ∀ u, coveredB R u = true → ∀ c b q, childCN cb.cn.ctx.K u c = .sym b q →
        Origin.sym b q ∈ cb.cn.ctx.origins → expB R (.sym b q) = true := by
      intro u hu c b q e _
      obtain ⟨q0, rfl, rfl⟩ := childCN_sym_inv e
      obtain ⟨a, ha, hd⟩ := coveredB_iff.mp hu
      obtain ⟨p, rfl, hp⟩ := descB_sym_inv hd
      refine expB_of ha ?_ (preB_append hp _)
      have := preB_len hp
      rw [List.length_append]; simp only [List.length_cons, List.length_nil]; omega
    exact ⟨InvG.callW hc hg hx hcnt hh hs hRU hVU hcov hcovc hcovS,
      InvXB.callW hc hg hx hcnt hh hs hRU hVU hcov hcovc hcovS hVc hEc⟩
  · have hEc : ∀ u, (fun _ => true) u = true → ∀ c b q, childCN cb.cn.ctx.K u c = .sym b q →
        Origin.sym b q ∈ cb.cn.ctx.origins → expB cb.cn.ctx.origins (.sym b q) = true := by
      intro u _ c b q e hin
      cases q with
      | nil => exact absurd e (childCN_ne_root _ u c b)
      | cons d ds =>
        exact expB_of (p := []) (hc.cn.rootIn b _ hin) (by simp) (by simp [preB])
    have hVc : ∀ u ∈ cb.cn.ctx.origins, (fun _ => true) u = true → ∀ c ∈ cb.cn.ctx.cells,
        ∀ v ∈ X.heap u c, v ∈ cb.cn.ctx.origins :=
      fun u hu _ c hc1 v hv => hs (.h u c) ⟨hu, hc1⟩ hv
    exact ⟨InvG.callW hc hg hx hcnt hh hs (fun _ h => h) (fun _ h => h) (fun _ _ => rfl)
        (fun _ _ _ => rfl) (fun _ _ _ _ _ _ _ => rfl),
      InvXB.callW hc hg hx hcnt hh hs (fun _ h => h) (fun _ h => h) (fun _ _ => rfl)
        (fun _ _ _ => rfl) (fun _ _ _ _ _ _ _ => rfl) hVc hEc⟩

/-- The counters of the new ghosts are the current counters. -/
theorem ghostLe_after {G : GNames} {cnt : Site → Nat} {h' : Heap} {X' : AState} {s n : Nat}
    (h : GhostLe G cnt) : GhostLe (ghostsAfter cb G src cnt h' X' s n) cnt := by
  intro s' n' k g e t
  rcases ghostsAfter_cases e with ⟨_, _, _, rfl⟩ | eG
  · exact Nat.le_refl _
  · exact h _ _ _ _ eG t

/-! ## The invariant -/

/-- The invariant of design BO is closed upward under state inclusion. -/
theorem InvBO.mono {st : CState} {X Y : AState} (h : InvBO cb st X) (hs : X.Sub Y) :
    InvBO cb st Y :=
  let ⟨G, hg, hx, hn⟩ := h
  ⟨G, hg.mono hs, hx.mono (fun _ ha => hs.1 _ ha) (fun _ ha => hs.1 _ ha), hn⟩

/-- The invariant of design BO is closed upward under inclusion on the universe. -/
theorem InvBO.mono_leOn (hc : CtxBOK cb) {st : CState} {X Y : AState} (h : InvBO cb st X)
    (hs : leOn cb.cn.ctx X Y = true) : InvBO cb st Y :=
  let ⟨G, hg, hx, hn⟩ := h
  ⟨G, hg.mono_leOn hs, hx.mono_leOn hc hs, hn⟩

/-- Each top state simulates each concrete state of the invariant. -/
theorem InvBO.top {st : CState} {X : AState} (h : InvBO cb st X) (W : AState) :
    InvBO cb st (top cb.cn.ctx W) :=
  let ⟨G, hg, hx, hn⟩ := h
  ⟨G, hg.top W, hx.top W, hn⟩

/-- A statement fits the universe of design BO: its variables are in the universe and are not
the reserved variables, its fields are cells, and its sites have their origins. -/
structure StmtOKB (cb : CtxB) (st : Stmt) : Prop where
  vars : ∀ v ∈ st.vars, v ∈ cb.cn.ctx.vars
  noXe : ∀ v ∈ st.vars, v ≠ cb.cn.xe
  noXv : ∀ v ∈ st.vars, v ≠ cb.xv
  fields : ∀ f ∈ st.fields, ACell.fld f ∈ cb.cn.ctx.cells
  newS : ∀ s, st.newSite? = some s → rNew s ∈ cb.cn.ctx.origins
  freshS : ∀ s, st.freshSite? = some s → Origin.sym (.fresh s) [] ∈ cb.cn.ctx.origins

/-! ## Support -/

/-- The recency facts of a closed context of design BO. -/
theorem recOK_of (hc : CtxBOK cb) : RecOK cb.cn.ctx :=
  fun s => ⟨hc.cn.base.newOld s, hc.cn.base.oldNew s⟩

/-- A closed context of design BO is closed under default content. -/
theorem ctxClosed_of (hc : CtxBOK cb) : CtxClosed cb.cn.ctx :=
  ⟨fun o ho c hc1 o' ho' => hc.cn.base.base.dflt o ho c hc1 o' ho', hc.cn.base.base.elem⟩

/-- The store of design BO keeps support. -/
theorem supp_storeBO {X : AState} (hs : Supp cb.cn.ctx X) (x : Var) (c : ACell)
    {S : List Origin} (hS : S ⊆ cb.cn.ctx.origins) : Supp cb.cn.ctx (storeBO cb X x c S) := by
  unfold storeBO
  split
  · split
    · intro k hk
      rw [cval_setCell]
      split
      · exact hS
      · exact hs k hk
    · exact hs.weakStore _ c hS
  · exact hs.weakStore _ c hS

/-- The call of design BO keeps support. -/
theorem supp_callBO (hc : CtxBOK cb) {X : AState} (hs : Supp cb.cn.ctx X) {args : List Var}
    (hargs : ∀ a ∈ args, a ∈ cb.cn.ctx.vars) : Supp cb.cn.ctx (callBO cb X args) := by
  have hroots := callRoots_sub hc hs hargs
  unfold callBO
  split
  · rename_i R hR
    exact supp_callWith hc hs (Opt.CellNamed.closeN_sub hs hroots hR)
      (Opt.CellNamed.succsN_sub hs R)
  · exact supp_callWith hc hs (fun _ h => h) (fun _ h => h)

/-- One statement of design BO keeps support. -/
theorem supp_astepBO (hc : CtxBOK cb) {X : AState} (hs : Supp cb.cn.ctx X) {st : Stmt}
    (ok : StmtOKB cb st) : Supp cb.cn.ctx (astepBO cb st X) := by
  have hr := recOK_of hc
  have cc := ctxClosed_of hc
  have okO : st.newSite? = none → st.freshSite? = none → st.callSite? = none →
      Opt.StmtOK cb.cn.ctx st := by
    intro h1 h2 h3
    refine ⟨ok.vars, ok.fields, ?_, ?_, ?_⟩
    · intro s e; rw [h1] at e; cases e
    · intro s e; rw [h2] at e; cases e
    · intro s e; rw [h3] at e; cases e
  cases st with
  | new x a =>
    exact (supp_retire hr hs a).setVar x
      (by intro o ho; simp at ho; subst ho; exact ok.newS a rfl)
  | unknown x a =>
    exact (supp_retire hr hs a).setVar x
      (by intro o ho; simp at ho; subst ho; exact ok.freshS a rfl)
  | call ret a args =>
    have hargs : ∀ v ∈ args, v ∈ cb.cn.ctx.vars := fun v hv => ok.vars v (by simp [Stmt.vars, hv])
    exact (supp_retire hr (supp_callBO hc hs hargs) a).setRet ret
      (by intro o ho; simp at ho; subst ho; exact ok.freshS a rfl)
  | store x f y =>
    exact supp_storeBO hs x _ (hs.env (ok.vars y (by simp [Stmt.vars])))
  | null x => exact hs.astep cc (okO rfl rfl rfl)
  | copy x y => exact hs.astep cc (okO rfl rfl rfl)
  | load x y f => exact hs.astep cc (okO rfl rfl rfl)
  | aload x y => exact hs.astep cc (okO rfl rfl rfl)
  | astore x y => exact hs.astep cc (okO rfl rfl rfl)

/-- The analysis of design BO keeps support. -/
theorem supp_analyzeBO (hc : CtxBOK cb) :
    ∀ (q : Prog) (X : AState), (∀ st ∈ q.stmts, StmtOKB cb st) → Supp cb.cn.ctx X →
      Supp cb.cn.ctx (analyzeBO cb q X)
  | .skip, _, _, h => h
  | .stmt st, _, ok, h => supp_astepBO hc h (ok st (by simp [Prog.stmts]))
  | .seq p q, X, ok, h =>
    supp_analyzeBO hc q _ (fun st hs => ok st (List.mem_append_right _ hs))
      (supp_analyzeBO hc p X (fun st hs => ok st (List.mem_append_left _ hs)) h)
  | .choice p q, X, ok, h =>
    (supp_analyzeBO hc p X (fun st hs => ok st (List.mem_append_left _ hs)) h).join
      (supp_analyzeBO hc q X (fun st hs => ok st (List.mem_append_right _ hs)) h)
  | .loop p, X, ok, h =>
    Supp.loopIter (fun Y hY => supp_analyzeBO hc p Y ok hY) _ X h

/-! ## One statement -/

/-- Local soundness of design BO: one strict narrow step keeps the invariant. -/
theorem step_soundBO (hc : CtxBOK cb) {st : Stmt} {s s' : CState} {X : AState}
    (hok : StmtOKB cb st) (hb : Budget cb.cn.ctx (.stmt st) s) (hs : Supp cb.cn.ctx X)
    (h : InvBO cb s X) (hst : SStepN src cb.cn.statics st s s') : InvBO cb s' (astepBO cb st X) := by
  obtain ⟨G, hg, hx, hn⟩ := h
  have hbump : ∀ (a : Site) (o : Obj), o ≠ .alloc a (s.cnt a) →
      alphaBO cb G (s.bump a).cnt o = renameO a (alphaBO cb G s.cnt o) :=
    fun a _ ho => alphaBO_bump s hn.2 a ho
  have nx : ∀ v ∈ st.vars, v ≠ cb.cn.xe := hok.noXe
  have nv : ∀ v ∈ st.vars, v ≠ cb.xv := hok.noXv
  cases hst with
  | @new x a =>
    have h1 := InvG.retire hc.cn.base a (hbump a) hg
    refine ⟨G, ?_, (InvXB.retire hc a hn.2 hg hx).setVar (nx x (by simp [Stmt.vars]))
      (nv x (by simp [Stmt.vars])), hn.bump a⟩
    show InvG cb.cn.ctx (alphaBO cb G) ((s.bump a).setVar x (some (.alloc a (s.cnt a))))
      ((retire a X).setVar x [rNew a])
    refine InvG.setVar h1 (hok.vars x (by simp [Stmt.vars])) ?_ ?_
    · intro o e
      cases e
      rw [alphaBO_new]
      refine ⟨?_, hok.newS a rfl, List.mem_singleton.mpr rfl⟩
      rintro ⟨ho, hn⟩
      have := Budget.stmt_site hb rfl ho
      omega
    · intro a' n e
      cases e
      show s.cnt a < fupd s.cnt a (s.cnt a + 1) a
      rw [fupd_same]; exact Nat.lt_succ_self _
  | @null x =>
    exact ⟨G, InvG.setVar hg (hok.vars x (by simp [Stmt.vars])) (fun o e => by cases e)
      (fun _ _ e => by cases e),
      hx.setVar (nx x (by simp [Stmt.vars])) (nv x (by simp [Stmt.vars])), hn⟩
  | @copy x y =>
    refine ⟨G, InvG.setVar hg (hok.vars x (by simp [Stmt.vars])) ?_
      (fun a n e => hg.envCr y a n e),
      hx.setVar (nx x (by simp [Stmt.vars])) (nv x (by simp [Stmt.vars])), hn⟩
    intro o e
    exact ⟨(hg.envOk y o e).1, (hg.envOk y o e).2, hg.env y (hok.vars y (by simp [Stmt.vars])) o e⟩
  | @load x y f _ o he =>
    refine ⟨G, InvG.setVar hg (hok.vars x (by simp [Stmt.vars])) ?_
      (fun a n e => hg.heapCr _ _ a n e),
      hx.setVar (nx x (by simp [Stmt.vars])) (nv x (by simp [Stmt.vars])), hn⟩
    intro o' e
    have hd := hg.envOk y o he
    have hf : (Cell.fld f).abs ∈ cb.cn.ctx.cells := hok.fields f (by simp [Stmt.fields])
    exact ⟨hg.heapLive o _ o' hd.1 e, hg.heapIn o _ o' hd.1 hd.2 hf e,
      mem_aread.mpr ⟨_, hg.env y (hok.vars y (by simp [Stmt.vars])) o he,
        hg.heap o _ o' hd.1 hd.2 hf e⟩⟩
  | @aload x y _ o i he =>
    refine ⟨G, InvG.setVar hg (hok.vars x (by simp [Stmt.vars])) ?_
      (fun a n e => hg.heapCr _ _ a n e),
      hx.setVar (nx x (by simp [Stmt.vars])) (nv x (by simp [Stmt.vars])), hn⟩
    intro o' e
    have hd := hg.envOk y o he
    have hf : (Cell.elem i).abs ∈ cb.cn.ctx.cells := hc.cn.base.base.elem
    exact ⟨hg.heapLive o _ o' hd.1 e, hg.heapIn o _ o' hd.1 hd.2 hf e,
      mem_aread.mpr ⟨_, hg.env y (hok.vars y (by simp [Stmt.vars])) o he,
        hg.heap o _ o' hd.1 hd.2 hf e⟩⟩
  | @store x f y _ o he =>
    have hd := hg.envOk x o he
    have hxo := hg.env x (hok.vars x (by simp [Stmt.vars])) o he
    have hf : ACell.fld f ∈ cb.cn.ctx.cells := hok.fields f (by simp [Stmt.fields])
    have hocr : ∀ a n, o = .alloc a n → n < s.cnt a := fun a n e => hg.envCr x a n (e ▸ he)
    have hv : ∀ o', s.env y = some o' → ¬ Dead cb.cn.ctx.once o' ∧
        alphaBO cb G s.cnt o' ∈ cb.cn.ctx.origins ∧ alphaBO cb G s.cnt o' ∈ X.env y :=
      fun o' e => ⟨(hg.envOk y o' e).1, (hg.envOk y o' e).2,
        hg.env y (hok.vars y (by simp [Stmt.vars])) o' e⟩
    have hvcr : ∀ a n, s.env y = some (.alloc a n) → n < s.cnt a := fun a n e => hg.envCr y a n e
    have hxw := fun (Y : AState) (hE : Y.env cb.cn.xe = X.env cb.cn.xe)
        (hV : Y.env cb.xv = X.env cb.xv) =>
      InvXB.write (Y := Y) (c := .fld f) (v := s.env y) hc hx hd hf hE hV
    show InvBO cb _ (storeBO cb X x (.fld f) (X.env y))
    unfold storeBO
    split
    · rename_i oa hsingle
      have hoa : alphaBO cb G s.cnt o = oa := (single?_spec hsingle).2 _ hxo
      split
      · rename_i hu
        rw [← hoa] at hu ⊢
        exact ⟨G, InvG.strong hg hd hocr hf
          (fun o1 hd1 ha => unique_objBO hx.blocked hd.2 hu hd.1 hd1 ha) hv hvcr,
          hxw _ rfl rfl, hn⟩
      · exact ⟨G, InvG.weak (c := .fld f) hg hd hocr hf hxo hv hvcr, hxw _ rfl rfl, hn⟩
    · exact ⟨G, InvG.weak (c := .fld f) hg hd hocr hf hxo hv hvcr, hxw _ rfl rfl, hn⟩
  | @astore x y _ o i he =>
    have hd := hg.envOk x o he
    have hxo := hg.env x (hok.vars x (by simp [Stmt.vars])) o he
    exact ⟨G, InvG.weak (c := .elem i) hg hd (fun a n e => hg.envCr x a n (e ▸ he))
      hc.cn.base.base.elem hxo
      (fun o' e => ⟨(hg.envOk y o' e).1, (hg.envOk y o' e).2,
        hg.env y (hok.vars y (by simp [Stmt.vars])) o' e⟩) (fun a n e => hg.envCr y a n e),
      InvXB.write (c := .elem i) hc hx hd hc.cn.base.base.elem rfl rfl, hn⟩
  | @unknown x a =>
    have h1 := InvG.retire hc.cn.base a (hbump a) hg
    refine ⟨G, ?_, (InvXB.retire hc a hn.2 hg hx).setVar (nx x (by simp [Stmt.vars]))
      (nv x (by simp [Stmt.vars])), hn.bump a⟩
    show InvG cb.cn.ctx (alphaBO cb G)
      ((s.bump a).setVar x (some (.sym (.fresh a (s.cnt a)) [])))
      ((retire a X).setVar x [.sym (.fresh a) []])
    refine InvG.setVar h1 (hok.vars x (by simp [Stmt.vars])) ?_ (fun _ _ e => by cases e)
    intro o e
    cases e
    rw [alphaBO_fresh]
    refine ⟨?_, hok.freshS a rfl, List.mem_singleton.mpr rfl⟩
    rintro ⟨ho, hn⟩
    have := Budget.stmt_site hb rfl ho
    omega
  | @call ret a args _ h' hh =>
    have hargs : ∀ v ∈ args, v ∈ cb.cn.ctx.vars := fun v hv => hok.vars v (by simp [Stmt.vars, hv])
    obtain ⟨hg1, hx1⟩ := callBO_sound hc hg hx hn hargs hh hs
    have hle1 : GhostLe (ghostsAfter cb G src s.cnt h' (callBO cb X args) a (s.cnt a)) s.cnt :=
      ghostLe_after hn.2
    have h2 := InvG.retire hc.cn.base a
      (fun o ho => alphaBO_bump (cb := cb) { s with heap := h' } hle1 a ho) hg1
    have hx2 := InvXB.retire (st := { s with heap := h' }) hc a hle1 hg1 hx1
    have hn2 : CntOKB (ghostsAfter cb G src s.cnt h' (callBO cb X args) a (s.cnt a))
        ({ s with heap := h' }.bump a).cnt := cnt_afterB hn
    show InvBO cb _ ((retire a (callBO cb X args)).setRet ret [.sym (.fresh a) []])
    cases ret with
    | none => exact ⟨_, h2, hx2, hn2⟩
    | some x =>
      refine ⟨_, ?_, hx2.setVar (nx x (by simp [Stmt.vars])) (nv x (by simp [Stmt.vars])), hn2⟩
      show InvG cb.cn.ctx _
        (({ s with heap := h' }.bump a).setVar x (some (.sym (.fresh a (s.cnt a)) [])))
        ((retire a (callBO cb X args)).setVar x [.sym (.fresh a) []])
      refine InvG.setVar h2 (hok.vars x (by simp [Stmt.vars])) ?_ (fun _ _ e => by cases e)
      intro o e
      cases e
      rw [alphaBO_fresh]
      refine ⟨?_, hok.freshS a rfl, List.mem_singleton.mpr rfl⟩
      rintro ⟨ho, hn⟩
      have := Budget.stmt_site hb rfl ho
      omega

/-! ## Programs -/

/-- A loop keeps an invariant state `Y` of design BO if one narrow run of the body keeps it. -/
theorem loop_keepsBO {body : Prog} {Y : AState} (P : CState → Prop)
    (hstep : ∀ s t, P s → InvBO cb s Y → ExecN src cb.cn.statics body s t → P t ∧ InvBO cb t Y) :
    ∀ {s u : CState}, ExecN src cb.cn.statics (.loop body) s u → P s → InvBO cb s Y →
      InvBO cb u Y := by
  intro s u hx
  generalize hq : Prog.loop body = q at hx
  induction hx with
  | skip => intro _ h; exact h
  | stmt _ => cases hq
  | seq _ _ _ _ => cases hq
  | choiceL _ _ => cases hq
  | choiceR _ _ => cases hq
  | loopZero => intro _ h; exact h
  | loopMore h1 _ _ ih2 =>
    cases hq
    intro hp hi
    obtain ⟨hp', hi'⟩ := hstep _ _ hp hi h1
    exact ih2 rfl hp' hi'

/-- Soundness of `analyzeBO`: each strict narrow execution ends in a state that the analysis
result simulates. -/
theorem analyze_soundBO (hc : CtxBOK cb) :
    ∀ (q : Prog) {s s' : CState} {X : AState}, (∀ st ∈ q.stmts, StmtOKB cb st) →
      Budget cb.cn.ctx q s → Supp cb.cn.ctx X → InvBO cb s X → ExecN src cb.cn.statics q s s' →
      InvBO cb s' (analyzeBO cb q X) := by
  intro q
  induction q with
  | skip => intro s s' X _ _ _ h hx; cases hx; exact h
  | stmt st =>
    intro s s' X hok hb hs h hx
    cases hx with
    | stmt hst => exact step_soundBO hc (hok st (List.mem_singleton.mpr rfl)) hb hs h hst
  | seq p q ihp ihq =>
    intro s s' X hok hb hs h hx
    cases hx with
    | seq h1 h2 =>
      have hokp : ∀ st ∈ p.stmts, StmtOKB cb st :=
        fun st hs => hok st (List.mem_append.mpr (Or.inl hs))
      have hokq : ∀ st ∈ q.stmts, StmtOKB cb st :=
        fun st hs => hok st (List.mem_append.mpr (Or.inr hs))
      exact ihq hokq (Budget.seqR hb h1.toExec) (supp_analyzeBO hc p X hokp hs)
        (ihp hokp (Budget.seqL hb) hs h h1) h2
  | choice p q ihp ihq =>
    intro s s' X hok hb hs h hx
    have hokp : ∀ st ∈ p.stmts, StmtOKB cb st :=
      fun st hs => hok st (List.mem_append.mpr (Or.inl hs))
    have hokq : ∀ st ∈ q.stmts, StmtOKB cb st :=
      fun st hs => hok st (List.mem_append.mpr (Or.inr hs))
    cases hx with
    | choiceL h1 => exact (ihp hokp (Budget.choiceL hb) hs h h1).mono (sub_join_left _ _)
    | choiceR h1 => exact (ihq hokq (Budget.choiceR hb) hs h h1).mono (sub_join_right _ _)
  | loop body ih =>
    intro s s' X hok hb hs h hx
    show InvBO cb s' (loopIter cb.cn.ctx (analyzeBO cb body) cb.cn.ctx.fuel X)
    have hsY := Supp.loopIter (fun Y hY => supp_analyzeBO hc body Y hok hY) cb.cn.ctx.fuel X hs
    have hY := h.mono (sub_loopIter cb.cn.ctx (analyzeBO cb body) cb.cn.ctx.fuel X)
    refine loop_keepsBO (Budget cb.cn.ctx (.loop body)) ?_ hx hb hY
    intro s1 t hb1 hi1 hx1
    refine ⟨Budget.again hb1 hx1.toExec, ?_⟩
    have hf := ih hok (Budget.body hb1) hsY hi1 hx1
    rcases loopIter_post cb.cn.ctx (analyzeBO cb body) cb.cn.ctx.fuel X with hpost | ⟨W, hW⟩
    · exact hf.mono_leOn hc hpost
    · rw [hW]; exact hf.top W

/-- The entry states satisfy the invariant of design BO, with the empty ghost naming. -/
theorem inv_initBO (hc : CtxBOK cb) {fr : Frame} (hf : FrameOK cb.cn.ctx fr) :
    InvBO cb (CState.init fr) (ainit cb.cn.ctx.K fr) := by
  let G0 : GNames := fun _ _ _ => none
  have hG0 : ∀ (o : Obj), ∀ s n k p, o = .sym (.havoc s n k) p → G0 s n k = none :=
    fun _ _ _ _ _ _ => rfl
  have hna : ∀ cnt (o : Obj) c o', cdefault o c = some o' →
      ∀ x, alphaBO cb G0 cnt o ≠ .alloc x := by
    intro cnt o c o' h x e
    cases o with
    | alloc _ _ => cases h
    | sym b p =>
      cases b with
      | root r => simp only [alphaBO, alpha, symOrDeep] at e; split at e <;> cases e
      | fresh s n => simp only [alphaBO, alpha, symOrDeep] at e; split at e <;> cases e
      | havoc s n k => rw [alphaBO_none _ rfl] at e; cases e
  have hdm : ∀ cnt (o : Obj) c o', cdefault o c = some o' →
      alphaBO cb G0 cnt o' ∈ adefault cb.cn.ctx.K (alphaBO cb G0 cnt o) c.abs := by
    intro cnt o c o' h
    rw [alphaBO_cdefault_plain cnt (hG0 o) h, adefault_childCN _ (hna cnt o c o' h)]
    exact List.mem_singleton.mpr rfl
  refine ⟨G0, ?_, ?_, ⟨(fun _ _ _ _ e => by cases e), (fun _ _ _ _ e => by cases e)⟩⟩
  · exact {
      outside := fun x hx => by
        show (fr.root? x).map _ = none
        cases e : fr.root? x with
        | none => rfl
        | some r => exact absurd (hf.vars x (lookup_mem e).1) hx
      envOk := fun x o he => by
        change (fr.root? x).map _ = some o at he
        cases e : fr.root? x with
        | none => rw [e] at he; cases he
        | some r =>
          rw [e] at he; cases he
          refine ⟨by simp [Dead], ?_⟩
          rw [alphaBO_root]
          exact hf.roots x r e
      heapLive := fun o c o' hd hh => by
        change cdefault o c = some o' at hh
        cases o with
        | alloc s n => cases hh
        | sym b p => cases hh; cases b <;> simp_all [Dead]
      heapIn := fun o c o' _ hin hc1 hh => by
        change cdefault o c = some o' at hh
        exact hc.cn.base.base.dflt _ hin _ hc1 _ (hdm _ o c o' hh)
      allocHeld := fun o c s n hh => by
        change cdefault o c = some (.alloc s n) at hh
        cases o with
        | alloc _ _ => cases hh
        | sym _ _ => cases hh
      envCr := fun x s n he => by
        change (fr.root? x).map _ = _ at he
        cases e : fr.root? x with
        | none => rw [e] at he; cases he
        | some r => rw [e] at he; cases he
      heapCr := fun o c s n he => by
        change cdefault o c = _ at he
        cases o with
        | sym _ _ => cases he
        | alloc _ _ => cases he
      fresh := fun _ _ _ _ => rfl
      env := fun x _ o he => by
        change (fr.root? x).map _ = some o at he
        show alphaBO cb G0 (CState.init fr).cnt o ∈ (match fr.root? x with
          | some r => [Origin.sym (.root r) []] | none => [])
        cases e : fr.root? x with
        | none => rw [e] at he; cases he
        | some r =>
          rw [e] at he; cases he
          rw [alphaBO_root]
          exact List.mem_singleton.mpr rfl
      heap := fun o c o' _ _ _ hh => by
        change cdefault o c = some o' at hh
        exact hdm _ o c o' hh }
  · exact {
      junkDflt := fun _ _ _ => rfl
      deadDflt := fun _ _ _ => rfl
      outside := fun o c o' _ hh => Or.inr (alphaBO_cdefault_plain _ (hG0 o) hh)
      ghosts := fun _ _ _ _ e => by cases e
      blocked := fun s n k p hin => by
        rw [alphaBO_none _ rfl] at hin
        exact absurd hin (hc.cn.noJunk s) }

/-! ## The context of a program -/

/-- The context of design BO of a program is closed. -/
theorem ctxBO_ok (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (qf : List Field) : CtxBOK (ctxBO eu K statics fr p qf) := by
  obtain ⟨⟨⟨el, df⟩, no, on⟩, nj, ci, pr, ri, _⟩ := ctxCN_ok eu K statics fr p qf
  exact ⟨⟨⟨⟨el, df⟩, no, on⟩, nj, ci, pr, ri, List.mem_cons_self⟩,
    List.mem_cons_of_mem _ List.mem_cons_self, Nat.succ_ne_self _,
    Opt.CellNamed.statics_CN eu K statics fr p qf⟩

/-- The frame fits the context of design BO of a program. -/
theorem ctxBO_frame (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (qf : List Field) : FrameOK (ctxBO eu K statics fr p qf).cn.ctx fr where
  vars _ hx :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_eraseDups.mpr (List.mem_append.mpr (Or.inr hx))))
  roots x r he := (ctxCN_frame eu K statics fr p qf).roots x r he

/-- Each statement of a program fits the context of design BO of the program. -/
theorem ctxBO_stmts (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (qf : List Field) : ∀ st ∈ p.stmts, StmtOKB (ctxBO eu K statics fr p qf) st := by
  intro st hst
  have h0 := ctxCN_stmts eu K statics fr p qf st hst
  have hpv : ∀ v ∈ st.vars, v ∈ progVars fr p := fun v hv =>
    List.mem_eraseDups.mpr (List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr ⟨st, hst, hv⟩)))
  refine ⟨fun v hv => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hpv v hv)), ?_, ?_,
    h0.fields, h0.newS, h0.freshS⟩
  · intro v hv e
    have := lt_freshVar (hpv v hv)
    have e' : v = freshVar (progVars fr p) := e
    rw [e'] at this
    exact Nat.lt_irrefl _ this
  · intro v hv e
    have := lt_freshVar (hpv v hv)
    have e' : v = freshVar (progVars fr p) + 1 := e
    rw [e'] at this
    exact Nat.lt_irrefl _ (Nat.lt_trans (Nat.lt_succ_self _) this)

/-- The once budget of a program holds at the entry state for the context of design BO. -/
theorem ctxBO_budget (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (qf : List Field) : Budget (ctxBO eu K statics fr p qf).cn.ctx p (CState.init fr) :=
  ctxCN_budget eu K statics fr p qf

/-- The entry state has support in the context of design BO. -/
theorem supp_ainitBO (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (qf : List Field) : Supp (ctxBO eu K statics fr p qf).cn.ctx (ainit K fr) := by
  intro k hk
  cases k with
  | v x =>
    intro o ho
    change o ∈ (match fr.root? x with | some r => [Origin.sym (.root r) []] | none => []) at ho
    cases e : fr.root? x with
    | none => rw [e] at ho; cases ho
    | some r =>
      rw [e, List.mem_singleton] at ho
      subst ho
      exact (ctxBO_frame eu K statics fr p qf).roots x r e
  | h o c => exact (ctxClosed_of (ctxBO_ok eu K statics fr p qf)).dflt o hk.1 c hk.2

/-! ## Soundness -/

/-- SOUNDNESS OF DESIGN BO under strict narrow A2, for each naming `src`, each list of static
roots, each depth limit and both strong-update policies: each strict narrow one-execution
alias is a may-alias of `mayProgBO`. -/
theorem csoundBO (src : Nat → Obj × Cell) (statics : List Root) (eu : Bool) (K : Nat)
    (fr : Frame) (p : Prog) (x : Var) (px : List Cell) (y : Var) (py : List Cell)
    (h : CAliasN src statics fr p x px y py) :
    mayProgBO eu K statics fr p x (px.map Cell.abs) y (py.map Cell.abs) = true := by
  obtain ⟨st, hx, o, h1, h2⟩ := h
  let qf := afields (px.map Cell.abs) ++ afields (py.map Cell.abs)
  obtain ⟨G, hinv, _, _⟩ := analyze_soundBO (src := src) (ctxBO_ok eu K statics fr p qf) p
    (ctxBO_stmts eu K statics fr p qf) (ctxBO_budget eu K statics fr p qf)
    (supp_ainitBO eu K statics fr p qf)
    (inv_initBO (ctxBO_ok eu K statics fr p qf) (ctxBO_frame eu K statics fr p qf)) hx
  have hcx := query_cells (cells := p.fields) qf (fun a ha => List.mem_append.mpr (Or.inl ha))
  have hcy := query_cells (cells := p.fields) qf (fun a ha => List.mem_append.mpr (Or.inr ha))
  exact may_iff.mpr ⟨_, hinv.evalPath_sound hcx h1, hinv.evalPath_sound hcy h2⟩

/-- Under strict narrow A2, no execution aliases two paths for which `mayProgBO` answers
false. -/
theorem no_alias_of_mayProgBO (src : Nat → Obj × Cell) (statics : List Root) (eu : Bool)
    (K : Nat) (fr : Frame) (p : Prog) (x : Var) (px : List Cell) (y : Var) (py : List Cell)
    (h : mayProgBO eu K statics fr p x (px.map Cell.abs) y (py.map Cell.abs) = false) :
    ¬ CAliasN src statics fr p x px y py := by
  intro ha
  have := csoundBO src statics eu K fr p x px y py ha
  rw [h] at this; cases this

/-! ## Default content in `Eval` -/

/-- INCLUDING DEFAULT CONTENT IN `Eval` COSTS NO STRONG UPDATE: an origin of the default content
of a cell of an origin that `R` covers is already not unique by the prefix rule, for each
`Etree` that contains `R`. So adding it to `Eval` changes no uniqueness answer. -/
theorem eval_default_free (K : Nat) (once : Site → Bool) (eu : Bool) {R E V : List Origin}
    (hRE : ∀ r ∈ R, r ∈ E) {u : Origin} (hu : coveredB R u = true) {c : ACell} {a : Origin}
    (ha : a ∈ adefault K u c) (o : Origin) :
    uniqueBO once eu E (a :: V) o = uniqueBO once eu E V o := by
  have hna : ∀ x, u ≠ .alloc x := by
    intro x e; subst e; simp [adefault] at ha
  rw [adefault_childCN K hna, List.mem_singleton] at ha
  subst ha
  have hblk : uniqueCN once eu E (childCN K u c) = false := by
    unfold uniqueCN
    cases h : uniqueR once eu (childCN K u c) with
    | false => rfl
    | true =>
      rcases uniqueR_shape h with ⟨b, q, e⟩ | ⟨x, e⟩
      · rw [e]
        obtain ⟨q0, rfl, rfl⟩ := childCN_sym_inv e
        obtain ⟨r, hr, hd⟩ := coveredB_iff.mp hu
        obtain ⟨p, rfl, hp⟩ := descB_sym_inv hd
        have hx : expB E (.sym b (q0 ++ [c])) = true := by
          refine expB_of (hRE _ hr) ?_ (preB_append hp _)
          have := preB_len hp
          rw [List.length_append]; simp only [List.length_cons, List.length_nil]; omega
        rw [hx]; rfl
      · exact absurd e (childCN_ne_alloc K u c x)
  by_cases e : o = childCN K u c
  · subst e
    unfold uniqueBO
    rw [hblk]; rfl
  · unfold uniqueBO
    have : decide (o ∈ childCN K u c :: V) = decide (o ∈ V) := by
      by_cases h : o ∈ V
      · rw [decide_eq_true h, decide_eq_true (List.mem_cons_of_mem _ h)]
      · rw [decide_eq_false h, decide_eq_false (fun h' => by
          rcases List.mem_cons.mp h' with h1 | h1
          · exact e h1
          · exact h h1)]
    rw [this]

end DirectedAlias.Sound.BlockOnly

import DirectedAlias.Sound.ValueSem.Inv

/-!
# Soundness of design VS (value semantics, passive calls)

The main theorem is `csoundVS`: for each naming `src`, each list of static roots, each depth
limit `K` and both strong-update policies, each one-execution VALUE alias of the instrumented
strict narrow semantics (`CAliasV`: the same object, or the same null instance) is a may-alias
of `mayProgVS`.

The proof reuses design BO. Without empty cells (`NE`), the passive call of design VS is the
call of design BO (`callBO_eq`), so `callBO_sound` gives the generic invariant and the blocked
facts for the ghost naming after the call. The new facts are:
* the null instances (`InvN`): a default null has the cell name, a null of site `i` has
  `null(i)`; a callee writes only objects, so a null cell after a call is a null cell before it
  (`InvN.call`);
* no empty cell (`NE`): the entry state and `retireV` give each cell a name, and a strong store
  writes the set of an ASSIGNED variable, which holds the origin of its value (an object or a
  null instance), so the set is not empty.
-/

namespace DirectedAlias.Sound.ValueSem

open DirectedAlias DirectedAlias.Sound DirectedAlias.Sound.Recency DirectedAlias.Sound.Havoc
open DirectedAlias.Sound.HavocRecency DirectedAlias.Sound.CellNamed DirectedAlias.Sound.BlockOnly
open DirectedAlias.Opt DirectedAlias.Opt.Rec

variable {src : Nat → Obj × Cell} {cb : CtxB}

/-! ## Values -/

/-- A variable with an object value holds the object. -/
theorem val_obj {vs : VState} {y : Var} {o : Obj} (h : vs.val y = some (.obj o)) :
    vs.cs.env y = some o := by
  have := val_toVal h; exact this.symm

/-- A variable with a null value holds null and has the tag. -/
theorem val_nul {vs : VState} {y : Var} {t : NTag} (h : vs.val y = some (.nul t)) :
    vs.cs.env y = none ∧ vs.nv y = some t := by
  unfold VState.val at h
  cases e : vs.cs.env y with
  | some o => rw [e] at h; cases h
  | none =>
    rw [e] at h
    cases e2 : vs.nv y with
    | none => rw [e2] at h; cases h
    | some t0 => rw [e2] at h; cases h; exact ⟨rfl, rfl⟩

/-- A cell with a null value holds null and has the tag. -/
theorem cell_nul {vs : VState} {o : Obj} {c : Cell} {t : NTag} (h : vs.cell o c = .nul t) :
    vs.cs.heap o c = none ∧ vs.nh o c = t := by
  unfold VState.cell at h
  cases e : vs.cs.heap o c with
  | some o' => rw [e] at h; cases h
  | none => rw [e] at h; cases h; exact ⟨rfl, rfl⟩

/-- The null facts depend only on the foundation state and the null tags. -/
theorem InvN.congr {G : GNames} {vs vs' : VState} {X : AState} (h : InvN cb G vs X)
    (hc : vs'.cs = vs.cs) (hv : vs'.nv = vs.nv) (hh : vs'.nh = vs.nh) : InvN cb G vs' X := by
  obtain ⟨a, b, c, d, e, f⟩ := h
  exact ⟨by rw [hv]; exact a, by rw [hc, hv]; exact b, by rw [hc, hv]; exact c,
    by rw [hc, hh]; exact d, by rw [hc, hh]; exact e, by rw [hc, hh]; exact f⟩

/-- The value of an assigned universe variable has its origin in the abstract set; so the set is
not empty. -/
theorem val_in {G : GNames} {vs : VState} {X : AState}
    (hg : InvG cb.cn.ctx (alphaBO cb G) vs.cs X) (hN : InvN cb G vs X) {y : Var}
    (hy : y ∈ cb.cn.ctx.vars) {v : VVal} (hv : vs.val y = some v) : X.env y ≠ [] := by
  cases v with
  | obj o => exact ne_nil_of_mem (hg.env y hy o (val_obj hv))
  | nul t =>
    obtain ⟨h1, h2⟩ := val_nul hv
    exact ne_nil_of_mem (hN.nenv y hy h1 t h2)

/-! ## The context -/

/-- Membership in the null origins. -/
theorem mem_nullKids {K n : Nat} {cells : List ACell} {o : Origin} :
    o ∈ nullKids K n cells ↔ ∃ i, i < n ∧
      ((∃ q ∈ pathsUpTo cells K, o = .hsym 1 (.havoc i) .elem q) ∨ o = .hdeep 1 (.havoc i) .elem) := by
  simp only [nullKids, List.mem_flatMap, List.mem_range, List.mem_append, List.mem_map,
    List.mem_singleton]
  constructor
  · rintro ⟨i, hi, ⟨q, hq, rfl⟩ | rfl⟩
    · exact ⟨i, hi, Or.inl ⟨q, hq, rfl⟩⟩
    · exact ⟨i, hi, Or.inr rfl⟩
  · rintro ⟨i, hi, ⟨q, hq, rfl⟩ | rfl⟩
    · exact ⟨i, hi, Or.inl ⟨q, hq, rfl⟩⟩
    · exact ⟨i, hi, Or.inr rfl⟩

/-- The null origin of a null site below `n` is a null origin of the universe. -/
theorem nullO_mem {K n : Nat} {cells : List ACell} {i : Nat} (h : i < n) :
    nullO i ∈ nullKids K n cells :=
  mem_nullKids.mpr ⟨i, h, Or.inl ⟨[], mem_pathsUpTo.mpr ⟨Nat.zero_le _, fun _ h => by cases h⟩,
    rfl⟩⟩

/-- The null origins are closed under cell names, and their default content is the cell name. -/
theorem nullKids_closed {K n : Nat} {cells : List ACell} {o : Origin} (ho : o ∈ nullKids K n cells)
    {c : ACell} (hc : c ∈ cells) :
    childCN K o c ∈ nullKids K n cells ∧ adefault K o c = [childCN K o c] := by
  obtain ⟨i, hi, ⟨q, hq, rfl⟩ | rfl⟩ := mem_nullKids.mp ho
  · refine ⟨?_, rfl⟩
    obtain ⟨_, hq2⟩ := mem_pathsUpTo.mp hq
    show (if (q ++ [c]).length ≤ K then Origin.hsym 1 (.havoc i) .elem (q ++ [c])
      else .hdeep 1 (.havoc i) .elem) ∈ _
    split
    · rename_i hl
      refine mem_nullKids.mpr ⟨i, hi, Or.inl ⟨q ++ [c], mem_pathsUpTo.mpr ⟨hl, ?_⟩, rfl⟩⟩
      intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · exact hq2 d hd
      · rw [List.mem_singleton.mp hd]; exact hc
    · exact mem_nullKids.mpr ⟨i, hi, Or.inr rfl⟩
  · exact ⟨mem_nullKids.mpr ⟨i, hi, Or.inr rfl⟩, rfl⟩

/-- A context of design BO with more origins `L` is closed, if `L` is closed under cell names
and has no allocation, junk or symbolic origin. -/
theorem CtxBOK.extend {cb0 : CtxB} (hc : CtxBOK cb0) (L : List Origin) (fuel : Nat)
    (hL : ∀ o ∈ L, ∀ c ∈ cb0.cn.ctx.cells,
      childCN cb0.cn.ctx.K o c ∈ L ∧ adefault cb0.cn.ctx.K o c = [childCN cb0.cn.ctx.K o c])
    (hna : ∀ x, Origin.alloc x ∉ L) (hnj : ∀ s, Origin.havoc s ∉ L)
    (hns : ∀ b q, Origin.sym b q ∉ L) :
    CtxBOK ⟨⟨{ cb0.cn.ctx with origins := cb0.cn.ctx.origins ++ L, fuel := fuel },
      cb0.cn.statics, cb0.cn.xe⟩, cb0.xv⟩ := by
  refine ⟨⟨⟨⟨hc.cn.base.base.elem, ?_⟩, ?_, ?_⟩, ?_, ?_, ?_, ?_, hc.cn.xeIn⟩, hc.xvIn, hc.xvNe, ?_⟩
  · intro o ho c hc1 o' ho'
    rcases List.mem_append.mp ho with h | h
    · exact List.mem_append.mpr (Or.inl (hc.cn.base.base.dflt o h c hc1 o' ho'))
    · rw [(hL o h c hc1).2, List.mem_singleton] at ho'
      subst ho'
      exact List.mem_append.mpr (Or.inr (hL o h c hc1).1)
  · intro s h
    rcases List.mem_append.mp h with h | h
    · exact List.mem_append.mpr (Or.inl (hc.cn.base.newOld s h))
    · exact absurd h (hna _)
  · intro s h
    rcases List.mem_append.mp h with h | h
    · exact List.mem_append.mpr (Or.inl (hc.cn.base.oldNew s h))
    · exact absurd h (hna _)
  · intro s h
    rcases List.mem_append.mp h with h | h
    · exact hc.cn.noJunk s h
    · exact hnj s h
  · intro a ha c hc1
    rcases List.mem_append.mp ha with h | h
    · exact List.mem_append.mpr (Or.inl (hc.cn.childIn a h c hc1))
    · exact List.mem_append.mpr (Or.inr (hL a h c hc1).1)
  · intro b q c h
    rcases List.mem_append.mp h with h | h
    · exact List.mem_append.mpr (Or.inl (hc.cn.pre b q c h))
    · exact absurd h (hns _ _)
  · intro b q h
    rcases List.mem_append.mp h with h | h
    · exact List.mem_append.mpr (Or.inl (hc.cn.rootIn b q h))
    · exact absurd h (hns _ _)
  · intro r hr
    exact List.mem_append.mpr (Or.inl (hc.statics r hr))

/-- The context of design VS of a program is closed. -/
theorem ctxVS_ok (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (qf : List Field) : CtxBOK (ctxVS eu K statics fr p qf) := by
  have hc := ctxBO_ok eu K statics fr p qf
  refine CtxBOK.extend hc _ _ (fun o ho c hc1 => nullKids_closed ho hc1) ?_ ?_ ?_
  · intro x h
    obtain ⟨_, _, ⟨_, _, e⟩ | e⟩ := mem_nullKids.mp h <;> cases e
  · intro s h
    obtain ⟨_, _, ⟨_, _, e⟩ | e⟩ := mem_nullKids.mp h <;> cases e
  · intro b q h
    obtain ⟨_, _, ⟨_, _, e⟩ | e⟩ := mem_nullKids.mp h <;> cases e

/-- The universe of design VS contains the universe of design BO. -/
theorem ctxVS_origins_sub (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (qf : List Field) {o : Origin} (h : o ∈ (ctxBO eu K statics fr p qf).cn.ctx.origins) :
    o ∈ (ctxVS eu K statics fr p qf).cn.ctx.origins :=
  List.mem_append.mpr (Or.inl h)

/-- The null origin of each null site of the program is in the universe of design VS. -/
theorem ctxVS_nulls (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (qf : List Field) {i : Nat} (h : i < p.nulls) :
    nullO i ∈ (ctxVS eu K statics fr p qf).cn.ctx.origins :=
  List.mem_append.mpr (Or.inr (nullO_mem h))

/-- The frame fits the context of design VS of a program. -/
theorem ctxVS_frame (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (qf : List Field) : FrameOK (ctxVS eu K statics fr p qf).cn.ctx fr where
  vars := (ctxBO_frame eu K statics fr p qf).vars
  roots x r he := ctxVS_origins_sub eu K statics fr p qf ((ctxBO_frame eu K statics fr p qf).roots x r he)

/-- Each statement of a program fits the context of design VS of the program. -/
theorem ctxVS_stmts (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (qf : List Field) : ∀ st ∈ p.stmts, StmtOKB (ctxVS eu K statics fr p qf) st := by
  intro st hst
  have h0 := ctxBO_stmts eu K statics fr p qf st hst
  exact ⟨h0.vars, h0.noXe, h0.noXv, h0.fields,
    fun s hs => ctxVS_origins_sub eu K statics fr p qf (h0.newS s hs),
    fun s hs => ctxVS_origins_sub eu K statics fr p qf (h0.freshS s hs)⟩

/-- The once budget of a program holds at the entry state for the context of design VS. -/
theorem ctxVS_budget (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (qf : List Field) : Budget (ctxVS eu K statics fr p qf).cn.ctx p (CState.init fr) :=
  ctxBO_budget eu K statics fr p qf

/-! ## Support -/

/-- `retireV` keeps support. -/
theorem supp_retireV (hc : CtxBOK cb) {X : AState} (hs : Supp cb.cn.ctx X) (s : Site) :
    Supp cb.cn.ctx (retireV cb.cn.ctx.K s X) := by
  have h1 := supp_retire (recOK_of hc) hs s
  intro k hk
  cases k with
  | v x => exact h1 (.v x) hk
  | h o c =>
    show (if o = rNew s then [childCN cb.cn.ctx.K (rNew s) c] else (retire s X).heap o c) ⊆ _
    split
    · rename_i e
      subst e
      intro a ha
      rw [List.mem_singleton.mp ha]
      exact hc.cn.childIn _ hk.1 c hk.2
    · exact h1 (.h o c) hk

/-- `setSets` keeps support if the two sets are in the universe. -/
theorem supp_setSets {X : AState} (hs : Supp cb.cn.ctx X) {E V : List Origin}
    (hE : E ⊆ cb.cn.ctx.origins) (hV : V ⊆ cb.cn.ctx.origins) : Supp cb.cn.ctx (setSets cb X E V) := by
  intro k hk
  cases k with
  | v x =>
    show fupd (fupd X.env cb.cn.xe _) cb.xv _ x ⊆ _
    by_cases e1 : x = cb.xv
    · subst e1; rw [fupd_same]; exact uni_sub hV (hs (.v _) hk)
    · rw [fupd_ne _ _ e1]
      by_cases e2 : x = cb.cn.xe
      · subst e2; rw [fupd_same]; exact uni_sub hE (hs (.v _) hk)
      · rw [fupd_ne _ _ e2]; exact hs (.v x) hk
  | h o c => exact hs (.h o c) hk

/-- The passive call keeps support. -/
theorem supp_callVS (hc : CtxBOK cb) {X : AState} (hs : Supp cb.cn.ctx X) {args : List Var}
    (hargs : ∀ a ∈ args, a ∈ cb.cn.ctx.vars) : Supp cb.cn.ctx (callVS cb X args) := by
  have hroots := callRoots_sub hc hs hargs
  unfold callVS
  split
  · rename_i R hR
    exact supp_setSets hs (Opt.CellNamed.closeN_sub hs hroots hR) (Opt.CellNamed.succsN_sub hs R)
  · exact supp_setSets hs (fun _ h => h) (fun _ h => h)

/-- One statement of design VS keeps support. -/
theorem supp_astepVS (hc : CtxBOK cb) {X : AState} (hs : Supp cb.cn.ctx X) {i : Nat} {st : Stmt}
    (ok : StmtOKB cb st) (hnull : st.nullN = 1 → nullO i ∈ cb.cn.ctx.origins) :
    Supp cb.cn.ctx (astepVS cb i st X) := by
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
    exact (supp_retireV hc hs a).setVar x
      (by intro o ho; simp at ho; subst ho; exact ok.newS a rfl)
  | unknown x a =>
    exact (supp_retireV hc hs a).setVar x
      (by intro o ho; simp at ho; subst ho; exact ok.freshS a rfl)
  | call ret a args =>
    have hargs : ∀ v ∈ args, v ∈ cb.cn.ctx.vars := fun v hv => ok.vars v (by simp [Stmt.vars, hv])
    exact (supp_retireV hc (supp_callVS hc hs hargs) a).setRet ret
      (by intro o ho; simp at ho; subst ho; exact ok.freshS a rfl)
  | store x f y =>
    exact supp_storeBO hs x _ (hs.env (ok.vars y (by simp [Stmt.vars])))
  | null x =>
    exact hs.setVar x (by intro o ho; rw [List.mem_singleton.mp ho]; exact hnull rfl)
  | copy x y => exact hs.astep cc (okO rfl rfl rfl)
  | load x y f => exact hs.astep cc (okO rfl rfl rfl)
  | aload x y => exact hs.astep cc (okO rfl rfl rfl)
  | astore x y => exact hs.astep cc (okO rfl rfl rfl)

/-- The null sites `i .. i + n - 1` have their origins in the universe. -/
def NullsIn (cb : CtxB) (i n : Nat) : Prop := ∀ j, i ≤ j → j < i + n → nullO j ∈ cb.cn.ctx.origins

/-- The null sites of the first part of a sequence. -/
theorem NullsIn.left {i n m : Nat} (h : NullsIn cb i (n + m)) : NullsIn cb i n :=
  fun j h1 h2 => h j h1 (by omega)

/-- The null sites of the second part of a sequence. -/
theorem NullsIn.right {i n m : Nat} (h : NullsIn cb i (n + m)) : NullsIn cb (i + n) m :=
  fun j h1 h2 => h j (by omega) (by omega)

/-- The analysis of design VS keeps support. -/
theorem supp_analyzeVS (hc : CtxBOK cb) :
    ∀ (q : Prog) (i : Nat) (X : AState), (∀ st ∈ q.stmts, StmtOKB cb st) → NullsIn cb i q.nulls →
      Supp cb.cn.ctx X → Supp cb.cn.ctx (analyzeVS cb i q X)
  | .skip, _, _, _, _, h => h
  | .stmt st, i, _, ok, hn, h =>
    supp_astepVS hc h (ok st (by simp [Prog.stmts]))
      (fun e => hn i (Nat.le_refl _) (by show i < i + st.nullN; rw [e]; exact Nat.lt_succ_self _))
  | .seq p q, i, X, ok, hn, h =>
    supp_analyzeVS hc q _ _ (fun st hs => ok st (List.mem_append_right _ hs)) hn.right
      (supp_analyzeVS hc p i X (fun st hs => ok st (List.mem_append_left _ hs)) hn.left h)
  | .choice p q, i, X, ok, hn, h =>
    (supp_analyzeVS hc p i X (fun st hs => ok st (List.mem_append_left _ hs)) hn.left h).join
      (supp_analyzeVS hc q _ X (fun st hs => ok st (List.mem_append_right _ hs)) hn.right h)
  | .loop p, i, X, ok, hn, h =>
    Supp.loopIter (fun Y hY => supp_analyzeVS hc p i Y ok hn hY) _ X h

/-- The entry state of design VS has support. -/
theorem supp_ainitVS (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (qf : List Field) : Supp (ctxVS eu K statics fr p qf).cn.ctx (ainitV K fr) := by
  have hc := ctxVS_ok eu K statics fr p qf
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
      exact (ctxVS_frame eu K statics fr p qf).roots x r e
  | h o c =>
    intro a ha
    change a ∈ [childCN K o c] at ha
    rw [List.mem_singleton] at ha
    subst ha
    exact hc.cn.childIn o hk.1 c hk.2

/-! ## One statement -/

/-- LOCAL SOUNDNESS OF DESIGN VS: one instrumented step keeps the invariant and the absence of
empty cells. -/
theorem step_soundVS (hc : CtxBOK cb) {i : Nat} {st : Stmt} {s s' : VState} {X : AState}
    (hok : StmtOKB cb st) (hnull : st.nullN = 1 → nullO i ∈ cb.cn.ctx.origins)
    (hb : Budget cb.cn.ctx (.stmt st) s.cs) (hs : Supp cb.cn.ctx X) (hne : NE X)
    (h : InvVS cb s X) (hst : SStepV src cb.cn.statics i st s s') :
    NE (astepVS cb i st X) ∧ InvVS cb s' (astepVS cb i st X) := by
  obtain ⟨G, hg, hx, hn, hN⟩ := h
  have hbump : ∀ (a : Site) (o : Obj), o ≠ .alloc a (s.cs.cnt a) →
      alphaBO cb G (s.cs.bump a).cnt o = renameO a (alphaBO cb G s.cs.cnt o) :=
    fun a _ ho => alphaBO_bump s.cs hn.2 a ho
  have nx : ∀ v ∈ st.vars, v ≠ cb.cn.xe := hok.noXe
  have nv : ∀ v ∈ st.vars, v ≠ cb.xv := hok.noXv
  cases hst with
  | @new x a =>
    have hxv := hok.vars x (by simp [Stmt.vars])
    have h1 := InvG.retire hc.cn.base a (hbump a) hg
    have hg2 : InvG cb.cn.ctx (alphaBO cb G)
        ((s.cs.bump a).setVar x (some (.alloc a (s.cs.cnt a))))
        ((Recency.retire a X).setVar x [rNew a]) := by
      refine InvG.setVar h1 hxv ?_ ?_
      · intro o e
        cases e
        rw [alphaBO_new]
        refine ⟨?_, hok.newS a rfl, List.mem_singleton.mpr rfl⟩
        rintro ⟨ho, hn⟩
        have := Budget.stmt_site hb rfl ho
        omega
      · intro a' n e
        cases e
        show s.cs.cnt a < fupd s.cs.cnt a (s.cs.cnt a + 1) a
        rw [fupd_same]; exact Nat.lt_succ_self _
    have hx2 := (InvXB.retire hc a hn.2 hg hx).setVar (S := [rNew a])
      (v := some (.alloc a (s.cs.cnt a))) (nx x (by simp [Stmt.vars])) (nv x (by simp [Stmt.vars]))
    refine ⟨(hne.retireV _ a).setVar x _, G, hg2.mono ((retire_sub_retireV _ a X).setVar x _),
      hx2.mono (fun _ h => h) (fun _ h => h), hn.bump a, ?_⟩
    exact (hN.retire hc a hn.2).setVarV (v := .obj (.alloc a (s.cs.cnt a))) hxv
      (fun t e => by cases e)
  | @null x =>
    have hxv := hok.vars x (by simp [Stmt.vars])
    have hin := hnull rfl
    refine ⟨hne.setVar x _, G, ?_, ?_, hn, ?_⟩
    · exact InvG.setVar (S := [nullO i]) hg hxv (fun o e => by cases e) (fun _ _ e => by cases e)
    · exact hx.setVar (v := none) (S := [nullO i]) (nx x (by simp [Stmt.vars]))
        (nv x (by simp [Stmt.vars]))
    · exact (hN.setVarV (v := .nul (.site i (s.nc i))) (S := [nullO i]) hxv
        (fun t e => by cases e; exact ⟨List.mem_singleton.mpr rfl, hin⟩)).congr rfl rfl rfl
  | @copy x y _ v hv =>
    have hxv := hok.vars x (by simp [Stmt.vars])
    have hyv := hok.vars y (by simp [Stmt.vars])
    have e : (s.setVarV x v).cs = s.cs.setVar x (s.cs.env y) := by rw [setVarV_cs, val_toVal hv]
    refine ⟨hne.setVar x _, G, ?_, ?_, ?_, ?_⟩
    · rw [e]
      refine InvG.setVar hg hxv ?_ (fun a n e => hg.envCr y a n e)
      intro o e
      exact ⟨(hg.envOk y o e).1, (hg.envOk y o e).2, hg.env y hyv o e⟩
    · rw [e]; exact hx.setVar (nx x (by simp [Stmt.vars])) (nv x (by simp [Stmt.vars]))
    · rw [e]; exact hn
    · refine hN.setVarV hxv (fun t et => ?_)
      subst et
      obtain ⟨h1, h2⟩ := val_nul hv
      exact ⟨hN.nenv y hyv h1 t h2, hN.nenvIn y t h1 h2⟩
  | @load x y f _ o he =>
    have hxv := hok.vars x (by simp [Stmt.vars])
    have hyv := hok.vars y (by simp [Stmt.vars])
    have e : (s.setVarV x (s.cell o (.fld f))).cs = s.cs.setVar x (s.cs.heap o (.fld f)) := by
      rw [setVarV_cs, cell_toVal]
    have hd := hg.envOk y o he
    have hf : (Cell.fld f).abs ∈ cb.cn.ctx.cells := hok.fields f (by simp [Stmt.fields])
    refine ⟨hne.setVar x _, G, ?_, ?_, ?_, ?_⟩
    · rw [e]
      refine InvG.setVar hg hxv ?_ (fun a n e => hg.heapCr _ _ a n e)
      intro o' e
      exact ⟨hg.heapLive o _ o' hd.1 e, hg.heapIn o _ o' hd.1 hd.2 hf e,
        mem_aread.mpr ⟨_, hg.env y hyv o he, hg.heap o _ o' hd.1 hd.2 hf e⟩⟩
    · rw [e]; exact hx.setVar (nx x (by simp [Stmt.vars])) (nv x (by simp [Stmt.vars]))
    · rw [e]; exact hn
    · refine hN.setVarV hxv (fun t et => ?_)
      obtain ⟨h1, h2⟩ := cell_nul et
      rw [← h2]
      exact ⟨mem_aread.mpr ⟨_, hg.env y hyv o he, hN.nheap o _ hd.1 hd.2 hf h1⟩,
        hN.nheapIn o _ hd.1 hd.2 hf h1⟩
  | @aload x y _ o j he =>
    have hxv := hok.vars x (by simp [Stmt.vars])
    have hyv := hok.vars y (by simp [Stmt.vars])
    have e : (s.setVarV x (s.cell o (.elem j))).cs = s.cs.setVar x (s.cs.heap o (.elem j)) := by
      rw [setVarV_cs, cell_toVal]
    have hd := hg.envOk y o he
    have hf : (Cell.elem j).abs ∈ cb.cn.ctx.cells := hc.cn.base.base.elem
    refine ⟨hne.setVar x _, G, ?_, ?_, ?_, ?_⟩
    · rw [e]
      refine InvG.setVar hg hxv ?_ (fun a n e => hg.heapCr _ _ a n e)
      intro o' e
      exact ⟨hg.heapLive o _ o' hd.1 e, hg.heapIn o _ o' hd.1 hd.2 hf e,
        mem_aread.mpr ⟨_, hg.env y hyv o he, hg.heap o _ o' hd.1 hd.2 hf e⟩⟩
    · rw [e]; exact hx.setVar (nx x (by simp [Stmt.vars])) (nv x (by simp [Stmt.vars]))
    · rw [e]; exact hn
    · refine hN.setVarV hxv (fun t et => ?_)
      obtain ⟨h1, h2⟩ := cell_nul et
      rw [← h2]
      exact ⟨mem_aread.mpr ⟨_, hg.env y hyv o he, hN.nheap o _ hd.1 hd.2 hf h1⟩,
        hN.nheapIn o _ hd.1 hd.2 hf h1⟩
  | @store x f y _ o v he hv =>
    have hxv := hok.vars x (by simp [Stmt.vars])
    have hyv := hok.vars y (by simp [Stmt.vars])
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
    have hxw := fun (Y : AState) (hE : Y.env cb.cn.xe = X.env cb.cn.xe)
        (hV : Y.env cb.xv = X.env cb.xv) =>
      InvXB.write (Y := Y) (c := .fld f) (v := s.cs.env y) hc hx hd hf hE hV
    refine ⟨hne.storeBO cb x _ (val_in hg hN hyv hv), ?_⟩
    show InvVS cb _ (BlockOnly.storeBO cb X x (.fld f) (X.env y))
    unfold BlockOnly.storeBO
    split
    · rename_i oa hsingle
      have hoa : alphaBO cb G s.cs.cnt o = oa := (single?_spec hsingle).2 _ hxo
      split
      · rename_i hu
        rw [← hoa] at hu ⊢
        have huniq : ∀ o1, ¬ Dead cb.cn.ctx.once o1 →
            alphaBO cb G s.cs.cnt o1 = alphaBO cb G s.cs.cnt o → o1 = o :=
          fun o1 hd1 ha => unique_objBO hx.blocked hd.2 hu hd.1 hd1 ha
        refine ⟨G, ?_, ?_, ?_, hN.strong huniq hvN hocr⟩
        · rw [e]; exact InvG.strong hg hd hocr hf huniq hv' hvcr
        · rw [e]; exact hxw _ rfl rfl
        · rw [e]; exact hn
      · refine ⟨G, ?_, ?_, ?_, hN.weak (c := .fld f) hxo hvN hocr⟩
        · rw [e]; exact InvG.weak (c := .fld f) hg hd hocr hf hxo hv' hvcr
        · rw [e]; exact hxw _ rfl rfl
        · rw [e]; exact hn
    · refine ⟨G, ?_, ?_, ?_, hN.weak (c := .fld f) hxo hvN hocr⟩
      · rw [e]; exact InvG.weak (c := .fld f) hg hd hocr hf hxo hv' hvcr
      · rw [e]; exact hxw _ rfl rfl
      · rw [e]; exact hn
  | @astore x y _ o v j he hv =>
    have hxv := hok.vars x (by simp [Stmt.vars])
    have hyv := hok.vars y (by simp [Stmt.vars])
    have e : (s.setCellV o (.elem j) v).cs = s.cs.setCell o (.elem j) (s.cs.env y) := by
      rw [setCellV_cs, val_toVal hv]
    have hd := hg.envOk x o he
    have hxo := hg.env x hxv o he
    have hocr : ∀ a n, o = .alloc a n → n < s.cs.cnt a := fun a n e => hg.envCr x a n (e ▸ he)
    have hvN : ∀ t, v = .nul t → alphaN cb.cn.ctx.K t ∈ X.env y ∧
        alphaN cb.cn.ctx.K t ∈ cb.cn.ctx.origins := by
      intro t et
      subst et
      obtain ⟨h1, h2⟩ := val_nul hv
      exact ⟨hN.nenv y hyv h1 t h2, hN.nenvIn y t h1 h2⟩
    refine ⟨hne.weakStore _ _ _, G, ?_, ?_, ?_, hN.weak (c := .elem j) hxo hvN hocr⟩
    · rw [e]
      exact InvG.weak (c := .elem j) hg hd hocr hc.cn.base.base.elem hxo
        (fun o' e => ⟨(hg.envOk y o' e).1, (hg.envOk y o' e).2, hg.env y hyv o' e⟩)
        (fun a n e => hg.envCr y a n e)
    · rw [e]; exact InvXB.write (c := .elem j) hc hx hd hc.cn.base.base.elem rfl rfl
    · rw [e]; exact hn
  | @unknown x a =>
    have hxv := hok.vars x (by simp [Stmt.vars])
    have h1 := InvG.retire hc.cn.base a (hbump a) hg
    have hg2 : InvG cb.cn.ctx (alphaBO cb G)
        ((s.cs.bump a).setVar x (some (.sym (.fresh a (s.cs.cnt a)) [])))
        ((Recency.retire a X).setVar x [.sym (.fresh a) []]) := by
      refine InvG.setVar h1 hxv ?_ (fun _ _ e => by cases e)
      intro o e
      cases e
      rw [alphaBO_fresh]
      refine ⟨?_, hok.freshS a rfl, List.mem_singleton.mpr rfl⟩
      rintro ⟨ho, hn⟩
      have := Budget.stmt_site hb rfl ho
      omega
    have hx2 := (InvXB.retire hc a hn.2 hg hx).setVar (S := [.sym (.fresh a) []])
      (v := some (.sym (.fresh a (s.cs.cnt a)) [])) (nx x (by simp [Stmt.vars]))
      (nv x (by simp [Stmt.vars]))
    refine ⟨(hne.retireV _ a).setVar x _, G, hg2.mono ((retire_sub_retireV _ a X).setVar x _),
      hx2.mono (fun _ h => h) (fun _ h => h), hn.bump a, ?_⟩
    exact (hN.retire hc a hn.2).setVarV (v := .obj (.sym (.fresh a (s.cs.cnt a)) [])) hxv
      (fun t e => by cases e)
  | @call ret a args _ h' hh =>
    have hargs : ∀ v ∈ args, v ∈ cb.cn.ctx.vars := fun v hv => hok.vars v (by simp [Stmt.vars, hv])
    obtain ⟨hg1, hx1⟩ := callBO_sound hc hg hx hn hargs hh hs
    rw [callBO_eq cb hne args] at hg1 hx1
    have hN1 := hN.call hx hn hh
    have hle1 : GhostLe (ghostsAfter cb G src s.cs.cnt h' (callVS cb X args) a (s.cs.cnt a))
        s.cs.cnt := ghostLe_after hn.2
    have h2 := InvG.retire hc.cn.base a
      (fun o ho => alphaBO_bump (cb := cb) { s.cs with heap := h' } hle1 a ho) hg1
    have hx2 := InvXB.retire (st := { s.cs with heap := h' }) hc a hle1 hg1 hx1
    have hn2 : CntOKB (ghostsAfter cb G src s.cs.cnt h' (callVS cb X args) a (s.cs.cnt a))
        ({ s.cs with heap := h' }.bump a).cnt := cnt_afterB hn
    have hN2 := InvN.retire (vs := { s with cs := { s.cs with heap := h' } }) hc a hle1 hN1
    refine ⟨((hne.callVS cb args).retireV _ a).setRet ret _, ?_⟩
    show InvVS cb _ ((retireV cb.cn.ctx.K a (callVS cb X args)).setRet ret [.sym (.fresh a) []])
    cases ret with
    | none =>
      exact ⟨_, h2.mono (retire_sub_retireV _ a _), hx2.mono (fun _ h => h) (fun _ h => h), hn2,
        hN2⟩
    | some x =>
      have hxv := hok.vars x (by simp [Stmt.vars])
      have hg3 : InvG cb.cn.ctx
          (alphaBO cb (ghostsAfter cb G src s.cs.cnt h' (callVS cb X args) a (s.cs.cnt a)))
          (({ s.cs with heap := h' }.bump a).setVar x (some (.sym (.fresh a (s.cs.cnt a)) [])))
          ((Recency.retire a (callVS cb X args)).setVar x [.sym (.fresh a) []]) := by
        refine InvG.setVar h2 hxv ?_ (fun _ _ e => by cases e)
        intro o e
        cases e
        rw [alphaBO_fresh]
        refine ⟨?_, hok.freshS a rfl, List.mem_singleton.mpr rfl⟩
        rintro ⟨ho, hn⟩
        have := Budget.stmt_site hb rfl ho
        omega
      have hx3 := hx2.setVar (S := [.sym (.fresh a) []])
        (v := some (.sym (.fresh a (s.cs.cnt a)) [])) (nx x (by simp [Stmt.vars]))
        (nv x (by simp [Stmt.vars]))
      exact ⟨_, hg3.mono ((retire_sub_retireV _ a _).setVar x _),
        hx3.mono (fun _ h => h) (fun _ h => h), hn2,
        hN2.setVarV (v := .obj (.sym (.fresh a (s.cs.cnt a)) [])) hxv (fun t e => by cases e)⟩

/-! ## Programs -/

/-- A loop keeps an invariant state `Y` of design VS if one run of the body keeps it. -/
theorem loop_keepsVS {i : Nat} {body : Prog} {Y : AState} (P : VState → Prop)
    (hstep : ∀ s t, P s → InvVS cb s Y → ExecV src cb.cn.statics i body s t → P t ∧ InvVS cb t Y) :
    ∀ {s u : VState}, ExecV src cb.cn.statics i (.loop body) s u → P s → InvVS cb s Y →
      InvVS cb u Y := by
  intro s u hx
  generalize hq : Prog.loop body = q at hx
  generalize hj : i = j at hx
  induction hx with
  | skip => intro _ h; exact h
  | stmt _ => cases hq
  | seq _ _ _ _ => cases hq
  | choiceL _ _ => cases hq
  | choiceR _ _ => cases hq
  | loopZero => intro _ h; exact h
  | loopMore h1 _ _ ih2 =>
    cases hq
    subst hj
    intro hp hi
    obtain ⟨hp', hi'⟩ := hstep _ _ hp hi h1
    exact ih2 rfl rfl hp' hi'

/-- Soundness of `analyzeVS`: each instrumented execution ends in a state that the analysis
result simulates, and the result has no empty cell. -/
theorem analyze_soundVS (hc : CtxBOK cb) :
    ∀ (q : Prog) (i : Nat) {s s' : VState} {X : AState}, (∀ st ∈ q.stmts, StmtOKB cb st) →
      NullsIn cb i q.nulls → Budget cb.cn.ctx q s.cs → Supp cb.cn.ctx X → NE X →
      InvVS cb s X → ExecV src cb.cn.statics i q s s' →
      NE (analyzeVS cb i q X) ∧ InvVS cb s' (analyzeVS cb i q X) := by
  intro q
  induction q with
  | skip => intro i s s' X _ _ _ _ hne h hx; cases hx; exact ⟨hne, h⟩
  | stmt st =>
    intro i s s' X hok hn hb hs hne h hx
    cases hx with
    | stmt hst =>
      exact step_soundVS hc (hok st (List.mem_singleton.mpr rfl))
        (fun e => hn i (Nat.le_refl _) (by show i < i + st.nullN; rw [e]; exact Nat.lt_succ_self _))
        hb hs hne h hst
  | seq p q ihp ihq =>
    intro i s s' X hok hn hb hs hne h hx
    cases hx with
    | seq h1 h2 =>
      have hokp : ∀ st ∈ p.stmts, StmtOKB cb st :=
        fun st hs => hok st (List.mem_append.mpr (Or.inl hs))
      have hokq : ∀ st ∈ q.stmts, StmtOKB cb st :=
        fun st hs => hok st (List.mem_append.mpr (Or.inr hs))
      obtain ⟨hne1, h1'⟩ := ihp i hokp hn.left (Budget.seqL hb) hs hne h h1
      exact ihq _ hokq hn.right (Budget.seqR hb h1.toN.toExec)
        (supp_analyzeVS hc p i X hokp hn.left hs) hne1 h1' h2
  | choice p q ihp ihq =>
    intro i s s' X hok hn hb hs hne h hx
    have hokp : ∀ st ∈ p.stmts, StmtOKB cb st :=
      fun st hs => hok st (List.mem_append.mpr (Or.inl hs))
    have hokq : ∀ st ∈ q.stmts, StmtOKB cb st :=
      fun st hs => hok st (List.mem_append.mpr (Or.inr hs))
    cases hx with
    | choiceL h1 =>
      obtain ⟨hne1, h1'⟩ := ihp i hokp hn.left (Budget.choiceL hb) hs hne h h1
      exact ⟨hne1.join _, h1'.mono (sub_join_left _ _)⟩
    | choiceR h1 =>
      obtain ⟨hne1, h1'⟩ := ihq _ hokq hn.right (Budget.choiceR hb) hs hne h h1
      exact ⟨hne1.mono (sub_join_right _ _), h1'.mono (sub_join_right _ _)⟩
  | loop body ih =>
    intro i s s' X hok hn hb hs hne h hx
    show NE (loopIter cb.cn.ctx (analyzeVS cb i body) cb.cn.ctx.fuel X) ∧
      InvVS cb s' (loopIter cb.cn.ctx (analyzeVS cb i body) cb.cn.ctx.fuel X)
    have hsY := Supp.loopIter (fun Y hY => supp_analyzeVS hc body i Y hok hn hY) cb.cn.ctx.fuel X hs
    have hneY := hne.loopIter cb.cn.ctx (analyzeVS cb i body) cb.cn.ctx.fuel
    have hY := h.mono (sub_loopIter cb.cn.ctx (analyzeVS cb i body) cb.cn.ctx.fuel X)
    refine ⟨hneY, loop_keepsVS (fun t => Budget cb.cn.ctx (.loop body) t.cs) ?_ hx hb hY⟩
    intro s1 t hb1 hi1 hx1
    refine ⟨Budget.again hb1 hx1.toN.toExec, ?_⟩
    have hf := (ih i hok hn (Budget.body hb1) hsY hneY hi1 hx1).2
    rcases loopIter_post cb.cn.ctx (analyzeVS cb i body) cb.cn.ctx.fuel X with hpost | ⟨W, hW⟩
    · exact hf.mono_leOn hc hpost
    · rw [hW]; exact hf.top W

/-- The entry states satisfy the invariant of design VS. -/
theorem inv_initVS (hc : CtxBOK cb) {fr : Frame} (hf : FrameOK cb.cn.ctx fr) :
    InvVS cb (VState.init fr) (ainitV cb.cn.ctx.K fr) := by
  obtain ⟨G, hg, hx, hn⟩ := inv_initBO hc hf
  have hsub : (ainit cb.cn.ctx.K fr).Sub (ainitV cb.cn.ctx.K fr) := by
    refine ⟨fun _ _ h => h, fun o c a h => ?_⟩
    show a ∈ [childCN cb.cn.ctx.K o c]
    cases o with
    | alloc x => change a ∈ ([] : List Origin) at h; cases h
    | _ => rw [← adefault_childCN cb.cn.ctx.K (fun x e => by cases e) c]; exact h
  refine ⟨G, hg.mono hsub, hx.mono (fun _ h => h) (fun _ h => h), hn, ?_⟩
  have hnone : ∀ o c, (CState.init fr).heap o c = none → ∃ s n, o = .alloc s n := by
    intro o c e
    cases o with
    | alloc s n => exact ⟨s, n, rfl⟩
    | sym b p => cases e
  exact {
    nout := fun _ _ => rfl
    nenv := fun _ _ _ _ e => by cases e
    nenvIn := fun _ _ _ e => by cases e
    nheap := fun o c _ _ _ he => by
      obtain ⟨s, n, rfl⟩ := hnone o c he
      show alphaN cb.cn.ctx.K (.dflt (.alloc s n) c) ∈ [childCN cb.cn.ctx.K _ c.abs]
      rw [alphaN_dflt_alloc cb G]
      exact List.mem_singleton.mpr rfl
    nheapIn := fun o c _ hin hc1 he => by
      obtain ⟨s, n, rfl⟩ := hnone o c he
      show alphaN cb.cn.ctx.K (.dflt (.alloc s n) c) ∈ _
      rw [alphaN_dflt_alloc cb G]
      exact hc.cn.childIn _ hin _ hc1
    nfresh := fun _ _ _ _ => rfl }

/-! ## Soundness -/

/-- SOUNDNESS OF DESIGN VS: for each naming `src`, each list of static roots, each depth limit
and both strong-update policies, each one-execution value alias of the instrumented strict
narrow semantics (the same object or the same null instance) is a may-alias of `mayProgVS`. -/
theorem csoundVS (src : Nat → Obj × Cell) (statics : List Root) (eu : Bool) (K : Nat)
    (fr : Frame) (p : Prog) (x : Var) (px : List Cell) (y : Var) (py : List Cell)
    (h : CAliasV src statics fr p x px y py) :
    mayProgVS eu K statics fr p x (px.map Cell.abs) y (py.map Cell.abs) = true := by
  obtain ⟨vs, hx, ha⟩ := h
  let qf := afields (px.map Cell.abs) ++ afields (py.map Cell.abs)
  have hc := ctxVS_ok eu K statics fr p qf
  obtain ⟨_, hinv⟩ := analyze_soundVS (src := src) hc p 0 (ctxVS_stmts eu K statics fr p qf)
    (fun j _ hj => ctxVS_nulls eu K statics fr p qf (by omega))
    (ctxVS_budget eu K statics fr p qf) (supp_ainitVS eu K statics fr p qf) (NE_ainitV K fr)
    (inv_initVS hc (ctxVS_frame eu K statics fr p qf)) hx
  have hcx := query_cells (cells := p.fields) qf (fun a ha => List.mem_append.mpr (Or.inl ha))
  have hcy := query_cells (cells := p.fields) qf (fun a ha => List.mem_append.mpr (Or.inr ha))
  exact hinv.may_of_alias hcx hcy ha

/-- No instrumented execution gives two paths the same value instance if `mayProgVS` answers
false. -/
theorem no_alias_of_mayProgVS (src : Nat → Obj × Cell) (statics : List Root) (eu : Bool)
    (K : Nat) (fr : Frame) (p : Prog) (x : Var) (px : List Cell) (y : Var) (py : List Cell)
    (h : mayProgVS eu K statics fr p x (px.map Cell.abs) y (py.map Cell.abs) = false) :
    ¬ CAliasV src statics fr p x px y py := by
  intro ha
  have := csoundVS src statics eu K fr p x px y py ha
  rw [h] at this; cases this

end DirectedAlias.Sound.ValueSem

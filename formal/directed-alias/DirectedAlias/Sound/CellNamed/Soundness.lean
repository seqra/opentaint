import DirectedAlias.Sound.CellNamed.Call

/-!
# Soundness of design CN under strict narrow A2

The main theorem is `csoundCN`: for each naming `src`, each set of static roots, each depth
limit and both strong-update policies, each strict narrow one-execution alias is a may-alias
of `mayProgCN`.
-/

namespace DirectedAlias.Sound.CellNamed

open DirectedAlias DirectedAlias.Sound DirectedAlias.Sound.Recency DirectedAlias.Sound.Havoc
open DirectedAlias.Sound.HavocRecency

variable {src : Nat → Obj × Cell} {cn : CtxN}

/-! ## The invariant -/

/-- The invariant of design CN is closed upward under state inclusion. -/
theorem InvCN.mono {st : CState} {X Y : AState} (h : InvCN cn st X) (hs : X.Sub Y) :
    InvCN cn st Y :=
  let ⟨N, hg, hx, hn⟩ := h
  ⟨N, hg.mono hs, hx.mono (fun _ ha => hs.1 _ ha), hn⟩

/-- The invariant of design CN is closed upward under inclusion on the universe. -/
theorem InvCN.mono_leOn (hc : CtxNOK cn) {st : CState} {X Y : AState} (h : InvCN cn st X)
    (hs : leOn cn.ctx X Y = true) : InvCN cn st Y :=
  let ⟨N, hg, hx, hn⟩ := h
  ⟨N, hg.mono_leOn hs, hx.mono_leOn hc hs, hn⟩

/-- Each top state simulates each concrete state of the invariant. -/
theorem InvCN.top (hc : CtxNOK cn) {st : CState} {X : AState} (h : InvCN cn st X)
    (W : AState) : InvCN cn st (top cn.ctx W) :=
  let ⟨N, hg, hx, hn⟩ := h
  ⟨N, hg.top W, hx.top hc W, hn⟩

/-- A counter bump keeps the counter facts of the ghost names. -/
theorem CntOK.bump {N : Names} {st : CState} (h : CntOK N st.cnt) (a : Site) :
    CntOK N (st.bump a).cnt := by
  intro s n k x e
  have := h s n k x e
  show n < fupd st.cnt a (st.cnt a + 1) s
  by_cases e2 : s = a
  · subst e2; rw [fupd_same]; omega
  · rw [fupd_ne _ _ e2]; exact this

/-- A statement fits the universe of design CN: its variables are in the universe and are not
the reserved variable, its fields are cells, and its sites have their origins. -/
structure StmtOKN (cn : CtxN) (st : Stmt) : Prop where
  vars : ∀ v ∈ st.vars, v ∈ cn.ctx.vars
  noXe : ∀ v ∈ st.vars, v ≠ cn.xe
  fields : ∀ f ∈ st.fields, ACell.fld f ∈ cn.ctx.cells
  newS : ∀ s, st.newSite? = some s → rNew s ∈ cn.ctx.origins
  freshS : ∀ s, st.freshSite? = some s → Origin.sym (.fresh s) [] ∈ cn.ctx.origins

/-! ## One statement -/

/-- Local soundness of design CN: one strict narrow step keeps the invariant. -/
theorem step_soundCN (hc : CtxNOK cn) {st : Stmt} {s s' : CState} {X : AState}
    (hok : StmtOKN cn st) (hb : Budget cn.ctx (.stmt st) s) (h : InvCN cn s X)
    (hs : SStepN src cn.statics st s s') : InvCN cn s' (astepCN cn st X) := by
  obtain ⟨N, hg, hx, hn⟩ := h
  have hN : ∀ s n k a, N s n k = some a → isName a = true :=
    fun s n k a e => (hx.names s n k a e).name
  have hbump : ∀ (t : CState) (a : Site) (o : Obj), o ≠ .alloc a (t.cnt a) →
      alphaCN cn.ctx.K N (t.bump a).cnt o = renameO a (alphaCN cn.ctx.K N t.cnt o) :=
    fun t a _ ho => alphaCN_bump cn.ctx.K hN t a ho
  have hv1 : ∀ v ∈ st.vars, v ∈ cn.ctx.vars := hok.vars
  cases hs with
  | @new x a =>
    have h1 := InvG.retire hc.base a (hbump s a) hg
    refine ⟨N, ?_, (InvX.retire hc a hg hx).setVar (hok.noXe x (by simp [Stmt.vars])),
      hn.bump a⟩
    show InvG cn.ctx (alphaCN cn.ctx.K N) ((s.bump a).setVar x (some (.alloc a (s.cnt a))))
      ((retire a X).setVar x [rNew a])
    refine InvG.setVar h1 (hok.vars x (by simp [Stmt.vars])) ?_ ?_
    · intro o e
      cases e
      rw [alphaCN_new]
      refine ⟨?_, hok.newS a rfl, List.mem_singleton.mpr rfl⟩
      rintro ⟨ho, hn⟩
      have := Budget.stmt_site hb rfl ho
      omega
    · intro a' n e
      cases e
      show s.cnt a < fupd s.cnt a (s.cnt a + 1) a
      rw [fupd_same]; exact Nat.lt_succ_self _
  | @null x =>
    exact ⟨N, InvG.setVar hg (hok.vars x (by simp [Stmt.vars])) (fun o e => by cases e)
      (fun _ _ e => by cases e), hx.setVar (hok.noXe x (by simp [Stmt.vars])), hn⟩
  | @copy x y =>
    refine ⟨N, InvG.setVar hg (hok.vars x (by simp [Stmt.vars])) ?_ (fun a n e => hg.envCr y a n e),
      hx.setVar (hok.noXe x (by simp [Stmt.vars])), hn⟩
    intro o e
    exact ⟨(hg.envOk y o e).1, (hg.envOk y o e).2, hg.env y (hok.vars y (by simp [Stmt.vars])) o e⟩
  | @load x y f _ o he =>
    refine ⟨N, InvG.setVar hg (hok.vars x (by simp [Stmt.vars])) ?_
      (fun a n e => hg.heapCr _ _ a n e), hx.setVar (hok.noXe x (by simp [Stmt.vars])), hn⟩
    intro o' e
    have hd := hg.envOk y o he
    have hf : (Cell.fld f).abs ∈ cn.ctx.cells := hok.fields f (by simp [Stmt.fields])
    exact ⟨hg.heapLive o _ o' hd.1 e, hg.heapIn o _ o' hd.1 hd.2 hf e,
      mem_aread.mpr ⟨_, hg.env y (hok.vars y (by simp [Stmt.vars])) o he,
        hg.heap o _ o' hd.1 hd.2 hf e⟩⟩
  | @aload x y _ o i he =>
    refine ⟨N, InvG.setVar hg (hok.vars x (by simp [Stmt.vars])) ?_
      (fun a n e => hg.heapCr _ _ a n e), hx.setVar (hok.noXe x (by simp [Stmt.vars])), hn⟩
    intro o' e
    have hd := hg.envOk y o he
    have hf : (Cell.elem i).abs ∈ cn.ctx.cells := hc.base.base.elem
    exact ⟨hg.heapLive o _ o' hd.1 e, hg.heapIn o _ o' hd.1 hd.2 hf e,
      mem_aread.mpr ⟨_, hg.env y (hok.vars y (by simp [Stmt.vars])) o he,
        hg.heap o _ o' hd.1 hd.2 hf e⟩⟩
  | @store x f y _ o he =>
    have hd := hg.envOk x o he
    have hxo := hg.env x (hok.vars x (by simp [Stmt.vars])) o he
    have hf : ACell.fld f ∈ cn.ctx.cells := hok.fields f (by simp [Stmt.fields])
    have hocr : ∀ a n, o = .alloc a n → n < s.cnt a := fun a n e => hg.envCr x a n (e ▸ he)
    have hv : ∀ o', s.env y = some o' → ¬ Dead cn.ctx.once o' ∧
        alphaCN cn.ctx.K N s.cnt o' ∈ cn.ctx.origins ∧ alphaCN cn.ctx.K N s.cnt o' ∈ X.env y :=
      fun o' e => ⟨(hg.envOk y o' e).1, (hg.envOk y o' e).2,
        hg.env y (hok.vars y (by simp [Stmt.vars])) o' e⟩
    have hvcr : ∀ a n, s.env y = some (.alloc a n) → n < s.cnt a := fun a n e => hg.envCr y a n e
    have hxw := fun (Y : AState) (hE : Y.env cn.xe = X.env cn.xe) =>
      InvX.write (Y := Y) (c := .fld f) (v := s.env y) hc hx hd hf hE
    show InvCN cn _ (storeCN cn X x (.fld f) (X.env y))
    unfold storeCN
    split
    · rename_i oa hsingle
      have hoa : alphaCN cn.ctx.K N s.cnt o = oa := (single?_spec hsingle).2 _ hxo
      split
      · rename_i hu
        rw [← hoa] at hu ⊢
        exact ⟨N, InvG.strong hg hd hocr hf
          (fun o1 hd1 ha => unique_objCN hc (fun s n k a e => hx.names s n k a e) hd.2 hu hd.1
            hd1 ha) hv hvcr, hxw _ rfl, hn⟩
      · exact ⟨N, InvG.weak (c := .fld f) hg hd hocr hf hxo hv hvcr, hxw _ rfl, hn⟩
    · exact ⟨N, InvG.weak (c := .fld f) hg hd hocr hf hxo hv hvcr, hxw _ rfl, hn⟩
  | @astore x y _ o i he =>
    have hd := hg.envOk x o he
    have hxo := hg.env x (hok.vars x (by simp [Stmt.vars])) o he
    exact ⟨N, InvG.weak (c := .elem i) hg hd (fun a n e => hg.envCr x a n (e ▸ he))
      hc.base.base.elem hxo
      (fun o' e => ⟨(hg.envOk y o' e).1, (hg.envOk y o' e).2,
        hg.env y (hok.vars y (by simp [Stmt.vars])) o' e⟩) (fun a n e => hg.envCr y a n e),
      InvX.write (c := .elem i) hc hx hd hc.base.base.elem rfl, hn⟩
  | @unknown x a =>
    have h1 := InvG.retire hc.base a (hbump s a) hg
    refine ⟨N, ?_, (InvX.retire hc a hg hx).setVar (hok.noXe x (by simp [Stmt.vars])),
      hn.bump a⟩
    show InvG cn.ctx (alphaCN cn.ctx.K N)
      ((s.bump a).setVar x (some (.sym (.fresh a (s.cnt a)) [])))
      ((retire a X).setVar x [.sym (.fresh a) []])
    refine InvG.setVar h1 (hok.vars x (by simp [Stmt.vars])) ?_ (fun _ _ e => by cases e)
    intro o e
    cases e
    rw [alphaCN_fresh]
    refine ⟨?_, hok.freshS a rfl, List.mem_singleton.mpr rfl⟩
    rintro ⟨ho, hn⟩
    have := Budget.stmt_site hb rfl ho
    omega
  | @call ret a args _ h' hh =>
    have hargs : ∀ v ∈ args, v ∈ cn.ctx.vars := fun v hv => hok.vars v (by simp [Stmt.vars, hv])
    obtain ⟨hg1, hx1⟩ := havocCN_sound hc hg hx hn hargs hh
    have hN' : ∀ s' n k b, namesAfter cn.ctx.K N src s.cnt h' a (s.cnt a) s' n k = some b →
        isName b = true := fun s' n k b e => (hx1.names s' n k b e).name
    have h2 := InvG.retire hc.base a
      (fun o ho => alphaCN_bump cn.ctx.K hN' { s with heap := h' } a ho) hg1
    have hx2 := InvX.retire hc a hg1 hx1
    have hn2 : CntOK (namesAfter cn.ctx.K N src s.cnt h' a (s.cnt a))
        ({ s with heap := h' }.bump a).cnt := cnt_after hn
    show InvCN cn _ ((retire a (havocCN cn X args)).setRet ret [.sym (.fresh a) []])
    cases ret with
    | none => exact ⟨_, h2, hx2, hn2⟩
    | some x =>
      refine ⟨_, ?_, hx2.setVar (hok.noXe x (by simp [Stmt.vars])), hn2⟩
      show InvG cn.ctx _
        (({ s with heap := h' }.bump a).setVar x (some (.sym (.fresh a (s.cnt a)) [])))
        ((retire a (havocCN cn X args)).setVar x [.sym (.fresh a) []])
      refine InvG.setVar h2 (hok.vars x (by simp [Stmt.vars])) ?_ (fun _ _ e => by cases e)
      intro o e
      cases e
      rw [alphaCN_fresh]
      refine ⟨?_, hok.freshS a rfl, List.mem_singleton.mpr rfl⟩
      rintro ⟨ho, hn⟩
      have := Budget.stmt_site hb rfl ho
      omega

/-! ## Programs -/

/-- A loop keeps an invariant state `Y` of design CN if one narrow run of the body keeps it. -/
theorem loop_keepsCN {body : Prog} {Y : AState} (P : CState → Prop)
    (hstep : ∀ s t, P s → InvCN cn s Y → ExecN src cn.statics body s t → P t ∧ InvCN cn t Y) :
    ∀ {s u : CState}, ExecN src cn.statics (.loop body) s u → P s → InvCN cn s Y →
      InvCN cn u Y := by
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

/-- Soundness of `analyzeCN`: each strict narrow execution ends in a state that the analysis
result simulates. -/
theorem analyze_soundCN (hc : CtxNOK cn) :
    ∀ (q : Prog) {s s' : CState} {X : AState}, (∀ st ∈ q.stmts, StmtOKN cn st) →
      Budget cn.ctx q s → InvCN cn s X → ExecN src cn.statics q s s' →
      InvCN cn s' (analyzeCN cn q X) := by
  intro q
  induction q with
  | skip => intro s s' X _ _ h hx; cases hx; exact h
  | stmt st =>
    intro s s' X hok hb h hx
    cases hx with
    | stmt hs => exact step_soundCN hc (hok st (List.mem_singleton.mpr rfl)) hb h hs
  | seq p q ihp ihq =>
    intro s s' X hok hb h hx
    cases hx with
    | seq h1 h2 =>
      have hokp : ∀ st ∈ p.stmts, StmtOKN cn st :=
        fun st hs => hok st (List.mem_append.mpr (Or.inl hs))
      have hokq : ∀ st ∈ q.stmts, StmtOKN cn st :=
        fun st hs => hok st (List.mem_append.mpr (Or.inr hs))
      exact ihq hokq (Budget.seqR hb h1.toExec) (ihp hokp (Budget.seqL hb) h h1) h2
  | choice p q ihp ihq =>
    intro s s' X hok hb h hx
    have hokp : ∀ st ∈ p.stmts, StmtOKN cn st :=
      fun st hs => hok st (List.mem_append.mpr (Or.inl hs))
    have hokq : ∀ st ∈ q.stmts, StmtOKN cn st :=
      fun st hs => hok st (List.mem_append.mpr (Or.inr hs))
    cases hx with
    | choiceL h1 => exact (ihp hokp (Budget.choiceL hb) h h1).mono (sub_join_left _ _)
    | choiceR h1 => exact (ihq hokq (Budget.choiceR hb) h h1).mono (sub_join_right _ _)
  | loop body ih =>
    intro s s' X hok hb h hx
    show InvCN cn s' (loopIter cn.ctx (analyzeCN cn body) cn.ctx.fuel X)
    have hY := h.mono (sub_loopIter cn.ctx (analyzeCN cn body) cn.ctx.fuel X)
    refine loop_keepsCN (Budget cn.ctx (.loop body)) ?_ hx hb hY
    intro s1 t hb1 hi1 hx1
    refine ⟨Budget.again hb1 hx1.toExec, ?_⟩
    have hf := ih hok (Budget.body hb1) hi1 hx1
    rcases loopIter_post cn.ctx (analyzeCN cn body) cn.ctx.fuel X with hpost | ⟨W, hW⟩
    · exact hf.mono_leOn hc hpost
    · rw [hW]; exact hf.top hc W

/-- The entry states satisfy the invariant of design CN, with the empty ghost naming. -/
theorem inv_initCN (hc : CtxNOK cn) {fr : Frame} (hf : FrameOK cn.ctx fr) :
    InvCN cn (CState.init fr) (ainit cn.ctx.K fr) := by
  let N0 : Names := fun _ _ _ => none
  have hN0 : ∀ s n k a, N0 s n k = some a → isName a = true := fun _ _ _ _ e => by cases e
  refine ⟨N0, ?_, ?_, fun _ _ _ _ e => by cases e⟩
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
          rw [alphaCN_root]
          exact hf.roots x r e
      heapLive := fun o c o' hd hh => by
        change cdefault o c = some o' at hh
        cases o with
        | alloc s n => cases hh
        | sym b p => cases hh; cases b <;> simp_all [Dead]
      heapIn := fun o c o' _ hin hc1 hh => by
        change cdefault o c = some o' at hh
        exact hc.base.base.dflt _ hin _ hc1 _ (alphaCN_cdefault_mem cn.ctx.K _ hN0 hh)
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
        show alphaCN cn.ctx.K N0 (CState.init fr).cnt o ∈ (match fr.root? x with
          | some r => [Origin.sym (.root r) []] | none => [])
        cases e : fr.root? x with
        | none => rw [e] at he; cases he
        | some r =>
          rw [e] at he; cases he
          rw [alphaCN_root]
          exact List.mem_singleton.mpr rfl
      heap := fun o c o' _ _ _ hh => by
        change cdefault o c = some o' at hh
        exact alphaCN_cdefault_mem cn.ctx.K _ hN0 hh }
  · exact {
      junkDflt := fun _ _ _ => rfl
      deadDflt := fun _ _ _ => rfl
      outside := fun o c o' _ hh => Or.inr (alphaCN_cdefault cn.ctx.K N0 _ hh)
      names := fun _ _ _ _ e => by cases e }

/-! ## The universe of a program -/

/-- Membership in the universe of design CN. -/
theorem mem_originsCN {K : Nat} {fr : Frame} {statics : List Root} {p : Prog}
    {cells : List ACell} {o : Origin} :
    o ∈ originsCN K fr statics p cells ↔
      (∃ b ∈ basesCN fr statics p, (∃ q ∈ pathsUpTo cells K, o = .sym b q) ∨ o = .deep b) ∨
      (∃ s ∈ p.newSites, o = rNew s ∨ o = rOld s) ∨
      (∃ s ∈ p.newSites, ∃ c ∈ cells,
        (∃ q ∈ pathsUpTo cells K, o = .hsym 0 (rOld s) c q) ∨ o = .hdeep 0 (rOld s) c) := by
  simp only [originsCN, heapKids, List.mem_append, List.mem_flatMap, List.mem_map,
    List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ((⟨b, hb, ⟨q, hq, rfl⟩ | rfl⟩ | ⟨s, hs, h⟩) | ⟨s, hs, c, hc, ⟨q, hq, rfl⟩ | rfl⟩)
    · exact Or.inl ⟨b, hb, Or.inl ⟨q, hq, rfl⟩⟩
    · exact Or.inl ⟨b, hb, Or.inr rfl⟩
    · exact Or.inr (Or.inl ⟨s, hs, h⟩)
    · exact Or.inr (Or.inr ⟨s, hs, c, hc, Or.inl ⟨q, hq, rfl⟩⟩)
    · exact Or.inr (Or.inr ⟨s, hs, c, hc, Or.inr rfl⟩)
  · rintro (⟨b, hb, ⟨q, hq, rfl⟩ | rfl⟩ | ⟨s, hs, h⟩ | ⟨s, hs, c, hc, ⟨q, hq, rfl⟩ | rfl⟩)
    · exact Or.inl (Or.inl ⟨b, hb, Or.inl ⟨q, hq, rfl⟩⟩)
    · exact Or.inl (Or.inl ⟨b, hb, Or.inr rfl⟩)
    · exact Or.inl (Or.inr ⟨s, hs, h⟩)
    · exact Or.inr ⟨s, hs, c, hc, Or.inl ⟨q, hq, rfl⟩⟩
    · exact Or.inr ⟨s, hs, c, hc, Or.inr rfl⟩

/-- Each variable of a list is smaller than `freshVar` of the list. -/
theorem lt_freshVar : ∀ {l : List Var} {v : Var}, v ∈ l → v < freshVar l
  | a :: l, v, h => by
    show v < max a (l.foldr max 0) + 1
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.lt_succ_of_le (Nat.le_max_left _ _)
    · exact Nat.lt_of_lt_of_le (lt_freshVar h) (Nat.succ_le_succ (Nat.le_max_right _ _))

/-- The context of design CN of a program is closed. -/
theorem ctxCN_ok (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (qf : List Field) : CtxNOK (ctxCN eu K statics fr p qf) := by
  have dflt : ∀ o ∈ originsCN K fr statics p (cellsOf (p.fields ++ qf)),
      ∀ c ∈ cellsOf (p.fields ++ qf), ∀ o' ∈ adefault K o c,
        o' ∈ originsCN K fr statics p (cellsOf (p.fields ++ qf)) := by
    intro o ho c hc o' ho'
    rw [mem_originsCN] at ho ⊢
    rcases ho with ⟨b, hb, ⟨q, hq, rfl⟩ | rfl⟩ | ⟨s, hs, rfl | rfl⟩ |
        ⟨s, hs, c0, hc0, ⟨q, hq, rfl⟩ | rfl⟩
    · simp only [adefault, symOrDeep, List.mem_singleton] at ho'
      obtain ⟨_, hcq⟩ := mem_pathsUpTo.mp hq
      split at ho'
      · rename_i hl2
        subst ho'
        refine Or.inl ⟨b, hb, Or.inl ⟨q ++ [c], mem_pathsUpTo.mpr ⟨hl2, ?_⟩, rfl⟩⟩
        intro d hd
        rcases List.mem_append.mp hd with hd | hd
        · exact hcq d hd
        · rw [List.mem_singleton.mp hd]; exact hc
      · subst ho'; exact Or.inl ⟨b, hb, Or.inr rfl⟩
    · simp only [adefault, List.mem_singleton] at ho'
      subst ho'; exact Or.inl ⟨b, hb, Or.inr rfl⟩
    · simp [rNew, adefault] at ho'
    · simp [rOld, adefault] at ho'
    · simp only [adefault, List.mem_singleton] at ho'
      obtain ⟨_, hq2⟩ := mem_pathsUpTo.mp hq
      split at ho'
      · rename_i hl
        subst ho'
        refine Or.inr (Or.inr ⟨s, hs, c0, hc0, Or.inl ⟨q ++ [c], mem_pathsUpTo.mpr ⟨hl, ?_⟩, rfl⟩⟩)
        intro d hd
        rcases List.mem_append.mp hd with hd | hd
        · exact hq2 d hd
        · rw [List.mem_singleton.mp hd]; exact hc
      · subst ho'; exact Or.inr (Or.inr ⟨s, hs, c0, hc0, Or.inr rfl⟩)
    · simp only [adefault, List.mem_singleton] at ho'
      subst ho'; exact Or.inr (Or.inr ⟨s, hs, c0, hc0, Or.inr rfl⟩)
  have allocMem : ∀ a, Origin.alloc a ∈ originsCN K fr statics p (cellsOf (p.fields ++ qf)) →
      ∃ s ∈ p.newSites, Origin.alloc a = rNew s ∨ Origin.alloc a = rOld s := by
    intro a h
    rcases mem_originsCN.mp h with ⟨b, _, ⟨q, _, e⟩ | e⟩ | h | ⟨s, _, c, _, ⟨q, _, e⟩ | e⟩
    · cases e
    · cases e
    · exact h
    · cases e
    · cases e
  refine ⟨⟨⟨elem_mem_cellsOf _, dflt⟩, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro s h
    obtain ⟨s', hs', e⟩ := allocMem _ h
    show rOld s ∈ originsCN K fr statics p _
    rw [mem_originsCN]
    refine Or.inr (Or.inl ⟨s', hs', Or.inr ?_⟩)
    rcases e with e | e
    · rw [rNew_inj e]
    · exact absurd e.symm (rOld_ne_rNew s' s)
  · intro s h
    obtain ⟨s', hs', e⟩ := allocMem _ h
    show rNew s ∈ originsCN K fr statics p _
    rw [mem_originsCN]
    refine Or.inr (Or.inl ⟨s', hs', Or.inl ?_⟩)
    rcases e with e | e
    · exact absurd e (rOld_ne_rNew s s')
    · have : @Eq Nat (2 * s + 1) (2 * s' + 1) := Origin.alloc.inj e
      have hs : s = s' := by show @Eq Nat s s'; omega
      rw [hs]
  · intro s h
    rcases mem_originsCN.mp h with ⟨b, _, ⟨q, _, e⟩ | e⟩ | ⟨_, _, e | e⟩ | ⟨_, _, _, _, ⟨q, _, e⟩ | e⟩
      <;> cases e
  · intro a ha c hc
    cases a with
    | alloc x =>
      obtain ⟨s, hs, e⟩ := allocMem _ ha
      have hk : keyOfR (.alloc x) = rOld s := by
        rcases e with e | e <;> rw [e]
        · exact keyOfR_rNew s
        · exact keyOfR_rOld s
      show Origin.hsym 0 (keyOfR (.alloc x)) c [] ∈ originsCN K fr statics p _
      rw [hk, mem_originsCN]
      exact Or.inr (Or.inr ⟨s, hs, c, hc, Or.inl ⟨[],
        mem_pathsUpTo.mpr ⟨Nat.zero_le _, fun _ h => by cases h⟩, rfl⟩⟩)
    | sym b q => exact dflt _ ha c hc _ (List.mem_singleton.mpr rfl)
    | deep b => exact dflt _ ha c hc _ (List.mem_singleton.mpr rfl)
    | havoc s => exact dflt _ ha c hc _ (List.mem_singleton.mpr rfl)
    | hsym s k c' q => exact dflt _ ha c hc _ (List.mem_singleton.mpr rfl)
    | hdeep s k c' => exact dflt _ ha c hc _ (List.mem_singleton.mpr rfl)
  · intro b q c h
    rcases mem_originsCN.mp h with ⟨b', hb, ⟨q', hq, e⟩ | e⟩ | ⟨_, _, e | e⟩ |
        ⟨_, _, _, _, ⟨_, _, e⟩ | e⟩ <;> cases e
    obtain ⟨hl, hcs⟩ := mem_pathsUpTo.mp hq
    show _ ∈ originsCN K fr statics p _
    rw [mem_originsCN]
    refine Or.inl ⟨b, hb, Or.inl ⟨q, mem_pathsUpTo.mpr ⟨?_, fun d hd => hcs d
      (List.mem_append.mpr (Or.inl hd))⟩, rfl⟩⟩
    rw [List.length_append] at hl
    omega
  · intro b q h
    rcases mem_originsCN.mp h with ⟨b', hb, ⟨q', hq, e⟩ | e⟩ | ⟨_, _, e | e⟩ |
        ⟨_, _, _, _, ⟨_, _, e⟩ | e⟩ <;> cases e
    show _ ∈ originsCN K fr statics p _
    rw [mem_originsCN]
    exact Or.inl ⟨b, hb, Or.inl ⟨[], mem_pathsUpTo.mpr ⟨Nat.zero_le _, fun _ h => by cases h⟩,
      rfl⟩⟩
  · exact List.mem_cons_self

/-- The frame fits the context of design CN of a program. -/
theorem ctxCN_frame (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (qf : List Field) : FrameOK (ctxCN eu K statics fr p qf).ctx fr where
  vars x hx := by
    show x ∈ freshVar _ :: (p.vars ++ fr.vars).eraseDups
    exact List.mem_cons_of_mem _ (List.mem_eraseDups.mpr (List.mem_append.mpr (Or.inr hx)))
  roots x r he := by
    show _ ∈ originsCN K fr statics p _
    rw [mem_originsCN]
    refine Or.inl ⟨.root r, List.mem_append.mpr (Or.inl ?_), Or.inl ⟨[], ?_, rfl⟩⟩
    · exact List.mem_map.mpr ⟨r, List.mem_append.mpr (Or.inl (lookup_mem he).2), rfl⟩
    · exact mem_pathsUpTo.mpr ⟨Nat.zero_le _, fun _ h => by cases h⟩

/-- Each statement of a program fits the context of design CN of the program. -/
theorem ctxCN_stmts (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (qf : List Field) : ∀ st ∈ p.stmts, StmtOKN (ctxCN eu K statics fr p qf) st := by
  intro st hst
  have hpv : ∀ v ∈ st.vars, v ∈ (p.vars ++ fr.vars).eraseDups := fun v hv =>
    List.mem_eraseDups.mpr (List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr ⟨st, hst, hv⟩)))
  refine ⟨fun v hv => List.mem_cons_of_mem _ (hpv v hv), ?_, ?_, ?_, ?_⟩
  · intro v hv e
    have := lt_freshVar (hpv v hv)
    have e' : v = freshVar ((p.vars ++ fr.vars).eraseDups) := e
    rw [e'] at this
    exact Nat.lt_irrefl _ this
  · intro f hf
    exact fld_mem_cellsOf (List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr ⟨st, hst, hf⟩)))
  · intro s hs
    show _ ∈ originsCN K fr statics p _
    rw [mem_originsCN]
    exact Or.inr (Or.inl ⟨s, List.mem_filterMap.mpr ⟨st, hst, hs⟩, Or.inl rfl⟩)
  · intro s hs
    show _ ∈ originsCN K fr statics p _
    rw [mem_originsCN]
    refine Or.inl ⟨.fresh s, List.mem_append.mpr (Or.inr ?_), Or.inl ⟨[], ?_, rfl⟩⟩
    · exact List.mem_map.mpr ⟨s, List.mem_filterMap.mpr ⟨st, hst, hs⟩, rfl⟩
    · exact mem_pathsUpTo.mpr ⟨Nat.zero_le _, fun _ h => by cases h⟩

/-- The once budget of a program holds at the entry state for the context of design CN. -/
theorem ctxCN_budget (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (qf : List Field) : Budget (ctxCN eu K statics fr p qf).ctx p (CState.init fr) := by
  intro t ht
  simp only [ctxCN, Prog.onceB, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at ht
  refine ⟨by simp only [CState.init]; omega, fun hm => ?_⟩
  have := List.contains_iff_mem.mpr hm
  rw [ht.2] at this; cases this

/-! ## Soundness -/

/-- SOUNDNESS OF DESIGN CN under strict narrow A2, for each naming `src`, each set of static
roots, each depth limit and both strong-update policies: each strict narrow one-execution
alias is a may-alias of `mayProgCN`. -/
theorem csoundCN (src : Nat → Obj × Cell) (statics : List Root) (eu : Bool) (K : Nat)
    (fr : Frame) (p : Prog) (x : Var) (px : List Cell) (y : Var) (py : List Cell)
    (h : CAliasN src statics fr p x px y py) :
    mayProgCN eu K statics fr p x (px.map Cell.abs) y (py.map Cell.abs) = true := by
  obtain ⟨st, hx, o, h1, h2⟩ := h
  let qf := afields (px.map Cell.abs) ++ afields (py.map Cell.abs)
  obtain ⟨N, hinv, _, _⟩ := analyze_soundCN (src := src) (ctxCN_ok eu K statics fr p qf) p
    (ctxCN_stmts eu K statics fr p qf) (ctxCN_budget eu K statics fr p qf)
    (inv_initCN (ctxCN_ok eu K statics fr p qf) (ctxCN_frame eu K statics fr p qf)) hx
  have hcx := query_cells (cells := p.fields) qf (fun a ha => List.mem_append.mpr (Or.inl ha))
  have hcy := query_cells (cells := p.fields) qf (fun a ha => List.mem_append.mpr (Or.inr ha))
  exact may_iff.mpr ⟨_, hinv.evalPath_sound hcx h1, hinv.evalPath_sound hcy h2⟩

/-- Under strict narrow A2, no execution aliases two paths for which `mayProgCN` answers
false. -/
theorem no_alias_of_mayProgCN (src : Nat → Obj × Cell) (statics : List Root) (eu : Bool)
    (K : Nat) (fr : Frame) (p : Prog) (x : Var) (px : List Cell) (y : Var) (py : List Cell)
    (h : mayProgCN eu K statics fr p x (px.map Cell.abs) y (py.map Cell.abs) = false) :
    ¬ CAliasN src statics fr p x px y py := by
  intro ha
  have := csoundCN src statics eu K fr p x px y py ha
  rw [h] at this; cases this

end DirectedAlias.Sound.CellNamed

import DirectedAlias.Sound.HavocRecency.Concept

/-!
# Soundness of recency with per-cell havoc under strict A2

The invariant is the generic invariant `InvG` (`Inv.lean`) with the abstraction `alphaRS`.
The proof is the recency proof (`Sound/Recency`) with the per-cell havoc call of
`Sound/Havoc`. The main theorem is `csoundHR`: for each naming `src`, each depth limit and
both strong-update policies, each strict one-execution alias is a may-alias of `mayProgHR`.
-/

namespace DirectedAlias.Sound.HavocRecency

open DirectedAlias DirectedAlias.Sound DirectedAlias.Sound.Recency DirectedAlias.Sound.Havoc

variable {src : Nat → Obj × Cell}

/-- A statement fits the universe of a recency context with per-cell havoc: the recency
facts, and the per-cell havoc origin with the recency key of each universe cell of each
universe origin is in the universe. -/
structure StmtOKRH (ctx : Ctx) (st : Stmt) : Prop where
  ok : StmtOKR ctx st
  callH : ∀ s, st.callSite? = some s → ∀ a ∈ ctx.origins, ∀ c ∈ ctx.cells,
    Origin.hsym s (keyOfR a) c [] ∈ ctx.origins

/-! ## The call -/

/-- LOCAL SOUNDNESS OF THE CALL: the per-cell weak havoc with recency keys keeps the
invariant for each strict havoc. -/
theorem InvG.havocHR {ctx : Ctx} {st : CState} {X : AState} {args : List Var} {s n : Nat}
    {h' : Heap} (h : InvG ctx (alphaRS ctx.K src) st X) (hargs : ∀ a ∈ args, a ∈ ctx.vars)
    (hs : ∀ a ∈ ctx.origins, ∀ c ∈ ctx.cells, Origin.hsym s (keyOfR a) c [] ∈ ctx.origins)
    (hh : HavocS src st args s n h') :
    InvG ctx (alphaRS ctx.K src) { st with heap := h' } (havocHR ctx X args s) where
  outside := h.outside
  envOk := h.envOk
  heapLive o c o' hd he := by
    rcases hh o c with e | ⟨_, k, _, e⟩
    · exact h.heapLive o c o' hd (e ▸ he)
    · change h' o c = some o' at he
      rw [e] at he; cases he; simp [Dead]
  heapIn o c o' hd hin hc he := by
    rcases hh o c with e | ⟨_, k, hk, e⟩
    · exact h.heapIn o c o' hd hin hc (e ▸ he)
    · change h' o c = some o' at he
      rw [e] at he; cases he
      rw [alphaRS_head ctx.K _ hk]
      exact hs _ hin _ hc
  allocHeld o c a m he := by
    rcases hh o c with e | ⟨_, k, _, e⟩
    · exact h.allocHeld o c a m (e ▸ he)
    · change h' o c = some (.alloc a m) at he
      rw [e] at he; cases he
  envCr := h.envCr
  heapCr o c a m he := by
    rcases hh o c with e | ⟨_, k, _, e⟩
    · exact h.heapCr o c a m (e ▸ he)
    · change h' o c = some (.alloc a m) at he
      rw [e] at he; cases he
  fresh a m c hm := by
    show h' (.alloc a m) c = none
    rcases hh (.alloc a m) c with e | ⟨hr, _, _⟩
    · rw [e]; exact h.fresh a m c hm
    · have := h.reach_cr hr a m rfl
      change st.cnt a ≤ m at hm
      omega
  env := h.env
  heap o c o' hd hin hc he := by
    show alphaRS ctx.K src st.cnt o' ∈
      (if c.abs ∈ ctx.cells ∧ reachB ctx X args (alphaRS ctx.K src st.cnt o) = true
      then uni [.hsym s (keyOfR (alphaRS ctx.K src st.cnt o)) c.abs []]
        (X.heap (alphaRS ctx.K src st.cnt o) c.abs)
      else X.heap (alphaRS ctx.K src st.cnt o) c.abs)
    rcases hh o c with e | ⟨hr, k, hk, e⟩
    · have := h.heap o c o' hd hin hc (e ▸ he)
      split
      · exact mem_uni.mpr (Or.inr this)
      · exact this
    · change h' o c = some o' at he
      rw [e] at he; cases he
      rw [ite_eq_left ⟨hc, h.reachB_of_reach (alphaRS_sym_outer _ _) hargs hr⟩,
        alphaRS_head ctx.K _ hk]
      exact mem_uni.mpr (Or.inl (List.mem_singleton.mpr rfl))

/-! ## One statement -/

/-- Local soundness of recency with per-cell havoc: one strict step keeps the invariant. -/
theorem step_soundHR {ctx : Ctx} (hc : CtxROK ctx) {st : Stmt} {s s' : CState} {X : AState}
    (hok : StmtOKRH ctx st) (hb : Budget ctx (.stmt st) s)
    (h : InvG ctx (alphaRS ctx.K src) s X) (hs : SStepS src st s s') :
    InvG ctx (alphaRS ctx.K src) s' (astepHR ctx st X) := by
  have hbump : ∀ (t : CState) (a : Site) (o : Obj), o ≠ .alloc a (t.cnt a) →
      alphaRS ctx.K src (t.bump a).cnt o = renameO a (alphaRS ctx.K src t.cnt o) :=
    fun t a _ ho => alphaRS_bump ctx.K src t a ho
  cases hs with
  | @new x a =>
    have h1 := InvG.retire hc a (hbump s a) h
    show InvG ctx (alphaRS ctx.K src) ((s.bump a).setVar x (some (.alloc a (s.cnt a))))
      ((retire a X).setVar x [rNew a])
    refine InvG.setVar h1 (hok.ok.vars x (by simp [Stmt.vars])) ?_ ?_
    · intro o e
      cases e
      rw [alphaRS_new]
      refine ⟨?_, hok.ok.newS a rfl, List.mem_singleton.mpr rfl⟩
      rintro ⟨ho, hn⟩
      have := Budget.stmt_site hb rfl ho
      omega
    · intro a' n e
      cases e
      show s.cnt a < fupd s.cnt a (s.cnt a + 1) a
      rw [fupd_same]; exact Nat.lt_succ_self _
  | @null x =>
    exact InvG.setVar h (hok.ok.vars x (by simp [Stmt.vars])) (fun o e => by cases e)
      (fun _ _ e => by cases e)
  | @copy x y =>
    refine InvG.setVar h (hok.ok.vars x (by simp [Stmt.vars])) ?_ (fun a n e => h.envCr y a n e)
    intro o e
    exact ⟨(h.envOk y o e).1, (h.envOk y o e).2, h.env y (hok.ok.vars y (by simp [Stmt.vars])) o e⟩
  | @load x y f _ o he =>
    refine InvG.setVar h (hok.ok.vars x (by simp [Stmt.vars])) ?_ (fun a n e => h.heapCr _ _ a n e)
    intro o' e
    have hd := h.envOk y o he
    have hf : (Cell.fld f).abs ∈ ctx.cells := hok.ok.fields f (by simp [Stmt.fields])
    exact ⟨h.heapLive o _ o' hd.1 e, h.heapIn o _ o' hd.1 hd.2 hf e,
      mem_aread.mpr ⟨_, h.env y (hok.ok.vars y (by simp [Stmt.vars])) o he,
        h.heap o _ o' hd.1 hd.2 hf e⟩⟩
  | @aload x y _ o i he =>
    refine InvG.setVar h (hok.ok.vars x (by simp [Stmt.vars])) ?_ (fun a n e => h.heapCr _ _ a n e)
    intro o' e
    have hd := h.envOk y o he
    have hf : (Cell.elem i).abs ∈ ctx.cells := hc.base.elem
    exact ⟨h.heapLive o _ o' hd.1 e, h.heapIn o _ o' hd.1 hd.2 hf e,
      mem_aread.mpr ⟨_, h.env y (hok.ok.vars y (by simp [Stmt.vars])) o he,
        h.heap o _ o' hd.1 hd.2 hf e⟩⟩
  | @store x f y _ o he =>
    have hd := h.envOk x o he
    have hx := h.env x (hok.ok.vars x (by simp [Stmt.vars])) o he
    have hf : ACell.fld f ∈ ctx.cells := hok.ok.fields f (by simp [Stmt.fields])
    have hocr : ∀ a n, o = .alloc a n → n < s.cnt a := fun a n e => h.envCr x a n (e ▸ he)
    have hv : ∀ o', s.env y = some o' → ¬ Dead ctx.once o' ∧
        alphaRS ctx.K src s.cnt o' ∈ ctx.origins ∧ alphaRS ctx.K src s.cnt o' ∈ X.env y :=
      fun o' e => ⟨(h.envOk y o' e).1, (h.envOk y o' e).2,
        h.env y (hok.ok.vars y (by simp [Stmt.vars])) o' e⟩
    have hvcr : ∀ a n, s.env y = some (.alloc a n) → n < s.cnt a := fun a n e => h.envCr y a n e
    show InvG ctx (alphaRS ctx.K src) _ (storeR ctx X x (.fld f) (X.env y))
    unfold storeR
    split
    · rename_i oa hsingle
      have hoa : alphaRS ctx.K src s.cnt o = oa := (single?_spec hsingle).2 _ hx
      split
      · rename_i hu
        rw [← hoa] at hu ⊢
        exact InvG.strong h hd hocr hf (fun o1 hd1 ha => unique_objRS hu hd.1 hd1 ha) hv hvcr
      · exact InvG.weak (c := .fld f) h hd hocr hf hx hv hvcr
    · exact InvG.weak (c := .fld f) h hd hocr hf hx hv hvcr
  | @astore x y _ o i he =>
    have hd := h.envOk x o he
    have hx := h.env x (hok.ok.vars x (by simp [Stmt.vars])) o he
    exact InvG.weak (c := .elem i) h hd (fun a n e => h.envCr x a n (e ▸ he)) hc.base.elem hx
      (fun o' e => ⟨(h.envOk y o' e).1, (h.envOk y o' e).2,
        h.env y (hok.ok.vars y (by simp [Stmt.vars])) o' e⟩) (fun a n e => h.envCr y a n e)
  | @unknown x a =>
    have h1 := InvG.retire hc a (hbump s a) h
    show InvG ctx (alphaRS ctx.K src) ((s.bump a).setVar x (some (.sym (.fresh a (s.cnt a)) [])))
      ((retire a X).setVar x [.sym (.fresh a) []])
    refine InvG.setVar h1 (hok.ok.vars x (by simp [Stmt.vars])) ?_ (fun _ _ e => by cases e)
    intro o e
    cases e
    rw [alphaRS_fresh]
    refine ⟨?_, hok.ok.freshS a rfl, List.mem_singleton.mpr rfl⟩
    rintro ⟨ho, hn⟩
    have := Budget.stmt_site hb rfl ho
    omega
  | @call ret a args _ h' hh =>
    have hargs : ∀ v ∈ args, v ∈ ctx.vars := fun v hv => hok.ok.vars v (by simp [Stmt.vars, hv])
    have h1 := InvG.havocHR h hargs (hok.callH a rfl) hh
    have h2 := InvG.retire hc a (hbump { s with heap := h' } a) h1
    show InvG ctx (alphaRS ctx.K src) _
      ((retire a (havocHR ctx X args a)).setRet ret [.sym (.fresh a) []])
    cases ret with
    | none => exact h2
    | some x =>
      show InvG ctx (alphaRS ctx.K src)
        (({ s with heap := h' }.bump a).setVar x (some (.sym (.fresh a (s.cnt a)) [])))
        ((retire a (havocHR ctx X args a)).setVar x [.sym (.fresh a) []])
      refine InvG.setVar h2 (hok.ok.vars x (by simp [Stmt.vars])) ?_ (fun _ _ e => by cases e)
      intro o e
      cases e
      rw [alphaRS_fresh]
      refine ⟨?_, hok.ok.freshS a rfl, List.mem_singleton.mpr rfl⟩
      rintro ⟨ho, hn⟩
      have := Budget.stmt_site hb rfl ho
      omega

/-! ## Programs -/

/-- Soundness of `analyzeHR`: each strict execution ends in a state that the analysis result
simulates. -/
theorem analyze_soundHR (ctx : Ctx) (hc : CtxROK ctx) :
    ∀ (q : Prog) {s s' : CState} {X : AState}, (∀ st ∈ q.stmts, StmtOKRH ctx st) →
      Budget ctx q s → InvG ctx (alphaRS ctx.K src) s X → ExecS src q s s' →
      InvG ctx (alphaRS ctx.K src) s' (analyzeHR ctx q X) := by
  intro q
  induction q with
  | skip => intro s s' X _ _ h hx; cases hx; exact h
  | stmt st =>
    intro s s' X hok hb h hx
    cases hx with
    | stmt hs => exact step_soundHR hc (hok st (List.mem_singleton.mpr rfl)) hb h hs
  | seq p q ihp ihq =>
    intro s s' X hok hb h hx
    cases hx with
    | seq h1 h2 =>
      have hokp : ∀ st ∈ p.stmts, StmtOKRH ctx st :=
        fun st hs => hok st (List.mem_append.mpr (Or.inl hs))
      have hokq : ∀ st ∈ q.stmts, StmtOKRH ctx st :=
        fun st hs => hok st (List.mem_append.mpr (Or.inr hs))
      exact ihq hokq (Budget.seqR hb h1.toExec) (ihp hokp (Budget.seqL hb) h h1) h2
  | choice p q ihp ihq =>
    intro s s' X hok hb h hx
    have hokp : ∀ st ∈ p.stmts, StmtOKRH ctx st :=
      fun st hs => hok st (List.mem_append.mpr (Or.inl hs))
    have hokq : ∀ st ∈ q.stmts, StmtOKRH ctx st :=
      fun st hs => hok st (List.mem_append.mpr (Or.inr hs))
    cases hx with
    | choiceL h1 => exact (ihp hokp (Budget.choiceL hb) h h1).mono (sub_join_left _ _)
    | choiceR h1 => exact (ihq hokq (Budget.choiceR hb) h h1).mono (sub_join_right _ _)
  | loop body ih =>
    intro s s' X hok hb h hx
    show InvG ctx (alphaRS ctx.K src) s' (loopIter ctx (analyzeHR ctx body) ctx.fuel X)
    have hY := h.mono (sub_loopIter ctx (analyzeHR ctx body) ctx.fuel X)
    refine loop_keepsG (Budget ctx (.loop body)) ?_ hx hb hY
    intro s1 t hb1 hi1 hx1
    refine ⟨Budget.again hb1 hx1.toExec, ?_⟩
    have hf := ih hok (Budget.body hb1) hi1 hx1
    rcases loopIter_post ctx (analyzeHR ctx body) ctx.fuel X with hpost | ⟨W, hW⟩
    · exact hf.mono_leOn hpost
    · rw [hW]; exact hf.top W

/-- The entry states satisfy the invariant of recency with per-cell havoc. -/
theorem inv_initHR {ctx : Ctx} (hc : CtxOK ctx) {fr : Frame} (hf : FrameOK ctx fr) :
    InvG ctx (alphaRS ctx.K src) (CState.init fr) (ainit ctx.K fr) where
  outside x hx := by
    show (fr.root? x).map _ = none
    cases e : fr.root? x with
    | none => rfl
    | some r => exact absurd (hf.vars x (lookup_mem e).1) hx
  envOk x o he := by
    change (fr.root? x).map _ = some o at he
    cases e : fr.root? x with
    | none => rw [e] at he; cases he
    | some r =>
      rw [e] at he; cases he
      refine ⟨by simp [Dead], ?_⟩
      rw [alphaRS_root]
      exact hf.roots x r e
  heapLive o c o' hd hh := by
    change cdefault o c = some o' at hh
    cases o with
    | alloc s n => cases hh
    | sym b p => cases hh; cases b <;> simp_all [Dead]
  heapIn o c o' _ hin hc1 hh := by
    change cdefault o c = some o' at hh
    exact hc.dflt _ hin _ hc1 _ (alphaRS_cdefault ctx.K src _ hh)
  allocHeld o c s n hh := by
    change cdefault o c = some (.alloc s n) at hh
    cases o with
    | alloc _ _ => cases hh
    | sym _ _ => cases hh
  envCr x s n he := by
    change (fr.root? x).map _ = _ at he
    cases e : fr.root? x with
    | none => rw [e] at he; cases he
    | some r => rw [e] at he; cases he
  heapCr o c s n he := by
    change cdefault o c = _ at he
    cases o with
    | sym _ _ => cases he
    | alloc _ _ => cases he
  fresh _ _ _ _ := rfl
  env x _ o he := by
    change (fr.root? x).map _ = some o at he
    show alphaRS ctx.K src (CState.init fr).cnt o ∈ (match fr.root? x with
      | some r => [Origin.sym (.root r) []] | none => [])
    cases e : fr.root? x with
    | none => rw [e] at he; cases he
    | some r =>
      rw [e] at he; cases he
      rw [alphaRS_root]
      exact List.mem_singleton.mpr rfl
  heap o c o' _ _ _ hh := by
    change cdefault o c = some o' at hh
    exact alphaRS_cdefault ctx.K src _ hh

/-! ## The universe of a program -/

/-- Membership in the keys of the recency universe. -/
theorem mem_keysR {K : Nat} {fr : Frame} {p : Prog} {cells : List ACell} {o : Origin} :
    o ∈ keysR K fr p cells ↔
      (∃ b ∈ fr.roots.map ABase.root ++ p.freshSites.map ABase.fresh,
        (∃ q ∈ pathsUpTo cells K, o = .sym b q) ∨ o = .deep b) ∨
      (∃ s ∈ p.newSites, o = rOld s) ∨ (∃ s ∈ p.callSites, o = .havoc s) := by
  simp only [keysR, List.mem_append, List.mem_flatMap, List.mem_map,
    List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ((⟨b, hb, ⟨q, hq, rfl⟩ | rfl⟩ | ⟨s, hs, rfl⟩) | ⟨s, hs, rfl⟩)
    · exact Or.inl ⟨b, hb, Or.inl ⟨q, hq, rfl⟩⟩
    · exact Or.inl ⟨b, hb, Or.inr rfl⟩
    · exact Or.inr (Or.inl ⟨s, hs, rfl⟩)
    · exact Or.inr (Or.inr ⟨s, hs, rfl⟩)
  · rintro (⟨b, hb, ⟨q, hq, rfl⟩ | rfl⟩ | ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
    · exact Or.inl (Or.inl ⟨b, hb, Or.inl ⟨q, hq, rfl⟩⟩)
    · exact Or.inl (Or.inl ⟨b, hb, Or.inr rfl⟩)
    · exact Or.inl (Or.inr ⟨s, hs, rfl⟩)
    · exact Or.inr ⟨s, hs, rfl⟩

/-- The recency key of each origin of the universe is a key of the recency universe. -/
theorem keyOfR_mem {K : Nat} {fr : Frame} {p : Prog} {cells : List ACell} {a : Origin}
    (h : a ∈ originsHR K fr p cells) : keyOfR a ∈ keysR K fr p cells := by
  rcases List.mem_append.mp h with h | h
  · rcases mem_originsR.mp h with ⟨b, hb, ⟨q, hq, rfl⟩ | rfl⟩ | ⟨s, hs, rfl | rfl⟩ | ⟨s, hs, rfl⟩
    · exact mem_keysR.mpr (Or.inl ⟨b, hb, Or.inl ⟨q, hq, rfl⟩⟩)
    · exact mem_keysR.mpr (Or.inl ⟨b, hb, Or.inr rfl⟩)
    · rw [keyOfR_rNew]; exact mem_keysR.mpr (Or.inr (Or.inl ⟨s, hs, rfl⟩))
    · rw [keyOfR_rOld]; exact mem_keysR.mpr (Or.inr (Or.inl ⟨s, hs, rfl⟩))
    · exact mem_keysR.mpr (Or.inr (Or.inr ⟨s, hs, rfl⟩))
  · obtain ⟨s, hs, _, _, _, _, ⟨q, _, rfl⟩ | rfl⟩ := mem_havocCells.mp h <;>
    · exact mem_keysR.mpr (Or.inr (Or.inr ⟨s, hs, rfl⟩))

/-- An allocation origin of the universe is in the recency universe. -/
theorem alloc_mem_originsHR {K : Nat} {fr : Frame} {p : Prog} {cells : List ACell} {a : Nat}
    (h : Origin.alloc a ∈ originsHR K fr p cells) : Origin.alloc a ∈ originsR K fr p cells := by
  rcases List.mem_append.mp h with h | h
  · exact h
  · obtain ⟨_, _, _, _, _, _, ⟨q, _, e⟩ | e⟩ := mem_havocCells.mp h <;> cases e

/-- The recency context with per-cell havoc of a program is closed. -/
theorem ctxHR_ok (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    CtxROK (ctxHR eu K fr p qf) where
  base := {
    elem := (ctxR_ok eu K fr p qf).base.elem
    dflt := fun o ho c hc o' ho' => by
      rcases List.mem_append.mp ho with ho | ho
      · exact List.mem_append_left _ ((ctxR_ok eu K fr p qf).base.dflt o ho c hc o' ho')
      · apply List.mem_append_right
        obtain ⟨s, hs, a, ha, c0, hc0, ⟨q, hq, rfl⟩ | rfl⟩ := mem_havocCells.mp ho
        · simp only [adefault, List.mem_singleton] at ho'
          obtain ⟨_, hq2⟩ := mem_pathsUpTo.mp hq
          apply mem_havocCells.mpr
          refine ⟨s, hs, a, ha, c0, hc0, ?_⟩
          split at ho'
          · rename_i hl
            refine Or.inl ⟨q ++ [c], mem_pathsUpTo.mpr ⟨hl, ?_⟩, ho'⟩
            intro d hd
            rcases List.mem_append.mp hd with hd | hd
            · exact hq2 d hd
            · rw [List.mem_singleton.mp hd]; exact hc
          · exact Or.inr ho'
        · simp only [adefault, List.mem_singleton] at ho'
          exact mem_havocCells.mpr ⟨s, hs, a, ha, c0, hc0, Or.inr ho'⟩ }
  newOld s h :=
    List.mem_append_left _ ((ctxR_ok eu K fr p qf).newOld s (alloc_mem_originsHR h))
  oldNew s h :=
    List.mem_append_left _ ((ctxR_ok eu K fr p qf).oldNew s (alloc_mem_originsHR h))

/-- The frame fits the recency context with per-cell havoc of a program. -/
theorem ctxHR_frame (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    FrameOK (ctxHR eu K fr p qf) fr where
  vars := (ctxR_frame eu K fr p qf).vars
  roots x r he := List.mem_append_left _ ((ctxR_frame eu K fr p qf).roots x r he)

/-- Each statement of a program fits the recency context with per-cell havoc. -/
theorem ctxHR_stmts (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    ∀ st ∈ p.stmts, StmtOKRH (ctxHR eu K fr p qf) st := by
  intro st hst
  have h0 := ctxR_stmts eu K fr p qf st hst
  refine ⟨⟨h0.vars, h0.fields, fun s hs => List.mem_append_left _ (h0.newS s hs),
    fun s hs => List.mem_append_left _ (h0.freshS s hs),
    fun s hs => List.mem_append_left _ (h0.callS s hs)⟩, ?_⟩
  intro s hs a ha c hc
  apply List.mem_append_right
  refine mem_havocCells.mpr ⟨s, List.mem_filterMap.mpr ⟨st, hst, hs⟩, keyOfR a, keyOfR_mem ha,
    c, hc, Or.inl ⟨[], mem_pathsUpTo.mpr ⟨Nat.zero_le _, fun _ h => by cases h⟩, rfl⟩⟩

/-- The once budget of a program holds at the entry state for the recency context with
per-cell havoc. -/
theorem ctxHR_budget (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    Budget (ctxHR eu K fr p qf) p (CState.init fr) :=
  ctxR_budget eu K fr p qf

/-! ## Soundness -/

/-- Soundness of recency with per-cell havoc under strict A2, for each naming `src`, each
depth limit and both strong-update policies: each strict one-execution alias is a may-alias
of `mayProgHR`. -/
theorem csoundHR (src : Nat → Obj × Cell) (eu : Bool) (K : Nat) (fr : Frame) (p : Prog)
    (x : Var) (px : List Cell) (y : Var) (py : List Cell) (h : CAliasS src fr p x px y py) :
    mayProgHR eu K fr p x (px.map Cell.abs) y (py.map Cell.abs) = true := by
  obtain ⟨st, hx, o, h1, h2⟩ := h
  let qf := afields (px.map Cell.abs) ++ afields (py.map Cell.abs)
  have hinv := analyze_soundHR _ (ctxHR_ok eu K fr p qf) p (ctxHR_stmts eu K fr p qf)
    (ctxHR_budget eu K fr p qf) (inv_initHR (src := src) (ctxHR_ok eu K fr p qf).base
      (ctxHR_frame eu K fr p qf)) hx
  have hcx := query_cells (cells := p.fields) qf (fun a ha => List.mem_append.mpr (Or.inl ha))
  have hcy := query_cells (cells := p.fields) qf (fun a ha => List.mem_append.mpr (Or.inr ha))
  exact may_iff.mpr ⟨_, hinv.evalPath_sound hcx h1, hinv.evalPath_sound hcy h2⟩

/-- Under strict A2, no execution aliases two paths for which `mayProgHR` answers false. -/
theorem no_alias_of_mayProgHR (src : Nat → Obj × Cell) (eu : Bool) (K : Nat) (fr : Frame)
    (p : Prog) (x : Var) (px : List Cell) (y : Var) (py : List Cell)
    (h : mayProgHR eu K fr p x (px.map Cell.abs) y (py.map Cell.abs) = false) :
    ¬ CAliasS src fr p x px y py := by
  intro ha
  have := csoundHR src eu K fr p x px y py ha
  rw [h] at this; cases this

end DirectedAlias.Sound.HavocRecency

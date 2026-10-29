import DirectedAlias.Sound.Recency.Step

/-!
# Soundness of the recency refinement

`csoundR` proves: each one-execution alias is a may-alias of the recency analysis,
for both strong-update policies (`entryUnique`).
-/

namespace DirectedAlias.Sound.Recency

open DirectedAlias DirectedAlias.Sound

/-! ## Calls -/

/-- A reachable allocation exists. -/
theorem reach_alloc_cr {ctx : Ctx} {st : CState} {X : AState} {args : List Var}
    (h : InvR ctx st X) {o : Obj} (hr : Reach st args o) :
    ∀ a n, o = .alloc a n → n < st.cnt a := by
  induction hr with
  | outer => intro a n e; cases e
  | arg _ he => intro a n e; subst e; exact h.envCr _ a n he
  | step _ hh _ => intro a n e; subst e; exact h.heapCr _ _ a n hh

/-- Each object that a call can reach has an origin for which `reachB` is true. -/
theorem reachB_of_reachR {ctx : Ctx} {st : CState} {X : AState} {args : List Var} {o : Obj}
    (h : InvR ctx st X) (hargs : ∀ a ∈ args, a ∈ ctx.vars) (hr : Reach st args o) :
    reachB ctx X args (alphaR ctx.K st o) = true := by
  unfold reachB
  cases hR : closeIter ctx.cells X (ctx.origins.length + 1)
      (uni (uniMap X.env args) (ctx.origins.filter Origin.outer)) with
  | none => rfl
  | some R =>
    obtain ⟨hseed, hclosed⟩ := closeIter_spec hR
    have key : (alphaR ctx.K st o).outer = true ∨ alphaR ctx.K st o ∈ R := by
      induction hr with
      | outer => exact Or.inl (alpha_sym_outer _ _ _)
      | arg hx he =>
        exact Or.inr (hseed _ (mem_uni.mpr (Or.inl
          (mem_uniMap.mpr ⟨_, hx, h.env _ (hargs _ hx) _ he⟩))))
      | @step o1 o2 c _ hh ih =>
        cases o2 with
        | sym b p => exact Or.inl (alpha_sym_outer _ _ _)
        | alloc s n =>
          obtain ⟨hd, hin, hc⟩ := h.allocHeld _ _ _ _ hh
          have h1 : alphaR ctx.K st o1 ∈ R := by
            cases ih with
            | inl hout => exact hseed _ (mem_uni.mpr (Or.inr (List.mem_filter.mpr ⟨hin, hout⟩)))
            | inr h => exact h
          exact Or.inr (hclosed _ (mem_succs.mpr ⟨_, h1, _, hc, h.heap _ _ _ hd hin hc hh⟩))
    cases key with
    | inl h1 => simp [h1]
    | inr h1 => simp [h1]

/-- The havoc of a call keeps the recency invariant. -/
theorem InvR.havoc {ctx : Ctx} {st : CState} {X : AState} {args : List Var} {s n : Nat}
    {h' : Heap} (h : InvR ctx st X) (hargs : ∀ a ∈ args, a ∈ ctx.vars)
    (hs : Origin.havoc s ∈ ctx.origins) (hh : Havoc st args s n h') :
    InvR ctx { st with heap := h' } (X.havoc ctx args s) where
  outside := h.outside
  envOk := h.envOk
  heapLive o c o' hd he := by
    rcases hh o c with e | ⟨_, k, e⟩
    · exact h.heapLive o c o' hd (e ▸ he)
    · change h' o c = some o' at he
      rw [e] at he; cases he; simp [Dead]
  heapIn o c o' hd hin hc he := by
    rcases hh o c with e | ⟨_, k, e⟩
    · exact h.heapIn o c o' hd hin hc (e ▸ he)
    · change h' o c = some o' at he
      rw [e] at he; cases he; exact hs
  allocHeld o c a m he := by
    rcases hh o c with e | ⟨_, k, e⟩
    · exact h.allocHeld o c a m (e ▸ he)
    · change h' o c = some (.alloc a m) at he
      rw [e] at he; cases he
  envCr := h.envCr
  heapCr o c a m he := by
    rcases hh o c with e | ⟨_, k, e⟩
    · exact h.heapCr o c a m (e ▸ he)
    · change h' o c = some (.alloc a m) at he
      rw [e] at he; cases he
  fresh a m c hm := by
    show h' (.alloc a m) c = none
    rcases hh (.alloc a m) c with e | ⟨hr, _, _⟩
    · rw [e]; exact h.fresh a m c hm
    · have := reach_alloc_cr h hr a m rfl
      change st.cnt a ≤ m at hm
      omega
  env := h.env
  heap o c o' hd hin hc he := by
    show alphaR ctx.K st o' ∈ (if c.abs ∈ ctx.cells ∧ reachB ctx X args (alphaR ctx.K st o) = true
      then uni [.havoc s] (X.heap (alphaR ctx.K st o) c.abs) else X.heap (alphaR ctx.K st o) c.abs)
    rcases hh o c with e | ⟨hr, k, e⟩
    · have := h.heap o c o' hd hin hc (e ▸ he)
      split
      · exact mem_uni.mpr (Or.inr this)
      · exact this
    · change h' o c = some o' at he
      rw [e] at he; cases he
      rw [if_pos ⟨hc, reachB_of_reachR h hargs hr⟩]
      exact mem_uni.mpr (Or.inl (List.mem_singleton.mpr rfl))

/-! ## One statement -/

/-- Local soundness with recency: one concrete step keeps the invariant. -/
theorem step_soundR {ctx : Ctx} (hc : CtxROK ctx) {st : Stmt} {s s' : CState} {X : AState}
    (hok : StmtOKR ctx st) (hb : Budget ctx (.stmt st) s) (h : InvR ctx s X)
    (hs : SStep st s s') : InvR ctx s' (astepR ctx st X) := by
  cases hs with
  | @new x a =>
    have h1 := retire_inv hc a h
    show InvR ctx ((s.bump a).setVar x (some (.alloc a (s.cnt a)))) ((retire a X).setVar x [rNew a])
    refine InvR.setVar h1 (hok.vars x (by simp [Stmt.vars])) ?_ ?_
    · intro o e
      cases e
      have hr : alphaR ctx.K (s.bump a) (.alloc a (s.cnt a)) = rNew a := by
        show (if s.cnt a + 1 = fupd s.cnt a (s.cnt a + 1) a then rNew a else rOld a) = rNew a
        rw [fupd_same, if_pos rfl]
      rw [hr]
      refine ⟨?_, hok.newS a rfl, List.mem_singleton.mpr rfl⟩
      rintro ⟨ho, hn⟩
      have := Budget.stmt_site hb rfl ho
      omega
    · intro a' n e
      cases e
      show s.cnt a < fupd s.cnt a (s.cnt a + 1) a
      rw [fupd_same]; exact Nat.lt_succ_self _
  | @null x =>
    exact InvR.setVar h (hok.vars x (by simp [Stmt.vars])) (fun o e => by cases e)
      (fun _ _ e => by cases e)
  | @copy x y =>
    refine InvR.setVar h (hok.vars x (by simp [Stmt.vars])) ?_ (fun a n e => h.envCr y a n e)
    intro o e
    exact ⟨(h.envOk y o e).1, (h.envOk y o e).2, h.env y (hok.vars y (by simp [Stmt.vars])) o e⟩
  | @load x y f _ o he =>
    refine InvR.setVar h (hok.vars x (by simp [Stmt.vars])) ?_ (fun a n e => h.heapCr _ _ a n e)
    intro o' e
    have hd := h.envOk y o he
    have hf : (Cell.fld f).abs ∈ ctx.cells := hok.fields f (by simp [Stmt.fields])
    exact ⟨h.heapLive o _ o' hd.1 e, h.heapIn o _ o' hd.1 hd.2 hf e,
      mem_aread.mpr ⟨_, h.env y (hok.vars y (by simp [Stmt.vars])) o he,
        h.heap o _ o' hd.1 hd.2 hf e⟩⟩
  | @aload x y _ o i he =>
    refine InvR.setVar h (hok.vars x (by simp [Stmt.vars])) ?_ (fun a n e => h.heapCr _ _ a n e)
    intro o' e
    have hd := h.envOk y o he
    have hf : (Cell.elem i).abs ∈ ctx.cells := hc.base.elem
    exact ⟨h.heapLive o _ o' hd.1 e, h.heapIn o _ o' hd.1 hd.2 hf e,
      mem_aread.mpr ⟨_, h.env y (hok.vars y (by simp [Stmt.vars])) o he,
        h.heap o _ o' hd.1 hd.2 hf e⟩⟩
  | @store x f y _ o he =>
    have hd := h.envOk x o he
    have hx := h.env x (hok.vars x (by simp [Stmt.vars])) o he
    have hf : ACell.fld f ∈ ctx.cells := hok.fields f (by simp [Stmt.fields])
    have hocr : ∀ a n, o = .alloc a n → n < s.cnt a := fun a n e => h.envCr x a n (e ▸ he)
    have hv : ∀ o', s.env y = some o' → ¬ Dead ctx.once o' ∧ alphaR ctx.K s o' ∈ ctx.origins ∧
        alphaR ctx.K s o' ∈ X.env y := fun o' e =>
      ⟨(h.envOk y o' e).1, (h.envOk y o' e).2, h.env y (hok.vars y (by simp [Stmt.vars])) o' e⟩
    have hvcr : ∀ a n, s.env y = some (.alloc a n) → n < s.cnt a := fun a n e => h.envCr y a n e
    show InvR ctx _ (storeR ctx X x (.fld f) (X.env y))
    unfold storeR
    split
    · rename_i oa hsingle
      have hoa : alphaR ctx.K s o = oa := (single?_spec hsingle).2 _ hx
      split
      · rename_i hu
        rw [← hoa] at hu ⊢
        exact InvR.strong h hd hocr hf (fun o1 hd1 ha => unique_objR hu hd.1 hd1 ha) hv hvcr
      · exact InvR.weak (c := .fld f) h hd hocr hf hx hv hvcr
    · exact InvR.weak (c := .fld f) h hd hocr hf hx hv hvcr
  | @astore x y _ o i he =>
    have hd := h.envOk x o he
    have hx := h.env x (hok.vars x (by simp [Stmt.vars])) o he
    exact InvR.weak (c := .elem i) h hd (fun a n e => h.envCr x a n (e ▸ he)) hc.base.elem hx
      (fun o' e => ⟨(h.envOk y o' e).1, (h.envOk y o' e).2,
        h.env y (hok.vars y (by simp [Stmt.vars])) o' e⟩) (fun a n e => h.envCr y a n e)
  | @unknown x a =>
    have h1 := retire_inv hc a h
    show InvR ctx ((s.bump a).setVar x (some (.sym (.fresh a (s.cnt a)) [])))
      ((retire a X).setVar x [.sym (.fresh a) []])
    refine InvR.setVar h1 (hok.vars x (by simp [Stmt.vars])) ?_ (fun _ _ e => by cases e)
    intro o e
    cases e
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨ho, hn⟩
      have := Budget.stmt_site hb rfl ho
      omega
    · simp only [alphaR_sym, alpha, symOrDeep, List.map_nil, List.length_nil, Nat.zero_le, if_true]
      exact hok.freshS a rfl
    · simp [alphaR_sym, alpha, symOrDeep]
  | @call ret a args _ h' hh =>
    have hargs : ∀ v ∈ args, v ∈ ctx.vars := fun v hv => hok.vars v (by simp [Stmt.vars, hv])
    have h1 := InvR.havoc h hargs (hok.callS a rfl) hh
    have h2 := retire_inv hc a h1
    show InvR ctx _ ((retire a (X.havoc ctx args a)).setRet ret [.sym (.fresh a) []])
    cases ret with
    | none => exact h2
    | some x =>
      show InvR ctx (({ s with heap := h' }.bump a).setVar x (some (.sym (.fresh a (s.cnt a)) [])))
        ((retire a (X.havoc ctx args a)).setVar x [.sym (.fresh a) []])
      refine InvR.setVar h2 (hok.vars x (by simp [Stmt.vars])) ?_ (fun _ _ e => by cases e)
      intro o e
      cases e
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨ho, hn⟩
        have := Budget.stmt_site hb rfl ho
        omega
      · simp only [alphaR_sym, alpha, symOrDeep, List.map_nil, List.length_nil, Nat.zero_le,
          if_true]
        exact hok.freshS a rfl
      · simp [alphaR_sym, alpha, symOrDeep]

/-! ## Programs -/

/-- A loop keeps a recency invariant state `Y` if one run of the body keeps it. -/
theorem loop_keepsR {ctx : Ctx} {body : Prog} {Y : AState} (P : CState → Prop)
    (hstep : ∀ s t, P s → InvR ctx s Y → Exec body s t → P t ∧ InvR ctx t Y) :
    ∀ {s u : CState}, Exec (.loop body) s u → P s → InvR ctx s Y → InvR ctx u Y := by
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

/-- Soundness of `analyzeR`. -/
theorem analyze_soundR (ctx : Ctx) (hc : CtxROK ctx) :
    ∀ (q : Prog) {s s' : CState} {X : AState}, (∀ st ∈ q.stmts, StmtOKR ctx st) →
      Budget ctx q s → InvR ctx s X → Exec q s s' → InvR ctx s' (analyzeR ctx q X) := by
  intro q
  induction q with
  | skip => intro s s' X _ _ h hx; cases hx; exact h
  | stmt st =>
    intro s s' X hok hb h hx
    cases hx with
    | stmt hs => exact step_soundR hc (hok st (List.mem_singleton.mpr rfl)) hb h hs
  | seq p q ihp ihq =>
    intro s s' X hok hb h hx
    cases hx with
    | seq h1 h2 =>
      have hokp : ∀ st ∈ p.stmts, StmtOKR ctx st :=
        fun st hs => hok st (List.mem_append.mpr (Or.inl hs))
      have hokq : ∀ st ∈ q.stmts, StmtOKR ctx st :=
        fun st hs => hok st (List.mem_append.mpr (Or.inr hs))
      exact ihq hokq (Budget.seqR hb h1) (ihp hokp (Budget.seqL hb) h h1) h2
  | choice p q ihp ihq =>
    intro s s' X hok hb h hx
    have hokp : ∀ st ∈ p.stmts, StmtOKR ctx st :=
      fun st hs => hok st (List.mem_append.mpr (Or.inl hs))
    have hokq : ∀ st ∈ q.stmts, StmtOKR ctx st :=
      fun st hs => hok st (List.mem_append.mpr (Or.inr hs))
    cases hx with
    | choiceL h1 => exact (ihp hokp (Budget.choiceL hb) h h1).mono (sub_join_left _ _)
    | choiceR h1 => exact (ihq hokq (Budget.choiceR hb) h h1).mono (sub_join_right _ _)
  | loop body ih =>
    intro s s' X hok hb h hx
    show InvR ctx s' (loopIter ctx (analyzeR ctx body) ctx.fuel X)
    have hY := h.mono (sub_loopIter ctx (analyzeR ctx body) ctx.fuel X)
    refine loop_keepsR (Budget ctx (.loop body)) ?_ hx hb hY
    intro s1 t hb1 hi1 hx1
    refine ⟨Budget.again hb1 hx1, ?_⟩
    have hf := ih hok (Budget.body hb1) hi1 hx1
    rcases loopIter_post ctx (analyzeR ctx body) ctx.fuel X with hpost | ⟨W, hW⟩
    · exact hf.mono_leOn hpost
    · rw [hW]; exact hf.top W

/-- The entry states satisfy the recency invariant. -/
theorem inv_initR {ctx : Ctx} (hc : CtxOK ctx) {fr : Frame} (hf : FrameOK ctx fr) :
    InvR ctx (CState.init fr) (ainit ctx.K fr) := by
  have h := inv_init hc hf
  exact {
    outside := h.outside
    envOk := fun x o he => by
      have := h.envOk x o he
      cases o with
      | sym b p => exact this
      | alloc a n =>
        change (fr.root? x).map _ = _ at he
        cases e : fr.root? x with
        | none => rw [e] at he; cases he
        | some r => rw [e] at he; cases he
    heapLive := h.heapLive
    heapIn := fun o c o' hd hin hc1 hh => by
      change cdefault o c = some o' at hh
      cases o with
      | alloc _ _ => cases hh
      | sym b p => cases hh; exact h.heapIn _ c _ hd hin hc1 rfl
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
    env := fun x hx o he => by
      have := h.env x hx o he
      cases o with
      | sym b p => exact this
      | alloc a n =>
        change (fr.root? x).map _ = _ at he
        cases e : fr.root? x with
        | none => rw [e] at he; cases he
        | some r => rw [e] at he; cases he
    heap := fun o c o' hd hin hc1 hh => by
      change cdefault o c = some o' at hh
      cases o with
      | alloc _ _ => cases hh
      | sym b p => cases hh; exact h.heap _ c _ hd hin hc1 rfl }

/-- The abstract path evaluation contains the recency origin of the concrete path value. -/
theorem readPath_soundR {ctx : Ctx} {st : CState} {X : AState} (h : InvR ctx st X) :
    ∀ {cx : List Cell} {o0 o : Obj} {S : List Origin}, (∀ c ∈ cx, c.abs ∈ ctx.cells) →
      ¬ Dead ctx.once o0 → alphaR ctx.K st o0 ∈ ctx.origins → alphaR ctx.K st o0 ∈ S →
      readPath st.heap o0 cx = some o → alphaR ctx.K st o ∈ aevalFrom X S (cx.map Cell.abs)
  | [], o0, o, S, _, _, _, hS, hr => by
    simp only [readPath, Option.some.injEq] at hr
    subst hr; exact hS
  | c :: cs, o0, o, S, hcs, hd, hin, hS, hr => by
    simp only [readPath] at hr
    cases e : st.heap o0 c with
    | none => rw [e] at hr; cases hr
    | some o1 =>
      rw [e] at hr
      have hc : c.abs ∈ ctx.cells := hcs c (List.mem_cons_self)
      exact readPath_soundR (cx := cs) h (fun c' h' => hcs c' (List.mem_cons_of_mem _ h'))
        (h.heapLive o0 c o1 hd e) (h.heapIn o0 c o1 hd hin hc e)
        (mem_aread.mpr ⟨_, hS, h.heap o0 c o1 hd hin hc e⟩) hr

/-- The abstract evaluation of an access path contains the recency origin of the value. -/
theorem evalPath_soundR {ctx : Ctx} {st : CState} {X : AState} (h : InvR ctx st X)
    {x : Var} {cx : List Cell} {o : Obj} (hcs : ∀ c ∈ cx, c.abs ∈ ctx.cells)
    (he : evalPath st x cx = some o) : alphaR ctx.K st o ∈ aevalPath X x (cx.map Cell.abs) := by
  unfold evalPath at he
  cases e : st.env x with
  | none => rw [e] at he; cases he
  | some o0 =>
    rw [e] at he
    have hx : x ∈ ctx.vars := by
      by_cases hx : x ∈ ctx.vars
      · exact hx
      · rw [h.outside x hx] at e; cases e
    exact readPath_soundR h hcs (h.envOk x o0 e).1 (h.envOk x o0 e).2 (h.env x hx o0 e) he

/-! ## The recency universe of a program -/

/-- Each origin of the recency universe is a symbolic path origin, a deep origin, a recency
origin of an allocation site, or a havoc origin. -/
theorem mem_originsR {K : Nat} {fr : Frame} {p : Prog} {cells : List ACell} {o : Origin} :
    o ∈ originsR K fr p cells ↔
      (∃ b ∈ fr.roots.map ABase.root ++ p.freshSites.map ABase.fresh,
        (∃ q ∈ pathsUpTo cells K, o = .sym b q) ∨ o = .deep b) ∨
      (∃ s ∈ p.newSites, o = rNew s ∨ o = rOld s) ∨ (∃ s ∈ p.callSites, o = .havoc s) := by
  simp only [originsR, List.mem_append, List.mem_flatMap, List.mem_map,
    List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ((⟨b, hb, ⟨q, hq, rfl⟩ | rfl⟩ | ⟨s, hs, h⟩) | ⟨s, hs, rfl⟩)
    · exact Or.inl ⟨b, hb, Or.inl ⟨q, hq, rfl⟩⟩
    · exact Or.inl ⟨b, hb, Or.inr rfl⟩
    · exact Or.inr (Or.inl ⟨s, hs, h⟩)
    · exact Or.inr (Or.inr ⟨s, hs, rfl⟩)
  · rintro (⟨b, hb, ⟨q, hq, rfl⟩ | rfl⟩ | ⟨s, hs, h⟩ | ⟨s, hs, rfl⟩)
    · exact Or.inl (Or.inl ⟨b, hb, Or.inl ⟨q, hq, rfl⟩⟩)
    · exact Or.inl (Or.inl ⟨b, hb, Or.inr rfl⟩)
    · exact Or.inl (Or.inr ⟨s, hs, h⟩)
    · exact Or.inr ⟨s, hs, rfl⟩

/-- An allocation origin of the recency universe is a recency origin of a site. -/
theorem alloc_mem_originsR {K : Nat} {fr : Frame} {p : Prog} {cells : List ACell} {a : Nat}
    (h : Origin.alloc a ∈ originsR K fr p cells) :
    ∃ s ∈ p.newSites, Origin.alloc a = rNew s ∨ Origin.alloc a = rOld s := by
  rcases mem_originsR.mp h with ⟨b, _, ⟨q, _, e⟩ | e⟩ | h | ⟨s, _, e⟩
  · cases e
  · cases e
  · exact h
  · cases e

/-- The recency context of a program is closed. -/
theorem ctxR_ok (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    CtxROK (ctxR eu K fr p qf) where
  base := {
    elem := elem_mem_cellsOf _
    dflt := fun o ho c hc o' ho' => by
      simp only [ctxR] at ho hc ho' ⊢
      rw [mem_originsR] at ho ⊢
      rcases ho with ⟨b, hb, ⟨q, hq, rfl⟩ | rfl⟩ | ⟨s, hs, rfl | rfl⟩ | ⟨s, hs, rfl⟩
      · simp only [adefault, symOrDeep, List.mem_singleton] at ho'
        obtain ⟨hl, hcq⟩ := mem_pathsUpTo.mp hq
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
        subst ho'; exact Or.inr (Or.inr ⟨s, hs, rfl⟩) }
  newOld s h := by
    obtain ⟨s', hs', e⟩ := alloc_mem_originsR h
    show rOld s ∈ originsR K fr p (cellsOf (p.fields ++ qf))
    rw [mem_originsR]
    refine Or.inr (Or.inl ⟨s', hs', Or.inr ?_⟩)
    rcases e with e | e
    · rw [rNew_inj e]
    · exact absurd e.symm (rOld_ne_rNew s' s)
  oldNew s h := by
    obtain ⟨s', hs', e⟩ := alloc_mem_originsR h
    show rNew s ∈ originsR K fr p (cellsOf (p.fields ++ qf))
    rw [mem_originsR]
    refine Or.inr (Or.inl ⟨s', hs', Or.inl ?_⟩)
    rcases e with e | e
    · exact absurd e (rOld_ne_rNew s s')
    · have : @Eq Nat (2 * s + 1) (2 * s' + 1) := Origin.alloc.inj e
      have hs : s = s' := by show @Eq Nat s s'; omega
      rw [hs]

/-- The frame fits the recency context of a program. -/
theorem ctxR_frame (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    FrameOK (ctxR eu K fr p qf) fr where
  vars x hx := by
    simp only [ctxR, List.mem_eraseDups, List.mem_append]
    exact Or.inr hx
  roots x r he := by
    simp only [ctxR]
    rw [mem_originsR]
    refine Or.inl ⟨.root r, List.mem_append.mpr (Or.inl ?_), Or.inl ⟨[], ?_, rfl⟩⟩
    · exact List.mem_map.mpr ⟨r, (lookup_mem he).2, rfl⟩
    · exact mem_pathsUpTo.mpr ⟨Nat.zero_le _, fun _ h => by cases h⟩

/-- Each statement of a program fits the recency context of the program. -/
theorem ctxR_stmts (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    ∀ st ∈ p.stmts, StmtOKR (ctxR eu K fr p qf) st := by
  intro st hst
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    simp only [ctxR, List.mem_eraseDups, List.mem_append]
    exact Or.inl (List.mem_flatMap.mpr ⟨st, hst, hv⟩)
  · intro f hf
    simp only [ctxR]
    exact fld_mem_cellsOf (List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr ⟨st, hst, hf⟩)))
  · intro s hs
    simp only [ctxR]
    rw [mem_originsR]
    exact Or.inr (Or.inl ⟨s, List.mem_filterMap.mpr ⟨st, hst, hs⟩, Or.inl rfl⟩)
  · intro s hs
    simp only [ctxR]
    rw [mem_originsR]
    refine Or.inl ⟨.fresh s, List.mem_append.mpr (Or.inr ?_), Or.inl ⟨[], ?_, rfl⟩⟩
    · exact List.mem_map.mpr ⟨s, List.mem_filterMap.mpr ⟨st, hst, hs⟩, rfl⟩
    · exact mem_pathsUpTo.mpr ⟨Nat.zero_le _, fun _ h => by cases h⟩
  · intro s hs
    simp only [ctxR]
    rw [mem_originsR]
    exact Or.inr (Or.inr ⟨s, List.mem_filterMap.mpr ⟨st, hst, hs⟩, rfl⟩)

/-- The once budget of a program holds at the entry state, in the recency context. -/
theorem ctxR_budget (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    Budget (ctxR eu K fr p qf) p (CState.init fr) := by
  intro t ht
  simp only [ctxR, Prog.onceB, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at ht
  refine ⟨by simp only [CState.init]; omega, fun hm => ?_⟩
  have := List.contains_iff_mem.mpr hm
  rw [ht.2] at this; cases this

/-- Soundness of the recency refinement, for both strong-update policies: each one-execution
alias is a may-alias. -/
theorem csoundR (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (x : Var) (px : List Cell)
    (y : Var) (py : List Cell) (h : CAlias fr p x px y py) :
    mayProgR eu K fr p x (px.map Cell.abs) y (py.map Cell.abs) = true := by
  obtain ⟨st, hx, o, h1, h2⟩ := h
  let qf := afields (px.map Cell.abs) ++ afields (py.map Cell.abs)
  have hinv := analyze_soundR _ (ctxR_ok eu K fr p qf) p (ctxR_stmts eu K fr p qf)
    (ctxR_budget eu K fr p qf) (inv_initR (ctxR_ok eu K fr p qf).base (ctxR_frame eu K fr p qf)) hx
  have hcx := query_cells (cells := p.fields) qf (fun a ha => List.mem_append.mpr (Or.inl ha))
  have hcy := query_cells (cells := p.fields) qf (fun a ha => List.mem_append.mpr (Or.inr ha))
  exact may_iff.mpr ⟨_, evalPath_soundR hinv hcx h1, evalPath_soundR hinv hcy h2⟩

end DirectedAlias.Sound.Recency

import DirectedAlias.Sound.Step

/-!
# Soundness of concept C

The main induction is on the program structure. A loop uses the checked post-fixpoint
(`loopIter_post`), or the top state when the fuel runs out.
The final theorem `csound` proves `CSound K` for each `K`.
`csoundE` proves the same for both strong-update policies (`entryUnique` true or false).
-/

namespace DirectedAlias.Sound

open DirectedAlias

/-- A loop keeps an invariant state `Y` if one run of the body keeps it. -/
theorem loop_keeps {ctx : Ctx} {body : Prog} {Y : AState} (P : CState → Prop)
    (hstep : ∀ s t, P s → Inv ctx s Y → Exec body s t → P t ∧ Inv ctx t Y) :
    ∀ {s u : CState}, Exec (.loop body) s u → P s → Inv ctx s Y → Inv ctx u Y := by
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

/-- Soundness of `analyze`: each execution of a program ends in a state that the analysis
result simulates. -/
theorem analyze_sound (ctx : Ctx) (hc : CtxOK ctx) :
    ∀ (q : Prog) {s s' : CState} {X : AState}, (∀ st ∈ q.stmts, StmtOK ctx st) →
      Budget ctx q s → Inv ctx s X → Exec q s s' → Inv ctx s' (analyze ctx q X) := by
  intro q
  induction q with
  | skip => intro s s' X _ _ h hx; cases hx; exact h
  | stmt st =>
    intro s s' X hok hb h hx
    cases hx with
    | stmt hs => exact step_sound hc (hok st (List.mem_singleton.mpr rfl)) hb h hs
  | seq p q ihp ihq =>
    intro s s' X hok hb h hx
    cases hx with
    | seq h1 h2 =>
      have hokp : ∀ st ∈ p.stmts, StmtOK ctx st :=
        fun st hs => hok st (List.mem_append.mpr (Or.inl hs))
      have hokq : ∀ st ∈ q.stmts, StmtOK ctx st :=
        fun st hs => hok st (List.mem_append.mpr (Or.inr hs))
      exact ihq hokq (Budget.seqR hb h1) (ihp hokp (Budget.seqL hb) h h1) h2
  | choice p q ihp ihq =>
    intro s s' X hok hb h hx
    have hokp : ∀ st ∈ p.stmts, StmtOK ctx st :=
      fun st hs => hok st (List.mem_append.mpr (Or.inl hs))
    have hokq : ∀ st ∈ q.stmts, StmtOK ctx st :=
      fun st hs => hok st (List.mem_append.mpr (Or.inr hs))
    cases hx with
    | choiceL h1 =>
      exact (ihp hokp (Budget.choiceL hb) h h1).mono (sub_join_left _ _)
    | choiceR h1 =>
      exact (ihq hokq (Budget.choiceR hb) h h1).mono (sub_join_right _ _)
  | loop body ih =>
    intro s s' X hok hb h hx
    show Inv ctx s' (loopIter ctx (analyze ctx body) ctx.fuel X)
    have hY := h.mono (sub_loopIter ctx (analyze ctx body) ctx.fuel X)
    refine loop_keeps (Budget ctx (.loop body)) ?_ hx hb hY
    intro s1 t hb1 hi1 hx1
    refine ⟨Budget.again hb1 hx1, ?_⟩
    have hf := ih hok (Budget.body hb1) hi1 hx1
    rcases loopIter_post ctx (analyze ctx body) ctx.fuel X with hpost | ⟨W, hW⟩
    · exact hf.mono_leOn hpost
    · rw [hW]; exact hf.top W

/-! ## The entry state -/

/-- A frame lookup gives a bound variable. -/
theorem lookup_mem : ∀ {l : List (Var × Root)} {x : Var} {r : Root},
    l.lookup x = some r → x ∈ l.map Prod.fst ∧ r ∈ l.map Prod.snd
  | [], _, _, h => by simp [List.lookup] at h
  | (a, b) :: l, x, r, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i he
      cases h
      have : x = a := by simpa using he
      subst this
      simp
    · have := lookup_mem h
      simp only [List.map_cons, List.mem_cons]
      exact ⟨Or.inr this.1, Or.inr this.2⟩

/-- The entry states satisfy the invariant. -/
theorem inv_init {ctx : Ctx} (hc : CtxOK ctx) {fr : Frame} (hf : FrameOK ctx fr) :
    Inv ctx (CState.init fr) (ainit ctx.K fr) where
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
      simp only [alpha, symOrDeep, List.map_nil, List.length_nil, Nat.zero_le, ite_true]
      exact hf.roots x r e
  heapLive o c o' hd hh := by
    change cdefault o c = some o' at hh
    cases o with
    | alloc s n => cases hh
    | sym b p => cases hh; cases b <;> simp_all [Dead]
  heapIn o c o' _ hin hc1 hh := by
    change cdefault o c = some o' at hh
    have := alphaV_cdefault ctx.K o c
    rw [hh] at this
    exact hc.dflt _ hin _ hc1 _ (by rw [← this]; exact List.mem_singleton.mpr rfl)
  allocHeld o c s n hh := by
    change cdefault o c = some (.alloc s n) at hh
    cases o with
    | alloc _ _ => cases hh
    | sym _ _ => cases hh
  env x _ o he := by
    have := alphaV_init_env ctx.K fr x
    rw [he] at this
    rw [← this]; exact List.mem_singleton.mpr rfl
  heap o c o' _ _ _ hh := by
    change cdefault o c = some o' at hh
    have := alphaV_cdefault ctx.K o c
    rw [hh] at this
    show alpha ctx.K o' ∈ adefault ctx.K (alpha ctx.K o) c.abs
    rw [← this]; exact List.mem_singleton.mpr rfl

/-! ## Queries -/

/-- The abstract path evaluation contains the origin of the concrete path value. -/
theorem readPath_sound {ctx : Ctx} {st : CState} {X : AState} (h : Inv ctx st X) :
    ∀ {cx : List Cell} {o0 o : Obj} {S : List Origin}, (∀ c ∈ cx, c.abs ∈ ctx.cells) →
      ¬ Dead ctx.once o0 → alpha ctx.K o0 ∈ ctx.origins → alpha ctx.K o0 ∈ S →
      readPath st.heap o0 cx = some o → alpha ctx.K o ∈ aevalFrom X S (cx.map Cell.abs)
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
      exact readPath_sound (cx := cs) h (fun c' h' => hcs c' (List.mem_cons_of_mem _ h'))
        (h.heapLive o0 c o1 hd e) (h.heapIn o0 c o1 hd hin hc e)
        (mem_aread.mpr ⟨_, hS, h.heap o0 c o1 hd hin hc e⟩) hr

/-- The abstract evaluation of an access path contains the origin of the concrete value. -/
theorem evalPath_sound {ctx : Ctx} {st : CState} {X : AState} (h : Inv ctx st X)
    {x : Var} {cx : List Cell} {o : Obj} (hcs : ∀ c ∈ cx, c.abs ∈ ctx.cells)
    (he : evalPath st x cx = some o) : alpha ctx.K o ∈ aevalPath X x (cx.map Cell.abs) := by
  unfold evalPath at he
  cases e : st.env x with
  | none => rw [e] at he; cases he
  | some o0 =>
    rw [e] at he
    have hx : x ∈ ctx.vars := by
      by_cases hx : x ∈ ctx.vars
      · exact hx
      · rw [h.outside x hx] at e; cases e
    exact readPath_sound h hcs (h.envOk x o0 e).1 (h.envOk x o0 e).2 (h.env x hx o0 e) he

/-! ## The universe of a program -/

/-- The cell universe of a field list contains each of its fields. -/
theorem fld_mem_cellsOf {fs : List Field} {f : Field} (h : f ∈ fs) : ACell.fld f ∈ cellsOf fs := by
  simp only [cellsOf, List.mem_append, List.mem_map, List.mem_eraseDups]
  exact Or.inl ⟨f, h, rfl⟩

/-- The cell universe of a field list contains the array cell. -/
theorem elem_mem_cellsOf (fs : List Field) : ACell.elem ∈ cellsOf fs := by
  simp [cellsOf]

/-- Each origin of a program universe is a symbolic path origin, a deep origin of a base,
an allocation origin, or a havoc origin. -/
theorem mem_originsOf {K : Nat} {fr : Frame} {p : Prog} {cells : List ACell} {o : Origin} :
    o ∈ originsOf K fr p cells ↔
      (∃ b ∈ fr.roots.map ABase.root ++ p.freshSites.map ABase.fresh,
        (∃ q ∈ pathsUpTo cells K, o = .sym b q) ∨ o = .deep b) ∨
      (∃ s ∈ p.newSites, o = .alloc s) ∨ (∃ s ∈ p.callSites, o = .havoc s) := by
  simp only [originsOf, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_singleton]
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

/-- The context of a program, with any strong-update policy. -/
def ctxE (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) : Ctx :=
  { Ctx.ofProg K fr p qf with entryUnique := eu }

/-- The context of a program is closed. -/
theorem ctxE_ok (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    CtxOK (ctxE eu K fr p qf) where
  elem := elem_mem_cellsOf _
  dflt o ho c hc o' ho' := by
    simp only [ctxE, Ctx.ofProg] at ho hc ho' ⊢
    rw [mem_originsOf] at ho ⊢
    rcases ho with ⟨b, hb, ⟨q, hq, rfl⟩ | rfl⟩ | ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
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
    · simp [adefault] at ho'
    · simp only [adefault, List.mem_singleton] at ho'
      subst ho'; exact Or.inr (Or.inr ⟨s, hs, rfl⟩)

/-- The frame fits the context of a program. -/
theorem ctxE_frame (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    FrameOK (ctxE eu K fr p qf) fr where
  vars x hx := by
    simp only [ctxE, Ctx.ofProg, List.mem_eraseDups, List.mem_append]
    exact Or.inr hx
  roots x r he := by
    simp only [ctxE, Ctx.ofProg]
    rw [mem_originsOf]
    refine Or.inl ⟨.root r, List.mem_append.mpr (Or.inl ?_), Or.inl ⟨[], ?_, rfl⟩⟩
    · exact List.mem_map.mpr ⟨r, (lookup_mem he).2, rfl⟩
    · exact mem_pathsUpTo.mpr ⟨Nat.zero_le _, fun _ h => by cases h⟩

/-- Each statement of a program fits the context of the program. -/
theorem ctxE_stmts (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    ∀ st ∈ p.stmts, StmtOK (ctxE eu K fr p qf) st := by
  intro st hst
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    simp only [ctxE, Ctx.ofProg, List.mem_eraseDups, List.mem_append]
    exact Or.inl (List.mem_flatMap.mpr ⟨st, hst, hv⟩)
  · intro f hf
    simp only [ctxE, Ctx.ofProg]
    exact fld_mem_cellsOf (List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr ⟨st, hst, hf⟩)))
  · intro s hs
    simp only [ctxE, Ctx.ofProg]
    rw [mem_originsOf]
    exact Or.inr (Or.inl ⟨s, List.mem_filterMap.mpr ⟨st, hst, hs⟩, rfl⟩)
  · intro s hs
    simp only [ctxE, Ctx.ofProg]
    rw [mem_originsOf]
    refine Or.inl ⟨.fresh s, List.mem_append.mpr (Or.inr ?_), Or.inl ⟨[], ?_, rfl⟩⟩
    · exact List.mem_map.mpr ⟨s, List.mem_filterMap.mpr ⟨st, hst, hs⟩, rfl⟩
    · exact mem_pathsUpTo.mpr ⟨Nat.zero_le _, fun _ h => by cases h⟩
  · intro s hs
    simp only [ctxE, Ctx.ofProg]
    rw [mem_originsOf]
    exact Or.inr (Or.inr ⟨s, List.mem_filterMap.mpr ⟨st, hst, hs⟩, rfl⟩)

/-- The once budget of a program holds at the entry state. -/
theorem ctxE_budget (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    Budget (ctxE eu K fr p qf) p (CState.init fr) := by
  intro t ht
  simp only [ctxE, Ctx.ofProg, Prog.onceB, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true'] at ht
  refine ⟨by simp only [CState.init]; omega, fun hm => ?_⟩
  have := List.contains_iff_mem.mpr hm
  rw [ht.2] at this; cases this

/-- The context with the `true` policy is the context of `mayProg`. -/
theorem ctxE_true (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    ctxE true K fr p qf = progCtx K fr p qf := rfl

/-- May-alias at the end of `p`, with the strong-update policy `eu`. -/
def mayProgE (eu : Bool) (K : Nat) (fr : Frame) (p : Prog)
    (x : Var) (px : List ACell) (y : Var) (py : List ACell) : Bool :=
  may (analyze (ctxE eu K fr p (afields px ++ afields py)) p (ainit K fr)) x px y py

/-- The `true` policy gives `mayProg`. -/
theorem mayProgE_true (K : Nat) (fr : Frame) (p : Prog)
    (x : Var) (px : List ACell) (y : Var) (py : List ACell) :
    mayProgE true K fr p x px y py = mayProg K fr p x px y py := rfl

/-- The query cells are in the cell universe of the query context. -/
theorem query_cells {cells : List Field} {px : List Cell} (qf : List Field)
    (h : afields (px.map Cell.abs) ⊆ qf) :
    ∀ c ∈ px, c.abs ∈ cellsOf (cells ++ qf) := by
  intro c hc
  cases c with
  | elem i => exact elem_mem_cellsOf _
  | fld f =>
    apply fld_mem_cellsOf
    apply List.mem_append.mpr (Or.inr (h _))
    simp only [afields, List.mem_filterMap, List.mem_map]
    exact ⟨.fld f, ⟨.fld f, hc, rfl⟩, rfl⟩

/-- Soundness for both strong-update policies: each one-execution alias is a may-alias. -/
theorem csoundE (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (x : Var) (px : List Cell)
    (y : Var) (py : List Cell) (h : CAlias fr p x px y py) :
    mayProgE eu K fr p x (px.map Cell.abs) y (py.map Cell.abs) = true := by
  obtain ⟨st, hx, o, h1, h2⟩ := h
  let qf := afields (px.map Cell.abs) ++ afields (py.map Cell.abs)
  have hinv := analyze_sound _ (ctxE_ok eu K fr p qf) p (ctxE_stmts eu K fr p qf)
    (ctxE_budget eu K fr p qf) (inv_init (ctxE_ok eu K fr p qf) (ctxE_frame eu K fr p qf)) hx
  have hcx := query_cells (cells := p.fields) qf (fun a ha => List.mem_append.mpr (Or.inl ha))
  have hcy := query_cells (cells := p.fields) qf (fun a ha => List.mem_append.mpr (Or.inr ha))
  exact may_iff.mpr ⟨_, evalPath_sound hinv hcx h1, evalPath_sound hinv hcy h2⟩

/-- Concept C is sound (`CSound K`) for each depth limit `K`. -/
theorem csound (K : Nat) : CSound K := fun fr p x px y py h =>
  (mayProgE_true K fr p _ _ _ _) ▸ csoundE true K fr p x px y py h

end DirectedAlias.Sound

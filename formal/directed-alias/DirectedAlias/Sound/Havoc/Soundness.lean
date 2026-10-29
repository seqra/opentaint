import DirectedAlias.Sound.Havoc.Concept

/-!
# Soundness of per-cell havoc under strict A2

The proof is the proof of concept C (`Sound/Step.lean`, `Sound/Soundness.lean`) with the
strict abstraction `alphaS K src` in place of `alpha K`. Only the call step is new
(`InvS.havocH`). The budget and counter lemmas are reused through `ExecS.toExec`.
The main theorem is `csoundH`: for each naming `src`, each strict one-execution alias is a
may-alias of the per-cell havoc analysis, for both strong-update policies.
-/

namespace DirectedAlias.Sound.Havoc

open DirectedAlias DirectedAlias.Sound

variable {src : Nat → Obj × Cell}

/-- The simulation invariant with the strict abstraction (the same facts as `Inv`). -/
structure InvS (ctx : Ctx) (src : Nat → Obj × Cell) (st : CState) (X : AState) : Prop where
  outside : ∀ x, x ∉ ctx.vars → st.env x = none
  envOk : ∀ x o, st.env x = some o → ¬ Dead ctx.once o ∧ alphaS ctx.K src o ∈ ctx.origins
  heapLive : ∀ o c o', ¬ Dead ctx.once o → st.heap o c = some o' → ¬ Dead ctx.once o'
  heapIn : ∀ o c o', ¬ Dead ctx.once o → alphaS ctx.K src o ∈ ctx.origins → c.abs ∈ ctx.cells →
    st.heap o c = some o' → alphaS ctx.K src o' ∈ ctx.origins
  allocHeld : ∀ o c s n, st.heap o c = some (.alloc s n) →
    ¬ Dead ctx.once o ∧ alphaS ctx.K src o ∈ ctx.origins ∧ c.abs ∈ ctx.cells
  env : ∀ x ∈ ctx.vars, ∀ o, st.env x = some o → alphaS ctx.K src o ∈ X.env x
  heap : ∀ o c o', ¬ Dead ctx.once o → alphaS ctx.K src o ∈ ctx.origins → c.abs ∈ ctx.cells →
    st.heap o c = some o' → alphaS ctx.K src o' ∈ X.heap (alphaS ctx.K src o) c.abs

/-- A statement fits the universe of a per-cell havoc context: the foundation facts, and the
per-cell havoc origin of each universe cell of each universe origin is in the universe. -/
structure StmtOKH (ctx : Ctx) (st : Stmt) : Prop where
  ok : StmtOK ctx st
  callH : ∀ s, st.callSite? = some s → ∀ a ∈ ctx.origins, ∀ c ∈ ctx.cells,
    Origin.hsym s (keyOf a) c [] ∈ ctx.origins

/-! ## Basic lemmas -/

/-- The strict invariant is closed upward under state inclusion. -/
theorem InvS.mono {ctx : Ctx} {st : CState} {X Y : AState} (h : InvS ctx src st X)
    (hs : X.Sub Y) : InvS ctx src st Y where
  outside := h.outside
  envOk := h.envOk
  heapLive := h.heapLive
  heapIn := h.heapIn
  allocHeld := h.allocHeld
  env x hx o he := hs.1 x (h.env x hx o he)
  heap o c o' hd ho hc hh := hs.2 _ _ (h.heap o c o' hd ho hc hh)

/-- The strict invariant is closed upward under inclusion on the universe. -/
theorem InvS.mono_leOn {ctx : Ctx} {st : CState} {X Y : AState} (h : InvS ctx src st X)
    (hs : leOn ctx X Y = true) : InvS ctx src st Y := by
  obtain ⟨h1, h2⟩ := leOn_iff.mp hs
  exact { outside := h.outside, envOk := h.envOk, heapLive := h.heapLive, heapIn := h.heapIn,
          allocHeld := h.allocHeld,
          env := fun x hx o he => h1 x hx (h.env x hx o he),
          heap := fun o c o' hd ho hc hh => h2 _ ho _ hc (h.heap o c o' hd ho hc hh) }

/-- Each top state simulates each concrete state that has the concrete support facts. -/
theorem InvS.top {ctx : Ctx} {st : CState} {X : AState} (h : InvS ctx src st X) (W : AState) :
    InvS ctx src st (top ctx W) where
  outside := h.outside
  envOk := h.envOk
  heapLive := h.heapLive
  heapIn := h.heapIn
  allocHeld := h.allocHeld
  env x _ o he := mem_uni.mpr (Or.inl (h.envOk x o he).2)
  heap o c o' hd ho hc hh := mem_uni.mpr (Or.inl (h.heapIn o c o' hd ho hc hh))

/-- The strict invariant depends only on the environment and the heap. -/
theorem InvS.congr {ctx : Ctx} {s s' : CState} {X : AState} (h : InvS ctx src s X)
    (he : s'.env = s.env) (hh : s'.heap = s.heap) : InvS ctx src s' X := by
  obtain ⟨a, b, c, d, e, f, g⟩ := h
  exact ⟨by rw [he]; exact a, by rw [he]; exact b, by rw [hh]; exact c, by rw [hh]; exact d,
    by rw [hh]; exact e, by rw [he]; exact f, by rw [hh]; exact g⟩

/-! ## The strict abstraction -/

/-- The strict origin of a symbolic object is an outer origin. -/
theorem alphaS_sym_outer (K : Nat) (src : Nat → Obj × Cell) (b : Base) (p : List Cell) :
    (alphaS K src (.sym b p)).outer = true := by
  cases b with
  | root r => exact alpha_sym_outer K (.root r) p
  | fresh s n => exact alpha_sym_outer K (.fresh s n) p
  | havoc s n k =>
    show (hsymOrDeep K s _ _ _).outer = true
    unfold hsymOrDeep; split <;> rfl

/-- A unique strict origin is the foundation origin of the object. -/
theorem alphaS_unique {K : Nat} {once : Site → Bool} {eu : Bool} {o : Obj}
    (hu : (alphaS K src o).uniqueB once eu = true) : alphaS K src o = alpha K o := by
  cases o with
  | alloc s n => rfl
  | sym b p =>
    cases b with
    | root r => rfl
    | fresh s n => rfl
    | havoc s n k =>
      exfalso
      change (hsymOrDeep K s _ _ _).uniqueB once eu = true at hu
      unfold hsymOrDeep at hu
      split at hu <;> simp [Origin.uniqueB] at hu

/-- A unique strict origin denotes at most one object that is not dead. -/
theorem unique_objS {K : Nat} {once : Site → Bool} {eu : Bool} {o o' : Obj}
    (hu : (alphaS K src o).uniqueB once eu = true) (hd : ¬ Dead once o) (hd' : ¬ Dead once o')
    (ha : alphaS K src o' = alphaS K src o) : o' = o := by
  have h1 := alphaS_unique hu
  have hu' : (alphaS K src o').uniqueB once eu = true := by rw [ha]; exact hu
  have h2 := alphaS_unique hu'
  rw [h1] at hu
  exact unique_obj hu hd hd' (by rw [← h1, ← h2]; exact ha)

/-- The strict origin of a default child is in the abstract default content of the parent. -/
theorem alphaS_cdefault (K : Nat) (src : Nat → Obj × Cell) {o o' : Obj} {c : Cell}
    (h : cdefault o c = some o') : alphaS K src o' ∈ adefault K (alphaS K src o) c.abs := by
  cases o with
  | alloc s n => cases h
  | sym b p =>
    cases h
    cases b with
    | root r =>
      show alpha K (.sym (.root r) (p ++ [c])) ∈ adefault K (alpha K (.sym (.root r) p)) c.abs
      rw [← alphaV_cdefault]; exact List.mem_singleton.mpr rfl
    | fresh s n =>
      show alpha K (.sym (.fresh s n) (p ++ [c])) ∈ adefault K (alpha K (.sym (.fresh s n) p)) c.abs
      rw [← alphaV_cdefault]; exact List.mem_singleton.mpr rfl
    | havoc s n k =>
      show hsymOrDeep K s _ _ ((p ++ [c]).map Cell.abs) ∈
        adefault K (hsymOrDeep K s _ _ (p.map Cell.abs)) c.abs
      unfold hsymOrDeep
      rw [List.map_append, List.map_cons, List.map_nil]
      by_cases h1 : (p.map Cell.abs).length ≤ K
      · rw [ite_eq_left h1]
        exact List.mem_singleton.mpr rfl
      · have h2 : ¬ (p.map Cell.abs ++ [c.abs]).length ≤ K := by
          rw [List.length_append]; omega
        rw [ite_eq_right h1, ite_eq_right h2]
        exact List.mem_singleton.mpr rfl

/-! ## Variable updates -/

/-- Setting a variable keeps the invariant if the abstract set covers the new value. -/
theorem InvS.setVar {ctx : Ctx} {st : CState} {X : AState} {x : Var} {v : Val}
    {S : List Origin} (h : InvS ctx src st X) (hx : x ∈ ctx.vars)
    (hv : ∀ o, v = some o → ¬ Dead ctx.once o ∧ alphaS ctx.K src o ∈ ctx.origins ∧ alphaS ctx.K src o ∈ S) :
    InvS ctx src (st.setVar x v) (X.setVar x S) where
  outside y hy := by
    have hne : y ≠ x := fun e => hy (e ▸ hx)
    show fupd st.env x v y = none
    rw [fupd_ne _ _ hne]; exact h.outside y hy
  envOk y o he := by
    change fupd st.env x v y = some o at he
    by_cases e : y = x
    · subst e; rw [fupd_same] at he; exact ⟨(hv o he).1, (hv o he).2.1⟩
    · rw [fupd_ne _ _ e] at he; exact h.envOk y o he
  heapLive := h.heapLive
  heapIn := h.heapIn
  allocHeld := h.allocHeld
  env y hy o he := by
    change fupd st.env x v y = some o at he
    show alphaS ctx.K src o ∈ fupd X.env x S y
    by_cases e : y = x
    · subst e; rw [fupd_same] at he; rw [fupd_same]; exact (hv o he).2.2
    · rw [fupd_ne _ _ e] at he; rw [fupd_ne _ _ e]; exact h.env y hy o he
  heap := h.heap

/-! ## Heap updates -/

/-- A concrete store keeps the concrete support facts. The caller proves the abstract heap facts. -/
theorem InvS.write {ctx : Ctx} {st : CState} {X Y : AState} {o : Obj} {c : Cell} {v : Val}
    (h : InvS ctx src st X) (ho : ¬ Dead ctx.once o ∧ alphaS ctx.K src o ∈ ctx.origins)
    (hc : c.abs ∈ ctx.cells)
    (hv : ∀ o', v = some o' → ¬ Dead ctx.once o' ∧ alphaS ctx.K src o' ∈ ctx.origins)
    (henv : ∀ x ∈ ctx.vars, ∀ o', st.env x = some o' → alphaS ctx.K src o' ∈ Y.env x)
    (hheap : ∀ o1 c1 o2, ¬ Dead ctx.once o1 → alphaS ctx.K src o1 ∈ ctx.origins →
      c1.abs ∈ ctx.cells → fupd2 st.heap o c v o1 c1 = some o2 →
      alphaS ctx.K src o2 ∈ Y.heap (alphaS ctx.K src o1) c1.abs) :
    InvS ctx src (st.setCell o c v) Y where
  outside := h.outside
  envOk := h.envOk
  heapLive o1 c1 o2 hd hh := by
    change fupd2 st.heap o c v o1 c1 = some o2 at hh
    by_cases e : o1 = o ∧ c1 = c
    · obtain ⟨rfl, rfl⟩ := e; rw [fupd2_same] at hh; exact (hv o2 hh).1
    · rw [fupd2_ne _ _ e] at hh; exact h.heapLive o1 c1 o2 hd hh
  heapIn o1 c1 o2 hd hin hc1 hh := by
    change fupd2 st.heap o c v o1 c1 = some o2 at hh
    by_cases e : o1 = o ∧ c1 = c
    · obtain ⟨rfl, rfl⟩ := e; rw [fupd2_same] at hh; exact (hv o2 hh).2
    · rw [fupd2_ne _ _ e] at hh; exact h.heapIn o1 c1 o2 hd hin hc1 hh
  allocHeld o1 c1 s n hh := by
    change fupd2 st.heap o c v o1 c1 = some (.alloc s n) at hh
    by_cases e : o1 = o ∧ c1 = c
    · obtain ⟨rfl, rfl⟩ := e; exact ⟨ho.1, ho.2, hc⟩
    · rw [fupd2_ne _ _ e] at hh; exact h.allocHeld o1 c1 s n hh
  env := henv
  heap := hheap

/-- A weak store keeps the invariant if one origin of the target is the target's origin. -/
theorem InvS.weak {ctx : Ctx} {st : CState} {X : AState} {o : Obj} {c : Cell} {v : Val}
    {os : List Origin} {S : List Origin}
    (h : InvS ctx src st X) (ho : ¬ Dead ctx.once o ∧ alphaS ctx.K src o ∈ ctx.origins)
    (hc : c.abs ∈ ctx.cells) (hos : alphaS ctx.K src o ∈ os)
    (hv : ∀ o', v = some o' → ¬ Dead ctx.once o' ∧ alphaS ctx.K src o' ∈ ctx.origins ∧
      alphaS ctx.K src o' ∈ S) :
    InvS ctx src (st.setCell o c v) (X.weakStore os c.abs S) := by
  apply InvS.write (Y := X.weakStore os c.abs S) h ho hc (fun o' e => ⟨(hv o' e).1, (hv o' e).2.1⟩) h.env
  intro o1 c1 o2 hd hin hc1 hh
  show alphaS ctx.K src o2 ∈ (if c1.abs = c.abs ∧ alphaS ctx.K src o1 ∈ os then
    uni S (X.heap (alphaS ctx.K src o1) c1.abs) else X.heap (alphaS ctx.K src o1) c1.abs)
  by_cases e : o1 = o ∧ c1 = c
  · obtain ⟨rfl, rfl⟩ := e
    rw [fupd2_same] at hh
    rw [ite_eq_left ⟨rfl, hos⟩]
    exact mem_uni.mpr (Or.inl (hv o2 hh).2.2)
  · rw [fupd2_ne _ _ e] at hh
    have := h.heap o1 c1 o2 hd hin hc1 hh
    split
    · exact mem_uni.mpr (Or.inr this)
    · exact this

/-- A strong store keeps the invariant if the target origin is unique and the cell is a field. -/
theorem InvS.strong {ctx : Ctx} {st : CState} {X : AState} {o : Obj} {f : Field} {v : Val}
    {S : List Origin}
    (h : InvS ctx src st X) (ho : ¬ Dead ctx.once o ∧ alphaS ctx.K src o ∈ ctx.origins)
    (hc : ACell.fld f ∈ ctx.cells)
    (huniq : ∀ o1, ¬ Dead ctx.once o1 → alphaS ctx.K src o1 = alphaS ctx.K src o → o1 = o)
    (hv : ∀ o', v = some o' → ¬ Dead ctx.once o' ∧ alphaS ctx.K src o' ∈ ctx.origins ∧
      alphaS ctx.K src o' ∈ S) :
    InvS ctx src (st.setCell o (.fld f) v) (X.setCell (alphaS ctx.K src o) (.fld f) S) := by
  apply InvS.write (Y := X.setCell (alphaS ctx.K src o) (.fld f) S) (c := .fld f) h ho hc (fun o' e => ⟨(hv o' e).1, (hv o' e).2.1⟩) h.env
  intro o1 c1 o2 hd hin hc1 hh
  show alphaS ctx.K src o2 ∈ fupd2 X.heap (alphaS ctx.K src o) (.fld f) S (alphaS ctx.K src o1) c1.abs
  by_cases e : o1 = o ∧ c1 = .fld f
  · obtain ⟨rfl, rfl⟩ := e
    rw [fupd2_same] at hh
    exact (fupd2_same X.heap (alphaS ctx.K src o1) (ACell.fld f) S).symm ▸ (hv o2 hh).2.2
  · rw [fupd2_ne _ _ e] at hh
    have e2 : ¬ (alphaS ctx.K src o1 = alphaS ctx.K src o ∧ c1.abs = .fld f) := by
      rintro ⟨h1, h2⟩
      apply e
      refine ⟨huniq o1 hd h1, ?_⟩
      cases c1 with
      | fld g => simp only [Cell.abs, ACell.fld.injEq] at h2; rw [h2]
      | elem i => simp [Cell.abs] at h2
    rw [fupd2_ne _ _ e2]
    exact h.heap o1 c1 o2 hd hin hc1 hh

/-! ## Calls -/

/-- Each object that a call can reach has an origin for which `reachB` is true. -/
theorem reachB_of_reachS {ctx : Ctx} {st : CState} {X : AState} {args : List Var} {o : Obj}
    (h : InvS ctx src st X) (hargs : ∀ a ∈ args, a ∈ ctx.vars) (hr : Reach st args o) :
    reachB ctx X args (alphaS ctx.K src o) = true := by
  unfold reachB
  cases hR : closeIter ctx.cells X (ctx.origins.length + 1)
      (uni (uniMap X.env args) (ctx.origins.filter Origin.outer)) with
  | none => rfl
  | some R =>
    obtain ⟨hseed, hclosed⟩ := closeIter_spec hR
    have key : (alphaS ctx.K src o).outer = true ∨ alphaS ctx.K src o ∈ R := by
      induction hr with
      | outer => exact Or.inl (alphaS_sym_outer _ _ _ _)
      | arg hx he =>
        exact Or.inr (hseed _ (mem_uni.mpr (Or.inl
          (mem_uniMap.mpr ⟨_, hx, h.env _ (hargs _ hx) _ he⟩))))
      | @step o1 o2 c _ hh ih =>
        cases o2 with
        | sym b p => exact Or.inl (alphaS_sym_outer _ _ _ _)
        | alloc s n =>
          obtain ⟨hd, hin, hc⟩ := h.allocHeld _ _ _ _ hh
          have h1 : alphaS ctx.K src o1 ∈ R := by
            cases ih with
            | inl hout => exact hseed _ (mem_uni.mpr (Or.inr (List.mem_filter.mpr ⟨hin, hout⟩)))
            | inr h => exact h
          exact Or.inr (hclosed _ (mem_succs.mpr ⟨_, h1, _, hc, h.heap _ _ _ hd hin hc hh⟩))
    cases key with
    | inl h1 => simp [h1]
    | inr h1 => simp [h1]


/-- The per-cell weak havoc keeps the strict invariant for each strict havoc. -/
theorem InvS.havocH {ctx : Ctx} {st : CState} {X : AState} {args : List Var} {s n : Nat}
    {h' : Heap} (h : InvS ctx src st X) (hargs : ∀ a ∈ args, a ∈ ctx.vars)
    (hs : ∀ a ∈ ctx.origins, ∀ c ∈ ctx.cells, Origin.hsym s (keyOf a) c [] ∈ ctx.origins)
    (hh : HavocS src st args s n h') :
    InvS ctx src { st with heap := h' } (X.havocH ctx args s) where
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
      rw [alphaS_head ctx.K hk]
      exact hs _ hin _ hc
  allocHeld o c a m he := by
    rcases hh o c with e | ⟨_, k, _, e⟩
    · exact h.allocHeld o c a m (e ▸ he)
    · change h' o c = some (.alloc a m) at he
      rw [e] at he; cases he
  env := h.env
  heap o c o' hd hin hc he := by
    show alphaS ctx.K src o' ∈ (if c.abs ∈ ctx.cells ∧ reachB ctx X args (alphaS ctx.K src o) = true
      then uni [.hsym s (keyOf (alphaS ctx.K src o)) c.abs []] (X.heap (alphaS ctx.K src o) c.abs)
      else X.heap (alphaS ctx.K src o) c.abs)
    rcases hh o c with e | ⟨hr, k, hk, e⟩
    · have := h.heap o c o' hd hin hc (e ▸ he)
      split
      · exact mem_uni.mpr (Or.inr this)
      · exact this
    · change h' o c = some o' at he
      rw [e] at he; cases he
      rw [ite_eq_left ⟨hc, reachB_of_reachS h hargs hr⟩, alphaS_head ctx.K hk]
      exact mem_uni.mpr (Or.inl (List.mem_singleton.mpr rfl))

/-! ## One statement -/

/-- Local soundness: one concrete step keeps the invariant for the abstract transfer. -/
theorem step_soundS {ctx : Ctx} (hc : CtxOK ctx) {st : Stmt} {s s' : CState} {X : AState}
    (hok : StmtOKH ctx st) (hb : Budget ctx (.stmt st) s) (h : InvS ctx src s X)
    (hs : SStepS src st s s') : InvS ctx src s' (astepH ctx st X) := by
  cases hs with
  | @new x a =>
    refine InvS.congr (InvS.setVar h (hok.ok.vars x (by simp [Stmt.vars])) ?_) rfl rfl
    intro o e
    cases e
    refine ⟨?_, hok.ok.newS a rfl, List.mem_singleton.mpr rfl⟩
    rintro ⟨ho, hn⟩
    have := Budget.stmt_site hb rfl ho
    omega
  | @null x =>
    exact InvS.setVar h (hok.ok.vars x (by simp [Stmt.vars])) (fun o e => by cases e)
  | @copy x y =>
    refine InvS.setVar h (hok.ok.vars x (by simp [Stmt.vars])) ?_
    intro o e
    exact ⟨(h.envOk y o e).1, (h.envOk y o e).2, h.env y (hok.ok.vars y (by simp [Stmt.vars])) o e⟩
  | @load x y f _ o he =>
    refine InvS.setVar h (hok.ok.vars x (by simp [Stmt.vars])) ?_
    intro o' e
    have hd := h.envOk y o he
    have hf : (Cell.fld f).abs ∈ ctx.cells := hok.ok.fields f (by simp [Stmt.fields])
    exact ⟨h.heapLive o _ o' hd.1 e, h.heapIn o _ o' hd.1 hd.2 hf e,
      mem_aread.mpr ⟨_, h.env y (hok.ok.vars y (by simp [Stmt.vars])) o he,
        h.heap o _ o' hd.1 hd.2 hf e⟩⟩
  | @aload x y _ o i he =>
    refine InvS.setVar h (hok.ok.vars x (by simp [Stmt.vars])) ?_
    intro o' e
    have hd := h.envOk y o he
    have hf : (Cell.elem i).abs ∈ ctx.cells := hc.elem
    exact ⟨h.heapLive o _ o' hd.1 e, h.heapIn o _ o' hd.1 hd.2 hf e,
      mem_aread.mpr ⟨_, h.env y (hok.ok.vars y (by simp [Stmt.vars])) o he,
        h.heap o _ o' hd.1 hd.2 hf e⟩⟩
  | @store x f y _ o he =>
    have hd := h.envOk x o he
    have hx := h.env x (hok.ok.vars x (by simp [Stmt.vars])) o he
    have hf : ACell.fld f ∈ ctx.cells := hok.ok.fields f (by simp [Stmt.fields])
    have hv : ∀ o', s.env y = some o' → ¬ Dead ctx.once o' ∧ alphaS ctx.K src o' ∈ ctx.origins ∧
        alphaS ctx.K src o' ∈ X.env y := fun o' e =>
      ⟨(h.envOk y o' e).1, (h.envOk y o' e).2, h.env y (hok.ok.vars y (by simp [Stmt.vars])) o' e⟩
    show InvS ctx src _ (X.store ctx.once x (.fld f) (X.env y) ctx.entryUnique)
    unfold AState.store
    split
    · rename_i oa hsingle
      have hoa : alphaS ctx.K src o = oa := (single?_spec hsingle).2 _ hx
      split
      · rename_i hu
        rw [← hoa] at hu ⊢
        exact InvS.strong h hd hf
          (fun o1 hd1 ha => unique_objS hu hd.1 hd1 ha) hv
      · exact InvS.weak (c := .fld f) h hd hf hx hv
    · exact InvS.weak (c := .fld f) h hd hf hx hv
  | @astore x y _ o i he =>
    have hd := h.envOk x o he
    have hx := h.env x (hok.ok.vars x (by simp [Stmt.vars])) o he
    exact InvS.weak (c := .elem i) h hd hc.elem hx (fun o' e =>
      ⟨(h.envOk y o' e).1, (h.envOk y o' e).2, h.env y (hok.ok.vars y (by simp [Stmt.vars])) o' e⟩)
  | @unknown x a =>
    refine InvS.congr (InvS.setVar h (hok.ok.vars x (by simp [Stmt.vars])) ?_) rfl rfl
    intro o e
    cases e
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨ho, hn⟩
      have := Budget.stmt_site hb rfl ho
      omega
    · simp only [alphaS, alpha, symOrDeep, List.map_nil, List.length_nil, Nat.zero_le, ite_true]
      exact hok.ok.freshS a rfl
    · simp [alphaS, alpha, symOrDeep]
  | @call ret a args _ h' hh =>
    have hargs : ∀ v ∈ args, v ∈ ctx.vars := fun v hv => hok.ok.vars v (by simp [Stmt.vars, hv])
    have h1 := InvS.havocH h hargs (hok.callH a rfl) hh
    show InvS ctx src _ ((X.havocH ctx args a).setRet ret [.sym (.fresh a) []])
    refine InvS.congr (s := { s with heap := h' }.setRet ret
      (some (.sym (.fresh a (s.cnt a)) []))) ?_ rfl rfl
    cases ret with
    | none => exact h1
    | some x =>
      refine InvS.setVar h1 (hok.ok.vars x (by simp [Stmt.vars])) ?_
      intro o e
      cases e
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨ho, hn⟩
        have := Budget.stmt_site hb rfl ho
        omega
      · simp only [alphaS, alpha, symOrDeep, List.map_nil, List.length_nil, Nat.zero_le, ite_true]
        exact hok.ok.freshS a rfl
      · simp [alphaS, alpha, symOrDeep]

/-- A loop keeps an invariant state `Y` if one run of the body keeps it. -/
theorem loop_keepsS {ctx : Ctx} {body : Prog} {Y : AState} (P : CState → Prop)
    (hstep : ∀ s t, P s → InvS ctx src s Y → ExecS src body s t → P t ∧ InvS ctx src t Y) :
    ∀ {s u : CState}, ExecS src (.loop body) s u → P s → InvS ctx src s Y → InvS ctx src u Y := by
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
theorem analyze_soundS (ctx : Ctx) (hc : CtxOK ctx) :
    ∀ (q : Prog) {s s' : CState} {X : AState}, (∀ st ∈ q.stmts, StmtOKH ctx st) →
      Budget ctx q s → InvS ctx src s X → ExecS src q s s' → InvS ctx src s' (analyzeH ctx q X) := by
  intro q
  induction q with
  | skip => intro s s' X _ _ h hx; cases hx; exact h
  | stmt st =>
    intro s s' X hok hb h hx
    cases hx with
    | stmt hs => exact step_soundS hc (hok st (List.mem_singleton.mpr rfl)) hb h hs
  | seq p q ihp ihq =>
    intro s s' X hok hb h hx
    cases hx with
    | seq h1 h2 =>
      have hokp : ∀ st ∈ p.stmts, StmtOKH ctx st :=
        fun st hs => hok st (List.mem_append.mpr (Or.inl hs))
      have hokq : ∀ st ∈ q.stmts, StmtOKH ctx st :=
        fun st hs => hok st (List.mem_append.mpr (Or.inr hs))
      exact ihq hokq (Budget.seqR hb h1.toExec) (ihp hokp (Budget.seqL hb) h h1) h2
  | choice p q ihp ihq =>
    intro s s' X hok hb h hx
    have hokp : ∀ st ∈ p.stmts, StmtOKH ctx st :=
      fun st hs => hok st (List.mem_append.mpr (Or.inl hs))
    have hokq : ∀ st ∈ q.stmts, StmtOKH ctx st :=
      fun st hs => hok st (List.mem_append.mpr (Or.inr hs))
    cases hx with
    | choiceL h1 =>
      exact (ihp hokp (Budget.choiceL hb) h h1).mono (sub_join_left _ _)
    | choiceR h1 =>
      exact (ihq hokq (Budget.choiceR hb) h h1).mono (sub_join_right _ _)
  | loop body ih =>
    intro s s' X hok hb h hx
    show InvS ctx src s' (loopIter ctx (analyzeH ctx body) ctx.fuel X)
    have hY := h.mono (sub_loopIter ctx (analyzeH ctx body) ctx.fuel X)
    refine loop_keepsS (Budget ctx (.loop body)) ?_ hx hb hY
    intro s1 t hb1 hi1 hx1
    refine ⟨Budget.again hb1 hx1.toExec, ?_⟩
    have hf := ih hok (Budget.body hb1) hi1 hx1
    rcases loopIter_post ctx (analyzeH ctx body) ctx.fuel X with hpost | ⟨W, hW⟩
    · exact hf.mono_leOn hpost
    · rw [hW]; exact hf.top W


/-- The entry states satisfy the strict invariant. -/
theorem inv_initS {ctx : Ctx} (hc : CtxOK ctx) {fr : Frame} (hf : FrameOK ctx fr) :
    InvS ctx src (CState.init fr) (ainit ctx.K fr) where
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
      simp only [alphaS, alpha, symOrDeep, List.map_nil, List.length_nil, Nat.zero_le, ite_true]
      exact hf.roots x r e
  heapLive o c o' hd hh := by
    change cdefault o c = some o' at hh
    cases o with
    | alloc s n => cases hh
    | sym b p => cases hh; cases b <;> simp_all [Dead]
  heapIn o c o' _ hin hc1 hh := by
    change cdefault o c = some o' at hh
    exact hc.dflt _ hin _ hc1 _ (alphaS_cdefault ctx.K src hh)
  allocHeld o c s n hh := by
    change cdefault o c = some (.alloc s n) at hh
    cases o with
    | alloc _ _ => cases hh
    | sym _ _ => cases hh
  env x _ o he := by
    change (fr.root? x).map _ = some o at he
    show alphaS ctx.K src o ∈ (match fr.root? x with
      | some r => [Origin.sym (.root r) []] | none => [])
    cases e : fr.root? x with
    | none => rw [e] at he; cases he
    | some r =>
      rw [e] at he; cases he
      simp only [alphaS, alpha, symOrDeep, List.map_nil, List.length_nil, Nat.zero_le, ite_true]
      exact List.mem_singleton.mpr rfl
  heap o c o' _ _ _ hh := by
    change cdefault o c = some o' at hh
    exact alphaS_cdefault ctx.K src hh

/-! ## Queries -/

/-- The abstract path evaluation contains the origin of the concrete path value. -/
theorem readPath_soundS {ctx : Ctx} {st : CState} {X : AState} (h : InvS ctx src st X) :
    ∀ {cx : List Cell} {o0 o : Obj} {S : List Origin}, (∀ c ∈ cx, c.abs ∈ ctx.cells) →
      ¬ Dead ctx.once o0 → alphaS ctx.K src o0 ∈ ctx.origins → alphaS ctx.K src o0 ∈ S →
      readPath st.heap o0 cx = some o → alphaS ctx.K src o ∈ aevalFrom X S (cx.map Cell.abs)
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
      exact readPath_soundS (cx := cs) h (fun c' h' => hcs c' (List.mem_cons_of_mem _ h'))
        (h.heapLive o0 c o1 hd e) (h.heapIn o0 c o1 hd hin hc e)
        (mem_aread.mpr ⟨_, hS, h.heap o0 c o1 hd hin hc e⟩) hr

/-- The abstract evaluation of an access path contains the origin of the concrete value. -/
theorem evalPath_soundS {ctx : Ctx} {st : CState} {X : AState} (h : InvS ctx src st X)
    {x : Var} {cx : List Cell} {o : Obj} (hcs : ∀ c ∈ cx, c.abs ∈ ctx.cells)
    (he : evalPath st x cx = some o) : alphaS ctx.K src o ∈ aevalPath X x (cx.map Cell.abs) := by
  unfold evalPath at he
  cases e : st.env x with
  | none => rw [e] at he; cases he
  | some o0 =>
    rw [e] at he
    have hx : x ∈ ctx.vars := by
      by_cases hx : x ∈ ctx.vars
      · exact hx
      · rw [h.outside x hx] at e; cases e
    exact readPath_soundS h hcs (h.envOk x o0 e).1 (h.envOk x o0 e).2 (h.env x hx o0 e) he

/-! ## The universe of a program with per-cell havoc -/

/-- Membership in the per-cell havoc origins. -/
theorem mem_havocCells {K : Nat} {keys : List Origin} {cells : List ACell} {calls : List Site}
    {o : Origin} :
    o ∈ havocCells K keys cells calls ↔ ∃ s ∈ calls, ∃ a ∈ keys, ∃ c ∈ cells,
      (∃ q ∈ pathsUpTo cells K, o = .hsym s a c q) ∨ o = .hdeep s a c := by
  simp only [havocCells, List.mem_flatMap, List.mem_append, List.mem_map, List.mem_singleton]
  constructor
  · rintro ⟨s, hs, a, ha, c, hc, ⟨q, hq, rfl⟩ | rfl⟩
    · exact ⟨s, hs, a, ha, c, hc, Or.inl ⟨q, hq, rfl⟩⟩
    · exact ⟨s, hs, a, ha, c, hc, Or.inr rfl⟩
  · rintro ⟨s, hs, a, ha, c, hc, ⟨q, hq, rfl⟩ | rfl⟩
    · exact ⟨s, hs, a, ha, c, hc, Or.inl ⟨q, hq, rfl⟩⟩
    · exact ⟨s, hs, a, ha, c, hc, Or.inr rfl⟩

/-- The foundation context and the per-cell havoc context have the same cells. -/
theorem ctxH_cells (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    (ctxH eu K fr p qf).cells = (ctxE eu K fr p qf).cells := rfl

/-- The per-cell havoc universe contains the foundation universe. -/
theorem ctxH_origins_base {eu : Bool} {K : Nat} {fr : Frame} {p : Prog} {qf : List Field}
    {o : Origin} (h : o ∈ (ctxE eu K fr p qf).origins) : o ∈ (ctxH eu K fr p qf).origins :=
  List.mem_append_left _ h

/-- The key of each origin of the per-cell havoc universe is in the foundation universe. -/
theorem keyOf_mem {eu : Bool} {K : Nat} {fr : Frame} {p : Prog} {qf : List Field} {a : Origin}
    (h : a ∈ (ctxH eu K fr p qf).origins) : keyOf a ∈ (ctxE eu K fr p qf).origins := by
  rcases List.mem_append.mp h with h | h
  · have h' := h
    rcases mem_originsOf.mp h with ⟨b, _, ⟨q, _, rfl⟩ | rfl⟩ | ⟨s, _, rfl⟩ | ⟨s, _, rfl⟩ <;>
      exact h'
  · obtain ⟨s, hs, _, _, _, _, ⟨q, _, rfl⟩ | rfl⟩ := mem_havocCells.mp h <;>
    · simp only [keyOf, ctxE, Ctx.ofProg]
      exact mem_originsOf.mpr (Or.inr (Or.inr ⟨s, hs, rfl⟩))

/-- The per-cell havoc context of a program is closed. -/
theorem ctxH_ok (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    CtxOK (ctxH eu K fr p qf) where
  elem := (ctxE_ok eu K fr p qf).elem
  dflt o ho c hc o' ho' := by
    rcases List.mem_append.mp ho with ho | ho
    · exact ctxH_origins_base ((ctxE_ok eu K fr p qf).dflt o ho c hc o' ho')
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
        exact mem_havocCells.mpr ⟨s, hs, a, ha, c0, hc0, Or.inr ho'⟩

/-- The frame fits the per-cell havoc context of a program. -/
theorem ctxH_frame (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    FrameOK (ctxH eu K fr p qf) fr where
  vars := (ctxE_frame eu K fr p qf).vars
  roots x r he := ctxH_origins_base ((ctxE_frame eu K fr p qf).roots x r he)

/-- Each statement of a program fits the per-cell havoc context of the program. -/
theorem ctxH_stmts (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    ∀ st ∈ p.stmts, StmtOKH (ctxH eu K fr p qf) st := by
  intro st hst
  have h0 := ctxE_stmts eu K fr p qf st hst
  refine ⟨⟨h0.vars, h0.fields, fun s hs => ctxH_origins_base (h0.newS s hs),
    fun s hs => ctxH_origins_base (h0.freshS s hs),
    fun s hs => ctxH_origins_base (h0.callS s hs)⟩, ?_⟩
  intro s hs a ha c hc
  apply List.mem_append_right
  refine mem_havocCells.mpr ⟨s, List.mem_filterMap.mpr ⟨st, hst, hs⟩, keyOf a, keyOf_mem ha,
    c, hc, Or.inl ⟨[], mem_pathsUpTo.mpr ⟨Nat.zero_le _, fun _ h => by cases h⟩, rfl⟩⟩

/-- The once budget of a program holds at the entry state for the per-cell havoc context. -/
theorem ctxH_budget (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    Budget (ctxH eu K fr p qf) p (CState.init fr) :=
  ctxE_budget eu K fr p qf

/-! ## Soundness -/

/-- Soundness of per-cell havoc under strict A2, for each naming `src` and both strong-update
policies: each strict one-execution alias is a may-alias of `mayProgH`. -/
theorem csoundH (src : Nat → Obj × Cell) (eu : Bool) (K : Nat) (fr : Frame) (p : Prog)
    (x : Var) (px : List Cell) (y : Var) (py : List Cell) (h : CAliasS src fr p x px y py) :
    mayProgH eu K fr p x (px.map Cell.abs) y (py.map Cell.abs) = true := by
  obtain ⟨st, hx, o, h1, h2⟩ := h
  let qf := afields (px.map Cell.abs) ++ afields (py.map Cell.abs)
  have hinv := analyze_soundS _ (ctxH_ok eu K fr p qf) p (ctxH_stmts eu K fr p qf)
    (ctxH_budget eu K fr p qf) (inv_initS (src := src) (ctxH_ok eu K fr p qf)
      (ctxH_frame eu K fr p qf)) hx
  have hcx := query_cells (cells := p.fields) qf (fun a ha => List.mem_append.mpr (Or.inl ha))
  have hcy := query_cells (cells := p.fields) qf (fun a ha => List.mem_append.mpr (Or.inr ha))
  exact may_iff.mpr ⟨_, evalPath_soundS hinv hcx h1, evalPath_soundS hinv hcy h2⟩

/-- Under strict A2, no execution aliases two paths for which `mayProgH` answers false. -/
theorem no_alias_of_mayProgH (src : Nat → Obj × Cell) (eu : Bool) (K : Nat) (fr : Frame)
    (p : Prog) (x : Var) (px : List Cell) (y : Var) (py : List Cell)
    (h : mayProgH eu K fr p x (px.map Cell.abs) y (py.map Cell.abs) = false) :
    ¬ CAliasS src fr p x px y py := by
  intro ha
  have := csoundH src eu K fr p x px y py ha
  rw [h] at this; cases this

end DirectedAlias.Sound.Havoc

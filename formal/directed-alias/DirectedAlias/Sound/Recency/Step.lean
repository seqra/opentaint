import DirectedAlias.Sound.Recency.Concept

/-!
# Soundness of the recency refinement: invariant and local soundness

The invariant is the invariant of concept C with the state-dependent abstraction `alphaR`,
and three more facts about allocations: each held allocation exists (its index is below
the counter), and an allocation that does not exist yet has null cells.
The new step is `retire_inv`: a counter bump keeps the invariant for `retire`.
-/

namespace DirectedAlias.Sound.Recency

open DirectedAlias DirectedAlias.Sound

/-- A statement fits the recency universe of a context. -/
structure StmtOKR (ctx : Ctx) (st : Stmt) : Prop where
  vars : ∀ v ∈ st.vars, v ∈ ctx.vars
  fields : ∀ f ∈ st.fields, ACell.fld f ∈ ctx.cells
  newS : ∀ s, st.newSite? = some s → rNew s ∈ ctx.origins
  freshS : ∀ s, st.freshSite? = some s → Origin.sym (.fresh s) [] ∈ ctx.origins
  callS : ∀ s, st.callSite? = some s → Origin.havoc s ∈ ctx.origins

/-- A recency context is closed, and it has both origins of a site or none. -/
structure CtxROK (ctx : Ctx) : Prop where
  base : CtxOK ctx
  newOld : ∀ s, rNew s ∈ ctx.origins → rOld s ∈ ctx.origins
  oldNew : ∀ s, rOld s ∈ ctx.origins → rNew s ∈ ctx.origins

/-- The simulation invariant with recency. -/
structure InvR (ctx : Ctx) (st : CState) (X : AState) : Prop where
  outside : ∀ x, x ∉ ctx.vars → st.env x = none
  envOk : ∀ x o, st.env x = some o → ¬ Dead ctx.once o ∧ alphaR ctx.K st o ∈ ctx.origins
  heapLive : ∀ o c o', ¬ Dead ctx.once o → st.heap o c = some o' → ¬ Dead ctx.once o'
  heapIn : ∀ o c o', ¬ Dead ctx.once o → alphaR ctx.K st o ∈ ctx.origins → c.abs ∈ ctx.cells →
    st.heap o c = some o' → alphaR ctx.K st o' ∈ ctx.origins
  allocHeld : ∀ o c s n, st.heap o c = some (.alloc s n) →
    ¬ Dead ctx.once o ∧ alphaR ctx.K st o ∈ ctx.origins ∧ c.abs ∈ ctx.cells
  envCr : ∀ x s n, st.env x = some (.alloc s n) → n < st.cnt s
  heapCr : ∀ o c s n, st.heap o c = some (.alloc s n) → n < st.cnt s
  fresh : ∀ s n c, st.cnt s ≤ n → st.heap (.alloc s n) c = none
  env : ∀ x ∈ ctx.vars, ∀ o, st.env x = some o → alphaR ctx.K st o ∈ X.env x
  heap : ∀ o c o', ¬ Dead ctx.once o → alphaR ctx.K st o ∈ ctx.origins → c.abs ∈ ctx.cells →
    st.heap o c = some o' → alphaR ctx.K st o' ∈ X.heap (alphaR ctx.K st o) c.abs

/-- The recency invariant is closed upward under state inclusion. -/
theorem InvR.mono {ctx : Ctx} {st : CState} {X Y : AState} (h : InvR ctx st X)
    (hs : X.Sub Y) : InvR ctx st Y :=
  { h with
    env := fun x hx o he => hs.1 x (h.env x hx o he)
    heap := fun o c o' hd ho hc hh => hs.2 _ _ (h.heap o c o' hd ho hc hh) }

/-- The recency invariant is closed upward under inclusion on the universe. -/
theorem InvR.mono_leOn {ctx : Ctx} {st : CState} {X Y : AState} (h : InvR ctx st X)
    (hs : leOn ctx X Y = true) : InvR ctx st Y := by
  obtain ⟨h1, h2⟩ := leOn_iff.mp hs
  exact { h with
    env := fun x hx o he => h1 x hx (h.env x hx o he)
    heap := fun o c o' hd ho hc hh => h2 _ ho _ hc (h.heap o c o' hd ho hc hh) }

/-- Each top state simulates each concrete state with the concrete facts. -/
theorem InvR.top {ctx : Ctx} {st : CState} {X : AState} (h : InvR ctx st X) (W : AState) :
    InvR ctx st (top ctx W) :=
  { h with
    env := fun x _ o he => mem_uni.mpr (Or.inl (h.envOk x o he).2)
    heap := fun o c o' hd ho hc hh => mem_uni.mpr (Or.inl (h.heapIn o c o' hd ho hc hh)) }

/-! ## The abstraction -/

/-- The recency abstraction of a symbolic object is its plain abstraction. -/
theorem alphaR_sym (K : Nat) (st : CState) (b : Base) (p : List Cell) :
    alphaR K st (.sym b p) = alpha K (.sym b p) := rfl

/-- The recency abstraction does not read the environment or the heap. -/
theorem alphaR_congr {K : Nat} {s s' : CState} (h : s'.cnt = s.cnt) (o : Obj) :
    alphaR K s' o = alphaR K s o := by
  cases o with
  | sym b p => rfl
  | alloc a n => simp only [alphaR, h]

/-- The two origins of a site are different. -/
theorem rOld_ne_rNew (s s' : Site) : rOld s ≠ rNew s' := by
  intro h
  have : @Eq Nat (2 * s + 1) (2 * s') := Origin.alloc.inj h
  omega

/-- The new origins of two sites are equal only for one site. -/
theorem rNew_inj {s s' : Site} (h : rNew s = rNew s') : s = s' := by
  have : @Eq Nat (2 * s) (2 * s') := Origin.alloc.inj h
  show @Eq Nat s s'
  omega

/-- The renaming never gives the new origin of the site. -/
theorem renameO_ne_new (s : Site) (o : Origin) : renameO s o ≠ rNew s := by
  unfold renameO
  split
  · exact rOld_ne_rNew s s
  · assumption

/-- A counter bump of site `s` renames the abstraction of every object except the next
object of `s`. -/
theorem alphaR_bump (K : Nat) (st : CState) (s : Site) {o : Obj}
    (h : o ≠ .alloc s (st.cnt s)) : alphaR K (st.bump s) o = renameO s (alphaR K st o) := by
  cases o with
  | sym b p =>
    have hn : alpha K (.sym b p) ≠ rNew s := by
      cases b with
      | root r => simp only [alpha, symOrDeep]; split <;> simp [rNew]
      | fresh a n => simp only [alpha, symOrDeep]; split <;> simp [rNew]
      | havoc a n k => simp [alpha, rNew]
    rw [alphaR_sym]; unfold renameO; exact (if_neg hn).symm
  | alloc a n =>
    show (if n + 1 = fupd st.cnt s (st.cnt s + 1) a then rNew a else rOld a) =
      renameO s (if n + 1 = st.cnt a then rNew a else rOld a)
    by_cases e : a = s
    · subst e
      rw [fupd_same]
      have hn : n ≠ st.cnt a := fun e => h (by rw [e])
      rw [if_neg (by omega)]
      by_cases e2 : n + 1 = st.cnt a
      · rw [if_pos e2]; simp [renameO]
      · rw [if_neg e2]; simp only [renameO, if_neg (rOld_ne_rNew a a)]
    · rw [fupd_ne _ _ e]
      by_cases e2 : n + 1 = st.cnt a
      · rw [if_pos e2]
        simp only [renameO]
        rw [if_neg (fun h => e (rNew_inj h))]
      · rw [if_neg e2]; simp only [renameO, if_neg (rOld_ne_rNew a s)]

/-- An origin and its renaming are in the universe together. -/
theorem renameO_mem {ctx : Ctx} (hc : CtxROK ctx) (s : Site) {o : Origin}
    (h : o ∈ ctx.origins) : renameO s o ∈ ctx.origins := by
  unfold renameO
  split
  · rename_i e; subst e; exact hc.newOld s h
  · exact h

/-- If the renaming is in the universe, the origin is in the universe. -/
theorem mem_of_renameO {ctx : Ctx} (hc : CtxROK ctx) (s : Site) {o : Origin}
    (h : renameO s o ∈ ctx.origins) : o ∈ ctx.origins := by
  unfold renameO at h
  split at h
  · rename_i e; subst e; exact hc.oldNew s h
  · exact h

/-! ## Retire -/

/-- A counter bump of site `s` keeps the invariant for `retire s`. -/
theorem retire_inv {ctx : Ctx} (hc : CtxROK ctx) {st : CState} {X : AState} (s : Site)
    (h : InvR ctx st X) : InvR ctx (st.bump s) (retire s X) := by
  have hne_env : ∀ x o, st.env x = some o → o ≠ .alloc s (st.cnt s) := by
    intro x o he e; subst e; have := h.envCr x s _ he; omega
  have hne_heap : ∀ o c o', st.heap o c = some o' → o' ≠ .alloc s (st.cnt s) := by
    intro o c o' he e; subst e; have := h.heapCr o c s _ he; omega
  have hne_src : ∀ o c o', st.heap o c = some o' → o ≠ .alloc s (st.cnt s) := by
    intro o c o' he e; subst e; rw [h.fresh s _ c (Nat.le_refl _)] at he; cases he
  have hcnt : ∀ a, st.cnt a ≤ (st.bump s).cnt a := by
    intro a
    show st.cnt a ≤ fupd st.cnt s (st.cnt s + 1) a
    by_cases e : a = s
    · subst e; rw [fupd_same]; exact Nat.le_succ _
    · rw [fupd_ne _ _ e]; exact Nat.le_refl _
  exact {
    outside := h.outside
    envOk := fun x o he => by
      refine ⟨(h.envOk x o he).1, ?_⟩
      rw [alphaR_bump _ _ _ (hne_env x o he)]
      exact renameO_mem hc s (h.envOk x o he).2
    heapLive := h.heapLive
    heapIn := fun o c o' hd hin hc1 he => by
      change st.heap o c = some o' at he
      rw [alphaR_bump _ _ _ (hne_src o c o' he)] at hin
      rw [alphaR_bump _ _ _ (hne_heap o c o' he)]
      exact renameO_mem hc s (h.heapIn o c o' hd (mem_of_renameO hc s hin) hc1 he)
    allocHeld := fun o c a n he => by
      change st.heap o c = some (.alloc a n) at he
      obtain ⟨h1, h2, h3⟩ := h.allocHeld o c a n he
      refine ⟨h1, ?_, h3⟩
      rw [alphaR_bump _ _ _ (hne_src o c _ he)]
      exact renameO_mem hc s h2
    envCr := fun x a n he => Nat.lt_of_lt_of_le (h.envCr x a n he) (hcnt a)
    heapCr := fun o c a n he => Nat.lt_of_lt_of_le (h.heapCr o c a n he) (hcnt a)
    fresh := fun a n c hn => h.fresh a n c (Nat.le_trans (hcnt a) hn)
    env := fun x hx o he => by
      rw [alphaR_bump _ _ _ (hne_env x o he)]
      exact List.mem_map.mpr ⟨_, h.env x hx o he, rfl⟩
    heap := fun o c o' hd hin hc1 he => by
      change st.heap o c = some o' at he
      rw [alphaR_bump _ _ _ (hne_src o c o' he)] at hin ⊢
      rw [alphaR_bump _ _ _ (hne_heap o c o' he)]
      have hold := h.heap o c o' hd (mem_of_renameO hc s hin) hc1 he
      show _ ∈ (if renameO s (alphaR ctx.K st o) = rNew s then []
        else if renameO s (alphaR ctx.K st o) = rOld s then
          renameL s (uni (X.heap (rNew s) c.abs) (X.heap (rOld s) c.abs))
        else renameL s (X.heap (renameO s (alphaR ctx.K st o)) c.abs))
      rw [if_neg (renameO_ne_new s _)]
      split
      · rename_i e
        refine List.mem_map.mpr ⟨_, mem_uni.mpr ?_, rfl⟩
        unfold renameO at e
        split at e
        · rename_i e2; rw [e2] at hold; exact Or.inl hold
        · rw [e] at hold; exact Or.inr hold
      · rename_i e
        have e3 : renameO s (alphaR ctx.K st o) = alphaR ctx.K st o := by
          unfold renameO at e ⊢
          split
          · rename_i e2; rw [if_pos e2] at e; exact absurd rfl e
          · rfl
        rw [e3]
        exact List.mem_map.mpr ⟨_, hold, rfl⟩ }

/-! ## Updates -/

/-- Setting a variable keeps the recency invariant if the abstract set covers the new value. -/
theorem InvR.setVar {ctx : Ctx} {st : CState} {X : AState} {x : Var} {v : Val}
    {S : List Origin} (h : InvR ctx st X) (hx : x ∈ ctx.vars)
    (hv : ∀ o, v = some o → ¬ Dead ctx.once o ∧ alphaR ctx.K st o ∈ ctx.origins ∧
      alphaR ctx.K st o ∈ S)
    (hcr : ∀ a n, v = some (.alloc a n) → n < st.cnt a) :
    InvR ctx (st.setVar x v) (X.setVar x S) where
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
  envCr y a n he := by
    change fupd st.env x v y = _ at he
    by_cases e : y = x
    · subst e; rw [fupd_same] at he; exact hcr a n he
    · rw [fupd_ne _ _ e] at he; exact h.envCr y a n he
  heapCr := h.heapCr
  fresh := h.fresh
  env y hy o he := by
    change fupd st.env x v y = some o at he
    show alphaR ctx.K st o ∈ fupd X.env x S y
    by_cases e : y = x
    · subst e; rw [fupd_same] at he; rw [fupd_same]; exact (hv o he).2.2
    · rw [fupd_ne _ _ e] at he; rw [fupd_ne _ _ e]; exact h.env y hy o he
  heap := h.heap

/-- A concrete store keeps the concrete facts. The caller proves the abstract heap facts. -/
theorem InvR.write {ctx : Ctx} {st : CState} {X Y : AState} {o : Obj} {c : Cell} {v : Val}
    (h : InvR ctx st X) (ho : ¬ Dead ctx.once o ∧ alphaR ctx.K st o ∈ ctx.origins)
    (hocr : ∀ a n, o = .alloc a n → n < st.cnt a)
    (hc : c.abs ∈ ctx.cells)
    (hv : ∀ o', v = some o' → ¬ Dead ctx.once o' ∧ alphaR ctx.K st o' ∈ ctx.origins)
    (hvcr : ∀ a n, v = some (.alloc a n) → n < st.cnt a)
    (henv : ∀ x ∈ ctx.vars, ∀ o', st.env x = some o' → alphaR ctx.K st o' ∈ Y.env x)
    (hheap : ∀ o1 c1 o2, ¬ Dead ctx.once o1 → alphaR ctx.K st o1 ∈ ctx.origins →
      c1.abs ∈ ctx.cells → fupd2 st.heap o c v o1 c1 = some o2 →
      alphaR ctx.K st o2 ∈ Y.heap (alphaR ctx.K st o1) c1.abs) :
    InvR ctx (st.setCell o c v) Y where
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
  envCr := h.envCr
  heapCr o1 c1 a n hh := by
    change fupd2 st.heap o c v o1 c1 = some (.alloc a n) at hh
    by_cases e : o1 = o ∧ c1 = c
    · obtain ⟨rfl, rfl⟩ := e; rw [fupd2_same] at hh; exact hvcr a n hh
    · rw [fupd2_ne _ _ e] at hh; exact h.heapCr o1 c1 a n hh
  fresh a n c1 hn := by
    show fupd2 st.heap o c v (.alloc a n) c1 = none
    have hne : ¬ (Obj.alloc a n = o ∧ c1 = c) := by
      rintro ⟨e, _⟩
      have := hocr a n e.symm
      change st.cnt a ≤ n at hn
      omega
    rw [fupd2_ne _ _ hne]
    exact h.fresh a n c1 hn
  env := henv
  heap := hheap

/-- A weak store keeps the recency invariant. -/
theorem InvR.weak {ctx : Ctx} {st : CState} {X : AState} {o : Obj} {c : Cell} {v : Val}
    {os : List Origin} {S : List Origin}
    (h : InvR ctx st X) (ho : ¬ Dead ctx.once o ∧ alphaR ctx.K st o ∈ ctx.origins)
    (hocr : ∀ a n, o = .alloc a n → n < st.cnt a)
    (hc : c.abs ∈ ctx.cells) (hos : alphaR ctx.K st o ∈ os)
    (hv : ∀ o', v = some o' → ¬ Dead ctx.once o' ∧ alphaR ctx.K st o' ∈ ctx.origins ∧
      alphaR ctx.K st o' ∈ S)
    (hvcr : ∀ a n, v = some (.alloc a n) → n < st.cnt a) :
    InvR ctx (st.setCell o c v) (X.weakStore os c.abs S) := by
  apply InvR.write (Y := X.weakStore os c.abs S) h ho hocr hc
    (fun o' e => ⟨(hv o' e).1, (hv o' e).2.1⟩) hvcr h.env
  intro o1 c1 o2 hd hin hc1 hh
  show alphaR ctx.K st o2 ∈ (if c1.abs = c.abs ∧ alphaR ctx.K st o1 ∈ os then
    uni S (X.heap (alphaR ctx.K st o1) c1.abs) else X.heap (alphaR ctx.K st o1) c1.abs)
  by_cases e : o1 = o ∧ c1 = c
  · obtain ⟨rfl, rfl⟩ := e
    rw [fupd2_same] at hh
    rw [if_pos ⟨rfl, hos⟩]
    exact mem_uni.mpr (Or.inl (hv o2 hh).2.2)
  · rw [fupd2_ne _ _ e] at hh
    have := h.heap o1 c1 o2 hd hin hc1 hh
    split
    · exact mem_uni.mpr (Or.inr this)
    · exact this

/-- A strong store keeps the recency invariant if the target origin is unique. -/
theorem InvR.strong {ctx : Ctx} {st : CState} {X : AState} {o : Obj} {f : Field} {v : Val}
    {S : List Origin}
    (h : InvR ctx st X) (ho : ¬ Dead ctx.once o ∧ alphaR ctx.K st o ∈ ctx.origins)
    (hocr : ∀ a n, o = .alloc a n → n < st.cnt a)
    (hc : ACell.fld f ∈ ctx.cells)
    (huniq : ∀ o1, ¬ Dead ctx.once o1 → alphaR ctx.K st o1 = alphaR ctx.K st o → o1 = o)
    (hv : ∀ o', v = some o' → ¬ Dead ctx.once o' ∧ alphaR ctx.K st o' ∈ ctx.origins ∧
      alphaR ctx.K st o' ∈ S)
    (hvcr : ∀ a n, v = some (.alloc a n) → n < st.cnt a) :
    InvR ctx (st.setCell o (.fld f) v) (X.setCell (alphaR ctx.K st o) (.fld f) S) := by
  apply InvR.write (Y := X.setCell (alphaR ctx.K st o) (.fld f) S) (c := .fld f) h ho hocr hc
    (fun o' e => ⟨(hv o' e).1, (hv o' e).2.1⟩) hvcr h.env
  intro o1 c1 o2 hd hin hc1 hh
  show alphaR ctx.K st o2 ∈ fupd2 X.heap (alphaR ctx.K st o) (.fld f) S (alphaR ctx.K st o1) c1.abs
  by_cases e : o1 = o ∧ c1 = .fld f
  · obtain ⟨rfl, rfl⟩ := e
    rw [fupd2_same] at hh
    exact (fupd2_same X.heap (alphaR ctx.K st o1) (ACell.fld f) S).symm ▸ (hv o2 hh).2.2
  · rw [fupd2_ne _ _ e] at hh
    have e2 : ¬ (alphaR ctx.K st o1 = alphaR ctx.K st o ∧ c1.abs = .fld f) := by
      rintro ⟨h1, h2⟩
      apply e
      refine ⟨huniq o1 hd h1, ?_⟩
      cases c1 with
      | fld g => simp only [Cell.abs, ACell.fld.injEq] at h2; rw [h2]
      | elem i => simp [Cell.abs] at h2
    rw [fupd2_ne _ _ e2]
    exact h.heap o1 c1 o2 hd hin hc1 hh

/-- A unique recency origin denotes at most one object that is not dead. -/
theorem unique_objR {K : Nat} {once : Site → Bool} {eu : Bool} {st : CState} {o o' : Obj}
    (hu : uniqueR once eu (alphaR K st o) = true) (hd : ¬ Dead once o) (hd' : ¬ Dead once o')
    (ha : alphaR K st o' = alphaR K st o) : o' = o := by
  cases o with
  | sym b p =>
    cases o' with
    | sym b' p' =>
      have hu' : (alpha K (.sym b p)).uniqueB once eu = true := by
        cases hb : alpha K (.sym b p) with
        | alloc a =>
          exfalso
          cases b with
          | root r => simp only [alpha, symOrDeep] at hb; split at hb <;> cases hb
          | fresh a n => simp only [alpha, symOrDeep] at hb; split at hb <;> cases hb
          | havoc a n k => cases hb
        | sym _ _ => rw [alphaR_sym, hb] at hu; exact hu
        | deep _ => rw [alphaR_sym, hb] at hu; exact hu
        | havoc _ => rw [alphaR_sym, hb] at hu; exact hu
        | hsym _ _ _ _ => rw [alphaR_sym, hb] at hu; exact hu
        | hdeep _ _ _ => rw [alphaR_sym, hb] at hu; exact hu
      exact unique_obj hu' hd hd' ha
    | alloc a n =>
      exfalso
      change (if n + 1 = st.cnt a then rNew a else rOld a) = alpha K (.sym b p) at ha
      cases b with
      | root r =>
        simp only [alpha, symOrDeep] at ha
        split at ha <;> split at ha <;> simp [rNew, rOld] at ha
      | fresh a n => simp only [alpha, symOrDeep] at ha; split at ha <;> split at ha <;> simp [rNew, rOld] at ha
      | havoc a n k => simp only [alpha] at ha; split at ha <;> simp [rNew, rOld] at ha
  | alloc a n =>
    change uniqueR once eu (if n + 1 = st.cnt a then rNew a else rOld a) = true at hu
    by_cases e : n + 1 = st.cnt a
    · rw [if_pos e] at hu
      cases o' with
      | sym b p =>
        exfalso
        change alpha K (.sym b p) = (if n + 1 = st.cnt a then rNew a else rOld a) at ha
        rw [if_pos e] at ha
        cases b with
        | root r => simp only [alpha, symOrDeep] at ha; split at ha <;> simp [rNew] at ha
        | fresh _ _ => simp only [alpha, symOrDeep] at ha; split at ha <;> simp [rNew] at ha
        | havoc _ _ _ => simp [alpha, rNew] at ha
      | alloc a' n' =>
        change (if n' + 1 = st.cnt a' then rNew a' else rOld a') =
          (if n + 1 = st.cnt a then rNew a else rOld a) at ha
        rw [if_pos e] at ha
        split at ha
        · rename_i e'
          have := rNew_inj ha
          subst this
          have : n' = n := by omega
          rw [this]
        · exact absurd ha (rOld_ne_rNew a' a)
    · rw [if_neg e] at hu
      simp [uniqueR, rOld] at hu

end DirectedAlias.Sound.Recency

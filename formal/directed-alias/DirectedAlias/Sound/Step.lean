import DirectedAlias.Sound.Invariant

/-!
# Soundness of concept C: local soundness of each statement

Each lemma shows: if the invariant holds before a concrete step, it holds after the step
for the abstract transfer of the statement. The transfer is not monotone, so the proof
does not use monotonicity.
-/

namespace DirectedAlias.Sound

open DirectedAlias

/-! ## The abstraction of objects -/

/-- The abstraction of a symbolic object is an outer origin. -/
theorem alpha_sym_outer (K : Nat) (b : Base) (p : List Cell) :
    (alpha K (.sym b p)).outer = true := by
  cases b with
  | root r => simp only [alpha, symOrDeep]; split <;> rfl
  | fresh s n => simp only [alpha, symOrDeep]; split <;> rfl
  | havoc s n k => rfl

/-- An object with the origin `sym (root r) q` is the entry object at a path that abstracts to `q`. -/
theorem alpha_eq_root {K : Nat} {o : Obj} {r : Root} {q : List ACell}
    (h : alpha K o = .sym (.root r) q) : ∃ p, o = .sym (.root r) p ∧ p.map Cell.abs = q := by
  cases o with
  | alloc s n => simp [alpha] at h
  | sym b p =>
    cases b with
    | root r' =>
      simp only [alpha, symOrDeep] at h
      split at h
      · cases h; exact ⟨p, rfl, rfl⟩
      · cases h
    | fresh s n => simp only [alpha, symOrDeep] at h; split at h <;> cases h
    | havoc s n k => simp [alpha] at h

/-- An object with the origin `sym (fresh s) q` is a fresh object of site `s` at a path that
abstracts to `q`. -/
theorem alpha_eq_fresh {K : Nat} {o : Obj} {s : Site} {q : List ACell}
    (h : alpha K o = .sym (.fresh s) q) :
    ∃ n p, o = .sym (.fresh s n) p ∧ p.map Cell.abs = q := by
  cases o with
  | alloc s n => simp [alpha] at h
  | sym b p =>
    cases b with
    | root r' => simp only [alpha, symOrDeep] at h; split at h <;> cases h
    | fresh s' n =>
      simp only [alpha, symOrDeep] at h
      split at h
      · cases h; exact ⟨n, p, rfl, rfl⟩
      · cases h
    | havoc s n k => simp [alpha] at h

/-- An object with the origin `alloc s` is an allocation of site `s`. -/
theorem alpha_eq_alloc {K : Nat} {o : Obj} {s : Site} (h : alpha K o = .alloc s) :
    ∃ n, o = .alloc s n := by
  cases o with
  | alloc s' n => simp only [alpha] at h; cases h; exact ⟨n, rfl⟩
  | sym b p =>
    cases b with
    | root r' => simp only [alpha, symOrDeep] at h; split at h <;> cases h
    | fresh s' n => simp only [alpha, symOrDeep] at h; split at h <;> cases h
    | havoc s n k => simp [alpha] at h

/-- The abstraction of concrete paths is injective on paths without array elements. -/
theorem map_abs_inj : ∀ {p p' : List Cell}, p.map Cell.abs = p'.map Cell.abs →
    ACell.elem ∉ p.map Cell.abs → p = p'
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | c :: cs, c' :: cs', h, hn => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [List.map_cons, List.mem_cons, not_or] at hn
    have hc : c = c' := by
      cases c with
      | fld f =>
        cases c' with
        | fld f' => simp only [Cell.abs, ACell.fld.injEq] at h; rw [h.1]
        | elem i => simp [Cell.abs] at h
      | elem i => simp [Cell.abs] at hn
    rw [hc, map_abs_inj h.2 hn.2]

/-- A unique origin denotes at most one object that is not dead. -/
theorem unique_obj {K : Nat} {once : Site → Bool} {eu : Bool} {o o' : Obj}
    (hu : (alpha K o).uniqueB once eu = true) (hd : ¬ Dead once o) (hd' : ¬ Dead once o')
    (ha : alpha K o' = alpha K o) : o' = o := by
  cases hao : alpha K o with
  | sym b q =>
    rw [hao] at hu ha
    cases b with
    | root r =>
      simp only [Origin.uniqueB, Bool.and_eq_true, Bool.not_eq_true'] at hu
      have hq : ACell.elem ∉ q := fun hm => by
        have := List.contains_iff_mem.mpr hm; rw [hu.2] at this; cases this
      obtain ⟨p, rfl, hp⟩ := alpha_eq_root hao
      obtain ⟨p', rfl, hp'⟩ := alpha_eq_root ha
      rw [map_abs_inj (hp'.trans hp.symm) (by rw [hp']; exact hq)]
    | fresh s =>
      simp only [Origin.uniqueB, Bool.and_eq_true, Bool.not_eq_true'] at hu
      have hq : ACell.elem ∉ q := fun hm => by
        have := List.contains_iff_mem.mpr hm; rw [hu.2] at this; cases this
      obtain ⟨n, p, rfl, hp⟩ := alpha_eq_fresh hao
      obtain ⟨n', p', rfl, hp'⟩ := alpha_eq_fresh ha
      have hn : n = 0 := by
        simp only [Dead, not_and] at hd; have := hd hu.1.2; omega
      have hn' : n' = 0 := by
        simp only [Dead, not_and] at hd'; have := hd' hu.1.2; omega
      rw [hn, hn', map_abs_inj (hp'.trans hp.symm) (by rw [hp']; exact hq)]
  | deep b => rw [hao] at hu; simp [Origin.uniqueB] at hu
  | havoc s => rw [hao] at hu; simp [Origin.uniqueB] at hu
  | hsym _ _ _ _ => rw [hao] at hu; simp [Origin.uniqueB] at hu
  | hdeep _ _ _ => rw [hao] at hu; simp [Origin.uniqueB] at hu
  | alloc s =>
    rw [hao] at hu ha
    simp only [Origin.uniqueB] at hu
    obtain ⟨n, rfl⟩ := alpha_eq_alloc hao
    obtain ⟨n', rfl⟩ := alpha_eq_alloc ha
    have hn : n = 0 := by simp only [Dead, not_and] at hd; have := hd hu; omega
    have hn' : n' = 0 := by simp only [Dead, not_and] at hd'; have := hd' hu; omega
    rw [hn, hn']

/-! ## Variable updates -/

/-- Setting a variable keeps the invariant if the abstract set covers the new value. -/
theorem Inv.setVar {ctx : Ctx} {st : CState} {X : AState} {x : Var} {v : Val}
    {S : List Origin} (h : Inv ctx st X) (hx : x ∈ ctx.vars)
    (hv : ∀ o, v = some o → ¬ Dead ctx.once o ∧ alpha ctx.K o ∈ ctx.origins ∧ alpha ctx.K o ∈ S) :
    Inv ctx (st.setVar x v) (X.setVar x S) where
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
    show alpha ctx.K o ∈ fupd X.env x S y
    by_cases e : y = x
    · subst e; rw [fupd_same] at he; rw [fupd_same]; exact (hv o he).2.2
    · rw [fupd_ne _ _ e] at he; rw [fupd_ne _ _ e]; exact h.env y hy o he
  heap := h.heap

/-! ## Heap updates -/

/-- A concrete store keeps the concrete support facts. The caller proves the abstract heap facts. -/
theorem Inv.write {ctx : Ctx} {st : CState} {X Y : AState} {o : Obj} {c : Cell} {v : Val}
    (h : Inv ctx st X) (ho : ¬ Dead ctx.once o ∧ alpha ctx.K o ∈ ctx.origins)
    (hc : c.abs ∈ ctx.cells)
    (hv : ∀ o', v = some o' → ¬ Dead ctx.once o' ∧ alpha ctx.K o' ∈ ctx.origins)
    (henv : ∀ x ∈ ctx.vars, ∀ o', st.env x = some o' → alpha ctx.K o' ∈ Y.env x)
    (hheap : ∀ o1 c1 o2, ¬ Dead ctx.once o1 → alpha ctx.K o1 ∈ ctx.origins →
      c1.abs ∈ ctx.cells → fupd2 st.heap o c v o1 c1 = some o2 →
      alpha ctx.K o2 ∈ Y.heap (alpha ctx.K o1) c1.abs) :
    Inv ctx (st.setCell o c v) Y where
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
theorem Inv.weak {ctx : Ctx} {st : CState} {X : AState} {o : Obj} {c : Cell} {v : Val}
    {os : List Origin} {S : List Origin}
    (h : Inv ctx st X) (ho : ¬ Dead ctx.once o ∧ alpha ctx.K o ∈ ctx.origins)
    (hc : c.abs ∈ ctx.cells) (hos : alpha ctx.K o ∈ os)
    (hv : ∀ o', v = some o' → ¬ Dead ctx.once o' ∧ alpha ctx.K o' ∈ ctx.origins ∧
      alpha ctx.K o' ∈ S) :
    Inv ctx (st.setCell o c v) (X.weakStore os c.abs S) := by
  apply Inv.write (Y := X.weakStore os c.abs S) h ho hc (fun o' e => ⟨(hv o' e).1, (hv o' e).2.1⟩) h.env
  intro o1 c1 o2 hd hin hc1 hh
  show alpha ctx.K o2 ∈ (if c1.abs = c.abs ∧ alpha ctx.K o1 ∈ os then
    uni S (X.heap (alpha ctx.K o1) c1.abs) else X.heap (alpha ctx.K o1) c1.abs)
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

/-- A strong store keeps the invariant if the target origin is unique and the cell is a field. -/
theorem Inv.strong {ctx : Ctx} {st : CState} {X : AState} {o : Obj} {f : Field} {v : Val}
    {S : List Origin}
    (h : Inv ctx st X) (ho : ¬ Dead ctx.once o ∧ alpha ctx.K o ∈ ctx.origins)
    (hc : ACell.fld f ∈ ctx.cells)
    (huniq : ∀ o1, ¬ Dead ctx.once o1 → alpha ctx.K o1 = alpha ctx.K o → o1 = o)
    (hv : ∀ o', v = some o' → ¬ Dead ctx.once o' ∧ alpha ctx.K o' ∈ ctx.origins ∧
      alpha ctx.K o' ∈ S) :
    Inv ctx (st.setCell o (.fld f) v) (X.setCell (alpha ctx.K o) (.fld f) S) := by
  apply Inv.write (Y := X.setCell (alpha ctx.K o) (.fld f) S) (c := .fld f) h ho hc (fun o' e => ⟨(hv o' e).1, (hv o' e).2.1⟩) h.env
  intro o1 c1 o2 hd hin hc1 hh
  show alpha ctx.K o2 ∈ fupd2 X.heap (alpha ctx.K o) (.fld f) S (alpha ctx.K o1) c1.abs
  by_cases e : o1 = o ∧ c1 = .fld f
  · obtain ⟨rfl, rfl⟩ := e
    rw [fupd2_same] at hh
    exact (fupd2_same X.heap (alpha ctx.K o1) (ACell.fld f) S).symm ▸ (hv o2 hh).2.2
  · rw [fupd2_ne _ _ e] at hh
    have e2 : ¬ (alpha ctx.K o1 = alpha ctx.K o ∧ c1.abs = .fld f) := by
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
theorem reachB_of_reach {ctx : Ctx} {st : CState} {X : AState} {args : List Var} {o : Obj}
    (h : Inv ctx st X) (hargs : ∀ a ∈ args, a ∈ ctx.vars) (hr : Reach st args o) :
    reachB ctx X args (alpha ctx.K o) = true := by
  unfold reachB
  cases hR : closeIter ctx.cells X (ctx.origins.length + 1)
      (uni (uniMap X.env args) (ctx.origins.filter Origin.outer)) with
  | none => rfl
  | some R =>
    obtain ⟨hseed, hclosed⟩ := closeIter_spec hR
    have key : (alpha ctx.K o).outer = true ∨ alpha ctx.K o ∈ R := by
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
          have h1 : alpha ctx.K o1 ∈ R := by
            cases ih with
            | inl hout => exact hseed _ (mem_uni.mpr (Or.inr (List.mem_filter.mpr ⟨hin, hout⟩)))
            | inr h => exact h
          exact Or.inr (hclosed _ (mem_succs.mpr ⟨_, h1, _, hc, h.heap _ _ _ hd hin hc hh⟩))
    cases key with
    | inl h1 => simp [h1]
    | inr h1 => simp [h1]

/-- The havoc of a call keeps the invariant. -/
theorem Inv.havoc {ctx : Ctx} {st : CState} {X : AState} {args : List Var} {s n : Nat}
    {h' : Heap} (h : Inv ctx st X) (hargs : ∀ a ∈ args, a ∈ ctx.vars)
    (hs : Origin.havoc s ∈ ctx.origins) (hh : Havoc st args s n h') :
    Inv ctx { st with heap := h' } (X.havoc ctx args s) where
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
  env := h.env
  heap o c o' hd hin hc he := by
    show alpha ctx.K o' ∈ (if c.abs ∈ ctx.cells ∧ reachB ctx X args (alpha ctx.K o) = true then
      uni [.havoc s] (X.heap (alpha ctx.K o) c.abs) else X.heap (alpha ctx.K o) c.abs)
    rcases hh o c with e | ⟨hr, k, e⟩
    · have := h.heap o c o' hd hin hc (e ▸ he)
      split
      · exact mem_uni.mpr (Or.inr this)
      · exact this
    · change h' o c = some o' at he
      rw [e] at he; cases he
      rw [if_pos ⟨hc, reachB_of_reach h hargs hr⟩]
      exact mem_uni.mpr (Or.inl (List.mem_singleton.mpr rfl))

/-! ## One statement -/

/-- Local soundness: one concrete step keeps the invariant for the abstract transfer. -/
theorem step_sound {ctx : Ctx} (hc : CtxOK ctx) {st : Stmt} {s s' : CState} {X : AState}
    (hok : StmtOK ctx st) (hb : Budget ctx (.stmt st) s) (h : Inv ctx s X)
    (hs : SStep st s s') : Inv ctx s' (astep ctx st X) := by
  cases hs with
  | @new x a =>
    refine Inv.congr (Inv.setVar h (hok.vars x (by simp [Stmt.vars])) ?_) rfl rfl
    intro o e
    cases e
    refine ⟨?_, hok.newS a rfl, List.mem_singleton.mpr rfl⟩
    rintro ⟨ho, hn⟩
    have := Budget.stmt_site hb rfl ho
    omega
  | @null x =>
    exact Inv.setVar h (hok.vars x (by simp [Stmt.vars])) (fun o e => by cases e)
  | @copy x y =>
    refine Inv.setVar h (hok.vars x (by simp [Stmt.vars])) ?_
    intro o e
    exact ⟨(h.envOk y o e).1, (h.envOk y o e).2, h.env y (hok.vars y (by simp [Stmt.vars])) o e⟩
  | @load x y f _ o he =>
    refine Inv.setVar h (hok.vars x (by simp [Stmt.vars])) ?_
    intro o' e
    have hd := h.envOk y o he
    have hf : (Cell.fld f).abs ∈ ctx.cells := hok.fields f (by simp [Stmt.fields])
    exact ⟨h.heapLive o _ o' hd.1 e, h.heapIn o _ o' hd.1 hd.2 hf e,
      mem_aread.mpr ⟨_, h.env y (hok.vars y (by simp [Stmt.vars])) o he,
        h.heap o _ o' hd.1 hd.2 hf e⟩⟩
  | @aload x y _ o i he =>
    refine Inv.setVar h (hok.vars x (by simp [Stmt.vars])) ?_
    intro o' e
    have hd := h.envOk y o he
    have hf : (Cell.elem i).abs ∈ ctx.cells := hc.elem
    exact ⟨h.heapLive o _ o' hd.1 e, h.heapIn o _ o' hd.1 hd.2 hf e,
      mem_aread.mpr ⟨_, h.env y (hok.vars y (by simp [Stmt.vars])) o he,
        h.heap o _ o' hd.1 hd.2 hf e⟩⟩
  | @store x f y _ o he =>
    have hd := h.envOk x o he
    have hx := h.env x (hok.vars x (by simp [Stmt.vars])) o he
    have hf : ACell.fld f ∈ ctx.cells := hok.fields f (by simp [Stmt.fields])
    have hv : ∀ o', s.env y = some o' → ¬ Dead ctx.once o' ∧ alpha ctx.K o' ∈ ctx.origins ∧
        alpha ctx.K o' ∈ X.env y := fun o' e =>
      ⟨(h.envOk y o' e).1, (h.envOk y o' e).2, h.env y (hok.vars y (by simp [Stmt.vars])) o' e⟩
    show Inv ctx _ (X.store ctx.once x (.fld f) (X.env y) ctx.entryUnique)
    unfold AState.store
    split
    · rename_i oa hsingle
      have hoa : alpha ctx.K o = oa := (single?_spec hsingle).2 _ hx
      split
      · rename_i hu
        rw [← hoa] at hu ⊢
        exact Inv.strong h hd hf
          (fun o1 hd1 ha => unique_obj hu hd.1 hd1 ha) hv
      · exact Inv.weak (c := .fld f) h hd hf hx hv
    · exact Inv.weak (c := .fld f) h hd hf hx hv
  | @astore x y _ o i he =>
    have hd := h.envOk x o he
    have hx := h.env x (hok.vars x (by simp [Stmt.vars])) o he
    exact Inv.weak (c := .elem i) h hd hc.elem hx (fun o' e =>
      ⟨(h.envOk y o' e).1, (h.envOk y o' e).2, h.env y (hok.vars y (by simp [Stmt.vars])) o' e⟩)
  | @unknown x a =>
    refine Inv.congr (Inv.setVar h (hok.vars x (by simp [Stmt.vars])) ?_) rfl rfl
    intro o e
    cases e
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨ho, hn⟩
      have := Budget.stmt_site hb rfl ho
      omega
    · simp only [alpha, symOrDeep, List.map_nil, List.length_nil, Nat.zero_le, if_true]
      exact hok.freshS a rfl
    · simp [alpha, symOrDeep]
  | @call ret a args _ h' hh =>
    have hargs : ∀ v ∈ args, v ∈ ctx.vars := fun v hv => hok.vars v (by simp [Stmt.vars, hv])
    have h1 := Inv.havoc h hargs (hok.callS a rfl) hh
    show Inv ctx _ ((X.havoc ctx args a).setRet ret [.sym (.fresh a) []])
    refine Inv.congr (s := { s with heap := h' }.setRet ret
      (some (.sym (.fresh a (s.cnt a)) []))) ?_ rfl rfl
    cases ret with
    | none => exact h1
    | some x =>
      refine Inv.setVar h1 (hok.vars x (by simp [Stmt.vars])) ?_
      intro o e
      cases e
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨ho, hn⟩
        have := Budget.stmt_site hb rfl ho
        omega
      · simp only [alpha, symOrDeep, List.map_nil, List.length_nil, Nat.zero_le, if_true]
        exact hok.freshS a rfl
      · simp [alpha, symOrDeep]

end DirectedAlias.Sound

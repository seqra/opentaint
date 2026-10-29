import DirectedAlias.Concept

/-!
# Soundness of concept C: the simulation invariant

The simulation is relative to the finite universe of the context.
It has two parts:
* concrete support facts (they do not mention the abstract state), and
* the abstraction facts (the alpha of each value is in the abstract set).

Dead objects are objects of a `once` site with an execution index of at least one.
No execution makes them, so the invariant does not speak about their cells.
This is what makes the strong update sound.
-/

namespace DirectedAlias.Sound

open DirectedAlias

/-- An object is dead when its site is a `once` site and its execution index is one or more. -/
def Dead (once : Site → Bool) : Obj → Prop
  | .sym (.fresh s n) _ => once s = true ∧ 1 ≤ n
  | .alloc s n => once s = true ∧ 1 ≤ n
  | _ => False

/-- A statement fits the universe of a context: its variables, fields and sites are in it. -/
structure StmtOK (ctx : Ctx) (st : Stmt) : Prop where
  vars : ∀ v ∈ st.vars, v ∈ ctx.vars
  fields : ∀ f ∈ st.fields, ACell.fld f ∈ ctx.cells
  newS : ∀ s, st.newSite? = some s → Origin.alloc s ∈ ctx.origins
  freshS : ∀ s, st.freshSite? = some s → Origin.sym (.fresh s) [] ∈ ctx.origins
  callS : ∀ s, st.callSite? = some s → Origin.havoc s ∈ ctx.origins

/-- A context is closed: it has the array cell, and default contents stay in the universe. -/
structure CtxOK (ctx : Ctx) : Prop where
  elem : ACell.elem ∈ ctx.cells
  dflt : ∀ o ∈ ctx.origins, ∀ c ∈ ctx.cells, ∀ o' ∈ adefault ctx.K o c, o' ∈ ctx.origins

/-- A frame fits the universe of a context. -/
structure FrameOK (ctx : Ctx) (fr : Frame) : Prop where
  vars : ∀ x ∈ fr.vars, x ∈ ctx.vars
  roots : ∀ x r, fr.root? x = some r → Origin.sym (.root r) [] ∈ ctx.origins

/-- The simulation invariant between a concrete state and an abstract state. -/
structure Inv (ctx : Ctx) (st : CState) (X : AState) : Prop where
  outside : ∀ x, x ∉ ctx.vars → st.env x = none
  envOk : ∀ x o, st.env x = some o → ¬ Dead ctx.once o ∧ alpha ctx.K o ∈ ctx.origins
  heapLive : ∀ o c o', ¬ Dead ctx.once o → st.heap o c = some o' → ¬ Dead ctx.once o'
  heapIn : ∀ o c o', ¬ Dead ctx.once o → alpha ctx.K o ∈ ctx.origins → c.abs ∈ ctx.cells →
    st.heap o c = some o' → alpha ctx.K o' ∈ ctx.origins
  allocHeld : ∀ o c s n, st.heap o c = some (.alloc s n) →
    ¬ Dead ctx.once o ∧ alpha ctx.K o ∈ ctx.origins ∧ c.abs ∈ ctx.cells
  env : ∀ x ∈ ctx.vars, ∀ o, st.env x = some o → alpha ctx.K o ∈ X.env x
  heap : ∀ o c o', ¬ Dead ctx.once o → alpha ctx.K o ∈ ctx.origins → c.abs ∈ ctx.cells →
    st.heap o c = some o' → alpha ctx.K o' ∈ X.heap (alpha ctx.K o) c.abs

/-- The once budget: each `once` site runs at most one more time in `q`, and not in a loop. -/
def Budget (ctx : Ctx) (q : Prog) (st : CState) : Prop :=
  ∀ t, ctx.once t = true → st.cnt t + q.sites.count t ≤ 1 ∧ t ∉ q.loopSites

/-! ## Basic lemmas -/

/-- The invariant is closed upward under state inclusion. -/
theorem Inv.mono {ctx : Ctx} {st : CState} {X Y : AState} (h : Inv ctx st X) (hs : X.Sub Y) :
    Inv ctx st Y where
  outside := h.outside
  envOk := h.envOk
  heapLive := h.heapLive
  heapIn := h.heapIn
  allocHeld := h.allocHeld
  env x hx o he := hs.1 x (h.env x hx o he)
  heap o c o' hd ho hc hh := hs.2 _ _ (h.heap o c o' hd ho hc hh)

/-- The invariant is closed upward under inclusion on the universe. -/
theorem Inv.mono_leOn {ctx : Ctx} {st : CState} {X Y : AState} (h : Inv ctx st X)
    (hs : leOn ctx X Y = true) : Inv ctx st Y := by
  obtain ⟨h1, h2⟩ := leOn_iff.mp hs
  exact { outside := h.outside, envOk := h.envOk, heapLive := h.heapLive, heapIn := h.heapIn,
          allocHeld := h.allocHeld,
          env := fun x hx o he => h1 x hx (h.env x hx o he),
          heap := fun o c o' hd ho hc hh => h2 _ ho _ hc (h.heap o c o' hd ho hc hh) }

/-- Each top state simulates each concrete state that has the concrete support facts. -/
theorem Inv.top {ctx : Ctx} {st : CState} {X : AState} (h : Inv ctx st X) (W : AState) :
    Inv ctx st (top ctx W) where
  outside := h.outside
  envOk := h.envOk
  heapLive := h.heapLive
  heapIn := h.heapIn
  allocHeld := h.allocHeld
  env x _ o he := mem_uni.mpr (Or.inl (h.envOk x o he).2)
  heap o c o' hd ho hc hh := mem_uni.mpr (Or.inl (h.heapIn o c o' hd ho hc hh))

/-- The invariant depends only on the environment and the heap, not on the counters. -/
theorem Inv.congr {ctx : Ctx} {s s' : CState} {X : AState} (h : Inv ctx s X)
    (he : s'.env = s.env) (hh : s'.heap = s.heap) : Inv ctx s' X := by
  obtain ⟨a, b, c, d, e, f, g⟩ := h
  exact ⟨by rw [he]; exact a, by rw [he]; exact b, by rw [hh]; exact c, by rw [hh]; exact d,
    by rw [hh]; exact e, by rw [he]; exact f, by rw [hh]; exact g⟩

/-! ## Sites and counters -/

/-- The sites of one statement. -/
theorem sites_stmt (st : Stmt) : (Prog.stmt st).sites = st.site?.toList := by
  cases st <;> rfl

/-- The sites of a sequence. -/
theorem sites_seq (p q : Prog) : (Prog.seq p q).sites = p.sites ++ q.sites := by
  simp [Prog.sites, Prog.stmts, List.filterMap_append]

/-- The sites of a choice. -/
theorem sites_choice (p q : Prog) : (Prog.choice p q).sites = p.sites ++ q.sites := by
  simp [Prog.sites, Prog.stmts, List.filterMap_append]

/-- The sites of a loop are the sites of its body. -/
theorem sites_loop (p : Prog) : (Prog.loop p).sites = p.sites := rfl

/-- The loop sites of a sequence. -/
theorem loopSites_seq (p q : Prog) :
    (Prog.seq p q).loopSites = p.loopSites ++ q.loopSites := by
  simp [Prog.loopSites, Prog.loopStmts, List.filterMap_append]

/-- The loop sites of a choice. -/
theorem loopSites_choice (p q : Prog) :
    (Prog.choice p q).loopSites = p.loopSites ++ q.loopSites := by
  simp [Prog.loopSites, Prog.loopStmts, List.filterMap_append]

/-- The loop sites of a loop are all sites of its body. -/
theorem loopSites_loop (p : Prog) : (Prog.loop p).loopSites = p.sites := rfl

/-- The statements under a loop are statements of the program. -/
theorem loopStmts_sub : ∀ (p : Prog), ∀ st ∈ p.loopStmts, st ∈ p.stmts
  | .skip, _, h => by simp [Prog.loopStmts] at h
  | .stmt _, _, h => by simp [Prog.loopStmts] at h
  | .seq p q, st, h => by
    simp only [Prog.loopStmts, List.mem_append, Prog.stmts] at h ⊢
    exact h.elim (fun h => Or.inl (loopStmts_sub p st h)) (fun h => Or.inr (loopStmts_sub q st h))
  | .choice p q, st, h => by
    simp only [Prog.loopStmts, List.mem_append, Prog.stmts] at h ⊢
    exact h.elim (fun h => Or.inl (loopStmts_sub p st h)) (fun h => Or.inr (loopStmts_sub q st h))
  | .loop _, _, h => h

/-- Each loop site is a site. -/
theorem loopSites_sub (p : Prog) {t : Site} (h : t ∈ p.loopSites) : t ∈ p.sites := by
  simp only [Prog.loopSites, Prog.sites, List.mem_filterMap] at h ⊢
  obtain ⟨st, h1, h2⟩ := h
  exact ⟨st, loopStmts_sub p st h1, h2⟩

/-- A bump of site `a` adds at most one occurrence of `a` to the counters. -/
theorem bump_cnt_le (s : CState) (a t : Site) : (s.bump a).cnt t ≤ s.cnt t + [a].count t := by
  show fupd s.cnt a (s.cnt a + 1) t ≤ _
  by_cases h : t = a
  · subst h; rw [fupd_same, List.count_singleton_self]; exact Nat.le_refl _
  · rw [fupd_ne _ _ h]; exact Nat.le_add_right _ _

/-- One statement adds at most its own site occurrences to the counters. -/
theorem SStep.cnt_le {st : Stmt} {s s' : CState} (h : SStep st s s') (t : Site) :
    s'.cnt t ≤ s.cnt t + (Prog.stmt st).sites.count t := by
  rw [sites_stmt]
  cases h with
  | @new x a => exact bump_cnt_le _ a t
  | @unknown x a => exact bump_cnt_le _ a t
  | @call ret a args _ h' =>
    have := bump_cnt_le ({ s with heap := h' }.setRet ret (some (.sym (.fresh a (s.cnt a)) []))) a t
    cases ret <;> exact this
  | null => exact Nat.le_add_right _ _
  | copy => exact Nat.le_add_right _ _
  | load => exact Nat.le_add_right _ _
  | store => exact Nat.le_add_right _ _
  | aload => exact Nat.le_add_right _ _
  | astore => exact Nat.le_add_right _ _

/-- An execution adds at most the site occurrences of the program to a counter,
if the site is not under a loop. -/
theorem Exec.cnt_le {q : Prog} {s s' : CState} (h : Exec q s s') :
    ∀ t, t ∉ q.loopSites → s'.cnt t ≤ s.cnt t + q.sites.count t := by
  induction h with
  | skip => intro t _; omega
  | stmt h => intro t _; exact SStep.cnt_le h t
  | @seq p q _ _ _ _ _ ih1 ih2 =>
    intro t ht
    rw [loopSites_seq, List.mem_append, not_or] at ht
    have := ih1 t ht.1
    have := ih2 t ht.2
    rw [sites_seq, List.count_append]; omega
  | @choiceL p q _ _ _ ih =>
    intro t ht
    rw [loopSites_choice, List.mem_append, not_or] at ht
    have := ih t ht.1
    rw [sites_choice, List.count_append]; omega
  | @choiceR p q _ _ _ ih =>
    intro t ht
    rw [loopSites_choice, List.mem_append, not_or] at ht
    have := ih t ht.2
    rw [sites_choice, List.count_append]; omega
  | loopZero => intro t _; omega
  | @loopMore p _ _ _ _ _ ih1 ih2 =>
    intro t ht
    rw [loopSites_loop] at ht
    have h0 : p.sites.count t = 0 := List.count_eq_zero.mpr ht
    have := ih1 t (fun h => ht (loopSites_sub p h))
    have := ih2 t (by rw [loopSites_loop]; exact ht)
    rw [sites_loop] at this ⊢
    omega

/-- The budget of a sequence gives the budget of its first part. -/
theorem Budget.seqL {ctx : Ctx} {p q : Prog} {s : CState} (h : Budget ctx (.seq p q) s) :
    Budget ctx p s := by
  intro t ht
  obtain ⟨h1, h2⟩ := h t ht
  rw [sites_seq, List.count_append] at h1
  rw [loopSites_seq, List.mem_append, not_or] at h2
  exact ⟨by omega, h2.1⟩

/-- After the first part of a sequence, the budget of the second part holds. -/
theorem Budget.seqR {ctx : Ctx} {p q : Prog} {s t : CState} (h : Budget ctx (.seq p q) s)
    (hx : Exec p s t) : Budget ctx q t := by
  intro a ha
  obtain ⟨h1, h2⟩ := h a ha
  rw [sites_seq, List.count_append] at h1
  rw [loopSites_seq, List.mem_append, not_or] at h2
  have := Exec.cnt_le hx a h2.1
  exact ⟨by omega, h2.2⟩

/-- The budget of a choice gives the budget of the left branch. -/
theorem Budget.choiceL {ctx : Ctx} {p q : Prog} {s : CState} (h : Budget ctx (.choice p q) s) :
    Budget ctx p s := by
  intro t ht
  obtain ⟨h1, h2⟩ := h t ht
  rw [sites_choice, List.count_append] at h1
  rw [loopSites_choice, List.mem_append, not_or] at h2
  exact ⟨by omega, h2.1⟩

/-- The budget of a choice gives the budget of the right branch. -/
theorem Budget.choiceR {ctx : Ctx} {p q : Prog} {s : CState} (h : Budget ctx (.choice p q) s) :
    Budget ctx q s := by
  intro t ht
  obtain ⟨h1, h2⟩ := h t ht
  rw [sites_choice, List.count_append] at h1
  rw [loopSites_choice, List.mem_append, not_or] at h2
  exact ⟨by omega, h2.2⟩

/-- The budget of a loop gives the budget of its body. -/
theorem Budget.body {ctx : Ctx} {p : Prog} {s : CState} (h : Budget ctx (.loop p) s) :
    Budget ctx p s := by
  intro t ht
  obtain ⟨h1, h2⟩ := h t ht
  rw [loopSites_loop] at h2
  exact ⟨by rw [sites_loop] at h1; omega, fun h => h2 (loopSites_sub p h)⟩

/-- The budget of a loop holds again after one run of the body. -/
theorem Budget.again {ctx : Ctx} {p : Prog} {s t : CState} (h : Budget ctx (.loop p) s)
    (hx : Exec p s t) : Budget ctx (.loop p) t := by
  intro a ha
  obtain ⟨h1, h2⟩ := h a ha
  rw [loopSites_loop] at h2
  have h0 : p.sites.count a = 0 := List.count_eq_zero.mpr h2
  have := Exec.cnt_le hx a (fun h => h2 (loopSites_sub p h))
  rw [sites_loop] at h1 ⊢
  exact ⟨by omega, by rw [loopSites_loop]; exact h2⟩

/-- The budget of one statement: a `once` site of the statement has the counter 0. -/
theorem Budget.stmt_site {ctx : Ctx} {st : Stmt} {s : CState} (h : Budget ctx (.stmt st) s)
    {a : Site} (hs : st.site? = some a) (ho : ctx.once a = true) : s.cnt a = 0 := by
  have := (h a ho).1
  rw [sites_stmt, hs] at this
  simp at this
  omega

end DirectedAlias.Sound

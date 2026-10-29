import DirectedAlias.Sound.Recency.Soundness
import DirectedAlias.Sound.Havoc.Soundness

/-!
# A generic simulation invariant for counter-dependent abstractions

The recency invariant `InvR` (`Sound/Recency/Step.lean`) uses one fixed abstraction `alphaR`.
This file states the same invariant for each abstraction `α` that reads only the site
counters. The update lemmas (variables, weak and strong stores, `retire`, loops, queries)
are proved once, with the properties of `α` as hypotheses.
`Sound/HavocRecency/Soundness.lean` uses it for recency with per-cell havoc origins.
-/

namespace DirectedAlias.Sound.HavocRecency

open DirectedAlias DirectedAlias.Sound DirectedAlias.Sound.Recency DirectedAlias.Sound.Havoc

/-- An abstraction of objects that reads only the site counters of the state. -/
abbrev Abs := (Site → Nat) → Obj → Origin

/-- The simulation invariant for the abstraction `α` (the same facts as `InvR`). -/
structure InvG (ctx : Ctx) (α : Abs) (st : CState) (X : AState) : Prop where
  outside : ∀ x, x ∉ ctx.vars → st.env x = none
  envOk : ∀ x o, st.env x = some o → ¬ Dead ctx.once o ∧ α st.cnt o ∈ ctx.origins
  heapLive : ∀ o c o', ¬ Dead ctx.once o → st.heap o c = some o' → ¬ Dead ctx.once o'
  heapIn : ∀ o c o', ¬ Dead ctx.once o → α st.cnt o ∈ ctx.origins → c.abs ∈ ctx.cells →
    st.heap o c = some o' → α st.cnt o' ∈ ctx.origins
  allocHeld : ∀ o c s n, st.heap o c = some (.alloc s n) →
    ¬ Dead ctx.once o ∧ α st.cnt o ∈ ctx.origins ∧ c.abs ∈ ctx.cells
  envCr : ∀ x s n, st.env x = some (.alloc s n) → n < st.cnt s
  heapCr : ∀ o c s n, st.heap o c = some (.alloc s n) → n < st.cnt s
  fresh : ∀ s n c, st.cnt s ≤ n → st.heap (.alloc s n) c = none
  env : ∀ x ∈ ctx.vars, ∀ o, st.env x = some o → α st.cnt o ∈ X.env x
  heap : ∀ o c o', ¬ Dead ctx.once o → α st.cnt o ∈ ctx.origins → c.abs ∈ ctx.cells →
    st.heap o c = some o' → α st.cnt o' ∈ X.heap (α st.cnt o) c.abs

variable {ctx : Ctx} {α : Abs}

/-- The generic invariant is closed upward under state inclusion. -/
theorem InvG.mono {st : CState} {X Y : AState} (h : InvG ctx α st X) (hs : X.Sub Y) :
    InvG ctx α st Y :=
  { h with
    env := fun x hx o he => hs.1 x (h.env x hx o he)
    heap := fun o c o' hd ho hc hh => hs.2 _ _ (h.heap o c o' hd ho hc hh) }

/-- The generic invariant is closed upward under inclusion on the universe. -/
theorem InvG.mono_leOn {st : CState} {X Y : AState} (h : InvG ctx α st X)
    (hs : leOn ctx X Y = true) : InvG ctx α st Y := by
  obtain ⟨h1, h2⟩ := leOn_iff.mp hs
  exact { h with
    env := fun x hx o he => h1 x hx (h.env x hx o he)
    heap := fun o c o' hd ho hc hh => h2 _ ho _ hc (h.heap o c o' hd ho hc hh) }

/-- Each top state simulates each concrete state that has the concrete facts. -/
theorem InvG.top {st : CState} {X : AState} (h : InvG ctx α st X) (W : AState) :
    InvG ctx α st (top ctx W) :=
  { h with
    env := fun x _ o he => mem_uni.mpr (Or.inl (h.envOk x o he).2)
    heap := fun o c o' hd ho hc hh => mem_uni.mpr (Or.inl (h.heapIn o c o' hd ho hc hh)) }

/-- The generic invariant depends only on the environment, the heap and the counters. -/
theorem InvG.congr {s s' : CState} {X : AState} (h : InvG ctx α s X)
    (he : s'.env = s.env) (hh : s'.heap = s.heap) (hn : s'.cnt = s.cnt) : InvG ctx α s' X := by
  obtain ⟨a, b, c, d, e, f, g, i, j, k⟩ := h
  exact ⟨by rw [he]; exact a, by rw [he, hn]; exact b, by rw [hh]; exact c,
    by rw [hh, hn]; exact d, by rw [hh, hn]; exact e, by rw [he, hn]; exact f,
    by rw [hh, hn]; exact g, by rw [hh, hn]; exact i, by rw [he, hn]; exact j,
    by rw [hh, hn]; exact k⟩

/-! ## Retire -/

/-- A counter bump of site `s` keeps the invariant for `retire s`, if the bump renames the
abstraction of every object except the next object of `s`. -/
theorem InvG.retire (hc : CtxROK ctx) {st : CState} {X : AState} (s : Site)
    (hbump : ∀ o, o ≠ .alloc s (st.cnt s) → α (st.bump s).cnt o = renameO s (α st.cnt o))
    (h : InvG ctx α st X) : InvG ctx α (st.bump s) (retire s X) := by
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
      rw [hbump o (hne_env x o he)]
      exact renameO_mem hc s (h.envOk x o he).2
    heapLive := h.heapLive
    heapIn := fun o c o' hd hin hc1 he => by
      change st.heap o c = some o' at he
      rw [hbump o (hne_src o c o' he)] at hin
      rw [hbump o' (hne_heap o c o' he)]
      exact renameO_mem hc s (h.heapIn o c o' hd (mem_of_renameO hc s hin) hc1 he)
    allocHeld := fun o c a n he => by
      change st.heap o c = some (.alloc a n) at he
      obtain ⟨h1, h2, h3⟩ := h.allocHeld o c a n he
      refine ⟨h1, ?_, h3⟩
      rw [hbump o (hne_src o c _ he)]
      exact renameO_mem hc s h2
    envCr := fun x a n he => Nat.lt_of_lt_of_le (h.envCr x a n he) (hcnt a)
    heapCr := fun o c a n he => Nat.lt_of_lt_of_le (h.heapCr o c a n he) (hcnt a)
    fresh := fun a n c hn => h.fresh a n c (Nat.le_trans (hcnt a) hn)
    env := fun x hx o he => by
      rw [hbump o (hne_env x o he)]
      exact List.mem_map.mpr ⟨_, h.env x hx o he, rfl⟩
    heap := fun o c o' hd hin hc1 he => by
      change st.heap o c = some o' at he
      rw [hbump o (hne_src o c o' he)] at hin ⊢
      rw [hbump o' (hne_heap o c o' he)]
      have hold := h.heap o c o' hd (mem_of_renameO hc s hin) hc1 he
      show _ ∈ (if renameO s (α st.cnt o) = rNew s then []
        else if renameO s (α st.cnt o) = rOld s then
          renameL s (uni (X.heap (rNew s) c.abs) (X.heap (rOld s) c.abs))
        else renameL s (X.heap (renameO s (α st.cnt o)) c.abs))
      rw [ite_eq_right (renameO_ne_new s _)]
      split
      · rename_i e
        refine List.mem_map.mpr ⟨_, mem_uni.mpr ?_, rfl⟩
        unfold renameO at e
        split at e
        · rename_i e2; rw [e2] at hold; exact Or.inl hold
        · rw [e] at hold; exact Or.inr hold
      · rename_i e
        have e3 : renameO s (α st.cnt o) = α st.cnt o := by
          unfold renameO at e ⊢
          split
          · rename_i e2; rw [ite_eq_left e2] at e; exact absurd rfl e
          · rfl
        rw [e3]
        exact List.mem_map.mpr ⟨_, hold, rfl⟩ }

/-! ## Updates -/

/-- Setting a variable keeps the generic invariant if the abstract set covers the new value. -/
theorem InvG.setVar {st : CState} {X : AState} {x : Var} {v : Val}
    {S : List Origin} (h : InvG ctx α st X) (hx : x ∈ ctx.vars)
    (hv : ∀ o, v = some o → ¬ Dead ctx.once o ∧ α st.cnt o ∈ ctx.origins ∧ α st.cnt o ∈ S)
    (hcr : ∀ a n, v = some (.alloc a n) → n < st.cnt a) :
    InvG ctx α (st.setVar x v) (X.setVar x S) where
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
    show α st.cnt o ∈ fupd X.env x S y
    by_cases e : y = x
    · subst e; rw [fupd_same] at he; rw [fupd_same]; exact (hv o he).2.2
    · rw [fupd_ne _ _ e] at he; rw [fupd_ne _ _ e]; exact h.env y hy o he
  heap := h.heap

/-- A concrete store keeps the concrete facts. The caller proves the abstract heap facts. -/
theorem InvG.write {st : CState} {X Y : AState} {o : Obj} {c : Cell} {v : Val}
    (h : InvG ctx α st X) (ho : ¬ Dead ctx.once o ∧ α st.cnt o ∈ ctx.origins)
    (hocr : ∀ a n, o = .alloc a n → n < st.cnt a)
    (hc : c.abs ∈ ctx.cells)
    (hv : ∀ o', v = some o' → ¬ Dead ctx.once o' ∧ α st.cnt o' ∈ ctx.origins)
    (hvcr : ∀ a n, v = some (.alloc a n) → n < st.cnt a)
    (henv : ∀ x ∈ ctx.vars, ∀ o', st.env x = some o' → α st.cnt o' ∈ Y.env x)
    (hheap : ∀ o1 c1 o2, ¬ Dead ctx.once o1 → α st.cnt o1 ∈ ctx.origins →
      c1.abs ∈ ctx.cells → fupd2 st.heap o c v o1 c1 = some o2 →
      α st.cnt o2 ∈ Y.heap (α st.cnt o1) c1.abs) :
    InvG ctx α (st.setCell o c v) Y where
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

/-- A weak store keeps the generic invariant. -/
theorem InvG.weak {st : CState} {X : AState} {o : Obj} {c : Cell} {v : Val}
    {os : List Origin} {S : List Origin}
    (h : InvG ctx α st X) (ho : ¬ Dead ctx.once o ∧ α st.cnt o ∈ ctx.origins)
    (hocr : ∀ a n, o = .alloc a n → n < st.cnt a)
    (hc : c.abs ∈ ctx.cells) (hos : α st.cnt o ∈ os)
    (hv : ∀ o', v = some o' → ¬ Dead ctx.once o' ∧ α st.cnt o' ∈ ctx.origins ∧
      α st.cnt o' ∈ S)
    (hvcr : ∀ a n, v = some (.alloc a n) → n < st.cnt a) :
    InvG ctx α (st.setCell o c v) (X.weakStore os c.abs S) := by
  apply InvG.write (Y := X.weakStore os c.abs S) h ho hocr hc
    (fun o' e => ⟨(hv o' e).1, (hv o' e).2.1⟩) hvcr h.env
  intro o1 c1 o2 hd hin hc1 hh
  show α st.cnt o2 ∈ (if c1.abs = c.abs ∧ α st.cnt o1 ∈ os then
    uni S (X.heap (α st.cnt o1) c1.abs) else X.heap (α st.cnt o1) c1.abs)
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

/-- A strong store keeps the generic invariant if the target origin denotes one live object. -/
theorem InvG.strong {st : CState} {X : AState} {o : Obj} {f : Field} {v : Val}
    {S : List Origin}
    (h : InvG ctx α st X) (ho : ¬ Dead ctx.once o ∧ α st.cnt o ∈ ctx.origins)
    (hocr : ∀ a n, o = .alloc a n → n < st.cnt a)
    (hc : ACell.fld f ∈ ctx.cells)
    (huniq : ∀ o1, ¬ Dead ctx.once o1 → α st.cnt o1 = α st.cnt o → o1 = o)
    (hv : ∀ o', v = some o' → ¬ Dead ctx.once o' ∧ α st.cnt o' ∈ ctx.origins ∧
      α st.cnt o' ∈ S)
    (hvcr : ∀ a n, v = some (.alloc a n) → n < st.cnt a) :
    InvG ctx α (st.setCell o (.fld f) v) (X.setCell (α st.cnt o) (.fld f) S) := by
  apply InvG.write (Y := X.setCell (α st.cnt o) (.fld f) S) (c := .fld f) h ho hocr hc
    (fun o' e => ⟨(hv o' e).1, (hv o' e).2.1⟩) hvcr h.env
  intro o1 c1 o2 hd hin hc1 hh
  show α st.cnt o2 ∈ fupd2 X.heap (α st.cnt o) (.fld f) S (α st.cnt o1) c1.abs
  by_cases e : o1 = o ∧ c1 = .fld f
  · obtain ⟨rfl, rfl⟩ := e
    rw [fupd2_same] at hh
    exact (fupd2_same X.heap (α st.cnt o1) (ACell.fld f) S).symm ▸ (hv o2 hh).2.2
  · rw [fupd2_ne _ _ e] at hh
    have e2 : ¬ (α st.cnt o1 = α st.cnt o ∧ c1.abs = .fld f) := by
      rintro ⟨h1, h2⟩
      apply e
      refine ⟨huniq o1 hd h1, ?_⟩
      cases c1 with
      | fld g => simp only [Cell.abs, ACell.fld.injEq] at h2; rw [h2]
      | elem i => simp [Cell.abs] at h2
    rw [fupd2_ne _ _ e2]
    exact h.heap o1 c1 o2 hd hin hc1 hh

/-! ## Calls -/

/-- A reachable allocation exists. -/
theorem InvG.reach_cr {st : CState} {X : AState} {args : List Var}
    (h : InvG ctx α st X) {o : Obj} (hr : Reach st args o) :
    ∀ a n, o = .alloc a n → n < st.cnt a := by
  induction hr with
  | outer => intro a n e; cases e
  | arg _ he => intro a n e; subst e; exact h.envCr _ a n he
  | step _ hh _ => intro a n e; subst e; exact h.heapCr _ _ a n hh

/-- Each object that a call can reach has an origin for which `reachB` is true, if the
abstraction of each symbolic object is an outer origin. -/
theorem InvG.reachB_of_reach {st : CState} {X : AState} {args : List Var} {o : Obj}
    (hout : ∀ cnt b p, (α cnt (.sym b p)).outer = true)
    (h : InvG ctx α st X) (hargs : ∀ a ∈ args, a ∈ ctx.vars) (hr : Reach st args o) :
    reachB ctx X args (α st.cnt o) = true := by
  unfold reachB
  cases hR : closeIter ctx.cells X (ctx.origins.length + 1)
      (uni (uniMap X.env args) (ctx.origins.filter Origin.outer)) with
  | none => rfl
  | some R =>
    obtain ⟨hseed, hclosed⟩ := closeIter_spec hR
    have key : (α st.cnt o).outer = true ∨ α st.cnt o ∈ R := by
      induction hr with
      | outer => exact Or.inl (hout _ _ _)
      | arg hx he =>
        exact Or.inr (hseed _ (mem_uni.mpr (Or.inl
          (mem_uniMap.mpr ⟨_, hx, h.env _ (hargs _ hx) _ he⟩))))
      | @step o1 o2 c _ hh ih =>
        cases o2 with
        | sym b p => exact Or.inl (hout _ _ _)
        | alloc s n =>
          obtain ⟨hd, hin, hc⟩ := h.allocHeld _ _ _ _ hh
          have h1 : α st.cnt o1 ∈ R := by
            cases ih with
            | inl hout => exact hseed _ (mem_uni.mpr (Or.inr (List.mem_filter.mpr ⟨hin, hout⟩)))
            | inr h => exact h
          exact Or.inr (hclosed _ (mem_succs.mpr ⟨_, h1, _, hc, h.heap _ _ _ hd hin hc hh⟩))
    cases key with
    | inl h1 => simp [h1]
    | inr h1 => simp [h1]

/-! ## Loops and queries -/

/-- A loop keeps a generic invariant state `Y` if one strict run of the body keeps it. -/
theorem loop_keepsG {src : Nat → Obj × Cell} {body : Prog} {Y : AState} (P : CState → Prop)
    (hstep : ∀ s t, P s → InvG ctx α s Y → ExecS src body s t → P t ∧ InvG ctx α t Y) :
    ∀ {s u : CState}, ExecS src (.loop body) s u → P s → InvG ctx α s Y → InvG ctx α u Y := by
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

/-- The abstract path evaluation contains the origin of the concrete path value. -/
theorem InvG.readPath_sound {st : CState} {X : AState} (h : InvG ctx α st X) :
    ∀ {cx : List Cell} {o0 o : Obj} {S : List Origin}, (∀ c ∈ cx, c.abs ∈ ctx.cells) →
      ¬ Dead ctx.once o0 → α st.cnt o0 ∈ ctx.origins → α st.cnt o0 ∈ S →
      readPath st.heap o0 cx = some o → α st.cnt o ∈ aevalFrom X S (cx.map Cell.abs)
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
      exact InvG.readPath_sound (cx := cs) h (fun c' h' => hcs c' (List.mem_cons_of_mem _ h'))
        (h.heapLive o0 c o1 hd e) (h.heapIn o0 c o1 hd hin hc e)
        (mem_aread.mpr ⟨_, hS, h.heap o0 c o1 hd hin hc e⟩) hr

/-- The abstract evaluation of an access path contains the origin of the concrete value. -/
theorem InvG.evalPath_sound {st : CState} {X : AState} (h : InvG ctx α st X)
    {x : Var} {cx : List Cell} {o : Obj} (hcs : ∀ c ∈ cx, c.abs ∈ ctx.cells)
    (he : evalPath st x cx = some o) : α st.cnt o ∈ aevalPath X x (cx.map Cell.abs) := by
  unfold evalPath at he
  cases e : st.env x with
  | none => rw [e] at he; cases he
  | some o0 =>
    rw [e] at he
    have hx : x ∈ ctx.vars := by
      by_cases hx : x ∈ ctx.vars
      · exact hx
      · rw [h.outside x hx] at e; cases e
    exact h.readPath_sound hcs (h.envOk x o0 e).1 (h.envOk x o0 e).2 (h.env x hx o0 e) he

end DirectedAlias.Sound.HavocRecency

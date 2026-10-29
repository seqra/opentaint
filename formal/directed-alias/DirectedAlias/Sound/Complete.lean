import DirectedAlias.Sound.Soundness

/-!
# Completeness of concept C in the store-free core scope

Scope (`CoreScope K`):
* no loop, no call, no store, no array store (`coreP`);
* each site of the program runs once (`onceB`);
* the number of loads plus the query length is at most `K` (no `deep` origin is used);
* no execution blocks on a null dereference (`Safe`).

In this scope `may` is cross-execution exact: each may-alias has two executions
in which the two concrete paths give the same object.
The proof gives the executions by construction: for each origin, it builds the execution
that realizes it. The canonical object of an origin is `gamma o`.
-/

namespace DirectedAlias.Sound

open DirectedAlias

/-! ## Scope -/

/-- A statement of the store-free core: no store, no array store, no call. -/
def coreS : Stmt → Bool
  | .store _ _ _ => false
  | .astore _ _ => false
  | .call _ _ _ => false
  | _ => true

/-- A program of the store-free core: no loop, and only core statements. -/
def coreP : Prog → Bool
  | .skip => true
  | .stmt st => coreS st
  | .seq p q => coreP p && coreP q
  | .choice p q => coreP p && coreP q
  | .loop _ => false

/-- The number of loads of a statement. -/
def loadsS : Stmt → Nat
  | .load _ _ _ => 1
  | .aload _ _ => 1
  | _ => 0

/-- The number of load statements of a program. -/
def loadsP : Prog → Nat
  | .skip => 0
  | .stmt st => loadsS st
  | .seq p q => loadsP p + loadsP q
  | .choice p q => loadsP p + loadsP q
  | .loop p => loadsP p

/-- No execution of the program from this state blocks: each statement can run. -/
def Safe : Prog → CState → Prop
  | .skip, _ => True
  | .stmt st, s => ∃ s', SStep st s s'
  | .seq p q, s => Safe p s ∧ ∀ t, Exec p s t → Safe q t
  | .choice p q, s => Safe p s ∧ Safe q s
  | .loop p, s => ∀ t, Exec (.loop p) s t → Safe p t

/-- The store-free core scope of completeness. -/
def CoreScope (K : Nat) (fr : Frame) (p : Prog) (px py : List ACell) : Prop :=
  coreP p = true ∧ (∀ s ∈ p.sites, p.onceB s = true) ∧ loadsP p + px.length ≤ K ∧
    loadsP p + py.length ≤ K ∧ Safe p (CState.init fr)

/-! ## Canonical objects -/

/-- The canonical concrete cell of an abstract cell: index 0 for an array element. -/
def canon : ACell → Cell
  | .fld f => .fld f
  | .elem => .elem 0

/-- The canonical concrete object of an origin. A deep or havoc origin has no canonical object. -/
def gamma : Origin → Obj
  | .sym (.root r) q => .sym (.root r) (q.map canon)
  | .sym (.fresh s) q => .sym (.fresh s 0) (q.map canon)
  | .alloc s => .alloc s 0
  | .deep _ => .alloc 0 0
  | .havoc s => .sym (.havoc s 0 0) []
  | .hsym _ _ _ _ => .alloc 0 0
  | .hdeep _ _ _ => .alloc 0 0

/-- The depth of an origin. A deep or havoc origin has depth `K + 1`. -/
def dep (K : Nat) : Origin → Nat
  | .sym _ q => q.length
  | .alloc _ => 0
  | .deep _ => K + 1
  | .havoc _ => K + 1
  | .hsym _ _ _ _ => K + 1
  | .hdeep _ _ _ => K + 1

/-- The canonical cells abstract back to the abstract cells. -/
theorem canon_abs : ∀ (q : List ACell), (q.map canon).map Cell.abs = q
  | [] => rfl
  | c :: cs => by
    cases c <;> simp only [List.map_cons, canon, Cell.abs, canon_abs cs]

/-- A default edge of a shallow origin is a concrete default edge of the canonical objects. -/
theorem dflt_gamma {K : Nat} {o o' : Origin} {c : ACell} (hd : dep K o + 1 ≤ K)
    (h : o' ∈ adefault K o c) :
    cdefault (gamma o) (canon c) = some (gamma o') ∧ dep K o' ≤ dep K o + 1 := by
  cases o with
  | sym b q =>
    simp only [dep] at hd
    have hl : (q ++ [c]).length ≤ K := by simp; omega
    simp only [adefault, symOrDeep, hl, ite_true, List.mem_singleton] at h
    subst h
    cases b with
    | root r => simp [gamma, cdefault, dep, List.map_append]
    | fresh s => simp [gamma, cdefault, dep, List.map_append]
  | deep b => simp only [dep] at hd; omega
  | alloc s => simp [adefault] at h
  | havoc s => simp only [dep] at hd; omega
  | hsym _ _ _ _ => simp only [dep] at hd; omega
  | hdeep _ _ _ => simp only [dep] at hd; omega

/-- A core execution does not change the heap. -/
theorem core_heap {q : Prog} {t u : CState} (h : Exec q t u) : coreP q = true → u.heap = t.heap := by
  induction h with
  | skip => intro _; rfl
  | stmt hs =>
    intro hc
    cases hs <;> first | rfl | (simp [coreP, coreS] at hc)
  | seq _ _ ih1 ih2 =>
    intro hc
    simp only [coreP, Bool.and_eq_true] at hc
    rw [ih2 hc.2, ih1 hc.1]
  | choiceL _ ih => intro hc; simp only [coreP, Bool.and_eq_true] at hc; exact ih hc.1
  | choiceR _ ih => intro hc; simp only [coreP, Bool.and_eq_true] at hc; exact ih hc.2
  | loopZero => intro _; rfl
  | loopMore _ _ _ _ => intro hc; simp [coreP] at hc

/-! ## Realization -/

/-- Each origin of a variable has a state in `E` where the variable holds the canonical object. -/
def RealEnv (K : Nat) (E : CState → Prop) (Y : AState) (D : Nat) : Prop :=
  ∀ x o, o ∈ Y.env x → dep K o ≤ D ∧ ∃ t, E t ∧ t.env x = some (gamma o)

/-- The abstract heap has only default contents. -/
def HeapDef (K : Nat) (Y : AState) : Prop :=
  ∀ o c, ∀ o' ∈ Y.heap o c, o' ∈ adefault K o c

/-- Realization is monotone in the state set and the depth bound. -/
theorem RealEnv.mono {K : Nat} {E E' : CState → Prop} {Y : AState} {D D' : Nat}
    (h : RealEnv K E Y D) (hE : ∀ t, E t → E' t) (hD : D ≤ D') : RealEnv K E' Y D' := by
  intro x o ho
  obtain ⟨h1, t, ht, he⟩ := h x o ho
  exact ⟨Nat.le_trans h1 hD, t, hE t ht, he⟩

/-- A step that sets only variable `x` keeps the realization of the other variables. -/
theorem realize_other {K : Nat} {E : CState → Prop} {Y : AState} {D D' : Nat} {st : Stmt}
    {x : Var} (hD : D ≤ D') (hsafe : ∀ t, E t → ∃ u, SStep st t u)
    (hkeep : ∀ t u, SStep st t u → ∀ x', x' ≠ x → u.env x' = t.env x')
    (h : RealEnv K E Y D) {x' : Var} (hx : x' ≠ x) {o : Origin} (ho : o ∈ Y.env x') :
    dep K o ≤ D' ∧ ∃ u, (∃ t, E t ∧ Exec (.stmt st) t u) ∧ u.env x' = some (gamma o) := by
  obtain ⟨h1, t, ht, he⟩ := h x' o ho
  obtain ⟨u, hu⟩ := hsafe t ht
  exact ⟨Nat.le_trans h1 hD, u, ⟨t, ht, .stmt hu⟩, (hkeep t u hu x' hx).trans he⟩

/-- `setVar` keeps the other variables. -/
theorem setVar_other (t : CState) (x : Var) (v : Val) (x' : Var) (h : x' ≠ x) :
    (t.setVar x v).env x' = t.env x' := fupd_ne _ _ h

/-- Realization through one core statement. -/
theorem realize_stmt (ctx : Ctx) (st : Stmt) (hcore : coreS st = true)
    (honce : ∀ s ∈ (Prog.stmt st).sites, ctx.once s = true)
    {E : CState → Prop} {Y : AState} {D : Nat}
    (hE : ∀ t, E t → t.heap = cdefault ∧ Budget ctx (.stmt st) t ∧ Safe (.stmt st) t)
    (hne : ∃ t, E t) (hY : HeapDef ctx.K Y) (hR : RealEnv ctx.K E Y D)
    (hD : D + loadsS st ≤ ctx.K) :
    (∃ u, ∃ t, E t ∧ Exec (.stmt st) t u) ∧ HeapDef ctx.K (astep ctx st Y) ∧
      RealEnv ctx.K (fun u => ∃ t, E t ∧ Exec (.stmt st) t u) (astep ctx st Y) (D + loadsS st) := by
  have hsafe : ∀ t, E t → ∃ u, SStep st t u := fun t ht => (hE t ht).2.2
  obtain ⟨t0, ht0⟩ := hne
  obtain ⟨u0, hu0⟩ := hsafe t0 ht0
  refine ⟨⟨u0, t0, ht0, .stmt hu0⟩, ?_, ?_⟩
  · cases st <;> first | exact hY | simp [coreS] at hcore
  · cases st with
    | store _ _ _ => simp [coreS] at hcore
    | astore _ _ => simp [coreS] at hcore
    | call _ _ _ => simp [coreS] at hcore
    | new x s =>
      have hkeep : ∀ t u, SStep (.new x s) t u → ∀ x', x' ≠ x → u.env x' = t.env x' := by
        intro t u hs x' hx; cases hs; exact setVar_other _ _ _ _ hx
      intro x' o ho
      by_cases hx : x' = x
      · subst hx
        change o ∈ fupd Y.env x' [.alloc s] x' at ho
        rw [fupd_same, List.mem_singleton] at ho
        subst ho
        have hc0 : t0.cnt s = 0 :=
          Budget.stmt_site (hE t0 ht0).2.1 rfl (honce s (by simp [sites_stmt, Stmt.site?]))
        refine ⟨Nat.zero_le _, _, ⟨t0, ht0, .stmt .new⟩, ?_⟩
        simp [CState.bump, CState.setVar, hc0, gamma]
      · change o ∈ fupd Y.env x [.alloc s] x' at ho
        rw [fupd_ne _ _ hx] at ho
        exact realize_other (Nat.le_add_right _ _) hsafe hkeep hR hx ho
    | null x =>
      have hkeep : ∀ t u, SStep (.null x) t u → ∀ x', x' ≠ x → u.env x' = t.env x' := by
        intro t u hs x' hx; cases hs; exact setVar_other _ _ _ _ hx
      intro x' o ho
      by_cases hx : x' = x
      · subst hx
        change o ∈ fupd Y.env x' [] x' at ho
        rw [fupd_same] at ho; cases ho
      · change o ∈ fupd Y.env x [] x' at ho
        rw [fupd_ne _ _ hx] at ho
        exact realize_other (Nat.le_add_right _ _) hsafe hkeep hR hx ho
    | copy x y =>
      have hkeep : ∀ t u, SStep (.copy x y) t u → ∀ x', x' ≠ x → u.env x' = t.env x' := by
        intro t u hs x' hx; cases hs; exact setVar_other _ _ _ _ hx
      intro x' o ho
      by_cases hx : x' = x
      · subst hx
        change o ∈ fupd Y.env x' (Y.env y) x' at ho
        rw [fupd_same] at ho
        obtain ⟨h1, t, ht, he⟩ := hR y o ho
        refine ⟨Nat.le_trans h1 (Nat.le_add_right _ _), _, ⟨t, ht, .stmt .copy⟩, ?_⟩
        show fupd t.env x' (t.env y) x' = _
        rw [fupd_same, he]
      · change o ∈ fupd Y.env x (Y.env y) x' at ho
        rw [fupd_ne _ _ hx] at ho
        exact realize_other (Nat.le_add_right _ _) hsafe hkeep hR hx ho
    | load x y f =>
      have hkeep : ∀ t u, SStep (.load x y f) t u → ∀ x', x' ≠ x → u.env x' = t.env x' := by
        intro t u hs x' hx; cases hs; exact setVar_other _ _ _ _ hx
      intro x' o ho
      by_cases hx : x' = x
      · subst hx
        change o ∈ fupd Y.env x' (aread Y (Y.env y) (.fld f)) x' at ho
        rw [fupd_same, mem_aread] at ho
        obtain ⟨o0, h0, h1⟩ := ho
        obtain ⟨hd0, t, ht, he⟩ := hR y o0 h0
        have hdd : dep ctx.K o0 + 1 ≤ ctx.K := by simp only [loadsS] at hD; omega
        obtain ⟨hg, hdo⟩ := dflt_gamma (c := .fld f) hdd (hY o0 _ o h1)
        refine ⟨by simp only [loadsS]; omega, _, ⟨t, ht, .stmt (.load he)⟩, ?_⟩
        show fupd t.env x' (t.heap (gamma o0) (.fld f)) x' = _
        rw [fupd_same, (hE t ht).1]
        exact hg
      · change o ∈ fupd Y.env x (aread Y (Y.env y) (.fld f)) x' at ho
        rw [fupd_ne _ _ hx] at ho
        exact realize_other (Nat.le_add_right _ _) hsafe hkeep hR hx ho
    | aload x y =>
      have hkeep : ∀ t u, SStep (.aload x y) t u → ∀ x', x' ≠ x → u.env x' = t.env x' := by
        intro t u hs x' hx; cases hs; exact setVar_other _ _ _ _ hx
      intro x' o ho
      by_cases hx : x' = x
      · subst hx
        change o ∈ fupd Y.env x' (aread Y (Y.env y) .elem) x' at ho
        rw [fupd_same, mem_aread] at ho
        obtain ⟨o0, h0, h1⟩ := ho
        obtain ⟨hd0, t, ht, he⟩ := hR y o0 h0
        have hdd : dep ctx.K o0 + 1 ≤ ctx.K := by simp only [loadsS] at hD; omega
        obtain ⟨hg, hdo⟩ := dflt_gamma (c := .elem) hdd (hY o0 _ o h1)
        refine ⟨by simp only [loadsS]; omega, _, ⟨t, ht, .stmt (.aload 0 he)⟩, ?_⟩
        show fupd t.env x' (t.heap (gamma o0) (.elem 0)) x' = _
        rw [fupd_same, (hE t ht).1]
        exact hg
      · change o ∈ fupd Y.env x (aread Y (Y.env y) .elem) x' at ho
        rw [fupd_ne _ _ hx] at ho
        exact realize_other (Nat.le_add_right _ _) hsafe hkeep hR hx ho
    | unknown x s =>
      have hkeep : ∀ t u, SStep (.unknown x s) t u → ∀ x', x' ≠ x → u.env x' = t.env x' := by
        intro t u hs x' hx; cases hs; exact setVar_other _ _ _ _ hx
      intro x' o ho
      by_cases hx : x' = x
      · subst hx
        change o ∈ fupd Y.env x' [.sym (.fresh s) []] x' at ho
        rw [fupd_same, List.mem_singleton] at ho
        subst ho
        have hc0 : t0.cnt s = 0 :=
          Budget.stmt_site (hE t0 ht0).2.1 rfl (honce s (by simp [sites_stmt, Stmt.site?]))
        refine ⟨Nat.zero_le _, _, ⟨t0, ht0, .stmt .unknown⟩, ?_⟩
        simp [CState.bump, CState.setVar, hc0, gamma]
      · change o ∈ fupd Y.env x [.sym (.fresh s) []] x' at ho
        rw [fupd_ne _ _ hx] at ho
        exact realize_other (Nat.le_add_right _ _) hsafe hkeep hR hx ho

/-- Realization through a core program: each origin of the analysis result is realized by an
execution of the program from a state of `E`. -/
theorem realize (ctx : Ctx) : ∀ (q : Prog), coreP q = true → (∀ s ∈ q.sites, ctx.once s = true) →
    ∀ {E : CState → Prop} {Y : AState} {D : Nat},
    (∀ t, E t → t.heap = cdefault ∧ Budget ctx q t ∧ Safe q t) → (∃ t, E t) →
    HeapDef ctx.K Y → RealEnv ctx.K E Y D → D + loadsP q ≤ ctx.K →
    (∃ u, ∃ t, E t ∧ Exec q t u) ∧ HeapDef ctx.K (analyze ctx q Y) ∧
      RealEnv ctx.K (fun u => ∃ t, E t ∧ Exec q t u) (analyze ctx q Y) (D + loadsP q) := by
  intro q
  induction q with
  | skip =>
    intro _ _ E Y D _ hne hY hR _
    obtain ⟨t, ht⟩ := hne
    refine ⟨⟨t, t, ht, .skip⟩, hY, ?_⟩
    intro x o ho
    obtain ⟨h1, t, ht, he⟩ := hR x o ho
    exact ⟨h1, t, ⟨t, ht, .skip⟩, he⟩
  | stmt st =>
    intro hc ho E Y D hE hne hY hR hD
    exact realize_stmt ctx st hc ho hE hne hY hR hD
  | seq p q ihp ihq =>
    intro hc ho E Y D hE hne hY hR hD
    simp only [coreP, Bool.and_eq_true] at hc
    have hop : ∀ s ∈ p.sites, ctx.once s = true :=
      fun s hs => ho s (by rw [sites_seq]; exact List.mem_append.mpr (Or.inl hs))
    have hoq : ∀ s ∈ q.sites, ctx.once s = true :=
      fun s hs => ho s (by rw [sites_seq]; exact List.mem_append.mpr (Or.inr hs))
    simp only [loadsP] at hD
    obtain ⟨hne1, hY1, hR1⟩ := ihp hc.1 hop
      (fun t ht => ⟨(hE t ht).1, Budget.seqL (hE t ht).2.1, (hE t ht).2.2.1⟩) hne hY hR
      (by omega)
    have hE1 : ∀ u, (∃ t, E t ∧ Exec p t u) →
        u.heap = cdefault ∧ Budget ctx q u ∧ Safe q u := by
      rintro u ⟨t, ht, hx⟩
      exact ⟨(core_heap hx hc.1).trans (hE t ht).1, Budget.seqR (hE t ht).2.1 hx,
        (hE t ht).2.2.2 u hx⟩
    obtain ⟨⟨v, u, ⟨t, ht, hx1⟩, hx2⟩, hY2, hR2⟩ := ihq hc.2 hoq hE1 hne1 hY1 hR1 (by omega)
    refine ⟨⟨v, t, ht, .seq hx1 hx2⟩, hY2, ?_⟩
    simp only [loadsP]
    rw [← Nat.add_assoc]
    exact hR2.mono (fun w ⟨u, ⟨t, ht, h1⟩, h2⟩ => ⟨t, ht, .seq h1 h2⟩) (Nat.le_refl _)
  | choice p q ihp ihq =>
    intro hc ho E Y D hE hne hY hR hD
    simp only [coreP, Bool.and_eq_true] at hc
    have hop : ∀ s ∈ p.sites, ctx.once s = true :=
      fun s hs => ho s (by rw [sites_choice]; exact List.mem_append.mpr (Or.inl hs))
    have hoq : ∀ s ∈ q.sites, ctx.once s = true :=
      fun s hs => ho s (by rw [sites_choice]; exact List.mem_append.mpr (Or.inr hs))
    simp only [loadsP] at hD ⊢
    obtain ⟨⟨u, t, ht, hx⟩, hYp, hRp⟩ := ihp hc.1 hop
      (fun t ht => ⟨(hE t ht).1, Budget.choiceL (hE t ht).2.1, (hE t ht).2.2.1⟩) hne hY hR
      (by omega)
    obtain ⟨_, hYq, hRq⟩ := ihq hc.2 hoq
      (fun t ht => ⟨(hE t ht).1, Budget.choiceR (hE t ht).2.1, (hE t ht).2.2.2⟩) hne hY hR
      (by omega)
    refine ⟨⟨u, t, ht, .choiceL hx⟩, ?_, ?_⟩
    · intro o c o' h
      rcases mem_uni.mp h with h | h
      · exact hYp o c o' h
      · exact hYq o c o' h
    · intro x o h
      rcases mem_uni.mp h with h | h
      · exact (hRp.mono (fun w ⟨t, ht, h1⟩ => ⟨t, ht, .choiceL h1⟩) (by omega)) x o h
      · exact (hRq.mono (fun w ⟨t, ht, h1⟩ => ⟨t, ht, .choiceR h1⟩) (by omega)) x o h
  | loop _ _ => intro hc; simp [coreP] at hc

/-- A path walk over the default heap from a shallow origin reads the canonical objects. -/
theorem walk_gamma {K : Nat} {Y : AState} (hY : HeapDef K Y) :
    ∀ (px : List ACell) (S : List Origin) (o : Origin), o ∈ aevalFrom Y S px →
      (∀ o0 ∈ S, dep K o0 + px.length ≤ K) →
      ∃ o0 ∈ S, readPath cdefault (gamma o0) (px.map canon) = some (gamma o)
  | [], S, o, h, _ => ⟨o, h, rfl⟩
  | c :: cs, S, o, h, hd => by
    have hd1 : ∀ o1 ∈ aread Y S c, dep K o1 + cs.length ≤ K := by
      intro o1 h1
      obtain ⟨o0, h0, h01⟩ := mem_aread.mp h1
      have := hd o0 h0
      simp only [List.length_cons] at this
      have := (dflt_gamma (by omega) (hY o0 c o1 h01)).2
      omega
    obtain ⟨o1, h1, hr⟩ := walk_gamma hY cs (aread Y S c) o h hd1
    obtain ⟨o0, h0, h01⟩ := mem_aread.mp h1
    have := hd o0 h0
    simp only [List.length_cons] at this
    have hg := (dflt_gamma (by omega) (hY o0 c o1 h01)).1
    refine ⟨o0, h0, ?_⟩
    simp only [List.map_cons, readPath, hg, Option.bind_some]
    exact hr

/-- The query realization: each origin of an abstract path value is the value of the canonical
concrete path in some realizing state. -/
theorem realize_path {K : Nat} {E : CState → Prop} {Y : AState} {D : Nat}
    (hE : ∀ t, E t → t.heap = cdefault) (hY : HeapDef K Y) (hR : RealEnv K E Y D)
    {x : Var} {px : List ACell} (hd : D + px.length ≤ K) {o : Origin}
    (h : o ∈ aevalPath Y x px) :
    ∃ t, E t ∧ evalPath t x (px.map canon) = some (gamma o) := by
  obtain ⟨o0, h0, hr⟩ := walk_gamma hY px (Y.env x) o h
    (fun o0 h0 => Nat.le_trans (Nat.add_le_add_right (hR x o0 h0).1 _) hd)
  obtain ⟨_, t, ht, he⟩ := hR x o0 h0
  refine ⟨t, ht, ?_⟩
  simp only [evalPath, he, Option.bind_some, hE t ht]
  exact hr

/-- Completeness in the store-free core scope: each may-alias is a cross-execution alias of
the canonical concrete paths. -/
theorem ccomplete_core (K : Nat) : CCompleteIn K (CoreScope K) := by
  intro fr p x px y py hs hmay
  obtain ⟨hcore, honce, hdx, hdy, hsafe⟩ := hs
  let qf := afields px ++ afields py
  let ctx := progCtx K fr p qf
  have hE : ∀ t, t = CState.init fr → t.heap = cdefault ∧ Budget ctx p t ∧ Safe p t := by
    rintro t rfl
    exact ⟨rfl, ctxE_budget true K fr p qf, hsafe⟩
  have hY0 : HeapDef ctx.K (ainit K fr) := fun o c o' h => h
  have hR0 : RealEnv ctx.K (fun t => t = CState.init fr) (ainit K fr) 0 := by
    intro x o ho
    change o ∈ (match fr.root? x with | some r => [Origin.sym (.root r) []] | none => []) at ho
    cases e : fr.root? x with
    | none => rw [e] at ho; cases ho
    | some r =>
      rw [e, List.mem_singleton] at ho
      subst ho
      refine ⟨Nat.zero_le _, _, rfl, ?_⟩
      simp [CState.init, e, gamma]
  obtain ⟨_, hY, hR⟩ := realize ctx p hcore (fun s h => honce s h) hE ⟨_, rfl⟩ hY0 hR0
    (by simp only [ctx, progCtx, Ctx.ofProg]; omega)
  obtain ⟨o, hox, hoy⟩ := may_iff.mp hmay
  have hEh : ∀ u, (∃ t, t = CState.init fr ∧ Exec p t u) → u.heap = cdefault := by
    rintro u ⟨t, rfl, hx⟩; exact core_heap hx hcore
  obtain ⟨u1, ⟨_, rfl, hx1⟩, h1⟩ := realize_path hEh hY hR
    (by simp only [ctx, progCtx, Ctx.ofProg]; omega) hox
  obtain ⟨u2, ⟨_, rfl, hx2⟩, h2⟩ := realize_path hEh hY hR
    (by simp only [ctx, progCtx, Ctx.ofProg]; omega) hoy
  exact ⟨px.map canon, py.map canon, canon_abs px, canon_abs py,
    u1, u2, gamma o, hx1, hx2, h1, h2⟩

end DirectedAlias.Sound

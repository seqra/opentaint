import DirectedAlias.Sound.NullSafe

/-!
# Completeness with stores: the exactness certificate

This file widens the completeness scope to programs with field stores.
The analysis checks a certificate (`bcert`) while it runs. The certificate asks:
* each store `x.f = y` is strong, and its value is deterministic: `x` and `y` each have
  exactly one origin, the origin is unique, and the null kinds say that `x` and `y` are not null;
* at each join, the two branch heaps are equal on the universe, except on cells of an
  allocation site of one branch where the other branch has no content
  (the "initialize a new object in a branch" pattern);
* no loop, no call, no array store, and no load can block (the null kinds).
Counterexamples B4, B5 and B6 (`Boundary.lean`) show that each part of the store condition
is necessary.
-/

namespace DirectedAlias.Sound

open DirectedAlias

/-! ## The certificate -/

/-- An origin is an allocation origin. -/
def Origin.isAlloc : Origin → Bool
  | .alloc _ => true
  | _ => false

/-- Variable `x` has exactly one origin, and the origin is unique. -/
def strongB (ctx : Ctx) (Y : AState) (x : Var) : Bool :=
  match single? (Y.env x) with
  | some o => o.uniqueB ctx.once ctx.entryUnique
  | none => false

/-- The null kind of a loaded value. -/
def loadKind (Y : AState) (k : Var → NK) (y : Var) (c : ACell) : Option NK :=
  match k y with
  | .sym => some (if (aread Y (Y.env y) c).any Origin.isAlloc then .obj else .sym)
  | .obj => some .maybe
  | .maybe => none

/-- The certificate check and the null-kind transfer of one statement. -/
def bstep (ctx : Ctx) (k : Var → NK) (Y : AState) : Stmt → Option (Var → NK)
  | .new x _ => some (fupd k x .obj)
  | .null x => some (fupd k x .maybe)
  | .copy x y => some (fupd k x (k y))
  | .load x y f => (loadKind Y k y (.fld f)).map (fupd k x)
  | .aload x y => (loadKind Y k y .elem).map (fupd k x)
  | .unknown x _ => some (fupd k x .sym)
  | .store x _ y =>
    if k x ≠ .maybe ∧ k y ≠ .maybe ∧ strongB ctx Y x = true ∧ strongB ctx Y y = true then some k
    else none
  | _ => none

/-- The join check of two branches on one cell. -/
def cellJoinOK (p q : Prog) (Yp Yq : AState) (o : Origin) (c : ACell) : Bool :=
  (subB (Yp.heap o c) (Yq.heap o c) && subB (Yq.heap o c) (Yp.heap o c)) ||
    match o with
    | .alloc s => (p.sites.contains s && (Yq.heap o c).isEmpty) ||
        (q.sites.contains s && (Yp.heap o c).isEmpty)
    | _ => false

/-- The join check of two branches on the universe. -/
def joinOK (ctx : Ctx) (p q : Prog) (Yp Yq : AState) : Bool :=
  ctx.origins.all fun o => ctx.cells.all fun c => cellJoinOK p q Yp Yq o c

/-- The exactness certificate. It runs with the analysis and gives the final null kinds. -/
def bcert (ctx : Ctx) : Prog → (Var → NK) → AState → Option (Var → NK)
  | .skip, k, _ => some k
  | .stmt st, k, Y => bstep ctx k Y st
  | .seq p q, k, Y => (bcert ctx p k Y).bind (fun k1 => bcert ctx q k1 (analyze ctx p Y))
  | .choice p q, k, Y =>
    match bcert ctx p k Y, bcert ctx q k Y with
    | some k1, some k2 =>
      if joinOK ctx p q (analyze ctx p Y) (analyze ctx q Y) then
        some (fun x => (k1 x).join (k2 x))
      else none
    | _, _ => none
  | .loop _, _, _ => none

/-- The checkable scope with stores. -/
def storeScopeB (K : Nat) (fr : Frame) (p : Prog) (px py : List ACell) : Bool :=
  p.sites.all p.onceB && decide (loadsP p + px.length ≤ K) &&
    decide (loadsP p + py.length ≤ K) &&
    (bcert (progCtx K fr p (afields px ++ afields py)) p (entryKinds fr) (ainit K fr)).isSome

/-! ## Facts about canonical objects -/

/-- The canonical cells are injective. -/
theorem canon_inj {q1 q2 : List ACell} (h : q1.map canon = q2.map canon) : q1 = q2 := by
  rw [← canon_abs q1, ← canon_abs q2, h]

/-- The canonical objects of shallow origins are injective. -/
theorem gamma_inj {K : Nat} {o1 o2 : Origin} (h1 : dep K o1 ≤ K) (h2 : dep K o2 ≤ K)
    (h : gamma o1 = gamma o2) : o1 = o2 := by
  cases o1 with
  | deep _ => simp only [dep] at h1; omega
  | havoc _ => simp only [dep] at h1; omega
  | hsym _ _ _ _ => simp only [dep] at h1; omega
  | hdeep _ _ _ => simp only [dep] at h1; omega
  | alloc s =>
    cases o2 with
    | deep _ => simp only [dep] at h2; omega
    | havoc _ => simp only [dep] at h2; omega
    | hsym _ _ _ _ => simp only [dep] at h2; omega
    | hdeep _ _ _ => simp only [dep] at h2; omega
    | alloc s' => simp only [gamma, Obj.alloc.injEq] at h; rw [h.1]
    | sym b q => cases b <;> simp [gamma] at h
  | sym b q =>
    cases o2 with
    | deep _ => simp only [dep] at h2; omega
    | havoc _ => simp only [dep] at h2; omega
    | hsym _ _ _ _ => simp only [dep] at h2; omega
    | hdeep _ _ _ => simp only [dep] at h2; omega
    | alloc s' => cases b <;> simp [gamma] at h
    | sym b' q' =>
      cases b with
      | root r =>
        cases b' with
        | root r' =>
          simp only [gamma, Obj.sym.injEq, Base.root.injEq] at h
          rw [h.1, canon_inj h.2]
        | fresh s' => simp [gamma] at h
      | fresh s =>
        cases b' with
        | root r' => simp [gamma] at h
        | fresh s' =>
          simp only [gamma, Obj.sym.injEq, Base.fresh.injEq] at h
          rw [h.1.1, canon_inj h.2]

/-- A unique shallow origin is the abstraction of its canonical object, and that object is
not dead. -/
theorem canon_of_unique {K : Nat} {once : Site → Bool} {eu : Bool} {o : Origin}
    (hu : o.uniqueB once eu = true) (hd : dep K o ≤ K) :
    alpha K (gamma o) = o ∧ ¬ Dead once (gamma o) := by
  cases o with
  | sym b q =>
    simp only [dep] at hd
    have hl : (q.map canon).length ≤ K := by simp; exact hd
    cases b with
    | root r =>
      refine ⟨?_, by simp [gamma, Dead]⟩
      simp only [gamma, alpha, symOrDeep, canon_abs, List.length_map] at hl ⊢
      rw [if_pos (by simpa using hl)]
    | fresh s =>
      refine ⟨?_, by simp [gamma, Dead]⟩
      simp only [gamma, alpha, symOrDeep, canon_abs, List.length_map] at hl ⊢
      rw [if_pos (by simpa using hl)]
  | deep _ => simp [Origin.uniqueB] at hu
  | havoc _ => simp [Origin.uniqueB] at hu
  | hsym _ _ _ _ => simp [Origin.uniqueB] at hu
  | hdeep _ _ _ => simp [Origin.uniqueB] at hu
  | alloc s => exact ⟨rfl, by simp [gamma, Dead]⟩

/-- The value of a variable with one unique origin is the canonical object of the origin. -/
theorem value_of_strong {ctx : Ctx} {t : CState} {Y : AState} {x : Var} {v : Obj}
    (hi : Inv ctx t Y) (hx : x ∈ ctx.vars) (hv : t.env x = some v)
    (hs : strongB ctx Y x = true) (hd : ∀ o ∈ Y.env x, dep ctx.K o ≤ ctx.K) :
    ∃ o, single? (Y.env x) = some o ∧ o.uniqueB ctx.once ctx.entryUnique = true ∧
      v = gamma o := by
  unfold strongB at hs
  cases e : single? (Y.env x) with
  | none => rw [e] at hs; cases hs
  | some o =>
    rw [e] at hs
    refine ⟨o, rfl, hs, ?_⟩
    have ha : alpha ctx.K v = o := (single?_spec e).2 _ (hi.env x hx v hv)
    have ho : o ∈ Y.env x := (single?_spec e).1
    obtain ⟨hga, hgd⟩ := canon_of_unique (K := ctx.K) hs (hd o ho)
    rw [← ha] at hs
    exact (unique_obj hs (hi.envOk x v hv).1 hgd (hga.trans ha.symm)).symm

/-! ## The invariant of the realization -/

/-- Allocation facts of a concrete state: each held allocation exists, an allocation that
does not exist yet has null cells, and no cell of a symbolic object is null. -/
structure AllocOK (t : CState) : Prop where
  env : ∀ x s n, t.env x = some (.alloc s n) → n < t.cnt s
  heap : ∀ o c s n, t.heap o c = some (.alloc s n) → n < t.cnt s
  fresh : ∀ s n c, t.cnt s ≤ n → t.heap (.alloc s n) c = none
  symNN : ∀ b p c, t.heap (.sym b p) c ≠ none

/-- Abstract support: the abstract values of variables and universe cells are in the universe. -/
structure ASupp (ctx : Ctx) (Y : AState) : Prop where
  env : ∀ x, ∀ o ∈ Y.env x, o ∈ ctx.origins
  heap : ∀ o ∈ ctx.origins, ∀ c ∈ ctx.cells, ∀ o' ∈ Y.heap o c, o' ∈ ctx.origins

/-- The depth of a cell content is at most `D`, or one more than the depth of its origin. -/
def DepH (K : Nat) (Y : AState) (D : Nat) : Prop :=
  ∀ o c, ∀ o' ∈ Y.heap o c, dep K o' ≤ max D (dep K o + 1)

/-- An allocation site that no state of `E` ran has empty abstract cells. -/
def A0 (E : CState → Prop) (Y : AState) : Prop :=
  ∀ s, (∀ t, E t → t.cnt s = 0) → ∀ c, Y.heap (.alloc s) c = []

/-- The canonical object of an origin exists in a state, if the origin is an allocation. -/
def AllocLive (t : CState) (o : Origin) : Prop :=
  ∀ s, o = .alloc s → 1 ≤ t.cnt s

/-- Heap realization: each abstract edge of a shallow universe origin is a concrete edge
in each state of `E` where its canonical object exists. -/
def HR (ctx : Ctx) (E : CState → Prop) (Y : AState) : Prop :=
  ∀ o ∈ ctx.origins, ∀ c ∈ ctx.cells, ∀ o' ∈ Y.heap o c, dep ctx.K o < ctx.K →
    ∀ t, E t → AllocLive t o → t.heap (gamma o) (canon c) = some (gamma o')

/-- The invariant of the realization with stores. -/
structure BInv (ctx : Ctx) (k : Var → NK) (E : CState → Prop) (Y : AState) (D : Nat) : Prop where
  states : ∀ t, E t → Inv ctx t Y ∧ Good k t ∧ AllocOK t
  ne : ∃ t, E t
  supp : ASupp ctx Y
  depH : DepH ctx.K Y D
  a0 : A0 E Y
  real : RealEnv ctx.K E Y D
  hr : HR ctx E Y

/-! ## Null kinds with stores -/

/-- The certificate of one statement is sound for the null kinds: the statement can run,
and the new kinds hold after each step. -/
theorem bstep_good {ctx : Ctx} (hc : CtxOK ctx) {st : Stmt} {k k' : Var → NK} {Y : AState}
    {t : CState} (hok : StmtOK ctx st) (h : bstep ctx k Y st = some k') (hi : Inv ctx t Y)
    (hg : Good k t) (ha : AllocOK t) :
    (∃ u, SStep st t u) ∧ ∀ u, SStep st t u → Good k' u := by
  cases st with
  | new x s =>
    simp only [bstep, Option.some.injEq] at h; subst h
    refine ⟨⟨_, .new⟩, fun u hu => ?_⟩
    cases hu
    exact Good.set hg x .obj _ (fun e => by cases e) (fun _ => ⟨_, rfl⟩)
  | null x =>
    simp only [bstep, Option.some.injEq] at h; subst h
    refine ⟨⟨_, .null⟩, fun u hu => ?_⟩
    cases hu
    exact Good.set hg x .maybe _ (fun e => by cases e) (fun e => absurd rfl e)
  | copy x y =>
    simp only [bstep, Option.some.injEq] at h; subst h
    refine ⟨⟨_, .copy⟩, fun u hu => ?_⟩
    cases hu
    exact Good.set hg x _ _ (hg y).1 (hg y).2
  | unknown x s =>
    simp only [bstep, Option.some.injEq] at h; subst h
    refine ⟨⟨_, .unknown⟩, fun u hu => ?_⟩
    cases hu
    exact Good.set hg x .sym _ (fun _ => ⟨_, _, rfl⟩) (fun _ => ⟨_, rfl⟩)
  | store x f y =>
    simp only [bstep] at h
    split at h
    · rename_i hcond
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨o, ho⟩ := (hg x).2 hcond.1
      refine ⟨⟨_, .store ho⟩, fun u hu => ?_⟩
      cases hu
      exact hg
    · cases h
  | load x y f =>
    simp only [bstep] at h
    cases hk : loadKind Y k y (.fld f) with
    | none => rw [hk] at h; cases h
    | some a =>
      rw [hk] at h
      simp only [Option.map_some, Option.some.injEq] at h; subst h
      unfold loadKind at hk
      cases hy : k y with
      | maybe => rw [hy] at hk; cases hk
      | obj =>
        rw [hy] at hk; cases hk
        obtain ⟨o, ho⟩ := (hg y).2 (by rw [hy]; intro e; cases e)
        refine ⟨⟨_, .load ho⟩, fun u hu => ?_⟩
        cases hu with
        | load ho' =>
          exact Good.set hg x .maybe _ (fun e => by cases e) (fun e => absurd rfl e)
      | sym =>
        rw [hy] at hk
        simp only [Option.some.injEq] at hk
        obtain ⟨b, p, ho⟩ := (hg y).1 hy
        refine ⟨⟨_, .load ho⟩, fun u hu => ?_⟩
        cases hu with
        | load ho' =>
          rename_i o'
          rw [ho] at ho'; cases ho'
          have hnn := ha.symNN b p (.fld f)
          cases hv : t.heap (.sym b p) (.fld f) with
          | none => exact absurd hv hnn
          | some v =>
            refine Good.set hg x a _ ?_ (fun _ => ⟨v, rfl⟩)
            intro hs
            subst hk
            cases v with
            | sym b' p' => exact ⟨b', p', rfl⟩
            | alloc s n =>
              exfalso
              have hy' : y ∈ ctx.vars := hok.vars y (by simp [Stmt.vars])
              have hd := hi.envOk y _ ho
              have hf : (Cell.fld f).abs ∈ ctx.cells := hok.fields f (by simp [Stmt.fields])
              have hin := mem_aread.mpr ⟨_, hi.env y hy' _ ho, hi.heap _ _ _ hd.1 hd.2 hf hv⟩
              have : (aread Y (Y.env y) (.fld f)).any Origin.isAlloc = true :=
                List.any_eq_true.mpr ⟨_, hin, rfl⟩
              rw [this] at hs; cases hs
  | aload x y =>
    simp only [bstep] at h
    cases hk : loadKind Y k y .elem with
    | none => rw [hk] at h; cases h
    | some a =>
      rw [hk] at h
      simp only [Option.map_some, Option.some.injEq] at h; subst h
      unfold loadKind at hk
      cases hy : k y with
      | maybe => rw [hy] at hk; cases hk
      | obj =>
        rw [hy] at hk; cases hk
        obtain ⟨o, ho⟩ := (hg y).2 (by rw [hy]; intro e; cases e)
        refine ⟨⟨_, .aload 0 ho⟩, fun u hu => ?_⟩
        cases hu with
        | aload i ho' =>
          exact Good.set hg x .maybe _ (fun e => by cases e) (fun e => absurd rfl e)
      | sym =>
        rw [hy] at hk
        simp only [Option.some.injEq] at hk
        obtain ⟨b, p, ho⟩ := (hg y).1 hy
        refine ⟨⟨_, .aload 0 ho⟩, fun u hu => ?_⟩
        cases hu with
        | aload i ho' =>
          rename_i o'
          rw [ho] at ho'; cases ho'
          have hnn := ha.symNN b p (.elem i)
          cases hv : t.heap (.sym b p) (.elem i) with
          | none => exact absurd hv hnn
          | some v =>
            refine Good.set hg x a _ ?_ (fun _ => ⟨v, rfl⟩)
            intro hs
            subst hk
            cases v with
            | sym b' p' => exact ⟨b', p', rfl⟩
            | alloc s n =>
              exfalso
              have hy' : y ∈ ctx.vars := hok.vars y (by simp [Stmt.vars])
              have hd := hi.envOk y _ ho
              have hf : (Cell.elem i).abs ∈ ctx.cells := hc.elem
              have hin := mem_aread.mpr ⟨_, hi.env y hy' _ ho, hi.heap _ _ _ hd.1 hd.2 hf hv⟩
              have : (aread Y (Y.env y) .elem).any Origin.isAlloc = true :=
                List.any_eq_true.mpr ⟨_, hin, rfl⟩
              rw [this] at hs; cases hs
  | astore _ _ => simp [bstep] at h
  | call _ _ _ => simp [bstep] at h

/-! ## One statement -/

/-- The budget of a statement with a once site gives counter 0 in every state. -/
theorem budget_zero {ctx : Ctx} {st : Stmt} {E : CState → Prop}
    (hb : ∀ t, E t → Budget ctx (.stmt st) t) {s : Site} (hs : st.site? = some s)
    (ho : ctx.once s = true) : ∀ t, E t → t.cnt s = 0 :=
  fun t ht => Budget.stmt_site (hb t ht) hs ho

/-- Realization through a statement that sets only one variable. -/
theorem bset {ctx : Ctx} (hc : CtxOK ctx) {st : Stmt} {x : Var} {S : List Origin}
    {k k' : Var → NK} {E : CState → Prop} {Y : AState} {D D' : Nat}
    (hok : StmtOK ctx st) (hb : ∀ t, E t → Budget ctx (.stmt st) t) (h : BInv ctx k E Y D)
    (hDD : D ≤ D') (habs : astep ctx st Y = Y.setVar x S) (hcert : bstep ctx k Y st = some k')
    (hframe : ∀ t u, SStep st t u → u.heap = t.heap ∧ (∀ x', x' ≠ x → u.env x' = t.env x') ∧
      (∀ s, t.cnt s ≤ u.cnt s) ∧ (∀ s, t.cnt s ≠ u.cnt s → st.site? = some s))
    (honce : ∀ s, st.site? = some s → ctx.once s = true)
    (hval : ∀ t u, E t → SStep st t u → ∀ s n, u.env x = some (.alloc s n) → n < u.cnt s)
    (hS : ∀ o ∈ S, o ∈ ctx.origins ∧ dep ctx.K o ≤ D' ∧
      ∃ u, (∃ t, E t ∧ Exec (.stmt st) t u) ∧ u.env x = some (gamma o)) :
    BInv ctx k' (fun u => ∃ t, E t ∧ Exec (.stmt st) t u) (astep ctx st Y) D' := by
  have hrun : ∀ t, E t → (∃ u, SStep st t u) ∧ ∀ u, SStep st t u → Good k' u := fun t ht =>
    bstep_good hc hok hcert (h.states t ht).1 (h.states t ht).2.1 (h.states t ht).2.2
  have hEx : ∀ u, (∃ t, E t ∧ Exec (.stmt st) t u) → ∃ t, E t ∧ SStep st t u := by
    rintro u ⟨t, ht, hx⟩; cases hx with | stmt hs => exact ⟨t, ht, hs⟩
  have hsucc : ∀ t, E t → ∃ u, (∃ t', E t' ∧ Exec (.stmt st) t' u) ∧ SStep st t u := by
    intro t ht
    obtain ⟨u, hu⟩ := (hrun t ht).1
    exact ⟨u, ⟨t, ht, .stmt hu⟩, hu⟩
  have hE0 : ∀ s, (∀ u, (∃ t, E t ∧ Exec (.stmt st) t u) → u.cnt s = 0) → ∀ t, E t → t.cnt s = 0 := by
    intro s hz t ht
    obtain ⟨u, hu, hs⟩ := hsucc t ht
    have := (hframe t u hs).2.2.1 s
    have := hz u hu
    omega
  rw [habs]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- states
    intro u hu
    obtain ⟨t, ht, hs⟩ := hEx u hu
    obtain ⟨hi, _, ha⟩ := h.states t ht
    obtain ⟨hh, henv, hcnt, _⟩ := hframe t u hs
    refine ⟨habs ▸ step_sound hc hok (hb t ht) hi hs, (hrun t ht).2 u hs, ?_, ?_, ?_, ?_⟩
    · intro x' a n he
      by_cases e : x' = x
      · subst e; exact hval t u ht hs a n he
      · rw [henv x' e] at he
        exact Nat.lt_of_lt_of_le (ha.env x' a n he) (hcnt a)
    · intro o c a n he
      rw [hh] at he
      exact Nat.lt_of_lt_of_le (ha.heap o c a n he) (hcnt a)
    · intro a n c hn
      rw [hh]
      exact ha.fresh a n c (Nat.le_trans (hcnt a) hn)
    · intro b p c
      rw [hh]
      exact ha.symNN b p c
  · -- ne
    obtain ⟨t, ht⟩ := h.ne
    obtain ⟨u, hu, _⟩ := hsucc t ht
    exact ⟨u, hu⟩
  · -- supp
    refine ⟨fun x' o ho => ?_, h.supp.heap⟩
    change o ∈ fupd Y.env x S x' at ho
    by_cases e : x' = x
    · subst e; rw [fupd_same] at ho; exact (hS o ho).1
    · rw [fupd_ne _ _ e] at ho; exact h.supp.env x' o ho
  · -- depH
    intro o c o' ho'
    have := h.depH o c o' ho'
    omega
  · -- a0
    intro s hz c
    exact h.a0 s (hE0 s hz) c
  · -- real
    intro x' o ho
    change o ∈ fupd Y.env x S x' at ho
    by_cases e : x' = x
    · subst e; rw [fupd_same] at ho; exact ⟨(hS o ho).2.1, (hS o ho).2.2⟩
    · rw [fupd_ne _ _ e] at ho
      obtain ⟨hd, t, ht, he⟩ := h.real x' o ho
      obtain ⟨u, hu, hs⟩ := hsucc t ht
      exact ⟨Nat.le_trans hd hDD, u, hu, ((hframe t u hs).2.1 x' e).trans he⟩
  · -- hr
    intro o ho c hc' o' ho' hd u hu hl
    obtain ⟨t, ht, hs⟩ := hEx u hu
    obtain ⟨hh, _, _, hsite⟩ := hframe t u hs
    rw [hh]
    have hlt : AllocLive t o := by
      intro a e
      by_cases hz : 1 ≤ t.cnt a
      · exact hz
      · exfalso
        have hne : t.cnt a ≠ u.cnt a := by have := hl a e; omega
        have hsa := hsite a hne
        have := h.a0 a (budget_zero hb hsa (honce a hsa)) c
        subst e
        change o' ∈ Y.heap (.alloc a) c at ho'
        rw [this] at ho'
        cases ho'
    exact h.hr o ho c hc' o' ho' hd t ht hlt

/-- Realization through a certified store: the store is strong, and it writes the same
canonical object into the same canonical cell in every state. -/
theorem bstore {ctx : Ctx} (hc : CtxOK ctx) {x y : Var} {f : Field}
    {k k' : Var → NK} {E : CState → Prop} {Y : AState} {D : Nat}
    (hok : StmtOK ctx (.store x f y)) (hb : ∀ t, E t → Budget ctx (.stmt (.store x f y)) t)
    (h : BInv ctx k E Y D) (hDK : D ≤ ctx.K) (hcert : bstep ctx k Y (.store x f y) = some k') :
    BInv ctx k' (fun u => ∃ t, E t ∧ Exec (.stmt (.store x f y)) t u)
      (astep ctx (.store x f y) Y) D := by
  have hcert' := hcert
  simp only [bstep] at hcert'
  split at hcert'
  · rename_i hcond
    simp only [Option.some.injEq] at hcert'
    subst hcert'
    obtain ⟨hkx, hky, hsx, hsy⟩ := hcond
    have hxv : x ∈ ctx.vars := hok.vars x (by simp [Stmt.vars])
    have hyv : y ∈ ctx.vars := hok.vars y (by simp [Stmt.vars])
    have hf : ACell.fld f ∈ ctx.cells := hok.fields f (by simp [Stmt.fields])
    have hdx : ∀ o ∈ Y.env x, dep ctx.K o ≤ ctx.K := fun o ho => Nat.le_trans (h.real x o ho).1 hDK
    have hdy : ∀ o ∈ Y.env y, dep ctx.K o ≤ ctx.K := fun o ho => Nat.le_trans (h.real y o ho).1 hDK
    -- the origins of `x` and `y`
    unfold strongB at hsx hsy
    cases ex : single? (Y.env x) with
    | none => rw [ex] at hsx; cases hsx
    | some o =>
    rw [ex] at hsx
    cases ey : single? (Y.env y) with
    | none => rw [ey] at hsy; cases hsy
    | some o' =>
    rw [ey] at hsy
    have habs : astep ctx (.store x f y) Y = Y.setCell o (.fld f) (Y.env y) := by
      show Y.store ctx.once x (.fld f) (Y.env y) ctx.entryUnique = _
      unfold AState.store
      rw [ex]
      exact if_pos hsx
    have hval : ∀ t, E t → t.env x = some (gamma o) ∧ t.env y = some (gamma o') := by
      intro t ht
      obtain ⟨hi, hg, _⟩ := h.states t ht
      obtain ⟨vx, hvx⟩ := (hg x).2 hkx
      obtain ⟨vy, hvy⟩ := (hg y).2 hky
      have hsx' : strongB ctx Y x = true := by unfold strongB; rw [ex]; exact hsx
      have hsy' : strongB ctx Y y = true := by unfold strongB; rw [ey]; exact hsy
      obtain ⟨o1, e1, _, h1⟩ := value_of_strong hi hxv hvx hsx' hdx
      obtain ⟨o2, e2, _, h2⟩ := value_of_strong hi hyv hvy hsy' hdy
      rw [ex] at e1; rw [ey] at e2
      cases e1; cases e2
      exact ⟨hvx.trans (congrArg some h1), hvy.trans (congrArg some h2)⟩
    have hoy : ∀ o2 ∈ Y.env y, o2 = o' := (single?_spec ey).2
    have hox : o ∈ Y.env x := (single?_spec ex).1
    have hrun : ∀ t, E t → (∃ u, SStep (.store x f y) t u) ∧
        ∀ u, SStep (.store x f y) t u → Good k u := fun t ht =>
      bstep_good hc hok hcert (h.states t ht).1 (h.states t ht).2.1 (h.states t ht).2.2
    -- each successor state is the store of the canonical objects
    have hEx : ∀ u, (∃ t, E t ∧ Exec (.stmt (.store x f y)) t u) →
        ∃ t, E t ∧ SStep (.store x f y) t u ∧
          u = t.setCell (gamma o) (.fld f) (some (gamma o')) := by
      rintro u ⟨t, ht, hx⟩
      cases hx with
      | stmt hs =>
        refine ⟨t, ht, hs, ?_⟩
        cases hs with
        | store he =>
          rw [(hval t ht).1] at he; cases he
          rw [(hval t ht).2]
    have hsucc : ∀ t, E t → ∃ u, (∃ t', E t' ∧ Exec (.stmt (.store x f y)) t' u) ∧
        u = t.setCell (gamma o) (.fld f) (some (gamma o')) := by
      intro t ht
      obtain ⟨u, hu⟩ := (hrun t ht).1
      obtain ⟨t', _, _, e⟩ := hEx u ⟨t, ht, .stmt hu⟩
      refine ⟨u, ⟨t, ht, .stmt hu⟩, ?_⟩
      cases hu with
      | store he =>
        rw [(hval t ht).1] at he; cases he
        rw [(hval t ht).2]
    rw [habs]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- states
      intro u hu
      obtain ⟨t, ht, hs, rfl⟩ := hEx u hu
      obtain ⟨hi, _, ha⟩ := h.states t ht
      refine ⟨habs ▸ step_sound hc hok (hb t ht) hi hs, (hrun t ht).2 _ hs, ?_, ?_, ?_, ?_⟩
      · exact ha.env
      · intro o1 c a n he
        change fupd2 t.heap (gamma o) (.fld f) (some (gamma o')) o1 c = _ at he
        by_cases e : o1 = gamma o ∧ c = .fld f
        · obtain ⟨rfl, rfl⟩ := e
          rw [fupd2_same] at he
          exact ha.env y a n (((hval t ht).2).trans he)
        · rw [fupd2_ne _ _ e] at he; exact ha.heap o1 c a n he
      · intro a n c hn
        show fupd2 t.heap (gamma o) (.fld f) (some (gamma o')) (.alloc a n) c = none
        have hne : ¬ (Obj.alloc a n = gamma o ∧ c = .fld f) := by
          rintro ⟨e, _⟩
          have := ha.env x a n (((hval t ht).1).trans (congrArg some e.symm))
          change t.cnt a ≤ n at hn
          omega
        rw [fupd2_ne _ _ hne]
        exact ha.fresh a n c hn
      · intro b p c
        show fupd2 t.heap (gamma o) (.fld f) (some (gamma o')) (.sym b p) c ≠ none
        by_cases e : Obj.sym b p = gamma o ∧ c = .fld f
        · obtain ⟨e1, rfl⟩ := e
          rw [e1, fupd2_same]; intro h; cases h
        · rw [fupd2_ne _ _ e]; exact ha.symNN b p c
    · -- ne
      obtain ⟨t, ht⟩ := h.ne
      obtain ⟨u, hu, _⟩ := hsucc t ht
      exact ⟨u, hu⟩
    · -- supp
      refine ⟨h.supp.env, fun o1 ho1 c hc1 o2 ho2 => ?_⟩
      change o2 ∈ fupd2 Y.heap o (.fld f) (Y.env y) o1 c at ho2
      by_cases e : o1 = o ∧ c = .fld f
      · obtain ⟨rfl, rfl⟩ := e
        rw [fupd2_same] at ho2; exact h.supp.env y o2 ho2
      · rw [fupd2_ne _ _ e] at ho2; exact h.supp.heap o1 ho1 c hc1 o2 ho2
    · -- depH
      intro o1 c o2 ho2
      change o2 ∈ fupd2 Y.heap o (.fld f) (Y.env y) o1 c at ho2
      by_cases e : o1 = o ∧ c = .fld f
      · obtain ⟨rfl, rfl⟩ := e
        rw [fupd2_same] at ho2
        have := (h.real y o2 ho2).1
        omega
      · rw [fupd2_ne _ _ e] at ho2; exact h.depH o1 c o2 ho2
    · -- a0
      intro a hz c
      have hz' : ∀ t, E t → t.cnt a = 0 := by
        intro t ht
        obtain ⟨u, hu, e⟩ := hsucc t ht
        have := hz u hu
        rw [e] at this
        exact this
      change fupd2 Y.heap o (.fld f) (Y.env y) (.alloc a) c = []
      by_cases e : Origin.alloc a = o ∧ c = .fld f
      · exfalso
        obtain ⟨t, ht⟩ := h.ne
        obtain ⟨_, _, ha⟩ := h.states t ht
        have hx1 := (hval t ht).1
        rw [← e.1] at hx1
        have := ha.env x a 0 hx1
        have := hz' t ht
        omega
      · rw [fupd2_ne _ _ e]; exact h.a0 a hz' c
    · -- real
      intro x' o1 ho1
      obtain ⟨hd, t, ht, he⟩ := h.real x' o1 ho1
      obtain ⟨u, hu, rfl⟩ := hsucc t ht
      exact ⟨hd, _, hu, he⟩
    · -- hr
      intro o1 ho1 c hc1 o2 ho2 hd u hu hl
      obtain ⟨t, ht, _, rfl⟩ := hEx u hu
      show fupd2 t.heap (gamma o) (.fld f) (some (gamma o')) (gamma o1) (canon c) = _
      change o2 ∈ fupd2 Y.heap o (.fld f) (Y.env y) o1 c at ho2
      by_cases e : o1 = o ∧ c = .fld f
      · obtain ⟨rfl, rfl⟩ := e
        rw [fupd2_same] at ho2
        rw [hoy o2 ho2]
        exact fupd2_same _ _ _ _
      · rw [fupd2_ne _ _ e] at ho2
        have e2 : ¬ (gamma o1 = gamma o ∧ canon c = .fld f) := by
          rintro ⟨e1, e2⟩
          apply e
          refine ⟨gamma_inj (Nat.le_of_lt hd) (hdx o hox) e1, ?_⟩
          cases c with
          | fld g => simp only [canon, Cell.fld.injEq] at e2; rw [e2]
          | elem => simp [canon] at e2
        rw [fupd2_ne _ _ e2]
        exact h.hr o1 ho1 c hc1 o2 ho2 hd t ht hl
  · cases hcert'

/-- The frame facts of a variable update. -/
theorem frame_setVar (t : CState) (x : Var) (v : Val) (st : Stmt) :
    (t.setVar x v).heap = t.heap ∧ (∀ x', x' ≠ x → (t.setVar x v).env x' = t.env x') ∧
      (∀ s, t.cnt s ≤ (t.setVar x v).cnt s) ∧ (∀ s, t.cnt s ≠ (t.setVar x v).cnt s → st.site? = some s) :=
  ⟨rfl, fun x' h => setVar_other t x v x' h, fun _ => Nat.le_refl _, fun _ h => absurd rfl h⟩

/-- The frame facts of a variable update followed by a bump of the site of the statement. -/
theorem frame_setVar_bump (t : CState) (x : Var) (v : Val) (st : Stmt) (a : Site)
    (hs : st.site? = some a) :
    ((t.setVar x v).bump a).heap = t.heap ∧
      (∀ x', x' ≠ x → ((t.setVar x v).bump a).env x' = t.env x') ∧
      (∀ s, t.cnt s ≤ ((t.setVar x v).bump a).cnt s) ∧
      (∀ s, t.cnt s ≠ ((t.setVar x v).bump a).cnt s → st.site? = some s) := by
  refine ⟨rfl, fun x' h => setVar_other t x v x' h, fun s => ?_, fun s h => ?_⟩
  · show t.cnt s ≤ fupd t.cnt a (t.cnt a + 1) s
    by_cases e : s = a
    · subst e; rw [fupd_same]; exact Nat.le_succ _
    · rw [fupd_ne _ _ e]; exact Nat.le_refl _
  · change t.cnt s ≠ fupd t.cnt a (t.cnt a + 1) s at h
    by_cases e : s = a
    · rw [e]; exact hs
    · rw [fupd_ne _ _ e] at h; exact absurd rfl h

/-- Realization through one certified statement. -/
theorem bstmt {ctx : Ctx} (hc : CtxOK ctx) {st : Stmt} {k k' : Var → NK} {E : CState → Prop}
    {Y : AState} {D : Nat} (hok : StmtOK ctx st) (hb : ∀ t, E t → Budget ctx (.stmt st) t)
    (honce : ∀ s ∈ (Prog.stmt st).sites, ctx.once s = true) (h : BInv ctx k E Y D)
    (hD : D + loadsS st ≤ ctx.K) (hcert : bstep ctx k Y st = some k') :
    BInv ctx k' (fun u => ∃ t, E t ∧ Exec (.stmt st) t u) (astep ctx st Y) (D + loadsS st) := by
  have honce' : ∀ s, st.site? = some s → ctx.once s = true :=
    fun s hs => honce s (by rw [sites_stmt, hs]; exact List.mem_singleton.mpr rfl)
  obtain ⟨t0, ht0⟩ := h.ne
  cases st with
  | new x a =>
    have hz := budget_zero hb rfl (honce' a rfl) t0 ht0
    refine bset hc hok hb h (Nat.le_add_right _ _) rfl hcert ?_ honce' ?_ ?_
    · intro t u hs; cases hs; exact frame_setVar_bump t x _ _ a rfl
    · intro t u _ hs a' n he
      cases hs
      change fupd t.env x (some (.alloc a (t.cnt a))) x = _ at he
      rw [fupd_same] at he; cases he
      show t.cnt a < fupd t.cnt a (t.cnt a + 1) a
      rw [fupd_same]; exact Nat.lt_succ_self _
    · intro o ho
      rw [List.mem_singleton] at ho; subst ho
      refine ⟨hok.newS a rfl, Nat.zero_le _, _, ⟨t0, ht0, .stmt .new⟩, ?_⟩
      show fupd t0.env x (some (.alloc a (t0.cnt a))) x = _
      rw [fupd_same, hz]; rfl
  | null x =>
    refine bset (S := []) hc hok hb h (Nat.le_add_right _ _) rfl hcert ?_ honce' ?_ ?_
    · intro t u hs; cases hs; exact frame_setVar t x _ _
    · intro t u _ hs a' n he
      cases hs
      change fupd t.env x none x = _ at he
      rw [fupd_same] at he; cases he
    · intro o ho; cases ho
  | copy x y =>
    refine bset hc hok hb h (Nat.le_add_right _ _) rfl hcert ?_ honce' ?_ ?_
    · intro t u hs; cases hs; exact frame_setVar t x _ _
    · intro t u ht hs a' n he
      cases hs
      change fupd t.env x (t.env y) x = _ at he
      rw [fupd_same] at he
      exact (h.states t ht).2.2.env y a' n he
    · intro o ho
      obtain ⟨hd, t, ht, he⟩ := h.real y o ho
      refine ⟨h.supp.env y o ho, Nat.le_trans hd (Nat.le_add_right _ _), _,
        ⟨t, ht, .stmt .copy⟩, ?_⟩
      show fupd t.env x (t.env y) x = _
      rw [fupd_same, he]
  | unknown x a =>
    have hz := budget_zero hb rfl (honce' a rfl) t0 ht0
    refine bset hc hok hb h (Nat.le_add_right _ _) rfl hcert ?_ honce' ?_ ?_
    · intro t u hs; cases hs; exact frame_setVar_bump t x _ _ a rfl
    · intro t u _ hs a' n he
      cases hs
      change fupd t.env x (some (.sym (.fresh a (t.cnt a)) [])) x = _ at he
      rw [fupd_same] at he; cases he
    · intro o ho
      rw [List.mem_singleton] at ho; subst ho
      refine ⟨hok.freshS a rfl, Nat.zero_le _, _, ⟨t0, ht0, .stmt .unknown⟩, ?_⟩
      show fupd t0.env x (some (.sym (.fresh a (t0.cnt a)) [])) x = _
      rw [fupd_same, hz]; rfl
  | load x y f =>
    have hf : ACell.fld f ∈ ctx.cells := hok.fields f (by simp [Stmt.fields])
    refine bset hc hok hb h (Nat.le_add_right _ _) rfl hcert ?_ honce' ?_ ?_
    · intro t u hs; cases hs; exact frame_setVar t x _ _
    · intro t u ht hs a' n he
      cases hs with
      | load _ =>
        change fupd t.env x _ x = _ at he
        rw [fupd_same] at he
        exact (h.states t ht).2.2.heap _ _ a' n he
    · intro o ho
      obtain ⟨o0, h0, h1⟩ := mem_aread.mp ho
      obtain ⟨hd, t, ht, he⟩ := h.real y o0 h0
      have hdk : dep ctx.K o0 < ctx.K := by simp only [loadsS] at hD; omega
      have hl : AllocLive t o0 := by
        intro a e; subst e
        exact (h.states t ht).2.2.env y a 0 he
      have hr := h.hr o0 (h.supp.env y o0 h0) _ hf o h1 hdk t ht hl
      refine ⟨h.supp.heap o0 (h.supp.env y o0 h0) _ hf o h1, ?_, _,
        ⟨t, ht, .stmt (.load he)⟩, ?_⟩
      · have := h.depH o0 _ o h1
        simp only [loadsS]; omega
      · show fupd t.env x (t.heap (gamma o0) (.fld f)) x = _
        rw [fupd_same]; exact hr
  | aload x y =>
    refine bset hc hok hb h (Nat.le_add_right _ _) rfl hcert ?_ honce' ?_ ?_
    · intro t u hs; cases hs; exact frame_setVar t x _ _
    · intro t u ht hs a' n he
      cases hs with
      | aload i _ =>
        change fupd t.env x _ x = _ at he
        rw [fupd_same] at he
        exact (h.states t ht).2.2.heap _ _ a' n he
    · intro o ho
      obtain ⟨o0, h0, h1⟩ := mem_aread.mp ho
      obtain ⟨hd, t, ht, he⟩ := h.real y o0 h0
      have hdk : dep ctx.K o0 < ctx.K := by simp only [loadsS] at hD; omega
      have hl : AllocLive t o0 := by
        intro a e; subst e
        exact (h.states t ht).2.2.env y a 0 he
      have hr := h.hr o0 (h.supp.env y o0 h0) _ hc.elem o h1 hdk t ht hl
      refine ⟨h.supp.heap o0 (h.supp.env y o0 h0) _ hc.elem o h1, ?_, _,
        ⟨t, ht, .stmt (.aload 0 he)⟩, ?_⟩
      · have := h.depH o0 _ o h1
        simp only [loadsS]; omega
      · show fupd t.env x (t.heap (gamma o0) (.elem 0)) x = _
        rw [fupd_same]; exact hr
  | store x f y =>
    have := bstore hc hok hb h (by simp only [loadsS] at hD; omega) hcert
    simp only [loadsS, Nat.add_zero]
    exact this
  | astore _ _ => simp [bstep] at hcert
  | call _ _ _ => simp [bstep] at hcert

/-! ## Programs -/

/-- The realization invariant depends only on the members of the state set. -/
theorem BInv.congrE {ctx : Ctx} {k : Var → NK} {E E' : CState → Prop} {Y : AState} {D : Nat}
    (h : BInv ctx k E Y D) (hE : ∀ u, E' u ↔ E u) : BInv ctx k E' Y D where
  states t ht := h.states t ((hE t).mp ht)
  ne := let ⟨t, ht⟩ := h.ne; ⟨t, (hE t).mpr ht⟩
  supp := h.supp
  depH := h.depH
  a0 s hz c := h.a0 s (fun t ht => hz t ((hE t).mpr ht)) c
  real x o ho := let ⟨hd, t, ht, he⟩ := h.real x o ho; ⟨hd, t, (hE t).mpr ht, he⟩
  hr o ho c hc o' ho' hd t ht hl := h.hr o ho c hc o' ho' hd t ((hE t).mp ht) hl

/-- The join check of one cell: equal contents, or a cell of an allocation site of one
branch where the other branch has no content. -/
theorem cellJoinOK_spec {p q : Prog} {Yp Yq : AState} {o : Origin} {c : ACell}
    (h : cellJoinOK p q Yp Yq o c = true) :
    (∀ a, a ∈ Yp.heap o c ↔ a ∈ Yq.heap o c) ∨
      ∃ s, o = .alloc s ∧ ((s ∈ p.sites ∧ Yq.heap o c = []) ∨ (s ∈ q.sites ∧ Yp.heap o c = [])) := by
  unfold cellJoinOK at h
  rcases Bool.or_eq_true_iff.mp h with h1 | h1
  · rw [Bool.and_eq_true] at h1
    exact Or.inl fun a => ⟨fun ha => subB_iff.mp h1.1 a ha, fun ha => subB_iff.mp h1.2 a ha⟩
  · right
    cases o with
    | alloc s =>
      refine ⟨s, rfl, ?_⟩
      rcases Bool.or_eq_true_iff.mp h1 with h2 | h2
      · rw [Bool.and_eq_true, List.contains_iff_mem, List.isEmpty_iff] at h2
        exact Or.inl h2
      · rw [Bool.and_eq_true, List.contains_iff_mem, List.isEmpty_iff] at h2
        exact Or.inr h2
    | sym _ _ => cases h1
    | deep _ => cases h1
    | havoc _ => cases h1
    | hsym _ _ _ _ => cases h1
    | hdeep _ _ _ => cases h1

/-- A site of the left branch does not run in the right branch, from a state with the budget. -/
theorem branch_site_zero {ctx : Ctx} {p q : Prog} {t u : CState} {s : Site}
    (hb : Budget ctx (.choice p q) t) (ho : ctx.once s = true) (hs : s ∈ p.sites)
    (hx : Exec q t u) : u.cnt s = 0 := by
  obtain ⟨h1, h2⟩ := hb s ho
  rw [sites_choice, List.count_append] at h1
  rw [loopSites_choice, List.mem_append, not_or] at h2
  have hp : 0 < p.sites.count s := List.count_pos_iff.mpr hs
  have := Exec.cnt_le hx s h2.2
  omega

/-- Realization through a certified program. -/
theorem realizeB {ctx : Ctx} (hc : CtxOK ctx) : ∀ (q : Prog), (∀ st ∈ q.stmts, StmtOK ctx st) →
    (∀ s ∈ q.sites, ctx.once s = true) →
    ∀ {k k' : Var → NK} {E : CState → Prop} {Y : AState} {D : Nat},
    bcert ctx q k Y = some k' → (∀ t, E t → Budget ctx q t) → BInv ctx k E Y D →
    D + loadsP q ≤ ctx.K →
    BInv ctx k' (fun u => ∃ t, E t ∧ Exec q t u) (analyze ctx q Y) (D + loadsP q) := by
  intro q
  induction q with
  | skip =>
    intro _ _ k k' E Y D hcert _ h _
    simp only [bcert, Option.some.injEq] at hcert; subst hcert
    refine h.congrE fun u => ⟨fun ⟨t, ht, hx⟩ => by cases hx; exact ht, fun hu => ⟨u, hu, .skip⟩⟩
  | stmt st =>
    intro hok ho k k' E Y D hcert hb h hD
    exact bstmt hc (hok st (List.mem_singleton.mpr rfl)) hb ho h hD hcert
  | seq p q ihp ihq =>
    intro hok ho k k' E Y D hcert hb h hD
    simp only [bcert] at hcert
    cases e1 : bcert ctx p k Y with
    | none => rw [e1] at hcert; cases hcert
    | some k1 =>
      rw [e1, Option.bind_some] at hcert
      have hokp : ∀ st ∈ p.stmts, StmtOK ctx st :=
        fun st hs => hok st (List.mem_append.mpr (Or.inl hs))
      have hokq : ∀ st ∈ q.stmts, StmtOK ctx st :=
        fun st hs => hok st (List.mem_append.mpr (Or.inr hs))
      have hop : ∀ s ∈ p.sites, ctx.once s = true :=
        fun s hs => ho s (by rw [sites_seq]; exact List.mem_append.mpr (Or.inl hs))
      have hoq : ∀ s ∈ q.sites, ctx.once s = true :=
        fun s hs => ho s (by rw [sites_seq]; exact List.mem_append.mpr (Or.inr hs))
      simp only [loadsP] at hD ⊢
      have h1 := ihp hokp hop e1 (fun t ht => Budget.seqL (hb t ht)) h (by omega)
      have hb1 : ∀ u, (∃ t, E t ∧ Exec p t u) → Budget ctx q u := by
        rintro u ⟨t, ht, hx⟩; exact Budget.seqR (hb t ht) hx
      have h2 := ihq hokq hoq hcert hb1 h1 (by omega)
      rw [← Nat.add_assoc]
      refine h2.congrE fun v => ⟨?_, ?_⟩
      · rintro ⟨t, ht, hx⟩
        cases hx with
        | seq h1 h2 => exact ⟨_, ⟨t, ht, h1⟩, h2⟩
      · rintro ⟨u, ⟨t, ht, h1⟩, h2⟩
        exact ⟨t, ht, .seq h1 h2⟩
  | choice p q ihp ihq =>
    intro hok ho k k' E Y D hcert hb h hD
    simp only [bcert] at hcert
    cases e1 : bcert ctx p k Y with
    | none => rw [e1] at hcert; cases hcert
    | some k1 =>
    cases e2 : bcert ctx q k Y with
    | none => rw [e1, e2] at hcert; cases hcert
    | some k2 =>
    rw [e1, e2] at hcert
    simp only at hcert
    split at hcert
    · rename_i hj
      simp only [Option.some.injEq] at hcert; subst hcert
      have hokp : ∀ st ∈ p.stmts, StmtOK ctx st :=
        fun st hs => hok st (List.mem_append.mpr (Or.inl hs))
      have hokq : ∀ st ∈ q.stmts, StmtOK ctx st :=
        fun st hs => hok st (List.mem_append.mpr (Or.inr hs))
      have hop : ∀ s ∈ p.sites, ctx.once s = true :=
        fun s hs => ho s (by rw [sites_choice]; exact List.mem_append.mpr (Or.inl hs))
      have hoq : ∀ s ∈ q.sites, ctx.once s = true :=
        fun s hs => ho s (by rw [sites_choice]; exact List.mem_append.mpr (Or.inr hs))
      simp only [loadsP] at hD ⊢
      have hp := ihp hokp hop e1 (fun t ht => Budget.choiceL (hb t ht)) h (by omega)
      have hq := ihq hokq hoq e2 (fun t ht => Budget.choiceR (hb t ht)) h (by omega)
      have hEx : ∀ u, (∃ t, E t ∧ Exec (.choice p q) t u) →
          (∃ t, E t ∧ Exec p t u) ∨ (∃ t, E t ∧ Exec q t u) := by
        rintro u ⟨t, ht, hx⟩
        cases hx with
        | choiceL h1 => exact Or.inl ⟨t, ht, h1⟩
        | choiceR h1 => exact Or.inr ⟨t, ht, h1⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro u hu
        rcases hEx u hu with hu | hu
        · obtain ⟨hi, hg, ha⟩ := hp.states u hu
          exact ⟨hi.mono (sub_join_left _ _), hg.joinL, ha⟩
        · obtain ⟨hi, hg, ha⟩ := hq.states u hu
          exact ⟨hi.mono (sub_join_right _ _), hg.joinR, ha⟩
      · obtain ⟨u, t, ht, hx⟩ := hp.ne
        exact ⟨u, t, ht, .choiceL hx⟩
      · refine ⟨fun x o ho => ?_, fun o ho c hc' o' ho' => ?_⟩
        · rcases mem_uni.mp ho with ho | ho
          · exact hp.supp.env x o ho
          · exact hq.supp.env x o ho
        · rcases mem_uni.mp ho' with ho' | ho'
          · exact hp.supp.heap o ho c hc' o' ho'
          · exact hq.supp.heap o ho c hc' o' ho'
      · intro o c o' ho'
        rcases mem_uni.mp ho' with ho' | ho'
        · have := hp.depH o c o' ho'; omega
        · have := hq.depH o c o' ho'; omega
      · intro s hz c
        have h1 := hp.a0 s (fun u ⟨t, ht, hx⟩ => hz u ⟨t, ht, .choiceL hx⟩) c
        have h2 := hq.a0 s (fun u ⟨t, ht, hx⟩ => hz u ⟨t, ht, .choiceR hx⟩) c
        show uni _ _ = []
        rw [h1, h2]; rfl
      · intro x o ho
        rcases mem_uni.mp ho with ho | ho
        · obtain ⟨hd, u, ⟨t, ht, hx⟩, he⟩ := hp.real x o ho
          exact ⟨by omega, u, ⟨t, ht, .choiceL hx⟩, he⟩
        · obtain ⟨hd, u, ⟨t, ht, hx⟩, he⟩ := hq.real x o ho
          exact ⟨by omega, u, ⟨t, ht, .choiceR hx⟩, he⟩
      · intro o ho c hc' o' ho' hd u hu hl
        have hcell := cellJoinOK_spec
          (List.all_eq_true.mp (List.all_eq_true.mp hj o ho) c hc')
        rcases hEx u hu with hu | hu
        · -- the state comes from the left branch
          rcases hcell with heq | ⟨s, rfl, ⟨hs, hqe⟩ | ⟨hs, hpe⟩⟩
          · have : o' ∈ (analyze ctx p Y).heap o c := by
              rcases mem_uni.mp ho' with h' | h'
              · exact h'
              · exact (heq o').mpr h'
            exact hp.hr o ho c hc' o' this hd u hu hl
          · have : o' ∈ (analyze ctx p Y).heap (.alloc s) c := by
              rcases mem_uni.mp ho' with h' | h'
              · exact h'
              · rw [hqe] at h'; cases h'
            exact hp.hr _ ho c hc' o' this hd u hu hl
          · exfalso
            obtain ⟨t, ht, hx⟩ := hu
            have := branch_site_zero (p := q) (q := p) (by
              intro a ha
              obtain ⟨h1, h2⟩ := hb t ht a ha
              rw [sites_choice, List.count_append] at h1
              rw [loopSites_choice, List.mem_append, not_or] at h2
              refine ⟨?_, ?_⟩
              · rw [sites_choice, List.count_append]; omega
              · rw [loopSites_choice, List.mem_append, not_or]; exact ⟨h2.2, h2.1⟩)
              (hoq s hs) hs hx
            have := hl s rfl
            omega
        · -- the state comes from the right branch
          rcases hcell with heq | ⟨s, rfl, ⟨hs, hqe⟩ | ⟨hs, hpe⟩⟩
          · have : o' ∈ (analyze ctx q Y).heap o c := by
              rcases mem_uni.mp ho' with h' | h'
              · exact (heq o').mp h'
              · exact h'
            exact hq.hr o ho c hc' o' this hd u hu hl
          · exfalso
            obtain ⟨t, ht, hx⟩ := hu
            have := branch_site_zero (hb t ht) (hop s hs) hs hx
            have := hl s rfl
            omega
          · have : o' ∈ (analyze ctx q Y).heap (.alloc s) c := by
              rcases mem_uni.mp ho' with h' | h'
              · rw [hpe] at h'; cases h'
              · exact h'
            exact hq.hr _ ho c hc' o' this hd u hu hl
    · cases hcert
  | loop _ _ => intro _ _ k k' E Y D hcert; simp [bcert] at hcert

/-! ## Entry state and queries -/

/-- The entry state satisfies the realization invariant. -/
theorem binv_init {ctx : Ctx} (hc : CtxOK ctx) {fr : Frame} (hf : FrameOK ctx fr) :
    BInv ctx (entryKinds fr) (fun t => t = CState.init fr) (ainit ctx.K fr) 0 where
  states t ht := by
    subst ht
    refine ⟨inv_init hc hf, good_entry fr, ?_, ?_, ?_, ?_⟩
    · intro x s n he
      change (fr.root? x).map _ = _ at he
      cases e : fr.root? x with
      | none => rw [e] at he; cases he
      | some r => rw [e] at he; cases he
    · intro o c s n he
      change cdefault o c = _ at he
      cases o with
      | sym _ _ => cases he
      | alloc _ _ => cases he
    · intro s n c _; rfl
    · intro b p c he; cases he
  ne := ⟨_, rfl⟩
  supp := by
    refine ⟨fun x o ho => ?_, fun o ho c hc' o' ho' => hc.dflt o ho c hc' o' ho'⟩
    change o ∈ (match fr.root? x with | some r => [Origin.sym (.root r) []] | none => []) at ho
    cases e : fr.root? x with
    | none => rw [e] at ho; cases ho
    | some r =>
      rw [e, List.mem_singleton] at ho
      subst ho
      exact hf.roots x r e
  depH := by
    intro o c o' ho'
    change o' ∈ adefault ctx.K o c at ho'
    cases o with
    | sym b q =>
      simp only [adefault, symOrDeep, List.mem_singleton] at ho'
      split at ho'
      · subst ho'; simp [dep]
      · rename_i hl
        subst ho'; simp only [dep]
        simp only [List.length_append, List.length_singleton] at hl
        omega
    | deep b =>
      simp only [adefault, List.mem_singleton] at ho'; subst ho'; simp [dep]
    | alloc s => cases ho'
    | havoc s =>
      simp only [adefault, List.mem_singleton] at ho'; subst ho'; simp [dep]
    | hsym s k c0 q =>
      simp only [adefault, List.mem_singleton] at ho'
      split at ho' <;> (subst ho'; simp [dep])
    | hdeep s k c0 =>
      simp only [adefault, List.mem_singleton] at ho'; subst ho'; simp [dep]
  a0 s _ c := rfl
  real := by
    intro x o ho
    change o ∈ (match fr.root? x with | some r => [Origin.sym (.root r) []] | none => []) at ho
    cases e : fr.root? x with
    | none => rw [e] at ho; cases ho
    | some r =>
      rw [e, List.mem_singleton] at ho
      subst ho
      refine ⟨Nat.zero_le _, _, rfl, ?_⟩
      simp [CState.init, e, gamma]
  hr := by
    intro o _ c _ o' ho' hd t ht _
    subst ht
    exact (dflt_gamma (by omega) ho').1

/-- A path walk over a realized heap reads the canonical objects in every state of `E`. -/
theorem walkB {ctx : Ctx} {k : Var → NK} {E : CState → Prop} {Y : AState} {D : Nat}
    (h : BInv ctx k E Y D) :
    ∀ (px : List ACell) (S : List Origin) (o : Origin), o ∈ aevalFrom Y S px →
      (∀ c ∈ px, c ∈ ctx.cells) → (∀ o0 ∈ S, o0 ∈ ctx.origins ∧ dep ctx.K o0 + px.length ≤ ctx.K) →
      D + px.length ≤ ctx.K →
      ∃ o0 ∈ S, ∀ t, E t → AllocLive t o0 →
        readPath t.heap (gamma o0) (px.map canon) = some (gamma o)
  | [], S, o, ho, _, _, _ => ⟨o, ho, fun _ _ _ => rfl⟩
  | c :: cs, S, o, ho, hcs, hS, hD => by
    simp only [List.length_cons] at hS hD
    have hc : c ∈ ctx.cells := hcs c List.mem_cons_self
    have hS' : ∀ o1 ∈ aread Y S c, o1 ∈ ctx.origins ∧ dep ctx.K o1 + cs.length ≤ ctx.K := by
      intro o1 h1
      obtain ⟨o0, h0, h01⟩ := mem_aread.mp h1
      obtain ⟨hin, hd⟩ := hS o0 h0
      refine ⟨h.supp.heap o0 hin c hc o1 h01, ?_⟩
      have := h.depH o0 c o1 h01
      omega
    obtain ⟨o1, h1, hr⟩ := walkB h cs (aread Y S c) o ho
      (fun c' h' => hcs c' (List.mem_cons_of_mem _ h')) hS' (by omega)
    obtain ⟨o0, h0, h01⟩ := mem_aread.mp h1
    obtain ⟨hin, hd⟩ := hS o0 h0
    refine ⟨o0, h0, fun t ht hl => ?_⟩
    have he := h.hr o0 hin c hc o1 h01 (by omega) t ht hl
    have hl1 : AllocLive t o1 := by
      intro a e; subst e
      exact (h.states t ht).2.2.heap _ _ a 0 he
    simp only [List.map_cons, readPath, he, Option.bind_some]
    exact hr t ht hl1

/-- The query cells are in the cell universe of the query context. -/
theorem query_cells_abs {cells : List Field} {px : List ACell} (qf : List Field)
    (h : afields px ⊆ qf) : ∀ c ∈ px, c ∈ cellsOf (cells ++ qf) := by
  intro c hc
  cases c with
  | elem => exact elem_mem_cellsOf _
  | fld f =>
    apply fld_mem_cellsOf
    apply List.mem_append.mpr (Or.inr (h _))
    simp only [afields, List.mem_filterMap]
    exact ⟨.fld f, hc, rfl⟩

/-- Completeness with stores: in the certified scope, each may-alias is a cross-execution
alias of the canonical concrete paths. -/
theorem ccomplete_store (K : Nat) :
    CCompleteIn K (fun fr p px py => storeScopeB K fr p px py = true) := by
  intro fr p x px y py hs hmay
  simp only [storeScopeB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Option.isSome_iff_exists] at hs
  obtain ⟨⟨⟨honce, hdx⟩, hdy⟩, k', hcert⟩ := hs
  let qf := afields px ++ afields py
  let ctx := progCtx K fr p qf
  have hc : CtxOK ctx := ctxE_ok true K fr p qf
  have h0 := binv_init hc (ctxE_frame true K fr p qf)
  have hb0 : ∀ t, t = CState.init fr → Budget ctx p t := by
    rintro t rfl; exact ctxE_budget true K fr p qf
  have h := realizeB hc p (ctxE_stmts true K fr p qf) (fun s hs => honce s hs) hcert hb0 h0
    (by simp only [ctx, progCtx, Ctx.ofProg]; omega)
  obtain ⟨o, hox, hoy⟩ := may_iff.mp hmay
  have hcx := query_cells_abs (cells := p.fields) qf (fun a ha => List.mem_append.mpr (Or.inl ha))
  have hcy := query_cells_abs (cells := p.fields) qf (fun a ha => List.mem_append.mpr (Or.inr ha))
  have hK : ctx.K = K := rfl
  have real_path : ∀ (z : Var) (pz : List ACell), (∀ c ∈ pz, c ∈ ctx.cells) →
      loadsP p + pz.length ≤ K → o ∈ aevalPath (analyze ctx p (ainit ctx.K fr)) z pz →
      ∃ u, Exec p (CState.init fr) u ∧ evalPath u z (pz.map canon) = some (gamma o) := by
    intro z pz hcz hdz hoz
    obtain ⟨o0, h0, hr⟩ := walkB h pz _ o hoz hcz (fun o0 h0 =>
      ⟨h.supp.env z o0 h0, by have := (h.real z o0 h0).1; omega⟩)
      (by omega)
    obtain ⟨_, u, ⟨_, rfl, hx⟩, he⟩ := h.real z o0 h0
    have hl : AllocLive u o0 := by
      intro a e; subst e
      exact (h.states u ⟨_, rfl, hx⟩).2.2.env z a 0 he
    refine ⟨u, hx, ?_⟩
    simp only [evalPath, he, Option.bind_some]
    exact hr u ⟨_, rfl, hx⟩ hl
  obtain ⟨u1, hx1, h1⟩ := real_path x px hcx hdx hox
  obtain ⟨u2, hx2, h2⟩ := real_path y py hcy hdy hoy
  exact ⟨px.map canon, py.map canon, canon_abs px, canon_abs py, u1, u2, gamma o, hx1, hx2, h1, h2⟩

end DirectedAlias.Sound

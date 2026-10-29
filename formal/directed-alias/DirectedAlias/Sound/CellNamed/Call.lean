import DirectedAlias.Sound.CellNamed.Inv

/-!
# Local soundness of the cell-named call

The call `m(args)` at site `s` writes, for each tag `k` that it uses, the new object
`sym (havoc s n k) []` into the cell `src k = (O, c)` of a narrow-reachable object `O`.
The proof gives this object the ghost name `childCN (alpha O) c` (`namesAfter`).

The three new facts of design CN:
1. A written object has the name of its cell, and the abstract call adds this name to the
   abstract cell, because the origin of `O` is covered (`reach_cover`).
2. The name of a written object is below an exposed origin, because the origin of `O`
   descends from an origin of the closure `R`, and `R` is exposed (`expOK_closure`).
3. A cell that the callee cannot reach keeps its value (`HavocN`), and a junk object (no call
   wrote it) is never reachable (`reach_facts`).
-/

namespace DirectedAlias.Sound.CellNamed

open DirectedAlias DirectedAlias.Sound DirectedAlias.Sound.Recency DirectedAlias.Sound.Havoc
open DirectedAlias.Sound.HavocRecency

variable {src : Nat → Obj × Cell} {cn : CtxN}

/-! ## The closure -/

/-- Membership in `succsN`. -/
theorem mem_succsN {X : AState} {R : List Origin} {v : Origin} :
    v ∈ succsN cn X R ↔ ∃ u ∈ cn.ctx.origins, coveredB R u = true ∧
      ∃ c ∈ cn.ctx.cells, v ∈ X.heap u c := by
  simp only [succsN, mem_uniMap, List.mem_filter]
  constructor
  · rintro ⟨u, ⟨hu, hc⟩, hv⟩; exact ⟨u, hu, hc, hv⟩
  · rintro ⟨u, hu, hc, hv⟩; exact ⟨u, ⟨hu, hc⟩, hv⟩

/-- A result of `closeN` contains the start set and is closed under `succsN`. -/
theorem closeN_spec {X : AState} :
    ∀ {n : Nat} {R0 R : List Origin}, closeN cn X n R0 = some R →
      (∀ o ∈ R0, o ∈ R) ∧ ∀ o ∈ succsN cn X R, o ∈ R
  | 0, R0, R, h => by simp [closeN] at h
  | n + 1, R0, R, h => by
    simp only [closeN] at h
    split at h
    · rename_i hs
      cases h
      exact ⟨fun _ h => h, subB_iff.mp hs⟩
    · obtain ⟨h1, h2⟩ := closeN_spec h
      exact ⟨fun o ho => h1 o (mem_uni.mpr (Or.inr ho)), h2⟩

/-! ## Narrow reach -/

/-- A narrow-reachable object is not dead, and its origin is not junk. -/
theorem reach_facts (hc : CtxNOK cn) {N : Names} {st : CState} {X : AState} {args : List Var}
    (hg : InvG cn.ctx (alphaCN cn.ctx.K N) st X) (hx : InvX cn N st X) {o : Obj}
    (hr : ReachN st cn.statics args o) :
    ¬ Dead cn.ctx.once o ∧ isJunk (alphaCN cn.ctx.K N st.cnt o) = false := by
  induction hr with
  | arg _ he => exact ⟨(hg.envOk _ _ he).1, notJunk_of_mem hc (hg.envOk _ _ he).2⟩
  | static _ =>
    refine ⟨by simp [Dead], ?_⟩
    rw [alphaCN_root]; rfl
  | @step o1 o2 c _ hh ih =>
    refine ⟨hg.heapLive _ _ _ ih.1 hh, ?_⟩
    rcases hx.outside _ _ _ ih.1 hh with ⟨hcell, hin⟩ | e
    · exact notJunk_of_mem hc (hg.heapIn _ _ _ ih.1 hin hcell hh)
    · rw [e, isJunk_childCN]; exact ih.2

/-- COVERAGE: the origin of each narrow-reachable object is covered by each closed set that
contains the start set of the call. -/
theorem reach_cover (hc : CtxNOK cn) {N : Names} {st : CState} {X : AState} {args : List Var}
    (hg : InvG cn.ctx (alphaCN cn.ctx.K N) st X) (hx : InvX cn N st X)
    (hargs : ∀ a ∈ args, a ∈ cn.ctx.vars) {R : List Origin}
    (h0 : ∀ a ∈ callRoots cn X args, a ∈ R) (hcl : ∀ v ∈ succsN cn X R, v ∈ R) {o : Obj}
    (hr : ReachN st cn.statics args o) : coveredB R (alphaCN cn.ctx.K N st.cnt o) = true := by
  induction hr with
  | arg hxa he =>
    exact coveredB_iff.mpr ⟨_, h0 _ (mem_uni.mpr (Or.inl
      (mem_uniMap.mpr ⟨_, hxa, hg.env _ (hargs _ hxa) _ he⟩))), descB_refl _⟩
  | static hr =>
    rw [alphaCN_root]
    exact coveredB_iff.mpr ⟨_, h0 _ (mem_uni.mpr (Or.inr (List.mem_map.mpr ⟨_, hr, rfl⟩))),
      descB_refl _⟩
  | @step o1 o2 c hr1 hh ih =>
    have hd := (reach_facts hc hg hx hr1).1
    rcases hx.outside _ _ _ hd hh with ⟨hcell, hin⟩ | e
    · exact coveredB_iff.mpr ⟨_, hcl _ (mem_succsN.mpr
        ⟨_, hin, ih, _, hcell, hg.heap _ _ _ hd hin hcell hh⟩), descB_refl _⟩
    · rw [e]
      obtain ⟨a, ha, hd'⟩ := coveredB_iff.mp ih
      exact coveredB_iff.mpr ⟨a, ha, descB_child _ _ hd'⟩

/-- EXPOSURE: the name of each cell of a narrow-reachable object is below an origin of each
closed set that contains the start set. -/
theorem expOK_closure (hc : CtxNOK cn) {N : Names} {st : CState} {X : AState}
    {args : List Var} (hg : InvG cn.ctx (alphaCN cn.ctx.K N) st X) (hx : InvX cn N st X)
    (hargs : ∀ a ∈ args, a ∈ cn.ctx.vars) {R : List Origin}
    (h0 : ∀ a ∈ callRoots cn X args, a ∈ R) (hcl : ∀ v ∈ succsN cn X R, v ∈ R) {o : Obj}
    (hr : ReachN st cn.statics args o) (c : ACell) (E : List Origin) :
    ExpOK cn.ctx (uni R E) (childCN cn.ctx.K (alphaCN cn.ctx.K N st.cnt o) c) := by
  intro _ b q e
  obtain ⟨q0, e0, rfl⟩ := childCN_sym_inv e
  have hcov := reach_cover hc hg hx hargs h0 hcl hr
  rw [e0] at hcov
  obtain ⟨a, ha, hd⟩ := coveredB_iff.mp hcov
  obtain ⟨p, rfl, hp⟩ := descB_sym_inv hd
  refine expB_of (mem_uni.mpr (Or.inl ha)) ?_ (preB_append hp _)
  have := preB_len hp
  rw [List.length_append]; simp only [List.length_cons, List.length_nil]; omega

/-- Each object is dead or not dead (a constructive case split). -/
theorem dead_or_not (once : Site → Bool) : ∀ o : Obj, Dead once o ∨ ¬ Dead once o
  | .sym (.root _) _ => Or.inr id
  | .sym (.havoc _ _ _) _ => Or.inr id
  | .sym (.fresh s n) _ => Decidable.em (once s = true ∧ 1 ≤ n)
  | .alloc s n => Decidable.em (once s = true ∧ 1 ≤ n)

/-! ## The ghost naming after a call -/

/-- The ghost naming after the `n`-th execution of call site `s` with the new heap `h'`: each
tag `k` that the call wrote into its cell `src k = (O, c)` gets the name
`childCN (alpha O) c`. -/
def namesAfter (K : Nat) (N : Names) (src : Nat → Obj × Cell) (cnt : Site → Nat) (h' : Heap)
    (s n : Nat) : Names :=
  fun s' n' k =>
    if s' = s ∧ n' = n ∧ h' (src k).1 (src k).2 = some (.sym (.havoc s n k) []) then
      some (childCN K (alphaCN K N cnt (src k).1) (src k).2.abs)
    else N s' n' k

/-- A name after the call is a new name of the call or an old name. -/
theorem namesAfter_cases {K : Nat} {N : Names} {cnt : Site → Nat} {h' : Heap} {s n : Nat}
    {s' n' k : Nat} {a : Origin} (h : namesAfter K N src cnt h' s n s' n' k = some a) :
    (s' = s ∧ n' = n ∧ h' (src k).1 (src k).2 = some (.sym (.havoc s n k) []) ∧
      a = childCN K (alphaCN K N cnt (src k).1) (src k).2.abs) ∨ N s' n' k = some a := by
  unfold namesAfter at h
  split at h
  · rename_i hc
    cases h
    exact Or.inl ⟨hc.1, hc.2.1, hc.2.2, rfl⟩
  · exact Or.inr h

/-- An old name stays. -/
theorem namesAfter_old {K : Nat} {N : Names} {cnt : Site → Nat} {h' : Heap} {s : Nat}
    (hcnt : CntOK N cnt) {s' n' k : Nat} {a : Origin} (h : N s' n' k = some a) :
    namesAfter K N src cnt h' s (cnt s) s' n' k = some a := by
  unfold namesAfter
  split
  · rename_i hc
    obtain ⟨rfl, rfl, _⟩ := hc
    have := hcnt _ _ _ _ h
    omega
  · exact h

/-- A written object has the name of its cell. -/
theorem namesAfter_new {K : Nat} {N : Names} {cnt : Site → Nat} {h' : Heap} {s n k : Nat}
    (hw : h' (src k).1 (src k).2 = some (.sym (.havoc s n k) [])) :
    namesAfter K N src cnt h' s n s n k =
      some (childCN K (alphaCN K N cnt (src k).1) (src k).2.abs) := by
  unfold namesAfter
  rw [ite_eq_left ⟨rfl, rfl, hw⟩]

/-- The abstraction of an object with an origin that is not junk does not change. -/
theorem alphaCN_after {K : Nat} {N : Names} {cnt : Site → Nat} {h' : Heap} {s : Nat}
    (hcnt : CntOK N cnt) {o : Obj} (hj : isJunk (alphaCN K N cnt o) = false) :
    alphaCN K (namesAfter K N src cnt h' s (cnt s)) cnt o = alphaCN K N cnt o := by
  cases o with
  | alloc a m => rfl
  | sym b p =>
    cases b with
    | root r => rfl
    | fresh a m => rfl
    | havoc a m k =>
      cases eN : N a m k with
      | none => rw [alphaCN_havoc_none K cnt eN] at hj; cases hj
      | some x =>
        rw [alphaCN_havoc_some K cnt eN, alphaCN_havoc_some K cnt (namesAfter_old hcnt eN)]

/-- An object that is junk after the call was junk before the call. -/
theorem junk_before {K : Nat} {N : Names} {cnt : Site → Nat} {h' : Heap} {s : Nat}
    (hcnt : CntOK N cnt) {o : Obj}
    (hj : isJunk (alphaCN K (namesAfter K N src cnt h' s (cnt s)) cnt o) = true) :
    isJunk (alphaCN K N cnt o) = true := by
  cases e : isJunk (alphaCN K N cnt o) with
  | true => rfl
  | false => rw [alphaCN_after hcnt e, e] at hj; exact hj

/-- The names below a covered origin are covered, if coverage is closed under cell names. -/
theorem cov_extend {K : Nat} {cov : Origin → Bool}
    (hcovc : ∀ u c, cov u = true → cov (childCN K u c) = true) :
    ∀ {u : Origin} (q : List ACell), cov u = true → cov (extendCN K u q) = true
  | _, [], h => h
  | _, d :: ds, h => cov_extend hcovc ds (hcovc _ d h)

/-! ## The call -/

section call

variable (hc : CtxNOK cn) {N : Names} {st : CState} {X : AState} {args : List Var} {s : Site}
  {h' : Heap} (hg : InvG cn.ctx (alphaCN cn.ctx.K N) st X) (hx : InvX cn N st X)
  (hcnt : CntOK N st.cnt) (hh : HavocN src cn.statics st args s (st.cnt s) h')
  {E : List Origin} {cov : Origin → Bool}
  (hcov : ∀ o, ReachN st cn.statics args o → cov (alphaCN cn.ctx.K N st.cnt o) = true)
  (hcovc : ∀ u c, cov u = true → cov (childCN cn.ctx.K u c) = true)

include hc hg hx hcnt hh

/-- A written object was written into a cell of a narrow-reachable object. -/
theorem written_reach {k : Nat}
    (hw : h' (src k).1 (src k).2 = some (.sym (.havoc s (st.cnt s) k) [])) :
    ReachN st cn.statics args (src k).1 := by
  rcases hh (src k).1 (src k).2 with e | ⟨hr, _, _, _⟩
  · exfalso
    rw [e] at hw
    have hN : N s (st.cnt s) k = none := by
      cases eN : N s (st.cnt s) k with
      | none => rfl
      | some a => have := hcnt _ _ _ _ eN; omega
    have hnd : ∀ o c, cdefault o c ≠ some (.sym (.havoc s (st.cnt s) k) []) := by
      intro o c e
      cases o with
      | alloc _ _ => cases e
      | sym b p =>
        simp only [cdefault, Option.some.injEq, Obj.sym.injEq] at e
        cases p <;> simp at e
    rcases dead_or_not cn.ctx.once (src k).1 with hd | hd
    · rw [hx.deadDflt _ _ hd] at hw; exact hnd _ _ hw
    · cases hj : isJunk (alphaCN cn.ctx.K N st.cnt (src k).1) with
      | true => rw [hx.junkDflt _ _ hj] at hw; exact hnd _ _ hw
      | false =>
        rcases hx.outside _ _ _ hd hw with ⟨hcell, hin⟩ | e2
        · have := hg.heapIn _ _ _ hd hin hcell hw
          rw [alphaCN_havoc_none _ _ hN] at this
          exact hc.noJunk _ this
        · rw [alphaCN_havoc_none _ _ hN] at e2
          have := congrArg isJunk e2
          rw [isJunk_childCN, hj] at this
          cases this
  · exact hr

omit hcnt in
/-- A junk object keeps its default cells through the call. -/
theorem junk_kept {o : Obj} (hj : isJunk (alphaCN cn.ctx.K N st.cnt o) = true) (c : Cell) :
    h' o c = cdefault o c := by
  rcases hh o c with e | ⟨hr, _⟩
  · rw [e]; exact hx.junkDflt o c hj
  · have := (reach_facts hc hg hx hr).2; rw [hj] at this; cases this

include hcov hcovc in
/-- An object that was junk and has a universe name after the call is below a written object,
and its name is covered. -/
theorem cov_new {o : Obj} (hj : isJunk (alphaCN cn.ctx.K N st.cnt o) = true)
    (hj' : isJunk (alphaCN cn.ctx.K (namesAfter cn.ctx.K N src st.cnt h' s (st.cnt s))
      st.cnt o) = false) :
    cov (alphaCN cn.ctx.K (namesAfter cn.ctx.K N src st.cnt h' s (st.cnt s)) st.cnt o) = true := by
  have hN : ∀ s n k a, N s n k = some a → isName a = true :=
    fun s n k a e => (hx.names s n k a e).name
  cases o with
  | alloc a m =>
    exfalso; revert hj
    show isJunk (if m + 1 = st.cnt a then rNew a else rOld a) = true → False
    split <;> intro h <;> cases h
  | sym b p =>
    cases b with
    | root r => exfalso; simp only [alphaCN, alpha, symOrDeep] at hj; split at hj <;> cases hj
    | fresh a m => exfalso; simp only [alphaCN, alpha, symOrDeep] at hj; split at hj <;> cases hj
    | havoc a m k =>
      cases eN' : namesAfter cn.ctx.K N src st.cnt h' s (st.cnt s) a m k with
      | none => rw [alphaCN_havoc_none _ _ eN'] at hj'; cases hj'
      | some x =>
        rw [alphaCN_havoc_some _ _ eN']
        rcases namesAfter_cases eN' with ⟨rfl, rfl, hw, rfl⟩ | eN
        · exact cov_extend hcovc _ (hcovc _ _ (hcov _ (written_reach hc hg hx hcnt hh hw)))
        · rw [alphaCN_havoc_some _ _ eN] at hj
          rw [isName_notJunk (extendCN_name _ _ (hN _ _ _ _ eN))] at hj
          cases hj

include hcov hcovc in
/-- LOCAL SOUNDNESS OF THE CALL (generic part): the cell-named havoc with a coverage test
that covers each narrow-reachable origin keeps the generic invariant for the new names. -/
theorem InvG.havocCN :
    InvG cn.ctx (alphaCN cn.ctx.K (namesAfter cn.ctx.K N src st.cnt h' s (st.cnt s)))
      { st with heap := h' } (havocWith cn X E cov) := by
  have ag := fun {o : Obj} (hj : isJunk (alphaCN cn.ctx.K N st.cnt o) = false) =>
    alphaCN_after (src := src) (K := cn.ctx.K) (h' := h') (s := s) hcnt hj
  have agU := fun {o : Obj} (hin : alphaCN cn.ctx.K N st.cnt o ∈ cn.ctx.origins) =>
    ag (notJunk_of_mem hc hin)
  have hsub : ∀ x, ∀ a ∈ X.env x, a ∈ (havocWith cn X E cov).env x := by
    intro x a ha
    show a ∈ fupd X.env cn.xe (uni E (X.env cn.xe)) x
    by_cases e : x = cn.xe
    · subst e; rw [fupd_same]; exact mem_uni.mpr (Or.inr ha)
    · rw [fupd_ne _ _ e]; exact ha
  have hcell : ∀ u c a, a ∈ X.heap u c → a ∈ (havocWith cn X E cov).heap u c := by
    intro u c a ha
    show a ∈ (if c ∈ cn.ctx.cells ∧ cov u = true then uni [childCN cn.ctx.K u c] (X.heap u c)
      else X.heap u c)
    split
    · exact mem_uni.mpr (Or.inr ha)
    · exact ha
  have hnew : ∀ u c, c ∈ cn.ctx.cells → cov u = true →
      childCN cn.ctx.K u c ∈ (havocWith cn X E cov).heap u c := by
    intro u c hc1 hcu
    show _ ∈ (if c ∈ cn.ctx.cells ∧ cov u = true then uni [childCN cn.ctx.K u c] (X.heap u c)
      else X.heap u c)
    rw [ite_eq_left ⟨hc1, hcu⟩]
    exact mem_uni.mpr (Or.inl (List.mem_singleton.mpr rfl))
  have hwr : ∀ o c k, ReachN st cn.statics args o → src k = (o, c) →
      h' o c = some (.sym (.havoc s (st.cnt s) k) []) →
      alphaCN cn.ctx.K (namesAfter cn.ctx.K N src st.cnt h' s (st.cnt s)) st.cnt
        (.sym (.havoc s (st.cnt s) k) []) =
        childCN cn.ctx.K (alphaCN cn.ctx.K N st.cnt o) c.abs := by
    intro o c k _ hk e
    have hw : h' (src k).1 (src k).2 = some (.sym (.havoc s (st.cnt s) k) []) := by rw [hk]; exact e
    rw [alphaCN_havoc_some _ _ (namesAfter_new hw), hk]
    rfl
  exact {
    outside := hg.outside
    envOk := fun x o he => ⟨(hg.envOk x o he).1, by rw [agU (hg.envOk x o he).2]; exact (hg.envOk x o he).2⟩
    heapLive := fun o c o' hd he => by
      rcases hh o c with e | ⟨_, k, _, e⟩
      · exact hg.heapLive o c o' hd (e ▸ he)
      · change h' o c = some o' at he
        rw [e] at he; cases he; simp [Dead]
    heapIn := fun o c o' hd hin hc1 he => by
      change h' o c = some o' at he
      rcases hh o c with e | ⟨hr, k, hk, e⟩
      · rw [e] at he
        cases hj : isJunk (alphaCN cn.ctx.K N st.cnt o) with
        | false =>
          rw [ag hj] at hin
          have := hg.heapIn o c o' hd hin hc1 he
          rw [agU this]; exact this
        | true =>
          rw [hx.junkDflt o c hj] at he
          rw [alphaCN_cdefault _ _ _ he]
          exact hc.childIn _ hin _ hc1
      · rw [e] at he; cases he
        have hj := (reach_facts hc hg hx hr).2
        rw [hwr o c k hr hk e]
        rw [ag hj] at hin
        exact hc.childIn _ hin _ hc1
    allocHeld := fun o c a m he => by
      change h' o c = some (.alloc a m) at he
      rcases hh o c with e | ⟨_, k, _, e⟩
      · rw [e] at he
        obtain ⟨h1, h2, h3⟩ := hg.allocHeld o c a m he
        exact ⟨h1, by rw [agU h2]; exact h2, h3⟩
      · rw [e] at he; cases he
    envCr := hg.envCr
    heapCr := fun o c a m he => by
      change h' o c = some (.alloc a m) at he
      rcases hh o c with e | ⟨_, k, _, e⟩
      · exact hg.heapCr o c a m (e ▸ he)
      · rw [e] at he; cases he
    fresh := fun a m c hm => by
      show h' (.alloc a m) c = none
      rcases hh (.alloc a m) c with e | ⟨hr, _, _⟩
      · rw [e]; exact hg.fresh a m c hm
      · have := hg.reach_cr hr.toReach a m rfl
        change st.cnt a ≤ m at hm
        omega
    env := fun x hx1 o he => by
      rw [agU (hg.envOk x o he).2]
      exact hsub x _ (hg.env x hx1 o he)
    heap := fun o c o' hd hin hc1 he => by
      change h' o c = some o' at he
      rcases hh o c with e | ⟨hr, k, hk, e⟩
      · rw [e] at he
        cases hj : isJunk (alphaCN cn.ctx.K N st.cnt o) with
        | false =>
          rw [ag hj] at hin ⊢
          have h1 := hg.heap o c o' hd hin hc1 he
          rw [agU (hg.heapIn o c o' hd hin hc1 he)]
          exact hcell _ _ _ h1
        | true =>
          rw [hx.junkDflt o c hj] at he
          rw [alphaCN_cdefault _ _ _ he]
          exact hnew _ _ hc1 (cov_new hc hg hx hcnt hh hcov hcovc hj
            (notJunk_of_mem hc hin))
      · rw [e] at he; cases he
        have hj := (reach_facts hc hg hx hr).2
        rw [hwr o c k hr hk e, ag hj]
        exact hnew _ _ hc1 (hcov o hr) }

/-- LOCAL SOUNDNESS OF THE CALL (extra part): the cell-named havoc keeps the extra facts for
the new names, if the name of each cell of each narrow-reachable object is below the new
exposed set. -/
theorem InvX.havocCN
    (hexp : ∀ o c, ReachN st cn.statics args o →
      ExpOK cn.ctx (uni E (X.env cn.xe)) (childCN cn.ctx.K (alphaCN cn.ctx.K N st.cnt o) c)) :
    InvX cn (namesAfter cn.ctx.K N src st.cnt h' s (st.cnt s)) { st with heap := h' }
      (havocWith cn X E cov) := by
  have ag := fun {o : Obj} (hj : isJunk (alphaCN cn.ctx.K N st.cnt o) = false) =>
    alphaCN_after (src := src) (K := cn.ctx.K) (h' := h') (s := s) hcnt hj
  exact {
    junkDflt := fun o c hj => junk_kept hc hg hx hh (junk_before hcnt hj) c
    deadDflt := fun o c hd => by
      show h' o c = cdefault o c
      rcases hh o c with e | ⟨hr, _⟩
      · rw [e]; exact hx.deadDflt o c hd
      · exact absurd hd (reach_facts hc hg hx hr).1
    outside := fun o c o' hd he => by
      change h' o c = some o' at he
      rcases hh o c with e | ⟨hr, k, hk, e⟩
      · rw [e] at he
        cases hj : isJunk (alphaCN cn.ctx.K N st.cnt o) with
        | false =>
          rw [ag hj]
          rcases hx.outside o c o' hd he with h1 | h1
          · exact Or.inl h1
          · right
            have hj' : isJunk (alphaCN cn.ctx.K N st.cnt o') = false := by
              rw [h1, isJunk_childCN]; exact hj
            rw [ag hj']; exact h1
        | true =>
          rw [hx.junkDflt o c hj] at he
          exact Or.inr (alphaCN_cdefault _ _ _ he)
      · rw [e] at he; cases he
        right
        have hj := (reach_facts hc hg hx hr).2
        have hw : h' (src k).1 (src k).2 = some (.sym (.havoc s (st.cnt s) k) []) := by
          rw [hk]; exact e
        rw [alphaCN_havoc_some _ _ (namesAfter_new hw), hk, ag hj]
        rfl
    names := fun s' n' k a e => by
      have hE : ∀ x ∈ X.env cn.xe, x ∈ (havocWith cn X E cov).env cn.xe := by
        intro x hm
        show x ∈ fupd X.env cn.xe (uni E (X.env cn.xe)) cn.xe
        rw [fupd_same]; exact mem_uni.mpr (Or.inr hm)
      rcases namesAfter_cases e with ⟨rfl, rfl, hw, rfl⟩ | eN
      · have hr := written_reach hc hg hx hcnt hh hw
        refine ⟨childCN_name _ _ (reach_facts hc hg hx hr).2, childCN_ne_root _ _ _, ?_⟩
        have := hexp _ (src k).2.abs hr
        show ExpOK cn.ctx (fupd X.env cn.xe (uni E (X.env cn.xe)) cn.xe) _
        rw [fupd_same]; exact this
      · exact (hx.names s' n' k a eN).mono hE }

end call

/-- The new names of a call are names of that call. -/
theorem cnt_after {K : Nat} {N : Names} {cnt : Site → Nat} {h' : Heap} {s : Nat}
    (hcnt : CntOK N cnt) : CntOK (namesAfter K N src cnt h' s (cnt s)) (fupd cnt s (cnt s + 1)) := by
  intro s' n' k a e
  rcases namesAfter_cases e with ⟨rfl, rfl, _, _⟩ | eN
  · rw [fupd_same]; exact Nat.lt_succ_self _
  · have := hcnt _ _ _ _ eN
    by_cases e2 : s' = s
    · subst e2; rw [fupd_same]; omega
    · rw [fupd_ne _ _ e2]; exact this

/-- LOCAL SOUNDNESS OF THE CELL-NAMED CALL: the abstract call `havocCN` keeps the generic
invariant and the extra facts for the new names, for each strict narrow havoc. -/
theorem havocCN_sound (hc : CtxNOK cn) {N : Names} {st : CState} {X : AState}
    {args : List Var} {s : Site} {h' : Heap}
    (hg : InvG cn.ctx (alphaCN cn.ctx.K N) st X) (hx : InvX cn N st X)
    (hcnt : CntOK N st.cnt) (hargs : ∀ a ∈ args, a ∈ cn.ctx.vars)
    (hh : HavocN src cn.statics st args s (st.cnt s) h') :
    InvG cn.ctx (alphaCN cn.ctx.K (namesAfter cn.ctx.K N src st.cnt h' s (st.cnt s)))
      { st with heap := h' } (havocCN cn X args) ∧
    InvX cn (namesAfter cn.ctx.K N src st.cnt h' s (st.cnt s)) { st with heap := h' }
      (havocCN cn X args) := by
  unfold havocCN
  split
  · rename_i R hR
    obtain ⟨h0, hcl⟩ := closeN_spec hR
    have hcov := fun o (hr : ReachN st cn.statics args o) => reach_cover hc hg hx hargs h0 hcl hr
    have hcovc : ∀ u c, coveredB R u = true → coveredB R (childCN cn.ctx.K u c) = true := by
      intro u c h
      obtain ⟨a, ha, hd⟩ := coveredB_iff.mp h
      exact coveredB_iff.mpr ⟨a, ha, descB_child _ _ hd⟩
    exact ⟨InvG.havocCN hc hg hx hcnt hh hcov hcovc,
      InvX.havocCN hc hg hx hcnt hh (fun o c hr => expOK_closure hc hg hx hargs h0 hcl hr c _)⟩
  · exact ⟨InvG.havocCN hc hg hx hcnt hh (fun _ _ => rfl) (fun _ _ _ => rfl),
      InvX.havocCN hc hg hx hcnt hh (fun o c _ => ExpOK_univ hc
        (fun _ hm => mem_uni.mpr (Or.inl hm)) (childCN_ne_root _ _ c))⟩

end DirectedAlias.Sound.CellNamed

import DirectedAlias.Sound.BlockOnly.Inv

/-!
# Local soundness of the call of design BO

The call `m(args)` at site `s` writes, for each tag `k` that it uses, the new object
`sym (havoc s n k) []` into the cell `src k = (O, c)` of a narrow-reachable object `O`.
The abstract call changes only the two sets and the covered empty cells (`callWith`).

The proof gives the new object the ghost data `⟨X', alpha O, c, cnt⟩` (`ghostsAfter`), where
`X'` is the abstract state after the call. Its name is `stepB X' (alpha O) c`: the first origin
of the abstract content of the cell after the call. The three facts of the call:
1. NAMING: the name of a written object is in the abstract content of its cell, because the
   origin of `O` is covered (`reach_coverB`), and a covered universe cell is not empty after
   the call (`callWith_heap_ne`). An object below a written object has a name in the content
   of the cell of its parent name, because all chain names are covered (`cov_chainB`).
2. NO UNIQUE NAME: a chain name is a content of a covered cell before the call (so it is in
   `Eval`), or a cell name of a covered origin (so it is below `Etree`, or never unique)
   (`blocked_stepB`).
3. A cell that the callee cannot reach keeps its value (`HavocN`), and a junk object is never
   reachable (`reach_factsB`).
-/

namespace DirectedAlias.Sound.BlockOnly

open DirectedAlias DirectedAlias.Sound DirectedAlias.Sound.Recency DirectedAlias.Sound.Havoc
open DirectedAlias.Sound.HavocRecency DirectedAlias.Sound.CellNamed DirectedAlias.Opt

variable {src : Nat → Obj × Cell} {cb : CtxB}

/-! ## Narrow reach -/

/-- A narrow-reachable object is not dead, and its origin is not junk. -/
theorem reach_factsB (hc : CtxBOK cb) {G : GNames} {st : CState} {X : AState} {args : List Var}
    (hg : InvG cb.cn.ctx (alphaBO cb G) st X) (hx : InvXB cb G st X) {o : Obj}
    (hr : ReachN st cb.cn.statics args o) :
    ¬ Dead cb.cn.ctx.once o ∧ isJunk (alphaBO cb G st.cnt o) = false := by
  induction hr with
  | arg _ he => exact ⟨(hg.envOk _ _ he).1, notJunk_of_mem hc.cn (hg.envOk _ _ he).2⟩
  | static _ =>
    refine ⟨by simp [Dead], ?_⟩
    rw [alphaBO_root]; rfl
  | @step o1 o2 c _ hh ih =>
    refine ⟨hg.heapLive _ _ _ ih.1 hh, ?_⟩
    rcases hx.outside _ _ _ ih.1 hh with ⟨hcell, hin⟩ | e
    · exact notJunk_of_mem hc.cn (hg.heapIn _ _ _ ih.1 hin hcell hh)
    · rw [e, isJunk_childCN]; exact ih.2

/-- COVERAGE: the origin of each narrow-reachable object is covered by each closed set that
contains the start set of the call. -/
theorem reach_coverB (hc : CtxBOK cb) {G : GNames} {st : CState} {X : AState} {args : List Var}
    (hg : InvG cb.cn.ctx (alphaBO cb G) st X) (hx : InvXB cb G st X)
    (hargs : ∀ a ∈ args, a ∈ cb.cn.ctx.vars) {R : List Origin}
    (h0 : ∀ a ∈ callRoots cb.cn X args, a ∈ R) (hcl : ∀ v ∈ succsN cb.cn X R, v ∈ R) {o : Obj}
    (hr : ReachN st cb.cn.statics args o) : coveredB R (alphaBO cb G st.cnt o) = true := by
  induction hr with
  | arg hxa he =>
    exact coveredB_iff.mpr ⟨_, h0 _ (mem_uni.mpr (Or.inl
      (mem_uniMap.mpr ⟨_, hxa, hg.env _ (hargs _ hxa) _ he⟩))), descB_refl _⟩
  | static hr =>
    rw [alphaBO_root]
    exact coveredB_iff.mpr ⟨_, h0 _ (mem_uni.mpr (Or.inr (List.mem_map.mpr ⟨_, hr, rfl⟩))),
      descB_refl _⟩
  | @step o1 o2 c hr1 hh ih =>
    have hd := (reach_factsB hc hg hx hr1).1
    rcases hx.outside _ _ _ hd hh with ⟨hcell, hin⟩ | e
    · exact coveredB_iff.mpr ⟨_, hcl _ (mem_succsN.mpr
        ⟨_, hin, ih, _, hcell, hg.heap _ _ _ hd hin hcell hh⟩), descB_refl _⟩
    · rw [e]
      obtain ⟨a, ha, hd'⟩ := coveredB_iff.mp ih
      exact coveredB_iff.mpr ⟨a, ha, descB_child _ _ hd'⟩

/-! ## The abstract state after the call -/

section callState

variable (hc : CtxBOK cb) {X : AState} {E V : List Origin} {cov : Origin → Bool}

include hc in
/-- After the call, `Etree` is the old set with `E`. -/
theorem callWith_xe : (callWith cb X E V cov).env cb.cn.xe = uni E (X.env cb.cn.xe) := by
  show fupd (fupd X.env cb.cn.xe (uni E (X.env cb.cn.xe))) cb.xv (uni V (X.env cb.xv)) cb.cn.xe = _
  rw [fupd_ne _ _ (Ne.symm hc.xvNe), fupd_same]

omit hc in
/-- After the call, `Eval` is the old set with `V`. -/
theorem callWith_xv : (callWith cb X E V cov).env cb.xv = uni V (X.env cb.xv) := by
  show fupd (fupd X.env cb.cn.xe (uni E (X.env cb.cn.xe))) cb.xv (uni V (X.env cb.xv)) cb.xv = _
  rw [fupd_same]

include hc in
/-- The call keeps each origin of each variable. -/
theorem callWith_env_sub (x : Var) {a : Origin} (h : a ∈ X.env x) :
    a ∈ (callWith cb X E V cov).env x := by
  by_cases e1 : x = cb.xv
  · subst e1; rw [callWith_xv]; exact mem_uni.mpr (Or.inr h)
  · by_cases e2 : x = cb.cn.xe
    · subst e2; rw [callWith_xe hc]; exact mem_uni.mpr (Or.inr h)
    · show a ∈ fupd (fupd X.env cb.cn.xe _) cb.xv _ x
      rw [fupd_ne _ _ e1, fupd_ne _ _ e2]; exact h

omit hc in
/-- The call changes no other variable. -/
theorem callWith_env_ne (x : Var) (h1 : x ≠ cb.cn.xe) (h2 : x ≠ cb.xv) :
    (callWith cb X E V cov).env x = X.env x := by
  show fupd (fupd X.env cb.cn.xe _) cb.xv _ x = _
  rw [fupd_ne _ _ h2, fupd_ne _ _ h1]

omit hc in
/-- The cells after the call: a covered empty universe cell has its cell name, every other cell
keeps its content. -/
theorem callWith_heap_cases (u : Origin) (c : ACell) :
    (c ∈ cb.cn.ctx.cells ∧ cov u = true ∧ X.heap u c = [] ∧
      (callWith cb X E V cov).heap u c = [childCN cb.cn.ctx.K u c]) ∨
    (¬ (c ∈ cb.cn.ctx.cells ∧ cov u = true ∧ X.heap u c = []) ∧
      (callWith cb X E V cov).heap u c = X.heap u c) := by
  show (_ ∧ _ ∧ _ ∧ (if c ∈ cb.cn.ctx.cells ∧ cov u = true ∧ (X.heap u c).isEmpty = true
      then [childCN cb.cn.ctx.K u c] else X.heap u c) = _) ∨
    (_ ∧ (if c ∈ cb.cn.ctx.cells ∧ cov u = true ∧ (X.heap u c).isEmpty = true
      then [childCN cb.cn.ctx.K u c] else X.heap u c) = _)
  by_cases h : c ∈ cb.cn.ctx.cells ∧ cov u = true ∧ X.heap u c = []
  · have h' : c ∈ cb.cn.ctx.cells ∧ cov u = true ∧ (X.heap u c).isEmpty = true :=
      ⟨h.1, h.2.1, by rw [h.2.2]; rfl⟩
    exact Or.inl ⟨h.1, h.2.1, h.2.2, ite_eq_left h'⟩
  · have h' : ¬ (c ∈ cb.cn.ctx.cells ∧ cov u = true ∧ (X.heap u c).isEmpty = true) := by
      rintro ⟨h1, h2, h3⟩
      exact h ⟨h1, h2, List.isEmpty_iff.mp h3⟩
    exact Or.inr ⟨h, ite_eq_right h'⟩

omit hc in
/-- The call keeps each origin of each cell. -/
theorem callWith_heap_sub (u : Origin) (c : ACell) {a : Origin} (h : a ∈ X.heap u c) :
    a ∈ (callWith cb X E V cov).heap u c := by
  rcases callWith_heap_cases (X := X) (E := E) (V := V) (cov := cov) u c with
    ⟨_, _, e, _⟩ | ⟨_, e⟩
  · rw [e] at h; cases h
  · rw [e]; exact h

omit hc in
/-- A covered universe cell is not empty after the call. -/
theorem callWith_heap_ne {u : Origin} {c : ACell} (hc1 : c ∈ cb.cn.ctx.cells)
    (hu : cov u = true) : (callWith cb X E V cov).heap u c ≠ [] := by
  rcases callWith_heap_cases (X := X) (E := E) (V := V) (cov := cov) u c with
    ⟨_, _, _, e⟩ | ⟨hn, e⟩
  · rw [e]; simp
  · rw [e]; intro h; exact hn ⟨hc1, hu, h⟩

include hc in
/-- The call keeps support if the two sets are in the universe. -/
theorem supp_callWith (hs : Supp cb.cn.ctx X) (hE : E ⊆ cb.cn.ctx.origins)
    (hV : V ⊆ cb.cn.ctx.origins) : Supp cb.cn.ctx (callWith cb X E V cov) := by
  intro k hk
  cases k with
  | v x =>
    show (callWith cb X E V cov).env x ⊆ _
    by_cases e1 : x = cb.xv
    · subst e1; rw [callWith_xv]; exact uni_sub hV (hs (.v _) hk)
    · by_cases e2 : x = cb.cn.xe
      · subst e2; rw [callWith_xe hc]; exact uni_sub hE (hs (.v _) hk)
      · rw [callWith_env_ne x e2 e1]; exact hs (.v x) hk
  | h o c =>
    show (callWith cb X E V cov).heap o c ⊆ _
    rcases callWith_heap_cases (X := X) (E := E) (V := V) (cov := cov) o c with
      ⟨_, _, _, e⟩ | ⟨_, e⟩
    · rw [e]; intro a ha
      rw [List.mem_singleton.mp ha]
      exact hc.cn.childIn o hk.1 c hk.2
    · rw [e]; exact hs (.h o c) hk

end callState

/-! ## The ghost naming after a call -/

/-- The ghost naming after the `n`-th execution of call site `s` with the new heap `h'` and the
abstract state `X'` after the call: each tag `k` that the call wrote into its cell
`src k = (O, c)` gets the ghost data `⟨X', alpha O, c, cnt⟩`. -/
def ghostsAfter (cb : CtxB) (G : GNames) (src : Nat → Obj × Cell) (cnt : Site → Nat) (h' : Heap)
    (X' : AState) (s n : Nat) : GNames :=
  fun s' n' k =>
    if s' = s ∧ n' = n ∧ h' (src k).1 (src k).2 = some (.sym (.havoc s n k) []) then
      some ⟨X', alphaBO cb G cnt (src k).1, (src k).2.abs, cnt⟩
    else G s' n' k

/-- A ghost after the call is a new ghost of the call or an old ghost. -/
theorem ghostsAfter_cases {G : GNames} {cnt : Site → Nat} {h' : Heap} {X' : AState} {s n : Nat}
    {s' n' k : Nat} {g : Ghost} (h : ghostsAfter cb G src cnt h' X' s n s' n' k = some g) :
    (s' = s ∧ n' = n ∧ h' (src k).1 (src k).2 = some (.sym (.havoc s n k) []) ∧
      g = ⟨X', alphaBO cb G cnt (src k).1, (src k).2.abs, cnt⟩) ∨ G s' n' k = some g := by
  unfold ghostsAfter at h
  split at h
  · rename_i hc
    cases h
    exact Or.inl ⟨hc.1, hc.2.1, hc.2.2, rfl⟩
  · exact Or.inr h

/-- An old ghost stays. -/
theorem ghostsAfter_old {G : GNames} {cnt : Site → Nat} {h' : Heap} {X' : AState} {s : Nat}
    (hcnt : CntOKB G cnt) {s' n' k : Nat} {g : Ghost} (h : G s' n' k = some g) :
    ghostsAfter cb G src cnt h' X' s (cnt s) s' n' k = some g := by
  unfold ghostsAfter
  split
  · rename_i hc
    obtain ⟨rfl, rfl, _⟩ := hc
    have := hcnt.1 _ _ _ _ h
    exact absurd this (Nat.lt_irrefl _)
  · exact h

/-- A written object gets the new ghost. -/
theorem ghostsAfter_new {G : GNames} {cnt : Site → Nat} {h' : Heap} {X' : AState} {s n k : Nat}
    (hw : h' (src k).1 (src k).2 = some (.sym (.havoc s n k) [])) :
    ghostsAfter cb G src cnt h' X' s n s n k =
      some ⟨X', alphaBO cb G cnt (src k).1, (src k).2.abs, cnt⟩ := by
  unfold ghostsAfter
  rw [ite_eq_left ⟨rfl, rfl, hw⟩]

/-- The abstraction of an object with an origin that is not junk does not change. -/
theorem alphaBO_after {G : GNames} {cnt : Site → Nat} {h' : Heap} {X' : AState} {s : Nat}
    (hcnt : CntOKB G cnt) {o : Obj} (hj : isJunk (alphaBO cb G cnt o) = false) :
    alphaBO cb (ghostsAfter cb G src cnt h' X' s (cnt s)) cnt o = alphaBO cb G cnt o := by
  cases o with
  | alloc a m => rfl
  | sym b p =>
    cases b with
    | root r => rfl
    | fresh a m => rfl
    | havoc a m k =>
      cases eN : G a m k with
      | none => rw [alphaBO_none cnt eN] at hj; cases hj
      | some x =>
        rw [alphaBO_some cnt eN, alphaBO_some cnt (ghostsAfter_old hcnt eN)]

/-- An object that is junk after the call was junk before the call. -/
theorem junk_beforeB {G : GNames} {cnt : Site → Nat} {h' : Heap} {X' : AState} {s : Nat}
    (hcnt : CntOKB G cnt) {o : Obj}
    (hj : isJunk (alphaBO cb (ghostsAfter cb G src cnt h' X' s (cnt s)) cnt o) = true) :
    isJunk (alphaBO cb G cnt o) = true := by
  cases e : isJunk (alphaBO cb G cnt o) with
  | true => rfl
  | false => rw [alphaBO_after hcnt e, e] at hj; exact hj

/-- An object that was junk and is not junk after the call is a callee object of this call
with the new ghost. -/
theorem junk_new {G : GNames} {cnt : Site → Nat} {h' : Heap} {X' : AState} {s : Nat}
    {o : Obj} (hj : isJunk (alphaBO cb G cnt o) = true)
    (hj' : isJunk (alphaBO cb (ghostsAfter cb G src cnt h' X' s (cnt s)) cnt o) = false) :
    ∃ k p, o = .sym (.havoc s (cnt s) k) p ∧
      h' (src k).1 (src k).2 = some (.sym (.havoc s (cnt s) k) []) ∧
      ghostsAfter cb G src cnt h' X' s (cnt s) s (cnt s) k =
        some ⟨X', alphaBO cb G cnt (src k).1, (src k).2.abs, cnt⟩ := by
  cases o with
  | alloc a m =>
    exfalso; revert hj
    show isJunk (if m + 1 = cnt a then rNew a else rOld a) = true → False
    split <;> intro h <;> cases h
  | sym b p =>
    cases b with
    | root r => exfalso; simp only [alphaBO, alpha, symOrDeep] at hj; split at hj <;> cases hj
    | fresh a m => exfalso; simp only [alphaBO, alpha, symOrDeep] at hj; split at hj <;> cases hj
    | havoc a m k =>
      cases eN' : ghostsAfter cb G src cnt h' X' s (cnt s) a m k with
      | none => rw [alphaBO_none _ eN'] at hj'; cases hj'
      | some x =>
        rcases ghostsAfter_cases eN' with ⟨rfl, rfl, hw, rfl⟩ | eN
        · exact ⟨k, p, rfl, hw, eN'⟩
        · exfalso
          rw [alphaBO_some cnt eN] at hj
          rw [alphaBO_some cnt eN'] at hj'
          rw [hj'] at hj; cases hj

/-! ## Names after the call -/

section names

variable {X : AState} {E V : List Origin} {cov : Origin → Bool}
  (hcovc : ∀ u c, cov u = true → cov (childCN cb.cn.ctx.K u c) = true)
  (hcovS : ∀ u ∈ cb.cn.ctx.origins, cov u = true → ∀ c ∈ cb.cn.ctx.cells, ∀ v ∈ X.heap u c,
    cov v = true)

include hcovc hcovS in
/-- A step from a covered origin in the state after the call is covered. -/
theorem cov_stepB {u : Origin} (hu : cov u = true) (c : ACell) :
    cov (stepB cb (callWith cb X E V cov) u c) = true := by
  rcases stepB_cases (cb := cb) (callWith cb X E V cov) u c with ⟨hu1, hc1, _, hm⟩ | e
  · rcases callWith_heap_cases (X := X) (E := E) (V := V) (cov := cov) u c with
      ⟨_, _, _, e⟩ | ⟨_, e⟩
    · rw [e, List.mem_singleton] at hm; rw [hm]; exact hcovc u c hu
    · rw [e] at hm; exact hcovS u hu1 hu c hc1 _ hm
  · rw [e]; exact hcovc u c hu

include hcovc hcovS in
/-- A chain from a covered origin in the state after the call is covered. -/
theorem cov_chainB : ∀ {u : Origin} (q : List ACell), cov u = true →
    cov (chainB cb (callWith cb X E V cov) u q) = true
  | _, [], h => h
  | _, d :: ds, h => cov_chainB ds (cov_stepB hcovc hcovS h d)

/-- A step from a covered universe origin in a universe cell is in the cell after the call. -/
theorem stepB_in_callWith {u : Origin} {c : ACell} (hu : u ∈ cb.cn.ctx.origins)
    (hc1 : c ∈ cb.cn.ctx.cells) (hcu : cov u = true) :
    stepB cb (callWith cb X E V cov) u c ∈ (callWith cb X E V cov).heap u c :=
  stepB_mem hu hc1 (callWith_heap_ne hc1 hcu)

/-- A recency-unique origin is a symbolic or an allocation origin. -/
theorem uniqueR_shape {once : Site → Bool} {eu : Bool} {a : Origin}
    (h : uniqueR once eu a = true) : (∃ b q, a = .sym b q) ∨ ∃ x, a = .alloc x := by
  cases a with
  | sym b q => exact Or.inl ⟨b, q, rfl⟩
  | alloc x => exact Or.inr ⟨x, rfl⟩
  | deep b => simp [uniqueR, Origin.uniqueB] at h
  | havoc _ => simp [uniqueR, Origin.uniqueB] at h
  | hsym _ _ _ _ => simp [uniqueR, Origin.uniqueB] at h
  | hdeep _ _ _ => simp [uniqueR, Origin.uniqueB] at h

/-- The cell name of a covered origin is not unique, if each symbolic cell name of a covered
origin is below `E`. -/
theorem blocked_childCN {E' V' : List Origin}
    (hE : ∀ u, cov u = true → ∀ c b q, childCN cb.cn.ctx.K u c = .sym b q →
      Origin.sym b q ∈ cb.cn.ctx.origins → expB E' (.sym b q) = true)
    {u : Origin} (hu : cov u = true) (c : ACell)
    (hin : childCN cb.cn.ctx.K u c ∈ cb.cn.ctx.origins) :
    uniqueBO cb.cn.ctx.once cb.cn.ctx.entryUnique E' V' (childCN cb.cn.ctx.K u c) = false := by
  cases h : uniqueR cb.cn.ctx.once cb.cn.ctx.entryUnique (childCN cb.cn.ctx.K u c) with
  | false => exact uniqueBO_false_iff.mpr (Or.inl h)
  | true =>
    rcases uniqueR_shape h with ⟨b, q, e⟩ | ⟨x, e⟩
    · rw [e] at hin ⊢
      exact uniqueBO_false_iff.mpr (Or.inr (Or.inl (hE u hu c b q e hin)))
    · exact absurd e (childCN_ne_alloc _ u c x)

/-- NO UNIQUE NAME: a step from a covered origin in the state after the call is not unique for
the new sets, if the contents of the covered universe cells are in `V` and the symbolic cell
names of the covered origins are below `E`. -/
theorem blocked_stepB {E0 V0 : List Origin}
    (hV : ∀ u ∈ cb.cn.ctx.origins, cov u = true → ∀ c ∈ cb.cn.ctx.cells, ∀ v ∈ X.heap u c, v ∈ V)
    (hE : ∀ u, cov u = true → ∀ c b q, childCN cb.cn.ctx.K u c = .sym b q →
      Origin.sym b q ∈ cb.cn.ctx.origins → expB E (.sym b q) = true)
    {u : Origin} (hu : cov u = true) (c : ACell)
    (hin : stepB cb (callWith cb X E V cov) u c ∈ cb.cn.ctx.origins) :
    uniqueBO cb.cn.ctx.once cb.cn.ctx.entryUnique (uni E E0) (uni V V0)
      (stepB cb (callWith cb X E V cov) u c) = false := by
  have hE' : ∀ u, cov u = true → ∀ c b q, childCN cb.cn.ctx.K u c = .sym b q →
      Origin.sym b q ∈ cb.cn.ctx.origins → expB (uni E E0) (.sym b q) = true :=
    fun u hu c b q e hin => expB_mono (fun a ha => mem_uni.mpr (Or.inl ha)) (hE u hu c b q e hin)
  rcases stepB_cases (cb := cb) (callWith cb X E V cov) u c with ⟨hu1, hc1, _, hm⟩ | e
  · rcases callWith_heap_cases (X := X) (E := E) (V := V) (cov := cov) u c with
      ⟨_, _, _, e⟩ | ⟨_, e⟩
    · rw [e, List.mem_singleton] at hm
      rw [hm] at hin ⊢
      exact blocked_childCN hE' hu c hin
    · rw [e] at hm
      exact uniqueBO_false_of_mem (mem_uni.mpr (Or.inl (hV u hu1 hu c hc1 _ hm)))
  · rw [e] at hin ⊢
    exact blocked_childCN hE' hu c hin

include hcovc hcovS in
/-- No chain name of a nonempty path from a covered origin is unique for the new sets. -/
theorem blocked_chainB {E0 V0 : List Origin}
    (hV : ∀ u ∈ cb.cn.ctx.origins, cov u = true → ∀ c ∈ cb.cn.ctx.cells, ∀ v ∈ X.heap u c, v ∈ V)
    (hE : ∀ u, cov u = true → ∀ c b q, childCN cb.cn.ctx.K u c = .sym b q →
      Origin.sym b q ∈ cb.cn.ctx.origins → expB E (.sym b q) = true) :
    ∀ {u : Origin} (c : ACell) (q : List ACell), cov u = true →
      chainB cb (callWith cb X E V cov) u (c :: q) ∈ cb.cn.ctx.origins →
      uniqueBO cb.cn.ctx.once cb.cn.ctx.entryUnique (uni E E0) (uni V V0)
        (chainB cb (callWith cb X E V cov) u (c :: q)) = false
  | _, c, [], hu, hin => blocked_stepB hV hE hu c hin
  | _, c, d :: ds, hu, hin =>
    blocked_chainB hV hE d ds (cov_stepB hcovc hcovS hu c) hin

end names

/-! ## The call -/

/-- Each object is dead or not dead (a constructive case split). -/
theorem dead_or_notB (once : Site → Bool) : ∀ o : Obj, Dead once o ∨ ¬ Dead once o :=
  dead_or_not once

section call

variable (hc : CtxBOK cb) {G : GNames} {st : CState} {X : AState} {args : List Var} {s : Site}
  {h' : Heap} (hg : InvG cb.cn.ctx (alphaBO cb G) st X) (hx : InvXB cb G st X)
  (hcnt : CntOKB G st.cnt) (hh : HavocN src cb.cn.statics st args s (st.cnt s) h')

include hc hg hx hcnt hh

/-- A written object was written into a cell of a narrow-reachable object. -/
theorem written_reachB {k : Nat}
    (hw : h' (src k).1 (src k).2 = some (.sym (.havoc s (st.cnt s) k) [])) :
    ReachN st cb.cn.statics args (src k).1 := by
  rcases hh (src k).1 (src k).2 with e | ⟨hr, _, _, _⟩
  · exfalso
    rw [e] at hw
    have hN : G s (st.cnt s) k = none := by
      cases eN : G s (st.cnt s) k with
      | none => rfl
      | some a => have := hcnt.1 _ _ _ _ eN; omega
    have hnd : ∀ o c, cdefault o c ≠ some (.sym (.havoc s (st.cnt s) k) []) := by
      intro o c e
      cases o with
      | alloc _ _ => cases e
      | sym b p =>
        simp only [cdefault, Option.some.injEq, Obj.sym.injEq] at e
        cases p <;> simp at e
    rcases dead_or_not cb.cn.ctx.once (src k).1 with hd | hd
    · rw [hx.deadDflt _ _ hd] at hw; exact hnd _ _ hw
    · cases hj : isJunk (alphaBO cb G st.cnt (src k).1) with
      | true => rw [hx.junkDflt _ _ hj] at hw; exact hnd _ _ hw
      | false =>
        rcases hx.outside _ _ _ hd hw with ⟨hcell, hin⟩ | e2
        · have := hg.heapIn _ _ _ hd hin hcell hw
          rw [alphaBO_none _ hN] at this
          exact hc.cn.noJunk _ this
        · rw [alphaBO_none _ hN] at e2
          have := congrArg isJunk e2
          rw [isJunk_childCN, hj] at this
          cases this
  · exact hr

omit hcnt in
/-- A junk object keeps its default cells through the call. -/
theorem junk_keptB {o : Obj} (hj : isJunk (alphaBO cb G st.cnt o) = true) (c : Cell) :
    h' o c = cdefault o c := by
  rcases hh o c with e | ⟨hr, _⟩
  · rw [e]; exact hx.junkDflt o c hj
  · have := (reach_factsB hc hg hx hr).2; rw [hj] at this; cases this

variable {E V : List Origin} {cov : Origin → Bool}
  (hs : Supp cb.cn.ctx X) (hEU : E ⊆ cb.cn.ctx.origins) (hVU : V ⊆ cb.cn.ctx.origins)
  (hcov : ∀ o, ReachN st cb.cn.statics args o → cov (alphaBO cb G st.cnt o) = true)
  (hcovc : ∀ u c, cov u = true → cov (childCN cb.cn.ctx.K u c) = true)
  (hcovS : ∀ u ∈ cb.cn.ctx.origins, cov u = true → ∀ c ∈ cb.cn.ctx.cells, ∀ v ∈ X.heap u c,
    cov v = true)

omit hc hg hx hcnt hh in
/-- The abstraction of a written object and of the objects below it: the chain name from the
holder origin at the call, in the state after the call. -/
theorem alphaBO_written {k : Nat}
    (hw : h' (src k).1 (src k).2 = some (.sym (.havoc s (st.cnt s) k) [])) (p : List Cell) :
    alphaBO cb (ghostsAfter cb G src st.cnt h' (callWith cb X E V cov) s (st.cnt s)) st.cnt
        (.sym (.havoc s (st.cnt s) k) p) =
      chainB cb (callWith cb X E V cov) (alphaBO cb G st.cnt (src k).1)
        ((src k).2.abs :: p.map Cell.abs) := by
  rw [alphaBO_some _ (ghostsAfter_new hw), renB_same]

include hcov hcovc hcovS in
/-- The name of a written object and of each object below it is covered. -/
theorem cov_written {k : Nat}
    (hw : h' (src k).1 (src k).2 = some (.sym (.havoc s (st.cnt s) k) [])) (p : List Cell) :
    cov (alphaBO cb (ghostsAfter cb G src st.cnt h' (callWith cb X E V cov) s (st.cnt s)) st.cnt
      (.sym (.havoc s (st.cnt s) k) p)) = true := by
  rw [alphaBO_written hw]
  exact cov_chainB hcovc hcovS _ (hcov _ (written_reachB hc hg hx hcnt hh hw))

include hs hEU hVU hcov hcovc hcovS in
/-- LOCAL SOUNDNESS OF THE CALL (generic part): the call of design BO keeps the generic
invariant for the new ghost naming, if the coverage test covers each narrow-reachable origin,
is closed under cell names and under the contents of covered universe cells. -/
theorem InvG.callW :
    InvG cb.cn.ctx (alphaBO cb (ghostsAfter cb G src st.cnt h' (callWith cb X E V cov) s
      (st.cnt s))) { st with heap := h' } (callWith cb X E V cov) := by
  have ag := fun {o : Obj} (hj : isJunk (alphaBO cb G st.cnt o) = false) =>
    alphaBO_after (src := src) (h' := h') (X' := callWith cb X E V cov) (s := s) hcnt hj
  have agU := fun {o : Obj} (hin : alphaBO cb G st.cnt o ∈ cb.cn.ctx.origins) =>
    ag (notJunk_of_mem hc.cn hin)
  have hsX' := supp_callWith (cov := cov) hc hs hEU hVU
  -- a written object: its name is one step from the holder origin
  have hwr : ∀ o c k, src k = (o, c) →
      h' o c = some (.sym (.havoc s (st.cnt s) k) []) →
      alphaBO cb (ghostsAfter cb G src st.cnt h' (callWith cb X E V cov) s (st.cnt s)) st.cnt
        (.sym (.havoc s (st.cnt s) k) []) =
        stepB cb (callWith cb X E V cov) (alphaBO cb G st.cnt o) c.abs := by
    intro o c k hk e
    have hw : h' (src k).1 (src k).2 = some (.sym (.havoc s (st.cnt s) k) []) := by
      rw [hk]; exact e
    rw [alphaBO_written hw, hk]; rfl
  -- a default child of a newly named object: one step from the name of its parent
  have hkid : ∀ o c o', isJunk (alphaBO cb G st.cnt o) = true →
      alphaBO cb (ghostsAfter cb G src st.cnt h' (callWith cb X E V cov) s (st.cnt s)) st.cnt o ∈
        cb.cn.ctx.origins →
      cdefault o c = some o' →
      alphaBO cb (ghostsAfter cb G src st.cnt h' (callWith cb X E V cov) s (st.cnt s)) st.cnt o' =
        stepB cb (callWith cb X E V cov)
          (alphaBO cb (ghostsAfter cb G src st.cnt h' (callWith cb X E V cov) s (st.cnt s))
            st.cnt o) c.abs ∧
      cov (alphaBO cb (ghostsAfter cb G src st.cnt h' (callWith cb X E V cov) s (st.cnt s))
        st.cnt o) = true := by
    intro o c o' hj hin he
    obtain ⟨k, p, rfl, hw, eg⟩ := junk_new hj (notJunk_of_mem hc.cn hin)
    cases he
    exact ⟨alphaBO_cdefault_ghost eg p c,
      cov_written hc hg hx hcnt hh hcov hcovc hcovS hw p⟩
  exact {
    outside := hg.outside
    envOk := fun x o he => ⟨(hg.envOk x o he).1,
      by rw [agU (hg.envOk x o he).2]; exact (hg.envOk x o he).2⟩
    heapLive := fun o c o' hd he => by
      rcases hh o c with e | ⟨_, k, _, e⟩
      · exact hg.heapLive o c o' hd (e ▸ he)
      · change h' o c = some o' at he
        rw [e] at he; cases he; simp [Dead]
    heapIn := fun o c o' hd hin hc1 he => by
      change h' o c = some o' at he
      rcases hh o c with e | ⟨hr, k, hk, e⟩
      · rw [e] at he
        cases hj : isJunk (alphaBO cb G st.cnt o) with
        | false =>
          rw [ag hj] at hin
          have := hg.heapIn o c o' hd hin hc1 he
          rw [agU this]; exact this
        | true =>
          rw [hx.junkDflt o c hj] at he
          obtain ⟨e1, hcv⟩ := hkid o c o' hj hin he
          rw [e1]
          exact hsX' (.h _ _) ⟨hin, hc1⟩ (stepB_in_callWith hin hc1 hcv)
      · rw [e] at he; cases he
        have hj := (reach_factsB hc hg hx hr).2
        rw [hwr o c k hk e]
        rw [ag hj] at hin
        exact hsX' (.h _ _) ⟨hin, hc1⟩ (stepB_in_callWith hin hc1 (hcov o hr))
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
      exact callWith_env_sub hc x (hg.env x hx1 o he)
    heap := fun o c o' hd hin hc1 he => by
      change h' o c = some o' at he
      rcases hh o c with e | ⟨hr, k, hk, e⟩
      · rw [e] at he
        cases hj : isJunk (alphaBO cb G st.cnt o) with
        | false =>
          rw [ag hj] at hin ⊢
          have h1 := hg.heap o c o' hd hin hc1 he
          rw [agU (hg.heapIn o c o' hd hin hc1 he)]
          exact callWith_heap_sub _ _ h1
        | true =>
          rw [hx.junkDflt o c hj] at he
          obtain ⟨e1, hcv⟩ := hkid o c o' hj hin he
          rw [e1]
          exact stepB_in_callWith hin hc1 hcv
      · rw [e] at he; cases he
        have hj := (reach_factsB hc hg hx hr).2
        rw [hwr o c k hk e, ag hj]
        rw [ag hj] at hin
        exact stepB_in_callWith hin hc1 (hcov o hr) }

include hs hEU hVU hcov hcovc hcovS in
/-- LOCAL SOUNDNESS OF THE CALL (extra part): the call of design BO keeps the extra facts for
the new ghost naming, if the contents of the covered universe cells are in `V` and the symbolic
cell names of the covered origins are below `E`. -/
theorem InvXB.callW
    (hVc : ∀ u ∈ cb.cn.ctx.origins, cov u = true → ∀ c ∈ cb.cn.ctx.cells, ∀ v ∈ X.heap u c,
      v ∈ V)
    (hEc : ∀ u, cov u = true → ∀ c b q, childCN cb.cn.ctx.K u c = .sym b q →
      Origin.sym b q ∈ cb.cn.ctx.origins → expB E (.sym b q) = true) :
    InvXB cb (ghostsAfter cb G src st.cnt h' (callWith cb X E V cov) s (st.cnt s))
      { st with heap := h' } (callWith cb X E V cov) := by
  have ag := fun {o : Obj} (hj : isJunk (alphaBO cb G st.cnt o) = false) =>
    alphaBO_after (src := src) (h' := h') (X' := callWith cb X E V cov) (s := s) hcnt hj
  have hsX' := supp_callWith (cov := cov) hc hs hEU hVU
  exact {
    junkDflt := fun o c hj => junk_keptB hc hg hx hh (junk_beforeB hcnt hj) c
    deadDflt := fun o c hd => by
      show h' o c = cdefault o c
      rcases hh o c with e | ⟨hr, _⟩
      · rw [e]; exact hx.deadDflt o c hd
      · exact absurd hd (reach_factsB hc hg hx hr).1
    outside := fun o c o' hd he => by
      change h' o c = some o' at he
      rcases hh o c with e | ⟨hr, k, hk, e⟩
      · rw [e] at he
        cases hj : isJunk (alphaBO cb G st.cnt o) with
        | false =>
          rw [ag hj]
          rcases hx.outside o c o' hd he with h1 | h1
          · exact Or.inl h1
          · right
            have hj' : isJunk (alphaBO cb G st.cnt o') = false := by
              rw [h1, isJunk_childCN]; exact hj
            rw [ag hj']; exact h1
        | true =>
          rw [hx.junkDflt o c hj] at he
          cases hj' : isJunk (alphaBO cb (ghostsAfter cb G src st.cnt h'
              (callWith cb X E V cov) s (st.cnt s)) st.cnt o) with
          | true =>
            right
            -- the object stays junk, and so does its default child
            cases o with
            | alloc _ _ => cases he
            | sym b p =>
              cases he
              cases b with
              | root r => simp only [alphaBO, alpha, symOrDeep] at hj; split at hj <;> cases hj
              | fresh a m => simp only [alphaBO, alpha, symOrDeep] at hj; split at hj <;> cases hj
              | havoc a m k =>
                cases eN : ghostsAfter cb G src st.cnt h' (callWith cb X E V cov) s (st.cnt s)
                    a m k with
                | none => rw [alphaBO_none _ eN, alphaBO_none _ eN]; rfl
                | some g =>
                  exfalso
                  have gok : GhostOK cb g := by
                    rcases ghostsAfter_cases eN with ⟨rfl, rfl, hw, rfl⟩ | eG
                    · exact ⟨(reach_factsB hc hg hx (written_reachB hc hg hx hcnt hh hw)).2, hsX'⟩
                    · exact hx.ghosts _ _ _ _ eG
                  rw [alphaBO_some _ eN, isJunk_renB,
                    chainB_notJunk hc.cn gok.supp _ gok.hold] at hj'
                  cases hj'
          | false =>
            obtain ⟨k, p, rfl, hw, eg⟩ := junk_new hj hj'
            cases he
            rw [show alphaBO cb (ghostsAfter cb G src st.cnt h' (callWith cb X E V cov) s
                (st.cnt s)) st.cnt (.sym (.havoc s (st.cnt s) k) (p ++ [c])) = _ from
              alphaBO_cdefault_ghost eg p c]
            rcases stepB_cases (cb := cb) (callWith cb X E V cov) (alphaBO cb (ghostsAfter cb G
                src st.cnt h' (callWith cb X E V cov) s (st.cnt s)) st.cnt
                (.sym (.havoc s (st.cnt s) k) p)) c.abs with ⟨h1, h2, _, _⟩ | e2
            · exact Or.inl ⟨h2, h1⟩
            · exact Or.inr e2
      · rw [e] at he; cases he
        have hj := (reach_factsB hc hg hx hr).2
        have hw : h' (src k).1 (src k).2 = some (.sym (.havoc s (st.cnt s) k) []) := by
          rw [hk]; exact e
        rw [ag hj]
        have e3 := alphaBO_written (cb := cb) (G := G) (X := X) (E := E) (V := V) (cov := cov) hw []
        rw [hk] at e3
        change _ = stepB cb (callWith cb X E V cov) (alphaBO cb G st.cnt o) c.abs at e3
        rw [e3]
        rcases stepB_cases (cb := cb) (callWith cb X E V cov) (alphaBO cb G st.cnt o) c.abs with
          ⟨h1, h2, _, _⟩ | e2
        · exact Or.inl ⟨h2, h1⟩
        · exact Or.inr e2
    ghosts := fun s' n' k g e => by
      rcases ghostsAfter_cases e with ⟨rfl, rfl, hw, rfl⟩ | eG
      · exact ⟨(reach_factsB hc hg hx (written_reachB hc hg hx hcnt hh hw)).2, hsX'⟩
      · exact hx.ghosts s' n' k g eG
    blocked := fun a m k p hin => by
      rw [callWith_xe hc, callWith_xv]
      cases hj : isJunk (alphaBO cb G st.cnt (.sym (.havoc a m k) p)) with
      | false =>
        rw [ag hj] at hin ⊢
        exact uniqueBO_false_mono (fun x hx' => mem_uni.mpr (Or.inr hx'))
          (fun x hx' => mem_uni.mpr (Or.inr hx')) (hx.blocked a m k p hin)
      | true =>
        obtain ⟨k', p', e, hw, _⟩ := junk_new hj (notJunk_of_mem hc.cn hin)
        cases e
        rw [alphaBO_written hw] at hin ⊢
        exact blocked_chainB hcovc hcovS hVc hEc _ _
          (hcov _ (written_reachB hc hg hx hcnt hh hw)) hin }

end call

/-- The new ghosts of a call are ghosts of that call, with the counters of the call. -/
theorem cnt_afterB {G : GNames} {cnt : Site → Nat} {h' : Heap} {X' : AState} {s : Nat}
    (hcnt : CntOKB G cnt) :
    CntOKB (ghostsAfter cb G src cnt h' X' s (cnt s)) (fupd cnt s (cnt s + 1)) := by
  have hle : ∀ t, cnt t ≤ fupd cnt s (cnt s + 1) t := by
    intro t
    by_cases e : t = s
    · subst e; rw [fupd_same]; exact Nat.le_succ _
    · rw [fupd_ne _ _ e]; exact Nat.le_refl _
  refine ⟨fun s' n' k g e => ?_, fun s' n' k g e t => ?_⟩
  · rcases ghostsAfter_cases e with ⟨rfl, rfl, _, _⟩ | eN
    · rw [fupd_same]; exact Nat.lt_succ_self _
    · exact Nat.lt_of_lt_of_le (hcnt.1 _ _ _ _ eN) (hle s')
  · rcases ghostsAfter_cases e with ⟨rfl, rfl, _, rfl⟩ | eN
    · exact hle t
    · exact Nat.le_trans (hcnt.2 _ _ _ _ eN t) (hle t)

end DirectedAlias.Sound.BlockOnly

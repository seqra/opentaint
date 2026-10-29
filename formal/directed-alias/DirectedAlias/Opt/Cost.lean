import DirectedAlias.Opt.Equiv

/-!
# Optimization O, part 6: cost models and the state-size separation

Cost model of the state size:

* `csize ctx X`: the size of a C state = the sum of the set lengths over all universe keys.
* `osize st`: the size of an O state = the number of map entries. The node table is shared by
  all program points of the analysis. It is not part of the per-point state.

General bound: an O state never has more entries than there are universe keys
(`osize_le_ukeys`).

Family `fam n m`: a join of `m + 1` allocations into variable `0`, then `n` copies
`b := 0` for `b = 1 .. n`. At the end, `n + 1` variables hold the same `m + 1` origins.
C needs at least `(n + 1) * (m + 1)` set elements (`fam_csize`). O needs at most
`(n + 1) + (m + 1)` map entries (`fam_osize`).
-/

namespace DirectedAlias.Opt

open DirectedAlias

/-! ## Cost functions -/

/-- The size of a C state: the sum of the set lengths over all universe keys. -/
def csize (ctx : Ctx) (X : AState) : Nat := ((ukeys ctx).map (fun k => (cval X k).length)).sum

/-- The size of an O state: the number of map entries. -/
def osize (st : OState) : Nat := st.length

/-- The size of the shared node table: the number of nodes plus the sum of the set lengths. -/
def tsize (T : Tbl) : Nat := (T.nodes.map (fun n => n.set.length + 1)).sum

/-- The final O state of each program has at most one entry for each universe key. -/
theorem osize_le_ukeys (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    osize (analyzeProgO K fr p qf).2 ≤ (ukeys (progCtx K fr p qf)).length :=
  (analyzeProgO_rel K fr p qf).2.ent.length_le

/-! ## Sum lemmas -/

/-- The sum over a filtered list is at most the sum over the list. -/
theorem sum_filter_le {α : Type} (f : α → Nat) (p : α → Bool) :
    ∀ (l : List α), ((l.filter p).map f).sum ≤ (l.map f).sum
  | [] => Nat.le_refl _
  | a :: l => by
    rw [List.filter_cons]
    have ih := sum_filter_le f p l
    cases p a with
    | true => simp only [ite_true, List.map_cons, List.sum_cons]; exact Nat.add_le_add_left ih _
    | false =>
      simp only [Bool.false_eq_true, ite_false, List.map_cons, List.sum_cons]
      exact Nat.le_trans ih (Nat.le_add_left _ _)

/-- If `x` is in the list, then `f x` plus the sum over the other elements is at most the sum. -/
theorem sum_filter_add {α : Type} [DecidableEq α] (f : α → Nat) {x : α} :
    ∀ {l : List α}, x ∈ l → f x + ((l.filter (fun y => decide (y ≠ x))).map f).sum ≤ (l.map f).sum
  | [], h => by cases h
  | y :: l, h => by
    rw [List.filter_cons]
    by_cases hy : y = x
    · subst hy
      simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ite_false,
        List.map_cons, List.sum_cons]
      exact Nat.add_le_add_left (sum_filter_le f _ l) _
    · have hx : x ∈ l := by
        cases List.mem_cons.mp h with
        | inl h1 => exact absurd h1.symm hy
        | inr h1 => exact h1
      simp only [ne_eq, hy, not_false_eq_true, decide_true, ite_true, List.map_cons,
        List.sum_cons]
      have := sum_filter_add f hx
      simp only [ne_eq] at this
      omega

/-- The sum over a list with no duplicates that is a subset of a second list is at most the sum
over the second list. -/
theorem sum_le_of_nodup_sub {α : Type} [DecidableEq α] (f : α → Nat) :
    ∀ {l m : List α}, l.Nodup → (∀ a ∈ l, a ∈ m) → (l.map f).sum ≤ (m.map f).sum
  | [], _, _, _ => Nat.zero_le _
  | x :: l, m, hn, hs => by
    rw [List.nodup_cons] at hn
    have hx : x ∈ m := hs x List.mem_cons_self
    have hsub : ∀ a ∈ l, a ∈ m.filter (fun y => decide (y ≠ x)) := by
      intro a ha
      refine List.mem_filter.mpr ⟨hs a (List.mem_cons_of_mem _ ha), ?_⟩
      have : a ≠ x := fun h => hn.1 (h ▸ ha)
      simp [this]
    have h1 := sum_le_of_nodup_sub f hn.2 hsub
    have h2 := sum_filter_add f hx
    simp only [List.map_cons, List.sum_cons]
    omega

/-- If each term is at least `c`, the sum is at least the length times `c`. -/
theorem sum_ge_length_mul {α : Type} (f : α → Nat) (c : Nat) :
    ∀ (l : List α), (∀ a ∈ l, c ≤ f a) → l.length * c ≤ (l.map f).sum
  | [], _ => by simp
  | a :: l, h => by
    have ih := sum_ge_length_mul f c l (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have ha := h a List.mem_cons_self
    simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.succ_mul]
    omega

/-! ## Lists of distinct numbers -/

/-- The list `k, k + 1, ..., k + n - 1`. -/
def ids : Nat → Nat → List Nat
  | _, 0 => []
  | k, n + 1 => k :: ids (k + 1) n

/-- The members of `ids k n` are the numbers from `k` below `k + n`. -/
theorem mem_ids : ∀ {k n x : Nat}, x ∈ ids k n ↔ k ≤ x ∧ x < k + n
  | k, 0, x => by
    constructor
    · intro h; cases h
    · rintro ⟨h1, h2⟩
      exact absurd (Nat.lt_of_le_of_lt h1 h2) (Nat.lt_irrefl _)
  | k, n + 1, x => by
    simp only [ids, List.mem_cons]
    rw [mem_ids]
    constructor
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨Nat.le_refl _, by omega⟩
      · exact ⟨by omega, by omega⟩
    · rintro ⟨h1, h2⟩
      cases Nat.eq_or_lt_of_le h1 with
      | inl h => exact Or.inl h.symm
      | inr h => exact Or.inr ⟨h, by omega⟩

/-- `ids k n` has no duplicates. -/
theorem nodup_ids : ∀ (k n : Nat), (ids k n).Nodup
  | _, 0 => List.nodup_nil
  | k, n + 1 => by
    simp only [ids]
    rw [List.nodup_cons]
    refine ⟨?_, nodup_ids (k + 1) n⟩
    intro h
    have := (mem_ids.mp h).1
    omega

/-- `ids k n` has `n` elements. -/
theorem length_ids : ∀ (k n : Nat), (ids k n).length = n
  | _, 0 => rfl
  | k, n + 1 => by simp [ids, length_ids (k + 1) n]

/-- The allocation origins of a list of distinct sites are distinct. -/
theorem nodup_map_alloc : ∀ {l : List Site}, l.Nodup → (l.map Origin.alloc).Nodup
  | [], _ => List.nodup_nil
  | s :: l, h => by
    rw [List.nodup_cons] at h
    simp only [List.map_cons]
    rw [List.nodup_cons]
    refine ⟨?_, nodup_map_alloc h.2⟩
    intro hm
    obtain ⟨t, ht, he⟩ := List.mem_map.mp hm
    cases he
    exact h.1 ht

/-! ## The state-size family -/

/-- A join chain: `a := new s`, or `a := new t` for each further site `t`. -/
def chainJ (a : Var) : Site → List Site → Prog
  | s, [] => .stmt (.new a s)
  | s, t :: r => .choice (.stmt (.new a s)) (chainJ a t r)

/-- Copies `b := a` for each `b` of the list. -/
def copies (a : Var) : List Var → Prog
  | [] => .skip
  | b :: bs => .seq (.stmt (.copy b a)) (copies a bs)

/-- The family: a join of the sites `0 .. m` into variable `0`, then copies to `1 .. n`. -/
def fam (n m : Nat) : Prog := .seq (chainJ 0 0 (ids 1 m)) (copies 0 (ids 1 n))

/-- The empty frame. -/
def fr0 : Frame := ⟨[]⟩

/-- After the join chain, variable `a` holds exactly the allocations of the sites. -/
theorem chain_env (ctx : Ctx) (a : Var) :
    ∀ (s : Site) (ss : List Site) (X : AState) (o : Origin),
      o ∈ (analyze ctx (chainJ a s ss) X).env a ↔ o ∈ (s :: ss).map Origin.alloc
  | s, [], X, o => by
    simp [chainJ, analyze, astep, AState.setVar]
  | s, t :: r, X, o => by
    simp only [chainJ, analyze, join]
    rw [mem_uni, chain_env ctx a t r X o]
    simp [astep, AState.setVar]

/-- After the copies, each copied variable holds the old value of `a`; other variables keep
their values. -/
theorem copies_env (ctx : Ctx) (a : Var) :
    ∀ (bs : List Var) (Y : AState), a ∉ bs → ∀ z,
      (analyze ctx (copies a bs) Y).env z = if z ∈ bs then Y.env a else Y.env z
  | [], Y, _, z => by simp [copies, analyze]
  | b :: bs, Y, ha, z => by
    have hab : a ≠ b := fun h => ha (h ▸ List.mem_cons_self)
    have ha' : a ∉ bs := fun h => ha (List.mem_cons_of_mem _ h)
    simp only [copies, analyze]
    rw [copies_env ctx a bs _ ha' z]
    simp only [astep, AState.setVar, fupd, ite_eq_right hab]
    by_cases hz : z = b
    · subst hz; simp
    · simp [hz]

/-- The statements of a join chain. -/
theorem chainJ_stmts (a : Var) :
    ∀ (s : Site) (ss : List Site), (chainJ a s ss).stmts = (s :: ss).map (Stmt.new a)
  | s, [] => rfl
  | s, t :: r => by simp [chainJ, Prog.stmts, chainJ_stmts a t r]

/-- The statements of the copies. -/
theorem copies_stmts (a : Var) : ∀ (bs : List Var),
    (copies a bs).stmts = bs.map (fun b => Stmt.copy b a)
  | [] => rfl
  | b :: bs => by simp [copies, Prog.stmts, copies_stmts a bs]

/-- The variables of the family are `0 .. n`. -/
theorem fam_vars (n m : Nat) {x : Var} : x ∈ (fam n m).vars ↔ x ∈ 0 :: ids 1 n := by
  simp only [fam, Prog.vars, Prog.stmts, chainJ_stmts, copies_stmts, List.flatMap_append,
    List.mem_append, List.mem_flatMap, List.mem_map, List.mem_cons]
  constructor
  · rintro (⟨st, ⟨s, _, rfl⟩, hx⟩ | ⟨st, ⟨b, hb, rfl⟩, hx⟩)
    · simp [Stmt.vars] at hx; exact Or.inl hx
    · simp only [Stmt.vars, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact Or.inr hb
      · exact Or.inl rfl
  · rintro (rfl | hx)
    · exact Or.inl ⟨.new 0 0, ⟨0, Or.inl rfl, rfl⟩, by simp [Stmt.vars]⟩
    · exact Or.inr ⟨.copy x 0, ⟨x, hx, rfl⟩, by simp [Stmt.vars]⟩

/-- A filter map with the constant `none` gives the empty list. -/
theorem filterMap_none {α β : Type} : ∀ (l : List α), l.filterMap (fun _ => (none : Option β)) = []
  | [] => rfl
  | _ :: l => by simp only [List.filterMap_cons]; exact filterMap_none l

/-- A flat map with the constant empty list gives the empty list. -/
theorem flatMap_nil' {α β : Type} : ∀ (l : List α), l.flatMap (fun _ => ([] : List β)) = []
  | [] => rfl
  | _ :: l => by simp only [List.flatMap_cons, List.nil_append]; exact flatMap_nil' l

/-- A flat map with singletons has the length of the list. -/
theorem length_flatMap_single {α β : Type} (g : α → β) :
    ∀ (l : List α), (l.flatMap (fun a => [g a])).length = l.length
  | [] => rfl
  | a :: l => by
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil,
      length_flatMap_single g l]
    omega

/-- The statements of the family. -/
theorem fam_stmts (n m : Nat) : (fam n m).stmts =
    (0 :: ids 1 m).map (Stmt.new 0) ++ (ids 1 n).map (fun b => Stmt.copy b 0) := by
  simp only [fam, Prog.stmts, chainJ_stmts, copies_stmts]

/-- The origins of the family context are the allocations of the sites `0 .. m`. -/
theorem fam_origins (K n m : Nat) (qf : List Field) :
    (progCtx K fr0 (fam n m) qf).origins = (0 :: ids 1 m).map Origin.alloc := by
  have h1 : (fam n m).freshSites = [] := by
    simp only [Prog.freshSites, fam_stmts, List.filterMap_append, List.filterMap_map]
    have e1 : (Stmt.freshSite? ∘ Stmt.new 0) = fun _ => none := rfl
    have e2 : (Stmt.freshSite? ∘ fun b => Stmt.copy b 0) = fun _ => none := rfl
    rw [e1, e2, filterMap_none, filterMap_none]; rfl
  have h2 : (fam n m).callSites = [] := by
    simp only [Prog.callSites, fam_stmts, List.filterMap_append, List.filterMap_map]
    have e1 : (Stmt.callSite? ∘ Stmt.new 0) = fun _ => none := rfl
    have e2 : (Stmt.callSite? ∘ fun b => Stmt.copy b 0) = fun _ => none := rfl
    rw [e1, e2, filterMap_none, filterMap_none]; rfl
  have h3 : (fam n m).newSites = 0 :: ids 1 m := by
    simp only [Prog.newSites, fam_stmts, List.filterMap_append, List.filterMap_map]
    have e1 : (Stmt.newSite? ∘ Stmt.new 0) = some := rfl
    have e2 : (Stmt.newSite? ∘ fun b => Stmt.copy b 0) = fun _ => none := rfl
    rw [e1, e2, List.filterMap_some, filterMap_none, List.append_nil]
  simp only [progCtx, Ctx.ofProg, originsOf, h1, h2, h3, fr0, Frame.roots, List.map_nil,
    List.append_nil, List.flatMap_nil, List.nil_append]

/-- The cells of the family context with no query fields: only the array element. -/
theorem fam_cells (K n m : Nat) : (progCtx K fr0 (fam n m) []).cells = [.elem] := by
  have h : (fam n m).fields = [] := by
    simp only [Prog.fields, fam_stmts, List.flatMap_append, List.flatMap_map]
    have e1 : (Stmt.fields ∘ Stmt.new 0) = fun _ => [] := rfl
    have e2 : (Stmt.fields ∘ fun b => Stmt.copy b 0) = fun _ => [] := rfl
    simp only [Function.comp_def] at e1 e2
    rw [e1, e2, flatMap_nil', flatMap_nil']; rfl
  simp only [progCtx, Ctx.ofProg, cellsOf, h, List.append_nil]
  rfl

/-- In the family, C needs at least `(n + 1) * (m + 1)` set elements at the end. -/
theorem fam_csize (K n m : Nat) :
    (n + 1) * (m + 1) ≤ csize (progCtx K fr0 (fam n m) []) (analyzeProg K fr0 (fam n m) []) := by
  let ctx := progCtx K fr0 (fam n m) []
  let X := analyzeProg K fr0 (fam n m) []
  have h0 : (0 : Var) ∉ ids 1 n := fun h => by have := (mem_ids.mp h).1; omega
  have henv : ∀ x ∈ 0 :: ids 1 n, ∀ o, o ∈ X.env x ↔ o ∈ (0 :: ids 1 m).map Origin.alloc := by
    intro x hx o
    show o ∈ (analyze ctx (copies 0 (ids 1 n)) (analyze ctx (chainJ 0 0 (ids 1 m))
      (ainit K fr0))).env x ↔ _
    rw [copies_env ctx 0 (ids 1 n) _ h0 x]
    split
    · exact chain_env ctx 0 0 (ids 1 m) _ o
    · rename_i hn
      have : x = 0 := by
        cases List.mem_cons.mp hx with
        | inl h => exact h
        | inr h => exact absurd h hn
      subst this
      exact chain_env ctx 0 0 (ids 1 m) _ o
  have hlen : ∀ x ∈ 0 :: ids 1 n, m + 1 ≤ (X.env x).length := by
    intro x hx
    have := nodup_length_le (nodup_map_alloc (l := 0 :: ids 1 m) (by
        rw [List.nodup_cons]
        exact ⟨fun h => by have := (mem_ids.mp h).1; omega, nodup_ids 1 m⟩))
      (fun o ho => (henv x hx o).mpr ho)
    simpa [length_ids] using this
  have hvars : ∀ x ∈ 0 :: ids 1 n, x ∈ ctx.vars := by
    intro x hx
    show x ∈ ((fam n m).vars ++ fr0.vars).eraseDups
    rw [List.mem_eraseDups]
    exact List.mem_append_left _ ((fam_vars n m).mpr hx)
  have hnd : (0 :: ids 1 n).Nodup := by
    rw [List.nodup_cons]; exact ⟨h0, nodup_ids 1 n⟩
  have s1 : (0 :: ids 1 n).length * (m + 1) ≤ ((0 :: ids 1 n).map (fun x => (X.env x).length)).sum :=
    sum_ge_length_mul _ _ _ hlen
  have s2 : ((0 :: ids 1 n).map (fun x => (X.env x).length)).sum ≤
      (ctx.vars.map (fun x => (X.env x).length)).sum :=
    sum_le_of_nodup_sub _ hnd hvars
  have s3 : (ctx.vars.map (fun x => (X.env x).length)).sum ≤ csize ctx X := by
    unfold csize ukeys
    rw [List.map_append, List.sum_append, List.map_map]
    exact Nat.le_add_right _ _
  simp only [List.length_cons, length_ids] at s1
  exact Nat.le_trans s1 (Nat.le_trans s2 s3)

/-- In the family, the O state has at most `(n + 1) + (m + 1)` map entries at the end. -/
theorem fam_osize (K n m : Nat) :
    osize (analyzeProgO K fr0 (fam n m) []).2 ≤ (n + 1) + (m + 1) := by
  let ctx := progCtx K fr0 (fam n m) []
  have hR := (analyzeProgO_rel K fr0 (fam n m) []).2
  let L : List Key := (0 :: ids 1 n).map Key.v ++
    ((0 :: ids 1 m).map Origin.alloc).flatMap (fun o => [Key.h o .elem])
  have hsub : ∀ k ∈ (analyzeProgO K fr0 (fam n m) []).2.map Prod.fst, k ∈ L := by
    intro k hk
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hk
    have hu := (hR.ent.ent p hp).2
    cases hpk : p.1 with
    | v x =>
      rw [hpk] at hu
      have hx : x ∈ ((fam n m).vars ++ fr0.vars).eraseDups := hu
      rw [List.mem_eraseDups] at hx
      have hx' : x ∈ (fam n m).vars := by simpa [fr0, Frame.vars] using hx
      exact List.mem_append_left _ (List.mem_map.mpr ⟨x, (fam_vars n m).mp hx', rfl⟩)
    | h o c =>
      rw [hpk] at hu
      obtain ⟨ho, hc⟩ := hu
      have ho' : o ∈ (0 :: ids 1 m).map Origin.alloc := by
        rw [← fam_origins K n m []]; exact ho
      have hc' : c = .elem := by
        have : c ∈ ctx.cells := hc
        rw [fam_cells] at this; simpa using this
      subst hc'
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨o, ho', List.mem_singleton_self _⟩)
  have hL : L.length = (n + 1) + (m + 1) := by
    simp only [L, List.length_append, List.length_map, length_flatMap_single, List.length_cons,
      length_ids]
  have := nodup_length_le hR.ent.nodup hsub
  rw [List.length_map, hL] at this
  exact this

end DirectedAlias.Opt

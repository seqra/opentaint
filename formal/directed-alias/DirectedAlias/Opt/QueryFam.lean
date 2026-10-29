import DirectedAlias.Opt.Query
import DirectedAlias.Examples

/-!
# Optimization O, part 9: the query layer on O states, and the query separation family

* `findAliasO_iff`: the search on the denotation of the O state gives exactly the C
  enumeration result on the C state.
* `progCtx_vars_nodup`, `progCtx_cells_nodup`: the program context lists have no duplicates,
  so the search output of a program has no duplicates.
* `qfam_sep`: on the family `qfam n` (`i := new i` for `i = 0 .. n`, with `c` query fields), the
  query `findAlias(0)` costs at most `(n + 1) ((D + 2) (c + 2) + D)` by search, and at least
  `(n + 1) (c + 1) ^ D` by enumeration.
* Examples: `findAlias(z)` after the field example is `{z, x.f, y.f}` (by search on the O state).
-/

namespace DirectedAlias.Opt

open DirectedAlias

/-! ## The search on O states -/

/-- The denotation of an O state has support. -/
theorem supp_den {ctx : Ctx} (cc : CtxClosed ctx) {T : Tbl} (g : T.Good ctx.origins)
    (st : OState) : Supp ctx (den ctx.K T st) := by
  intro k hk
  rw [cval_den]
  exact val_sub cc g st hk

/-- Path evaluation on the denotation of an O state agrees with path evaluation on the C state. -/
theorem aevalFrom_den {ctx : Ctx} {T : Tbl} {st : OState} {X : AState} (hR : Rel ctx T st X) :
    ∀ (p : List ACell) {S S' : List Origin}, SetEq S S' → S' ⊆ ctx.origins →
      (∀ c ∈ p, c ∈ ctx.cells) → SetEq (aevalFrom (den ctx.K T st) S p) (aevalFrom X S' p)
  | [], _, _, h, _, _ => h
  | c :: p, S, S', h, hS', hp => by
    have hc : c ∈ ctx.cells := hp c List.mem_cons_self
    simp only [aevalFrom]
    apply aevalFrom_den hR p _ (aread_sub hR.supp hS' hc)
      (fun c' hc' => hp c' (List.mem_cons_of_mem _ hc'))
    intro o'
    rw [mem_aread]
    exact aread_agree hR h hS' hc o'

/-- May-alias on the denotation of an O state is may-alias on the C state. -/
theorem may_den {ctx : Ctx} {T : Tbl} {st : OState} {X : AState} (hR : Rel ctx T st X)
    {v x : Var} (hv : v ∈ ctx.vars) (hx : x ∈ ctx.vars) {π π' : List ACell}
    (hπ : ∀ c ∈ π, c ∈ ctx.cells) (hπ' : ∀ c ∈ π', c ∈ ctx.cells) :
    may (den ctx.K T st) v π x π' = may X v π x π' := by
  unfold may aevalPath
  exact meetB_congr (aevalFrom_den hR π (hR.agree (.v v) hv) (hR.supp.env hv) hπ)
    (aevalFrom_den hR π' (hR.agree (.v x) hx) (hR.supp.env hx) hπ')

/-- The search on the denotation of an O state gives exactly the C enumeration result. -/
theorem findAliasO_iff {ctx : Ctx} (cc : CtxClosed ctx) {T : Tbl} (g : T.Good ctx.origins)
    {st : OState} {X : AState} (hR : Rel ctx T st X) {x : Var} (hx : x ∈ ctx.vars) (D : Nat)
    (v : Var) (π : List ACell) :
    (v, π) ∈ findAlias ctx (den ctx.K T st) D x ↔ (v, π) ∈ enumAlias ctx X D x := by
  rw [findAlias_iff (supp_den cc g st) hx]
  simp only [enumAlias, List.mem_filter, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨w, hw, ρ, hρ, rfl, rfl⟩, hm⟩
    refine ⟨⟨w, hw, ρ, hρ, rfl, rfl⟩, ?_⟩
    rw [← may_den hR hw hx (mem_pathsUpTo.mp hρ).2 (fun _ h => by cases h)]
    exact hm
  · rintro ⟨⟨w, hw, ρ, hρ, rfl, rfl⟩, hm⟩
    refine ⟨⟨w, hw, ρ, hρ, rfl, rfl⟩, ?_⟩
    rw [may_den hR hw hx (mem_pathsUpTo.mp hρ).2 (fun _ h => by cases h)]
    exact hm

/-! ## No duplicates in the program context -/

/-- `eraseDups` gives a list with no duplicates. -/
theorem nodup_eraseDups {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (n : Nat) (l : List α), l.length ≤ n → l.eraseDups.Nodup
  | _, [], _ => List.nodup_nil
  | 0, _ :: _, h => absurd h (by simp)
  | n + 1, a :: as, h => by
    rw [List.eraseDups_cons, List.nodup_cons]
    refine ⟨?_, nodup_eraseDups n _ (Nat.le_trans (List.length_filter_le _ _)
      (by simp at h; omega))⟩
    intro hm
    rw [List.mem_eraseDups, List.mem_filter] at hm
    simp at hm

/-- The variables of a program context have no duplicates. -/
theorem progCtx_vars_nodup (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    (progCtx K fr p qf).vars.Nodup :=
  nodup_eraseDups _ _ (Nat.le_refl _)

/-- The cells of a program context have no duplicates. -/
theorem progCtx_cells_nodup (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    (progCtx K fr p qf).cells.Nodup := by
  show (cellsOf (p.fields ++ qf)).Nodup
  unfold cellsOf
  rw [List.nodup_append]
  have hfs := nodup_eraseDups _ (p.fields ++ qf) (Nat.le_refl _)
  refine ⟨?_, by simp, ?_⟩
  · generalize (p.fields ++ qf).eraseDups = l at hfs
    induction l with
    | nil => exact List.nodup_nil
    | cons f l ih =>
      rw [List.nodup_cons] at hfs
      simp only [List.map_cons]
      rw [List.nodup_cons]
      refine ⟨?_, ih hfs.2⟩
      intro hm
      obtain ⟨f', hf', he⟩ := List.mem_map.mp hm
      cases he
      exact hfs.1 hf'
  · intro a ha b hb heq
    subst heq
    obtain ⟨f, _, rfl⟩ := List.mem_map.mp ha
    simp at hb

/-! ## The query family -/

/-- The family program: `i := new i` for each `i` of the list. -/
def newsP : List Nat → Prog
  | [] => .skip
  | i :: is => .seq (.stmt (.new i i)) (newsP is)

/-- The family: `i := new i` for `i = 0 .. n`. -/
def qfam (n : Nat) : Prog := newsP (ids 0 (n + 1))

/-- The statements of the family program. -/
theorem newsP_stmts : ∀ (is : List Nat), (newsP is).stmts = is.map (fun i => Stmt.new i i)
  | [] => rfl
  | i :: is => by simp [newsP, Prog.stmts, newsP_stmts is]

/-- The family program sets each listed variable to its allocation and keeps the heap. -/
theorem newsP_env (ctx : Ctx) : ∀ (is : List Nat) (X : AState) (z : Var),
    (analyze ctx (newsP is) X).env z = if z ∈ is then [.alloc z] else X.env z
  | [], X, z => by simp [newsP, analyze]
  | i :: is, X, z => by
    simp only [newsP, analyze]
    rw [newsP_env ctx is _ z]
    simp only [astep, AState.setVar, fupd]
    by_cases h1 : z ∈ is
    · simp [h1]
    · by_cases h2 : z = i
      · subst h2; simp [h1]
      · simp [h1, h2]

/-- The family program keeps the heap. -/
theorem newsP_heap (ctx : Ctx) : ∀ (is : List Nat) (X : AState),
    (analyze ctx (newsP is) X).heap = X.heap
  | [], _ => rfl
  | i :: is, X => by
    simp only [newsP, analyze]
    rw [newsP_heap ctx is _]
    rfl

/-- The variables of the family. -/
theorem qfam_vars (K n : Nat) (qf : List Field) {x : Var} :
    x ∈ (progCtx K fr0 (qfam n) qf).vars ↔ x ∈ ids 0 (n + 1) := by
  show x ∈ ((qfam n).vars ++ fr0.vars).eraseDups ↔ _
  rw [List.mem_eraseDups]
  simp only [qfam, Prog.vars, newsP_stmts, fr0, Frame.vars, List.map_nil, List.append_nil,
    List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨st, ⟨i, hi, rfl⟩, hx⟩
    simp only [Stmt.vars, List.mem_singleton] at hx
    exact hx ▸ hi
  · intro hx
    exact ⟨.new x x, ⟨x, hx, rfl⟩, by simp [Stmt.vars]⟩

/-- The origins of the family. -/
theorem qfam_origins (K n : Nat) (qf : List Field) :
    (progCtx K fr0 (qfam n) qf).origins = (ids 0 (n + 1)).map Origin.alloc := by
  have h1 : (qfam n).freshSites = [] := by
    simp only [Prog.freshSites, qfam, newsP_stmts, List.filterMap_map]
    have e : (Stmt.freshSite? ∘ fun i => Stmt.new i i) = fun _ => none := rfl
    rw [e, filterMap_none]
  have h2 : (qfam n).callSites = [] := by
    simp only [Prog.callSites, qfam, newsP_stmts, List.filterMap_map]
    have e : (Stmt.callSite? ∘ fun i => Stmt.new i i) = fun _ => none := rfl
    rw [e, filterMap_none]
  have h3 : (qfam n).newSites = ids 0 (n + 1) := by
    simp only [Prog.newSites, qfam, newsP_stmts, List.filterMap_map]
    have e : (Stmt.newSite? ∘ fun i => Stmt.new i i) = some := rfl
    rw [e, List.filterMap_some]
  simp only [progCtx, Ctx.ofProg, originsOf, h1, h2, h3, fr0, Frame.roots, List.map_nil,
    List.append_nil, List.flatMap_nil, List.nil_append]

/-- The cells of the family with the query fields `0 .. c - 1`. -/
theorem qfam_cells (K n c : Nat) :
    (progCtx K fr0 (qfam n) (ids 0 c)).cells = (ids 0 c).eraseDups.map ACell.fld ++ [.elem] := by
  have h : (qfam n).fields = [] := by
    simp only [Prog.fields, qfam, newsP_stmts, List.flatMap_map]
    have e : (Stmt.fields ∘ fun i => Stmt.new i i) = fun _ => [] := rfl
    simp only [Function.comp_def] at e
    rw [e, flatMap_nil']
  simp only [progCtx, Ctx.ofProg, cellsOf, h, List.nil_append]

/-- The evaluation of a path from the empty set is empty. -/
theorem aevalFrom_nil (X : AState) : ∀ (p : List ACell), aevalFrom X [] p = []
  | [] => rfl
  | _ :: p => aevalFrom_nil X p

/-- A list with no duplicates whose elements are all `a` has at most one element. -/
theorem length_le_one_of_all_eq {α : Type} {a : α} : ∀ {l : List α}, l.Nodup →
    (∀ b ∈ l, b = a) → l.length ≤ 1
  | [], _, _ => Nat.zero_le _
  | [_], _, _ => Nat.le_refl _
  | b1 :: b2 :: l, hn, h => by
    rw [List.nodup_cons] at hn
    exact absurd ((h b2 (by simp)).trans (h b1 List.mem_cons_self).symm ▸ List.mem_cons_self) hn.1

/-- The number of paths of length at most `D` is at least `|cells| ^ D`. -/
theorem pathsUpTo_length_ge (cells : List ACell) :
    ∀ (D : Nat), cells.length ^ D ≤ (pathsUpTo cells D).length
  | 0 => by simp [pathsUpTo]
  | D + 1 => by
    have ih := pathsUpTo_length_ge cells D
    have hl : (pathsUpTo cells (D + 1)).length = 1 + cells.length * (pathsUpTo cells D).length := by
      simp only [pathsUpTo, List.length_cons, List.length_flatMap, List.length_map]
      have : ∀ (l : List ACell), (l.map (fun _ => (pathsUpTo cells D).length)).sum =
          l.length * (pathsUpTo cells D).length := by
        intro l; induction l with
        | nil => simp
        | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons,
            Nat.succ_mul]; omega
      rw [this]; omega
    rw [hl, Nat.pow_succ, Nat.mul_comm (cells.length ^ D)]
    have := Nat.mul_le_mul_left cells.length ih
    omega

/-- The query separation on the family `qfam n` with `c` query fields and depth `D`: the search
costs at most `(n + 1) ((D + 2) (c + 2) + D)`, and the enumeration costs at least
`(n + 1) (c + 1) ^ D`. -/
theorem qfam_sep (K n c D : Nat) :
    searchCost (progCtx K fr0 (qfam n) (ids 0 c)) (analyzeProg K fr0 (qfam n) (ids 0 c)) D 0 ≤
        (n + 1) * ((D + 2) * (c + 2) + D) ∧
      (n + 1) * (c + 1) ^ D ≤ enumCost (progCtx K fr0 (qfam n) (ids 0 c)) D := by
  let ctx := progCtx K fr0 (qfam n) (ids 0 c)
  let X := analyzeProg K fr0 (qfam n) (ids 0 c)
  have hs : Supp ctx X :=
    Supp.analyze (ctxClosed_ofProg K fr0 (qfam n) (ids 0 c)) _ _
      (progOK_ofProg K fr0 (qfam n) (ids 0 c)) (supp_ainit K fr0 (qfam n) (ids 0 c))
  have henv : ∀ z, z ∈ ids 0 (n + 1) → X.env z = [.alloc z] := by
    intro z hz
    show (analyze ctx (newsP (ids 0 (n + 1))) (ainit K fr0)).env z = _
    rw [newsP_env]; simp [hz]
  have hheap : ∀ o c', X.heap o c' = adefault K o c' := by
    intro o c'
    show (analyze ctx (newsP (ids 0 (n + 1))) (ainit K fr0)).heap o c' = _
    rw [newsP_heap]; rfl
  have h0 : (0 : Var) ∈ ctx.vars := (qfam_vars K n _).mpr (mem_ids.mpr ⟨Nat.le_refl _, by omega⟩)
  have hvn := progCtx_vars_nodup K fr0 (qfam n) (ids 0 c)
  have hcn := progCtx_cells_nodup K fr0 (qfam n) (ids 0 c)
  -- the output has at most one element: `(0, [])`
  have hout : (findAlias ctx X D 0).length ≤ 1 := by
    apply length_le_one_of_all_eq (findAlias_nodup hs h0 hvn hcn D) (a := ((0 : Var), ([] : List ACell)))
    rintro ⟨v, π⟩ hm
    have := (findAlias_iff hs h0 D v π).mp hm
    simp only [enumAlias, List.mem_filter, List.mem_flatMap, List.mem_map, Prod.mk.injEq] at this
    obtain ⟨⟨w, hw, ρ, _, rfl, rfl⟩, hmay⟩ := this
    have hw' := (qfam_vars K n _).mp hw
    obtain ⟨o, h1, h2⟩ := may_iff.mp hmay
    simp only [aevalPath, aevalFrom, henv 0 (mem_ids.mpr ⟨Nat.le_refl _, by omega⟩),
      List.mem_singleton] at h2
    subst h2
    cases ρ with
    | nil =>
      simp only [aevalPath, aevalFrom, henv w hw', List.mem_singleton, Origin.alloc.injEq] at h1
      rw [h1]
    | cons c' ρ' =>
      exfalso
      simp only [aevalPath, aevalFrom, henv w hw'] at h1
      have hr : aread X [Origin.alloc w] c' = [] := by
        simp [aread, uniMap, hheap, adefault, uni]
      rw [hr, aevalFrom_nil] at h1
      cases h1
  -- the index
  have hhidx : (hidx ctx X).length = 0 := by
    cases h : hidx ctx X with
    | nil => rfl
    | cons e _ =>
      exfalso
      have he : e ∈ hidx ctx X := by rw [h]; exact List.mem_cons_self
      obtain ⟨h1, _, h3⟩ := mem_hidx.mp he
      have h1' : e.1 ∈ (ids 0 (n + 1)).map Origin.alloc := by
        have : ctx.origins = _ := qfam_origins K n (ids 0 c); rw [← this]; exact h1
      obtain ⟨i, _, hi⟩ := List.mem_map.mp h1'
      rw [hheap, ← hi] at h3
      simp [adefault] at h3
  have hvars_le : ctx.vars.length ≤ n + 1 := by
    have := nodup_length_le hvn (m := ids 0 (n + 1)) (fun x hx => (qfam_vars K n _).mp hx)
    rw [length_ids] at this; exact this
  have hvidx : (vidx ctx X).length = ctx.vars.length := by
    unfold vidx
    rw [List.length_flatMap]
    have : ∀ (l : List Var), (∀ v ∈ l, v ∈ ids 0 (n + 1)) →
        (l.map (fun v => ((X.env v).map (fun o => (v, o))).length)).sum = l.length := by
      intro l hl
      induction l with
      | nil => rfl
      | cons v l ih =>
        simp only [List.map_cons, List.sum_cons, List.length_map, List.length_cons]
        rw [henv v (hl v List.mem_cons_self)]
        have := ih (fun w hw => hl w (List.mem_cons_of_mem _ hw))
        simp only [List.length_map] at this
        simp only [List.length_singleton]
        omega
    exact this ctx.vars (fun x hx => (qfam_vars K n _).mp hx)
  have hU : ctx.origins.length = n + 1 := by
    have : ctx.origins = _ := qfam_origins K n (ids 0 c)
    rw [this, List.length_map, length_ids]
  have hcells_le : ctx.cells.length ≤ c + 1 := by
    have : ctx.cells = _ := qfam_cells K n c
    rw [this, List.length_append, List.length_map]
    have := nodup_length_le (nodup_eraseDups _ (ids 0 c) (Nat.le_refl _)) (m := ids 0 c)
      (fun f hf => (List.mem_eraseDups).mp hf)
    rw [length_ids] at this
    simp only [List.length_singleton]
    omega
  have hcells_ge : c + 1 ≤ ctx.cells.length := by
    have hl : ((ids 0 c).map ACell.fld ++ [ACell.elem]).Nodup := by
      rw [List.nodup_append]
      refine ⟨?_, by simp, ?_⟩
      · have := nodup_ids 0 c
        generalize ids 0 c = l at this
        induction l with
        | nil => exact List.nodup_nil
        | cons f l ih =>
          rw [List.nodup_cons] at this
          simp only [List.map_cons]
          rw [List.nodup_cons]
          refine ⟨?_, ih this.2⟩
          intro hm
          obtain ⟨f', hf', he⟩ := List.mem_map.mp hm
          cases he
          exact this.1 hf'
      · intro a ha b hb heq; subst heq
        obtain ⟨f, _, rfl⟩ := List.mem_map.mp ha; simp at hb
    have := nodup_length_le hl (m := ctx.cells) (by
      intro a ha
      have : ctx.cells = _ := qfam_cells K n c
      rw [this]
      cases List.mem_append.mp ha with
      | inl h =>
        obtain ⟨f, hf, rfl⟩ := List.mem_map.mp h
        exact List.mem_append_left _ (List.mem_map.mpr ⟨f, List.mem_eraseDups.mpr hf, rfl⟩)
      | inr h => exact List.mem_append_right _ h)
    simp only [List.length_append, List.length_map, length_ids, List.length_singleton] at this
    exact this
  have hvars_ge : n + 1 ≤ ctx.vars.length := by
    have := nodup_length_le (nodup_ids 0 (n + 1)) (m := ctx.vars)
      (fun x hx => (qfam_vars K n _).mpr hx)
    rw [length_ids] at this; exact this
  constructor
  · have hc := searchCost_le hs h0 D
    have hI : isize ctx X ≤ n + 1 := by
      unfold isize; rw [hhidx, hvidx]; omega
    refine Nat.le_trans hc ?_
    have h1 : 1 + (D + 1) * (findAlias ctx X D 0).length ≤ D + 2 := by
      have := Nat.mul_le_mul_left (D + 1) hout; omega
    have h2 : isize ctx X + ctx.cells.length * ctx.origins.length ≤ (n + 1) * (c + 2) := by
      rw [hU]
      have := Nat.mul_le_mul_right (n + 1) hcells_le
      rw [Nat.mul_comm (n + 1) (c + 2), Nat.add_mul (c + 1) 1]
      omega
    have h3 := Nat.mul_le_mul h1 h2
    have h4 : D * isize ctx X ≤ D * (n + 1) := Nat.mul_le_mul_left D hI
    have e : (n + 1) * ((D + 2) * (c + 2) + D) = (D + 2) * ((n + 1) * (c + 2)) + D * (n + 1) := by
      rw [Nat.mul_add (n + 1) ((D + 2) * (c + 2)) D, Nat.mul_left_comm (n + 1) (D + 2) (c + 2),
        Nat.mul_comm (n + 1) D]
    omega
  · unfold enumCost
    have h1 := pathsUpTo_length_ge ctx.cells D
    have h2 : (c + 1) ^ D ≤ ctx.cells.length ^ D := Nat.pow_le_pow_left hcells_ge D
    exact Nat.mul_le_mul hvars_ge (Nat.le_trans h2 h1)

/-! ## Examples -/

namespace QExamples

open DirectedAlias.Examples

/-- The O state after the field example. -/
def oField : Tbl × OState := analyzeProgO 2 fr pField []

/-- After `a.f = z; a = w`, `findAlias(z)` by search on the O state is `{z, x.f, y.f}`. -/
theorem field_findAlias_z :
    findAlias (progCtx 2 fr pField []) (den 2 oField.1 oField.2) 2 vz =
      [(vz, []), (vx, [.fld ff]), (vy, [.fld ff])] := by decide +kernel

/-- `forEachHeapAlias(x, [f])` on the field example: the prefix `[]` gives `{x}`, and the prefix
`[f]` gives `{z, x.f, y.f}`. -/
theorem field_heapAliases_x :
    heapAliases (progCtx 2 fr pField []) (den 2 oField.1 oField.2) 2 vx [.fld ff] =
      [[(vx, [])], [(vz, []), (vx, [.fld ff]), (vy, [.fld ff])]] := by decide +kernel

end QExamples

end DirectedAlias.Opt

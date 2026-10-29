import DirectedAlias.Opt.Cost

/-!
# Optimization O, part 7: the cost of the join and of the fixpoint test

Cost model of C (the sorted-merge model, the most favourable list model for C):
a union or an inclusion test of two sets costs the sum of the two lengths. C tests and joins
every universe key (`leCost`, `joinCost`, `loopCost`).

Cost model of O: the work counter of the node table. A union of two equal ids or a memo hit
costs 1. A miss costs at most `2 + 2 (|A| + |B|)`. An intern costs `|S| + 1`. Map lookups and
updates are free in this model (a persistent hash map does them in O(log n) or less).

Results:
* `jfold_work`: the O join costs at most 5 for each map key whose two values are set-equal,
  and at most `6 + 4 |U|` for the other keys.
* `loopCost_ge`: each C loop analysis costs at least the size of the loop entry state.
* `loop_copy_work`: an O loop with body `t := y` costs at most `20 |L| + 16 |U| + 24`, where `L`
  lists the universe keys.
* `loopFam_sep`: on the family (the state family, then `loop { t := 0 }`), C costs at least
  `(n + 1) (m + 1)` and O costs at most `20 (n + m + 3) + 4 (6 + 4 (m + 1))`.
-/

namespace DirectedAlias.Opt

open DirectedAlias

/-! ## Work lemmas of the table -/

/-- `put` does not change the work counter. -/
theorem Tbl.put_work (U : List Origin) (T : Tbl) (S : List Origin) (k : Option (Nat × Nat)) :
    (T.put U S k).2.work = T.work := by
  unfold Tbl.put
  simp only
  split <;> rfl

/-- An intern costs the size of the set plus one. -/
theorem Tbl.intern_work (U : List Origin) (T : Tbl) (S : List Origin) (k : Option (Nat × Nat)) :
    (T.intern U S k).2.work = T.work + (S.length + 1) := by
  unfold Tbl.intern
  rw [Tbl.put_work]; rfl

/-- An insert adds at most one element. -/
theorem length_insert_le' {α : Type} [DecidableEq α] (a : α) (l : List α) :
    (List.insert a l).length ≤ l.length + 1 := by
  unfold List.insert
  split
  · exact Nat.le_succ _
  · exact Nat.le_refl _

/-- The length of a union is at most the sum of the lengths. -/
theorem length_uni_le {α : Type} [DecidableEq α] : ∀ (l m : List α),
    (uni l m).length ≤ l.length + m.length
  | [], m => by simp [uni]
  | a :: l, m => by
    have ih := length_uni_le l m
    simp only [uni, List.foldr_cons] at ih ⊢
    have := length_insert_le' a (l.foldr List.insert m)
    simp only [List.length_cons]
    omega

/-- A node of a good table has at most as many members as the universe. -/
theorem Tbl.Good.mem_length {U : List Origin} {T : Tbl} (g : T.Good U) (i : Nat) :
    (T.mem i).length ≤ U.length := by
  rw [← g.mem_canonical i]
  exact List.length_filter_le _ _

/-- A union of a node with itself costs one unit. -/
theorem Tbl.union_self_work (U : List Origin) (T : Tbl) (a : Nat) :
    (T.union U a a).2.work = T.work + 1 := by
  simp [Tbl.union, Tbl.tick]

/-- A union costs at most `2 + 2 (|A| + |B|)`. -/
theorem Tbl.union_work (U : List Origin) (T : Tbl) (a b : Nat) :
    (T.union U a b).2.work ≤ T.work + 2 + 2 * ((T.mem a).length + (T.mem b).length) := by
  unfold Tbl.union
  split
  · simp only [Tbl.tick]; omega
  · cases mlook T.memo (mkey a b) with
    | some c => simp only [Tbl.tick]; omega
    | none =>
      simp only
      have h1 := Tbl.intern_work U (T.tick (1 + (T.mem a).length + (T.mem b).length))
        (uni (T.mem a) (T.mem b)) (some (a, b))
      have h2 := length_uni_le (T.mem a) (T.mem b)
      have h3 : (T.tick (1 + (T.mem a).length + (T.mem b).length)).work =
          T.work + (1 + (T.mem a).length + (T.mem b).length) := rfl
      show (Tbl.intern U _ _ _).2.work ≤ _
      omega

/-- The default content of a key has at most one origin. -/
theorem dflt_length_le (K : Nat) (k : Key) : (dflt K k).length ≤ 1 := by
  cases k with
  | v x => exact Nat.zero_le _
  | h o c =>
    show (adefault K o c).length ≤ 1
    cases o <;> simp only [adefault, List.length_cons, List.length_nil] <;> omega

/-- `getId` costs at most two units. -/
theorem getId_work (ctx : Ctx) (T : Tbl) (st : OState) (k : Key) :
    (getId ctx T st k).2.work ≤ T.work + 2 := by
  unfold getId
  split
  · exact Nat.le_add_right _ _
  · rw [Tbl.intern_work]; have := dflt_length_le ctx.K k; omega

/-! ## The cost of the O join -/

/-- The per-key cost bound of the O join: 5 if the two values are set-equal, else
`6 + 4 |U|`. -/
def keyCost (ctx : Ctx) (T : Tbl) (s1 s2 : OState) (k : Key) : Nat :=
  if subB (val ctx.K T s1 k) (val ctx.K T s2 k) && subB (val ctx.K T s2 k) (val ctx.K T s1 k)
  then 5 else 6 + 4 * ctx.origins.length

/-- The O join loop costs at most the sum of the per-key cost bounds. -/
theorem jfold_work {ctx : Ctx} (cc : CtxClosed ctx) {s1 s2 : OState} :
    ∀ (ks : List Key) {T : Tbl} {out : OState} {ch : Bool}, T.Good ctx.origins →
      EntOK ctx T s1 → EntOK ctx T s2 → (∀ k ∈ ks, InU ctx k) →
      (jfold ctx s1 s2 ks T out ch).1.work ≤
        T.work + (ks.map (keyCost ctx T s1 s2)).sum
  | [], T, _, _, _, _, _, _ => by simp [jfold]
  | k :: ks, T, out, ch, g, h1, h2, hks => by
    have hk : InU ctx k := hks k List.mem_cons_self
    obtain ⟨ga, ea, ia, ma⟩ := getId_spec cc g h1 hk
    have wa := getId_work ctx T s1 k
    simp only [jfold]
    generalize getId ctx T s1 k = a at ga ea ia ma wa
    obtain ⟨gb, eb, ib, mb⟩ := getId_spec cc ga (h2.ext ea) hk
    have wb := getId_work ctx a.2 s2 k
    generalize getId ctx a.2 s2 k = b at gb eb ib mb wb
    have iab : a.1 < b.2.size := Nat.lt_of_lt_of_le ia eb.size_le
    obtain ⟨gu, eu, _, _⟩ := Tbl.union_spec gb iab ib
    have wu := Tbl.union_work ctx.origins b.2 a.1 b.1
    have wself : a.1 = b.1 → (b.2.union ctx.origins a.1 b.1).2.work = b.2.work + 1 := by
      intro h; rw [← h]; exact Tbl.union_self_work _ _ _
    have hA : SetEq (b.2.mem a.1) (val ctx.K T s1 k) := by rw [eb.mem_eq ia]; exact ma
    have hB : SetEq (b.2.mem b.1) (val ctx.K T s2 k) := by rw [← val_ext h2 ea]; exact mb
    have la := gb.mem_length a.1
    have lb := gb.mem_length b.1
    generalize b.2.union ctx.origins a.1 b.1 = u at gu eu wu wself
    have eT : T.Ext u.2 := ea.trans (eb.trans eu)
    have ih := jfold_work cc ks gu (h1.ext eT) (h2.ext eT)
      (fun k' hk' => hks k' (List.mem_cons_of_mem _ hk')) (out := oset out k u.1)
      (ch := ch || decide (u.1 ≠ a.1))
    have hcost : ∀ k', keyCost ctx u.2 s1 s2 k' = keyCost ctx T s1 s2 k' := by
      intro k'; simp only [keyCost, val_ext h1 eT, val_ext h2 eT]
    rw [show keyCost ctx u.2 s1 s2 = keyCost ctx T s1 s2 from funext hcost] at ih
    simp only [List.map_cons, List.sum_cons]
    have hk1 : u.2.work ≤ T.work + keyCost ctx T s1 s2 k := by
      unfold keyCost
      split
      · rename_i heq
        simp only [Bool.and_eq_true] at heq
        have hseq : SetEq (b.2.mem a.1) (b.2.mem b.1) := by
          intro o
          constructor
          · intro ho
            exact (hB o).mpr (subB_iff.mp heq.1 o ((hA o).mp ho))
          · intro ho
            exact (hA o).mpr (subB_iff.mp heq.2 o ((hB o).mp ho))
        have := wself (Tbl.id_inj gb iab ib hseq)
        omega
      · have : 2 * ((b.2.mem a.1).length + (b.2.mem b.1).length) ≤ 4 * ctx.origins.length := by
          omega
        omega
    omega

/-- The O join costs at most the sum of the per-key cost bounds over the keys of both maps. -/
theorem joinO_work {ctx : Ctx} (cc : CtxClosed ctx) {T : Tbl} (g : T.Good ctx.origins)
    {s1 s2 : OState} (h1 : EntOK ctx T s1) (h2 : EntOK ctx T s2) :
    (joinO ctx T s1 s2).1.work ≤
      T.work + ((s1.map Prod.fst ++ s2.map Prod.fst).map (keyCost ctx T s1 s2)).sum := by
  apply jfold_work cc _ g h1 h2
  intro k hk
  cases List.mem_append.mp hk with
  | inl h => exact inU_of_key h1 h
  | inr h => exact inU_of_key h2 h

/-! ## The cost of C loops -/

/-- The C cost of an inclusion test over the universe (sorted-merge model). -/
def leCost (ctx : Ctx) (X Y : AState) : Nat :=
  ((ukeys ctx).map (fun k => (cval X k).length + (cval Y k).length)).sum

/-- The C cost of a join over the universe (sorted-merge model). -/
def joinCost (ctx : Ctx) (X Y : AState) : Nat :=
  ((ukeys ctx).map (fun k => (cval X k).length + (cval Y k).length)).sum

/-- The C cost of the loop iteration: the tests and the joins (the body cost is not counted). -/
def loopCost (ctx : Ctx) (F : AState → AState) : Nat → AState → Nat
  | 0, Y => csize ctx Y
  | n + 1, Y =>
    leCost ctx (F Y) Y +
      (if leOn ctx (F Y) Y then 0 else joinCost ctx Y (F Y) + loopCost ctx F n (join Y (F Y)))

/-- The C inclusion test costs at least the size of its second state. -/
theorem csize_le_leCost (ctx : Ctx) (X Y : AState) : csize ctx Y ≤ leCost ctx X Y := by
  unfold csize leCost
  induction ukeys ctx with
  | nil => exact Nat.le_refl _
  | cons k ks ih => simp only [List.map_cons, List.sum_cons]; omega

/-- Each C loop analysis costs at least the size of the loop entry state. -/
theorem loopCost_ge (ctx : Ctx) (F : AState → AState) (n : Nat) (Y : AState) :
    csize ctx Y ≤ loopCost ctx F (n + 1) Y := by
  simp only [loopCost]
  have := csize_le_leCost ctx (F Y) Y
  omega

/-! ## The cost of the O loop with a copy body -/

/-- The value of each key after `copyO`. -/
theorem copyO_val (K : Nat) (T : Tbl) (st : OState) (x y : Var) (k : Key) :
    val K (copyO T st x y).1 (copyO T st x y).2 k =
      if k = .v x then val K T st (.v y) else val K T st k := by
  unfold copyO
  cases ho : oget st (.v y) with
  | some i =>
    simp only
    rw [val_oset]
    split
    · simp [val, ho]
    · rfl
  | none =>
    simp only
    rw [val_oerase]
    split
    · simp [val, ho, dflt]
    · rfl

/-- `copyO` does not change the table. -/
theorem copyO_tbl (T : Tbl) (st : OState) (x y : Var) : (copyO T st x y).1 = T := by
  unfold copyO; split <;> rfl

/-- A sum of per-key costs: each key other than `k0` costs at most `a`, and `k0` costs at most
`b`. -/
theorem sum_cost_le {f : Key → Nat} {a b : Nat} {k0 : Key} (h1 : ∀ k, k ≠ k0 → f k ≤ a)
    (h2 : f k0 ≤ b) : ∀ (ks : List Key), (ks.map f).sum ≤ a * ks.length + b * ks.count k0
  | [] => by simp
  | k :: ks => by
    have ih := sum_cost_le h1 h2 ks
    simp only [List.map_cons, List.sum_cons, List.length_cons, List.count_cons]
    by_cases hk : k = k0
    · subst hk
      simp only [beq_self_eq_true, ite_true, Nat.mul_succ]
      omega
    · have : (k == k0) = false := by simp [hk]
      simp only [this, Bool.false_eq_true, ite_false, Nat.add_zero, Nat.mul_succ]
      have := h1 k hk
      omega

/-- A key occurs at most one time in the key list of a valid map. -/
theorem count_le_one_of_nodup {α : Type} [DecidableEq α] (k : α) :
    ∀ {l : List α}, l.Nodup → l.count k ≤ 1
  | [], _ => Nat.zero_le _
  | a :: l, h => by
    rw [List.nodup_cons] at h
    rw [List.count_cons]
    by_cases ha : a = k
    · subst ha
      have : l.count a = 0 := List.count_eq_zero.mpr h.1
      simp [this]
    · have : (a == k) = false := by simp [ha]
      simp only [this, Bool.false_eq_true, ite_false, Nat.add_zero]
      exact count_le_one_of_nodup k h.2

/-- A key occurs at most one time in the key list of a valid map. -/
theorem count_keys_le {ctx : Ctx} {T : Tbl} {st : OState} (h : EntOK ctx T st) (k : Key) :
    (st.map Prod.fst).count k ≤ 1 :=
  count_le_one_of_nodup k h.nodup

/-- A valid map has at most as many entries as a list that holds every universe key. -/
theorem EntOK.length_le_of {ctx : Ctx} {T : Tbl} {st : OState} (h : EntOK ctx T st)
    {L : List Key} (hL : ∀ k, InU ctx k → k ∈ L) : st.length ≤ L.length := by
  have := nodup_length_le h.nodup (fun k hk => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hk
    exact hL _ (h.ent p hp).2)
  rw [List.length_map] at this
  exact this

/-- One step of the O loop. -/
theorem loopO_step (ctx : Ctx) (f : Tbl → OState → Tbl × OState) (n : Nat) (T : Tbl)
    (st : OState) : loopO ctx f (n + 1) T st =
      if (joinO ctx (f T st).1 st (f T st).2).2.2 then
        loopO ctx f n (joinO ctx (f T st).1 st (f T st).2).1
          (joinO ctx (f T st).1 st (f T st).2).2.1
      else ((joinO ctx (f T st).1 st (f T st).2).1, st) := rfl

/-- `copyO` keeps the map valid. -/
theorem copyO_ok {ctx : Ctx} {T : Tbl} {st : OState} (h : EntOK ctx T st) {t y : Var}
    (ht : t ∈ ctx.vars) : EntOK ctx T (copyO T st t y).2 := by
  unfold copyO
  cases ho : oget st (.v y) with
  | some i => exact h.oset (h.ent _ (oget_mem ho)).1 ht
  | none => exact h.oerase _

/-- The cost bound of one O join after a copy `t := y`: each key except `t` costs at most 5. -/
theorem copy_join_work {ctx : Ctx} (cc : CtxClosed ctx) {T : Tbl} (g : T.Good ctx.origins)
    {st : OState} (h : EntOK ctx T st) {t y : Var} (ht : t ∈ ctx.vars)
    {L : List Key} (hL : ∀ k, InU ctx k → k ∈ L) :
    (joinO ctx T st (copyO T st t y).2).1.work ≤
      T.work + (10 * L.length + 2 * (6 + 4 * ctx.origins.length)) := by
  have hs2 := copyO_ok h (y := y) ht
  have hrv : ∀ k, val ctx.K T (copyO T st t y).2 k =
      if k = .v t then val ctx.K T st (.v y) else val ctx.K T st k := by
    intro k; have := copyO_val ctx.K T st t y k; rw [copyO_tbl] at this; exact this
  have w1 := joinO_work cc g h hs2
  generalize (copyO T st t y).2 = s2 at hs2 hrv w1
  have c1 : ∀ k, k ≠ .v t → keyCost ctx T st s2 k ≤ 5 := by
    intro k hk
    simp only [keyCost, hrv k, ite_eq_right hk]
    have : subB (val ctx.K T st k) (val ctx.K T st k) = true := subB_iff.mpr (fun _ h => h)
    simp [this]
  have c1t : keyCost ctx T st s2 (.v t) ≤ 6 + 4 * ctx.origins.length := by
    unfold keyCost; split <;> omega
  have s1 := sum_cost_le c1 c1t (st.map Prod.fst ++ s2.map Prod.fst)
  have cnt1 : (st.map Prod.fst ++ s2.map Prod.fst).count (.v t) ≤ 2 := by
    rw [List.count_append]
    have := count_keys_le h (.v t); have := count_keys_le hs2 (.v t); omega
  have len1 : (st.map Prod.fst ++ s2.map Prod.fst).length ≤ 2 * L.length := by
    rw [List.length_append, List.length_map, List.length_map]
    have := h.length_le_of hL; have := hs2.length_le_of hL; omega
  have : (6 + 4 * ctx.origins.length) * (st.map Prod.fst ++ s2.map Prod.fst).count (.v t) ≤
      (6 + 4 * ctx.origins.length) * 2 := Nat.mul_le_mul_left _ cnt1
  have : 5 * (st.map Prod.fst ++ s2.map Prod.fst).length ≤ 5 * (2 * L.length) :=
    Nat.mul_le_mul_left _ len1
  omega

/-- An O loop with body `t := y` stops after at most two iterations. Its cost is at most
`20 |L| + 4 (6 + 4 |U|)`, where `L` lists the universe keys. -/
theorem loop_copy_work {ctx : Ctx} (cc : CtxClosed ctx) {T : Tbl} (g : T.Good ctx.origins)
    {st : OState} (h : EntOK ctx T st) {t y : Var} (ht : t ∈ ctx.vars)
    {L : List Key} (hL : ∀ k, InU ctx k → k ∈ L) (n : Nat) :
    (loopO ctx (fun T st => copyO T st t y) (n + 2) T st).1.work ≤
      T.work + (20 * L.length + 4 * (6 + 4 * ctx.origins.length)) := by
  have hs2 := copyO_ok h (y := y) ht
  have hrv : ∀ k, val ctx.K T (copyO T st t y).2 k =
      if k = .v t then val ctx.K T st (.v y) else val ctx.K T st k := by
    intro k; have := copyO_val ctx.K T st t y k; rw [copyO_tbl] at this; exact this
  have w1 := copy_join_work cc g h (y := y) ht hL
  obtain ⟨g1, _, h3, m1, _⟩ := joinO_spec cc g h hs2
  rw [loopO_step]
  simp only [copyO_tbl]
  generalize (copyO T st t y).2 = s2 at hs2 hrv w1 m1 h3 g1
  generalize joinO ctx T st s2 = j at g1 h3 m1 w1
  split
  · rw [loopO_step]
    simp only [copyO_tbl]
    have w2 := copy_join_work cc g1 h3 (y := y) ht hL
    have hs3 := copyO_ok h3 (y := y) ht
    have hqv : ∀ k, val ctx.K j.1 (copyO j.1 j.2.1 t y).2 k =
        if k = .v t then val ctx.K j.1 j.2.1 (.v y) else val ctx.K j.1 j.2.1 k := by
      intro k; have := copyO_val ctx.K j.1 j.2.1 t y k; rw [copyO_tbl] at this; exact this
    have hflag : (joinO ctx j.1 j.2.1 (copyO j.1 j.2.1 t y).2).2.2 = false := by
      obtain ⟨_, _, _, _, c⟩ := joinO_spec cc g1 h3 hs3
      cases hf : (joinO ctx j.1 j.2.1 (copyO j.1 j.2.1 t y).2).2.2 with
      | false => rfl
      | true =>
        obtain ⟨k, _, hk⟩ := c.mp hf
        exfalso
        have hsub : val ctx.K j.1 (copyO j.1 j.2.1 t y).2 k ⊆ val ctx.K j.1 j.2.1 k := by
          rw [hqv k]
          split
          · rename_i hkt
            subst hkt
            intro o ho
            have hy1 := (m1 (.v y) o).mp ho
            apply (m1 (.v t) o).mpr
            rw [mem_uni] at hy1 ⊢
            rw [hrv (.v t), ite_eq_left rfl]
            by_cases hyt : (Key.v y) = Key.v t
            · rw [hrv (.v y), ite_eq_left hyt] at hy1
              exact Or.inr (hy1.elim id id)
            · rw [hrv (.v y), ite_eq_right hyt] at hy1
              exact Or.inr (hy1.elim id id)
          · exact fun _ h => h
        rw [subB_iff.mpr hsub] at hk; cases hk
    rw [hflag]
    simp only [Bool.false_eq_true, ite_false]
    omega
  · show j.1.work ≤ _
    omega

/-! ## The loop family -/

/-- The loop body of the family: `t := 0` with `t = n + 1`. -/
def loopBody (n : Nat) : Prog := .stmt (.copy (n + 1) 0)

/-- The loop family: the state family, then `loop { t := 0 }`. -/
def loopFam (n m : Nat) : Prog := .seq (fam n m) (.loop (loopBody n))

/-- The statements of the loop family. -/
theorem loopFam_stmts (n m : Nat) : (loopFam n m).stmts =
    (0 :: ids 1 m).map (Stmt.new 0) ++ (ids 1 n).map (fun b => Stmt.copy b 0) ++
      [Stmt.copy (n + 1) 0] := by
  simp only [loopFam, loopBody, Prog.stmts, fam_stmts]

/-- The variables of the loop family are `0 .. n + 1`. -/
theorem loopFam_vars (n m : Nat) {x : Var} :
    x ∈ (loopFam n m).vars → x ∈ 0 :: ids 1 (n + 1) := by
  intro hx
  simp only [Prog.vars, loopFam_stmts, List.flatMap_append, List.mem_append,
    List.mem_flatMap, List.mem_map] at hx
  rcases hx with (⟨st, ⟨s, _, rfl⟩, hx⟩ | ⟨st, ⟨b, hb, rfl⟩, hx⟩) | ⟨st, hst, hx⟩
  · simp only [Stmt.vars, List.mem_singleton] at hx; exact hx ▸ List.mem_cons_self
  · simp only [Stmt.vars, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · have := mem_ids.mp hb
      exact List.mem_cons_of_mem _ (mem_ids.mpr ⟨this.1, by omega⟩)
    · exact List.mem_cons_self
  · simp only [List.mem_singleton] at hst
    subst hst
    simp only [Stmt.vars, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact List.mem_cons_of_mem _ (mem_ids.mpr ⟨by omega, by omega⟩)
    · exact List.mem_cons_self

/-- The origins of the loop family context are the allocations of the sites `0 .. m`. -/
theorem loopFam_origins (K n m : Nat) :
    (progCtx K fr0 (loopFam n m) []).origins = (0 :: ids 1 m).map Origin.alloc := by
  have h1 : (loopFam n m).freshSites = [] := by
    simp only [Prog.freshSites, loopFam_stmts, List.filterMap_append, List.filterMap_map]
    have e1 : (Stmt.freshSite? ∘ Stmt.new 0) = fun _ => none := rfl
    have e2 : (Stmt.freshSite? ∘ fun b => Stmt.copy b 0) = fun _ => none := rfl
    rw [e1, e2, filterMap_none, filterMap_none]; rfl
  have h2 : (loopFam n m).callSites = [] := by
    simp only [Prog.callSites, loopFam_stmts, List.filterMap_append, List.filterMap_map]
    have e1 : (Stmt.callSite? ∘ Stmt.new 0) = fun _ => none := rfl
    have e2 : (Stmt.callSite? ∘ fun b => Stmt.copy b 0) = fun _ => none := rfl
    rw [e1, e2, filterMap_none, filterMap_none]; rfl
  have h3 : (loopFam n m).newSites = 0 :: ids 1 m := by
    simp only [Prog.newSites, loopFam_stmts, List.filterMap_append, List.filterMap_map]
    have e1 : (Stmt.newSite? ∘ Stmt.new 0) = some := rfl
    have e2 : (Stmt.newSite? ∘ fun b => Stmt.copy b 0) = fun _ => none := rfl
    rw [e1, e2, List.filterMap_some, filterMap_none, List.append_nil]
    simp only [List.filterMap_cons, List.filterMap_nil, Stmt.newSite?, List.append_nil]
  simp only [progCtx, Ctx.ofProg, originsOf, h1, h2, h3, fr0, Frame.roots, List.map_nil,
    List.append_nil, List.flatMap_nil, List.nil_append]

/-- The cells of the loop family context: only the array element. -/
theorem loopFam_cells (K n m : Nat) : (progCtx K fr0 (loopFam n m) []).cells = [.elem] := by
  have h : (loopFam n m).fields = [] := by
    simp only [Prog.fields, loopFam_stmts, List.flatMap_append, List.flatMap_map]
    have e1 : (Stmt.fields ∘ Stmt.new 0) = fun _ => [] := rfl
    have e2 : (Stmt.fields ∘ fun b => Stmt.copy b 0) = fun _ => [] := rfl
    simp only [Function.comp_def] at e1 e2
    rw [e1, e2, flatMap_nil', flatMap_nil']; rfl
  simp only [progCtx, Ctx.ofProg, cellsOf, h, List.append_nil]
  rfl

/-- After the state family, C needs at least `(n + 1) (m + 1)` set elements in each context
that has the variables `0 .. n`. -/
theorem fam_csize_in (ctx : Ctx) (n m : Nat) (hv : ∀ x ∈ 0 :: ids 1 n, x ∈ ctx.vars)
    (X0 : AState) : (n + 1) * (m + 1) ≤ csize ctx (analyze ctx (fam n m) X0) := by
  let X := analyze ctx (fam n m) X0
  have h0 : (0 : Var) ∉ ids 1 n := fun h => by have := (mem_ids.mp h).1; omega
  have henv : ∀ x ∈ 0 :: ids 1 n, ∀ o, o ∈ X.env x ↔ o ∈ (0 :: ids 1 m).map Origin.alloc := by
    intro x hx o
    show o ∈ (analyze ctx (copies 0 (ids 1 n)) (analyze ctx (chainJ 0 0 (ids 1 m)) X0)).env x ↔ _
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
  have hnd : (0 :: ids 1 n).Nodup := by
    rw [List.nodup_cons]; exact ⟨h0, nodup_ids 1 n⟩
  have s1 : (0 :: ids 1 n).length * (m + 1) ≤
      ((0 :: ids 1 n).map (fun x => (X.env x).length)).sum :=
    sum_ge_length_mul _ _ _ hlen
  have s2 : ((0 :: ids 1 n).map (fun x => (X.env x).length)).sum ≤
      (ctx.vars.map (fun x => (X.env x).length)).sum :=
    sum_le_of_nodup_sub _ hnd hv
  have s3 : (ctx.vars.map (fun x => (X.env x).length)).sum ≤ csize ctx X := by
    unfold csize ukeys
    rw [List.map_append, List.sum_append, List.map_map]
    exact Nat.le_add_right _ _
  simp only [List.length_cons, length_ids] at s1
  exact Nat.le_trans s1 (Nat.le_trans s2 s3)

/-- The loop separation on the family. C pays at least `(n + 1) (m + 1)` for the loop tests and
joins. O pays at most `20 (n + m + 3) + 4 (6 + 4 (m + 1))` table work for the whole loop. -/
theorem loopFam_sep (K n m : Nat) :
    (n + 1) * (m + 1) ≤ loopCost (progCtx K fr0 (loopFam n m) [])
        (analyze (progCtx K fr0 (loopFam n m) []) (loopBody n))
        (progCtx K fr0 (loopFam n m) []).fuel
        (analyze (progCtx K fr0 (loopFam n m) []) (fam n m) (ainit K fr0)) ∧
      (analyzeProgO K fr0 (loopFam n m) []).1.work ≤
        (analyzeO (progCtx K fr0 (loopFam n m) []) (fam n m)
          (initO (progCtx K fr0 (loopFam n m) []) fr0).1
          (initO (progCtx K fr0 (loopFam n m) []) fr0).2).1.work +
          (20 * (n + m + 3) + 4 * (6 + 4 * (m + 1))) := by
  have hvars : ∀ x, x ∈ (progCtx K fr0 (loopFam n m) []).vars ↔ x ∈ (loopFam n m).vars := by
    intro x
    show x ∈ ((loopFam n m).vars ++ fr0.vars).eraseDups ↔ _
    rw [List.mem_eraseDups]; simp [fr0, Frame.vars]
  have hfuel : ∃ k, (progCtx K fr0 (loopFam n m) []).fuel = k + 2 := by
    have hU : 1 ≤ (progCtx K fr0 (loopFam n m) []).origins.length := by
      rw [loopFam_origins]; simp
    have hV : 1 ≤ (progCtx K fr0 (loopFam n m) []).vars.length := by
      have h0 : (0 : Var) ∈ (progCtx K fr0 (loopFam n m) []).vars := by
        rw [hvars]
        simp only [Prog.vars, loopFam_stmts, List.flatMap_append, List.mem_append,
          List.mem_flatMap]
        exact Or.inl (Or.inl ⟨.new 0 0, List.mem_cons_self, by simp [Stmt.vars]⟩)
      cases h : (progCtx K fr0 (loopFam n m) []).vars with
      | nil => rw [h] at h0; cases h0
      | cons _ _ => simp
    have hf : (progCtx K fr0 (loopFam n m) []).fuel =
        ((progCtx K fr0 (loopFam n m) []).vars.length +
          (progCtx K fr0 (loopFam n m) []).origins.length *
            (progCtx K fr0 (loopFam n m) []).cells.length) *
          (progCtx K fr0 (loopFam n m) []).origins.length + 1 := rfl
    have : 1 ≤ ((progCtx K fr0 (loopFam n m) []).vars.length +
          (progCtx K fr0 (loopFam n m) []).origins.length *
            (progCtx K fr0 (loopFam n m) []).cells.length) *
          (progCtx K fr0 (loopFam n m) []).origins.length :=
      Nat.mul_le_mul (Nat.le_trans hV (Nat.le_add_right _ _)) hU
    exact ⟨((progCtx K fr0 (loopFam n m) []).vars.length +
          (progCtx K fr0 (loopFam n m) []).origins.length *
            (progCtx K fr0 (loopFam n m) []).cells.length) *
          (progCtx K fr0 (loopFam n m) []).origins.length - 1, by rw [hf]; omega⟩
  obtain ⟨k, hk⟩ := hfuel
  constructor
  · rw [hk]
    refine Nat.le_trans ?_ (loopCost_ge _ _ (k + 1) _)
    apply fam_csize_in
    intro x hx
    rw [hvars]
    simp only [Prog.vars, loopFam_stmts, List.flatMap_append, List.mem_append, List.mem_flatMap,
      List.mem_map]
    cases List.mem_cons.mp hx with
    | inl h => subst h; exact Or.inl (Or.inl ⟨.new 0 0, ⟨0, List.mem_cons_self, rfl⟩,
        by simp [Stmt.vars]⟩)
    | inr h => exact Or.inl (Or.inr ⟨.copy x 0, ⟨x, h, rfl⟩, by simp [Stmt.vars]⟩)
  · have cc := ctxClosed_ofProg K fr0 (loopFam n m) []
    have hfv : ∀ x ∈ fr0.vars, x ∈ (progCtx K fr0 (loopFam n m) []).vars := by
      intro x hx; simp [fr0, Frame.vars] at hx
    obtain ⟨g0, r0⟩ := initO_rel (ctx := progCtx K fr0 (loopFam n m) []) fr0
      (supp_ainit K fr0 (loopFam n m) []) hfv
    obtain ⟨g1, _, r1⟩ := analyzeO_rel cc (fam n m) _ _ _
      (fun st hst => progOK_ofProg K fr0 (loopFam n m) [] st
        (by simp only [loopFam, Prog.stmts]; exact List.mem_append_left _ hst)) g0 r0
    have ht : n + 1 ∈ (progCtx K fr0 (loopFam n m) []).vars := by
      rw [hvars]
      simp only [Prog.vars, loopFam_stmts, List.flatMap_append, List.mem_append,
        List.mem_flatMap]
      exact Or.inr ⟨.copy (n + 1) 0, List.mem_singleton_self _, by simp [Stmt.vars]⟩
    let L : List Key := (0 :: ids 1 (n + 1)).map Key.v ++
      ((0 :: ids 1 m).map Origin.alloc).flatMap (fun o => [Key.h o .elem])
    have hL : ∀ k, InU (progCtx K fr0 (loopFam n m) []) k → k ∈ L := by
      intro k hk
      cases k with
      | v x =>
        have hx : x ∈ (loopFam n m).vars := (hvars x).mp hk
        exact List.mem_append_left _ (List.mem_map.mpr ⟨x, loopFam_vars n m hx, rfl⟩)
      | h o c =>
        obtain ⟨ho, hc⟩ := hk
        rw [loopFam_origins] at ho
        rw [loopFam_cells] at hc
        simp only [List.mem_singleton] at hc
        subst hc
        exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨o, ho, List.mem_singleton_self _⟩)
    have hLlen : L.length = (n + 2) + (m + 1) := by
      simp only [L, List.length_append, List.length_map, length_flatMap_single, List.length_cons,
        length_ids]
    have hw := loop_copy_work cc g1 r1.ent (y := 0) ht hL k
    have hU : (progCtx K fr0 (loopFam n m) []).origins.length = m + 1 := by
      rw [loopFam_origins]; simp [length_ids]
    rw [hLlen] at hw
    show (loopO _ (analyzeO _ (loopBody n)) _ _ _).1.work ≤ _
    rw [hk]
    have : analyzeO (progCtx K fr0 (loopFam n m) []) (loopBody n) =
        fun T st => copyO T st (n + 1) 0 := rfl
    rw [this]
    simp only [progCtx] at hw hU ⊢
    rw [hU] at hw
    omega

end DirectedAlias.Opt

import DirectedAlias.Opt.BlockOnly
import DirectedAlias.Opt.Cost

/-!
# The cost of a call in design BO, design CN and the per-cell design

The cost model is the work counter of the node table (`Opt/Table.lean`): an intern costs the size
of the set plus one, a memoized union costs one unit on a hit and the merge on a miss. The
closure `closeN` is the same function in design BO and design CN (it runs on the denotation of
the O state), so it is not in the counter; only the work after the closure is compared.

Results (`U` is the origin universe, `R` the closure, `V` the contents of the covered cells):
* `callWithO_work`: the call of design BO costs at most `(|R| + 5 + 4|U|) + (|V| + 5 + 4|U|)`
  (two interns and two memoized unions on the reserved keys) plus `6 + 4|U|` for each covered
  universe cell whose value is EMPTY.
* `callBOO_frame`: the call of design BO changes no key of the map except the two reserved keys
  and the covered empty cells; `callBOO_zero_writes`: if no covered universe cell is empty, the
  call writes NO heap key. `ostepBO_call_frame`: the call statement also changes the result
  variable, and nothing else (for a call site that is not an allocation site).
* `havocWithO_work`, `havocWithO_work_ge`: the call of design CN costs at most
  `(|R| + 5 + 4|U|) + (6 + 4|U|)` for each universe cell of each covered origin, and at least
  one unit for each of these cells.
* `havocHRO_work_ge`: the per-cell call costs at least one unit, and at most `6 + 4|U|`, for
  each universe cell of each reachable origin.
* `separation`: a family with `n` fields written on a reached argument and `m` calls: design BO
  writes no heap key, design CN writes at least `m n` heap keys, and the per-cell design writes
  at least `m^2 n^2` heap keys.
* `expB_prefixes`, `uniqueBO_prefixes`: the uniqueness test of design BO is one membership test
  in `Eval` and at most `K` membership tests in `Etree` (the proper prefixes of the origin).
* `sets_in_universe`, `callWith_xe_length`: both sets stay in the universe, and a call adds at
  most `|R|` origins to `Etree`.
* `astepBO_xe_grow`, `astepBO_xv_grow`: along a path, the two sets only grow (up to the renaming
  of `retire`); a join is their union. So they take part in the post-fixpoint test like any
  other key, and the fuel bound counts them as two more variable keys.
-/

namespace DirectedAlias.Opt.BlockOnly

open DirectedAlias DirectedAlias.Opt DirectedAlias.Opt.Rec DirectedAlias.Opt.HvRec
open DirectedAlias.Opt.CellNamed
open DirectedAlias.Sound.Recency DirectedAlias.Sound.HavocRecency DirectedAlias.Sound.CellNamed
open DirectedAlias.Sound.BlockOnly

/-! ## Work lemmas of the table -/

/-- A union costs at least one unit. -/
theorem Tbl.union_work_ge (U : List Origin) (T : Tbl) (a b : Nat) :
    T.work + 1 ≤ (T.union U a b).2.work := by
  unfold Tbl.union
  split
  · simp only [Tbl.tick]; omega
  · cases mlook T.memo (mkey a b) with
    | some c => simp only [Tbl.tick]; omega
    | none =>
      simp only
      have h1 := Tbl.intern_work U (T.tick (1 + (T.mem a).length + (T.mem b).length))
        (uni (T.mem a) (T.mem b)) (some (a, b))
      have h3 : (T.tick (1 + (T.mem a).length + (T.mem b).length)).work =
          T.work + (1 + (T.mem a).length + (T.mem b).length) := rfl
      show T.work + 1 ≤ (Tbl.intern U _ _ _).2.work
      omega

/-- `getId` costs nothing or one intern. -/
theorem getId_work_ge (ctx : Ctx) (T : Tbl) (st : OState) (k : Key) :
    T.work ≤ (getId ctx T st k).2.work := by
  unfold getId
  split
  · exact Nat.le_refl _
  · rw [Tbl.intern_work]; omega

/-- One `addKey` costs at least one unit (its union). -/
theorem addKey_work_ge (ctx : Ctx) (T : Tbl) (st : OState) (k : Key) (n : Nat) :
    T.work + 1 ≤ (addKey ctx T st k n).1.work := by
  unfold addKey
  simp only
  have w1 := getId_work_ge ctx T st k
  have w2 := Tbl.union_work_ge ctx.origins (getId ctx T st k).2 (getId ctx T st k).1 n
  omega

/-- `addSets` costs at least two units for each key: one intern and one union. -/
theorem addSets_work_ge (ctx : Ctx) (f : Key → List Origin) :
    ∀ (ks : List Key) (T : Tbl) (st : OState),
      T.work + 2 * ks.length ≤ (addSets ctx f T st ks).1.work
  | [], T, st => by simp [addSets]
  | k :: ks, T, st => by
    simp only [addSets]
    have w0 := Tbl.intern_work ctx.origins T (f k) none
    have w1 := addKey_work_ge ctx (T.intern ctx.origins (f k) none).2 st k
      (T.intern ctx.origins (f k) none).1
    have w2 := addSets_work_ge ctx f ks
      (addKey ctx (T.intern ctx.origins (f k) none).2 st k (T.intern ctx.origins (f k) none).1).1
      (addKey ctx (T.intern ctx.origins (f k) none).2 st k (T.intern ctx.origins (f k) none).1).2
    rw [List.length_cons]
    omega

/-- `addSets` costs at most the size of the added set plus `5 + 4 |U|` for each key. -/
theorem addSets_work_le {ctx : Ctx} (cc : CtxClosed ctx) (f : Key → List Origin) :
    ∀ (ks : List Key) {T : Tbl} {st : OState}, T.Good ctx.origins → EntOK ctx T st →
      (∀ k ∈ ks, InU ctx k) → (∀ k ∈ ks, f k ⊆ ctx.origins) →
      (addSets ctx f T st ks).1.work ≤
        T.work + (ks.map (fun k => (f k).length + 5 + 4 * ctx.origins.length)).sum
  | [], T, st, _, _, _, _ => by simp [addSets]
  | k :: ks, T, st, g, h, hks, hhv => by
    obtain ⟨g0, e0, i0, _⟩ := Tbl.intern_none_spec g (hhv k List.mem_cons_self)
    have w0 := Tbl.intern_work ctx.origins T (f k) none
    simp only [addSets]
    generalize T.intern ctx.origins (f k) none = n at g0 e0 i0 w0
    have w1 := Hv.addKey_work cc g0 (h.ext e0) (hks k List.mem_cons_self) n.1
    obtain ⟨g1, _, h1, _⟩ := addKey_spec cc g0 (h.ext e0) (hks k List.mem_cons_self) i0
    generalize addKey ctx n.2 st k n.1 = r at g1 h1 w1
    have w2 := addSets_work_le cc f ks g1 h1 (fun k' hk' => hks k' (List.mem_cons_of_mem _ hk'))
      (fun k' hk' => hhv k' (List.mem_cons_of_mem _ hk'))
    simp only [List.map_cons, List.sum_cons]
    omega

/-- `addSets` changes no key outside its key list. -/
theorem addSets_oget (ctx : Ctx) (f : Key → List Origin) :
    ∀ (ks : List Key) (T : Tbl) (st : OState) (k : Key), k ∉ ks →
      oget (addSets ctx f T st ks).2 k = oget st k
  | [], _, _, _, _ => rfl
  | k0 :: ks, T, st, k, hk => by
    simp only [addSets]
    rw [addSets_oget ctx f ks _ _ k (fun h => hk (List.mem_cons_of_mem _ h))]
    show oget (oset st k0 _) k = oget st k
    rw [oget_oset, ite_eq_right (fun (e : k = k0) => hk (e ▸ List.mem_cons_self))]

/-- The sum of a constant over a list. -/
theorem sum_const_of {α : Type} (F : α → Nat) (c : Nat) :
    ∀ (l : List α), (∀ a ∈ l, F a = c) → (l.map F).sum = l.length * c
  | [], _ => by simp
  | a :: l, h => by
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [h a List.mem_cons_self, sum_const_of F c l (fun b hb => h b (List.mem_cons_of_mem _ hb)),
      Nat.succ_mul]
    omega

/-! ## The call of design BO -/

section bo

variable {cb : CtxB} {T : Tbl} {st : OState} {E V : List Origin} {cov : Origin → Bool}

/-- The keys of the call of design BO are universe keys. -/
theorem callKeys_inU (hc : CtxBOK cb) : ∀ k ∈ callKeys cb T st cov, InU cb.cn.ctx k := by
  intro k hk
  simp only [callKeys, List.mem_cons] at hk
  rcases hk with rfl | rfl | h
  · exact hc.cn.xeIn
  · exact hc.xvIn
  · obtain ⟨o, c, rfl, h1, _, h3, _⟩ := mem_emptyKeys.mp h
    exact ⟨h1, h3⟩

/-- The sets of the call of design BO are in the universe. -/
theorem hvBO_sub (hc : CtxBOK cb) (hE : E ⊆ cb.cn.ctx.origins) (hV : V ⊆ cb.cn.ctx.origins) :
    ∀ k ∈ callKeys cb T st cov, hvBO cb E V k ⊆ cb.cn.ctx.origins := by
  intro k hk
  simp only [callKeys, List.mem_cons] at hk
  rcases hk with rfl | rfl | h
  · intro a ha; simp only [hvBO, ite_true] at ha; exact hE ha
  · intro a ha; simp only [hvBO, ite_eq_right hc.xvNe] at ha; exact hV ha
  · obtain ⟨o, c, rfl, h1, _, h3, _⟩ := mem_emptyKeys.mp h
    intro a ha
    simp only [hvBO, List.mem_singleton] at ha
    subst ha
    exact hc.cn.childIn o h1 c h3

/-- COST OF THE CALL OF DESIGN BO (after the closure): two interns and two memoized unions on
the reserved keys, and `6 + 4 |U|` for each covered universe cell whose value is empty. -/
theorem callWithO_work (hc : CtxBOK cb) (g : T.Good cb.cn.ctx.origins)
    (h : EntOK cb.cn.ctx T st) (hE : E ⊆ cb.cn.ctx.origins) (hV : V ⊆ cb.cn.ctx.origins) :
    (callWithO cb T st E V cov).1.work ≤ T.work + (E.length + 5 + 4 * cb.cn.ctx.origins.length) +
      (V.length + 5 + 4 * cb.cn.ctx.origins.length) +
      (emptyKeys cb T st cov).length * (6 + 4 * cb.cn.ctx.origins.length) := by
  have w := addSets_work_le (ctxClosed_of hc) (hvBO cb E V) (callKeys cb T st cov) g h
    (callKeys_inU hc) (hvBO_sub hc hE hV)
  have hs : ((emptyKeys cb T st cov).map
      (fun k => (hvBO cb E V k).length + 5 + 4 * cb.cn.ctx.origins.length)).sum =
      (emptyKeys cb T st cov).length * (6 + 4 * cb.cn.ctx.origins.length) := by
    apply sum_const_of
    intro k hk
    obtain ⟨o, c, rfl, _⟩ := mem_emptyKeys.mp hk
    simp only [hvBO, List.length_singleton] <;> omega
  have e1 : hvBO cb E V (.v cb.cn.xe) = E := by simp [hvBO]
  have e2 : hvBO cb E V (.v cb.xv) = V := by simp [hvBO, hc.xvNe]
  unfold callWithO
  simp only [callKeys, List.map_cons, List.sum_cons] at w
  rw [e1, e2, hs] at w
  simp only [callKeys]
  omega

/-- The call of design BO changes no key outside its key list. -/
theorem callWithO_frame {k : Key} (hk : k ∉ callKeys cb T st cov) :
    oget (callWithO cb T st E V cov).2 k = oget st k :=
  addSets_oget _ _ _ _ _ _ hk

/-- A key that is neither a reserved key nor an empty universe cell is not a key of the call. -/
theorem not_mem_callKeys {k : Key} (h1 : k ≠ .v cb.cn.xe) (h2 : k ≠ .v cb.xv)
    (h3 : ¬ ∃ o c, k = .h o c ∧ o ∈ cb.cn.ctx.origins ∧ c ∈ cb.cn.ctx.cells ∧
      val cb.cn.ctx.K T st (.h o c) = []) :
    k ∉ callKeys cb T st cov := by
  intro hk
  simp only [callKeys, List.mem_cons] at hk
  rcases hk with e | e | h
  · exact h1 e
  · exact h2 e
  · obtain ⟨o, c, rfl, ho, _, hc1, he⟩ := mem_emptyKeys.mp h
    exact h3 ⟨o, c, rfl, ho, hc1, he⟩

/-- FRAME OF THE CALL OF DESIGN BO: the call changes no key of the map except the two reserved
keys and the universe cells whose value is empty. -/
theorem callBOO_frame (args : List Var) {k : Key} (h1 : k ≠ .v cb.cn.xe) (h2 : k ≠ .v cb.xv)
    (h3 : ¬ ∃ o c, k = .h o c ∧ o ∈ cb.cn.ctx.origins ∧ c ∈ cb.cn.ctx.cells ∧
      val cb.cn.ctx.K T st (.h o c) = []) :
    oget (callBOO cb T st args).2 k = oget st k := by
  unfold callBOO
  simp only
  split
  · exact callWithO_frame (not_mem_callKeys h1 h2 h3)
  · exact callWithO_frame (not_mem_callKeys h1 h2 h3)

/-- ZERO HEAP WRITES: if no universe cell has an empty value, the call of design BO does not
change any heap key of the map. -/
theorem callBOO_zero_writes (args : List Var)
    (hne : ∀ o ∈ cb.cn.ctx.origins, ∀ c ∈ cb.cn.ctx.cells, val cb.cn.ctx.K T st (.h o c) ≠ [])
    (o : Origin) (c : ACell) : oget (callBOO cb T st args).2 (.h o c) = oget st (.h o c) :=
  callBOO_frame args (fun e => by cases e) (fun e => by cases e)
    (fun ⟨o', c', e, ho, hc1, he⟩ => by cases e; exact hne o ho c hc1 he)

/-- The call of design BO changes no variable key except the two reserved keys. -/
theorem callBOO_env_frame (args : List Var) {x : Var} (h1 : x ≠ cb.cn.xe) (h2 : x ≠ cb.xv) :
    oget (callBOO cb T st args).2 (.v x) = oget st (.v x) :=
  callBOO_frame args (fun e => h1 (Key.v.inj e)) (fun e => h2 (Key.v.inj e))
    (fun ⟨_, _, e, _⟩ => by cases e)

/-- FRAME OF THE CALL STATEMENT OF DESIGN BO: for a call site that is not an allocation site,
the statement changes no key except the two reserved keys, the result variable, and the
universe cells whose value is empty. -/
theorem ostepBO_call_frame {ret : Option Var} {s : Site} {args : List Var}
    (hn : rNew s ∉ cb.cn.ctx.origins) {k : Key} (h1 : k ≠ .v cb.cn.xe) (h2 : k ≠ .v cb.xv)
    (h3 : ¬ ∃ o c, k = .h o c ∧ o ∈ cb.cn.ctx.origins ∧ c ∈ cb.cn.ctx.cells ∧
      val cb.cn.ctx.K T st (.h o c) = [])
    (h4 : ∀ x, ret = some x → k ≠ .v x) :
    oget (ostepBO cb (.call ret s args) T st).2 k = oget st k := by
  simp only [ostepBO]
  rw [retireO_skip _ _ _ _ hn]
  cases ret with
  | none => exact callBOO_frame args h1 h2 h3
  | some x =>
    show oget (oset _ (.v x) _) k = oget st k
    rw [oget_oset, ite_eq_right (h4 x rfl)]
    exact callBOO_frame args h1 h2 h3

/-- A read of design BO is the read of the recency machine: no read rule, no extra test. -/
theorem ostepBO_load (x y : Var) (f : Field) :
    ostepBO cb (.load x y f) T st = ostepR cb.cn.ctx (.load x y f) T st := rfl

end bo

/-! ## The call of design CN -/

section cn

variable {cn : CtxN} {T : Tbl} {st : OState} {E : List Origin} {cov : Origin → Bool}

/-- The cell keys of the call of design CN: each universe cell of each covered universe
origin. -/
def cnCells (cn : CtxN) (cov : Origin → Bool) : List Key :=
  (cn.ctx.origins.filter cov).flatMap (fun o => cn.ctx.cells.map (Key.h o))

/-- The call of design CN writes the reserved key and each universe cell of each covered
universe origin. -/
theorem hvKeys_eq : hvKeys cn cov = Key.v cn.xe :: cnCells cn cov := rfl

/-- COST OF THE CALL OF DESIGN CN (after the closure), upper bound: the reserved key, and
`6 + 4 |U|` for each universe cell of each covered universe origin. -/
theorem havocWithO_work (hc : CtxNOK cn) (g : T.Good cn.ctx.origins) (h : EntOK cn.ctx T st)
    (hE : E ⊆ cn.ctx.origins) :
    (havocWithO cn T st E cov).1.work ≤ T.work + (E.length + 5 + 4 * cn.ctx.origins.length) +
      (cnCells cn cov).length * (6 + 4 * cn.ctx.origins.length) := by
  have cc : CtxClosed cn.ctx := ⟨fun o ho c hc1 o' ho' => hc.base.base.dflt o ho c hc1 o' ho',
    hc.base.base.elem⟩
  have hks : ∀ k ∈ hvKeys cn cov, InU cn.ctx k := by
    intro k hk
    rw [hvKeys_eq, List.mem_cons] at hk
    rcases hk with rfl | h
    · exact hc.xeIn
    · simp only [cnCells, List.mem_flatMap, List.mem_filter, List.mem_map] at h
      obtain ⟨o, ⟨ho, _⟩, c, hc1, rfl⟩ := h
      exact ⟨ho, hc1⟩
  have hhs : ∀ k ∈ hvKeys cn cov, hvCN cn.ctx.K E k ⊆ cn.ctx.origins := by
    intro k hk
    rw [hvKeys_eq, List.mem_cons] at hk
    rcases hk with rfl | h
    · exact hE
    · simp only [cnCells, List.mem_flatMap, List.mem_filter, List.mem_map] at h
      obtain ⟨o, ⟨ho, _⟩, c, hc1, rfl⟩ := h
      intro a ha
      simp only [hvCN, List.mem_singleton] at ha
      subst ha
      exact hc.childIn o ho c hc1
  have w := addSets_work_le cc (hvCN cn.ctx.K E) (hvKeys cn cov) g h hks hhs
  have hs : ((cnCells cn cov).map
      (fun k => (hvCN cn.ctx.K E k).length + 5 + 4 * cn.ctx.origins.length)).sum =
      (cnCells cn cov).length * (6 + 4 * cn.ctx.origins.length) := by
    apply sum_const_of
    intro k hk
    simp only [cnCells, List.mem_flatMap, List.mem_filter, List.mem_map] at hk
    obtain ⟨o, _, c, _, rfl⟩ := hk
    simp only [hvCN, List.length_singleton] <;> omega
  unfold havocWithO
  rw [hvKeys_eq, List.map_cons, List.sum_cons, hs] at w
  simp only [hvCN] at w
  rw [hvKeys_eq]
  omega

/-- COST OF THE CALL OF DESIGN CN, lower bound: at least two units for the reserved key and for
each universe cell of each covered universe origin (one intern and one union each). -/
theorem havocWithO_work_ge :
    T.work + 2 * (1 + (cnCells cn cov).length) ≤ (havocWithO cn T st E cov).1.work := by
  have := addSets_work_ge cn.ctx (hvCN cn.ctx.K E) (hvKeys cn cov) T st
  rw [hvKeys_eq, List.length_cons] at this
  unfold havocWithO
  rw [hvKeys_eq]
  omega

/-- The call of design CN writes each universe cell of each covered universe origin. -/
theorem mem_cnCells {o : Origin} {c : ACell} (ho : o ∈ cn.ctx.origins) (hcov : cov o = true)
    (hc1 : c ∈ cn.ctx.cells) : Key.h o c ∈ cnCells cn cov :=
  List.mem_flatMap.mpr ⟨o, List.mem_filter.mpr ⟨ho, hcov⟩, List.mem_map.mpr ⟨c, hc1, rfl⟩⟩

end cn

/-! ## The per-cell call -/

/-- The keys of the per-cell call: each universe cell of each reachable universe origin. -/
def hrCells (ctx : Ctx) (X : AState) (args : List Var) : List Key :=
  (ctx.origins.filter (reachB ctx X args)).flatMap (fun o => ctx.cells.map (Key.h o))

/-- COST OF THE PER-CELL CALL: at least two units, and at most `6 + 4 |U|`, for each universe
cell of each reachable universe origin. -/
theorem havocHRO_work {ctx : Ctx} (cc : CtxClosed ctx) {T : Tbl} (g : T.Good ctx.origins)
    {st : OState} (h : EntOK ctx T st) (args : List Var) {s : Site}
    (hs : ∀ k ∈ hrCells ctx (den ctx.K T st) args, hvOfR s k ⊆ ctx.origins) :
    T.work + 2 * (hrCells ctx (den ctx.K T st) args).length ≤ (havocHRO ctx T st args s).1.work ∧
      (havocHRO ctx T st args s).1.work ≤
        T.work + (hrCells ctx (den ctx.K T st) args).length * (6 + 4 * ctx.origins.length) := by
  have hks : ∀ k ∈ hrCells ctx (den ctx.K T st) args, InU ctx k := by
    intro k hk
    simp only [hrCells, List.mem_flatMap, List.mem_filter, List.mem_map] at hk
    obtain ⟨o, ⟨ho, _⟩, c, hc1, rfl⟩ := hk
    exact ⟨ho, hc1⟩
  exact ⟨addSets_work_ge ctx (hvOfR s) _ T st,
    addSets_work cc (hvOfR s) (hvOfR_length_le s) _ g h hks hs⟩

/-! ## The cost of the uniqueness test -/

/-- THE PREFIX TEST BY LOOKUPS: a symbolic origin `sym b q` is below `E` if and only if one of
its `|q|` proper prefixes `sym b (q.take i)` (`i < |q|`) is in `E`. So the test is at most `K`
membership tests in `Etree` for a universe origin. -/
theorem expB_prefixes (E : List Origin) (b : ABase) (q : List ACell) :
    expB E (.sym b q) = (List.range q.length).any (fun i => decide (Origin.sym b (q.take i) ∈ E)) := by
  cases h : expB E (.sym b q) with
  | true =>
    obtain ⟨p, hm, hl, hp⟩ := expB_inv h
    have e : q.take p.length = p := of_decide_eq_true hp
    symm
    apply List.any_eq_true.mpr
    exact ⟨p.length, List.mem_range.mpr hl, by rw [e]; exact decide_eq_true hm⟩
  | false =>
    symm
    cases h2 : (List.range q.length).any (fun i => decide (Origin.sym b (q.take i) ∈ E)) with
    | false => rfl
    | true =>
      obtain ⟨i, hi, hm⟩ := List.any_eq_true.mp h2
      have hi' := List.mem_range.mp hi
      have hm' := of_decide_eq_true hm
      have hlen : (q.take i).length = i := by rw [List.length_take]; omega
      have : expB E (.sym b q) = true := by
        refine expB_of hm' (by rw [hlen]; exact hi') ?_
        apply decide_eq_true
        rw [hlen]
      rw [h] at this; cases this

/-- THE UNIQUENESS TEST BY LOOKUPS: for a symbolic origin, the test of design BO is the
recency test, at most `|q|` membership tests in `Etree` (the proper prefixes), and one
membership test in `Eval`. -/
theorem uniqueBO_prefixes (once : Site → Bool) (eu : Bool) (E V : List Origin) (b : ABase)
    (q : List ACell) :
    uniqueBO once eu E V (.sym b q) =
      ((uniqueR once eu (.sym b q) &&
        !((List.range q.length).any (fun i => decide (Origin.sym b (q.take i) ∈ E)))) &&
      !(decide (Origin.sym b q ∈ V))) := by
  unfold uniqueBO uniqueCN
  rw [expB_prefixes]

/-- For an origin that is not symbolic, the uniqueness test of design BO is the recency test
and one membership test in `Eval`. -/
theorem uniqueBO_not_sym (once : Site → Bool) (eu : Bool) (E V : List Origin) {o : Origin}
    (h : ∀ b q, o ≠ .sym b q) :
    uniqueBO once eu E V o = (uniqueR once eu o && !(decide (o ∈ V))) := by
  unfold uniqueBO uniqueCN
  cases o with
  | sym b q => exact absurd rfl (h b q)
  | _ => simp [expB]

/-- A symbolic origin of the universe of design BO has a path of at most `K` cells, so its
prefix test is at most `K` lookups. -/
theorem prefix_lookups_le {eu : Bool} {K : Nat} {statics : List Root} {fr : Frame} {p : Prog}
    {qf : List Field} {b : ABase} {q : List ACell}
    (h : Origin.sym b q ∈ (ctxBO eu K statics fr p qf).cn.ctx.origins) :
    (List.range q.length).length ≤ K := by
  rw [List.length_range]
  change Origin.sym b q ∈ originsCN K fr statics p _ at h
  rcases mem_originsCN.mp h with ⟨b', _, ⟨q', hq, e⟩ | e⟩ | ⟨_, _, e | e⟩ |
      ⟨_, _, _, _, ⟨_, _, e⟩ | e⟩
  · cases e; exact (mem_pathsUpTo.mp hq).1
  all_goals cases e

/-! ## The size of the two sets -/

/-- Both sets of a supported state are in the universe. -/
theorem sets_in_universe {cb : CtxB} (hc : CtxBOK cb) {X : AState} (hs : Supp cb.cn.ctx X) :
    X.env cb.cn.xe ⊆ cb.cn.ctx.origins ∧ X.env cb.xv ⊆ cb.cn.ctx.origins :=
  ⟨hs.env hc.cn.xeIn, hs.env hc.xvIn⟩

/-- In O, each of the two sets is one node of at most `|U|` origins. -/
theorem sets_node_length {cb : CtxB} {T : Tbl} (g : T.Good cb.cn.ctx.origins)
    (st : OState) :
    (val cb.cn.ctx.K T st (.v cb.cn.xe)).length ≤ cb.cn.ctx.origins.length ∧
      (val cb.cn.ctx.K T st (.v cb.xv)).length ≤ cb.cn.ctx.origins.length := by
  have hd : ∀ x, (val cb.cn.ctx.K T st (.v x)).length ≤ cb.cn.ctx.origins.length := by
    intro x
    unfold val
    split
    · exact g.mem_length _
    · exact Nat.zero_le _
  exact ⟨hd _, hd _⟩

/-- GROWTH OF `Etree` AT A CALL: the new set is the old set with the closure. -/
theorem callWith_xe_length {cb : CtxB} (hc : CtxBOK cb) (X : AState) (E V : List Origin)
    (cov : Origin → Bool) :
    ((callWith cb X E V cov).env cb.cn.xe).length ≤ E.length + (X.env cb.cn.xe).length := by
  rw [callWith_xe hc]; exact length_uni_le _ _

/-- GROWTH OF `Eval` AT A CALL: the new set is the old set with the contents of the covered
cells. -/
theorem callWith_xv_length {cb : CtxB} (X : AState) (E V : List Origin) (cov : Origin → Bool) :
    ((callWith cb X E V cov).env cb.xv).length ≤ V.length + (X.env cb.xv).length := by
  rw [callWith_xv]; exact length_uni_le _ _

/-! ## The two sets only grow along a path -/

/-- The renaming of a statement: `retire s` for a statement with site `s` that retires, and no
renaming for the other statements. -/
def renAt : Stmt → Origin → Origin
  | .new _ s => renameO s
  | .unknown _ s => renameO s
  | .call _ s _ => renameO s
  | _ => id

/-- ALONG A PATH, `Etree` ONLY GROWS: each origin of `Etree` stays, up to the renaming of
`retire`. -/
theorem astepBO_xe_grow {cb : CtxB} (hc : CtxBOK cb) {st : Stmt} (ok : StmtOKB cb st)
    (X : AState) {a : Origin} (ha : a ∈ X.env cb.cn.xe) :
    renAt st a ∈ (astepBO cb st X).env cb.cn.xe := by
  have nx : ∀ v ∈ st.vars, cb.cn.xe ≠ v := fun v hv e => ok.noXe v hv e.symm
  cases st with
  | new x s =>
    show renameO s a ∈ fupd (fun y => renameL s (X.env y)) x [rNew s] cb.cn.xe
    rw [fupd_ne _ _ (nx x (by simp [Stmt.vars]))]
    exact List.mem_map.mpr ⟨a, ha, rfl⟩
  | unknown x s =>
    show renameO s a ∈ fupd (fun y => renameL s (X.env y)) x _ cb.cn.xe
    rw [fupd_ne _ _ (nx x (by simp [Stmt.vars]))]
    exact List.mem_map.mpr ⟨a, ha, rfl⟩
  | call ret s args =>
    have h1 : a ∈ (callBO cb X args).env cb.cn.xe := by
      unfold callBO
      split
      · exact callWith_env_sub hc _ ha
      · exact callWith_env_sub hc _ ha
    have h2 : renameO s a ∈ (retire s (callBO cb X args)).env cb.cn.xe :=
      List.mem_map.mpr ⟨a, h1, rfl⟩
    cases ret with
    | none => exact h2
    | some x =>
      show renameO s a ∈ fupd _ x _ cb.cn.xe
      rw [fupd_ne _ _ (nx x (by simp [Stmt.vars]))]
      exact h2
  | store x f y =>
    show a ∈ (storeBO cb X x (.fld f) (X.env y)).env cb.cn.xe
    unfold storeBO
    split
    · split <;> exact ha
    · exact ha
  | null x =>
    show a ∈ fupd X.env x [] cb.cn.xe
    rw [fupd_ne _ _ (nx x (by simp [Stmt.vars]))]; exact ha
  | copy x y =>
    show a ∈ fupd X.env x _ cb.cn.xe
    rw [fupd_ne _ _ (nx x (by simp [Stmt.vars]))]; exact ha
  | load x y f =>
    show a ∈ fupd X.env x _ cb.cn.xe
    rw [fupd_ne _ _ (nx x (by simp [Stmt.vars]))]; exact ha
  | aload x y =>
    show a ∈ fupd X.env x _ cb.cn.xe
    rw [fupd_ne _ _ (nx x (by simp [Stmt.vars]))]; exact ha
  | astore x y => exact ha

/-- ALONG A PATH, `Eval` ONLY GROWS: each origin of `Eval` stays, up to the renaming of
`retire`. -/
theorem astepBO_xv_grow {cb : CtxB} (hc : CtxBOK cb) {st : Stmt} (ok : StmtOKB cb st)
    (X : AState) {a : Origin} (ha : a ∈ X.env cb.xv) :
    renAt st a ∈ (astepBO cb st X).env cb.xv := by
  have nx : ∀ v ∈ st.vars, cb.xv ≠ v := fun v hv e => ok.noXv v hv e.symm
  cases st with
  | new x s =>
    show renameO s a ∈ fupd (fun y => renameL s (X.env y)) x [rNew s] cb.xv
    rw [fupd_ne _ _ (nx x (by simp [Stmt.vars]))]
    exact List.mem_map.mpr ⟨a, ha, rfl⟩
  | unknown x s =>
    show renameO s a ∈ fupd (fun y => renameL s (X.env y)) x _ cb.xv
    rw [fupd_ne _ _ (nx x (by simp [Stmt.vars]))]
    exact List.mem_map.mpr ⟨a, ha, rfl⟩
  | call ret s args =>
    have h1 : a ∈ (callBO cb X args).env cb.xv := by
      unfold callBO
      split
      · exact callWith_env_sub hc _ ha
      · exact callWith_env_sub hc _ ha
    have h2 : renameO s a ∈ (retire s (callBO cb X args)).env cb.xv :=
      List.mem_map.mpr ⟨a, h1, rfl⟩
    cases ret with
    | none => exact h2
    | some x =>
      show renameO s a ∈ fupd _ x _ cb.xv
      rw [fupd_ne _ _ (nx x (by simp [Stmt.vars]))]
      exact h2
  | store x f y =>
    show a ∈ (storeBO cb X x (.fld f) (X.env y)).env cb.xv
    unfold storeBO
    split
    · split <;> exact ha
    · exact ha
  | null x =>
    show a ∈ fupd X.env x [] cb.xv
    rw [fupd_ne _ _ (nx x (by simp [Stmt.vars]))]; exact ha
  | copy x y =>
    show a ∈ fupd X.env x _ cb.xv
    rw [fupd_ne _ _ (nx x (by simp [Stmt.vars]))]; exact ha
  | load x y f =>
    show a ∈ fupd X.env x _ cb.xv
    rw [fupd_ne _ _ (nx x (by simp [Stmt.vars]))]; exact ha
  | aload x y =>
    show a ∈ fupd X.env x _ cb.xv
    rw [fupd_ne _ _ (nx x (by simp [Stmt.vars]))]; exact ha
  | astore x y => exact ha

/-- The join keeps both sets of both sides (it is their union). -/
theorem join_sets (cb : CtxB) (X Y : AState) :
    (∀ a ∈ X.env cb.cn.xe, a ∈ (join X Y).env cb.cn.xe) ∧
      (∀ a ∈ X.env cb.xv, a ∈ (join X Y).env cb.xv) ∧
      (∀ a ∈ Y.env cb.cn.xe, a ∈ (join X Y).env cb.cn.xe) ∧
      (∀ a ∈ Y.env cb.xv, a ∈ (join X Y).env cb.xv) :=
  ⟨fun _ h => mem_uni.mpr (Or.inl h), fun _ h => mem_uni.mpr (Or.inl h),
    fun _ h => mem_uni.mpr (Or.inr h), fun _ h => mem_uni.mpr (Or.inr h)⟩

/-- The two sets are variable keys of the universe, so the post-fixpoint test of a loop
(`leOn`) compares them like any other key. -/
theorem sets_in_loop_test {cb : CtxB} (hc : CtxBOK cb) {X Y : AState}
    (h : leOn cb.cn.ctx X Y = true) :
    X.env cb.cn.xe ⊆ Y.env cb.cn.xe ∧ X.env cb.xv ⊆ Y.env cb.xv :=
  ⟨(leOn_iff.mp h).1 _ hc.cn.xeIn, (leOn_iff.mp h).1 _ hc.xvIn⟩

/-! ## Heap writes of one call, counted on the concept state -/

/-- The coverage test of a call of design CN or BO: the descendants of the closure, or every
origin if the closure fails. -/
def covN (cn : CtxN) (X : AState) (args : List Var) : Origin → Bool :=
  match closeN cn X (cn.ctx.origins.length + 1) (callRoots cn X args) with
  | some R => coveredB R
  | none => fun _ => true

/-- The covered universe cells with an empty value in a concept state. -/
def emptyCells (cb : CtxB) (X : AState) (cov : Origin → Bool) : List Key :=
  (cb.cn.ctx.origins.filter cov).flatMap (fun o =>
    (cb.cn.ctx.cells.filter (fun c => (X.heap o c).isEmpty)).map (Key.h o))

/-- The number of heap keys that a call of design BO writes. -/
def writesBO (cb : CtxB) (X : AState) (args : List Var) : Nat :=
  (emptyCells cb X (covN cb.cn X args)).length

/-- The number of heap keys that a call of design CN writes. -/
def writesCN (cn : CtxN) (X : AState) (args : List Var) : Nat :=
  (cnCells cn (covN cn X args)).length

/-- The number of heap keys that a per-cell call writes. -/
def writesHR (ctx : Ctx) (X : AState) (args : List Var) : Nat :=
  (hrCells ctx X args).length

/-- `flatMap` with functions that agree on the list. -/
theorem flatMap_congr' {α β : Type} {f g : α → List β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.flatMap_cons]
    rw [h a List.mem_cons_self, flatMap_congr' (fun b hb => h b (List.mem_cons_of_mem _ hb))]

/-- The empty keys of O are the empty cells of the concept state that it represents. -/
theorem emptyKeys_eq {cb : CtxB} {T : Tbl} {st : OState} {X : AState}
    (hR : Rel cb.cn.ctx T st X) (cov : Origin → Bool) :
    emptyKeys cb T st cov = emptyCells cb X cov := by
  unfold emptyKeys emptyCells
  apply flatMap_congr'
  intro o ho
  have ho' := (List.mem_filter.mp ho).1
  congr 1
  apply List.filter_congr
  intro c hc1
  have := setEq_nil (hR.agree (.h o c) ⟨ho', hc1⟩)
  cases h1 : (X.heap o c).isEmpty with
  | true =>
    rw [List.isEmpty_iff] at h1
    have : val cb.cn.ctx.K T st (.h o c) = [] := this.mpr h1
    rw [this]; rfl
  | false =>
    cases h2 : (val cb.cn.ctx.K T st (.h o c)).isEmpty with
    | false => rfl
    | true =>
      rw [List.isEmpty_iff] at h2
      have h3 : X.heap o c = [] := this.mp h2
      rw [h3] at h1; cases h1

/-- THE HEAP WRITES OF THE O CALL OF DESIGN BO are among the covered empty cells of the
concept state: every other heap key keeps its entry. -/
theorem callBOO_writes {cb : CtxB} {T : Tbl} {st : OState} {X : AState}
    (hR : Rel cb.cn.ctx T st X) {args : List Var} (hargs : ∀ x ∈ args, x ∈ cb.cn.ctx.vars)
    {o : Origin} {c : ACell} (hk : Key.h o c ∉ emptyCells cb X (covN cb.cn X args)) :
    oget (callBOO cb T st args).2 (.h o c) = oget st (.h o c) := by
  have hag : ∀ k, InU cb.cn.ctx k → SetEq (cval X k) (cval (den cb.cn.ctx.K T st) k) := by
    intro k hk; rw [cval_den]; exact (hR.agree k hk).symm
  have hXY : ∀ o ∈ cb.cn.ctx.origins, ∀ c ∈ cb.cn.ctx.cells,
      SetEq (X.heap o c) ((den cb.cn.ctx.K T st).heap o c) :=
    fun o ho c hc1 => hag (.h o c) ⟨ho, hc1⟩
  have hroots : SetEq (callRoots cb.cn X args) (callRoots cb.cn (den cb.cn.ctx.K T st) args) := by
    refine SetEq.uni ?_ (SetEq.refl _)
    intro o
    rw [mem_uniMap, mem_uniMap]
    constructor
    · rintro ⟨x, hx, h⟩; exact ⟨x, hx, (hag (.v x) (hargs x hx) o).mp h⟩
    · rintro ⟨x, hx, h⟩; exact ⟨x, hx, (hag (.v x) (hargs x hx) o).mpr h⟩
  have hnk : ∀ cov, covN cb.cn X args = cov → Key.h o c ∉ callKeys cb T st cov := by
    intro cov e hm
    simp only [callKeys, List.mem_cons] at hm
    rcases hm with h | h | h
    · cases h
    · cases h
    · rw [emptyKeys_eq hR, ← e] at h; exact hk h
  unfold callBOO
  simp only
  rcases closeN_congr (cn := cb.cn) hXY (cb.cn.ctx.origins.length + 1) _ _ hroots with
    ⟨h1, h2⟩ | ⟨A, B, h1, h2, h3⟩
  · rw [h2]
    exact callWithO_frame (hnk _ (by unfold covN; rw [h1]))
  · rw [h2]
    simp only
    refine callWithO_frame (hnk _ ?_)
    unfold covN; rw [h1]
    exact funext (fun u => coveredB_congr h3 u)

/-- If the concept count of the heap writes of a call of design BO is zero, the O call writes
no heap key. -/
theorem callBOO_writes_zero {cb : CtxB} {T : Tbl} {st : OState} {X : AState}
    (hR : Rel cb.cn.ctx T st X) {args : List Var} (hargs : ∀ x ∈ args, x ∈ cb.cn.ctx.vars)
    (h0 : writesBO cb X args = 0) (o : Origin) (c : ACell) :
    oget (callBOO cb T st args).2 (.h o c) = oget st (.h o c) := by
  refine callBOO_writes hR hargs ?_
  intro hm
  unfold writesBO at h0
  rw [List.length_eq_zero_iff] at h0
  rw [h0] at hm; cases hm

/-- Pointwise smaller terms give a smaller sum. -/
theorem sum_le_sum_of {α : Type} (f g : α → Nat) :
    ∀ (l : List α), (∀ a ∈ l, f a ≤ g a) → (l.map f).sum ≤ (l.map g).sum
  | [], _ => Nat.le_refl _
  | a :: l, h => by
    simp only [List.map_cons, List.sum_cons]
    have := sum_le_sum_of f g l (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have := h a List.mem_cons_self
    omega

/-- AT THE SAME STATE AND COVERAGE, DESIGN BO WRITES NO MORE HEAP KEYS THAN DESIGN CN: the
covered empty cells are some of the cells of the covered origins. -/
theorem emptyCells_le (cb : CtxB) (X : AState) (cov : Origin → Bool) :
    (emptyCells cb X cov).length ≤ (cnCells cb.cn cov).length := by
  unfold emptyCells cnCells
  rw [List.length_flatMap, List.length_flatMap]
  apply sum_le_sum_of
  intro o _
  rw [List.length_map, List.length_map]
  exact List.length_filter_le _ _

/-! ## The separation family -/

/-- `x.f = y` for each field `f` of the list. -/
def storesP (x y : Var) : List Field → Prog
  | [] => .skip
  | f :: fs => .seq (.stmt (.store x f y)) (storesP x y fs)

/-- `m(x)` at each site of the list. -/
def callsP (x : Var) : List Site → Prog
  | [] => .skip
  | s :: l => .seq (.stmt (.call none s [x])) (callsP x l)

/-- THE FAMILY: `x.f_0 = y; ...; x.f_(n-1) = y; m(x)@1; ...; m(x)@m`. -/
def famP (n m : Nat) : Prog := .seq (storesP 0 1 (ids 0 n)) (callsP 0 (ids 1 m))

/-- The frame of the family: `x` (variable 0) and `y` (variable 1) hold roots 0 and 1. -/
def frF : Frame := ⟨[(0, 0), (1, 1)]⟩

/-- The total number of heap keys that the calls of design BO write, along the analysis. -/
def totalBO (cb : CtxB) (x : Var) : List Site → AState → Nat
  | [], _ => 0
  | s :: l, X => writesBO cb X [x] + totalBO cb x l (astepBO cb (.call none s [x]) X)

/-- The total number of heap keys that the calls of design CN write, along the analysis. -/
def totalCN (cn : CtxN) (x : Var) : List Site → AState → Nat
  | [], _ => 0
  | s :: l, X => writesCN cn X [x] + totalCN cn x l (astepCN cn (.call none s [x]) X)

/-- The total number of heap keys that the per-cell calls write, along the analysis. -/
def totalHR (ctx : Ctx) (x : Var) : List Site → AState → Nat
  | [], _ => 0
  | s :: l, X => writesHR ctx X [x] + totalHR ctx x l (astepHR ctx (.call none s [x]) X)

/-- The totals follow the analysis states: the analysis of the calls is one call step, then
the analysis of the other calls. -/
theorem analyzeBO_callsP (cb : CtxB) (x : Var) (s : Site) (l : List Site) (X : AState) :
    analyzeBO cb (callsP x (s :: l)) X = analyzeBO cb (callsP x l) (astepBO cb (.call none s [x]) X) :=
  rfl

/-- The statements of the stores are stores. -/
theorem storesP_stmts (x y : Var) : ∀ (fs : List Field) {st : Stmt}, st ∈ (storesP x y fs).stmts →
    ∃ f ∈ fs, st = .store x f y
  | [], _, h => by cases h
  | f :: fs, st, h => by
    simp only [storesP, Prog.stmts, List.mem_append, List.mem_singleton] at h
    rcases h with rfl | h
    · exact ⟨f, List.mem_cons_self, rfl⟩
    · obtain ⟨g, hg, e⟩ := storesP_stmts x y fs h
      exact ⟨g, List.mem_cons_of_mem _ hg, e⟩

/-- The statements of the calls are calls. -/
theorem callsP_stmts (x : Var) : ∀ (l : List Site) {st : Stmt}, st ∈ (callsP x l).stmts →
    ∃ s ∈ l, st = .call none s [x]
  | [], _, h => by cases h
  | s :: l, st, h => by
    simp only [callsP, Prog.stmts, List.mem_append, List.mem_singleton] at h
    rcases h with rfl | h
    · exact ⟨s, List.mem_cons_self, rfl⟩
    · obtain ⟨t, ht, e⟩ := callsP_stmts x l h
      exact ⟨t, List.mem_cons_of_mem _ ht, e⟩

/-- A `filterMap` that gives nothing on each element is empty. -/
theorem filterMap_nil {α β : Type} {f : α → Option β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = none) → l.filterMap f = []
  | [], _ => rfl
  | a :: l, h => by
    rw [List.filterMap_cons, h a List.mem_cons_self]
    exact filterMap_nil (fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- The family has no allocation site. -/
theorem famP_newSites (n m : Nat) : (famP n m).newSites = [] := by
  apply filterMap_nil
  intro st hst
  simp only [famP, Prog.stmts, List.mem_append] at hst
  rcases hst with h | h
  · obtain ⟨f, _, rfl⟩ := storesP_stmts _ _ _ h; rfl
  · obtain ⟨s, _, rfl⟩ := callsP_stmts _ _ h; rfl

/-- The call sites of the calls are the sites of the list. -/
theorem callsP_callSites (x : Var) : ∀ (l : List Site), (callsP x l).callSites = l
  | [] => rfl
  | s :: l => by
    show (Prog.stmts (.stmt (.call none s [x])) ++ (callsP x l).stmts).filterMap _ = _
    rw [List.filterMap_append]
    exact congrArg (s :: ·) (callsP_callSites x l)

/-- The call sites of the family are the `m` sites of the calls. -/
theorem famP_callSites (n m : Nat) : (famP n m).callSites = ids 1 m := by
  show ((storesP 0 1 (ids 0 n)).stmts ++ (callsP 0 (ids 1 m)).stmts).filterMap _ = _
  rw [List.filterMap_append, filterMap_nil, List.nil_append]
  · exact callsP_callSites 0 _
  · intro st hst
    obtain ⟨f, _, rfl⟩ := storesP_stmts _ _ _ hst; rfl

/-- The fields of the stores are fields of the family. -/
theorem famP_fields {n m : Nat} {f : Field} (hf : f ∈ ids 0 n) : f ∈ (famP n m).fields := by
  have : ∀ (fs : List Field), f ∈ fs → f ∈ (storesP 0 1 fs).fields := by
    intro fs
    induction fs with
    | nil => intro h; cases h
    | cons g gs ih =>
      intro h
      show f ∈ ((Prog.stmts (.stmt (.store 0 g 1))) ++ (storesP 0 1 gs).stmts).flatMap _
      rw [List.flatMap_append, List.mem_append]
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl (by simp [Prog.stmts, Stmt.fields])
      · exact Or.inr (ih h)
  show f ∈ ((storesP 0 1 (ids 0 n)).stmts ++ (callsP 0 (ids 1 m)).stmts).flatMap _
  rw [List.flatMap_append, List.mem_append]
  exact Or.inl (this _ hf)

/-- The field cells of a list of distinct fields are distinct. -/
theorem nodup_map_fld : ∀ {l : List Field}, l.Nodup → (l.map ACell.fld).Nodup
  | [], _ => List.nodup_nil
  | f :: l, h => by
    rw [List.nodup_cons] at h
    simp only [List.map_cons]
    rw [List.nodup_cons]
    refine ⟨?_, nodup_map_fld h.2⟩
    intro hm
    obtain ⟨g, hg, he⟩ := List.mem_map.mp hm
    cases he
    exact h.1 hg

/-- The cell universe of the family has at least the `n` fields of the stores. -/
theorem famP_cells (n m : Nat) (qf : List Field) :
    n ≤ (cellsOf ((famP n m).fields ++ qf)).length := by
  have h := nodup_length_le (nodup_map_fld (nodup_ids 0 n))
    (m := cellsOf ((famP n m).fields ++ qf)) (by
      intro c hc
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hc
      exact DirectedAlias.Sound.fld_mem_cellsOf (List.mem_append.mpr (Or.inl (famP_fields hf))))
  rw [List.length_map, length_ids] at h
  exact h

/-! ## The family: design BO writes no heap key -/

/-- No universe cell is empty. -/
def NoEmpty (ctx : Ctx) (X : AState) : Prop :=
  ∀ o ∈ ctx.origins, ∀ c ∈ ctx.cells, X.heap o c ≠ []

/-- The universe of the family (design CN and BO) has no allocation origin. -/
theorem famP_noAlloc {eu : Bool} {K n m : Nat} {qf : List Field} {o : Origin}
    (h : o ∈ (ctxCN eu K [] frF (famP n m) qf).ctx.origins) (x : Nat) : o ≠ .alloc x := by
  change o ∈ originsCN K frF [] (famP n m) _ at h
  rcases mem_originsCN.mp h with ⟨b, _, ⟨q, _, rfl⟩ | rfl⟩ | ⟨s, hs, _⟩ | ⟨s, hs, _⟩
  · intro e; cases e
  · intro e; cases e
  · rw [famP_newSites] at hs; cases hs
  · rw [famP_newSites] at hs; cases hs

/-- A filter that keeps nothing is empty. -/
theorem filter_nil' {α : Type} {p : α → Bool} :
    ∀ {l : List α}, (∀ a ∈ l, p a = false) → l.filter p = []
  | [], _ => rfl
  | a :: l, h => by
    rw [List.filter_cons, ite_eq_right (by rw [h a List.mem_cons_self]; simp)]
    exact filter_nil' (fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- A `flatMap` of empty lists is empty. -/
theorem flatMap_nil' {α β : Type} {f : α → List β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = []) → l.flatMap f = []
  | [], _ => rfl
  | a :: l, h => by
    rw [List.flatMap_cons, h a List.mem_cons_self, List.nil_append]
    exact flatMap_nil' (fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- If no universe cell is empty, a call of design BO writes no heap key. -/
theorem writesBO_zero {cb : CtxB} {X : AState} (h : NoEmpty cb.cn.ctx X) (args : List Var) :
    writesBO cb X args = 0 := by
  unfold writesBO emptyCells
  rw [flatMap_nil']
  · rfl
  · intro o ho
    rw [filter_nil']
    · rfl
    · intro c hc1
      cases e : (X.heap o c).isEmpty with
      | false => rfl
      | true => exact absurd (List.isEmpty_iff.mp e) (h o (List.mem_filter.mp ho).1 c hc1)

/-- The store of design BO keeps the cells non-empty, if the stored value is not empty. -/
theorem noEmpty_store {cb : CtxB} {X : AState} (h : NoEmpty cb.cn.ctx X) (x : Var) (c : ACell)
    {S : List Origin} (hS : S ≠ []) : NoEmpty cb.cn.ctx (storeBO cb X x c S) := by
  have hw : ∀ os, NoEmpty cb.cn.ctx (X.weakStore os c S) := by
    intro os o ho c' hc'
    show (if c' = c ∧ o ∈ os then uni S (X.heap o c') else X.heap o c') ≠ []
    split
    · cases S with
      | nil => exact absurd rfl hS
      | cons a rest =>
        intro e
        have : a ∈ uni (a :: rest) (X.heap o c') := mem_uni.mpr (Or.inl List.mem_cons_self)
        rw [e] at this; cases this
    · exact h o ho c' hc'
  unfold storeBO
  split
  · split
    · intro o ho c' hc'
      show fupd2 X.heap _ c S o c' ≠ []
      unfold fupd2
      split
      · exact hS
      · exact h o ho c' hc'
    · exact hw _
  · exact hw _

/-- The store of design BO does not change the variables. -/
theorem storeBO_env (cb : CtxB) (X : AState) (x : Var) (c : ACell) (S : List Origin) :
    (storeBO cb X x c S).env = X.env := by
  unfold storeBO
  split
  · split <;> rfl
  · rfl

/-- In the family, a call of design BO keeps the cells non-empty. -/
theorem noEmpty_call {eu : Bool} {K n m : Nat} {X : AState}
    (h : NoEmpty (ctxBO eu K [] frF (famP n m) []).cn.ctx X) (s : Site) (args : List Var) :
    NoEmpty (ctxBO eu K [] frF (famP n m) []).cn.ctx
      (astepBO (ctxBO eu K [] frF (famP n m) []) (.call none s args) X) := by
  intro o ho c hc1
  have hna := famP_noAlloc (eu := eu) (K := K) (n := n) (m := m) (qf := []) ho
  have hY : (callBO (ctxBO eu K [] frF (famP n m) []) X args).heap o c ≠ [] := by
    unfold callBO
    split
    all_goals
      rcases callWith_heap_cases (cb := ctxBO eu K [] frF (famP n m) []) (X := X) o c with
        ⟨_, _, _, e⟩ | ⟨_, e⟩
      · rw [e]; simp
      · rw [e]; exact h o ho c hc1
  show (retire s (callBO (ctxBO eu K [] frF (famP n m) []) X args)).heap o c ≠ []
  show (if o = rNew s then [] else if o = rOld s then _ else _) ≠ []
  rw [ite_eq_right (show o ≠ rNew s from hna _), ite_eq_right (show o ≠ rOld s from hna _)]
  intro e
  have := congrArg List.length e
  rw [length_renameL] at this
  exact hY (List.length_eq_zero_iff.mp this)

/-- In the family, the calls of design BO write no heap key, from each state without an empty
universe cell. -/
theorem totalBO_zero {eu : Bool} {K n m : Nat} :
    ∀ (l : List Site) (X : AState), NoEmpty (ctxBO eu K [] frF (famP n m) []).cn.ctx X →
      totalBO (ctxBO eu K [] frF (famP n m) []) 0 l X = 0
  | [], _, _ => rfl
  | s :: l, X, h => by
    show writesBO _ X [0] + totalBO _ 0 l _ = 0
    rw [writesBO_zero h, totalBO_zero l _ (noEmpty_call h s [0])]

/-- The stores of the family keep the cells non-empty and the variable `y`. -/
theorem stores_BO {eu : Bool} {K n m : Nat} :
    ∀ (fs : List Field) (X : AState), NoEmpty (ctxBO eu K [] frF (famP n m) []).cn.ctx X →
      X.env 1 = [.sym (.root 1) []] →
      NoEmpty (ctxBO eu K [] frF (famP n m) []).cn.ctx
          (analyzeBO (ctxBO eu K [] frF (famP n m) []) (storesP 0 1 fs) X) ∧
        (analyzeBO (ctxBO eu K [] frF (famP n m) []) (storesP 0 1 fs) X).env 1 =
          [.sym (.root 1) []]
  | [], _, h1, h2 => ⟨h1, h2⟩
  | f :: fs, X, h1, h2 => by
    show NoEmpty _ (analyzeBO _ (storesP 0 1 fs) (storeBO _ X 0 (.fld f) (X.env 1))) ∧ _
    refine stores_BO fs _ (noEmpty_store h1 0 _ (by rw [h2]; simp)) ?_
    rw [storeBO_env]; exact h2

/-- The entry state of the family has no empty universe cell. -/
theorem noEmpty_init (eu : Bool) (K n m : Nat) :
    NoEmpty (ctxBO eu K [] frF (famP n m) []).cn.ctx (ainit K frF) := by
  intro o ho c _
  show adefault K o c ≠ []
  rw [adefault_childCN K (famP_noAlloc (eu := eu) (n := n) (m := m) (qf := []) ho)]
  simp

/-- THE FAMILY, DESIGN BO: the `m` calls write no heap key. -/
theorem fam_BO (eu : Bool) (K n m : Nat) :
    totalBO (ctxBO eu K [] frF (famP n m) []) 0 (ids 1 m)
      (analyzeBO (ctxBO eu K [] frF (famP n m) []) (storesP 0 1 (ids 0 n)) (ainit K frF)) = 0 :=
  totalBO_zero _ _ (stores_BO _ _ (noEmpty_init eu K n m) rfl).1

/-! ## The family: design CN writes each cell of the reached argument at each call -/

/-- The length of a `flatMap` that gives `c` elements for each element of the list. -/
theorem length_flatMap_const {α β : Type} (f : α → List β) (c : Nat) (l : List α)
    (h : ∀ a ∈ l, (f a).length = c) : (l.flatMap f).length = l.length * c := by
  rw [List.length_flatMap]
  exact sum_const_of (fun a => (f a).length) c l h

/-- The cells of the covered origins number the covered origins times the cells. -/
theorem cnCells_length (cn : CtxN) (cov : Origin → Bool) :
    (cnCells cn cov).length = (cn.ctx.origins.filter cov).length * cn.ctx.cells.length :=
  length_flatMap_const _ _ _ (fun _ _ => List.length_map _)

/-- The variable `x` (0) is not the reserved variable of design CN in the family. -/
theorem famP_x_ne_xe (eu : Bool) (K n m : Nat) :
    (0 : Var) ≠ (ctxCN eu K [] frF (famP n m) []).xe := by
  intro e
  have h0 : (0 : Var) ∈ ((famP n m).vars ++ frF.vars).eraseDups :=
    List.mem_eraseDups.mpr (List.mem_append.mpr (Or.inr (by simp [frF, Frame.vars])))
  have := lt_freshVar h0
  have e' : (0 : Var) = freshVar ((famP n m).vars ++ frF.vars).eraseDups := e
  rw [← e'] at this
  exact Nat.lt_irrefl _ this

/-- The store of design CN does not change the variables. -/
theorem storeCN_env (cn : CtxN) (X : AState) (x : Var) (c : ACell) (S : List Origin) :
    (storeCN cn X x c S).env = X.env := by
  unfold storeCN
  split
  · split <;> rfl
  · rfl

/-- The call of design CN does not change a variable other than the reserved one. -/
theorem havocWith_env_ne (cn : CtxN) (X : AState) (E : List Origin) (cov : Origin → Bool)
    {x : Var} (h : x ≠ cn.xe) : (havocWith cn X E cov).env x = X.env x := by
  show fupd X.env cn.xe (uni E (X.env cn.xe)) x = X.env x
  exact fupd_ne _ _ h

/-- In the family, a call of design CN keeps the value of `x`. -/
theorem envX_call {eu : Bool} {K n m : Nat} {X : AState} (h : X.env 0 = [.sym (.root 0) []])
    (s : Site) :
    (astepCN (ctxCN eu K [] frF (famP n m) []) (.call none s [0]) X).env 0 =
      [.sym (.root 0) []] := by
  have hne := famP_x_ne_xe eu K n m
  have hY : (havocCN (ctxCN eu K [] frF (famP n m) []) X [0]).env 0 = [.sym (.root 0) []] := by
    unfold havocCN
    split
    all_goals rw [havocWith_env_ne _ _ _ _ hne, h]
  show renameL s ((havocCN (ctxCN eu K [] frF (famP n m) []) X [0]).env 0) = _
  rw [hY]
  show [renameO s (.sym (.root 0) [])] = _
  rw [renameO_name s rfl]

/-- The root of `x` is a universe origin of the family. -/
theorem famP_root0 (eu : Bool) (K n m : Nat) :
    Origin.sym (.root 0) [] ∈ (ctxCN eu K [] frF (famP n m) []).ctx.origins :=
  (ctxCN_frame eu K [] frF (famP n m) []).roots 0 0 rfl

/-- In the family, a call of design CN writes each universe cell of `x`. -/
theorem writesCN_ge {eu : Bool} {K n m : Nat} {X : AState} (h : X.env 0 = [.sym (.root 0) []]) :
    (ctxCN eu K [] frF (famP n m) []).ctx.cells.length ≤
      writesCN (ctxCN eu K [] frF (famP n m) []) X [0] := by
  have hcov : covN (ctxCN eu K [] frF (famP n m) []) X [0] (.sym (.root 0) []) = true := by
    unfold covN
    generalize hR : closeN (ctxCN eu K [] frF (famP n m) []) X _ _ = r
    cases r with
    | none => rfl
    | some R =>
      show coveredB R _ = true
      refine coveredB_iff.mpr ⟨_, (closeN_spec hR).1 _ ?_, descB_refl _⟩
      refine mem_uni.mpr (Or.inl (mem_uniMap.mpr ⟨0, List.mem_singleton.mpr rfl, ?_⟩))
      rw [h]; exact List.mem_singleton.mpr rfl
  unfold writesCN
  rw [cnCells_length]
  have hpos := List.length_pos_of_mem (List.mem_filter.mpr ⟨famP_root0 eu K n m, hcov⟩)
  exact Nat.le_mul_of_pos_left _ hpos

/-- In the family, the calls of design CN write at least the cells of `x` at each call. -/
theorem totalCN_ge {eu : Bool} {K n m : Nat} :
    ∀ (l : List Site) (X : AState), X.env 0 = [.sym (.root 0) []] →
      l.length * (ctxCN eu K [] frF (famP n m) []).ctx.cells.length ≤
        totalCN (ctxCN eu K [] frF (famP n m) []) 0 l X
  | [], _, _ => by simp [totalCN]
  | s :: l, X, h => by
    show _ ≤ writesCN _ X [0] + totalCN _ 0 l _
    have h1 := writesCN_ge (eu := eu) (K := K) (n := n) (m := m) h
    have h2 := totalCN_ge (eu := eu) (K := K) (n := n) (m := m) l _
      (envX_call (eu := eu) (K := K) (n := n) (m := m) h s)
    rw [List.length_cons, Nat.succ_mul]
    omega

/-- The stores of the family keep the value of `x` in design CN. -/
theorem stores_CN {eu : Bool} {K n m : Nat} :
    ∀ (fs : List Field) (X : AState), X.env 0 = [.sym (.root 0) []] →
      (analyzeCN (ctxCN eu K [] frF (famP n m) []) (storesP 0 1 fs) X).env 0 = [.sym (.root 0) []]
  | [], _, h => h
  | f :: fs, X, h => by
    show (analyzeCN _ (storesP 0 1 fs) (storeCN _ X 0 (.fld f) (X.env 1))).env 0 = _
    exact stores_CN fs _ (by rw [storeCN_env]; exact h)

/-- THE FAMILY, DESIGN CN: the `m` calls write at least `m` times the cells of `x`. -/
theorem fam_CN (eu : Bool) (K n m : Nat) :
    m * (ctxCN eu K [] frF (famP n m) []).ctx.cells.length ≤
      totalCN (ctxCN eu K [] frF (famP n m) []) 0 (ids 1 m)
        (analyzeCN (ctxCN eu K [] frF (famP n m) []) (storesP 0 1 (ids 0 n)) (ainit K frF)) := by
  have := totalCN_ge (eu := eu) (K := K) (n := n) (m := m) (ids 1 m) _
    (stores_CN (eu := eu) (K := K) (n := n) (m := m) (ids 0 n) (ainit K frF) rfl)
  rw [length_ids] at this
  exact this

/-! ## The family: the per-cell design writes each cell of each origin at each call -/

open DirectedAlias.Sound.Havoc

/-- An outer origin is reachable for each call of the per-cell design. -/
theorem reachB_outer (ctx : Ctx) (X : AState) (args : List Var) {o : Origin}
    (h : o.outer = true) : reachB ctx X args o = true := by
  unfold reachB
  generalize closeIter ctx.cells X _ _ = r
  cases r with
  | none => rfl
  | some R => show (o.outer || decide (o ∈ R)) = true; rw [h]; rfl

/-- Each origin of the per-cell universe of the family is outer. -/
theorem famP_outerHR {eu : Bool} {K n m : Nat} {o : Origin}
    (h : o ∈ (ctxHR eu K frF (famP n m) []).origins) : o.outer = true := by
  change o ∈ originsHR K frF (famP n m) _ at h
  rcases List.mem_append.mp h with h | h
  · rcases DirectedAlias.Sound.Recency.mem_originsR.mp h with
      ⟨b, _, ⟨q, _, rfl⟩ | rfl⟩ | ⟨s, hs, _⟩ | ⟨s, _, rfl⟩
    · rfl
    · rfl
    · rw [famP_newSites] at hs; cases hs
    · rfl
  · rcases DirectedAlias.Sound.Havoc.mem_havocCells.mp h with ⟨_, _, _, _, _, _, ⟨_, _, rfl⟩ | rfl⟩
    · rfl
    · rfl

/-- In the family, a per-cell call writes each universe cell of each universe origin. -/
theorem writesHR_eq {eu : Bool} {K n m : Nat} (X : AState) :
    writesHR (ctxHR eu K frF (famP n m) []) X [0] =
      (ctxHR eu K frF (famP n m) []).origins.length * (ctxHR eu K frF (famP n m) []).cells.length := by
  unfold writesHR hrCells
  rw [List.filter_eq_self.mpr (fun a ha => reachB_outer _ X [0] (famP_outerHR ha))]
  exact length_flatMap_const _ _ _ (fun _ _ => List.length_map _)

/-- In the family, the per-cell calls write each universe cell of each origin at each call. -/
theorem totalHR_eq {eu : Bool} {K n m : Nat} :
    ∀ (l : List Site) (X : AState), totalHR (ctxHR eu K frF (famP n m) []) 0 l X =
      l.length * ((ctxHR eu K frF (famP n m) []).origins.length *
        (ctxHR eu K frF (famP n m) []).cells.length)
  | [], _ => by simp [totalHR]
  | s :: l, X => by
    show writesHR _ X [0] + totalHR _ 0 l _ = _
    rw [writesHR_eq, totalHR_eq l, List.length_cons, Nat.succ_mul]
    omega

/-- One term of a sum is at most the sum. -/
theorem le_sum_of_mem {α : Type} (f : α → Nat) {a : α} :
    ∀ {l : List α}, a ∈ l → f a ≤ (l.map f).sum
  | [], h => by cases h
  | b :: l, h => by
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := le_sum_of_mem f h; omega

/-- The per-cell origins of a key list with one key number at least the call sites times the
cells. -/
theorem havocCells_length_ge (K : Nat) {keys : List Origin} {a : Origin} (ha : a ∈ keys)
    (cells : List ACell) (calls : List Site) :
    calls.length * cells.length ≤ (havocCells K keys cells calls).length := by
  unfold havocCells
  rw [List.length_flatMap]
  apply sum_ge_length_mul
  intro s _
  rw [List.length_flatMap]
  refine Nat.le_trans ?_ (le_sum_of_mem _ ha)
  show cells.length ≤ (cells.flatMap _).length
  rw [List.length_flatMap]
  have := sum_ge_length_mul (fun c => ((pathsUpTo cells K).map (Origin.hsym s a c) ++
    [Origin.hdeep s a c]).length) 1 cells (fun c _ => by simp)
  rw [Nat.mul_one] at this
  exact this

/-- The per-cell universe of the family has at least `m` times the cells origins. -/
theorem famP_originsHR (eu : Bool) (K n m : Nat) :
    m * (ctxHR eu K frF (famP n m) []).cells.length ≤ (ctxHR eu K frF (famP n m) []).origins.length := by
  have hkey : Origin.sym (.root 0) [] ∈ keysR K frF (famP n m) (cellsOf ((famP n m).fields ++ [])) :=
    mem_keysR.mpr (Or.inl ⟨.root 0, List.mem_append.mpr (Or.inl (by simp [frF, Frame.roots])),
      Or.inl ⟨[], mem_pathsUpTo.mpr ⟨Nat.zero_le _, fun _ h => by cases h⟩, rfl⟩⟩)
  have h := havocCells_length_ge K hkey (cellsOf ((famP n m).fields ++ [])) (famP n m).callSites
  rw [famP_callSites, length_ids] at h
  change _ ≤ (originsHR K frF (famP n m) _).length
  unfold originsHR
  rw [List.length_append, famP_callSites]
  exact Nat.le_trans h (Nat.le_add_left _ _)

/-- THE FAMILY, THE PER-CELL DESIGN: the `m` calls write `m` times the universe cells, and the
universe has at least `m` times the cells origins. -/
theorem fam_HR (eu : Bool) (K n m : Nat) :
    m * (m * (ctxHR eu K frF (famP n m) []).cells.length) *
        (ctxHR eu K frF (famP n m) []).cells.length ≤
      totalHR (ctxHR eu K frF (famP n m) []) 0 (ids 1 m)
        (analyzeHR (ctxHR eu K frF (famP n m) []) (storesP 0 1 (ids 0 n)) (ainit K frF)) := by
  rw [totalHR_eq, length_ids, Nat.mul_assoc]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (famP_originsHR eu K n m))

/-! ## The separation -/

/-- SEPARATION FAMILY: `n` fields written on the reached argument `x`, then `m` calls `m(x)`.
Design BO writes no heap key; design CN writes at least `m n` heap keys; the per-cell design
writes at least `m^2 n^2` heap keys. (A heap write of CN and of the per-cell design is one
memoized union; see `havocWithO_work_ge` and `havocHRO_work`.) -/
theorem separation (eu : Bool) (K n m : Nat) :
    totalBO (ctxBO eu K [] frF (famP n m) []) 0 (ids 1 m)
        (analyzeBO (ctxBO eu K [] frF (famP n m) []) (storesP 0 1 (ids 0 n)) (ainit K frF)) = 0 ∧
      m * n ≤ totalCN (ctxCN eu K [] frF (famP n m) []) 0 (ids 1 m)
        (analyzeCN (ctxCN eu K [] frF (famP n m) []) (storesP 0 1 (ids 0 n)) (ainit K frF)) ∧
      m * m * n * n ≤ totalHR (ctxHR eu K frF (famP n m) []) 0 (ids 1 m)
        (analyzeHR (ctxHR eu K frF (famP n m) []) (storesP 0 1 (ids 0 n)) (ainit K frF)) := by
  have hc : n ≤ (cellsOf ((famP n m).fields ++ [])).length := famP_cells n m []
  refine ⟨fam_BO eu K n m, ?_, ?_⟩
  · exact Nat.le_trans (Nat.mul_le_mul_left m hc) (fam_CN eu K n m)
  · have h := fam_HR eu K n m
    have e : (ctxHR eu K frF (famP n m) []).cells = cellsOf ((famP n m).fields ++ []) := rfl
    rw [e] at h
    refine Nat.le_trans ?_ h
    have h1 : m * m * n ≤ m * (m * (cellsOf ((famP n m).fields ++ [])).length) := by
      rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hc)
    exact Nat.mul_le_mul h1 hc

end DirectedAlias.Opt.BlockOnly

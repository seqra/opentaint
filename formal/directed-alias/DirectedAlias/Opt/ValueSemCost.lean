import DirectedAlias.Opt.ValueSem
import DirectedAlias.Opt.BlockOnlyCost
import DirectedAlias.Sound.ValueSem.BackwardEq

/-!
# The cost of design VS

The cost model is the work counter of the node table (`Opt/Table.lean`), as in
`Opt/BlockOnlyCost.lean`. The closure `closeN` runs on the denotation of the O state; it is the
same function in designs CN, BO and VS, so it is reported separately.

Results:
* THE PASSIVE CALL (`callVSO_work`, `callVSO_work_ge`): after the closure, two interns and two
  memoized unions on the two reserved keys: at most `(|R| + 5 + 4|U|) + (|V| + 5 + 4|U|)` and at
  least 4 units.
* ZERO HEAP WRITES (`callVSO_frame`, `callVSO_heap_frame`): the O call changes no key of the map
  except the two reserved keys; in particular NO heap key, in every state (design BO writes the
  covered empty cells). `ostepVS_call_frame`: the call statement changes only the two reserved
  keys and the result variable (for a call site that is not an allocation site).
* THE BACKWARD VARIANT (`astepBW_call`): the call does no closure and no union: it is the
  statement `x = unknown@s`.
* THE STORE TEST: forward, at most `K` membership tests in `Etree` and one in `Eval`
  (`uniqueBO_prefixes`, `prefix_lookups_leVS`); backward, one cached test per upstream call
  (`uniqueBO_up`).
* READS are the reads of the recency machine (`ostepVS_load`).
* SEPARATION (`separationVS`): on the family `x = new; t = x.f_0; ...; t = x.f_(n-1); m(x)@1;
  ...; m(x)@m`, the first call of design BO writes at least `n` heap keys (the reached empty
  cells of the new object), design VS writes none; on the family of `Opt/BlockOnlyCost.lean`
  design CN writes at least `m n` and the per-cell design at least `m^2 n^2` heap keys.
* PRECISION COST (`added_answers`): on the read family `x = new; a = x.f; b = x.g; c = x.h` and
  the null family `a = null; b = a; c = null`, design VS answers 4 of 9 queries true that design
  BO answers false; each of them is a real value alias (the same null instance).
-/

namespace DirectedAlias.Opt.ValueSem

open DirectedAlias DirectedAlias.Opt DirectedAlias.Opt.Rec DirectedAlias.Opt.HvRec
open DirectedAlias.Opt.CellNamed DirectedAlias.Opt.BlockOnly
open DirectedAlias.Sound DirectedAlias.Sound.Recency DirectedAlias.Sound.HavocRecency
open DirectedAlias.Sound.CellNamed DirectedAlias.Sound.BlockOnly DirectedAlias.Sound.ValueSem

/-! ## The passive call -/

section call

variable {cb : CtxB} {T : Tbl} {st : OState}

/-- The keys of the passive call are universe keys. -/
theorem setKeys_inU (hc : CtxBOK cb) : ∀ k ∈ setKeys cb, InU cb.cn.ctx k := by
  intro k hk
  simp only [setKeys, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact hc.cn.xeIn
  · exact hc.xvIn

/-- The sets of the passive call are in the universe. -/
theorem hvBO_setKeys_sub (hc : CtxBOK cb) {E V : List Origin} (hE : E ⊆ cb.cn.ctx.origins)
    (hV : V ⊆ cb.cn.ctx.origins) : ∀ k ∈ setKeys cb, hvBO cb E V k ⊆ cb.cn.ctx.origins := by
  intro k hk
  simp only [setKeys, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · intro a ha; simp only [hvBO, ite_true] at ha; exact hE ha
  · intro a ha; simp only [hvBO, ite_eq_right hc.xvNe] at ha; exact hV ha

/-- COST OF THE ADDITION OF TWO SETS TO THE RESERVED KEYS: two interns and two memoized unions. -/
theorem addSets_setKeys_work (hc : CtxBOK cb) (g : T.Good cb.cn.ctx.origins)
    (h : EntOK cb.cn.ctx T st) {E V : List Origin} (hE : E ⊆ cb.cn.ctx.origins)
    (hV : V ⊆ cb.cn.ctx.origins) :
    (addSets cb.cn.ctx (hvBO cb E V) T st (setKeys cb)).1.work ≤
      T.work + (E.length + 5 + 4 * cb.cn.ctx.origins.length) +
        (V.length + 5 + 4 * cb.cn.ctx.origins.length) := by
  have w := addSets_work_le (ctxClosed_of hc) (hvBO cb E V) (setKeys cb) g h
    (setKeys_inU hc) (hvBO_setKeys_sub hc hE hV)
  have e1 : hvBO cb E V (.v cb.cn.xe) = E := by simp [hvBO]
  have e2 : hvBO cb E V (.v cb.xv) = V := by simp [hvBO, hc.xvNe]
  have ek : setKeys cb = [Key.v cb.cn.xe, Key.v cb.xv] := rfl
  rw [ek] at w ⊢
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at w
  rw [e1, e2] at w
  omega

/-- COST OF THE PASSIVE CALL (after the closure): at most `(|E| + 5 + 4|U|) + (|V| + 5 + 4|U|)`
for the contribution `(E, V)` of the call at the denotation of the O state. -/
theorem callVSO_work (hc : CtxBOK cb) (g : T.Good cb.cn.ctx.origins) (h : EntOK cb.cn.ctx T st)
    (hs : Supp cb.cn.ctx (den cb.cn.ctx.K T st)) {args : List Var}
    (hargs : ∀ a ∈ args, a ∈ cb.cn.ctx.vars) :
    (callVSO cb T st args).1.work ≤
      T.work + ((contrib cb (den cb.cn.ctx.K T st) args).1.length + 5 + 4 * cb.cn.ctx.origins.length) +
        ((contrib cb (den cb.cn.ctx.K T st) args).2.length + 5 + 4 * cb.cn.ctx.origins.length) := by
  have hsub := contrib_sub hc hs hargs
  unfold callVSO
  unfold contrib at hsub ⊢
  simp only at hsub ⊢
  split
  · rename_i R hR
    rw [hR] at hsub ⊢
    exact addSets_setKeys_work hc g h hsub.1 hsub.2
  · rename_i hR
    rw [hR] at hsub ⊢
    exact addSets_setKeys_work hc g h hsub.1 hsub.2

/-- The passive call costs at least two units for each of the two reserved keys. -/
theorem callVSO_work_ge (args : List Var) : T.work + 4 ≤ (callVSO cb T st args).1.work := by
  have hg : ∀ f, T.work + 4 ≤ (addSets cb.cn.ctx f T st (setKeys cb)).1.work := by
    intro f
    have := addSets_work_ge cb.cn.ctx f (setKeys cb) T st
    have ek : (setKeys cb).length = 2 := rfl
    rw [ek] at this
    omega
  unfold callVSO
  simp only
  split <;> exact hg _

/-- FRAME OF THE PASSIVE CALL: the O call changes no key of the map except the two reserved
keys. -/
theorem callVSO_frame (args : List Var) {k : Key} (h1 : k ≠ .v cb.cn.xe) (h2 : k ≠ .v cb.xv) :
    oget (callVSO cb T st args).2 k = oget st k := by
  have hk : k ∉ setKeys cb := by
    simp only [setKeys, List.mem_cons, List.not_mem_nil, or_false]
    rintro (e | e)
    · exact h1 e
    · exact h2 e
  unfold callVSO
  simp only
  split <;> exact addSets_oget _ _ _ _ _ _ hk

/-- ZERO HEAP WRITES: the passive call changes no heap key of the map, in every state. -/
theorem callVSO_heap_frame (args : List Var) (o : Origin) (c : ACell) :
    oget (callVSO cb T st args).2 (.h o c) = oget st (.h o c) :=
  callVSO_frame args (fun e => by cases e) (fun e => by cases e)

/-- The passive call changes no variable key except the two reserved keys. -/
theorem callVSO_env_frame (args : List Var) {x : Var} (h1 : x ≠ cb.cn.xe) (h2 : x ≠ cb.xv) :
    oget (callVSO cb T st args).2 (.v x) = oget st (.v x) :=
  callVSO_frame args (fun e => h1 (Key.v.inj e)) (fun e => h2 (Key.v.inj e))

/-- If the universe has no `rNew s`, the O retire of design VS does nothing. -/
theorem retireVO_skip (ctx : Ctx) (s : Site) (T : Tbl) (st : OState)
    (hn : rNew s ∉ ctx.origins) : retireVO ctx s T st = (T, st) := by
  unfold retireVO
  rw [retireO_skip _ _ _ _ hn]
  exact ite_eq_right hn

/-- FRAME OF THE CALL STATEMENT OF DESIGN VS: for a call site that is not an allocation site,
the statement changes no key except the two reserved keys and the result variable. -/
theorem ostepVS_call_frame {i : Nat} {ret : Option Var} {s : Site} {args : List Var}
    (hn : rNew s ∉ cb.cn.ctx.origins) {k : Key} (h1 : k ≠ .v cb.cn.xe) (h2 : k ≠ .v cb.xv)
    (h4 : ∀ x, ret = some x → k ≠ .v x) :
    oget (ostepVS cb i (.call ret s args) T st).2 k = oget st k := by
  simp only [ostepVS]
  rw [retireVO_skip _ _ _ _ hn]
  cases ret with
  | none => exact callVSO_frame args h1 h2
  | some x =>
    show oget (oset _ (.v x) _) k = oget st k
    rw [oget_oset, ite_eq_right (h4 x rfl)]
    exact callVSO_frame args h1 h2

/-- The concept passive call changes no variable except the two reserved ones. -/
theorem callVS_env_ne (X : AState) (args : List Var) {x : Var} (h1 : x ≠ cb.cn.xe)
    (h2 : x ≠ cb.xv) : (callVS cb X args).env x = X.env x := by
  rw [callVS_contrib]
  show fupd (fupd X.env cb.cn.xe _) cb.xv _ x = _
  rw [fupd_ne _ _ h2, fupd_ne _ _ h1]

/-- A read of design VS is the read of the recency machine: no read rule, no extra test. -/
theorem ostepVS_load {i : Nat} (x y : Var) (f : Field) :
    ostepVS cb i (.load x y f) T st = ostepR cb.cn.ctx (.load x y f) T st := rfl

end call

/-! ## The backward variant -/

/-- ZERO WORK AT A CALL IN THE BACKWARD VARIANT: the call is `x = unknown@s` (retire and the
fresh result); it computes no closure and no union. -/
theorem astepBW_call (cb : CtxB) (ora : Oracle) (up : List (Site × List Var)) (i : Nat)
    (x : Var) (s : Site) (args : List Var) (X : AState) :
    astepBW cb ora up i (.call (some x) s args) X = astepVS cb i (.unknown x s) X := rfl

/-- The backward variant does not read the arguments at a call. -/
theorem astepBW_call_args (cb : CtxB) (ora : Oracle) (up : List (Site × List Var)) (i : Nat)
    (ret : Option Var) (s : Site) (args args' : List Var) (X : AState) :
    astepBW cb ora up i (.call ret s args) X = astepBW cb ora up i (.call ret s args') X := rfl

/-! ## The store test -/

/-- A symbolic origin of the universe of design VS has a path of at most `K` cells, so its
prefix test is at most `K` lookups (the null origins are not symbolic). -/
theorem prefix_lookups_leVS {eu : Bool} {K : Nat} {statics : List Root} {fr : Frame} {p : Prog}
    {qf : List Field} {b : ABase} {q : List ACell}
    (h : Origin.sym b q ∈ (ctxVS eu K statics fr p qf).cn.ctx.origins) :
    (List.range q.length).length ≤ K := by
  rcases List.mem_append.mp h with h1 | h1
  · exact prefix_lookups_le h1
  · obtain ⟨_, _, ⟨_, _, e⟩ | e⟩ := mem_nullKids.mp h1 <;> cases e

/-- The exposed test of the on-demand `Etree` is one exposed test for each upstream call. -/
theorem expB_upE (cb : CtxB) (ora : Oracle) (up : List (Site × List Var)) (o : Origin) :
    expB (upE cb ora up) o = up.any (fun c => expB (contrib cb (ora c.1) c.2).1 o) := by
  cases h : expB (upE cb ora up) o with
  | true =>
    cases o with
    | sym b q =>
      obtain ⟨p, hm, hl, hp⟩ := expB_inv h
      obtain ⟨c, hc, h1⟩ := mem_upE.mp hm
      symm
      exact List.any_eq_true.mpr ⟨c, hc, expB_of h1 hl hp⟩
    | _ => simp [expB] at h
  | false =>
    symm
    cases h2 : up.any (fun c => expB (contrib cb (ora c.1) c.2).1 o) with
    | false => rfl
    | true =>
      obtain ⟨c, hc, h3⟩ := List.any_eq_true.mp h2
      have : expB (upE cb ora up) o = true :=
        expB_mono (fun a ha => mem_upE.mpr ⟨c, hc, ha⟩) h3
      rw [h] at this; cases this

/-- The membership test of the on-demand `Eval` is one membership test for each upstream call. -/
theorem mem_upV_any (cb : CtxB) (ora : Oracle) (up : List (Site × List Var)) (o : Origin) :
    decide (o ∈ upV cb ora up) = up.any (fun c => decide (o ∈ (contrib cb (ora c.1) c.2).2)) := by
  cases h : decide (o ∈ upV cb ora up) with
  | true =>
    obtain ⟨c, hc, h1⟩ := mem_upV.mp (of_decide_eq_true h)
    symm
    exact List.any_eq_true.mpr ⟨c, hc, decide_eq_true h1⟩
  | false =>
    symm
    cases h2 : up.any (fun c => decide (o ∈ (contrib cb (ora c.1) c.2).2)) with
    | false => rfl
    | true =>
      obtain ⟨c, hc, h3⟩ := List.any_eq_true.mp h2
      have : decide (o ∈ upV cb ora up) = true :=
        decide_eq_true (mem_upV.mpr ⟨c, hc, of_decide_eq_true h3⟩)
      rw [h] at this; cases this

/-- THE BACKWARD UNIQUENESS TEST BY CACHED TESTS: the test is the recency test and, for each
upstream call, one exposed test in its closure and one membership test in its contents. -/
theorem uniqueBO_up (cb : CtxB) (ora : Oracle) (up : List (Site × List Var)) (once : Site → Bool)
    (eu : Bool) (o : Origin) :
    uniqueBO once eu (upE cb ora up) (upV cb ora up) o =
      ((uniqueR once eu o && !(up.any (fun c => expB (contrib cb (ora c.1) c.2).1 o))) &&
        !(up.any (fun c => decide (o ∈ (contrib cb (ora c.1) c.2).2)))) := by
  unfold uniqueBO uniqueCN
  rw [expB_upE, mem_upV_any]

/-! ## The separation family with an allocation -/

/-- `t = x.f` for each field `f` of the list. -/
def readsP (x t : Var) : List Field → Prog
  | [] => .skip
  | f :: fs => .seq (.stmt (.load t x f)) (readsP x t fs)

/-- THE ALLOCATION FAMILY: `x = new@0; t = x.f_0; ...; t = x.f_(n-1); m(x)@1; ...; m(x)@m`. -/
def famA (n m : Nat) : Prog :=
  .seq (.seq (.stmt (.new 0 0)) (readsP 0 2 (ids 0 n))) (callsP 0 (ids 1 m))

/-- The frame of the allocation family: no variable is bound. -/
def frA : Frame := ⟨[]⟩

/-- The fields of the reads are fields of the family. -/
theorem famA_fields {n m : Nat} {f : Field} (hf : f ∈ ids 0 n) : f ∈ (famA n m).fields := by
  have : ∀ (fs : List Field), f ∈ fs → f ∈ (readsP 0 2 fs).fields := by
    intro fs
    induction fs with
    | nil => intro h; cases h
    | cons g gs ih =>
      intro h
      show f ∈ ((Prog.stmts (.stmt (.load 2 0 g))) ++ (readsP 0 2 gs).stmts).flatMap _
      rw [List.flatMap_append, List.mem_append]
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl (by simp [Prog.stmts, Stmt.fields])
      · exact Or.inr (ih h)
  show f ∈ (((Prog.stmt (.new 0 0)).stmts ++ (readsP 0 2 (ids 0 n)).stmts) ++
    (callsP 0 (ids 1 m)).stmts).flatMap _
  rw [List.flatMap_append, List.flatMap_append, List.mem_append, List.mem_append]
  exact Or.inl (Or.inr (this _ hf))

/-- The cell universe of the allocation family has at least the `n` fields of the reads. -/
theorem famA_cells (n m : Nat) (qf : List Field) :
    n ≤ (cellsOf ((famA n m).fields ++ qf)).length := by
  have h := nodup_length_le (nodup_map_fld (nodup_ids 0 n))
    (m := cellsOf ((famA n m).fields ++ qf)) (by
      intro c hc
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hc
      exact DirectedAlias.Sound.fld_mem_cellsOf (List.mem_append.mpr (Or.inl (famA_fields hf))))
  rw [List.length_map, length_ids] at h
  exact h

/-- The reads keep the heap and the value of `x` (design BO). -/
theorem reads_BO (cb : CtxB) (h02 : (2 : Var) ≠ 0) :
    ∀ (fs : List Field) (X : AState),
      (analyzeBO cb (readsP 0 2 fs) X).heap = X.heap ∧ (analyzeBO cb (readsP 0 2 fs) X).env 0 = X.env 0
  | [], _ => ⟨rfl, rfl⟩
  | f :: fs, X => by
    obtain ⟨h1, h2⟩ := reads_BO cb h02 fs (X.setVar 2 (aread X (X.env 0) (.fld f)))
    refine ⟨h1, ?_⟩
    show (analyzeBO cb (readsP 0 2 fs) (X.setVar 2 (aread X (X.env 0) (.fld f)))).env 0 = X.env 0
    rw [h2]
    exact fupd_ne X.env (aread X (X.env 0) (.fld f)) (fun e => h02 e.symm)

/-- THE FIRST CALL OF DESIGN BO IN THE ALLOCATION FAMILY WRITES AT LEAST `n` HEAP KEYS: the `n`
fields of the new object are empty and reached. -/
theorem famA_BO_first (eu : Bool) (K n m : Nat) :
    n ≤ writesBO (ctxBO eu K [] frA (famA n m) []) (analyzeBO (ctxBO eu K [] frA (famA n m) [])
      (.seq (.stmt (.new 0 0)) (readsP 0 2 (ids 0 n))) (ainit K frA)) [0] := by
  let cb := ctxBO eu K [] frA (famA n m) []
  have hok := ctxBO_stmts eu K [] frA (famA n m) []
  have hnew : rNew 0 ∈ cb.cn.ctx.origins := (hok (.new 0 0) (by simp [famA, Prog.stmts])).newS 0 rfl
  let X0 := (Recency.retire 0 (ainit K frA)).setVar 0 [rNew 0]
  obtain ⟨hH, hE⟩ := reads_BO cb (by decide) (ids 0 n) X0
  have hX : analyzeBO cb (.seq (.stmt (.new 0 0)) (readsP 0 2 (ids 0 n))) (ainit K frA) =
      analyzeBO cb (readsP 0 2 (ids 0 n)) X0 := rfl
  have hemp : ∀ c, (analyzeBO cb (readsP 0 2 (ids 0 n)) X0).heap (rNew 0) c = [] := by
    intro c; rw [hH]
    show (if rNew 0 = rNew 0 then ([] : List Origin) else
      if rNew 0 = rOld 0 then renameL 0 (uni ((ainit K frA).heap (rNew 0) c)
        ((ainit K frA).heap (rOld 0) c)) else renameL 0 ((ainit K frA).heap (rNew 0) c)) = []
    exact ite_eq_left rfl
  have henv : (analyzeBO cb (readsP 0 2 (ids 0 n)) X0).env 0 = [rNew 0] := by
    rw [hE]; exact fupd_same (Recency.retire 0 (ainit K frA)).env 0 [rNew 0]
  show n ≤ writesBO cb (analyzeBO cb (.seq (.stmt (.new 0 0)) (readsP 0 2 (ids 0 n))) (ainit K frA)) [0]
  rw [hX]
  generalize hY : analyzeBO cb (readsP 0 2 (ids 0 n)) X0 = Y at hemp henv
  have hcov : covN cb.cn Y [0] (rNew 0) = true := by
    unfold covN
    generalize hR : closeN cb.cn Y _ _ = r
    cases r with
    | none => rfl
    | some R =>
      show coveredB R _ = true
      refine coveredB_iff.mpr ⟨_, (closeN_spec hR).1 _ ?_, descB_refl _⟩
      refine mem_uni.mpr (Or.inl (mem_uniMap.mpr ⟨0, List.mem_singleton.mpr rfl, ?_⟩))
      rw [henv]; exact List.mem_singleton.mpr rfl
  unfold writesBO emptyCells
  rw [List.length_flatMap]
  refine Nat.le_trans ?_ (le_sum_of_mem _ (List.mem_filter.mpr ⟨hnew, hcov⟩))
  rw [List.length_map, List.filter_eq_self.mpr (fun c _ => by rw [hemp c]; rfl)]
  exact famA_cells n m []

/-- SEPARATION OF DESIGN VS: (1) a call of design VS changes no heap key of the O map, in every
state; (2) on the allocation family, the first call of design BO writes at least `n` heap keys;
(3) on the family of `Opt/BlockOnlyCost.lean`, design CN writes at least `m n` and the per-cell
design at least `m^2 n^2` heap keys. -/
theorem separationVS (eu : Bool) (K n m : Nat) :
    (∀ (cb : CtxB) (T : Tbl) (st : OState) (args : List Var) (o : Origin) (c : ACell),
        oget (callVSO cb T st args).2 (.h o c) = oget st (.h o c)) ∧
      n ≤ writesBO (ctxBO eu K [] frA (famA n m) []) (analyzeBO (ctxBO eu K [] frA (famA n m) [])
        (.seq (.stmt (.new 0 0)) (readsP 0 2 (ids 0 n))) (ainit K frA)) [0] ∧
      m * n ≤ totalCN (ctxCN eu K [] frF (famP n m) []) 0 (ids 1 m)
        (analyzeCN (ctxCN eu K [] frF (famP n m) []) (storesP 0 1 (ids 0 n)) (ainit K frF)) ∧
      m * m * n * n ≤ totalHR (ctxHR eu K frF (famP n m) []) 0 (ids 1 m)
        (analyzeHR (ctxHR eu K frF (famP n m) []) (storesP 0 1 (ids 0 n)) (ainit K frF)) :=
  ⟨fun _ _ _ args o c => callVSO_heap_frame args o c, famA_BO_first eu K n m,
    (separation eu K n m).2.1, (separation eu K n m).2.2⟩

/-! ## The precision cost: the answers that design VS adds -/

section precision

open DirectedAlias.Sound.ValueSem.Examples

/-- The field `g`. -/
abbrev fg : Field := 1
/-- The field `h`. -/
abbrev fh : Field := 2
/-- Variable `c`. -/
abbrev vc : Var := 6

/-- The read family: `x = new@5; a = x.f; b = x.g; c = x.h`. -/
def pReads : Prog :=
  .seq (.stmt (.new U.vx 5)) <| .seq (.stmt (.load U.va U.vx U.ff)) <|
  .seq (.stmt (.load U.vb U.vx fg)) (.stmt (.load vc U.vx fh))

/-- The null family: `a = null; b = a; c = null`. -/
def pNulls : Prog :=
  .seq (.stmt (.null U.va)) <| .seq (.stmt (.copy U.vb U.va)) (.stmt (.null vc))

/-- A query: two variables with paths. -/
abbrev Query := Var × List ACell × Var × List ACell

/-- The queries of the read family: each read against each field, and the reads pairwise. -/
def readQueries : List Query :=
  [(U.va, [], U.vx, [.fld U.ff]), (U.vb, [], U.vx, [.fld fg]), (vc, [], U.vx, [.fld fh]),
   (U.va, [], U.vx, [.fld fg]), (U.va, [], U.vb, []), (U.vb, [], vc, [])]

/-- The queries of the null family: the three pairs. -/
def nullQueries : List Query := [(U.va, [], U.vb, []), (U.va, [], vc, []), (U.vb, [], vc, [])]

/-- The number of queries that an analysis answers true. -/
def countTrue (may : Var → List ACell → Var → List ACell → Bool) (qs : List Query) : Nat :=
  (qs.filter (fun q => may q.1 q.2.1 q.2.2.1 q.2.2.2)).length

/-- THE PRECISION COST OF DESIGN VS: on the read family design VS answers 3 of 6 queries true
(each read with its own field), design BO none; on the null family design VS answers 1 of 3
true (`a ~ b`), design BO none. So design VS adds 4 answers of 9; design BO adds none. -/
theorem added_answers :
    countTrue (mayProgVS true 1 [] U.frE pReads) readQueries = 3 ∧
      countTrue (mayProgBO true 1 [] U.frE pReads) readQueries = 0 ∧
      countTrue (mayProgVS true 1 [] U.frE pNulls) nullQueries = 1 ∧
      countTrue (mayProgBO true 1 [] U.frE pNulls) nullQueries = 0 := by decide +kernel

/-- Each added answer is a real value alias: the reader holds the default null instance of its
cell, and `b` holds the null instance of the null site of `a`. -/
theorem added_answers_real :
    CAliasV (srcL []) [] U.frE pReads U.va [] U.vx [.fld U.ff] ∧
      CAliasV (srcL []) [] U.frE pReads U.vb [] U.vx [.fld fg] ∧
      CAliasV (srcL []) [] U.frE pReads vc [] U.vx [.fld fh] ∧
      CAliasV (srcL []) [] U.frE pNulls U.va [] U.vb [] :=
  ⟨runAliasV_sound (cs := []) (by decide), runAliasV_sound (cs := []) (by decide),
    runAliasV_sound (cs := []) (by decide), runAliasV_sound (cs := []) (by decide)⟩

/-- The added answers are not object aliases: no strict narrow execution aliases the reader and
its cell as objects (the cell holds null), by design CN. -/
theorem added_answers_not_objects (src : Nat → Obj × Cell) :
    ¬ CAliasN src [] U.frE pReads U.va [] U.vx [.fld U.ff] :=
  no_alias_of_mayProgCN src [] true 1 U.frE pReads U.va [] U.vx [.fld U.ff] (by decide +kernel)

end precision

end DirectedAlias.Opt.ValueSem

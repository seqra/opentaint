import DirectedAlias.Sound.ValueSem.Examples
import DirectedAlias.Opt.BlockOnly

/-!
# Optimization O for design VS (value semantics, passive calls)

The concept is `analyzeVS` (`Sound/ValueSem/Concept.lean`). The O state is the map of
`Opt/Prim.lean` with two reserved keys: `Etree` is the node of `.v xe` and `Eval` is the node of
`.v xv` (as design BO).

* The call (`callVSO`): the closure `closeN` on the denotation (as designs CN and BO), then ONE
  `addSets` on the two reserved keys only: two memoized unions. NO heap key changes.
* The store: the O store of design BO (`storeBOO`).
* `new`, `unknown` and the call retire with `retireVO`: the O retire, then the cells of the new
  most recent object get their cell names (`addSets` on the universe cells of `rNew s`).
* `null` at null site `i`: the variable key gets `{null(i)}`.
* The entry state (`initVO`): the O entry state, then each universe cell of each allocation
  origin gets its cell name (the default value of design VS).

Results: `callVSO_rel`, `retireVO_rel`, `ostepVS_rel`, `analyzeVSO_rel`, `mayProgVSO_eq` (O and
the concept give the same may-alias Boolean), `csoundVSO` (O is sound for value aliases).
-/

namespace DirectedAlias.Opt.ValueSem

open DirectedAlias DirectedAlias.Opt DirectedAlias.Opt.Rec DirectedAlias.Opt.HvRec
open DirectedAlias.Opt.CellNamed DirectedAlias.Opt.BlockOnly
open DirectedAlias.Sound DirectedAlias.Sound.Recency DirectedAlias.Sound.HavocRecency
open DirectedAlias.Sound.CellNamed DirectedAlias.Sound.BlockOnly DirectedAlias.Sound.ValueSem

/-! ## The O operations -/

/-- The cell name of a cell key (the default value of design VS). -/
def childSet (K : Nat) : Key → List Origin
  | .v _ => []
  | .h o c => [childCN K o c]

/-- The keys of the universe cells of origin `o`. -/
def cellKeys (ctx : Ctx) (o : Origin) : List Key := ctx.cells.map (Key.h o)

/-- The O retire of design VS: the O retire, then each universe cell of `rNew s` gets its cell
name (if `rNew s` is a universe origin). -/
def retireVO (ctx : Ctx) (s : Site) (T : Tbl) (st : OState) : Tbl × OState :=
  let r := retireO ctx s T st
  if rNew s ∈ ctx.origins then addSets ctx (childSet ctx.K) r.1 r.2 (cellKeys ctx (rNew s)) else r

/-- An origin is an allocation origin. -/
def isAllocB : Origin → Bool
  | .alloc _ => true
  | _ => false

/-- The keys of the universe cells of the universe allocation origins. -/
def allocKeys (ctx : Ctx) : List Key :=
  (ctx.origins.filter isAllocB).flatMap (cellKeys ctx)

/-- The entry O state of design VS: the O entry state, and each universe cell of each
allocation origin gets its cell name. -/
def initVO (ctx : Ctx) (fr : Frame) : Tbl × OState :=
  let i := initO ctx fr
  addSets ctx (childSet ctx.K) i.1 i.2 (allocKeys ctx)

/-- The keys that the passive call writes: the two reserved keys. -/
def setKeys (cb : CtxB) : List Key := [.v cb.cn.xe, .v cb.xv]

/-- THE O PASSIVE CALL: the closure on the denotation, then one `addSets` on the two reserved
keys. No heap key changes. -/
def callVSO (cb : CtxB) (T : Tbl) (st : OState) (args : List Var) : Tbl × OState :=
  let X := den cb.cn.ctx.K T st
  match closeN cb.cn X (cb.cn.ctx.origins.length + 1) (callRoots cb.cn X args) with
  | some R => addSets cb.cn.ctx (hvBO cb R (succsN cb.cn X R)) T st (setKeys cb)
  | none => addSets cb.cn.ctx (hvBO cb cb.cn.ctx.origins cb.cn.ctx.origins) T st (setKeys cb)

/-- The O transfer of one statement in design VS; `i` is the null site of a null statement. -/
def ostepVS (cb : CtxB) (i : Nat) : Stmt → Tbl → OState → Tbl × OState
  | .new x s, T, st =>
    let r := retireVO cb.cn.ctx s T st
    setKey cb.cn.ctx r.1 r.2 (.v x) [rNew s]
  | .unknown x s, T, st =>
    let r := retireVO cb.cn.ctx s T st
    setKey cb.cn.ctx r.1 r.2 (.v x) [.sym (.fresh s) []]
  | .call ret s args, T, st =>
    let a := callVSO cb T st args
    let r := retireVO cb.cn.ctx s a.1 a.2
    match ret with
    | none => r
    | some x => setKey cb.cn.ctx r.1 r.2 (.v x) [.sym (.fresh s) []]
  | .store x f y, T, st => storeBOO cb T st x (.fld f) y
  | .null x, T, st => setKey cb.cn.ctx T st (.v x) [nullO i]
  | st, T, s => ostepR cb.cn.ctx st T s

/-- The O analysis of design VS; `i` is the null site of the first null statement. -/
def analyzeVSO (cb : CtxB) : Nat → Prog → Tbl → OState → Tbl × OState
  | _, .skip, T, st => (T, st)
  | i, .stmt s, T, st => ostepVS cb i s T st
  | i, .seq p q, T, st =>
    let r := analyzeVSO cb i p T st
    analyzeVSO cb (i + p.nulls) q r.1 r.2
  | i, .choice p q, T, st =>
    let r1 := analyzeVSO cb i p T st
    let r2 := analyzeVSO cb (i + p.nulls) q r1.1 st
    let j := joinO cb.cn.ctx r2.1 r1.2 r2.2
    (j.1, j.2.1)
  | i, .loop p, T, st => loopO cb.cn.ctx (analyzeVSO cb i p) cb.cn.ctx.fuel T st

/-! ## Simulation -/

/-- The cell name of a universe cell key is in the universe. -/
theorem childSet_sub {cb : CtxB} (hc : CtxBOK cb) {k : Key} (hk : InU cb.cn.ctx k) :
    childSet cb.cn.ctx.K k ⊆ cb.cn.ctx.origins := by
  cases k with
  | v x => intro a ha; cases ha
  | h o c =>
    intro a ha
    rw [show childSet cb.cn.ctx.K (.h o c) = [childCN cb.cn.ctx.K o c] from rfl,
      List.mem_singleton] at ha
    subst ha
    exact hc.cn.childIn o hk.1 c hk.2

/-- Membership in the cell keys. -/
theorem mem_cellKeys {ctx : Ctx} {o : Origin} {k : Key} :
    k ∈ cellKeys ctx o ↔ ∃ c ∈ ctx.cells, k = .h o c := by
  simp only [cellKeys, List.mem_map]
  constructor
  · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, rfl⟩

/-- The O retire of design VS represents `retireV`. -/
theorem retireVO_rel {cb : CtxB} (hc : CtxBOK cb) (cc : CtxClosed cb.cn.ctx) (hr : RecOK cb.cn.ctx)
    {T : Tbl} (g : T.Good cb.cn.ctx.origins) {st : OState} {X : AState} (hR : Rel cb.cn.ctx T st X)
    (s : Site) :
    (retireVO cb.cn.ctx s T st).1.Good cb.cn.ctx.origins ∧ T.Ext (retireVO cb.cn.ctx s T st).1 ∧
      Rel cb.cn.ctx (retireVO cb.cn.ctx s T st).1 (retireVO cb.cn.ctx s T st).2
        (retireV cb.cn.ctx.K s X) := by
  obtain ⟨g1, e1, r1⟩ := retireO_rel cc hr g hR s
  have hsV := supp_retireV hc hR.supp s
  unfold retireVO
  simp only
  generalize retireO cb.cn.ctx s T st = r at g1 e1 r1
  split
  · rename_i hn
    have hks : ∀ k ∈ cellKeys cb.cn.ctx (rNew s), InU cb.cn.ctx k := by
      intro k hk
      obtain ⟨c, hc1, rfl⟩ := mem_cellKeys.mp hk
      exact ⟨hn, hc1⟩
    obtain ⟨g2, e2, h2, m2⟩ := addSets_spec cc (childSet cb.cn.ctx.K) _ g1 r1.ent hks
      (fun k hk => childSet_sub hc (hks k hk))
    refine ⟨g2, e1.trans e2, rel_of_vals h2 hsV _ m2 ?_⟩
    intro k hk
    cases k with
    | v x =>
      have hnk : Key.v x ∉ cellKeys cb.cn.ctx (rNew s) := fun h => by
        obtain ⟨_, _, e⟩ := mem_cellKeys.mp h; cases e
      rw [ite_eq_right hnk]
      exact r1.agree (.v x) hk
    | h o c =>
      show SetEq _ ((retireV cb.cn.ctx.K s X).heap o c)
      by_cases e : o = rNew s
      · subst e
        have hm : Key.h (rNew s) c ∈ cellKeys cb.cn.ctx (rNew s) := mem_cellKeys.mpr ⟨c, hk.2, rfl⟩
        rw [ite_eq_left hm]
        show SetEq _ (if rNew s = rNew s then [childCN cb.cn.ctx.K (rNew s) c] else _)
        rw [ite_eq_left rfl]
        have h0 := r1.agree (.h (rNew s) c) hk
        change SetEq _ (if rNew s = rNew s then [] else _) at h0
        rw [ite_eq_left rfl] at h0
        intro a
        rw [mem_uni]
        constructor
        · rintro (h | h)
          · cases (h0 a).mp h
          · exact h
        · intro h; exact Or.inr h
      · have hnk : Key.h o c ∉ cellKeys cb.cn.ctx (rNew s) := fun h => by
          obtain ⟨_, _, e2⟩ := mem_cellKeys.mp h; cases e2; exact e rfl
        rw [ite_eq_right hnk]
        show SetEq _ (if o = rNew s then _ else (Recency.retire s X).heap o c)
        rw [ite_eq_right e]
        exact r1.agree (.h o c) hk
  · rename_i hn
    refine ⟨g1, e1, rel_of_vals r1.ent hsV _ (fun k => SetEq.refl _) ?_⟩
    intro k hk
    cases k with
    | v x => exact r1.agree (.v x) hk
    | h o c =>
      show SetEq _ ((retireV cb.cn.ctx.K s X).heap o c)
      have e : o ≠ rNew s := fun e => hn (e ▸ hk.1)
      show SetEq _ (if o = rNew s then _ else (Recency.retire s X).heap o c)
      rw [ite_eq_right e]
      exact r1.agree (.h o c) hk

/-- The O passive call with set-equal sets represents `setSets`. -/
theorem setSetsO_rel {cb : CtxB} (hc : CtxBOK cb) (cc : CtxClosed cb.cn.ctx) {T : Tbl}
    (g : T.Good cb.cn.ctx.origins) {st : OState} {X : AState} (hR : Rel cb.cn.ctx T st X)
    {E E' V V' : List Origin} (hEE : SetEq E' E) (hVV : SetEq V' V)
    (hE : E ⊆ cb.cn.ctx.origins) (hV : V ⊆ cb.cn.ctx.origins) :
    (addSets cb.cn.ctx (hvBO cb E' V') T st (setKeys cb)).1.Good cb.cn.ctx.origins ∧
      T.Ext (addSets cb.cn.ctx (hvBO cb E' V') T st (setKeys cb)).1 ∧
      Rel cb.cn.ctx (addSets cb.cn.ctx (hvBO cb E' V') T st (setKeys cb)).1
        (addSets cb.cn.ctx (hvBO cb E' V') T st (setKeys cb)).2 (setSets cb X E V) := by
  have hmem : ∀ k, k ∈ setKeys cb ↔ k = .v cb.cn.xe ∨ k = .v cb.xv := by
    intro k; simp [setKeys]
  have hks : ∀ k ∈ setKeys cb, InU cb.cn.ctx k := by
    intro k hk
    rcases (hmem k).mp hk with rfl | rfl
    · exact hc.cn.xeIn
    · exact hc.xvIn
  have hhs : ∀ k ∈ setKeys cb, hvBO cb E' V' k ⊆ cb.cn.ctx.origins := by
    intro k hk
    rcases (hmem k).mp hk with rfl | rfl
    · intro a ha
      simp only [hvBO, ite_true] at ha
      exact hE ((hEE a).mp ha)
    · intro a ha
      simp only [hvBO, ite_eq_right hc.xvNe] at ha
      exact hV ((hVV a).mp ha)
  obtain ⟨g2, e2, h2, m2⟩ := addSets_spec cc (hvBO cb E' V') _ g hR.ent hks hhs
  refine ⟨g2, e2, rel_of_vals h2 (supp_setSets hR.supp hE hV) _ m2 ?_⟩
  intro k hk
  cases k with
  | v x =>
    show SetEq _ (fupd (fupd X.env cb.cn.xe (uni E (X.env cb.cn.xe))) cb.xv (uni V (X.env cb.xv)) x)
    by_cases e1 : x = cb.cn.xe
    · subst e1
      rw [ite_eq_left ((hmem _).mpr (Or.inl rfl)), fupd_ne _ _ (Ne.symm hc.xvNe), fupd_same]
      simp only [hvBO, ite_true]
      exact (SetEq.uni (hR.agree (.v _) hk) hEE).trans (uni_comm_set _ _)
    · by_cases e2 : x = cb.xv
      · subst e2
        rw [ite_eq_left ((hmem _).mpr (Or.inr rfl)), fupd_same]
        simp only [hvBO, ite_eq_right e1]
        exact (SetEq.uni (hR.agree (.v _) hk) hVV).trans (uni_comm_set _ _)
      · have : Key.v x ∉ setKeys cb := by
          intro h
          rcases (hmem _).mp h with h | h
          · cases h; exact e1 rfl
          · cases h; exact e2 rfl
        rw [ite_eq_right this, fupd_ne _ _ e2, fupd_ne _ _ e1]
        exact hR.agree (.v x) hk
  | h o c =>
    have : Key.h o c ∉ setKeys cb := by
      intro h
      rcases (hmem _).mp h with h | h <;> cases h
    rw [ite_eq_right this]
    exact hR.agree (.h o c) hk

/-- The O passive call represents the concept passive call. -/
theorem callVSO_rel {cb : CtxB} (hc : CtxBOK cb) (cc : CtxClosed cb.cn.ctx) {T : Tbl}
    (g : T.Good cb.cn.ctx.origins) {st : OState} {X : AState} (hR : Rel cb.cn.ctx T st X)
    {args : List Var} (hargs : ∀ x ∈ args, x ∈ cb.cn.ctx.vars) :
    (callVSO cb T st args).1.Good cb.cn.ctx.origins ∧ T.Ext (callVSO cb T st args).1 ∧
      Rel cb.cn.ctx (callVSO cb T st args).1 (callVSO cb T st args).2 (callVS cb X args) := by
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
  have hrootsU := callRoots_sub hc hR.supp hargs
  unfold callVSO callVS
  simp only
  rcases closeN_congr (cn := cb.cn) hXY (cb.cn.ctx.origins.length + 1) _ _ hroots with
    ⟨h1, h2⟩ | ⟨A, B, h1, h2, h3⟩
  · rw [h1, h2]
    exact setSetsO_rel hc cc g hR (SetEq.refl _) (SetEq.refl _) (fun _ h => h) (fun _ h => h)
  · rw [h1, h2]
    exact setSetsO_rel hc cc g hR h3.symm (succsN_congr hXY h3).symm
      (Opt.CellNamed.closeN_sub hR.supp hrootsU h1) (Opt.CellNamed.succsN_sub hR.supp A)

/-- A statement fits the O universe of design VS: it fits design BO, and a null statement has
its null origin in the universe. -/
structure StmtOKV (cb : CtxB) (i : Nat) (st : Stmt) : Prop where
  bo : StmtOKB cb st
  null : st.nullN = 1 → nullO i ∈ cb.cn.ctx.origins

/-- Each O step of design VS represents the concept step. -/
theorem ostepVS_rel {cb : CtxB} (hc : CtxBOK cb) (cc : CtxClosed cb.cn.ctx) (hr : RecOK cb.cn.ctx)
    {T : Tbl} (g : T.Good cb.cn.ctx.origins) {st : OState} {X : AState}
    (hR : Rel cb.cn.ctx T st X) {i : Nat} {s : Stmt} (ok : StmtOKV cb i s) :
    (ostepVS cb i s T st).1.Good cb.cn.ctx.origins ∧ T.Ext (ostepVS cb i s T st).1 ∧
      Rel cb.cn.ctx (ostepVS cb i s T st).1 (ostepVS cb i s T st).2 (astepVS cb i s X) := by
  have okr : ∀ (st : Stmt), StmtOKB cb st → st.callSite? = none → Opt.Rec.StmtOKR cb.cn.ctx st :=
    fun st ok hn => ⟨ok.vars, ok.fields, ok.newS, ok.freshS,
      fun s hs => by rw [hn] at hs; cases hs⟩
  cases s with
  | new x s =>
    obtain ⟨g1, e1, r1⟩ := retireVO_rel hc cc hr g hR s
    simp only [ostepVS, astepVS]
    generalize retireVO cb.cn.ctx s T st = r at g1 e1 r1
    obtain ⟨g2, e2, r2⟩ := setKey_rel g1 r1 (ok.bo.vars x (by simp [Stmt.vars]))
      (S := [rNew s]) (by intro a ha; simp at ha; subst ha; exact ok.bo.newS s rfl)
    exact ⟨g2, e1.trans e2, r2⟩
  | unknown x s =>
    obtain ⟨g1, e1, r1⟩ := retireVO_rel hc cc hr g hR s
    simp only [ostepVS, astepVS]
    generalize retireVO cb.cn.ctx s T st = r at g1 e1 r1
    obtain ⟨g2, e2, r2⟩ := setKey_rel g1 r1 (ok.bo.vars x (by simp [Stmt.vars]))
      (S := [.sym (.fresh s) []]) (by intro a ha; simp at ha; subst ha; exact ok.bo.freshS s rfl)
    exact ⟨g2, e1.trans e2, r2⟩
  | call ret s args =>
    have hargs : ∀ x ∈ args, x ∈ cb.cn.ctx.vars :=
      fun x hx => ok.bo.vars x (by simp [Stmt.vars, hx])
    obtain ⟨g1, e1, r1⟩ := callVSO_rel hc cc g hR hargs
    obtain ⟨g2, e2, r2⟩ := retireVO_rel hc cc hr g1 r1 s
    simp only [ostepVS, astepVS]
    generalize callVSO cb T st args = a at g1 e1 r1 g2 e2 r2
    generalize retireVO cb.cn.ctx s a.1 a.2 = r at g2 e2 r2
    cases ret with
    | none => exact ⟨g2, e1.trans e2, r2⟩
    | some x =>
      obtain ⟨g3, e3, r3⟩ := setKey_rel g2 r2 (ok.bo.vars x (by simp [Stmt.vars]))
        (S := [.sym (.fresh s) []]) (by intro a ha; simp at ha; subst ha; exact ok.bo.freshS s rfl)
      exact ⟨g3, e1.trans (e2.trans e3), r3⟩
  | store x f y =>
    exact storeBOO_rel hc cc g hR (ok.bo.vars x (by simp [Stmt.vars]))
      (ok.bo.vars y (by simp [Stmt.vars])) (ok.bo.fields f (by simp [Stmt.fields]))
  | null x =>
    exact setKey_rel g hR (ok.bo.vars x (by simp [Stmt.vars])) (S := [nullO i])
      (by intro a ha; rw [List.mem_singleton.mp ha]; exact ok.null rfl)
  | copy x y => exact ostepR_rel cc hr g hR (okr _ ok.bo rfl)
  | load x y f => exact ostepR_rel cc hr g hR (okr _ ok.bo rfl)
  | aload x y => exact ostepR_rel cc hr g hR (okr _ ok.bo rfl)
  | astore x y => exact ostepR_rel cc hr g hR (okr _ ok.bo rfl)

/-- The O analysis of design VS represents the concept analysis on the universe. -/
theorem analyzeVSO_rel {cb : CtxB} (hc : CtxBOK cb) (cc : CtxClosed cb.cn.ctx)
    (hr : RecOK cb.cn.ctx) :
    ∀ (q : Prog) (i : Nat) (T : Tbl) (st : OState) (X : AState), (∀ s ∈ q.stmts, StmtOKB cb s) →
      NullsIn cb i q.nulls → T.Good cb.cn.ctx.origins → Rel cb.cn.ctx T st X →
      (analyzeVSO cb i q T st).1.Good cb.cn.ctx.origins ∧ T.Ext (analyzeVSO cb i q T st).1 ∧
      Rel cb.cn.ctx (analyzeVSO cb i q T st).1 (analyzeVSO cb i q T st).2 (analyzeVS cb i q X)
  | .skip, _, T, _, _, _, _, g, hR => ⟨g, Tbl.Ext.refl T, hR⟩
  | .stmt s, i, _, _, _, ok, hn, g, hR =>
    ostepVS_rel hc cc hr g hR ⟨ok s (by simp [Prog.stmts]),
      fun e => hn i (Nat.le_refl _) (by show i < i + s.nullN; rw [e]; exact Nat.lt_succ_self _)⟩
  | .seq p q, i, T, st, X, ok, hn, g, hR => by
    obtain ⟨g1, e1, r1⟩ := analyzeVSO_rel hc cc hr p i T st X
      (fun st hs => ok st (List.mem_append_left _ hs)) hn.left g hR
    simp only [analyzeVSO, analyzeVS]
    generalize analyzeVSO cb i p T st = r at g1 e1 r1
    obtain ⟨g2, e2, r2⟩ := analyzeVSO_rel hc cc hr q _ r.1 r.2 _
      (fun st hs => ok st (List.mem_append_right _ hs)) hn.right g1 r1
    exact ⟨g2, e1.trans e2, r2⟩
  | .choice p q, i, T, st, X, ok, hn, g, hR => by
    obtain ⟨g1, e1, r1⟩ := analyzeVSO_rel hc cc hr p i T st X
      (fun st hs => ok st (List.mem_append_left _ hs)) hn.left g hR
    simp only [analyzeVSO, analyzeVS]
    generalize analyzeVSO cb i p T st = a at g1 e1 r1
    obtain ⟨g2, e2, r2⟩ := analyzeVSO_rel hc cc hr q _ a.1 st X
      (fun st hs => ok st (List.mem_append_right _ hs)) hn.right g1 (hR.ext e1)
    generalize analyzeVSO cb (i + p.nulls) q a.1 st = b at g2 e2 r2
    obtain ⟨g3, e3, r3⟩ := joinO_rel cc g2 (r1.ext e2) r2
    exact ⟨g3, e1.trans (e2.trans e3), r3⟩
  | .loop p, i, T, st, X, ok, hn, g, hR => by
    simp only [analyzeVSO, analyzeVS]
    exact loopO_rel cc (fun T' st' Y g' hR' => analyzeVSO_rel hc cc hr p i T' st' Y ok hn g' hR')
      cb.cn.ctx.fuel T st X g hR

/-- An allocation origin is a key holder of `allocKeys`. -/
theorem mem_allocKeys {ctx : Ctx} {k : Key} :
    k ∈ allocKeys ctx ↔ ∃ o c, k = .h o c ∧ o ∈ ctx.origins ∧ isAllocB o = true ∧ c ∈ ctx.cells := by
  simp only [allocKeys, cellKeys, List.mem_flatMap, List.mem_filter, List.mem_map]
  constructor
  · rintro ⟨o, ⟨h1, h2⟩, c, h3, rfl⟩; exact ⟨o, c, rfl, h1, h2, h3⟩
  · rintro ⟨o, c, rfl, h1, h2, h3⟩; exact ⟨o, ⟨h1, h2⟩, c, h3, rfl⟩

/-- The entry O state of design VS represents `ainitV`. -/
theorem initVO_rel {cb : CtxB} (hc : CtxBOK cb) (cc : CtxClosed cb.cn.ctx) {fr : Frame}
    (hsupp : Supp cb.cn.ctx (ainit cb.cn.ctx.K fr)) (hsuppV : Supp cb.cn.ctx (ainitV cb.cn.ctx.K fr))
    (hfv : ∀ x ∈ fr.vars, x ∈ cb.cn.ctx.vars) :
    (initVO cb.cn.ctx fr).1.Good cb.cn.ctx.origins ∧
      Rel cb.cn.ctx (initVO cb.cn.ctx fr).1 (initVO cb.cn.ctx fr).2 (ainitV cb.cn.ctx.K fr) := by
  obtain ⟨g0, r0⟩ := initO_rel (ctx := cb.cn.ctx) fr hsupp hfv
  have hks : ∀ k ∈ allocKeys cb.cn.ctx, InU cb.cn.ctx k := by
    intro k hk
    obtain ⟨o, c, rfl, h1, _, h3⟩ := mem_allocKeys.mp hk
    exact ⟨h1, h3⟩
  unfold initVO
  simp only
  generalize initO cb.cn.ctx fr = i at g0 r0
  obtain ⟨g2, _, h2, m2⟩ := addSets_spec cc (childSet cb.cn.ctx.K) _ g0 r0.ent hks
    (fun k hk => childSet_sub hc (hks k hk))
  refine ⟨g2, rel_of_vals h2 hsuppV _ m2 ?_⟩
  intro k hk
  cases k with
  | v x =>
    have hnk : Key.v x ∉ allocKeys cb.cn.ctx := fun h => by
      obtain ⟨_, _, e, _⟩ := mem_allocKeys.mp h; cases e
    rw [ite_eq_right hnk]
    exact r0.agree (.v x) hk
  | h o c =>
    show SetEq _ [childCN cb.cn.ctx.K o c]
    have h0 := r0.agree (.h o c) hk
    change SetEq _ (adefault cb.cn.ctx.K o c) at h0
    by_cases ha : isAllocB o = true
    · obtain ⟨a, rfl⟩ : ∃ a, o = .alloc a := by
        cases o with
        | alloc a => exact ⟨a, rfl⟩
        | _ => cases ha
      have hm : Key.h (.alloc a) c ∈ allocKeys cb.cn.ctx :=
        mem_allocKeys.mpr ⟨_, c, rfl, hk.1, rfl, hk.2⟩
      rw [ite_eq_left hm]
      change SetEq _ ([] : List Origin) at h0
      intro z
      rw [mem_uni]
      constructor
      · rintro (h | h)
        · cases (h0 z).mp h
        · exact h
      · intro h; exact Or.inr h
    · have hnk : Key.h o c ∉ allocKeys cb.cn.ctx := fun h => by
        obtain ⟨o2, c2, e2, _, h2, _⟩ := mem_allocKeys.mp h
        cases e2; exact ha h2
      rw [ite_eq_right hnk]
      rw [adefault_childCN cb.cn.ctx.K (fun x e => by subst e; exact ha rfl) c] at h0
      exact h0

/-! ## Whole programs -/

/-- The final O state of program `p` in design VS. -/
def analyzeProgVSO (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (qf : List Field) : Tbl × OState :=
  let cb := ctxVS eu K statics fr p qf
  let i := initVO cb.cn.ctx fr
  analyzeVSO cb 0 p i.1 i.2

/-- O may-alias of design VS at the end of program `p`. -/
def mayProgVSO (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (x : Var) (px : List ACell) (y : Var) (py : List ACell) : Bool :=
  let r := analyzeProgVSO eu K statics fr p (afields px ++ afields py)
  omay (ctxVS eu K statics fr p (afields px ++ afields py)).cn.ctx r.1 r.2 x px y py

/-- The entry state of design BO has support in the universe of design VS. -/
theorem supp_ainit_VS (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (qf : List Field) : Supp (ctxVS eu K statics fr p qf).cn.ctx (ainit K fr) := by
  have cc := ctxClosed_of (ctxVS_ok eu K statics fr p qf)
  intro k hk
  cases k with
  | v x => exact supp_ainitVS eu K statics fr p qf (.v x) hk
  | h o c => exact cc.dflt o hk.1 c hk.2

/-- For each policy, each list of static roots and each program, the final O state of design
VS represents the final concept state. -/
theorem analyzeProgVSO_rel (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (qf : List Field) :
    (analyzeProgVSO eu K statics fr p qf).1.Good (ctxVS eu K statics fr p qf).cn.ctx.origins ∧
      Rel (ctxVS eu K statics fr p qf).cn.ctx (analyzeProgVSO eu K statics fr p qf).1
        (analyzeProgVSO eu K statics fr p qf).2 (analyzeProgVS eu K statics fr p qf) := by
  have hc := ctxVS_ok eu K statics fr p qf
  have cc := ctxClosed_of hc
  obtain ⟨g0, r0⟩ := initVO_rel hc cc (fr := fr) (supp_ainit_VS eu K statics fr p qf)
    (supp_ainitVS eu K statics fr p qf) (ctxVS_frame eu K statics fr p qf).vars
  obtain ⟨g1, _, r1⟩ := analyzeVSO_rel hc cc (recOK_of hc) p 0 _ _ _
    (ctxVS_stmts eu K statics fr p qf)
    (fun j _ hj => ctxVS_nulls eu K statics fr p qf (by omega)) g0 r0
  exact ⟨g1, r1⟩

/-- O EQUIVALENCE OF DESIGN VS: for both strong-update policies and each list of static roots,
O and the concept give the same may-alias answer on program and frame variables. -/
theorem mayProgVSO_eq (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (x : Var) (px : List ACell) (y : Var) (py : List ACell) (hx : x ∈ p.vars ++ fr.vars)
    (hy : y ∈ p.vars ++ fr.vars) :
    mayProgVSO eu K statics fr p x px y py = mayProgVS eu K statics fr p x px y py := by
  have cc := ctxClosed_of (ctxVS_ok eu K statics fr p (afields px ++ afields py))
  obtain ⟨g, hR⟩ := analyzeProgVSO_rel eu K statics fr p (afields px ++ afields py)
  unfold mayProgVSO mayProgVS
  simp only
  have hv : ∀ z, z ∈ p.vars ++ fr.vars →
      z ∈ (ctxVS eu K statics fr p (afields px ++ afields py)).cn.ctx.vars := by
    intro z hz
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_eraseDups.mpr hz))
  exact omay_eq cc g hR (hv x hx) (hv y hy)
    (Opt.query_cells K fr p _ px (fun f hf => List.mem_append_left _ hf))
    (Opt.query_cells K fr p _ py (fun f hf => List.mem_append_right _ hf))

/-- O of design VS is sound for value aliases: each one-execution value alias of program
variables of the instrumented strict narrow semantics is a may-alias of `mayProgVSO`. -/
theorem csoundVSO (src : Nat → Obj × Cell) (statics : List Root) (eu : Bool) (K : Nat)
    (fr : Frame) (p : Prog) (x : Var) (px : List Cell) (y : Var) (py : List Cell)
    (hx : x ∈ p.vars ++ fr.vars) (hy : y ∈ p.vars ++ fr.vars)
    (h : CAliasV src statics fr p x px y py) :
    mayProgVSO eu K statics fr p x (px.map Cell.abs) y (py.map Cell.abs) = true := by
  rw [mayProgVSO_eq eu K statics fr p x _ y _ hx hy]
  exact csoundVS src statics eu K fr p x px y py h

/-! ## Examples -/

section examples

open DirectedAlias.Sound.ValueSem.Examples

/-- O of design VS gives the answers of the concept on the user's rule, the null-store case and
the distinct null sites. -/
theorem o_answersVS :
    mayProgVSO true 1 [] U.frE pUser U.va [] U.vx [.fld U.ff] = true ∧
      mayProgVSO true 1 [] U.frX pNullStore U.va [] U.vb [] = true ∧
      mayProgVSO true 1 [] U.frE pTwoNull U.va [] U.vb [] = false ∧
      mayProgVSO true 1 [] U.frE pTwoNew U.va [] U.vb [] = false := by decide +kernel

end examples

end DirectedAlias.Opt.ValueSem

import DirectedAlias.Opt.HavocRecency
import DirectedAlias.Sound.CellNamed.Examples

/-!
# Optimization O for design CN (cell-named havoc, narrow reach, exposed set)

The concept is `analyzeCN` (`Sound/CellNamed/Concept.lean`). The O state is the map of
`Opt/Prim.lean`; the exposed set is the node of the reserved variable key `.v xe` (in Kotlin:
one reserved env key that holds a node id).

* The call (`havocCNO`): the closure `closeN` on the denotation of the O state, then one
  `addSets` (`Opt/HavocRecency.lean`): the reserved key gets the closure, and each universe
  cell of each covered universe origin gets its cell name. Then the O retire and the result.
* The store (`storeCNO`): the recency store of O with the uniqueness test `uniqueCN`, which
  reads the exposed set from the reserved key.
* The other statements are the O recency statements (`ostepR`).

Results: `havocCNO_rel` (one call), `ostepCN_rel` (one statement), `analyzeCNO_rel` (the
analysis), `mayProgCNO_eq` (O and the concept give the same may-alias Boolean, for both
strong-update policies and each set of static roots), `csoundCNO` (O is sound under strict
narrow A2).
-/

namespace DirectedAlias.Opt.CellNamed

open DirectedAlias DirectedAlias.Opt DirectedAlias.Opt.Rec DirectedAlias.Opt.HvRec
open DirectedAlias.Sound.Recency DirectedAlias.Sound.HavocRecency DirectedAlias.Sound.CellNamed

/-! ## The O call and store -/

/-- The sets that the cell-named havoc adds: the closure `E` to a variable key (the reserved
key), the cell name to a cell key. -/
def hvCN (K : Nat) (E : List Origin) : Key → List Origin
  | .v _ => E
  | .h o c => [childCN K o c]

/-- The keys of the cell-named havoc: the reserved key, and each universe cell of each covered
universe origin. -/
def hvKeys (cn : CtxN) (cov : Origin → Bool) : List Key :=
  Key.v cn.xe :: (cn.ctx.origins.filter cov).flatMap (fun o => cn.ctx.cells.map (Key.h o))

/-- The O cell-named havoc with exposed set `E` and coverage test `cov`. -/
def havocWithO (cn : CtxN) (T : Tbl) (st : OState) (E : List Origin) (cov : Origin → Bool) :
    Tbl × OState :=
  addSets cn.ctx (hvCN cn.ctx.K E) T st (hvKeys cn cov)

/-- The O cell-named havoc: the closure on the denotation, then `havocWithO`. -/
def havocCNO (cn : CtxN) (T : Tbl) (st : OState) (args : List Var) : Tbl × OState :=
  let X := den cn.ctx.K T st
  match closeN cn X (cn.ctx.origins.length + 1) (callRoots cn X args) with
  | some R => havocWithO cn T st R (coveredB R)
  | none => havocWithO cn T st cn.ctx.origins (fun _ => true)

/-- The O store of design CN: the recency store of O with the uniqueness test `uniqueCN` on
the exposed set of the reserved key. -/
def storeCNO (cn : CtxN) (T : Tbl) (st : OState) (x : Var) (c : ACell) (y : Var) :
    Tbl × OState :=
  match single? (val cn.ctx.K T st (.v x)) with
  | some o =>
    if uniqueCN cn.ctx.once cn.ctx.entryUnique (val cn.ctx.K T st (.v cn.xe)) o then
      let yi := getId cn.ctx T st (.v y)
      (yi.2, oset st (.h o c) yi.1)
    else weakO cn.ctx T st x c y
  | none => weakO cn.ctx T st x c y

/-- The O transfer of one statement in design CN. -/
def ostepCN (cn : CtxN) : Stmt → Tbl → OState → Tbl × OState
  | .call ret s args, T, st =>
    let a := havocCNO cn T st args
    let r := retireO cn.ctx s a.1 a.2
    match ret with
    | none => r
    | some x => setKey cn.ctx r.1 r.2 (.v x) [.sym (.fresh s) []]
  | .store x f y, T, st => storeCNO cn T st x (.fld f) y
  | st, T, s => ostepR cn.ctx st T s

/-- The O analysis of design CN. -/
def analyzeCNO (cn : CtxN) : Prog → Tbl → OState → Tbl × OState
  | .skip, T, st => (T, st)
  | .stmt s, T, st => ostepCN cn s T st
  | .seq p q, T, st =>
    let r := analyzeCNO cn p T st
    analyzeCNO cn q r.1 r.2
  | .choice p q, T, st =>
    let r1 := analyzeCNO cn p T st
    let r2 := analyzeCNO cn q r1.1 st
    let j := joinO cn.ctx r2.1 r1.2 r2.2
    (j.1, j.2.1)
  | .loop p, T, st => loopO cn.ctx (analyzeCNO cn p) cn.ctx.fuel T st

/-! ## Congruence of the closure and of the tests -/

/-- The coverage test depends only on the members of the closure. -/
theorem coveredB_congr {R R' : List Origin} (h : SetEq R R') (u : Origin) :
    coveredB R u = coveredB R' u := by
  cases h1 : coveredB R u with
  | true =>
    obtain ⟨a, ha, hd⟩ := coveredB_iff.mp h1
    exact (coveredB_iff.mpr ⟨a, (h a).mp ha, hd⟩).symm
  | false =>
    cases h2 : coveredB R' u with
    | false => rfl
    | true =>
      obtain ⟨a, ha, hd⟩ := coveredB_iff.mp h2
      rw [coveredB_iff.mpr ⟨a, (h a).mpr ha, hd⟩] at h1
      cases h1

/-- The exposed test depends only on the members of the exposed set. -/
theorem expB_congr {E E' : List Origin} (h : SetEq E E') (u : Origin) : expB E u = expB E' u := by
  cases h1 : expB E u with
  | true => exact (expB_mono (fun a ha => (h a).mp ha) h1).symm
  | false =>
    cases h2 : expB E' u with
    | false => rfl
    | true => rw [expB_mono (fun a ha => (h a).mpr ha) h2] at h1; cases h1

/-- `succsN` gives set-equal results on states that agree on the universe cells. -/
theorem succsN_congr {cn : CtxN} {X Y : AState} {R R' : List Origin}
    (hXY : ∀ o ∈ cn.ctx.origins, ∀ c ∈ cn.ctx.cells, SetEq (X.heap o c) (Y.heap o c))
    (h : SetEq R R') : SetEq (succsN cn X R) (succsN cn Y R') := by
  intro v
  rw [mem_succsN, mem_succsN]
  constructor
  · rintro ⟨u, hu, hc, c, hcc, hv⟩
    exact ⟨u, hu, (coveredB_congr h u) ▸ hc, c, hcc, (hXY u hu c hcc v).mp hv⟩
  · rintro ⟨u, hu, hc, c, hcc, hv⟩
    exact ⟨u, hu, (coveredB_congr h u).symm ▸ hc, c, hcc, (hXY u hu c hcc v).mpr hv⟩

/-- `succsN` of a supported state is in the universe. -/
theorem succsN_sub {cn : CtxN} {X : AState} (hs : Supp cn.ctx X) (R : List Origin) :
    succsN cn X R ⊆ cn.ctx.origins := by
  intro v hv
  obtain ⟨u, hu, _, c, hc, h⟩ := mem_succsN.mp hv
  exact hs (.h u c) ⟨hu, hc⟩ h

/-- `closeN` gives results of the same shape and set-equal results on states that agree on
the universe cells. -/
theorem closeN_congr {cn : CtxN} {X Y : AState}
    (hXY : ∀ o ∈ cn.ctx.origins, ∀ c ∈ cn.ctx.cells, SetEq (X.heap o c) (Y.heap o c)) :
    ∀ (n : Nat) (R R' : List Origin), SetEq R R' →
      (closeN cn X n R = none ∧ closeN cn Y n R' = none) ∨
      ∃ A B, closeN cn X n R = some A ∧ closeN cn Y n R' = some B ∧ SetEq A B
  | 0, _, _, _ => Or.inl ⟨rfl, rfl⟩
  | n + 1, R, R', h => by
    have hs : SetEq (succsN cn X R) (succsN cn Y R') := succsN_congr hXY h
    simp only [closeN]
    rw [subB_congr hs h]
    split
    · exact Or.inr ⟨R, R', rfl, rfl, h⟩
    · exact closeN_congr hXY n _ _ (SetEq.uni hs h)

/-- A closure from a universe start set of a supported state is in the universe. -/
theorem closeN_sub {cn : CtxN} {X : AState} (hs : Supp cn.ctx X) :
    ∀ {n : Nat} {R0 R : List Origin}, R0 ⊆ cn.ctx.origins → closeN cn X n R0 = some R →
      R ⊆ cn.ctx.origins
  | 0, _, _, _, h => by simp [closeN] at h
  | n + 1, R0, R, h0, h => by
    simp only [closeN] at h
    split at h
    · cases h; exact h0
    · exact closeN_sub hs (uni_sub (succsN_sub hs R0) h0) h

/-! ## The concept side -/

/-- The key values after the cell-named havoc. -/
theorem cval_havocWith (cn : CtxN) (X : AState) (E : List Origin) (cov : Origin → Bool)
    (k : Key) :
    cval (havocWith cn X E cov) k =
      match k with
      | .v x => if x = cn.xe then uni E (X.env cn.xe) else X.env x
      | .h o c => if c ∈ cn.ctx.cells ∧ cov o = true then
          uni [childCN cn.ctx.K o c] (X.heap o c) else X.heap o c := by
  cases k with
  | v x =>
    show fupd X.env cn.xe (uni E (X.env cn.xe)) x =
      (if x = cn.xe then uni E (X.env cn.xe) else X.env x)
    by_cases e : x = cn.xe
    · subst e; rw [fupd_same, ite_eq_left rfl]
    · rw [fupd_ne _ _ e, ite_eq_right e]
  | h o c => rfl

/-- The cell-named havoc keeps support if the exposed set is in the universe. -/
theorem supp_havocWith {cn : CtxN} (hc : CtxNOK cn) {X : AState} (hs : Supp cn.ctx X)
    {E : List Origin} (hE : E ⊆ cn.ctx.origins) (cov : Origin → Bool) :
    Supp cn.ctx (havocWith cn X E cov) := by
  intro k hk
  rw [cval_havocWith]
  cases k with
  | v x =>
    simp only
    split
    · rename_i e; subst e; exact uni_sub hE (hs (.v _) hk)
    · exact hs (.v x) hk
  | h o c =>
    simp only
    split
    · exact uni_sub (by intro a ha; simp at ha; subst ha; exact hc.childIn o hk.1 c hk.2)
        (hs (.h o c) hk)
    · exact hs (.h o c) hk

/-- The store of design CN keeps support. -/
theorem supp_storeCN {cn : CtxN} {X : AState} (hs : Supp cn.ctx X) (x : Var) (c : ACell)
    {S : List Origin} (hS : S ⊆ cn.ctx.origins) : Supp cn.ctx (storeCN cn X x c S) := by
  unfold storeCN
  split
  · split
    · intro k hk
      rw [cval_setCell]
      split
      · exact hS
      · exact hs k hk
    · exact hs.weakStore _ c hS
  · exact hs.weakStore _ c hS

/-! ## Simulation -/

/-- The O cell-named havoc with a set-equal exposed set represents the concept havoc. -/
theorem havocWithO_rel {cn : CtxN} (hc : CtxNOK cn) (cc : CtxClosed cn.ctx) {T : Tbl}
    (g : T.Good cn.ctx.origins) {st : OState} {X : AState} (hR : Rel cn.ctx T st X)
    {E E' : List Origin} (hEE : SetEq E' E) (hE : E ⊆ cn.ctx.origins) (cov : Origin → Bool) :
    (havocWithO cn T st E' cov).1.Good cn.ctx.origins ∧ T.Ext (havocWithO cn T st E' cov).1 ∧
      Rel cn.ctx (havocWithO cn T st E' cov).1 (havocWithO cn T st E' cov).2
        (havocWith cn X E cov) := by
  have hmem : ∀ k, k ∈ hvKeys cn cov ↔ k = .v cn.xe ∨
      ∃ o c, k = .h o c ∧ o ∈ cn.ctx.origins ∧ cov o = true ∧ c ∈ cn.ctx.cells := by
    intro k
    simp only [hvKeys, List.mem_cons, List.mem_flatMap, List.mem_filter, List.mem_map]
    constructor
    · rintro (h | ⟨o, ⟨h1, h2⟩, c, h3, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨o, c, rfl, h1, h2, h3⟩
    · rintro (h | ⟨o, c, rfl, h1, h2, h3⟩)
      · exact Or.inl h
      · exact Or.inr ⟨o, ⟨h1, h2⟩, c, h3, rfl⟩
  have hks : ∀ k ∈ hvKeys cn cov, InU cn.ctx k := by
    intro k hk
    rcases (hmem k).mp hk with rfl | ⟨o, c, rfl, h1, _, h3⟩
    · exact hc.xeIn
    · exact ⟨h1, h3⟩
  have hhs : ∀ k ∈ hvKeys cn cov, hvCN cn.ctx.K E' k ⊆ cn.ctx.origins := by
    intro k hk
    rcases (hmem k).mp hk with rfl | ⟨o, c, rfl, h1, _, h3⟩
    · intro a ha; exact hE ((hEE a).mp ha)
    · intro a ha
      simp only [hvCN, List.mem_singleton] at ha
      subst ha
      exact hc.childIn o h1 c h3
  obtain ⟨g2, e2, h2, m2⟩ := addSets_spec cc (hvCN cn.ctx.K E') _ g hR.ent hks hhs
  refine ⟨g2, e2, rel_of_vals h2 (supp_havocWith hc hR.supp hE cov) _ m2 ?_⟩
  intro k hk
  rw [cval_havocWith]
  cases k with
  | v x =>
    simp only
    by_cases e : x = cn.xe
    · subst e
      rw [ite_eq_left ((hmem _).mpr (Or.inl rfl)), ite_eq_left rfl]
      exact (SetEq.uni (hR.agree (.v _) hk) hEE).trans (uni_comm_set _ _)
    · have : Key.v x ∉ hvKeys cn cov := by
        intro h
        rcases (hmem _).mp h with h | ⟨o, c, he, _⟩
        · cases h; exact e rfl
        · cases he
      rw [ite_eq_right this, ite_eq_right e]
      exact hR.agree (.v x) hk
  | h o c =>
    simp only
    have hm : Key.h o c ∈ hvKeys cn cov ↔ (c ∈ cn.ctx.cells ∧ cov o = true) := by
      rw [hmem]
      constructor
      · rintro (h | ⟨o', c', he, _, h2, h3⟩)
        · cases h
        · cases he; exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩; exact Or.inr ⟨o, c, rfl, hk.1, h2, h1⟩
    by_cases h : c ∈ cn.ctx.cells ∧ cov o = true
    · rw [ite_eq_left (hm.mpr h), ite_eq_left h]
      exact (SetEq.uni (hR.agree (.h o c) hk) (SetEq.refl _)).trans (uni_comm_set _ _)
    · rw [ite_eq_right (fun h' => h (hm.mp h')), ite_eq_right h]
      exact hR.agree (.h o c) hk

/-- The O cell-named havoc represents the concept cell-named havoc. -/
theorem havocCNO_rel {cn : CtxN} (hc : CtxNOK cn) (cc : CtxClosed cn.ctx)
    (hst : ∀ r ∈ cn.statics, Origin.sym (.root r) [] ∈ cn.ctx.origins) {T : Tbl}
    (g : T.Good cn.ctx.origins) {st : OState} {X : AState} (hR : Rel cn.ctx T st X)
    {args : List Var} (hargs : ∀ x ∈ args, x ∈ cn.ctx.vars) :
    (havocCNO cn T st args).1.Good cn.ctx.origins ∧ T.Ext (havocCNO cn T st args).1 ∧
      Rel cn.ctx (havocCNO cn T st args).1 (havocCNO cn T st args).2 (havocCN cn X args) := by
  have hag : ∀ k, InU cn.ctx k → SetEq (cval X k) (cval (den cn.ctx.K T st) k) := by
    intro k hk; rw [cval_den]; exact (hR.agree k hk).symm
  have hroots : SetEq (callRoots cn X args) (callRoots cn (den cn.ctx.K T st) args) := by
    refine SetEq.uni ?_ (SetEq.refl _)
    intro o
    rw [mem_uniMap, mem_uniMap]
    constructor
    · rintro ⟨x, hx, h⟩; exact ⟨x, hx, (hag (.v x) (hargs x hx) o).mp h⟩
    · rintro ⟨x, hx, h⟩; exact ⟨x, hx, (hag (.v x) (hargs x hx) o).mpr h⟩
  have hrootsU : callRoots cn X args ⊆ cn.ctx.origins := by
    refine uni_sub ?_ ?_
    · intro o ho
      obtain ⟨x, hx, h⟩ := mem_uniMap.mp ho
      exact hR.supp (.v x) (hargs x hx) h
    · intro o ho
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ho
      exact hst r hr
  unfold havocCNO havocCN
  simp only
  rcases closeN_congr (cn := cn) (fun o ho c hc => hag (.h o c) ⟨ho, hc⟩)
      (cn.ctx.origins.length + 1) _ _ hroots with ⟨h1, h2⟩ | ⟨A, B, h1, h2, h3⟩
  · rw [h1, h2]
    exact havocWithO_rel hc cc g hR (SetEq.refl _) (fun _ h => h) _
  · rw [h1, h2]
    simp only
    have hcov : coveredB B = coveredB A := funext (fun u => (coveredB_congr h3 u).symm)
    rw [hcov]
    exact havocWithO_rel hc cc g hR h3.symm (closeN_sub hR.supp hrootsU h1) _

/-- The O store of design CN represents the concept store. -/
theorem storeCNO_rel {cn : CtxN} (hc : CtxNOK cn) (cc : CtxClosed cn.ctx) {T : Tbl}
    (g : T.Good cn.ctx.origins) {st : OState} {X : AState} (hR : Rel cn.ctx T st X)
    {x y : Var} (hx : x ∈ cn.ctx.vars) (hy : y ∈ cn.ctx.vars) {c : ACell}
    (hcell : c ∈ cn.ctx.cells) :
    (storeCNO cn T st x c y).1.Good cn.ctx.origins ∧ T.Ext (storeCNO cn T st x c y).1 ∧
      Rel cn.ctx (storeCNO cn T st x c y).1 (storeCNO cn T st x c y).2
        (storeCN cn X x c (X.env y)) := by
  have hsg : single? (val cn.ctx.K T st (.v x)) = single? (X.env x) :=
    single?_congr (hR.agree (.v x) hx)
  have hux : ∀ o, uniqueCN cn.ctx.once cn.ctx.entryUnique (val cn.ctx.K T st (.v cn.xe)) o =
      uniqueCN cn.ctx.once cn.ctx.entryUnique (X.env cn.xe) o := by
    intro o
    simp only [uniqueCN]
    rw [expB_congr (hR.agree (.v cn.xe) hc.xeIn) o]
    rfl
  unfold storeCNO storeCN
  rw [← hsg]
  cases hso : single? (val cn.ctx.K T st (.v x)) with
  | none => exact weakO_rel cc g hR hx hy hcell
  | some o =>
    simp only
    rw [hux o]
    split
    · have ho : o ∈ cn.ctx.origins := val_sub cc g st (k := .v x) hx (single?_spec hso).1
      have hk : InU cn.ctx (.h o c) := ⟨ho, hcell⟩
      obtain ⟨g1, e1, i1, m1⟩ := getId_spec cc g hR.ent (k := .v y) hy
      generalize getId cn.ctx T st (.v y) = yi at g1 e1 i1 m1
      refine ⟨g1, e1, rel_of_vals ((hR.ent.ext e1).oset i1 hk) ?_
        (fun k => if k = .h o c then yi.2.mem yi.1 else val cn.ctx.K T st k) ?_ ?_⟩
      · intro k hk'
        rw [cval_setCell]
        split
        · exact hR.supp.env hy
        · exact hR.supp k hk'
      · intro k
        rw [val_oset]
        split
        · exact SetEq.refl _
        · rw [val_ext hR.ent e1]; exact SetEq.refl _
      · intro k hk'
        rw [cval_setCell]
        split
        · exact m1.trans (hR.agree (.v y) hy)
        · exact hR.agree k hk'
    · exact weakO_rel cc g hR hx hy hcell

/-- Each O step of design CN represents the concept step. -/
theorem ostepCN_rel {cn : CtxN} (hc : CtxNOK cn) (cc : CtxClosed cn.ctx) (hr : RecOK cn.ctx)
    (hst : ∀ r ∈ cn.statics, Origin.sym (.root r) [] ∈ cn.ctx.origins) {T : Tbl}
    (g : T.Good cn.ctx.origins) {st : OState} {X : AState} (hR : Rel cn.ctx T st X) {s : Stmt}
    (ok : StmtOKN cn s) :
    (ostepCN cn s T st).1.Good cn.ctx.origins ∧ T.Ext (ostepCN cn s T st).1 ∧
      Rel cn.ctx (ostepCN cn s T st).1 (ostepCN cn s T st).2 (astepCN cn s X) := by
  have okr : ∀ (st : Stmt), StmtOKN cn st → st.callSite? = none → Opt.Rec.StmtOKR cn.ctx st :=
    fun st ok hn => ⟨ok.vars, ok.fields, ok.newS, ok.freshS,
      fun s hs => by rw [hn] at hs; cases hs⟩
  cases s with
  | call ret s args =>
    have hargs : ∀ x ∈ args, x ∈ cn.ctx.vars := fun x hx => ok.vars x (by simp [Stmt.vars, hx])
    obtain ⟨g1, e1, r1⟩ := havocCNO_rel hc cc hst g hR hargs
    obtain ⟨g2, e2, r2⟩ := retireO_rel cc hr g1 r1 s
    simp only [ostepCN, astepCN]
    generalize havocCNO cn T st args = a at g1 e1 r1 g2 e2 r2
    generalize retireO cn.ctx s a.1 a.2 = r at g2 e2 r2
    cases ret with
    | none => exact ⟨g2, e1.trans e2, r2⟩
    | some x =>
      obtain ⟨g3, e3, r3⟩ := setKey_rel g2 r2 (ok.vars x (by simp [Stmt.vars]))
        (S := [.sym (.fresh s) []]) (by intro a ha; simp at ha; subst ha; exact ok.freshS s rfl)
      exact ⟨g3, e1.trans (e2.trans e3), r3⟩
  | store x f y =>
    exact storeCNO_rel hc cc g hR (ok.vars x (by simp [Stmt.vars]))
      (ok.vars y (by simp [Stmt.vars])) (ok.fields f (by simp [Stmt.fields]))
  | new x s => exact ostepR_rel cc hr g hR (okr _ ok rfl)
  | null x => exact ostepR_rel cc hr g hR (okr _ ok rfl)
  | copy x y => exact ostepR_rel cc hr g hR (okr _ ok rfl)
  | load x y f => exact ostepR_rel cc hr g hR (okr _ ok rfl)
  | aload x y => exact ostepR_rel cc hr g hR (okr _ ok rfl)
  | astore x y => exact ostepR_rel cc hr g hR (okr _ ok rfl)
  | unknown x s => exact ostepR_rel cc hr g hR (okr _ ok rfl)

/-- The O analysis of design CN represents the concept analysis on the universe. -/
theorem analyzeCNO_rel {cn : CtxN} (hc : CtxNOK cn) (cc : CtxClosed cn.ctx) (hr : RecOK cn.ctx)
    (hst : ∀ r ∈ cn.statics, Origin.sym (.root r) [] ∈ cn.ctx.origins) :
    ∀ (q : Prog) (T : Tbl) (st : OState) (X : AState), (∀ s ∈ q.stmts, StmtOKN cn s) →
      T.Good cn.ctx.origins → Rel cn.ctx T st X →
      (analyzeCNO cn q T st).1.Good cn.ctx.origins ∧ T.Ext (analyzeCNO cn q T st).1 ∧
      Rel cn.ctx (analyzeCNO cn q T st).1 (analyzeCNO cn q T st).2 (analyzeCN cn q X)
  | .skip, T, _, _, _, g, hR => ⟨g, Tbl.Ext.refl T, hR⟩
  | .stmt s, _, _, _, ok, g, hR => ostepCN_rel hc cc hr hst g hR (ok s (by simp [Prog.stmts]))
  | .seq p q, T, st, X, ok, g, hR => by
    obtain ⟨g1, e1, r1⟩ := analyzeCNO_rel hc cc hr hst p T st X
      (fun st hs => ok st (List.mem_append_left _ hs)) g hR
    simp only [analyzeCNO, analyzeCN]
    generalize analyzeCNO cn p T st = r at g1 e1 r1
    obtain ⟨g2, e2, r2⟩ := analyzeCNO_rel hc cc hr hst q r.1 r.2 _
      (fun st hs => ok st (List.mem_append_right _ hs)) g1 r1
    exact ⟨g2, e1.trans e2, r2⟩
  | .choice p q, T, st, X, ok, g, hR => by
    obtain ⟨g1, e1, r1⟩ := analyzeCNO_rel hc cc hr hst p T st X
      (fun st hs => ok st (List.mem_append_left _ hs)) g hR
    simp only [analyzeCNO, analyzeCN]
    generalize analyzeCNO cn p T st = a at g1 e1 r1
    obtain ⟨g2, e2, r2⟩ := analyzeCNO_rel hc cc hr hst q a.1 st X
      (fun st hs => ok st (List.mem_append_right _ hs)) g1 (hR.ext e1)
    generalize analyzeCNO cn q a.1 st = b at g2 e2 r2
    obtain ⟨g3, e3, r3⟩ := joinO_rel cc g2 (r1.ext e2) r2
    exact ⟨g3, e1.trans (e2.trans e3), r3⟩
  | .loop p, T, st, X, ok, g, hR => by
    simp only [analyzeCNO, analyzeCN]
    exact loopO_rel cc (fun T' st' Y g' hR' => analyzeCNO_rel hc cc hr hst p T' st' Y ok g' hR')
      cn.ctx.fuel T st X g hR

/-! ## Whole programs -/

/-- The context of design CN of a program is closed under default content. -/
theorem ctxClosed_CN (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (qf : List Field) : CtxClosed (ctxCN eu K statics fr p qf).ctx :=
  ⟨fun o ho c hc o' ho' => (ctxCN_ok eu K statics fr p qf).base.base.dflt o ho c hc o' ho',
    (ctxCN_ok eu K statics fr p qf).base.base.elem⟩

/-- The universe of design CN has both recency origins of a site or neither. -/
theorem recOK_CN (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (qf : List Field) : RecOK (ctxCN eu K statics fr p qf).ctx := fun s =>
  ⟨(ctxCN_ok eu K statics fr p qf).base.newOld s, (ctxCN_ok eu K statics fr p qf).base.oldNew s⟩

/-- The static roots of a program are in the universe of design CN. -/
theorem statics_CN (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (qf : List Field) : ∀ r ∈ (ctxCN eu K statics fr p qf).statics,
      Origin.sym (.root r) [] ∈ (ctxCN eu K statics fr p qf).ctx.origins := by
  intro r hr
  show _ ∈ originsCN K fr statics p _
  rw [mem_originsCN]
  refine Or.inl ⟨.root r, List.mem_append.mpr (Or.inl ?_), Or.inl ⟨[], ?_, rfl⟩⟩
  · exact List.mem_map.mpr ⟨r, List.mem_append.mpr (Or.inr hr), rfl⟩
  · exact mem_pathsUpTo.mpr ⟨Nat.zero_le _, fun _ h => by cases h⟩

/-- The entry state has support in the context of design CN. -/
theorem supp_ainitCN (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (qf : List Field) : Supp (ctxCN eu K statics fr p qf).ctx (ainit K fr) := by
  intro k hk
  cases k with
  | v x =>
    intro o ho
    show o ∈ originsCN K fr statics p _
    change o ∈ (match fr.root? x with | some r => [Origin.sym (.root r) []] | none => []) at ho
    cases e : fr.root? x with
    | none => rw [e] at ho; cases ho
    | some r =>
      rw [e, List.mem_singleton] at ho
      subst ho
      exact (ctxCN_frame eu K statics fr p qf).roots x r e
  | h o c => exact (ctxClosed_CN eu K statics fr p qf).dflt o hk.1 c hk.2

/-- The final O state of program `p` in design CN. -/
def analyzeProgCNO (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (qf : List Field) : Tbl × OState :=
  let cn := ctxCN eu K statics fr p qf
  let i := initO cn.ctx fr
  analyzeCNO cn p i.1 i.2

/-- O may-alias of design CN at the end of program `p`. -/
def mayProgCNO (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (x : Var) (px : List ACell) (y : Var) (py : List ACell) : Bool :=
  let r := analyzeProgCNO eu K statics fr p (afields px ++ afields py)
  omay (ctxCN eu K statics fr p (afields px ++ afields py)).ctx r.1 r.2 x px y py

/-- For each policy, each set of static roots and each program, the final O state of design
CN represents the final concept state. -/
theorem analyzeProgCNO_rel (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (qf : List Field) :
    (analyzeProgCNO eu K statics fr p qf).1.Good (ctxCN eu K statics fr p qf).ctx.origins ∧
      Rel (ctxCN eu K statics fr p qf).ctx (analyzeProgCNO eu K statics fr p qf).1
        (analyzeProgCNO eu K statics fr p qf).2 (analyzeProgCN eu K statics fr p qf) := by
  have cc := ctxClosed_CN eu K statics fr p qf
  obtain ⟨g0, r0⟩ := initO_rel (ctx := (ctxCN eu K statics fr p qf).ctx) fr
    (supp_ainitCN eu K statics fr p qf) (ctxCN_frame eu K statics fr p qf).vars
  obtain ⟨g1, _, r1⟩ := analyzeCNO_rel (ctxCN_ok eu K statics fr p qf) cc
    (recOK_CN eu K statics fr p qf) (statics_CN eu K statics fr p qf) p _ _ _
    (ctxCN_stmts eu K statics fr p qf) g0 r0
  exact ⟨g1, r1⟩

/-- O EQUIVALENCE OF DESIGN CN: for both strong-update policies and each set of static roots,
O and the concept give the same may-alias answer on program and frame variables. -/
theorem mayProgCNO_eq (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (x : Var) (px : List ACell) (y : Var) (py : List ACell) (hx : x ∈ p.vars ++ fr.vars)
    (hy : y ∈ p.vars ++ fr.vars) :
    mayProgCNO eu K statics fr p x px y py = mayProgCN eu K statics fr p x px y py := by
  have cc := ctxClosed_CN eu K statics fr p (afields px ++ afields py)
  obtain ⟨g, hR⟩ := analyzeProgCNO_rel eu K statics fr p (afields px ++ afields py)
  unfold mayProgCNO mayProgCN
  simp only
  have hv : ∀ z, z ∈ p.vars ++ fr.vars →
      z ∈ (ctxCN eu K statics fr p (afields px ++ afields py)).ctx.vars := by
    intro z hz
    show z ∈ freshVar _ :: (p.vars ++ fr.vars).eraseDups
    exact List.mem_cons_of_mem _ (List.mem_eraseDups.mpr hz)
  exact omay_eq cc g hR (hv x hx) (hv y hy)
    (Opt.query_cells K fr p _ px (fun f hf => List.mem_append_left _ hf))
    (Opt.query_cells K fr p _ py (fun f hf => List.mem_append_right _ hf))

/-- O of design CN is sound under strict narrow A2: each strict narrow one-execution alias of
program variables is a may-alias of `mayProgCNO`. -/
theorem csoundCNO (src : Nat → Obj × Cell) (statics : List Root) (eu : Bool) (K : Nat)
    (fr : Frame) (p : Prog) (x : Var) (px : List Cell) (y : Var) (py : List Cell)
    (hx : x ∈ p.vars ++ fr.vars) (hy : y ∈ p.vars ++ fr.vars)
    (h : CAliasN src statics fr p x px y py) :
    mayProgCNO eu K statics fr p x (px.map Cell.abs) y (py.map Cell.abs) = true := by
  rw [mayProgCNO_eq eu K statics fr p x _ y _ hx hy]
  exact csoundCN src statics eu K fr p x px y py h

/-! ## Examples -/

section examples

open DirectedAlias.Sound.CellNamed.Examples

/-- O of design CN gives the answers of the concept on the narrow-reach and loss examples. -/
theorem o_answersCN :
    mayProgCNO true 1 [] frN (pGain []) vt [.fld fg] vu [] = false ∧
      mayProgCNO true 1 [] frN pL1 vt [.fld fg] vu [] = true ∧
      mayProgCNO true 0 [] frN pL2 vt [] vw [] = true ∧
      mayProgCNO true 0 [] frN pL3 va [] vc [] = true ∧
      mayProgCNO true 0 [] frN pDead vb [] vd [] = true := by decide +kernel

end examples

end DirectedAlias.Opt.CellNamed

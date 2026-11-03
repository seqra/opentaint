import DirectedAlias.Sound.BlockOnly.Examples
import DirectedAlias.Opt.CellNamed

/-!
# Optimization O for design BO (the call only blocks strong updates)

The concept is `analyzeBO` (`Sound/BlockOnly/Concept.lean`). The O state is the map of
`Opt/Prim.lean`. `Etree` is the node of the reserved variable key `.v xe`, and `Eval` is the
node of the reserved variable key `.v xv` (in Kotlin: two reserved env keys that hold node ids).

* The call (`callBOO`): the closure `closeN` on the denotation of the O state (the same as in
  design CN), then one `addSets` on the keys `callKeys`: the two reserved keys get the closure
  and the contents of the covered cells (two memoized unions), and each covered universe cell
  whose value is EMPTY gets its cell name. No other key of the map changes. Then the O retire
  and the result.
* The store (`storeBOO`): the recency store of O with the uniqueness test `uniqueBO`, which
  reads both reserved keys.
* The other statements are the O recency statements (`ostepR`).

Results: `callBOO_rel` (one call), `ostepBO_rel` (one statement), `analyzeBOO_rel` (the
analysis), `mayProgBOO_eq` (O and the concept give the same may-alias Boolean, for both
strong-update policies and each list of static roots), `csoundBOO` (O is sound under strict
narrow A2).
-/

namespace DirectedAlias.Opt.BlockOnly

open DirectedAlias DirectedAlias.Opt DirectedAlias.Opt.Rec DirectedAlias.Opt.HvRec
open DirectedAlias.Opt.CellNamed
open DirectedAlias.Sound.Recency DirectedAlias.Sound.HavocRecency DirectedAlias.Sound.CellNamed
open DirectedAlias.Sound.BlockOnly

/-! ## The O call and store -/

/-- The sets that the call of design BO adds: `E` to the key of `Etree`, `V` to the other
variable key (the key of `Eval`), and the cell name to a cell key. -/
def hvBO (cb : CtxB) (E V : List Origin) : Key → List Origin
  | .v x => if x = cb.cn.xe then E else V
  | .h o c => [childCN cb.cn.ctx.K o c]

/-- The keys of the covered universe cells whose value is empty. -/
def emptyKeys (cb : CtxB) (T : Tbl) (st : OState) (cov : Origin → Bool) : List Key :=
  (cb.cn.ctx.origins.filter cov).flatMap (fun o =>
    (cb.cn.ctx.cells.filter (fun c => (val cb.cn.ctx.K T st (.h o c)).isEmpty)).map (Key.h o))

/-- The keys that the call of design BO writes: the two reserved keys, and the covered empty
universe cells. -/
def callKeys (cb : CtxB) (T : Tbl) (st : OState) (cov : Origin → Bool) : List Key :=
  Key.v cb.cn.xe :: Key.v cb.xv :: emptyKeys cb T st cov

/-- The O call of design BO with closure `E`, contents `V` and coverage `cov`. -/
def callWithO (cb : CtxB) (T : Tbl) (st : OState) (E V : List Origin) (cov : Origin → Bool) :
    Tbl × OState :=
  addSets cb.cn.ctx (hvBO cb E V) T st (callKeys cb T st cov)

/-- The O call of design BO: the closure on the denotation, then `callWithO`. -/
def callBOO (cb : CtxB) (T : Tbl) (st : OState) (args : List Var) : Tbl × OState :=
  let X := den cb.cn.ctx.K T st
  match closeN cb.cn X (cb.cn.ctx.origins.length + 1) (callRoots cb.cn X args) with
  | some R => callWithO cb T st R (succsN cb.cn X R) (coveredB R)
  | none => callWithO cb T st cb.cn.ctx.origins cb.cn.ctx.origins (fun _ => true)

/-- The O store of design BO: the recency store of O with the uniqueness test `uniqueBO` on
the two reserved keys. -/
def storeBOO (cb : CtxB) (T : Tbl) (st : OState) (x : Var) (c : ACell) (y : Var) :
    Tbl × OState :=
  match single? (val cb.cn.ctx.K T st (.v x)) with
  | some o =>
    if uniqueBO cb.cn.ctx.once cb.cn.ctx.entryUnique (val cb.cn.ctx.K T st (.v cb.cn.xe))
        (val cb.cn.ctx.K T st (.v cb.xv)) o then
      let yi := getId cb.cn.ctx T st (.v y)
      (yi.2, oset st (.h o c) yi.1)
    else weakO cb.cn.ctx T st x c y
  | none => weakO cb.cn.ctx T st x c y

/-- The O transfer of one statement in design BO. -/
def ostepBO (cb : CtxB) : Stmt → Tbl → OState → Tbl × OState
  | .call ret s args, T, st =>
    let a := callBOO cb T st args
    let r := retireO cb.cn.ctx s a.1 a.2
    match ret with
    | none => r
    | some x => setKey cb.cn.ctx r.1 r.2 (.v x) [.sym (.fresh s) []]
  | .store x f y, T, st => storeBOO cb T st x (.fld f) y
  | st, T, s => ostepR cb.cn.ctx st T s

/-- The O analysis of design BO. -/
def analyzeBOO (cb : CtxB) : Prog → Tbl → OState → Tbl × OState
  | .skip, T, st => (T, st)
  | .stmt s, T, st => ostepBO cb s T st
  | .seq p q, T, st =>
    let r := analyzeBOO cb p T st
    analyzeBOO cb q r.1 r.2
  | .choice p q, T, st =>
    let r1 := analyzeBOO cb p T st
    let r2 := analyzeBOO cb q r1.1 st
    let j := joinO cb.cn.ctx r2.1 r1.2 r2.2
    (j.1, j.2.1)
  | .loop p, T, st => loopO cb.cn.ctx (analyzeBOO cb p) cb.cn.ctx.fuel T st

/-! ## Keys -/

/-- Membership in `emptyKeys`. -/
theorem mem_emptyKeys {cb : CtxB} {T : Tbl} {st : OState} {cov : Origin → Bool} {k : Key} :
    k ∈ emptyKeys cb T st cov ↔ ∃ o c, k = .h o c ∧ o ∈ cb.cn.ctx.origins ∧ cov o = true ∧
      c ∈ cb.cn.ctx.cells ∧ val cb.cn.ctx.K T st (.h o c) = [] := by
  simp only [emptyKeys, List.mem_flatMap, List.mem_filter, List.mem_map, List.isEmpty_iff]
  constructor
  · rintro ⟨o, ⟨h1, h2⟩, c, ⟨h3, h4⟩, rfl⟩; exact ⟨o, c, rfl, h1, h2, h3, h4⟩
  · rintro ⟨o, c, rfl, h1, h2, h3, h4⟩; exact ⟨o, ⟨h1, h2⟩, c, ⟨h3, h4⟩, rfl⟩

/-- Set-equal lists are both empty or both not empty. -/
theorem setEq_nil {α : Type} {l m : List α} (h : SetEq l m) : l = [] ↔ m = [] := by
  constructor
  · intro e; subst e
    cases m with
    | nil => rfl
    | cons a _ => cases (h a).mpr List.mem_cons_self
  · intro e; subst e
    cases l with
    | nil => rfl
    | cons a _ => cases (h a).mp List.mem_cons_self

/-- The uniqueness test of design BO depends only on the members of the two sets. -/
theorem uniqueBO_congr {once : Site → Bool} {eu : Bool} {E E' V V' : List Origin}
    (hE : SetEq E E') (hV : SetEq V V') (o : Origin) :
    uniqueBO once eu E V o = uniqueBO once eu E' V' o := by
  unfold uniqueBO uniqueCN
  rw [expB_congr hE o]
  by_cases h : o ∈ V
  · rw [decide_eq_true h, decide_eq_true ((hV o).mp h)]
  · rw [decide_eq_false h, decide_eq_false (fun h' => h ((hV o).mpr h'))]

/-! ## Simulation -/

/-- The O call with set-equal sets represents the concept call. -/
theorem callWithO_rel {cb : CtxB} (hc : CtxBOK cb) (cc : CtxClosed cb.cn.ctx) {T : Tbl}
    (g : T.Good cb.cn.ctx.origins) {st : OState} {X : AState} (hR : Rel cb.cn.ctx T st X)
    {E E' V V' : List Origin} (hEE : SetEq E' E) (hVV : SetEq V' V)
    (hE : E ⊆ cb.cn.ctx.origins) (hV : V ⊆ cb.cn.ctx.origins) (cov : Origin → Bool) :
    (callWithO cb T st E' V' cov).1.Good cb.cn.ctx.origins ∧
      T.Ext (callWithO cb T st E' V' cov).1 ∧
      Rel cb.cn.ctx (callWithO cb T st E' V' cov).1 (callWithO cb T st E' V' cov).2
        (callWith cb X E V cov) := by
  have hmem : ∀ k, k ∈ callKeys cb T st cov ↔ k = .v cb.cn.xe ∨ k = .v cb.xv ∨
      k ∈ emptyKeys cb T st cov := by
    intro k; simp [callKeys]
  have hks : ∀ k ∈ callKeys cb T st cov, InU cb.cn.ctx k := by
    intro k hk
    rcases (hmem k).mp hk with rfl | rfl | h
    · exact hc.cn.xeIn
    · exact hc.xvIn
    · obtain ⟨o, c, rfl, h1, _, h3, _⟩ := mem_emptyKeys.mp h
      exact ⟨h1, h3⟩
  have hhs : ∀ k ∈ callKeys cb T st cov, hvBO cb E' V' k ⊆ cb.cn.ctx.origins := by
    intro k hk
    rcases (hmem k).mp hk with rfl | rfl | h
    · intro a ha
      simp only [hvBO, ite_true] at ha
      exact hE ((hEE a).mp ha)
    · intro a ha
      simp only [hvBO, ite_eq_right hc.xvNe] at ha
      exact hV ((hVV a).mp ha)
    · obtain ⟨o, c, rfl, h1, _, h3, _⟩ := mem_emptyKeys.mp h
      intro a ha
      simp only [hvBO, List.mem_singleton] at ha
      subst ha
      exact hc.cn.childIn o h1 c h3
  obtain ⟨g2, e2, h2, m2⟩ := addSets_spec cc (hvBO cb E' V') _ g hR.ent hks hhs
  refine ⟨g2, e2, rel_of_vals h2 (supp_callWith hc hR.supp hE hV) _ m2 ?_⟩
  intro k hk
  cases k with
  | v x =>
    show SetEq _ ((callWith cb X E V cov).env x)
    by_cases e1 : x = cb.cn.xe
    · subst e1
      rw [ite_eq_left ((hmem _).mpr (Or.inl rfl)), callWith_xe hc]
      simp only [hvBO, ite_true]
      exact (SetEq.uni (hR.agree (.v _) hk) hEE).trans (uni_comm_set _ _)
    · by_cases e2 : x = cb.xv
      · subst e2
        rw [ite_eq_left ((hmem _).mpr (Or.inr (Or.inl rfl))), callWith_xv]
        simp only [hvBO, ite_eq_right e1]
        exact (SetEq.uni (hR.agree (.v _) hk) hVV).trans (uni_comm_set _ _)
      · have : Key.v x ∉ callKeys cb T st cov := by
          intro h
          rcases (hmem _).mp h with h | h | h
          · cases h; exact e1 rfl
          · cases h; exact e2 rfl
          · obtain ⟨o, c, he, _⟩ := mem_emptyKeys.mp h; cases he
        rw [ite_eq_right this, callWith_env_ne x e1 e2]
        exact hR.agree (.v x) hk
  | h o c =>
    show SetEq _ ((callWith cb X E V cov).heap o c)
    have hag := hR.agree (.h o c) hk
    have hm : Key.h o c ∈ callKeys cb T st cov ↔
        (cov o = true ∧ val cb.cn.ctx.K T st (.h o c) = []) := by
      rw [hmem]
      constructor
      · rintro (h | h | h)
        · cases h
        · cases h
        · obtain ⟨o', c', he, _, h2, _, h4⟩ := mem_emptyKeys.mp h
          cases he; exact ⟨h2, h4⟩
      · rintro ⟨h1, h2⟩
        exact Or.inr (Or.inr (mem_emptyKeys.mpr ⟨o, c, rfl, hk.1, h1, hk.2, h2⟩))
    rcases callWith_heap_cases (X := X) (E := E) (V := V) (cov := cov) o c with
      ⟨_, h2, h3, e⟩ | ⟨hn, e⟩
    · have hv0 : val cb.cn.ctx.K T st (.h o c) = [] := (setEq_nil hag).mpr h3
      rw [ite_eq_left (hm.mpr ⟨h2, hv0⟩), e, hv0]
      exact SetEq.refl _
    · have hnot : ¬ (cov o = true ∧ val cb.cn.ctx.K T st (.h o c) = []) := by
        rintro ⟨h1, h2⟩
        exact hn ⟨hk.2, h1, (setEq_nil hag).mp h2⟩
      rw [ite_eq_right (fun h => hnot (hm.mp h)), e]
      exact hag

/-- The O call of design BO represents the concept call. -/
theorem callBOO_rel {cb : CtxB} (hc : CtxBOK cb) (cc : CtxClosed cb.cn.ctx) {T : Tbl}
    (g : T.Good cb.cn.ctx.origins) {st : OState} {X : AState} (hR : Rel cb.cn.ctx T st X)
    {args : List Var} (hargs : ∀ x ∈ args, x ∈ cb.cn.ctx.vars) :
    (callBOO cb T st args).1.Good cb.cn.ctx.origins ∧ T.Ext (callBOO cb T st args).1 ∧
      Rel cb.cn.ctx (callBOO cb T st args).1 (callBOO cb T st args).2 (callBO cb X args) := by
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
  unfold callBOO callBO
  simp only
  rcases closeN_congr (cn := cb.cn) hXY (cb.cn.ctx.origins.length + 1) _ _ hroots with
    ⟨h1, h2⟩ | ⟨A, B, h1, h2, h3⟩
  · rw [h1, h2]
    exact callWithO_rel hc cc g hR (SetEq.refl _) (SetEq.refl _) (fun _ h => h) (fun _ h => h) _
  · rw [h1, h2]
    simp only
    have hcov : coveredB B = coveredB A := funext (fun u => (coveredB_congr h3 u).symm)
    rw [hcov]
    exact callWithO_rel hc cc g hR h3.symm (succsN_congr hXY h3).symm
      (Opt.CellNamed.closeN_sub hR.supp hrootsU h1) (Opt.CellNamed.succsN_sub hR.supp A) _

/-- The O store of design BO represents the concept store. -/
theorem storeBOO_rel {cb : CtxB} (hc : CtxBOK cb) (cc : CtxClosed cb.cn.ctx) {T : Tbl}
    (g : T.Good cb.cn.ctx.origins) {st : OState} {X : AState} (hR : Rel cb.cn.ctx T st X)
    {x y : Var} (hx : x ∈ cb.cn.ctx.vars) (hy : y ∈ cb.cn.ctx.vars) {c : ACell}
    (hcell : c ∈ cb.cn.ctx.cells) :
    (storeBOO cb T st x c y).1.Good cb.cn.ctx.origins ∧ T.Ext (storeBOO cb T st x c y).1 ∧
      Rel cb.cn.ctx (storeBOO cb T st x c y).1 (storeBOO cb T st x c y).2
        (storeBO cb X x c (X.env y)) := by
  have hsg : single? (val cb.cn.ctx.K T st (.v x)) = single? (X.env x) :=
    single?_congr (hR.agree (.v x) hx)
  have hux : ∀ o, uniqueBO cb.cn.ctx.once cb.cn.ctx.entryUnique
      (val cb.cn.ctx.K T st (.v cb.cn.xe)) (val cb.cn.ctx.K T st (.v cb.xv)) o =
      uniqueBO cb.cn.ctx.once cb.cn.ctx.entryUnique (X.env cb.cn.xe) (X.env cb.xv) o :=
    uniqueBO_congr (hR.agree (.v cb.cn.xe) hc.cn.xeIn) (hR.agree (.v cb.xv) hc.xvIn)
  unfold storeBOO storeBO
  rw [← hsg]
  cases hso : single? (val cb.cn.ctx.K T st (.v x)) with
  | none => exact weakO_rel cc g hR hx hy hcell
  | some o =>
    simp only
    rw [hux o]
    split
    · have ho : o ∈ cb.cn.ctx.origins := val_sub cc g st (k := .v x) hx (single?_spec hso).1
      have hk : InU cb.cn.ctx (.h o c) := ⟨ho, hcell⟩
      obtain ⟨g1, e1, i1, m1⟩ := getId_spec cc g hR.ent (k := .v y) hy
      generalize getId cb.cn.ctx T st (.v y) = yi at g1 e1 i1 m1
      refine ⟨g1, e1, rel_of_vals ((hR.ent.ext e1).oset i1 hk) ?_
        (fun k => if k = .h o c then yi.2.mem yi.1 else val cb.cn.ctx.K T st k) ?_ ?_⟩
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

/-- Each O step of design BO represents the concept step. -/
theorem ostepBO_rel {cb : CtxB} (hc : CtxBOK cb) (cc : CtxClosed cb.cn.ctx) (hr : RecOK cb.cn.ctx)
    {T : Tbl} (g : T.Good cb.cn.ctx.origins) {st : OState} {X : AState}
    (hR : Rel cb.cn.ctx T st X) {s : Stmt} (ok : StmtOKB cb s) :
    (ostepBO cb s T st).1.Good cb.cn.ctx.origins ∧ T.Ext (ostepBO cb s T st).1 ∧
      Rel cb.cn.ctx (ostepBO cb s T st).1 (ostepBO cb s T st).2 (astepBO cb s X) := by
  have okr : ∀ (st : Stmt), StmtOKB cb st → st.callSite? = none → Opt.Rec.StmtOKR cb.cn.ctx st :=
    fun st ok hn => ⟨ok.vars, ok.fields, ok.newS, ok.freshS,
      fun s hs => by rw [hn] at hs; cases hs⟩
  cases s with
  | call ret s args =>
    have hargs : ∀ x ∈ args, x ∈ cb.cn.ctx.vars := fun x hx => ok.vars x (by simp [Stmt.vars, hx])
    obtain ⟨g1, e1, r1⟩ := callBOO_rel hc cc g hR hargs
    obtain ⟨g2, e2, r2⟩ := retireO_rel cc hr g1 r1 s
    simp only [ostepBO, astepBO]
    generalize callBOO cb T st args = a at g1 e1 r1 g2 e2 r2
    generalize retireO cb.cn.ctx s a.1 a.2 = r at g2 e2 r2
    cases ret with
    | none => exact ⟨g2, e1.trans e2, r2⟩
    | some x =>
      obtain ⟨g3, e3, r3⟩ := setKey_rel g2 r2 (ok.vars x (by simp [Stmt.vars]))
        (S := [.sym (.fresh s) []]) (by intro a ha; simp at ha; subst ha; exact ok.freshS s rfl)
      exact ⟨g3, e1.trans (e2.trans e3), r3⟩
  | store x f y =>
    exact storeBOO_rel hc cc g hR (ok.vars x (by simp [Stmt.vars]))
      (ok.vars y (by simp [Stmt.vars])) (ok.fields f (by simp [Stmt.fields]))
  | new x s => exact ostepR_rel cc hr g hR (okr _ ok rfl)
  | null x => exact ostepR_rel cc hr g hR (okr _ ok rfl)
  | copy x y => exact ostepR_rel cc hr g hR (okr _ ok rfl)
  | load x y f => exact ostepR_rel cc hr g hR (okr _ ok rfl)
  | aload x y => exact ostepR_rel cc hr g hR (okr _ ok rfl)
  | astore x y => exact ostepR_rel cc hr g hR (okr _ ok rfl)
  | unknown x s => exact ostepR_rel cc hr g hR (okr _ ok rfl)

/-- The O analysis of design BO represents the concept analysis on the universe. -/
theorem analyzeBOO_rel {cb : CtxB} (hc : CtxBOK cb) (cc : CtxClosed cb.cn.ctx)
    (hr : RecOK cb.cn.ctx) :
    ∀ (q : Prog) (T : Tbl) (st : OState) (X : AState), (∀ s ∈ q.stmts, StmtOKB cb s) →
      T.Good cb.cn.ctx.origins → Rel cb.cn.ctx T st X →
      (analyzeBOO cb q T st).1.Good cb.cn.ctx.origins ∧ T.Ext (analyzeBOO cb q T st).1 ∧
      Rel cb.cn.ctx (analyzeBOO cb q T st).1 (analyzeBOO cb q T st).2 (analyzeBO cb q X)
  | .skip, T, _, _, _, g, hR => ⟨g, Tbl.Ext.refl T, hR⟩
  | .stmt s, _, _, _, ok, g, hR => ostepBO_rel hc cc hr g hR (ok s (by simp [Prog.stmts]))
  | .seq p q, T, st, X, ok, g, hR => by
    obtain ⟨g1, e1, r1⟩ := analyzeBOO_rel hc cc hr p T st X
      (fun st hs => ok st (List.mem_append_left _ hs)) g hR
    simp only [analyzeBOO, analyzeBO]
    generalize analyzeBOO cb p T st = r at g1 e1 r1
    obtain ⟨g2, e2, r2⟩ := analyzeBOO_rel hc cc hr q r.1 r.2 _
      (fun st hs => ok st (List.mem_append_right _ hs)) g1 r1
    exact ⟨g2, e1.trans e2, r2⟩
  | .choice p q, T, st, X, ok, g, hR => by
    obtain ⟨g1, e1, r1⟩ := analyzeBOO_rel hc cc hr p T st X
      (fun st hs => ok st (List.mem_append_left _ hs)) g hR
    simp only [analyzeBOO, analyzeBO]
    generalize analyzeBOO cb p T st = a at g1 e1 r1
    obtain ⟨g2, e2, r2⟩ := analyzeBOO_rel hc cc hr q a.1 st X
      (fun st hs => ok st (List.mem_append_right _ hs)) g1 (hR.ext e1)
    generalize analyzeBOO cb q a.1 st = b at g2 e2 r2
    obtain ⟨g3, e3, r3⟩ := joinO_rel cc g2 (r1.ext e2) r2
    exact ⟨g3, e1.trans (e2.trans e3), r3⟩
  | .loop p, T, st, X, ok, g, hR => by
    simp only [analyzeBOO, analyzeBO]
    exact loopO_rel cc (fun T' st' Y g' hR' => analyzeBOO_rel hc cc hr p T' st' Y ok g' hR')
      cb.cn.ctx.fuel T st X g hR

/-! ## Whole programs -/

/-- The final O state of program `p` in design BO. -/
def analyzeProgBOO (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (qf : List Field) : Tbl × OState :=
  let cb := ctxBO eu K statics fr p qf
  let i := initO cb.cn.ctx fr
  analyzeBOO cb p i.1 i.2

/-- O may-alias of design BO at the end of program `p`. -/
def mayProgBOO (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (x : Var) (px : List ACell) (y : Var) (py : List ACell) : Bool :=
  let r := analyzeProgBOO eu K statics fr p (afields px ++ afields py)
  omay (ctxBO eu K statics fr p (afields px ++ afields py)).cn.ctx r.1 r.2 x px y py

/-- For each policy, each list of static roots and each program, the final O state of design
BO represents the final concept state. -/
theorem analyzeProgBOO_rel (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (qf : List Field) :
    (analyzeProgBOO eu K statics fr p qf).1.Good (ctxBO eu K statics fr p qf).cn.ctx.origins ∧
      Rel (ctxBO eu K statics fr p qf).cn.ctx (analyzeProgBOO eu K statics fr p qf).1
        (analyzeProgBOO eu K statics fr p qf).2 (analyzeProgBO eu K statics fr p qf) := by
  have hc := ctxBO_ok eu K statics fr p qf
  have cc := ctxClosed_of hc
  obtain ⟨g0, r0⟩ := initO_rel (ctx := (ctxBO eu K statics fr p qf).cn.ctx) fr
    (supp_ainitBO eu K statics fr p qf) (ctxBO_frame eu K statics fr p qf).vars
  obtain ⟨g1, _, r1⟩ := analyzeBOO_rel hc cc (recOK_of hc) p _ _ _
    (ctxBO_stmts eu K statics fr p qf) g0 r0
  exact ⟨g1, r1⟩

/-- O EQUIVALENCE OF DESIGN BO: for both strong-update policies and each list of static roots,
O and the concept give the same may-alias answer on program and frame variables. -/
theorem mayProgBOO_eq (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (x : Var) (px : List ACell) (y : Var) (py : List ACell) (hx : x ∈ p.vars ++ fr.vars)
    (hy : y ∈ p.vars ++ fr.vars) :
    mayProgBOO eu K statics fr p x px y py = mayProgBO eu K statics fr p x px y py := by
  have cc := ctxClosed_of (ctxBO_ok eu K statics fr p (afields px ++ afields py))
  obtain ⟨g, hR⟩ := analyzeProgBOO_rel eu K statics fr p (afields px ++ afields py)
  unfold mayProgBOO mayProgBO
  simp only
  have hv : ∀ z, z ∈ p.vars ++ fr.vars →
      z ∈ (ctxBO eu K statics fr p (afields px ++ afields py)).cn.ctx.vars := by
    intro z hz
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_eraseDups.mpr hz))
  exact omay_eq cc g hR (hv x hx) (hv y hy)
    (Opt.query_cells K fr p _ px (fun f hf => List.mem_append_left _ hf))
    (Opt.query_cells K fr p _ py (fun f hf => List.mem_append_right _ hf))

/-- O of design BO is sound under strict narrow A2: each strict narrow one-execution alias of
program variables is a may-alias of `mayProgBOO`. -/
theorem csoundBOO (src : Nat → Obj × Cell) (statics : List Root) (eu : Bool) (K : Nat)
    (fr : Frame) (p : Prog) (x : Var) (px : List Cell) (y : Var) (py : List Cell)
    (hx : x ∈ p.vars ++ fr.vars) (hy : y ∈ p.vars ++ fr.vars)
    (h : CAliasN src statics fr p x px y py) :
    mayProgBOO eu K statics fr p x (px.map Cell.abs) y (py.map Cell.abs) = true := by
  rw [mayProgBOO_eq eu K statics fr p x _ y _ hx hy]
  exact csoundBO src statics eu K fr p x px y py h

/-! ## Examples -/

section examples

open DirectedAlias.Sound.CellNamed.Examples DirectedAlias.Sound.BlockOnly.Examples

/-- O of design BO gives the answers of the concept on the gain, loss, trace C, `Eval` and
dead-end examples. -/
theorem o_answersBO :
    mayProgBOO true 1 [] frN (pGain []) vt [.fld fg] vu [] = false ∧
      mayProgBOO true 1 [] frN pL1 vt [.fld fg] vu [] = true ∧
      mayProgBOO true 0 [] frN pL2 vt [] vw [] = false ∧
      mayProgBOO true 0 [] frN pL3 va [] vc [] = false ∧
      mayProgBOO true 1 [] frN pL4 vy [.fld fg] vu [] = true ∧
      mayProgBOO true 1 [] frN pC va [] vb [] = true ∧
      mayProgBOO true 1 [] frN pE vn [.fld fg] vy [] = true ∧
      mayProgBOO true 0 [] frN pDead vb [] vd [] = true := by decide +kernel

end examples

end DirectedAlias.Opt.BlockOnly

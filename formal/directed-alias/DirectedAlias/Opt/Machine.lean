import DirectedAlias.Opt.Prim

/-!
# Optimization O, part 4: the O analysis and its equivalence with C

The O analysis mirrors `astep`, `join`, `loopIter` and `analyze` of concept C:

* copy shares the node id (no table work),
* new, null, unknown and the call result intern one small set,
* load is a memoized union over the cells of the origins of the base node,
* store uses the same strong/weak test as C (a single-member node with a unique origin),
* join makes one memoized union for each key that one of the two maps holds,
* the loop uses the same checked post-fixpoint as C. The test is "no union changed an id".

The main theorems: `analyzeO_rel` (each O result represents the C result on the universe),
`omay_eq` (O answers each may-alias query with the same Boolean as C), and `mayProgO_eq`
(the same for whole programs).
-/

namespace DirectedAlias.Opt

open DirectedAlias

/-! ## Statement operations -/

/-- `x := y`: share the node id of `y`. -/
def copyO (T : Tbl) (st : OState) (x y : Var) : Tbl × OState :=
  match oget st (.v y) with
  | some i => (T, oset st (.v x) i)
  | none => (T, oerase st (.v x))

/-- `x := y.c`: memoized union of the cells `c` of the origins of `y`. -/
def loadO (ctx : Ctx) (T : Tbl) (st : OState) (x y : Var) (c : ACell) : Tbl × OState :=
  let e := T.intern ctx.origins [] none
  let r := readUnion ctx st c e.2 (val ctx.K T st (.v y)) e.1
  (r.2, oset st (.v x) r.1)

/-- Weak store `x.c := y`: add the node of `y` to the cell `c` of each origin of `x`. -/
def weakO (ctx : Ctx) (T : Tbl) (st : OState) (x : Var) (c : ACell) (y : Var) : Tbl × OState :=
  let yi := getId ctx T st (.v y)
  addAll ctx yi.2 st ((val ctx.K T st (.v x)).map (fun o => Key.h o c)) yi.1

/-- Store `x.c := y`: strong if the node of `x` has one member and it is unique, else weak. -/
def storeO (ctx : Ctx) (T : Tbl) (st : OState) (x : Var) (c : ACell) (y : Var) : Tbl × OState :=
  match single? (val ctx.K T st (.v x)) with
  | some o =>
    if o.uniqueB ctx.once ctx.entryUnique then
      let yi := getId ctx T st (.v y)
      (yi.2, oset st (.h o c) yi.1)
    else weakO ctx T st x c y
  | none => weakO ctx T st x c y

/-- The havoc of call site `s`: add `havoc s` to each universe cell of each reachable origin. -/
def havocO (ctx : Ctx) (T : Tbl) (st : OState) (args : List Var) (s : Site) : Tbl × OState :=
  let r := reachB ctx (den ctx.K T st) args
  let ks := (ctx.origins.filter r).flatMap (fun o => ctx.cells.map (Key.h o))
  let hv := T.intern ctx.origins [.havoc s] none
  addAll ctx hv.2 st ks hv.1

/-- An unresolved call: the havoc, then the fresh result. -/
def callO (ctx : Ctx) (T : Tbl) (st : OState) (ret : Option Var) (s : Site) (args : List Var) :
    Tbl × OState :=
  let a := havocO ctx T st args s
  match ret with
  | none => a
  | some x => setKey ctx a.1 a.2 (.v x) [.sym (.fresh s) []]

/-- The O transfer of one statement. -/
def ostep (ctx : Ctx) : Stmt → Tbl → OState → Tbl × OState
  | .new x s, T, st => setKey ctx T st (.v x) [.alloc s]
  | .null x, T, st => (T, oerase st (.v x))
  | .copy x y, T, st => copyO T st x y
  | .load x y f, T, st => loadO ctx T st x y (.fld f)
  | .store x f y, T, st => storeO ctx T st x (.fld f) y
  | .aload x y, T, st => loadO ctx T st x y .elem
  | .astore x y, T, st => weakO ctx T st x .elem y
  | .unknown x s, T, st => setKey ctx T st (.v x) [.sym (.fresh s) []]
  | .call ret s args, T, st => callO ctx T st ret s args

/-! ## Join, top, loop, analysis -/

/-- The join loop: for each key, one memoized union of the two nodes. The flag records whether
some union id differs from the id of the first state. -/
def jfold (ctx : Ctx) (s1 s2 : OState) : List Key → Tbl → OState → Bool → Tbl × OState × Bool
  | [], T, out, ch => (T, out, ch)
  | k :: ks, T, out, ch =>
    let a := getId ctx T s1 k
    let b := getId ctx a.2 s2 k
    let u := b.2.union ctx.origins a.1 b.1
    jfold ctx s1 s2 ks u.2 (oset out k u.1) (ch || decide (u.1 ≠ a.1))

/-- The join of two O states. The flag is true if the join is not the first state. -/
def joinO (ctx : Ctx) (T : Tbl) (s1 s2 : OState) : Tbl × OState × Bool :=
  jfold ctx s1 s2 (s1.map Prod.fst ++ s2.map Prod.fst) T [] false

/-- The top state above `st`: add the universe to each universe key. -/
def topO (ctx : Ctx) (T : Tbl) (st : OState) : Tbl × OState :=
  let u := T.intern ctx.origins ctx.origins none
  addAll ctx u.2 st (ukeys ctx) u.1

/-- The O loop: the same checked post-fixpoint iteration as `loopIter`. -/
def loopO (ctx : Ctx) (f : Tbl → OState → Tbl × OState) : Nat → Tbl → OState → Tbl × OState
  | 0, T, st => topO ctx T st
  | n + 1, T, st =>
    let r := f T st
    let j := joinO ctx r.1 st r.2
    if j.2.2 then loopO ctx f n j.1 j.2.1 else (j.1, st)

/-- The O analysis of a program. -/
def analyzeO (ctx : Ctx) : Prog → Tbl → OState → Tbl × OState
  | .skip, T, st => (T, st)
  | .stmt s, T, st => ostep ctx s T st
  | .seq p q, T, st =>
    let r := analyzeO ctx p T st
    analyzeO ctx q r.1 r.2
  | .choice p q, T, st =>
    let r1 := analyzeO ctx p T st
    let r2 := analyzeO ctx q r1.1 st
    let j := joinO ctx r2.1 r1.2 r2.2
    (j.1, j.2.1)
  | .loop p, T, st => loopO ctx (analyzeO ctx p) ctx.fuel T st

/-- Set each frame variable to its entry origins. -/
def initFold (ctx : Ctx) (fr : Frame) : List Var → Tbl → OState → Tbl × OState
  | [], T, st => (T, st)
  | x :: xs, T, st =>
    let r := setKey ctx T st (.v x) ((ainit ctx.K fr).env x)
    initFold ctx fr xs r.1 r.2

/-- The entry O state of a frame. -/
def initO (ctx : Ctx) (fr : Frame) : Tbl × OState :=
  initFold ctx fr fr.vars Tbl.empty []

/-! ## Queries -/

/-- O evaluation of a path from node `i`. -/
def oevalFrom (ctx : Ctx) (st : OState) : Tbl → Nat → List ACell → Nat × Tbl
  | T, i, [] => (i, T)
  | T, i, c :: cs =>
    let e := T.intern ctx.origins [] none
    let r := readUnion ctx st c e.2 (e.2.mem i) e.1
    oevalFrom ctx st r.2 r.1 cs

/-- O evaluation of the access path `x.p`. -/
def oevalPath (ctx : Ctx) (T : Tbl) (st : OState) (x : Var) (p : List ACell) : Nat × Tbl :=
  let g := getId ctx T st (.v x)
  oevalFrom ctx st g.2 g.1 p

/-- O may-alias: the two path nodes have a common member. -/
def omay (ctx : Ctx) (T : Tbl) (st : OState) (x : Var) (px : List ACell) (y : Var)
    (py : List ACell) : Bool :=
  let a := oevalPath ctx T st x px
  let b := oevalPath ctx a.2 st y py
  meetB (b.2.mem a.1) (b.2.mem b.1)

/-- The final O state of program `p` from frame `fr`. -/
def analyzeProgO (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) : Tbl × OState :=
  let ctx := progCtx K fr p qf
  let i := initO ctx fr
  analyzeO ctx p i.1 i.2

/-- O may-alias at the end of program `p`. -/
def mayProgO (K : Nat) (fr : Frame) (p : Prog)
    (x : Var) (px : List ACell) (y : Var) (py : List ACell) : Bool :=
  let r := analyzeProgO K fr p (afields px ++ afields py)
  omay (progCtx K fr p (afields px ++ afields py)) r.1 r.2 x px y py

/-! ## Set lemmas -/

/-- `single?` gives the same result on set-equal lists. -/
theorem single?_iff {α : Type} [DecidableEq α] {l : List α} {o : α} :
    single? l = some o ↔ o ∈ l ∧ ∀ a ∈ l, a = o := by
  constructor
  · exact single?_spec
  · rintro ⟨h1, h2⟩
    cases l with
    | nil => cases h1
    | cons x rest =>
      have hx : x = o := h2 x List.mem_cons_self
      subst hx
      simp only [single?]
      rw [ite_eq_left]
      exact List.all_eq_true.mpr (fun a ha => decide_eq_true (h2 a (List.mem_cons_of_mem _ ha)))

/-- `single?` gives the same result on set-equal lists. -/
theorem single?_congr {α : Type} [DecidableEq α] {l m : List α} (h : SetEq l m) :
    single? l = single? m := by
  cases hm : single? m with
  | some o =>
    have := single?_iff.mp hm
    exact single?_iff.mpr ⟨(h o).mpr this.1, fun a ha => this.2 a ((h a).mp ha)⟩
  | none =>
    cases hl : single? l with
    | none => rfl
    | some o =>
      have := single?_iff.mp hl
      have : single? m = some o :=
        single?_iff.mpr ⟨(h o).mp this.1, fun a ha => this.2 a ((h a).mpr ha)⟩
      rw [hm] at this; cases this

/-- `subB` gives the same result on set-equal lists. -/
theorem subB_congr {α : Type} [DecidableEq α] {l l' m m' : List α} (h1 : SetEq l l')
    (h2 : SetEq m m') : subB l m = subB l' m' := by
  cases h : subB l' m' with
  | true =>
    apply subB_iff.mpr
    intro a ha; exact (h2 a).mpr (subB_iff.mp h a ((h1 a).mp ha))
  | false =>
    cases h' : subB l m with
    | false => rfl
    | true =>
      have : subB l' m' = true :=
        subB_iff.mpr (fun a ha => (h2 a).mp (subB_iff.mp h' a ((h1 a).mpr ha)))
      rw [h] at this; cases this

/-- `meetB` gives the same result on set-equal lists. -/
theorem meetB_congr {α : Type} [DecidableEq α] {l l' m m' : List α} (h1 : SetEq l l')
    (h2 : SetEq m m') : meetB l m = meetB l' m' := by
  cases h : meetB l' m' with
  | true =>
    obtain ⟨a, ha1, ha2⟩ := meetB_iff.mp h
    exact meetB_iff.mpr ⟨a, (h1 a).mpr ha1, (h2 a).mpr ha2⟩
  | false =>
    cases h' : meetB l m with
    | false => rfl
    | true =>
      obtain ⟨a, ha1, ha2⟩ := meetB_iff.mp h'
      have : meetB l' m' = true := meetB_iff.mpr ⟨a, (h1 a).mp ha1, (h2 a).mp ha2⟩
      rw [h] at this; cases this

/-- A union is set-equal to its left part if and only if the right part is a subset. -/
theorem uni_setEq_left_iff {α : Type} [DecidableEq α] {A B : List α} :
    SetEq (uni A B) A ↔ B ⊆ A := by
  constructor
  · intro h a ha; exact (h a).mp (mem_uni.mpr (Or.inr ha))
  · intro h a; rw [mem_uni]; exact ⟨fun h' => h'.elim id (fun hb => h hb), Or.inl⟩

/-- A key that the map does not hold has no node. -/
theorem oget_none_of_not_mem : ∀ {m : OState} {k : Key}, k ∉ m.map Prod.fst → oget m k = none
  | [], _, _ => rfl
  | (k', i) :: r, k, h => by
    simp only [oget]
    split
    · rename_i he; subst he; exact absurd (List.mem_cons_self) h
    · exact oget_none_of_not_mem (fun h' => h (List.mem_cons_of_mem _ h'))

/-! ## Congruence of the reach closure -/

/-- `succs` gives set-equal results on states that agree on the universe cells. -/
theorem succs_congr {X Y : AState} {cs : List ACell} {R R' : List Origin}
    (hXY : ∀ o ∈ R, ∀ c ∈ cs, SetEq (X.heap o c) (Y.heap o c)) (h : SetEq R R') :
    SetEq (succs cs X R) (succs cs Y R') := by
  intro o'
  rw [mem_succs, mem_succs]
  constructor
  · rintro ⟨o, ho, c, hc, h1⟩; exact ⟨o, (h o).mp ho, c, hc, (hXY o ho c hc o').mp h1⟩
  · rintro ⟨o, ho, c, hc, h1⟩
    have ho' := (h o).mpr ho
    exact ⟨o, ho', c, hc, (hXY o ho' c hc o').mpr h1⟩

/-- `closeIter` gives results of the same shape and set-equal results on states that agree on
the universe cells. -/
theorem closeIter_congr {U : List Origin} {cs : List ACell} {X Y : AState}
    (hXY : ∀ o ∈ U, ∀ c ∈ cs, SetEq (X.heap o c) (Y.heap o c))
    (hX : ∀ o ∈ U, ∀ c ∈ cs, X.heap o c ⊆ U) :
    ∀ (n : Nat) (R R' : List Origin), R ⊆ U → SetEq R R' →
      (closeIter cs X n R = none ∧ closeIter cs Y n R' = none) ∨
      ∃ A B, closeIter cs X n R = some A ∧ closeIter cs Y n R' = some B ∧ SetEq A B
  | 0, _, _, _, _ => Or.inl ⟨rfl, rfl⟩
  | n + 1, R, R', hR, h => by
    have hs : SetEq (succs cs X R) (succs cs Y R') :=
      succs_congr (fun o ho c hc => hXY o (hR ho) c hc) h
    have hsU : succs cs X R ⊆ U := by
      intro o' ho'
      obtain ⟨o, ho, c, hc, h1⟩ := mem_succs.mp ho'
      exact hX o (hR ho) c hc h1
    simp only [closeIter]
    rw [subB_congr hs h]
    split
    · exact Or.inr ⟨R, R', rfl, rfl, h⟩
    · exact closeIter_congr hXY hX n _ _ (uni_sub hsU hR) (SetEq.uni hs h)

/-- The reach test is the same on a C state and on an O state that agrees with it. -/
theorem reachB_congr {ctx : Ctx} {X Y : AState} {args : List Var} (hs : Supp ctx X)
    (hargs : ∀ x ∈ args, x ∈ ctx.vars)
    (hXY : ∀ k, InU ctx k → SetEq (cval X k) (cval Y k)) :
    reachB ctx X args = reachB ctx Y args := by
  have hseed : SetEq (uni (uniMap X.env args) (ctx.origins.filter Origin.outer))
      (uni (uniMap Y.env args) (ctx.origins.filter Origin.outer)) := by
    refine SetEq.uni ?_ (SetEq.refl _)
    intro o
    rw [mem_uniMap, mem_uniMap]
    constructor
    · rintro ⟨x, hx, h⟩; exact ⟨x, hx, (hXY (.v x) (hargs x hx) o).mp h⟩
    · rintro ⟨x, hx, h⟩; exact ⟨x, hx, (hXY (.v x) (hargs x hx) o).mpr h⟩
  have hseedU : uni (uniMap X.env args) (ctx.origins.filter Origin.outer) ⊆ ctx.origins := by
    refine uni_sub ?_ (fun o ho => (List.mem_filter.mp ho).1)
    intro o ho
    obtain ⟨x, hx, h⟩ := mem_uniMap.mp ho
    exact hs (.v x) (hargs x hx) h
  unfold reachB
  rcases closeIter_congr (U := ctx.origins) (cs := ctx.cells)
      (fun o ho c hc => hXY (.h o c) ⟨ho, hc⟩) (fun o ho c hc => hs (.h o c) ⟨ho, hc⟩)
      (ctx.origins.length + 1) _ _ hseedU hseed with ⟨h1, h2⟩ | ⟨A, B, h1, h2, h3⟩
  · rw [h1, h2]
  · rw [h1, h2]
    funext o
    have : decide (o ∈ A) = decide (o ∈ B) := by
      by_cases ho : o ∈ A
      · simp [ho, (h3 o).mp ho]
      · have : o ∉ B := fun h => ho ((h3 o).mpr h)
        simp [ho, this]
    simp only [this]

/-! ## Simulation of the statements -/

/-- A pointwise value characterization gives the simulation relation. -/
theorem rel_of_vals {ctx : Ctx} {T' : Tbl} {st' : OState} {X' : AState}
    (h' : EntOK ctx T' st') (hs : Supp ctx X') (F : Key → List Origin)
    (hv : ∀ k, SetEq (val ctx.K T' st' k) (F k))
    (hc : ∀ k, InU ctx k → SetEq (F k) (cval X' k)) : Rel ctx T' st' X' where
  ent := h'
  agree := fun k hk => (hv k).trans (hc k hk)
  supp := hs

/-- The simulation of setting one variable. -/
theorem agree_setVar {ctx : Ctx} {T : Tbl} {st : OState} {X : AState} (hR : Rel ctx T st X)
    (x : Var) {S S' : List Origin} (h : SetEq S S') :
    ∀ k, InU ctx k → SetEq (if k = .v x then S else val ctx.K T st k)
      (cval (X.setVar x S') k) := by
  intro k hk
  rw [cval_setVar]
  split
  · exact h
  · exact hR.agree k hk

/-- The simulation of `new`, `unknown` and the other "set to a set" statements. -/
theorem setKey_rel {ctx : Ctx} {T : Tbl} (g : T.Good ctx.origins) {st : OState} {X : AState}
    (hR : Rel ctx T st X) {x : Var} (hx : x ∈ ctx.vars) {S : List Origin}
    (hS : S ⊆ ctx.origins) :
    (setKey ctx T st (.v x) S).1.Good ctx.origins ∧ T.Ext (setKey ctx T st (.v x) S).1 ∧
      Rel ctx (setKey ctx T st (.v x) S).1 (setKey ctx T st (.v x) S).2 (X.setVar x S) := by
  obtain ⟨g1, e1, h1, m1⟩ := setKey_spec g hR.ent (k := .v x) hx hS
  exact ⟨g1, e1, rel_of_vals h1 (hR.supp.setVar x hS) _ m1 (agree_setVar hR x (SetEq.refl _))⟩

/-- The simulation of `copy`. -/
theorem copyO_rel {ctx : Ctx} {T : Tbl} {st : OState} {X : AState} (hR : Rel ctx T st X)
    {x y : Var} (hx : x ∈ ctx.vars) (hy : y ∈ ctx.vars) :
    T.Ext (copyO T st x y).1 ∧
      Rel ctx (copyO T st x y).1 (copyO T st x y).2 (X.setVar x (X.env y)) := by
  have hs := hR.supp.setVar x (hR.supp.env hy)
  unfold copyO
  cases ho : oget st (.v y) with
  | some i =>
    have hi := (hR.ent.ent _ (oget_mem ho)).1
    refine ⟨Tbl.Ext.refl T, rel_of_vals (hR.ent.oset hi hx) hs
      (fun k => if k = .v x then val ctx.K T st (.v y) else val ctx.K T st k) ?_
      (agree_setVar hR x (hR.agree (.v y) hy))⟩
    intro k
    rw [val_oset]
    split
    · simp [val, ho]; exact SetEq.refl _
    · exact SetEq.refl _
  | none =>
    refine ⟨Tbl.Ext.refl T, rel_of_vals (hR.ent.oerase _) hs
      (fun k => if k = .v x then val ctx.K T st (.v y) else val ctx.K T st k) ?_
      (agree_setVar hR x (hR.agree (.v y) hy))⟩
    intro k
    rw [val_oerase]
    split
    · simp [val, ho, dflt]; exact SetEq.refl _
    · exact SetEq.refl _

/-- The simulation of `null`. -/
theorem nullO_rel {ctx : Ctx} {T : Tbl} {st : OState} {X : AState} (hR : Rel ctx T st X)
    (x : Var) : Rel ctx T (oerase st (.v x)) (X.setVar x []) := by
  refine rel_of_vals (hR.ent.oerase _) (hR.supp.setVar x (fun _ h => by cases h))
    (fun k => if k = .v x then [] else val ctx.K T st k) ?_ (agree_setVar hR x (SetEq.refl _))
  intro k
  rw [val_oerase]
  split
  · exact SetEq.refl _
  · exact SetEq.refl _

/-- The read through a node agrees with `aread` of C. -/
theorem aread_agree {ctx : Ctx} {T : Tbl} {st : OState} {X : AState} (hR : Rel ctx T st X)
    {S S' : List Origin} (hS : SetEq S S') (hS' : S' ⊆ ctx.origins) {c : ACell}
    (hc : c ∈ ctx.cells) (o' : Origin) :
    (∃ o ∈ S, o' ∈ val ctx.K T st (.h o c)) ↔ o' ∈ aread X S' c := by
  rw [mem_aread]
  constructor
  · rintro ⟨o, ho, h⟩
    have ho' := (hS o).mp ho
    exact ⟨o, ho', (hR.agree (.h o c) ⟨hS' ho', hc⟩ o').mp h⟩
  · rintro ⟨o, ho, h⟩
    exact ⟨o, (hS o).mpr ho, (hR.agree (.h o c) ⟨hS' ho, hc⟩ o').mpr h⟩

/-- The simulation of `load` and `aload`. -/
theorem loadO_rel {ctx : Ctx} (cc : CtxClosed ctx) {T : Tbl} (g : T.Good ctx.origins)
    {st : OState} {X : AState} (hR : Rel ctx T st X) {x y : Var} (hx : x ∈ ctx.vars)
    (hy : y ∈ ctx.vars) {c : ACell} (hc : c ∈ ctx.cells) :
    (loadO ctx T st x y c).1.Good ctx.origins ∧ T.Ext (loadO ctx T st x y c).1 ∧
      Rel ctx (loadO ctx T st x y c).1 (loadO ctx T st x y c).2
        (X.setVar x (aread X (X.env y) c)) := by
  obtain ⟨g1, e1, i1, m1⟩ := Tbl.intern_none_spec g (S := []) (fun _ h => by cases h)
  unfold loadO
  simp only
  generalize T.intern ctx.origins [] none = e at g1 e1 i1 m1
  have h1 : EntOK ctx e.2 st := hR.ent.ext e1
  obtain ⟨g2, e2, i2, m2⟩ := readUnion_spec cc hc (val ctx.K T st (.v y)) g1 h1
    (val_sub cc g st hy) i1
  generalize readUnion ctx st c e.2 (val ctx.K T st (.v y)) e.1 = r at g2 e2 i2 m2
  have e12 := e1.trans e2
  refine ⟨g2, e12, rel_of_vals ((hR.ent.ext e12).oset i2 hx)
    (hR.supp.setVar x (aread_sub hR.supp (hR.supp.env hy) hc))
    (fun k => if k = .v x then r.2.mem r.1 else val ctx.K T st k) ?_ ?_⟩
  · intro k
    rw [val_oset]
    split
    · exact SetEq.refl _
    · rw [val_ext hR.ent e12]; exact SetEq.refl _
  · refine agree_setVar hR x ?_
    intro o'
    rw [m2 o', m1 o']
    simp only [val_ext hR.ent e1, List.not_mem_nil, false_or]
    exact aread_agree hR (hR.agree (.v y) hy) (hR.supp.env hy) hc o'

/-- The simulation of a weak store. -/
theorem weakO_rel {ctx : Ctx} (cc : CtxClosed ctx) {T : Tbl} (g : T.Good ctx.origins)
    {st : OState} {X : AState} (hR : Rel ctx T st X) {x y : Var} (hx : x ∈ ctx.vars)
    (hy : y ∈ ctx.vars) {c : ACell} (hc : c ∈ ctx.cells) :
    (weakO ctx T st x c y).1.Good ctx.origins ∧ T.Ext (weakO ctx T st x c y).1 ∧
      Rel ctx (weakO ctx T st x c y).1 (weakO ctx T st x c y).2
        (X.weakStore (X.env x) c (X.env y)) := by
  obtain ⟨g1, e1, i1, m1⟩ := getId_spec cc g hR.ent (k := .v y) hy
  unfold weakO
  simp only
  generalize getId ctx T st (.v y) = yi at g1 e1 i1 m1
  have hxs := val_sub cc g st (k := .v x) hx
  have hks : ∀ k ∈ (val ctx.K T st (.v x)).map (fun o => Key.h o c), InU ctx k := by
    intro k hk
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hk
    exact ⟨hxs ho, hc⟩
  obtain ⟨g2, e2, h2, m2⟩ := addAll_spec cc _ g1 (hR.ent.ext e1) hks i1
  refine ⟨g2, e1.trans e2, rel_of_vals h2 (hR.supp.weakStore _ c (hR.supp.env hy)) _ m2 ?_⟩
  intro k hk
  rw [cval_weakStore, val_ext hR.ent e1]
  have hmem : k ∈ (val ctx.K T st (.v x)).map (fun o => Key.h o c) ↔
      k ∈ (X.env x).map (fun o => Key.h o c) := by
    simp only [List.mem_map]
    constructor
    · rintro ⟨o, ho, h⟩; exact ⟨o, (hR.agree (.v x) hx o).mp ho, h⟩
    · rintro ⟨o, ho, h⟩; exact ⟨o, (hR.agree (.v x) hx o).mpr ho, h⟩
  by_cases h : k ∈ (X.env x).map (fun o => Key.h o c)
  · rw [ite_eq_left (hmem.mpr h), ite_eq_left h]
    exact (SetEq.uni (hR.agree k hk) m1).trans
      ((SetEq.uni (SetEq.refl _) (hR.agree (.v y) hy)).trans (uni_comm_set _ _))
  · rw [ite_eq_right (fun h' => h (hmem.mp h')), ite_eq_right h]
    exact hR.agree k hk

/-- The simulation of `store`. -/
theorem storeO_rel {ctx : Ctx} (cc : CtxClosed ctx) {T : Tbl} (g : T.Good ctx.origins)
    {st : OState} {X : AState} (hR : Rel ctx T st X) {x y : Var} (hx : x ∈ ctx.vars)
    (hy : y ∈ ctx.vars) {c : ACell} (hc : c ∈ ctx.cells) :
    (storeO ctx T st x c y).1.Good ctx.origins ∧ T.Ext (storeO ctx T st x c y).1 ∧
      Rel ctx (storeO ctx T st x c y).1 (storeO ctx T st x c y).2
        (X.store ctx.once x c (X.env y) ctx.entryUnique) := by
  have hsg : single? (val ctx.K T st (.v x)) = single? (X.env x) :=
    single?_congr (hR.agree (.v x) hx)
  unfold storeO
  rw [cval_store, ← hsg]
  cases hso : single? (val ctx.K T st (.v x)) with
  | none => exact weakO_rel cc g hR hx hy hc
  | some o =>
    simp only
    split
    · rename_i hu
      have ho : o ∈ ctx.origins := val_sub cc g st (k := .v x) hx (single?_spec hso).1
      have hk : InU ctx (.h o c) := ⟨ho, hc⟩
      obtain ⟨g1, e1, i1, m1⟩ := getId_spec cc g hR.ent (k := .v y) hy
      generalize getId ctx T st (.v y) = yi at g1 e1 i1 m1
      refine ⟨g1, e1, rel_of_vals ((hR.ent.ext e1).oset i1 hk) ?_
        (fun k => if k = .h o c then yi.2.mem yi.1 else val ctx.K T st k) ?_ ?_⟩
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
    · exact weakO_rel cc g hR hx hy hc

/-- The simulation of a call. -/
theorem callO_rel {ctx : Ctx} (cc : CtxClosed ctx) {T : Tbl} (g : T.Good ctx.origins)
    {st : OState} {X : AState} (hR : Rel ctx T st X) {ret : Option Var} {s : Site}
    {args : List Var} (ok : StmtOK ctx (.call ret s args)) :
    (callO ctx T st ret s args).1.Good ctx.origins ∧ T.Ext (callO ctx T st ret s args).1 ∧
      Rel ctx (callO ctx T st ret s args).1 (callO ctx T st ret s args).2
        ((X.havoc ctx args s).setRet ret [.sym (.fresh s) []]) := by
  have hargs : ∀ x ∈ args, x ∈ ctx.vars := fun x hx => ok.vars x (by simp [Stmt.vars, hx])
  have hhv : Origin.havoc s ∈ ctx.origins := ok.call s rfl
  have hfr : Origin.sym (.fresh s) [] ∈ ctx.origins := ok.fresh s rfl
  have hreach : reachB ctx (den ctx.K T st) args = reachB ctx X args :=
    (reachB_congr hR.supp hargs (fun k hk => by
      rw [cval_den]; exact (hR.agree k hk).symm)).symm
  have hH : (havocO ctx T st args s).1.Good ctx.origins ∧ T.Ext (havocO ctx T st args s).1 ∧
      Rel ctx (havocO ctx T st args s).1 (havocO ctx T st args s).2 (X.havoc ctx args s) := by
    obtain ⟨g1, e1, i1, m1⟩ := Tbl.intern_none_spec g (S := [.havoc s])
      (by intro a ha; simp at ha; subst ha; exact hhv)
    unfold havocO
    simp only
    rw [hreach]
    generalize T.intern ctx.origins [.havoc s] none = hv at g1 e1 i1 m1
    have hks : ∀ k ∈ (ctx.origins.filter (reachB ctx X args)).flatMap
        (fun o => ctx.cells.map (Key.h o)), InU ctx k := by
      intro k hk
      obtain ⟨o, ho, hk⟩ := List.mem_flatMap.mp hk
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hk
      exact ⟨(List.mem_filter.mp ho).1, hc⟩
    obtain ⟨g2, e2, h2, m2⟩ := addAll_spec cc _ g1 (hR.ent.ext e1) hks i1
    refine ⟨g2, e1.trans e2, rel_of_vals h2 (hR.supp.havoc args hhv) _ m2 ?_⟩
    intro k hk
    rw [cval_havoc, val_ext hR.ent e1]
    cases k with
    | v x =>
      have : Key.v x ∉ (ctx.origins.filter (reachB ctx X args)).flatMap
          (fun o => ctx.cells.map (Key.h o)) := by
        intro h
        obtain ⟨o, _, h⟩ := List.mem_flatMap.mp h
        obtain ⟨_, _, h⟩ := List.mem_map.mp h
        cases h
      rw [ite_eq_right this]
      exact hR.agree (.v x) hk
    | h o c =>
      simp only
      have hmem : Key.h o c ∈ (ctx.origins.filter (reachB ctx X args)).flatMap
          (fun o => ctx.cells.map (Key.h o)) ↔ (c ∈ ctx.cells ∧ reachB ctx X args o = true) := by
        simp only [List.mem_flatMap, List.mem_filter, List.mem_map, Key.h.injEq]
        constructor
        · rintro ⟨o', ⟨_, h1⟩, c', h2, rfl, rfl⟩; exact ⟨h2, h1⟩
        · rintro ⟨h1, h2⟩; exact ⟨o, ⟨hk.1, h2⟩, c, h1, rfl, rfl⟩
      by_cases h : c ∈ ctx.cells ∧ reachB ctx X args o = true
      · rw [ite_eq_left (hmem.mpr h), ite_eq_left h]
        exact (SetEq.uni (hR.agree (.h o c) hk) m1).trans (uni_comm_set _ _)
      · rw [ite_eq_right (fun h' => h (hmem.mp h')), ite_eq_right h]
        exact hR.agree (.h o c) hk
  obtain ⟨g1, e1, h1⟩ := hH
  unfold callO
  simp only
  generalize havocO ctx T st args s = a at g1 e1 h1
  cases ret with
  | none => exact ⟨g1, e1, h1⟩
  | some x =>
    have hx : x ∈ ctx.vars := ok.vars x (by simp [Stmt.vars])
    obtain ⟨g2, e2, h2⟩ := setKey_rel g1 h1 hx (S := [.sym (.fresh s) []])
      (by intro a ha; simp at ha; subst ha; exact hfr)
    exact ⟨g2, e1.trans e2, h2⟩

/-- Each O statement step represents the C statement step. -/
theorem ostep_rel {ctx : Ctx} (cc : CtxClosed ctx) {T : Tbl} (g : T.Good ctx.origins)
    {st : OState} {X : AState} (hR : Rel ctx T st X) {s : Stmt} (ok : StmtOK ctx s) :
    (ostep ctx s T st).1.Good ctx.origins ∧ T.Ext (ostep ctx s T st).1 ∧
      Rel ctx (ostep ctx s T st).1 (ostep ctx s T st).2 (astep ctx s X) := by
  cases s with
  | new x s =>
    exact setKey_rel g hR (ok.vars x (by simp [Stmt.vars]))
      (by intro a ha; simp at ha; subst ha; exact ok.new s rfl)
  | null x => exact ⟨g, Tbl.Ext.refl T, nullO_rel hR x⟩
  | copy x y =>
    obtain ⟨e, h⟩ := copyO_rel hR (x := x) (y := y) (ok.vars x (by simp [Stmt.vars]))
      (ok.vars y (by simp [Stmt.vars]))
    refine ⟨?_, e, h⟩
    show (copyO T st x y).1.Good _
    unfold copyO; split <;> exact g
  | load x y f =>
    exact loadO_rel cc g hR (ok.vars x (by simp [Stmt.vars])) (ok.vars y (by simp [Stmt.vars]))
      (ok.fields f (by simp [Stmt.fields]))
  | store x f y =>
    exact storeO_rel cc g hR (ok.vars x (by simp [Stmt.vars])) (ok.vars y (by simp [Stmt.vars]))
      (ok.fields f (by simp [Stmt.fields]))
  | aload x y =>
    exact loadO_rel cc g hR (ok.vars x (by simp [Stmt.vars])) (ok.vars y (by simp [Stmt.vars]))
      cc.elem
  | astore x y =>
    exact weakO_rel cc g hR (ok.vars x (by simp [Stmt.vars])) (ok.vars y (by simp [Stmt.vars]))
      cc.elem
  | unknown x s =>
    exact setKey_rel g hR (ok.vars x (by simp [Stmt.vars]))
      (by intro a ha; simp at ha; subst ha; exact ok.fresh s rfl)
  | call ret s args => exact callO_rel cc g hR ok

end DirectedAlias.Opt

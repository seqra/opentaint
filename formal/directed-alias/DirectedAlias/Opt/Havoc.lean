import DirectedAlias.Opt.Equiv
import DirectedAlias.Opt.LoopCost
import DirectedAlias.Sound.Havoc.Soundness

/-!
# Optimization O with per-cell havoc

The per-cell havoc concept (`Sound/Havoc/Concept.lean`) adds `hsym s (keyOf o) c []` to the cell
`c` of each reachable origin `o`. O does the same on nodes (`havocHO`): the same reach test as
`havocO`, then for each universe cell of each reachable universe origin, one interned singleton
node and one memoized union (`addHv`). All other statements, the join, the loop and the queries
are the O operations of concept C.

Results: `callHO_rel` (one call), `ostepH_rel` (one statement), `analyzeHO_rel` (the analysis),
`mayProgHO_eq` (O and the per-cell havoc concept give the same may-alias Boolean, for both
strong-update policies), `addHv_work` (the cost of a per-cell havoc).
-/

namespace DirectedAlias.Opt.Hv

open DirectedAlias DirectedAlias.Opt DirectedAlias.Sound.Havoc

/-! ## The per-cell havoc of O -/

/-- The per-cell havoc origin set of a key: one origin for a cell, none for a variable. -/
def hvOf (s : Site) : Key → List Origin
  | .v _ => []
  | .h o c => [.hsym s (keyOf o) c []]

/-- Add the per-cell havoc origin of each key of `ks` to the key. -/
def addHv (ctx : Ctx) (s : Site) : Tbl → OState → List Key → Tbl × OState
  | T, st, [] => (T, st)
  | T, st, k :: ks =>
    let n := T.intern ctx.origins (hvOf s k) none
    let r := addKey ctx n.2 st k n.1
    addHv ctx s r.1 r.2 ks

/-- The per-cell havoc of call site `s` on O: the reach test of `havocO`, then `addHv` on each
universe cell of each reachable universe origin. -/
def havocHO (ctx : Ctx) (T : Tbl) (st : OState) (args : List Var) (s : Site) : Tbl × OState :=
  let r := reachB ctx (den ctx.K T st) args
  let ks := (ctx.origins.filter r).flatMap (fun o => ctx.cells.map (Key.h o))
  addHv ctx s T st ks

/-- An unresolved call with per-cell havoc: the havoc, then the fresh result. -/
def callHO (ctx : Ctx) (T : Tbl) (st : OState) (ret : Option Var) (s : Site) (args : List Var) :
    Tbl × OState :=
  let a := havocHO ctx T st args s
  match ret with
  | none => a
  | some x => setKey ctx a.1 a.2 (.v x) [.sym (.fresh s) []]

/-- The O transfer of one statement with per-cell havoc. -/
def ostepH (ctx : Ctx) : Stmt → Tbl → OState → Tbl × OState
  | .call ret s args, T, st => callHO ctx T st ret s args
  | st, T, s => ostep ctx st T s

/-- The O analysis with per-cell havoc. -/
def analyzeHO (ctx : Ctx) : Prog → Tbl → OState → Tbl × OState
  | .skip, T, st => (T, st)
  | .stmt s, T, st => ostepH ctx s T st
  | .seq p q, T, st =>
    let r := analyzeHO ctx p T st
    analyzeHO ctx q r.1 r.2
  | .choice p q, T, st =>
    let r1 := analyzeHO ctx p T st
    let r2 := analyzeHO ctx q r1.1 st
    let j := joinO ctx r2.1 r1.2 r2.2
    (j.1, j.2.1)
  | .loop p, T, st => loopO ctx (analyzeHO ctx p) ctx.fuel T st

/-! ## Coverage and support -/

/-- The context covers a statement for per-cell havoc: the O coverage, and the per-cell havoc
origin of each universe cell of each universe origin is in the universe. -/
def StmtOKHO (ctx : Ctx) (st : Stmt) : Prop :=
  StmtOK ctx st ∧ ∀ s, st.callSite? = some s → ∀ a ∈ ctx.origins, ∀ c ∈ ctx.cells,
    Origin.hsym s (keyOf a) c [] ∈ ctx.origins

/-- The context covers every statement of the program for per-cell havoc. -/
def ProgOKH (ctx : Ctx) (q : Prog) : Prop := ∀ st ∈ q.stmts, StmtOKHO ctx st

/-- The key values after a per-cell havoc. -/
theorem cval_havocH (ctx : Ctx) (X : AState) (args : List Var) (s : Site) (k : Key) :
    cval (X.havocH ctx args s) k =
      match k with
      | .v x => X.env x
      | .h o c => if c ∈ ctx.cells ∧ reachB ctx X args o = true then
          uni [.hsym s (keyOf o) c []] (X.heap o c) else X.heap o c := by
  cases k <;> rfl

/-- A per-cell havoc keeps support if the per-cell havoc origins are in the universe. -/
theorem _root_.DirectedAlias.Opt.Supp.havocH {ctx : Ctx} {X : AState} (hs : Supp ctx X) (args : List Var) {s : Site}
    (h : ∀ a ∈ ctx.origins, ∀ c ∈ ctx.cells, Origin.hsym s (keyOf a) c [] ∈ ctx.origins) :
    Supp ctx (X.havocH ctx args s) := by
  intro k hk
  rw [cval_havocH]
  cases k with
  | v x => exact hs (.v x) hk
  | h o c =>
    simp only
    split
    · exact uni_sub (by intro a ha; simp at ha; subst ha; exact h o hk.1 c hk.2)
        (hs (.h o c) hk)
    · exact hs (.h o c) hk

/-- One covered statement keeps support with per-cell havoc. -/
theorem _root_.DirectedAlias.Opt.Supp.astepH {ctx : Ctx} (cc : CtxClosed ctx) {X : AState} (hs : Supp ctx X) {st : Stmt}
    (ok : StmtOKHO ctx st) : Supp ctx (astepH ctx st X) := by
  cases st with
  | call r s args =>
    exact (hs.havocH args (ok.2 s rfl)).setRet r
      (by intro a ha; simp at ha; subst ha; exact ok.1.fresh s rfl)
  | new x s => exact hs.astep cc ok.1
  | null x => exact hs.astep cc ok.1
  | copy x y => exact hs.astep cc ok.1
  | load x y f => exact hs.astep cc ok.1
  | store x f y => exact hs.astep cc ok.1
  | aload x y => exact hs.astep cc ok.1
  | astore x y => exact hs.astep cc ok.1
  | unknown x s => exact hs.astep cc ok.1

/-- The per-cell havoc analysis of a covered program keeps support. -/
theorem _root_.DirectedAlias.Opt.Supp.analyzeH {ctx : Ctx} (cc : CtxClosed ctx) :
    ∀ (q : Prog) (X : AState), ProgOKH ctx q → Supp ctx X → Supp ctx (analyzeH ctx q X)
  | .skip, _, _, h => h
  | .stmt st, _, ok, h => h.astepH cc (ok st (by simp [Prog.stmts]))
  | .seq p q, X, ok, h =>
    Supp.analyzeH cc q _ (fun st hs => ok st (List.mem_append_right _ hs))
      (Supp.analyzeH cc p X (fun st hs => ok st (List.mem_append_left _ hs)) h)
  | .choice p q, X, ok, h =>
    (Supp.analyzeH cc p X (fun st hs => ok st (List.mem_append_left _ hs)) h).join
      (Supp.analyzeH cc q X (fun st hs => ok st (List.mem_append_right _ hs)) h)
  | .loop p, X, ok, h =>
    Supp.loopIter (fun Y hY => Supp.analyzeH cc p Y ok hY) _ X h

/-! ## Simulation -/

/-- `addHv` adds the per-cell havoc origin of each key of `ks` to the key, and keeps the other
values. -/
theorem addHv_spec {ctx : Ctx} (cc : CtxClosed ctx) (s : Site) :
    ∀ (ks : List Key) {T : Tbl} {st : OState}, T.Good ctx.origins → EntOK ctx T st →
      (∀ k ∈ ks, InU ctx k) → (∀ k ∈ ks, hvOf s k ⊆ ctx.origins) →
      (addHv ctx s T st ks).1.Good ctx.origins ∧ T.Ext (addHv ctx s T st ks).1 ∧
      EntOK ctx (addHv ctx s T st ks).1 (addHv ctx s T st ks).2 ∧
      ∀ k', SetEq (val ctx.K (addHv ctx s T st ks).1 (addHv ctx s T st ks).2 k')
        (if k' ∈ ks then uni (val ctx.K T st k') (hvOf s k') else val ctx.K T st k')
  | [], T, st, g, h, _, _ => by
    refine ⟨g, Tbl.Ext.refl T, h, ?_⟩
    intro k'; simp only [addHv, List.not_mem_nil, ite_false]; exact SetEq.refl _
  | k :: ks, T, st, g, h, hks, hhv => by
    obtain ⟨g0, e0, i0, m0⟩ := Tbl.intern_none_spec g (hhv k List.mem_cons_self)
    simp only [addHv]
    generalize T.intern ctx.origins (hvOf s k) none = n at g0 e0 i0 m0
    obtain ⟨g1, e1, h1, m1⟩ := addKey_spec cc g0 (h.ext e0) (hks k List.mem_cons_self) i0
    generalize addKey ctx n.2 st k n.1 = r at g1 e1 h1 m1
    obtain ⟨g2, e2, h2, m2⟩ := addHv_spec cc s ks g1 h1
      (fun k' hk' => hks k' (List.mem_cons_of_mem _ hk'))
      (fun k' hk' => hhv k' (List.mem_cons_of_mem _ hk'))
    refine ⟨g2, e0.trans (e1.trans e2), h2, ?_⟩
    intro k'
    refine (m2 k').trans ?_
    have m1k := m1 k'
    simp only [val_ext h e0] at m1k
    by_cases hk1 : k' = k
    · subst hk1
      rw [ite_eq_left rfl] at m1k
      rw [ite_eq_left List.mem_cons_self]
      have m1k' : SetEq (val ctx.K r.1 r.2 k') (uni (val ctx.K T st k') (hvOf s k')) :=
        m1k.trans (SetEq.uni (SetEq.refl _) m0)
      split
      · intro a
        rw [mem_uni, m1k' a, mem_uni]
        constructor
        · rintro ((h | h) | h)
          · exact Or.inl h
          · exact Or.inr h
          · exact Or.inr h
        · rintro (h | h)
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr h)
      · exact m1k'
    · rw [ite_eq_right hk1] at m1k
      have : (k' ∈ k :: ks) ↔ k' ∈ ks := by
        constructor
        · intro hm
          rcases List.mem_cons.mp hm with he | he
          · exact absurd he hk1
          · exact he
        · exact List.mem_cons_of_mem _
      by_cases hin : k' ∈ ks
      · rw [ite_eq_left hin, ite_eq_left (this.mpr hin)]
        exact SetEq.uni m1k (SetEq.refl _)
      · rw [ite_eq_right hin, ite_eq_right (fun h => hin (this.mp h))]
        exact m1k

/-- The simulation of a call with per-cell havoc. -/
theorem callHO_rel {ctx : Ctx} (cc : CtxClosed ctx) {T : Tbl} (g : T.Good ctx.origins)
    {st : OState} {X : AState} (hR : Rel ctx T st X) {ret : Option Var} {s : Site}
    {args : List Var} (ok : StmtOKHO ctx (.call ret s args)) :
    (callHO ctx T st ret s args).1.Good ctx.origins ∧ T.Ext (callHO ctx T st ret s args).1 ∧
      Rel ctx (callHO ctx T st ret s args).1 (callHO ctx T st ret s args).2
        ((X.havocH ctx args s).setRet ret [.sym (.fresh s) []]) := by
  have hargs : ∀ x ∈ args, x ∈ ctx.vars := fun x hx => ok.1.vars x (by simp [Stmt.vars, hx])
  have hhv := ok.2 s rfl
  have hfr : Origin.sym (.fresh s) [] ∈ ctx.origins := ok.1.fresh s rfl
  have hreach : reachB ctx (den ctx.K T st) args = reachB ctx X args :=
    (reachB_congr hR.supp hargs (fun k hk => by
      rw [cval_den]; exact (hR.agree k hk).symm)).symm
  have hH : (havocHO ctx T st args s).1.Good ctx.origins ∧ T.Ext (havocHO ctx T st args s).1 ∧
      Rel ctx (havocHO ctx T st args s).1 (havocHO ctx T st args s).2 (X.havocH ctx args s) := by
    unfold havocHO
    simp only
    rw [hreach]
    have hmemks : ∀ k, k ∈ (ctx.origins.filter (reachB ctx X args)).flatMap
        (fun o => ctx.cells.map (Key.h o)) ↔
        ∃ o c, k = .h o c ∧ o ∈ ctx.origins ∧ reachB ctx X args o = true ∧ c ∈ ctx.cells := by
      intro k
      simp only [List.mem_flatMap, List.mem_filter, List.mem_map]
      constructor
      · rintro ⟨o, ⟨h1, h2⟩, c, h3, rfl⟩; exact ⟨o, c, rfl, h1, h2, h3⟩
      · rintro ⟨o, c, rfl, h1, h2, h3⟩; exact ⟨o, ⟨h1, h2⟩, c, h3, rfl⟩
    have hks : ∀ k ∈ (ctx.origins.filter (reachB ctx X args)).flatMap
        (fun o => ctx.cells.map (Key.h o)), InU ctx k := by
      intro k hk
      obtain ⟨o, c, rfl, h1, _, h3⟩ := (hmemks k).mp hk
      exact ⟨h1, h3⟩
    have hhs : ∀ k ∈ (ctx.origins.filter (reachB ctx X args)).flatMap
        (fun o => ctx.cells.map (Key.h o)), hvOf s k ⊆ ctx.origins := by
      intro k hk
      obtain ⟨o, c, rfl, h1, _, h3⟩ := (hmemks k).mp hk
      intro a ha
      simp only [hvOf, List.mem_singleton] at ha
      subst ha
      exact hhv o h1 c h3
    obtain ⟨g2, e2, h2, m2⟩ := addHv_spec cc s _ g hR.ent hks hhs
    refine ⟨g2, e2, rel_of_vals h2 (hR.supp.havocH args hhv) _ m2 ?_⟩
    intro k hk
    rw [cval_havocH]
    cases k with
    | v x =>
      have : Key.v x ∉ (ctx.origins.filter (reachB ctx X args)).flatMap
          (fun o => ctx.cells.map (Key.h o)) := by
        intro h
        obtain ⟨o, c, he, _⟩ := (hmemks _).mp h
        cases he
      rw [ite_eq_right this]
      exact hR.agree (.v x) hk
    | h o c =>
      simp only
      have hmem : Key.h o c ∈ (ctx.origins.filter (reachB ctx X args)).flatMap
          (fun o => ctx.cells.map (Key.h o)) ↔ (c ∈ ctx.cells ∧ reachB ctx X args o = true) := by
        rw [hmemks]
        constructor
        · rintro ⟨o', c', he, _, h2, h3⟩
          cases he
          exact ⟨h3, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨o, c, rfl, hk.1, h2, h1⟩
      by_cases h : c ∈ ctx.cells ∧ reachB ctx X args o = true
      · rw [ite_eq_left (hmem.mpr h), ite_eq_left h]
        exact (SetEq.uni (hR.agree (.h o c) hk) (SetEq.refl _)).trans (uni_comm_set _ _)
      · rw [ite_eq_right (fun h' => h (hmem.mp h')), ite_eq_right h]
        exact hR.agree (.h o c) hk
  obtain ⟨g1, e1, h1⟩ := hH
  unfold callHO
  simp only
  generalize havocHO ctx T st args s = a at g1 e1 h1
  cases ret with
  | none => exact ⟨g1, e1, h1⟩
  | some x =>
    have hx : x ∈ ctx.vars := ok.1.vars x (by simp [Stmt.vars])
    obtain ⟨g2, e2, h2⟩ := setKey_rel g1 h1 hx (S := [.sym (.fresh s) []])
      (by intro a ha; simp at ha; subst ha; exact hfr)
    exact ⟨g2, e1.trans e2, h2⟩

/-- Each O step with per-cell havoc represents the concept step. -/
theorem ostepH_rel {ctx : Ctx} (cc : CtxClosed ctx) {T : Tbl} (g : T.Good ctx.origins)
    {st : OState} {X : AState} (hR : Rel ctx T st X) {s : Stmt} (ok : StmtOKHO ctx s) :
    (ostepH ctx s T st).1.Good ctx.origins ∧ T.Ext (ostepH ctx s T st).1 ∧
      Rel ctx (ostepH ctx s T st).1 (ostepH ctx s T st).2 (astepH ctx s X) := by
  cases s with
  | call ret s args => exact callHO_rel cc g hR ok
  | new x s => exact ostep_rel cc g hR ok.1
  | null x => exact ostep_rel cc g hR ok.1
  | copy x y => exact ostep_rel cc g hR ok.1
  | load x y f => exact ostep_rel cc g hR ok.1
  | store x f y => exact ostep_rel cc g hR ok.1
  | aload x y => exact ostep_rel cc g hR ok.1
  | astore x y => exact ostep_rel cc g hR ok.1
  | unknown x s => exact ostep_rel cc g hR ok.1

/-- The O analysis with per-cell havoc represents the concept analysis on the universe. -/
theorem analyzeHO_rel {ctx : Ctx} (cc : CtxClosed ctx) :
    ∀ (q : Prog) (T : Tbl) (st : OState) (X : AState), ProgOKH ctx q → T.Good ctx.origins →
      Rel ctx T st X →
      (analyzeHO ctx q T st).1.Good ctx.origins ∧ T.Ext (analyzeHO ctx q T st).1 ∧
      Rel ctx (analyzeHO ctx q T st).1 (analyzeHO ctx q T st).2 (analyzeH ctx q X)
  | .skip, T, _, _, _, g, hR => ⟨g, Tbl.Ext.refl T, hR⟩
  | .stmt s, _, _, _, ok, g, hR => ostepH_rel cc g hR (ok s (by simp [Prog.stmts]))
  | .seq p q, T, st, X, ok, g, hR => by
    obtain ⟨g1, e1, r1⟩ := analyzeHO_rel cc p T st X
      (fun st hs => ok st (List.mem_append_left _ hs)) g hR
    simp only [analyzeHO, analyzeH]
    generalize analyzeHO ctx p T st = r at g1 e1 r1
    obtain ⟨g2, e2, r2⟩ := analyzeHO_rel cc q r.1 r.2 _
      (fun st hs => ok st (List.mem_append_right _ hs)) g1 r1
    exact ⟨g2, e1.trans e2, r2⟩
  | .choice p q, T, st, X, ok, g, hR => by
    obtain ⟨g1, e1, r1⟩ := analyzeHO_rel cc p T st X
      (fun st hs => ok st (List.mem_append_left _ hs)) g hR
    simp only [analyzeHO, analyzeH]
    generalize analyzeHO ctx p T st = a at g1 e1 r1
    obtain ⟨g2, e2, r2⟩ := analyzeHO_rel cc q a.1 st X
      (fun st hs => ok st (List.mem_append_right _ hs)) g1 (hR.ext e1)
    generalize analyzeHO ctx q a.1 st = b at g2 e2 r2
    obtain ⟨g3, e3, r3⟩ := joinO_rel cc g2 (r1.ext e2) r2
    exact ⟨g3, e1.trans (e2.trans e3), r3⟩
  | .loop p, T, st, X, ok, g, hR => by
    simp only [analyzeHO, analyzeH]
    exact loopO_rel cc (fun T' st' Y g' hR' => analyzeHO_rel cc p T' st' Y ok g' hR')
      ctx.fuel T st X g hR

/-! ## Whole programs -/

/-- The per-cell havoc context of a program is closed under default content. -/
theorem ctxClosed_H (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    CtxClosed (ctxH eu K fr p qf) :=
  ⟨fun o ho c hc o' ho' => (ctxH_ok eu K fr p qf).dflt o ho c hc o' ho',
    (ctxH_ok eu K fr p qf).elem⟩

/-- The per-cell havoc context covers every statement of the program. -/
theorem progOKH_H (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    ProgOKH (ctxH eu K fr p qf) p := fun st hst =>
  let o := ctxH_stmts eu K fr p qf st hst
  ⟨⟨o.ok.vars, o.ok.fields, o.ok.newS, o.ok.freshS, o.ok.callS⟩, o.callH⟩

/-- The entry state has support in the per-cell havoc context. -/
theorem supp_ainitH (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    Supp (ctxH eu K fr p qf) (ainit K fr) := by
  intro k hk
  cases k with
  | v x =>
    intro o ho
    exact List.mem_append_left _ (supp_ainit K fr p qf (.v x) hk ho)
  | h o c => exact (ctxClosed_H eu K fr p qf).dflt o hk.1 c hk.2

/-- The final O state of program `p` with per-cell havoc. -/
def analyzeProgHO (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    Tbl × OState :=
  let ctx := ctxH eu K fr p qf
  let i := initO ctx fr
  analyzeHO ctx p i.1 i.2

/-- O may-alias with per-cell havoc at the end of program `p`. -/
def mayProgHO (eu : Bool) (K : Nat) (fr : Frame) (p : Prog)
    (x : Var) (px : List ACell) (y : Var) (py : List ACell) : Bool :=
  let r := analyzeProgHO eu K fr p (afields px ++ afields py)
  omay (ctxH eu K fr p (afields px ++ afields py)) r.1 r.2 x px y py

/-- For each policy and each program, the final O state with per-cell havoc represents the
final concept state with per-cell havoc. -/
theorem analyzeProgHO_rel (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    (analyzeProgHO eu K fr p qf).1.Good (ctxH eu K fr p qf).origins ∧
      Rel (ctxH eu K fr p qf) (analyzeProgHO eu K fr p qf).1 (analyzeProgHO eu K fr p qf).2
        (analyzeProgH eu K fr p qf) := by
  have cc := ctxClosed_H eu K fr p qf
  have hfv : ∀ x ∈ fr.vars, x ∈ (ctxH eu K fr p qf).vars := by
    intro x hx
    simp only [ctxH]
    rw [List.mem_eraseDups]
    exact List.mem_append_right _ hx
  obtain ⟨g0, r0⟩ := initO_rel (ctx := ctxH eu K fr p qf) fr (supp_ainitH eu K fr p qf) hfv
  obtain ⟨g1, _, r1⟩ := analyzeHO_rel cc p _ _ _ (progOKH_H eu K fr p qf) g0 r0
  exact ⟨g1, r1⟩

/-- For both strong-update policies, O with per-cell havoc and the per-cell havoc concept give
the same may-alias answer. -/
theorem mayProgHO_eq (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (x : Var) (px : List ACell)
    (y : Var) (py : List ACell) (hx : x ∈ p.vars ++ fr.vars) (hy : y ∈ p.vars ++ fr.vars) :
    mayProgHO eu K fr p x px y py = mayProgH eu K fr p x px y py := by
  have cc := ctxClosed_H eu K fr p (afields px ++ afields py)
  obtain ⟨g, hR⟩ := analyzeProgHO_rel eu K fr p (afields px ++ afields py)
  unfold mayProgHO mayProgH
  simp only
  have hv : ∀ z, z ∈ p.vars ++ fr.vars →
      z ∈ (ctxH eu K fr p (afields px ++ afields py)).vars := by
    intro z hz; simp only [ctxH]; rw [List.mem_eraseDups]; exact hz
  exact omay_eq cc g hR (hv x hx) (hv y hy)
    (query_cells K fr p _ px (fun f hf => List.mem_append_left _ hf))
    (query_cells K fr p _ py (fun f hf => List.mem_append_right _ hf))

/-! ## The cost of a per-cell havoc -/

/-- The per-cell havoc set of a key has at most one origin. -/
theorem hvOf_length_le (s : Site) (k : Key) : (hvOf s k).length ≤ 1 := by
  cases k with
  | v x => exact Nat.zero_le _
  | h o c => exact Nat.le_refl _

/-- One `addKey` costs at most `4 + 4 |U|`. -/
theorem addKey_work {ctx : Ctx} (cc : CtxClosed ctx) {T : Tbl} (g : T.Good ctx.origins)
    {st : OState} (h : EntOK ctx T st) {k : Key} (hk : InU ctx k) (n : Nat) :
    (addKey ctx T st k n).1.work ≤ T.work + 4 + 4 * ctx.origins.length := by
  obtain ⟨g1, _, _, _⟩ := getId_spec cc g h hk
  have w1 := getId_work ctx T st k
  unfold addKey
  simp only
  generalize getId ctx T st k = r at g1 w1
  have w2 := Tbl.union_work ctx.origins r.2 r.1 n
  have l1 := g1.mem_length r.1
  have l2 := g1.mem_length n
  omega

/-- A per-cell havoc over the keys `ks` costs at most `6 + 4 |U|` for each key: one intern of a
singleton and one memoized union. -/
theorem addHv_work {ctx : Ctx} (cc : CtxClosed ctx) (s : Site) :
    ∀ (ks : List Key) {T : Tbl} {st : OState}, T.Good ctx.origins → EntOK ctx T st →
      (∀ k ∈ ks, InU ctx k) → (∀ k ∈ ks, hvOf s k ⊆ ctx.origins) →
      (addHv ctx s T st ks).1.work ≤ T.work + ks.length * (6 + 4 * ctx.origins.length)
  | [], T, st, _, _, _, _ => by simp [addHv]
  | k :: ks, T, st, g, h, hks, hhv => by
    obtain ⟨g0, e0, i0, _⟩ := Tbl.intern_none_spec g (hhv k List.mem_cons_self)
    have w0 := Tbl.intern_work ctx.origins T (hvOf s k) none
    have l0 := hvOf_length_le s k
    simp only [addHv]
    generalize T.intern ctx.origins (hvOf s k) none = n at g0 e0 i0 w0
    have w1 := addKey_work cc g0 (h.ext e0) (hks k List.mem_cons_self) n.1
    obtain ⟨g1, _, h1, _⟩ := addKey_spec cc g0 (h.ext e0) (hks k List.mem_cons_self) i0
    generalize addKey ctx n.2 st k n.1 = r at g1 h1 w1
    have w2 := addHv_work cc s ks g1 h1 (fun k' hk' => hks k' (List.mem_cons_of_mem _ hk'))
      (fun k' hk' => hhv k' (List.mem_cons_of_mem _ hk'))
    rw [List.length_cons, Nat.succ_mul]
    omega

end DirectedAlias.Opt.Hv

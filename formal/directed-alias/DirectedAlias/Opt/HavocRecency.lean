import DirectedAlias.Opt.Recency
import DirectedAlias.Opt.Havoc
import DirectedAlias.Sound.HavocRecency.Examples

/-!
# Optimization O with recency and per-cell havoc

The concept is `analyzeHR` (`Sound/HavocRecency/Concept.lean`). O combines the O retire of
`Opt/Recency.lean` (`retireO`) with a per-cell havoc on nodes (`havocHRO`). The per-cell havoc
is the one of `Opt/Havoc.lean` with the recency key `keyOfR`: for each universe cell of each
reachable universe origin, one interned singleton node and one memoized union (`addSets`).
The key of an allocation holder is `rOld s` for both recency origins, so `retireO` never has
to rename a per-cell havoc origin: `retireO_rel` holds without change.

Results: `havocHRO_rel` (one per-cell havoc), `ostepHR_rel` (one statement), `analyzeHRO_rel`
(the analysis), `mayProgHRO_eq` (O and the concept give the same may-alias Boolean, for both
strong-update policies), `addSets_work` (the cost of a per-cell havoc).
-/

namespace DirectedAlias.Opt.HvRec

open DirectedAlias DirectedAlias.Opt DirectedAlias.Opt.Rec DirectedAlias.Sound.HavocRecency

/-! ## The per-cell havoc of O with recency keys -/

/-- The per-cell havoc origin set of a key, with the recency key of the holder. -/
def hvOfR (s : Site) : Key → List Origin
  | .v _ => []
  | .h o c => [.hsym s (keyOfR o) c []]

/-- Add the set `f k` to each key `k` of `ks`: one interned node and one memoized union for
each key. -/
def addSets (ctx : Ctx) (f : Key → List Origin) : Tbl → OState → List Key → Tbl × OState
  | T, st, [] => (T, st)
  | T, st, k :: ks =>
    let n := T.intern ctx.origins (f k) none
    let r := addKey ctx n.2 st k n.1
    addSets ctx f r.1 r.2 ks

/-- The per-cell havoc of `Opt/Havoc.lean` is `addSets` with the set function `hvOf s`. -/
theorem addHv_eq_addSets (ctx : Ctx) (s : Site) :
    ∀ (T : Tbl) (st : OState) (ks : List Key), Hv.addHv ctx s T st ks = addSets ctx (Hv.hvOf s) T st ks
  | _, _, [] => rfl
  | _, _, _ :: ks => addHv_eq_addSets ctx s _ _ ks

/-- The per-cell havoc of call site `s` on O with recency keys: the reach test of `havocO`,
then `addSets` on each universe cell of each reachable universe origin. -/
def havocHRO (ctx : Ctx) (T : Tbl) (st : OState) (args : List Var) (s : Site) : Tbl × OState :=
  let r := reachB ctx (den ctx.K T st) args
  let ks := (ctx.origins.filter r).flatMap (fun o => ctx.cells.map (Key.h o))
  addSets ctx (hvOfR s) T st ks

/-- The O transfer of one statement with recency and per-cell havoc. Only the call differs
from `ostepR`: the per-cell havoc, then the retire, then the fresh result. -/
def ostepHR (ctx : Ctx) : Stmt → Tbl → OState → Tbl × OState
  | .call ret s args, T, st =>
    let a := havocHRO ctx T st args s
    let r := retireO ctx s a.1 a.2
    match ret with
    | none => r
    | some x => setKey ctx r.1 r.2 (.v x) [.sym (.fresh s) []]
  | st, T, s => ostepR ctx st T s

/-- The O analysis with recency and per-cell havoc. -/
def analyzeHRO (ctx : Ctx) : Prog → Tbl → OState → Tbl × OState
  | .skip, T, st => (T, st)
  | .stmt s, T, st => ostepHR ctx s T st
  | .seq p q, T, st =>
    let r := analyzeHRO ctx p T st
    analyzeHRO ctx q r.1 r.2
  | .choice p q, T, st =>
    let r1 := analyzeHRO ctx p T st
    let r2 := analyzeHRO ctx q r1.1 st
    let j := joinO ctx r2.1 r1.2 r2.2
    (j.1, j.2.1)
  | .loop p, T, st => loopO ctx (analyzeHRO ctx p) ctx.fuel T st

/-! ## Coverage and support -/

/-- The context covers a statement: the O recency coverage, and the per-cell havoc origin with
the recency key of each universe cell of each universe origin is in the universe. -/
def StmtOKHRO (ctx : Ctx) (st : Stmt) : Prop :=
  Opt.Rec.StmtOKR ctx st ∧ ∀ s, st.callSite? = some s → ∀ a ∈ ctx.origins, ∀ c ∈ ctx.cells,
    Origin.hsym s (keyOfR a) c [] ∈ ctx.origins

/-- The context covers every statement of the program. -/
def ProgOKHR (ctx : Ctx) (q : Prog) : Prop := ∀ st ∈ q.stmts, StmtOKHRO ctx st

/-- The key values after a per-cell havoc with recency keys. -/
theorem cval_havocHR (ctx : Ctx) (X : AState) (args : List Var) (s : Site) (k : Key) :
    cval (havocHR ctx X args s) k =
      match k with
      | .v x => X.env x
      | .h o c => if c ∈ ctx.cells ∧ reachB ctx X args o = true then
          uni [.hsym s (keyOfR o) c []] (X.heap o c) else X.heap o c := by
  cases k <;> rfl

/-- A per-cell havoc with recency keys keeps support if its origins are in the universe. -/
theorem supp_havocHR {ctx : Ctx} {X : AState} (hs : Supp ctx X) (args : List Var) {s : Site}
    (h : ∀ a ∈ ctx.origins, ∀ c ∈ ctx.cells, Origin.hsym s (keyOfR a) c [] ∈ ctx.origins) :
    Supp ctx (havocHR ctx X args s) := by
  intro k hk
  rw [cval_havocHR]
  cases k with
  | v x => exact hs (.v x) hk
  | h o c =>
    simp only
    split
    · exact uni_sub (by intro a ha; simp at ha; subst ha; exact h o hk.1 c hk.2)
        (hs (.h o c) hk)
    · exact hs (.h o c) hk

/-- One covered statement keeps support with recency and per-cell havoc. -/
theorem supp_astepHR {ctx : Ctx} (cc : CtxClosed ctx) (hr : RecOK ctx) {X : AState}
    (hs : Supp ctx X) {st : Stmt} (ok : StmtOKHRO ctx st) : Supp ctx (astepHR ctx st X) := by
  cases st with
  | call r s args =>
    exact (supp_retire hr (supp_havocHR hs args (ok.2 s rfl)) s).setRet r
      (by intro a ha; simp at ha; subst ha; exact ok.1.fresh s rfl)
  | new x s => exact supp_astepR cc hr hs ok.1
  | null x => exact supp_astepR cc hr hs ok.1
  | copy x y => exact supp_astepR cc hr hs ok.1
  | load x y f => exact supp_astepR cc hr hs ok.1
  | store x f y => exact supp_astepR cc hr hs ok.1
  | aload x y => exact supp_astepR cc hr hs ok.1
  | astore x y => exact supp_astepR cc hr hs ok.1
  | unknown x s => exact supp_astepR cc hr hs ok.1

/-! ## Simulation -/

/-- `addSets` adds the set `f k` to each key `k` of `ks`, and keeps the other values. -/
theorem addSets_spec {ctx : Ctx} (cc : CtxClosed ctx) (f : Key → List Origin) :
    ∀ (ks : List Key) {T : Tbl} {st : OState}, T.Good ctx.origins → EntOK ctx T st →
      (∀ k ∈ ks, InU ctx k) → (∀ k ∈ ks, f k ⊆ ctx.origins) →
      (addSets ctx f T st ks).1.Good ctx.origins ∧ T.Ext (addSets ctx f T st ks).1 ∧
      EntOK ctx (addSets ctx f T st ks).1 (addSets ctx f T st ks).2 ∧
      ∀ k', SetEq (val ctx.K (addSets ctx f T st ks).1 (addSets ctx f T st ks).2 k')
        (if k' ∈ ks then uni (val ctx.K T st k') (f k') else val ctx.K T st k')
  | [], T, st, g, h, _, _ => by
    refine ⟨g, Tbl.Ext.refl T, h, ?_⟩
    intro k'; simp only [addSets, List.not_mem_nil, ite_false]; exact SetEq.refl _
  | k :: ks, T, st, g, h, hks, hhv => by
    obtain ⟨g0, e0, i0, m0⟩ := Tbl.intern_none_spec g (hhv k List.mem_cons_self)
    simp only [addSets]
    generalize T.intern ctx.origins (f k) none = n at g0 e0 i0 m0
    obtain ⟨g1, e1, h1, m1⟩ := addKey_spec cc g0 (h.ext e0) (hks k List.mem_cons_self) i0
    generalize addKey ctx n.2 st k n.1 = r at g1 e1 h1 m1
    obtain ⟨g2, e2, h2, m2⟩ := addSets_spec cc f ks g1 h1
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
      have m1k' : SetEq (val ctx.K r.1 r.2 k') (uni (val ctx.K T st k') (f k')) :=
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

/-- The O per-cell havoc with recency keys represents the concept per-cell havoc. -/
theorem havocHRO_rel {ctx : Ctx} (cc : CtxClosed ctx) {T : Tbl} (g : T.Good ctx.origins)
    {st : OState} {X : AState} (hR : Rel ctx T st X) {s : Site} {args : List Var}
    (hargs : ∀ x ∈ args, x ∈ ctx.vars)
    (hhv : ∀ a ∈ ctx.origins, ∀ c ∈ ctx.cells, Origin.hsym s (keyOfR a) c [] ∈ ctx.origins) :
    (havocHRO ctx T st args s).1.Good ctx.origins ∧ T.Ext (havocHRO ctx T st args s).1 ∧
      Rel ctx (havocHRO ctx T st args s).1 (havocHRO ctx T st args s).2 (havocHR ctx X args s) := by
  have hreach : reachB ctx (den ctx.K T st) args = reachB ctx X args :=
    (reachB_congr hR.supp hargs (fun k hk => by
      rw [cval_den]; exact (hR.agree k hk).symm)).symm
  unfold havocHRO
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
      (fun o => ctx.cells.map (Key.h o)), hvOfR s k ⊆ ctx.origins := by
    intro k hk
    obtain ⟨o, c, rfl, h1, _, h3⟩ := (hmemks k).mp hk
    intro a ha
    simp only [hvOfR, List.mem_singleton] at ha
    subst ha
    exact hhv o h1 c h3
  obtain ⟨g2, e2, h2, m2⟩ := addSets_spec cc (hvOfR s) _ g hR.ent hks hhs
  refine ⟨g2, e2, rel_of_vals h2 (supp_havocHR hR.supp args hhv) _ m2 ?_⟩
  intro k hk
  rw [cval_havocHR]
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

/-- Each O step with recency and per-cell havoc represents the concept step. -/
theorem ostepHR_rel {ctx : Ctx} (cc : CtxClosed ctx) (hr : RecOK ctx) {T : Tbl}
    (g : T.Good ctx.origins) {st : OState} {X : AState} (hR : Rel ctx T st X) {s : Stmt}
    (ok : StmtOKHRO ctx s) :
    (ostepHR ctx s T st).1.Good ctx.origins ∧ T.Ext (ostepHR ctx s T st).1 ∧
      Rel ctx (ostepHR ctx s T st).1 (ostepHR ctx s T st).2 (astepHR ctx s X) := by
  cases s with
  | call ret s args =>
    have hargs : ∀ x ∈ args, x ∈ ctx.vars := fun x hx => ok.1.vars x (by simp [Stmt.vars, hx])
    obtain ⟨g1, e1, r1⟩ := havocHRO_rel cc g hR hargs (ok.2 s rfl)
    obtain ⟨g2, e2, r2⟩ := retireO_rel cc hr g1 r1 s
    simp only [ostepHR, astepHR]
    generalize havocHRO ctx T st args s = a at g1 e1 r1 g2 e2 r2
    generalize retireO ctx s a.1 a.2 = r at g2 e2 r2
    cases ret with
    | none => exact ⟨g2, e1.trans e2, r2⟩
    | some x =>
      obtain ⟨g3, e3, r3⟩ := setKey_rel g2 r2 (ok.1.vars x (by simp [Stmt.vars]))
        (S := [.sym (.fresh s) []]) (by intro a ha; simp at ha; subst ha; exact ok.1.fresh s rfl)
      exact ⟨g3, e1.trans (e2.trans e3), r3⟩
  | new x s => exact ostepR_rel cc hr g hR ok.1
  | null x => exact ostepR_rel cc hr g hR ok.1
  | copy x y => exact ostepR_rel cc hr g hR ok.1
  | load x y f => exact ostepR_rel cc hr g hR ok.1
  | store x f y => exact ostepR_rel cc hr g hR ok.1
  | aload x y => exact ostepR_rel cc hr g hR ok.1
  | astore x y => exact ostepR_rel cc hr g hR ok.1
  | unknown x s => exact ostepR_rel cc hr g hR ok.1

/-- The O analysis with recency and per-cell havoc represents the concept analysis on the
universe. -/
theorem analyzeHRO_rel {ctx : Ctx} (cc : CtxClosed ctx) (hr : RecOK ctx) :
    ∀ (q : Prog) (T : Tbl) (st : OState) (X : AState), ProgOKHR ctx q → T.Good ctx.origins →
      Rel ctx T st X →
      (analyzeHRO ctx q T st).1.Good ctx.origins ∧ T.Ext (analyzeHRO ctx q T st).1 ∧
      Rel ctx (analyzeHRO ctx q T st).1 (analyzeHRO ctx q T st).2 (analyzeHR ctx q X)
  | .skip, T, _, _, _, g, hR => ⟨g, Tbl.Ext.refl T, hR⟩
  | .stmt s, _, _, _, ok, g, hR => ostepHR_rel cc hr g hR (ok s (by simp [Prog.stmts]))
  | .seq p q, T, st, X, ok, g, hR => by
    obtain ⟨g1, e1, r1⟩ := analyzeHRO_rel cc hr p T st X
      (fun st hs => ok st (List.mem_append_left _ hs)) g hR
    simp only [analyzeHRO, analyzeHR]
    generalize analyzeHRO ctx p T st = r at g1 e1 r1
    obtain ⟨g2, e2, r2⟩ := analyzeHRO_rel cc hr q r.1 r.2 _
      (fun st hs => ok st (List.mem_append_right _ hs)) g1 r1
    exact ⟨g2, e1.trans e2, r2⟩
  | .choice p q, T, st, X, ok, g, hR => by
    obtain ⟨g1, e1, r1⟩ := analyzeHRO_rel cc hr p T st X
      (fun st hs => ok st (List.mem_append_left _ hs)) g hR
    simp only [analyzeHRO, analyzeHR]
    generalize analyzeHRO ctx p T st = a at g1 e1 r1
    obtain ⟨g2, e2, r2⟩ := analyzeHRO_rel cc hr q a.1 st X
      (fun st hs => ok st (List.mem_append_right _ hs)) g1 (hR.ext e1)
    generalize analyzeHRO ctx q a.1 st = b at g2 e2 r2
    obtain ⟨g3, e3, r3⟩ := joinO_rel cc g2 (r1.ext e2) r2
    exact ⟨g3, e1.trans (e2.trans e3), r3⟩
  | .loop p, T, st, X, ok, g, hR => by
    simp only [analyzeHRO, analyzeHR]
    exact loopO_rel cc (fun T' st' Y g' hR' => analyzeHRO_rel cc hr p T' st' Y ok g' hR')
      ctx.fuel T st X g hR

/-! ## Whole programs -/

/-- The context of recency with per-cell havoc is closed under default content. -/
theorem ctxClosed_HR (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    CtxClosed (ctxHR eu K fr p qf) :=
  ⟨fun o ho c hc o' ho' => (ctxHR_ok eu K fr p qf).base.dflt o ho c hc o' ho',
    (ctxHR_ok eu K fr p qf).base.elem⟩

/-- The universe of recency with per-cell havoc has both recency origins of a site or neither. -/
theorem recOK_HR (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    RecOK (ctxHR eu K fr p qf) := fun s =>
  ⟨(ctxHR_ok eu K fr p qf).newOld s, (ctxHR_ok eu K fr p qf).oldNew s⟩

/-- The context of recency with per-cell havoc covers every statement of the program. -/
theorem progOKHR_HR (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    ProgOKHR (ctxHR eu K fr p qf) p := fun st hst =>
  let o := ctxHR_stmts eu K fr p qf st hst
  ⟨⟨o.ok.vars, o.ok.fields, o.ok.newS, o.ok.freshS, o.ok.callS⟩, o.callH⟩

/-- The entry state has support in the context of recency with per-cell havoc. -/
theorem supp_ainitHR (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    Supp (ctxHR eu K fr p qf) (ainit K fr) := by
  intro k hk
  cases k with
  | v x =>
    intro o ho
    exact List.mem_append_left _ (supp_ainitR eu K fr p qf (.v x) hk ho)
  | h o c => exact (ctxClosed_HR eu K fr p qf).dflt o hk.1 c hk.2

/-- The final O state of program `p` with recency and per-cell havoc. -/
def analyzeProgHRO (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    Tbl × OState :=
  let ctx := ctxHR eu K fr p qf
  let i := initO ctx fr
  analyzeHRO ctx p i.1 i.2

/-- O may-alias with recency and per-cell havoc at the end of program `p`. -/
def mayProgHRO (eu : Bool) (K : Nat) (fr : Frame) (p : Prog)
    (x : Var) (px : List ACell) (y : Var) (py : List ACell) : Bool :=
  let r := analyzeProgHRO eu K fr p (afields px ++ afields py)
  omay (ctxHR eu K fr p (afields px ++ afields py)) r.1 r.2 x px y py

/-- For each policy and each program, the final O state with recency and per-cell havoc
represents the final concept state. -/
theorem analyzeProgHRO_rel (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    (analyzeProgHRO eu K fr p qf).1.Good (ctxHR eu K fr p qf).origins ∧
      Rel (ctxHR eu K fr p qf) (analyzeProgHRO eu K fr p qf).1 (analyzeProgHRO eu K fr p qf).2
        (analyzeProgHR eu K fr p qf) := by
  have cc := ctxClosed_HR eu K fr p qf
  have hfv : ∀ x ∈ fr.vars, x ∈ (ctxHR eu K fr p qf).vars := by
    intro x hx
    simp only [ctxHR]
    rw [List.mem_eraseDups]
    exact List.mem_append_right _ hx
  obtain ⟨g0, r0⟩ := initO_rel (ctx := ctxHR eu K fr p qf) fr (supp_ainitHR eu K fr p qf) hfv
  obtain ⟨g1, _, r1⟩ := analyzeHRO_rel cc (recOK_HR eu K fr p qf) p _ _ _
    (progOKHR_HR eu K fr p qf) g0 r0
  exact ⟨g1, r1⟩

/-- For both strong-update policies, O with recency and per-cell havoc and the concept give
the same may-alias answer. -/
theorem mayProgHRO_eq (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (x : Var) (px : List ACell)
    (y : Var) (py : List ACell) (hx : x ∈ p.vars ++ fr.vars) (hy : y ∈ p.vars ++ fr.vars) :
    mayProgHRO eu K fr p x px y py = mayProgHR eu K fr p x px y py := by
  have cc := ctxClosed_HR eu K fr p (afields px ++ afields py)
  obtain ⟨g, hR⟩ := analyzeProgHRO_rel eu K fr p (afields px ++ afields py)
  unfold mayProgHRO mayProgHR
  simp only
  have hv : ∀ z, z ∈ p.vars ++ fr.vars →
      z ∈ (ctxHR eu K fr p (afields px ++ afields py)).vars := by
    intro z hz; simp only [ctxHR]; rw [List.mem_eraseDups]; exact hz
  exact omay_eq cc g hR (hv x hx) (hv y hy)
    (query_cells K fr p _ px (fun f hf => List.mem_append_left _ hf))
    (query_cells K fr p _ py (fun f hf => List.mem_append_right _ hf))

/-- O with recency and per-cell havoc is sound under strict A2: each strict one-execution
alias of program variables is a may-alias of `mayProgHRO`. -/
theorem csoundHRO (src : Nat → Obj × Cell) (eu : Bool) (K : Nat) (fr : Frame) (p : Prog)
    (x : Var) (px : List Cell) (y : Var) (py : List Cell) (hx : x ∈ p.vars ++ fr.vars)
    (hy : y ∈ p.vars ++ fr.vars) (h : Sound.Havoc.CAliasS src fr p x px y py) :
    mayProgHRO eu K fr p x (px.map Cell.abs) y (py.map Cell.abs) = true := by
  rw [mayProgHRO_eq eu K fr p x _ y _ hx hy]
  exact csoundHR src eu K fr p x px y py h

/-! ## The cost of a per-cell havoc -/

/-- A per-cell havoc set with recency keys has at most one origin. -/
theorem hvOfR_length_le (s : Site) (k : Key) : (hvOfR s k).length ≤ 1 := by
  cases k with
  | v x => exact Nat.zero_le _
  | h o c => exact Nat.le_refl _

/-- `addSets` with sets of at most one origin costs at most `6 + 4 |U|` for each key: one
intern of a singleton and one memoized union. -/
theorem addSets_work {ctx : Ctx} (cc : CtxClosed ctx) (f : Key → List Origin)
    (hf : ∀ k, (f k).length ≤ 1) :
    ∀ (ks : List Key) {T : Tbl} {st : OState}, T.Good ctx.origins → EntOK ctx T st →
      (∀ k ∈ ks, InU ctx k) → (∀ k ∈ ks, f k ⊆ ctx.origins) →
      (addSets ctx f T st ks).1.work ≤ T.work + ks.length * (6 + 4 * ctx.origins.length)
  | [], T, st, _, _, _, _ => by simp [addSets]
  | k :: ks, T, st, g, h, hks, hhv => by
    obtain ⟨g0, e0, i0, _⟩ := Tbl.intern_none_spec g (hhv k List.mem_cons_self)
    have w0 := Tbl.intern_work ctx.origins T (f k) none
    have l0 := hf k
    simp only [addSets]
    generalize T.intern ctx.origins (f k) none = n at g0 e0 i0 w0
    have w1 := Hv.addKey_work cc g0 (h.ext e0) (hks k List.mem_cons_self) n.1
    obtain ⟨g1, _, h1, _⟩ := addKey_spec cc g0 (h.ext e0) (hks k List.mem_cons_self) i0
    generalize addKey ctx n.2 st k n.1 = r at g1 h1 w1
    have w2 := addSets_work cc f hf ks g1 h1 (fun k' hk' => hks k' (List.mem_cons_of_mem _ hk'))
      (fun k' hk' => hhv k' (List.mem_cons_of_mem _ hk'))
    rw [List.length_cons, Nat.succ_mul]
    omega

/-! ## Examples -/

namespace HRExamples

open DirectedAlias.Examples DirectedAlias.Sound.Havoc.Examples
open DirectedAlias.Sound.HavocRecency.Examples

/-- O with recency and per-cell havoc, run by the kernel: `b.f` does not alias `x` after
the loop. -/
theorem o_loop_bf_x : mayProgHRO true 1 fr pLoop vb [.fld ff] vx [] = false := by decide +kernel

/-- O with recency and per-cell havoc, run by the kernel on the cost example (allocation, call,
retire, load): `t ~ u` is true, as in the concept. -/
theorem o_cost : mayProgHRO true 0 frE pCost va [] vz [] = true := by decide +kernel

/-- O with recency and per-cell havoc: the spread on `pHv` is gone, and `a ~ x.f` stays
(from `mayProgHRO_eq` and the concept answers). -/
theorem o_pHv : mayProgHRO true 0 fr pHv va [] vb [] = false ∧
    mayProgHRO true 0 fr pHv va [] vx [.fld ff] = true := by
  rw [mayProgHRO_eq true 0 fr pHv va [] vb [] (by decide) (by decide),
    mayProgHRO_eq true 0 fr pHv va [] vx [.fld ff] (by decide) (by decide)]
  exact ⟨strict_answersHR.1, strict_answersHR.2.2.2.1⟩

/-- O with recency and per-cell havoc answers both questions of `pBoth` with false (from
`mayProgHRO_eq` and the concept answers). -/
theorem o_both : mayProgHRO true 0 frB pBoth vb [.fld ff] vx [] = false ∧
    mayProgHRO true 0 frB pBoth va [] vz [] = false := by
  rw [mayProgHRO_eq true 0 frB pBoth vb [.fld ff] vx [] (by decide) (by decide),
    mayProgHRO_eq true 0 frB pBoth va [] vz [] (by decide) (by decide)]
  exact ⟨both_answers.1, both_answers.2.1⟩

end HRExamples

end DirectedAlias.Opt.HvRec

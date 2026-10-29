import DirectedAlias.Opt.LoopCost
import DirectedAlias.Sound.Recency.Concept
import DirectedAlias.Sound.Recency.Soundness
import DirectedAlias.Examples

/-!
# Optimization O with recency

The recency concept (`Sound/Recency/Concept.lean`) gives each allocation site two origins,
`rNew s` and `rOld s`. When site `s` runs, `retire s` renames `rNew s` to `rOld s` in every value,
moves the cells of `rNew s` into the cells of `rOld s` (weakly), and resets the cells of `rNew s`.

O realizes `retire` on nodes (`retireO`):
1. For each universe cell `c`: the cell `(rOld s, c)` gets the memoized union of the nodes of
   `(rNew s, c)` and `(rOld s, c)`, and the cell `(rNew s, c)` gets its default content (null).
2. Each map entry whose node holds `rNew s` gets the interned node of the renamed set. The other
   entries keep their node ids.

Results: `retireO_rel` (one retire), `ostepR_rel` (one statement), `analyzeRO_rel` (the
analysis), `mayProgRO_eq` (the may-alias Boolean is the recency concept Boolean, for both
strong-update policies), and `retireO_work` (the cost of a retire).
-/

namespace DirectedAlias.Opt.Rec

open DirectedAlias DirectedAlias.Opt DirectedAlias.Sound.Recency

/-! ## Renaming lemmas -/

/-- Membership in a renamed set. -/
theorem mem_renameL {s : Site} {l : List Origin} {o' : Origin} :
    o' ∈ renameL s l ↔ ∃ o ∈ l, renameO s o = o' := by
  simp [renameL, List.mem_map]

/-- Renaming keeps set equality. -/
theorem renameL_congr {s : Site} {l l' : List Origin} (h : SetEq l l') :
    SetEq (renameL s l) (renameL s l') := by
  intro o'
  rw [mem_renameL, mem_renameL]
  constructor
  · rintro ⟨o, ho, he⟩; exact ⟨o, (h o).mp ho, he⟩
  · rintro ⟨o, ho, he⟩; exact ⟨o, (h o).mpr ho, he⟩

/-- Renaming does not change a set without `rNew s`. -/
theorem renameL_of_not_mem {s : Site} : ∀ {l : List Origin}, rNew s ∉ l → renameL s l = l
  | [], _ => rfl
  | o :: l, h => by
    have h1 : o ≠ rNew s := fun he => h (he ▸ List.mem_cons_self)
    have h2 : rNew s ∉ l := fun hm => h (List.mem_cons_of_mem _ hm)
    simp only [renameL, List.map_cons, renameO, ite_eq_right h1]
    exact congrArg _ (renameL_of_not_mem h2)

/-- The default content of a key has no allocation origin, so renaming does not change it. -/
theorem renameL_dflt (s : Site) (K : Nat) (k : Key) : renameL s (dflt K k) = dflt K k := by
  apply renameL_of_not_mem
  intro h
  cases k with
  | v x => cases h
  | h o c =>
    cases o with
    | sym b q =>
      simp only [dflt, adefault, List.mem_singleton, rNew, symOrDeep] at h
      split at h <;> cases h
    | deep b => simp [dflt, adefault, rNew] at h
    | alloc a => cases h
    | havoc t => simp [dflt, adefault, rNew] at h
    | hsym t k c0 q =>
      simp only [dflt, adefault, List.mem_singleton, rNew] at h
      split at h <;> cases h
    | hdeep t k c0 => simp [dflt, adefault, rNew] at h

/-- The universe has `rNew s` if and only if it has `rOld s`. -/
def RecOK (ctx : Ctx) : Prop := ∀ s, rNew s ∈ ctx.origins ↔ rOld s ∈ ctx.origins

/-- Renaming keeps a set inside the universe. -/
theorem renameL_sub {ctx : Ctx} (hr : RecOK ctx) {s : Site} {l : List Origin}
    (h : l ⊆ ctx.origins) : renameL s l ⊆ ctx.origins := by
  intro o' ho'
  obtain ⟨o, ho, rfl⟩ := mem_renameL.mp ho'
  unfold renameO
  split
  · rename_i he; subst he; exact (hr s).mp (h ho)
  · exact h ho

/-- The length of a renamed set is the length of the set. -/
theorem length_renameL (s : Site) (l : List Origin) : (renameL s l).length = l.length := by
  simp [renameL]

/-- The recency origins of one site are different. -/
theorem rNew_ne_rOld (s : Site) : rNew s ≠ rOld s := by
  intro h
  exact (fun a (h : 2 * a = 2 * a + 1) => by omega : ∀ a : Nat, 2 * a = 2 * a + 1 → False) s
    (Origin.alloc.inj h)

/-! ## The concept side -/

/-- The key values after `retire`. -/
theorem cval_retire (s : Site) (X : AState) (k : Key) :
    cval (retire s X) k =
      match k with
      | .v x => renameL s (X.env x)
      | .h o c => if o = rNew s then [] else if o = rOld s then
          renameL s (uni (X.heap (rNew s) c) (X.heap (rOld s) c)) else renameL s (X.heap o c) := by
  cases k <;> rfl

/-- `retire` keeps support. -/
theorem supp_retire {ctx : Ctx} (hr : RecOK ctx) {X : AState} (hs : Supp ctx X) (s : Site) :
    Supp ctx (Sound.Recency.retire s X) := by
  intro k hk
  rw [cval_retire]
  cases k with
  | v x => exact renameL_sub hr (hs (.v x) hk)
  | h o c =>
    simp only
    split
    · intro _ h; cases h
    · split
      · rename_i _ he
        subst he
        have hn : rNew s ∈ ctx.origins := (hr s).mpr hk.1
        exact renameL_sub hr (uni_sub (hs (.h _ c) ⟨hn, hk.2⟩) (hs (.h _ c) hk))
      · exact renameL_sub hr (hs (.h o c) hk)

/-- The recency store keeps support. -/
theorem supp_storeR {ctx : Ctx} {X : AState} (hs : Supp ctx X) (x : Var) (c : ACell)
    {S : List Origin} (hS : S ⊆ ctx.origins) : Supp ctx (Sound.Recency.storeR ctx X x c S) := by
  unfold Sound.Recency.storeR
  split
  · split
    · intro k hk
      rw [cval_setCell]
      split
      · exact hS
      · exact hs k hk
    · exact hs.weakStore _ c hS
  · exact hs.weakStore _ c hS

/-- The context covers the statement for the recency analysis: an allocation gives `rNew s`. -/
structure StmtOKR (ctx : Ctx) (st : Stmt) : Prop where
  vars : ∀ x ∈ st.vars, x ∈ ctx.vars
  fields : ∀ f ∈ st.fields, ACell.fld f ∈ ctx.cells
  new : ∀ s, st.newSite? = some s → rNew s ∈ ctx.origins
  fresh : ∀ s, st.freshSite? = some s → Origin.sym (.fresh s) [] ∈ ctx.origins
  call : ∀ s, st.callSite? = some s → Origin.havoc s ∈ ctx.origins

/-- The context covers every statement of the program, for the recency analysis. -/
def ProgOKR (ctx : Ctx) (q : Prog) : Prop := ∀ st ∈ q.stmts, StmtOKR ctx st

/-- A statement that is not an allocation is covered in the sense of `StmtOK`. -/
theorem StmtOKR.toOK {ctx : Ctx} {st : Stmt} (h : StmtOKR ctx st) (hn : st.newSite? = none) :
    StmtOK ctx st :=
  ⟨h.vars, h.fields, (fun s hs => by rw [hn] at hs; cases hs), h.fresh, h.call⟩

/-- One recency statement keeps support. -/
theorem supp_astepR {ctx : Ctx} (cc : CtxClosed ctx) (hr : RecOK ctx) {X : AState}
    (hs : Supp ctx X) {st : Stmt} (ok : StmtOKR ctx st) : Supp ctx (astepR ctx st X) := by
  cases st with
  | new x s =>
    exact (supp_retire hr hs s).setVar x (by intro a ha; simp at ha; subst ha; exact ok.new s rfl)
  | unknown x s =>
    exact (supp_retire hr hs s).setVar x (by intro a ha; simp at ha; subst ha; exact ok.fresh s rfl)
  | call r s args =>
    exact (supp_retire hr (hs.havoc args (ok.call s rfl)) s).setRet r
      (by intro a ha; simp at ha; subst ha; exact ok.fresh s rfl)
  | store x f y =>
    exact supp_storeR hs x _ (hs.env (ok.vars y (by simp [Stmt.vars])))
  | null x => exact hs.astep cc (ok.toOK rfl)
  | copy x y => exact hs.astep cc (ok.toOK rfl)
  | load x y f => exact hs.astep cc (ok.toOK rfl)
  | aload x y => exact hs.astep cc (ok.toOK rfl)
  | astore x y => exact hs.astep cc (ok.toOK rfl)

/-- The recency analysis of a covered program keeps support. -/
theorem supp_analyzeR {ctx : Ctx} (cc : CtxClosed ctx) (hr : RecOK ctx) :
    ∀ (q : Prog) (X : AState), ProgOKR ctx q → Supp ctx X → Supp ctx (analyzeR ctx q X)
  | .skip, _, _, h => h
  | .stmt st, _, ok, h => supp_astepR cc hr h (ok st (by simp [Prog.stmts]))
  | .seq p q, X, ok, h =>
    supp_analyzeR cc hr q _ (fun st hs => ok st (List.mem_append_right _ hs))
      (supp_analyzeR cc hr p X (fun st hs => ok st (List.mem_append_left _ hs)) h)
  | .choice p q, X, ok, h =>
    (supp_analyzeR cc hr p X (fun st hs => ok st (List.mem_append_left _ hs)) h).join
      (supp_analyzeR cc hr q X (fun st hs => ok st (List.mem_append_right _ hs)) h)
  | .loop p, X, ok, h =>
    Supp.loopIter (fun Y hY => supp_analyzeR cc hr p Y ok hY) _ X h

/-! ## The O retire -/

/-- The merged value of a cell of `rOld s`: the union of the cells of `rNew s` and `rOld s`. -/
def mergeVal (K : Nat) (s : Site) (T : Tbl) (st : OState) : Key → List Origin
  | .h _ c => uni (val K T st (.h (rNew s) c)) (val K T st (.h (rOld s) c))
  | k => val K T st k

/-- Step 1 of the O retire: for each cell, merge the `rNew s` cell into the `rOld s` cell, and
reset the `rNew s` cell. It reads the input map `st0` and writes the map `out`. -/
def mergeCells (ctx : Ctx) (s : Site) (st0 : OState) : List ACell → Tbl → OState → Tbl × OState
  | [], T, out => (T, out)
  | c :: cs, T, out =>
    let a := getId ctx T st0 (.h (rNew s) c)
    let b := getId ctx a.2 st0 (.h (rOld s) c)
    let u := b.2.union ctx.origins a.1 b.1
    mergeCells ctx s st0 cs u.2 (oerase (oset out (.h (rOld s) c) u.1) (.h (rNew s) c))

/-- The node of a key is a holder of `rNew s` in table `T`. -/
def holderB (s : Site) (T : Tbl) (st : OState) (k : Key) : Bool :=
  match oget st k with
  | some i => decide (rNew s ∈ T.mem i)
  | none => false

/-- Step 2 of the O retire: rename each listed key of `st` into `out`. A key whose node does not
hold `rNew s` keeps its node id at no cost. -/
def renameKeys (ctx : Ctx) (s : Site) (st : OState) : List Key → Tbl → OState → Tbl × OState
  | [], T, out => (T, out)
  | k :: ks, T, out =>
    match oget st k with
    | none => renameKeys ctx s st ks T (oerase out k)
    | some i =>
      if rNew s ∈ T.mem i then
        let r := T.intern ctx.origins (renameL s (T.mem i)) none
        renameKeys ctx s st ks r.2 (oset out k r.1)
      else renameKeys ctx s st ks T (oset out k i)

/-- The O retire of site `s`. If the universe has no `rNew s`, no value holds it, and nothing
changes on the universe. -/
def retireO (ctx : Ctx) (s : Site) (T : Tbl) (st : OState) : Tbl × OState :=
  if rNew s ∈ ctx.origins then
    let m := mergeCells ctx s st ctx.cells T st
    renameKeys ctx s m.2 (m.2.map Prod.fst) m.1 []
  else (T, st)

/-- Step 1: the merged cells of `rOld s` get the merged value, the cells of `rNew s` get null,
and the other keys keep the values of `out`. -/
theorem mergeCells_spec {ctx : Ctx} (cc : CtxClosed ctx) {s : Site}
    (hn : rNew s ∈ ctx.origins) (ho : rOld s ∈ ctx.origins) {st0 : OState} :
    ∀ (cs : List ACell) {T : Tbl} {out : OState}, T.Good ctx.origins → EntOK ctx T st0 →
      EntOK ctx T out → (∀ c ∈ cs, c ∈ ctx.cells) →
      (mergeCells ctx s st0 cs T out).1.Good ctx.origins ∧ T.Ext (mergeCells ctx s st0 cs T out).1 ∧
      EntOK ctx (mergeCells ctx s st0 cs T out).1 (mergeCells ctx s st0 cs T out).2 ∧
      ∀ k, SetEq (val ctx.K (mergeCells ctx s st0 cs T out).1 (mergeCells ctx s st0 cs T out).2 k)
        (if k ∈ cs.map (Key.h (rOld s)) then mergeVal ctx.K s T st0 k
         else if k ∈ cs.map (Key.h (rNew s)) then [] else val ctx.K T out k)
  | [], T, out, g, _, ho', _ => by
    refine ⟨g, Tbl.Ext.refl T, ho', ?_⟩
    intro k; simp only [mergeCells, List.map_nil, List.not_mem_nil, ite_false]
    exact SetEq.refl _
  | c :: cs, T, out, g, h0, hout, hcs => by
    have hc : c ∈ ctx.cells := hcs c List.mem_cons_self
    have kn : InU ctx (.h (rNew s) c) := ⟨hn, hc⟩
    have kd : InU ctx (.h (rOld s) c) := ⟨ho, hc⟩
    obtain ⟨ga, ea, ia, ma⟩ := getId_spec cc g h0 kn
    simp only [mergeCells]
    generalize getId ctx T st0 (.h (rNew s) c) = a at ga ea ia ma
    obtain ⟨gb, eb, ib, mb⟩ := getId_spec cc ga (h0.ext ea) kd
    generalize getId ctx a.2 st0 (.h (rOld s) c) = b at gb eb ib mb
    have iab : a.1 < b.2.size := Nat.lt_of_lt_of_le ia eb.size_le
    obtain ⟨gu, eu, iu, mu⟩ := Tbl.union_spec gb iab ib
    generalize b.2.union ctx.origins a.1 b.1 = u at gu eu iu mu
    have eT : T.Ext u.2 := ea.trans (eb.trans eu)
    have hU : SetEq (u.2.mem u.1)
        (uni (val ctx.K T st0 (.h (rNew s) c)) (val ctx.K T st0 (.h (rOld s) c))) := by
      rw [eb.mem_eq ia] at mu
      refine mu.trans (SetEq.uni ma ?_)
      rw [← val_ext h0 ea]; exact mb
    have hout1 : EntOK ctx u.2 (oerase (oset out (.h (rOld s) c) u.1) (.h (rNew s) c)) :=
      ((hout.ext eT).oset iu kd).oerase _
    obtain ⟨g2, e2, h2, m2⟩ := mergeCells_spec cc hn ho cs gu (h0.ext eT) hout1
      (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc'))
    refine ⟨g2, eT.trans e2, h2, ?_⟩
    intro k
    refine (m2 k).trans ?_
    have hmv : mergeVal ctx.K s u.2 st0 k = mergeVal ctx.K s T st0 k := by
      cases k <;> simp only [mergeVal, val_ext h0 eT]
    rw [hmv, val_oerase, val_oset, val_ext hout eT]
    have hne : Key.h (rNew s) c ≠ Key.h (rOld s) c := by
      intro he; exact rNew_ne_rOld s (Key.h.inj he).1
    by_cases h1 : k ∈ cs.map (Key.h (rOld s))
    · rw [ite_eq_left h1, ite_eq_left (by simp only [List.map_cons]; exact List.mem_cons_of_mem _ h1)]
      exact SetEq.refl _
    · rw [ite_eq_right h1]
      by_cases h2 : k ∈ cs.map (Key.h (rNew s))
      · rw [ite_eq_left h2]
        have h3 : k ∉ (c :: cs).map (Key.h (rOld s)) := by
          simp only [List.map_cons, List.mem_cons]
          rintro (he | he)
          · obtain ⟨c', _, hc'⟩ := List.mem_map.mp h2
            rw [he] at hc'; exact rNew_ne_rOld s (Key.h.inj hc').1
          · exact h1 he
        rw [ite_eq_right h3, ite_eq_left (by simp only [List.map_cons]; exact List.mem_cons_of_mem _ h2)]
        exact SetEq.refl _
      · rw [ite_eq_right h2]
        by_cases hk1 : k = Key.h (rNew s) c
        · subst hk1
          have h3 : Key.h (rNew s) c ∉ (c :: cs).map (Key.h (rOld s)) := by
            simp only [List.map_cons, List.mem_cons]
            rintro (he | he)
            · exact hne he
            · exact h1 he
          rw [ite_eq_left rfl, ite_eq_right h3, ite_eq_left (List.mem_map.mpr ⟨c, List.mem_cons_self, rfl⟩)]
          simp only [dflt, adefault, rNew]
          exact SetEq.refl _
        · rw [ite_eq_right hk1]
          by_cases hk2 : k = Key.h (rOld s) c
          · subst hk2
            rw [ite_eq_left rfl, ite_eq_left (List.mem_map.mpr ⟨c, List.mem_cons_self, rfl⟩)]
            exact hU
          · rw [ite_eq_right hk2]
            have h3 : k ∉ (c :: cs).map (Key.h (rOld s)) := by
              simp only [List.map_cons, List.mem_cons]
              rintro (he | he)
              · exact hk2 he
              · exact h1 he
            have h4 : k ∉ (c :: cs).map (Key.h (rNew s)) := by
              simp only [List.map_cons, List.mem_cons]
              rintro (he | he)
              · exact hk1 he
              · exact h2 he
            rw [ite_eq_right h3, ite_eq_right h4]
            exact SetEq.refl _

/-- Step 2: each listed key gets the renamed value of `st`; the other keys keep the values of
`out`. -/
theorem renameKeys_spec {ctx : Ctx} (hr : RecOK ctx) {s : Site} {st : OState} :
    ∀ (ks : List Key) {T : Tbl} {out : OState}, T.Good ctx.origins → EntOK ctx T st →
      EntOK ctx T out → (∀ k ∈ ks, InU ctx k) →
      (renameKeys ctx s st ks T out).1.Good ctx.origins ∧ T.Ext (renameKeys ctx s st ks T out).1 ∧
      EntOK ctx (renameKeys ctx s st ks T out).1 (renameKeys ctx s st ks T out).2 ∧
      ∀ k, SetEq (val ctx.K (renameKeys ctx s st ks T out).1 (renameKeys ctx s st ks T out).2 k)
        (if k ∈ ks then renameL s (val ctx.K T st k) else val ctx.K T out k)
  | [], T, out, g, _, ho, _ => by
    refine ⟨g, Tbl.Ext.refl T, ho, ?_⟩
    intro k; simp only [renameKeys, List.not_mem_nil, ite_false]; exact SetEq.refl _
  | k :: ks, T, out, g, h0, hout, hks => by
    have hk : InU ctx k := hks k List.mem_cons_self
    have hks' : ∀ k' ∈ ks, InU ctx k' := fun k' h => hks k' (List.mem_cons_of_mem _ h)
    -- the combination of the step and the rest
    have comb : ∀ (T' : Tbl) (out' : OState) (V : List Origin), T.Ext T' →
        (∀ k', SetEq (val ctx.K (renameKeys ctx s st ks T' out').1
          (renameKeys ctx s st ks T' out').2 k')
          (if k' ∈ ks then renameL s (val ctx.K T' st k') else val ctx.K T' out' k')) →
        (∀ k', val ctx.K T' out' k' = if k' = k then V else val ctx.K T out k') →
        SetEq V (renameL s (val ctx.K T st k)) →
        ∀ k', SetEq (val ctx.K (renameKeys ctx s st ks T' out').1
          (renameKeys ctx s st ks T' out').2 k')
          (if k' ∈ k :: ks then renameL s (val ctx.K T st k') else val ctx.K T out k') := by
      intro T' out' V e hm hv hV k'
      refine (hm k').trans ?_
      rw [val_ext h0 e, hv k']
      by_cases h1 : k' ∈ ks
      · rw [ite_eq_left h1, ite_eq_left (List.mem_cons_of_mem _ h1)]; exact SetEq.refl _
      · rw [ite_eq_right h1]
        by_cases h2 : k' = k
        · subst h2; rw [ite_eq_left rfl, ite_eq_left List.mem_cons_self]; exact hV
        · have : k' ∉ k :: ks := by simp [h1, h2]
          rw [ite_eq_right h2, ite_eq_right this]; exact SetEq.refl _
    simp only [renameKeys]
    cases hg : oget st k with
    | none =>
      simp only
      obtain ⟨g2, e2, h2, m2⟩ := renameKeys_spec hr ks g h0 (hout.oerase k) hks'
      refine ⟨g2, e2, h2, comb T _ (dflt ctx.K k) (Tbl.Ext.refl T) m2 ?_ ?_⟩
      · intro k'; rw [val_oerase]
      · simp only [val, hg]; rw [renameL_dflt]; exact SetEq.refl _
    | some i =>
      simp only
      have hi : i < T.size := (h0.ent _ (oget_mem hg)).1
      split
      · have hsub : renameL s (T.mem i) ⊆ ctx.origins := renameL_sub hr (g.mem_sub i)
        obtain ⟨g1, e1, i1, m1⟩ := Tbl.intern_none_spec g hsub
        generalize T.intern ctx.origins (renameL s (T.mem i)) none = r at g1 e1 i1 m1
        obtain ⟨g2, e2, h2, m2⟩ := renameKeys_spec hr ks g1 (h0.ext e1)
          ((hout.ext e1).oset i1 hk) hks'
        refine ⟨g2, e1.trans e2, h2, comb r.2 _ (r.2.mem r.1) e1 m2 ?_ ?_⟩
        · intro k'; rw [val_oset, val_ext hout e1]
        · simp only [val, hg]; exact m1
      · rename_i hnm
        obtain ⟨g2, e2, h2, m2⟩ := renameKeys_spec hr ks g h0 (hout.oset hi hk) hks'
        refine ⟨g2, e2, h2, comb T _ (T.mem i) (Tbl.Ext.refl T) m2 ?_ ?_⟩
        · intro k'; rw [val_oset]
        · simp only [val, hg]; rw [renameL_of_not_mem hnm]; exact SetEq.refl _

/-- The O retire represents the concept `retire`. -/
theorem retireO_rel {ctx : Ctx} (cc : CtxClosed ctx) (hr : RecOK ctx) {T : Tbl}
    (g : T.Good ctx.origins) {st : OState} {X : AState} (hR : Rel ctx T st X) (s : Site) :
    (retireO ctx s T st).1.Good ctx.origins ∧ T.Ext (retireO ctx s T st).1 ∧
      Rel ctx (retireO ctx s T st).1 (retireO ctx s T st).2 (Sound.Recency.retire s X) := by
  unfold retireO
  split
  · rename_i hn
    have ho : rOld s ∈ ctx.origins := (hr s).mp hn
    obtain ⟨g1, e1, h1, m1⟩ := mergeCells_spec cc hn ho ctx.cells g hR.ent hR.ent
      (fun c h => h)
    simp only
    generalize mergeCells ctx s st ctx.cells T st = m at g1 e1 h1 m1
    obtain ⟨g2, e2, h2, m2⟩ := renameKeys_spec hr (m.2.map Prod.fst) g1 h1 (EntOK.nil ctx _)
      (fun k hk => inU_of_key h1 hk)
    refine ⟨g2, e1.trans e2, rel_of_vals h2 (supp_retire hr hR.supp s) _ m2 ?_⟩
    intro k hk
    -- the value after both steps is the renamed value after step 1
    have hstep : SetEq (if k ∈ m.2.map Prod.fst then renameL s (val ctx.K m.1 m.2 k)
        else val ctx.K m.1 [] k) (renameL s (val ctx.K m.1 m.2 k)) := by
      split
      · exact SetEq.refl _
      · rename_i hn'
        rw [val_nil]
        simp only [val, oget_none_of_not_mem hn']
        rw [renameL_dflt]; exact SetEq.refl _
    refine hstep.trans ((renameL_congr (m1 k)).trans ?_)
    rw [cval_retire]
    cases k with
    | v x =>
      have h1' : Key.v x ∉ ctx.cells.map (Key.h (rOld s)) := by simp
      have h2' : Key.v x ∉ ctx.cells.map (Key.h (rNew s)) := by simp
      rw [ite_eq_right h1', ite_eq_right h2']
      exact renameL_congr (hR.agree (.v x) hk)
    | h o c =>
      simp only
      by_cases hon : o = rNew s
      · subst hon
        have h1' : Key.h (rNew s) c ∉ ctx.cells.map (Key.h (rOld s)) := by
          simp only [List.mem_map, Key.h.injEq]
          rintro ⟨_, _, he, _⟩; exact rNew_ne_rOld s he.symm
        have h2' : Key.h (rNew s) c ∈ ctx.cells.map (Key.h (rNew s)) :=
          List.mem_map.mpr ⟨c, hk.2, rfl⟩
        rw [ite_eq_right h1', ite_eq_left h2', ite_eq_left rfl]
        exact SetEq.refl _
      · rw [ite_eq_right hon]
        by_cases hoo : o = rOld s
        · subst hoo
          have h1' : Key.h (rOld s) c ∈ ctx.cells.map (Key.h (rOld s)) :=
            List.mem_map.mpr ⟨c, hk.2, rfl⟩
          rw [ite_eq_left h1', ite_eq_left rfl]
          simp only [mergeVal]
          exact renameL_congr (SetEq.uni (hR.agree (.h (rNew s) c) ⟨hn, hk.2⟩)
            (hR.agree (.h (rOld s) c) hk))
        · have h1' : Key.h o c ∉ ctx.cells.map (Key.h (rOld s)) := by
            simp only [List.mem_map, Key.h.injEq]; rintro ⟨_, _, he, _⟩; exact hoo he.symm
          have h2' : Key.h o c ∉ ctx.cells.map (Key.h (rNew s)) := by
            simp only [List.mem_map, Key.h.injEq]; rintro ⟨_, _, he, _⟩; exact hon he.symm
          rw [ite_eq_right h1', ite_eq_right h2', ite_eq_right hoo]
          exact renameL_congr (hR.agree (.h o c) hk)
  · rename_i hn
    refine ⟨g, Tbl.Ext.refl T, rel_of_vals hR.ent (supp_retire hr hR.supp s) _
      (fun k => SetEq.refl (val ctx.K T st k)) ?_⟩
    intro k hk
    have ho : rOld s ∉ ctx.origins := fun h => hn ((hr s).mpr h)
    have hnot : ∀ l : List Origin, l ⊆ ctx.origins → renameL s l = l :=
      fun l hl => renameL_of_not_mem (fun h => hn (hl h))
    rw [cval_retire]
    cases k with
    | v x =>
      simp only
      rw [hnot (X.env x) (hR.supp (.v x) hk)]; exact hR.agree (.v x) hk
    | h o c =>
      simp only
      have hon : o ≠ rNew s := fun he => hn (he ▸ hk.1)
      have hoo : o ≠ rOld s := fun he => ho (he ▸ hk.1)
      rw [ite_eq_right hon, ite_eq_right hoo, hnot (X.heap o c) (hR.supp (.h o c) hk)]
      exact hR.agree (.h o c) hk

/-! ## The O recency analysis -/

/-- The recency store of O: the same as `storeO`, with the recency uniqueness test. -/
def storeRO (ctx : Ctx) (T : Tbl) (st : OState) (x : Var) (c : ACell) (y : Var) : Tbl × OState :=
  match single? (val ctx.K T st (.v x)) with
  | some o =>
    if uniqueR ctx.once ctx.entryUnique o then
      let yi := getId ctx T st (.v y)
      (yi.2, oset st (.h o c) yi.1)
    else weakO ctx T st x c y
  | none => weakO ctx T st x c y

/-- The O transfer of one statement, with recency. -/
def ostepR (ctx : Ctx) : Stmt → Tbl → OState → Tbl × OState
  | .new x s, T, st =>
    let r := retireO ctx s T st
    setKey ctx r.1 r.2 (.v x) [rNew s]
  | .unknown x s, T, st =>
    let r := retireO ctx s T st
    setKey ctx r.1 r.2 (.v x) [.sym (.fresh s) []]
  | .call ret s args, T, st =>
    let a := havocO ctx T st args s
    let r := retireO ctx s a.1 a.2
    match ret with
    | none => r
    | some x => setKey ctx r.1 r.2 (.v x) [.sym (.fresh s) []]
  | .store x f y, T, st => storeRO ctx T st x (.fld f) y
  | st, T, s => ostep ctx st T s

/-- The O analysis with recency. -/
def analyzeRO (ctx : Ctx) : Prog → Tbl → OState → Tbl × OState
  | .skip, T, st => (T, st)
  | .stmt s, T, st => ostepR ctx s T st
  | .seq p q, T, st =>
    let r := analyzeRO ctx p T st
    analyzeRO ctx q r.1 r.2
  | .choice p q, T, st =>
    let r1 := analyzeRO ctx p T st
    let r2 := analyzeRO ctx q r1.1 st
    let j := joinO ctx r2.1 r1.2 r2.2
    (j.1, j.2.1)
  | .loop p, T, st => loopO ctx (analyzeRO ctx p) ctx.fuel T st

/-- The simulation of the recency store. -/
theorem storeRO_rel {ctx : Ctx} (cc : CtxClosed ctx) {T : Tbl} (g : T.Good ctx.origins)
    {st : OState} {X : AState} (hR : Rel ctx T st X) {x y : Var} (hx : x ∈ ctx.vars)
    (hy : y ∈ ctx.vars) {c : ACell} (hc : c ∈ ctx.cells) :
    (storeRO ctx T st x c y).1.Good ctx.origins ∧ T.Ext (storeRO ctx T st x c y).1 ∧
      Rel ctx (storeRO ctx T st x c y).1 (storeRO ctx T st x c y).2
        (storeR ctx X x c (X.env y)) := by
  have hsg : single? (val ctx.K T st (.v x)) = single? (X.env x) :=
    single?_congr (hR.agree (.v x) hx)
  unfold storeRO storeR
  rw [← hsg]
  cases hso : single? (val ctx.K T st (.v x)) with
  | none => exact weakO_rel cc g hR hx hy hc
  | some o =>
    simp only
    split
    · have ho : o ∈ ctx.origins := val_sub cc g st (k := .v x) hx (single?_spec hso).1
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

/-- Each O recency step represents the concept recency step. -/
theorem ostepR_rel {ctx : Ctx} (cc : CtxClosed ctx) (hr : RecOK ctx) {T : Tbl}
    (g : T.Good ctx.origins) {st : OState} {X : AState} (hR : Rel ctx T st X) {s : Stmt}
    (ok : StmtOKR ctx s) :
    (ostepR ctx s T st).1.Good ctx.origins ∧ T.Ext (ostepR ctx s T st).1 ∧
      Rel ctx (ostepR ctx s T st).1 (ostepR ctx s T st).2 (astepR ctx s X) := by
  cases s with
  | new x s =>
    obtain ⟨g1, e1, r1⟩ := retireO_rel cc hr g hR s
    simp only [ostepR, astepR]
    generalize retireO ctx s T st = r at g1 e1 r1
    obtain ⟨g2, e2, r2⟩ := setKey_rel g1 r1 (ok.vars x (by simp [Stmt.vars]))
      (S := [rNew s]) (by intro a ha; simp at ha; subst ha; exact ok.new s rfl)
    exact ⟨g2, e1.trans e2, r2⟩
  | unknown x s =>
    obtain ⟨g1, e1, r1⟩ := retireO_rel cc hr g hR s
    simp only [ostepR, astepR]
    generalize retireO ctx s T st = r at g1 e1 r1
    obtain ⟨g2, e2, r2⟩ := setKey_rel g1 r1 (ok.vars x (by simp [Stmt.vars]))
      (S := [.sym (.fresh s) []]) (by intro a ha; simp at ha; subst ha; exact ok.fresh s rfl)
    exact ⟨g2, e1.trans e2, r2⟩
  | call ret s args =>
    -- the havoc part of `callO_rel` with no result variable
    have okc : StmtOK ctx (.call none s args) :=
      ⟨fun x hx => ok.vars x (by simp [Stmt.vars] at hx ⊢; exact Or.inr hx),
        ok.fields, (fun _ h => by cases h), ok.fresh, ok.call⟩
    obtain ⟨g1, e1, r1⟩ := callO_rel cc g hR okc
    have hcall : callO ctx T st none s args = havocO ctx T st args s := rfl
    rw [hcall] at g1 e1 r1
    obtain ⟨g2, e2, r2⟩ := retireO_rel cc hr g1 r1 s
    simp only [ostepR, astepR]
    generalize havocO ctx T st args s = a at g1 e1 r1 g2 e2 r2
    generalize retireO ctx s a.1 a.2 = r at g2 e2 r2
    have r1' : Rel ctx r.1 r.2 (Sound.Recency.retire s (X.havoc ctx args s)) := r2
    cases ret with
    | none => exact ⟨g2, e1.trans e2, r1'⟩
    | some x =>
      obtain ⟨g3, e3, r3⟩ := setKey_rel g2 r1' (ok.vars x (by simp [Stmt.vars]))
        (S := [.sym (.fresh s) []]) (by intro a ha; simp at ha; subst ha; exact ok.fresh s rfl)
      exact ⟨g3, e1.trans (e2.trans e3), r3⟩
  | store x f y =>
    exact storeRO_rel cc g hR (ok.vars x (by simp [Stmt.vars])) (ok.vars y (by simp [Stmt.vars]))
      (ok.fields f (by simp [Stmt.fields]))
  | null x => exact ostep_rel cc g hR (ok.toOK rfl)
  | copy x y => exact ostep_rel cc g hR (ok.toOK rfl)
  | load x y f => exact ostep_rel cc g hR (ok.toOK rfl)
  | aload x y => exact ostep_rel cc g hR (ok.toOK rfl)
  | astore x y => exact ostep_rel cc g hR (ok.toOK rfl)

/-- The O recency analysis represents the concept recency analysis on the universe. -/
theorem analyzeRO_rel {ctx : Ctx} (cc : CtxClosed ctx) (hr : RecOK ctx) :
    ∀ (q : Prog) (T : Tbl) (st : OState) (X : AState), ProgOKR ctx q → T.Good ctx.origins →
      Rel ctx T st X →
      (analyzeRO ctx q T st).1.Good ctx.origins ∧ T.Ext (analyzeRO ctx q T st).1 ∧
      Rel ctx (analyzeRO ctx q T st).1 (analyzeRO ctx q T st).2 (analyzeR ctx q X)
  | .skip, T, _, _, _, g, hR => ⟨g, Tbl.Ext.refl T, hR⟩
  | .stmt s, _, _, _, ok, g, hR => ostepR_rel cc hr g hR (ok s (by simp [Prog.stmts]))
  | .seq p q, T, st, X, ok, g, hR => by
    obtain ⟨g1, e1, r1⟩ := analyzeRO_rel cc hr p T st X
      (fun st hs => ok st (List.mem_append_left _ hs)) g hR
    simp only [analyzeRO, analyzeR]
    generalize analyzeRO ctx p T st = r at g1 e1 r1
    obtain ⟨g2, e2, r2⟩ := analyzeRO_rel cc hr q r.1 r.2 _
      (fun st hs => ok st (List.mem_append_right _ hs)) g1 r1
    exact ⟨g2, e1.trans e2, r2⟩
  | .choice p q, T, st, X, ok, g, hR => by
    obtain ⟨g1, e1, r1⟩ := analyzeRO_rel cc hr p T st X
      (fun st hs => ok st (List.mem_append_left _ hs)) g hR
    simp only [analyzeRO, analyzeR]
    generalize analyzeRO ctx p T st = a at g1 e1 r1
    obtain ⟨g2, e2, r2⟩ := analyzeRO_rel cc hr q a.1 st X
      (fun st hs => ok st (List.mem_append_right _ hs)) g1 (hR.ext e1)
    generalize analyzeRO ctx q a.1 st = b at g2 e2 r2
    obtain ⟨g3, e3, r3⟩ := joinO_rel cc g2 (r1.ext e2) r2
    exact ⟨g3, e1.trans (e2.trans e3), r3⟩
  | .loop p, T, st, X, ok, g, hR => by
    simp only [analyzeRO, analyzeR]
    exact loopO_rel cc (fun T' st' Y g' hR' => analyzeRO_rel cc hr p T' st' Y ok g' hR')
      ctx.fuel T st X g hR

/-! ## Whole programs -/

/-- The recency context of a program is closed under default content. -/
theorem ctxClosed_R (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    CtxClosed (ctxR eu K fr p qf) := by
  constructor
  · intro o ho c hc
    simp only [ctxR] at ho hc ⊢
    rcases mem_originsR.mp ho with ⟨b, hb, ⟨q, hq, rfl⟩ | rfl⟩ | ⟨s, hs, h⟩ | ⟨s, hs, rfl⟩
    · intro o' ho'
      simp only [adefault, List.mem_singleton] at ho'
      subst ho'
      apply mem_originsR.mpr
      refine Or.inl ⟨b, hb, ?_⟩
      unfold symOrDeep
      split
      · rename_i hl
        obtain ⟨_, hq2⟩ := mem_pathsUpTo.mp hq
        refine Or.inl ⟨q ++ [c], mem_pathsUpTo.mpr ⟨hl, ?_⟩, rfl⟩
        intro d hd
        cases List.mem_append.mp hd with
        | inl h => exact hq2 d h
        | inr h => simp at h; subst h; exact hc
      · exact Or.inr rfl
    · intro o' ho'
      simp only [adefault, List.mem_singleton] at ho'
      subst ho'
      exact mem_originsR.mpr (Or.inl ⟨b, hb, Or.inr rfl⟩)
    · rcases h with rfl | rfl <;> intro o' ho' <;> simp [adefault, rNew, rOld] at ho'
    · intro o' ho'
      simp only [adefault, List.mem_singleton] at ho'
      subst ho'
      exact mem_originsR.mpr (Or.inr (Or.inr ⟨s, hs, rfl⟩))
  · simp [ctxR, cellsOf]

/-- Two even numbers are equal if their halves are. -/
theorem half_eq : ∀ a b : Nat, 2 * a = 2 * b → a = b := fun a b h => by omega

/-- An even number is not odd. -/
theorem even_ne_odd : ∀ a b : Nat, 2 * a = 2 * b + 1 → False := fun a b h => by omega

/-- The recency universe has both recency origins of a site or neither. -/
theorem recOK_R (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    RecOK (ctxR eu K fr p qf) := by
  intro s
  simp only [ctxR]
  constructor
  · intro h
    obtain ⟨t, ht, he⟩ := alloc_mem_originsR h
    rcases he with he | he
    · have : s = t := half_eq s t (Origin.alloc.inj he)
      subst this
      exact mem_originsR.mpr (Or.inr (Or.inl ⟨s, ht, Or.inr rfl⟩))
    · exact (even_ne_odd s t (Origin.alloc.inj he)).elim
  · intro h
    obtain ⟨t, ht, he⟩ := alloc_mem_originsR h
    rcases he with he | he
    · exact (even_ne_odd t s (Origin.alloc.inj he).symm).elim
    · have : s = t := half_eq s t (Nat.succ.inj (Origin.alloc.inj he))
      subst this
      exact mem_originsR.mpr (Or.inr (Or.inl ⟨s, ht, Or.inl rfl⟩))

/-- The recency context covers every statement of the program. -/
theorem progOKR_R (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    ProgOKR (ctxR eu K fr p qf) p := by
  intro st hst
  have o := progOK_ofProg K fr p qf st hst
  refine ⟨o.vars, o.fields, ?_, ?_, ?_⟩
  · intro s hs
    exact mem_originsR.mpr (Or.inr (Or.inl ⟨s, List.mem_filterMap.mpr ⟨st, hst, hs⟩, Or.inl rfl⟩))
  · intro s hs
    apply mem_originsR.mpr
    refine Or.inl ⟨.fresh s, ?_, Or.inl ⟨[], mem_pathsUpTo.mpr ⟨by simp, by simp⟩, rfl⟩⟩
    exact List.mem_append_right _ (List.mem_map.mpr ⟨s, List.mem_filterMap.mpr ⟨st, hst, hs⟩, rfl⟩)
  · intro s hs
    exact mem_originsR.mpr (Or.inr (Or.inr ⟨s, List.mem_filterMap.mpr ⟨st, hst, hs⟩, rfl⟩))

/-- The entry state has support in the recency context. -/
theorem supp_ainitR (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    Supp (ctxR eu K fr p qf) (ainit K fr) := by
  intro k hk
  cases k with
  | v x =>
    simp only [cval, ainit]
    cases hr : fr.root? x with
    | none => intro _ h; cases h
    | some r =>
      intro o ho
      simp only [List.mem_singleton] at ho
      subst ho
      simp only [ctxR]
      apply mem_originsR.mpr
      refine Or.inl ⟨.root r, ?_, Or.inl ⟨[], mem_pathsUpTo.mpr ⟨by simp, by simp⟩, rfl⟩⟩
      exact List.mem_append_left _
        (List.mem_map.mpr ⟨r, lookup_mem_roots fr.binds x r hr, rfl⟩)
  | h o c => exact (ctxClosed_R eu K fr p qf).dflt o hk.1 c hk.2

/-- The final O recency state of program `p`. -/
def analyzeProgRO (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    Tbl × OState :=
  let ctx := ctxR eu K fr p qf
  let i := initO ctx fr
  analyzeRO ctx p i.1 i.2

/-- O may-alias with recency at the end of program `p`. -/
def mayProgRO (eu : Bool) (K : Nat) (fr : Frame) (p : Prog)
    (x : Var) (px : List ACell) (y : Var) (py : List ACell) : Bool :=
  let r := analyzeProgRO eu K fr p (afields px ++ afields py)
  omay (ctxR eu K fr p (afields px ++ afields py)) r.1 r.2 x px y py

/-- For each policy and each program, the final O recency state represents the final concept
recency state. -/
theorem analyzeProgRO_rel (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    (analyzeProgRO eu K fr p qf).1.Good (ctxR eu K fr p qf).origins ∧
      Rel (ctxR eu K fr p qf) (analyzeProgRO eu K fr p qf).1 (analyzeProgRO eu K fr p qf).2
        (analyzeR (ctxR eu K fr p qf) p (ainit K fr)) := by
  have cc := ctxClosed_R eu K fr p qf
  have hfv : ∀ x ∈ fr.vars, x ∈ (ctxR eu K fr p qf).vars := by
    intro x hx
    simp only [ctxR]
    rw [List.mem_eraseDups]
    exact List.mem_append_right _ hx
  obtain ⟨g0, r0⟩ := initO_rel (ctx := ctxR eu K fr p qf) fr (supp_ainitR eu K fr p qf) hfv
  obtain ⟨g1, _, r1⟩ := analyzeRO_rel cc (recOK_R eu K fr p qf) p _ _ _
    (progOKR_R eu K fr p qf) g0 r0
  exact ⟨g1, r1⟩

/-- For both strong-update policies, O with recency and the recency concept give the same
may-alias answer. -/
theorem mayProgRO_eq (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (x : Var) (px : List ACell)
    (y : Var) (py : List ACell) (hx : x ∈ p.vars ++ fr.vars) (hy : y ∈ p.vars ++ fr.vars) :
    mayProgRO eu K fr p x px y py = mayProgR eu K fr p x px y py := by
  have cc := ctxClosed_R eu K fr p (afields px ++ afields py)
  obtain ⟨g, hR⟩ := analyzeProgRO_rel eu K fr p (afields px ++ afields py)
  unfold mayProgRO mayProgR
  simp only
  have hv : ∀ z, z ∈ p.vars ++ fr.vars →
      z ∈ (ctxR eu K fr p (afields px ++ afields py)).vars := by
    intro z hz; simp only [ctxR]; rw [List.mem_eraseDups]; exact hz
  exact omay_eq cc g hR (hv x hx) (hv y hy)
    (query_cells K fr p _ px (fun f hf => List.mem_append_left _ hf))
    (query_cells K fr p _ py (fun f hf => List.mem_append_right _ hf))

/-! ## The cost of a retire -/

/-- A table extension keeps the holder test of a valid map. -/
theorem holderB_ext {ctx : Ctx} {s : Site} {T T' : Tbl} {st : OState} (h : EntOK ctx T st)
    (e : T.Ext T') (k : Key) : holderB s T' st k = holderB s T st k := by
  unfold holderB
  cases hg : oget st k with
  | none => rfl
  | some i => simp only; rw [e.mem_eq (h.ent _ (oget_mem hg)).1]

/-- Step 2 costs at most `|U| + 1` for each listed key whose node holds `rNew s`. The other keys
cost nothing in the model (a reverse index gives the holders directly). -/
theorem renameKeys_work {ctx : Ctx} (hr : RecOK ctx) {s : Site} {st : OState} :
    ∀ (ks : List Key) {T : Tbl} {out : OState}, T.Good ctx.origins → EntOK ctx T st →
      (renameKeys ctx s st ks T out).1.work ≤
        T.work + (ks.filter (holderB s T st)).length * (ctx.origins.length + 1)
  | [], T, _, _, _ => by simp [renameKeys]
  | k :: ks, T, out, g, h0 => by
    simp only [renameKeys]
    cases hg : oget st k with
    | none =>
      simp only
      have ih := renameKeys_work hr (s := s) ks (out := oerase out k) g h0
      have : holderB s T st k = false := by simp [holderB, hg]
      rw [List.filter_cons, this]
      simpa using ih
    | some i =>
      simp only
      split
      · rename_i hm
        have hsub : renameL s (T.mem i) ⊆ ctx.origins := renameL_sub hr (g.mem_sub i)
        obtain ⟨g1, e1, _, _⟩ := Tbl.intern_none_spec g hsub
        have w1 := Tbl.intern_work ctx.origins T (renameL s (T.mem i)) none
        have l1 := g.mem_length i
        rw [length_renameL] at w1
        generalize T.intern ctx.origins (renameL s (T.mem i)) none = r at g1 e1 w1
        have ih := renameKeys_work hr (s := s) ks (out := oset out k r.1) g1 (h0.ext e1)
        have hf : ks.filter (holderB s r.2 st) = ks.filter (holderB s T st) :=
          List.filter_congr (fun k' _ => holderB_ext h0 e1 k')
        rw [hf] at ih
        have : holderB s T st k = true := by simp [holderB, hg, hm]
        rw [List.filter_cons, this]
        simp only [ite_true, List.length_cons, Nat.succ_mul]
        omega
      · rename_i hnm
        have ih := renameKeys_work hr (s := s) ks (out := oset out k i) g h0
        have : holderB s T st k = false := by simp [holderB, hg, hnm]
        rw [List.filter_cons, this]
        simpa using ih

/-- Step 1 costs at most `6 + 4 |U|` for each cell. -/
theorem mergeCells_work {ctx : Ctx} (cc : CtxClosed ctx) {s : Site}
    (hn : rNew s ∈ ctx.origins) (ho : rOld s ∈ ctx.origins) {st0 : OState} :
    ∀ (cs : List ACell) {T : Tbl} {out : OState}, T.Good ctx.origins → EntOK ctx T st0 →
      (∀ c ∈ cs, c ∈ ctx.cells) →
      (mergeCells ctx s st0 cs T out).1.work ≤ T.work + cs.length * (6 + 4 * ctx.origins.length)
  | [], T, _, _, _, _ => by simp [mergeCells]
  | c :: cs, T, out, g, h0, hcs => by
    have hc : c ∈ ctx.cells := hcs c List.mem_cons_self
    obtain ⟨ga, ea, ia, _⟩ := getId_spec cc g h0 (k := .h (rNew s) c) ⟨hn, hc⟩
    have wa := getId_work ctx T st0 (.h (rNew s) c)
    simp only [mergeCells]
    generalize getId ctx T st0 (.h (rNew s) c) = a at ga ea ia wa
    obtain ⟨gb, eb, ib, _⟩ := getId_spec cc ga (h0.ext ea) (k := .h (rOld s) c) ⟨ho, hc⟩
    have wb := getId_work ctx a.2 st0 (.h (rOld s) c)
    generalize getId ctx a.2 st0 (.h (rOld s) c) = b at gb eb ib wb
    have iab : a.1 < b.2.size := Nat.lt_of_lt_of_le ia eb.size_le
    obtain ⟨gu, eu, _, _⟩ := Tbl.union_spec gb iab ib
    have wu := Tbl.union_work ctx.origins b.2 a.1 b.1
    have la := gb.mem_length a.1
    have lb := gb.mem_length b.1
    generalize b.2.union ctx.origins a.1 b.1 = u at gu eu wu
    have ih := mergeCells_work cc hn ho cs
      (out := oerase (oset out (.h (rOld s) c) u.1) (.h (rNew s) c)) gu
      (h0.ext (ea.trans (eb.trans eu))) (fun c' h => hcs c' (List.mem_cons_of_mem _ h))
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- The cost of the O retire: at most `6 + 4 |U|` for each universe cell (step 1), plus `|U| + 1`
for each map key whose node holds `rNew s` after step 1 (step 2). -/
theorem retireO_work {ctx : Ctx} (cc : CtxClosed ctx) (hr : RecOK ctx) {T : Tbl}
    (g : T.Good ctx.origins) {st : OState} (h : EntOK ctx T st) {s : Site}
    (hn : rNew s ∈ ctx.origins) :
    (retireO ctx s T st).1.work ≤
      T.work + ctx.cells.length * (6 + 4 * ctx.origins.length) +
        (((mergeCells ctx s st ctx.cells T st).2.map Prod.fst).filter
          (holderB s (mergeCells ctx s st ctx.cells T st).1
            (mergeCells ctx s st ctx.cells T st).2)).length * (ctx.origins.length + 1) := by
  have ho : rOld s ∈ ctx.origins := (hr s).mp hn
  have w1 := mergeCells_work cc hn ho ctx.cells (out := st) g h (fun c h => h)
  obtain ⟨g1, _, h1, _⟩ := mergeCells_spec cc hn ho ctx.cells g h h (fun c h => h)
  unfold retireO
  rw [ite_eq_left hn]
  simp only
  generalize mergeCells ctx s st ctx.cells T st = m at w1 g1 h1
  have w2 := renameKeys_work hr (s := s) (m.2.map Prod.fst) (out := []) g1 h1
  omega

/-- If the universe has no `rNew s`, the O retire does nothing. -/
theorem retireO_skip (ctx : Ctx) (s : Site) (T : Tbl) (st : OState)
    (hn : rNew s ∉ ctx.origins) : retireO ctx s T st = (T, st) := by
  unfold retireO; rw [ite_eq_right hn]

/-! ## Examples -/

namespace RExamples

open DirectedAlias.Examples

/-- O with recency: `b.f` does not alias `x` after the loop (strong stores on `rNew 7`). -/
theorem o_loop_bf_x : mayProgRO true 1 fr pLoop vb [.fld ff] vx [] = false := by decide +kernel

/-- O with recency: `b.f` may alias `y` after the loop. -/
theorem o_loop_bf_y : mayProgRO true 1 fr pLoop vb [.fld ff] vy [] = true := by decide +kernel

/-- O with recency and the weak policy for symbolic origins: the loop answer is also exact. -/
theorem o_loop_bf_x_weak : mayProgRO false 1 fr pLoop vb [.fld ff] vx [] = false := by
  decide +kernel

/-- O with recency keeps the answers of the field example. -/
theorem o_field : mayProgRO true 2 fr pField vx [.fld ff] vz [] = true ∧
    mayProgRO true 2 fr pField vy [.fld ff] vz [] = true ∧
    mayProgRO true 2 fr pField vx [] vy [] = false := by decide +kernel

end RExamples

end DirectedAlias.Opt.Rec

import DirectedAlias.Impl.EngineCall

/-!
# Engine runs: the sandwich invariant and equal answers on loop-free programs

The bridge (`EngineCall.lean`) compares one model step on the COMPLETED denotation with one
engine step. Along a run the model state is not exactly a completion. This file uses the
SANDWICH invariant `Sand E M`: the model state `M` is between the denotation of the engine state
and its completion, `den E ⊑ M ⊑ comp (den E)` in the order `Le` (set-equal env outside the
reserved keys, set-equal heap, included reserved sets). Results:

* `uniqueBO_between`, `sand_decide`: in a sandwich, the strong-update answers of `M` are the
  answers of the engine state.
* `call_lower`: with an adequate budget, the engine call is below the model call.
* `sand_step`: each statement keeps the sandwich (the engine uses an adequate budget at each call,
  `astepEA`), and keeps the universe keys of the engine heap (`HK.astepEA`); `sand_join`: the
  join keeps the sandwich.
* `sand_analyze`: on each LOOP-FREE program the engine analysis and the model analysis keep the
  sandwich. `mayProgVS_engine`: on each loop-free program the engine gives the may-alias answers
  of design VS for each query of program variables.

For a loop, the iteration counts of the two sides can differ (the model stability test reads the
raw sets); `post_fixpoint` (`EngineCall.lean`) gives the transfer of an engine post-fixpoint.
-/

namespace DirectedAlias.Impl.Engine

open DirectedAlias DirectedAlias.Opt DirectedAlias.Opt.Rec
open DirectedAlias.Sound.Recency DirectedAlias.Sound.HavocRecency DirectedAlias.Sound.CellNamed
open DirectedAlias.Sound.BlockOnly DirectedAlias.Sound.ValueSem

section run

variable {cb : CtxB}

/-! ## Model-side monotonicity for `Le` -/

/-- The join keeps `Le`. -/
theorem Le.join {X1 X2 Y1 Y2 : AState} (h1 : Le cb X1 Y1) (h2 : Le cb X2 Y2) :
    Le cb (DirectedAlias.join X1 X2) (DirectedAlias.join Y1 Y2) := by
  refine ⟨fun x e1 e2 => SetEq.uni (h1.env x e1 e2) (h2.env x e1 e2),
    fun o c => SetEq.uni (h1.heap o c) (h2.heap o c), fun a ha => ?_, fun a ha => ?_⟩
  · rcases mem_uni.mp ha with h | h
    · exact mem_uni.mpr (Or.inl (h1.te a h))
    · exact mem_uni.mpr (Or.inr (h2.te a h))
  · rcases mem_uni.mp ha with h | h
    · exact mem_uni.mpr (Or.inl (h1.tv a h))
    · exact mem_uni.mpr (Or.inr (h2.tv a h))

/-- `setCell` keeps `Le`. -/
theorem Le.setCell {X Y : AState} (h : Le cb X Y) (o : Origin) (c : ACell) {S S' : List Origin}
    (hS : SetEq S S') : Le cb (X.setCell o c S) (Y.setCell o c S') := by
  refine ⟨h.env, fun o' c' => ?_, h.te, h.tv⟩
  show SetEq (fupd2 X.heap o c S o' c') (fupd2 Y.heap o c S' o' c')
  by_cases e : o' = o ∧ c' = c
  · obtain ⟨rfl, rfl⟩ := e; rw [fupd2_same, fupd2_same]; exact hS
  · rw [fupd2_ne _ _ e, fupd2_ne _ _ e]; exact h.heap o' c'

/-- `weakStore` keeps `Le`. -/
theorem Le.weakStore {X Y : AState} (h : Le cb X Y) {os os' : List Origin} (ho : SetEq os os')
    (c : ACell) {S S' : List Origin} (hS : SetEq S S') :
    Le cb (X.weakStore os c S) (Y.weakStore os' c S') := by
  refine ⟨h.env, fun o' c' => ?_, h.te, h.tv⟩
  show SetEq (if c' = c ∧ o' ∈ os then uni S (X.heap o' c') else X.heap o' c')
    (if c' = c ∧ o' ∈ os' then uni S' (Y.heap o' c') else Y.heap o' c')
  by_cases e : c' = c ∧ o' ∈ os
  · rw [ite_eq_left e, ite_eq_left ⟨e.1, (ho o').mp e.2⟩]
    exact SetEq.uni hS (h.heap o' c')
  · have e' : ¬ (c' = c ∧ o' ∈ os') := fun h' => e ⟨h'.1, (ho o').mpr h'.2⟩
    rw [ite_eq_right e, ite_eq_right e']
    exact h.heap o' c'

/-- The read gives set-equal results on `Le` states. -/
theorem Le.aread {X Y : AState} (h : Le cb X Y) {S S' : List Origin} (hS : SetEq S S')
    (c : ACell) : SetEq (DirectedAlias.aread X S c) (DirectedAlias.aread Y S' c) := by
  intro a
  rw [mem_aread, mem_aread]
  constructor
  · rintro ⟨o, ho, ha⟩; exact ⟨o, (hS o).mp ho, (h.heap o c a).mp ha⟩
  · rintro ⟨o, ho, ha⟩; exact ⟨o, (hS o).mpr ho, (h.heap o c a).mpr ha⟩

/-- The store of design BO keeps `Le` if the two states give the same strong-update answers. -/
theorem Le.storeBO {X Y : AState} (h : Le cb X Y)
    (hu : ∀ o, uniqueBO cb.cn.ctx.once cb.cn.ctx.entryUnique (X.env cb.cn.xe) (X.env cb.xv) o =
      uniqueBO cb.cn.ctx.once cb.cn.ctx.entryUnique (Y.env cb.cn.xe) (Y.env cb.xv) o)
    {x : Var} (h1 : x ≠ cb.cn.xe) (h2 : x ≠ cb.xv) (c : ACell) {S S' : List Origin}
    (hS : SetEq S S') : Le cb (storeBO cb X x c S) (storeBO cb Y x c S') := by
  have hx := h.env x h1 h2
  unfold DirectedAlias.Sound.BlockOnly.storeBO
  rw [single?_congr hx]
  cases single? (Y.env x) with
  | none => exact h.weakStore hx c hS
  | some o =>
    simp only
    rw [hu o]
    split
    · exact h.setCell o c hS
    · exact h.weakStore hx c hS

/-- `setSets` keeps `Le`. -/
theorem Le.setSets (hx : cb.xv ≠ cb.cn.xe) {X Y : AState} (h : Le cb X Y) {R R' V V' : List Origin}
    (hR : ∀ a ∈ R, a ∈ R') (hV : ∀ a ∈ V, a ∈ V') :
    Le cb (DirectedAlias.Sound.ValueSem.setSets cb X R V)
      (DirectedAlias.Sound.ValueSem.setSets cb Y R' V') := by
  have sx : ∀ (Z : AState) (R V : List Origin),
      (DirectedAlias.Sound.ValueSem.setSets cb Z R V).env cb.cn.xe = uni R (Z.env cb.cn.xe) := by
    intro Z R V
    show fupd (fupd Z.env _ _) cb.xv _ cb.cn.xe = _
    rw [fupd_ne _ _ (fun e => hx e.symm), fupd_same]
  have sv : ∀ (Z : AState) (R V : List Origin),
      (DirectedAlias.Sound.ValueSem.setSets cb Z R V).env cb.xv = uni V (Z.env cb.xv) := by
    intro Z R V
    show fupd (fupd Z.env _ _) cb.xv _ cb.xv = _
    rw [fupd_same]
  have sn : ∀ (Z : AState) (R V : List Origin) (x : Var), x ≠ cb.cn.xe → x ≠ cb.xv →
      (DirectedAlias.Sound.ValueSem.setSets cb Z R V).env x = Z.env x := by
    intro Z R V x e1 e2
    show fupd (fupd Z.env _ _) cb.xv _ x = _
    rw [fupd_ne _ _ e2, fupd_ne _ _ e1]
  refine ⟨fun x e1 e2 => ?_, h.heap, ?_, ?_⟩
  · rw [sn _ _ _ x e1 e2, sn _ _ _ x e1 e2]; exact h.env x e1 e2
  · rw [sx, sx]
    intro a ha
    rcases mem_uni.mp ha with h' | h'
    · exact mem_uni.mpr (Or.inl (hR a h'))
    · exact mem_uni.mpr (Or.inr (h.te a h'))
  · rw [sv, sv]
    intro a ha
    rcases mem_uni.mp ha with h' | h'
    · exact mem_uni.mpr (Or.inl (hV a h'))
    · exact mem_uni.mpr (Or.inr (h.tv a h'))

/-- A union over a list gives set-equal results for pointwise set-equal functions. -/
theorem uniMap_setEq {α : Type} {f g : α → List Origin} {l : List α}
    (h : ∀ a ∈ l, SetEq (f a) (g a)) : SetEq (uniMap f l) (uniMap g l) := by
  intro v
  rw [mem_uniMap, mem_uniMap]
  constructor
  · rintro ⟨a, ha, hv⟩; exact ⟨a, ha, (h a ha v).mp hv⟩
  · rintro ⟨a, ha, hv⟩; exact ⟨a, ha, (h a ha v).mpr hv⟩

/-- The passive call keeps `Le`, for arguments that are not reserved. -/
theorem Le.callVS (hx : cb.xv ≠ cb.cn.xe) {X Y : AState} (h : Le cb X Y) {args : List Var}
    (hargs : ∀ a ∈ args, a ≠ cb.cn.xe ∧ a ≠ cb.xv) :
    Le cb (DirectedAlias.Sound.ValueSem.callVS cb X args)
      (DirectedAlias.Sound.ValueSem.callVS cb Y args) := by
  have hR : SetEq (callRoots cb.cn X args) (callRoots cb.cn Y args) := by
    unfold callRoots
    exact SetEq.uni (uniMap_setEq (fun a ha => h.env a (hargs a ha).1 (hargs a ha).2))
      (SetEq.refl _)
  have hXY : ∀ o ∈ cb.cn.ctx.origins, ∀ c ∈ cb.cn.ctx.cells, SetEq (X.heap o c) (Y.heap o c) :=
    fun o _ c _ => h.heap o c
  unfold DirectedAlias.Sound.ValueSem.callVS
  rcases Opt.CellNamed.closeN_congr hXY (cb.cn.ctx.origins.length + 1) _ _ hR with
    ⟨h1, h2⟩ | ⟨A, B, h1, h2, hAB⟩
  · rw [h1, h2]; exact h.setSets hx (fun _ h => h) (fun _ h => h)
  · rw [h1, h2]
    exact h.setSets hx (fun a ha => (hAB a).mp ha)
      (fun a ha => (Opt.CellNamed.succsN_congr hXY hAB a).mp ha)

/-- MODEL MONOTONICITY: one statement of design VS keeps `Le` if the two states give the same
strong-update answers and the statement does not mention a reserved variable. -/
theorem Le.astepVS (hx : cb.xv ≠ cb.cn.xe) {X Y : AState} (h : Le cb X Y)
    (hu : ∀ o, uniqueBO cb.cn.ctx.once cb.cn.ctx.entryUnique (X.env cb.cn.xe) (X.env cb.xv) o =
      uniqueBO cb.cn.ctx.once cb.cn.ctx.entryUnique (Y.env cb.cn.xe) (Y.env cb.xv) o)
    (i : Nat) : ∀ st : Stmt, (∀ x ∈ st.vars, x ≠ cb.cn.xe ∧ x ≠ cb.xv) →
      Le cb (DirectedAlias.Sound.ValueSem.astepVS cb i st X)
        (DirectedAlias.Sound.ValueSem.astepVS cb i st Y)
  | .new x s, hv => by
    have e := hv x List.mem_cons_self
    exact (h.retireV _ s).setVar e.1 e.2 (SetEq.refl _)
  | .null x, hv => by
    have e := hv x List.mem_cons_self
    exact h.setVar e.1 e.2 (SetEq.refl _)
  | .copy x y, hv => by
    have e := hv x List.mem_cons_self
    have e' := hv y (List.mem_cons_of_mem _ List.mem_cons_self)
    exact h.setVar e.1 e.2 (h.env y e'.1 e'.2)
  | .load x y f, hv => by
    have e := hv x List.mem_cons_self
    have e' := hv y (List.mem_cons_of_mem _ List.mem_cons_self)
    exact h.setVar e.1 e.2 (h.aread (h.env y e'.1 e'.2) _)
  | .store x f y, hv => by
    have e := hv x List.mem_cons_self
    have e' := hv y (List.mem_cons_of_mem _ List.mem_cons_self)
    exact h.storeBO hu e.1 e.2 _ (h.env y e'.1 e'.2)
  | .aload x y, hv => by
    have e := hv x List.mem_cons_self
    have e' := hv y (List.mem_cons_of_mem _ List.mem_cons_self)
    exact h.setVar e.1 e.2 (h.aread (h.env y e'.1 e'.2) _)
  | .astore x y, hv => by
    have e := hv x List.mem_cons_self
    have e' := hv y (List.mem_cons_of_mem _ List.mem_cons_self)
    exact h.weakStore (h.env x e.1 e.2) _ (h.env y e'.1 e'.2)
  | .unknown x s, hv => by
    have e := hv x List.mem_cons_self
    exact (h.retireV _ s).setVar e.1 e.2 (SetEq.refl _)
  | .call ret s args, hv => by
    have hargs : ∀ a ∈ args, a ≠ cb.cn.xe ∧ a ≠ cb.xv :=
      fun a ha => hv a (List.mem_append_right _ ha)
    have hr : ∀ x, ret = some x → x ≠ cb.cn.xe ∧ x ≠ cb.xv := by
      intro x e; subst e; exact hv x (List.mem_append_left _ List.mem_cons_self)
    exact ((h.callVS hx hargs).retireV _ s).setRet hr _

/-! ## The sandwich -/

/-- THE SANDWICH: the model state is between the denotation of the engine state and its
completion. -/
def Sand (cb : CtxB) (E : EState) (M : AState) : Prop :=
  Le cb (den cb.cn.ctx.K E) M ∧ Le cb M (comp cb (den cb.cn.ctx.K E))

/-- Sets between a pair of sets and its completion give the strong-update answers of the pair. -/
theorem uniqueBO_between {E E' V V' : List Origin} (h1 : ∀ a ∈ E, a ∈ E')
    (h2 : ∀ a ∈ E', a ∈ compE cb E) (h3 : ∀ a ∈ V, a ∈ V') (h4 : ∀ a ∈ V', a ∈ compV cb E V)
    (o : Origin) :
    uniqueBO cb.cn.ctx.once cb.cn.ctx.entryUnique E' V' o =
      uniqueBO cb.cn.ctx.once cb.cn.ctx.entryUnique E V o := by
  have hcn : uniqueCN cb.cn.ctx.once cb.cn.ctx.entryUnique E' o =
      uniqueCN cb.cn.ctx.once cb.cn.ctx.entryUnique E o := by
    cases h : uniqueCN cb.cn.ctx.once cb.cn.ctx.entryUnique E o with
    | false =>
      cases h' : uniqueCN cb.cn.ctx.once cb.cn.ctx.entryUnique E' o with
      | false => rfl
      | true => rw [uniqueCN_anti h1 h'] at h; cases h
    | true =>
      have := (uniqueCN_compE (cb := cb) E o).trans h
      exact uniqueCN_anti h2 this
  unfold uniqueBO
  rw [hcn]
  cases h : uniqueCN cb.cn.ctx.once cb.cn.ctx.entryUnique E o with
  | false => rfl
  | true =>
    simp only [Bool.true_and]
    have hiff : o ∈ V' ↔ o ∈ V := by
      constructor
      · intro ho
        have := h4 o ho
        unfold compV at this
        rcases mem_uni.mp this with h5 | h5
        · have hb := (List.mem_filter.mp h5).2
          unfold blkV at hb; rw [h] at hb; cases hb
        · exact h5
      · exact h3 o
    by_cases hv : o ∈ V
    · rw [decide_eq_true hv, decide_eq_true (hiff.mpr hv)]
    · rw [decide_eq_false hv, decide_eq_false (fun h' => hv (hiff.mp h'))]

/-- In a sandwich, the model state gives the strong-update answers of the engine state. -/
theorem sand_decide (hx : cb.xv ≠ cb.cn.xe) {E : EState} {M : AState} (hS : Sand cb E M)
    (o : Origin) :
    uniqueBO cb.cn.ctx.once cb.cn.ctx.entryUnique (M.env cb.cn.xe) (M.env cb.xv) o =
      uniqueBO cb.cn.ctx.once cb.cn.ctx.entryUnique (getE E cb.cn.xe) (getE E cb.xv) o := by
  have t2 := hS.2.te
  have v2 := hS.2.tv
  rw [comp_xe hx] at t2
  rw [comp_xv] at v2
  exact uniqueBO_between hS.1.te t2 hS.1.tv v2 o

/-- A state below a supported state is supported. -/
theorem supp_of_le {X Y : AState} (h : Le cb X Y) (hs : Supp cb.cn.ctx Y) : Supp cb.cn.ctx X := by
  intro k hk
  cases k with
  | v x =>
    intro a ha
    have hY : ∀ a ∈ X.env x, a ∈ Y.env x := h.sub.1 x
    exact hs (.v x) hk (hY a ha)
  | h o c =>
    intro a ha
    exact hs (.h o c) hk ((h.heap o c a).mp ha)

/-! ## The heap keys of the engine state -/

/-- The heap keys are universe keys. -/
def HK (cb : CtxB) (E : EState) : Prop :=
  ∀ k ∈ keys E.heap, k.1 ∈ cb.cn.ctx.origins ∧ k.2 ∈ cb.cn.ctx.cells

/-- A key of a list without key `k0` is a key of the list. -/
theorem keys_eraseK {κ : Type} [DecidableEq κ] :
    ∀ (l : List (κ × List Origin)) (k0 : κ) {k : κ}, k ∈ keys (eraseK l k0) → k ∈ keys l
  | [], _, _, h => h
  | p :: rest, k0, k, h => by
    unfold eraseK at h
    by_cases e : p.1 = k0
    · rw [ite_eq_left e] at h
      exact List.mem_cons_of_mem _ (keys_eraseK rest k0 h)
    · rw [ite_eq_right e] at h
      rcases List.mem_cons.mp h with h' | h'
      · rw [h']; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (keys_eraseK rest k0 h')

/-- A key of `put` is the new key or an old key. -/
theorem keys_put {κ : Type} [DecidableEq κ] (drop : κ → List Origin → Bool)
    (l : List (κ × List Origin)) (k0 : κ) (S : List Origin) {k : κ}
    (h : k ∈ keys (put drop l k0 S)) : k = k0 ∨ k ∈ keys l := by
  unfold put at h
  cases hd : drop k0 S with
  | true => rw [hd] at h; exact Or.inr (keys_eraseK l k0 h)
  | false =>
    rw [hd] at h
    rcases List.mem_cons.mp h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (keys_eraseK l k0 h')

/-- A key of `mkMap` is in the key list. -/
theorem keys_mkMap {κ : Type} [DecidableEq κ] (drop : κ → List Origin → Bool)
    (f : κ → List Origin) : ∀ (ks : List κ) {k : κ}, k ∈ keys (mkMap drop f ks) → k ∈ ks
  | [], _, h => h
  | k0 :: ks, k, h => by
    unfold mkMap at h
    cases hd : drop k0 (f k0) with
    | true =>
      rw [hd] at h
      exact List.mem_cons_of_mem _ (keys_mkMap drop f ks h)
    | false =>
      rw [hd] at h
      rcases List.mem_cons.mp h with h' | h'
      · rw [h']; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (keys_mkMap drop f ks h')

/-- `putH` at a universe key keeps `HK`. -/
theorem HK.putH {E : EState} (h : HK cb E) {o : Origin} {c : ACell} (ho : o ∈ cb.cn.ctx.origins)
    (hc : c ∈ cb.cn.ctx.cells) (S : List Origin) : HK cb (putH cb.cn.ctx.K E (o, c) S) := by
  intro k hk
  rcases keys_put _ _ _ _ hk with e | e
  · subst e; exact ⟨ho, hc⟩
  · exact h k e

/-- The weak store through universe origins keeps `HK`. -/
theorem HK.weakE {c : ACell} (hc : c ∈ cb.cn.ctx.cells) (S : List Origin) :
    ∀ {E : EState} (os : List Origin), (∀ o ∈ os, o ∈ cb.cn.ctx.origins) → HK cb E →
      HK cb (weakE cb.cn.ctx.K c S E os)
  | _, [], _, h => h
  | _, o :: os, hos, h =>
    HK.weakE hc S os (fun o' ho' => hos o' (List.mem_cons_of_mem _ ho'))
      (h.putH (hos o List.mem_cons_self) hc _)

/-- The engine store through universe origins keeps `HK`. -/
theorem HK.storeE {E : EState} (h : HK cb E) {x : Var} {c : ACell}
    (hx : ∀ o ∈ getE E x, o ∈ cb.cn.ctx.origins) (hc : c ∈ cb.cn.ctx.cells) (S : List Origin) :
    HK cb (storeE cb E x c S) := by
  unfold DirectedAlias.Impl.Engine.storeE
  cases hs : single? (getE E x) with
  | none => exact HK.weakE hc S _ hx h
  | some o =>
    simp only
    have ho := hx o (single?_spec hs).1
    split
    · exact h.putH ho hc _
    · split
      · exact h.putH ho hc _
      · exact HK.weakE hc S _ hx h

/-- The corrected retire keeps `HK`. -/
theorem HK.retireE (hc : CtxBOK cb) {E : EState} (h : HK cb E) (s : Site) :
    HK cb (retireE cb.cn.ctx.K s E) := by
  intro k hk
  have hk' := keys_mkMap _ _ _ hk
  obtain ⟨k0, hk0, e⟩ := List.mem_map.mp hk'
  subst e
  obtain ⟨h1, h2⟩ := h k0 hk0
  refine ⟨?_, h2⟩
  show renameO s k0.1 ∈ _
  unfold renameO
  split
  · rename_i e; rw [e] at h1; exact hc.cn.base.newOld s h1
  · exact h1

/-- The engine join keeps `HK`. -/
theorem HK.joinE {E1 E2 : EState} (h1 : HK cb E1) (h2 : HK cb E2) :
    HK cb (joinE cb.cn.ctx.K E1 E2) := by
  intro k hk
  rcases List.mem_append.mp (keys_mkMap _ _ _ hk) with h | h
  · exact h1 k h
  · exact h2 k h

/-- The engine call does not change the heap map. -/
theorem callE_heap (B : Nat) (E : EState) (args : List Var) : (callE cb B E args).heap = E.heap := by
  unfold callE
  split <;> rfl

/-! ## The engine with an adequate budget -/

/-- The adequate budget of a statement: above the measure of the closure at a call. -/
def budgetOf (cb : CtxB) (E : EState) : Stmt → Nat
  | .call _ _ args => cmeas cb.cn.ctx.K E (startE cb E args) (keys E.heap) + 1
  | _ => 0

/-- The engine transfer with the adequate budget: the call closure never falls back. -/
def astepEA (cb : CtxB) (i : Nat) (st : Stmt) (E : EState) : EState :=
  astepE cb (budgetOf cb E st) i st E

/-- One statement keeps `HK`. -/
theorem HK.astepEA (hc : CtxBOK cb) (i : Nat) {E : EState} (h : HK cb E)
    (hs : Supp cb.cn.ctx (den cb.cn.ctx.K E)) :
    ∀ st : Stmt, StmtOKB cb st → HK cb (astepEA cb i st E)
  | .new x s, _ => (h.retireE hc s : HK cb _)
  | .null x, _ => h
  | .copy x y, _ => h
  | .load x y f, _ => h
  | .store x f y, ok =>
    h.storeE (fun o ho => hs (.v x) (ok.vars x List.mem_cons_self) ho)
      (ok.fields f List.mem_cons_self) _
  | .aload x y, _ => h
  | .astore x y, ok =>
    HK.weakE hc.cn.base.base.elem _ _ (fun o ho => hs (.v x) (ok.vars x List.mem_cons_self) ho) h
  | .unknown x s, _ => (h.retireE hc s : HK cb _)
  | .call ret s args, _ => by
    show HK cb (setRetE (DirectedAlias.Impl.Engine.retireE cb.cn.ctx.K s (callE cb _ E args)) ret _)
    have h1 : HK cb (callE cb (budgetOf cb E (.call ret s args)) E args) := by
      intro k hk; rw [callE_heap] at hk; exact h k hk
    cases ret with
    | none => exact h1.retireE hc s
    | some x => exact (h1.retireE hc s : HK cb _)

/-- THE ENGINE CALL IS BELOW THE MODEL CALL with an adequate budget: the engine sets are in the
model sets (only filtered origins). -/
theorem call_lower (hc : CtxBOK cb) {E : EState} (hs : Supp cb.cn.ctx (den cb.cn.ctx.K E))
    (hk : HK cb E) {args : List Var} (hargs : ∀ a ∈ args, a ∈ cb.cn.ctx.vars) {B : Nat}
    (hB : cmeas cb.cn.ctx.K E (startE cb E args) (keys E.heap) < B) :
    Le cb (den cb.cn.ctx.K (callE cb B E args))
      (DirectedAlias.Sound.ValueSem.callVS cb (den cb.cn.ctx.K E) args) := by
  have hx := hc.xvNe
  have hroots := callRoots_sub hc hs hargs
  obtain ⟨RM, hM⟩ := closeN_some_top hs hroots
  obtain ⟨RE, A, hE⟩ := closeE_some B (startE cb E args) [] (keys E.heap) [] hB
  have spec := closeE_spec (R0 := startE cb E args) (P0 := keys E.heap) B _ [] _ [] hE
    (CInv.init _ _ _ _)
  obtain ⟨h1, _, _, _, _⟩ := call_facts hc hs hk hM hE
  have hcall : DirectedAlias.Sound.ValueSem.callVS cb (den cb.cn.ctx.K E) args =
      DirectedAlias.Sound.ValueSem.setSets cb (den cb.cn.ctx.K E) RM
        (succsN cb.cn (den cb.cn.ctx.K E) RM) := by
    unfold DirectedAlias.Sound.ValueSem.callVS
    rw [hM]
  rw [hcall]
  unfold callE
  rw [hE]
  simp only
  refine (Le.of_deq (den_setsE hx E _ _)).trans ((Le.refl _).setSets hx ?_ ?_)
  · intro a ha
    exact h1 a (List.mem_filter.mp ha).1
  · intro v hv
    obtain ⟨k, hkA, hv'⟩ := mem_uniMap.mp hv
    have hvk := (List.mem_filter.mp hv').1
    have hkK := spec.2.2.2.2 k hkA
    have hcov := coveredB_mono h1 (spec.2.2.2.1 k hkA)
    exact mem_succsN.mpr ⟨k.1, (hk k hkK).1, hcov, k.2, (hk k hkK).2, hvk⟩

/-- With an adequate budget, the engine step is below the model step on the denotation. -/
theorem astep_lower (hc : CtxBOK cb) (i : Nat) {E : EState}
    (hs : Supp cb.cn.ctx (den cb.cn.ctx.K E)) (hk : HK cb E) :
    ∀ st : Stmt, StmtOKB cb st →
      Le cb (den cb.cn.ctx.K (astepEA cb i st E))
        (DirectedAlias.Sound.ValueSem.astepVS cb i st (den cb.cn.ctx.K E)) := by
  intro st ok
  cases hst : st.callSite? with
  | none => exact Le.of_deq (den_astepE cb _ i E st hst)
  | some s0 =>
    cases st with
    | call ret s args =>
      have hargs : ∀ a ∈ args, a ∈ cb.cn.ctx.vars :=
        fun a ha => ok.vars a (List.mem_append_right _ ha)
      have hr : ∀ x, ret = some x → x ≠ cb.cn.xe ∧ x ≠ cb.xv := by
        intro x e; subst e
        exact ⟨ok.noXe x (List.mem_append_left _ List.mem_cons_self),
          ok.noXv x (List.mem_append_left _ List.mem_cons_self)⟩
      show Le cb (den cb.cn.ctx.K (setRetE (retireE cb.cn.ctx.K s
          (callE cb (budgetOf cb E (.call ret s args)) E args)) ret _)) _
      have e3 := (den_setRetE cb.cn.ctx.K _ ret [.sym (.fresh s) []]).trans
        ((den_retireE cb.cn.ctx.K s (callE cb (budgetOf cb E (.call ret s args)) E args)).setRet
          ret [.sym (.fresh s) []])
      refine (Le.of_deq e3).trans ?_
      exact ((call_lower hc hs hk hargs (Nat.lt_succ_self _)).retireV _ s).setRet hr _
    | _ => cases hst

/-- EACH STATEMENT KEEPS THE SANDWICH (with the adequate budget). -/
theorem sand_step (hc : CtxBOK cb) (i : Nat) {E : EState} {M : AState}
    (hs : Supp cb.cn.ctx M) (hk : HK cb E) (hS : Sand cb E M) (st : Stmt) (ok : StmtOKB cb st) :
    Sand cb (astepEA cb i st E) (DirectedAlias.Sound.ValueSem.astepVS cb i st M) := by
  have hx := hc.xvNe
  have hsE := supp_of_le hS.1 hs
  have hv : ∀ x ∈ st.vars, x ≠ cb.cn.xe ∧ x ≠ cb.xv := fun x h => ⟨ok.noXe x h, ok.noXv x h⟩
  have hd1 : ∀ o, uniqueBO cb.cn.ctx.once cb.cn.ctx.entryUnique
      ((den cb.cn.ctx.K E).env cb.cn.xe) ((den cb.cn.ctx.K E).env cb.xv) o =
      uniqueBO cb.cn.ctx.once cb.cn.ctx.entryUnique (M.env cb.cn.xe) (M.env cb.xv) o :=
    fun o => (sand_decide hx hS o).symm
  have hd2 : ∀ o, uniqueBO cb.cn.ctx.once cb.cn.ctx.entryUnique (M.env cb.cn.xe) (M.env cb.xv) o =
      uniqueBO cb.cn.ctx.once cb.cn.ctx.entryUnique
        ((comp cb (den cb.cn.ctx.K E)).env cb.cn.xe) ((comp cb (den cb.cn.ctx.K E)).env cb.xv) o :=
    fun o => (sand_decide hx hS o).trans (uniqueBO_comp hx (den cb.cn.ctx.K E) o).symm
  refine ⟨(astep_lower hc i hsE hk st ok).trans (hS.1.astepVS hx hd1 i st hv), ?_⟩
  exact (hS.2.astepVS hx hd2 i st hv).trans
    (bridge hc (budgetOf cb E st) i hsE hk st (fun x h => ⟨ok.vars x h, ok.noXe x h, ok.noXv x h⟩))

/-- THE JOIN KEEPS THE SANDWICH. -/
theorem sand_join (hc : CtxBOK cb) {E1 E2 : EState} {M1 M2 : AState} (h1 : Sand cb E1 M1)
    (h2 : Sand cb E2 M2) : Sand cb (joinE cb.cn.ctx.K E1 E2) (DirectedAlias.join M1 M2) :=
  ⟨(Le.of_deq (den_joinE _ E1 E2)).trans (h1.1.join h2.1),
   (h1.2.join h2.2).trans (join_bridge_le hc E1 E2)⟩

/-! ## The engine analysis -/

/-- The engine loop: stop when the change test says that the head is stable. The fallback at
the end of the fuel is not modelled (the head is returned). -/
def loopE (K : Nat) (f : EState → EState) : Nat → EState → EState
  | 0, E => E
  | n + 1, E => if mapEqB (joinE K E (f E)) E = true then E else loopE K f n (joinE K E (f E))

/-- The engine analysis of a program; `i` is the null site of the first null statement. -/
def analyzeE (cb : CtxB) (fuel : Nat) : Nat → Prog → EState → EState
  | _, .skip, E => E
  | i, .stmt st, E => astepEA cb i st E
  | i, .seq p q, E => analyzeE cb fuel (i + p.nulls) q (analyzeE cb fuel i p E)
  | i, .choice p q, E =>
    joinE cb.cn.ctx.K (analyzeE cb fuel i p E) (analyzeE cb fuel (i + p.nulls) q E)
  | i, .loop p, E => loopE cb.cn.ctx.K (analyzeE cb fuel i p) fuel E

/-- A program without a loop. -/
def loopFreeB : Prog → Bool
  | .skip => true
  | .stmt _ => true
  | .seq p q => loopFreeB p && loopFreeB q
  | .choice p q => loopFreeB p && loopFreeB q
  | .loop _ => false

/-- ON A LOOP-FREE PROGRAM THE ENGINE AND THE MODEL KEEP THE SANDWICH, and the engine heap keys
stay universe keys. -/
theorem sand_analyze (hc : CtxBOK cb) (fuel : Nat) :
    ∀ (p : Prog) (i : Nat) {E : EState} {M : AState}, loopFreeB p = true →
      (∀ st ∈ p.stmts, StmtOKB cb st) → NullsIn cb i p.nulls → Supp cb.cn.ctx M → HK cb E →
      Sand cb E M →
      Sand cb (analyzeE cb fuel i p E) (analyzeVS cb i p M) ∧ HK cb (analyzeE cb fuel i p E)
  | .skip, _, _, _, _, _, _, _, hk, hS => ⟨hS, hk⟩
  | .stmt st, i, _, _, _, ok, _, hs, hk, hS => by
    have hst : StmtOKB cb st := ok st List.mem_cons_self
    exact ⟨sand_step hc i hs hk hS st hst, hk.astepEA hc i (supp_of_le hS.1 hs) st hst⟩
  | .seq p q, i, _, M, hl, ok, hn, hs, hk, hS => by
    rw [loopFreeB, Bool.and_eq_true] at hl
    have okp : ∀ st ∈ p.stmts, StmtOKB cb st := fun st h => ok st (List.mem_append_left _ h)
    have okq : ∀ st ∈ q.stmts, StmtOKB cb st := fun st h => ok st (List.mem_append_right _ h)
    obtain ⟨s1, k1⟩ := sand_analyze hc fuel p i hl.1 okp hn.left hs hk hS
    exact sand_analyze hc fuel q (i + p.nulls) hl.2 okq hn.right
      (supp_analyzeVS hc p i M okp hn.left hs) k1 s1
  | .choice p q, i, _, _, hl, ok, hn, hs, hk, hS => by
    rw [loopFreeB, Bool.and_eq_true] at hl
    have okp : ∀ st ∈ p.stmts, StmtOKB cb st := fun st h => ok st (List.mem_append_left _ h)
    have okq : ∀ st ∈ q.stmts, StmtOKB cb st := fun st h => ok st (List.mem_append_right _ h)
    obtain ⟨s1, k1⟩ := sand_analyze hc fuel p i hl.1 okp hn.left hs hk hS
    obtain ⟨s2, k2⟩ := sand_analyze hc fuel q (i + p.nulls) hl.2 okq hn.right hs hk hS
    exact ⟨sand_join hc s1 s2, k1.joinE k2⟩
  | .loop _, _, _, _, hl, _, _, _, _, _ => by cases hl

/-- In a sandwich, the engine denotation has the cell names in the cells of `old(s)` if the model
state has them. -/
theorem oldDflt_of_sand {E : EState} {M : AState} (hS : Sand cb E M)
    (h : OldDflt cb.cn.ctx.K M) : OldDflt cb.cn.ctx.K (den cb.cn.ctx.K E) :=
  fun s c => (hS.1.heap (rOld s) c _).mpr (h s c)

/-- THE NAIVE RETIRE IS HARMLESS ALONG A SANDWICHED RUN: if the model state comes from the model
analysis (so it has `OldDflt`), the naive and the corrected retire of the engine state are
set-equal. -/
theorem retireNaive_ok_of_sand {E : EState} {M : AState} (hS : Sand cb E M)
    (h : OldDflt cb.cn.ctx.K M) (s : Site) :
    DEq (den cb.cn.ctx.K (retireNaive cb.cn.ctx.K s E)) (den cb.cn.ctx.K (retireE cb.cn.ctx.K s E)) :=
  den_retireNaive_of_oldDflt (oldDflt_of_sand hS h)

end run

/-- The engine analysis of a program in the context of design VS, from the engine entry
state. -/
def analyzeProgE (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (qf : List Field) : EState :=
  analyzeE (ctxVS eu K statics fr p qf) (ctxVS eu K statics fr p qf).cn.ctx.fuel 0 p (initE fr)

/-- The reserved variables of design VS are not variables of the program. -/
theorem ctxVS_reserved (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (qf : List Field) {x : Var} (hx : x ∈ progVars fr p) :
    x ≠ (ctxVS eu K statics fr p qf).cn.xe ∧ x ≠ (ctxVS eu K statics fr p qf).xv := by
  have h : @LT.lt Nat _ x (freshVar (progVars fr p)) := DirectedAlias.Sound.CellNamed.lt_freshVar hx
  constructor
  · intro e
    have : @Eq Nat x (freshVar (progVars fr p)) := e
    omega
  · intro e
    have : @Eq Nat x (freshVar (progVars fr p) + 1) := e
    omega

/-- THE ENGINE GIVES THE ANSWERS OF DESIGN VS ON LOOP-FREE PROGRAMS: for each query of two
program variables, the may-alias answer of the engine analysis is `mayProgVS`. -/
theorem mayProgVS_engine (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (hl : loopFreeB p = true) (x : Var) (px : List ACell) (y : Var) (py : List ACell)
    (hx : x ∈ progVars fr p) (hy : y ∈ progVars fr p) :
    mayProgVS eu K statics fr p x px y py =
      may (den K (analyzeProgE eu K statics fr p (afields px ++ afields py))) x px y py := by
  let qf := afields px ++ afields py
  let cb := ctxVS eu K statics fr p qf
  have hc : CtxBOK cb := ctxVS_ok eu K statics fr p qf
  have hS0 : Sand cb (initE fr) (ainitV K fr) :=
    ⟨Le.of_deq (den_initE K fr), (Le.of_deq (den_initE K fr).symm).trans (le_comp hc.xvNe _)⟩
  have hk0 : HK cb (initE fr) := fun _ h => by cases h
  obtain ⟨hS, _⟩ := sand_analyze hc cb.cn.ctx.fuel p 0 hl (ctxVS_stmts eu K statics fr p qf)
    (fun j _ hj => ctxVS_nulls eu K statics fr p qf (by omega))
    (supp_ainitVS eu K statics fr p qf) hk0 hS0
  have ex := ctxVS_reserved eu K statics fr p qf hx
  have ey := ctxVS_reserved eu K statics fr p qf hy
  exact (may_le hS.1 ex.1 ex.2 ey.1 ey.2 px py).symm

end DirectedAlias.Impl.Engine

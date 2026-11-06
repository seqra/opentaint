import DirectedAlias.Impl.EngineState
import DirectedAlias.Sound.ValueSem.BackwardEq

/-!
# The engine call: closure over the written entries, filtered sets, completion (obligation 3)

The model call (`callVS`, closure `closeN`/`succsN`) reads every universe cell of every covered
universe origin. The engine call (`callE`) runs a worklist over the WRITTEN entries only
(`closeE`): when an origin `a` enters `R`, each pending written entry whose origin is a
descendant of `a` (`descB`) is activated, and its content is pushed. The covered test is the
test of the model (`coveredB`). The start set is the start set of the model (`callRoots`).

The two reserved sets keep only the origins that can matter for the strong-update test:
* `Etree` gets the SYMBOLIC origins of `R` (`isSymB`);
* `Eval` gets the contents of the activated entries that CAN BE UNIQUE (`canU`: a symbolic origin
  without an array cell, or an allocation origin). Default contents are not added.
If the budget of the worklist runs out, both sets get every universe origin (the marker).

THE COMPLETION `comp` adds to `Etree` the universe origins that are not symbolic or not unique
for `Etree`, and to `Eval` the universe origins that are not unique for `Etree` (`blkT`, `blkV`).
These origins are already blocked, so:
* (a) `comp` changes no `uniqueBO` answer (`uniqueBO_comp`); it is monotone (`comp_mono`),
  it distributes over `join` (`comp_join`), and the retire rename commutes with it up to `⊑`
  (`retireV_comp_le`).
* (b) the engine closure covers the same origins as the model closure (`closure_cover_eq`), and
  the model sets are in the completion of the engine sets (`call_bridge`).
* (c) THE BRIDGE (`bridge`): for each statement and engine state with support and universe keys,
  `astepVS (comp (den E))` and `comp (den (astepE E))` have set-equal env (outside the reserved
  keys) and heap, and the model sets are in the completed engine sets (`Le`). For the join the
  two sides are set-equal (`join_bridge`). An engine post-fixpoint gives a model post-fixpoint
  (`post_fixpoint`) with the same may-alias answers (`may_comp`).
-/

namespace DirectedAlias.Impl.Engine

open DirectedAlias DirectedAlias.Opt DirectedAlias.Opt.Rec
open DirectedAlias.Sound.Recency DirectedAlias.Sound.HavocRecency DirectedAlias.Sound.CellNamed
open DirectedAlias.Sound.BlockOnly DirectedAlias.Sound.ValueSem

/-! ## Prefix facts -/

/-- The prefix relation is transitive. -/
theorem preB_trans {p q r : List ACell} (h1 : preB p q = true) (h2 : preB q r = true) :
    preB p r = true := by
  have e1 : q.take p.length = p := of_decide_eq_true h1
  have e2 : r.take q.length = q := of_decide_eq_true h2
  have hl := preB_len h1
  apply decide_eq_true
  calc r.take p.length = (r.take q.length).take p.length := by
        rw [List.take_take, Nat.min_eq_left hl]
    _ = p := by rw [e2, e1]

/-- A prefix with the same length is the path. -/
theorem preB_eq {p q : List ACell} (h : preB p q = true) (hl : p.length = q.length) : p = q := by
  have e : q.take p.length = p := of_decide_eq_true h
  rw [hl, List.take_length] at e
  exact e.symm

/-- A proper descendant relation is transitive. -/
theorem descM_trans : ∀ {a u w : Origin}, descM a u = true → descM u w = true → descM a w = true := by
  intro a u w h1 h2
  cases a <;> cases u <;> simp only [descM, Bool.false_eq_true] at h1 <;>
    cases w <;> simp only [descM, Bool.false_eq_true] at h2 ⊢
  case sym.sym.sym b p b' q b'' r =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1 h2 ⊢
    exact ⟨h1.1.trans h2.1, preB_trans h1.2 h2.2⟩
  case sym.sym.deep b p b' q b'' =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1 h2 ⊢
    exact h1.1.trans h2
  case alloc.hsym.hsym x s k c q s' k' c' r =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1 h2 ⊢
    obtain ⟨⟨⟨e1, e2⟩, _⟩, _⟩ := h2
    subst e1; subst e2
    exact h1
  case alloc.hsym.hdeep x s k c s' k' c' =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1 h2 ⊢
    obtain ⟨⟨e1, e2⟩, _⟩ := h2
    subst e1; subst e2
    exact h1
  case hsym.hsym.hsym s k c p s' k' c' q s'' k'' c'' r =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1 h2 ⊢
    obtain ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩ := h1
    obtain ⟨⟨⟨b1, b2⟩, b3⟩, b4⟩ := h2
    exact ⟨⟨⟨a1.trans b1, a2.trans b2⟩, a3.trans b3⟩, preB_trans a4 b4⟩
  case hsym.hsym.hdeep s k c p s' k' c' q s'' k'' c'' =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1 h2 ⊢
    obtain ⟨⟨⟨a1, a2⟩, a3⟩, _⟩ := h1
    obtain ⟨⟨b1, b2⟩, b3⟩ := h2
    exact ⟨⟨a1.trans b1, a2.trans b2⟩, a3.trans b3⟩

/-- The descendant relation is transitive. -/
theorem descB_trans {a u w : Origin} (h1 : descB a u = true) (h2 : descB u w = true) :
    descB a w = true := by
  rcases descB_iff.mp h1 with e | m1
  · subst e; exact h2
  rcases descB_iff.mp h2 with e | m2
  · subst e; exact h1
  exact descB_iff.mpr (Or.inr (descM_trans m1 m2))

/-- The covered test of a list with one more origin. -/
theorem coveredB_cons (a : Origin) (R : List Origin) (u : Origin) :
    coveredB (a :: R) u = (descB a u || coveredB R u) := rfl

/-- The covered test is monotone in the list. -/
theorem coveredB_mono {R R' : List Origin} (h : ∀ a ∈ R, a ∈ R') {u : Origin}
    (hu : coveredB R u = true) : coveredB R' u = true := by
  obtain ⟨a, ha, hd⟩ := coveredB_iff.mp hu
  exact coveredB_iff.mpr ⟨a, h a ha, hd⟩

/-! ## Uniqueness facts -/

/-- A path with an array cell has the array cell in each extension. -/
theorem contains_pre {p q : List ACell} (h : preB p q = true) (hp : p.contains .elem = true) :
    q.contains .elem = true := by
  have e : q.take p.length = p := of_decide_eq_true h
  rw [List.contains_iff_mem] at hp ⊢
  rw [← e] at hp
  exact List.mem_of_mem_take hp

/-- A prefix of a unique symbolic origin is unique by kind. -/
theorem uniqueR_pre {once : Site → Bool} {eu : Bool} {b : ABase} {p q : List ACell}
    (h : preB p q = true) (hu : uniqueR once eu (.sym b q) = true) :
    uniqueR once eu (.sym b p) = true := by
  have hc : p.contains .elem = false := by
    cases hp : p.contains .elem with
    | false => rfl
    | true =>
      have hq := contains_pre h hp
      cases b with
      | root r =>
        have hu' : (eu && !(q.contains .elem)) = true := hu
        rw [hq] at hu'; simp at hu'
      | fresh s =>
        have hu' : (eu && once s && !(q.contains .elem)) = true := hu
        rw [hq] at hu'; simp at hu'
  cases b with
  | root r =>
    have hu' : (eu && !(q.contains .elem)) = true := hu
    show (eu && !(p.contains .elem)) = true
    rw [hc]
    rw [Bool.and_eq_true] at hu'
    rw [hu'.1]; rfl
  | fresh s =>
    have hu' : (eu && once s && !(q.contains .elem)) = true := hu
    show (eu && once s && !(p.contains .elem)) = true
    rw [hc]
    rw [Bool.and_eq_true] at hu'
    rw [hu'.1]; rfl

/-- A symbolic origin with a blocked prefix is blocked by the same exposed origin. -/
theorem expB_pre {E : List Origin} {b : ABase} {p q : List ACell}
    (he : expB E (.sym b p) = true) (h : preB p q = true) : expB E (.sym b q) = true := by
  obtain ⟨p0, hm, hl, hp⟩ := expB_inv he
  exact expB_of hm (Nat.lt_of_lt_of_le hl (preB_len h)) (preB_trans hp h)

/-- A prefix of a unique symbolic origin is unique. -/
theorem uniqueCN_pre {once : Site → Bool} {eu : Bool} {E : List Origin} {b : ABase}
    {p q : List ACell} (h : preB p q = true) (hu : uniqueCN once eu E (.sym b q) = true) :
    uniqueCN once eu E (.sym b p) = true := by
  unfold uniqueCN at hu ⊢
  rw [Bool.and_eq_true] at hu ⊢
  refine ⟨uniqueR_pre h hu.1, ?_⟩
  cases he : expB E (.sym b p) with
  | false => rfl
  | true => rw [expB_pre he h] at hu; exact absurd hu.2 (by decide)

/-- Uniqueness is antitone in the exposed set. -/
theorem uniqueCN_anti {once : Site → Bool} {eu : Bool} {E E' : List Origin}
    (hs : ∀ a ∈ E, a ∈ E') {u : Origin} (hu : uniqueCN once eu E' u = true) :
    uniqueCN once eu E u = true := by
  unfold uniqueCN at hu ⊢
  rw [Bool.and_eq_true] at hu ⊢
  refine ⟨hu.1, ?_⟩
  cases he : expB E u with
  | false => rfl
  | true => rw [expB_mono hs he] at hu; exact absurd hu.2 (by decide)

/-! ## The completion -/

/-- An origin is symbolic. -/
def isSymB : Origin → Bool
  | .sym _ _ => true
  | _ => false

/-- An origin that `Etree` can hold without effect: it is not symbolic, or not unique for `E`. -/
def blkT (once : Site → Bool) (eu : Bool) (E : List Origin) (u : Origin) : Bool :=
  !isSymB u || !uniqueCN once eu E u

/-- An origin that `Eval` can hold without effect: it is not unique for `E`. -/
def blkV (once : Site → Bool) (eu : Bool) (E : List Origin) (u : Origin) : Bool :=
  !uniqueCN once eu E u

/-- The completion of the `Etree` set `E`. -/
def compE (cb : CtxB) (E : List Origin) : List Origin :=
  uni (cb.cn.ctx.origins.filter (blkT cb.cn.ctx.once cb.cn.ctx.entryUnique E)) E

/-- The completion of the `Eval` set `V`, for the `Etree` set `E`. -/
def compV (cb : CtxB) (E V : List Origin) : List Origin :=
  uni (cb.cn.ctx.origins.filter (blkV cb.cn.ctx.once cb.cn.ctx.entryUnique E)) V

/-- THE COMPLETION: add to `Etree` and `Eval` the universe origins that are already blocked.
The heap and every other variable do not change. -/
def comp (cb : CtxB) (X : AState) : AState where
  env := fupd (fupd X.env cb.cn.xe (compE cb (X.env cb.cn.xe))) cb.xv
    (compV cb (X.env cb.cn.xe) (X.env cb.xv))
  heap := X.heap

section comp

variable {cb : CtxB}

/-- The `Etree` key of the completion. -/
theorem comp_xe (hx : cb.xv ≠ cb.cn.xe) (X : AState) :
    (comp cb X).env cb.cn.xe = compE cb (X.env cb.cn.xe) := by
  show fupd (fupd X.env _ _) cb.xv _ cb.cn.xe = _
  rw [fupd_ne _ _ (fun h => hx h.symm), fupd_same]

/-- The `Eval` key of the completion. -/
theorem comp_xv (X : AState) :
    (comp cb X).env cb.xv = compV cb (X.env cb.cn.xe) (X.env cb.xv) := by
  show fupd (fupd X.env _ _) cb.xv _ cb.xv = _
  rw [fupd_same]

/-- The completion keeps the other variables. -/
theorem comp_ne (X : AState) {x : Var} (h1 : x ≠ cb.cn.xe) (h2 : x ≠ cb.xv) :
    (comp cb X).env x = X.env x := by
  show fupd (fupd X.env _ _) cb.xv _ x = _
  rw [fupd_ne _ _ h2, fupd_ne _ _ h1]

/-- Each added `Etree` origin is blocked. -/
theorem uniqueCN_compE (E : List Origin) (o : Origin) :
    uniqueCN cb.cn.ctx.once cb.cn.ctx.entryUnique (compE cb E) o =
      uniqueCN cb.cn.ctx.once cb.cn.ctx.entryUnique E o := by
  have hA : ∀ u ∈ cb.cn.ctx.origins.filter (blkT cb.cn.ctx.once cb.cn.ctx.entryUnique E),
      blkT cb.cn.ctx.once cb.cn.ctx.entryUnique E u = true :=
    fun u hu => (List.mem_filter.mp hu).2
  unfold compE
  generalize cb.cn.ctx.origins.filter (blkT cb.cn.ctx.once cb.cn.ctx.entryUnique E) = A at hA
  show uniqueCN _ _ (uni A E) o = _
  cases h1 : uniqueCN cb.cn.ctx.once cb.cn.ctx.entryUnique E o with
  | false =>
    cases h2 : uniqueCN cb.cn.ctx.once cb.cn.ctx.entryUnique (uni A E) o with
    | false => rfl
    | true =>
      rw [uniqueCN_anti (fun a ha => mem_uni.mpr (Or.inr ha)) h2] at h1; cases h1
  | true =>
    have hu := h1
    unfold uniqueCN at hu ⊢
    rw [Bool.and_eq_true] at hu
    rw [hu.1]
    cases o with
    | sym b q =>
      cases he : expB (uni A E) (.sym b q) with
      | false => rfl
      | true =>
        obtain ⟨p, hm, hl, hp⟩ := expB_inv he
        rcases mem_uni.mp hm with hmA | hmE
        · have hb := hA _ hmA
          unfold blkT at hb
          have hu2 : uniqueCN cb.cn.ctx.once cb.cn.ctx.entryUnique E (.sym b p) = true :=
            uniqueCN_pre hp h1
          rw [hu2] at hb
          cases hb
        · rw [expB_of hmE hl hp] at hu; exact absurd hu.2 (by decide)
    | deep _ => rfl
    | alloc _ => rfl
    | havoc _ => rfl
    | hsym _ _ _ _ => rfl
    | hdeep _ _ _ => rfl

/-- (a) THE COMPLETION CHANGES NO STRONG-UPDATE ANSWER: `uniqueBO` with the completed sets is
`uniqueBO` with the sets, for every origin. -/
theorem uniqueBO_compSets (E V : List Origin) (o : Origin) :
    uniqueBO cb.cn.ctx.once cb.cn.ctx.entryUnique (compE cb E) (compV cb E V) o =
      uniqueBO cb.cn.ctx.once cb.cn.ctx.entryUnique E V o := by
  unfold uniqueBO
  rw [uniqueCN_compE]
  cases h : uniqueCN cb.cn.ctx.once cb.cn.ctx.entryUnique E o with
  | false => rfl
  | true =>
    simp only [Bool.true_and]
    have : o ∈ compV cb E V ↔ o ∈ V := by
      unfold compV
      rw [mem_uni, List.mem_filter]
      constructor
      · rintro (⟨_, hb⟩ | hv)
        · unfold blkV at hb; rw [h] at hb; cases hb
        · exact hv
      · exact Or.inr
    by_cases hv : o ∈ V
    · rw [decide_eq_true hv, decide_eq_true (this.mpr hv)]
    · rw [decide_eq_false hv, decide_eq_false (fun h' => hv (this.mp h'))]

/-- (a) The completion of a state changes no `uniqueBO` answer of the state. -/
theorem uniqueBO_comp (hx : cb.xv ≠ cb.cn.xe) (X : AState) (o : Origin) :
    uniqueBO cb.cn.ctx.once cb.cn.ctx.entryUnique ((comp cb X).env cb.cn.xe)
        ((comp cb X).env cb.xv) o =
      uniqueBO cb.cn.ctx.once cb.cn.ctx.entryUnique (X.env cb.cn.xe) (X.env cb.xv) o := by
  rw [comp_xe hx, comp_xv]
  exact uniqueBO_compSets _ _ o

/-- `blkT` is monotone in the exposed set. -/
theorem blkT_mono {E E' : List Origin} (hs : ∀ a ∈ E, a ∈ E') {u : Origin}
    (h : blkT cb.cn.ctx.once cb.cn.ctx.entryUnique E u = true) :
    blkT cb.cn.ctx.once cb.cn.ctx.entryUnique E' u = true := by
  unfold blkT at h ⊢
  cases hs1 : isSymB u with
  | false => rfl
  | true =>
    rw [hs1] at h
    cases hu : uniqueCN cb.cn.ctx.once cb.cn.ctx.entryUnique E' u with
    | false => rfl
    | true => rw [uniqueCN_anti hs hu] at h; cases h

/-- `blkV` is monotone in the exposed set. -/
theorem blkV_mono {E E' : List Origin} (hs : ∀ a ∈ E, a ∈ E') {u : Origin}
    (h : blkV cb.cn.ctx.once cb.cn.ctx.entryUnique E u = true) :
    blkV cb.cn.ctx.once cb.cn.ctx.entryUnique E' u = true := by
  unfold blkV at h ⊢
  cases hu : uniqueCN cb.cn.ctx.once cb.cn.ctx.entryUnique E' u with
  | false => rfl
  | true => rw [uniqueCN_anti hs hu] at h; cases h

/-- The `Etree` completion is monotone. -/
theorem compE_mono {E E' : List Origin} (hs : ∀ a ∈ E, a ∈ E') :
    ∀ a ∈ compE cb E, a ∈ compE cb E' := by
  intro a ha
  unfold compE at ha ⊢
  rcases mem_uni.mp ha with h | h
  · obtain ⟨h1, h2⟩ := List.mem_filter.mp h
    exact mem_uni.mpr (Or.inl (List.mem_filter.mpr ⟨h1, blkT_mono hs h2⟩))
  · exact mem_uni.mpr (Or.inr (hs a h))

/-- The `Eval` completion is monotone. -/
theorem compV_mono {E E' V V' : List Origin} (hs : ∀ a ∈ E, a ∈ E') (hv : ∀ a ∈ V, a ∈ V') :
    ∀ a ∈ compV cb E V, a ∈ compV cb E' V' := by
  intro a ha
  unfold compV at ha ⊢
  rcases mem_uni.mp ha with h | h
  · obtain ⟨h1, h2⟩ := List.mem_filter.mp h
    exact mem_uni.mpr (Or.inl (List.mem_filter.mpr ⟨h1, blkV_mono hs h2⟩))
  · exact mem_uni.mpr (Or.inr (hv a h))

/-- A set is in its `Etree` completion. -/
theorem sub_compE (E : List Origin) : ∀ a ∈ E, a ∈ compE cb E :=
  fun _ h => mem_uni.mpr (Or.inr h)

/-- A set is in its `Eval` completion. -/
theorem sub_compV (E V : List Origin) : ∀ a ∈ V, a ∈ compV cb E V :=
  fun _ h => mem_uni.mpr (Or.inr h)

/-- (a) THE COMPLETION IS MONOTONE. -/
theorem comp_mono (hx : cb.xv ≠ cb.cn.xe) {X Y : AState} (h : X.Sub Y) :
    (comp cb X).Sub (comp cb Y) := by
  refine ⟨fun x => ?_, fun o c => h.2 o c⟩
  by_cases e1 : x = cb.xv
  · subst e1; rw [comp_xv, comp_xv]; exact compV_mono (h.1 _) (h.1 _)
  · by_cases e2 : x = cb.cn.xe
    · subst e2; rw [comp_xe hx, comp_xe hx]; exact compE_mono (h.1 _)
    · rw [comp_ne X e2 e1, comp_ne Y e2 e1]; exact h.1 x

/-- The exposed test of a union. -/
theorem expB_uni {A B : List Origin} {u : Origin} (h : expB (uni A B) u = true) :
    expB A u = true ∨ expB B u = true := by
  cases u with
  | sym b q =>
    obtain ⟨p, hm, hl, hp⟩ := expB_inv h
    rcases mem_uni.mp hm with h1 | h1
    · exact Or.inl (expB_of h1 hl hp)
    · exact Or.inr (expB_of h1 hl hp)
  | _ => cases h

/-- A non-unique origin for a union is non-unique for one side. -/
theorem uniqueCN_uni {A B : List Origin} {u : Origin}
    (h : uniqueCN cb.cn.ctx.once cb.cn.ctx.entryUnique (uni A B) u = false) :
    uniqueCN cb.cn.ctx.once cb.cn.ctx.entryUnique A u = false ∨
      uniqueCN cb.cn.ctx.once cb.cn.ctx.entryUnique B u = false := by
  unfold uniqueCN at h ⊢
  cases hr : uniqueR cb.cn.ctx.once cb.cn.ctx.entryUnique u with
  | false => exact Or.inl rfl
  | true =>
    rw [hr] at h
    cases he : expB (uni A B) u with
    | false => rw [he] at h; cases h
    | true =>
      rcases expB_uni he with h1 | h1
      · left; rw [h1]; rfl
      · right; rw [h1]; rfl

/-- (a) THE COMPLETION DISTRIBUTES OVER THE JOIN (up to set equality). -/
theorem comp_join (hx : cb.xv ≠ cb.cn.xe) (X Y : AState) :
    DEq (comp cb (join X Y)) (join (comp cb X) (comp cb Y)) := by
  refine ⟨fun x => ?_, fun o c => SetEq.refl _⟩
  show SetEq ((comp cb (join X Y)).env x) (uni ((comp cb X).env x) ((comp cb Y).env x))
  by_cases e1 : x = cb.xv
  · subst e1
    rw [comp_xv, comp_xv, comp_xv]
    intro a
    rw [mem_uni]
    constructor
    · intro ha
      unfold compV at ha
      rcases mem_uni.mp ha with h | h
      · obtain ⟨h1, h2⟩ := List.mem_filter.mp h
        unfold blkV at h2
        change (!uniqueCN _ _ (uni (X.env cb.cn.xe) (Y.env cb.cn.xe)) a) = true at h2
        have h3 : uniqueCN cb.cn.ctx.once cb.cn.ctx.entryUnique
            (uni (X.env cb.cn.xe) (Y.env cb.cn.xe)) a = false := by
          cases e : uniqueCN cb.cn.ctx.once cb.cn.ctx.entryUnique
            (uni (X.env cb.cn.xe) (Y.env cb.cn.xe)) a with
          | false => rfl
          | true => rw [e] at h2; cases h2
        rcases uniqueCN_uni h3 with h4 | h4
        · left; unfold compV; refine mem_uni.mpr (Or.inl (List.mem_filter.mpr ⟨h1, ?_⟩))
          unfold blkV; rw [h4]; rfl
        · right; unfold compV; refine mem_uni.mpr (Or.inl (List.mem_filter.mpr ⟨h1, ?_⟩))
          unfold blkV; rw [h4]; rfl
      · rcases mem_uni.mp h with h' | h'
        · exact Or.inl (sub_compV _ _ a h')
        · exact Or.inr (sub_compV _ _ a h')
    · rintro (h | h)
      · exact compV_mono (fun b hb => mem_uni.mpr (Or.inl hb))
          (fun b hb => mem_uni.mpr (Or.inl hb)) a h
      · exact compV_mono (fun b hb => mem_uni.mpr (Or.inr hb))
          (fun b hb => mem_uni.mpr (Or.inr hb)) a h
  · by_cases e2 : x = cb.cn.xe
    · subst e2
      rw [comp_xe hx, comp_xe hx, comp_xe hx]
      intro a
      rw [mem_uni]
      constructor
      · intro ha
        unfold compE at ha
        rcases mem_uni.mp ha with h | h
        · obtain ⟨h1, h2⟩ := List.mem_filter.mp h
          unfold blkT at h2
          cases hs : isSymB a with
          | false =>
            left; unfold compE; refine mem_uni.mpr (Or.inl (List.mem_filter.mpr ⟨h1, ?_⟩))
            unfold blkT; rw [hs]; rfl
          | true =>
            rw [hs] at h2
            change (!true || !uniqueCN _ _ (uni (X.env cb.cn.xe) (Y.env cb.cn.xe)) a) = true at h2
            have h3 : uniqueCN cb.cn.ctx.once cb.cn.ctx.entryUnique
                (uni (X.env cb.cn.xe) (Y.env cb.cn.xe)) a = false := by
              cases e : uniqueCN cb.cn.ctx.once cb.cn.ctx.entryUnique
                (uni (X.env cb.cn.xe) (Y.env cb.cn.xe)) a with
              | false => rfl
              | true => rw [e] at h2; cases h2
            rcases uniqueCN_uni h3 with h4 | h4
            · left; unfold compE; refine mem_uni.mpr (Or.inl (List.mem_filter.mpr ⟨h1, ?_⟩))
              unfold blkT; rw [h4]; simp
            · right; unfold compE; refine mem_uni.mpr (Or.inl (List.mem_filter.mpr ⟨h1, ?_⟩))
              unfold blkT; rw [h4]; simp
        · rcases mem_uni.mp h with h' | h'
          · exact Or.inl (sub_compE _ a h')
          · exact Or.inr (sub_compE _ a h')
      · rintro (h | h)
        · exact compE_mono (fun b hb => mem_uni.mpr (Or.inl hb)) a h
        · exact compE_mono (fun b hb => mem_uni.mpr (Or.inr hb)) a h
    · show SetEq ((comp cb (join X Y)).env x) (uni ((comp cb X).env x) ((comp cb Y).env x))
      rw [comp_ne _ e2 e1, comp_ne _ e2 e1, comp_ne _ e2 e1]
      exact SetEq.refl _

/-! ## The relation of the bridge -/

/-- The bridge relation: set-equal env outside the two reserved keys, set-equal heap, and the
two reserved sets are included. -/
structure Le (cb : CtxB) (X Y : AState) : Prop where
  env : ∀ x, x ≠ cb.cn.xe → x ≠ cb.xv → SetEq (X.env x) (Y.env x)
  heap : ∀ o c, SetEq (X.heap o c) (Y.heap o c)
  te : ∀ a ∈ X.env cb.cn.xe, a ∈ Y.env cb.cn.xe
  tv : ∀ a ∈ X.env cb.xv, a ∈ Y.env cb.xv

/-- `Le` is reflexive. -/
theorem Le.refl (X : AState) : Le cb X X :=
  ⟨fun _ _ _ => SetEq.refl _, fun _ _ => SetEq.refl _, fun _ h => h, fun _ h => h⟩

/-- `Le` is transitive. -/
theorem Le.trans {X Y Z : AState} (h1 : Le cb X Y) (h2 : Le cb Y Z) : Le cb X Z :=
  ⟨fun x e1 e2 => (h1.env x e1 e2).trans (h2.env x e1 e2),
   fun o c => (h1.heap o c).trans (h2.heap o c),
   fun a h => h2.te a (h1.te a h), fun a h => h2.tv a (h1.tv a h)⟩

/-- Set equality gives `Le`. -/
theorem Le.of_deq {X Y : AState} (h : DEq X Y) : Le cb X Y :=
  ⟨fun x _ _ => h.1 x, h.2, fun a ha => (h.1 _ a).mp ha, fun a ha => (h.1 _ a).mp ha⟩

/-- `Le` gives inclusion. -/
theorem Le.sub {X Y : AState} (h : Le cb X Y) : X.Sub Y := by
  refine ⟨fun x => ?_, fun o c a ha => (h.heap o c a).mp ha⟩
  by_cases e1 : x = cb.cn.xe
  · subst e1; exact h.te
  · by_cases e2 : x = cb.xv
    · subst e2; exact h.tv
    · exact fun a ha => (h.env x e1 e2 a).mp ha

/-- `setVar` of a variable that is not reserved keeps `Le`. -/
theorem Le.setVar {X Y : AState} (h : Le cb X Y) {x : Var} (h1 : x ≠ cb.cn.xe) (h2 : x ≠ cb.xv)
    {S S' : List Origin} (hS : SetEq S S') : Le cb (X.setVar x S) (Y.setVar x S') := by
  refine ⟨fun y e1 e2 => ?_, h.heap, ?_, ?_⟩
  · show SetEq (fupd X.env x S y) (fupd Y.env x S' y)
    by_cases e : y = x
    · subst e; rw [fupd_same, fupd_same]; exact hS
    · rw [fupd_ne _ _ e, fupd_ne _ _ e]; exact h.env y e1 e2
  · show ∀ a ∈ fupd X.env x S cb.cn.xe, a ∈ fupd Y.env x S' cb.cn.xe
    rw [fupd_ne _ _ (fun e => h1 e.symm), fupd_ne _ _ (fun e => h1 e.symm)]; exact h.te
  · show ∀ a ∈ fupd X.env x S cb.xv, a ∈ fupd Y.env x S' cb.xv
    rw [fupd_ne _ _ (fun e => h2 e.symm), fupd_ne _ _ (fun e => h2 e.symm)]; exact h.tv

/-- `setRet` of a result variable that is not reserved keeps `Le`. -/
theorem Le.setRet {X Y : AState} (h : Le cb X Y) {r : Option Var}
    (hr : ∀ x, r = some x → x ≠ cb.cn.xe ∧ x ≠ cb.xv) (S : List Origin) :
    Le cb (X.setRet r S) (Y.setRet r S) := by
  cases r with
  | none => exact h
  | some x =>
    obtain ⟨h1, h2⟩ := hr x rfl
    exact h.setVar h1 h2 (SetEq.refl S)

/-- `retireV` keeps `Le`. -/
theorem Le.retireV {X Y : AState} (h : Le cb X Y) (K : Nat) (s : Site) :
    Le cb (DirectedAlias.Sound.ValueSem.retireV K s X)
      (DirectedAlias.Sound.ValueSem.retireV K s Y) := by
  refine ⟨fun x e1 e2 => renameL_congr (h.env x e1 e2), fun o c => ?_, ?_, ?_⟩
  · show SetEq (if o = rNew s then _ else (retire s X).heap o c)
      (if o = rNew s then _ else (retire s Y).heap o c)
    by_cases e : o = rNew s
    · rw [ite_eq_left e, ite_eq_left e]; exact SetEq.refl _
    · rw [ite_eq_right e, ite_eq_right e]
      show SetEq (if o = rNew s then [] else if o = rOld s then
          renameL s (uni (X.heap (rNew s) c) (X.heap (rOld s) c)) else renameL s (X.heap o c))
        (if o = rNew s then [] else if o = rOld s then
          renameL s (uni (Y.heap (rNew s) c) (Y.heap (rOld s) c)) else renameL s (Y.heap o c))
      rw [ite_eq_right e, ite_eq_right e]
      by_cases e2 : o = rOld s
      · rw [ite_eq_left e2, ite_eq_left e2]
        exact renameL_congr (SetEq.uni (h.heap _ _) (h.heap _ _))
      · rw [ite_eq_right e2, ite_eq_right e2]; exact renameL_congr (h.heap _ _)
  · intro a ha
    obtain ⟨o, ho, rfl⟩ := mem_renameL.mp ha
    exact mem_renameL.mpr ⟨o, h.te o ho, rfl⟩
  · intro a ha
    obtain ⟨o, ho, rfl⟩ := mem_renameL.mp ha
    exact mem_renameL.mpr ⟨o, h.tv o ho, rfl⟩

/-- The completion keeps `Le`. -/
theorem Le.comp (hx : cb.xv ≠ cb.cn.xe) {X Y : AState} (h : Le cb X Y) :
    Le cb (comp cb X) (comp cb Y) := by
  refine ⟨fun x e1 e2 => ?_, h.heap, ?_, ?_⟩
  · rw [comp_ne X e1 e2, comp_ne Y e1 e2]; exact h.env x e1 e2
  · rw [comp_xe hx, comp_xe hx]; exact compE_mono h.te
  · rw [comp_xv, comp_xv]; exact compV_mono h.te h.tv

/-- A state is `Le` its completion. -/
theorem le_comp (hx : cb.xv ≠ cb.cn.xe) (X : AState) : Le cb X (comp cb X) := by
  refine ⟨fun x e1 e2 => ?_, fun o c => SetEq.refl _, ?_, ?_⟩
  · rw [comp_ne X e1 e2]; exact SetEq.refl _
  · rw [comp_xe hx]; exact sub_compE _
  · rw [comp_xv]; exact sub_compV _ _

/-- The completion keeps set equality. -/
theorem DEq.comp (hx : cb.xv ≠ cb.cn.xe) {X Y : AState} (h : DEq X Y) :
    DEq (comp cb X) (comp cb Y) := by
  have h1 := (Le.of_deq (cb := cb) h).comp hx
  have h2 := (Le.of_deq (cb := cb) h.symm).comp hx
  refine ⟨fun x => ?_, h1.heap⟩
  by_cases e1 : x = cb.cn.xe
  · subst e1; exact fun a => ⟨h1.te a, h2.te a⟩
  · by_cases e2 : x = cb.xv
    · subst e2; exact fun a => ⟨h1.tv a, h2.tv a⟩
    · exact h1.env x e1 e2

/-- (a) THE RETIRE RENAME COMMUTES WITH THE COMPLETION, up to `⊑`: the renamed completed sets
are in the completion of the renamed sets. -/
theorem retireV_comp_le (hc : CtxBOK cb) (X : AState) (s : Site) :
    Le cb (DirectedAlias.Sound.ValueSem.retireV cb.cn.ctx.K s (comp cb X))
      (comp cb (DirectedAlias.Sound.ValueSem.retireV cb.cn.ctx.K s X)) := by
  have hx := hc.xvNe
  have hren : ∀ {E : List Origin} {u : Origin},
      uniqueCN cb.cn.ctx.once cb.cn.ctx.entryUnique (renameL s E) u = true →
      uniqueCN cb.cn.ctx.once cb.cn.ctx.entryUnique E u = true := by
    intro E u hu
    unfold uniqueCN at hu ⊢
    rw [Bool.and_eq_true] at hu ⊢
    refine ⟨hu.1, ?_⟩
    cases he : expB E u with
    | false => rfl
    | true => rw [expB_renameL s he] at hu; exact absurd hu.2 (by decide)
  have hOldU : ∀ u ∈ cb.cn.ctx.origins, renameO s u ∈ cb.cn.ctx.origins := by
    intro u hu
    unfold renameO
    split
    · rename_i e; subst e; exact hc.cn.base.newOld s hu
    · exact hu
  have hOldNU : ∀ E, uniqueCN cb.cn.ctx.once cb.cn.ctx.entryUnique E (rOld s) = false := by
    intro E
    have h : @Eq Nat ((2 * s + 1) % 2) 1 := by omega
    show (((2 * s + 1) % 2 == 0) && !expB E (rOld s)) = false
    rw [h]; rfl
  refine ⟨fun x e1 e2 => ?_, fun o c => SetEq.refl _, ?_, ?_⟩
  · show SetEq (renameL s ((comp cb X).env x)) ((comp cb _).env x)
    rw [comp_ne X e1 e2, comp_ne _ e1 e2]; exact SetEq.refl _
  · show ∀ a ∈ renameL s ((comp cb X).env cb.cn.xe), a ∈ (comp cb _).env cb.cn.xe
    rw [comp_xe hx, comp_xe hx]
    intro a ha
    obtain ⟨u, hu, rfl⟩ := mem_renameL.mp ha
    unfold compE at hu ⊢
    rcases mem_uni.mp hu with h | h
    · obtain ⟨h1, h2⟩ := List.mem_filter.mp h
      refine mem_uni.mpr (Or.inl (List.mem_filter.mpr ⟨hOldU u h1, ?_⟩))
      show blkT _ _ (renameL s (X.env cb.cn.xe)) (renameO s u) = true
      unfold renameO
      split
      · unfold blkT; rfl
      · unfold blkT at h2 ⊢
        cases hs1 : isSymB u with
        | false => rfl
        | true =>
          rw [hs1] at h2
          cases hu2 : uniqueCN cb.cn.ctx.once cb.cn.ctx.entryUnique
            (renameL s (X.env cb.cn.xe)) u with
          | false => rfl
          | true => rw [hren hu2] at h2; cases h2
    · exact mem_uni.mpr (Or.inr (mem_renameL.mpr ⟨u, h, rfl⟩))
  · show ∀ a ∈ renameL s ((comp cb X).env cb.xv), a ∈ (comp cb _).env cb.xv
    rw [comp_xv, comp_xv]
    intro a ha
    obtain ⟨u, hu, rfl⟩ := mem_renameL.mp ha
    unfold compV at hu ⊢
    rcases mem_uni.mp hu with h | h
    · obtain ⟨h1, h2⟩ := List.mem_filter.mp h
      refine mem_uni.mpr (Or.inl (List.mem_filter.mpr ⟨hOldU u h1, ?_⟩))
      show blkV _ _ (renameL s (X.env cb.cn.xe)) (renameO s u) = true
      unfold renameO
      split
      · unfold blkV; rw [hOldNU]; rfl
      · unfold blkV at h2 ⊢
        cases hu2 : uniqueCN cb.cn.ctx.once cb.cn.ctx.entryUnique
          (renameL s (X.env cb.cn.xe)) u with
        | false => rfl
        | true => rw [hren hu2] at h2; cases h2
    · exact mem_uni.mpr (Or.inr (mem_renameL.mpr ⟨u, h, rfl⟩))

end comp

/-! ## The engine closure over the written entries -/

/-- THE ENGINE CLOSURE: a worklist `W`, the reached set `R`, the pending written keys `P`, and
the activated keys `A`. A new origin `a` activates each pending key whose origin is a
descendant of `a`, and pushes the content of its cell. The budget is the fuel `n`. -/
def closeE (K : Nat) (E : EState) :
    Nat → List Origin → List Origin → List (Origin × ACell) → List (Origin × ACell) →
      Option (List Origin × List (Origin × ACell))
  | 0, _, _, _, _ => none
  | _ + 1, [], R, _, A => some (R, A)
  | n + 1, a :: W, R, P, A =>
    if a ∈ R then closeE K E n W R P A
    else closeE K E n (uniMap (getH K E) (P.filter (fun k => descB a k.1)) ++ W) (a :: R)
      (P.filter (fun k => !descB a k.1)) (P.filter (fun k => descB a k.1) ++ A)

/-- The invariant of the engine closure for start set `R0` and written keys `P0`. -/
structure CInv (K : Nat) (E : EState) (R0 : List Origin) (P0 : List (Origin × ACell))
    (W R : List Origin) (P A : List (Origin × ACell)) : Prop where
  start : ∀ a ∈ R0, a ∈ R ∨ a ∈ W
  acts : ∀ k ∈ A, ∀ v ∈ getH K E k, v ∈ R ∨ v ∈ W
  pend : ∀ k ∈ P, coveredB R k.1 = false
  part : ∀ k ∈ P0, k ∈ P ∨ k ∈ A
  cov : ∀ k ∈ A, coveredB R k.1 = true
  subP : ∀ k ∈ P, k ∈ P0
  subA : ∀ k ∈ A, k ∈ P0

/-- The invariant holds at the start. -/
theorem CInv.init (K : Nat) (E : EState) (R0 : List Origin) (P0 : List (Origin × ACell)) :
    CInv K E R0 P0 R0 [] P0 [] :=
  ⟨fun _ h => Or.inr h, fun _ h => (by cases h), fun _ _ => rfl, fun _ h => Or.inl h,
   fun _ h => (by cases h), fun _ h => h, fun _ h => (by cases h)⟩

/-- The result of the engine closure: the start set is reached, each activated cell content is
reached, each written key with a covered origin is activated, and each activated key is
covered and written. -/
theorem closeE_spec {K : Nat} {E : EState} {R0 : List Origin} {P0 : List (Origin × ACell)} :
    ∀ (n : Nat) (W R : List Origin) (P A : List (Origin × ACell)) {R' : List Origin}
      {A' : List (Origin × ACell)}, closeE K E n W R P A = some (R', A') →
      CInv K E R0 P0 W R P A →
      (∀ a ∈ R0, a ∈ R') ∧ (∀ k ∈ A', ∀ v ∈ getH K E k, v ∈ R') ∧
      (∀ k ∈ P0, coveredB R' k.1 = true → k ∈ A') ∧ (∀ k ∈ A', coveredB R' k.1 = true) ∧
      (∀ k ∈ A', k ∈ P0)
  | 0, _, _, _, _, _, _, h, _ => by cases h
  | n + 1, [], R, P, A, R', A', h, I => by
    cases h
    refine ⟨fun a ha => ?_, fun k hk v hv => ?_, fun k hk hc => ?_, I.cov, I.subA⟩
    · rcases I.start a ha with h | h
      · exact h
      · cases h
    · rcases I.acts k hk v hv with h | h
      · exact h
      · cases h
    · rcases I.part k hk with h | h
      · rw [I.pend k h] at hc; cases hc
      · exact h
  | n + 1, a :: W, R, P, A, R', A', h, I => by
    unfold closeE at h
    by_cases ha : a ∈ R
    · rw [ite_eq_left ha] at h
      refine closeE_spec n W R P A h ⟨fun b hb => ?_, fun k hk v hv => ?_, I.pend, I.part,
        I.cov, I.subP, I.subA⟩
      · rcases I.start b hb with h1 | h1
        · exact Or.inl h1
        · rcases List.mem_cons.mp h1 with e | e
          · subst e; exact Or.inl ha
          · exact Or.inr e
      · rcases I.acts k hk v hv with h1 | h1
        · exact Or.inl h1
        · rcases List.mem_cons.mp h1 with e | e
          · subst e; exact Or.inl ha
          · exact Or.inr e
    · rw [ite_eq_right ha] at h
      refine closeE_spec n _ _ _ _ h ⟨fun b hb => ?_, fun k hk v hv => ?_, fun k hk => ?_,
        fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
      · rcases I.start b hb with h1 | h1
        · exact Or.inl (List.mem_cons_of_mem _ h1)
        · rcases List.mem_cons.mp h1 with e | e
          · subst e; exact Or.inl List.mem_cons_self
          · exact Or.inr (List.mem_append_right _ e)
      · rcases List.mem_append.mp hk with hN | hA
        · exact Or.inr (List.mem_append_left _ (mem_uniMap.mpr ⟨k, hN, hv⟩))
        · rcases I.acts k hA v hv with h1 | h1
          · exact Or.inl (List.mem_cons_of_mem _ h1)
          · rcases List.mem_cons.mp h1 with e | e
            · subst e; exact Or.inl List.mem_cons_self
            · exact Or.inr (List.mem_append_right _ e)
      · obtain ⟨h1, h2⟩ := List.mem_filter.mp hk
        rw [coveredB_cons, I.pend k h1]
        cases hd : descB a k.1 with
        | false => rfl
        | true => rw [hd] at h2; cases h2
      · rcases I.part k hk with h1 | h1
        · cases hd : descB a k.1 with
          | true => exact Or.inr (List.mem_append_left _ (List.mem_filter.mpr ⟨h1, hd⟩))
          | false => exact Or.inl (List.mem_filter.mpr ⟨h1, by rw [hd]; rfl⟩)
        · exact Or.inr (List.mem_append_right _ h1)
      · rcases List.mem_append.mp hk with hN | hA
        · rw [coveredB_cons, (List.mem_filter.mp hN).2]; rfl
        · rw [coveredB_cons, I.cov k hA, Bool.or_true]
      · exact I.subP k (List.mem_filter.mp hk).1
      · rcases List.mem_append.mp hk with hN | hA
        · exact I.subP k (List.mem_filter.mp hN).1
        · exact I.subA k hA

/-- THE ENGINE CLOSURE IS LEAST: its result is in each set that contains the current sets and
the content of each pending written cell with a covered origin. -/
theorem closeE_least {K : Nat} {E : EState} {C : List Origin} :
    ∀ (n : Nat) (W R : List Origin) (P A : List (Origin × ACell)) {R' : List Origin}
      {A' : List (Origin × ACell)}, closeE K E n W R P A = some (R', A') →
      (∀ a ∈ R, a ∈ C) → (∀ a ∈ W, a ∈ C) →
      (∀ k ∈ P, coveredB C k.1 = true → ∀ v ∈ getH K E k, v ∈ C) → ∀ a ∈ R', a ∈ C
  | 0, _, _, _, _, _, _, h, _, _, _ => by cases h
  | n + 1, [], R, P, A, R', A', h, hR, _, _ => by cases h; exact hR
  | n + 1, a :: W, R, P, A, R', A', h, hR, hW, hP => by
    unfold closeE at h
    by_cases ha : a ∈ R
    · rw [ite_eq_left ha] at h
      exact closeE_least n W R P A h hR (fun b hb => hW b (List.mem_cons_of_mem _ hb)) hP
    · rw [ite_eq_right ha] at h
      have haC : a ∈ C := hW a List.mem_cons_self
      refine closeE_least n _ _ _ _ h ?_ ?_ ?_
      · intro b hb
        rcases List.mem_cons.mp hb with e | e
        · subst e; exact haC
        · exact hR b e
      · intro b hb
        rcases List.mem_append.mp hb with h1 | h1
        · obtain ⟨k, hk, hv⟩ := mem_uniMap.mp h1
          obtain ⟨hk1, hk2⟩ := List.mem_filter.mp hk
          exact hP k hk1 (coveredB_iff.mpr ⟨a, haC, hk2⟩) b hv
        · exact hW b (List.mem_cons_of_mem _ h1)
      · intro k hk hc
        exact hP k (List.mem_filter.mp hk).1 hc

/-! ## The success of the engine closure -/

/-- The length of a union of lists is at most the sum of the lengths. -/
theorem len_uniMap_le {α : Type} (f : α → List Origin) :
    ∀ l : List α, (uniMap f l).length ≤ (l.map (fun a => (f a).length)).sum
  | [] => Nat.le_refl _
  | a :: l => by
    have ih := len_uniMap_le f l
    have hu : ∀ (m n : List Origin), (uni m n).length ≤ m.length + n.length := by
      intro m n
      induction m with
      | nil => show n.length ≤ 0 + n.length; omega
      | cons b m ihm =>
        show (List.insert b (uni m n)).length ≤ _
        have : (List.insert b (uni m n)).length ≤ (uni m n).length + 1 := by
          by_cases hb : b ∈ uni m n
          · rw [List.insert_of_mem hb]; omega
          · rw [List.insert_of_not_mem hb]; simp
        simp only [List.length_cons]
        omega
    show (uni (f a) (uniMap f l)).length ≤ _
    simp only [List.map_cons, List.sum_cons]
    have := hu (f a) (uniMap f l)
    omega

/-- A filter and its complement split a sum. -/
theorem sum_filter_split {α : Type} (g : α → Nat) (p : α → Bool) :
    ∀ l : List α, ((l.filter p).map g).sum + ((l.filter (fun x => !p x)).map g).sum =
      (l.map g).sum
  | [] => rfl
  | a :: l => by
    have ih := sum_filter_split g p l
    cases hp : p a with
    | true =>
      rw [List.filter_cons_of_pos hp, List.filter_cons_of_neg (by rw [hp]; decide)]
      simp only [List.map_cons, List.sum_cons]
      omega
    | false =>
      rw [List.filter_cons_of_neg (by rw [hp]; decide),
        List.filter_cons_of_pos (by rw [hp]; rfl)]
      simp only [List.map_cons, List.sum_cons]
      omega

/-- A filter and its complement split a length. -/
theorem length_filter_split {α : Type} (p : α → Bool) :
    ∀ l : List α, (l.filter p).length + (l.filter (fun x => !p x)).length = l.length
  | [] => rfl
  | a :: l => by
    have ih := length_filter_split p l
    cases hp : p a with
    | true =>
      rw [List.filter_cons_of_pos hp, List.filter_cons_of_neg (by rw [hp]; decide)]
      simp only [List.length_cons]
      omega
    | false =>
      rw [List.filter_cons_of_neg (by rw [hp]; decide),
        List.filter_cons_of_pos (by rw [hp]; rfl)]
      simp only [List.length_cons]
      omega

/-- The measure of the engine closure: the worklist and the contents of the pending cells. -/
def cmeas (K : Nat) (E : EState) (W : List Origin) (P : List (Origin × ACell)) : Nat :=
  W.length + (P.map (fun k => (getH K E k).length)).sum

/-- THE ENGINE CLOSURE ENDS WITHIN ITS MEASURE: a budget above the number of pushes is
enough, so the fallback never runs with this budget. -/
theorem closeE_some {K : Nat} {E : EState} :
    ∀ (n : Nat) (W R : List Origin) (P A : List (Origin × ACell)), cmeas K E W P < n →
      ∃ R' A', closeE K E n W R P A = some (R', A')
  | 0, _, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, [], R, _, A, _ => ⟨R, A, rfl⟩
  | n + 1, a :: W, R, P, A, h => by
    unfold closeE
    by_cases ha : a ∈ R
    · rw [ite_eq_left ha]
      apply closeE_some n W R P A
      unfold cmeas at h ⊢
      simp only [List.length_cons] at h
      omega
    · rw [ite_eq_right ha]
      apply closeE_some n _ _ _ _
      unfold cmeas at h ⊢
      simp only [List.length_cons] at h
      have h1 := len_uniMap_le (getH K E) (P.filter (fun k => descB a k.1))
      have h2 := sum_filter_split (fun k => (getH K E k).length) (fun k => descB a k.1) P
      simp only [List.length_append]
      omega

/-! ## The engine call -/

/-- An origin can be unique by kind: a symbolic origin without an array cell, or an
allocation origin. -/
def canU : Origin → Bool
  | .sym _ q => !(q.contains .elem)
  | .alloc _ => true
  | _ => false

/-- An origin that cannot be unique by kind is not unique. -/
theorem uniqueCN_of_canU {once : Site → Bool} {eu : Bool} {E : List Origin} {u : Origin}
    (h : canU u = false) : uniqueCN once eu E u = false := by
  unfold uniqueCN
  cases u with
  | sym b q =>
    have hq : q.contains .elem = true := by
      cases e : q.contains .elem with
      | false =>
        have h' : (!(q.contains .elem)) = false := h
        rw [e] at h'; cases h'
      | true => rfl
    cases b with
    | root r =>
      show ((eu && !(q.contains .elem)) && !expB E _) = false
      rw [hq]; simp
    | fresh s =>
      show ((eu && once s && !(q.contains .elem)) && !expB E _) = false
      rw [hq]; simp
  | alloc _ => cases h
  | deep _ => rfl
  | havoc _ => rfl
  | hsym _ _ _ _ => rfl
  | hdeep _ _ _ => rfl

/-- The start set of the engine call: the start set of the model. -/
def startE (cb : CtxB) (E : EState) (args : List Var) : List Origin :=
  callRoots cb.cn (den cb.cn.ctx.K E) args

/-- The `Eval` contribution of the activated keys: their contents that can be unique. -/
def valsE (K : Nat) (E : EState) (A : List (Origin × ACell)) : List Origin :=
  uniMap (fun k => (getH K E k).filter canU) A

/-- Add `T` to `Etree` and `V` to `Eval`. -/
def setsE (cb : CtxB) (E : EState) (T V : List Origin) : EState :=
  putV (putV E cb.cn.xe (uni T (getE E cb.cn.xe))) cb.xv (uni V (getE E cb.xv))

/-- THE ENGINE CALL: the closure over the written entries with budget `B`; `Etree` gets the
symbolic origins of `R`, `Eval` gets the contents of the activated entries that can be unique.
If the budget runs out, both sets get every universe origin. No heap entry changes. -/
def callE (cb : CtxB) (B : Nat) (E : EState) (args : List Var) : EState :=
  match closeE cb.cn.ctx.K E B (startE cb E args) [] (keys E.heap) [] with
  | some (R, A) => setsE cb E (R.filter isSymB) (valsE cb.cn.ctx.K E A)
  | none => setsE cb E cb.cn.ctx.origins cb.cn.ctx.origins

/-- `setsE` keeps the normal form. -/
theorem NF_setsE (cb : CtxB) {E : EState} (h : NF cb.cn.ctx.K E) (T V : List Origin) :
    NF cb.cn.ctx.K (setsE cb E T V) :=
  NF_putV (NF_putV h _ _) _ _

/-- The engine call keeps the normal form. -/
theorem NF_callE (cb : CtxB) (B : Nat) {E : EState} (h : NF cb.cn.ctx.K E) (args : List Var) :
    NF cb.cn.ctx.K (callE cb B E args) := by
  unfold callE
  split
  · exact NF_setsE cb h _ _
  · exact NF_setsE cb h _ _

/-- `setsE` denotes `setSets`. -/
theorem den_setsE {cb : CtxB} (hx : cb.xv ≠ cb.cn.xe) (E : EState) (T V : List Origin) :
    DEq (den cb.cn.ctx.K (setsE cb E T V)) (setSets cb (den cb.cn.ctx.K E) T V) := by
  refine ⟨fun x => ?_, fun o c => SetEq.refl _⟩
  show SetEq (getE (setsE cb E T V) x)
    (fupd (fupd (getE E) cb.cn.xe (uni T (getE E cb.cn.xe))) cb.xv (uni V (getE E cb.xv)) x)
  unfold setsE
  by_cases e1 : x = cb.xv
  · subst e1; rw [getE_putV_same, fupd_same]; exact SetEq.refl _
  · rw [getE_putV_ne _ _ e1, fupd_ne _ _ e1]
    by_cases e2 : x = cb.cn.xe
    · subst e2; rw [getE_putV_same, fupd_same]; exact SetEq.refl _
    · rw [getE_putV_ne _ _ e2, fupd_ne _ _ e2]; exact SetEq.refl _

/-- The engine call does not change the heap. -/
theorem getH_callE (cb : CtxB) (B : Nat) (E : EState) (args : List Var) (k : Origin × ACell) :
    getH cb.cn.ctx.K (callE cb B E args) k = getH cb.cn.ctx.K E k := by
  unfold callE
  split <;> rfl

/-! ## The model side of the call -/

/-- `uniMap` depends only on the values on the list. -/
theorem uniMap_congr {α : Type} {f g : α → List Origin} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → uniMap f l = uniMap g l
  | [], _ => rfl
  | a :: l, h => by
    show uni (f a) (uniMap f l) = uni (g a) (uniMap g l)
    rw [h a List.mem_cons_self, uniMap_congr (fun b hb => h b (List.mem_cons_of_mem _ hb))]

/-- The model closure reads only the heap: it is the same on the completed state. -/
theorem closeN_comp (cb : CtxB) (X : AState) :
    ∀ (n : Nat) (R : List Origin), closeN cb.cn (comp cb X) n R = closeN cb.cn X n R
  | 0, _ => rfl
  | n + 1, R => by
    show (if subB (succsN cb.cn X R) R then some R
        else closeN cb.cn (comp cb X) n (uni (succsN cb.cn X R) R)) =
      (if subB (succsN cb.cn X R) R then some R
        else closeN cb.cn X n (uni (succsN cb.cn X R) R))
    rw [closeN_comp cb X n]

/-- The model start set is the same on the completed state, for arguments that are not
reserved. -/
theorem callRoots_comp (cb : CtxB) (X : AState) {args : List Var}
    (h : ∀ a ∈ args, a ≠ cb.cn.xe ∧ a ≠ cb.xv) :
    callRoots cb.cn (comp cb X) args = callRoots cb.cn X args := by
  unfold callRoots
  rw [uniMap_congr (fun a ha => comp_ne X (h a ha).1 (h a ha).2)]

/-- `succsN` is monotone in the reached set. -/
theorem succsN_mono {cn : CtxN} {X : AState} {R R' : List Origin} (h : ∀ a ∈ R, a ∈ R') :
    ∀ v ∈ succsN cn X R, v ∈ succsN cn X R' := by
  intro v hv
  obtain ⟨u, hu, hc, c, hcc, hv'⟩ := mem_succsN.mp hv
  exact mem_succsN.mpr ⟨u, hu, coveredB_mono h hc, c, hcc, hv'⟩

/-- THE MODEL CLOSURE IS LEAST: its result is in each set that contains the start set and is
closed under `succsN`. -/
theorem closeN_least {cn : CtxN} {X : AState} {C : List Origin}
    (hC : ∀ v ∈ succsN cn X C, v ∈ C) :
    ∀ (n : Nat) {R0 R : List Origin}, closeN cn X n R0 = some R → (∀ a ∈ R0, a ∈ C) →
      ∀ a ∈ R, a ∈ C
  | 0, _, _, h, _ => by cases h
  | n + 1, R0, R, h, h0 => by
    unfold closeN at h
    split at h
    · cases h; exact h0
    · refine closeN_least hC n h ?_
      intro a ha
      rcases mem_uni.mp ha with h1 | h1
      · exact hC a (succsN_mono h0 a h1)
      · exact h0 a h1

/-- The cell name of a covered origin is not unique for a set that holds the symbolic origins
of the reached set. -/
theorem uniqueCN_child {once : Site → Bool} {eu : Bool} {K : Nat} {R T : List Origin}
    (hT : ∀ a ∈ R, isSymB a = true → a ∈ T) {u : Origin} (hu : coveredB R u = true) (c : ACell) :
    uniqueCN once eu T (childCN K u c) = false := by
  cases u with
  | sym b q =>
    obtain ⟨a, ha, hd⟩ := coveredB_iff.mp hu
    obtain ⟨p, rfl, hp⟩ := descB_sym_inv hd
    show uniqueCN once eu T (symOrDeep K b (q ++ [c])) = false
    unfold symOrDeep
    split
    · have he : expB T (.sym b (q ++ [c])) = true := by
        refine expB_of (hT _ ha rfl) ?_ (preB_append hp _)
        have := preB_len hp
        rw [List.length_append]
        simp only [List.length_cons, List.length_nil]
        omega
      unfold uniqueCN; rw [he]; simp
    · rfl
  | deep _ => rfl
  | alloc _ => rfl
  | havoc _ => rfl
  | hsym s k c' q =>
    show uniqueCN once eu T (if (q ++ [c]).length ≤ K then .hsym s k c' (q ++ [c])
      else .hdeep s k c') = false
    split <;> rfl
  | hdeep _ _ _ => rfl

section call

variable {cb : CtxB}

/-- The facts of the engine call when its closure succeeds: the model closure `RM`, the engine
closure `RE` and its activated keys `A`. -/
theorem call_facts (hc : CtxBOK cb) {E : EState} (hs : Supp cb.cn.ctx (den cb.cn.ctx.K E))
    (hk : ∀ k ∈ keys E.heap, k.1 ∈ cb.cn.ctx.origins ∧ k.2 ∈ cb.cn.ctx.cells)
    {R0 RM RE : List Origin} {A : List (Origin × ACell)} {n m : Nat}
    (hM : closeN cb.cn (den cb.cn.ctx.K E) m R0 = some RM)
    (hE : closeE cb.cn.ctx.K E n R0 [] (keys E.heap) [] = some (RE, A)) :
    (∀ a ∈ RE, a ∈ RM) ∧
    (∀ a ∈ RM, a ∈ RE ∨ (a ∈ cb.cn.ctx.origins ∧ coveredB RE a = true)) ∧
    (∀ u, coveredB RM u = true → coveredB RE u = true) ∧
    (∀ k ∈ keys E.heap, coveredB RE k.1 = true → k ∈ A) ∧
    (∀ k ∈ A, ∀ v ∈ getH cb.cn.ctx.K E k, v ∈ RE) := by
  have spec := closeE_spec (R0 := R0) (P0 := keys E.heap) n R0 [] (keys E.heap) [] hE
    (CInv.init _ _ _ _)
  obtain ⟨sp1, sp2, sp3, _, _⟩ := spec
  have specM := closeN_spec hM
  -- the engine result is in the model result
  have h1 : ∀ a ∈ RE, a ∈ RM := by
    refine closeE_least n R0 [] (keys E.heap) [] hE (fun _ h => by cases h) specM.1 ?_
    intro k hkm hcov v hv
    exact specM.2 v (mem_succsN.mpr ⟨k.1, (hk k hkm).1, hcov, k.2, (hk k hkm).2, hv⟩)
  -- the covered test of the completed engine set is the covered test of the engine set
  let C := uni RE (cb.cn.ctx.origins.filter (coveredB RE))
  have hCcov : ∀ u, coveredB C u = true → coveredB RE u = true := by
    intro u hu
    obtain ⟨a, ha, hd⟩ := coveredB_iff.mp hu
    rcases mem_uni.mp ha with h | h
    · exact coveredB_iff.mpr ⟨a, h, hd⟩
    · obtain ⟨a', ha', hd'⟩ := coveredB_iff.mp (List.mem_filter.mp h).2
      exact coveredB_iff.mpr ⟨a', ha', descB_trans hd' hd⟩
  have hC : ∀ v ∈ succsN cb.cn (den cb.cn.ctx.K E) C, v ∈ C := by
    intro v hv
    obtain ⟨u, hu, hcov, c, hcc, hv'⟩ := mem_succsN.mp hv
    have hcovE := hCcov u hcov
    by_cases hw : (u, c) ∈ keys E.heap
    · exact mem_uni.mpr (Or.inl (sp2 _ (sp3 _ hw hcovE) v hv'))
    · have e : (den cb.cn.ctx.K E).heap u c = [childCN cb.cn.ctx.K u c] := by
        show getH cb.cn.ctx.K E (u, c) = _
        unfold getH; rw [look_none_of hw]; rfl
      rw [e, List.mem_singleton] at hv'
      subst hv'
      refine mem_uni.mpr (Or.inr (List.mem_filter.mpr ⟨hc.cn.childIn u hu c hcc, ?_⟩))
      obtain ⟨a, ha, hd⟩ := coveredB_iff.mp hcovE
      exact coveredB_iff.mpr ⟨a, ha, descB_child _ c hd⟩
  have h2 : ∀ a ∈ RM, a ∈ C := closeN_least hC m hM (fun a ha => mem_uni.mpr (Or.inl (sp1 a ha)))
  refine ⟨h1, fun a ha => ?_, fun u hu => ?_, sp3, sp2⟩
  · rcases mem_uni.mp (h2 a ha) with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_filter.mp h)
  · obtain ⟨a, ha, hd⟩ := coveredB_iff.mp hu
    exact hCcov u (coveredB_iff.mpr ⟨a, h2 a ha, hd⟩)

/-- (b) THE ENGINE CLOSURE COVERS THE SAME ORIGINS AS THE MODEL CLOSURE. -/
theorem closure_cover_eq (hc : CtxBOK cb) {E : EState} (hs : Supp cb.cn.ctx (den cb.cn.ctx.K E))
    (hk : ∀ k ∈ keys E.heap, k.1 ∈ cb.cn.ctx.origins ∧ k.2 ∈ cb.cn.ctx.cells)
    {R0 RM RE : List Origin} {A : List (Origin × ACell)} {n m : Nat}
    (hM : closeN cb.cn (den cb.cn.ctx.K E) m R0 = some RM)
    (hE : closeE cb.cn.ctx.K E n R0 [] (keys E.heap) [] = some (RE, A)) (u : Origin) :
    coveredB RE u = coveredB RM u := by
  obtain ⟨h1, _, h3, _, _⟩ := call_facts hc hs hk hM hE
  cases e : coveredB RM u with
  | true => exact h3 u e
  | false =>
    cases e2 : coveredB RE u with
    | false => rfl
    | true => rw [coveredB_mono h1 e2] at e; cases e

/-- The set relation of a call: if the model sets are in the completed engine sets, the model
call on the completed state is `Le` the completion of the engine call. -/
theorem setsE_le (hx : cb.xv ≠ cb.cn.xe) (E : EState) {RM VM T V : List Origin}
    (hT : ∀ a ∈ RM, a ∈ compE cb (uni T (getE E cb.cn.xe)))
    (hV : ∀ a ∈ VM, a ∈ compV cb (uni T (getE E cb.cn.xe)) (uni V (getE E cb.xv))) :
    Le cb (setSets cb (comp cb (den cb.cn.ctx.K E)) RM VM)
      (comp cb (den cb.cn.ctx.K (setsE cb E T V))) := by
  have hd := (den_setsE (cb := cb) hx E T V).comp hx
  refine Le.trans ?_ (Le.of_deq hd.symm)
  have sx : ∀ (Y : AState) (R V' : List Origin), (setSets cb Y R V').env cb.cn.xe =
      uni R (Y.env cb.cn.xe) := by
    intro Y R V'
    show fupd (fupd Y.env _ _) cb.xv _ cb.cn.xe = _
    rw [fupd_ne _ _ (fun h => hx h.symm), fupd_same]
  have sv : ∀ (Y : AState) (R V' : List Origin), (setSets cb Y R V').env cb.xv =
      uni V' (Y.env cb.xv) := by
    intro Y R V'
    show fupd (fupd Y.env _ _) cb.xv _ cb.xv = _
    rw [fupd_same]
  have sn : ∀ (Y : AState) (R V' : List Origin) (x : Var), x ≠ cb.cn.xe → x ≠ cb.xv →
      (setSets cb Y R V').env x = Y.env x := by
    intro Y R V' x e1 e2
    show fupd (fupd Y.env _ _) cb.xv _ x = _
    rw [fupd_ne _ _ e2, fupd_ne _ _ e1]
  refine ⟨fun x e1 e2 => ?_, fun o c => SetEq.refl _, ?_, ?_⟩
  · rw [sn _ _ _ x e1 e2, comp_ne _ e1 e2, comp_ne _ e1 e2, sn _ _ _ x e1 e2]
    exact SetEq.refl _
  · rw [sx, comp_xe hx, comp_xe hx, sx]
    intro a ha
    rcases mem_uni.mp ha with h | h
    · exact hT a h
    · exact compE_mono (fun b hb => mem_uni.mpr (Or.inr hb)) a h
  · rw [sv, comp_xv, comp_xv, sv, sx]
    intro a ha
    rcases mem_uni.mp ha with h | h
    · exact hV a h
    · exact compV_mono (fun b hb => mem_uni.mpr (Or.inr hb)) (fun b hb => mem_uni.mpr (Or.inr hb))
        a h

/-- (b) THE CALL BRIDGE: the model call on the completed denotation is `Le` the completion of
the engine call, for an engine state with support and universe keys, and arguments that are
universe variables and not reserved. -/
theorem call_bridge (hc : CtxBOK cb) (B : Nat) {E : EState}
    (hs : Supp cb.cn.ctx (den cb.cn.ctx.K E))
    (hk : ∀ k ∈ keys E.heap, k.1 ∈ cb.cn.ctx.origins ∧ k.2 ∈ cb.cn.ctx.cells) {args : List Var}
    (hargs : ∀ a ∈ args, a ∈ cb.cn.ctx.vars ∧ a ≠ cb.cn.xe ∧ a ≠ cb.xv) :
    Le cb (callVS cb (comp cb (den cb.cn.ctx.K E)) args)
      (comp cb (den cb.cn.ctx.K (callE cb B E args))) := by
  have hx := hc.xvNe
  have hroots := callRoots_sub hc hs (fun a ha => (hargs a ha).1)
  obtain ⟨RM, hM⟩ := closeN_some_top hs hroots
  have hcall : callVS cb (comp cb (den cb.cn.ctx.K E)) args =
      setSets cb (comp cb (den cb.cn.ctx.K E)) RM (succsN cb.cn (den cb.cn.ctx.K E) RM) := by
    unfold callVS
    rw [callRoots_comp cb _ (fun a ha => (hargs a ha).2), closeN_comp, hM]
    rfl
  rw [hcall]
  have hRMU : ∀ a ∈ RM, a ∈ cb.cn.ctx.origins := Opt.CellNamed.closeN_sub hs hroots hM
  have hVMU := Opt.CellNamed.succsN_sub hs RM
  unfold callE
  split
  · rename_i RE A hE
    obtain ⟨_, h2, h3, h4, _⟩ := call_facts hc hs hk hM hE
    have hT : ∀ a ∈ RE, isSymB a = true → a ∈ uni (RE.filter isSymB) (getE E cb.cn.xe) :=
      fun a ha hsym => mem_uni.mpr (Or.inl (List.mem_filter.mpr ⟨ha, hsym⟩))
    apply setsE_le hx E
    · intro a ha
      unfold compE
      by_cases hsym : isSymB a = true
      · rcases h2 a ha with hE' | ⟨hU, hcov⟩
        · exact mem_uni.mpr (Or.inr (hT a hE' hsym))
        · obtain ⟨a', ha', hd⟩ := coveredB_iff.mp hcov
          cases a with
          | sym b q =>
            obtain ⟨p, rfl, hp⟩ := descB_sym_inv hd
            by_cases hl : p.length = q.length
            · rw [preB_eq hp hl] at ha'
              exact mem_uni.mpr (Or.inr (hT _ ha' rfl))
            · have hlt : p.length < q.length := Nat.lt_of_le_of_ne (preB_len hp) hl
              have he := expB_of (hT _ ha' rfl) hlt hp
              refine mem_uni.mpr (Or.inl (List.mem_filter.mpr ⟨hU, ?_⟩))
              unfold blkT uniqueCN; rw [he]; simp
          | _ => cases hsym
      · refine mem_uni.mpr (Or.inl (List.mem_filter.mpr ⟨hRMU a ha, ?_⟩))
        unfold blkT
        cases e : isSymB a with
        | false => rfl
        | true => exact absurd e hsym
    · intro v hv
      obtain ⟨u, hu, hcov, c, hcc, hv'⟩ := mem_succsN.mp hv
      have hcovE := h3 u hcov
      unfold compV
      by_cases hw : (u, c) ∈ keys E.heap
      · cases hcu : canU v with
        | true =>
          refine mem_uni.mpr (Or.inr (mem_uni.mpr (Or.inl ?_)))
          exact mem_uniMap.mpr ⟨(u, c), h4 _ hw hcovE, List.mem_filter.mpr ⟨hv', hcu⟩⟩
        | false =>
          refine mem_uni.mpr (Or.inl (List.mem_filter.mpr ⟨hVMU hv, ?_⟩))
          unfold blkV; rw [uniqueCN_of_canU hcu]; rfl
      · have e : (den cb.cn.ctx.K E).heap u c = [childCN cb.cn.ctx.K u c] := by
          show getH cb.cn.ctx.K E (u, c) = _
          unfold getH; rw [look_none_of hw]; rfl
        rw [e, List.mem_singleton] at hv'
        subst hv'
        refine mem_uni.mpr (Or.inl (List.mem_filter.mpr ⟨hc.cn.childIn u hu c hcc, ?_⟩))
        unfold blkV; rw [uniqueCN_child hT hcovE c]; rfl
  · apply setsE_le hx E
    · intro a ha
      exact sub_compE _ a (mem_uni.mpr (Or.inl (hRMU a ha)))
    · intro v hv
      exact sub_compV _ _ v (mem_uni.mpr (Or.inl (hVMU hv)))

end call

/-! ## The engine transfer and the bridge -/

/-- The engine transfer of one statement of design VS; `i` is the null site of a null
statement, `B` the budget of the call closure. -/
def astepE (cb : CtxB) (B : Nat) (i : Nat) : Stmt → EState → EState
  | .new x s, E => putV (retireE cb.cn.ctx.K s E) x [rNew s]
  | .null x, E => putV E x [nullO i]
  | .copy x y, E => putV E x (getE E y)
  | .load x y f, E => putV E x (readE cb.cn.ctx.K E (getE E y) (.fld f))
  | .store x f y, E => storeE cb E x (.fld f) (getE E y)
  | .aload x y, E => putV E x (readE cb.cn.ctx.K E (getE E y) .elem)
  | .astore x y, E => weakE cb.cn.ctx.K .elem (getE E y) E (getE E x)
  | .unknown x s, E => putV (retireE cb.cn.ctx.K s E) x [.sym (.fresh s) []]
  | .call ret s args, E =>
    setRetE (retireE cb.cn.ctx.K s (callE cb B E args)) ret [.sym (.fresh s) []]

/-- The engine transfer keeps the normal form. -/
theorem NF_astepE (cb : CtxB) (B i : Nat) {E : EState} (h : NF cb.cn.ctx.K E) :
    ∀ st : Stmt, NF cb.cn.ctx.K (astepE cb B i st E)
  | .new x s => NF_putV (NF_retireE h s) _ _
  | .null x => NF_putV h _ _
  | .copy x y => NF_putV h _ _
  | .load x y f => NF_putV h _ _
  | .store x f y => NF_storeE cb h _ _ _
  | .aload x y => NF_putV h _ _
  | .astore x y => NF_weakE _ _ _ h
  | .unknown x s => NF_putV (NF_retireE h s) _ _
  | .call ret s args => NF_setRetE (NF_retireE (NF_callE cb B h args) s) _ _

/-- EACH ENGINE STEP BUT THE CALL COMMUTES WITH THE DENOTATION: it is the step of design VS. -/
theorem den_astepE (cb : CtxB) (B i : Nat) (E : EState) :
    ∀ st : Stmt, st.callSite? = none →
      DEq (den cb.cn.ctx.K (astepE cb B i st E)) (astepVS cb i st (den cb.cn.ctx.K E))
  | .new x s, _ => (den_putV _ _ x _).trans ((den_retireE _ s E).setVar x (SetEq.refl _))
  | .null x, _ => den_putV _ _ x _
  | .copy x y, _ => den_putV _ _ x _
  | .load x y f, _ => den_putV _ _ x _
  | .store x f y, _ => den_storeE cb E x _ _
  | .aload x y, _ => den_putV _ _ x _
  | .astore x y, _ => den_weakE _ _ _ E _
  | .unknown x s, _ => (den_putV _ _ x _).trans ((den_retireE _ s E).setVar x (SetEq.refl _))
  | .call _ _ _, h => by cases h

section bridge

variable {cb : CtxB}

/-- The completion commutes with `setVar` of a variable that is not reserved. -/
theorem comp_setVar (hx : cb.xv ≠ cb.cn.xe) (X : AState) {x : Var} (h1 : x ≠ cb.cn.xe)
    (h2 : x ≠ cb.xv) (S : List Origin) : DEq ((comp cb X).setVar x S) (comp cb (X.setVar x S)) := by
  refine ⟨fun y => ?_, fun o c => SetEq.refl _⟩
  have hxe : (X.setVar x S).env cb.cn.xe = X.env cb.cn.xe := fupd_ne _ _ (fun e => h1 e.symm)
  have hxv : (X.setVar x S).env cb.xv = X.env cb.xv := fupd_ne _ _ (fun e => h2 e.symm)
  show SetEq (fupd (comp cb X).env x S y) ((comp cb (X.setVar x S)).env y)
  by_cases e1 : y = cb.cn.xe
  · subst e1
    rw [fupd_ne _ _ (fun e => h1 e.symm), comp_xe hx, comp_xe hx, hxe]
    exact SetEq.refl _
  · by_cases e2 : y = cb.xv
    · subst e2
      rw [fupd_ne _ _ (fun e => h2 e.symm), comp_xv, comp_xv, hxe, hxv]
      exact SetEq.refl _
    · rw [comp_ne _ e1 e2]
      by_cases e : y = x
      · subst e
        rw [fupd_same]
        show SetEq S (fupd X.env y S y)
        rw [fupd_same]; exact SetEq.refl _
      · rw [fupd_ne _ _ e, comp_ne _ e1 e2]
        show SetEq (X.env y) (fupd X.env x S y)
        rw [fupd_ne _ _ e]; exact SetEq.refl _

/-- The completion commutes with `setRet` of a result variable that is not reserved. -/
theorem comp_setRet (hx : cb.xv ≠ cb.cn.xe) (X : AState) {r : Option Var}
    (hr : ∀ x, r = some x → x ≠ cb.cn.xe ∧ x ≠ cb.xv) (S : List Origin) :
    DEq ((comp cb X).setRet r S) (comp cb (X.setRet r S)) := by
  cases r with
  | none => exact DEq.refl _
  | some x => exact comp_setVar hx X (hr x rfl).1 (hr x rfl).2 S

/-- The completion commutes with the store of design BO. -/
theorem comp_storeBO (hx : cb.xv ≠ cb.cn.xe) (X : AState) {x : Var} (h1 : x ≠ cb.cn.xe)
    (h2 : x ≠ cb.xv) (c : ACell) (S : List Origin) :
    storeBO cb (comp cb X) x c S = comp cb (storeBO cb X x c S) := by
  unfold storeBO
  rw [comp_ne X h1 h2]
  cases single? (X.env x) with
  | none => rfl
  | some o =>
    simp only
    rw [uniqueBO_comp hx X o]
    split <;> rfl

/-- One statement of design VS, but the call, on the completed state is `Le` the completion
of the statement, for a statement whose variables are not reserved. -/
theorem astepVS_comp_le (hc : CtxBOK cb) (i : Nat) (X : AState) :
    ∀ st : Stmt, st.callSite? = none → (∀ x ∈ st.vars, x ≠ cb.cn.xe ∧ x ≠ cb.xv) →
      Le cb (astepVS cb i st (comp cb X)) (comp cb (astepVS cb i st X))
  | .new x s, _, hv => by
    have h := hv x List.mem_cons_self
    exact ((retireV_comp_le hc X s).setVar h.1 h.2 (SetEq.refl _)).trans
      (Le.of_deq (comp_setVar hc.xvNe _ h.1 h.2 _))
  | .null x, _, hv => by
    have h := hv x List.mem_cons_self
    exact Le.of_deq (comp_setVar hc.xvNe X h.1 h.2 _)
  | .copy x y, _, hv => by
    have h := hv x List.mem_cons_self
    have h' := hv y (List.mem_cons_of_mem _ List.mem_cons_self)
    show Le cb ((comp cb X).setVar x ((comp cb X).env y)) (comp cb (X.setVar x (X.env y)))
    rw [comp_ne X h'.1 h'.2]
    exact Le.of_deq (comp_setVar hc.xvNe X h.1 h.2 _)
  | .load x y f, _, hv => by
    have h := hv x List.mem_cons_self
    have h' := hv y (List.mem_cons_of_mem _ List.mem_cons_self)
    show Le cb ((comp cb X).setVar x (DirectedAlias.aread (comp cb X) ((comp cb X).env y) _))
      (comp cb (X.setVar x (DirectedAlias.aread X (X.env y) _)))
    rw [comp_ne X h'.1 h'.2]
    exact Le.of_deq (comp_setVar hc.xvNe X h.1 h.2 _)
  | .store x f y, _, hv => by
    have h := hv x List.mem_cons_self
    have h' := hv y (List.mem_cons_of_mem _ List.mem_cons_self)
    show Le cb (storeBO cb (comp cb X) x _ ((comp cb X).env y)) (comp cb (storeBO cb X x _ (X.env y)))
    rw [comp_ne X h'.1 h'.2, comp_storeBO hc.xvNe X h.1 h.2]
    exact Le.refl _
  | .aload x y, _, hv => by
    have h := hv x List.mem_cons_self
    have h' := hv y (List.mem_cons_of_mem _ List.mem_cons_self)
    show Le cb ((comp cb X).setVar x (DirectedAlias.aread (comp cb X) ((comp cb X).env y) _))
      (comp cb (X.setVar x (DirectedAlias.aread X (X.env y) _)))
    rw [comp_ne X h'.1 h'.2]
    exact Le.of_deq (comp_setVar hc.xvNe X h.1 h.2 _)
  | .astore x y, _, hv => by
    have h := hv x List.mem_cons_self
    have h' := hv y (List.mem_cons_of_mem _ List.mem_cons_self)
    show Le cb ((comp cb X).weakStore ((comp cb X).env x) _ ((comp cb X).env y))
      (comp cb (X.weakStore (X.env x) _ (X.env y)))
    rw [comp_ne X h'.1 h'.2, comp_ne X h.1 h.2]
    exact Le.refl _
  | .unknown x s, _, hv => by
    have h := hv x List.mem_cons_self
    exact ((retireV_comp_le hc X s).setVar h.1 h.2 (SetEq.refl _)).trans
      (Le.of_deq (comp_setVar hc.xvNe _ h.1 h.2 _))
  | .call _ _ _, h, _ => by cases h

/-- (c) THE BRIDGE: for each statement whose variables are universe variables and not reserved,
and each engine state whose denotation has support and whose heap keys are universe keys, the
model step on the completed denotation is `Le` the completion of the engine step: set-equal env
outside the reserved keys, set-equal heap, and the model sets in the completed engine sets. -/
theorem bridge (hc : CtxBOK cb) (B i : Nat) {E : EState}
    (hs : Supp cb.cn.ctx (den cb.cn.ctx.K E))
    (hk : ∀ k ∈ keys E.heap, k.1 ∈ cb.cn.ctx.origins ∧ k.2 ∈ cb.cn.ctx.cells) (st : Stmt)
    (hv : ∀ x ∈ st.vars, x ∈ cb.cn.ctx.vars ∧ x ≠ cb.cn.xe ∧ x ≠ cb.xv) :
    Le cb (astepVS cb i st (comp cb (den cb.cn.ctx.K E)))
      (comp cb (den cb.cn.ctx.K (astepE cb B i st E))) := by
  have hx := hc.xvNe
  cases hst : st.callSite? with
  | none =>
    exact (astepVS_comp_le hc i _ st hst (fun x hx' => (hv x hx').2)).trans
      (Le.of_deq ((den_astepE cb B i E st hst).comp hx).symm)
  | some s0 =>
    cases st with
    | call ret s args =>
      have hargs : ∀ a ∈ args, a ∈ cb.cn.ctx.vars ∧ a ≠ cb.cn.xe ∧ a ≠ cb.xv :=
        fun a ha => hv a (List.mem_append_right _ ha)
      have hr : ∀ x, ret = some x → x ≠ cb.cn.xe ∧ x ≠ cb.xv := by
        intro x e
        subst e
        exact (hv x (List.mem_append_left _ List.mem_cons_self)).2
      show Le cb ((DirectedAlias.Sound.ValueSem.retireV cb.cn.ctx.K s
          (callVS cb (comp cb (den cb.cn.ctx.K E)) args)).setRet ret _)
        (comp cb (den cb.cn.ctx.K (setRetE (retireE cb.cn.ctx.K s (callE cb B E args)) ret _)))
      have e1 := (call_bridge hc B hs hk hargs).retireV cb.cn.ctx.K s
      have e2 := retireV_comp_le hc (den cb.cn.ctx.K (callE cb B E args)) s
      have e3 : DEq (den cb.cn.ctx.K (setRetE (retireE cb.cn.ctx.K s (callE cb B E args)) ret
          [.sym (.fresh s) []]))
          ((DirectedAlias.Sound.ValueSem.retireV cb.cn.ctx.K s
            (den cb.cn.ctx.K (callE cb B E args))).setRet ret [.sym (.fresh s) []]) :=
        (den_setRetE _ _ ret _).trans ((den_retireE _ s _).setRet ret _)
      refine ((e1.trans e2).setRet hr _).trans ?_
      refine (Le.of_deq (comp_setRet hx _ hr _)).trans ?_
      exact Le.of_deq (e3.comp hx).symm
    | _ => cases hst

/-- (c) THE JOIN BRIDGE: the join of the completed denotations is set-equal to the completion
of the denotation of the engine join. -/
theorem join_bridge (hc : CtxBOK cb) (E1 E2 : EState) :
    DEq (join (comp cb (den cb.cn.ctx.K E1)) (comp cb (den cb.cn.ctx.K E2)))
      (comp cb (den cb.cn.ctx.K (joinE cb.cn.ctx.K E1 E2))) :=
  (comp_join hc.xvNe _ _).symm.trans ((den_joinE _ E1 E2).comp hc.xvNe).symm

/-- The join bridge as `Le`. -/
theorem join_bridge_le (hc : CtxBOK cb) (E1 E2 : EState) :
    Le cb (join (comp cb (den cb.cn.ctx.K E1)) (comp cb (den cb.cn.ctx.K E2)))
      (comp cb (den cb.cn.ctx.K (joinE cb.cn.ctx.K E1 E2))) :=
  Le.of_deq (join_bridge hc E1 E2)

/-- The engine change test of a head: if the join of the head with the body result has the map
of the head, the body result is included in the head. -/
theorem fix_of_mapEqB {K : Nat} {E F : EState} (hE : NF K E)
    (h : mapEqB (joinE K E F) E = true) : (den K F).Sub (den K E) := by
  have hd := (mapEqB_iff_den (NF_joinE K E F) hE).mp h
  have hj := den_joinE K E F
  exact ⟨fun x a ha => (hd.1 x a).mp ((hj.1 x a).mpr (mem_uni.mpr (Or.inr ha))),
    fun o c a ha => (hd.2 o c a).mp ((hj.2 o c a).mpr (mem_uni.mpr (Or.inr ha)))⟩

/-- AN ENGINE POST-FIXPOINT IS A MODEL POST-FIXPOINT: if the model body on the completed
denotation is `Le` the completion of the engine body, and the engine change test says that the
head is stable, then the completed denotation of the head is a model post-fixpoint. -/
theorem post_fixpoint (hc : CtxBOK cb) {F : AState → AState} {G : EState → EState}
    {E : EState} (hE : NF cb.cn.ctx.K E)
    (hb : Le cb (F (comp cb (den cb.cn.ctx.K E))) (comp cb (den cb.cn.ctx.K (G E))))
    (hfix : mapEqB (joinE cb.cn.ctx.K E (G E)) E = true) :
    (F (comp cb (den cb.cn.ctx.K E))).Sub (comp cb (den cb.cn.ctx.K E)) ∧
      leOn cb.cn.ctx (F (comp cb (den cb.cn.ctx.K E))) (comp cb (den cb.cn.ctx.K E)) = true := by
  have h := hb.sub.trans (comp_mono hc.xvNe (fix_of_mapEqB hE hfix))
  refine ⟨h, leOn_iff.mpr ⟨fun x _ => h.1 x, fun o _ c _ => h.2 o c⟩⟩

/-- The answers of `Le`-related states are equal for variables that are not reserved. -/
theorem may_le {X Y : AState} (h : Le cb X Y) {x y : Var} (hx1 : x ≠ cb.cn.xe)
    (hx2 : x ≠ cb.xv) (hy1 : y ≠ cb.cn.xe) (hy2 : y ≠ cb.xv) (px py : List ACell) :
    may X x px y py = may Y x px y py := by
  have hread : ∀ (p : List ACell) (S S' : List Origin), SetEq S S' →
      SetEq (aevalFrom X S p) (aevalFrom Y S' p) := by
    intro p
    induction p with
    | nil => intro S S' h; exact h
    | cons c p ih =>
      intro S S' hS
      apply ih
      intro a
      rw [mem_aread, mem_aread]
      constructor
      · rintro ⟨o, ho, ha⟩; exact ⟨o, (hS o).mp ho, (h.heap o c a).mp ha⟩
      · rintro ⟨o, ho, ha⟩; exact ⟨o, (hS o).mpr ho, (h.heap o c a).mpr ha⟩
  have h1 := hread px _ _ (h.env x hx1 hx2)
  have h2 := hread py _ _ (h.env y hy1 hy2)
  unfold may aevalPath
  cases e : meetB (aevalFrom Y (Y.env x) px) (aevalFrom Y (Y.env y) py) with
  | true =>
    obtain ⟨a, ha1, ha2⟩ := meetB_iff.mp e
    exact meetB_iff.mpr ⟨a, (h1 a).mpr ha1, (h2 a).mpr ha2⟩
  | false =>
    cases e2 : meetB (aevalFrom X (X.env x) px) (aevalFrom X (X.env y) py) with
    | false => rfl
    | true =>
      obtain ⟨a, ha1, ha2⟩ := meetB_iff.mp e2
      rw [meetB_iff.mpr ⟨a, (h1 a).mp ha1, (h2 a).mp ha2⟩] at e
      cases e

/-- THE ANSWERS ARE EQUAL: a may-alias query of variables that are not reserved has the same
answer on the completed state. -/
theorem may_comp (hx : cb.xv ≠ cb.cn.xe) (X : AState) {x y : Var} (hx1 : x ≠ cb.cn.xe)
    (hx2 : x ≠ cb.xv) (hy1 : y ≠ cb.cn.xe) (hy2 : y ≠ cb.xv) (px py : List ACell) :
    may (comp cb X) x px y py = may X x px y py :=
  (may_le (le_comp hx X) hx1 hx2 hy1 hy2 px py).symm

end bridge

end DirectedAlias.Impl.Engine

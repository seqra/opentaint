/-
  ApSpec.Invariant — shape invariants of the analysis result.

  1. `final_star_legal`: a final fact with the `*` tail has an abstract mark (`*` or `*∖x`)
     and is complete (rule W2 and "the demand layer has no `*` leaf"). A cleaner of all
     marks that cleans a `*` fact only partly gives the normal form of the fact in the
     demand layer, so `[any]` or `$` (`cleanAll_part_gives_any`).
  2. `star_final_keeps_initial_excl`: a final `*/Ec` under an initial `*/Ei`
     keeps every exclusion of the initial (`Ei ⊆ Ec`).
  3. `star_initial_complete`: under an initial fact `*/Ei`, a final fact in the
     normal layer has the `*` tail, or `Ei` is empty. So every complete record
     with a `*` premise has an exact reversal (`Reverse.ExactShape`).
  4. `demand_monotone`: the demand layer never goes back to the normal layer.
     `applyEdge_demand_monotone`, `applySummary_demand_monotone`,
     `limitF_demand_monotone`, `transfer_demand_monotone` (rule `step`),
     `demand_monotone_ret` (rule `ret`) and `cleanRes_demand_monotone` (rule `clean`; the
     rule `filt` keeps the fact).
  5. `no_univ_star`: no edge fact has the kind `*/Universe`, if a `$` premise of a micro
     edge has a concrete mark, no micro edge has the kind `*/Universe`, and no initial fact
     has it (`no_univ_star_of_α`, `no_univ_star_policy`). Each hypothesis is necessary
     (`no_univ_needs_*`).
  6. `demand_of_any_ok`: rule W6 (every `[any]` fact in the demand layer) keeps the fact and
     the complete edges and only raises the layer; `applyEdge_tag`, `applySummary_tag`: the
     layer of a non-`*` fact is only a tag downstream.
-/
import ApSpec.Core

namespace ApSpec.Invariant
open ApSpec

/-! ## The normal form -/

/-- Version 5: the mark of a normal `*` fact is `*` OR `*∖x` (W2 allows both). -/
theorem norm_legal {x : AFact} {e : Excl} (h : x.norm.fact.kind = .star e) :
    (x.norm.fact.mark = .star ∨ ∃ y, x.norm.fact.mark = .starEx y) ∧ x.norm.demand = false := by
  obtain ⟨⟨b, p, k, m⟩, ap⟩ := x
  cases k with
  | star e0 =>
    cases m with
    | star =>
      cases ap with
      | false => cases e0 <;> exact ⟨Or.inl rfl, rfl⟩
      | true => cases e0 <;> cases h
    | starEx y =>
      cases ap with
      | false => cases e0 <;> exact ⟨Or.inr ⟨y, rfl⟩, rfl⟩
      | true => cases e0 <;> cases h
    | conc t => cases e0 <;> cases h
  | any => cases h
  | exact => cases h

/-! ## The shape of an `applyEdge` result -/

/-- Version 5: the result mark is the mark `m` of `markComp` (it was `markOutA`). -/
theorem applyEdge_shape {c r : AFact} {fr to : PFact} (h : r ∈ (applyEdge c fr to).facts) :
    ∃ p k ap m, CoreAux.geo c.fact.kind fr.kind fr.path c.fact.path to.path to.kind = some (p, k, ap) ∧
      markComp to.mark c.fact.mark = some m ∧
      r = AFact.norm ⟨⟨to.base, p, k, m⟩, c.demand || ap⟩ := by
  obtain ⟨p, k, ap, m, hg, _, hm, hr⟩ := CoreAux.mem_applyEdge_facts_inv h
  exact ⟨p, k, ap, m, hg, hm, hr⟩

/-! ## Exclusion inclusion -/

theorem subB_univ (e : Excl) : e.subB .univ = true := by cases e <;> rfl

theorem subB_union_right {e1 e2 : Excl} (e3 : Excl) (h : e1.subB e2 = true) :
    e1.subB (e2.union e3) = true := by
  cases e2 with
  | univ => exact subB_univ _
  | set ys =>
    cases e3 with
    | univ => exact subB_univ _
    | set zs =>
      cases e1 with
      | univ => cases h
      | set xs =>
        show xs.all (fun a => memB a (ys ++ zs)) = true
        have hx : xs.all (fun a => memB a ys) = true := h
        apply List.all_eq_true.mpr
        intro a ha
        have hay : memB a ys = true := List.all_eq_true.mp hx a ha
        rw [CoreAux.memB_append, hay]
        rfl

theorem isEmpty_of_subB_empty {e : Excl} (h : e.subB (.set []) = true) : e.isEmptyB = true := by
  cases e with
  | univ => cases h
  | set xs =>
    cases xs with
    | nil => rfl
    | cons a r =>
      have h' : (a :: r).all (fun b => memB b []) = true := h
      cases h'

theorem isEmptyB_eq {e : Excl} (h : e.isEmptyB = true) : e = .set [] := by
  cases e with
  | univ => cases h
  | set xs => cases xs with
    | nil => rfl
    | cons a r => cases h

theorem union_isEmpty_left {e1 e2 : Excl} (h : (e1.union e2).isEmptyB = true) : e1.isEmptyB = true := by
  cases e1 with
  | univ => cases h
  | set xs =>
    cases e2 with
    | univ => cases h
    | set ys =>
      cases xs with
      | nil => rfl
      | cons a r => cases h

/-! ## The geometry on a correlated `*` fact -/

/-- A `*` result keeps the exclusion of the correlated input. -/
theorem belowCase_star_keeps {ec e0 : Excl} {fk tk : Kind} {r tp p : List Acc} {ek : Excl} {ap : Bool}
    (h0 : e0.subB ec = true)
    (h : belowCase (.star ec) fk r tp tk = some (p, .star ek, ap)) : e0.subB ek = true := by
  unfold belowCase at h
  cases ha : admitsTailB fk r with
  | false => rw [ha, if_neg Bool.false_ne_true] at h; cases h
  | true =>
    rw [ha, if_pos rfl] at h
    cases tk with
    | star et =>
      cases r with
      | cons a r' =>
        dsimp only at h
        cases he : et.admits (a :: r') with
        | false => rw [he, if_neg Bool.false_ne_true] at h; cases h
        | true =>
          rw [he, if_pos rfl] at h
          cases h
          exact h0
      | nil =>
        dsimp only at h
        cases h
        exact subB_union_right _ h0
    | any => cases h
    | exact =>
      cases fk with
      | exact =>
        cases r with
        | nil => cases h; exact subB_univ _
        | cons a r' => cases h
      | star e => cases h
      | any => cases h

theorem lostCorr_false_empty {ec : Excl} {fk : Kind} {r : List Acc}
    (h : lostCorr (.star ec) fk r = false) : ec.isEmptyB = true := by
  cases r with
  | nil =>
    have h' : (!(ec.union (tailExcl fk)).isEmptyB) = false := h
    cases hq : (ec.union (tailExcl fk)).isEmptyB with
    | true => exact union_isEmpty_left hq
    | false => rw [hq] at h'; cases h'
  | cons a r' =>
    have h' : (!ec.isEmptyB) = false := h
    cases hq : ec.isEmptyB with
    | true => rfl
    | false => rw [hq] at h'; cases h'

/-- A complete non-`*` result of a correlated `*` input needs an empty exclusion. -/
theorem belowCase_star_nonstar {ec : Excl} {fk tk k : Kind} {r tp p : List Acc}
    (hk : k.isStar = false)
    (h : belowCase (.star ec) fk r tp tk = some (p, k, false)) : ec.isEmptyB = true := by
  unfold belowCase at h
  cases ha : admitsTailB fk r with
  | false => rw [ha, if_neg Bool.false_ne_true] at h; cases h
  | true =>
    rw [ha, if_pos rfl] at h
    cases tk with
    | star et =>
      cases r with
      | cons a r' =>
        dsimp only at h
        cases he : et.admits (a :: r') with
        | false => rw [he, if_neg Bool.false_ne_true] at h; cases h
        | true =>
          rw [he, if_pos rfl] at h
          cases h
          cases hk
      | nil =>
        dsimp only at h
        cases h
        cases hk
    | any =>
      injection h with h
      injection h with _ h
      injection h with _ h
      exact lostCorr_false_empty h
    | exact =>
      cases fk with
      | exact =>
        cases r with
        | nil => cases h; cases hk
        | cons a r' => cases ha
      | star e =>
        injection h with h
        injection h with _ h
        injection h with _ h
        exact lostCorr_false_empty h
      | any =>
        injection h with h
        injection h with _ h
        injection h with _ h
        exact lostCorr_false_empty h

theorem aboveCase_star {ec : Excl} {fk tk k : Kind} {r tp p : List Acc} {ap : Bool}
    (h : aboveCase (.star ec) fk r tp tk = some (p, k, ap)) : k.isStar = false ∧ ap = true := by
  unfold aboveCase at h
  cases ha : admitsTailB (.star ec) r with
  | false => rw [ha, if_neg Bool.false_ne_true] at h; cases h
  | true =>
    rw [ha, if_pos rfl] at h
    cases tk with
    | star et => cases h; exact ⟨rfl, rfl⟩
    | any => cases h; exact ⟨rfl, rfl⟩
    | exact => cases h; exact ⟨rfl, rfl⟩

theorem belowCase_nonstar {ck fk tk k : Kind} {r tp p : List Acc} {ap : Bool}
    (hc : ck.isStar = false)
    (h : belowCase ck fk r tp tk = some (p, k, ap)) : k.isStar = false := by
  unfold belowCase at h
  cases ha : admitsTailB fk r with
  | false => rw [ha, if_neg Bool.false_ne_true] at h; cases h
  | true =>
    rw [ha, if_pos rfl] at h
    cases tk with
    | star et =>
      cases r with
      | cons a r' =>
        dsimp only at h
        cases he : et.admits (a :: r') with
        | false => rw [he, if_neg Bool.false_ne_true] at h; cases h
        | true => rw [he, if_pos rfl] at h; cases h; exact hc
      | nil =>
        dsimp only at h
        cases ck with
        | star e => cases hc
        | exact => cases h; rfl
        | any =>
          cases hx : (tailExcl fk).union et with
          | univ => rw [hx] at h; cases h; rfl
          | set xs => rw [hx] at h; cases h; rfl
    | any => cases h; rfl
    | exact =>
      cases ck with
      | star e => cases hc
      | any => cases h; rfl
      | exact => cases h; rfl

theorem aboveCase_nonstar {ck fk tk k : Kind} {r tp p : List Acc} {ap : Bool}
    (h : aboveCase ck fk r tp tk = some (p, k, ap)) : k.isStar = false := by
  unfold aboveCase at h
  cases ha : admitsTailB ck r with
  | false => rw [ha, if_neg Bool.false_ne_true] at h; cases h
  | true =>
    rw [ha, if_pos rfl] at h
    cases tk with
    | star et => cases h; rfl
    | any => cases h; rfl
    | exact => cases h; rfl

theorem geo_nonstar {ck fk tk k : Kind} {P q tp p : List Acc} {ap : Bool}
    (hc : ck.isStar = false)
    (h : CoreAux.geo ck fk P q tp tk = some (p, k, ap)) : k.isStar = false := by
  unfold CoreAux.geo at h
  cases hrel : relate P q with
  | apart => rw [hrel] at h; cases h
  | above r0 => rw [hrel] at h; exact aboveCase_nonstar h
  | below r0 => rw [hrel] at h; exact belowCase_nonstar hc h

/-! ## The edge invariant relative to the initial exclusion -/

/-- `Q ei c`: the shape invariant of a final fact `c` under an initial `*/ei`. -/
def Q (ei : Excl) (c : AFact) : Prop :=
  (∀ ec, c.fact.kind = .star ec → ei.subB ec = true) ∧
  (c.fact.kind.isStar = false → c.demand = true ∨ ei.isEmptyB = true)

/-- The mark is abstract: `*` or `*∖x`. -/
def AbsMark (m : MarkA) : Prop := m = .star ∨ ∃ x, m = .starEx x

/-- Legality (W2): a `*` fact has an abstract mark and is complete. Version 5: the mark
    `*∖x` is also legal. -/
def Legal (c : AFact) : Prop := ∀ e, c.fact.kind = .star e → AbsMark c.fact.mark ∧ c.demand = false

/-- The mark part of W2: a `*` fact has an abstract mark. -/
def LegalM (c : AFact) : Prop := ∀ e, c.fact.kind = .star e → AbsMark c.fact.mark

theorem Legal.toM {c : AFact} (h : Legal c) : LegalM c := fun e hk => (h e hk).1

theorem AbsMark.not_conc {m : MarkA} (h : AbsMark m) (t : Mark) : m ≠ .conc t := by
  rcases h with h | ⟨x, h⟩ <;> (rw [h]; intro h'; cases h')

theorem norm_Q {ei : Excl} {x : AFact} (h : Q ei x) : Q ei x.norm := by
  obtain ⟨⟨b, p, k, m⟩, ap⟩ := x
  obtain ⟨h1, h2⟩ := h
  cases k with
  | star e0 =>
    cases m with
    | star =>
      cases ap with
      | false => cases e0 <;> exact ⟨h1, h2⟩
      | true => cases e0 <;> exact ⟨fun _ hk => (by cases hk), fun _ => Or.inl rfl⟩
    | starEx y =>
      cases ap with
      | false => cases e0 <;> exact ⟨h1, h2⟩
      | true => cases e0 <;> exact ⟨fun _ hk => (by cases hk), fun _ => Or.inl rfl⟩
    | conc t => cases e0 <;> exact ⟨fun _ hk => (by cases hk), fun _ => Or.inl rfl⟩
  | any => exact ⟨h1, h2⟩
  | exact => exact ⟨h1, h2⟩

theorem applyEdge_Q {ei : Excl} {c r : AFact} {fr to : PFact}
    (hq : Q ei c) (_hl : Legal c) (hr : r ∈ (applyEdge c fr to).facts) : Q ei r := by
  obtain ⟨p, k, ap, m, hg, _, rfl⟩ := applyEdge_shape hr
  apply norm_Q
  obtain ⟨hq1, hq2⟩ := hq
  cases hck : c.fact.kind with
  | star ec =>
    have hsub := hq1 ec hck
    unfold CoreAux.geo at hg
    rw [hck] at hg
    cases hrel : relate fr.path c.fact.path with
    | apart => rw [hrel] at hg; cases hg
    | above r0 =>
      rw [hrel] at hg
      obtain ⟨hks, hap⟩ := aboveCase_star hg
      refine ⟨fun e hk => ?_, fun _ => Or.inl ?_⟩
      · have : k = .star e := hk
        rw [this] at hks; cases hks
      · show (c.demand || ap) = true
        rw [hap, Bool.or_true]
    | below r0 =>
      rw [hrel] at hg
      refine ⟨fun e hk => ?_, fun hns => ?_⟩
      · have hk' : k = .star e := hk
        rw [hk'] at hg
        exact belowCase_star_keeps hsub hg
      · cases hap : ap with
        | true =>
          left
          show (c.demand || true) = true
          rw [Bool.or_true]
        | false =>
          right
          rw [hap] at hg
          have hec := belowCase_star_nonstar hns hg
          rw [isEmptyB_eq hec] at hsub
          exact isEmpty_of_subB_empty hsub
  | any =>
    have hns : k.isStar = false := by
      rw [hck] at hg
      exact geo_nonstar rfl hg
    refine ⟨fun e hk => ?_, fun _ => ?_⟩
    · have : k = .star e := hk
      rw [this] at hns; cases hns
    · rcases hq2 (by rw [hck]; rfl) with ha | he
      · left
        show (c.demand || ap) = true
        rw [ha, Bool.true_or]
      · exact Or.inr he
  | exact =>
    have hns : k.isStar = false := by
      rw [hck] at hg
      exact geo_nonstar rfl hg
    refine ⟨fun e hk => ?_, fun _ => ?_⟩
    · have : k = .star e := hk
      rw [this] at hns; cases hns
    · rcases hq2 (by rw [hck]; rfl) with ha | he
      · left
        show (c.demand || ap) = true
        rw [ha, Bool.true_or]
      · exact Or.inr he

theorem applyEdge_legal {c r : AFact} {fr to : PFact} {e : Excl}
    (hr : r ∈ (applyEdge c fr to).facts) (hk : r.fact.kind = .star e) :
    AbsMark r.fact.mark ∧ r.demand = false := by
  obtain ⟨p, k, ap, m, _, _, rfl⟩ := applyEdge_shape hr
  exact norm_legal hk

theorem applySummary_shape {a r g : AFact} {j : PFact} (h : r ∈ (applySummary a j g).facts) :
    ∃ x, x ∈ (applyEdge a j g.fact).facts ∧ r = AFact.norm ⟨x.fact, x.demand || g.demand⟩ := by
  obtain ⟨x, hx, e⟩ := List.mem_map.mp h
  exact ⟨x, hx, e.symm⟩

theorem applySummary_legal {a r g : AFact} {j : PFact} {e : Excl}
    (hr : r ∈ (applySummary a j g).facts) (hk : r.fact.kind = .star e) :
    AbsMark r.fact.mark ∧ r.demand = false := by
  obtain ⟨x, _, rfl⟩ := applySummary_shape hr
  exact norm_legal hk

/-! ## Field limit, start fact, transfer -/

theorem limitF_cases (counted : Acc → Bool) (L : Nat) (f : AFact) :
    limitF counted L f = f ∨ ((limitF counted L f).fact.kind = .any ∧ (limitF counted L f).demand = true) := by
  unfold limitF
  cases cutPath counted L f.fact.path with
  | none => exact Or.inl rfl
  | some p => exact Or.inr ⟨rfl, rfl⟩

theorem limitF_legal {counted : Acc → Bool} {L : Nat} {f : AFact} {e : Excl}
    (hf : ∀ e, f.fact.kind = .star e → AbsMark f.fact.mark ∧ f.demand = false)
    (hk : (limitF counted L f).fact.kind = .star e) :
    AbsMark (limitF counted L f).fact.mark ∧ (limitF counted L f).demand = false := by
  rcases limitF_cases counted L f with eq | ⟨hany, _⟩
  · rw [eq] at hk ⊢; exact hf e hk
  · rw [hany] at hk; cases hk

theorem startFact_legal {i : PFact} {e : Excl} (hk : (startFact i).fact.kind = .star e) :
    AbsMark (startFact i).fact.mark ∧ (startFact i).demand = false := by
  obtain ⟨b, p, k, m⟩ := i
  cases k with
  | star e0 =>
    cases m with
    | star => exact ⟨Or.inl rfl, rfl⟩
    | starEx y => exact ⟨Or.inr ⟨y, rfl⟩, rfl⟩
    | conc t => cases hk
  | any => cases m <;> cases hk
  | exact => cases hk

theorem mem_applyAll {c r : AFact} :
    ∀ {es : List MicroEdge}, r ∈ (applyAll c es).facts → ∃ e, e ∈ es ∧ r ∈ (applyEdge c e.1 e.2).facts
  | [], h => absurd h List.not_mem_nil
  | e :: es, h => by
    have h' : r ∈ (applyEdge c e.1 e.2).facts ++ (applyAll c es).facts := h
    rcases List.mem_append.mp h' with h1 | h2
    · exact ⟨e, List.mem_cons_self .., h1⟩
    · obtain ⟨e', he', hr⟩ := mem_applyAll h2
      exact ⟨e', List.mem_cons_of_mem _ he', hr⟩

theorem transfer_mem {counted : Acc → Bool} {L : Nat} {s : Stmt} {c r : AFact}
    (h : r ∈ (transfer counted L s c).facts) :
    r = c ∨ ∃ x e, e ∈ s.edges ∧ x ∈ (applyEdge c e.1 e.2).facts ∧ r = limitF counted L x := by
  unfold transfer at h
  cases ht : memB c.fact.base s.touched with
  | false =>
    rw [ht, if_neg Bool.false_ne_true] at h
    exact Or.inl (List.mem_singleton.mp h)
  | true =>
    rw [ht, if_pos rfl] at h
    obtain ⟨x, hx, e⟩ := List.mem_map.mp h
    obtain ⟨ed, hed, hxe⟩ := mem_applyAll hx
    exact Or.inr ⟨x, ed, hed, hxe, e.symm⟩

theorem applySummary_Q {ei : Excl} {a r g : AFact} {j : PFact}
    (hq : Q ei a) (hl : Legal a) (hr : r ∈ (applySummary a j g).facts) : Q ei r := by
  obtain ⟨x, hx, rfl⟩ := applySummary_shape hr
  apply norm_Q
  obtain ⟨h1, h2⟩ := applyEdge_Q hq hl hx
  refine ⟨h1, fun hns => ?_⟩
  rcases h2 hns with ha | he
  · left
    show (x.demand || g.demand) = true
    rw [ha, Bool.true_or]
  · exact Or.inr he

theorem applyEdge_Legal {c r : AFact} {fr to : PFact} (hr : r ∈ (applyEdge c fr to).facts) : Legal r :=
  fun _ hk => applyEdge_legal hr hk

theorem applySummary_Legal {a r g : AFact} {j : PFact} (hr : r ∈ (applySummary a j g).facts) : Legal r :=
  fun _ hk => applySummary_legal hr hk

theorem applyEdge_LegalM {c r : AFact} {fr to : PFact} (hr : r ∈ (applyEdge c fr to).facts) : LegalM r :=
  (applyEdge_Legal hr).toM

theorem applySummary_LegalM {a r g : AFact} {j : PFact} (hr : r ∈ (applySummary a j g).facts) :
    LegalM r :=
  (applySummary_Legal hr).toM

theorem limitF_Q {counted : Acc → Bool} {L : Nat} {ei : Excl} {f : AFact} (h : Q ei f) :
    Q ei (limitF counted L f) := by
  rcases limitF_cases counted L f with e | ⟨hany, ha⟩
  · rw [e]; exact h
  · refine ⟨fun ec hk => ?_, fun _ => Or.inl ha⟩
    rw [hany] at hk; cases hk

theorem limitF_Legal {counted : Acc → Bool} {L : Nat} {f : AFact} (h : Legal f) :
    Legal (limitF counted L f) := fun _ hk => limitF_legal h hk

theorem limitF_LegalM {counted : Acc → Bool} {L : Nat} {f : AFact} (h : LegalM f) :
    LegalM (limitF counted L f) := by
  intro e hk
  rcases limitF_cases counted L f with eq | ⟨hany, _⟩
  · rw [eq] at hk ⊢; exact h e hk
  · rw [hany] at hk; cases hk

theorem startFact_Q {i : PFact} {ei : Excl} (hi : i.kind = .star ei) : Q ei (startFact i) := by
  obtain ⟨b, p, k, m⟩ := i
  cases hi
  cases m with
  | star => exact ⟨fun ec hk => (by cases hk; exact subB_refl ei), fun h => (by cases h)⟩
  | starEx y => exact ⟨fun ec hk => (by cases hk; exact subB_refl ei), fun h => (by cases h)⟩
  | conc t => exact ⟨fun ec hk => (by cases hk), fun _ => Or.inl rfl⟩

/-! ## The demand layer is monotone

  An approximation step sets `demand`, and no operation clears it. So along every
  closure rule (`step`, `ret`) the layer of an edge never goes back from the
  demand layer to the normal layer. -/

/-- The normal form never clears `demand`. -/
theorem norm_demand {x : AFact} (h : x.demand = true) : x.norm.demand = true := by
  obtain ⟨⟨b, p, k, m⟩, d⟩ := x
  cases h
  cases k with
  | star e => cases m <;> cases e <;> rfl
  | any => rfl
  | exact => rfl

/-- `applyEdge` keeps the demand layer of its input fact. -/
theorem applyEdge_demand_monotone {c r : AFact} {fr to : PFact}
    (hc : c.demand = true) (hr : r ∈ (applyEdge c fr to).facts) : r.demand = true := by
  obtain ⟨p, k, ap, m, _, _, rfl⟩ := applyEdge_shape hr
  apply norm_demand
  show (c.demand || ap) = true
  rw [hc, Bool.true_or]

#print axioms applyEdge_demand_monotone

/-- `applySummary` keeps the demand layer of the caller fact AND of the summary edge. -/
theorem applySummary_demand_monotone {a r g : AFact} {j : PFact}
    (h : a.demand = true ∨ g.demand = true) (hr : r ∈ (applySummary a j g).facts) :
    r.demand = true := by
  obtain ⟨x, hx, rfl⟩ := applySummary_shape hr
  apply norm_demand
  show (x.demand || g.demand) = true
  rcases h with ha | hg
  · rw [applyEdge_demand_monotone ha hx, Bool.true_or]
  · rw [hg, Bool.or_true]

#print axioms applySummary_demand_monotone

/-- The field limit keeps the demand layer. -/
theorem limitF_demand_monotone {counted : Acc → Bool} {L : Nat} {f : AFact}
    (h : f.demand = true) : (limitF counted L f).demand = true := by
  rcases limitF_cases counted L f with e | ⟨_, hd⟩
  · rw [e]; exact h
  · exact hd

#print axioms limitF_demand_monotone

/-- The statement transfer keeps the demand layer (rule `step`). -/
theorem transfer_demand_monotone {counted : Acc → Bool} {L : Nat} {s : Stmt} {c r : AFact}
    (hc : c.demand = true) (hr : r ∈ (transfer counted L s c).facts) : r.demand = true := by
  rcases transfer_mem hr with rfl | ⟨x, e, _, hx, rfl⟩
  · exact hc
  · exact limitF_demand_monotone (applyEdge_demand_monotone hc hx)

#print axioms transfer_demand_monotone

/-- `demand_monotone` for the rule `ret`: if the caller edge or the callee summary is in
    the demand layer, the return edge is in the demand layer. -/
theorem demand_monotone_ret {counted : Acc → Bool} {L : Nat} {f a g r r' : AFact}
    {e1 e2 : MicroEdge} {j : PFact}
    (h : f.demand = true ∨ g.demand = true)
    (ha : a ∈ (applyEdge f e1.1 e1.2).facts) (hr : r ∈ (applySummary a j g).facts)
    (hr' : r' ∈ (applyEdge r e2.1 e2.2).facts) : (limitF counted L r').demand = true := by
  have hag : a.demand = true ∨ g.demand = true := by
    rcases h with hf | hg
    · exact Or.inl (applyEdge_demand_monotone hf ha)
    · exact Or.inr hg
  exact limitF_demand_monotone
    (applyEdge_demand_monotone (applySummary_demand_monotone hag hr) hr')

#print axioms demand_monotone_ret

/-! ## The cleaner and the type filter -/

/-- The four kinds of a cleaner result: the input fact; the input fact with the cleaned
    mark added to its abstract mark (`addEx`); the normal form of the input fact in the
    demand layer (a cleaner of all marks, `part`); `concPart` of a concrete-mark fact. -/
theorem cleanRes_facts_cases {cl : Cleaner} {c f : AFact} (h : f ∈ (cleanRes cl c).facts) :
    f = c ∨
    (∃ t, cl.mark = some t ∧ (∀ t', c.fact.mark ≠ .conc t') ∧
      f = ⟨⟨c.fact.base, c.fact.path, c.fact.kind, addEx c.fact.mark t⟩, c.demand⟩) ∨
    (cl.mark = none ∧ (∀ t', c.fact.mark ≠ .conc t') ∧ f = AFact.norm ⟨c.fact, true⟩) ∨
    ((∃ t, c.fact.mark = .conc t) ∧ f = concPart cl c) := by
  unfold cleanRes at h
  cases hp : cleanPos cl c.fact with
  | disjoint => rw [hp] at h; exact Or.inl (List.mem_singleton.mp h)
  | inside =>
    rw [hp] at h
    cases hm : c.fact.mark with
    | conc t =>
      rw [hm] at h
      dsimp only at h
      cases hb : cl.markB t with
      | true => rw [hb, if_pos rfl] at h; exact absurd h List.not_mem_nil
      | false =>
        rw [hb, if_neg Bool.false_ne_true] at h
        exact Or.inl (List.mem_singleton.mp h)
    | star =>
      rw [hm] at h
      dsimp only at h
      cases hcm : cl.mark with
      | none => rw [hcm] at h; dsimp only at h; exact absurd h List.not_mem_nil
      | some t =>
        rw [hcm] at h
        dsimp only at h
        exact Or.inr (Or.inl ⟨t, rfl, (fun t' h' => by cases h'), List.mem_singleton.mp h⟩)
    | starEx x =>
      rw [hm] at h
      dsimp only at h
      cases hcm : cl.mark with
      | none => rw [hcm] at h; dsimp only at h; exact absurd h List.not_mem_nil
      | some t =>
        rw [hcm] at h
        dsimp only at h
        exact Or.inr (Or.inl ⟨t, rfl, (fun t' h' => by cases h'), List.mem_singleton.mp h⟩)
  | part =>
    rw [hp] at h
    cases hm : c.fact.mark with
    | conc t =>
      rw [hm] at h
      dsimp only at h
      cases hb : cl.markB t with
      | true =>
        rw [hb, if_pos rfl] at h
        exact Or.inr (Or.inr (Or.inr ⟨⟨t, rfl⟩, List.mem_singleton.mp h⟩))
      | false =>
        rw [hb, if_neg Bool.false_ne_true] at h
        exact Or.inl (List.mem_singleton.mp h)
    | star =>
      rw [hm] at h
      dsimp only at h
      cases hcm : cl.mark with
      | none =>
        rw [hcm] at h
        dsimp only at h
        exact Or.inr (Or.inr (Or.inl ⟨rfl, (fun t' h' => by cases h'), List.mem_singleton.mp h⟩))
      | some t =>
        rw [hcm] at h
        dsimp only at h
        exact Or.inr (Or.inl ⟨t, rfl, (fun t' h' => by cases h'), List.mem_singleton.mp h⟩)
    | starEx x =>
      rw [hm] at h
      dsimp only at h
      cases hcm : cl.mark with
      | none =>
        rw [hcm] at h
        dsimp only at h
        exact Or.inr (Or.inr (Or.inl ⟨rfl, (fun t' h' => by cases h'), List.mem_singleton.mp h⟩))
      | some t =>
        rw [hcm] at h
        dsimp only at h
        exact Or.inr (Or.inl ⟨t, rfl, (fun t' h' => by cases h'), List.mem_singleton.mp h⟩)

/-- `concPart` gives the input fact in the demand layer, or (an `[any]` input) the `$` fact
    at the same position in the same layer. -/
theorem concPart_cases (cl : Cleaner) (c : AFact) :
    concPart cl c = ⟨c.fact, true⟩ ∨
    (c.fact.kind = .any ∧
      concPart cl c = ⟨⟨c.fact.base, c.fact.path, .exact, c.fact.mark⟩, c.demand⟩) := by
  unfold concPart
  cases hk : c.fact.kind with
  | any =>
    cases hr : cl.reach with
    | below =>
      cases hrel : relate cl.path c.fact.path with
      | below r =>
        cases r with
        | nil => exact Or.inr ⟨rfl, rfl⟩
        | cons a r => exact Or.inl rfl
      | above r => exact Or.inl rfl
      | apart => exact Or.inl rfl
    | exact => exact Or.inl rfl
    | atAndBelow => exact Or.inl rfl
  | star e => exact Or.inl rfl
  | exact => exact Or.inl rfl

theorem addEx_abs {m : MarkA} (h : AbsMark m) (t : Mark) : AbsMark (addEx m t) := by
  rcases h with h | ⟨x, h⟩
  · rw [h]; exact Or.inr ⟨[t], rfl⟩
  · rw [h]; exact Or.inr ⟨t :: x, rfl⟩

/-- The cleaner keeps the mark part of W2. -/
theorem cleanRes_LegalM {cl : Cleaner} {c f : AFact} (hc : LegalM c)
    (h : f ∈ (cleanRes cl c).facts) : LegalM f := by
  rcases cleanRes_facts_cases h with rfl | ⟨t, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩
  · exact hc
  · exact fun e hk => addEx_abs (hc e hk) t
  · exact fun e hk => (norm_legal hk).1
  · rcases concPart_cases cl c with h1 | ⟨_, h1⟩
    · rw [h1]; exact hc
    · rw [h1]; intro e hk; cases hk

/-- The cleaner keeps W2. -/
theorem cleanRes_Legal {cl : Cleaner} {c f : AFact} (hc : Legal c)
    (h : f ∈ (cleanRes cl c).facts) : Legal f := by
  rcases cleanRes_facts_cases h with rfl | ⟨t, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨⟨t, ht⟩, rfl⟩
  · exact hc
  · exact fun e hk => ⟨addEx_abs (hc e hk).1 t, (hc e hk).2⟩
  · exact fun e hk => norm_legal hk
  · intro e hk
    rcases concPart_cases cl c with h1 | ⟨hka, h1⟩
    · rw [h1] at hk
      exact absurd ht ((hc e hk).1.not_conc t)
    · rw [h1] at hk; cases hk

/-- The cleaner keeps the edge invariant `Q`. -/
theorem cleanRes_Q {ei : Excl} {cl : Cleaner} {c f : AFact} (hq : Q ei c)
    (h : f ∈ (cleanRes cl c).facts) : Q ei f := by
  obtain ⟨h1, h2⟩ := hq
  rcases cleanRes_facts_cases h with rfl | ⟨t, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩
  · exact ⟨h1, h2⟩
  · exact ⟨h1, h2⟩
  · exact norm_Q ⟨h1, fun _ => Or.inl rfl⟩
  · rcases concPart_cases cl c with h3 | ⟨hk, h3⟩
    · rw [h3]; exact ⟨h1, fun _ => Or.inl rfl⟩
    · rw [h3]
      exact ⟨fun _ hk' => (by cases hk'), fun _ => h2 (by rw [hk]; rfl)⟩

/-- The cleaner keeps the demand layer. -/
theorem cleanRes_demand_monotone {cl : Cleaner} {c f : AFact} (hc : c.demand = true)
    (h : f ∈ (cleanRes cl c).facts) : f.demand = true := by
  rcases cleanRes_facts_cases h with rfl | ⟨t, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩
  · exact hc
  · exact hc
  · exact norm_demand rfl
  · rcases concPart_cases cl c with h3 | ⟨_, h3⟩
    · rw [h3]
    · rw [h3]; exact hc

#print axioms cleanRes_demand_monotone

/-! ## The invariants of the closure -/

section
variable (P : Program) (counted : Acc → Bool) (L : Nat) (α : MethodId → PFact → PFact)
  (sinks : List (MethodId × Node × PFact)) (roots : List MethodId)

/-- The motive: shape invariants on edges, `True` elsewhere. -/
def Inv : Obj → Prop
  | .edge _ i _ f => Legal f ∧ (∀ ei, i.kind = .star ei → Q ei f)
  | _ => True

theorem D_inv {o : Obj} (h : D P counted L α sinks roots o) : Inv o := by
  induction h with
  | root => trivial
  | @start M i _ =>
    exact ⟨fun e hk => startFact_legal hk, fun ei hi => startFact_Q hi⟩
  | @step M i n f n' s f' _ _ hf' ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rcases transfer_mem hf' with rfl | ⟨x, e, _, hx, rfl⟩
    · exact ⟨ih1, ih2⟩
    · exact ⟨limitF_Legal (applyEdge_Legal hx),
        fun ei hi => limitF_Q (applyEdge_Q (ih2 ei hi) ih1 hx)⟩
  | reqStmt => trivial
  | pass _ _ _ ih => exact ih
  | added => trivial
  | initA => trivial
  | @ret M i n f n' c e1 a j g r e2 r' _ _ _ ha _ _ _ hr _ hr' ihF _ _ =>
    obtain ⟨ihL, ihQ⟩ := ihF
    refine ⟨limitF_Legal (applyEdge_Legal hr'), fun ei hi => ?_⟩
    have qa := applyEdge_Q (ihQ ei hi) ihL ha
    have qr := applySummary_Q qa (applyEdge_Legal ha) hr
    exact limitF_Q (applyEdge_Q qr (applySummary_Legal hr) hr')
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial
  | @clean M i n f n' cl f' _ _ hf' ih =>
    obtain ⟨ih1, ih2⟩ := ih
    exact ⟨cleanRes_Legal ih1 hf', fun ei hi => cleanRes_Q (ih2 ei hi) hf'⟩
  | reqClean => trivial
  | filt _ _ _ ih => exact ih

/-- The motive of W2: every edge fact is legal. -/
def InvL : Obj → Prop
  | .edge _ _ _ f => Legal f
  | _ => True

/-- W2 holds on every edge. -/
theorem D_legal {o : Obj} (h : D P counted L α sinks roots o) : InvL o := by
  have hi := D_inv P counted L α sinks roots h
  cases o with
  | edge M i n f => exact hi.1
  | init => trivial
  | added => trivial
  | req => trivial
  | vuln => trivial

/-- The mark part of W2: a final `*` fact has the mark `*` or `*∖x`. -/
theorem final_star_abstract {M : MethodId} {i : PFact} {n : Node} {f : AFact} {e : Excl}
    (h : D P counted L α sinks roots (.edge M i n f)) (hk : f.fact.kind = .star e) :
    AbsMark f.fact.mark :=
  ((D_inv P counted L α sinks roots h).1 e hk).1

/-- W2 and the demand-layer invariant: a final `*` fact has the mark `*` or `*∖x` and is
    complete. Version 5: the mark can be `*∖x`. -/
theorem final_star_legal {M : MethodId} {i : PFact} {n : Node} {f : AFact}
    {e : Excl} (h : D P counted L α sinks roots (.edge M i n f)) (hk : f.fact.kind = .star e) :
    AbsMark f.fact.mark ∧ f.demand = false :=
  (D_inv P counted L α sinks roots h).1 e hk

/-- A final `*/Ec` under an initial `*/Ei` keeps every exclusion of the initial. -/
theorem star_final_keeps_initial_excl {M : MethodId} {i : PFact} {n : Node} {f : AFact}
    {ei ec : Excl}
    (h : D P counted L α sinks roots (.edge M i n f)) (hi : i.kind = .star ei)
    (hk : f.fact.kind = .star ec) : ei.subB ec = true :=
  ((D_inv P counted L α sinks roots h).2 ei hi).1 ec hk

/-- Under a `*/Ei` initial fact, a complete final fact has the `*` tail, or `Ei` is empty. -/
theorem star_initial_complete {M : MethodId} {i : PFact} {n : Node} {f : AFact} {ei : Excl}
    (h : D P counted L α sinks roots (.edge M i n f)) (hi : i.kind = .star ei)
    (hc : f.demand = false) : f.fact.kind.isStar = true ∨ ei.isEmptyB = true := by
  cases hs : f.fact.kind.isStar with
  | true => exact Or.inl rfl
  | false =>
    rcases ((D_inv P counted L α sinks roots h).2 ei hi).2 hs with ha | he
    · rw [hc] at ha; cases ha
    · exact Or.inr he

end

/-! ## A cleaner of all marks on a partly cleaned `*` fact

  The root `0` calls the method `1`; the abstraction gives the initial fact `i0 = 1.*` with
  the mark `*`. At the entry of the method `1`, a cleaner of ALL marks at `1` with the reach
  `exact` cleans the `*` fact only partly (`cleanPos = part`). The result is the normal form
  of the fact in the demand layer: `1.[any]` (W2 holds). The definitions also serve the
  counterexample `no_univ_needs_premConc`. -/
namespace Run0

def i0 : PFact := ⟨1, [], .star (.set []), .star⟩
def a0 : PFact := ⟨1, [], .exact, .conc 0⟩
def call0 : Call := ⟨1, [0], [(zeroFact, a0)], []⟩
def cl0 : Cleaner := ⟨1, [], .exact, none⟩
def P0 : Program := ⟨fun _ => 0, fun _ => 1, [(0, 0, .call call0, 1), (1, 0, .clean cl0, 1)]⟩
def α0 : MethodId → PFact → PFact := fun _ _ => i0

end Run0

open Run0 in
/-- The cleaner of all marks on the partly cleaned `*` fact `1.*` gives the demand fact
    `1.[any]`, and the run `P0` has this edge. -/
theorem cleanAll_part_gives_any (counted : Acc → Bool) (L : Nat)
    (sinks : List (MethodId × Node × PFact)) :
    cleanPos cl0 i0 = .part ∧
    (cleanRes cl0 (startFact i0)).facts = [⟨⟨1, [], .any, .star⟩, true⟩] ∧
    D P0 counted L α0 sinks [0] (.edge 1 i0 1 ⟨⟨1, [], .any, .star⟩, true⟩) := by
  have h1 : D P0 counted L α0 sinks [0] (.init 0 zeroFact) := D.root (List.Mem.head _)
  have h2 := D.start h1
  have ha : (⟨a0, false⟩ : AFact) ∈ (applyEdge (startFact zeroFact) zeroFact a0).facts := by decide
  have h3 : D P0 counted L α0 sinks [0] (.added call0.callee a0) :=
    D.added (n' := 1) (e := (zeroFact, a0)) (a := ⟨a0, false⟩) h2 (List.Mem.head _)
      (List.Mem.head _) ha
  have h4 : D P0 counted L α0 sinks [0] (.init 1 i0) := D.initA h3
  have h5 := D.start h4
  have hc : (⟨⟨1, [], .any, .star⟩, true⟩ : AFact) ∈ (cleanRes cl0 (startFact i0)).facts := by
    decide
  exact ⟨by decide, by decide, D.clean (cl := cl0) h5 (List.Mem.tail _ (List.Mem.head _)) hc⟩

/-! ## No Universe exclusion on a `*` conclusion (`no_univ_star`)

  The spec claims that the exclusion Universe never occurs on a `*` final fact. The claim is
  a closure invariant of `D` under three hypotheses:
  (a) `PremConc`: a micro edge (statement edge or call binding) whose premise has the `$`
      tail has a concrete premise mark;
  (b) `NoUnivE`: no premise and no target of a micro edge has the kind `*/Universe`;
  (c) no initial fact of `D` has the kind `*/Universe` (`D_init_no_univ`: true if the
      abstraction never gives it, for example `policy`; the answers keep the kind of the
      request or give `$`).
  No hypothesis on cleaners or type filters is necessary: they keep the kind (or make `$`).
  No hypothesis on summary edges is necessary: a `$` premise of a summary applies only to a
  `$` or a `*/Universe` caller fact (`applicable_exact_nonstar`).
  Why each hypothesis stays: the `*/Universe` kind comes only from `belowCase` at the premise
  position, with a correlated `*` fact and a `$` or `*/Universe` premise, or a `*/Universe`
  target (`belowCase_univ`). A concrete premise mark stops a `*` fact (its mark is abstract)
  at the gate. The counterexamples are `no_univ_needs_premConc` (a run of `D`),
  `no_univ_needs_premise`, `no_univ_needs_target` and `no_univ_needs_init` (`decide`). -/

theorem union_univ {e1 e2 : Excl} (h : e1.union e2 = .univ) : e1 = .univ ∨ e2 = .univ := by
  cases e1 with
  | univ => exact Or.inl rfl
  | set xs =>
    cases e2 with
    | univ => exact Or.inr rfl
    | set ys => cases h

theorem tailExcl_univ {k : Kind} (h : tailExcl k = .univ) : k = .exact ∨ k = .star .univ := by
  cases k with
  | star e =>
    have he : e = .univ := h
    rw [he]; exact Or.inr rfl
  | any => cases h
  | exact => exact Or.inl rfl

/-- The only sources of a `*/Universe` result of the geometry. -/
theorem belowCase_univ {ck fk tk : Kind} {r tp p : List Acc} {ap : Bool}
    (h : belowCase ck fk r tp tk = some (p, .star .univ, ap)) :
    ck = .star .univ ∨ fk = .star .univ ∨ tk = .star .univ ∨ (fk = .exact ∧ ck.isStar = true) := by
  cases ck with
  | any => exact absurd (belowCase_nonstar rfl h) (by decide)
  | exact => exact absurd (belowCase_nonstar rfl h) (by decide)
  | star ec =>
    unfold belowCase at h
    cases ha : admitsTailB fk r with
    | false => rw [ha, if_neg Bool.false_ne_true] at h; cases h
    | true =>
      rw [ha, if_pos rfl] at h
      cases tk with
      | star et =>
        cases r with
        | cons a r' =>
          dsimp only at h
          cases he : et.admits (a :: r') with
          | false => rw [he, if_neg Bool.false_ne_true] at h; cases h
          | true =>
            rw [he, if_pos rfl] at h
            cases h
            exact Or.inl rfl
        | nil =>
          dsimp only at h
          injection h with h
          injection h with _ h
          injection h with h _
          injection h with h
          rcases union_univ h with h1 | h1
          · exact Or.inl (by rw [h1])
          · rcases union_univ h1 with h2 | h2
            · rcases tailExcl_univ h2 with h3 | h3
              · exact Or.inr (Or.inr (Or.inr ⟨h3, rfl⟩))
              · exact Or.inr (Or.inl h3)
            · exact Or.inr (Or.inr (Or.inl (by rw [h2])))
      | any => cases h
      | exact =>
        cases fk with
        | exact => exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
        | star e' => cases h
        | any => cases h

theorem gate_ok_conc {t : Mark} {cm : MarkA} (h : markGate (.conc t) cm = .ok) :
    ∃ t', cm = .conc t' := by
  cases cm with
  | conc t' => exact ⟨t', rfl⟩
  | star => cases h
  | starEx x =>
    have h' : (if memB t x = true then Gate.no else Gate.req t) = .ok := h
    cases hm : memB t x with
    | true => rw [hm, if_pos rfl] at h'; cases h'
    | false => rw [hm, if_neg Bool.false_ne_true] at h'; cases h'

/-- A `*/Universe` normal form comes from a `*/Universe` fact with an abstract mark. -/
theorem norm_univ {x : AFact} (h : x.norm.fact.kind = .star .univ) :
    x.fact.kind = .star .univ ∧ AbsMark x.fact.mark := by
  have hl := (norm_legal h).1
  rw [CoreAux.norm_mark] at hl
  refine ⟨?_, hl⟩
  obtain ⟨⟨b, p, k, m⟩, d⟩ := x
  cases k with
  | star e => cases m <;> cases d <;> cases e <;> first | exact h | cases h
  | any => cases h
  | exact => cases h

/-- `applyEdge` makes no `*/Universe` result from a fact without it, if the edge has no
    `*/Universe` kind and a `$` premise has a concrete mark or meets a non-`*` fact. -/
theorem applyEdge_no_univ {c r : AFact} {fr to : PFact}
    (hc : c.fact.kind ≠ .star .univ) (hfr : fr.kind ≠ .star .univ) (hto : to.kind ≠ .star .univ)
    (hex : fr.kind = .exact → (∃ t, fr.mark = .conc t) ∨ c.fact.kind.isStar = false)
    (hr : r ∈ (applyEdge c fr to).facts) : r.fact.kind ≠ .star .univ := by
  intro hk
  obtain ⟨p, k, ap, m, hg, hgate, hm, rfl⟩ := CoreAux.mem_applyEdge_facts_inv hr
  obtain ⟨hk', habs⟩ := norm_univ hk
  have hk2 : k = .star .univ := hk'
  subst hk2
  unfold CoreAux.geo at hg
  cases hrel : relate fr.path c.fact.path with
  | apart => rw [hrel] at hg; cases hg
  | above r0 => rw [hrel] at hg; exact absurd (aboveCase_nonstar hg) (by decide)
  | below r0 =>
    rw [hrel] at hg
    rcases belowCase_univ hg with h1 | h1 | h1 | ⟨h1, h2⟩
    · exact hc h1
    · exact hfr h1
    · exact hto h1
    · rcases hex h1 with ⟨t, ht⟩ | h3
      · rw [ht] at hgate
        obtain ⟨t', ht'⟩ := gate_ok_conc hgate
        rw [ht'] at hm
        obtain ⟨t'', ht''⟩ := CoreAux.markComp_conc hm
        exact habs.not_conc t'' ht''
      · rw [h2] at h3; cases h3

/-- A `$` premise covers only a `$` or a `*/Universe` fact. -/
theorem applicable_exact_nonstar {j a : PFact} (hj : j.kind = .exact) (ha : a.kind ≠ .star .univ)
    (h : applicable j a = true) : a.kind.isStar = false := by
  unfold applicable coversB at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨_, _⟩, hd⟩, _⟩ := h
  rw [hj] at hd
  cases hdp : dropPrefix j.path a.path with
  | none => rw [hdp] at hd; cases hd
  | some r =>
    rw [hdp] at hd
    cases r with
    | cons x r => cases hd
    | nil =>
      dsimp only at hd
      cases hk : a.kind with
      | star e =>
        cases e with
        | univ => exact absurd hk ha
        | set xs => rw [hk] at hd; cases hd
      | any => rfl
      | exact => rfl

theorem applySummary_no_univ {a r g : AFact} {j : PFact}
    (ha : a.fact.kind ≠ .star .univ) (hj : j.kind ≠ .star .univ) (hg : g.fact.kind ≠ .star .univ)
    (happ : applicable j a.fact = true) (hr : r ∈ (applySummary a j g).facts) :
    r.fact.kind ≠ .star .univ := by
  obtain ⟨x, hx, rfl⟩ := applySummary_shape hr
  intro hk
  have hxk : x.fact.kind = .star .univ := (norm_univ hk).1
  exact applyEdge_no_univ ha hj hg (fun hje => Or.inr (applicable_exact_nonstar hje ha happ)) hx hxk

theorem limitF_no_univ {counted : Acc → Bool} {L : Nat} {f : AFact}
    (h : f.fact.kind ≠ .star .univ) : (limitF counted L f).fact.kind ≠ .star .univ := by
  rcases limitF_cases counted L f with e | ⟨hany, _⟩
  · rw [e]; exact h
  · rw [hany]; intro h'; cases h'

theorem startFact_no_univ {i : PFact} (h : i.kind ≠ .star .univ) :
    (startFact i).fact.kind ≠ .star .univ := by
  obtain ⟨b, p, k, m⟩ := i
  cases k with
  | star e =>
    cases m with
    | star => exact h
    | starEx _ => exact h
    | conc _ => intro h'; cases h'
  | any => cases m <;> (intro h'; cases h')
  | exact => exact h

theorem cleanRes_no_univ {cl : Cleaner} {c f : AFact} (hc : c.fact.kind ≠ .star .univ)
    (h : f ∈ (cleanRes cl c).facts) : f.fact.kind ≠ .star .univ := by
  rcases cleanRes_facts_cases h with rfl | ⟨t, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩
  · exact hc
  · exact hc
  · exact fun hk => hc (norm_univ hk).1
  · rcases concPart_cases cl c with h1 | ⟨_, h1⟩
    · rw [h1]; exact hc
    · rw [h1]; intro h'; cases h'

/-- (a) A micro edge with a `$` premise has a concrete premise mark. -/
def PremConc (e : MicroEdge) : Prop := e.1.kind = .exact → ∃ t, e.1.mark = .conc t

/-- (b) No premise and no target of a micro edge has the kind `*/Universe`. -/
def NoUnivE (e : MicroEdge) : Prop := e.1.kind ≠ .star .univ ∧ e.2.kind ≠ .star .univ

/-- Every micro edge of the program (statement edges and both call bindings) satisfies `Φ`. -/
def AllEdges (P : Program) (Φ : MicroEdge → Prop) : Prop :=
  (∀ M n s n', (M, n, Instr.stmt s, n') ∈ P.edges → ∀ e, e ∈ s.edges → Φ e) ∧
  (∀ M n c n', (M, n, Instr.call c, n') ∈ P.edges → ∀ e, e ∈ c.toCallee → Φ e) ∧
  (∀ M n c n', (M, n, Instr.call c, n') ∈ P.edges → ∀ e, e ∈ c.fromCallee → Φ e)

/-- The motive of `no_univ_star`. -/
def NU : Obj → Prop
  | .edge _ _ _ f => f.fact.kind ≠ .star .univ
  | _ => True

/-- The motive of `D_init_no_univ`: the initial fact of an object. -/
def NUI : Obj → Prop
  | .init _ i => i.kind ≠ .star .univ
  | .edge _ i _ _ => i.kind ≠ .star .univ
  | .req _ i _ => i.kind ≠ .star .univ
  | _ => True

theorem answerInit_kind (i a : PFact) (t : Mark) :
    (answerInit i a t).kind = .exact ∨ (answerInit i a t).kind = i.kind := by
  unfold answerInit
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The policy never gives the kind `*/Universe`. -/
theorem policy_no_univ (demand : MethodId → List PFact) (m : MethodId) (a : PFact) :
    (policy demand m a).kind ≠ .star .univ := by
  unfold policy
  split
  · intro h; cases h
  · split
    · intro h; cases h
    · intro h; cases h

section
variable (P : Program) (counted : Acc → Bool) (L : Nat) (α : MethodId → PFact → PFact)
  (sinks : List (MethodId × Node × PFact)) (roots : List MethodId)

/-- Hypothesis (c) from the abstraction: if `α` never gives `*/Universe`, no initial fact of
    `D` has it (the root is `$`; an answer is `$` or has the kind of its request). -/
theorem D_init_no_univ (hα : ∀ m a, (α m a).kind ≠ .star .univ) {o : Obj}
    (h : D P counted L α sinks roots o) : NUI o := by
  induction h with
  | root => intro h; cases h
  | start _ ih => exact ih
  | step _ _ _ ih => exact ih
  | reqStmt _ _ _ ih => exact ih
  | pass _ _ _ ih => exact ih
  | added => trivial
  | initA _ _ => exact hα _ _
  | ret _ _ _ _ _ _ _ _ _ _ ih _ _ => exact ih
  | reqSink _ _ _ ih => exact ih
  | @answer M i t a _ _ _ _ ihR _ =>
    rcases answerInit_kind i a t with h1 | h1
    · show (answerInit i a t).kind ≠ _
      rw [h1]; intro h; cases h
    · show (answerInit i a t).kind ≠ _
      rw [h1]; exact ihR
  | reqUp _ _ _ _ _ _ _ _ _ ihE => exact ihE
  | vuln => trivial
  | clean _ _ _ ih => exact ih
  | reqClean _ _ _ ih => exact ih
  | filt _ _ _ ih => exact ih

theorem D_no_univ (hA : AllEdges P PremConc) (hB : AllEdges P NoUnivE)
    (hC : ∀ M i, D P counted L α sinks roots (.init M i) → i.kind ≠ .star .univ)
    {o : Obj} (h : D P counted L α sinks roots o) : NU o := by
  induction h with
  | root => trivial
  | @start M i hi _ => exact startFact_no_univ (hC M i hi)
  | @step M i n f n' s f' _ hm hf' ih =>
    rcases transfer_mem hf' with rfl | ⟨x, e, he, hx, rfl⟩
    · exact ih
    · have hb := hB.1 _ _ _ _ hm e he
      exact limitF_no_univ (applyEdge_no_univ ih hb.1 hb.2
        (fun h0 => Or.inl (hA.1 _ _ _ _ hm e he h0)) hx)
  | reqStmt => trivial
  | pass _ _ _ ih => exact ih
  | added => trivial
  | initA => trivial
  | @ret M i n f n' c e1 a j g r e2 r' _ hm he1 ha1 hj happ _ hr he2 hr' ihF _ ihG =>
    have hb1 := hB.2.1 _ _ _ _ hm e1 he1
    have hb2 := hB.2.2 _ _ _ _ hm e2 he2
    have h1 := applyEdge_no_univ ihF hb1.1 hb1.2
      (fun h0 => Or.inl (hA.2.1 _ _ _ _ hm e1 he1 h0)) ha1
    have h2 := applySummary_no_univ h1 (hC _ _ hj) ihG happ hr
    exact limitF_no_univ (applyEdge_no_univ h2 hb2.1 hb2.2
      (fun h0 => Or.inl (hA.2.2 _ _ _ _ hm e2 he2 h0)) hr')
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial
  | clean _ _ hf' ih => exact cleanRes_no_univ ih hf'
  | reqClean => trivial
  | filt _ _ _ ih => exact ih

/-- The Universe exclusion never occurs on a `*` conclusion (hypotheses (a), (b), (c)). -/
theorem no_univ_star (hA : AllEdges P PremConc) (hB : AllEdges P NoUnivE)
    (hC : ∀ M i, D P counted L α sinks roots (.init M i) → i.kind ≠ .star .univ)
    {M : MethodId} {i : PFact} {n : Node} {f : AFact}
    (h : D P counted L α sinks roots (.edge M i n f)) : f.fact.kind ≠ .star .univ :=
  D_no_univ P counted L α sinks roots hA hB hC h

/-- The same with hypothesis (c) from the abstraction. -/
theorem no_univ_star_of_α (hA : AllEdges P PremConc) (hB : AllEdges P NoUnivE)
    (hα : ∀ m a, (α m a).kind ≠ .star .univ)
    {M : MethodId} {i : PFact} {n : Node} {f : AFact}
    (h : D P counted L α sinks roots (.edge M i n f)) : f.fact.kind ≠ .star .univ :=
  no_univ_star P counted L α sinks roots hA hB
    (fun _ _ hi => D_init_no_univ P counted L α sinks roots hα hi) h

/-- The same for the policy. -/
theorem no_univ_star_policy (demand : MethodId → List PFact) (hA : AllEdges P PremConc)
    (hB : AllEdges P NoUnivE) {M : MethodId} {i : PFact} {n : Node} {f : AFact}
    (h : D P counted L (policy demand) sinks roots (.edge M i n f)) :
    f.fact.kind ≠ .star .univ :=
  no_univ_star_of_α P counted L (policy demand) sinks roots hA hB (policy_no_univ demand) h

end

/-! ### The hypotheses stay: counterexamples -/

/-- (b) premise: a `*/Universe` premise makes a `*/Universe` result. -/
theorem no_univ_needs_premise :
    (applyEdge ⟨⟨1, [], .star (.set []), .star⟩, false⟩ ⟨1, [], .star .univ, .star⟩
      ⟨2, [], .star (.set []), .star⟩).facts = [⟨⟨2, [], .star .univ, .star⟩, false⟩] := by decide

/-- (b) target: a `*/Universe` target makes a `*/Universe` result. -/
theorem no_univ_needs_target :
    (applyEdge ⟨⟨1, [], .star (.set []), .star⟩, false⟩ ⟨1, [], .star (.set []), .star⟩
      ⟨2, [], .star .univ, .star⟩).facts = [⟨⟨2, [], .star .univ, .star⟩, false⟩] := by decide

/-- (c): a `*/Universe` initial fact with the mark `*` starts a `*/Universe` edge. -/
theorem no_univ_needs_init :
    (startFact ⟨1, [], .star .univ, .star⟩).fact.kind = .star .univ := by decide

/-- (a), one step: a `$` premise with the mark `*` makes a `*/Universe` result. -/
theorem no_univ_needs_premConc_step :
    (applyEdge ⟨⟨1, [], .star (.set []), .star⟩, false⟩ ⟨1, [], .exact, .star⟩
      ⟨2, [], .star (.set []), .star⟩).facts = [⟨⟨2, [], .star .univ, .star⟩, false⟩] := by decide

namespace CounterUniv

def s1 : Stmt := ⟨[1], [(⟨1, [], .exact, .star⟩, ⟨2, [], .star (.set []), .star⟩)]⟩
def P1 : Program :=
  ⟨fun _ => 0, fun _ => 1, [(0, 0, .call Run0.call0, 1), (1, 0, .stmt s1, 1)]⟩

end CounterUniv

open Run0 CounterUniv in
/-- (a) stays, as a run of `D`: the program `P1` meets (b) and (c) but not (a), and `D` has a
    `*/Universe` edge. -/
theorem no_univ_needs_premConc (counted : Acc → Bool) (L : Nat)
    (sinks : List (MethodId × Node × PFact)) :
    AllEdges P1 NoUnivE ∧
    (∀ M i, D P1 counted L α0 sinks [0] (.init M i) → i.kind ≠ .star .univ) ∧
    ¬ AllEdges P1 PremConc ∧
    D P1 counted L α0 sinks [0] (.edge 1 i0 1 ⟨⟨2, [], .star .univ, .star⟩, false⟩) := by
  have hB : AllEdges P1 NoUnivE := by
    refine ⟨?_, ?_, ?_⟩
    · intro M n s n' hm e he
      cases hm with
      | tail _ hm =>
        cases hm with
        | head =>
          cases he with
          | head => exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
          | tail _ he => cases he
        | tail _ hm => cases hm
    · intro M n c n' hm e he
      cases hm with
      | head =>
        cases he with
        | head => exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
        | tail _ he => cases he
      | tail _ hm =>
        cases hm with
        | tail _ hm => cases hm
    · intro M n c n' hm e he
      cases hm with
      | head => cases he
      | tail _ hm =>
        cases hm with
        | tail _ hm => cases hm
  have hα : ∀ m a, (α0 m a).kind ≠ .star .univ := fun _ _ h => by cases h
  refine ⟨hB, fun _ _ hi => D_init_no_univ P1 counted L α0 sinks [0] hα hi, ?_, ?_⟩
  · intro hA
    obtain ⟨t, ht⟩ := hA.1 1 0 s1 1 (List.Mem.tail _ (List.Mem.head _)) _ (List.Mem.head _) rfl
    cases ht
  · have h1 : D P1 counted L α0 sinks [0] (.init 0 zeroFact) := D.root (List.Mem.head _)
    have h2 := D.start h1
    have ha : (⟨a0, false⟩ : AFact) ∈ (applyEdge (startFact zeroFact) zeroFact a0).facts := by
      decide
    have h3 : D P1 counted L α0 sinks [0] (.added call0.callee a0) :=
      D.added (n' := 1) (e := (zeroFact, a0)) (a := ⟨a0, false⟩) h2 (List.Mem.head _)
        (List.Mem.head _) ha
    have h4 : D P1 counted L α0 sinks [0] (.init 1 i0) := D.initA h3
    have h5 := D.start h4
    have ht : (transfer counted L s1 (startFact i0)).facts =
        [⟨⟨2, [], .star .univ, .star⟩, false⟩] := rfl
    have hf : (⟨⟨2, [], .star .univ, .star⟩, false⟩ : AFact) ∈
        (transfer counted L s1 (startFact i0)).facts := by
      rw [ht]; exact List.Mem.head _
    exact D.step (s := s1) h5 (List.Mem.tail _ (List.Mem.head _)) hf

/-! ## W6 is a layer refinement (`demand_of_any_ok`)

  Rule W6 of the spec puts every `[any]` result in the demand layer. Claim: W6 only moves
  edges from the normal layer to the demand layer. `normA` is W6 on one fact. It keeps the
  fact (so the pair relation `den` of the edge), it only raises the layer, and it keeps the
  complete edges (`AFact.complete`), `LegalM`, `Legal` and `Q` (`demand_of_any_ok`,
  `normA_*`). After W6, the layer of an `[any]` fact (and of each fact that comes from it)
  is only a tag:
  * `applyEdge` ORs the layer of a non-`*` fact into each result and changes nothing else
    (`applyEdge_tag`); the results of a non-`*` fact are non-`*` (`geo_nonstar`);
  * `applySummary` does the same with the layer of the summary edge if no result is `*`
    (`applySummary_tag`). From a non-`*` summary conclusion a `*` result is only
    `*/Universe` (`belowCase_univ`), and a summary edge in the demand layer changes it into
    `$` (`summary_layer_changes_univ`). The hypotheses of `no_univ_star` exclude this case;
  * `cleanRes`, `limitF`, `transfer` of an untouched base, the rules `pass` and `filt` copy
    the layer or set it, and do not read it.
  So, if no edge has the kind `*/Universe`, a run with W6 has the same edge facts, each in
  the same or a higher layer, and the same complete edges. -/

/-- W6 on one fact: an `[any]` fact goes to the demand layer. -/
def normA (f : AFact) : AFact := if f.fact.kind.isAny then ⟨f.fact, true⟩ else f

theorem normA_cases (f : AFact) :
    normA f = f ∨ (f.fact.kind.isAny = true ∧ normA f = ⟨f.fact, true⟩) := by
  unfold normA
  cases h : f.fact.kind.isAny with
  | true => exact Or.inr ⟨rfl, if_pos rfl⟩
  | false => exact Or.inl (if_neg Bool.false_ne_true)

/-- W6 keeps the fact, only raises the layer, and keeps the complete edges. -/
theorem demand_of_any_ok (f : AFact) :
    (normA f).fact = f.fact ∧ (f.demand = true → (normA f).demand = true) ∧
    ((normA f).demand = f.demand ∨ (normA f).demand = true) ∧
    (normA f).complete = f.complete := by
  rcases normA_cases f with h | ⟨ha, h⟩ <;> rw [h]
  · exact ⟨rfl, id, Or.inl rfl, rfl⟩
  · refine ⟨rfl, fun _ => rfl, Or.inr rfl, ?_⟩
    show (!true && !f.fact.kind.isAny) = (!f.demand && !f.fact.kind.isAny)
    rw [ha]
    cases f.demand <;> rfl

theorem normA_den {i : PFact} {f : AFact} {l0 l1 : Loc} :
    den i (normA f).fact l0 l1 ↔ den i f.fact l0 l1 := by
  rw [(demand_of_any_ok f).1]

theorem normA_Q {ei : Excl} {f : AFact} (h : Q ei f) : Q ei (normA f) := by
  rcases normA_cases f with e | ⟨_, e⟩ <;> rw [e]
  · exact h
  · exact ⟨h.1, fun _ => Or.inl rfl⟩

theorem normA_Legal {f : AFact} (h : Legal f) : Legal (normA f) := by
  rcases normA_cases f with e | ⟨ha, e⟩ <;> rw [e]
  · exact h
  · intro x hk
    have hk' : f.fact.kind = .star x := hk
    rw [hk'] at ha
    cases ha

theorem normA_LegalM {f : AFact} (h : LegalM f) : LegalM (normA f) := by
  rcases normA_cases f with e | ⟨_, e⟩ <;> rw [e]
  · exact h
  · exact h

theorem norm_id_of_nonstar {x : AFact} (h : x.fact.kind.isStar = false) : x.norm = x := by
  obtain ⟨⟨b, p, k, m⟩, d⟩ := x
  cases k with
  | star e => cases h
  | any => rfl
  | exact => rfl

/-- The layer of a non-`*` fact is only a tag for `applyEdge`. -/
theorem applyEdge_tag {cf fr to : PFact} {d : Bool} (hc : cf.kind.isStar = false) :
    (applyEdge ⟨cf, d⟩ fr to).facts =
      (applyEdge ⟨cf, false⟩ fr to).facts.map (fun x => ⟨x.fact, d || x.demand⟩) := by
  rw [CoreAux.applyEdge_eq, CoreAux.applyEdge_eq]
  show (if Nat.beq cf.base fr.base = true then
      CoreAux.fin ⟨cf, d⟩ fr to (CoreAux.geo cf.kind fr.kind fr.path cf.path to.path to.kind)
      else Res.none).facts =
    List.map _ (if Nat.beq cf.base fr.base = true then
      CoreAux.fin ⟨cf, false⟩ fr to (CoreAux.geo cf.kind fr.kind fr.path cf.path to.path to.kind)
      else Res.none).facts
  cases hb : Nat.beq cf.base fr.base with
  | false => rfl
  | true =>
    rw [if_pos rfl, if_pos rfl]
    cases hg : CoreAux.geo cf.kind fr.kind fr.path cf.path to.path to.kind with
    | none => rfl
    | some x =>
      obtain ⟨p, k, ap⟩ := x
      have hk : k.isStar = false := geo_nonstar hc hg
      show (CoreAux.finG ⟨cf, d⟩ to p k ap (markGate fr.mark cf.mark)).facts =
        List.map _ (CoreAux.finG ⟨cf, false⟩ to p k ap (markGate fr.mark cf.mark)).facts
      cases markGate fr.mark cf.mark with
      | no => rfl
      | req t => rfl
      | ok =>
        show (CoreAux.finM ⟨cf, d⟩ to p k ap (markComp to.mark cf.mark)).facts =
          List.map _ (CoreAux.finM ⟨cf, false⟩ to p k ap (markComp to.mark cf.mark)).facts
        cases markComp to.mark cf.mark with
        | none => rfl
        | some m =>
          show [AFact.norm ⟨⟨to.base, p, k, m⟩, d || ap⟩] =
            List.map _ [AFact.norm ⟨⟨to.base, p, k, m⟩, false || ap⟩]
          rw [norm_id_of_nonstar (x := ⟨⟨to.base, p, k, m⟩, d || ap⟩) hk,
            norm_id_of_nonstar (x := ⟨⟨to.base, p, k, m⟩, false || ap⟩) hk]
          rfl

theorem map_tag_aux (d : Bool) : ∀ (xs : List AFact), (∀ x, x ∈ xs → x.fact.kind.isStar = false) →
    xs.map (fun x => AFact.norm ⟨x.fact, x.demand || d⟩) =
      (xs.map (fun x => AFact.norm ⟨x.fact, x.demand || false⟩)).map
        (fun x => ⟨x.fact, d || x.demand⟩)
  | [], _ => rfl
  | x :: xs, h => by
    show AFact.norm ⟨x.fact, x.demand || d⟩ :: _ =
      (fun x => (⟨x.fact, d || x.demand⟩ : AFact)) (AFact.norm ⟨x.fact, x.demand || false⟩) :: _
    rw [norm_id_of_nonstar (x := ⟨x.fact, x.demand || d⟩) (h x (List.Mem.head _)),
      norm_id_of_nonstar (x := ⟨x.fact, x.demand || false⟩) (h x (List.Mem.head _)),
      map_tag_aux d xs (fun y hy => h y (List.Mem.tail _ hy))]
    cases x.demand <;> cases d <;> rfl

/-- The layer of a summary edge is only a tag for `applySummary`, if no result is `*`. -/
theorem applySummary_tag {a g : AFact} {j : PFact} {d : Bool}
    (h : ∀ x, x ∈ (applyEdge a j g.fact).facts → x.fact.kind.isStar = false) :
    (applySummary a j ⟨g.fact, d⟩).facts =
      (applySummary a j ⟨g.fact, false⟩).facts.map (fun x => ⟨x.fact, d || x.demand⟩) :=
  map_tag_aux d _ h

/-- The limit of `applySummary_tag`: a summary edge in the demand layer changes a
    `*/Universe` result into `$` (the caller fact `1.*/Universe`, the premise `1.$`). -/
theorem summary_layer_changes_univ :
    (applySummary ⟨⟨1, [], .star .univ, .star⟩, false⟩ ⟨1, [], .exact, .star⟩
      ⟨⟨2, [], .exact, .star⟩, false⟩).facts = [⟨⟨2, [], .star .univ, .star⟩, false⟩] ∧
    (applySummary ⟨⟨1, [], .star .univ, .star⟩, false⟩ ⟨1, [], .exact, .star⟩
      ⟨⟨2, [], .exact, .star⟩, true⟩).facts = [⟨⟨2, [], .exact, .star⟩, true⟩] := by decide

#print axioms ApSpec.Invariant.D_inv
#print axioms ApSpec.Invariant.D_legal
#print axioms ApSpec.Invariant.final_star_abstract
#print axioms ApSpec.Invariant.final_star_legal
#print axioms ApSpec.Invariant.star_final_keeps_initial_excl
#print axioms ApSpec.Invariant.star_initial_complete
#print axioms ApSpec.Invariant.cleanAll_part_gives_any
#print axioms ApSpec.Invariant.D_no_univ
#print axioms ApSpec.Invariant.no_univ_star
#print axioms ApSpec.Invariant.no_univ_star_of_α
#print axioms ApSpec.Invariant.no_univ_star_policy
#print axioms ApSpec.Invariant.no_univ_needs_premConc
#print axioms ApSpec.Invariant.no_univ_needs_premise
#print axioms ApSpec.Invariant.no_univ_needs_target
#print axioms ApSpec.Invariant.no_univ_needs_init
#print axioms ApSpec.Invariant.demand_of_any_ok
#print axioms ApSpec.Invariant.normA_den
#print axioms ApSpec.Invariant.normA_Q
#print axioms ApSpec.Invariant.normA_Legal
#print axioms ApSpec.Invariant.applyEdge_tag
#print axioms ApSpec.Invariant.applySummary_tag
#print axioms ApSpec.Invariant.summary_layer_changes_univ

end ApSpec.Invariant

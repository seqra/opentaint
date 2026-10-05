/-
  ApSpec.Invariant — shape invariants of the analysis result.

  1. `final_star_legal`: a final fact with the `*` tail has the mark `*` and is
     complete (rule W2 and "the demand layer has no `*` leaf").
  2. `star_final_keeps_initial_excl`: a final `*/Ec` under an initial `*/Ei`
     keeps every exclusion of the initial (`Ei ⊆ Ec`).
  3. `star_initial_complete`: under an initial fact `*/Ei`, a final fact in the
     normal layer has the `*` tail, or `Ei` is empty. So every complete record
     with a `*` premise has an exact reversal (`Reverse.ExactShape`).
  4. `demand_monotone`: the demand layer never goes back to the normal layer.
     `applyEdge_demand_monotone`, `applySummary_demand_monotone`,
     `limitF_demand_monotone`, `transfer_demand_monotone` (rule `step`) and
     `demand_monotone_ret` (rule `ret`).
-/
import ApSpec.Core

namespace ApSpec.Invariant
open ApSpec

/-! ## The normal form -/

theorem norm_legal {x : AFact} {e : Excl} (h : x.norm.fact.kind = .star e) :
    x.norm.fact.mark = .star ∧ x.norm.demand = false := by
  obtain ⟨⟨b, p, k, m⟩, ap⟩ := x
  cases k with
  | star e0 =>
    cases m with
    | star =>
      cases ap with
      | false => cases e0 <;> exact ⟨rfl, rfl⟩
      | true => cases e0 <;> cases h
    | conc t => cases e0 <;> cases h
  | any => cases h
  | exact => cases h

/-! ## The shape of an `applyEdge` result -/

theorem applyEdge_shape {c r : AFact} {fr to : PFact} (h : r ∈ (applyEdge c fr to).facts) :
    ∃ p k ap, CoreAux.geo c.fact.kind fr.kind fr.path c.fact.path to.path to.kind = some (p, k, ap) ∧
      r = AFact.norm ⟨⟨to.base, p, k, markOutA to.mark c.fact.mark⟩, c.demand || ap⟩ := by
  rw [CoreAux.applyEdge_eq] at h
  cases hb : Nat.beq c.fact.base fr.base with
  | false =>
    rw [hb, if_neg Bool.false_ne_true] at h
    exact absurd h List.not_mem_nil
  | true =>
    rw [hb, if_pos rfl] at h
    cases hg : CoreAux.geo c.fact.kind fr.kind fr.path c.fact.path to.path to.kind with
    | none =>
      rw [hg] at h
      exact absurd h List.not_mem_nil
    | some x =>
      obtain ⟨p, k, ap⟩ := x
      rw [hg, CoreAux.fin_some] at h
      cases hgt : markGate fr.mark c.fact.mark with
      | ok =>
        rw [hgt] at h
        exact ⟨p, k, ap, rfl, List.mem_singleton.mp h⟩
      | no =>
        rw [hgt] at h
        exact absurd h List.not_mem_nil
      | req t =>
        rw [hgt] at h
        exact absurd h List.not_mem_nil

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

/-- Legality: a `*` fact has the mark `*` and is complete. -/
def Legal (c : AFact) : Prop := ∀ e, c.fact.kind = .star e → c.fact.mark = .star ∧ c.demand = false

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
    | conc t => cases e0 <;> exact ⟨fun _ hk => (by cases hk), fun _ => Or.inl rfl⟩
  | any => exact ⟨h1, h2⟩
  | exact => exact ⟨h1, h2⟩

theorem applyEdge_Q {ei : Excl} {c r : AFact} {fr to : PFact}
    (hq : Q ei c) (hl : Legal c) (hr : r ∈ (applyEdge c fr to).facts) : Q ei r := by
  obtain ⟨p, k, ap, hg, rfl⟩ := applyEdge_shape hr
  apply norm_Q
  obtain ⟨hq1, hq2⟩ := hq
  cases hck : c.fact.kind with
  | star ec =>
    have hsub := hq1 ec hck
    have hca : c.demand = false := (hl ec hck).2
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
    r.fact.mark = .star ∧ r.demand = false := by
  obtain ⟨p, k, ap, _, rfl⟩ := applyEdge_shape hr
  exact norm_legal hk

theorem applySummary_shape {a r g : AFact} {j : PFact} (h : r ∈ (applySummary a j g).facts) :
    ∃ x, x ∈ (applyEdge a j g.fact).facts ∧ r = AFact.norm ⟨x.fact, x.demand || g.demand⟩ := by
  obtain ⟨x, hx, e⟩ := List.mem_map.mp h
  exact ⟨x, hx, e.symm⟩

theorem applySummary_legal {a r g : AFact} {j : PFact} {e : Excl}
    (hr : r ∈ (applySummary a j g).facts) (hk : r.fact.kind = .star e) :
    r.fact.mark = .star ∧ r.demand = false := by
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
    (hf : ∀ e, f.fact.kind = .star e → f.fact.mark = .star ∧ f.demand = false)
    (hk : (limitF counted L f).fact.kind = .star e) :
    (limitF counted L f).fact.mark = .star ∧ (limitF counted L f).demand = false := by
  rcases limitF_cases counted L f with eq | ⟨hany, _⟩
  · rw [eq] at hk ⊢; exact hf e hk
  · rw [hany] at hk; cases hk

theorem startFact_legal {i : PFact} {e : Excl} (hk : (startFact i).fact.kind = .star e) :
    (startFact i).fact.mark = .star ∧ (startFact i).demand = false := by
  obtain ⟨b, p, k, m⟩ := i
  cases k with
  | star e0 =>
    cases m with
    | star => exact ⟨rfl, rfl⟩
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

theorem limitF_Q {counted : Acc → Bool} {L : Nat} {ei : Excl} {f : AFact} (h : Q ei f) :
    Q ei (limitF counted L f) := by
  rcases limitF_cases counted L f with e | ⟨hany, ha⟩
  · rw [e]; exact h
  · refine ⟨fun ec hk => ?_, fun _ => Or.inl ha⟩
    rw [hany] at hk; cases hk

theorem limitF_Legal {counted : Acc → Bool} {L : Nat} {f : AFact} (h : Legal f) :
    Legal (limitF counted L f) := fun _ hk => limitF_legal h hk

theorem startFact_Q {i : PFact} {ei : Excl} (hi : i.kind = .star ei) : Q ei (startFact i) := by
  obtain ⟨b, p, k, m⟩ := i
  cases hi
  cases m with
  | star => exact ⟨fun ec hk => (by cases hk; exact subB_refl ei), fun h => (by cases h)⟩
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
  obtain ⟨p, k, ap, _, rfl⟩ := applyEdge_shape hr
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

/-- W2 and the demand-layer invariant: a final `*` fact has the mark `*` and is complete. -/
theorem final_star_legal {M : MethodId} {i : PFact} {n : Node} {f : AFact} {e : Excl}
    (h : D P counted L α sinks roots (.edge M i n f)) (hk : f.fact.kind = .star e) :
    f.fact.mark = .star ∧ f.demand = false :=
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

#print axioms ApSpec.Invariant.final_star_legal
#print axioms ApSpec.Invariant.star_final_keeps_initial_excl
#print axioms ApSpec.Invariant.star_initial_complete

end ApSpec.Invariant

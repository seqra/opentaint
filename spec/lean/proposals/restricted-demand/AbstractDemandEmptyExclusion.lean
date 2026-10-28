/- Local boundary model for the user's 28 October 2026 decision:
   ignore field E on abstract STAR demand endpoints. Concrete demand,
   actual inputs, native records and executable transfer keep their E.
   The uniform entry/exit interpretation is explicit in the accompanying
   design fragment. This file changes no runtime operation.
   The earlier exclusion-union candidate is not used. -/
import ApSpec.AbsDefs
import ApSpec.CurrentSimplifications

namespace AbstractDemandEmptyExclusion
open ApSpec ApSpec.Reverse ApSpec.Handoff ApSpec.Abs
set_option autoImplicit false

/-- Apply after existing mark normalization, only to demand endpoints. -/
def clearAbstractFieldE (d : PFact) : PFact :=
  match d.mark, d.kind with
  | .star, .star _ => ⟨d.base, d.path, .star Excl.empty, d.mark⟩
  | _, _ => d

/-- Existing mark normalization, then the selected demand-field normalization. -/
def normalizeEndpoint (d : PFact) : PFact := clearAbstractFieldE (normFact d)

def normalizeDemand (d : DemandEdge) : DemandEdge :=
  ⟨normalizeEndpoint d.din, d.dout.map normalizeEndpoint⟩

theorem clear_covers {d : PFact} {l : Loc} (covered : d.covers l) :
    (clearAbstractFieldE d).covers l := by
  obtain ⟨b, p, k, m⟩ := d
  cases m with
  | conc _ => exact covered
  | starEx _ => exact covered
  | star =>
    cases k with
    | exact => exact covered
    | any => exact covered
    | star e =>
      obtain ⟨base, ⟨suffix, path, _⟩, mark⟩ := covered
      exact ⟨base, ⟨suffix, path, CoreAux.empty_admits suffix⟩, mark⟩

theorem normalization_enlarges {d : PFact} {l : Loc} (covered : d.covers l) :
    (normalizeEndpoint d).covers l := clear_covers (normFact_covers covered)

theorem concrete_unchanged {d : PFact} {t : Mark} (mark : d.mark = .conc t) :
    normalizeEndpoint d = d := by
  obtain ⟨b, p, k, m⟩ := d
  cases mark
  rfl

theorem normalized_abstract_guard (d : PFact)
    (abstractMark : (normalizeEndpoint d).mark = .star) :
    PatTailB (normalizeEndpoint d).kind = true := by
  obtain ⟨b, p, k, m⟩ := d
  cases m <;> cases k <;> simp_all [normalizeEndpoint, clearAbstractFieldE, normFact, markNorm, PatTailB, Excl.empty, Excl.isEmptyB]

theorem normalization_idempotent (d : PFact) :
    normalizeEndpoint (normalizeEndpoint d) = normalizeEndpoint d := by
  obtain ⟨b, p, k, m⟩ := d
  cases m <;> cases k <;> rfl

/-- C2 is relative to the normalized demand, whose field E is authoritative. -/
theorem normalized_entry_contract {d a : PFact} {l : Loc}
    (abstractMark : (normalizeEndpoint d).mark = .star)
    (demanded : (normalizeEndpoint d).covers l) (actual : a.covers l) :
    emitW (normalizeEndpoint d) a = some (flowForm (normalizeEndpoint d)) ∧
      (flowForm (normalizeEndpoint d)).covers l ∧
      satW (flowForm (normalizeEndpoint d)) a = true ∧
      insideB (flowForm (normalizeEndpoint d)) (normalizeEndpoint d) = true := by
  obtain ⟨emitted, covered, satisfied⟩ := emitW_contract_star abstractMark
    (normalized_abstract_guard d abstractMark) demanded actual
  exact ⟨emitted, covered, satisfied, flowForm_inside abstractMark⟩

/-- Every old demanded common location still receives a satisfiable witness. -/
theorem old_common_location_kept {d a : PFact} {l : Loc}
    (abstractMark : (normalizeEndpoint d).mark = .star)
    (demanded : d.covers l) (actual : a.covers l) :
    emitW (normalizeEndpoint d) a = some (flowForm (normalizeEndpoint d)) ∧
      (flowForm (normalizeEndpoint d)).covers l ∧
      satW (flowForm (normalizeEndpoint d)) a = true ∧
      insideB (flowForm (normalizeEndpoint d)) (normalizeEndpoint d) = true :=
  normalized_entry_contract abstractMark (normalization_enlarges demanded) actual

/-- Typed ANY or STAR demand keeps a correlated STAR/empty-E FLOW initial. -/
theorem typed_shared_initial_empty {d : PFact}
    (abstractMark : (normalizeEndpoint d).mark = .star)
    (typed : d.kind = .any ∨ ∃ e, d.kind = .star e) :
    (flowForm (normalizeEndpoint d)).kind = .star Excl.empty := by
  obtain ⟨b, p, k, m⟩ := d
  cases m <;> cases k <;>
    simp_all [normalizeEndpoint, clearAbstractFieldE, normFact, markNorm, flowForm, flowK]

/-- No actual mark or actual field E is copied into the shared initial. -/
theorem shared_initial_independent_of_actual (d a1 a2 : PFact)
    (served1 : emitW (normalizeEndpoint d) a1 = some (flowForm (normalizeEndpoint d)))
    (served2 : emitW (normalizeEndpoint d) a2 = some (flowForm (normalizeEndpoint d))) :
    emitW (normalizeEndpoint d) a1 = emitW (normalizeEndpoint d) a2 :=
  served1.trans served2.symm

/-- Widening a STAR demand to empty E preserves whole-location containment. -/
theorem inside_empty_star {j d : PFact} {e : Excl}
    (_kind : d.kind = .star e) (contained : insideLocB j d = true) :
    insideLocB j ⟨d.base, d.path, .star Excl.empty, .star⟩ = true := by
  unfold insideLocB coversB at contained ⊢
  dsimp only at contained ⊢
  cases hb : Nat.beq d.base j.base <;> simp [hb] at contained ⊢
  cases hp : dropPrefix d.path j.path with
  | none => simp [hp] at contained
  | some suffix =>
    cases suffix with
    | nil => simpa [hp, markSubB] using RCore.tailSubB_starEmpty j.kind
    | cons a rest => simp [admitsTailB, Excl.empty, Excl.admits, markSubB, memB]

/-- C5 still admits every original which was wholly inside the old entry. -/
theorem whole_guard_preserved {j d : PFact} (contained : insideB j d = true) :
    insideB j (normalizeEndpoint d) = true := by
  obtain ⟨b, p, k, m⟩ := d
  cases m with
  | conc t => exact contained
  | star =>
    have both := contained
    unfold insideB at both
    rw [Bool.and_eq_true] at both
    have loc := both.1
    cases k with
    | exact => simpa [normalizeEndpoint, clearAbstractFieldE, normFact, markNorm, insideB, insideLocB, markSubB] using loc
    | any => simpa [normalizeEndpoint, clearAbstractFieldE, normFact, markNorm, insideB, insideLocB, markSubB] using loc
    | star e =>
      have empty := inside_empty_star rfl loc
      simpa [normalizeEndpoint, clearAbstractFieldE, normFact, markNorm, insideB, insideLocB, markSubB] using empty
  | starEx x =>
    have both := contained
    unfold insideB at both
    rw [Bool.and_eq_true] at both
    have loc := both.1
    cases k with
    | exact => simpa [normalizeEndpoint, clearAbstractFieldE, normFact, markNorm, insideB, insideLocB, markSubB] using loc
    | any => simpa [normalizeEndpoint, clearAbstractFieldE, normFact, markNorm, insideB, insideLocB, markSubB] using loc
    | star e =>
      have empty := inside_empty_star rfl loc
      simpa [normalizeEndpoint, clearAbstractFieldE, normFact, markNorm, insideB, insideLocB, markSubB] using empty

/-- Normalizing both endpoints keeps every pair required by the old demand. -/
theorem old_required_pair_kept {j : PFact} {g : AFact} {d : DemandEdge}
    {exit : PFact} {l1 l2 : Loc}
    (contained : insideB j d.din = true) (pair : den j g.fact l1 l2)
    (hasExit : d.dout = some exit) (demanded : exit.covers l2) :
    ∃ g', restrictI j g (normalizeDemand d) = some g' ∧
      den j g'.fact l1 l2 ∧ g'.demand = g.demand :=
  restrictI_contract (whole_guard_preserved contained) pair
    (by simp [normalizeDemand, hasExit]) (normalization_enlarges demanded)

/-- The same C5 reduction still returns only raw pairs, in the raw layer. -/
theorem publication_has_only_raw_pairs {j : PFact} {g out : AFact} {d : DemandEdge}
    (published : restrictI j g (normalizeDemand d) = some out) :
    out.demand = g.demand ∧ ∀ l1 l2, den j out.fact l1 l2 → den j g.fact l1 l2 :=
  restrictI_sub j g (normalizeDemand d) out published

/-- The annotated current algebra retains actual E in canonical FLOW matching.
    A MUST actual is represented by ANY plus its separate annotation E here. -/
theorem canonical_match_keeps_actual_E (base : Base) (path : List Acc)
    (actual : PFact) (actualE : Excl) :
    (ApSpec.AnyTaintEx.satX ⟨base, path, .star Excl.empty, .star⟩ Excl.empty actual actualE ||
      applicable ⟨base, path, .star Excl.empty, .star⟩ actual) =
    ApSpec.AnyTaintEx.overlapX ⟨base, path, .star Excl.empty, .star⟩ Excl.empty actual actualE :=
  ApSpec.CurrentSimplifications.Flow.canonical_flow_satisfaction_X base path actual actualE

/-- C2's shared initial also satisfies the annotated MUST-input boundary.
    Demand E is cleared; actual E is read through overlapX without alteration. -/
theorem annotated_actual_contract {d a : PFact} {l : Loc} {actualE : Excl}
    (abstractMark : (normalizeEndpoint d).mark = .star)
    (typed : d.kind = .any ∨ ∃ e, d.kind = .star e)
    (demanded : d.covers l) (actual : ApSpec.AnyTaintEx.coversX a actualE l) :
    let j := flowForm (normalizeEndpoint d)
    emitW (normalizeEndpoint d) a = some j ∧ j.covers l ∧
      (ApSpec.AnyTaintEx.satX j Excl.empty a actualE || applicable j a) = true ∧
      insideB j (normalizeEndpoint d) = true := by
  have plainActual : a.covers l := by
    obtain ⟨base, ⟨suffix, path, tail, _⟩, mark⟩ := actual
    exact ⟨base, ⟨suffix, path, tail⟩, mark⟩
  obtain ⟨emitted, covered, _, contained⟩ := old_common_location_kept abstractMark demanded plainActual
  refine ⟨emitted, covered, ?_, contained⟩
  have canonical : flowForm (normalizeEndpoint d) =
      ⟨(normalizeEndpoint d).base, (normalizeEndpoint d).path, .star Excl.empty, .star⟩ := by
    have tail := typed_shared_initial_empty abstractMark typed
    change flowK (normalizeEndpoint d).kind = .star Excl.empty at tail
    unfold flowForm
    rw [tail]
  rw [canonical, canonical_match_keeps_actual_E]
  apply ApSpec.AnyTaintExCov.overlapX_of_common
  · exact ApSpec.AnyTaintExCov.covLoc_of_covers (canonical ▸ covered)
  · exact ApSpec.AnyTaintExCov.covLoc_of_coversX actual

/-- An ignored demand E does not clear the actual STAR input's E. -/
theorem blocked_actual_star_still_rejected :
    emitW (normalizeEndpoint ⟨3, [10], .star (.set [11]), .star⟩)
      ⟨3, [], .star (.set [10]), .conc 7⟩ = none := rfl

/-- Same control with an annotated MUST input: the actual E blocks descent. -/
theorem blocked_actual_must_still_rejected :
    (ApSpec.AnyTaintEx.satX ⟨3, [10], .star Excl.empty, .star⟩ Excl.empty
      ⟨3, [], .any, .conc 7⟩ (.set [10]) ||
      applicable ⟨3, [10], .star Excl.empty, .star⟩ ⟨3, [], .any, .conc 7⟩) = false := rfl

/-- Concrete entry eligibility still rejects abstract actual marks. -/
theorem concrete_demand_cannot_obtain_T_from_FLOW :
    emitW (normalizeEndpoint ⟨3, [], .star (.set [10]), .conc 7⟩)
      ⟨3, [], .star Excl.empty, .star⟩ = none := rfl

/-- Clearing exit demand E is a real permission widening, not field transfer. -/
theorem exit_normalization_widens_permission :
    let initial : PFact := ⟨3, [], .exact, .conc 7⟩
    let raw : AFact := ⟨⟨4, [10], .exact, .conc 7⟩, false⟩
    let guide : DemandEdge := ⟨⟨3, [], .any, .conc 7⟩, some ⟨4, [], .star (.set [10]), .star⟩⟩
    restrictI initial raw guide = none ∧
      restrictI initial raw (normalizeDemand guide) = some raw := by decide

#print axioms blocked_actual_star_still_rejected
#print axioms blocked_actual_must_still_rejected
#print axioms concrete_demand_cannot_obtain_T_from_FLOW
#print axioms exit_normalization_widens_permission
#print axioms inside_empty_star
#print axioms whole_guard_preserved
#print axioms old_required_pair_kept
#print axioms publication_has_only_raw_pairs
#print axioms canonical_match_keeps_actual_E
#print axioms annotated_actual_contract
#print axioms clear_covers
#print axioms normalization_enlarges
#print axioms concrete_unchanged
#print axioms normalized_abstract_guard
#print axioms normalization_idempotent
#print axioms normalized_entry_contract
#print axioms old_common_location_kept
#print axioms typed_shared_initial_empty
#print axioms shared_initial_independent_of_actual
end AbstractDemandEmptyExclusion

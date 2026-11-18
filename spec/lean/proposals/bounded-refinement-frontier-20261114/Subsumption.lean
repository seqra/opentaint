import Frontier

namespace BoundedRefinementSubsumption
open NonEmptyPolicy NonEmptyRestriction NonEmptyCoverage BoundedRefinementFrontier

def parent : Ap := flow .may
def deeper : Ap := flow .ne [1]
def offered : Offered := ⟨full .exact [1,2],false⟩

theorem parent_and_child_have_different_admission_images :
    emit 3 2 false parent offered =
      [⟨flow .star [1],false⟩,⟨flow .exact,false⟩] ∧
    emit 3 2 false deeper offered = [⟨flow .exact [1,2],false⟩] := by decide

theorem semantic_may_coverage_does_hold :
    coversPost [] .may [1] .nonEmpty := by
  simpa using may_prefix_covers_nonempty_descendant [] [1]

/-- Even the new one-step parent plan cannot authorize the child row's
    two-field raw initial. Its original bound remains one. -/
theorem a_parent_plan_cannot_admit_the_deeper_initial (base : Seed)
    (old : legalSeed 2 parent base) (field : Nat) :
    (⟨flow .exact [1,2],false⟩ : Seed) ∉ oneFieldPlan 2 parent base field := by
  intro member
  have bound := (one_field_plan_keeps_both_original_bounds
    2 parent base ⟨flow .exact [1,2],false⟩ field old member).2
  change 2 ≤ 1 at bound
  omega

theorem same_head_ne_plan_is_covered_by_may_plan :
    (oneFieldPlan 2 (flow .ne) ⟨flow .star,false⟩ 1).all
      (fun q => (oneFieldPlan 2 (flow .may) ⟨flow .star,false⟩ 1).contains q) = true := by decide

theorem normal_service_can_discharge_captured_demand (normal demand : List Ap)
    (cover : serviceCovers normal demand) (key : Ap) :
    key ∈ normal ++ demand ↔ key ∈ normal := by
  constructor
  · intro member
    rcases List.mem_append.mp member with already | captured
    · exact already
    · exact cover key captured
  · intro member
    exact List.mem_append.mpr (Or.inl member)

theorem refinement_service_cover_is_transitive (a b c : List Ap)
    (ab : serviceCovers a b) (bc : serviceCovers b c) : serviceCovers a c :=
  service_cover_is_transitive a b c ab bc

theorem captured_heads_do_not_depend_on_arrival_order (head : Path) :
    head ∈ retainHead (retainHead [] []) [1] ↔
    head ∈ retainHead (retainHead [] [1]) [] := by
  change head ∈ [[1],[]] ↔ head ∈ [[],[1]]
  simp only [List.mem_cons,List.not_mem_nil,or_false]
  exact or_comm

end BoundedRefinementSubsumption

#print axioms BoundedRefinementSubsumption.parent_and_child_have_different_admission_images
#print axioms BoundedRefinementSubsumption.semantic_may_coverage_does_hold
#print axioms BoundedRefinementSubsumption.a_parent_plan_cannot_admit_the_deeper_initial
#print axioms BoundedRefinementSubsumption.same_head_ne_plan_is_covered_by_may_plan
#print axioms BoundedRefinementSubsumption.normal_service_can_discharge_captured_demand
#print axioms BoundedRefinementSubsumption.refinement_service_cover_is_transitive
#print axioms BoundedRefinementSubsumption.captured_heads_do_not_depend_on_arrival_order

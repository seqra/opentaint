/-
Selected delta to checked RelativeAdmission + ConcreteStarFlowCompanion.
An ordinary STAR actual cannot supply a strictly deeper initial demand.
No imported operator or theorem is edited. MUST/ANY actuals and every other
cell retain their old behavior. The structural image is unchanged because
every old output template has a legal, unblocked constructive actual witness.
-/
import ConcreteStarFlowCompanion

namespace RejectAncestorStarAdmission
open PlainStarRelativeAdmission
open ConcreteStarFlowCompanion

def blocked (d : Demand) (actual : Actual) : Bool :=
  decide (actual.pattern.tail = .star ∧ actual.pattern.path.length < d.path.length) &&
    (ApSpec.dropPrefix actual.pattern.path d.path).isSome

def emit (mode : Mode) (d : Demand) (actual : Actual) : Option Seed :=
  if blocked d actual then none else PlainStarRelativeAdmission.emit mode d actual

def emitSeeds (mode : Mode) (d : Demand) (actual : Actual) : List Seed :=
  match emit mode d actual with
  | none => []
  | some primary => expanded primary

def command (mode : Mode) (d : Demand) (actual : Actual) : Command :=
  ⟨actual,emitSeeds mode d actual⟩

theorem strict_ancestor_STAR_is_blocked (d : Demand) (actual : Actual)
    (star : actual.pattern.tail = .star) (field : Nat) (rest : List Nat)
    (deeper : d.path = actual.pattern.path ++ (field :: rest)) : blocked d actual = true := by
  have located : ApSpec.dropPrefix actual.pattern.path d.path = some (field :: rest) :=
    ApSpec.CoreAux.dropPrefix_some.mpr deeper
  have length : actual.pattern.path.length < d.path.length := by
    rw [deeper,List.length_append,List.length_cons]
    omega
  simp [blocked,star,length,located]

theorem same_head_is_not_blocked (d : Demand) (actual : Actual)
    (same : actual.pattern.path = d.path) : blocked d actual = false := by
  simp [blocked,same]

theorem actual_at_or_below_demand_is_not_blocked (d : Demand) (actual : Actual)
    (length : d.path.length ≤ actual.pattern.path.length) : blocked d actual = false := by
  have notLess : ¬actual.pattern.path.length < d.path.length := by omega
  simp [blocked,notLess]

theorem non_STAR_actual_is_not_blocked (d : Demand) (actual : Actual)
    (notStar : actual.pattern.tail ≠ .star) : blocked d actual = false := by
  simp [blocked,notStar]

theorem new_stream_is_only_a_precheck (mode : Mode) (d : Demand) (actual : Actual) :
    emitSeeds mode d actual =
      if blocked d actual then [] else ConcreteStarFlowCompanion.emitSeeds mode d actual := by
  cases check : blocked d actual <;>
    simp [emitSeeds,emit,check,ConcreteStarFlowCompanion.emitSeeds]
  all_goals rfl

theorem unblocked_primary_and_layer_are_identical (mode : Mode) (d : Demand) (actual : Actual)
    (accepted : blocked d actual = false) :
    emit mode d actual = PlainStarRelativeAdmission.emit mode d actual := by simp [emit,accepted]

theorem blocked_primary_has_no_companion (mode : Mode) (d : Demand) (actual : Actual)
    (rejected : blocked d actual = true) : emitSeeds mode d actual = [] := by
  simp [emitSeeds,emit,rejected]

theorem same_head_stream_is_unchanged (mode : Mode) (d : Demand) (actual : Actual)
    (same : actual.pattern.path = d.path) :
    emitSeeds mode d actual = ConcreteStarFlowCompanion.emitSeeds mode d actual := by
  simp [new_stream_is_only_a_precheck,same_head_is_not_blocked d actual same]

theorem MUST_and_ANY_actual_streams_are_unchanged (mode : Mode) (d : Demand) (actual : Actual)
    (tail : actual.pattern.tail = .must ∨ actual.pattern.tail = .any) :
    emitSeeds mode d actual = ConcreteStarFlowCompanion.emitSeeds mode d actual := by
  have notStar : actual.pattern.tail ≠ .star := by rcases tail with h | h <;> simp [h]
  simp [new_stream_is_only_a_precheck,non_STAR_actual_is_not_blocked d actual notStar]

theorem no_new_seed_or_layer_is_introduced (mode : Mode) (d : Demand) (actual : Actual)
    (result : Seed) (member : result ∈ emitSeeds mode d actual) :
    result ∈ ConcreteStarFlowCompanion.emitSeeds mode d actual := by
  rw [new_stream_is_only_a_precheck] at member
  split at member
  next => simp at member
  next => exact member

theorem original_actual_is_not_modified (mode : Mode) (d : Demand) (actual : Actual) :
    (command mode d actual).originalActual = actual := rfl

theorem template_witness_is_never_blocked (d : Demand) (template : Template) :
    blocked d (templateActual d template) = false := by
  cases template with
  | rootExact => simp [blocked,templateActual,render]
  | rootMust e => simp [blocked,templateActual,render]
  | childExact field => simp [blocked,templateActual,render]
  | childStar field =>
    have notLess : ¬d.path.length + 1 < d.path.length := by omega
    simp [blocked,templateActual,render,notLess]
  | rootStar =>
    by_cases shape : d.shape = .star
    · simp [templateActual,shape,blocked]
    · simp [templateActual,shape,blocked,render]

theorem old_raw_image_has_an_unblocked_executable_primary
    (mode : Mode) (d : Demand) (initial : Pattern)
    (image : rawImage mode d initial = true) :
    ∃ actual, legalActual mode actual ∧ blocked d actual = false ∧
      emit mode d actual = some ⟨initial,intrinsic initial⟩ := by
  obtain ⟨template,allowed,same⟩ :=
    (raw_image_iff_relative_allowed_template mode d initial).mp image
  obtain ⟨legal,emitted⟩ := allowed_template_has_legal_executable_witness mode d template allowed
  have openQuery := template_witness_is_never_blocked d template
  refine ⟨templateActual d template,legal,openQuery,?_⟩
  simpa [emit,openQuery,same] using emitted

theorem original_raw_permission_still_has_an_executable_new_seed
    (mode : Mode) (d : Demand) (raw : Pattern) (permission : RawPermission mode d raw) :
    ∃ actual result, result ∈ emitSeeds mode d actual ∧ result.initial = raw := by
  rcases permission with old | ⟨primary,image,made⟩
  · obtain ⟨actual,legal,notBlocked,emitted⟩ :=
      old_raw_image_has_an_unblocked_executable_primary mode d raw old
    refine ⟨actual,⟨raw,intrinsic raw⟩,?_,rfl⟩
    simp [emitSeeds,emitted,expanded]
  · obtain ⟨actual,legal,notBlocked,emitted⟩ :=
      old_raw_image_has_an_unblocked_executable_primary mode d primary image
    let original : Seed := ⟨primary,intrinsic primary⟩
    let result : Seed := ⟨raw,.normal⟩
    have supplied : companionSeed original = some result := by
      simp [companionSeed,original,result,made]
    refine ⟨actual,result,?_,rfl⟩
    rw [emitSeeds,emitted]
    exact companion_always_in_expansion original result supplied

theorem structural_C2_image_is_unchanged (mode : Mode) (d : Demand) (raw : Pattern) :
    RawPermission mode d raw ↔
      ∃ actual result, result ∈ emitSeeds mode d actual ∧ result.initial = raw := by
  constructor
  · exact original_raw_permission_still_has_an_executable_new_seed mode d raw
  · rintro ⟨actual,result,member,same⟩
    rw [← same]
    exact every_executable_emission_has_raw_permission mode d actual result
      (no_new_seed_or_layer_is_introduced mode d actual result member)

theorem normalized_C5_image_is_unchanged (mode : Mode) (d : Demand) (stored : Pattern) :
    StoredPermission mode d stored ↔
      ∃ actual result, result ∈ emitSeeds mode d actual ∧ publicInitial result.initial = stored := by
  constructor
  · intro permission
    obtain ⟨oldActual,oldSeed,oldMember,normalized⟩ :=
      stored_permission_has_normalized_executable_actual mode d stored permission
    have rawPermission := every_executable_emission_has_raw_permission mode d oldActual oldSeed oldMember
    obtain ⟨actual,result,member,same⟩ :=
      original_raw_permission_still_has_an_executable_new_seed mode d oldSeed.initial rawPermission
    exact ⟨actual,result,member,by simpa [same] using normalized⟩
  · rintro ⟨actual,result,member,normalized⟩
    exact (stored_permission_exactly_matches_normalized_C2 mode d stored).mpr
      ⟨actual,result,no_new_seed_or_layer_is_introduced mode d actual result member,normalized⟩

theorem no_ANY_initial_is_introduced (mode : Mode) (d : Demand) (actual : Actual)
    (result : Seed) (member : result ∈ emitSeeds mode d actual) : result.initial.tail ≠ .any := by
  have permission := every_executable_emission_has_raw_permission mode d actual result
    (no_new_seed_or_layer_is_introduced mode d actual result member)
  rcases permission with old | ⟨primary,image,made⟩
  · exact (raw_image_preserves_base_mark_budget_and_has_no_ANY mode d result.initial old).2.2.2.1
  · have geometry := companion_has_same_geometry_and_NORMAL_FLOW primary result.initial made
    simp [geometry.2.2.1]

theorem H_free_identity_start_is_unchanged (seed : Seed) :
    (start seed).hasProtection = false := rfl

def exampleMode : Mode := ⟨3,2,.forward⟩
def exampleDemand : Demand := ⟨1,[4],.exact,.full 7,[]⟩
def ancestorSTAR : Actual := ⟨⟨1,[],.star,.full 7,[]⟩,.demand,false⟩

theorem selected_concrete_ancestor_example_now_rejects :
    PlainStarRelativeAdmission.emit exampleMode exampleDemand ancestorSTAR =
      some ⟨⟨1,[4],.exact,.full 7,[]⟩,.demand⟩ ∧
    emitSeeds exampleMode exampleDemand ancestorSTAR = [] := by decide

theorem same_head_STAR_keeps_primary_and_FLOW_companion :
    emitSeeds exampleMode ⟨1,[],.any,.full 7,[]⟩ ancestorSTAR =
      [⟨⟨1,[],.star,.full 7,[]⟩,.demand⟩,⟨⟨1,[],.star,.flow,[]⟩,.normal⟩] := by decide

end RejectAncestorStarAdmission

#print axioms RejectAncestorStarAdmission.strict_ancestor_STAR_is_blocked
#print axioms RejectAncestorStarAdmission.same_head_is_not_blocked
#print axioms RejectAncestorStarAdmission.actual_at_or_below_demand_is_not_blocked
#print axioms RejectAncestorStarAdmission.non_STAR_actual_is_not_blocked
#print axioms RejectAncestorStarAdmission.new_stream_is_only_a_precheck
#print axioms RejectAncestorStarAdmission.unblocked_primary_and_layer_are_identical
#print axioms RejectAncestorStarAdmission.blocked_primary_has_no_companion
#print axioms RejectAncestorStarAdmission.same_head_stream_is_unchanged
#print axioms RejectAncestorStarAdmission.MUST_and_ANY_actual_streams_are_unchanged
#print axioms RejectAncestorStarAdmission.no_new_seed_or_layer_is_introduced
#print axioms RejectAncestorStarAdmission.original_actual_is_not_modified
#print axioms RejectAncestorStarAdmission.template_witness_is_never_blocked
#print axioms RejectAncestorStarAdmission.old_raw_image_has_an_unblocked_executable_primary
#print axioms RejectAncestorStarAdmission.original_raw_permission_still_has_an_executable_new_seed
#print axioms RejectAncestorStarAdmission.structural_C2_image_is_unchanged
#print axioms RejectAncestorStarAdmission.normalized_C5_image_is_unchanged
#print axioms RejectAncestorStarAdmission.no_ANY_initial_is_introduced
#print axioms RejectAncestorStarAdmission.H_free_identity_start_is_unchanged
#print axioms RejectAncestorStarAdmission.selected_concrete_ancestor_example_now_rejects
#print axioms RejectAncestorStarAdmission.same_head_STAR_keeps_primary_and_FLOW_companion

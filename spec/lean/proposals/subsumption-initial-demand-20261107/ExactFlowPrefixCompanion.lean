/-
Selected scalar FULL C2 extension. An ANY demand with a strictly deeper
submitted actual adds a raw EXACT/FLOW/NORMAL prefix identity, only after a
successful latest primary admission. Keep old primary and STAR mark companion.
No early EXACT-to-STAR conversion is performed. The unchanged whole-summary
normalizer supplies the public STAR/FLOW premise at publication.

Both FLOW and full-mark demand scopes are included; GROUP, mark-exclusion
catalogs and typed JVM anchors remain native adapters. No field transfer,
source gate, actual support, H flag or C5 paired exit is changed here.
-/
import RejectAncestorStarAdmission

namespace ExactFlowPrefixCompanion
open PlainStarRelativeAdmission
open ConcreteStarFlowCompanion

def prefixSeed (d : Demand) : Seed :=
  ⟨⟨d.base,d.path,.exact,.flow,[]⟩,.normal⟩

def prefixPublic (d : Demand) : Pattern :=
  ⟨d.base,d.path,.star,.flow,[]⟩

def wanted (d : Demand) (actual : Actual) : Bool :=
  decide (d.shape = .any ∧ d.path.length < actual.pattern.path.length ∧
    (ApSpec.dropPrefix d.path actual.pattern.path).isSome = true)

def extra (mode : Mode) (d : Demand) (actual : Actual) : Option Seed :=
  if wanted d actual then
    (RejectAncestorStarAdmission.emit mode d actual).map fun _ => prefixSeed d
  else none

def emitSeeds (mode : Mode) (d : Demand) (actual : Actual) : List Seed :=
  RejectAncestorStarAdmission.emitSeeds mode d actual ++ (extra mode d actual).toList

def command (mode : Mode) (d : Demand) (actual : Actual) : Command :=
  ⟨actual,emitSeeds mode d actual⟩

theorem old_seed_and_layer_are_retained (mode : Mode) (d : Demand) (actual : Actual)
    (seed : Seed) (member : seed ∈ RejectAncestorStarAdmission.emitSeeds mode d actual) :
    seed ∈ emitSeeds mode d actual := List.mem_append_left _ member

theorem extra_requires_a_real_primary (mode : Mode) (d : Demand) (actual : Actual) (seed : Seed)
    (made : extra mode d actual = some seed) :
    wanted d actual = true ∧ ∃ primary,
      RejectAncestorStarAdmission.emit mode d actual = some primary ∧ seed = prefixSeed d := by
  unfold extra at made
  split at made
  next yes =>
    cases primary : RejectAncestorStarAdmission.emit mode d actual with
    | none => simp [primary] at made
    | some value =>
      simp only [primary,Option.map_some,Option.some.injEq] at made
      exact ⟨yes,⟨value,rfl,made.symm⟩⟩
  next => cases made

theorem no_primary_means_no_extra (mode : Mode) (d : Demand) (actual : Actual)
    (absent : RejectAncestorStarAdmission.emit mode d actual = none) : extra mode d actual = none := by
  simp [extra,absent]

theorem no_strict_descendant_means_old_stream (mode : Mode) (d : Demand) (actual : Actual)
    (notWanted : wanted d actual = false) :
    emitSeeds mode d actual = RejectAncestorStarAdmission.emitSeeds mode d actual := by
  simp [emitSeeds,extra,notWanted]

theorem same_head_is_unchanged (mode : Mode) (d : Demand) (actual : Actual)
    (same : actual.pattern.path = d.path) :
    emitSeeds mode d actual = RejectAncestorStarAdmission.emitSeeds mode d actual := by
  apply no_strict_descendant_means_old_stream
  simp [wanted,same]

theorem non_ANY_demand_is_unchanged (mode : Mode) (d : Demand) (actual : Actual)
    (notAny : d.shape ≠ .any) :
    emitSeeds mode d actual = RejectAncestorStarAdmission.emitSeeds mode d actual := by
  apply no_strict_descendant_means_old_stream
  simp [wanted,notAny]

theorem prefix_is_raw_EXACT_FLOW_NORMAL_with_empty_E (d : Demand) :
    (prefixSeed d).initial.base = d.base ∧ (prefixSeed d).initial.path = d.path ∧
      (prefixSeed d).initial.tail = .exact ∧ (prefixSeed d).initial.mark = .flow ∧
      (prefixSeed d).initial.exclusion = [] ∧ (prefixSeed d).layer = .normal :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem prefix_start_is_an_H_free_exact_identity (d : Demand) :
    start (prefixSeed d) = ⟨(prefixSeed d).initial,.normal,false⟩ := rfl

theorem public_prefix_uses_only_existing_FLOW_normalization (d : Demand) :
    publicInitial (prefixSeed d).initial = prefixPublic d := rfl

theorem original_actual_E_layer_mark_and_H_are_retained (mode : Mode) (d : Demand) (actual : Actual) :
    (command mode d actual).originalActual = actual := rfl

theorem latest_primary_retains_old_common_legality (mode : Mode) (d : Demand) (actual : Actual)
    (seed : Seed) (made : RejectAncestorStarAdmission.emit mode d actual = some seed) :
    commonLegal mode d actual := by
  have oldMade : PlainStarRelativeAdmission.emit mode d actual = some seed := by
    unfold RejectAncestorStarAdmission.emit at made
    split at made
    next => cases made
    next => exact made
  cases chosen : selected mode d actual with
  | none => simp [PlainStarRelativeAdmission.emit,chosen] at oldMade
  | some template => exact selected_implies_common_legal mode d actual template chosen

theorem emitted_prefix_is_bounded_and_has_a_new_field_witness
    (mode : Mode) (d : Demand) (actual : Actual) (seed : Seed)
    (made : extra mode d actual = some seed) :
    seed.initial.path.length ≤ mode.limit ∧ d.path.length + 1 ≤ mode.limit := by
  obtain ⟨isWanted,primary,accepted,same⟩ := extra_requires_a_real_primary mode d actual seed made
  obtain ⟨any,strict,prefixPath⟩ := of_decide_eq_true isWanted
  obtain ⟨run,limit,valid,depth,legal,base,mark,provisional⟩ :=
    latest_primary_retains_old_common_legality mode d actual primary accepted
  have actualDepth := legal.1
  rw [same]
  exact ⟨depth,by omega⟩

theorem emitted_prefix_normalized_key_was_already_in_C5_image
    (mode : Mode) (d : Demand) (actual : Actual) (seed : Seed)
    (made : extra mode d actual = some seed) :
    StoredPermission mode d (publicInitial seed.initial) := by
  obtain ⟨isWanted,primary,accepted,same⟩ := extra_requires_a_real_primary mode d actual seed made
  obtain ⟨any,strict,prefixPath⟩ := of_decide_eq_true isWanted
  obtain ⟨run,limit,valid,depth,legal,base,mark,provisional⟩ :=
    latest_primary_retains_old_common_legality mode d actual primary accepted
  have allowed : Allowed mode d .rootStar := ⟨run,limit,valid,depth,Or.inl any⟩
  have image : rawImage mode d (render d .rootStar) = true :=
    (raw_image_iff_relative_allowed_template mode d (render d .rootStar)).mpr
      ⟨.rootStar,allowed,rfl⟩
  have contained := every_raw_image_is_inside_its_demand mode d (render d .rootStar) image
  rw [same,public_prefix_uses_only_existing_FLOW_normalization]
  cases markIs : d.mark with
  | flow =>
    have equal : render d .rootStar = prefixPublic d := by
      simp [render,starE,any,markIs,prefixPublic]
    obtain ⟨witness,chosen,legalWitness,emitted⟩ :=
      raw_image_supplies_actual_witness mode d (render d .rootStar) image
    apply Or.inl
    apply (C5_permission_iff_normalized_actual_emission mode d (prefixPublic d)).mpr
    refine ⟨witness,⟨render d .rootStar,intrinsic (render d .rootStar)⟩,emitted,?_,contained⟩
    simp [equal,prefixPublic,publicInitial]
  | full markId =>
    have companion : companionInitial (render d .rootStar) = some (prefixPublic d) := by
      simp [companionInitial,render,starE,any,markIs,prefixPublic]
    exact Or.inr ⟨render d .rootStar,prefixPublic d,image,contained,companion,rfl⟩

theorem every_new_public_key_has_existing_C5_permission (mode : Mode) (d : Demand) (actual : Actual)
    (seed : Seed) (member : seed ∈ emitSeeds mode d actual) :
    StoredPermission mode d (publicInitial seed.initial) := by
  rcases List.mem_append.mp member with old | added
  · exact (RejectAncestorStarAdmission.normalized_C5_image_is_unchanged mode d
      (publicInitial seed.initial)).mpr ⟨actual,seed,old,rfl⟩
  · have made : extra mode d actual = some seed := by simpa using added
    exact emitted_prefix_normalized_key_was_already_in_C5_image mode d actual seed made

theorem complete_normalized_C5_image_is_unchanged (mode : Mode) (d : Demand) (stored : Pattern) :
    StoredPermission mode d stored ↔
      ∃ actual seed, seed ∈ emitSeeds mode d actual ∧ publicInitial seed.initial = stored := by
  constructor
  · intro permitted
    obtain ⟨actual,seed,member,normalized⟩ :=
      (RejectAncestorStarAdmission.normalized_C5_image_is_unchanged mode d stored).mp permitted
    exact ⟨actual,seed,old_seed_and_layer_are_retained mode d actual seed member,normalized⟩
  · rintro ⟨actual,seed,member,normalized⟩
    rw [← normalized]
    exact every_new_public_key_has_existing_C5_permission mode d actual seed member

theorem full_mark_prefix_EXACT_is_not_in_the_old_raw_image (mode : Mode) (d : Demand)
    (markId : Nat) (full : d.mark = .full markId) :
    ¬RawPermission mode d (prefixSeed d).initial := by
  rintro (old | ⟨primary,image,made⟩)
  · have sameMark := (raw_image_preserves_base_mark_budget_and_has_no_ANY mode d
      (prefixSeed d).initial old).2.1
    simp [prefixSeed,full] at sameMark
  · have geometry := companion_has_same_geometry_and_NORMAL_FLOW primary (prefixSeed d).initial made
    have wrongTail := geometry.2.2.1
    simp [prefixSeed] at wrongTail

theorem no_ANY_initial_is_added (mode : Mode) (d : Demand) (actual : Actual)
    (seed : Seed) (member : seed ∈ emitSeeds mode d actual) : seed.initial.tail ≠ .any := by
  rcases List.mem_append.mp member with old | added
  · exact RejectAncestorStarAdmission.no_ANY_initial_is_introduced mode d actual seed old
  · have made : extra mode d actual = some seed := by simpa using added
    obtain ⟨isWanted,primary,accepted,same⟩ := extra_requires_a_real_primary mode d actual seed made
    simp [same,prefixSeed]

theorem wrong_mark_has_no_new_prefix (mode : Mode) (d : Demand) (actual : Actual)
    (wrong : RestrictedInitialPolicy.acceptsMark d.mark actual.pattern.mark = false) :
    extra mode d actual = none := by
  apply no_primary_means_no_extra
  unfold RejectAncestorStarAdmission.emit
  rw [mark_mismatch_never_emits mode d actual wrong]
  split <;> rfl

theorem wrong_base_has_no_new_prefix (mode : Mode) (d : Demand) (actual : Actual)
    (wrong : d.base ≠ actual.pattern.base) : extra mode d actual = none := by
  apply no_primary_means_no_extra
  unfold RejectAncestorStarAdmission.emit
  rw [base_mismatch_never_emits mode d actual wrong]
  split <;> rfl

def exampleMode : Mode := ⟨3,2,.forward⟩
def concreteDemand : Demand := ⟨1,[],.any,.full 7,[]⟩
def flowDemand : Demand := ⟨1,[],.any,.flow,[]⟩
def concreteActual : Actual := ⟨⟨1,[4,5],.exact,.full 7,[]⟩,.normal,false⟩

theorem concrete_descendant_keeps_both_old_seeds_and_adds_raw_prefix :
    emitSeeds exampleMode concreteDemand concreteActual =
      [⟨⟨1,[4],.star,.full 7,[]⟩,.demand⟩,
       ⟨⟨1,[4],.star,.flow,[]⟩,.normal⟩,
       ⟨⟨1,[],.exact,.flow,[]⟩,.normal⟩] := by decide

theorem FLOW_descendant_also_adds_raw_prefix :
    emitSeeds exampleMode flowDemand concreteActual =
      [⟨⟨1,[4],.star,.flow,[]⟩,.normal⟩,
       ⟨⟨1,[],.exact,.flow,[]⟩,.normal⟩] := by decide

end ExactFlowPrefixCompanion

#print axioms ExactFlowPrefixCompanion.old_seed_and_layer_are_retained
#print axioms ExactFlowPrefixCompanion.extra_requires_a_real_primary
#print axioms ExactFlowPrefixCompanion.no_primary_means_no_extra
#print axioms ExactFlowPrefixCompanion.no_strict_descendant_means_old_stream
#print axioms ExactFlowPrefixCompanion.same_head_is_unchanged
#print axioms ExactFlowPrefixCompanion.non_ANY_demand_is_unchanged
#print axioms ExactFlowPrefixCompanion.prefix_is_raw_EXACT_FLOW_NORMAL_with_empty_E
#print axioms ExactFlowPrefixCompanion.prefix_start_is_an_H_free_exact_identity
#print axioms ExactFlowPrefixCompanion.public_prefix_uses_only_existing_FLOW_normalization
#print axioms ExactFlowPrefixCompanion.original_actual_E_layer_mark_and_H_are_retained
#print axioms ExactFlowPrefixCompanion.latest_primary_retains_old_common_legality
#print axioms ExactFlowPrefixCompanion.emitted_prefix_is_bounded_and_has_a_new_field_witness
#print axioms ExactFlowPrefixCompanion.emitted_prefix_normalized_key_was_already_in_C5_image
#print axioms ExactFlowPrefixCompanion.every_new_public_key_has_existing_C5_permission
#print axioms ExactFlowPrefixCompanion.complete_normalized_C5_image_is_unchanged
#print axioms ExactFlowPrefixCompanion.full_mark_prefix_EXACT_is_not_in_the_old_raw_image
#print axioms ExactFlowPrefixCompanion.no_ANY_initial_is_added
#print axioms ExactFlowPrefixCompanion.wrong_mark_has_no_new_prefix
#print axioms ExactFlowPrefixCompanion.wrong_base_has_no_new_prefix
#print axioms ExactFlowPrefixCompanion.concrete_descendant_keeps_both_old_seeds_and_adds_raw_prefix
#print axioms ExactFlowPrefixCompanion.FLOW_descendant_also_adds_raw_prefix

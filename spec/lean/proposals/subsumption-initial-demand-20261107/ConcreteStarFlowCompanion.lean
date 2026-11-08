/-
Selected extension of the frozen ordinary four-tail C2 component.
This file does not change its imported definitions or its old theorems.
Every old primary emission is retained. A concrete STAR primary adds one
same-geometry FLOW STAR/NORMAL seed. The original actual stays in binding.

Scope: scalar FULL marks and counted Nat fields. Ordinary C2, mark gates,
actual legality and normalized FLOW EXACT preimages are imported unchanged.
The C5 entry image uses a concrete primary preimage for a new companion;
it must not test required full T against FLOW a second time. Paired C5 exit
matching, source callbacks, native packed storage and driver progress are
not redefined here. No new NORMAL concrete result is asserted.
-/
import RelativeAdmission

namespace ConcreteStarFlowCompanion
open PlainStarRelativeAdmission

def companionInitial (primary : Pattern) : Option Pattern :=
  match primary.tail, primary.mark with
  | .star, .full _ => some {primary with mark := .flow}
  | _, _ => none

def companionSeed (primary : Seed) : Option Seed :=
  (companionInitial primary.initial).map fun p => ⟨p,.normal⟩

def expanded (primary : Seed) : List Seed :=
  primary :: (companionSeed primary).toList

def emitSeeds (mode : Mode) (d : Demand) (actual : Actual) : List Seed :=
  match emit mode d actual with
  | none => []
  | some primary => expanded primary

/- This is the exact raw image relation. Its existential is constructive:
the old image supplies an executable finite-template witness. A native
classifier can recover the candidate primary by restoring d.mark. -/
def RawPermission (mode : Mode) (d : Demand) (raw : Pattern) : Prop :=
  rawImage mode d raw = true ∨
    ∃ primary, rawImage mode d primary = true ∧
      companionInitial primary = some raw

/- Raw containment remains attached to the primary witness. In particular,
STAR/E run-2 requested initials must retain the original concrete E. -/
def StoredPermission (mode : Mode) (d : Demand) (stored : Pattern) : Prop :=
  canStoreInitial mode d stored = true ∨
    ∃ primary raw,
      rawImage mode d primary = true ∧
      insideDemand d primary = true ∧
      companionInitial primary = some raw ∧ publicInitial raw = stored

structure Command where
  originalActual : Actual
  seeds : List Seed
deriving DecidableEq, Repr

def command (mode : Mode) (d : Demand) (actual : Actual) : Command :=
  ⟨actual,emitSeeds mode d actual⟩

theorem primary_always_in_expansion (primary : Seed) : primary ∈ expanded primary := by
  simp [expanded]

theorem companion_always_in_expansion (primary companion : Seed)
    (made : companionSeed primary = some companion) : companion ∈ expanded primary := by
  simp [expanded,made]

theorem expansion_membership (primary result : Seed) :
    result ∈ expanded primary ↔
      result = primary ∨ companionSeed primary = some result := by
  cases made : companionSeed primary <;> simp [expanded,made,eq_comm]

theorem primary_is_preserved (mode : Mode) (d : Demand) (actual : Actual) (primary : Seed)
    (made : emit mode d actual = some primary) : primary ∈ emitSeeds mode d actual := by
  simpa [emitSeeds,made] using primary_always_in_expansion primary

theorem no_primary_means_no_companion (mode : Mode) (d : Demand) (actual : Actual)
    (absent : emit mode d actual = none) : emitSeeds mode d actual = [] := by
  simp [emitSeeds,absent]

theorem companion_has_same_geometry_and_NORMAL_FLOW (primary raw : Pattern)
    (made : companionInitial primary = some raw) :
    raw.base = primary.base ∧ raw.path = primary.path ∧
      raw.tail = .star ∧ raw.exclusion = primary.exclusion ∧ raw.mark = .flow := by
  cases primary with
  | mk base path tail mark e =>
    cases tail <;> cases mark <;> simp [companionInitial] at made
    all_goals cases made; exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem companion_requires_concrete_STAR (primary raw : Pattern)
    (made : companionInitial primary = some raw) :
    primary.tail = .star ∧ ∃ mark, primary.mark = .full mark := by
  cases primary with
  | mk base path tail mark e =>
    cases tail <;> cases mark <;> simp [companionInitial] at made
    all_goals exact ⟨rfl,⟨_,rfl⟩⟩

theorem companion_seed_is_intrinsically_NORMAL (primary companion : Seed)
    (made : companionSeed primary = some companion) : companion.layer = .normal := by
  cases raw : companionInitial primary.initial with
  | none => simp [companionSeed,raw] at made
  | some p =>
    simp only [companionSeed,raw,Option.map_some,Option.some.injEq] at made
    cases made; rfl

theorem concrete_STAR_primary_remains_DEMAND (mode : Mode) (d : Demand)
    (actual : Actual) (primary : Seed) (raw : Pattern)
    (made : emit mode d actual = some primary)
    (companion : companionInitial primary.initial = some raw) : primary.layer = .demand := by
  obtain ⟨tail,mark,full⟩ := companion_requires_concrete_STAR primary.initial raw companion
  have joint := (joint_image_exactly_characterizes_arbitrary_admission mode d primary).mpr
    ⟨actual,made⟩
  have layer := of_decide_eq_true (Bool.and_eq_true_iff.mp joint).2
  simpa [JointLayer,intrinsic,tail,full] using layer

theorem raw_permission_has_executable_actual (mode : Mode) (d : Demand) (raw : Pattern)
    (permission : RawPermission mode d raw) :
    ∃ actual result, result ∈ emitSeeds mode d actual ∧ result.initial = raw := by
  rcases permission with old | ⟨primary,image,made⟩
  · obtain ⟨actual,result,emitted,same⟩ :=
      (raw_image_exactly_characterizes_arbitrary_emission mode d raw).mp old
    exact ⟨actual,result,primary_is_preserved mode d actual result emitted,same⟩
  · obtain ⟨actual,chosen,legal,emitted⟩ := raw_image_supplies_actual_witness mode d primary image
    let original : Seed := ⟨primary,intrinsic primary⟩
    let result : Seed := ⟨raw,.normal⟩
    have supplied : companionSeed original = some result := by
      simp [companionSeed,original,result,made]
    refine ⟨actual,result,?_,rfl⟩
    rw [emitSeeds,emitted]
    exact companion_always_in_expansion original result supplied

theorem every_executable_emission_has_raw_permission (mode : Mode) (d : Demand)
    (actual : Actual) (result : Seed) (member : result ∈ emitSeeds mode d actual) :
    RawPermission mode d result.initial := by
  cases emitted : emit mode d actual with
  | none => simp [emitSeeds,emitted] at member
  | some primary =>
    have belongs : result ∈ expanded primary := by simpa [emitSeeds,emitted] using member
    rcases (expansion_membership primary result).mp belongs with same | made
    · subst result
      exact Or.inl (arbitrary_actual_emission_is_in_raw_image mode d actual primary emitted)
    · cases raw : companionInitial primary.initial with
      | none => simp [companionSeed,raw] at made
      | some p =>
        simp only [companionSeed,raw,Option.map_some,Option.some.injEq] at made
        cases made
        exact Or.inr ⟨primary.initial,
          arbitrary_actual_emission_is_in_raw_image mode d actual primary emitted,raw⟩

theorem raw_permission_exactly_matches_C2 (mode : Mode) (d : Demand) (raw : Pattern) :
    RawPermission mode d raw ↔
      ∃ actual result, result ∈ emitSeeds mode d actual ∧ result.initial = raw := by
  constructor
  · exact raw_permission_has_executable_actual mode d raw
  · rintro ⟨actual,result,member,same⟩
    rw [← same]
    exact every_executable_emission_has_raw_permission mode d actual result member

theorem stored_permission_has_normalized_executable_actual
    (mode : Mode) (d : Demand) (stored : Pattern)
    (permission : StoredPermission mode d stored) :
    ∃ actual result, result ∈ emitSeeds mode d actual ∧ publicInitial result.initial = stored := by
  rcases permission with old | ⟨primary,raw,image,inside,made,normal⟩
  · obtain ⟨actual,result,emitted,normalized,contained⟩ :=
      (C5_permission_iff_normalized_actual_emission mode d stored).mp old
    exact ⟨actual,result,primary_is_preserved mode d actual result emitted,normalized⟩
  · obtain ⟨actual,result,member,same⟩ := raw_permission_has_executable_actual mode d raw
      (Or.inr ⟨primary,image,made⟩)
    exact ⟨actual,result,member,by simpa [same] using normal⟩

theorem old_stored_permission_is_preserved (mode : Mode) (d : Demand) (stored : Pattern)
    (old : canStoreInitial mode d stored = true) : StoredPermission mode d stored := Or.inl old

theorem stored_permission_exactly_matches_normalized_C2
    (mode : Mode) (d : Demand) (stored : Pattern) :
    StoredPermission mode d stored ↔
      ∃ actual result, result ∈ emitSeeds mode d actual ∧ publicInitial result.initial = stored := by
  constructor
  · exact stored_permission_has_normalized_executable_actual mode d stored
  · rintro ⟨actual,result,member,normalized⟩
    cases emitted : emit mode d actual with
    | none => simp [emitSeeds,emitted] at member
    | some primary =>
      have belongs : result ∈ expanded primary := by simpa [emitSeeds,emitted] using member
      rcases (expansion_membership primary result).mp belongs with same | made
      · subst result
        have image := arbitrary_actual_emission_is_in_raw_image mode d actual primary emitted
        exact Or.inl ((C5_permission_iff_normalized_actual_emission mode d stored).mpr
          ⟨actual,primary,emitted,normalized,
            every_raw_image_is_inside_its_demand mode d primary.initial image⟩)
      · cases raw : companionInitial primary.initial with
        | none => simp [companionSeed,raw] at made
        | some p =>
          simp only [companionSeed,raw,Option.map_some,Option.some.injEq] at made
          cases made
          have image := arbitrary_actual_emission_is_in_raw_image mode d actual primary emitted
          exact Or.inr ⟨primary.initial,p,image,
            every_raw_image_is_inside_its_demand mode d primary.initial image,raw,normalized⟩

theorem original_actual_is_not_replaced (mode : Mode) (d : Demand) (actual : Actual) :
    (command mode d actual).originalActual = actual := rfl

theorem companion_NORMAL_does_not_upgrade_DEMAND_actual :
    joinLayer .normal .demand = .demand := rfl

theorem positive_source_guard_cannot_use_companion_FLOW (required : Nat) :
    RestrictedInitialPolicy.acceptsMark (.full required) .flow = false := rfl

theorem mismatching_mark_cannot_create_companion (mode : Mode) (d : Demand) (actual : Actual)
    (mismatch : RestrictedInitialPolicy.acceptsMark d.mark actual.pattern.mark = false) :
    emitSeeds mode d actual = [] :=
  no_primary_means_no_companion mode d actual (mark_mismatch_never_emits mode d actual mismatch)

theorem mismatching_base_cannot_create_companion (mode : Mode) (d : Demand) (actual : Actual)
    (mismatch : d.base ≠ actual.pattern.base) : emitSeeds mode d actual = [] :=
  no_primary_means_no_companion mode d actual (base_mismatch_never_emits mode d actual mismatch)

theorem precise_later_STAR_rejection_still_has_no_companion
    (mode : Mode) (d : Demand) (actual : Actual) (field : Nat) (rest : List Nat)
    (star : d.shape = .star) (later : mode.run ≠ 2)
    (below : ApSpec.relate d.path actual.pattern.path = .below (field :: rest)) :
    emitSeeds mode d actual = [] :=
  no_primary_means_no_companion mode d actual
    (later_STAR_demand_rejects_every_strict_descendant mode d actual field rest star later below)

end ConcreteStarFlowCompanion

#print axioms ConcreteStarFlowCompanion.primary_always_in_expansion
#print axioms ConcreteStarFlowCompanion.companion_always_in_expansion
#print axioms ConcreteStarFlowCompanion.expansion_membership
#print axioms ConcreteStarFlowCompanion.primary_is_preserved
#print axioms ConcreteStarFlowCompanion.no_primary_means_no_companion
#print axioms ConcreteStarFlowCompanion.companion_has_same_geometry_and_NORMAL_FLOW
#print axioms ConcreteStarFlowCompanion.companion_requires_concrete_STAR
#print axioms ConcreteStarFlowCompanion.companion_seed_is_intrinsically_NORMAL
#print axioms ConcreteStarFlowCompanion.concrete_STAR_primary_remains_DEMAND
#print axioms ConcreteStarFlowCompanion.raw_permission_has_executable_actual
#print axioms ConcreteStarFlowCompanion.every_executable_emission_has_raw_permission
#print axioms ConcreteStarFlowCompanion.raw_permission_exactly_matches_C2
#print axioms ConcreteStarFlowCompanion.stored_permission_has_normalized_executable_actual
#print axioms ConcreteStarFlowCompanion.old_stored_permission_is_preserved
#print axioms ConcreteStarFlowCompanion.stored_permission_exactly_matches_normalized_C2
#print axioms ConcreteStarFlowCompanion.original_actual_is_not_replaced
#print axioms ConcreteStarFlowCompanion.companion_NORMAL_does_not_upgrade_DEMAND_actual
#print axioms ConcreteStarFlowCompanion.positive_source_guard_cannot_use_companion_FLOW
#print axioms ConcreteStarFlowCompanion.mismatching_mark_cannot_create_companion
#print axioms ConcreteStarFlowCompanion.mismatching_base_cannot_create_companion
#print axioms ConcreteStarFlowCompanion.precise_later_STAR_rejection_still_has_no_companion

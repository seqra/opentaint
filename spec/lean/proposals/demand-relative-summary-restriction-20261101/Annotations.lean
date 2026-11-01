import Geometry

/-!
Mark-slot and field-exclusion abstraction. This module extends the local cut
law to symbolic FLOW slots and full concrete marks. It preserves possible
locations; it does not interpret MUST as universal evidence or replace the
existing correlated-FLOW application/protection proof.
-/
namespace RelativeRestriction.Annotations
set_option autoImplicit false

inductive Slot where
  | flow (excluded : List Nat)
  | concrete (mark : Nat)
  deriving DecidableEq, Repr

def slotAdmits : Slot → Nat → Prop
  | .flow excluded, mark => mark ∉ excluded
  | .concrete wanted, mark => mark = wanted

structure Annotated where
  shape : Scalar
  slot : Slot
  excludedFields : List Accessor
  deriving DecidableEq, Repr

def fieldsAdmit (excluded : List Accessor) : Path → Prop
  | [] => True
  | first :: _ => first ∉ excluded

def meaning (fact : Annotated) (base mark : Nat) (location : Path) : Prop :=
  base = fact.shape.base ∧ slotAdmits fact.slot mark ∧
    possiblePath fact.shape.tail fact.shape.path location ∧
    fieldsAdmit fact.excludedFields (location.drop fact.shape.path.length)

def cut (budget : Nat) (fact : Annotated) : Annotated :=
  if depth fact.shape.path ≤ budget then fact
  else ⟨limit budget fact.shape, fact.slot, []⟩

theorem empty_fields_admit_every_suffix (suffix : Path) : fieldsAdmit [] suffix := by
  cases suffix <;> simp [fieldsAdmit]

theorem cut_slot_is_identical (budget : Nat) (fact : Annotated) :
    (cut budget fact).slot = fact.slot := by
  unfold cut
  split <;> rfl

theorem cut_protection_is_identical (budget : Nat) (fact : Annotated) :
    (cut budget fact).shape.protection = fact.shape.protection := by
  unfold cut
  split
  · rfl
  · exact limit_protection_retained _ _

theorem cut_shape_is_bounded (budget : Nat) (fact : Annotated) :
    depth (cut budget fact).shape.path ≤ budget := by
  unfold cut
  split
  · assumption
  · exact limit_depth_bound _ _

theorem cut_keeps_every_selected_location_and_mark (budget : Nat) (fact : Annotated)
    (base mark : Nat) (location : Path) (selected : meaning fact base mark location) :
    meaning (cut budget fact) base mark location := by
  unfold cut
  split
  · exact selected
  · obtain ⟨sameBase,allowedMark,geometry,_⟩ := selected
    have oldPossible : possible fact.shape base fact.shape.mark location :=
      ⟨sameBase,rfl,geometry⟩
    have widened := limit_possible_coverage budget fact.shape base fact.shape.mark location oldPossible
    exact ⟨widened.1,allowedMark,widened.2.2,empty_fields_admit_every_suffix _⟩

theorem normal_admitted_annotated_result_was_not_cut (budget : Nat) (fact : Annotated)
    (normal : (cut budget fact).shape.layer = .normal) : cut budget fact = fact := by
  unfold cut at normal ⊢
  split
  · rfl
  next overflow =>
    simp only [overflow, ↓reduceIte] at normal
    have demoted := limit_overflow_is_demand budget fact.shape overflow
    have impossible : Layer.demand = Layer.normal := demoted.symm.trans normal
    cases impossible

def packedMeaning (facts : List Annotated) (base mark : Nat) (location : Path) : Prop :=
  ∃ fact, fact ∈ facts ∧ meaning fact base mark location

def cutPacked (budget : Nat) (facts : List Annotated) : List Annotated := facts.map (cut budget)

theorem packed_cut_preserves_all_candidate_memberships (budget : Nat) (facts : List Annotated)
    (base mark : Nat) (location : Path) (selected : packedMeaning facts base mark location) :
    packedMeaning (cutPacked budget facts) base mark location := by
  obtain ⟨fact,member,atLocation⟩ := selected
  refine ⟨cut budget fact,?_,cut_keeps_every_selected_location_and_mark budget fact base mark location atLocation⟩
  exact List.mem_map.mpr ⟨fact,member,rfl⟩

theorem excluded_mark_is_still_excluded_after_cut (budget : Nat) (fact : Annotated)
    (excluded : List Nat) (mark : Nat) (slot : fact.slot = .flow excluded)
    (blocked : mark ∈ excluded) : ¬ slotAdmits (cut budget fact).slot mark := by
  rw [cut_slot_is_identical,slot]
  exact fun allowed => allowed blocked

theorem different_concrete_mark_is_not_invented (budget : Nat) (fact : Annotated)
    (wanted other : Nat) (slot : fact.slot = .concrete wanted) (different : other ≠ wanted) :
    ¬ slotAdmits (cut budget fact).slot other := by
  rw [cut_slot_is_identical,slot]
  exact different

end RelativeRestriction.Annotations

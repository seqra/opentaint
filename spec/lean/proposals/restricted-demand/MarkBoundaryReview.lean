/- Review controls for the ORIGINAL restricted mark gates. The final section
   states the exclusion-rebasing law needed by the selected concrete-STAR
   extension. No production operation is changed by this model. -/
import ApSpec.AbsDefs

namespace MarkBoundaryReview
open ApSpec ApSpec.Abs ApSpec.Handoff
set_option autoImplicit false

def input (mark : MarkA) (kind : Kind := .any) : PFact := ⟨3, [], kind, mark⟩
def output (mark : MarkA) (kind : Kind := .star Excl.empty) : AFact :=
  ⟨⟨4, [], kind, mark⟩, false⟩
def guide (entry exit : MarkA) : DemandEdge :=
  ⟨input entry, some ⟨4, [], .any, exit⟩⟩
def shared : PFact := input .star (.star Excl.empty)

theorem concrete_entry_does_not_invent_mark :
    emitW (input (.conc 7)) (input .star) = none := rfl

theorem concrete_entry_rejects_abstract_even_when_mark_not_excluded :
    emitW (input (.conc 7)) (input (.starEx [8]) (.star Excl.empty)) = none := rfl

theorem concrete_entry_preserves_actual_mark :
    emitW (input (.conc 7)) (input (.conc 7)) = some (input (.conc 7)) := rfl

theorem concrete_entry_rejects_other_mark :
    emitW (input (.conc 7)) (input (.conc 8)) = none := rfl

theorem abstract_entry_emits_shared_flow :
    emitW (input .star) (input (.conc 7)) = some shared := rfl

theorem abstract_entry_does_not_copy_actual_mark_exclusions :
    emitW (input .star) (input (.starEx [7]) (.star Excl.empty)) = some shared := rfl

theorem concrete_entry_cannot_authorize_flow_premise :
    restrictI shared (output .star) (guide (.conc 7) (.conc 7)) = none := rfl

theorem concrete_exit_keeps_correlated_abstract_conclusion :
    restrictI shared (output .star) (guide .star (.conc 7)) = some (output .star) := rfl

theorem concrete_exit_rejects_excluded_mark :
    restrictI shared (output (.starEx [7])) (guide .star (.conc 7)) = none := rfl

theorem concrete_exit_keeps_other_mark_exclusions :
    restrictI shared (output (.starEx [8])) (guide .star (.conc 7)) =
      some (output (.starEx [8])) := rfl

theorem exact_exit_does_not_decorrelate_star :
    restrictI shared (output .star)
      ⟨input .star, some ⟨4, [], .exact, .conc 7⟩⟩ = some (output .star) := rfl

theorem abstract_exit_does_not_erase_concrete_mark :
    restrictI (input (.conc 7)) (output (.conc 7)) (guide .star .star) =
      some (output (.conc 7)) := rfl

theorem original_normalization_preserves_star_and_field_exclusion (e : Excl) :
    (normFact ⟨3, [], .star e, .starEx [7]⟩).kind = .star e := rfl

/-- First-accessor exclusions belong to the ancestor. Once a strict descent
    is admitted, that ancestor exclusion cannot reject a later suffix. -/
theorem admitted_descent_rebases_exclusion (e : Excl) (first : Acc)
    (rest suffix : List Acc) (admitted : e.admits (first :: rest) = true) :
    e.admits ((first :: rest) ++ suffix) = Excl.empty.admits suffix := by
  cases e <;> cases suffix <;> simp_all [Excl.admits, Excl.empty, memB]

/-- The E part of MUST intersect STAR is their location intersection.
    The two tail categories remain distinct in the typed adapter. -/
theorem must_star_intersection_uses_exclusion_union (e1 e2 : Excl) (suffix : List Acc) :
    (e1.union e2).admits suffix = (e1.admits suffix && e2.admits suffix) :=
  ApSpec.Reverse.admits_union e1 e2 suffix

def ancestor : PFact := ⟨3, [], .star (.set [10]), .conc 7⟩
def requested : PFact := ⟨3, [11], .any, .conc 7⟩
def currentWrong : PFact := ⟨3, [11], .star (.set [10]), .conc 7⟩
def corrected : PFact := ⟨3, [11], .star Excl.empty, .conc 7⟩
def location : Loc := ⟨3, [11,10], 7⟩

theorem ancestor_and_request_cover_location :
    ancestor.covers location ∧ requested.covers location := by
  exact ⟨⟨rfl, ⟨[11,10], rfl, rfl⟩, rfl⟩,
    ⟨rfl, ⟨[10], rfl, trivial⟩, rfl⟩⟩

theorem wrongly_copied_exclusion_loses_location : ¬ currentWrong.covers location := by
  intro covered
  obtain ⟨_, ⟨suffix, same, allowed⟩, _⟩ := covered
  have suffixEq : suffix = [10] := by simpa [location, currentWrong] using same.symm
  subst suffix
  cases allowed

theorem corrected_rebasing_keeps_location : corrected.covers location := by
  exact ⟨rfl, ⟨[10], rfl, rfl⟩, rfl⟩

#print axioms concrete_entry_does_not_invent_mark
#print axioms concrete_entry_rejects_abstract_even_when_mark_not_excluded
#print axioms concrete_entry_preserves_actual_mark
#print axioms concrete_entry_rejects_other_mark
#print axioms abstract_entry_emits_shared_flow
#print axioms abstract_entry_does_not_copy_actual_mark_exclusions
#print axioms concrete_entry_cannot_authorize_flow_premise
#print axioms concrete_exit_keeps_correlated_abstract_conclusion
#print axioms concrete_exit_rejects_excluded_mark
#print axioms concrete_exit_keeps_other_mark_exclusions
#print axioms exact_exit_does_not_decorrelate_star
#print axioms abstract_exit_does_not_erase_concrete_mark
#print axioms original_normalization_preserves_star_and_field_exclusion
#print axioms admitted_descent_rebases_exclusion
#print axioms must_star_intersection_uses_exclusion_union
#print axioms ancestor_and_request_cover_location
#print axioms wrongly_copied_exclusion_loses_location
#print axioms corrected_rebasing_keeps_location
end MarkBoundaryReview

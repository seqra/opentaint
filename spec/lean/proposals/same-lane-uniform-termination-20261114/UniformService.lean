import ProtectedCycle
import Regressions
import VirtualProviders

/- Proposed extension, not a production change. Uniform coverage preserves
   the complete original, diagonal mark lane, output mx and literal H.
   Both H=true and H=false lanes are allowed, but never cross each other.
   Only forward singleton MUST originals, empty real E, and NE results. -/
namespace SameLaneUniform
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle
open NormalUniformNE

local instance : ReflBEq Nat where
  rfl := by intro a; exact Nat.beq_refl a
local instance : LawfulBEq Nat where
  eq_of_beq := by intro a b h; exact Nat.eq_of_beq_eq_true h

def diagonal (edge : Edge) : Prop :=
  match edge.1.mark with
  | none => edge.2.ap.mark = none
  | some mark => edge.2.ap.mark = some mark ∧
      edge.1.mx = [] ∧ edge.2.ap.mx = []

instance (edge : Edge) : Decidable (diagonal edge) := by
  unfold diagonal
  split <;> infer_instance

def headers (normal cut : Edge) : Prop :=
  normal.1 = cut.1 ∧ normal.1.tail = .must ∧
  normal.1.e = [] ∧ normal.2.ap.e = [] ∧ cut.2.ap.e = [] ∧
  normal.2.demand = false ∧ cut.2.demand = true ∧
  normal.2.ap.tail = .must ∧ cut.2.ap.tail = .ne ∧
  normal.2.ap.base = cut.2.ap.base ∧
  normal.2.ap.mark = cut.2.ap.mark ∧ normal.2.ap.mx = cut.2.ap.mx ∧
  normal.2.h = cut.2.h ∧ diagonal normal

instance (normal cut : Edge) : Decidable (headers normal cut) := by
  unfold headers
  infer_instance

def covers (normal cut : Edge) : Bool :=
  if headers normal cut then
    (dropHead normal.2.ap.path cut.2.ap.path).isSome else false

def compact (forward : Bool) (edges : List Edge) : List Edge :=
  if forward then edges.filter fun e => !(edges.any fun n => covers n e)
  else edges

theorem coverage_has_identical_mark_mx_and_protection (normal cut : Edge)
    (covered : covers normal cut = true) :
    normal.1 = cut.1 ∧ normal.2.ap.mark = cut.2.ap.mark ∧
    normal.2.ap.mx = cut.2.ap.mx ∧ normal.2.h = cut.2.h := by
  unfold covers at covered
  split at covered
  · rename_i same
    exact ⟨same.1,same.2.2.2.2.2.2.2.2.2.2.1,
      same.2.2.2.2.2.2.2.2.2.2.2.1,same.2.2.2.2.2.2.2.2.2.2.2.2.1⟩
  · simp at covered

def acceptsMark (a : Ap) (mark : Nat) : Bool :=
  match a.mark with
  | none => !a.mx.contains mark
  | some expected => expected == mark

theorem every_covered_mark_has_the_same_normal_gate (normal cut : Edge)
    (covered : covers normal cut = true) (mark : Nat) :
    acceptsMark normal.2.ap mark = acceptsMark cut.2.ap mark := by
  rcases coverage_has_identical_mark_mx_and_protection normal cut covered with ⟨_,sameMark,sameMx,_⟩
  simp only [acceptsMark,sameMark,sameMx]

theorem every_covered_point_has_a_constructive_uniform_witness
    (normal cut : Edge) (covered : covers normal cut = true) (rest : Path) :
    ∃ suffix : Path,
      dropHead normal.2.ap.path (cut.2.ap.path ++ rest) = some suffix ∧
      admits .must [] suffix = true := by
  unfold covers at covered
  split at covered
  · cases shape : dropHead normal.2.ap.path cut.2.ap.path with
    | none => simp [shape] at covered
    | some extra => exact uniform_provider_contains_every_covered_ne_point _ _ _ rest shape
  · simp at covered

theorem a_normal_provider_cannot_be_removed (normal candidate : Edge)
    (isNormal : candidate.2.demand = false) : covers normal candidate = false := by
  simp [covers,headers,isNormal]

theorem normal_providers_remain_in_the_final_basis (all : List Edge)
    (normal : Edge) (member : normal ∈ all) (isNormal : normal.2.demand = false) :
    normal ∈ compact true all := by
  have noCover : ∀ provider, covers provider normal = false :=
    fun provider => a_normal_provider_cannot_be_removed provider normal isNormal
  simp [compact,member,noCover]

theorem protection_classes_do_not_cross (normal cut : Edge)
    (different : normal.2.h ≠ cut.2.h) : covers normal cut = false := by
  simp [covers,headers,different]

theorem backward_behavior_is_unchanged (all : List Edge) : compact false all = all := rfl

theorem no_star_original_is_retired (normal cut : Edge)
    (star : cut.1.tail = .star) : covers normal cut = false := by
  unfold covers
  split
  · rename_i h
    have conflict := congrArg Ap.tail h.1
    rw [h.2.1,star] at conflict
    cases conflict
  · rfl

theorem no_may_output_is_retired (normal cut : Edge)
    (may : cut.2.ap.tail = .may) : covers normal cut = false := by
  simp [covers,headers,may]

theorem the_new_protected_concrete_cut_has_a_valid_provider :
    covers ProtectedCleanerCycle.normalReader3 (ProtectedCleanerGrowth.fEdge 0) = true ∧
    compact true [ProtectedCleanerGrowth.fEdge 0,ProtectedCleanerCycle.normalReader3] =
      [ProtectedCleanerCycle.normalReader3] := by decide

theorem the_retained_provider_is_still_protected :
    ((compact true [ProtectedCleanerGrowth.fEdge 0,ProtectedCleanerCycle.normalReader3]).all
      fun e => e.2.h) = true := by decide

theorem either_arrival_order_keeps_the_same_protected_basis :
    compact true [ProtectedCleanerGrowth.fEdge 0,ProtectedCleanerCycle.normalReader3] =
    compact true [ProtectedCleanerCycle.normalReader3,ProtectedCleanerGrowth.fEdge 0] := by decide

def excludedNormal : Edge :=
  ({(ProtectedCleanerGrowth.fQ 0).ap with mark := none},
    {ProtectedCleanerCycle.normalReader3.2 with
      ap := {ProtectedCleanerCycle.normalReader3.2.ap with mark := none,mx := [t]},h := false})
def excludedCut : Edge :=
  (excludedNormal.1,{ProtectedCleanerGrowth.fEdge 0 |>.2 with
    ap := {ProtectedCleanerGrowth.fEdge 0 |>.2.ap with mark := none,mx := [t]},h := false})

theorem matching_flow_exclusions_are_allowed_without_enumerating_marks :
    covers excludedNormal excludedCut = true ∧
    acceptsMark excludedNormal.2.ap t = false := by decide

theorem a_different_exclusion_or_mark_does_not_match :
    covers excludedNormal (excludedCut.1,{excludedCut.2 with ap := {excludedCut.2.ap with mx := []}}) = false ∧
    covers ProtectedCleanerCycle.normalReader3
      ((ProtectedCleanerGrowth.fEdge 0).1,{(ProtectedCleanerGrowth.fEdge 0).2 with
        ap := {(ProtectedCleanerGrowth.fEdge 0).2.ap with mark := some (t+1)}}) = false := by decide

end SameLaneUniform

#print axioms SameLaneUniform.coverage_has_identical_mark_mx_and_protection
#print axioms SameLaneUniform.every_covered_mark_has_the_same_normal_gate
#print axioms SameLaneUniform.every_covered_point_has_a_constructive_uniform_witness
#print axioms SameLaneUniform.a_normal_provider_cannot_be_removed
#print axioms SameLaneUniform.normal_providers_remain_in_the_final_basis
#print axioms SameLaneUniform.protection_classes_do_not_cross
#print axioms SameLaneUniform.backward_behavior_is_unchanged
#print axioms SameLaneUniform.no_star_original_is_retired
#print axioms SameLaneUniform.no_may_output_is_retired
#print axioms SameLaneUniform.the_new_protected_concrete_cut_has_a_valid_provider
#print axioms SameLaneUniform.the_retained_provider_is_still_protected
#print axioms SameLaneUniform.either_arrival_order_keeps_the_same_protected_basis
#print axioms SameLaneUniform.matching_flow_exclusions_are_allowed_without_enumerating_marks
#print axioms SameLaneUniform.a_different_exclusion_or_mark_does_not_match

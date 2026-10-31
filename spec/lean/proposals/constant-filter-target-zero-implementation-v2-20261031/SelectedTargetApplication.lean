import TargetZeroND

/-!
Selected Target summary application, 2026-10-31.

NormalTarget(id) applies only with complete, admitted, all-NORMAL support,
including native MUST classification. Any DEMAND support rejects that normal
summary application: NONE is returned, not a derived DemandTarget. DemandTarget
applies to any complete admitted support and remains anonymous DEMAND.

This module constructs only selected target applications. Admission/completeness
and actual native-MUST/AP classification are explicit production adapters.
-/
namespace SelectedTargetApplication
open SelectedCore
open TargetZeroND
set_option autoImplicit false

structure Support where
  admitted : Bool
  complete : Bool
  contributors : List Layer
  nativeMustClassification : Layer
  deriving DecidableEq, Repr

def allNormal (support : Support) : Bool :=
  decide (support.nativeMustClassification = .normal) &&
    support.contributors.all (fun layer => decide (layer = .normal))

def ready (support : Support) : Bool := support.admitted && support.complete

def applyTarget (caller : Nat) (premise : Premise) (support : Support) : Target → Option Summary
  | .normalTarget reportId =>
      if ready support && allNormal support then
        some (layeredTargetSummary caller premise .normal reportId)
      else none
  | .demandTarget =>
      if ready support then
        some (targetSummary caller premise)
      else none

/-- Direction dispatch also covers freshly produced/current NormalTarget, not
    only saved native records. Backward DemandTarget remains eligible. -/
def applyInDirection (direction : Direction) (caller : Nat) (premise : Premise)
    (support : Support) (label : Target) : Option Summary :=
  match direction, label with
  | .backward, .normalTarget _ => none
  | _, _ => applyTarget caller premise support label

theorem backward_current_normal_application_none (caller : Nat) (premise : Premise)
    (support : Support) (reportId : Nat) :
    applyInDirection .backward caller premise support (.normalTarget reportId) = none := rfl

theorem forward_dispatch_uses_selected_application (caller : Nat) (premise : Premise)
    (support : Support) (label : Target) :
    applyInDirection .forward caller premise support label = applyTarget caller premise support label := by
  cases label <;> rfl

theorem all_normal_iff (support : Support) :
    allNormal support = true ↔ support.nativeMustClassification = .normal ∧
      ∀ layer ∈ support.contributors, layer = .normal := by
  constructor
  · intro normal
    have parts : decide (support.nativeMustClassification = .normal) = true ∧
        support.contributors.all (fun layer => decide (layer = .normal)) = true := by
      simpa only [allNormal, Bool.and_eq_true] using normal
    refine ⟨of_decide_eq_true parts.1, ?_⟩
    intro layer member
    exact of_decide_eq_true (List.all_eq_true.mp parts.2 layer member)
  · rintro ⟨nativeNormal, contributorsNormal⟩
    have native : decide (support.nativeMustClassification = .normal) = true := decide_eq_true nativeNormal
    have contributors : support.contributors.all (fun layer => decide (layer = .normal)) = true :=
      List.all_eq_true.mpr (fun layer member => decide_eq_true (contributorsNormal layer member))
    simp only [allNormal, native, contributors, Bool.true_and]

theorem normal_keeps_id (caller : Nat) (premise : Premise) (support : Support) (reportId : Nat)
    (admitted : support.admitted = true) (complete : support.complete = true)
    (normal : allNormal support = true) :
    applyTarget caller premise support (.normalTarget reportId) =
      some (layeredTargetSummary caller premise .normal reportId) := by
  simp only [applyTarget, ready, admitted, complete, normal, Bool.true_and, ↓reduceIte]

theorem nonnormal_support_rejects_normal (caller : Nat) (premise : Premise)
    (support : Support) (reportId : Nat) (notNormal : allNormal support = false) :
    applyTarget caller premise support (.normalTarget reportId) = none := by
  simp only [applyTarget, notNormal, Bool.and_false, Bool.false_eq_true, ↓reduceIte]

theorem demand_contributor_rejects_normal (caller : Nat) (premise : Premise)
    (support : Support) (reportId : Nat) (demand : Layer.demand ∈ support.contributors) :
    applyTarget caller premise support (.normalTarget reportId) = none := by
  apply nonnormal_support_rejects_normal
  cases classified : allNormal support with
  | false => rfl
  | true =>
      have normal := (all_normal_iff support).mp classified
      cases normal.2 .demand demand

theorem demand_native_classification_rejects_normal (caller : Nat) (premise : Premise)
    (support : Support) (reportId : Nat)
    (nativeDemand : support.nativeMustClassification = .demand) :
    applyTarget caller premise support (.normalTarget reportId) = none := by
  apply nonnormal_support_rejects_normal
  simp only [allNormal, nativeDemand, reduceCtorEq, decide_false, Bool.false_and]

theorem demand_target_persists (caller : Nat) (premise : Premise) (support : Support)
    (admitted : support.admitted = true) (complete : support.complete = true) :
    applyTarget caller premise support .demandTarget = some (targetSummary caller premise) := by
  simp only [applyTarget, ready, admitted, complete, Bool.true_and, ↓reduceIte]

theorem incomplete_application_is_none (caller : Nat) (premise : Premise) (support : Support)
    (label : Target) (incomplete : support.complete = false) :
    applyTarget caller premise support label = none := by
  cases label <;> simp only [applyTarget, ready, incomplete, Bool.and_false, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte]

theorem rejected_admission_is_none (caller : Nat) (premise : Premise) (support : Support)
    (label : Target) (rejected : support.admitted = false) :
    applyTarget caller premise support label = none := by
  cases label <;> simp only [applyTarget, ready, rejected, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte]

def applicationEffects (applied : Option Summary) : List Summary := applied.toList

theorem failed_application_creates_no_target (applied : Option Summary) (failed : applied = none) :
    applicationEffects applied = [] := by rw [failed]; rfl

namespace Controls
def allNormalND : Support := ⟨true, true, [.normal, .normal], .normal⟩
def demandND : Support := ⟨true, true, [.normal, .demand], .normal⟩
def nativeMustDemand : Support := ⟨true, true, [.normal, .normal], .demand⟩
def incompleteND : Support := ⟨true, false, [.normal, .normal], .normal⟩

theorem complete_nd_normal_only_guard :
    applyTarget 2 .zero allNormalND (.normalTarget 7) = some (layeredTargetSummary 2 .zero .normal 7) ∧
    applyTarget 2 .zero demandND (.normalTarget 7) = none ∧
    applyTarget 2 .zero nativeMustDemand (.normalTarget 7) = none ∧
    applyTarget 2 .zero incompleteND (.normalTarget 7) = none := by decide

theorem demand_marker_accepts_any_complete_admitted_layers :
    applyTarget 2 .zero demandND .demandTarget = some (targetSummary 2 .zero) ∧
    applyTarget 2 .zero nativeMustDemand .demandTarget = some (targetSummary 2 .zero) ∧
    applyTarget 2 .zero incompleteND .demandTarget = none := by decide

def checks : Bool :=
  decide (applyTarget 2 .zero allNormalND (.normalTarget 7) = some (layeredTargetSummary 2 .zero .normal 7)) &&
  decide (applyTarget 2 .zero demandND (.normalTarget 7) = none) &&
  decide (applyTarget 2 .zero nativeMustDemand (.normalTarget 7) = none) &&
  decide (applyTarget 2 .zero demandND .demandTarget = some (targetSummary 2 .zero)) &&
  decide (applyTarget 2 .zero incompleteND (.normalTarget 7) = none)

theorem checks_pass : checks = true := rfl
end Controls

#print axioms all_normal_iff
#print axioms backward_current_normal_application_none
#print axioms normal_keeps_id
#print axioms demand_contributor_rejects_normal
#print axioms demand_native_classification_rejects_normal
#print axioms demand_target_persists
#print axioms incomplete_application_is_none
#print axioms failed_application_creates_no_target
#print axioms Controls.checks_pass
#eval Controls.checks

end SelectedTargetApplication

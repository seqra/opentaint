import SelectedCore

/-!
Selected C2 exact-$ admission correction, 2026-10-31.

An ANY actual cannot satisfy an exact-$ entry demand at the same path, at an
ancestor wildcard path, or at any other path. This rejection precedes the
existing emitter. EXACT and MUST actuals use the unchanged geometry, mark,
full-emission-budget and materialization adapters. This module changes neither
generic AP applicability nor C5.

The reverse direction is different: an ANY entry demand can be refined by
an EXACT submitted position through the existing emitter. The admission
relation is directed; a symmetric geometric meet is not its definition.

All AP values here are nonzero. No emitted initial means no nonzero callee start
or terminal witness on this call path; it never means an implicit ZERO fallback.
Other independent method entries or run-1 discovery are outside that statement.
-/
namespace InitialEmissionExact
open SelectedCore
set_option autoImplicit false

inductive Tail where
  | exactDollar | must | any
  deriving DecidableEq, Repr

structure AP where
  base : Nat
  path : List Nat
  tail : Tail
  mark : Nat
  deriving DecidableEq, Repr

structure ExactDemand where
  base : Nat
  path : List Nat
  mark : Nat
  budget : Nat
  deriving DecidableEq, Repr

/-- Existing C2 checks/emission are parameters. Their AP/mark/field semantics
    must be supplied by the production adapter; no narrowing is inferred here. -/
structure EmitterAdapter where
  geometry : AP → ExactDemand → Bool
  markCompatible : AP → ExactDemand → Bool
  fullBudgetAllows : AP → ExactDemand → Bool
  materialize : AP → ExactDemand → List AP

def ordinaryEmitter (adapter : EmitterAdapter) (actual : AP) (demand : ExactDemand) : List AP :=
  if adapter.geometry actual demand && adapter.markCompatible actual demand &&
      adapter.fullBudgetAllows actual demand then adapter.materialize actual demand
  else []

def emitExact (adapter : EmitterAdapter) (actual : AP) (demand : ExactDemand) : List AP :=
  match actual.tail with
  | .any => []
  | .exactDollar | .must => ordinaryEmitter adapter actual demand

/-- An ANY demand keeps the existing emission policy. This shape parameter
    carries its base/path/mark/budget; the adapter supplies the ANY policy. -/
def emitAnyDemand (adapter : EmitterAdapter) (actual : AP)
    (demandShape : ExactDemand) : List AP := ordinaryEmitter adapter actual demandShape

theorem any_demand_uses_existing_emitter (adapter : EmitterAdapter) (actual : AP)
    (demandShape : ExactDemand) :
    emitAnyDemand adapter actual demandShape = ordinaryEmitter adapter actual demandShape := rfl

theorem any_actual_rejected_at_every_path (adapter : EmitterAdapter) (base mark : Nat)
    (path : List Nat) (demand : ExactDemand) :
    emitExact adapter ⟨base, path, .any, mark⟩ demand = [] := rfl

theorem exact_actual_uses_existing_emitter (adapter : EmitterAdapter) (base mark : Nat)
    (path : List Nat) (demand : ExactDemand) :
    emitExact adapter ⟨base, path, .exactDollar, mark⟩ demand =
      ordinaryEmitter adapter ⟨base, path, .exactDollar, mark⟩ demand := rfl

theorem must_actual_uses_existing_emitter (adapter : EmitterAdapter) (base mark : Nat)
    (path : List Nat) (demand : ExactDemand) :
    emitExact adapter ⟨base, path, .must, mark⟩ demand =
      ordinaryEmitter adapter ⟨base, path, .must, mark⟩ demand := rfl

theorem full_budget_guard_retained (adapter : EmitterAdapter) (actual : AP)
    (demand : ExactDemand) (rejected : adapter.fullBudgetAllows actual demand = false) :
    emitExact adapter actual demand = [] := by
  cases actual with
  | mk base path tail mark =>
      cases tail <;> simp only [emitExact, ordinaryEmitter, rejected, Bool.and_false, Bool.false_eq_true, ↓reduceIte]

theorem mark_guard_retained (adapter : EmitterAdapter) (actual : AP)
    (demand : ExactDemand) (rejected : adapter.markCompatible actual demand = false) :
    emitExact adapter actual demand = [] := by
  cases actual with
  | mk base path tail mark =>
      cases tail <;> simp only [emitExact, ordinaryEmitter, rejected, Bool.and_false,
        Bool.false_and, Bool.false_eq_true, ↓reduceIte]

inductive CalleeInitial where
  | zero | nonzero (value : AP)
  deriving DecidableEq, Repr

def starts (emitted : List AP) : List CalleeInitial := emitted.map CalleeInitial.nonzero
def terminalEffects (terminal : AP → Option Summary) (emitted : List AP) : List Summary :=
  emitted.filterMap terminal

theorem no_emission_no_initial : starts [] = [] := rfl
theorem no_emission_no_terminal_witness (terminal : AP → Option Summary) : terminalEffects terminal [] = [] := rfl

theorem zero_not_a_nonzero_fallback (emitted : List AP) : CalleeInitial.zero ∉ starts emitted := by
  intro member
  obtain ⟨value, _, impossible⟩ := List.mem_map.mp member
  cases impossible

theorem any_actual_has_no_callee_witness (adapter : EmitterAdapter) (base mark : Nat)
    (path : List Nat) (demand : ExactDemand) (terminal : AP → Option Summary) :
    starts (emitExact adapter ⟨base, path, .any, mark⟩ demand) = [] ∧
    terminalEffects terminal (emitExact adapter ⟨base, path, .any, mark⟩ demand) = [] := ⟨rfl, rfl⟩

namespace Controls

def exactDemand : ExactDemand := ⟨0, [1, 2, 3], 7, 4⟩
def samePrefixAny : AP := ⟨0, [1, 2, 3], .any, 7⟩
def ancestorAny : AP := ⟨0, [1], .any, 7⟩
def exactActual : AP := ⟨0, [1, 2, 3], .exactDollar, 7⟩
def mustActual : AP := ⟨0, [1, 2, 3], .must, 7⟩

/-- An intentionally permissive applicability adapter isolates the C2 guard.
    This is not a new production AP applicability implementation. -/
def permissiveAdapter : EmitterAdapter where
  geometry := fun _ _ => true
  markCompatible := fun _ _ => true
  fullBudgetAllows := fun _ _ => true
  materialize := fun actual _ => [actual]

def helperNormal : AP → Option Summary := fun _ => some (layeredTargetSummary 0 (.ap .a) .normal 7)

/-- A concrete same-prefix cell, with real base/mark/budget checks. This does
    not specify all descendant/ancestor ANY-demand refinement cells. -/
def samePrefixAdapter : EmitterAdapter where
  geometry := fun actual demand => actual.base == demand.base && actual.path == demand.path
  markCompatible := fun actual demand => actual.mark == demand.mark
  fullBudgetAllows := fun actual demand => actual.path.length <= demand.budget
  materialize := fun actual _ => [actual]

theorem exact_refines_any_but_any_does_not_satisfy_exact :
    emitAnyDemand samePrefixAdapter exactActual exactDemand = [exactActual] ∧
    emitExact samePrefixAdapter samePrefixAny exactDemand = [] := by decide

theorem any_same_prefix_and_ancestor_both_rejected :
    emitExact permissiveAdapter samePrefixAny exactDemand = [] ∧
    emitExact permissiveAdapter ancestorAny exactDemand = [] := ⟨rfl, rfl⟩

theorem valid_exact_and_must_preserved :
    emitExact permissiveAdapter exactActual exactDemand = [exactActual] ∧
    emitExact permissiveAdapter mustActual exactDemand = [mustActual] := ⟨rfl, rfl⟩

theorem none_result_produces_no_nonzero_initial_or_normal_helper_witness :
    starts (emitExact permissiveAdapter ancestorAny exactDemand) = [] ∧
    terminalEffects helperNormal (emitExact permissiveAdapter ancestorAny exactDemand) = [] ∧
    emittedZero .restricted [⟨0, .ap .a, .zero⟩] 0 (.ap .a) = [] := ⟨rfl, rfl, rfl⟩

theorem existing_mark_and_budget_rejections_preserved :
    emitExact {permissiveAdapter with markCompatible := fun _ _ => false} mustActual exactDemand = [] ∧
    emitExact {permissiveAdapter with fullBudgetAllows := fun _ _ => false} exactActual exactDemand = [] := ⟨rfl, rfl⟩

def checks : Bool :=
  decide (emitAnyDemand samePrefixAdapter exactActual exactDemand = [exactActual]) &&
  decide (emitExact permissiveAdapter samePrefixAny exactDemand = []) &&
  decide (emitExact permissiveAdapter ancestorAny exactDemand = []) &&
  decide (emitExact permissiveAdapter exactActual exactDemand = [exactActual]) &&
  decide (emitExact permissiveAdapter mustActual exactDemand = [mustActual]) &&
  decide (terminalEffects helperNormal (emitExact permissiveAdapter ancestorAny exactDemand) = [])

theorem checks_pass : checks = true := rfl
end Controls

#print axioms any_actual_rejected_at_every_path
#print axioms exact_actual_uses_existing_emitter
#print axioms must_actual_uses_existing_emitter
#print axioms full_budget_guard_retained
#print axioms mark_guard_retained
#print axioms zero_not_a_nonzero_fallback
#print axioms any_actual_has_no_callee_witness
#print axioms Controls.checks_pass
#eval Controls.checks

end InitialEmissionExact

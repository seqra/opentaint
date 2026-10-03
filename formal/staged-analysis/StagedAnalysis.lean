import Std
import BaseOnly

namespace StagedAnalysis

abbrev Rule := Nat

structure Finding where
  id : Nat
  requiredRules : List Rule
deriving Repr, DecidableEq

def Finding.enabledBy (finding : Finding) (rules : List Rule) : Bool :=
  finding.requiredRules.all rules.contains

def restrictedScan (findings : List Finding) (rules : List Rule) : List Finding :=
  findings.filter fun finding => finding.enabledBy rules

inductive ScanPlan where
  | exact (rules : List Rule)
  | baseline
deriving Repr, DecidableEq

def scan (findings : List Finding) (baselineRules : List Rule) (plan : ScanPlan) : List Finding :=
  match plan with
  | .exact rules => restrictedScan findings rules
  | .baseline => restrictedScan findings baselineRules

/-- Exact discovery returns `none` whenever any candidate is incomplete. -/
def planFromExactSelection (rules : Option (List Rule)) : ScanPlan :=
  match rules with
  | some selected => .exact selected
  | none => .baseline

theorem incomplete_discovery_is_baseline (findings : List Finding) (baselineRules : List Rule) :
    scan findings baselineRules (planFromExactSelection none) =
      restrictedScan findings baselineRules := by
  rfl

structure ExactCoverage (findings : List Finding) (selected : List Rule) where
  covered :
    ∀ finding, finding ∈ findings →
      ∀ rule, rule ∈ finding.requiredRules → rule ∈ selected

theorem exact_selection_preserves_covered_findings
    {findings : List Finding}
    {selected : List Rule}
    (coverage : ExactCoverage findings selected) :
    restrictedScan findings selected = findings := by
  unfold restrictedScan
  apply List.filter_eq_self.mpr
  intro finding findingMem
  simp only [Finding.enabledBy, List.all_eq_true]
  intro rule ruleMem
  rw [List.contains_iff_mem]
  exact coverage.covered finding findingMem rule ruleMem

end StagedAnalysis

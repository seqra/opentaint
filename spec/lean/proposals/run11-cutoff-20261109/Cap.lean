import Std.Tactic

namespace Run11Cutoff

inductive Decision where
  | next (run : Nat)
  | converged
  | policy
  | runLimit
  | abnormal
  deriving DecidableEq, Repr

/-- The native driver calls the policy only at a complete forward barrier. -/
def atBarrier (run : Nat) (complete noDemand delegateContinue : Bool) : Decision :=
  if !complete then .abnormal
  else if run % 2 = 1 then
    if noDemand then .converged
    else if run ≥ 11 then .runLimit
    else if !delegateContinue then .policy
    else .next (run + 1)
  else .next (run + 1)

/-- The explicit witness has eleven positive engine indices. -/
def engineIndices : List Nat := (List.range 11).map (· + 1)

theorem cap_is_forward : 11 % 2 = 1 := by decide

theorem cap_indices : engineIndices = [1,2,3,4,5,6,7,8,9,10,11] := by decide

theorem cap_indices_bounded : engineIndices.all (fun run => 1 ≤ run && run ≤ 11) = true := by
  decide

theorem completed_forward_cap : atBarrier 11 true false true = .runLimit := by decide

theorem no_twelfth_engine : atBarrier 11 true false true ≠ .next 12 := by decide

theorem convergence_has_priority (delegate : Bool) :
    atBarrier 11 true true delegate = .converged := by
  cases delegate <;> decide

theorem failed_cap_is_not_a_cutoff (empty delegate : Bool) :
    atBarrier 11 false empty delegate = .abnormal := by
  cases empty <;> cases delegate <;> decide

theorem earlier_delegate_stop : atBarrier 3 true false false = .policy := by decide

theorem backward_ten_reaches_forward_cap : atBarrier 10 true false false = .next 11 := by decide

theorem run_limit_needs_complete_forward_nonempty (run : Nat)
    (complete empty delegate : Bool)
    (h : atBarrier run complete empty delegate = .runLimit) :
    complete = true ∧ run % 2 = 1 ∧ empty = false ∧ 11 ≤ run := by
  unfold atBarrier at h
  split at h
  · contradiction
  · split at h
    · rename_i hforward
      split at h
      · contradiction
      · split at h
        · rename_i hlimit
          have hc : complete = true := by cases complete <;> simp_all
          have he : empty = false := by cases empty <;> simp_all
          exact ⟨hc, hforward, he, hlimit⟩
        · split at h <;> contradiction
    · contradiction

/-- On the reachable bounded schedule, a next step never crosses eleven. -/
theorem next_preserves_bound (run next : Nat) (bound : run ≤ 11)
    (h : atBarrier run true false true = .next next) : next ≤ 11 := by
  unfold atBarrier at h
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.false_eq_true] at h
  split at h
  · split at h
    · contradiction
    · rename_i hlimit
      cases h
      omega
  · rename_i hbackward
    cases h
    have hne : run ≠ 11 := by intro heq; subst run; contradiction
    omega

/-- A cap is an execution policy result, never a convergence certificate. -/
theorem cutoff_distinct_from_convergence : Decision.runLimit ≠ .converged := by decide

#print axioms cap_indices_bounded
#print axioms run_limit_needs_complete_forward_nonempty
#print axioms next_preserves_bound
#eval engineIndices
#eval atBarrier 11 true false true

end Run11Cutoff

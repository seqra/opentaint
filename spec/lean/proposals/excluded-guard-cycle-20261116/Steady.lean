import ParametricRounds
import Frozen
namespace ExcludedSteady
open ExcludedGuardCycle ExcludedPhase ExcludedFrozen ExcludedRounds
set_option maxRecDepth 65536
set_option maxHeartbeats 320000000

theorem forward_budget_saturates (n : Nat) : stepWithLimit true 5 (n+4) s8 = s7 := by
  simp only [stepWithLimit,analyzeF n,targetF n]
  kernel_decide_open

theorem backward_budget_saturates (n : Nat) : stepWithLimit true 6 (n+4) s7 = s8 := by
  simp only [stepWithLimit,analyzeB n]
  kernel_decide_open

theorem forward_at_every_later_run (n : Nat) : step true (2*n+9) s8 = s7 := by
  unfold step
  rw [step_regular true (2*n+9) 5 _ s8 (by omega) (by decide) (by omega) (by decide) (by omega)]
  have hh : ExcludedGuardCycle.limit (2*n+9) = (2*n+4)+4 := by
    simp only [ExcludedGuardCycle.limit]
    omega
  rw [hh]
  exact forward_budget_saturates (2*n+4)

theorem backward_at_every_later_run (n : Nat) : step true (2*n+10) s7 = s8 := by
  unfold step
  rw [step_regular true (2*n+10) 6 _ s7 (by omega) (by decide) (by omega) (by decide) (by omega)]
  have hh : ExcludedGuardCycle.limit (2*n+10) = (2*n+5)+4 := by
    simp only [ExcludedGuardCycle.limit]
    omega
  rw [hh]
  exact backward_budget_saturates (2*n+5)
end ExcludedSteady

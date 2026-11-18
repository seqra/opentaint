import ProtectedRounds
namespace ProtectedSteady
open ProtectedReturn ProtectedPhase ProtectedFrozen ProtectedRounds
set_option maxRecDepth 65536
set_option maxHeartbeats 320000000

def forward : State := s11

theorem targetF (n : Nat) : anyTarget true 5 (n+8) s12 = true := by
  unfold anyTarget
  rw [initialF n]
  simp only [UniformSticky.seenDemand]
  rw [roundF1 n,roundF2 n,roundF3 n,roundF4 n,roundF5 n,roundF6 n,roundF7 n,roundF8 n]
  decide

theorem forward_budget_saturates (n : Nat) : stepWithLimit true 5 (n+8) s12 = forward := by
  simp only [stepWithLimit,analyzeF n,targetF n,producerHit,entryBackValues]
  kernel_decide_open

theorem backward_budget_saturates (n : Nat) : stepWithLimit true 6 (n+8) forward = s12 := by
  simp only [stepWithLimit,producerHit,entryBackValues]
  kernel_decide_open

theorem forward_at_every_later_run (n : Nat) : step true (2*n+11) s12 = forward := by
  unfold step
  rw [step_regular true (2*n+11) 5 _ s12 (by omega) (by decide)
    (by omega) (by decide) (by omega) (by decide) (by omega)]
  have hh : ProtectedReturn.limit (2*n+11) = (2*n+2)+8 := by
    simp only [ProtectedReturn.limit]
    omega
  rw [hh]
  exact forward_budget_saturates (2*n+2)

theorem backward_at_every_later_run (n : Nat) : step true (2*n+12) forward = s12 := by
  unfold step
  rw [step_regular true (2*n+12) 6 _ forward (by omega) (by decide)
    (by omega) (by decide) (by omega) (by decide) (by omega)]
  have hh : ProtectedReturn.limit (2*n+12) = (2*n+3)+8 := by
    simp only [ProtectedReturn.limit]
    omega
  rw [hh]
  exact backward_budget_saturates (2*n+3)
end ProtectedSteady

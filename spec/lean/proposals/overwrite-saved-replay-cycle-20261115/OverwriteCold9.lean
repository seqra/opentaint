import OverwriteWitnesses

namespace OverwriteCold9

open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NormalUniformNE NestedSavedReplayCycle NestedColdMachine OverwriteReplay OverwriteWitnesses

set_option maxRecDepth 16384

set_option maxHeartbeats 80000000

theorem cold : OverwriteReplay.rounds true 6 9 8 3 methods rows8 saved8 OverwriteWitnesses.source = state9 := by decide

theorem quiescent : OverwriteReplay.round true 9 8 3 methods rows8 saved8 state9 = state9 := by decide

theorem handoff : OverwriteReplay.outputRows state9 = rows9 ∧ OverwriteReplay.outputSaved 9 saved8 state9 = saved9 := by decide

end OverwriteCold9

#print axioms OverwriteCold9.cold

#print axioms OverwriteCold9.quiescent

#print axioms OverwriteCold9.handoff

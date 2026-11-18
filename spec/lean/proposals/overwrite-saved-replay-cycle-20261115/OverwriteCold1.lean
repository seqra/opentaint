import OverwriteWitnesses

namespace OverwriteCold1

open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NormalUniformNE NestedSavedReplayCycle NestedColdMachine OverwriteReplay OverwriteWitnesses

set_option maxRecDepth 16384

set_option maxHeartbeats 80000000

theorem cold : OverwriteReplay.rounds true 6 1 1 3 methods rows0 saved0 OverwriteWitnesses.source = state1 := by decide

theorem quiescent : OverwriteReplay.round true 1 1 3 methods rows0 saved0 state1 = state1 := by decide

theorem handoff : OverwriteReplay.outputRows state1 = rows1 ∧ OverwriteReplay.outputSaved 1 saved0 state1 = saved1 := by decide

end OverwriteCold1

#print axioms OverwriteCold1.cold

#print axioms OverwriteCold1.quiescent

#print axioms OverwriteCold1.handoff

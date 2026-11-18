import OverwriteWitnesses

namespace OverwriteCold2

open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NormalUniformNE NestedSavedReplayCycle NestedColdMachine OverwriteReplay OverwriteWitnesses

set_option maxRecDepth 16384

set_option maxHeartbeats 80000000

theorem cold : OverwriteReplay.rounds true 6 2 1 3 methods rows1 saved1 OverwriteWitnesses.source = state2 := by decide

theorem quiescent : OverwriteReplay.round true 2 1 3 methods rows1 saved1 state2 = state2 := by decide

theorem handoff : OverwriteReplay.outputRows state2 = rows2 ∧ OverwriteReplay.outputSaved 2 saved1 state2 = saved2 := by decide

end OverwriteCold2

#print axioms OverwriteCold2.cold

#print axioms OverwriteCold2.quiescent

#print axioms OverwriteCold2.handoff

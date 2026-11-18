import OverwriteWitnesses

namespace OverwriteCold4

open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NormalUniformNE NestedSavedReplayCycle NestedColdMachine OverwriteReplay OverwriteWitnesses

set_option maxRecDepth 16384

set_option maxHeartbeats 80000000

theorem cold : OverwriteReplay.rounds true 6 4 3 3 methods rows3 saved3 OverwriteWitnesses.source = state4 := by decide

theorem quiescent : OverwriteReplay.round true 4 3 3 methods rows3 saved3 state4 = state4 := by decide

theorem handoff : OverwriteReplay.outputRows state4 = rows4 ∧ OverwriteReplay.outputSaved 4 saved3 state4 = saved4 := by decide

end OverwriteCold4

#print axioms OverwriteCold4.cold

#print axioms OverwriteCold4.quiescent

#print axioms OverwriteCold4.handoff

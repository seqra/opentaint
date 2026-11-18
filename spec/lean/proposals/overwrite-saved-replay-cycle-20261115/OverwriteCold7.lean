import OverwriteWitnesses

namespace OverwriteCold7

open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NormalUniformNE NestedSavedReplayCycle NestedColdMachine OverwriteReplay OverwriteWitnesses

set_option maxRecDepth 16384

set_option maxHeartbeats 80000000

theorem cold : OverwriteReplay.rounds true 6 7 6 3 methods rows6 saved6 OverwriteWitnesses.source = state7 := by decide

theorem quiescent : OverwriteReplay.round true 7 6 3 methods rows6 saved6 state7 = state7 := by decide

theorem handoff : OverwriteReplay.outputRows state7 = rows7 ∧ OverwriteReplay.outputSaved 7 saved6 state7 = saved7 := by decide

end OverwriteCold7

#print axioms OverwriteCold7.cold

#print axioms OverwriteCold7.quiescent

#print axioms OverwriteCold7.handoff

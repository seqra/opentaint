import OverwriteWitnesses

namespace OverwriteCold13

open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NormalUniformNE NestedSavedReplayCycle NestedColdMachine OverwriteReplay OverwriteWitnesses

set_option maxRecDepth 16384

set_option maxHeartbeats 80000000

theorem cold : OverwriteReplay.rounds true 6 13 12 3 methods rows12 saved12 OverwriteWitnesses.source = state13 := by decide

theorem quiescent : OverwriteReplay.round true 13 12 3 methods rows12 saved12 state13 = state13 := by decide

theorem handoff : OverwriteReplay.outputRows state13 = rows13 ∧ OverwriteReplay.outputSaved 13 saved12 state13 = saved13 := by decide

end OverwriteCold13

#print axioms OverwriteCold13.cold

#print axioms OverwriteCold13.quiescent

#print axioms OverwriteCold13.handoff

import OverwriteWitnesses

namespace OverwriteCold12

open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NormalUniformNE NestedSavedReplayCycle NestedColdMachine OverwriteReplay OverwriteWitnesses

set_option maxRecDepth 16384

set_option maxHeartbeats 80000000

theorem cold : OverwriteReplay.rounds true 6 12 11 3 methods rows11 saved11 OverwriteWitnesses.source = state12 := by decide

theorem quiescent : OverwriteReplay.round true 12 11 3 methods rows11 saved11 state12 = state12 := by decide

theorem handoff : OverwriteReplay.outputRows state12 = rows12 ∧ OverwriteReplay.outputSaved 12 saved11 state12 = saved12 := by decide

end OverwriteCold12

#print axioms OverwriteCold12.cold

#print axioms OverwriteCold12.quiescent

#print axioms OverwriteCold12.handoff

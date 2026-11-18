import OverwriteWitnesses

namespace OverwriteCold11

open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NormalUniformNE NestedSavedReplayCycle NestedColdMachine OverwriteReplay OverwriteWitnesses

set_option maxRecDepth 16384

set_option maxHeartbeats 80000000

theorem cold : OverwriteReplay.rounds true 6 11 10 3 methods rows10 saved10 OverwriteWitnesses.source = state11 := by decide

theorem quiescent : OverwriteReplay.round true 11 10 3 methods rows10 saved10 state11 = state11 := by decide

theorem handoff : OverwriteReplay.outputRows state11 = rows11 ∧ OverwriteReplay.outputSaved 11 saved10 state11 = saved11 := by decide

end OverwriteCold11

#print axioms OverwriteCold11.cold

#print axioms OverwriteCold11.quiescent

#print axioms OverwriteCold11.handoff

import OverwriteWitnesses

namespace OverwriteCold8

open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NormalUniformNE NestedSavedReplayCycle NestedColdMachine OverwriteReplay OverwriteWitnesses

set_option maxRecDepth 16384

set_option maxHeartbeats 80000000

theorem cold : OverwriteReplay.rounds true 6 8 7 3 methods rows7 saved7 OverwriteWitnesses.source = state8 := by decide

theorem quiescent : OverwriteReplay.round true 8 7 3 methods rows7 saved7 state8 = state8 := by decide

theorem handoff : OverwriteReplay.outputRows state8 = rows8 ∧ OverwriteReplay.outputSaved 8 saved7 state8 = saved8 := by decide

end OverwriteCold8

#print axioms OverwriteCold8.cold

#print axioms OverwriteCold8.quiescent

#print axioms OverwriteCold8.handoff

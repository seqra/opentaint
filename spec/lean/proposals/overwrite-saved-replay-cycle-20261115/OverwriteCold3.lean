import OverwriteWitnesses

namespace OverwriteCold3

open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NormalUniformNE NestedSavedReplayCycle NestedColdMachine OverwriteReplay OverwriteWitnesses

set_option maxRecDepth 16384

set_option maxHeartbeats 80000000

theorem cold : OverwriteReplay.rounds true 6 3 2 3 methods rows2 saved2 OverwriteWitnesses.source = state3 := by decide

theorem quiescent : OverwriteReplay.round true 3 2 3 methods rows2 saved2 state3 = state3 := by decide

theorem handoff : OverwriteReplay.outputRows state3 = rows3 ∧ OverwriteReplay.outputSaved 3 saved2 state3 = saved3 := by decide

end OverwriteCold3

#print axioms OverwriteCold3.cold

#print axioms OverwriteCold3.quiescent

#print axioms OverwriteCold3.handoff

import OverwriteWitnesses

namespace OverwriteCold5

open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NormalUniformNE NestedSavedReplayCycle NestedColdMachine OverwriteReplay OverwriteWitnesses

set_option maxRecDepth 16384

set_option maxHeartbeats 80000000

theorem cold : OverwriteReplay.rounds true 6 5 4 3 methods rows4 saved4 OverwriteWitnesses.source = state5 := by decide

theorem quiescent : OverwriteReplay.round true 5 4 3 methods rows4 saved4 state5 = state5 := by decide

theorem handoff : OverwriteReplay.outputRows state5 = rows5 ∧ OverwriteReplay.outputSaved 5 saved4 state5 = saved5 := by decide

end OverwriteCold5

#print axioms OverwriteCold5.cold

#print axioms OverwriteCold5.quiescent

#print axioms OverwriteCold5.handoff

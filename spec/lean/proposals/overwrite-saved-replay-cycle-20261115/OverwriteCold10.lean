import OverwriteWitnesses

namespace OverwriteCold10

open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NormalUniformNE NestedSavedReplayCycle NestedColdMachine OverwriteReplay OverwriteWitnesses

set_option maxRecDepth 16384

set_option maxHeartbeats 80000000

theorem cold : OverwriteReplay.rounds true 6 10 9 3 methods rows9 saved9 OverwriteWitnesses.source = state10 := by decide

theorem quiescent : OverwriteReplay.round true 10 9 3 methods rows9 saved9 state10 = state10 := by decide

theorem handoff : OverwriteReplay.outputRows state10 = rows10 ∧ OverwriteReplay.outputSaved 10 saved9 state10 = saved10 := by decide

end OverwriteCold10

#print axioms OverwriteCold10.cold

#print axioms OverwriteCold10.quiescent

#print axioms OverwriteCold10.handoff

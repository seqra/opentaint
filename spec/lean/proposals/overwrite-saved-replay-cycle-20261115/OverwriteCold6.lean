import OverwriteWitnesses

namespace OverwriteCold6

open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NormalUniformNE NestedSavedReplayCycle NestedColdMachine OverwriteReplay OverwriteWitnesses

set_option maxRecDepth 16384

set_option maxHeartbeats 80000000

theorem cold : OverwriteReplay.rounds true 6 6 5 3 methods rows5 saved5 OverwriteWitnesses.source = state6 := by decide

theorem quiescent : OverwriteReplay.round true 6 5 3 methods rows5 saved5 state6 = state6 := by decide

theorem handoff : OverwriteReplay.outputRows state6 = rows6 ∧ OverwriteReplay.outputSaved 6 saved5 state6 = saved6 := by decide

end OverwriteCold6

#print axioms OverwriteCold6.cold

#print axioms OverwriteCold6.quiescent

#print axioms OverwriteCold6.handoff

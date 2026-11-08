/- E16 feasible source/loop/mapper path, with a whole-query gate witness.
The loop performs g then f writes. The adjacent getter demand is computed
from the real B2 getter row in WrapperRecovery. ALL extra query families can
be included provided their heads obey B2's global limit one. No historical
leaf or NORMAL provider is an input. Native dispatcher/alias adapters remain
implementation obligations. This is not a global loop termination theorem. -/
import WrapperRecovery
import GeneralLoopAdmissionOneStep

namespace LoopMapperRecovery
open PlainStarRelativeAdmission
open PlainStarWrapperRecovery
open GeneralLoopAdmissionBound

def rawLoopResult : Actual := writeForward 2 [f] (writeForward 2 [g] sourceExact)
def cutLoopResult : Actual := bound 1 rawLoopResult

theorem one_loop_body_derives_the_precise_NORMAL_fact :
    rawLoopResult = a (p argBase [f,g] .exact T) := by decide

theorem one_loop_body_has_the_actual_run1_cut :
    cutLoopResult = nextRun1 := by decide

theorem adjacent_demand_is_the_handoff_of_the_real_B2_getter :
    handoff fDemand = f3Pair := rfl

theorem adjacent_entry_is_the_fine_FLOW_query :
    f3Pair.entry = fineDemand argBase [f] := rfl

theorem real_loop_output_matches_the_general_fine_input :
    rawLoopResult = fineActual argBase [f] g 7 := rfl

universe u
theorem ALL_families_keep_the_fine_adjacent_command {Label : Type u}
    (query : List (Query Label)) (label : Label)
    (present : (⟨label,f3Pair.entry⟩ : Query Label) ∈ query) :
    (⟨label,fineSeed argBase [f] g⟩ : Command Label) ∈ commands f3 query rawLoopResult := by
  rw [real_loop_output_matches_the_general_fine_input]
  exact fine_command_is_present_with_its_own_label f3 query label argBase [f] g 7
    (by decide) (by decide) present

theorem NO_extra_cut_family_can_reproduce_that_key {Label : Type u}
    (query : List (Query Label)) (coarse : Actual)
    (heads : ∀ row ∈ query, row.entry.path.length ≤ 1)
    (cutDepth : coarse.pattern.path.length ≤ 1)
    (command : Command Label) (member : command ∈ commands f3 query coarse) :
    command.seed.initial ≠ (fineSeed argBase [f] g).initial := by
  exact NO_cut_from_ANY_other_family_reproduces_the_fine_key
    f3 query coarse argBase [f] g heads cutDepth command member

theorem proper_cut_changes_the_whole_labelled_observation {Label : Type u}
    (query : List (Query Label)) (label : Label)
    (present : (⟨label,f3Pair.entry⟩ : Query Label) ∈ query)
    (heads : ∀ row ∈ query, row.entry.path.length ≤ 1)
    (coarse : Actual) (cutDepth : coarse.pattern.path.length ≤ 1) :
    (⟨label,fineSeed argBase [f] g⟩ : Command Label) ∈ commands f3 query rawLoopResult ∧
    (⟨label,fineSeed argBase [f] g⟩ : Command Label) ∉ commands f3 query coarse := by
  constructor
  · exact ALL_families_keep_the_fine_adjacent_command query label present
  · intro member
    exact NO_extra_cut_family_can_reproduce_that_key query coarse heads cutDepth _ member rfl

/-- A concrete reference gate for the single adjacent family. The previous
all-family theorem proves that adding any bounded family cannot erase this
witness. The native gate compares its complete labelled observations. -/
def selectedAdjacentGate : Option Actual :=
  let fine := emit f3 f3Pair.entry rawLoopResult
  let coarse := emit f3 f3Pair.entry cutLoopResult
  if fine != coarse then some rawLoopResult else none

theorem actual_adjacent_C2_keeps_the_fine_key :
    emit f3 f3Pair.entry rawLoopResult = some fSeedF3 := by decide

theorem actual_coarse_C2_does_not_keep_the_fine_key :
    emit f3 f3Pair.entry cutLoopResult ≠ some fSeedF3 := by decide

theorem loop_gate_keeps_the_precise_NORMAL_output :
    selectedAdjacentGate = some nextRun3 := by decide

/-- Recompute the source, R1/B2 getter records, real reverse source permission
and precise F3 mapper output. Gate success does not create the source permit;
operationalThreeRuns derives it through the real reverse read/write path. -/
def loopMapperRuns (fWrappers gWrappers : Nat) : Option Actual := do
  let loopOutput ← selectedAdjacentGate
  if loopOutput = nextRun3 then operationalThreeRuns fWrappers gWrappers else none

theorem feasible_loop_mapper_path_keeps_the_required_NORMAL_finding
    (fWrappers gWrappers : Nat) :
    (loopMapperRuns fWrappers gWrappers).bind observeSink = some .normalReport := by
  unfold loopMapperRuns
  rw [loop_gate_keeps_the_precise_NORMAL_output]
  rw [operational_three_runs_recover]
  decide

theorem wrong_full_mark_still_cannot_trigger_the_sink (other : Nat) (different : other ≠ 7) :
    observeSink (a (p outBase [element,h] .exact (.full other))) = none := by
  simp [observeSink,a,p,T,different]

end LoopMapperRecovery

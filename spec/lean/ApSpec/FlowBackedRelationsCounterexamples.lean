/-
  Edge-case checks for the FLOW-backed relation specification.
  These use the original AP emitter and selected-mark cleaner, without
  StrongQueries. No field transfer or rule condition is changed.
-/
import ApSpec.Run1FlowTaintCoverage
import ApSpec.BaseCleaner
import ApSpec.FlowBackedProtection

namespace ApSpec.FlowBackedRelationsCounterexamples
open ApSpec ApSpec.Abs ApSpec.Run1FlowTaintCoverage

def leftRead : PFact := ⟨1, [10], .star Excl.empty, .star⟩
def rightRead : PFact := ⟨1, [20], .star Excl.empty, .star⟩
def valueX : PFact := initial 2 [] .star
def resultR : PFact := anyFinal 3 [] .star
def cleanFieldsT : Cleaner := ⟨2, [], .below, some 7⟩

/-- Two branches: left read then selected cleanup, or right read without cleanup. -/
theorem left_read_flow :
    applyEdge (startFact (initial 1 [] .star)) leftRead valueX =
      ⟨[⟨anyFinal 2 [] .star, true⟩], []⟩ := by rfl

theorem right_read_flow :
    applyEdge (startFact (initial 1 [] .star)) rightRead valueX =
      ⟨[⟨anyFinal 2 [] .star, true⟩], []⟩ := by rfl

theorem selected_cleanup_excludes_flow_T :
    BaseCleaner.cleanRes cleanFieldsT ⟨anyFinal 2 [] .star, true⟩ =
      ⟨[⟨anyFinal 2 [] (.starEx [7]), true⟩], [7]⟩ := by rfl

theorem marked_left_read :
    applyEdge (startFact (initial 1 [] (.conc 7))) leftRead valueX =
      ⟨[⟨anyFinal 2 [] (.conc 7), true⟩], []⟩ := by rfl

theorem selected_cleanup_keeps_marked_root :
    BaseCleaner.cleanRes cleanFieldsT ⟨anyFinal 2 [] (.conc 7), true⟩ =
      ⟨[⟨⟨2, [], .exact, .conc 7⟩, true⟩], []⟩ := by rfl

theorem spread_kept_root :
    applyEdge ⟨⟨2, [], .exact, .conc 7⟩, true⟩ valueX resultR =
      ⟨[⟨anyFinal 3 [] (.conc 7), true⟩], []⟩ := by rfl

/-- The uncleaned branch supplies a FLOW/ANY image which covers the marked image. -/
theorem right_branch_coarse_coverage (l0 l1 : Loc)
    (h : den (initial 1 [] (.conc 7)) (anyFinal 3 [] (.conc 7)) l0 l1) :
    den (initial 1 [] .star) (anyFinal 3 [] .star) l0 l1 :=
  generated_output_is_coarsely_covered l0 l1 h

/-- The first three protection rules do not detect a selected cleanup. -/
theorem ordinary_mark_transport_stays_unprotected :
    summaryProtection false false 7 7 7 = false := by decide

theorem coarse_rule_would_remove_the_marked_demand :
    maySubsume true (summaryProtection false false 7 7 7) = true := by decide

/-- A real root T survives a below cleaner. -/
theorem real_root_survives : cleanFieldsT.cleansB ⟨2, [], 7⟩ = false := by rfl

/-- The original FLOW-form start also excludes T on the backwards cleaner path. -/
theorem backward_selected_cleanup :
    BaseCleaner.cleanRes cleanFieldsT ⟨valueX, false⟩ =
      ⟨[⟨{ valueX with mark := .starEx [7] }, false⟩], [7]⟩ := by rfl

def leftBackwardSummary : AFact :=
  ⟨⟨1, [10], .any, .starEx [7]⟩, true⟩

def rightBackwardSummary : AFact :=
  ⟨⟨1, [20], .any, .star⟩, true⟩

theorem left_flow_summary_does_not_answer_T :
    (applySummary ⟨⟨3, [], .exact, .conc 7⟩, false⟩
      (initial 3 [] .star) leftBackwardSummary).facts = [] := by rfl

theorem marked_query_can_keep_root_T :
    (BaseCleaner.cleanRes cleanFieldsT ⟨⟨2, [], .exact, .conc 7⟩, false⟩).facts =
      [⟨⟨2, [], .exact, .conc 7⟩, false⟩] := by rfl

/-- Accepted correction: the cleaner residual is an assign-back of T. -/
theorem corrected_cleaner_keeps_demand :
    maySubsume true (FlowBackedProtection.ruleFlag false 7 7 7) = false := by decide

def controls : List Bool := [
  decide (maySubsume true (FlowBackedProtection.ruleFlag false 7 7 7) = false),
  decide (maySubsume true (FlowBackedProtection.ruleFlag false 7 9 7) = false),
  decide (maySubsume true (FlowBackedProtection.callFlag false false 7 9 7) = false),
  decide (cleanFieldsT.cleansB ⟨2, [], 7⟩ = false),
  decide (memB 7 [7] = true)
]

#print axioms left_read_flow
#print axioms right_read_flow
#print axioms selected_cleanup_excludes_flow_T
#print axioms marked_left_read
#print axioms selected_cleanup_keeps_marked_root
#print axioms spread_kept_root
#print axioms right_branch_coarse_coverage
#print axioms ordinary_mark_transport_stays_unprotected
#print axioms coarse_rule_would_remove_the_marked_demand
#print axioms real_root_survives
#print axioms backward_selected_cleanup
#print axioms left_flow_summary_does_not_answer_T
#print axioms marked_query_can_keep_root_T
#print axioms corrected_cleaner_keeps_demand

end ApSpec.FlowBackedRelationsCounterexamples

/- Executable scalar table for the existing C5 conclusion operator.
No native packed backend or complete block fixed point is claimed. -/
import AnnotatedC5Exit

namespace ScalarChainIntersectionExamples
open AnnotatedC5Exit

def pat (path : List Nat) (tail : Tail) (slot : Slot := .full 7)
    (excluded : List Nat := []) : Pattern :=
  ⟨0,path.map RelativeRestriction.Accessor.field,tail,slot,excluded.map RelativeRestriction.Accessor.field⟩
def fact (path : List Nat) (tail : Tail) (layer : Layer)
    (slot : Slot := .full 7) (excluded : List Nat := []) : Fact :=
  ⟨pat path tail slot excluded,layer,false⟩
def meet (raw : Fact) (demand : Pattern) (limit : Nat := 4) : Option Fact :=
  restrictData true limit raw demand

theorem exact_under_ANY_stays_NORMAL :
    meet (fact [] .exact .normal) (pat [] .may) = some (fact [] .exact .normal) := by decide
theorem MAY_to_exact_stays_DEMAND :
    meet (fact [] .may .demand) (pat [] .exact) = some (fact [] .exact .demand) := by decide
theorem STAR_under_exact_keeps_correlation :
    meet (fact [] .star .demand) (pat [] .exact) = some (fact [] .star .demand) := by decide
theorem MUST_collects_both_exclusions :
    meet (fact [] .must .normal (.full 7) [1]) (pat [] .star (.full 7) [2]) =
      some (fact [] .must .normal (.full 7) [1,2]) := by decide
theorem one_new_field_fits_the_paired_budget :
    meet (fact [1,2] .exact .normal) (pat [1] .may) =
      some (fact [1,2] .exact .normal) := by decide
theorem overflow_cuts_at_dp_depth_plus_one :
    meet (fact [1,2,3] .exact .normal) (pat [1] .may) =
      some (fact [1,2] .may .demand) := by decide
theorem exact_selector_rejects_deeper_conclusion :
    meet (fact [1,2] .exact .normal) (pat [1] .exact) = none := by decide
theorem uniform_ancestor_rebases_at_demand :
    meet (fact [] .must .normal) (pat [1] .may) =
      some (fact [1] .must .normal) := by decide
theorem MAY_ancestor_refines_with_DEMAND_support :
    meet (fact [] .may .demand) (pat [1] .exact) =
      some (fact [1] .exact .demand) := by decide
theorem STAR_ancestor_conclusion_keeps_its_whole_relation :
    meet (fact [] .star .demand) (pat [1] .exact) =
      some (fact [] .star .demand) := by decide
theorem exact_ancestor_does_not_taint_child :
    meet (fact [] .exact .normal) (pat [1] .may) = none := by decide
theorem excluded_child_is_rejected :
    meet (fact [] .must .normal (.full 7) [1]) (pat [1] .may) = none := by decide
theorem different_branches_reject :
    meet (fact [1] .exact .normal) (pat [2] .may) = none := by decide
theorem different_marks_reject :
    meet (fact [] .exact .normal (.full 9)) (pat [] .may) = none := by decide
theorem FLOW_is_not_converted_to_T :
    meet (fact [] .star .normal (.flow [])) (pat [] .may) =
      some (fact [] .star .normal (.flow [])) := by decide
theorem FLOW_excluding_T_is_rejected :
    meet (fact [] .star .normal (.flow [7])) (pat [] .may) = none := by decide

/-- Reference splitting keeps each original dp; it never pools unrelated exits. -/
structure Row where
  dp : Pattern
  dc : List Pattern

def splitResults (entry : Pattern → Pattern → Bool) (p : Pattern)
    (conclusions : List Fact) (rows : List Row) : List Fact :=
  rows.flatMap fun row => row.dc.flatMap fun dc =>
    if entry dc p then conclusions.filterMap (fun c => meet c row.dp) else []

theorem each_split_output_uses_ONE_original_pair
    (entry : Pattern → Pattern → Bool) (p : Pattern) (conclusions : List Fact)
    (rows : List Row) (result : Fact) (present : result ∈ splitResults entry p conclusions rows) :
    ∃ row, row ∈ rows ∧ ∃ dc, dc ∈ row.dc ∧ entry dc p = true ∧
      ∃ c, c ∈ conclusions ∧ meet c row.dp = some result := by
  obtain ⟨row,inRows,inRow⟩ := List.mem_flatMap.mp present
  obtain ⟨dc,inEntries,inEntry⟩ := List.mem_flatMap.mp inRow
  split at inEntry
  next accepted =>
    obtain ⟨c,inConclusions,produced⟩ := List.mem_filterMap.mp inEntry
    exact ⟨row,inRows,dc,inEntries,accepted,c,inConclusions,produced⟩
  next rejected => simp at inEntry

def acceptsBase (dc p : Pattern) : Bool := decide (dc.base = p.base)
def twoPairs : List Row := [
  ⟨pat [1] .may,[pat [] .may]⟩,
  ⟨pat [1,2,3] .may,[{(pat [] .may) with base := 1}]⟩]

theorem unrelated_long_exit_budget_cannot_be_borrowed :
    splitResults acceptsBase (pat [] .star (.flow []))
      [fact [1,2,3] .exact .normal (.flow [])] twoPairs =
      [fact [1,2] .may .demand (.flow [])] := by decide

end ScalarChainIntersectionExamples

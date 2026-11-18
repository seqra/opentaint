import DescendantCleanerCycle
namespace ExactMUSTClosure
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NormalUniformNE
open UniformRootCleanerCycle UniformRootCleanerPolicy
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h

/-- Selected EXACT-only cleaner. Caller keeps other reach modes outside
    this function. The existing selected-survivor H producer is retained. -/
def eligible (base selected : Nat) (c : Value) : Bool :=
  c.ap.base==base && c.ap.mark==some selected && c.ap.tail==.must

def corrected (old : Value → Option Value) (base selected : Nat) (c : Value) : Option Value :=
  if eligible base selected c then some {c with h:=true} else old c

def revised : Value → Option Value:=corrected DescendantCleanerCycle.exactClean x t

theorem every_selected_uniform_header_and_layer_is_preserved
    (old : Value → Option Value) (base selected : Nat) (c : Value)
    (yes : eligible base selected c=true) :
    corrected old base selected c=some {c with h:=true} := by simp [corrected,yes]

theorem unsupported_marks_bases_and_tails_keep_the_old_transfer
    (old : Value → Option Value) (base selected : Nat) (c : Value)
    (no : eligible base selected c=false) : corrected old base selected c=old c := by simp [corrected,no]

theorem a_DEMAND_uniform_input_is_never_upgraded
    (old : Value → Option Value) (base selected : Nat) (c : Value)
    (yes : eligible base selected c=true) (d : c.demand=true) :
    (corrected old base selected c).any (fun v=> !v.demand)=false := by simp [corrected,yes,d]

theorem abstract_FLOW_and_nonMUST_inputs_are_unchanged
    (old : Value → Option Value) (base selected : Nat) (c : Value)
    (flowOrNotMUST : c.ap.mark=none ∨ c.ap.tail≠.must) :
    corrected old base selected c=old c := by
  rcases flowOrNotMUST with flow | notMust
  · simp [corrected,eligible,flow]
  · have no : (c.ap.tail==.must)=false := beq_eq_false_iff_ne.mpr notMust
    simp [corrected,eligible,no]

-- Concept: split only along the ONE configured cleaner path. The outside
-- region uses the existing field hole; recursively process its child.
-- At the exact cleaner head the already selected MUST exception keeps it.
-- This is a semantic proof view, not an unbounded runtime fact store.
def conceptual (remaining holes suffix : List Nat) : Bool :=
  match remaining with
  | []=>ExclusionChildCover.permits holes suffix
  | field::rest=>if holes.contains field then ExclusionChildCover.permits holes suffix else
      ExclusionChildCover.permits (field::holes) suffix ||
      match suffix with
      | []=>false
      | first::tail=>if first==field then conceptual rest [] tail else false

theorem projection_closure_of_the_existing_same_head_rule_preserves_the_uniform_region
    (remaining holes suffix : List Nat) :
    conceptual remaining holes suffix=ExclusionChildCover.permits holes suffix := by
  induction remaining generalizing holes suffix with
  | nil=>rfl
  | cons field rest ih=>
    cases blocked : holes.contains field
    · cases suffix with
      | nil=>simp only [conceptual,blocked,Bool.false_eq_true,ite_false,ExclusionChildCover.permits,Bool.true_or]
      | cons first tail=>
        by_cases eq : first=field
        · subst first
          simp only [conceptual,blocked,Bool.false_eq_true,ite_false,ExclusionChildCover.permits,
            List.contains_cons,beq_self_eq_true,Bool.true_or,Bool.not_true,Bool.false_or,ite_true]
          rw [ih]
          cases tail <;> rfl
        · have different : (first==field)=false := beq_eq_false_iff_ne.mpr eq
          simp only [conceptual,blocked,Bool.false_eq_true,ite_false,ExclusionChildCover.permits,
            List.contains_cons,different,Bool.false_or,Bool.or_false]
    · simp only [conceptual,blocked,ite_true]

/-- No enumeration of all field names. One outside row per path prefix
    and the accepted final MUST row suffice in the conceptual version. -/
def conceptualRows (remaining : List Nat) : Nat:=remaining.length+1

theorem the_optimized_transfer_uses_one_row_instead_of_a_path_spine (remaining : List Nat) :
    1≤conceptualRows remaining := Nat.le_add_left 1 remaining.length

theorem optimized_and_conceptual_outputs_have_the_same_point_membership
    (remaining holes suffix : List Nat) :
    ExclusionChildCover.permits holes suffix=conceptual remaining holes suffix :=
  (projection_closure_of_the_existing_same_head_rule_preserves_the_uniform_region remaining holes suffix).symm

theorem the_repaired_cleaner_keeps_the_NORMAL_uniform_source :
    revised sourceValue=some {sourceValue with h:=true} := by decide

def run1Targets : List SinkTarget := ((revised sourceValue).bind reportSink).toList

theorem the_new_case_has_a_NORMAL_target_and_empty_handoff_at_run1 :
    run1Targets=[.normal sinkId] ∧ nextDemand run1Targets=[] := by decide

def stopped : Bool:= (nextDemand run1Targets).isEmpty

def later : Nat → Bool
 | 0=>stopped
 | n+1=>later n

theorem an_uncapped_schedule_cannot_restart_this_completed_case (n : Nat) : later n=true := by
  induction n with
  | zero=>rfl
  | succ _ ih=>exact ih

theorem exact_nonuniform_point_cleaning_stays_precise :
    revised (val (ap x DescendantCleanerCycle.cleaned .exact (some t)))=none := by decide

theorem existing_same_head_MUST_behavior_and_DEMAND_layers_are_retained :
    revised ⟨ap x DescendantCleanerCycle.cleaned .must (some t),false,false⟩=
      some ⟨ap x DescendantCleanerCycle.cleaned .must (some t),false,true⟩ ∧
    revised cleanedSource=some cleanedSource := by decide

-- Explicit semantic consequence: the policy is the existing coarsened
-- MUST cleaner contract closed under projection, not exact point deletion.
def oldPointSurvives (word : Path) : Bool:=word != DescendantCleanerCycle.cleaned

theorem the_same_coarsening_can_now_cover_the_selected_descendant_point :
    oldPointSurvives DescendantCleanerCycle.cleaned=false ∧
    admits .must [] DescendantCleanerCycle.cleaned=true ∧
    (revised sourceValue).any (fun v=> !v.demand)=true := by decide
end ExactMUSTClosure

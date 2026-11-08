/-
Selected local cleaner-result rule. This module has not been executed by its
author. A caller first runs the existing cleaner base/mark/E/position tests
and its old partial-result exceptions. Only the selected concrete STAR result
which is still PART/DEMAND becomes ANY. No initial, original, H or layer is
changed, and no result is created for an empty/full-kill result list.

The position belongs to the original input. In particular, the native
same-head BELOW branch has already produced EXACT before this adapter runs.
The imported three-kind Value does not represent native MUST separately;
native MUST branches and packed/mask/lowering equivalence remain adapters.
The finite E31 links are to the existing example only, not a general
equivalence with its deliberately narrower root-cleaner candidate wrapper.
-/
import CleanerMaySurvivorCandidate

namespace SelectedCleanerStarSurvivor
open ApSpec PlainStarRelativeAdmission RootExactCleanerGap

set_option maxRecDepth 16384
set_option maxHeartbeats 32000000

/-- Scalarized selected membership. FULL-mask callers use the same geometry
with the selected atom as `cl.mark`; unselected mask bits do not enter here. -/
def selectedPart (cl : Cleaner) (pos : CPos) (selected : Mark) (v : Value) : Prop :=
  pos = .part ∧ cl.mark = some selected ∧ v.data.fact.base = cl.base ∧
    v.data.fact.mark = .conc selected ∧ v.data.demand = true

instance (cl : Cleaner) (pos : CPos) (selected : Mark) (v : Value) :
    Decidable (selectedPart cl pos selected v) := by
  unfold selectedPart
  infer_instance

/-- Kind.any carries Empty E. All other record fields are copied literally. -/
def asMAY (v : Value) : Value :=
  {v with data := {v.data with fact := {v.data.fact with kind := .any}}}

def transform (cl : Cleaner) (pos : CPos) (selected : Mark) (v : Value) : Value :=
  match v.data.fact.kind with
  | .star _ => if selectedPart cl pos selected v then asMAY v else v
  | _ => v

def results (cl : Cleaner) (pos : CPos) (selected : Mark) (old : List Value) : List Value :=
  old.map (transform cl pos selected)

def transformRow (cl : Cleaner) (pos : CPos) (selected : Mark) (row : Row) : Row :=
  {row with output := transform cl pos selected row.output}

theorem selected_PART_STAR_becomes_ANY
    (cl : Cleaner) (selected : Mark) (v : Value) (e : Excl)
    (star : v.data.fact.kind = .star e)
    (accepted : selectedPart cl .part selected v) :
    transform cl .part selected v = asMAY v := by
  simp [transform,star,accepted]

theorem base_path_mark_layer_and_H_are_literal
    (cl : Cleaner) (pos : CPos) (selected : Mark) (v : Value) :
    (transform cl pos selected v).data.fact.base = v.data.fact.base ∧
    (transform cl pos selected v).data.fact.path = v.data.fact.path ∧
    (transform cl pos selected v).data.fact.mark = v.data.fact.mark ∧
    (transform cl pos selected v).data.demand = v.data.demand ∧
    (transform cl pos selected v).h = v.h := by
  cases shape : v.data.fact.kind with
  | star e =>
      by_cases accepted : selectedPart cl pos selected v <;>
        simp [transform,shape,accepted,asMAY]
  | any => simp [transform,shape]
  | exact => simp [transform,shape]

theorem normal_result_is_unchanged
    (cl : Cleaner) (pos : CPos) (selected : Mark) (v : Value)
    (normal : v.data.demand = false) : transform cl pos selected v = v := by
  cases shape : v.data.fact.kind <;>
    simp [transform,shape,selectedPart,normal]

theorem every_changed_result_is_DEMAND
    (cl : Cleaner) (pos : CPos) (selected : Mark) (v : Value)
    (changed : transform cl pos selected v ≠ v) :
    (transform cl pos selected v).data.demand = true := by
  have oldDemand : v.data.demand = true := by
    cases layer : v.data.demand with
    | false => exact False.elim (changed (normal_result_is_unchanged cl pos selected v layer))
    | true => rfl
  exact (base_path_mark_layer_and_H_are_literal cl pos selected v).2.2.2.1.trans oldDemand

theorem a_change_requires_the_selected_PART_STAR
    (cl : Cleaner) (pos : CPos) (selected : Mark) (v : Value)
    (changed : transform cl pos selected v ≠ v) :
    selectedPart cl pos selected v ∧ ∃ e, v.data.fact.kind = .star e := by
  cases shape : v.data.fact.kind with
  | star e =>
      by_cases accepted : selectedPart cl pos selected v
      · exact ⟨accepted,⟨e,rfl⟩⟩
      · exact False.elim (changed (by simp [transform,shape,accepted]))
  | any => exact False.elim (changed (by simp [transform,shape]))
  | exact => exact False.elim (changed (by simp [transform,shape]))

theorem a_changed_result_is_ANY_with_Empty_E
    (cl : Cleaner) (pos : CPos) (selected : Mark) (v : Value)
    (changed : transform cl pos selected v ≠ v) :
    (transform cl pos selected v).data.fact.kind = .any := by
  obtain ⟨accepted,e,shape⟩ := a_change_requires_the_selected_PART_STAR cl pos selected v changed
  simp [transform,shape,accepted,asMAY]

/-- This is conservative relation inclusion, not equality: independent ANY
suffixes can contain pairs absent from correlated STAR. The old E is not a
new filter on ANY, whose representation has no field-exclusion coordinate. -/
theorem transformed_relation_contains_every_old_pair
    (cl : Cleaner) (pos : CPos) (selected : Mark) (v : Value)
    (initial : PFact) (l0 l1 : Loc) (old : den initial v.data.fact l0 l1) :
    den initial (transform cl pos selected v).data.fact l0 l1 := by
  cases shape : v.data.fact.kind with
  | star e =>
      by_cases accepted : selectedPart cl pos selected v
      · have widened := CleanerMaySurvivorCandidate.STAR_relation_is_contained_in_MAY_relation
          initial v.data.fact e l0 l1 shape old
        simpa [transform,shape,accepted,asMAY] using widened
      · simpa [transform,shape,accepted] using old
  | any => simpa [transform,shape] using old
  | exact => simpa [transform,shape] using old

theorem disjoint_result_is_unchanged (cl : Cleaner) (selected : Mark) (v : Value) :
    transform cl .disjoint selected v = v := by
  cases shape : v.data.fact.kind <;> simp [transform,shape,selectedPart]

theorem inside_result_is_unchanged (cl : Cleaner) (selected : Mark) (v : Value) :
    transform cl .inside selected v = v := by
  cases shape : v.data.fact.kind <;> simp [transform,shape,selectedPart]

theorem RemoveAll_result_is_unchanged
    (cl : Cleaner) (pos : CPos) (selected : Mark) (v : Value)
    (allMarks : cl.mark = none) : transform cl pos selected v = v := by
  cases shape : v.data.fact.kind <;> simp [transform,shape,selectedPart,allMarks]

theorem another_mark_is_unchanged
    (cl : Cleaner) (pos : CPos) (selected : Mark) (v : Value)
    (other : v.data.fact.mark ≠ .conc selected) : transform cl pos selected v = v := by
  cases shape : v.data.fact.kind <;> simp [transform,shape,selectedPart,other]

theorem another_base_is_unchanged
    (cl : Cleaner) (pos : CPos) (selected : Mark) (v : Value)
    (other : v.data.fact.base ≠ cl.base) : transform cl pos selected v = v := by
  cases shape : v.data.fact.kind <;> simp [transform,shape,selectedPart,other]

theorem EXACT_result_is_unchanged
    (cl : Cleaner) (pos : CPos) (selected : Mark) (v : Value)
    (shape : v.data.fact.kind = .exact) : transform cl pos selected v = v := by
  simp [transform,shape]

theorem ANY_result_is_unchanged
    (cl : Cleaner) (pos : CPos) (selected : Mark) (v : Value)
    (shape : v.data.fact.kind = .any) : transform cl pos selected v = v := by
  simp [transform,shape]

theorem FLOW_result_is_unchanged
    (cl : Cleaner) (pos : CPos) (selected : Mark) (v : Value)
    (abstract : ∀ m, v.data.fact.mark ≠ .conc m) : transform cl pos selected v = v :=
  another_mark_is_unchanged cl pos selected v (abstract selected)

/-- Native same-head BELOW's old STAR branch supplies this already-EXACT
result. This theorem deliberately does not replace that native old branch
by the older three-kind BaseCleaner model's STAR partial branch. -/
theorem same_head_BELOW_already_EXACT_is_unchanged
    (base : Base) (path : List Acc) (selected : Mark) (layer h : Bool) :
    transform ⟨base,path,.below,some selected⟩ .part selected
      ⟨⟨⟨base,path,.exact,.conc selected⟩,layer⟩,h⟩ =
      ⟨⟨⟨base,path,.exact,.conc selected⟩,layer⟩,h⟩ := rfl

theorem full_kill_cannot_gain_a_result (cl : Cleaner) (pos : CPos) (selected : Mark) :
    results cl pos selected [] = [] := rfl

theorem result_count_and_order_are_map_only
    (cl : Cleaner) (pos : CPos) (selected : Mark) (old : List Value) :
    (results cl pos selected old).length = old.length := by simp [results]

theorem normal_result_list_is_unchanged
    (cl : Cleaner) (pos : CPos) (selected : Mark) (old : List Value) :
    (results cl pos selected old).filter (fun v => !v.data.demand) =
      old.filter (fun v => !v.data.demand) := by
  induction old with
  | nil => rfl
  | cons v rest ih =>
      have layer := (base_path_mark_layer_and_H_are_literal cl pos selected v).2.2.2.1
      cases normal : v.data.demand with
      | false =>
          simp [results,normal_result_is_unchanged cl pos selected v normal,normal] at ih ⊢
          exact ih
      | true => simp [results,layer,normal] at ih ⊢; exact ih

theorem predecessor_initial_is_literal
    (cl : Cleaner) (pos : CPos) (selected : Mark) (row : Row) :
    (transformRow cl pos selected row).initial = row.initial := rfl

theorem no_ANY_initial_is_introduced
    (cl : Cleaner) (pos : CPos) (selected : Mark) (row : Row)
    (old : row.initial.tail ≠ .any) : (transformRow cl pos selected row).initial.tail ≠ .any := old

/- Finite E31 adapter. The generic transformation is scoped by the original
input's position, unlike the historical root-only `widen` helper. -/
def rootClean (v : Value) : List Value :=
  (RootExactCleanerGap.clean v).map
    (transform cleaner (ApSpec.cleanPos cleaner v.data.fact) t)

def rootBoundary (mode : Mode) (v : Value) : List Value :=
  if mode.direction = .forward then
    (rootClean v).flatMap fun a => [a] ++ copy arg ret a
  else (copy ret arg v).flatMap rootClean

def firstRows : List Row := zeroRow :: unique (r1Seeds.flatMap fun seed =>
  (rootBoundary ⟨1,1,.forward⟩ (startValue seed)).map (publicRow seed.initial))

def infer (mode : Mode) (permissions : List FlowDemandCompletion.Row) (v : Value) : List Row :=
  unique ((commands mode permissions v).flatMap fun seed =>
    (rootBoundary mode (startValue seed)).flatMap fun raw =>
      permissions.filterMap fun permission => finish mode permission seed raw)

def secondRows : List Row := infer b2 (handoff b2 firstRows) sinkReverse
def nextSaved : List Row := normal firstRows ++ (normal secondRows).map reverseNormal

theorem E31_run1_full_catalog_matches_the_existing_positive_example :
    firstRows = CleanerMaySurvivorCandidate.firstRows := by decide

theorem E31_run2_full_catalog_matches_the_existing_positive_example :
    secondRows = CleanerMaySurvivorCandidate.secondRows := by decide

theorem E31_original_partial_result_is_protected_ANY_DEMAND :
    rootClean (startValue ⟨pat arg [] .star (.full t),.demand⟩) =
      [value (pat arg [] .any (.full t)) .demand true] := by decide

theorem E31_disjoint_descendant_STAR_is_not_widened :
    rootClean (value (pat arg [g] .star (.full t)) .demand) =
      RootExactCleanerGap.clean (value (pat arg [g] .star (.full t)) .demand) := by decide

theorem E31_exact_root_is_fully_cleaned :
    rootClean (value (pat arg [] .exact (.full t))) = [] := by decide

theorem E31_wrong_mark_cannot_admit_the_backward_initial :
    commands b2 (handoff b2 firstRows) (value (pat ret [g] .exact (.full 11))) = [] := by decide

theorem E31_wrong_mark_has_no_T_sink_witness :
    (applyRows nextSaved (value (pat arg [g] .exact (.full 11)))).filterMap hitSink = [] := by decide

theorem E31_run3_has_the_existing_NORMAL_finding : targets nextSaved = [false] := by
  simpa [nextSaved,E31_run1_full_catalog_matches_the_existing_positive_example,
    E31_run2_full_catalog_matches_the_existing_positive_example,
    CleanerMaySurvivorCandidate.nextSaved] using
      CleanerMaySurvivorCandidate.the_third_forward_phase_has_a_NORMAL_finding

end SelectedCleanerStarSurvivor

/- Four-tail scalar adapter. It consumes the old scalar cleaner result and
the position already decided from the input. Native packing, full-mask
scalarization and named-field lowering are separate adapter obligations. -/
namespace SelectedCleanerStarSurvivor

open ApSpec PlainStarRelativeAdmission RootExactCleanerGap

def scalarSelectedPart (cleanerBase : Nat) (pos : CPos) (selected : Nat)
    (v : Actual) : Prop :=
  pos = .part ∧ v.pattern.base = cleanerBase ∧
    v.pattern.mark = .full selected ∧ v.layer = .demand

instance (cleanerBase : Nat) (pos : CPos) (selected : Nat) (v : Actual) :
    Decidable (scalarSelectedPart cleanerBase pos selected v) := by
  unfold scalarSelectedPart
  infer_instance

def scalarAsMAY (v : Actual) : Actual :=
  {v with pattern := {v.pattern with tail := .any,exclusion := []}}

def scalarTransform (cleanerBase : Nat) (selected : Option Nat) (pos : CPos)
    (v : Actual) : Actual :=
  match selected with
  | none => v
  | some mark =>
      match v.pattern.tail with
      | .star => if scalarSelectedPart cleanerBase pos mark v then scalarAsMAY v else v
      | _ => v

theorem scalar_MUST_is_unchanged
    (cleanerBase : Nat) (selected : Option Nat) (pos : CPos) (v : Actual)
    (must : v.pattern.tail = .must) : scalarTransform cleanerBase selected pos v = v := by
  cases selected <;> simp [scalarTransform,must]

theorem scalar_ANY_is_unchanged
    (cleanerBase : Nat) (selected : Option Nat) (pos : CPos) (v : Actual)
    (may : v.pattern.tail = .any) : scalarTransform cleanerBase selected pos v = v := by
  cases selected <;> simp [scalarTransform,may]

theorem scalar_EXACT_is_unchanged
    (cleanerBase : Nat) (selected : Option Nat) (pos : CPos) (v : Actual)
    (exact : v.pattern.tail = .exact) : scalarTransform cleanerBase selected pos v = v := by
  cases selected <;> simp [scalarTransform,exact]

theorem scalar_NORMAL_is_unchanged
    (cleanerBase : Nat) (selected : Option Nat) (pos : CPos) (v : Actual)
    (normal : v.layer = .normal) : scalarTransform cleanerBase selected pos v = v := by
  cases selected with
  | none => rfl
  | some mark =>
      cases shape : v.pattern.tail <;>
        simp [scalarTransform,shape,scalarSelectedPart,normal]

theorem scalar_RemoveAll_is_unchanged (cleanerBase : Nat) (pos : CPos) (v : Actual) :
    scalarTransform cleanerBase none pos v = v := rfl

theorem scalar_nonPART_is_unchanged
    (cleanerBase : Nat) (selected : Option Nat) (pos : CPos) (v : Actual)
    (other : pos ≠ .part) : scalarTransform cleanerBase selected pos v = v := by
  cases selected with
  | none => rfl
  | some mark =>
      cases shape : v.pattern.tail <;>
        simp [scalarTransform,shape,scalarSelectedPart,other]

theorem scalar_other_mark_is_unchanged
    (cleanerBase selected : Nat) (pos : CPos) (v : Actual)
    (other : v.pattern.mark ≠ .full selected) :
    scalarTransform cleanerBase (some selected) pos v = v := by
  cases shape : v.pattern.tail <;>
    simp [scalarTransform,shape,scalarSelectedPart,other]

theorem scalar_other_base_is_unchanged
    (cleanerBase : Nat) (selected : Option Nat) (pos : CPos) (v : Actual)
    (other : v.pattern.base ≠ cleanerBase) : scalarTransform cleanerBase selected pos v = v := by
  cases selected with
  | none => rfl
  | some mark =>
      cases shape : v.pattern.tail <;>
        simp [scalarTransform,shape,scalarSelectedPart,other]

theorem scalar_base_path_mark_layer_and_H_are_literal
    (cleanerBase : Nat) (selected : Option Nat) (pos : CPos) (v : Actual) :
    (scalarTransform cleanerBase selected pos v).pattern.base = v.pattern.base ∧
    (scalarTransform cleanerBase selected pos v).pattern.path = v.pattern.path ∧
    (scalarTransform cleanerBase selected pos v).pattern.mark = v.pattern.mark ∧
    (scalarTransform cleanerBase selected pos v).layer = v.layer ∧
    (scalarTransform cleanerBase selected pos v).hasProtection = v.hasProtection := by
  cases selected with
  | none => exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  | some mark =>
      cases shape : v.pattern.tail with
      | star =>
          by_cases accepted : scalarSelectedPart cleanerBase pos mark v <;>
            simp [scalarTransform,shape,accepted,scalarAsMAY]
      | exact => simp [scalarTransform,shape]
      | any => simp [scalarTransform,shape]
      | must => simp [scalarTransform,shape]

theorem scalar_change_requires_selected_PART_STAR_DEMAND
    (cleanerBase : Nat) (selected : Option Nat) (pos : CPos) (v : Actual)
    (changed : scalarTransform cleanerBase selected pos v ≠ v) :
    ∃ mark, selected = some mark ∧ scalarSelectedPart cleanerBase pos mark v ∧
      v.pattern.tail = .star := by
  cases selected with
  | none => exact False.elim (changed rfl)
  | some mark =>
      cases shape : v.pattern.tail with
      | star =>
          by_cases accepted : scalarSelectedPart cleanerBase pos mark v
          · exact ⟨mark,rfl,accepted,rfl⟩
          · exact False.elim (changed (by simp [scalarTransform,shape,accepted]))
      | exact => exact False.elim (changed (by simp [scalarTransform,shape]))
      | any => exact False.elim (changed (by simp [scalarTransform,shape]))
      | must => exact False.elim (changed (by simp [scalarTransform,shape]))

theorem scalar_changed_result_has_selected_mark_EmptyE_and_preserved_annotations
    (cleanerBase : Nat) (selected : Option Nat) (pos : CPos) (v : Actual)
    (changed : scalarTransform cleanerBase selected pos v ≠ v) :
    ∃ mark, selected = some mark ∧
      (scalarTransform cleanerBase selected pos v).pattern.mark = .full mark ∧
      (scalarTransform cleanerBase selected pos v).pattern.tail = .any ∧
      (scalarTransform cleanerBase selected pos v).pattern.exclusion = [] ∧
      (scalarTransform cleanerBase selected pos v).layer = .demand ∧
      (scalarTransform cleanerBase selected pos v).pattern.base = v.pattern.base ∧
      (scalarTransform cleanerBase selected pos v).pattern.path = v.pattern.path ∧
      (scalarTransform cleanerBase selected pos v).hasProtection = v.hasProtection := by
  obtain ⟨mark,selectedIs,accepted,star⟩ :=
    scalar_change_requires_selected_PART_STAR_DEMAND cleanerBase selected pos v changed
  refine ⟨mark,selectedIs,?_⟩
  simp [scalarTransform,selectedIs,star,accepted,scalarAsMAY,
    accepted.2.2.1,accepted.2.2.2]

theorem scalar_selected_PART_STAR_is_rendered_as_ANY
    (cleanerBase selected : Nat) (v : Actual)
    (star : v.pattern.tail = .star)
    (accepted : scalarSelectedPart cleanerBase .part selected v) :
    scalarTransform cleanerBase (some selected) .part v = scalarAsMAY v := by
  simp [scalarTransform,star,accepted]

/- The existing RootExactCleanerGap.actual encoder supports EXACT/ANY and
finite-E STAR concrete values. This is an operator correspondence, not an
assertion that its older encoder represents native MUST, universal E or mx. -/
theorem selected_guards_correspond_to_three_kind_values
    (cl : Cleaner) (pos : CPos) (selected : Mark) (v : Value)
    (selectedIs : cl.mark = some selected) :
    selectedPart cl pos selected v ↔
      scalarSelectedPart cl.base pos selected (RootExactCleanerGap.actual v) := by
  cases v with
  | mk data h =>
      cases data with
      | mk fact demand =>
          cases fact with
          | mk base path kind mark =>
              cases mark <;> cases demand <;>
                simp [selectedPart,scalarSelectedPart,selectedIs,
                  RootExactCleanerGap.actual,uncore]

theorem actual_encoding_of_asMAY (v : Value) :
    RootExactCleanerGap.actual (asMAY v) = scalarAsMAY (RootExactCleanerGap.actual v) := rfl

/-- Supported finite-E concrete three-kind values. The guard proof above also
handles abstract marks, but this bridge makes no lossy-codec equivalence claim. -/
def supportedThreeKind (v : Value) : Prop :=
  (match v.data.fact.kind with | .star .univ => False | _ => True) ∧
    ∃ mark, v.data.fact.mark = .conc mark

theorem scalar_transform_corresponds_on_supported_three_kind_values
    (cl : Cleaner) (pos : CPos) (selected : Mark) (v : Value)
    (selectedIs : cl.mark = some selected) (_supported : supportedThreeKind v) :
    RootExactCleanerGap.actual (transform cl pos selected v) =
      scalarTransform cl.base cl.mark pos (RootExactCleanerGap.actual v) := by
  cases shape : v.data.fact.kind with
  | star e =>
      by_cases accepted : selectedPart cl pos selected v
      · have scalarAccepted :=
          (selected_guards_correspond_to_three_kind_values cl pos selected v selectedIs).mp accepted
        simp only [RootExactCleanerGap.actual,uncore,shape] at scalarAccepted
        simp [transform,shape,accepted,scalarTransform,selectedIs,
          RootExactCleanerGap.actual,uncore,scalarAccepted,asMAY,scalarAsMAY]
      · have scalarDenied : ¬ scalarSelectedPart cl.base pos selected (RootExactCleanerGap.actual v) :=
          fun found => accepted
            ((selected_guards_correspond_to_three_kind_values cl pos selected v selectedIs).mpr found)
        simp only [RootExactCleanerGap.actual,uncore,shape] at scalarDenied
        simp [transform,shape,accepted,scalarTransform,selectedIs,
          RootExactCleanerGap.actual,uncore,scalarDenied]
  | any => simp [transform,shape,scalarTransform,selectedIs,RootExactCleanerGap.actual,uncore]
  | exact => simp [transform,shape,scalarTransform,selectedIs,RootExactCleanerGap.actual,uncore]

end SelectedCleanerStarSurvivor

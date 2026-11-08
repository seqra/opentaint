/-
Selected same-head STAR/STAR record overlap component. The actual can have
STAR or MUST tail. The record itself always has correlated STAR endpoints;
no native MUST-record capability is synthesized. No proper-ancestor matching
lane is added. Native mark matching and packed-tree adapters are separate.
-/
import ExclusionCorrelatedInclusion
import Matching

namespace StarHeadOverlap
open ExclusionCorrelatedInclusion

inductive Direction where | direct | inverse
deriving DecidableEq, Repr
inductive ActualTail where | star | must
deriving DecidableEq, Repr
inductive Layer where | normal | demand
deriving DecidableEq, Repr

def joinLayer : Layer → Layer → Layer
  | .normal, .normal => .normal
  | _, _ => .demand

structure Actual where
  base : Nat
  path : List Nat
  tail : ActualTail
  exclusion : List Nat
  layer : Layer
  mark : Nat
  protection : List Nat
deriving DecidableEq, Repr

def readerGeometry (direction : Direction) (row : Row) : FlowAntichains.Relations.Row Nat :=
  match direction with
  | .direct => row.geometry
  | .inverse => FlowAntichains.Relations.reverseGeometry row.geometry

def readerE (direction : Direction) (row : Row) : List Nat :=
  match direction with
  | .direct => row.inputE
  | .inverse => []

def effectiveE (row : Row) : List Nat := row.inputE ++ row.outputE

def sameHead (direction : Direction) (row : Row) (actual : Actual) : Bool :=
  decide (actual.base = (readerGeometry direction row).inputBase ∧
    actual.path = (readerGeometry direction row).inputPrefix) &&
    markAdmits row.excludedMarks actual.mark

def matchedSlice (direction : Direction) (row : Row) (actual : Actual) : Actual :=
  {actual with exclusion := actual.exclusion ++ readerE direction row}

/- Lists represent exclusion sets denotationally. Idempotent native union
can remove the duplicated reader E since it already occurs in effectiveE. -/
def output (direction : Direction) (row : Row) (recordLayer : Layer)
    (actual : Actual) : Actual :=
  {actual with
    base := (readerGeometry direction row).outputBase
    path := (readerGeometry direction row).outputPrefix
    exclusion := actual.exclusion ++ effectiveE row
    layer := joinLayer actual.layer recordLayer}

structure Applied where
  original : Actual
  slice : Actual
  result : Actual
deriving DecidableEq, Repr

def applyAtHead (direction : Direction) (row : Row) (recordLayer : Layer)
    (actual : Actual) : Option Applied :=
  if sameHead direction row actual then
    some ⟨actual,matchedSlice direction row actual,output direction row recordLayer actual⟩
  else none

theorem admits_append_exact_intersection (left right suffix : List Nat) :
    admits (left ++ right) suffix = true ↔
      admits left suffix = true ∧ admits right suffix = true := by
  cases suffix with
  | nil => simp [admits]
  | cons first rest => simp [admits,List.mem_append,not_or]

theorem matched_slice_is_exact_read_overlap (direction : Direction) (row : Row)
    (actual : Actual) (suffix : List Nat) :
    admits (matchedSlice direction row actual).exclusion suffix = true ↔
      admits actual.exclusion suffix = true ∧ admits (readerE direction row) suffix = true := by
  exact admits_append_exact_intersection _ _ _

theorem effective_E_requires_both_endpoints (row : Row) (suffix : List Nat) :
    admits (effectiveE row) suffix = true ↔
      admits row.inputE suffix = true ∧ admits row.outputE suffix = true := by
  exact admits_append_exact_intersection _ _ _

theorem output_retains_actual_and_both_endpoint_Es (direction : Direction) (row : Row)
    (recordLayer : Layer) (actual : Actual) (suffix : List Nat) :
    admits (output direction row recordLayer actual).exclusion suffix = true ↔
      admits actual.exclusion suffix = true ∧
        admits row.inputE suffix = true ∧ admits row.outputE suffix = true := by
  simp only [output,admits_append_exact_intersection,effective_E_requires_both_endpoints]

theorem output_using_matched_slice_is_equivalent (direction : Direction) (row : Row)
    (recordLayer : Layer) (actual : Actual) (suffix : List Nat) :
    admits ((matchedSlice direction row actual).exclusion ++ effectiveE row) suffix = true ↔
      admits (output direction row recordLayer actual).exclusion suffix = true := by
  cases direction <;>
    simp [matchedSlice,readerE,output,effectiveE,admits,and_assoc,and_comm]

theorem same_head_overlap_is_always_nonempty_at_root (direction : Direction) (row : Row)
    (actual : Actual) : admits (matchedSlice direction row actual).exclusion [] = true := rfl

theorem equal_head_and_mark_are_sufficient_to_accept (direction : Direction) (row : Row)
    (recordLayer : Layer) (actual : Actual)
    (head : actual.base = (readerGeometry direction row).inputBase ∧
      actual.path = (readerGeometry direction row).inputPrefix)
    (mark : markAdmits row.excludedMarks actual.mark = true) :
    applyAtHead direction row recordLayer actual =
      some ⟨actual,matchedSlice direction row actual,output direction row recordLayer actual⟩ := by
  simp [applyAtHead,sameHead,head,mark]

theorem base_mismatch_still_rejects (direction : Direction) (row : Row)
    (recordLayer : Layer) (actual : Actual)
    (mismatch : actual.base ≠ (readerGeometry direction row).inputBase) :
    applyAtHead direction row recordLayer actual = none := by
  simp [applyAtHead,sameHead,mismatch]

theorem different_head_still_rejects_this_lane (direction : Direction) (row : Row)
    (recordLayer : Layer) (actual : Actual)
    (mismatch : actual.path ≠ (readerGeometry direction row).inputPrefix) :
    applyAtHead direction row recordLayer actual = none := by
  simp [applyAtHead,sameHead,mismatch]

theorem excluded_mark_still_rejects (direction : Direction) (row : Row)
    (recordLayer : Layer) (actual : Actual)
    (excluded : markAdmits row.excludedMarks actual.mark = false) :
    applyAtHead direction row recordLayer actual = none := by
  simp [applyAtHead,sameHead,excluded]

theorem slice_does_not_change_actual_tail_layer_mark_or_H (direction : Direction) (row : Row)
    (actual : Actual) :
    (matchedSlice direction row actual).tail = actual.tail ∧
    (matchedSlice direction row actual).layer = actual.layer ∧
    (matchedSlice direction row actual).mark = actual.mark ∧
    (matchedSlice direction row actual).protection = actual.protection := ⟨rfl,rfl,rfl,rfl⟩

theorem successful_application_retains_original_storage_value (direction : Direction) (row : Row)
    (recordLayer : Layer) (actual : Actual) (applied : Applied)
    (made : applyAtHead direction row recordLayer actual = some applied) :
    applied.original = actual := by
  unfold applyAtHead at made
  split at made
  next => cases made; rfl
  next => cases made

theorem output_does_not_change_tail_mark_or_H (direction : Direction) (row : Row)
    (recordLayer : Layer) (actual : Actual) :
    (output direction row recordLayer actual).tail = actual.tail ∧
    (output direction row recordLayer actual).mark = actual.mark ∧
    (output direction row recordLayer actual).protection = actual.protection := ⟨rfl,rfl,rfl⟩

theorem DEMAND_actual_never_becomes_NORMAL (direction : Direction) (row : Row)
    (recordLayer : Layer) (actual : Actual) (demand : actual.layer = .demand) :
    (output direction row recordLayer actual).layer = .demand := by
  cases recordLayer <;> simp [output,joinLayer,demand]

theorem DEMAND_record_never_produces_NORMAL (direction : Direction) (row : Row)
    (actual : Actual) : (output direction row .demand actual).layer = .demand := by
  cases layer : actual.layer <;> simp [output,joinLayer,layer]

theorem NORMAL_support_stays_NORMAL (direction : Direction) (row : Row)
    (actual : Actual) (normal : actual.layer = .normal) :
    (output direction row .normal actual).layer = .normal := by simp [output,joinLayer,normal]

theorem inverse_has_no_invented_reader_E (row : Row) : readerE .inverse row = [] := rfl

theorem inverse_result_still_contains_both_endpoint_Es (row : Row)
    (actual : Actual) (recordLayer : Layer) :
    (output .inverse row recordLayer actual).exclusion =
      actual.exclusion ++ (row.inputE ++ row.outputE) := rfl

/- A denotational effect retains the SAME original actual membership and
mark. Only the stored record relation changes under coverage. For STAR this
states pair inclusion; for MUST it also retains every supplied point. This
is not a proof about an arbitrary native MUST-record constructor. -/
def supplies (actual : Actual) (location : List Nat) : Prop :=
  ∃ suffix, actual.path ++ suffix = location ∧ admits actual.exclusion suffix = true

def effect (row : Row) (actual : Actual) (pair : FlowAntichains.Relations.Pair Nat) : Prop :=
  pair.mark = actual.mark ∧ actual.base = pair.inputBase ∧
    supplies actual pair.inputPath ∧ denotes row pair

theorem checked_pair_cover_preserves_every_actual_effect (short long : Row)
    (residual : List Nat) (actual : Actual) (pair : FlowAntichains.Relations.Pair Nat)
    (covered : coverAt short long residual = true) (member : effect long actual pair) :
    effect short actual pair := by
  obtain ⟨mark,base,input,record⟩ := member
  exact ⟨mark,base,input,generalized_cover_transports_every_pair short long residual covered pair record⟩

def inverseRow (row : Row) : Row :=
  ⟨FlowAntichains.Relations.reverseGeometry row.geometry,
    row.outputE,row.inputE,row.excludedMarks⟩

theorem checked_pair_cover_is_symmetric_under_generic_reversal (short long : Row)
    (residual : List Nat) (covered : coverAt short long residual = true) :
    coverAt (inverseRow short) (inverseRow long) residual = true := by
  obtain ⟨geometry,marks,excluded⟩ := of_decide_eq_true covered
  apply decide_eq_true
  refine ⟨?_,marks,?_⟩
  · change FlowAntichains.Relations.specialize
      (FlowAntichains.Relations.reverseGeometry short.geometry) residual =
      FlowAntichains.Relations.reverseGeometry long.geometry
    rw [← FlowAntichains.Relations.reverse_geometry_specializes,geometry]
  · cases residual with
    | nil => exact ⟨excluded.2,excluded.1⟩
    | cons first rest => exact ⟨excluded.2,excluded.1⟩

theorem inverse_checked_cover_keeps_every_actual_effect (short long : Row)
    (residual : List Nat) (actual : Actual) (pair : FlowAntichains.Relations.Pair Nat)
    (covered : coverAt short long residual = true)
    (member : effect (inverseRow long) actual pair) :
    effect (inverseRow short) actual pair :=
  checked_pair_cover_preserves_every_actual_effect (inverseRow short) (inverseRow long)
    residual actual pair (checked_pair_cover_is_symmetric_under_generic_reversal short long residual covered) member

theorem same_head_role_guard_is_unchanged (role : FlowAntichains.Matching.Role)
    (candidate : FlowAntichains.Matching.Candidate)
    (same : candidate.leaf.path = candidate.query.path) :
    FlowAntichains.Matching.keep role candidate = FlowAntichains.Matching.nativeKeep candidate :=
  FlowAntichains.Matching.preserve_at role candidate same

theorem proper_ancestor_STAR_current_lane_remains_blocked
    (candidate : FlowAntichains.Matching.Candidate)
    (tail : candidate.leaf.tail = .star)
    (base : FlowAntichains.Matching.sameBase candidate = true)
    (proper : FlowAntichains.Matching.strictAncestor candidate.leaf.path candidate.query.path = true) :
    FlowAntichains.Matching.keep .current candidate = false := by
  simp [FlowAntichains.Matching.keep,FlowAntichains.Matching.blocked,tail,base,proper]

def exampleRow : Row := ⟨⟨1,10,20,[],[]⟩,[3],[4],[]⟩
def exampleActual : Actual := ⟨10,[],.must,[5],.normal,7,[7]⟩

theorem incomparable_E_now_matches_without_losing_E :
    sameHeadNativeStarMatch exampleActual.exclusion exampleRow.inputE = false ∧
    sameHead .direct exampleRow exampleActual = true ∧
    (output .direct exampleRow .normal exampleActual).exclusion = [5,3,4] ∧
    admits (output .direct exampleRow .normal exampleActual).exclusion [6] = true ∧
    admits (output .direct exampleRow .normal exampleActual).exclusion [3] = false ∧
    admits (output .direct exampleRow .normal exampleActual).exclusion [4] = false ∧
    admits (output .direct exampleRow .normal exampleActual).exclusion [5] = false := by decide

theorem incoming_STAR_uses_the_same_overlap_without_a_MUST_upgrade :
    (output .direct exampleRow .normal {exampleActual with tail := .star}).tail = .star ∧
    (output .direct exampleRow .normal {exampleActual with tail := .star,layer := .demand}).layer = .demand := by decide

end StarHeadOverlap

#print axioms StarHeadOverlap.admits_append_exact_intersection
#print axioms StarHeadOverlap.matched_slice_is_exact_read_overlap
#print axioms StarHeadOverlap.effective_E_requires_both_endpoints
#print axioms StarHeadOverlap.output_retains_actual_and_both_endpoint_Es
#print axioms StarHeadOverlap.output_using_matched_slice_is_equivalent
#print axioms StarHeadOverlap.same_head_overlap_is_always_nonempty_at_root
#print axioms StarHeadOverlap.equal_head_and_mark_are_sufficient_to_accept
#print axioms StarHeadOverlap.base_mismatch_still_rejects
#print axioms StarHeadOverlap.different_head_still_rejects_this_lane
#print axioms StarHeadOverlap.excluded_mark_still_rejects
#print axioms StarHeadOverlap.slice_does_not_change_actual_tail_layer_mark_or_H
#print axioms StarHeadOverlap.successful_application_retains_original_storage_value
#print axioms StarHeadOverlap.output_does_not_change_tail_mark_or_H
#print axioms StarHeadOverlap.DEMAND_actual_never_becomes_NORMAL
#print axioms StarHeadOverlap.DEMAND_record_never_produces_NORMAL
#print axioms StarHeadOverlap.NORMAL_support_stays_NORMAL
#print axioms StarHeadOverlap.inverse_has_no_invented_reader_E
#print axioms StarHeadOverlap.inverse_result_still_contains_both_endpoint_Es
#print axioms StarHeadOverlap.checked_pair_cover_preserves_every_actual_effect
#print axioms StarHeadOverlap.checked_pair_cover_is_symmetric_under_generic_reversal
#print axioms StarHeadOverlap.inverse_checked_cover_keeps_every_actual_effect
#print axioms StarHeadOverlap.same_head_role_guard_is_unchanged
#print axioms StarHeadOverlap.proper_ancestor_STAR_current_lane_remains_blocked
#print axioms StarHeadOverlap.incomparable_E_now_matches_without_losing_E
#print axioms StarHeadOverlap.incoming_STAR_uses_the_same_overlap_without_a_MUST_upgrade

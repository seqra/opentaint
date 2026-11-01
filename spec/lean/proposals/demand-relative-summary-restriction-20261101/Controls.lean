import Std

/-!
Typed boundary controls for demand-relative AP summary restriction, 2026-11-01.

This model keeps the AP geometry meet as an explicit parameter. It proves the
control/terminal boundary, not the scalar or packed geometry implementation.
ZERO control and Targets are separate constructors; they are not APs of depth 0.
The newly selected restriction applies to AP summaries. The selected NORMAL
Target lane retains its existing admission, application, persistence and skip
rules. A DEMAND Target still needs its existing complete paired permission.
-/
namespace RelativeControls
set_option autoImplicit false

inductive Direction where | forward | backward deriving DecidableEq, Repr
inductive Layer where | normal | demand deriving DecidableEq, Repr
inductive Tail where | exact | star | may | must deriving DecidableEq, Repr

structure AP where
  base : Nat
  fields : List Nat
  mark : Nat
  tail : Tail
  layer : Layer
  nonSubsumable : Bool
  deriving DecidableEq, Repr

inductive Original where
  | zero
  | single (key : Nat)
  | nd (keys : List Nat)
  deriving DecidableEq, Repr

inductive Entry where
  | zero
  | target
  | data (key : Nat)
  deriving DecidableEq, Repr

inductive Exit where
  | zero
  | data (selector : AP)
  deriving DecidableEq, Repr

structure Pair where
  entry : Entry
  exit : Exit
  deriving DecidableEq, Repr

def entryAccepts : Entry → Original → Bool
  | .zero, .zero | .target, .zero => true
  | .data key, .single actual => key == actual
  | .data key, .nd keys => keys.contains key
  | _, _ => false

/-- Only data selectors supply a field budget. Typed ZERO has no AP depth. -/
def fieldBudget (runLimit : Nat) : Exit → Option Nat
  | .zero => none
  | .data dp => some (min runLimit (dp.fields.length + 1))

theorem zero_has_no_field_budget (runLimit : Nat) :
    fieldBudget runLimit .zero = none := rfl

theorem data_budget_uses_old_dp (runLimit : Nat) (dp : AP) :
    fieldBudget runLimit (.data dp) = some (min runLimit (dp.fields.length + 1)) := rfl

/-- A cut preserves the mark and annotation; overflow is retained as MAY/DEMAND. -/
def cut (limit : Nat) (value : AP) : AP :=
  if value.fields.length ≤ limit then value
  else { value with fields := value.fields.take limit, tail := .may, layer := .demand }

theorem cut_preserves_mark (limit : Nat) (value : AP) :
    (cut limit value).mark = value.mark := by
  unfold cut
  split <;> rfl

theorem cut_preserves_protection (limit : Nat) (value : AP) :
    (cut limit value).nonSubsumable = value.nonSubsumable := by
  unfold cut
  split <;> rfl

theorem overflowing_cut_is_demand (limit : Nat) (value : AP)
    (overflow : limit < value.fields.length) :
    (cut limit value).tail = .may ∧ (cut limit value).layer = .demand := by
  have tooLong : ¬ value.fields.length ≤ limit := Nat.not_le_of_gt overflow
  simp only [cut, tooLong, ↓reduceIte, and_self]

theorem cut_is_bounded (limit : Nat) (value : AP) :
    (cut limit value).fields.length ≤ limit := by
  unfold cut
  split
  next within => exact within
  next => simpa only [List.length_take] using Nat.min_le_left limit value.fields.length

inductive Candidate where
  | data (value : AP)
  | reach (layer : Layer)
  deriving DecidableEq, Repr

/-- The complete entry and exit come from one row. The supplied meet is the
existing AP exit meet; the cut occurs after that meet, never before it. -/
def admitPair (meet : AP → AP → Option AP) (runLimit : Nat) (original : Original)
    (raw : Candidate) (pair : Pair) : Option Candidate :=
  if entryAccepts pair.entry original then
    match raw, pair.exit with
    | .reach layer, .zero => some (.reach layer)
    | .data value, .data dp =>
        (meet value dp).map fun kept => .data (cut (min runLimit (dp.fields.length + 1)) kept)
    | _, _ => none
  else none

theorem zero_original_data_is_not_exempt (meet : AP → AP → Option AP)
    (runLimit : Nat) (value dp : AP) :
    admitPair meet runLimit .zero (.data value) ⟨.target, .data dp⟩ =
      (meet value dp).map (fun kept => .data (cut (min runLimit (dp.fields.length + 1)) kept)) := rfl

theorem zero_exit_keeps_reach (meet : AP → AP → Option AP) (runLimit : Nat)
    (layer : Layer) :
    admitPair meet runLimit .zero (.reach layer) ⟨.target, .zero⟩ =
      some (.reach layer) := rfl

theorem zero_exit_does_not_admit_data (meet : AP → AP → Option AP) (runLimit : Nat)
    (value : AP) :
    admitPair meet runLimit .zero (.data value) ⟨.target, .zero⟩ = none := rfl

theorem data_exit_does_not_admit_reach (meet : AP → AP → Option AP) (runLimit : Nat)
    (dp : AP) (layer : Layer) :
    admitPair meet runLimit .zero (.reach layer) ⟨.target, .data dp⟩ = none := rfl

/-- Use the exhaustive per-pair union unless a new, cap-aware cover proof is
available. Aggregation may deduplicate exact results after this operation. -/
def admitted (meet : AP → AP → Option AP) (runLimit : Nat) (original : Original)
    (raw : Candidate) (pairs : List Pair) : List Candidate :=
  pairs.filterMap (admitPair meet runLimit original raw)

theorem admitted_has_complete_pair_witness (meet : AP → AP → Option AP)
    (runLimit : Nat) (original : Original) (raw value : Candidate) (pairs : List Pair)
    (selected : value ∈ admitted meet runLimit original raw pairs) :
    ∃ pair, pair ∈ pairs ∧ admitPair meet runLimit original raw pair = some value := by
  exact List.mem_filterMap.mp selected

theorem each_pair_result_is_retained (meet : AP → AP → Option AP)
    (runLimit : Nat) (original : Original) (raw value : Candidate) (pairs : List Pair)
    (pair : Pair) (member : pair ∈ pairs)
    (selected : admitPair meet runLimit original raw pair = some value) :
    value ∈ admitted meet runLimit original raw pairs := by
  exact List.mem_filterMap.mpr ⟨pair, member, selected⟩

inductive Target where
  | normal (id : Nat)
  | demand
  deriving DecidableEq, Repr

structure TerminalRow where
  original : Original
  target : Target
  deriving DecidableEq, Repr

/-- Targets are not Candidate.data or Candidate.reach values. No AP conversion
or field budget is used by terminal composition. -/
def terminalFieldBudget (_runLimit : Nat) (_target : Target) : Option Nat := none

theorem target_has_no_field_budget (runLimit : Nat) (target : Target) :
    terminalFieldBudget runLimit target = none := rfl

def applyTarget : Direction → Target → Layer → Option Target
  | .backward, .normal _, _ => none
  | .forward, .normal id, .normal => some (.normal id)
  | .forward, .normal _, .demand => none
  | _, .demand, _ => some .demand

theorem normal_target_requires_normal_composition (id : Nat) :
    applyTarget .forward (.normal id) .demand = none := rfl

theorem normal_target_is_ignored_backward (id : Nat) (support : Layer) :
    applyTarget .backward (.normal id) support = none := rfl

theorem normal_target_keeps_its_id (id : Nat) :
    applyTarget .forward (.normal id) .normal = some (.normal id) := rfl

def targetPairAccepts (original : Original) (pair : Pair) : Bool :=
  entryAccepts pair.entry original && match pair.exit with
    | .zero => true | .data _ => false

/-- The pre-existing DEMAND Target gate is independent of AP field cuts. The
retained NORMAL Target lane keeps its explicit selected exemption from AP C5. -/
def admitTarget (direction : Direction) (run1 knownNormal : Bool) (pairs : List Pair)
    (original : Original) (target : Target) : Option TerminalRow :=
  match target with
  | .normal id =>
      match direction with
      | .backward => none
      | .forward => if knownNormal then none else some ⟨original, .normal id⟩
  | .demand =>
      if run1 || pairs.any (targetPairAccepts original) then some ⟨original, .demand⟩ else none

theorem known_normal_target_is_not_reemitted (direction : Direction) (run1 : Bool)
    (pairs : List Pair) (original : Original) (id : Nat) :
    admitTarget direction run1 true pairs original (.normal id) = none := by
  cases direction <;> rfl

theorem normal_target_lane_does_not_require_ap_demand (run1 : Bool)
    (original : Original) (id : Nat) :
    admitTarget .forward run1 false [] original (.normal id) = some ⟨original, .normal id⟩ := rfl

theorem demand_target_requires_a_paired_zero_exit (direction : Direction)
    (original : Original) (pairs : List Pair) :
    admitTarget direction false false pairs original .demand = some ⟨original, .demand⟩ ↔
      pairs.any (targetPairAccepts original) = true := by
  simp only [admitTarget, Bool.false_or]
  split <;> simp_all

theorem demand_target_preserves_full_original (direction : Direction) (original : Original) :
    admitTarget direction true false [] original .demand = some ⟨original, .demand⟩ := rfl

def candidateLayer : Candidate → Layer
  | .data value => value.layer | .reach layer => layer

/-- This is the selected AP demand extraction rule, not terminal admission.
NORMAL ND and NORMAL backward-ZERO rows are explicit pre-existing exceptions. -/
def outgoingAP (direction : Direction) (original : Original) (candidate : Candidate) : Bool :=
  match candidateLayer candidate, original, direction with
  | .demand, _, _ => true
  | .normal, .nd _, _ => true
  | .normal, .zero, .backward => true
  | _, _, _ => false

theorem normal_backward_zero_ap_remains_guidance (value : AP)
    (normal : value.layer = .normal) :
    outgoingAP .backward .zero (.data value) = true := by
  simp only [outgoingAP, candidateLayer, normal]

theorem normal_forward_single_ap_is_not_guidance (key : Nat) (value : AP)
    (normal : value.layer = .normal) :
    outgoingAP .forward (.single key) (.data value) = false := by
  simp only [outgoingAP, candidateLayer, normal]

theorem capped_demand_must_be_classified_after_admission (direction : Direction)
    (original : Original) (limit : Nat) (value : AP) (overflow : limit < value.fields.length) :
    outgoingAP direction original (.data (cut limit value)) = true := by
  have changed := (overflowing_cut_is_demand limit value overflow).2
  simp only [outgoingAP, candidateLayer, changed]

namespace Examples

/-- A small executable geometry cell: matching bases and marks, with a MAY
selector accepting descendants. It is not a replacement for full AP geometry. -/
def descendantMeet (raw dp : AP) : Option AP :=
  if raw.base == dp.base && raw.mark == dp.mark &&
      dp.fields.isPrefixOf raw.fields && dp.tail == .may then some raw else none

def raw : AP := ⟨3, [10,20,30], 9, .exact, .normal, true⟩
def deep : AP := { raw with tail := .may }
def shallow : AP := { raw with fields := [10], tail := .may }
def deepPair : Pair := ⟨.data 7, .data deep⟩
def shallowPair : Pair := ⟨.data 7, .data shallow⟩
def capped : AP := { raw with fields := [10,20], tail := .may, layer := .demand }

theorem uncut_normal_survives :
    admitPair descendantMeet 7 (.single 7) (.data raw) deepPair = some (.data raw) := rfl

theorem shallower_pair_emits_new_demand :
    admitPair descendantMeet 7 (.single 7) (.data raw) shallowPair = some (.data capped) := rfl

/-- This represents the old raw EXACT/STAR cover shortcut. The first result
equals the whole raw value, so it stops before trying the remaining rows. -/
def oldRawCoverLoop (original : Original) (raw : Candidate) : List Pair → List Candidate
  | [] => []
  | pair :: rest =>
      match admitPair descendantMeet 7 original raw pair with
      | none => oldRawCoverLoop original raw rest
      | some value =>
          if value == raw then [value]
          else value :: oldRawCoverLoop original raw rest

theorem exhaustive_union_keeps_both_cap_families :
    admitted descendantMeet 7 (.single 7) (.data raw) [deepPair, shallowPair] =
      [.data raw, .data capped] := rfl

theorem old_raw_cover_loses_later_demand :
    oldRawCoverLoop (.single 7) (.data raw) [deepPair, shallowPair] = [.data raw] := rfl

theorem old_raw_cover_is_not_new_union :
    oldRawCoverLoop (.single 7) (.data raw) [deepPair, shallowPair] ≠
      admitted descendantMeet 7 (.single 7) (.data raw) [deepPair, shallowPair] := by decide

theorem zero_original_with_data_exit_is_capped :
    admitPair descendantMeet 7 .zero (.data raw) ⟨.target, .data shallow⟩ =
      some (.data capped) := rfl

theorem normal_raw_selection_misses_new_demand :
    outgoingAP .forward (.single 7) (.data raw) = false ∧
    outgoingAP .forward (.single 7) (.data capped) = true := ⟨rfl, rfl⟩

theorem crossed_terminal_permissions_do_not_combine :
    admitTarget .backward false false [⟨.data 7,.zero⟩, ⟨.target,.data shallow⟩]
      .zero .demand = none := rfl

theorem normal_target_still_rejects_demand_support :
    applyTarget .forward (.normal 42) .demand = none := rfl

theorem checks :
    fieldBudget 7 .zero = none ∧
    terminalFieldBudget 7 (.normal 42) = none ∧
    terminalFieldBudget 7 .demand = none ∧
    (cut 2 raw).nonSubsumable = true ∧
    (cut 2 raw).mark = 9 ∧
    outgoingAP .backward .zero (.data raw) = true := by decide

end Examples

#print axioms admitted_has_complete_pair_witness
#print axioms cut_is_bounded
#print axioms demand_target_requires_a_paired_zero_exit
#print axioms capped_demand_must_be_classified_after_admission
#print axioms Examples.old_raw_cover_is_not_new_union
#print axioms Examples.checks

end RelativeControls

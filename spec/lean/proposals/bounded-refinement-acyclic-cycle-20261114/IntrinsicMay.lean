import LocalRouting

/- A closed straight-line root with a supported AnyField-target pass rule.
   The imported proposals preserve this rule and typed ZERO/Target handling.
   No method call has an analyzable body, so there is one summarizable block.
   Only demands, sources, supported pass/sink actions and ordinary controls
   are modeled. This is not an execution of an implemented NE engine. -/
namespace BoundedIntrinsicMayCycle
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle
open BoundedLocalRouting

def x : Nat := 10
def y : Nat := 11
def sourceValue : Value := val (ap x [] .exact (some t))

inductive Endpoint where
  | zero
  | target
  deriving DecidableEq, BEq, Repr

structure Edge where
  premise : Endpoint
  conclusion : Endpoint
  demand : Bool
  deriving DecidableEq, BEq, Repr

structure ControlRow where
  entry : Endpoint
  exit : Endpoint
  deriving DecidableEq, BEq, Repr

def terminal : Edge := ⟨.zero,.target,true⟩
def completion : Edge := ⟨.zero,.zero,false⟩
def targetRow : ControlRow := ⟨.target,.zero⟩

/-- Dc Target accepts actual ZERO. Dp ZERO accepts ZERO and Target.
    A ControlRow is a demand row, never an ordinary DATA selector. -/
def controlInitial (row : ControlRow) (actual : Endpoint) : Option Endpoint :=
  if row.entry == .target && actual == .zero then some .zero else none

def controlC5 (row : ControlRow) (raw : Edge) : Option Edge :=
  if controlInitial row raw.premise == some .zero && row.exit == .zero
  then some raw else none

def handoff (edges : List Edge) : List ControlRow :=
  edges.filterMap fun e =>
    if e.demand then some ⟨e.conclusion,e.premise⟩ else none

/-- CopyMark(T, arg0 -> result.AnyField). An allowed MAY TARGET,
    not an AnyField pass input. Its result is always DEMAND (I14/D18). -/
def passForward (v : Value) : Option Value :=
  if v.ap.base == x && v.ap.path.isEmpty && v.ap.tail == .exact &&
      v.ap.mark == some t then
    some ⟨ap y [] .may (some t),true,v.h⟩
  else none

/-- The chosen sink checks y.$/T. A MAY witness includes epsilon,
    but its support remains DEMAND; no NormalTarget is manufactured. -/
def sinkForward (v : Value) : Option Edge :=
  if v.ap.base == y && v.ap.path.isEmpty && v.ap.mark == some t &&
      (v.ap.tail == .exact || v.ap.tail == .may || v.ap.tail == .must) then
    some ⟨.zero,.target,v.demand⟩
  else none

def sinkBackward : Value := val (ap y [] .exact (some t)) true

/-- Reverse the allowed AnyField TARGET. An exact y requirement overlaps
    that MAY target. Every result stays DEMAND, including exact x (I14). -/
def passBackward (v : Value) : Option Value :=
  if v.ap.base == y && v.ap.path.isEmpty && v.ap.tail == .exact &&
      v.ap.mark == some t then
    some ⟨ap x [] .exact (some t),true,v.h⟩
  else none

def sourceMatches (v : Value) : Bool :=
  v.ap.base == x && v.ap.path.isEmpty && v.ap.tail == .exact &&
    v.ap.mark == some t

/-- Apply the saved NORMAL ZERO -> x.$/T source in reverse. Convert
    its ZERO result to Target; join the already DEMAND reverse support. -/
def sourceBackward (v : Value) : Option Edge :=
  if sourceMatches v then some ⟨.zero,.target,v.demand⟩ else none

structure Capture where
  summaries : List Edge := []
  sourcePermission : Bool := false
  deriving DecidableEq, BEq, Repr

def admitted (rows : List ControlRow) : Bool := rows.contains targetRow

def forwardRun (run : Nat) (rows : List ControlRow) (permission : Bool) : Capture :=
  if (run == 1 || admitted rows) && (run == 1 || permission) then
    let result := (passForward sourceValue).bind sinkForward
    let published := if run == 1 then result.toList
      else result.toList.filterMap (controlC5 targetRow)
    ⟨completion :: published,false⟩
  else ⟨[],false⟩

def backwardRun (rows : List ControlRow) : Capture :=
  if admitted rows then
    let result := passBackward sinkBackward
    let published := (result.bind sourceBackward).toList.filterMap (controlC5 targetRow)
    ⟨completion :: published,result.any sourceMatches⟩
  else ⟨[],false⟩

def forwardFixed : Capture := ⟨[completion,terminal],false⟩
def backwardFixed : Capture := ⟨[completion,terminal],true⟩

theorem exact_source_becomes_intrinsic_may :
    passForward sourceValue = some (val (ap y [] .may (some t)) true) := by decide

theorem no_normal_output_of_the_pass (v result : Value)
    (emitted : passForward v = some result) : result.demand = true := by
  unfold passForward at emitted
  split at emitted
  · have same := Option.some.inj emitted
    rw [← same]
  · simp at emitted

theorem no_normal_output_of_the_reversed_pass (v result : Value)
    (emitted : passBackward v = some result) : result.demand = true := by
  unfold passBackward at emitted
  split at emitted
  · have same := Option.some.inj emitted
    rw [← same]
  · simp at emitted

theorem the_exact_sink_is_reached_only_with_demand_in_this_program :
    (passForward sourceValue).bind sinkForward = some terminal := by decide

theorem the_reverse_pass_reaches_the_exact_real_source :
    passBackward sinkBackward = some (val (ap x [] .exact (some t)) true) ∧
    (passBackward sinkBackward).any sourceMatches = true := by decide

theorem the_reversed_normal_source_produces_demand_target :
    (passBackward sinkBackward).bind sourceBackward = some terminal := by decide

theorem no_data_may_or_ne_initial_is_used :
    controlInitial targetRow .zero = some .zero := by decide

theorem terminal_passes_paired_c5_and_regenerates_the_same_row :
    controlC5 targetRow terminal = some terminal ∧
    handoff [completion,terminal] = [targetRow] := by decide

theorem all_data_paths_have_zero_concrete_fields :
    sourceValue.ap.path.length = 0 ∧ sinkBackward.ap.path.length = 0 ∧
    (passForward sourceValue).all (fun v => v.ap.path.isEmpty) = true := by decide

theorem no_field_cut_can_change_the_intrinsic_may (limit : Nat) :
    (passForward sourceValue).map (cut limit) = passForward sourceValue := by
  change some (cut limit (val (ap y [] .may (some t)) true)) =
    some (val (ap y [] .may (some t)) true)
  rw [no_cut_preserves_intrinsic_may limit
    (val (ap y [] .may (some t)) true) (Nat.zero_le limit)]

/-- There is no DATA query in the only analyzable block, so the prepared
    plan has no field guard or delegated coarse transfer in either run. -/
theorem no_delegation_can_be_enabled_by_an_empty_plan :
    safeCommonDelegation [] f = false := by decide

theorem the_new_normal_precoverage_case_cannot_accept_the_target :
    terminal.demand = true := rfl

theorem run1_constructs_the_base_instead_of_assuming_it :
    forwardRun 1 [] false = forwardFixed := by decide

theorem backward_recomputes_permission_and_demand :
    backwardRun (handoff forwardFixed.summaries) = backwardFixed := by decide

theorem no_saved_or_synthetic_permission_is_needed :
    backwardFixed.sourcePermission = true ∧
    forwardRun 3 [targetRow] false = ⟨[],false⟩ ∧
    backwardRun [] = ⟨[],false⟩ := by decide

theorem every_later_forward_run_recomputes_the_demand (n : Nat) :
    forwardRun (n+3) (handoff backwardFixed.summaries)
      backwardFixed.sourcePermission = forwardFixed := by
  have notFirst : (n+3 == 1) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have bad : n+3 = 1 := Nat.eq_of_beq_eq_true h
    omega
  unfold forwardRun
  rw [notFirst]
  rfl

def forwardHandoffs : Nat → Capture
  | 0 => forwardRun 1 [] false
  | n+1 =>
      let backward := backwardRun (handoff (forwardHandoffs n).summaries)
      forwardRun (2*n+3) (handoff backward.summaries) backward.sourcePermission

theorem every_forward_handoff_is_the_same_nonempty_fixed_point (n : Nat) :
    forwardHandoffs n = forwardFixed := by
  induction n with
  | zero => exact run1_constructs_the_base_instead_of_assuming_it
  | succ n ih =>
    simp only [forwardHandoffs,ih,backward_recomputes_permission_and_demand]
    exact every_later_forward_run_recomputes_the_demand (2*n)

theorem every_backward_run_also_keeps_the_same_demand (n : Nat) :
    backwardRun (handoff (forwardHandoffs n).summaries) = backwardFixed := by
  rw [every_forward_handoff_is_the_same_nonempty_fixed_point]
  exact backward_recomputes_permission_and_demand

theorem no_forward_handoff_has_empty_outgoing_demand (n : Nat) :
    handoff (forwardHandoffs n).summaries = [targetRow] := by
  rw [every_forward_handoff_is_the_same_nonempty_fixed_point]
  decide

theorem no_backward_handoff_has_empty_outgoing_demand (n : Nat) :
    handoff (backwardRun (handoff (forwardHandoffs n).summaries)).summaries =
      [targetRow] := by
  rw [every_backward_run_also_keeps_the_same_demand]
  decide

theorem finite_per_run_summary_domain (n : Nat) :
    (forwardHandoffs n).summaries.length = 2 ∧
    (backwardRun (handoff (forwardHandoffs n).summaries)).summaries.length = 2 := by
  rw [every_forward_handoff_is_the_same_nonempty_fixed_point,
    backward_recomputes_permission_and_demand]
  decide

end BoundedIntrinsicMayCycle

#print axioms BoundedIntrinsicMayCycle.exact_source_becomes_intrinsic_may
#print axioms BoundedIntrinsicMayCycle.no_normal_output_of_the_pass
#print axioms BoundedIntrinsicMayCycle.no_normal_output_of_the_reversed_pass
#print axioms BoundedIntrinsicMayCycle.the_exact_sink_is_reached_only_with_demand_in_this_program
#print axioms BoundedIntrinsicMayCycle.the_reverse_pass_reaches_the_exact_real_source
#print axioms BoundedIntrinsicMayCycle.the_reversed_normal_source_produces_demand_target
#print axioms BoundedIntrinsicMayCycle.no_data_may_or_ne_initial_is_used
#print axioms BoundedIntrinsicMayCycle.terminal_passes_paired_c5_and_regenerates_the_same_row
#print axioms BoundedIntrinsicMayCycle.all_data_paths_have_zero_concrete_fields
#print axioms BoundedIntrinsicMayCycle.no_field_cut_can_change_the_intrinsic_may
#print axioms BoundedIntrinsicMayCycle.no_delegation_can_be_enabled_by_an_empty_plan
#print axioms BoundedIntrinsicMayCycle.the_new_normal_precoverage_case_cannot_accept_the_target
#print axioms BoundedIntrinsicMayCycle.run1_constructs_the_base_instead_of_assuming_it
#print axioms BoundedIntrinsicMayCycle.backward_recomputes_permission_and_demand
#print axioms BoundedIntrinsicMayCycle.no_saved_or_synthetic_permission_is_needed
#print axioms BoundedIntrinsicMayCycle.every_later_forward_run_recomputes_the_demand
#print axioms BoundedIntrinsicMayCycle.every_forward_handoff_is_the_same_nonempty_fixed_point
#print axioms BoundedIntrinsicMayCycle.every_backward_run_also_keeps_the_same_demand
#print axioms BoundedIntrinsicMayCycle.no_forward_handoff_has_empty_outgoing_demand
#print axioms BoundedIntrinsicMayCycle.no_backward_handoff_has_empty_outgoing_demand
#print axioms BoundedIntrinsicMayCycle.finite_per_run_summary_domain

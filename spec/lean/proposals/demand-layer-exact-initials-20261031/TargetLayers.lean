import ExactAdmission
import NDProjection

namespace ExactDemand
set_option autoImplicit false

inductive Target where
  | normal (id : Nat)
  | demand
  deriving DecidableEq, Repr

def sinkTarget (id : Nat) : Layer → Target
  | .normal => .normal id | .demand => .demand

def applyTarget (target : Target) (support : Layer) : Option Target :=
  match target, support with
  | .normal id, .normal => some (.normal id)
  | .normal _, .demand => none
  | .demand, _ => some .demand

def report (zeroOrigin : Bool) : Target → Option Nat
  | .normal id => if zeroOrigin then some id else none
  | .demand => none

def continues : Target → Bool | .normal _ => false | .demand => true

def backwardTarget : Target → Option Target | .normal _ => none | .demand => some .demand

theorem demand_seed_has_no_normal_sink_witness (key : InitialKey) (id : Nat) :
    sinkTarget id (start ⟨key,.demand⟩).layer = .demand := by
  rw [demand_seed_starts_demand]
  rfl

theorem normal_target_cannot_downgrade_to_demand (id : Nat) :
    applyTarget (.normal id) .demand = none := rfl

theorem normal_target_is_ignored_backward (id : Nat) : backwardTarget (.normal id) = none := rfl

theorem demand_target_continues : continues .demand = true := rfl

theorem demand_target_cannot_report (zero : Bool) : report zero .demand = none := rfl

theorem normal_report_requires_zero (id : Nat) :
    report true (.normal id) = some id ∧ report false (.normal id) = none := ⟨rfl,rfl⟩

/-- Same key, different starting layers give different terminal behavior. -/
theorem normal_analysis_does_not_replace_demand_analysis (key : InitialKey) (id : Nat)
    (intrinsicNormal : intrinsicInitialLayer key = .normal) :
    applyTarget (sinkTarget id (start ⟨key,.normal⟩).layer) .demand = none ∧
    applyTarget (sinkTarget id (start ⟨key,.demand⟩).layer) .demand = some .demand := by
  simp only [start, intrinsicNormal, join, sinkTarget, applyTarget, and_self]

structure Summary where
  original : InitialKey
  conclusion : Pattern
  layer : Layer
  deriving DecidableEq, Repr

/-- Existing native eligibility also checks shape/kind. Layer is necessary. -/
def nativeCandidate (summary : Summary) : Option Summary :=
  match summary.layer with | .normal => some summary | .demand => none

theorem demand_summary_has_no_normal_native_record (initial : InitialKey) (output : Pattern) :
    nativeCandidate ⟨initial,output,.demand⟩ = none := rfl

/-- Dependent transfer includes incoming layer. Independent ZERO GEN is outside
    this relation and cannot be inferred from an admission event. -/
def dependentResult (seed : Seed) (operationLayer : Layer) : Layer := join (start seed).layer operationLayer

theorem dependent_demand_never_becomes_normal (key : InitialKey) (op : Layer) :
    dependentResult ⟨key,.demand⟩ op = .demand := by
  unfold dependentResult
  rw [demand_seed_starts_demand]
  rfl

/-- Arbitrary forward chains whose original dependency is retained. -/
def chainLayer (incoming : Layer) : List Layer → Layer
  | [] => incoming
  | operation :: rest => chainLayer (join incoming operation) rest

theorem demand_is_preserved_through_any_dependent_chain (operations : List Layer) :
    chainLayer .demand operations = .demand := by
  induction operations with
  | nil => rfl
  | cons operation rest ih => exact ih

/-- Existing caller application support is available before current C2.
It uses the real offered fact, caller, link, and stored-summary layers. -/
def applicationLayer (actual caller link summary : Layer) : Layer :=
  join actual (join caller (join link summary))

theorem normal_application_requires_all_normal_support (actual caller link summary : Layer) :
    applicationLayer actual caller link summary = .normal ↔
      actual = .normal ∧ caller = .normal ∧ link = .normal ∧ summary = .normal := by
  simp only [applicationLayer, join_normal_iff]

theorem demand_actual_keeps_summary_application_demand (caller link summary : Layer) :
    applicationLayer .demand caller link summary = .demand := rfl

/-- W6 production MAY facts carry DEMAND. Synthetic MAY/N values test only
    local admission robustness, not cached-caller legality. -/
def legalCaller (actual : Actual) : Bool :=
  match actual.pattern.tail with
  | .may => decide (actual.layer = .demand)
  | _ => true

theorem legal_may_actual_has_demand_layer (actual : Actual)
    (may : actual.pattern.tail = .may) (legal : legalCaller actual = true) :
    actual.layer = .demand := by
  unfold legalCaller at legal
  rw [may] at legal
  exact of_decide_eq_true legal

theorem legal_may_cannot_apply_cached_normal_target (actual : Actual)
    (may : actual.pattern.tail = .may) (legal : legalCaller actual = true)
    (caller link summary : Layer) (id : Nat) :
    applicationLayer actual.layer caller link summary = .demand ∧
    applyTarget (.normal id) (applicationLayer actual.layer caller link summary) = none := by
  rw [legal_may_actual_has_demand_layer actual may legal]
  exact ⟨rfl,rfl⟩

inductive SourceEvent where
  | none
  | acceptedReverseAction (action : Nat)
  deriving DecidableEq, Repr

def sourcePermissions : SourceEvent → List Nat
  | .none => [] | .acceptedReverseAction action => [action]

theorem admission_alone_creates_no_source_permission : sourcePermissions .none = [] := rfl

theorem native_replay_is_not_a_new_action : sourcePermissions .none = [] := rfl

theorem accepted_reverse_action_records_its_real_id (action : Nat) :
    sourcePermissions (.acceptedReverseAction action) = [action] := rfl

structure TerminalSummary where
  original : InitialKey
  target : Target
  deriving DecidableEq, Repr

/-- Existing backward source completion keeps the original data dependency. -/
def sourceCompletion (seed : Seed) : TerminalSummary := ⟨seed.initial,.demand⟩

theorem source_completion_preserves_nonzero_origin (pattern : Pattern) (layer : Layer) :
    (sourceCompletion ⟨.data pattern,layer⟩).original = .data pattern := rfl

def zeroOnlyCallAllowed (original : InitialKey) : Bool :=
  match original with | .zero => true | .data _ => false

theorem data_demand_does_not_open_zero_only_call (pattern : Pattern) :
    zeroOnlyCallAllowed (sourceCompletion ⟨.data pattern,.demand⟩).original = false := rfl

/-- Source and sink projection use the same support-sensitive arm layer. -/
def projectedSinkTargets (id : Nat) (requirements : List Nat) (inputs : List NDProjection.Input) :
    List (NDProjection.Origin × Target) :=
  (NDProjection.project requirements inputs).map fun arm => (arm.origin, sinkTarget id arm.layer)

theorem split_nd_sink_produces_only_demand_targets :
    projectedSinkTargets 42 [1,2] NDProjection.Controls.both =
      [(.input 0,.demand),(.input 1,.demand)] := rfl

theorem split_nd_sink_keeps_physical_seed :
    NDProjection.physicalSinkSeed [1,2] = [1,2] := rfl

end ExactDemand

import Domain

namespace ExactDemand.NDProjection
open ExactDemand
set_option autoImplicit false

inductive Origin where | zero | input (id : Nat) deriving DecidableEq, Repr
structure Input where
  origin : Origin
  layer : Layer
  requirement : Nat
  deriving DecidableEq, Repr
structure Arm where
  origin : Origin
  layer : Layer
  deriving DecidableEq, Repr

def cubeLayer : List Input → Layer
  | [] => .normal
  | i :: rest => join i.layer (cubeLayer rest)

/-- Retain NORMAL only if this arm contains every dependency of the witness.
A conservative multi-origin-header implementation may demote more arms. -/
def supportsWholeWitness (origin : Origin) (inputs : List Input) : Bool :=
  inputs.all fun i => decide (i.origin = .zero) || decide (i.origin = origin)

def armLayer (origin : Origin) (inputs : List Input) : Layer :=
  if supportsWholeWitness origin inputs then cubeLayer inputs else .demand

def originIds (inputs : List Input) : List Nat :=
  (inputs.filterMap fun i => match i.origin with | .zero => none | .input id => some id).eraseDups

def arms (inputs : List Input) : List Arm :=
  match originIds inputs with
  | [] => [⟨.zero, armLayer .zero inputs⟩]
  | ids => ids.map fun id => ⟨.input id, armLayer (.input id) inputs⟩

/-- The binding is complete before projection; missing columns emit no arm. -/
def project (requirements : List Nat) (inputs : List Input) : List Arm :=
  if inputs.map Input.requirement == requirements then arms inputs else []

/-- Physical sink guidance is the full rule, never a projected unary arm. -/
def physicalSinkSeed (requirements : List Nat) : List Nat := requirements

theorem cube_is_normal_iff_every_input_is_normal (inputs : List Input) :
    cubeLayer inputs = .normal ↔ ∀ input ∈ inputs, input.layer = .normal := by
  induction inputs with
  | nil => simp [cubeLayer]
  | cons head rest ih => simp [cubeLayer, join_normal_iff, ih]

theorem normal_arm_has_whole_support (origin : Origin) (inputs : List Input)
    (normal : armLayer origin inputs = .normal) : supportsWholeWitness origin inputs = true := by
  unfold armLayer at normal
  split at normal
  · assumption
  · cases normal

theorem normal_arm_has_normal_cube (origin : Origin) (inputs : List Input)
    (normal : armLayer origin inputs = .normal) : cubeLayer inputs = .normal := by
  unfold armLayer at normal
  split at normal
  · exact normal
  · cases normal

theorem normal_arm_has_all_normal_inputs (origin : Origin) (inputs : List Input)
    (normal : armLayer origin inputs = .normal) :
    ∀ input ∈ inputs, input.layer = .normal :=
  (cube_is_normal_iff_every_input_is_normal inputs).mp (normal_arm_has_normal_cube origin inputs normal)

theorem projected_arm_retains_support_sensitive_layer (requirements : List Nat) (inputs : List Input)
    (arm : Arm) (member : arm ∈ project requirements inputs) :
    arm.layer = armLayer arm.origin inputs := by
  unfold project at member
  split at member
  next =>
    unfold arms at member
    split at member
    next =>
      have same : arm = ⟨.zero, armLayer .zero inputs⟩ := by simpa only [List.mem_singleton] using member
      cases same
      rfl
    next =>
      obtain ⟨id, _, same⟩ := List.mem_map.mp member
      cases same
      rfl
  next => cases member

theorem normal_projected_arm_has_complete_dependency_support
    (requirements : List Nat) (inputs : List Input) (arm : Arm)
    (member : arm ∈ project requirements inputs) (normal : arm.layer = .normal) :
    supportsWholeWitness arm.origin inputs = true ∧
    (∀ input ∈ inputs, input.layer = .normal) := by
  have layerEq := projected_arm_retains_support_sensitive_layer requirements inputs arm member
  have supportedNormal : armLayer arm.origin inputs = .normal := layerEq.symm.trans normal
  exact ⟨normal_arm_has_whole_support arm.origin inputs supportedNormal,
    normal_arm_has_all_normal_inputs arm.origin inputs supportedNormal⟩

theorem partial_binding_emits_nothing (requirements : List Nat) (inputs : List Input)
    (incomplete : inputs.map Input.requirement ≠ requirements) : project requirements inputs = [] := by
  simp only [project, beq_iff_eq, incomplete, ↓reduceIte]

theorem missing_support_is_demand (origin : Origin) (inputs : List Input)
    (missing : supportsWholeWitness origin inputs = false) : armLayer origin inputs = .demand := by
  simp only [armLayer, missing, Bool.false_eq_true, ↓reduceIte]

theorem sink_seed_keeps_all_columns (requirements : List Nat) :
    physicalSinkSeed requirements = requirements := rfl

namespace Controls

def both : List Input := [⟨.input 0,.normal,1⟩,⟨.input 1,.normal,2⟩]
def one : List Input := [⟨.input 0,.normal,1⟩]

theorem split_normal_source_witness_arms_are_demand :
    project [1,2] both = [⟨.input 0,.demand⟩,⟨.input 1,.demand⟩] := rfl

theorem split_normal_sink_witness_arms_are_demand :
    project [1,2] both = [⟨.input 0,.demand⟩,⟨.input 1,.demand⟩] ∧
    physicalSinkSeed [1,2] = [1,2] := ⟨rfl,rfl⟩

theorem unary_full_is_not_blanket_demoted :
    project [1] [⟨.input 0,.normal,1⟩] = [⟨.input 0,.normal⟩] := rfl

theorem same_origin_retains_normal_complete_support :
    project [1,2] [⟨.input 0,.normal,1⟩,⟨.input 0,.normal,2⟩] =
      [⟨.input 0,.normal⟩] := rfl

theorem one_origin_plus_zero_retains_normal :
    project [1,2] [⟨.input 0,.normal,1⟩,⟨.zero,.normal,2⟩] =
      [⟨.input 0,.normal⟩] := rfl

theorem zero_only_requires_the_complete_binding :
    project [1,2] [⟨.zero,.normal,1⟩,⟨.zero,.normal,2⟩] = [⟨.zero,.normal⟩] ∧
    project [1,2] [⟨.zero,.normal,1⟩] = [] := ⟨rfl,rfl⟩

theorem incomplete_source_or_sink_has_no_projection : project [1,2] one = [] := rfl

end Controls
end ExactDemand.NDProjection

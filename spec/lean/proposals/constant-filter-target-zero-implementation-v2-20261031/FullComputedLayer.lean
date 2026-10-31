import FullZeroSourceReplay

/-!
The new FULL policy preserves the layer already computed by ordinary AP
semantics. GROUP and the separately selected run-1 static approximation
remain DEMAND. The old ZERO-only force in FullZeroSourceReplay is historical;
its exact ZERO-native kernel remains valid by the compatibility theorem below.
No initial, field, cleaner, matcher, or source transfer is redefined by force.
-/
namespace FullComputedLayer
open SelectedCore
open FullZeroSourceReplay
set_option autoImplicit false

/-- No FULL-kind or ordinary-origin test remains in the selected override. -/
def force (run1 : Bool) (packet : Packet) : Packet :=
  if run1 && (packet.kind == .groupTaint || staticDependent packet) then
    { packet with layer := .demand }
  else packet

theorem later_run_unchanged (packet : Packet) : force false packet = packet := rfl

theorem ordinary_full_keeps_computed_layer (key : SourceKey) (tail : Tail)
    (layer : Layer) :
    force true ⟨key, tail, .fullTaint, .ordinary, false, layer⟩ =
      ⟨key, tail, .fullTaint, .ordinary, false, layer⟩ := rfl

theorem zero_full_keeps_computed_layer (key : SourceKey) (tail : Tail) (layer : Layer) :
    force true ⟨key, tail, .fullTaint, .zero, false, layer⟩ =
      ⟨key, tail, .fullTaint, .zero, false, layer⟩ := rfl

theorem ordinary_exact_full_can_be_normal (key : SourceKey) :
    (force true ⟨key, .exact, .fullTaint, .ordinary, false, .normal⟩).layer = .normal := rfl

theorem computed_demand_is_never_promoted (run1 : Bool) (packet : Packet)
    (demand : packet.layer = .demand) : (force run1 packet).layer = .demand := by
  unfold force
  split
  · rfl
  · exact demand

theorem payload_unchanged (run1 : Bool) (packet : Packet) :
    (force run1 packet).key = packet.key ∧
    (force run1 packet).tail = packet.tail ∧
    (force run1 packet).kind = packet.kind ∧
    (force run1 packet).origin = packet.origin ∧
    (force run1 packet).staticConclusion = packet.staticConclusion := by
  unfold force
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem group_keeps_override (key : SourceKey) (tail : Tail) (origin : Origin)
    (stat : Bool) (layer : Layer) :
    (force true ⟨key, tail, .groupTaint, origin, stat, layer⟩).layer = .demand := rfl

theorem static_conclusion_keeps_override (key : SourceKey) (tail : Tail) (kind : Kind)
    (origin : Origin) (layer : Layer) :
    (force true ⟨key, tail, kind, origin, true, layer⟩).layer = .demand := by
  cases kind <;> cases origin <;> rfl

theorem static_origin_keeps_override (key : SourceKey) (tail : Tail) (kind : Kind)
    (stat : Bool) (layer : Layer) :
    (force true ⟨key, tail, kind, .static, stat, layer⟩).layer = .demand := by
  cases kind <;> cases stat <;> rfl

theorem zero_native_kernel_unchanged (key : SourceKey) (tail : Tail) (kind : Kind)
    (stat : Bool) (layer : Layer) :
    force true ⟨key, tail, kind, .zero, stat, layer⟩ =
      FullZeroSourceReplay.force true ⟨key, tail, kind, .zero, stat, layer⟩ := by
  cases kind <;> cases stat <;> rfl

/-- This table models existing initialFacts, independently of the actor override. -/
def initialLayer (kind : Kind) (tail : Tail) : Layer :=
  match kind, tail with
  | .flow, .may => .demand
  | .flow, _ => .normal
  | _, .exact | _, .must => .normal
  | _, .star | _, .may => .demand

theorem concrete_star_initial_is_demand (kind : Kind) (notFlow : kind ≠ .flow) :
    initialLayer kind .star = .demand := by cases kind <;> simp_all [initialLayer]

theorem concrete_exact_initial_is_normal (kind : Kind) (notFlow : kind ≠ .flow) :
    initialLayer kind .exact = .normal := by cases kind <;> rfl

theorem full_star_initial_stays_demand (key : SourceKey) :
    (force true ⟨key, .star, .fullTaint, .ordinary, false,
      initialLayer .fullTaint .star⟩).layer = .demand := rfl

theorem full_exact_initial_keeps_normal (key : SourceKey) :
    (force true ⟨key, .exact, .fullTaint, .ordinary, false,
      initialLayer .fullTaint .exact⟩).layer = .normal := rfl

def cubeLayer : List Layer → Layer
  | [] => .normal
  | layer :: rest => composeLayer layer (cubeLayer rest)

theorem any_demand_keeps_cube_demand (layers : List Layer) (hit : Layer.demand ∈ layers) :
    cubeLayer layers = .demand := by
  induction layers with
  | nil => cases hit
  | cons head rest ih =>
      cases head with
      | demand => rfl
      | normal =>
          have tailHit : Layer.demand ∈ rest := by simpa using hit
          rw [cubeLayer, ih tailHit]
          rfl

theorem all_normal_cube_is_normal (n : Nat) :
    cubeLayer (List.replicate n .normal) = .normal := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, cubeLayer, ih, composeLayer]

/- A real concern after removing the blanket override: a complete NORMAL
   two-origin rule is weakened to one NORMAL arm per origin in run-1.
   A later caller can offer only that arm. The counterexample is conditional
   on those exact NORMAL inputs; their run-1 admission is a runtime adapter.
   It does not choose a mitigation or permit promoting DEMAND initials. -/
namespace NDArmRisk

def fullGuard (first second : Bool) : Bool := first && second

def weakenedArmApplies (first : Bool) (armLayer : Layer) : Bool :=
  first && (armLayer == .normal)

def reportedFromOneArm (first : Bool) (armLayer : Layer) : Option Nat :=
  if weakenedArmApplies first armLayer then
    finalReport [0] (layeredTargetSummary 0 .zero .normal 17)
  else none

theorem normal_origin_projection_can_report_without_other_input :
    cubeLayer [.normal, .normal] = .normal ∧
    fullGuard true false = false ∧
    weakenedArmApplies true .normal = true ∧
    reportedFromOneArm true .normal = some 17 := by decide

theorem demand_arm_does_not_use_normal_report_lane :
    reportedFromOneArm true .demand = none := rfl

end NDArmRisk

#print axioms ordinary_full_keeps_computed_layer
#print axioms computed_demand_is_never_promoted
#print axioms zero_native_kernel_unchanged
#print axioms full_star_initial_stays_demand
#print axioms full_exact_initial_keeps_normal
#print axioms NDArmRisk.normal_origin_projection_can_report_without_other_input

end FullComputedLayer

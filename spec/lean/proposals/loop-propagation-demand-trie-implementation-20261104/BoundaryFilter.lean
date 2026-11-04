import Std

namespace BoundaryFilter

inductive Endpoint where
  | local (id : Nat)
  | zero | static | argument (id : Nat) | receiver | returned | exception
deriving DecidableEq, Repr

inductive Direction where | forward | reverse deriving DecidableEq, Repr

structure Relation where
  premise : Endpoint
  conclusion : Endpoint
deriving DecidableEq, Repr

/-- Reverse applications produce the stored PREMISE endpoint. -/
def destination (direction : Direction) (relation : Relation) : Endpoint :=
  match direction with | .forward => relation.conclusion | .reverse => relation.premise

structure DataPacket (bits : Nat) where
  endpoint : Endpoint
  ordinaryPayload : Nat
  protection : Fin bits → Bool

inductive Output (bits : Nat) where
  | data (packet : DataPacket bits)
  | target (id : Nat)
  | request (mark : Nat)
  | staticEffect (id : Nat)

def keepEndpoint (live : Nat → Bool) : Endpoint → Bool
  | .local id => live id
  | _ => true

def keepOutput {bits : Nat} (live : Nat → Bool) : Output bits → Bool
  | .data packet => keepEndpoint live packet.endpoint
  | _ => true

/-- A capability for this exact application, not a law of arbitrary native AP. -/
def DataOnlyAt {bits : Nat} (endpoint : Endpoint) (outputs : List (Output bits)) : Prop :=
  ∀ output ∈ outputs, ∃ packet, output = .data packet ∧ packet.endpoint = endpoint

/-- Mutable applications may retain arbitrary effects. Only DATA has a fixed destination. -/
def DataAt {bits : Nat} (endpoint : Endpoint) (outputs : List (Output bits)) : Prop :=
  ∀ output ∈ outputs, match output with
    | .data packet => packet.endpoint = endpoint
    | _ => True

/-- The precomputed route token affects DATA callbacks only. Application still runs. -/
def keepPrepared {bits : Nat} (token : Bool) : Output bits → Bool
  | .data _ => token
  | _ => true

def dispatchPrepared {bits : Nat} (token : Bool) (outputs : List (Output bits)) : List (Output bits) :=
  outputs.filter (keepPrepared token)

theorem prepared_token_matches_native_guard {bits : Nat} (live : Nat → Bool) (endpoint : Endpoint)
    (outputs : List (Output bits)) (capability : DataAt endpoint outputs) :
    dispatchPrepared (keepEndpoint live endpoint) outputs = outputs.filter (keepOutput live) := by
  induction outputs with
  | nil => rfl
  | cons output rest ih =>
    have tailCapability : DataAt endpoint rest :=
      fun other member => capability other (List.mem_cons_of_mem output member)
    have atHead : keepPrepared (keepEndpoint live endpoint) output = keepOutput live output := by
      cases output with
      | data packet =>
        have same := capability (.data packet) List.mem_cons_self
        simp only [keepPrepared, keepOutput, same]
      | _ => rfl
    simp only [dispatchPrepared, List.filter_cons, atHead]
    rw [← ih tailCapability]
    rfl

theorem prepare_route_before_application_keep_effects {bits : Nat} {Input : Type}
    (apply : Direction → Relation → Input → List (Output bits))
    (direction : Direction) (relation : Relation) (input : Input) (live : Nat → Bool)
    (capability : DataAt (destination direction relation) (apply direction relation input)) :
    dispatchPrepared (keepEndpoint live (destination direction relation)) (apply direction relation input) =
      (apply direction relation input).filter (keepOutput live) :=
  prepared_token_matches_native_guard live (destination direction relation) _ capability

def nonData {bits : Nat} : Output bits → Bool
  | .data _ => false
  | _ => true

theorem all_effects_preserved_for_every_token {bits : Nat} (token : Bool) (outputs : List (Output bits)) :
    (dispatchPrepared token outputs).filter nonData = outputs.filter nonData := by
  unfold dispatchPrepared
  rw [List.filter_filter]
  apply congrArg (fun predicate => outputs.filter predicate)
  funext output
  cases output <;> rfl

theorem uniform_keep {bits : Nat} (live : Nat → Bool) (endpoint : Endpoint)
    (outputs : List (Output bits)) (capability : DataOnlyAt endpoint outputs)
    (output : Output bits) (member : output ∈ outputs) :
    keepOutput live output = keepEndpoint live endpoint := by
  obtain ⟨packet, same, base⟩ := capability output member
  subst output
  simp only [keepOutput, base]

theorem uniform_filter {bits : Nat} (live : Nat → Bool) (endpoint : Endpoint)
    (outputs : List (Output bits)) (capability : DataOnlyAt endpoint outputs) :
    outputs.filter (keepOutput live) = if keepEndpoint live endpoint then outputs else [] := by
  induction outputs with
  | nil => cases keepEndpoint live endpoint <;> rfl
  | cons output rest ih =>
    have atHead := uniform_keep live endpoint (output :: rest) capability output List.mem_cons_self
    have atTail : DataOnlyAt endpoint rest :=
      fun other member => capability other (List.mem_cons_of_mem output member)
    rw [List.filter_cons, atHead, ih atTail]
    cases keepEndpoint live endpoint <;> rfl

/-- Filtering before a pure DATA-only application retains the exact ordered output list. -/
theorem move_boundary_filter_before_application {bits : Nat} {Input : Type}
    (apply : Direction → Relation → Input → List (Output bits))
    (direction : Direction) (relation : Relation) (input : Input) (live : Nat → Bool)
    (capability : DataOnlyAt (destination direction relation) (apply direction relation input)) :
    (if keepEndpoint live (destination direction relation) then apply direction relation input else []) =
      (apply direction relation input).filter (keepOutput live) := by
  exact (uniform_filter live (destination direction relation) _ capability).symm

theorem forward_destination (relation : Relation) : destination .forward relation = relation.conclusion := rfl

theorem reverse_destination (relation : Relation) : destination .reverse relation = relation.premise := rfl

theorem typed_endpoints_always_keep (live : Nat → Bool) :
    keepEndpoint live .zero = true ∧ keepEndpoint live .static = true ∧
    (∀ argument, keepEndpoint live (.argument argument) = true) ∧
    keepEndpoint live .receiver = true ∧ keepEndpoint live .returned = true ∧
    keepEndpoint live .exception = true := by
  exact ⟨rfl, rfl, fun _ => rfl, rfl, rfl, rfl⟩

theorem nondata_effects_always_keep {bits : Nat} (live : Nat → Bool) (id : Nat) :
    keepOutput live (Output.target (bits := bits) id) = true ∧
    keepOutput live (Output.request (bits := bits) id) = true ∧
    keepOutput live (Output.staticEffect (bits := bits) id) = true := ⟨rfl, rfl, rfl⟩

theorem a_target_prevents_data_only_capability {bits : Nat} (endpoint : Endpoint) (id : Nat) :
    ¬ DataOnlyAt endpoint [Output.target (bits := bits) id] := by
  intro capability
  obtain ⟨packet, impossible, _⟩ := capability _ List.mem_cons_self
  cases impossible

theorem a_request_prevents_data_only_capability {bits : Nat} (endpoint : Endpoint) (id : Nat) :
    ¬ DataOnlyAt endpoint [Output.request (bits := bits) id] := by
  intro capability
  obtain ⟨packet, impossible, _⟩ := capability _ List.mem_cons_self
  cases impossible

theorem move_route_filter_over_rows {bits : Nat} {Row : Type} {Input : Type}
    (apply : Row → Input → List (Output bits)) (outputBase : Row → Endpoint)
    (rows : List Row) (input : Input) (live : Nat → Bool)
    (capability : ∀ row ∈ rows, DataOnlyAt (outputBase row) (apply row input)) :
    rows.flatMap (fun row => if keepEndpoint live (outputBase row) then apply row input else []) =
      (rows.flatMap (fun row => apply row input)).filter (keepOutput live) := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    have tailCapability : ∀ other ∈ rest, DataOnlyAt (outputBase other) (apply other input) :=
      fun other member => capability other (List.mem_cons_of_mem row member)
    simp only [List.flatMap_cons, List.filter_append, ih tailCapability]
    rw [uniform_filter live (outputBase row) (apply row input) (capability row List.mem_cons_self)]

def unionMask {Route : Type} (live : Route → Nat → Bool) (routes : List Route) (localId : Nat) : Bool :=
  routes.any (fun route => live route localId)

theorem route_guard_absorbs_producer_union {Route : Type} (live : Route → Nat → Bool)
    (routes : List Route) (route : Route) (member : route ∈ routes) (endpoint : Endpoint) :
    (keepEndpoint (unionMask live routes) endpoint && keepEndpoint (live route) endpoint) =
      keepEndpoint (live route) endpoint := by
  cases endpoint with
  | «local» localId =>
    cases atRoute : live route localId with
    | false => simp [keepEndpoint, atRoute]
    | true =>
      have inUnion : unionMask live routes localId = true := List.any_eq_true.mpr ⟨route, member, atRoute⟩
      simp [keepEndpoint, inUnion, atRoute]
  | _ => rfl

theorem output_guard_absorbs_producer_union {bits : Nat} {Route : Type} (live : Route → Nat → Bool)
    (routes : List Route) (route : Route) (member : route ∈ routes) (output : Output bits) :
    (keepOutput (unionMask live routes) output && keepOutput (live route) output) =
      keepOutput (live route) output := by
  cases output with
  | data packet => exact route_guard_absorbs_producer_union live routes route member packet.endpoint
  | _ => rfl

theorem producer_then_actual_route_is_exact {bits : Nat} {Route : Type} (live : Route → Nat → Bool)
    (routes : List Route) (route : Route) (member : route ∈ routes) (outputs : List (Output bits)) :
    (outputs.filter (keepOutput (unionMask live routes))).filter (keepOutput (live route)) =
      outputs.filter (keepOutput (live route)) := by
  rw [List.filter_filter]
  apply congrArg (fun predicate => outputs.filter predicate)
  funext output
  rw [Bool.and_comm]
  exact output_guard_absorbs_producer_union live routes route member output

inductive Route where | repeat | leave deriving DecidableEq, Repr

def exampleLive : Route → Nat → Bool
  | .repeat, localId => localId == 0
  | .leave, _ => false

def examplePacket : DataPacket 2 := ⟨.local 0, 37, fun bit => bit.val == 1⟩

def exampleRelation : Relation := ⟨.local 0, .local 1⟩

def exampleApply (direction : Direction) (relation : Relation) (_input : Nat) : List (Output 2) :=
  [.data {examplePacket with endpoint := destination direction relation}]

theorem example_apply_has_oriented_capability (direction : Direction) (relation : Relation) (input : Nat) :
    DataOnlyAt (destination direction relation) (exampleApply direction relation input) := by
  intro output member
  have same : output = .data {examplePacket with endpoint := destination direction relation} :=
    List.mem_singleton.mp member
  exact ⟨_, same, rfl⟩

theorem live_feedback_is_preserved :
    ((exampleApply .reverse exampleRelation 9).filter (keepOutput (exampleLive .repeat))).length = 1 := rfl

theorem dead_leaving_route_is_dropped :
    ((exampleApply .reverse exampleRelation 9).filter (keepOutput (exampleLive .leave))).length = 0 := rfl

theorem wrong_reverse_destination_is_unsound :
    ((exampleApply .reverse exampleRelation 9).filter (keepOutput (fun localId => localId == 1))).length = 0 ∧
    (if keepEndpoint (fun localId => localId == 1) exampleRelation.conclusion
     then exampleApply .reverse exampleRelation 9 else []).length = 1 := by decide

/-- A control/request lane cannot be silently removed with a dead DATA lane. -/
theorem blindly_skipping_request_is_unsound :
    ([Output.request (bits := 2) 6].filter (keepOutput (fun _ => false))).length = 1 := rfl

end BoundaryFilter

import Protocol
import Restriction
import Shape
import Blocks
import Decomposition
import Std

/-!
Implementation-reference pipeline for scoped loop output.

The supplied fixed observer is the complete AL/BL C2, native continuation
application plus enclosing-B C5, L C2 and guidance metadata signature.
The shape gate either keeps the exact state, or invokes the constructive
shortest-safe-prefix reference from Restriction. It does not change owner,
context, whole original or actual control port. Actual publication still
requires an independent complete paired row.

These are parametric and scalar EXACT/MAY laws. They do not prove that the
Kotlin full-AP observer, SCC/layout builder or coroutine adapter realizes
these pure functions. The proposal states those correspondence checks.
-/
namespace LoopFragments.Implementation
open LoopFragments.Geometry
set_option autoImplicit false

variable {nodes bases marks fields : Nat} {Observation : Type} [DecidableEq Observation]

abbrev State (nodes bases marks fields : Nat) := Protocol.State nodes bases marks fields

def gate (shape : Guidance.UnaryGuidance bases marks fields)
    (observe : Fact bases marks fields → Observation) (isEmpty : Observation → Bool)
    (raw : State nodes bases marks fields) : Option (State nodes bases marks fields) :=
  if Shape.needsRestriction shape then
    (Restriction.restrict observe isEmpty raw.fact).map fun fact => { raw with fact := fact }
  else some raw

theorem bounded_shape_is_identity (shape : Guidance.UnaryGuidance bases marks fields)
    (bounded : Shape.needsRestriction shape = false)
    (observe : Fact bases marks fields → Observation) (isEmpty : Observation → Bool)
    (raw : State nodes bases marks fields) : gate shape observe isEmpty raw = some raw := by
  simp [gate, bounded]

theorem growing_shape_uses_selected_reference (shape : Guidance.UnaryGuidance bases marks fields)
    (growing : Shape.needsRestriction shape = true)
    (observe : Fact bases marks fields → Observation) (isEmpty : Observation → Bool)
    (raw : State nodes bases marks fields) :
    gate shape observe isEmpty raw =
      (Restriction.restrict observe isEmpty raw.fact).map fun fact => { raw with fact := fact } := by
  simp [gate, growing]

theorem kept_state_has_only_a_value_change (shape : Guidance.UnaryGuidance bases marks fields)
    (observe : Fact bases marks fields → Observation) (isEmpty : Observation → Bool)
    (raw kept : State nodes bases marks fields) (found : gate shape observe isEmpty raw = some kept) :
    kept.unit = raw.unit ∧ kept.context = raw.context ∧
      kept.wholeOriginal = raw.wholeOriginal ∧ kept.port = raw.port := by
  unfold gate at found
  split at found
  · cases selected : Restriction.restrict observe isEmpty raw.fact with
    | none => simp [selected] at found
    | some value =>
        simp only [selected, Option.map_some] at found
        cases Option.some.inj found
        exact ⟨rfl, rfl, rfl, rfl⟩
  · cases Option.some.inj found
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem kept_observation_is_equal (shape : Guidance.UnaryGuidance bases marks fields)
    (observe : Fact bases marks fields → Observation) (isEmpty : Observation → Bool)
    (raw kept : State nodes bases marks fields) (found : gate shape observe isEmpty raw = some kept) :
    observe kept.fact = observe raw.fact := by
  unfold gate at found
  split at found
  · cases selected : Restriction.restrict observe isEmpty raw.fact with
    | none => simp [selected] at found
    | some value =>
        simp only [selected, Option.map_some] at found
        cases Option.some.inj found
        exact Restriction.restricted_observation_equal observe isEmpty raw.fact value selected
  · cases Option.some.inj found
    rfl

theorem nonempty_observation_has_a_kept_state (shape : Guidance.UnaryGuidance bases marks fields)
    (observe : Fact bases marks fields → Observation) (isEmpty : Observation → Bool)
    (raw : State nodes bases marks fields) (nonempty : isEmpty (observe raw.fact) = false) :
    ∃ kept, gate shape observe isEmpty raw = some kept := by
  unfold gate
  split
  · exact ⟨{ raw with fact := Restriction.chosen observe raw.fact }, by
      simp only [Restriction.restrict, nonempty, Bool.false_eq_true, ↓reduceIte, Option.map_some]⟩
  · exact ⟨raw, rfl⟩

theorem normal_kept_state_is_raw (shape : Guidance.UnaryGuidance bases marks fields)
    (observe : Fact bases marks fields → Observation) (isEmpty : Observation → Bool)
    (raw kept : State nodes bases marks fields) (found : gate shape observe isEmpty raw = some kept)
    (normal : kept.fact.layer = .normal) : kept = raw := by
  unfold gate at found
  split at found
  · cases selected : Restriction.restrict observe isEmpty raw.fact with
    | none => simp [selected] at found
    | some value =>
        simp only [selected, Option.map_some] at found
        cases Option.some.inj found
        have same := Restriction.restricted_normal_requires_raw observe isEmpty raw.fact value selected normal
        cases same
        rfl
  · exact (Option.some.inj found).symm

def publishAfterGate (rows : List (Protocol.PairedRow nodes bases marks fields))
    (shape : Guidance.UnaryGuidance bases marks fields)
    (observe : Fact bases marks fields → Observation) (isEmpty : Observation → Bool)
    (raw : State nodes bases marks fields) : Option (State nodes bases marks fields) :=
  (gate shape observe isEmpty raw).bind (Protocol.publish rows)

theorem publication_has_one_complete_original_row
    (rows : List (Protocol.PairedRow nodes bases marks fields))
    (shape : Guidance.UnaryGuidance bases marks fields)
    (observe : Fact bases marks fields → Observation) (isEmpty : Observation → Bool)
    (raw result : State nodes bases marks fields)
    (published : publishAfterGate rows shape observe isEmpty raw = some result) :
    ∃ row ∈ rows, row.wholeOriginal = raw.wholeOriginal ∧ row.port = raw.port ∧
      row.accepts result.fact = true := by
  unfold publishAfterGate at published
  cases selected : gate shape observe isEmpty raw with
  | none => simp [selected] at published
  | some kept =>
      simp only [selected, Option.bind_some] at published
      have scope := kept_state_has_only_a_value_change shape observe isEmpty raw kept selected
      obtain ⟨same, row, included, original, port, accepted⟩ :=
        Protocol.publication_requires_complete_row rows kept result published
      exact ⟨row, included, original.trans scope.2.2.1, port.trans scope.2.2.2, by simpa [same] using accepted⟩

theorem no_rows_no_publication (shape : Guidance.UnaryGuidance bases marks fields)
    (observe : Fact bases marks fields → Observation) (isEmpty : Observation → Bool)
    (raw : State nodes bases marks fields) : publishAfterGate [] shape observe isEmpty raw = none := by
  unfold publishAfterGate
  cases gate shape observe isEmpty raw <;> rfl

def idle (body localDelivery localPublication requests staticEffects : Nat) : Bool :=
  decide (body = 0 ∧ localDelivery = 0 ∧ localPublication = 0 ∧ requests = 0 ∧ staticEffects = 0)

theorem idle_requires_all_internal_work_drained (body localDelivery localPublication requests staticEffects : Nat) :
    idle body localDelivery localPublication requests staticEffects = true ↔
      body = 0 ∧ localDelivery = 0 ∧ localPublication = 0 ∧ requests = 0 ∧ staticEffects = 0 := by
  simp only [idle, decide_eq_true_eq]

theorem pending_local_delivery_prevents_idle (body localDelivery localPublication requests staticEffects : Nat)
    (pending : localDelivery ≠ 0) : idle body localDelivery localPublication requests staticEffects = false := by
  simp [idle, pending]

end LoopFragments.Implementation

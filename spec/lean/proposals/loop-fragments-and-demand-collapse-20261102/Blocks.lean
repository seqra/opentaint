import Control
import Shape
import Std

/-!
Method-owned internal block states.

The layout, instruction partition and parent certificate are supplied inputs.
One method owns every block. All blocks address the same original registers.
Internal boundary transport is identity on an opaque whole AP payload; alias
requests keep the original method and instruction. Separate indexed state
updates cannot modify another block or processed point. Routing uses the same
ports in either direction. A loop-output shape gate is used for both repeat
and leave; sequential output bypasses this extra gate. A retained value cannot
change its control destination. Only root rows use the public interface.

This is a local ownership/transport model, not a CFG decomposition algorithm,
AP interpreter, summary-C5 implementation, alias analysis, work scheduler or
driver convergence proof. In particular shared registers do not share stores.
-/
namespace LoopFragments.Blocks
open LoopFragments.Guidance
set_option autoImplicit false

inductive Kind where | sequential | loop deriving DecidableEq, Repr

structure Layout (nodes blocks : Nat) where
  method : Nat
  root : Fin blocks
  kind : Fin blocks → Kind
  instructionBlock : Fin nodes → Fin blocks
  parent : Fin blocks → Option (Fin blocks)
  depth : Fin blocks → Nat
  parentShallower : ∀ child ancestor, parent child = some ancestor → depth ancestor < depth child
  onlyRootHasNoParent : ∀ block, parent block = none ↔ block = root

variable {nodes blocks registers points : Nat} {Value : Type}

def owner (layout : Layout nodes blocks) (_block : Fin blocks) : Nat := layout.method

theorem one_method_owns_every_block (layout : Layout nodes blocks) (left right : Fin blocks) :
    owner layout left = owner layout right := rfl

theorem instruction_has_one_lowest_owner (layout : Layout nodes blocks) (inst : Fin nodes)
    (left right : Fin blocks) (first : layout.instructionBlock inst = left)
    (second : layout.instructionBlock inst = right) : left = right := first.symm.trans second

theorem parent_cannot_be_self (layout : Layout nodes blocks) (block : Fin blocks) :
    layout.parent block ≠ some block := by
  intro equal
  exact Nat.lt_irrefl _ (layout.parentShallower block block equal)

theorem two_blocks_cannot_parent_each_other (layout : Layout nodes blocks)
    (left right : Fin blocks) (first : layout.parent left = some right)
    (second : layout.parent right = some left) : False :=
  Nat.lt_asymm (layout.parentShallower left right first) (layout.parentShallower right left second)

inductive ParentPath (layout : Layout nodes blocks) : Fin blocks → Fin blocks → Prop where
  | one {child ancestor} : layout.parent child = some ancestor → ParentPath layout child ancestor
  | cons {child middle ancestor} : layout.parent child = some middle →
      ParentPath layout middle ancestor → ParentPath layout child ancestor

theorem parent_path_strictly_decreases (layout : Layout nodes blocks)
    {child ancestor : Fin blocks} (path : ParentPath layout child ancestor) :
    layout.depth ancestor < layout.depth child := by
  induction path with
  | one step => exact layout.parentShallower _ _ step
  | cons step _ previous => exact Nat.lt_trans previous (layout.parentShallower _ _ step)

theorem containment_has_no_positive_cycle (layout : Layout nodes blocks) (block : Fin blocks) :
    ¬ ParentPath layout block block := by
  intro path
  exact Nat.lt_irrefl _ (parent_path_strictly_decreases layout path)

/-- A block argument does not introduce another register namespace. -/
def register (_layout : Layout nodes blocks) (_block : Fin blocks) (reg : Fin registers) : Fin registers := reg

theorem every_original_register_is_accessible (layout : Layout nodes blocks)
    (block : Fin blocks) (reg : Fin registers) : register layout block reg = reg := rfl

theorem sibling_register_identity (layout : Layout nodes blocks) (left right : Fin blocks)
    (reg : Fin registers) : register layout left reg = register layout right reg := rfl

def boundaryTransport (_source _target : Fin blocks) (value : Value) : Value := value

theorem boundary_keeps_whole_payload (source target : Fin blocks) (value : Value) :
    boundaryTransport source target value = value := rfl

theorem boundary_composition_is_identity (first middle last : Fin blocks) (value : Value) :
    boundaryTransport middle last (boundaryTransport first middle value) = value := rfl

/-- An alias query is still identified by the original method/instruction. -/
def aliasRequest (layout : Layout nodes blocks) (_block : Fin blocks)
    (inst : Fin nodes) (value : Value) : Nat × Fin nodes × Value := ⟨layout.method, inst, value⟩

theorem block_does_not_change_alias_request (layout : Layout nodes blocks)
    (left right : Fin blocks) (inst : Fin nodes) (value : Value) :
    aliasRequest layout left inst value = aliasRequest layout right inst value := rfl

def updateBlock {State : Type} (states : Fin blocks → State) (block : Fin blocks)
    (change : State → State) : Fin blocks → State :=
  fun location => if location = block then change (states location) else states location

theorem target_block_is_updated {State : Type} (states : Fin blocks → State)
    (block : Fin blocks) (change : State → State) :
    updateBlock states block change block = change (states block) := by simp [updateBlock]

theorem other_block_store_is_unchanged {State : Type} (states : Fin blocks → State)
    (block other : Fin blocks) (different : other ≠ block) (change : State → State) :
    updateBlock states block change other = states other := by simp [updateBlock, different]

def updatePostS (store : Fin blocks → Fin points → Value) (block : Fin blocks)
    (point : Fin points) (value : Value) : Fin blocks → Fin points → Value :=
  updateBlock store block (fun current location => if location = point then value else current location)

theorem result_is_stored_at_processed_point (store : Fin blocks → Fin points → Value)
    (block : Fin blocks) (point : Fin points) (value : Value) :
    updatePostS store block point value block point = value := by simp [updatePostS, updateBlock]

theorem successor_store_is_not_updated (store : Fin blocks → Fin points → Value)
    (block : Fin blocks) (point successor : Fin points) (different : successor ≠ point) (value : Value) :
    updatePostS store block point value block successor = store block successor := by
  simp [updatePostS, updateBlock, different]

theorem another_block_post_store_is_not_updated (store : Fin blocks → Fin points → Value)
    (block other : Fin blocks) (different : other ≠ block) (point location : Fin points) (value : Value) :
    updatePostS store block point value other location = store other location := by
  simp [updatePostS, updateBlock, different]

inductive Exit where | repeat | leave deriving DecidableEq, Repr
inductive Destination where | loop | before | after deriving DecidableEq, Repr

def destination : Direction → Exit → Destination
  | _, .repeat => .loop
  | .forward, .leave => .after
  | .backward, .leave => .before

theorem forward_repeat_returns_to_loop : destination .forward .repeat = .loop := rfl
theorem backward_repeat_returns_to_loop : destination .backward .repeat = .loop := rfl
theorem forward_leave_reaches_after : destination .forward .leave = .after := rfl
theorem backward_leave_reaches_before : destination .backward .leave = .before := rfl

structure Delivery (blocks ports : Nat) (Payload : Type) where
  block : Fin blocks
  actualPort : Fin ports
  route : Destination
  value : Payload
  deriving DecidableEq

def routeOutput {bases marks fields ports : Nat} (kind : Kind) (direction : Direction)
    (exit : Exit) (block : Fin blocks) (actualPort : Fin ports)
    (shape : UnaryGuidance bases marks fields) (restrict : Value → Option Value)
    (value : Value) : Option (Delivery blocks ports Value) :=
  let kept := match kind with
    | .sequential => some value
    | .loop => Shape.applyGate shape (fun input => input.bind restrict) (some value)
  kept.map fun result => ⟨block, actualPort, destination direction exit, result⟩

theorem sequential_output_bypasses_extra_gate {bases marks fields ports : Nat}
    (direction : Direction) (exit : Exit) (block : Fin blocks) (actualPort : Fin ports)
    (shape : UnaryGuidance bases marks fields) (restrict : Value → Option Value) (value : Value) :
    routeOutput .sequential direction exit block actualPort shape restrict value =
      some ⟨block, actualPort, destination direction exit, value⟩ := rfl

theorem retained_output_keeps_port_and_destination {bases marks fields ports : Nat}
    (kind : Kind) (direction : Direction) (exit : Exit) (block : Fin blocks) (actualPort : Fin ports)
    (shape : UnaryGuidance bases marks fields) (restrict : Value → Option Value) (value : Value)
    (result : Delivery blocks ports Value)
    (retained : routeOutput kind direction exit block actualPort shape restrict value = some result) :
    result.block = block ∧ result.actualPort = actualPort ∧ result.route = destination direction exit := by
  unfold routeOutput at retained
  split at retained
  · cases Option.some.inj retained
    exact ⟨rfl, rfl, rfl⟩
  · cases kept : Shape.applyGate shape (fun input => input.bind restrict) (some value) with
    | none => simp [kept] at retained
    | some raw =>
        simp only [kept, Option.map_some] at retained
        cases Option.some.inj retained
        exact ⟨rfl, rfl, rfl⟩

theorem growing_loop_result_uses_gate_on_both_routes {bases marks fields ports : Nat}
    (direction : Direction) (exit : Exit) (block : Fin blocks) (actualPort : Fin ports)
    (shape : UnaryGuidance bases marks fields) (growth : Shape.needsRestriction shape = true)
    (restrict : Value → Option Value) (value : Value) :
    routeOutput .loop direction exit block actualPort shape restrict value =
      (restrict value).map (fun result => ⟨block, actualPort, destination direction exit, result⟩) := by
  simp [routeOutput, Shape.applyGate, growth]

theorem nonincreasing_loop_result_is_unchanged {bases marks fields ports : Nat}
    (direction : Direction) (exit : Exit) (block : Fin blocks) (actualPort : Fin ports)
    (shape : UnaryGuidance bases marks fields) (bounded : Shape.needsRestriction shape = false)
    (restrict : Value → Option Value) (value : Value) :
    routeOutput .loop direction exit block actualPort shape restrict value =
      some ⟨block, actualPort, destination direction exit, value⟩ := by
  simp [routeOutput, Shape.applyGate, bounded]

/-- Existing local continuation data; it is not another AP mark or field. -/
structure LocalLink (blocks : Nat) where
  parentBlock : Fin blocks
  childBlock : Fin blocks
  parentOriginal : Nat
  childInitial : Nat

def attachChildResult (link : LocalLink blocks) (value : Value) : Nat × Value :=
  (link.parentOriginal, value)

theorem child_result_keeps_parent_dependency (link : LocalLink blocks) (value : Value) :
    (attachChildResult link value).1 = link.parentOriginal := rfl

theorem attaching_child_result_does_not_relabel_value (link : LocalLink blocks) (value : Value) :
    (attachChildResult link value).2 = value := rfl

theorem child_and_parent_delivery_have_one_method_owner (layout : Layout nodes blocks)
    (link : LocalLink blocks) : owner layout link.childBlock = owner layout link.parentBlock := rfl

structure ScopedRow (blocks ports : Nat) (Payload : Type) where
  block : Fin blocks
  entry : Fin ports
  exit : Fin ports
  localOriginal : Nat
  value : Payload

def publicRow {ports : Nat} (layout : Layout nodes blocks) (row : ScopedRow blocks ports Value) :
    Option (ScopedRow blocks ports Value) := if row.block = layout.root then some row else none

theorem only_root_rows_are_public {ports : Nat} (layout : Layout nodes blocks)
    (row result : ScopedRow blocks ports Value) (published : publicRow layout row = some result) :
    result = row ∧ row.block = layout.root := by
  unfold publicRow at published
  split at published
  next isRoot => exact ⟨(Option.some.inj published).symm, isRoot⟩
  next => cases published

def methodFrontier (directory : List (Fin blocks)) (selected : Fin blocks → List Value) :
    List (Fin blocks × Value) :=
  directory.flatMap fun block => (selected block).map fun value => (block, value)

theorem every_selected_internal_row_is_in_method_frontier
    (directory : List (Fin blocks)) (selected : Fin blocks → List Value)
    (block : Fin blocks) (present : block ∈ directory) (value : Value) (admitted : value ∈ selected block) :
    (block, value) ∈ methodFrontier directory selected := by
  apply List.mem_flatMap.mpr
  exact ⟨block, present, List.mem_map.mpr ⟨value, admitted, rfl⟩⟩

theorem empty_method_frontier_has_no_selected_internal_row
    (directory : List (Fin blocks)) (selected : Fin blocks → List Value)
    (empty : methodFrontier directory selected = []) (block : Fin blocks) (present : block ∈ directory)
    (value : Value) : value ∉ selected block := by
  intro admitted
  have included := every_selected_internal_row_is_in_method_frontier directory selected block present value admitted
  rw [empty] at included
  cases included

end LoopFragments.Blocks

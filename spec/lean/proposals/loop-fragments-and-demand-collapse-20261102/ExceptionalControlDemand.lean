import Discovery
import Geometry

/-!
The selected exceptional-ZERO control-demand lookup. This is not a CFG rewrite.

An invocation contains an executable path in the existing directed graph.
Only backward ZERO at the exceptional exit can borrow normal-exit rows.
Rows are retained as complete values, including their paired requirement.
DATA/native AP matching and the concrete Kotlin dispatcher are outside this
small model. No path, start, source permission or NORMAL witness is invented.
-/
namespace LoopFragments.ExceptionalControlDemand
set_option autoImplicit false

inductive Direction where
  | forward | backward
  deriving DecidableEq, Repr

inductive Packet where
  | zero
  | data (tag : Nat)
  deriving DecidableEq, Repr

inductive Requirement where
  | zero | target | data (tag : Nat)
  deriving DecidableEq, Repr

structure DemandRow where
  entry : Requirement
  exit : Requirement
  annotations : Nat
  deriving DecidableEq, Repr

inductive Source where
  | ordinary | normal
  deriving DecidableEq, Repr

variable {nodes : Nat}

def oriented (graph : Discovery.Overlay nodes) (direction : Direction) : Discovery.Edges nodes :=
  match direction with
  | .forward => Discovery.forward graph
  | .backward => Discovery.backward graph

structure Invocation (graph : Discovery.Overlay nodes) where
  direction : Direction
  packet : Packet
  start : Fin nodes
  location : Fin nodes
  reached : Discovery.Path (oriented graph direction) start location

def borrowNormal {graph : Discovery.Overlay nodes} (invocation : Invocation graph) : Bool :=
  decide (invocation.direction = .backward ∧ invocation.packet = .zero ∧ invocation.location = graph.exceptional)

def selected {graph : Discovery.Overlay nodes} (invocation : Invocation graph)
    (ordinary normal : List DemandRow) : List (Source × DemandRow) :=
  ordinary.map (fun row => (.ordinary, row)) ++
    if borrowNormal invocation then normal.map (fun row => (.normal, row)) else []

def visibleRows {graph : Discovery.Overlay nodes} (invocation : Invocation graph)
    (ordinary normal : List DemandRow) : List DemandRow :=
  (selected invocation ordinary normal).map Prod.snd

def admitsZero (row : DemandRow) : Bool :=
  decide (row.entry = .zero ∨ row.entry = .target)

def acceptedRows {graph : Discovery.Overlay nodes} (invocation : Invocation graph)
    (ordinary normal : List DemandRow) (acceptExit : Requirement → Bool) : List DemandRow :=
  (visibleRows invocation ordinary normal).filter (fun row => admitsZero row && acceptExit row.exit)

theorem borrow_has_exact_scope {graph : Discovery.Overlay nodes} (invocation : Invocation graph) :
    borrowNormal invocation = true ↔
      invocation.direction = .backward ∧ invocation.packet = .zero ∧ invocation.location = graph.exceptional := by
  simp [borrowNormal]

theorem forward_lookup_is_ordinary {graph : Discovery.Overlay nodes} (invocation : Invocation graph)
    (ordinary normal : List DemandRow) (forward : invocation.direction = .forward) :
    selected invocation ordinary normal = ordinary.map (fun row => (.ordinary, row)) := by
  simp [selected, borrowNormal, forward]

theorem nonzero_lookup_is_ordinary {graph : Discovery.Overlay nodes} (invocation : Invocation graph)
    (ordinary normal : List DemandRow) (nonzero : invocation.packet ≠ .zero) :
    selected invocation ordinary normal = ordinary.map (fun row => (.ordinary, row)) := by
  simp [selected, borrowNormal, nonzero]

theorem other_boundary_lookup_is_ordinary {graph : Discovery.Overlay nodes} (invocation : Invocation graph)
    (ordinary normal : List DemandRow) (other : invocation.location ≠ graph.exceptional) :
    selected invocation ordinary normal = ordinary.map (fun row => (.ordinary, row)) := by
  simp [selected, borrowNormal, other]

theorem normal_boundary_lookup_is_ordinary {graph : Discovery.Overlay nodes} (invocation : Invocation graph)
    (ordinary normal : List DemandRow) (normalAt : invocation.location = graph.normal) :
    selected invocation ordinary normal = ordinary.map (fun row => (.ordinary, row)) := by
  apply other_boundary_lookup_is_ordinary invocation ordinary normal
  rw [normalAt]
  exact graph.distinctExits

theorem complete_rows_are_unmodified {graph : Discovery.Overlay nodes} (invocation : Invocation graph)
    (ordinary normal : List DemandRow) :
    visibleRows invocation ordinary normal =
      ordinary ++ if borrowNormal invocation then normal else [] := by
  cases allowed : borrowNormal invocation <;> simp [visibleRows, selected, allowed, Function.comp_def]

theorem backward_exceptional_zero_borrows_complete_normal_rows
    {graph : Discovery.Overlay nodes} (invocation : Invocation graph)
    (ordinary normal : List DemandRow)
    (backward : invocation.direction = .backward) (zero : invocation.packet = .zero)
    (exceptional : invocation.location = graph.exceptional) :
    visibleRows invocation ordinary normal = ordinary ++ normal := by
  simp [complete_rows_are_unmodified, borrowNormal, backward, zero, exceptional]

theorem publication_keeps_one_complete_pair {graph : Discovery.Overlay nodes} (invocation : Invocation graph)
    (ordinary normal : List DemandRow) (acceptExit : Requirement → Bool) (row : DemandRow) :
    row ∈ acceptedRows invocation ordinary normal acceptExit ↔
      row ∈ visibleRows invocation ordinary normal ∧ admitsZero row = true ∧ acceptExit row.exit = true := by
  simp [acceptedRows, Bool.and_eq_true]

theorem data_entry_is_not_a_zero_permission (tag : Nat) (exit : Requirement) (annotations : Nat) :
    admitsZero ⟨.data tag, exit, annotations⟩ = false := by
  simp [admitsZero]

theorem incompatible_paired_exit_is_rejected {graph : Discovery.Overlay nodes} (invocation : Invocation graph)
    (ordinary normal : List DemandRow) (acceptExit : Requirement → Bool) (row : DemandRow)
    (reject : acceptExit row.exit = false) :
    row ∉ acceptedRows invocation ordinary normal acceptExit := by
  simp [publication_keeps_one_complete_pair, reject]

def reachedWitness {graph : Discovery.Overlay nodes} (invocation : Invocation graph) :
    Discovery.Path (oriented graph invocation.direction) invocation.start invocation.location :=
  invocation.reached

def continueAlongExistingPath {graph : Discovery.Overlay nodes} (invocation : Invocation graph)
    {target : Fin nodes} (continuation : Discovery.Path (oriented graph invocation.direction) invocation.location target) :
    Discovery.Path (oriented graph invocation.direction) invocation.start target :=
  Discovery.append invocation.reached continuation

theorem forward_graph_is_still_raw (graph : Discovery.Overlay nodes) :
    oriented graph .forward = graph.raw := rfl

structure TerminalRow (nodes : Nat) where
  original : Nat
  id : Nat
  normalWitness : Bool
  physicalSink : Fin nodes
  conclusionBoundary : Fin nodes

/-- This is terminal publication, not an added normal-return CFG edge. -/
def emitTarget {graph : Discovery.Overlay nodes} (invocation : Invocation graph)
    (original id : Nat) (normalWitness : Bool) : TerminalRow nodes :=
  ⟨original, id, normalWitness, invocation.location, graph.normal⟩

theorem target_uses_normal_conclusion_without_waiting_for_return
    {graph : Discovery.Overlay nodes} (invocation : Invocation graph)
    (original id : Nat) (normalWitness : Bool) :
    (emitTarget invocation original id normalWitness).conclusionBoundary = graph.normal := rfl

theorem target_keeps_its_reached_physical_sink
    {graph : Discovery.Overlay nodes} (invocation : Invocation graph)
    (original id : Nat) (normalWitness : Bool) :
    (emitTarget invocation original id normalWitness).physicalSink = invocation.location := rfl

theorem target_lookup_does_not_create_normal_evidence
    {graph : Discovery.Overlay nodes} (invocation : Invocation graph) (original id : Nat) :
    (emitTarget invocation original id false).normalWitness = false := rfl

def noLeaveSink : Invocation Discovery.noLeave where
  direction := .forward
  packet := .data 0
  start := 0
  location := 1
  reached := .cons (by decide) (.refl 1)

def noLeaveExceptionalZero : Invocation Discovery.noLeave where
  direction := .backward
  packet := .zero
  start := 3
  location := 3
  reached := .refl 3

def noLeaveTarget : TerminalRow 4 := emitTarget noLeaveSink 0 7 false

theorem no_leave_target_keeps_the_normal_endpoint : noLeaveTarget.conclusionBoundary = 2 := rfl

theorem no_leave_exception_borrows_without_a_forward_return : borrowNormal noLeaveExceptionalZero = true := by decide

theorem no_leave_normal_has_no_incoming_edge (node : Fin 4) : Discovery.noLeave.raw node 2 = false := by
  simp [Discovery.noLeave]

theorem noLeaveNormalPathStart {source target : Fin 4}
    (path : Discovery.Path Discovery.noLeave.raw source target) (normal : target = 2) : source = 2 := by
  induction path with
  | refl _ => exact normal
  | cons present _ ih =>
      have atNormal := ih normal
      rw [atNormal, no_leave_normal_has_no_incoming_edge] at present
      cases present

theorem no_leave_sink_has_no_normal_return (path : Discovery.Path Discovery.noLeave.raw 1 2) : False :=
  (by decide : (1 : Fin 4) ≠ 2) (noLeaveNormalPathStart path rfl)

def noLeaveExistingDiscovery : Discovery.Path (Discovery.backward Discovery.noLeave) 3 1 :=
  continueAlongExistingPath noLeaveExceptionalZero (Discovery.discoverDead Discovery.noLeave 1 (by decide))

/-! Only outgoing ZERO -> DemandTarget handoff metadata can use the borrowed
normal invocation. Live subscriptions and DATA/native physical ports do not.
The witness records an actual admitted complete normal control row. -/

structure BorrowWitness {graph : Discovery.Overlay nodes} (invocation : Invocation graph)
    (normalRows : List DemandRow) where
  borrowed : borrowNormal invocation = true
  row : DemandRow
  present : row ∈ normalRows
  zeroAdmitted : admitsZero row = true

inductive ControlPort where
  | normalInvocation
  | physical (id : Nat)
  deriving DecidableEq, Repr

structure ControlScope where
  block : Nat
  entry : ControlPort
  deriving DecidableEq, Repr

inductive Original where
  | zero | data (id : Nat)
  deriving DecidableEq, Repr

inductive TerminalKind where
  | demand | normal (id : Nat)
  deriving DecidableEq, Repr

structure TargetHandoff where
  scope : ControlScope
  original : Original
  target : TerminalKind
  pairedPayload : DemandRow
  annotations : Nat
  deriving DecidableEq, Repr

def targetHandoffMetadata {graph : Discovery.Overlay nodes} {invocation : Invocation graph}
    {normalRows : List DemandRow} (witness : Option (BorrowWitness invocation normalRows))
    (row : TargetHandoff) : TargetHandoff :=
  match witness with
  | none => row
  | some _ => if row.original = .zero ∧ row.target = .demand then
      { row with scope := { row.scope with entry := .normalInvocation } }
    else row

inductive HandoffPacket where
  | data (payload : Nat)
  | native (payload : Nat)
  | terminal (row : TargetHandoff)
  deriving DecidableEq, Repr

def handoffMetadata {graph : Discovery.Overlay nodes} {invocation : Invocation graph}
    {normalRows : List DemandRow} (witness : Option (BorrowWitness invocation normalRows)) :
    HandoffPacket → HandoffPacket
  | .data payload => .data payload
  | .native payload => .native payload
  | .terminal row => .terminal (targetHandoffMetadata witness row)

theorem unborrowed_handoff_is_unchanged {graph : Discovery.Overlay nodes} {invocation : Invocation graph}
    {normalRows : List DemandRow} (row : TargetHandoff) :
    targetHandoffMetadata (invocation := invocation) (normalRows := normalRows) none row = row := rfl

theorem data_handoff_is_unchanged {graph : Discovery.Overlay nodes} {invocation : Invocation graph}
    {normalRows : List DemandRow} (witness : Option (BorrowWitness invocation normalRows)) (payload : Nat) :
    handoffMetadata witness (.data payload) = .data payload := rfl

theorem native_handoff_is_unchanged {graph : Discovery.Overlay nodes} {invocation : Invocation graph}
    {normalRows : List DemandRow} (witness : Option (BorrowWitness invocation normalRows)) (payload : Nat) :
    handoffMetadata witness (.native payload) = .native payload := rfl

theorem normal_target_handoff_is_unchanged {graph : Discovery.Overlay nodes} {invocation : Invocation graph}
    {normalRows : List DemandRow} (witness : Option (BorrowWitness invocation normalRows))
    (row : TargetHandoff) (id : Nat) (normal : row.target = .normal id) :
    targetHandoffMetadata witness row = row := by
  cases witness <;> simp [targetHandoffMetadata, normal]

theorem nonzero_target_handoff_is_unchanged {graph : Discovery.Overlay nodes} {invocation : Invocation graph}
    {normalRows : List DemandRow} (witness : Option (BorrowWitness invocation normalRows))
    (row : TargetHandoff) (nonzero : row.original ≠ .zero) :
    targetHandoffMetadata witness row = row := by
  cases witness <;> simp [targetHandoffMetadata, nonzero]

theorem handoff_change_requires_actual_borrow {graph : Discovery.Overlay nodes} {invocation : Invocation graph}
    {normalRows : List DemandRow} (witness : Option (BorrowWitness invocation normalRows))
    (row : TargetHandoff) (changed : targetHandoffMetadata witness row ≠ row) :
    borrowNormal invocation = true := by
  cases witness with
  | none => exact False.elim (changed rfl)
  | some evidence => exact evidence.borrowed

theorem zero_demand_handoff_uses_normal_invocation
    {graph : Discovery.Overlay nodes} {invocation : Invocation graph} {normalRows : List DemandRow}
    (witness : BorrowWitness invocation normalRows) (row : TargetHandoff)
    (zero : row.original = .zero) (demand : row.target = .demand) :
    (targetHandoffMetadata (some witness) row).scope.entry = .normalInvocation := by
  simp [targetHandoffMetadata, zero, demand]

theorem handoff_keeps_complete_payload_and_identity
    {graph : Discovery.Overlay nodes} {invocation : Invocation graph} {normalRows : List DemandRow}
    (witness : Option (BorrowWitness invocation normalRows)) (row : TargetHandoff) :
    let kept := targetHandoffMetadata witness row
    kept.pairedPayload = row.pairedPayload ∧ kept.original = row.original ∧
      kept.target = row.target ∧ kept.annotations = row.annotations ∧ kept.scope.block = row.scope.block := by
  cases witness with
  | none => simp [targetHandoffMetadata]
  | some _ => simp only [targetHandoffMetadata]; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! A finite continuation witness. Geometry.project is the existing scalar
global cut. Four ordinary field reads follow one source derivation. This
does not model all source permissions, C2/C5 or whole-driver convergence. -/

def sourceFFFF : Geometry.Fact 1 1 1 := ⟨0, 0, [0, 0, 0, 0], .exact, .normal, false⟩

def cutSource (limit : Nat) : Geometry.Fact 1 1 1 :=
  Geometry.project limit [sourceFFFF.path] sourceFFFF

def readField (fact : Geometry.Fact 1 1 1) : Option (Geometry.Fact 1 1 1) :=
  match fact.path with
  | [] => if fact.tail = .may then some fact else none
  | _ :: rest => some { fact with path := rest }

def readFields (count : Nat) (fact : Geometry.Fact 1 1 1) : Option (Geometry.Fact 1 1 1) :=
  match count with
  | 0 => some fact
  | rest + 1 => (readField fact).bind (readFields rest)

inductive ForwardOutcome where
  | stopped | demand | normal
  deriving DecidableEq, Repr

def forwardPortPresent (scope : ControlScope) : Bool :=
  match scope.entry with
  | .normalInvocation => true
  | .physical id => id == 0 || id == 1

def forwardObservation (scope : ControlScope) (limit : Nat) : ForwardOutcome :=
  if forwardPortPresent scope then
    match readFields 4 (cutSource limit) with
    | none => .stopped
    | some fact => if fact.path ≠ [] then .stopped
        else if fact.tail = .exact ∧ fact.layer = .normal then .normal else .demand
  else .stopped

def normalControlRows : List DemandRow := [⟨.target, .zero, 7⟩]

def normalBorrowWitness : BorrowWitness noLeaveExceptionalZero normalControlRows where
  borrowed := by decide
  row := ⟨.target, .zero, 7⟩
  present := by decide
  zeroAdmitted := by decide

def discoveryTargetHandoff : TargetHandoff :=
  ⟨⟨2, .physical 99⟩, .zero, .demand, ⟨.target, .zero, 7⟩, 11⟩

def continuedTargetHandoff : TargetHandoff := targetHandoffMetadata (some normalBorrowWitness) discoveryTargetHandoff

theorem source_ffff_needs_four_fields : sourceFFFF.path.length = 4 := rfl

theorem no_leave_first_forward_is_demand :
    forwardObservation ⟨2, .normalInvocation⟩ 1 = .demand := by decide

theorem discovery_port_is_absent_in_forward : forwardPortPresent discoveryTargetHandoff.scope = false := by decide

theorem unremapped_discovery_metadata_stops_run3 :
    forwardObservation discoveryTargetHandoff.scope 2 = .stopped := by decide

theorem borrowed_handoff_keeps_run3_demand :
    forwardObservation continuedTargetHandoff.scope 2 = .demand := by decide

theorem continued_run5_can_resolve_source_ffff :
    forwardObservation continuedTargetHandoff.scope 4 = .normal := by decide

def finiteContinuationResult (remap : Bool) : ForwardOutcome :=
  let scope := if remap then continuedTargetHandoff.scope else discoveryTargetHandoff.scope
  if forwardObservation scope 2 = .demand then forwardObservation scope 4 else .stopped

theorem finite_continuation_without_remap_misses_later_precision : finiteContinuationResult false = .stopped := by decide

theorem finite_continuation_with_remap_reaches_run5 : finiteContinuationResult true = .normal := by decide

end LoopFragments.ExceptionalControlDemand

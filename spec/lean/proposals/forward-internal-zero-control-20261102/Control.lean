import Std

/-!
UNSELECTED conditional design model. It does not authorize a runtime change.
An actual admitted root and a Type-valued path are required. AP demand,
source permissions, records and Target rules are immutable opaque inputs.
Finite endpoint matching below models only the ZERO Target probe hazard.
It is not a full AP matcher or Kotlin proof.
-/
namespace ForwardInternalZeroControl
set_option autoImplicit false

inductive Direction where
  | forward | backward
  deriving DecidableEq, Repr
inductive Layer where
  | normal | demand
  deriving DecidableEq, Repr
structure Mode where
  direction : Direction
  restricted : Bool
  internalBoundary : Bool
  deriving DecidableEq, Repr

def enabled (mode : Mode) : Bool :=
  mode.direction == .forward && mode.restricted && mode.internalBoundary

def forwardInternal : Mode := ⟨.forward, true, true⟩
def backwardInternal : Mode := ⟨.backward, true, true⟩
def publicBoundary : Mode := ⟨.forward, true, false⟩
def run1 : Mode := ⟨.forward, false, true⟩

structure Origin where
  method : Nat
  context : Nat
  original : Nat
  deriving DecidableEq, Repr
structure Scope where
  method : Nat
  context : Nat
  block : Nat
  entryPort : Nat
  deriving DecidableEq, Repr
structure Edge where
  source : Nat
  destination : Nat
  exitPort : Nat
  entryPort : Nat
  deriving DecidableEq, Repr

/-- The witness contains only supplied edges in the existing graph. -/
inductive Path (graph : List Edge) : Nat → Nat → Type where
  | stay (vertex : Nat) : Path graph vertex vertex
  | next {start middle : Nat} (initialPath : Path graph start middle)
      (edge : Edge) (present : edge ∈ graph) (startsHere : edge.source = middle) :
      Path graph start edge.destination

namespace Path

def append {graph : List Edge} {a b c : Nat}
    (first : Path graph a b) (last : Path graph b c) : Path graph a c :=
  match last with
  | .stay _ => first
  | .next before edge present same => .next (append first before) edge present same

theorem invariant {graph : List Edge} {a b : Nat} (path : Path graph a b)
    (property : Nat → Prop) (initial : property a)
    (closed : (edge : Edge) → edge ∈ graph → property edge.source → property edge.destination) :
    property b := by
  induction path with
  | stay => exact initial
  | next initialPath edge present same ih =>
      exact closed edge present (same.symm ▸ ih)
end Path

/-- A token cannot be constructed from local demand. It needs the existing
root-policy admission proof. This is a model witness, not a new AP label. -/
structure RootZero (rootPolicy : Origin → Bool) where
  origin : Origin
  layer : Layer
  start : Nat
  admitted : rootPolicy origin = true

structure Reached (graph : List Edge) (rootPolicy : Origin → Bool) where
  root : RootZero rootPolicy
  scope : Scope
  ownerMethod : scope.method = root.origin.method
  ownerContext : scope.context = root.origin.context
  vertex : Nat
  path : Path graph root.start vertex
  layer : Layer
  offeredOriginalZero : Bool
  noUpgrade : root.layer = .demand → layer = .demand

structure Token where
  scope : Scope
  original : Origin
  vertex : Nat
  layer : Layer
  deriving DecidableEq, Repr

def token {graph : List Edge} {policy : Origin → Bool} (actual : Reached graph policy) : Token :=
  ⟨actual.scope, actual.root.origin, actual.vertex, actual.layer⟩

def admitControl {graph : List Edge} {policy : Origin → Bool}
    (mode : Mode) (actual : Reached graph policy) (ordinaryZeroAlready : Bool := false) : Option Token :=
  if enabled mode && actual.offeredOriginalZero && !ordinaryZeroAlready then some (token actual) else none

theorem control_admission_has_the_existing_root_permission
    {graph : List Edge} {policy : Origin → Bool} (actual : Reached graph policy) :
    policy (token actual).original = true := actual.root.admitted

theorem admission_keeps_scope_original_vertex_and_layer
    {graph : List Edge} {policy : Origin → Bool} (actual : Reached graph policy)
    (zero : actual.offeredOriginalZero = true) :
    admitControl forwardInternal actual = some
      ⟨actual.scope, actual.root.origin, actual.vertex, actual.layer⟩ := by
  simp [admitControl, enabled, forwardInternal, zero, token]

theorem nonzero_origin_Reach_gets_no_inherited_admission
    {graph : List Edge} {policy : Origin → Bool} (actual : Reached graph policy)
    (nonzero : actual.offeredOriginalZero = false) :
    admitControl forwardInternal actual = none := by
  simp [admitControl, nonzero]

theorem an_existing_ordinary_ZERO_C2_result_needs_no_new_admission
    {graph : List Edge} {policy : Origin → Bool} (actual : Reached graph policy) :
    admitControl forwardInternal actual true = none := by simp [admitControl]

theorem a_demand_root_never_becomes_normal_control
    {graph : List Edge} {policy : Origin → Bool} (actual : Reached graph policy)
    (demand : actual.root.layer = .demand) : (token actual).layer = .demand :=
  actual.noUpgrade demand

theorem backward_has_no_new_control_admission
    {graph : List Edge} {policy : Origin → Bool} (actual : Reached graph policy) :
    admitControl backwardInternal actual = none := rfl

theorem public_method_admission_has_no_new_control_permission
    {graph : List Edge} {policy : Origin → Bool} (actual : Reached graph policy) :
    admitControl publicBoundary actual = none := rfl

theorem run1_keeps_its_previous_policy
    {graph : List Edge} {policy : Origin → Bool} (actual : Reached graph policy) :
    admitControl run1 actual = none := rfl

theorem no_reached_control_can_exist_without_root_admission
    {graph : List Edge} (actual : Reached graph (fun _ => false)) : False := by
  have impossible := actual.root.admitted
  contradiction

/-- A real traversed output, including its actual edge and whole root. -/
structure Completion (graph : List Edge) (policy : Origin → Bool) where
  input : Reached graph policy
  last : Nat
  body : Path graph input.vertex last
  route : Edge
  present : route ∈ graph
  actualOutlet : route.source = last
  layer : Layer
  rawOriginalZero : Bool
  noUpgrade : input.layer = .demand → layer = .demand

structure ControlOutput where
  scope : Scope
  original : Origin
  exitPort : Nat
  nextEntryPort : Nat
  target : Nat
  layer : Layer
  deriving DecidableEq, Repr

def output {graph : List Edge} {policy : Origin → Bool}
    (actual : Completion graph policy) : ControlOutput :=
  ⟨actual.input.scope, actual.input.root.origin, actual.route.exitPort,
    actual.route.entryPort, actual.route.destination, actual.layer⟩

def publishControl {graph : List Edge} {policy : Origin → Bool}
    (mode : Mode) (actual : Completion graph policy) (ordinaryC5Accepted : Bool := false) : Option ControlOutput :=
  if enabled mode && actual.input.offeredOriginalZero && actual.rawOriginalZero && !ordinaryC5Accepted then some (output actual) else none

def advance {graph : List Edge} {policy : Origin → Bool}
    (actual : Completion graph policy) (nextBlock : Nat) : Reached graph policy :=
  { root := actual.input.root
    scope := { actual.input.scope with block := nextBlock, entryPort := actual.route.entryPort }
    ownerMethod := actual.input.ownerMethod
    ownerContext := actual.input.ownerContext
    vertex := actual.route.destination
    path := .next (actual.input.path.append actual.body) actual.route actual.present actual.actualOutlet
    layer := actual.layer
    offeredOriginalZero := actual.rawOriginalZero
    noUpgrade := fun demand => actual.noUpgrade (actual.input.noUpgrade demand) }

theorem internal_output_keeps_both_actual_ports_and_full_origin
    {graph : List Edge} {policy : Origin → Bool} (actual : Completion graph policy)
    (inputZero : actual.input.offeredOriginalZero = true) (outputZero : actual.rawOriginalZero = true) :
    publishControl forwardInternal actual = some
      ⟨actual.input.scope, actual.input.root.origin, actual.route.exitPort,
       actual.route.entryPort, actual.route.destination, actual.layer⟩ := by
  simp [publishControl, enabled, forwardInternal, inputZero, outputZero, output]

theorem output_is_an_existing_graph_edge
    {graph : List Edge} {policy : Origin → Bool} (actual : Completion graph policy) :
    actual.route ∈ graph := actual.present

theorem continuation_keeps_root_and_actual_target
    {graph : List Edge} {policy : Origin → Bool} (actual : Completion graph policy)
    (nextBlock : Nat) :
    (advance actual nextBlock).root.origin = actual.input.root.origin ∧
    (advance actual nextBlock).scope.entryPort = actual.route.entryPort ∧
    (advance actual nextBlock).vertex = actual.route.destination ∧
    (advance actual nextBlock).layer = actual.layer := ⟨rfl, rfl, rfl, rfl⟩

def continuation_still_has_a_constructive_root_path
    {graph : List Edge} {policy : Origin → Bool} (actual : Completion graph policy)
    (nextBlock : Nat) :
    Path graph actual.input.root.start (advance actual nextBlock).vertex :=
  (advance actual nextBlock).path

theorem backward_has_no_new_control_output
    {graph : List Edge} {policy : Origin → Bool} (actual : Completion graph policy) :
    publishControl backwardInternal actual = none := rfl

theorem an_ordinary_C5_accepted_output_gets_no_fallback_control
    {graph : List Edge} {policy : Origin → Bool} (actual : Completion graph policy) :
    publishControl forwardInternal actual true = none := by simp [publishControl]

theorem a_nonzero_raw_original_gets_no_control_fallback
    {graph : List Edge} {policy : Origin → Bool} (actual : Completion graph policy)
    (nonzero : actual.rawOriginalZero = false) :
    publishControl forwardInternal actual = none := by simp [publishControl, nonzero]

theorem inherited_control_output_cannot_upgrade_DEMAND
    {graph : List Edge} {policy : Origin → Bool} (actual : Completion graph policy)
    (demand : actual.input.layer = .demand) : (output actual).layer = .demand :=
  actual.noUpgrade demand

/-- Existing standing inputs retain the complete parent original. This finite
link adapter assumes the supplied parent-exit mapping was already validated. -/
structure Link where
  child : Scope
  parent : Scope
  original : Origin
  childExitPort : Nat
  parentExitPort : Nat
  actualZero : Bool
  originalZero : Bool
  layer : Layer
  deriving DecidableEq, Repr
structure ParentControl where
  scope : Scope
  original : Origin
  exitPort : Nat
  layer : Layer
  deriving DecidableEq, Repr

def joinLayer (left right : Layer) : Layer :=
  if left = .demand ∨ right = .demand then .demand else .normal

def applyControl (cell : ControlOutput) (link : Link) : Option ParentControl :=
  if cell.scope = link.child ∧ cell.original = link.original ∧
      cell.exitPort = link.childExitPort ∧
      cell.scope.method = link.parent.method ∧ cell.scope.context = link.parent.context ∧
      link.actualZero = true ∧ link.originalZero = true then
    some ⟨link.parent, link.original, link.parentExitPort, joinLayer cell.layer link.layer⟩
  else none

theorem current_control_binding_keeps_the_complete_waiting_original
    (cell : ControlOutput) (link : Link) (result : ParentControl)
    (found : applyControl cell link = some result) :
    result.scope = link.parent ∧ result.original = link.original ∧
    result.exitPort = link.parentExitPort ∧ result.layer = joinLayer cell.layer link.layer := by
  unfold applyControl at found
  split at found
  · cases Option.some.inj found; exact ⟨rfl, rfl, rfl, rfl⟩
  · contradiction

theorem a_DATA_input_cannot_consume_a_control_identity
    (cell : ControlOutput) (link : Link) (dataInput : link.actualZero = false) :
    applyControl cell link = none := by simp [applyControl, dataInput]

theorem a_nonzero_parent_original_cannot_consume_a_control_identity
    (cell : ControlOutput) (link : Link) (nonzero : link.originalZero = false) :
    applyControl cell link = none := by simp [applyControl, nonzero]

theorem an_unrelated_scope_cannot_consume_a_control_identity
    (cell : ControlOutput) (link : Link) (different : cell.scope ≠ link.child) :
    applyControl cell link = none := by simp [applyControl, different]

theorem an_unrelated_exit_cannot_consume_a_control_identity
    (cell : ControlOutput) (link : Link) (different : cell.exitPort ≠ link.childExitPort) :
    applyControl cell link = none := by simp [applyControl, different]

theorem a_DEMAND_waiting_input_remains_DEMAND (layer : Layer) :
    joinLayer layer .demand = .demand := by simp [joinLayer]

theorem a_DEMAND_identity_remains_DEMAND (layer : Layer) :
    joinLayer .demand layer = .demand := by simp [joinLayer]

/-- One-cell/one-standing-link executable rendezvous. The queue is an observation
of actual delivery, not a proposed extra request or raw-input history. -/
structure ReplayState where
  cell : Option ControlOutput
  link : Option Link
  queued : List ParentControl
  reserved : Bool
  deriving DecidableEq, Repr

def emptyReplay : ReplayState := ⟨none, none, [], false⟩

def replay (before : ReplayState) : ReplayState :=
  match before.cell, before.link with
  | some cell, some link => match applyControl cell link with
    | none => before
    | some result =>
        let queued := if before.queued.contains result then before.queued else before.queued ++ [result]
        { before with queued, reserved := before.reserved || !queued.isEmpty }
  | _, _ => before

def publish (before : ReplayState) (cell : ControlOutput) : ReplayState :=
  replay { before with cell := some cell }

def offer (before : ReplayState) (link : Link) : ReplayState :=
  replay { before with link := some link }

theorem late_link_and_early_link_have_the_same_delivery
    (cell : ControlOutput) (link : Link) :
    (offer (publish emptyReplay cell) link).queued =
      (publish (offer emptyReplay link) cell).queued := by
  simp [offer, publish, replay, emptyReplay]

theorem a_cached_identity_replays_without_a_new_initial
    (cell : ControlOutput) (link : Link) (result : ParentControl)
    (matched : applyControl cell link = some result) :
    (offer (publish emptyReplay cell) link).queued = [result] := by
  simp [offer, publish, replay, emptyReplay, matched]

theorem a_fresh_late_control_delivery_reserves_owner_work
    (cell : ControlOutput) (link : Link) (result : ParentControl)
    (matched : applyControl cell link = some result) :
    (offer (publish emptyReplay cell) link).reserved = true := by
  simp [offer, publish, replay, emptyReplay, matched]

theorem repeating_the_same_identity_does_not_duplicate_the_delivery
    (cell : ControlOutput) (link : Link) (result : ParentControl)
    (matched : applyControl cell link = some result) :
    (publish (offer (publish emptyReplay cell) link) cell).queued = [result] := by
  simp [offer, publish, replay, emptyReplay, matched]

/-- Existing semantic views remain opaque immutable values. Control storage is
separate; a control completion is not a Pair or a DATA/native/public record. -/
inductive Endpoint where
  | zero | data (id : Nat) | target
  deriving DecidableEq, Repr
structure Pair where
  entry : Endpoint
  exit : Endpoint
  deriving DecidableEq, Repr
structure Views where
  demand : List Pair
  sources : List Nat
  nativeRecords : List Nat
  publicRecords : List Nat
  deriving DecidableEq, Repr
structure State where
  views : Views
  controls : List ControlOutput
  deriving DecidableEq, Repr

def rememberControl (before : State) (control : ControlOutput) : State :=
  { before with controls := before.controls ++ [control] }

theorem remembering_control_keeps_all_semantic_views (before : State) (control : ControlOutput) :
    (rememberControl before control).views = before.views := rfl

theorem every_old_DATA_lookup_is_equal {Input Result : Type}
    (lookup : Views → Input → Result) (before : State) (control : ControlOutput) (input : Input) :
    lookup (rememberControl before control).views input = lookup before.views input := rfl

theorem every_old_paired_C5_lookup_is_equal {Input Result : Type}
    (lookup : List Pair → Input → Result) (before : State) (control : ControlOutput) (input : Input) :
    lookup (rememberControl before control).views.demand input = lookup before.views.demand input := rfl

def sourceAllowed (views : Views) (action : Nat) : Bool := views.sources.contains action

theorem source_permission_and_action_key_are_unchanged
    (before : State) (control : ControlOutput) (action : Nat) :
    sourceAllowed (rememberControl before control).views action = sourceAllowed before.views action := rfl

theorem a_missing_source_permission_stays_missing
    (before : State) (control : ControlOutput) (action : Nat)
    (missing : sourceAllowed before.views action = false) :
    sourceAllowed (rememberControl before control).views action = false := missing

/-- Finite endpoint cell for the real acceptsTarget hazard: Target publication
probes C5 with a ZERO/Reach DEMAND exit. Full AP matching is outside this cell. -/
def endpointC5 (rows : List Pair) (entry exit : Endpoint) : Bool :=
  rows.any (fun row => row.entry == entry && row.exit == exit)

def acceptsTarget (views : Views) (entry : Endpoint) : Bool :=
  endpointC5 views.demand entry .zero

theorem actual_control_does_not_change_Target_permission
    (before : State) (control : ControlOutput) (entry : Endpoint) :
    acceptsTarget (rememberControl before control).views entry = acceptsTarget before.views entry := rfl

theorem no_AP_rows_still_reject_Target_after_control (control : ControlOutput) :
    acceptsTarget (rememberControl ⟨⟨[], [], [], []⟩, []⟩ control).views .zero = false := rfl

def virtualZeroDemand : Pair := ⟨.zero, .zero⟩

theorem rejected_virtual_Zero_Zero_demand_grants_Target_permission :
    acceptsTarget ⟨[virtualZeroDemand], [], [], []⟩ .zero = true := by decide

theorem control_only_storage_creates_no_native_or_public_record
    (before : State) (control : ControlOutput) :
    (rememberControl before control).views.nativeRecords = before.views.nativeRecords ∧
    (rememberControl before control).views.publicRecords = before.views.publicRecords := ⟨rfl, rfl⟩

/-- Ordinary NORMAL derivations remain eligible for the unchanged paired C5.
The no-new-record law concerns the control-cache operation only. -/
def inferOrdinaryNative (before : State) (entry exit : Endpoint) (id : Nat) (layer : Layer) : Option State :=
  if layer == .normal && endpointC5 before.views.demand entry exit then
    some { before with views := { before.views with nativeRecords := before.views.nativeRecords ++ [id] } }
  else none

theorem control_transport_does_not_grant_ordinary_native_permission
    (before : State) (control : ControlOutput) (entry exit : Endpoint) (id : Nat) (layer : Layer) :
    (inferOrdinaryNative (rememberControl before control) entry exit id layer).isSome =
      (inferOrdinaryNative before entry exit id layer).isSome := by
  cases permitted : (layer == .normal && endpointC5 before.views.demand entry exit) <;>
    simp [inferOrdinaryNative, rememberControl, permitted]

theorem a_DEMAND_derivation_is_not_a_NORMAL_native_record
    (before : State) (entry exit : Endpoint) (id : Nat) :
    inferOrdinaryNative before entry exit id .demand = none := rfl

theorem legitimate_ordinary_native_derivation_can_grow_the_store_after_control
    (control : ControlOutput) :
    ((inferOrdinaryNative (rememberControl ⟨⟨[⟨.zero, .data 7⟩], [], [], []⟩, []⟩ control)
        .zero (.data 7) 9 .normal).map (fun state => state.views.nativeRecords)) = some [9] := by
  simp [inferOrdinaryNative, rememberControl, endpointC5]

/-- The complete witness is supplied by existing rule execution. Extra control
is not another member, a replacement DATA literal or an independent ND arm. -/
structure Member where
  literal : Nat
  origin : Endpoint
  layer : Layer
  deriving DecidableEq, Repr

def complete (required : List Nat) (members : List Member) : Bool :=
  required.all (fun id => members.any (fun member => member.literal == id))

def normalTarget (required : List Nat) (members : List Member) : Bool :=
  complete required members && members.all (fun member => member.layer == .normal)

def zeroPremiseArm (required : List Nat) (members : List Member) : Bool :=
  complete required members && members.all (fun member => member.origin == .zero)

def normZero : Member := ⟨0, .zero, .normal⟩
def normData : Member := ⟨1, .data 7, .normal⟩

theorem a_missing_ND_literal_still_rejects_NormalTarget :
    normalTarget [0, 1] [normZero] = false := by decide

theorem a_complete_NORMAL_witness_can_still_create_NormalTarget :
    normalTarget [0, 1] [normZero, normData] = true := by decide

theorem DEMAND_control_cannot_upgrade_a_NormalTarget :
    normalTarget [0, 1] [{ normZero with layer := .demand }, normData] = false := by decide

theorem a_mixed_ZERO_DATA_cube_does_not_gain_a_ZERO_arm :
    zeroPremiseArm [0, 1] [normZero, normData] = false := by decide

theorem only_a_complete_all_ZERO_cube_gets_the_ZERO_arm :
    zeroPremiseArm [0, 1] [normZero, { normData with origin := .zero }] = true ∧
    zeroPremiseArm [0, 1] [normZero] = false := by decide

def finiteOrigin : Origin := ⟨1, 2, 0⟩
def finiteScope : Scope := ⟨1, 2, 7, 99⟩
def finiteGraph : List Edge := [⟨0, 1, 10, 11⟩, ⟨1, 2, 20, 30⟩]
def finiteRoot : RootZero (fun _ => true) :=
  ⟨finiteOrigin, .normal, 0, rfl⟩
def finiteInput : Reached finiteGraph (fun _ => true) :=
  { root := finiteRoot, scope := finiteScope, ownerMethod := rfl, ownerContext := rfl,
    vertex := 0, path := .stay 0, layer := .normal, offeredOriginalZero := true,
    noUpgrade := by intro impossible; cases impossible }
def finiteDemandInput : Reached finiteGraph (fun _ => true) :=
  { finiteInput with layer := .demand, noUpgrade := fun _ => rfl }

theorem a_NORMAL_root_flag_does_not_upgrade_an_actual_DEMAND_input :
    finiteDemandInput.root.layer = .normal ∧
    ((admitControl forwardInternal finiteDemandInput).map Token.layer) = some .demand := by decide

def finiteCompletion : Completion finiteGraph (fun _ => true) :=
  { input := finiteInput, last := 1,
    body := .next (.stay 0) ⟨0, 1, 10, 11⟩ (by decide) rfl,
    route := ⟨1, 2, 20, 30⟩, present := by decide, actualOutlet := rfl,
    layer := .normal, rawOriginalZero := true,
    noUpgrade := by intro impossible; cases impossible }

theorem actual_root_input_can_pass_C2_but_fail_the_ordinary_identity_C5 :
    (admitControl forwardInternal finiteInput).isSome = true ∧
    endpointC5 [] .zero .zero = false := by decide

theorem the_actual_C2_only_pipeline_still_drops_the_identity :
    ((admitControl forwardInternal finiteInput).isSome && endpointC5 [] .zero .zero) = false := by decide

theorem actual_control_output_reaches_the_next_real_block_without_Target_permission :
    (publishControl forwardInternal finiteCompletion).isSome = true ∧
    (advance finiteCompletion 8).vertex = 2 ∧
    (advance finiteCompletion 8).scope.entryPort = 30 ∧
    acceptsTarget ⟨[], [], [], []⟩ .zero = false := by decide

theorem having_a_root_ZERO_does_not_admit_a_nonzero_original_Reach :
    admitControl forwardInternal { finiteInput with offeredOriginalZero := false } = none := by decide

/-- No arbitrary return from a loop: every supplied path preserves an edge-closed
set. This graph contains only 0->1 and 1->1, so a control at2 cannot be constructed. -/
def noLeaveGraph : List Edge := [⟨0, 1, 10, 11⟩, ⟨1, 1, 12, 11⟩]

theorem a_no_leave_control_cannot_invent_a_return (path : Path noLeaveGraph 0 2) : False := by
  have bounded := path.invariant (fun node => node = 0 ∨ node = 1) (Or.inl rfl) (by
    intro edge present _
    have allEdges : noLeaveGraph.all (fun edge => decide (edge.destination = 1)) = true := by decide
    have destination := (List.all_eq_true.mp allEdges) edge present
    exact Or.inr (of_decide_eq_true destination))
  rcases bounded with impossible | impossible <;> contradiction

/-- A finite three-state cache. It represents ordinary layer improvement and
must not be used to bound the number of downstream source or DATA operations. -/
inductive Seen where
  | absent | demand | normal
  deriving DecidableEq, Repr

def admitLayer (seen : Seen) (offered : Layer) : Seen :=
  match offered with
  | .normal => .normal
  | .demand => match seen with
    | .absent => .demand
    | other => other

def rank : Seen → Nat
  | .absent => 0
  | .demand => 1
  | .normal => 2

def fresh (seen : Seen) (offered : Layer) : Nat :=
  if admitLayer seen offered = seen then 0 else 1

def offers (seen : Seen) : List Layer → Seen × Nat
  | [] => (seen, 0)
  | layer :: rest =>
      let after := offers (admitLayer seen layer) rest
      (after.1, after.2 + fresh seen layer)

theorem one_admission_consumes_finite_layer_budget (seen : Seen) (layer : Layer) :
    rank seen + fresh seen layer ≤ rank (admitLayer seen layer) := by
  cases seen <;> cases layer <;> decide

theorem layer_rank_is_at_most_two (seen : Seen) : rank seen ≤ 2 := by cases seen <;> decide

theorem all_admissions_fit_the_layer_budget (seen : Seen) (layers : List Layer) :
    rank seen + (offers seen layers).2 ≤ rank (offers seen layers).1 := by
  induction layers generalizing seen with
  | nil => simp [offers]
  | cons layer rest ih =>
      have next := ih (admitLayer seen layer)
      have one := one_admission_consumes_finite_layer_budget seen layer
      simp only [offers] at *
      omega

theorem at_most_two_fresh_control_admissions_per_scope (seen : Seen) (layers : List Layer) :
    (offers seen layers).2 ≤ 2 := by
  have budget := all_admissions_fit_the_layer_budget seen layers
  have bound := layer_rank_is_at_most_two (offers seen layers).1
  omega

def scopeAdmissions (events : List (List Layer)) : Nat :=
  (events.map (fun layers => (offers .absent layers).2)).sum

theorem finite_scopes_have_a_two_per_scope_admission_bound (events : List (List Layer)) :
    scopeAdmissions events ≤ 2 * events.length := by
  induction events with
  | nil => simp [scopeAdmissions]
  | cons events rest ih =>
      have bound := at_most_two_fresh_control_admissions_per_scope .absent events
      simp only [scopeAdmissions, List.map_cons, List.sum_cons, List.length_cons] at *
      omega

structure WorkFamily where
  controlOffers : List Layer
  sourceActions : List Nat
  deriving Repr

def arbitraryRuleWork (count : Nat) : WorkFamily := ⟨[.normal], List.range count⟩

theorem bounded_control_admission_does_not_bound_all_rule_work (count : Nat) :
    (offers .absent (arbitraryRuleWork count).controlOffers).2 = 1 ∧
    (arbitraryRuleWork count).sourceActions.length = count := by
  simp [arbitraryRuleWork, offers, fresh, admitLayer, List.length_range]

end ForwardInternalZeroControl

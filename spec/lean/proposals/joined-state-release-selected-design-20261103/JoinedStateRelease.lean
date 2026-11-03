import Std

namespace PostJoinRelease

/- J is the whole immutable retained read footprint. X is the selected execution
   root bundle, S the completed diagnostic/contributor snapshot, O the bound result.
   No object graph, collector, mutable store or concurrency adapter is modeled. -/
inductive Phase where
  | running | joined | snapshotted | bindingReady | bound | failed
  deriving DecidableEq, Repr

inductive LiveEvent where
  | work | publication | delivery
  deriving DecidableEq, Repr

structure State (J X S O E : Type) where
  phase : Phase
  retained : J
  execution : Option X
  snapshots : Option S
  output : Option O
  published : Option O
  failure : Option E

structure RawId where
  value : Nat
  deriving DecidableEq, Repr

structure Owner where
  value : Nat
  deriving DecidableEq, Repr

structure Port where
  value : Nat
  deriving DecidableEq, Repr

structure Mark where
  value : Nat
  deriving DecidableEq, Repr

structure Identities where
  rawIds : List RawId
  owners : List Owner
  ports : List Port
  marks : List Mark
  deriving DecidableEq, Repr

def fresh (j : J) (x : X) : State J X S O E :=
  { phase := .running, retained := j, execution := some x,
    snapshots := none, output := none, published := none, failure := none }

def admitLive (phase : Phase) (_event : LiveEvent) : Bool :=
  match phase with
  | .running => true
  | _ => false

def joinSuccess (s : State J X S O E) : State J X S O E :=
  if s.phase = .running then { s with phase := .joined } else s

def joinFailure (s : State J X S O E) (error : E) : State J X S O E :=
  { s with phase := .failed, output := none, published := none, failure := some error }

def capture (snapshot : J → Option X → S) (s : State J X S O E) : State J X S O E :=
  if s.phase = .joined then
    { s with phase := .snapshotted, snapshots := some (snapshot s.retained s.execution) }
  else s

def releaseExecution (s : State J X S O E) : State J X S O E :=
  if s.phase = .snapshotted then { s with phase := .bindingReady, execution := none } else s

/- This signature is the read-footprint prerequisite: the pure binder receives J
   and cannot inspect X. No Kotlin binder is claimed to implement this signature. -/
def bind (binder : J → Except E O) (s : State J X S O E) : State J X S O E :=
  if s.phase = .snapshotted ∨ s.phase = .bindingReady then
    match binder s.retained with
    | .ok out => { s with phase := .bound, output := some out, published := none, failure := none }
    | .error error => { s with phase := .failed, output := none, published := none, failure := some error }
  else s

def commit (s : State J X S O E) : State J X S O E :=
  if s.phase = .bound then { s with published := s.output } else s

def finalRelease (s : State J X S O E) : State J X S O E :=
  if s.phase = .bound ∨ s.phase = .failed then { s with execution := none } else s

def oldPath (binder : J → Except E O) (s : State J X S O E) : State J X S O E :=
  finalRelease (commit (bind binder s))

def proposedPath (binder : J → Except E O) (s : State J X S O E) : State J X S O E :=
  finalRelease (commit (bind binder (releaseExecution s)))

theorem no_live_after_join (event : LiveEvent) : admitLive .joined event = false := rfl

theorem no_live_after_snapshots (event : LiveEvent) : admitLive .snapshotted event = false := rfl

theorem no_live_after_release (event : LiveEvent) : admitLive .bindingReady event = false := rfl

theorem no_live_after_binding (event : LiveEvent) : admitLive .bound event = false := rfl

theorem no_live_after_failure (event : LiveEvent) : admitLive .failed event = false := rfl

theorem no_work_publication_or_delivery_after_join :
    admitLive .joined .work = false ∧ admitLive .joined .publication = false ∧
      admitLive .joined .delivery = false := by decide

theorem fresh_not_published (j : J) (x : X) :
    (fresh j x : State J X S O E).published = none := rfl

theorem failed_join_not_published (s : State J X S O E) (error : E) :
    (joinFailure s error).published = none := rfl

theorem failed_join_has_no_bound_output (s : State J X S O E) (error : E) :
    (joinFailure s error).output = none := rfl

theorem failed_join_cannot_early_release (s : State J X S O E) (error : E) :
    releaseExecution (joinFailure s error) = joinFailure s error := rfl

theorem cannot_release_while_running (s : State J X S O E) (h : s.phase = .running) :
    releaseExecution s = s := by simp [releaseExecution, h]

theorem cannot_release_before_snapshot (s : State J X S O E) (h : s.phase = .joined) :
    releaseExecution s = s := by simp [releaseExecution, h]

theorem release_removes_selected_execution_root (s : State J X S O E)
    (h : s.phase = .snapshotted) : (releaseExecution s).execution = none := by
  simp [releaseExecution, h]

theorem release_preserves_retained_footprint (s : State J X S O E) :
    (releaseExecution s).retained = s.retained := by
  unfold releaseExecution
  split <;> rfl

theorem release_preserves_completed_snapshots (s : State J X S O E) :
    (releaseExecution s).snapshots = s.snapshots := by
  unfold releaseExecution
  split <;> rfl

theorem every_retained_read_unchanged (read : J → A) (s : State J X S O E) :
    read (releaseExecution s).retained = read s.retained := by
  rw [release_preserves_retained_footprint]

theorem all_raw_ids_owners_ports_marks_unchanged (read : J → Identities) (s : State J X S O E) :
    read (releaseExecution s).retained = read s.retained :=
  every_retained_read_unchanged read s

theorem release_makes_no_early_publication (s : State J X S O E) :
    (releaseExecution s).published = s.published := by
  unfold releaseExecution
  split <;> rfl

theorem capture_precedes_release (snapshot : J → Option X → S) (s : State J X S O E)
    (h : s.phase = .joined) :
    (releaseExecution (capture snapshot s)).snapshots = some (snapshot s.retained s.execution) := by
  simp [capture, releaseExecution, h]

theorem captured_state_is_ready_to_drop (snapshot : J → Option X → S) (s : State J X S O E)
    (h : s.phase = .joined) : (releaseExecution (capture snapshot s)).phase = .bindingReady := by
  simp [capture, releaseExecution, h]

theorem release_is_idempotent (s : State J X S O E) :
    releaseExecution (releaseExecution s) = releaseExecution s := by
  unfold releaseExecution
  split <;> simp_all

theorem final_release_idempotent (s : State J X S O E) :
    finalRelease (finalRelease s) = finalRelease s := by
  unfold finalRelease
  split <;> simp_all

theorem final_release_cannot_skip_snapshots (s : State J X S O E) (h : s.phase = .joined) :
    finalRelease s = s := by simp [finalRelease, h]

theorem final_release_retains_binding_inputs (s : State J X S O E) :
    (finalRelease s).retained = s.retained := by
  unfold finalRelease
  split <;> rfl

theorem final_release_does_not_publish (s : State J X S O E) :
    (finalRelease s).published = s.published := by
  unfold finalRelease
  split <;> rfl

theorem release_then_binding_same_final_state (binder : J → Except E O)
    (s : State J X S O E) (h : s.phase = .snapshotted) :
    proposedPath binder s = oldPath binder s := by
  cases result : binder s.retained <;>
    simp [proposedPath, oldPath, releaseExecution, bind, commit, finalRelease, h, result]

theorem release_then_binding_same_output (binder : J → Except E O)
    (s : State J X S O E) (h : s.phase = .snapshotted) :
    (proposedPath binder s).output = (oldPath binder s).output := by
  rw [release_then_binding_same_final_state binder s h]

theorem release_then_binding_same_publication (binder : J → Except E O)
    (s : State J X S O E) (h : s.phase = .snapshotted) :
    (proposedPath binder s).published = (oldPath binder s).published := by
  rw [release_then_binding_same_final_state binder s h]

theorem failed_binding_never_publishes (binder : J → Except E O)
    (s : State J X S O E) (error : E) (h : s.phase = .snapshotted)
    (failed : binder s.retained = .error error) :
    (proposedPath binder s).published = none := by
  simp [proposedPath, releaseExecution, bind, commit, finalRelease, h, failed]

theorem failed_binding_has_no_output (binder : J → Except E O)
    (s : State J X S O E) (error : E) (h : s.phase = .snapshotted)
    (failed : binder s.retained = .error error) :
    (proposedPath binder s).output = none := by
  simp [proposedPath, releaseExecution, bind, commit, finalRelease, h, failed]

theorem successful_binding_publishes_same_value (binder : J → Except E O)
    (s : State J X S O E) (out : O) (h : s.phase = .snapshotted)
    (ok : binder s.retained = .ok out) :
    (proposedPath binder s).published = some out := by
  simp [proposedPath, releaseExecution, bind, commit, finalRelease, h, ok]

theorem early_commit_joined_is_noop (s : State J X S O E) (h : s.phase = .joined) :
    commit s = s := by simp [commit, h]

theorem early_commit_released_is_noop (s : State J X S O E) (h : s.phase = .bindingReady) :
    commit s = s := by simp [commit, h]

/- A retained alias can keep execution data reachable. Dropping one root is not
   a collector reachability or freed-byte theorem. -/
def aliasWitness : State Nat Nat Unit Nat Unit :=
  { phase := .snapshotted, retained := 9, execution := some 9, snapshots := some (),
    output := none, published := none, failure := none }

theorem retained_alias_survives_root_release :
    (releaseExecution aliasWitness).execution = none ∧
      (releaseExecution aliasWitness).retained = 9 := by decide

def executionDependent (x : Option Nat) : Nat := x.getD 0

theorem execution_read_breaks_equivalence_witness :
    executionDependent (some 9) ≠ executionDependent none := by decide

end PostJoinRelease

namespace JoinedStateRelease

/- Selected design, not a verification of Kotlin. Values below are finite,
   ordered certificates. Field/AP matching is supplied by the existing adapter;
   this model neither weakens that matching nor adds an analysis permission. -/
structure Scope where
  method : Nat
  block : Nat
  entry : Nat
  deriving DecidableEq, Repr

inductive Layer where
  | normal | demand
  deriving DecidableEq, Repr

structure Payload where
  premise : List Nat
  concreteFields : List Nat
  marks : List Nat
  exclusions : List Nat
  protectedMarks : List Nat
  layer : Layer
  deriving DecidableEq, Repr

structure LocalInput where
  child : Scope
  parent : Scope
  point : Nat
  value : Payload
  deriving DecidableEq, Repr

structure CallerInput where
  callee : Nat
  caller : Scope
  call : Nat
  stage : Nat
  value : Payload
  deriving DecidableEq, Repr

structure StaticRow where
  owner : Scope
  exit : Nat
  rawId : Nat
  value : Payload
  deriving DecidableEq, Repr

structure TargetRow where
  owner : Scope
  exit : Nat
  normalId : Option Nat
  value : Payload
  deriving DecidableEq, Repr

structure Exports where
  admitted : List StaticRow
  rawTargets : List TargetRow
  outgoingDemandTargets : List TargetRow
  sourceHits : List Nat
  sinkSeeds : List Nat
  normalContributors : List Payload
  diagnostics : List Nat
  nonZeroInitial : Bool
  deriving DecidableEq, Repr

structure Retained where
  localInputs : List LocalInput
  callerInputs : List CallerInput
  rawWrites : List StaticRow
  privateSeeds : List StaticRow
  exports : Exports
  deriving DecidableEq, Repr

/- Publication indexes and ND/current-delivery joins belong to execution.
   The actual inputs and raw/admitted/Target inventories do not. -/
structure Execution where
  statementCells : List Nat
  initials : List Nat
  resumes : List Nat
  publicationIndex : List Nat
  currentDeliveryJoins : List Nat
  cfgCache : List Nat
  diagnosticsWorking : List Nat
  deriving DecidableEq, Repr

structure Pending where
  countedEvents : Nat
  ownerWork : Nat
  localDeliveries : Nat
  callbacks : Nat
  deriving DecidableEq, Repr

def idle (p : Pending) : Bool :=
  p.countedEvents == 0 && p.ownerWork == 0 && p.localDeliveries == 0 && p.callbacks == 0

inductive Phase where
  | live | joined | captured | released | bound | committed | failed | disposed
  deriving DecidableEq, Repr

structure Session where
  phase : Phase
  stopped : Bool
  pending : Pending
  retained : Retained
  execution : Option Execution
  captured : Option Exports
  lease : Bool
  candidate : Option (List StaticRow)
  previousAccepted : List Nat
  accepted : List Nat
  deriving DecidableEq, Repr

def mayLive (s : Session) : Bool := s.phase == .live && !s.stopped

def join (s : Session) : Session :=
  if s.phase == .live && s.stopped && idle s.pending then { s with phase := .joined }
  else s

def capture (s : Session) : Session :=
  if s.phase == .joined then
    { s with phase := .captured, captured := some s.retained.exports, lease := true }
  else s

def releaseExecution (s : Session) : Session :=
  if s.phase == .captured && s.lease then
    { s with phase := .released, execution := none }
  else s

def localAt (r : Retained) (scope : Scope) : List LocalInput :=
  r.localInputs.filter fun input => input.child == scope

def callersAt (r : Retained) (callee : Nat) : List CallerInput :=
  r.callerInputs.filter fun input => input.callee == callee

/- The exact existing AP eligibility predicate is a parameter. Owner checks
   precede it. No input is rebound or promoted by sealing. -/
def bindLocal (fits : StaticRow → LocalInput → Bool) (r : Retained) :
    List (StaticRow × LocalInput) :=
  r.rawWrites.flatMap fun row =>
    (localAt r row.owner).filterMap fun input =>
      if fits row input then some (row, input) else none

def bindCaller (fits : StaticRow → CallerInput → Bool) (r : Retained) :
    List (StaticRow × CallerInput) :=
  r.rawWrites.flatMap fun row =>
    (callersAt r row.owner.method).filterMap fun input =>
      if fits row input then some (row, input) else none

def bind (binder : Retained → Except Nat (List StaticRow)) (s : Session) : Session :=
  if s.phase == .released && s.lease then
    match binder s.retained with
    | .ok rows => { s with phase := .bound, candidate := some rows }
    | .error _ => { s with phase := .failed, candidate := none }
  else s

/- Driver validation includes all existing record/report/handoff preparation.
   An unsuccessful preparation cannot commit contributors or accepted reports. -/
def commit (valid : Exports → List StaticRow → Bool) (reports : Exports → List Nat)
    (s : Session) : Session :=
  match s.phase, s.captured, s.candidate with
  | .bound, some capturedValue, some rows =>
    if valid capturedValue rows then
      { s with phase := .committed, accepted := reports capturedValue }
    else { s with phase := .failed, candidate := none }
  | _, _, _ => s

def abort (s : Session) : Session :=
  { s with phase := .failed, candidate := none, accepted := s.previousAccepted }

def dispose (s : Session) : Session :=
  if s.phase == .committed || s.phase == .failed then
    { s with phase := .disposed, lease := false, execution := none }
  else s

theorem join_requires_idle (s : Session) (notIdle : idle s.pending = false) :
    join s = s := by simp [join, notIdle]

theorem join_requires_stopped (s : Session) (active : s.stopped = false) :
    join s = s := by simp [join, active]

theorem joined_has_no_live_routing (s : Session) (h : s.phase = .joined) :
    mayLive s = false := by simp [mayLive, h]

theorem captured_has_no_live_routing (s : Session) (h : s.phase = .captured) :
    mayLive s = false := by simp [mayLive, h]

theorem released_has_no_live_routing (s : Session) (h : s.phase = .released) :
    mayLive s = false := by simp [mayLive, h]

theorem release_requires_capture (s : Session) (h : s.phase = .joined) :
    releaseExecution s = s := by simp [releaseExecution, h]

theorem release_requires_lease (s : Session) (h : s.lease = false) :
    releaseExecution s = s := by simp [releaseExecution, h]

theorem release_preserves_retained (s : Session) :
    (releaseExecution s).retained = s.retained := by
  unfold releaseExecution
  split <;> rfl

theorem release_preserves_capture (s : Session) :
    (releaseExecution s).captured = s.captured := by
  unfold releaseExecution
  split <;> rfl

theorem release_preserves_previous_acceptance (s : Session) :
    (releaseExecution s).previousAccepted = s.previousAccepted := by
  unfold releaseExecution
  split <;> rfl

theorem release_preserves_current_acceptance (s : Session) :
    (releaseExecution s).accepted = s.accepted := by
  unfold releaseExecution
  split <;> rfl

theorem release_discards_selected_bundle (s : Session)
    (phase : s.phase = .captured) (lease : s.lease = true) :
    (releaseExecution s).execution = none := by
  simp [releaseExecution, phase, lease]

theorem capture_complete_exports (s : Session) (phase : s.phase = .joined) :
    (capture s).captured = some s.retained.exports := by simp [capture, phase]

theorem capture_does_not_rebind_inputs (s : Session) :
    (capture s).retained = s.retained := by
  unfold capture
  split <;> rfl

theorem capture_does_not_publish_reports (s : Session) :
    (capture s).accepted = s.accepted := by
  unfold capture
  split <;> rfl

theorem exact_local_owner (r : Retained) (scope : Scope) (input : LocalInput)
    (member : input ∈ localAt r scope) : input.child = scope := by
  exact of_decide_eq_true (List.mem_filter.mp member).2

theorem no_cross_scope_local_read (r : Retained) (scope : Scope) (input : LocalInput)
    (different : input.child ≠ scope) : input ∉ localAt r scope := by
  intro member
  exact different (exact_local_owner r scope input member)

theorem exact_callee_owner (r : Retained) (callee : Nat) (input : CallerInput)
    (member : input ∈ callersAt r callee) : input.callee = callee := by
  exact of_decide_eq_true (List.mem_filter.mp member).2

theorem local_query_preserved (s : Session) (scope : Scope) :
    localAt (releaseExecution s).retained scope = localAt s.retained scope := by
  rw [release_preserves_retained]

theorem caller_query_preserved (s : Session) (method : Nat) :
    callersAt (releaseExecution s).retained method = callersAt s.retained method := by
  rw [release_preserves_retained]

theorem concrete_local_binding_sequence_preserved (s : Session)
    (fits : StaticRow → LocalInput → Bool) :
    bindLocal fits (releaseExecution s).retained = bindLocal fits s.retained := by
  rw [release_preserves_retained]

theorem concrete_physical_binding_sequence_preserved (s : Session)
    (fits : StaticRow → CallerInput → Bool) :
    bindCaller fits (releaseExecution s).retained = bindCaller fits s.retained := by
  rw [release_preserves_retained]

theorem all_driver_exports_preserved (s : Session) :
    (releaseExecution s).retained.exports = s.retained.exports := by
  rw [release_preserves_retained]

theorem raw_target_inventory_preserved (s : Session) :
    (releaseExecution s).retained.exports.rawTargets = s.retained.exports.rawTargets := by
  rw [release_preserves_retained]

theorem outgoing_target_inventory_preserved (s : Session) :
    (releaseExecution s).retained.exports.outgoingDemandTargets =
      s.retained.exports.outgoingDemandTargets := by rw [release_preserves_retained]

theorem diagnostics_preserved (s : Session) :
    (releaseExecution s).retained.exports.diagnostics = s.retained.exports.diagnostics := by
  rw [release_preserves_retained]

theorem contributors_preserved (s : Session) :
    (releaseExecution s).retained.exports.normalContributors =
      s.retained.exports.normalContributors := by rw [release_preserves_retained]

theorem all_raw_writes_preserved (s : Session) :
    (releaseExecution s).retained.rawWrites = s.retained.rawWrites := by
  rw [release_preserves_retained]

theorem failed_binding_keeps_old_acceptance (s : Session) (binder : Retained → Except Nat (List StaticRow))
    (phase : s.phase = .released) (lease : s.lease = true)
    (error : binder s.retained = .error code) :
    (bind binder s).accepted = s.accepted ∧ (bind binder s).candidate = none := by
  simp [bind, phase, lease, error]

theorem failed_driver_validation_keeps_old_acceptance (s : Session)
    (valid : Exports → List StaticRow → Bool) (reports : Exports → List Nat)
    (phase : s.phase = .bound) (captured : s.captured = some capturedValue)
    (candidate : s.candidate = some rows) (rejected : valid capturedValue rows = false) :
    (commit valid reports s).accepted = s.accepted := by
  simp [commit, phase, captured, candidate, rejected]

theorem abort_has_no_new_candidate (s : Session) : (abort s).candidate = none := rfl

theorem abort_preserves_prior_reports (s : Session) :
    (abort s).accepted = s.previousAccepted := rfl

theorem dispose_releases_binding_lease (s : Session) (phase : s.phase = .failed) :
    (dispose s).lease = false := by simp [dispose, phase]

theorem dispose_preserves_committed_exports (s : Session) :
    (dispose s).captured = s.captured := by
  unfold dispose
  split <;> rfl

theorem dispose_preserves_reports (s : Session) :
    (dispose s).accepted = s.accepted := by
  unfold dispose
  split <;> rfl

theorem release_idempotent (s : Session) :
    releaseExecution (releaseExecution s) = releaseExecution s := by
  unfold releaseExecution
  split <;> simp_all

theorem dispose_idempotent (s : Session) : dispose (dispose s) = dispose s := by
  unfold dispose
  split <;> simp_all

/- Ownership transfer, not a second standing input table. The element values
   stand for immutable AP/caller keys and retain their exact ordered identity. -/
structure Directory (A : Type) where
  live : Option (List A)
  joined : Option (List A)

def detach (d : Directory A) : Directory A :=
  match d.live, d.joined with
  | some rows, none => { live := none, joined := some rows }
  | _, _ => d

theorem detach_moves_exact_values (rows : List A) :
    detach ({ live := some rows, joined := none } : Directory A) =
      { live := none, joined := some rows } := rfl

theorem detach_does_not_keep_two_standing_directories (rows : List A) :
    (detach ({ live := some rows, joined := none } : Directory A)).live = none := rfl

theorem detach_preserves_order_and_multiplicity (rows : List A) :
    (detach ({ live := some rows, joined := none } : Directory A)).joined = some rows := rfl

theorem detach_idempotent (d : Directory A) : detach (detach d) = detach d := by
  rcases d with ⟨live, joined⟩
  cases live <;> cases joined <;> rfl

def closeJoined (d : Directory A) : Directory A := { d with joined := none }

theorem close_joined_drops_owner_reference (d : Directory A) :
    (closeJoined d).joined = none := rfl

theorem close_joined_does_not_clear_live_alias (d : Directory A) :
    (closeJoined d).live = d.live := rfl

theorem moved_then_closed_has_no_directory_root (rows : List A) :
    closeJoined (detach ({ live := some rows, joined := none } : Directory A)) =
      { live := none, joined := none } := rfl

theorem close_joined_idempotent (d : Directory A) : closeJoined (closeJoined d) = closeJoined d := rfl

theorem failed_join_cannot_capture (s : Session) : capture (abort s) = abort s := rfl

theorem failed_join_cannot_bind (s : Session) (binder : Retained → Except Nat (List StaticRow)) :
    bind binder (abort s) = abort s := rfl

theorem failure_cleanup_does_not_restore_execution (s : Session) :
    (dispose (abort s)).execution = none := by simp [dispose, abort]

theorem no_new_report_from_failure_cleanup (s : Session) :
    (dispose (abort s)).accepted = s.previousAccepted := by simp [dispose, abort]

/- Executable finite object-graph witnesses: removing one root is insufficient
   if a borrowed reader closes over the actor. These do not model a JVM GC. -/
def edges (badAlias : Bool) (node : Nat) : List Nat :=
  if node == 1 then (if badAlias then [2] else [4])
  else if node == 2 then [3]
  else []

def reachable : Nat → (Nat → List Nat) → List Nat → List Nat
  | 0, _, roots => roots
  | fuel + 1, next, roots => roots ++ reachable fuel next (roots.flatMap next)

theorem plain_input_reader_does_not_retain_execution :
    3 ∉ reachable 3 (edges false) [1] := by decide

theorem actor_callback_alias_keeps_execution :
    3 ∈ reachable 3 (edges true) [1] := by decide

theorem removing_input_reader_would_lose_input :
    4 ∈ reachable 3 (edges false) [1] ∧ 4 ∉ reachable 3 (edges false) [] := by decide

end JoinedStateRelease

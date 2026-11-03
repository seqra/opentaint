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

/-- State includes the ordered demand and seeds, saved NORMAL records,
    condition contributors, report receipts and every other input read
    by a restricted run. The field limit is an explicit parameter. -/
structure ClosedRunPair (State : Type) (forward backward : Nat → State → State) where
  beforeForward : State
  beforeBackward : State
  minForward : Nat
  minBackward : Nat
  stepForward : ∀ limit, minForward ≤ limit →
    forward limit beforeForward = beforeBackward
  stepBackward : ∀ limit, minBackward ≤ limit →
    backward limit beforeBackward = beforeForward

def advanceRuns {State : Type} (forward backward : Nat → State → State)
    (start : State) : List (Nat × Nat) → State
  | [] => start
  | (f, b) :: rest => advanceRuns forward backward (backward b (forward f start)) rest

/-- Any future field-limit schedule above the two verified minima
    repeats the same state. Projection equality alone does not provide
    the two step witnesses. -/
theorem closedPairRepeats {State : Type} {forward backward : Nat → State → State}
    (pair : ClosedRunPair State forward backward) (limits : List (Nat × Nat))
    (enough : ∀ x ∈ limits, pair.minForward ≤ x.1 ∧ pair.minBackward ≤ x.2) :
    advanceRuns forward backward pair.beforeForward limits = pair.beforeForward := by
  induction limits with
  | nil => rfl
  | cons next rest ih =>
    obtain ⟨df, db⟩ := enough next (by simp)
    rw [advanceRuns, pair.stepForward _ df, pair.stepBackward _ db]
    exact ih (fun x hx => enough x (List.mem_cons_of_mem _ hx))

/-- Forward termination, at any future cutoff or at the current seal,
    presents the same identities when its provisional set is served. -/
theorem closedPairPreservesReport {State Key : Type}
    {forward backward : Nat → State → State}
    (pair : ClosedRunPair State forward backward) (limits : List (Nat × Nat))
    (enough : ∀ x ∈ limits, pair.minForward ≤ x.1 ∧ pair.minBackward ≤ x.2)
    (confirmed reached : State → List Key)
    (served : ∀ k ∈ reached pair.beforeBackward, k ∈ confirmed pair.beforeBackward)
    (lastForward : Nat) (valid : pair.minForward ≤ lastForward) (key : Key) :
    let final := forward lastForward (advanceRuns forward backward pair.beforeForward limits)
    key ∈ confirmed final ++ reached final ↔ key ∈ confirmed pair.beforeBackward := by
  dsimp only
  rw [closedPairRepeats pair limits enough, pair.stepForward _ valid]
  simp only [List.mem_append]
  exact ⟨fun h => h.elim id (served key), Or.inl⟩

/-- Equal projected demand can conceal a newly enabled native action. -/
example :
    let a := (true, false)
    let b := (true, true)
    let run (s : Bool × Bool) := s.2
    a.1 = b.1 ∧ run a ≠ run b := by decide

inductive GlobalLimitRead where
  | depthFits (fields : Nat)
  | pairedCap (requested : Nat)
  deriving DecidableEq

def independentAt (limit : Nat) : GlobalLimitRead → Bool
  | .depthFits fields => fields ≤ limit
  | .pairedCap requested => requested ≤ limit

def evaluateLimitRead (limit : Nat) : GlobalLimitRead → Bool × Nat
  | .depthFits fields => (fields ≤ limit, 0)
  | .pairedCap requested => (true, min requested limit)

/-- A guard or cap known to fit at the witnessed limit yields exactly
    the same answer at each larger limit. An early speculative cut
    cannot supply this premise, even when the projected rows repeat. -/
theorem limitReadStable (lo hi : Nat) (higher : lo ≤ hi)
    (read : GlobalLimitRead) (ok : independentAt lo read = true) :
    evaluateLimitRead hi read = evaluateLimitRead lo read := by
  cases read with
  | depthFits fields =>
    have fits : fields ≤ lo := of_decide_eq_true ok
    simp [evaluateLimitRead, fits, Nat.le_trans fits higher]
  | pairedCap requested =>
    have fits : requested ≤ lo := of_decide_eq_true ok
    simp [evaluateLimitRead, Nat.min_eq_left fits, Nat.min_eq_left (Nat.le_trans fits higher)]

theorem saturatedAuditKeepsFailure {cap failures : Nat}
    (positive : 0 < cap) (observed : 0 < failures) :
    min cap failures ≠ 0 :=
  Nat.ne_of_gt (Nat.lt_min.mpr ⟨positive, observed⟩)

inductive RunAction (Work Sealed : Type) where
  | step (next : Work)
  | limit (read : GlobalLimitRead) (resume : Bool × Nat → Work)
  | complete (sealed : Sealed)
  | external

/-- A deterministic run can emit an exact limit-independence witness
    during its ordinary finite execution. Unknown effects and exhausted
    work give no witness. -/
def auditRun {Work Sealed : Type} (next : Work → RunAction Work Sealed)
    (limit : Nat) : Nat → Work → Option Sealed
  | 0, _ => none
  | fuel + 1, work =>
    match next work with
    | .step later => auditRun next limit fuel later
    | .limit read resume =>
      if independentAt limit read then auditRun next limit fuel (resume (evaluateLimitRead limit read))
      else none
    | .complete sealed => some sealed
    | .external => none

theorem auditRunStable {Work Sealed : Type} (next : Work → RunAction Work Sealed)
    (lo hi : Nat) (higher : lo ≤ hi) (fuel : Nat) (work : Work) (sealed : Sealed)
    (witness : auditRun next lo fuel work = some sealed) :
    auditRun next hi fuel work = some sealed := by
  induction fuel generalizing work with
  | zero => simp [auditRun] at witness
  | succ fuel ih =>
    cases step : next work with
    | step later =>
      simpa [auditRun, step] using ih later (by simpa [auditRun, step] using witness)
    | complete frozen =>
      simpa [auditRun, step] using witness
    | external =>
      simp [auditRun, step] at witness
    | limit read resume =>
      by_cases good : independentAt lo read = true
      · have still : independentAt hi read = true := by
          cases read <;> exact decide_eq_true (Nat.le_trans (of_decide_eq_true good) higher)
        have continuation : auditRun next lo fuel (resume (evaluateLimitRead lo read)) = some sealed := by
          simpa [auditRun, step, good] using witness
        simpa [auditRun, step, still, limitReadStable lo hi higher read good] using
          ih _ continuation
      · simp [auditRun, step, good] at witness

inductive ExampleRun where
  | start
  | report (reached : Bool)

def deepObserver : ExampleRun → RunAction ExampleRun Bool
  | .start => .limit (.depthFits 9) fun (fits, _) => .report fits
  | .report reached => .complete reached

-- A fixed demand and an initially cut path cannot close the pair.
example : auditRun deepObserver 8 2 .start = none := rfl
example : auditRun deepObserver 9 2 .start = some true := rfl

/-- The residual cleaner uses the ordinary non-strict depth check.
    The point-cleaner witness needs one extra field. A trace with a
    rejected cleaner test cannot justify a transition at higher limits. -/
def residualCleanerRead (fields : Nat) : GlobalLimitRead := .depthFits fields
def pointCleanerRead (head : Nat) : GlobalLimitRead := .depthFits (head + 1)

example : independentAt 8 (residualCleanerRead 9) = false := rfl
example : independentAt 8 (pointCleanerRead 8) = false := rfl
example : independentAt 9 (pointCleanerRead 8) = true := rfl

/-- Rejected root starts can appear between active input events. The
    certificate permits their erasure only after checking that their
    admission is independent of the limit and that rejection has no
    semantic effect. Keep the order of all active events. -/
inductive RootEvent (E : Type) where
  | active (event : E)
  | rejected

def activeEvents {E : Type} : List (RootEvent E) → List E
  | [] => []
  | .active event :: rest => event :: activeEvents rest
  | .rejected :: rest => activeEvents rest

def applyEvents {E State : Type} (apply : State → E → State) :
    State → List (RootEvent E) → State
  | s, [] => s
  | s, .active event :: rest => applyEvents apply (apply s event) rest
  | s, .rejected :: rest => applyEvents apply s rest

theorem rejectedRootErasure {E State : Type} (apply : State → E → State)
    (state : State) (events : List (RootEvent E)) :
    applyEvents apply state events = (activeEvents events).foldl apply state := by
  induction events generalizing state with
  | nil => rfl
  | cons event rest ih =>
    cases event <;> simp [applyEvents, activeEvents, ih]

example (apply : Nat → Nat → Nat) (s : Nat) :
    applyEvents apply s [.rejected, .active 9, .rejected] = apply s 9 := rfl

structure QueuePriority where
  rank : Nat
  steps : Nat
  serial : Nat

def QueuePriority.before (a b : QueuePriority) : Prop :=
  a.rank < b.rank ∨ a.rank = b.rank ∧
    (a.steps < b.steps ∨ a.steps = b.steps ∧ a.serial < b.serial)

def QueuePriority.renumber (key : QueuePriority) (f : Nat → Nat) : QueuePriority :=
  { key with serial := f key.serial }

/-- A finite insertion or erasure of inactive starts changes serials by
    a strictly increasing renumbering on the active enqueue sequence. -/
theorem QueuePriority.renumber_preserves_order (a b : QueuePriority)
    (f : Nat → Nat) (increasing : ∀ i j, i < j → f i < f j) :
    (a.renumber f).before (b.renumber f) ↔ a.before b := by
  have serial : f a.serial < f b.serial ↔ a.serial < b.serial := by
    refine ⟨fun h => ?_, increasing _ _⟩
    cases Nat.lt_trichotomy a.serial b.serial with
    | inl lt => exact lt
    | inr other =>
      cases other with
      | inl eq => exact False.elim (Nat.lt_irrefl _ (eq ▸ h))
      | inr gt => exact False.elim (Nat.lt_asymm h (increasing _ _ gt))
  simp only [before, renumber, serial]

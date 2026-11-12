import Std

/- A candidate proof component. It classifies no campaign edge.
   A key must encode a complete native lookup, including its owner and ports.
   The answer is an ordered list of canonical tokens. The state contains all
   work, summaries, NORMAL records, sources, Targets and reports.
   Source correspondence and a complete native trace remain separate gates. -/
namespace SuccessorQueryTrace

abbrev Answer := List Nat
abbrev Oracle (Key : Type) := Key → Answer

inductive Action (State Key : Type) where
  | halt
  | localStep (next : State)
  | query (key : Key) (resume : Answer → State)

structure Result (State Key : Type) where
  state : State
  complete : Bool
  queries : List Key

def prepend (q : Key) (r : Result State Key) : Result State Key :=
  { r with queries := q :: r.queries }

def execute (step : State → Action State Key) (oracle : Oracle Key) :
    Nat → State → Result State Key
  | 0, state => ⟨state, false, []⟩
  | fuel + 1, state =>
      match step state with
      | .halt => ⟨state, true, []⟩
      | .localStep next => execute step oracle fuel next
      | .query q resume => prepend q (execute step oracle fuel (resume (oracle q)))

def neutral (old replacement : Oracle Key) : List Key → Bool
  | [] => true
  | q :: qs => decide (old q = replacement q) && neutral old replacement qs

theorem neutral_cons (old replacement : Oracle Key) (q : Key) (qs : List Key) :
    neutral old replacement (q :: qs) = true ↔
      old q = replacement q ∧ neutral old replacement qs = true := by
  simp [neutral]

theorem checked_trace_preserves_execution
    (step : State → Action State Key) (old replacement : Oracle Key)
    (fuel : Nat) (state : State)
    (h : neutral old replacement (execute step old fuel state).queries = true) :
    execute step old fuel state = execute step replacement fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      cases action : step state with
      | halt => simp [execute, action]
      | localStep next =>
          simp only [execute, action] at h ⊢
          exact ih next h
      | query q resume =>
          simp only [execute, action, prepend] at h ⊢
          have pair := (neutral_cons old replacement q _).mp h
          have rest := ih (resume (old q)) pair.2
          rw [pair.1] at rest
          rw [pair.1, rest]

def check (step : State → Action State Key) (old replacement : Oracle Key)
    (fuel : Nat) (state : State) : Bool :=
  let result := execute step old fuel state
  result.complete && neutral old replacement result.queries

theorem accepted_certificate_has_complete_baseline
    (step : State → Action State Key) (old replacement : Oracle Key)
    (fuel : Nat) (state : State)
    (h : check step old replacement fuel state = true) :
    (execute step old fuel state).complete = true := by
  have both : (execute step old fuel state).complete = true ∧
      neutral old replacement (execute step old fuel state).queries = true := by
    simpa [check] using h
  exact both.1

theorem accepted_certificate_preserves_execution
    (step : State → Action State Key) (old replacement : Oracle Key)
    (fuel : Nat) (state : State)
    (h : check step old replacement fuel state = true) :
    execute step old fuel state = execute step replacement fuel state := by
  have both : (execute step old fuel state).complete = true ∧
      neutral old replacement (execute step old fuel state).queries = true := by
    simpa [check] using h
  exact checked_trace_preserves_execution step old replacement fuel state
    both.2

theorem accepted_certificate_has_complete_replacement
    (step : State → Action State Key) (old replacement : Oracle Key)
    (fuel : Nat) (state : State)
    (h : check step old replacement fuel state = true) :
    (execute step replacement fuel state).complete = true := by
  rw [← accepted_certificate_preserves_execution step old replacement fuel state h]
  exact accepted_certificate_has_complete_baseline step old replacement fuel state h

theorem accepted_certificate_preserves_handoff
    (step : State → Action State Key) (old replacement : Oracle Key)
    (fuel : Nat) (state : State) (handoff : State → NextState)
    (h : check step old replacement fuel state = true) :
    handoff (execute step old fuel state).state =
      handoff (execute step replacement fuel state).state := by
  rw [accepted_certificate_preserves_execution step old replacement fuel state h]

theorem accepted_certificate_preserves_all_later_behavior
    (step : State → Action State Key) (old replacement : Oracle Key)
    (fuel : Nat) (state : State) (handoff : State → NextState)
    (future : NextState → Observation)
    (h : check step old replacement fuel state = true) :
    future (handoff (execute step old fuel state).state) =
      future (handoff (execute step replacement fuel state).state) := by
  rw [accepted_certificate_preserves_handoff step old replacement fuel state handoff h]

/- Explicit cells reject weaker certificates. C2 and C5 are distinct keys. -/
def twoQueryStep : Nat → Action Nat Nat
  | 0 => .query 0 (fun answer => if answer == [1] then 1 else 4)
  | 1 => .query 1 (fun answer => if answer == [2] then 2 else 3)
  | _ => .halt

def oldOracle : Oracle Nat
  | 0 => [1]
  | 1 => [2]
  | _ => [7]

def changedOutput : Oracle Nat
  | 0 => [1]
  | 1 => []
  | _ => [7]

def changedUnqueried : Oracle Nat
  | 0 => [1]
  | 1 => [2]
  | _ => []

theorem c2_only_agreement_is_insufficient :
    oldOracle 0 = changedOutput 0 ∧
      (execute twoQueryStep oldOracle 4 0).state ≠
        (execute twoQueryStep changedOutput 4 0).state := by decide

theorem partial_query_prefix_is_insufficient :
    neutral oldOracle changedOutput [0] = true ∧
      check twoQueryStep oldOracle changedOutput 4 0 = false := by decide

theorem absent_query_can_change :
    check twoQueryStep oldOracle changedUnqueried 4 0 = true := by decide

theorem incomplete_execution_is_rejected :
    check twoQueryStep oldOracle oldOracle 1 0 = false := by decide

def orderStep : Nat → Action Nat Nat
  | 0 => .query 0 (fun answer => answer.headD 9)
  | _ => .halt

def firstOrder : Oracle Nat := fun _ => [1, 2]
def secondOrder : Oracle Nat := fun _ => [2, 1]

theorem equal_membership_does_not_imply_equal_order :
    (∀ n, n ∈ firstOrder 0 ↔ n ∈ secondOrder 0) ∧
      check orderStep firstOrder secondOrder 3 0 = false := by
  constructor
  · intro n; simp [firstOrder, secondOrder, or_comm]
  · decide

/- This third key models a prepared emptyForBase/saved-replay decision. -/
def preparedDecisionStep : Nat → Action Nat Nat
  | 0 => .query 2 (fun answer => if answer == [0] then 1 else 2)
  | _ => .halt

def changedPreparedDecision : Oracle Nat
  | 0 => [1]
  | 1 => [2]
  | _ => [1]

theorem prepared_decision_must_be_in_frame :
    oldOracle 0 = changedPreparedDecision 0 ∧
    oldOracle 1 = changedPreparedDecision 1 ∧
    check preparedDecisionStep oldOracle changedPreparedDecision 3 0 = false := by decide

#print axioms neutral_cons
#print axioms checked_trace_preserves_execution
#print axioms accepted_certificate_has_complete_baseline
#print axioms accepted_certificate_preserves_execution
#print axioms accepted_certificate_has_complete_replacement
#print axioms accepted_certificate_preserves_handoff
#print axioms accepted_certificate_preserves_all_later_behavior
#print axioms c2_only_agreement_is_insufficient
#print axioms partial_query_prefix_is_insufficient
#print axioms absent_query_can_change
#print axioms incomplete_execution_is_rejected
#print axioms equal_membership_does_not_imply_equal_order
#print axioms prepared_decision_must_be_in_frame

end SuccessorQueryTrace

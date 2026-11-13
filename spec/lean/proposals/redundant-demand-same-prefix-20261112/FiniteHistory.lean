import Std

namespace FiniteHistory

-- Logical concept only. This file does not claim native AP correspondence.
-- The native test must establish every actual observation and sink result.
inductive World where | a | b
  deriving DecidableEq, Repr
inductive Observation where | common | normalRename
  deriving DecidableEq, Repr

def observed (world : World) (run : Nat) : Observation :=
  if run < 11 then .common else
  match world with | .a => .common | .b => .normalRename

def observedPrefix (world : World) (last : Nat) : List Observation :=
  (List.range last).map (fun index => observed world (index + 1))

theorem same_five_run_prefix : observedPrefix .a 5 = observedPrefix .b 5 := by decide

theorem later_distinct : observed .a 11 ≠ observed .b 11 := by decide

theorem executable_counterpair :
    ∃ a b : World, observedPrefix a 5 = observedPrefix b 5 ∧ observed a 11 ≠ observed b 11 := by
  exact ⟨.a, .b, same_five_run_prefix, later_distinct⟩

-- Generic extensionality: a history-only decision cannot distinguish equal inputs.
theorem policy_same_on_equal_prefix (policy : List Observation → Bool) :
    policy (observedPrefix .a 5) = policy (observedPrefix .b 5) := by
  rw [same_five_run_prefix]

-- These booleans describe the measured U-finding cut outcomes. They are not
-- an AP transfer model. The native four-control test supplies that evidence.
def observedULoss : World → Bool
  | .a => false
  | .b => true

def SafeDeletion (policy : List Observation → Bool) : Prop :=
  ∀ world, policy (observedPrefix world 5) = true → observedULoss world = false

theorem safe_policy_keeps_this_history (policy : List Observation → Bool)
    (safe : SafeDeletion policy) : policy (observedPrefix .a 5) = false := by
  cases result : policy (observedPrefix .a 5) with
  | false => rfl
  | true =>
      have same : policy (observedPrefix .b 5) = true := by
        rw [← policy_same_on_equal_prefix policy]
        exact result
      have impossible : true = false := safe .b same
      cases impossible

#print axioms policy_same_on_equal_prefix
#print axioms safe_policy_keeps_this_history
#print axioms same_five_run_prefix
#print axioms later_distinct
#print axioms executable_counterpair
end FiniteHistory

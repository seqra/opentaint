import Std

/- A finite base-graph component, not a demand-retirement theorem.
The source adapter overapproximates unknown callees, paths and filters.
Only a checked closed-set witness is used for negative reachability. -/
namespace DirectFlowBaseReachability

abbrev Edge := Nat × Nat

inductive Walk (edges : List Edge) (start : Nat) : Nat → Prop where
  | start : Walk edges start start
  | step {before after} : Walk edges start before → (before, after) ∈ edges →
      Walk edges start after

def closedCheck (edges : List Edge) (vertices : List Nat) : Bool :=
  edges.all fun edge => !(decide (edge.1 ∈ vertices)) || decide (edge.2 ∈ vertices)

theorem checked_step_closed (edges : List Edge) (vertices : List Nat)
    (checked : closedCheck edges vertices = true) (before after : Nat)
    (edge : (before, after) ∈ edges) (member : before ∈ vertices) : after ∈ vertices := by
  have h := List.all_eq_true.mp checked (before, after) edge
  simpa [member] using h

theorem checked_walk_closed (edges : List Edge) (vertices : List Nat)
    (checked : closedCheck edges vertices = true) (start : Nat)
    (seed : start ∈ vertices) (target : Nat) (walk : Walk edges start target) :
    target ∈ vertices := by
  induction walk with
  | start => exact seed
  | step walk edge ih => exact checked_step_closed edges vertices checked _ _ edge ih

theorem outside_checked_closure_unreachable (edges : List Edge) (vertices : List Nat)
    (checked : closedCheck edges vertices = true) (start : Nat)
    (seed : start ∈ vertices) (target : Nat) (outside : target ∉ vertices) :
    ¬ Walk edges start target := by
  intro walk
  exact outside (checked_walk_closed edges vertices checked start seed target walk)

end DirectFlowBaseReachability

#print axioms DirectFlowBaseReachability.checked_step_closed
#print axioms DirectFlowBaseReachability.checked_walk_closed
#print axioms DirectFlowBaseReachability.outside_checked_closure_unreachable

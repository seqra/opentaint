import Std

namespace CandidateJoin

variable {Row Input Result : Type}

/-- An inverse selector may omit only a native None pair. -/
def Complete (select : Row → Input → Option Result) (candidate : Row → Input → Bool) : Prop :=
  ∀ row input, candidate row input = false → select row input = none

def selected (select : Row → Input → Option Result) (candidate : Row → Input → Bool)
    (row : Row) (input : Input) : Option Result :=
  if candidate row input then select row input else none

theorem selected_equals_native (select : Row → Input → Option Result)
    (candidate : Row → Input → Bool) (complete : Complete select candidate) (row : Row) (input : Input) :
    selected select candidate row input = select row input := by
  cases answer : candidate row input with
  | false => simp [selected, answer, complete row input answer]
  | true => simp [selected, answer]

theorem same_ordered_input_matches (select : Row → Input → Option Result)
    (candidate : Row → Input → Bool) (complete : Complete select candidate)
    (row : Row) (inputs : List Input) :
    inputs.filterMap (selected select candidate row) = inputs.filterMap (select row) := by
  have same : selected select candidate row = select row := by
    funext input
    exact selected_equals_native select candidate complete row input
  rw [same]

theorem same_ordered_row_input_join (select : Row → Input → Option Result)
    (candidate : Row → Input → Bool) (complete : Complete select candidate)
    (rows : List Row) (inputs : List Input) :
    rows.flatMap (fun row => inputs.filterMap (selected select candidate row)) =
      rows.flatMap (fun row => inputs.filterMap (select row)) := by
  have same : (fun row => inputs.filterMap (selected select candidate row)) =
      (fun row => inputs.filterMap (select row)) := by
    funext row
    exact same_ordered_input_matches select candidate complete row inputs
  rw [same]

theorem omitting_live_pair_is_unsound :
    ([0] : List Nat).filterMap (fun input => some input) ≠
      ([0] : List Nat).filterMap (selected (fun (_ : Nat) (input : Nat) => some input) (fun _ _ => false) 7) := by
  decide

end CandidateJoin

import Relations

/-!
Concrete finite traces through the selected NORMAL relation basis.
This is a composition theorem for the denotation proved in Relations.lean.
It does not model native AP approximation, C2/C5, worklist discovery or cutoffs.
-/
namespace FlowAntichains.Reachability
set_option autoImplicit false

open FlowAntichains.Relations

structure Position (Field : Type) where
  base : Nat
  path : List Field
  mark : Nat

variable {Field : Type}

def pairAt (owner : Nat) (input output : Position Field) : Pair Field :=
  ⟨owner, input.base, output.base, input.mark, input.path, output.path⟩

def edge (rows : List (Row Field)) (input output : Position Field) : Prop :=
  input.mark = output.mark ∧ ∃ owner, listDenotes rows (pairAt owner input output)

/-- A concrete list of intermediate positions is an explicit path witness. -/
def path (rows : List (Row Field)) : List (Position Field) → Prop
  | [] => True
  | [_] => True
  | input :: output :: rest => edge rows input output ∧ path rows (output :: rest)

theorem canonical_edge [DecidableEq Field] (rows : List (Row Field))
    (input output : Position Field) :
    edge (canonical rows) input output ↔ edge rows input output := by
  simp only [edge]
  apply and_congr_right
  intro _
  exact exists_congr fun owner => canonical_relation rows (pairAt owner input output)

theorem canonical_path [DecidableEq Field] (rows : List (Row Field))
    (positions : List (Position Field)) :
    path (canonical rows) positions ↔ path rows positions := by
  induction positions with
  | nil => rfl
  | cons input rest ih =>
    cases rest with
    | nil => rfl
    | cons output rest =>
      simpa only [path, canonical_edge] using and_congr Iff.rfl ih

theorem exact_intermediate_positions [DecidableEq Field] (rows : List (Row Field))
    (positions : List (Position Field)) (old : path rows positions) :
    path (canonical rows) positions := (canonical_path rows positions).mpr old

theorem no_new_concrete_path [DecidableEq Field] (rows : List (Row Field))
    (positions : List (Position Field)) (fresh : path (canonical rows) positions) :
    path rows positions := (canonical_path rows positions).mp fresh

/-- Observations use the same supplied endpoint predicates and the same concrete path.
    This models concrete source/sink observations, not native report construction. -/
def observed (rows : List (Row Field)) (source sink : Position Field → Prop)
    (input output : Position Field) (middle : List (Position Field)) : Prop :=
  source input ∧ path rows (input :: middle ++ [output]) ∧ sink output

theorem canonical_observation [DecidableEq Field] (rows : List (Row Field))
    (source sink : Position Field → Prop) (input output : Position Field)
    (middle : List (Position Field)) :
    observed (canonical rows) source sink input output middle ↔
      observed rows source sink input output middle := by
  simp only [observed, canonical_path]

theorem observation_witness_unchanged [DecidableEq Field] (rows : List (Row Field))
    (source sink : Position Field → Prop) (input output : Position Field)
    (middle : List (Position Field))
    (old : observed rows source sink input output middle) :
    observed (canonical rows) source sink input output middle :=
  (canonical_observation rows source sink input output middle).mpr old

theorem edge_preserves_full_mark (rows : List (Row Field)) (input output : Position Field)
    (valid : edge rows input output) : input.mark = output.mark := valid.1

theorem path_nil (rows : List (Row Field)) : path rows [] := True.intro

theorem path_single (rows : List (Row Field)) (p : Position Field) : path rows [p] := True.intro

end FlowAntichains.Reachability

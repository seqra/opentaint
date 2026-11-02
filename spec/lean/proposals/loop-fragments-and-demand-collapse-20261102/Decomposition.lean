import Init

/-!
Ordered-region decomposition: B = BL ; L ; AL, recursively through AL.

A segment is an opaque sequential operation or an already selected loop
region. A split is a sequential composite containing a sequential BL,
one loop L and a possibly deep AL tree. Successive source loops therefore
occur in nested after regions, not as extra children beside the first L.
The loop body itself is opaque here; its internal decomposition follows
the supplied CFG/layout contract in Control and Blocks.

The executable build preserves the exact source segment sequence, including
order and multiplicity. It supports an empty prefix and arbitrarily many
successive loops. These are ordered-region laws, not a general JVM CFG
partition algorithm or a proof of AP summary/demand composition.
-/
namespace LoopFragments.Decomposition
set_option autoImplicit false

inductive Segment (Atom : Type) where
  | plain (atom : Atom)
  | loop (atom : Atom)
  deriving DecidableEq, Repr

inductive Tree (Atom : Type) where
  | sequential (operations : List Atom)
  | split (before : List Atom) (body : Atom) (after : Tree Atom)
  deriving DecidableEq, Repr

variable {Atom State : Type}

def prepend (atom : Atom) : Tree Atom → Tree Atom
  | .sequential operations => .sequential (atom :: operations)
  | .split before body after => .split (atom :: before) body after

def build : List (Segment Atom) → Tree Atom
  | [] => .sequential []
  | .plain atom :: rest => prepend atom (build rest)
  | .loop atom :: rest => .split [] atom (build rest)

def flatten : Tree Atom → List (Segment Atom)
  | .sequential operations => operations.map .plain
  | .split before body after => before.map .plain ++ .loop body :: flatten after

theorem prepend_preserves_first_sequential_operation (atom : Atom) (tree : Tree Atom) :
    flatten (prepend atom tree) = .plain atom :: flatten tree := by
  cases tree <;> rfl

theorem exact_source_sequence (source : List (Segment Atom)) :
    flatten (build source) = source := by
  induction source with
  | nil => rfl
  | cons segment rest previous =>
      cases segment with
      | plain atom => simp only [build, prepend_preserves_first_sequential_operation, previous]
      | loop atom => simp only [build, flatten, List.map_nil, List.nil_append, previous]

theorem split_at_first_loop (before : List Atom) (body : Atom) (after : List (Segment Atom)) :
    build (before.map .plain ++ .loop body :: after) = .split before body (build after) := by
  induction before with
  | nil => rfl
  | cons atom rest previous =>
      simp only [List.map_cons, List.cons_append, build, previous, prepend]

theorem no_loop_region_is_sequential (operations : List Atom) :
    build (operations.map .plain) = .sequential operations := by
  induction operations with
  | nil => rfl
  | cons atom rest previous => simp only [List.map_cons, build, previous, prepend]

theorem immediate_next_loop_has_empty_before (first second : Atom) :
    build [.loop first, .loop second] =
      .split [] first (.split [] second (.sequential [])) := rfl

theorem successor_loop_is_in_after (first second : Atom) (after : List (Segment Atom)) :
    build (.loop first :: .loop second :: after) =
      .split [] first (.split [] second (build after)) := rfl

def loopCount : List (Segment Atom) → Nat
  | [] => 0
  | .plain _ :: rest => loopCount rest
  | .loop _ :: rest => loopCount rest + 1

def afterDepth : Tree Atom → Nat
  | .sequential _ => 0
  | .split _ _ after => afterDepth after + 1

theorem prepend_keeps_after_depth (atom : Atom) (tree : Tree Atom) :
    afterDepth (prepend atom tree) = afterDepth tree := by cases tree <;> rfl

theorem after_hierarchy_accounts_for_every_successive_loop (source : List (Segment Atom)) :
    afterDepth (build source) = loopCount source := by
  induction source with
  | nil => rfl
  | cons segment rest previous =>
      cases segment with
      | plain atom => simpa only [build, prepend_keeps_after_depth, loopCount] using previous
      | loop atom => simp only [build, afterDepth, loopCount, previous]

theorem empty_region_has_no_operations : flatten (build ([] : List (Segment Atom))) = [] := rfl

/-- A supplied semantics can treat each selected loop atom as a whole region. -/
def evaluate (step : State → Segment Atom → State) (initial : State) (tree : Tree Atom) : State :=
  (flatten tree).foldl step initial

theorem decomposition_preserves_supplied_ordered_semantics
    (step : State → Segment Atom → State) (initial : State) (source : List (Segment Atom)) :
    evaluate step initial (build source) = source.foldl step initial := by
  simp only [evaluate, exact_source_sequence]

def twoLoops : List (Segment Nat) := [.plain 0, .loop 1, .loop 2, .plain 3]

theorem user_two_loop_shape :
    build twoLoops = .split [0] 1 (.split [] 2 (.sequential [3])) := rfl

theorem user_two_loop_source_order :
    flatten (build twoLoops) = [.plain 0, .loop 1, .loop 2, .plain 3] := rfl

theorem user_two_loop_after_is_composite : afterDepth (build twoLoops) = 2 := rfl

end LoopFragments.Decomposition

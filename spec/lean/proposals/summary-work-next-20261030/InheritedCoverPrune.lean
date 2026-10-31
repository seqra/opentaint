import Std

/-! A finite marked-coordinate tree, with typed exact/nonexact mark atoms.
The fold forgets positions only to ask whether inherited cover removes every
payload. Future cover may grow, but cannot remove inherited cover.
Generic Kotlin leaf algebras, cached DAG folds and protection adapters are not
verified by this kernel. -/
namespace InheritedCoverPrune

inductive Slot where | exact | nonexact deriving DecidableEq, Repr
structure Atom where
  mark : Nat
  slot : Slot
  deriving DecidableEq, Repr
inductive Tree where
  | leaf (payload : List Atom)
  | branch (payload : List Atom) (left right : Tree)
  deriving Repr
abbrev Path := List Bool
abbrev Cover := Path → List Atom

def folded : Tree → List Atom
  | .leaf atoms => atoms
  | .branch atoms left right => atoms ++ folded left ++ folded right

def strip (atoms cover : List Atom) : List Atom := atoms.filter fun a => !cover.contains a

def walk (cover : Cover) (path : Path) : Tree → List (Path × Atom)
  | .leaf atoms => (strip atoms (cover path)).map fun a => (path,a)
  | .branch atoms left right =>
      (strip atoms (cover path)).map (fun a => (path,a)) ++
        walk cover (path ++ [false]) left ++ walk cover (path ++ [true]) right

def containsAll (atoms cover : List Atom) : Prop := ∀ a, a ∈ atoms → a ∈ cover

def futureRetains (above : List Atom) (future : Cover) : Prop :=
  ∀ path a, a ∈ above → a ∈ future path

def canPrune (tree : Tree) (above : List Atom) : Bool :=
  (folded tree).all fun a => above.contains a

theorem strip_all_covered_is_empty (atoms cover : List Atom) (h : containsAll atoms cover) :
    strip atoms cover = [] := by
  induction atoms with
  | nil => rfl
  | cons head tail ih =>
      have hit : cover.contains head = true := List.contains_iff_mem.mpr (h head (List.mem_cons_self))
      have rest := ih (fun a ha => h a (List.mem_cons_of_mem head ha))
      simpa only [strip, List.filter_cons, hit, Bool.not_true, Bool.false_eq_true, ↓reduceIte] using rest

theorem canPrune_iff_all_payloads_covered (tree : Tree) (above : List Atom) :
    canPrune tree above = true ↔ containsAll (folded tree) above := by
  constructor
  · intro h a ha
    exact List.contains_iff_mem.mp (List.all_eq_true.mp h a ha)
  · intro h
    exact List.all_eq_true.mpr (fun a ha => List.contains_iff_mem.mpr (h a ha))

theorem future_cover_keeps_payload_covered (atoms above : List Atom) (future : Cover)
    (h : containsAll atoms above) (keep : futureRetains above future) (path : Path) :
    containsAll atoms (future path) := by
  intro a ha
  exact keep path a (h a ha)

theorem inherited_fold_cover_removes_every_residual_coordinate (tree : Tree)
    (above : List Atom) (future : Cover) (path : Path)
    (h : containsAll (folded tree) above) (keep : futureRetains above future) :
    walk future path tree = [] := by
  induction tree generalizing path with
  | leaf atoms =>
      have noLeaf := strip_all_covered_is_empty atoms (future path)
        (future_cover_keeps_payload_covered atoms above future h keep path)
      simp only [walk, noLeaf, List.map_nil]
  | branch atoms left right ihLeft ihRight =>
      have own : containsAll atoms above := by
        intro a ha; apply h a
        exact List.mem_append_left _ (List.mem_append_left _ ha)
      have leftCovered : containsAll (folded left) above := by
        intro a ha; apply h a
        exact List.mem_append_left _ (List.mem_append_right _ ha)
      have rightCovered : containsAll (folded right) above := by
        intro a ha; apply h a
        exact List.mem_append_right _ ha
      have noLeaf := strip_all_covered_is_empty atoms (future path)
        (future_cover_keeps_payload_covered atoms above future own keep path)
      rw [walk, noLeaf, ihLeft _ leftCovered, ihRight _ rightCovered]
      rfl

theorem executable_prune_preserves_empty_residual (tree : Tree) (above : List Atom)
    (future : Cover) (path : Path) (h : canPrune tree above = true)
    (keep : futureRetains above future) : walk future path tree = [] :=
  inherited_fold_cover_removes_every_residual_coordinate tree above future path
    ((canPrune_iff_all_payloads_covered tree above).mp h) keep

/-- The two passes are independent. Ordinary cover does not replace guarded cover. -/
def bothPasses (ordinary guarded : Tree) (ordinaryCover protectedCover : Cover) :
    List (Path × Atom) × List (Path × Atom) :=
  (walk ordinaryCover [] ordinary, walk protectedCover [] guarded)

theorem ordinary_pruning_leaves_protected_pass_unchanged (ordinary guarded : Tree)
    (above : List Atom) (ordinaryCover protectedCover : Cover)
    (h : canPrune ordinary above = true) (keep : futureRetains above ordinaryCover) :
    bothPasses ordinary guarded ordinaryCover protectedCover =
      ([], walk protectedCover [] guarded) := by
  rw [bothPasses, executable_prune_preserves_empty_residual ordinary above ordinaryCover [] h keep]

def exactT : Atom := ⟨1,.exact⟩
def nonexactT : Atom := ⟨1,.nonexact⟩
def singletonIncoming : Tree := .leaf [exactT]
def ordinaryAbove : Cover := fun _ => [exactT,nonexactT]
def noProtectedAbove : Cover := fun _ => []

theorem unprotected_MAY_cover_cannot_remove_protected_EXACT :
    bothPasses singletonIncoming singletonIncoming ordinaryAbove noProtectedAbove =
      ([], [([],exactT)]) := by decide

def fullNodeCount : Tree → Nat
  | .leaf _ => 1
  | .branch _ left right => 1 + fullNodeCount left + fullNodeCount right

def oldWalkNodes (tree : Tree) : Nat := fullNodeCount tree
/-- One root test. The fold is assumed already cached for this work metric. -/
def newWalkNodes (tree : Tree) (above : List Atom) : Nat :=
  if canPrune tree above then 1 else fullNodeCount tree

theorem pruning_visits_one_node (tree : Tree) (above : List Atom)
    (h : canPrune tree above = true) : newWalkNodes tree above = 1 := by simp [newWalkNodes,h]

theorem tree_has_at_least_one_node (tree : Tree) : 1 ≤ fullNodeCount tree := by
  cases tree <;> simp [fullNodeCount] <;> omega

theorem covered_branch_saves_at_least_twofold_node_visits (atoms : List Atom)
    (left right : Tree) (above : List Atom)
    (h : canPrune (.branch atoms left right) above = true) :
    2 * newWalkNodes (.branch atoms left right) above ≤ oldWalkNodes (.branch atoms left right) := by
  have hl := tree_has_at_least_one_node left
  have hr := tree_has_at_least_one_node right
  simp [pruning_visits_one_node _ _ h, oldWalkNodes, fullNodeCount]
  omega

def exampleTree : Tree := .branch [] (.leaf [exactT]) (.leaf [nonexactT])

theorem three_nodes_become_one :
    oldWalkNodes exampleTree = 3 ∧ newWalkNodes exampleTree [exactT,nonexactT] = 1 := by decide

end InheritedCoverPrune

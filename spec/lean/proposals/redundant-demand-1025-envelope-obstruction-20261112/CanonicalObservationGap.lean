import Std

namespace CanonicalObservationGap

-- This is a small observational model. It is not a model of the selected
-- method body or of the complete native C2/C5/Target pipeline.
inductive Tail where | may | must | exact deriving BEq, DecidableEq
inductive Layer where | normal | demand deriving BEq, DecidableEq
structure Fact where
  path : List Nat
  tail : Tail
  layer : Layer
  h : Bool := false
  mark : Nat := 0
  exclusion : List Nat := []
  deriving BEq, DecidableEq

-- The proved absorption cells use empty exclusions and equal marks/layers/flags.
-- This helper is not the native coverage rule for arbitrary nonempty exclusions.
-- EXACT uses equality, while MAY/MUST use the path-prefix case only.
def covers (a b : Fact) : Bool :=
  a.tail == b.tail && a.layer == b.layer &&
  a.h == b.h && a.mark == b.mark &&
  a.exclusion == b.exclusion &&
  if a.tail == .exact then a.path == b.path else a.path.isPrefixOf b.path

def insert (xs : List Fact) (f : Fact) : List Fact :=
  if xs.any (fun x => covers x f) then xs
  else f :: xs.filter (fun x => !(covers f x))
def canonical (xs : List Fact) : List Fact := xs.foldl insert []

inductive Input where | coarseMay | coarseMust | pointG
  deriving BEq, DecidableEq

def primary : Input → Fact
  | .coarseMay => ⟨[], .may, .demand, false, 0, []⟩
  | .coarseMust => ⟨[], .must, .normal, false, 0, []⟩
  | .pointG => ⟨[16], .exact, .normal, false, 0, []⟩
def latent : Input → Fact
  | .coarseMay => ⟨[12], .may, .demand, false, 0, []⟩
  | .coarseMust => ⟨[12], .must, .normal, false, 0, []⟩
  | .pointG => ⟨[12], .exact, .normal, false, 0, []⟩

def baseOutput (i : Input) := canonical [primary i]
def extraBranchOutput (i : Input) := canonical [primary i, latent i]

-- A child MAY or MUST output is invisible under the same-lane root.
theorem coarse_may_equal :
    extraBranchOutput .coarseMay = baseOutput .coarseMay := by rfl
theorem coarse_must_equal :
    extraBranchOutput .coarseMust = baseOutput .coarseMust := by rfl

-- The same two coarse observations can be repeated for any number of rounds.
def coarseHistory : Nat → Bool → List (List Fact)
  | 0, _ => []
  | n + 1, extra =>
      (if extra then extraBranchOutput .coarseMay else baseOutput .coarseMay) ::
      (if extra then extraBranchOutput .coarseMust else baseOutput .coarseMust) ::
      coarseHistory n extra
theorem arbitrary_coarse_history_equal (n : Nat) :
    coarseHistory n true = coarseHistory n false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change baseOutput .coarseMay :: baseOutput .coarseMust :: coarseHistory n true =
      baseOutput .coarseMay :: baseOutput .coarseMust :: coarseHistory n false
    exact congrArg (fun xs => baseOutput .coarseMay :: baseOutput .coarseMust :: xs) ih

-- A later point input distinguishes the two transfer candidates.
theorem point_output_differs :
    extraBranchOutput .pointG ≠ baseOutput .pointG := by decide
theorem hidden_point_is_not_covered :
    (baseOutput .pointG).any (fun x => covers x (latent .pointG)) = false := by rfl

-- A coarse MAY self-return cannot by itself supply a strict natural rank.
theorem no_strict_rank_for_coarse_self_return (rank : Input → Nat) :
    ¬ rank .coarseMay < rank .coarseMay := Nat.lt_irrefl _

#print axioms coarse_may_equal
#print axioms coarse_must_equal
#print axioms arbitrary_coarse_history_equal
#print axioms point_output_differs
#print axioms hidden_point_is_not_covered
#print axioms no_strict_rank_for_coarse_self_return

end CanonicalObservationGap

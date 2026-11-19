/- Structural comparison before traversal scratch is needed. -/

inductive TriePrefix (Header Branch : Type) where
  | terminal (header : Header)
  | linear (header : Header) (next : TriePrefix Header Branch)
  | divergent (header : Header) (body : Branch)
  deriving DecidableEq

def trieCompare {Header Branch : Type} [DecidableEq Header] [DecidableEq Branch] :
    TriePrefix Header Branch → TriePrefix Header Branch → Bool
  | .terminal h, .terminal k => decide (h = k)
  | .linear h a, .linear k b => decide (h = k) && trieCompare a b
  | a@(.divergent _ _), b@(.divergent _ _) => decide (a = b)
  | _, _ => false

/-- The header contains the leaf and all accessor labels at this node.
    Before a branch, each successful comparison leaves exactly one
    pair to check. At the first branch the native comparison resumes. -/
theorem trieCompare_spec {Header Branch : Type} [DecidableEq Header] [DecidableEq Branch]
    (a b : TriePrefix Header Branch) : trieCompare a b = decide (a = b) := by
  induction a generalizing b with
  | terminal h =>
    cases b <;> simp [trieCompare]
  | linear h child ih =>
    cases b <;> simp [trieCompare, ih]
  | divergent h body =>
    cases b <;> simp [trieCompare]

/-- A childless postorder walk invokes the operation once with no
    child results. Its identity memo has no readings before that call. -/
def singletonPostorder {Key Value : Type} (key : Key) (step : Key → List Value → Value) :
    List Value := [step key []]

theorem singletonNeedsNoMemo {Key Value : Type} (key : Key) (step : Key → List Value → Value) :
    (singletonPostorder key step).head? = some (step key []) := rfl

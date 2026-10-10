/-
  Count accepted normalized demand patterns at hand-off.

  The full AP hand-off supplies normalized, canonical patterns. Here their
  identity is a Nat tag; tag zero is the implicit zero demand. This model checks
  the builder/count boundary, not AP normalization or canonical shape.
-/
import Std

namespace ApSpec.CurrentDemandFrontier

-- Avoid the generic Ord-derived reflexivity instance, whose proof is classical.
local instance : ReflBEq Nat := ⟨by intro n; exact decide_eq_true rfl⟩

structure Key where
  method : Nat
  pattern : Nat
deriving DecidableEq, Repr

/-- Exact insertion reports whether it added a stored pattern. -/
def add (entries : List Key) (k : Key) : Bool × List Key :=
  if k.pattern = 0 then (false, entries)
  else if k ∈ entries then (false, entries)
  else (true, k :: entries)

theorem length_delta (entries : List Key) (k : Key) :
    (add entries k).2.length = entries.length + if (add entries k).1 then 1 else 0 := by
  by_cases hz : k.pattern = 0
  · simp [add, hz]
  · by_cases hm : k ∈ entries <;> simp [add, hz, hm]

/-- Number of stored outgoing patterns of one method key. -/
def methodCount (entries : List Key) (m : Nat) : Nat :=
  (entries.filter fun k => k.method == m).length

theorem method_count_delta (entries : List Key) (k : Key) (m : Nat) :
    methodCount (add entries k).2 m = methodCount entries m +
      if (add entries k).1 && k.method == m then 1 else 0 := by
  by_cases hz : k.pattern = 0
  · simp [add, hz]
  · by_cases hm : k ∈ entries
    · simp [add, hz, hm]
    · by_cases hmethod : k.method = m <;> simp [add, hz, hm, methodCount, hmethod]

structure State where
  entries : List Key
  count : Nat
deriving DecidableEq, Repr

def push (s : State) (k : Key) : State :=
  let r := add s.entries k
  ⟨r.2, s.count + if r.1 then 1 else 0⟩

theorem push_count (s : State) (k : Key) (h : s.count = s.entries.length) :
    (push s k).count = (push s k).entries.length := by
  simp only [push, h]
  exact (length_delta s.entries k).symm

theorem fold_count (keys : List Key) (s : State) (h : s.count = s.entries.length) :
    (keys.foldl push s).count = (keys.foldl push s).entries.length := by
  induction keys generalizing s with
  | nil => exact h
  | cons k ks ih => exact ih (push s k) (push_count s k h)

def build (keys : List Key) : State := keys.foldl push ⟨[], 0⟩

theorem build_count (keys : List Key) : (build keys).count = (build keys).entries.length :=
  fold_count keys ⟨[], 0⟩ rfl

namespace Certificate

/-- Two raw pieces normalized to the same canonical pattern. -/
def duplicatePatterns : List Key := [⟨4, 8⟩, ⟨4, 8⟩]

theorem duplicate_count : (build duplicatePatterns).count = 1 := rfl

theorem old_duplicate_overcount : duplicatePatterns.length = 2 := rfl

def implicitZero : List Key := [⟨4, 0⟩]

theorem zero_not_counted : (build implicitZero).count = 0 := rfl

theorem old_zero_overcount : implicitZero.length = 1 := rfl

def differentMethods : List Key := [⟨4, 8⟩, ⟨5, 8⟩]

theorem different_methods_kept : (build differentMethods).count = 2 := rfl

def check : Bool := (build duplicatePatterns).count == 1 &&
  (build implicitZero).count == 0 && (build differentMethods).count == 2

theorem checked : check = true := rfl

end Certificate
end ApSpec.CurrentDemandFrontier

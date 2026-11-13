import Std

namespace BoundedRoundTrip

-- A concept model only. The native test must establish the correspondence.
-- A copy first stores under a fixed deep path, then reads that same path.
-- If the temporary path is cut, the read returns MAY/DEMAND.
inductive Result where | normalCopy | coarseDemand
  deriving DecidableEq, Repr

def fieldLimit (run : Nat) : Nat := max 1 (run - 1)
def roundTrip (depth limit : Nat) : Result :=
  if depth ≤ limit then .normalCopy else .coarseDemand
def atRun (depth run : Nat) : Result := roundTrip depth (fieldLimit run)

theorem eight_field_repetition :
    atRun 8 3 = .coarseDemand ∧ atRun 8 5 = .coarseDemand := by decide

theorem eight_field_future_change : atRun 8 9 = .normalCopy := by decide

theorem repetition_does_not_prove_stability :
    atRun 8 3 = atRun 8 5 ∧ atRun 8 9 ≠ atRun 8 5 := by decide

theorem bounded_copy_precise (depth limit : Nat) (fits : depth ≤ limit) :
    roundTrip depth limit = .normalCopy := by
  simp only [roundTrip, fits, ↓reduceIte]

#print axioms eight_field_repetition
#print axioms eight_field_future_change
#print axioms repetition_does_not_prove_stability
#print axioms bounded_copy_precise
end BoundedRoundTrip

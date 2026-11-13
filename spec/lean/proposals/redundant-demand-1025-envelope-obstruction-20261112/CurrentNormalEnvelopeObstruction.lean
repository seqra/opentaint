import Std

namespace CurrentNormalEnvelopeObstruction

-- Coordinate family observed for every precise NORMAL saved read of ret.f.*.
-- This model does not assert that the method can produce the candidate below.
def normalPaths (bytes element stringBytes f : Nat) : List (List Nat) :=
  [[f], [element,f], [stringBytes,f], [stringBytes,element,f],
   [bytes,f], [bytes,element,f]]

def target (bytes g : Nat) : List Nat := [bytes,g]

-- The assertion is uniform in the common future suffix. It uses only literal
-- accessor inequalities, with no finite JVM field/type universe assumption.
theorem no_normal_prefix_cover (bytes element stringBytes f g : Nat)
    (e : (element == bytes) = false) (s : (stringBytes == bytes) = false)
    (f0 : (f == bytes) = false) (f1 : (f == g) = false)
    (e1 : (element == g) = false) (suffix : List Nat) :
    (normalPaths bytes element stringBytes f).any
      (fun p => p.isPrefixOf (target bytes g ++ suffix)) = false := by
  change ((f == bytes && true) ||
    ((element == bytes && (f == g && true)) ||
    ((stringBytes == bytes && (f == g && true)) ||
    ((stringBytes == bytes && (element == g && [f].isPrefixOf suffix)) ||
    ((bytes == bytes && (f == g && true)) ||
    ((bytes == bytes && (element == g && [f].isPrefixOf suffix)) || false)))))) = false
  rw [e, s, f0, f1, e1]
  cases bytes == bytes <;> rfl

theorem native_accessor_control :
    (normalPaths 4 11 0 12).any
      (fun p => p.isPrefixOf (target 4 16)) = false := by
  decide

-- A MAY result at bytes or at the root has a geometric cover. Native saved
-- MUST inversion produces that result on DEMAND, so it is not a NORMAL cover.
theorem coarse_bytes_cover (suffix : List Nat) :
    [4].isPrefixOf (target 4 16 ++ suffix) = true := by
  rfl

theorem coarse_root_cover (suffix : List Nat) :
    ([] : List Nat).isPrefixOf (target 4 16 ++ suffix) = true := by
  rfl

#print axioms no_normal_prefix_cover
#print axioms native_accessor_control
#print axioms coarse_bytes_cover
#print axioms coarse_root_cover

end CurrentNormalEnvelopeObstruction

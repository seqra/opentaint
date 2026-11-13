import Std

namespace NormalEnvelopeObstruction

-- These are the distinct precise output paths observed when all saved
-- direct/opposite NORMAL views read ret.bytes.h.*. The remaining matching
-- MUST records produce MAY/DEMAND, not a precise NORMAL result.
def normalPaths (bytes element stringBytes h : Nat) : List (List Nat) :=
  [[bytes,h], [element,bytes,h], [stringBytes,bytes,h],
   [stringBytes,element,bytes,h], [bytes,bytes,h],
   [bytes,element,bytes,h], [h], [stringBytes,h]]

def target (bytes element h : Nat) : List Nat := [bytes,element,h]

-- Prefix coverage is at least as permissive as native same-tail FLOW
-- coverage here. Even that test has no precise NORMAL witness.
theorem no_normal_prefix_cover (bytes element stringBytes h : Nat)
    (be : bytes ≠ element) (bs : bytes ≠ stringBytes)
    (hb : h ≠ bytes) (he : h ≠ element) :
    (normalPaths bytes element stringBytes h).any
      (fun p => p.isPrefixOf (target bytes element h)) = false := by
  have eb : (element == bytes) = false := beq_eq_false_iff_ne.mpr (Ne.symm be)
  have sb : (stringBytes == bytes) = false := beq_eq_false_iff_ne.mpr (Ne.symm bs)
  have bb : (bytes == element) = false := beq_eq_false_iff_ne.mpr be
  have fb : (h == bytes) = false := beq_eq_false_iff_ne.mpr hb
  have fe : (h == element) = false := beq_eq_false_iff_ne.mpr he
  have self : ∀ n : Nat, (n == n) = true := fun _ => beq_iff_eq.mpr rfl
  simp only [normalPaths,target,List.any_cons,List.any_nil,List.isPrefixOf_cons_cons,
    List.isPrefixOf_nil_left,List.isPrefixOf_cons_nil,eb,sb,bb,fb,fe,self,
    Bool.false_and,Bool.true_and,Bool.and_false,Bool.or_false]

theorem concrete_control :
    (normalPaths 1 2 3 4).any (fun p => p.isPrefixOf (target 1 2 4)) = false := by
  decide

-- A coarse MAY rooted at bytes.Element geometrically includes this point.
-- That says nothing about a NORMAL result: native MUST inversion demotes it.
theorem coarse_prefix_covers : [1,2].isPrefixOf (target 1 2 4) = true := by
  decide

#print axioms no_normal_prefix_cover
#print axioms concrete_control
#print axioms coarse_prefix_covers
end NormalEnvelopeObstruction

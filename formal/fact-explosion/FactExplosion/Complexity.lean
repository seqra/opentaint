import FactExplosion.Bounded

namespace FactExplosion

def openLeaf : AccessTree :=
  .node true false none .nil

def repeatedFacts (copies : Nat) : List AccessTree :=
  List.replicate copies openLeaf

theorem openLeaf_nodeCount : openLeaf.nodeCount = 1 := by
  rfl

theorem openLeaf_subtrees : openLeaf.subtrees = [openLeaf] := by
  rfl

theorem occurrenceCost_repeatedFacts (copies : Nat) :
    occurrenceCost (repeatedFacts copies) = copies := by
  simp [occurrenceCost, repeatedFacts, openLeaf_nodeCount]

theorem flatMap_subtrees_replicate_openLeaf (copies : Nat) :
    (List.replicate copies openLeaf).flatMap AccessTree.subtrees =
      List.replicate copies openLeaf := by
  induction copies with
  | zero => rfl
  | succ copies ih =>
      simp [List.replicate_succ, openLeaf_subtrees, ih]

theorem rawNodes_repeatedFacts (copies : Nat) :
    rawNodes (repeatedFacts copies) = List.replicate copies openLeaf := by
  simpa [rawNodes, repeatedFacts] using flatMap_subtrees_replicate_openLeaf copies

theorem filter_not_openLeaf_replicate (copies : Nat) :
    (List.replicate copies openLeaf).filter (fun tree => !tree == openLeaf) = [] := by
  induction copies with
  | zero => rfl
  | succ copies ih =>
      rw [List.replicate_succ, List.filter_cons]
      change (if false then openLeaf :: List.filter (fun tree => !tree == openLeaf)
        (List.replicate copies openLeaf) else
        List.filter (fun tree => !tree == openLeaf) (List.replicate copies openLeaf)) = []
      exact ih

theorem canonicalNodes_repeatedFacts (copies : Nat) :
    canonicalNodes (repeatedFacts (copies + 1)) = [openLeaf] := by
  rw [canonicalNodes, rawNodes_repeatedFacts]
  rw [List.replicate_succ, List.eraseDups_cons, filter_not_openLeaf_replicate]
  rfl

theorem canonicalCost_repeatedFacts (copies : Nat) :
    canonicalCost (repeatedFacts (copies + 1)) = 1 := by
  simp [canonicalCost, canonicalNodes_repeatedFacts]

theorem repeatedFacts_complexity_gap (copies : Nat) :
    occurrenceCost (repeatedFacts (copies + 1)) = copies + 1 ∧
    canonicalCost (repeatedFacts (copies + 1)) = 1 := by
  exact ⟨occurrenceCost_repeatedFacts (copies + 1), canonicalCost_repeatedFacts copies⟩

theorem indexedNodeCost_repeatedFacts (copies : Nat) :
    indexedNodeCost (repeatedFacts (copies + 1)) = 1 := by
  rw [indexedNodeCost_eq_canonicalCost, canonicalCost_repeatedFacts]

theorem boundedRepeated_complexity_gap
    {limit : Nat}
    (positive : 0 < limit)
    (copies : Nat) :
    occurrenceCost (repeatedFacts (copies + 1)) = copies + 1 ∧
    (boundedInternFacts limit [] (repeatedFacts (copies + 1))).1.length = 1 := by
  constructor
  · exact occurrenceCost_repeatedFacts (copies + 1)
  · change (boundedInternFacts limit []
      (List.replicate (copies + 1) openLeaf)).1.length = 1
    rw [boundedInternFacts_repeated positive copies openLeaf]
    rfl

def baselineRepeatedSingletonArrayCost (copies : Nat) : Nat :=
  2 * copies

def optimizedRepeatedSingletonArrayCost (copies : Nat) : Nat :=
  if copies = 0 then 0 else 1

theorem repeatedSingletonArray_complexity_gap (copies : Nat) :
    baselineRepeatedSingletonArrayCost (copies + 1) = 2 * (copies + 1) ∧
    optimizedRepeatedSingletonArrayCost (copies + 1) = 1 := by
  simp [baselineRepeatedSingletonArrayCost, optimizedRepeatedSingletonArrayCost]

def splitChildStorageSlots (nodes : Nat) : Nat :=
  2 * nodes

def unionChildStorageSlots (nodes : Nat) : Nat :=
  nodes

theorem taggedChildUnion_slot_gap (nodes : Nat) :
    splitChildStorageSlots nodes = 2 * nodes ∧
    unionChildStorageSlots nodes = nodes := by
  exact ⟨rfl, rfl⟩

end FactExplosion

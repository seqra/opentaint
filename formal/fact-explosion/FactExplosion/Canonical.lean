import FactExplosion.Concept

namespace FactExplosion

def rawNodes (facts : List AccessTree) : List AccessTree :=
  facts.flatMap AccessTree.subtrees

def canonicalNodes (facts : List AccessTree) : List AccessTree :=
  (rawNodes facts).eraseDups

def locate (target : AccessTree) : List AccessTree -> Option Nat
  | [] => none
  | head :: tail =>
      if target == head then some 0
      else (locate target tail).map Nat.succ

def encodeRoot (facts : List AccessTree) (root : AccessTree) : Option Nat :=
  locate root (canonicalNodes facts)

def decodeRoot (facts : List AccessTree) (root : Nat) : Option AccessTree :=
  (canonicalNodes facts)[root]?

theorem locate_sound {target : AccessTree} {nodes : List AccessTree} {index : Nat}
    (found : locate target nodes = some index) : nodes[index]? = some target := by
  induction nodes generalizing index with
  | nil => simp [locate] at found
  | cons head tail ih =>
      by_cases equal : target = head
      · subst equal
        simp [locate] at found
        subst found
        simp
      · have notEqual : (target == head) = false := by
          simp [equal]
        simp [locate, notEqual] at found
        obtain ⟨tailIndex, located, rfl⟩ := found
        simp [ih located]

theorem locate_complete {target : AccessTree} {nodes : List AccessTree}
    (present : target ∈ nodes) : ∃ index, locate target nodes = some index := by
  induction nodes with
  | nil => simp at present
  | cons head tail ih =>
      by_cases equal : target = head
      · subst equal
        exact ⟨0, by simp [locate]⟩
      · have inTail : target ∈ tail := by
          simpa [equal] using present
        obtain ⟨index, found⟩ := ih inTail
        exact ⟨index + 1, by simp [locate, equal, found]⟩

theorem mem_rawNodes_of_mem {facts : List AccessTree} {tree : AccessTree}
    (present : tree ∈ facts) : tree ∈ rawNodes facts := by
  induction facts with
  | nil => simp at present
  | cons head tail ih =>
      simp only [List.mem_cons] at present
      simp only [rawNodes, List.flatMap_cons, List.mem_append]
      cases present with
      | inl equal =>
          subst equal
          exact Or.inl (AccessTree.self_mem_subtrees _)
      | inr inTail =>
          exact Or.inr (ih inTail)

theorem mem_canonicalNodes_of_mem {facts : List AccessTree} {tree : AccessTree}
    (present : tree ∈ facts) : tree ∈ canonicalNodes facts := by
  rw [canonicalNodes, List.mem_eraseDups]
  exact mem_rawNodes_of_mem present

theorem encodeRoot_witness {facts : List AccessTree} {tree : AccessTree}
    (present : tree ∈ facts) :
    ∃ index, encodeRoot facts tree = some index ∧ decodeRoot facts index = some tree := by
  have inTable := mem_canonicalNodes_of_mem present
  obtain ⟨index, found⟩ := locate_complete inTable
  exact ⟨index, found, locate_sound found⟩

theorem encoded_accepts_exactly {facts : List AccessTree} {tree : AccessTree}
    (present : tree ∈ facts) (fuel : Nat) (path : List Step) :
    ∃ index decoded,
      encodeRoot facts tree = some index ∧
      decodeRoot facts index = some decoded ∧
      accepts fuel decoded path = accepts fuel tree path := by
  obtain ⟨index, encoded, decoded⟩ := encodeRoot_witness present
  exact ⟨index, tree, encoded, decoded, rfl⟩

theorem encoded_wellFormed_exactly {facts : List AccessTree} {tree : AccessTree}
    (present : tree ∈ facts) :
    ∃ index decoded,
      encodeRoot facts tree = some index ∧
      decodeRoot facts index = some decoded ∧
      decoded.wellFormed = tree.wellFormed := by
  obtain ⟨index, encoded, decoded⟩ := encodeRoot_witness present
  exact ⟨index, tree, encoded, decoded, rfl⟩

def occurrenceCost (facts : List AccessTree) : Nat :=
  (facts.map AccessTree.nodeCount).sum

def canonicalCost (facts : List AccessTree) : Nat :=
  (canonicalNodes facts).length

theorem eraseDups_nodup (nodes : List AccessTree) : nodes.eraseDups.Nodup := by
  cases nodes with
  | nil => simp
  | cons head tail =>
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · rw [List.mem_eraseDups]
        simp
      · exact eraseDups_nodup (tail.filter fun node => !node == head)
termination_by nodes.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem eraseDups_length_le (nodes : List AccessTree) :
    nodes.eraseDups.length ≤ nodes.length := by
  cases nodes with
  | nil => simp
  | cons head tail =>
      rw [List.eraseDups_cons]
      simp only [List.length_cons]
      have recursive := eraseDups_length_le (tail.filter fun node => !node == head)
      have filtered := List.length_filter_le (fun node => !node == head) tail
      omega
termination_by nodes.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem canonicalNodes_nodup (facts : List AccessTree) :
    (canonicalNodes facts).Nodup := by
  exact eraseDups_nodup (rawNodes facts)

theorem rawNodes_length (facts : List AccessTree) :
    (rawNodes facts).length = occurrenceCost facts := by
  simp [rawNodes, occurrenceCost, List.length_flatMap, AccessTree.subtrees_length]

theorem canonicalCost_le_occurrenceCost (facts : List AccessTree) :
    canonicalCost facts ≤ occurrenceCost facts := by
  calc
    canonicalCost facts ≤ (rawNodes facts).length := eraseDups_length_le (rawNodes facts)
    _ = occurrenceCost facts := rawNodes_length facts

end FactExplosion

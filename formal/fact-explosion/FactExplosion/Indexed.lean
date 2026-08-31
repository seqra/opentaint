import FactExplosion.Canonical

namespace FactExplosion

structure IndexedNode where
  isAbstract : Bool
  isFinal : Bool
  exclusions : Option DeepExclusion
  children : List (Edge × Nat)
deriving DecidableEq, Repr

structure IndexedDag where
  nodes : List IndexedNode
  roots : List Nat
deriving DecidableEq, Repr

def locateIndex (target : AccessTree) (trees : List AccessTree) : Nat :=
  (locate target trees).getD 0

def encodeIndexedNode (trees : List AccessTree) : AccessTree → IndexedNode
  | .node abstract final excluded children =>
      ⟨abstract, final, excluded,
        children.toList.map fun pair => (pair.1, locateIndex pair.2 trees)⟩

def encodeIndexedDag (facts : List AccessTree) : IndexedDag :=
  let trees := canonicalNodes facts
  ⟨trees.map (encodeIndexedNode trees), facts.map fun tree => locateIndex tree trees⟩

mutual
  def decodeIndexedNode : Nat → List IndexedNode → Nat → Option AccessTree
    | 0, _, _ => none
    | fuel + 1, nodes, index => do
        let node ← nodes[index]?
        let children ← decodeIndexedBranches fuel nodes node.children
        some (.node node.isAbstract node.isFinal node.exclusions children)

  def decodeIndexedBranches : Nat → List IndexedNode → List (Edge × Nat) → Option Branches
    | _, _, [] => some .nil
    | fuel, nodes, (edge, index) :: tail => do
        let child ← decodeIndexedNode fuel nodes index
        let decodedTail ← decodeIndexedBranches fuel nodes tail
        some (.cons edge child decodedTail)
end

def indexedAccepts
    (decodeFuel matchFuel : Nat)
    (dag : IndexedDag)
    (root : Nat)
    (path : List Step) : Bool :=
  match decodeIndexedNode decodeFuel dag.nodes root with
  | none => false
  | some tree => accepts matchFuel tree path

def indexedWellFormed (decodeFuel : Nat) (dag : IndexedDag) (root : Nat) : Bool :=
  match decodeIndexedNode decodeFuel dag.nodes root with
  | none => false
  | some tree => tree.wellFormed

def ReferencesValid (dag : IndexedDag) : Prop :=
  ∀ node ∈ dag.nodes, ∀ edge index,
    (edge, index) ∈ node.children →
    ∃ childNode, dag.nodes[index]? = some childNode

def ChildClosed (trees : List AccessTree) : Prop :=
  ∀ tree ∈ trees, ∀ edge child,
    (edge, child) ∈ tree.children.toList → child ∈ trees

theorem locateIndex_sound {target : AccessTree} {trees : List AccessTree}
    (present : target ∈ trees) : trees[locateIndex target trees]? = some target := by
  obtain ⟨index, found⟩ := locate_complete present
  have selected := locate_sound found
  simpa [locateIndex, found] using selected

theorem encodedNode_at_locateIndex {target : AccessTree} {trees : List AccessTree}
    (present : target ∈ trees) :
    (trees.map (encodeIndexedNode trees))[locateIndex target trees]? =
      some (encodeIndexedNode trees target) := by
  rw [List.getElem?_map]
  simp [locateIndex_sound present]

theorem Branches.directChild_mem_subtrees
    {branches : Branches} {edge : Edge} {child : AccessTree}
    (member : (edge, child) ∈ branches.toList) : child ∈ branches.subtrees := by
  cases branches with
  | nil => simp [Branches.toList] at member
  | cons headEdge headChild tail =>
      simp only [Branches.toList, List.mem_cons] at member
      simp only [Branches.subtrees, List.mem_append]
      cases member with
      | inl equal =>
          cases equal
          exact Or.inl (AccessTree.self_mem_subtrees child)
      | inr inTail =>
          exact Or.inr (Branches.directChild_mem_subtrees inTail)
termination_by branches

theorem AccessTree.directChild_mem_subtrees
    {tree : AccessTree} {edge : Edge} {child : AccessTree}
    (member : (edge, child) ∈ tree.children.toList) : child ∈ tree.subtrees := by
  cases tree with
  | node abstract final excluded branches =>
      simp only [AccessTree.children] at member
      simp only [AccessTree.subtrees, List.mem_cons]
      exact Or.inr (Branches.directChild_mem_subtrees member)

mutual
  theorem AccessTree.subtrees_transitive
      {root middle descendant : AccessTree}
      (middleMember : middle ∈ root.subtrees)
      (descendantMember : descendant ∈ middle.subtrees) :
      descendant ∈ root.subtrees := by
    cases root with
    | node abstract final excluded branches =>
        simp only [AccessTree.subtrees, List.mem_cons] at middleMember ⊢
        cases middleMember with
        | inl equal =>
            cases equal
            simpa [AccessTree.subtrees] using descendantMember
        | inr inBranches =>
            exact Or.inr (Branches.subtrees_transitive inBranches descendantMember)

  theorem Branches.subtrees_transitive
      {branches : Branches} {middle descendant : AccessTree}
      (middleMember : middle ∈ branches.subtrees)
      (descendantMember : descendant ∈ middle.subtrees) :
      descendant ∈ branches.subtrees := by
    cases branches with
    | nil => simp [Branches.subtrees] at middleMember
    | cons edge child tail =>
        simp only [Branches.subtrees, List.mem_append] at middleMember ⊢
        cases middleMember with
        | inl inChild =>
            exact Or.inl (AccessTree.subtrees_transitive inChild descendantMember)
        | inr inTail =>
            exact Or.inr (Branches.subtrees_transitive inTail descendantMember)
end

theorem rawNodes_childClosed (facts : List AccessTree) : ChildClosed (rawNodes facts) := by
  intro tree treeMember edge child childMember
  rw [rawNodes] at treeMember ⊢
  simp only [List.mem_flatMap] at treeMember ⊢
  obtain ⟨root, rootMember, treeInRoot⟩ := treeMember
  exact ⟨root, rootMember,
    AccessTree.subtrees_transitive treeInRoot
      (AccessTree.directChild_mem_subtrees childMember)⟩

theorem canonicalNodes_childClosed (facts : List AccessTree) :
    ChildClosed (canonicalNodes facts) := by
  intro tree treeMember edge child childMember
  rw [canonicalNodes, List.mem_eraseDups] at treeMember ⊢
  exact rawNodes_childClosed facts tree treeMember edge child childMember

mutual
  theorem decodeIndexedNode_exact
      (trees : List AccessTree)
      (closed : ChildClosed trees)
      (tree : AccessTree)
      (present : tree ∈ trees)
      (fuel : Nat)
      (enough : tree.nodeCount < fuel) :
      decodeIndexedNode fuel (trees.map (encodeIndexedNode trees))
        (locateIndex tree trees) = some tree := by
    cases tree with
    | node abstract final excluded children =>
        cases fuel with
        | zero => simp [AccessTree.nodeCount] at enough
        | succ fuel =>
            have childrenEnough : children.nodeCount < fuel := by
              simp [AccessTree.nodeCount] at enough
              omega
            have childrenPresent : ∀ edge child,
                (edge, child) ∈ children.toList → child ∈ trees := by
              intro edge child member
              exact closed (.node abstract final excluded children) present edge child member
            rw [decodeIndexedNode]
            rw [encodedNode_at_locateIndex present]
            change (do
              let decodedChildren ← decodeIndexedBranches fuel
                (trees.map (encodeIndexedNode trees))
                (children.toList.map fun pair => (pair.1, locateIndex pair.2 trees))
              some (AccessTree.node abstract final excluded decodedChildren)) =
              some (AccessTree.node abstract final excluded children)
            rw [decodeIndexedBranches_exact trees closed children childrenPresent fuel childrenEnough]
            rfl

  theorem decodeIndexedBranches_exact
      (trees : List AccessTree)
      (closed : ChildClosed trees)
      (branches : Branches)
      (present : ∀ edge child,
        (edge, child) ∈ branches.toList → child ∈ trees)
      (fuel : Nat)
      (enough : branches.nodeCount < fuel) :
      decodeIndexedBranches fuel (trees.map (encodeIndexedNode trees))
        (branches.toList.map fun pair => (pair.1, locateIndex pair.2 trees)) =
        some branches := by
    cases branches with
    | nil => simp [Branches.toList, decodeIndexedBranches]
    | cons edge child tail =>
        have childPresent : child ∈ trees := by
          exact present edge child (by simp [Branches.toList])
        have tailPresent : ∀ tailEdge tailChild,
            (tailEdge, tailChild) ∈ tail.toList → tailChild ∈ trees := by
          intro tailEdge tailChild member
          exact present tailEdge tailChild (by simp [Branches.toList, member])
        have childEnough : child.nodeCount < fuel := by
          simp [Branches.nodeCount] at enough
          omega
        have tailEnough : tail.nodeCount < fuel := by
          simp [Branches.nodeCount] at enough
          omega
        rw [Branches.toList]
        simp only [List.map_cons]
        rw [decodeIndexedBranches]
        rw [decodeIndexedNode_exact trees closed child childPresent fuel childEnough]
        rw [decodeIndexedBranches_exact trees closed tail tailPresent fuel tailEnough]
        rfl
end

theorem encodedDag_root_mem {facts : List AccessTree} {tree : AccessTree}
    (present : tree ∈ facts) :
    locateIndex tree (canonicalNodes facts) ∈ (encodeIndexedDag facts).roots := by
  simp only [encodeIndexedDag, List.mem_map]
  exact ⟨tree, present, rfl⟩

theorem decodeEncodedDag_exact {facts : List AccessTree} {tree : AccessTree}
    (present : tree ∈ facts) :
    decodeIndexedNode (tree.nodeCount + 1) (encodeIndexedDag facts).nodes
      (locateIndex tree (canonicalNodes facts)) = some tree := by
  have canonicalPresent := mem_canonicalNodes_of_mem present
  change decodeIndexedNode (tree.nodeCount + 1)
    ((canonicalNodes facts).map (encodeIndexedNode (canonicalNodes facts)))
    (locateIndex tree (canonicalNodes facts)) = some tree
  exact decodeIndexedNode_exact
    (canonicalNodes facts)
    (canonicalNodes_childClosed facts)
    tree canonicalPresent (tree.nodeCount + 1) (Nat.lt_succ_self tree.nodeCount)

theorem encodedChildIndex_valid
    {facts : List AccessTree}
    {tree child : AccessTree}
    {edge : Edge}
    (treePresent : tree ∈ canonicalNodes facts)
    (childMember : (edge, child) ∈ tree.children.toList) :
    (encodeIndexedDag facts).nodes[locateIndex child (canonicalNodes facts)]? =
      some (encodeIndexedNode (canonicalNodes facts) child) := by
  have childPresent := canonicalNodes_childClosed facts
    tree treePresent edge child childMember
  change ((canonicalNodes facts).map (encodeIndexedNode (canonicalNodes facts)))[locateIndex child (canonicalNodes facts)]? =
      some (encodeIndexedNode (canonicalNodes facts) child)
  exact encodedNode_at_locateIndex childPresent

theorem encodedDag_references_valid (facts : List AccessTree) :
    ReferencesValid (encodeIndexedDag facts) := by
  intro node nodeMember edge index childMember
  change node ∈ (canonicalNodes facts).map
    (encodeIndexedNode (canonicalNodes facts)) at nodeMember
  rw [List.mem_map] at nodeMember
  obtain ⟨tree, treeMember, nodeEqual⟩ := nodeMember
  subst node
  cases tree with
  | node abstract final excluded branches =>
      simp only [encodeIndexedNode] at childMember
      rw [List.mem_map] at childMember
      obtain ⟨sourcePair, sourceMember, pairEqual⟩ := childMember
      rcases sourcePair with ⟨sourceEdge, child⟩
      cases pairEqual
      exact ⟨encodeIndexedNode (canonicalNodes facts) child,
        encodedChildIndex_valid treeMember sourceMember⟩

theorem encodeIndexedRoot_witness {facts : List AccessTree} {tree : AccessTree}
    (present : tree ∈ facts) :
    ∃ root,
      root ∈ (encodeIndexedDag facts).roots ∧
      decodeIndexedNode (tree.nodeCount + 1) (encodeIndexedDag facts).nodes root = some tree := by
  exact ⟨locateIndex tree (canonicalNodes facts),
    encodedDag_root_mem present,
    decodeEncodedDag_exact present⟩

theorem encodedRoot_sound {facts : List AccessTree} {root : Nat}
    (rootMember : root ∈ (encodeIndexedDag facts).roots) :
    ∃ tree,
      tree ∈ facts ∧
      root = locateIndex tree (canonicalNodes facts) ∧
      decodeIndexedNode (tree.nodeCount + 1) (encodeIndexedDag facts).nodes root = some tree := by
  simp only [encodeIndexedDag, List.mem_map] at rootMember
  obtain ⟨tree, treeMember, equal⟩ := rootMember
  exact ⟨tree, treeMember, equal.symm, equal.symm ▸ decodeEncodedDag_exact treeMember⟩

theorem indexed_accepts_exactly
    {facts : List AccessTree} {tree : AccessTree}
    (present : tree ∈ facts)
    (matchFuel : Nat)
    (path : List Step) :
    ∃ root,
      root ∈ (encodeIndexedDag facts).roots ∧
      indexedAccepts (tree.nodeCount + 1) matchFuel
        (encodeIndexedDag facts) root path = accepts matchFuel tree path := by
  obtain ⟨root, rootMember, decoded⟩ := encodeIndexedRoot_witness present
  exact ⟨root, rootMember, by simp [indexedAccepts, decoded]⟩

theorem indexed_wellFormed_exactly
    {facts : List AccessTree} {tree : AccessTree}
    (present : tree ∈ facts) :
    ∃ root,
      root ∈ (encodeIndexedDag facts).roots ∧
      indexedWellFormed (tree.nodeCount + 1) (encodeIndexedDag facts) root =
        tree.wellFormed := by
  obtain ⟨root, rootMember, decoded⟩ := encodeIndexedRoot_witness present
  exact ⟨root, rootMember, by simp [indexedWellFormed, decoded]⟩

theorem encodeIndexedNode_injective_on
    (trees : List AccessTree)
    (closed : ChildClosed trees)
    {left right : AccessTree}
    (leftMember : left ∈ trees)
    (rightMember : right ∈ trees)
    (encodedEqual : encodeIndexedNode trees left = encodeIndexedNode trees right) :
    left = right := by
  let fuel := left.nodeCount + right.nodeCount + 1
  have leftEnough : left.nodeCount < fuel := by
    simp [fuel]
    omega
  have rightEnough : right.nodeCount < fuel := by
    simp [fuel]
    omega
  have leftDecoded := decodeIndexedNode_exact
    trees closed left leftMember fuel leftEnough
  have rightDecoded := decodeIndexedNode_exact
    trees closed right rightMember fuel rightEnough
  have decodedEqual :
      decodeIndexedNode fuel (trees.map (encodeIndexedNode trees)) (locateIndex left trees) =
      decodeIndexedNode fuel (trees.map (encodeIndexedNode trees)) (locateIndex right trees) := by
    rw [show fuel = (left.nodeCount + right.nodeCount) + 1 by simp [fuel]]
    simp only [decodeIndexedNode]
    rw [encodedNode_at_locateIndex leftMember,
      encodedNode_at_locateIndex rightMember, encodedEqual]
  rw [leftDecoded, rightDecoded] at decodedEqual
  exact Option.some.inj decodedEqual

theorem map_nodup_of_injective_on
    {source : List AccessTree}
    {target : AccessTree → IndexedNode}
    (sourceNodup : source.Nodup)
    (injectiveOn : ∀ left ∈ source, ∀ right ∈ source,
      target left = target right → left = right) :
    (source.map target).Nodup := by
  induction source with
  | nil => simp
  | cons head tail ih =>
      rw [List.nodup_cons] at sourceNodup
      rw [List.map_cons, List.nodup_cons]
      constructor
      · intro mappedMember
        rw [List.mem_map] at mappedMember
        obtain ⟨other, otherMember, equal⟩ := mappedMember
        have same := injectiveOn head (by simp) other (by simp [otherMember]) equal.symm
        subst other
        exact sourceNodup.1 otherMember
      · exact ih sourceNodup.2 (by
          intro left leftMember right rightMember equal
          exact injectiveOn left (by simp [leftMember]) right (by simp [rightMember]) equal)

theorem indexedNodes_nodup (facts : List AccessTree) :
    (encodeIndexedDag facts).nodes.Nodup := by
  change ((canonicalNodes facts).map
    (encodeIndexedNode (canonicalNodes facts))).Nodup
  exact map_nodup_of_injective_on
    (canonicalNodes_nodup facts)
    (by
      intro left leftMember right rightMember equal
      exact encodeIndexedNode_injective_on
        (canonicalNodes facts) (canonicalNodes_childClosed facts)
        leftMember rightMember equal)

def indexedNodeCost (facts : List AccessTree) : Nat :=
  (encodeIndexedDag facts).nodes.length

theorem indexedNodeCost_eq_canonicalCost (facts : List AccessTree) :
    indexedNodeCost facts = canonicalCost facts := by
  simp [indexedNodeCost, encodeIndexedDag, canonicalCost]

theorem indexedNodeCost_le_occurrenceCost (facts : List AccessTree) :
    indexedNodeCost facts ≤ occurrenceCost facts := by
  rw [indexedNodeCost_eq_canonicalCost]
  exact canonicalCost_le_occurrenceCost facts

end FactExplosion

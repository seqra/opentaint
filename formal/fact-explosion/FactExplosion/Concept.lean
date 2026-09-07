namespace FactExplosion

inductive Step where
  | field : Nat -> Step
  | element : Step
  | mark : Nat -> Step
  | static : Nat -> Step
  | value : Step
  | final : Step
  | typeGroup : Step
  | typeInfo : Nat -> Step
deriving BEq, DecidableEq, Repr

inductive Edge where
  | concrete : Step -> Edge
  | any : Edge
deriving BEq, DecidableEq, Repr

structure DeepExclusion where
  accessorsFromDepth0 : List Nat
  accessorsFromDepth1 : List Nat
deriving BEq, DecidableEq, Repr

mutual
  inductive AccessTree where
    | node : Bool -> Bool -> Option DeepExclusion -> Branches -> AccessTree
  deriving DecidableEq, Repr

  inductive Branches where
    | nil : Branches
    | cons : Edge -> AccessTree -> Branches -> Branches
  deriving DecidableEq, Repr
end

instance : BEq AccessTree where
  beq left right := decide (left = right)

instance : LawfulBEq AccessTree where
  eq_of_beq {left right} equal := by
    simpa using equal
  rfl := by
    intro tree
    simp

def Step.coveredByAny : Step -> Bool
  | .field _ => true
  | .element => true
  | _ => false

def Branches.toList : Branches -> List (Edge × AccessTree)
  | .nil => []
  | .cons edge child tail => (edge, child) :: tail.toList

def AccessTree.isAbstract : AccessTree -> Bool
  | .node abstract _ _ _ => abstract

def AccessTree.isFinal : AccessTree -> Bool
  | .node _ final _ _ => final

def AccessTree.exclusions : AccessTree -> Option DeepExclusion
  | .node _ _ excluded _ => excluded

def AccessTree.children : AccessTree -> Branches
  | .node _ _ _ children => children

def DeepExclusion.contains (excluded : DeepExclusion) (accessor : Nat) : Bool :=
  excluded.accessorsFromDepth0.contains accessor ||
    excluded.accessorsFromDepth1.contains accessor

def abstractAccepts
    (abstract : Bool)
    (excluded : Option DeepExclusion)
    (path : List Step) : Bool :=
  abstract && match path with
    | .field field :: _ =>
        match excluded with
        | none => true
        | some value => !(value.contains field)
    | _ => true

mutual
  def accepts : Nat -> AccessTree -> List Step -> Bool
    | 0, _, _ => false
    | fuel + 1, .node abstract final excluded children, path =>
        abstractAccepts abstract excluded path ||
        (final && path.isEmpty) ||
        acceptsBranches fuel children path

  def acceptsBranches : Nat -> Branches -> List Step -> Bool
    | _, .nil, _ => false
    | fuel, .cons edge child tail, path =>
        (match edge with
        | .concrete step =>
            match path with
            | [] => false
            | head :: rest => head == step && accepts fuel child rest
        | .any => acceptsThroughAny fuel child path) ||
        acceptsBranches fuel tail path

  def acceptsThroughAny : Nat -> AccessTree -> List Step -> Bool
    | 0, _, _ => false
    | fuel + 1, child, path =>
        accepts fuel child path ||
        match path with
        | [] => false
        | head :: tail => head.coveredByAny && acceptsThroughAny fuel child tail
end

mutual
  def AccessTree.nodeCount : AccessTree -> Nat
    | .node _ _ _ children => 1 + children.nodeCount

  def Branches.nodeCount : Branches -> Nat
    | .nil => 0
    | .cons _ child tail => child.nodeCount + tail.nodeCount
end

mutual
  def AccessTree.subtrees : AccessTree -> List AccessTree
    | tree@(.node _ _ _ children) => tree :: children.subtrees

  def Branches.subtrees : Branches -> List AccessTree
    | .nil => []
    | .cons _ child tail => child.subtrees ++ tail.subtrees
end

def AccessTree.terminalShape : AccessTree -> Bool
  | .node abstract final _ children =>
      (children matches .nil) && (abstract || final)

def edgeShapeIsValid (edge : Edge) (child : AccessTree) : Bool :=
  match edge with
  | .concrete (.mark _) => child.terminalShape
  | .concrete .final => child.terminalShape
  | _ => true

mutual
  def AccessTree.wellFormed : AccessTree -> Bool
    | .node abstract _ excluded children =>
        (abstract || excluded.isNone) &&
        children.uniqueEdges &&
        children.wellFormed

  def Branches.wellFormed : Branches -> Bool
    | .nil => true
    | .cons edge child tail =>
        edgeShapeIsValid edge child && child.wellFormed && tail.wellFormed

  def Branches.uniqueEdges : Branches -> Bool
    | .nil => true
    | .cons edge _ tail =>
        !(tail.toList.map Prod.fst).contains edge && tail.uniqueEdges
end

theorem AccessTree.self_mem_subtrees (tree : AccessTree) : tree ∈ tree.subtrees := by
  cases tree
  simp [AccessTree.subtrees]

mutual
  theorem AccessTree.subtrees_length (tree : AccessTree) :
      tree.subtrees.length = tree.nodeCount := by
    cases tree with
    | node abstract final excluded children =>
        simp [AccessTree.subtrees, AccessTree.nodeCount, Branches.subtrees_length, Nat.add_comm]

  theorem Branches.subtrees_length (branches : Branches) :
      branches.subtrees.length = branches.nodeCount := by
    cases branches with
    | nil => rfl
    | cons edge child tail =>
        simp [Branches.subtrees, Branches.nodeCount, AccessTree.subtrees_length,
          Branches.subtrees_length]
end

theorem accepts_equal {left right : AccessTree} (equal : left = right) (fuel : Nat) (path : List Step) :
    accepts fuel left path = accepts fuel right path := by
  cases equal
  rfl

theorem wellFormed_equal {left right : AccessTree} (equal : left = right) :
    left.wellFormed = right.wellFormed := by
  cases equal
  rfl

end FactExplosion

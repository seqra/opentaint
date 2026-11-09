/-
# Does the ADDED TREE bound what TIFA emits?

The design question, stated as a theorem rather than a measurement: if the added set is ONE tree with
`N` nodes, is the number of distinct initials TIFA can emit bounded by a function of `N`? If it is,
then bounding the tree's NODE COUNT bounds the emission structurally, and no emission-side policy is
needed at all.

Two facts about the walk are load-bearing, both read off `TreeInitialFactAbstraction`:

* A premise is the accumulated path `currentAp`, and the walk lengthens it only by descending the
  ADDED tree. The demand-trie step pushes `AbstractionState(trieChild, state.added, absorbed)` --
  the SAME `absorbed` path for every trie child -- so following the demand does not make the path
  longer, and cannot multiply premises by the size of the trie.
* The star step is `if (apHasAny) state.currentAp else ReversedApNode(ANY_ACCESSOR_IDX, ...)`, so an
  emitted path carries **at most one** `[any]`.

`emitted_le` proves the bound. `the_guard_is_load_bearing` shows what the second fact buys: without
it the same walk is EXPONENTIAL in the depth, so the guard is not a detail.
-/

namespace FactExplosion.TifaBound

abbrev Acc := Nat

/-- The wildcard accessor. Any value distinct from a real accessor will do. -/
def ANY : Acc := 0

/-- The added set, as one tree: children indexed by accessor. -/
inductive Tree where
  | mk (children : List (Acc × Tree))

mutual
  /-- Nodes of the tree. This is the quantity a size bound would control. -/
  def nodes : Tree → Nat
    | .mk cs => 1 + nodesL cs
  def nodesL : List (Acc × Tree) → Nat
    | [] => 0
    | c :: rest => nodes c.2 + nodesL rest
end

mutual
  /-- Every root-to-node path: exactly one per node. -/
  def paths : Tree → List (List Acc)
    | .mk cs => [] :: pathsL cs
  def pathsL : List (Acc × Tree) → List (List Acc)
    | [] => []
    | c :: rest => ((paths c.2).map (fun p => c.1 :: p)) ++ pathsL rest
end

mutual
  def height : Tree → Nat
    | .mk cs => heightL cs
  def heightL : List (Acc × Tree) → Nat
    | [] => 0
    | c :: rest => max (1 + height c.2) (heightL rest)
end

/-! ## One path per node -/

mutual
  theorem paths_length_eq_nodes : ∀ t : Tree, (paths t).length = nodes t := by
    intro t
    cases t with
    | mk cs =>
        show ((([] : List Acc)) :: pathsL cs).length = 1 + nodesL cs
        simp only [List.length_cons]
        rw [pathsL_length_eq_nodesL cs]
        omega

  theorem pathsL_length_eq_nodesL : ∀ cs : List (Acc × Tree), (pathsL cs).length = nodesL cs := by
    intro cs
    cases cs with
    | nil => rfl
    | cons c rest =>
        show (((paths c.2).map (fun p => c.1 :: p)) ++ pathsL rest).length
             = nodes c.2 + nodesL rest
        rw [List.length_append, List.length_map,
            paths_length_eq_nodes c.2, pathsL_length_eq_nodesL rest]
end

/-! ## The star, inserted at one position

`starAt p` is every way to put ONE `[any]` into `p`. The engine's `apHasAny` guard is exactly what
makes this the right model: a path that already carries a star does not get a second one.
-/

def starAt : List Acc → List (List Acc)
  | [] => [[ANY]]
  | x :: xs => (ANY :: x :: xs) :: (starAt xs).map (fun r => x :: r)

theorem starAt_length : ∀ p : List Acc, (starAt p).length = p.length + 1 := by
  intro p
  induction p with
  | nil => rfl
  | cons x xs ih => simp only [starAt, List.length_cons, List.length_map, ih]

/-- What the walk can emit: a path of the added tree, or such a path with one star in it. -/
def emitted (t : Tree) : List (List Acc) :=
  paths t ++ (paths t).flatMap starAt

/-! ## The bound -/

-- Every path of the tree is no longer than its height.
mutual
  theorem path_length_le_height : ∀ (t : Tree) (p : List Acc), p ∈ paths t → p.length ≤ height t := by
    intro t p hp
    cases t with
    | mk cs =>
        show p.length ≤ heightL cs
        rcases List.mem_cons.mp hp with h | h
        · subst h; simp
        · exact pathL_length_le_heightL cs p h

  theorem pathL_length_le_heightL :
      ∀ (cs : List (Acc × Tree)) (p : List Acc), p ∈ pathsL cs → p.length ≤ heightL cs := by
    intro cs p hp
    cases cs with
    | nil => cases hp
    | cons c rest =>
        show p.length ≤ max (1 + height c.2) (heightL rest)
        rcases List.mem_append.mp hp with h | h
        · obtain ⟨q, hq, hpq⟩ := List.mem_map.mp h
          have := path_length_le_height c.2 q hq
          subst hpq
          simp only [List.length_cons]
          omega
        · have := pathL_length_le_heightL rest p h
          omega
end

/-- The sum of `|p| + 1` over a list of paths, all of length at most `h`. -/
theorem flatMap_starAt_length_le : ∀ (ps : List (List Acc)) (h : Nat),
    (∀ p ∈ ps, p.length ≤ h) → (ps.flatMap starAt).length ≤ ps.length * (h + 1) := by
  intro ps h hlen
  induction ps with
  | nil => simp
  | cons p rest ih =>
      have hp : p.length ≤ h := hlen p (by simp)
      have hrest : ∀ q ∈ rest, q.length ≤ h := fun q hq => hlen q (by simp [hq])
      have := ih hrest
      simp only [List.flatMap_cons, List.length_append, starAt_length, List.length_cons]
      have hmul : (rest.length + 1) * (h + 1) = rest.length * (h + 1) + (h + 1) := by
        rw [Nat.add_mul, Nat.one_mul]
      omega

/--
**THE BOUND.** The number of initials the walk can emit is at most
`nodes * (height + 2)` -- so bounding the added tree's NODE COUNT bounds the emission, with no
emission-side policy. `height < nodes` always, so this is polynomial in the node count alone.
-/
theorem emitted_le (t : Tree) : (emitted t).length ≤ nodes t * (height t + 2) := by
  have hp : (paths t).length = nodes t := paths_length_eq_nodes t
  have hstar : ((paths t).flatMap starAt).length ≤ (paths t).length * (height t + 1) :=
    flatMap_starAt_length_le (paths t) (height t) (fun p hp' => path_length_le_height t p hp')
  have h1 : nodes t * (height t + 1) = nodes t * height t + nodes t := by
    rw [Nat.mul_add, Nat.mul_one]
  have h2 : nodes t * (height t + 2) = nodes t * height t + nodes t * 2 := by
    rw [Nat.mul_add]
  rw [hp] at hstar
  unfold emitted
  rw [List.length_append, hp]
  omega

/--
**Star-free, the bound is an EQUALITY and it is exactly the user's statement:** one initial per node
of the added tree.
-/
theorem star_free_is_exactly_nodes (t : Tree) : (paths t).length = nodes t :=
  paths_length_eq_nodes t

/-! ## Why the one-star guard is load-bearing

Drop `apHasAny` and a path may take a star at every position independently. The count is then `2^|p|`
rather than `|p| + 1`, and no bound in the node count survives.
-/

/-- Every way to insert stars at any subset of the positions of `p`. -/
def starAnywhere : List Acc → List (List Acc)
  | [] => [[]]
  | x :: xs =>
      let rest := starAnywhere xs
      rest.map (fun r => x :: r) ++ rest.map (fun r => ANY :: x :: r)

theorem starAnywhere_length : ∀ p : List Acc, (starAnywhere p).length = 2 ^ p.length := by
  intro p
  induction p with
  | nil => rfl
  | cons x xs ih =>
      show ((starAnywhere xs).map _ ++ (starAnywhere xs).map _).length = 2 ^ (xs.length + 1)
      rw [List.length_append, List.length_map, List.length_map, ih, Nat.pow_succ]
      omega

/-- **The separation.** One star per path is linear in the depth; unrestricted stars are exponential. -/
theorem the_guard_is_load_bearing :
    (starAt [1, 2, 3, 4, 5, 6, 7, 8]).length = 9 ∧
    (starAnywhere [1, 2, 3, 4, 5, 6, 7, 8]).length = 256 := by
  constructor
  · rw [starAt_length]; rfl
  · rw [starAnywhere_length]; rfl

end FactExplosion.TifaBound

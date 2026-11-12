import Std

/-! Metadata only. No facts, summaries, demand or report observations are imported. -/
namespace SupplementalMetadata
set_option autoImplicit false

/-- The source generator emits one optional prepare call, five fixed instructions,
 two instructions per branch and two instructions per saved registry field. -/
def bodyLength (prepare : Bool) (branches registry : Nat) : Nat :=
  (if prepare then 1 else 0) + 5 + 2 * branches + 2 * registry

theorem root_arity_unique (branches registry : Nat)
    (nonempty : 0 < branches) (size : bodyLength true branches registry = 8) :
    branches = 1 ∧ registry = 0 := by
  cases branches with
  | zero => exact False.elim (Nat.not_lt_zero 0 nonempty)
  | succ n =>
    have expand : bodyLength true (Nat.succ n) registry = 8 + 2 * (n + registry) := by
      change 6 + 2 * (n + 1) + 2 * registry = (6 + 2) + 2 * (n + registry)
      simp only [Nat.mul_add, Nat.mul_one]
      ac_rfl
    have product : 2 * (n + registry) = 0 :=
      Nat.add_left_cancel (expand.symm.trans size)
    have sum : n + registry = 0 := by
      cases Nat.mul_eq_zero.mp product with
      | inl impossible => exact False.elim (Nat.noConfusion impossible)
      | inr h => exact h
    obtain ⟨hn, hr⟩ := Nat.add_eq_zero_iff.mp sum
    exact ⟨congrArg Nat.succ hn, hr⟩

theorem child_arity_unique (branches : Nat)
    (size : bodyLength false branches 0 = 11) : branches = 3 := by
  change 5 + 2 * branches = 5 + 2 * 3 at size
  exact Nat.mul_left_cancel (by decide : 0 < 2) (Nat.add_left_cancel size)

def insertEdge (e : Nat × Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [e]
  | h :: t => if e.1 < h.1 ∨ (e.1 = h.1 ∧ e.2 ≤ h.2)
      then e :: h :: t else h :: insertEdge e t

def sortEdges : List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | h :: t => insertEdge h (sortEdges t)

/-- R=0 template. All call targets have the same CFG behavior at this boundary.
 This does not say their transfer summaries are interchangeable. -/
def templateEdges (prepare : Bool) (branches : Nat) : List (Nat × Nat) := Id.run do
  let header := if prepare then 1 else 0
  let switch := header + 1
  let cleanup := header + 2 + 2 * branches
  let branchEdges := (List.range branches).flatMap fun i =>
    let start := header + 2 + 2 * i
    [(switch, start), (start, start + 1), (start + 1, cleanup)]
  let edges := (if prepare then [(0, header)] else []) ++
    [(header, switch), (switch, cleanup)] ++ branchEdges ++
    [(cleanup, cleanup + 1), (cleanup + 1, header),
     (cleanup + 1, cleanup + 2), (cleanup + 2, cleanup + 4),
     (cleanup + 3, 0)]
  return sortEdges edges

theorem root_template_checked : templateEdges true 1 =
    [(0,1),(1,2),(2,3),(2,5),(3,4),(4,5),(5,6),(6,1),(6,7),(7,9),(8,0)] := by decide

theorem child_template_checked : templateEdges false 3 =
    [(0,1),(1,2),(1,4),(1,6),(1,8),(2,3),(3,8),(4,5),(5,8),
     (6,7),(7,8),(8,9),(9,0),(9,10),(10,12),(11,0)] := by decide

/-- The executable uniqueness test fixes the old and new source generator arity.
 The source correspondence supplies its body-length equation and nonemptiness. -/
theorem root_graph_equal (oldBranches oldRegistry newBranches newRegistry : Nat)
    (oldNonempty : 0 < oldBranches) (newNonempty : 0 < newBranches)
    (oldSize : bodyLength true oldBranches oldRegistry = 8)
    (newSize : bodyLength true newBranches newRegistry = 8) :
    templateEdges true oldBranches = templateEdges true newBranches := by
  obtain ⟨oldOne, _⟩ := root_arity_unique oldBranches oldRegistry oldNonempty oldSize
  obtain ⟨newOne, _⟩ := root_arity_unique newBranches newRegistry newNonempty newSize
  rw [oldOne, newOne]

theorem child_graph_equal (oldBranches newBranches : Nat)
    (oldSize : bodyLength false oldBranches 0 = 11)
    (newSize : bodyLength false newBranches 0 = 11) :
    templateEdges false oldBranches = templateEdges false newBranches := by
  rw [child_arity_unique oldBranches oldSize, child_arity_unique newBranches newSize]

/-- Once ordered CFG and boundary inputs agree, a deterministic builder's
 entire topology agrees. This is a model/source adapter contract, not a proof
 of the Kotlin frontend. -/
theorem deterministic_layout_equal {Input Output : Type}
    (builder : Input → Output) (old new : Input) (same : old = new) :
    builder old = builder new := congrArg builder same

#print axioms root_arity_unique
#print axioms child_arity_unique
#print axioms root_template_checked
#print axioms child_template_checked
#print axioms root_graph_equal
#print axioms child_graph_equal
#print axioms deterministic_layout_equal
end SupplementalMetadata

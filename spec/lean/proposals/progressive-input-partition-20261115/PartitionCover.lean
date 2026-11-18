import ColdMachine

/- A constructive local input partition. No AP field exclusion is created.
   A branch is installed at handoff, never during a deduplicated query. -/
namespace ProgressiveInputPartition
abbrev Word := List Nat

def childCase (field : Nat) (rest : Word) : Prop := ∃ suffix, rest = field :: suffix

def residual (children rest : Word) : Prop :=
  match rest with
  | [] => False
  | f :: _ => f ∉ children

def covered (children rest : Word) : Prop :=
  rest = [] ∨ residual children rest ∨ ∃ f, f ∈ children ∧ childCase f rest

theorem every_word_has_a_constructive_owner (children rest : Word) :
    covered children rest := by
  cases rest with
  | nil => exact Or.inl rfl
  | cons f tail =>
    by_cases yes : f ∈ children
    · exact Or.inr (Or.inr ⟨f,yes,tail,rfl⟩)
    · exact Or.inr (Or.inl yes)

theorem a_child_contains_its_point_and_nonempty_remainder (f : Nat) (rest : Word) :
    childCase f rest ↔ rest = [f] ∨ ∃ g suffix, rest = f :: g :: suffix := by
  constructor
  · rintro ⟨suffix,rfl⟩
    cases suffix with
    | nil => exact Or.inl rfl
    | cons g tail => exact Or.inr ⟨g,tail,rfl⟩
  · intro h
    rcases h with h | ⟨g,suffix,h⟩
    · exact ⟨[],h⟩
    · exact ⟨g :: suffix,h⟩

theorem delegated_child_never_belongs_to_the_residual
    (children : Word) (f : Nat) (suffix : Word) (member : f ∈ children) :
    ¬ residual children (f :: suffix) := by
  exact fun h => h member

/-- This is the semantic cover used at a local field transfer AND at a saved
    unary NORMAL prefix record. It concerns the entire remaining continuation,
    not just the equality of their abstract output APs. -/
theorem complete_child_service_preserves_any_continuation
    (children : Word) (service result : Word → Prop)
    (point : service [] → result [])
    (coarse : ∀ rest, residual children rest → service rest → result rest)
    (child : ∀ f, f ∈ children → ∀ suffix, service (f :: suffix) → result (f :: suffix)) :
    ∀ rest, service rest → result rest := by
  intro rest has
  rcases every_word_has_a_constructive_owner children rest with empty | rem | ⟨f,member,suffix,eq⟩
  · subst rest; exact point has
  · exact coarse rest rem has
  · subst rest; exact child f member suffix has

/-- Ordinary operations and call-summary applications are relations on words.
    The input-cover proof is therefore independent of where the consumer lives. -/
def image (transfer : Word → Word → Prop) (region : Word → Prop) (out : Word) : Prop :=
  ∃ input, region input ∧ transfer input out

theorem partition_distributes_over_any_transfer
    (transfer : Word → Word → Prop) (children : Word) (out : Word) :
    image transfer (fun _ => True) out ↔
      transfer [] out ∨ image transfer (residual children) out ∨
        ∃ f, f ∈ children ∧ image transfer (childCase f) out := by
  constructor
  · rintro ⟨input,_,h⟩
    rcases every_word_has_a_constructive_owner children input with empty | rem | ⟨f,member,child⟩
    · subst input; exact Or.inl h
    · exact Or.inr (Or.inl ⟨input,rem,h⟩)
    · exact Or.inr (Or.inr ⟨f,member,input,child,h⟩)
  · intro h
    rcases h with h | ⟨input,_,h⟩ | ⟨_,_,input,_,h⟩
    · exact ⟨[],True.intro,h⟩
    · exact ⟨input,True.intro,h⟩
    · exact ⟨input,True.intro,h⟩

structure LocalRow (α : Type) where
  inputHead : Word
  originalExit : α
  deriving DecidableEq

def refineInput (r : LocalRow α) (suffix : Word) : LocalRow α :=
  {r with inputHead := r.inputHead ++ suffix}

theorem refined_cells_preserve_the_complete_paired_exit
    (r : LocalRow α) (suffix : Word) :
    (refineInput r suffix).originalExit = r.originalExit := rfl

def install (tree : List Word) (next : Option Word) : List Word :=
  match next with | none => tree | some p => if p ∈ tree then tree else p :: tree

theorem one_handoff_adds_at_most_one_edge (tree : List Word) (next : Option Word) :
    (install tree next).length ≤ tree.length + 1 := by
  cases next with
  | none => simp [install]
  | some path => simp only [install]; split <;> simp_all

theorem installed_edges_are_never_lost (tree : List Word) (next : Option Word)
    (p : Word) (member : p ∈ tree) : p ∈ install tree next := by
  cases next with
  | none => exact member
  | some path => simp only [install]; split <;> simp_all

theorem a_fresh_split_strictly_grows_the_plan (tree : List Word) (path : Word)
    (fresh : path ∉ tree) :
    (install tree (some path)).length = tree.length + 1 := by
  simp [install,fresh]

/-- A finite priority prefix is a computable anti-starvation potential.
    The actual streaming selector chooses the least fresh observed edge;
    hence a continuously offered key k can only lose to keys <= k. -/
def pendingBelow (bound : Nat) (installed : List Nat) : List Nat :=
  (List.range (bound+1)).filter fun k => !(installed.contains k)

theorem chosen_below_a_waiting_key_is_still_an_uninstalled_witness
    (bound selected : Nat) (installed : List Nat)
    (small : selected ≤ bound) (fresh : selected ∉ installed) :
    selected ∈ pendingBelow bound installed := by
  simp [pendingBelow,List.mem_range,Nat.lt_succ_iff,small,fresh]

/-- Each successful installation removes the selected key from this finite
    waiting set. No iteration cap, JVM type or full field suffix is consulted. -/
theorem selected_key_is_not_pending_after_install
    (bound selected : Nat) (installed : List Nat) :
    selected ∉ pendingBelow bound (selected :: installed) := by
  simp [pendingBelow]


theorem installing_a_waiting_priority_strictly_decreases_its_finite_potential
    (bound selected : Nat) (installed : List Nat)
    (small : selected ≤ bound) (fresh : selected ∉ installed) :
    (pendingBelow bound (selected :: installed)).length <
      (pendingBelow bound installed).length := by
  have member := chosen_below_a_waiting_key_is_still_an_uninstalled_witness bound selected installed small fresh
  have shape : pendingBelow bound (selected :: installed) =
      (pendingBelow bound installed).filter (fun k => k != selected) := by
    simp only [pendingBelow,List.filter_filter,List.contains_cons,Bool.not_or]
    rfl
  rw [shape]
  have le := List.length_filter_le (fun k => k != selected) (pendingBelow bound installed)
  have ne : ((pendingBelow bound installed).filter (fun k => k != selected)).length ≠
      (pendingBelow bound installed).length := by
    intro eq
    have holds := (List.length_filter_eq_length_iff.mp eq) selected member
    simp at holds
  omega

/-- A stream of successful splits chosen at or below k cannot continue longer
    than its finite waiting set. Apply this while a fixed loss stays offered. -/
theorem no_infinite_stream_of_strict_potential_decreases
    (potential : Nat → Nat) (decreases : ∀ n, potential (n+1) < potential n) : False := by
  have bound : ∀ n, potential n + n ≤ potential 0 := by
    intro n
    induction n with
    | zero => omega
    | succ n ih => have step := decreases n; omega
  have tooLong := bound (potential 0+1)
  omega

end ProgressiveInputPartition

#print axioms ProgressiveInputPartition.every_word_has_a_constructive_owner
#print axioms ProgressiveInputPartition.a_child_contains_its_point_and_nonempty_remainder
#print axioms ProgressiveInputPartition.delegated_child_never_belongs_to_the_residual
#print axioms ProgressiveInputPartition.complete_child_service_preserves_any_continuation
#print axioms ProgressiveInputPartition.partition_distributes_over_any_transfer
#print axioms ProgressiveInputPartition.refined_cells_preserve_the_complete_paired_exit
#print axioms ProgressiveInputPartition.one_handoff_adds_at_most_one_edge
#print axioms ProgressiveInputPartition.installed_edges_are_never_lost
#print axioms ProgressiveInputPartition.a_fresh_split_strictly_grows_the_plan
#print axioms ProgressiveInputPartition.chosen_below_a_waiting_key_is_still_an_uninstalled_witness
#print axioms ProgressiveInputPartition.selected_key_is_not_pending_after_install

#print axioms ProgressiveInputPartition.installing_a_waiting_priority_strictly_decreases_its_finite_potential
#print axioms ProgressiveInputPartition.no_infinite_stream_of_strict_potential_decreases

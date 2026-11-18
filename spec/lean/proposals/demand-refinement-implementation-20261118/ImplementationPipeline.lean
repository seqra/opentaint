import Std

namespace ImplementationPipeline

structure Pair where
  entry : Nat
  exit : Nat
  exitDepth : Nat
  deriving DecidableEq

def cap (global : Nat) (row : Pair) : Nat :=
  min global (row.exitDepth + 1)

-- The chosen operator has already selected a leaf for this particular row.
-- Keep the full original in the publication, including when one arm qualified.
structure Publication (Leaf : Type) where
  original : List Nat
  row : Pair
  leaf : Leaf
  deriving DecidableEq

def publish (global : Nat) (accepts : Nat → Nat → Bool)
    (select : Nat → Raw → Option Leaf) (cut : Nat → Leaf → Leaf)
    (rows : List Pair) (original : List Nat) (rawLeaves : List Raw) :
    List (Publication Leaf) :=
  rows.flatMap fun row =>
    if original.any (accepts row.entry) then
      rawLeaves.filterMap fun raw =>
        (select row.exit raw).map fun leaf => ⟨original, row, cut (cap global row) leaf⟩
    else []

theorem a_published_leaf_has_one_complete_row_and_original
    (accepts : Nat → Nat → Bool) (select : Nat → Raw → Option Leaf)
    (cut : Nat → Leaf → Leaf) (result : Publication Leaf) :
    result ∈ publish global accepts select cut rows original rawLeaves ↔
      ∃ row ∈ rows, ∃ member ∈ original, ∃ raw ∈ rawLeaves, ∃ leaf,
        accepts row.entry member = true ∧ select row.exit raw = some leaf ∧
        result = ⟨original, row, cut (cap global row) leaf⟩ := by
  rw [publish, List.mem_flatMap]
  constructor
  · rintro ⟨row, rowMember, published⟩
    split at published
    next hit =>
      rcases List.any_eq_true.mp hit with ⟨member, memberIn, matched⟩
      rcases List.mem_filterMap.mp published with ⟨raw, rawIn, served⟩
      cases selected : select row.exit raw with
      | none => simp [selected] at served
      | some leaf =>
        simp [selected] at served
        exact ⟨row, rowMember, member, memberIn, raw, rawIn, leaf, matched,
          selected, served.symm⟩
    next _ => simp at published
  · rintro ⟨row, rowMember, member, memberIn, raw, rawIn, leaf, matched, selected, rfl⟩
    refine ⟨row, rowMember, ?_⟩
    have hit : original.any (accepts row.entry) = true :=
      List.any_eq_true.mpr ⟨member, memberIn, matched⟩
    simp only [hit, ite_true]
    exact List.mem_filterMap.mpr ⟨raw, rawIn, by simp [selected]⟩

theorem the_publication_budget_uses_the_chosen_exit_only
    (accepts : Nat → Nat → Bool) (select : Nat → Raw → Option Leaf)
    (cut : Nat → Leaf → Leaf) (depth : Leaf → Nat)
    (bounded : ∀ budget leaf, depth (cut budget leaf) ≤ budget)
    (result : Publication Leaf)
    (mem : result ∈ publish global accepts select cut rows original rawLeaves) :
    depth result.leaf ≤ global ∧ depth result.leaf ≤ result.row.exitDepth + 1 := by
  obtain ⟨row, _, _, _, _, _, leaf, _, _, rfl⟩ :=
    (a_published_leaf_has_one_complete_row_and_original accepts select cut result).mp mem
  exact ⟨Nat.le_trans (bounded (cap global row) leaf) (Nat.min_le_left ..),
    Nat.le_trans (bounded (cap global row) leaf) (Nat.min_le_right ..)⟩

-- Qualifiers are local keys on a public row, checked independently of AP
-- equality. This model compares memberships, so list order is immaterial.
def delta [DecidableEq A] (old offered : List A) : List A :=
  offered.filter fun key => decide (key ∉ old)

theorem exact_memberships_after_qualified_delivery [DecidableEq A]
    (old offered : List A) (key : A) :
    key ∈ old ++ delta old offered ↔ key ∈ old ∨ key ∈ offered := by
  by_cases h : key ∈ old <;> simp [delta, h]

theorem qualifier_arrival_order_keeps_the_same_final_memberships [DecidableEq A]
    (first second : List A) (key : A) :
    key ∈ first ++ delta first second ↔ key ∈ second ++ delta second first := by
  rw [exact_memberships_after_qualified_delivery, exact_memberships_after_qualified_delivery, or_comm]

theorem an_existing_public_row_does_not_hide_a_new_qualifier
    (row first second : Nat) (different : second ≠ first) :
    (row, second) ∈ delta [(row, first)] [(row, second)] := by
  simp [delta, different]

end ImplementationPipeline

import RoutedCalls

/- Concrete positive unary prefix semantics. The normal reader may consume
   many fields: the prepared first child need not already solve that reader. -/
namespace SavedReplayChildCover
open NonEmptyPolicy NonEmptyRestriction
abbrev Word := List Nat

def step (read write input : Word) : Option Word :=
  (dropHead read input).map (write ++ ·)

theorem cancel_common_prefix (head read input : Word) :
    dropHead (head ++ read) (head ++ input) = dropHead read input := by
  induction head with
  | nil => rfl
  | cons field head ih => simpa [dropHead] using ih

theorem consume_named_child (head : Word) (field : Nat) (rest write suffix : Word) :
    step (head ++ field :: rest) write (head ++ field :: suffix) = step rest write suffix := by
  simp [step,cancel_common_prefix,dropHead]

theorem successful_read_requires_the_first_unknown_child
    (head : Word) (field : Nat) (rest write suffix result : Word)
    (hit : step (head ++ field :: rest) write (head ++ suffix) = some result) :
    ∃ childSuffix, suffix = field :: childSuffix := by
  simp only [step,cancel_common_prefix] at hit
  cases suffix with
  | nil => simp [dropHead] at hit
  | cons f tail =>
    by_cases equal : field = f
    · subst f; exact ⟨tail,rfl⟩
    · simp [dropHead,equal] at hit

def observed (initial current read write input output : Word) : Prop :=
  ∃ suffix, input = initial ++ suffix ∧ step read write (current ++ suffix) = some output

theorem the_child_covers_the_whole_normal_reader_contribution
    (initial current : Word) (field : Nat) (rest write input output : Word) :
    observed initial current (current ++ field :: rest) write input output ↔
      observed (initial ++ [field]) (current ++ [field])
        (current ++ field :: rest) write input output := by
  constructor
  · rintro ⟨suffix,eq,hit⟩
    obtain ⟨tail,rfl⟩ := successful_read_requires_the_first_unknown_child current field rest write suffix output hit
    exact ⟨tail,by simpa [List.append_assoc] using eq,by simpa [List.append_assoc] using hit⟩
  · rintro ⟨suffix,eq,hit⟩
    exact ⟨field :: suffix,by simpa [List.append_assoc] using eq,by simpa [List.append_assoc] using hit⟩

/-- A first child whose remaining suffix is empty and one whose suffix is
    nonempty are both necessary. This is why a STAR-only child is insufficient. -/
theorem child_point_and_suffix_are_constructively_complete (suffix : Word) :
    suffix = [] ∨ ∃ first rest, suffix = first :: rest := by
  cases suffix with
  | nil => exact Or.inl rfl
  | cons first rest => exact Or.inr ⟨first,rest,rfl⟩

/-- Output permission remains the SAME original selector. Neither this cover
    nor the NORMAL record is a reason to borrow another row's paired exit. -/
theorem cover_survives_any_fixed_paired_output_selector
    (initial current : Word) (field : Nat) (rest write input output : Word)
    (allowed : Word → Prop) :
    (observed initial current (current ++ field :: rest) write input output ∧ allowed output) ↔
      (observed (initial ++ [field]) (current ++ [field])
        (current ++ field :: rest) write input output ∧ allowed output) := by
  exact and_congr (the_child_covers_the_whole_normal_reader_contribution initial current field rest write input output) Iff.rfl

/-- The suffix behind the first child can be arbitrarily long. Coverage does
    not assume a completed child summary, a transparent method or a full guard
    admitted at method entry. -/
theorem arbitrary_remaining_reader_is_covered (rest : Word) :
    step ([1] ++ 2 :: rest) [] ([1] ++ 2 :: rest) = some [] := by
  simp [step,dropHead]
  induction rest with
  | nil => rfl
  | cons h rest ih => simpa [dropHead] using ih

end SavedReplayChildCover

#print axioms SavedReplayChildCover.cancel_common_prefix
#print axioms SavedReplayChildCover.consume_named_child
#print axioms SavedReplayChildCover.successful_read_requires_the_first_unknown_child
#print axioms SavedReplayChildCover.the_child_covers_the_whole_normal_reader_contribution
#print axioms SavedReplayChildCover.child_point_and_suffix_are_constructively_complete
#print axioms SavedReplayChildCover.cover_survives_any_fixed_paired_output_selector
#print axioms SavedReplayChildCover.arbitrary_remaining_reader_is_covered

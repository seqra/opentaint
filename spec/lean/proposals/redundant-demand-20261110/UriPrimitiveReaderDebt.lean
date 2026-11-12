import Std

namespace UriPrimitiveReaderDebt
/- Primitive whole-word readers, not a proof of arbitrary store provenance.
   Symbols are counted nonstatic fields; field exclusions are empty; mark=FLOW. -/
def same : List Nat → List Nat → Bool
  | [], [] => true
  | x::xs, y::ys => Nat.beq x y && same xs ys
  | _, _ => false
private theorem same_self (p : List Nat) : same p p = true := by
  induction p with
  | nil => rfl
  | cons x xs ih => simp only [same, Nat.beq_refl, Bool.true_and, ih]
def prefixB (p q : List Nat) : Bool := same p (q.take p.length)
inductive Debt where
  | normal (readWord : List Nat)
  | may (inputPrefix : List Nat)
  deriving DecidableEq, Repr
/- Reverse a normal whole-word read; cut the growing result at the field cap.
   Native paired restriction and demand provenance are separate obligations. -/
def generated (budget : Nat) (readWord : List Nat) : Debt :=
  if readWord.length <= budget then .normal readWord
  else .may (readWord.take budget)
def mayStart (inputPrefix actual : List Nat) : Option (List Nat) :=
  if prefixB inputPrefix actual then some (actual.take (inputPrefix.length + 1)) else none
def normalReplay (readWord actual : List Nat) : Option (List Nat) :=
  if prefixB readWord actual then some (actual.drop readWord.length) else none
def resolve (debt : Debt) (actual : List Nat) : Option (List Nat) :=
  match debt with
  | .normal word => normalReplay word actual
  | .may word => mayStart word actual

theorem word_is_prefix (word suffix : List Nat) :
    prefixB word (word ++ suffix) = true := by simp only [prefixB, List.take_left, same_self]
theorem open_prefix_is_prefix (word suffix : List Nat) (budget : Nat)
    (h : budget <= word.length) :
    prefixB (word.take budget) (word ++ suffix) = true := by
  simp only [prefixB, List.length_take, Nat.min_eq_left h]
  rw [List.take_append_of_le_length h]
  exact same_self _

theorem known_reader_replays (word suffix : List Nat) :
    normalReplay word (word ++ suffix) = some suffix := by
  simp [normalReplay, word_is_prefix]
theorem unknown_reader_has_open_query (word : List Nat) (budget : Nat)
    (h : budget < word.length) :
    generated budget word = .may (word.take budget) := by
  simp [generated, Nat.not_le_of_lt h]
theorem known_reader_has_native_relation (word : List Nat) (budget : Nat)
    (h : word.length <= budget) :
    generated budget word = .normal word := by simp [generated, h]
theorem unknown_reader_admits_refinement (word suffix : List Nat) (budget : Nat)
    (h : budget < word.length) :
    resolve (generated budget word) (word ++ suffix) =
      some ((word ++ suffix).take (budget + 1)) := by
  rw [unknown_reader_has_open_query word budget h]
  simp only [resolve, mayStart, open_prefix_is_prefix word suffix budget (Nat.le_of_lt h),
    if_true, List.length_take, Nat.min_eq_left (Nat.le_of_lt h)]
theorem generated_debt_has_executable_continuation (word suffix : List Nat) (budget : Nat) :
    (resolve (generated budget word) (word ++ suffix)).isSome = true := by
  by_cases h : word.length <= budget
  · rw [known_reader_has_native_relation word budget h]
    simp [resolve, known_reader_replays]
  · rw [unknown_reader_admits_refinement word suffix budget (Nat.lt_of_not_ge h)]
    rfl
/- Arbitrary STAR-only state need not satisfy this generated lineage. -/
def c2Star (entry actual : List Nat) : Bool := same entry actual
theorem star_entry_rejects_strict_child (field : Nat) :
    c2Star [] [field] = false := by rfl
theorem open_query_still_emits_first_field (field : Nat) :
    mayStart [] [field] = some [field] := by rfl
end UriPrimitiveReaderDebt
#print axioms UriPrimitiveReaderDebt.word_is_prefix
#print axioms UriPrimitiveReaderDebt.open_prefix_is_prefix
#print axioms UriPrimitiveReaderDebt.known_reader_replays
#print axioms UriPrimitiveReaderDebt.unknown_reader_has_open_query
#print axioms UriPrimitiveReaderDebt.known_reader_has_native_relation
#print axioms UriPrimitiveReaderDebt.unknown_reader_admits_refinement
#print axioms UriPrimitiveReaderDebt.generated_debt_has_executable_continuation
#print axioms UriPrimitiveReaderDebt.star_entry_rejects_strict_child
#print axioms UriPrimitiveReaderDebt.open_query_still_emits_first_field

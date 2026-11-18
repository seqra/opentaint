import ChildCover
import ExclusionRoutedCalls

/- Concrete suffix membership with the real field exclusions at their
   native scopes. No E is copied from a parent scope to a child scope. -/
namespace ExclusionChildCover
open NonEmptyPolicy NonEmptyRestriction SavedReplayChildCover
abbrev Word := List Nat

def permits (excluded : List Nat) : Word → Bool
  | [] => true
  | first :: _ => !excluded.contains first

def parent (initial current : Word) (field : Nat) (rest write : Word)
    (operandE premiseE resultE : List Nat) (input output : Word) : Prop :=
  ∃ suffix residual,
    input = initial ++ suffix ∧ permits operandE suffix = true ∧
    dropHead (current ++ field :: rest) (current ++ suffix) = some residual ∧
    permits premiseE residual = true ∧ permits resultE residual = true ∧
    output = write ++ residual

def child (initial current : Word) (field : Nat) (rest write : Word)
    (operandE premiseE resultE : List Nat) (input output : Word) : Prop :=
  ∃ suffix residual,
    input = (initial ++ [field]) ++ suffix ∧ permits operandE (field :: suffix) = true ∧
    dropHead (current ++ field :: rest) ((current ++ [field]) ++ suffix) = some residual ∧
    permits premiseE residual = true ∧ permits resultE residual = true ∧
    output = write ++ residual

/-- Arbitrary real exclusions only filter successful concrete witnesses.
    Every successful reader still needs the selected first field. -/
theorem complete_child_cover_with_arbitrary_real_exclusions
    (initial current : Word) (field : Nat) (rest write : Word)
    (operandE premiseE resultE : List Nat) (input output : Word) :
    parent initial current field rest write operandE premiseE resultE input output ↔
      child initial current field rest write operandE premiseE resultE input output := by
  constructor
  · rintro ⟨suffix,residual,eq,operand,read,premise,result,out⟩
    have plain : step (current ++ field :: rest) write (current ++ suffix) = some (write ++ residual) := by
      simp only [step,read,Option.map_some]
    obtain ⟨tail,rfl⟩ := successful_read_requires_the_first_unknown_child current field rest write suffix (write ++ residual) plain
    refine ⟨tail,residual,?_,operand,?_,premise,result,out⟩
    · simpa only [List.append_assoc,List.singleton_append] using eq
    · simpa only [List.append_assoc,List.singleton_append] using read
  · rintro ⟨suffix,residual,eq,operand,read,premise,result,out⟩
    refine ⟨field :: suffix,residual,?_,operand,?_,premise,result,out⟩
    · simpa only [List.append_assoc,List.singleton_append] using eq
    · simpa only [List.append_assoc,List.singleton_append] using read

/-- An exclusion of the chosen field makes this particular contribution
    empty; it is not a reason to widen, clear E, or invent another field. -/
theorem excluded_first_field_has_no_concrete_parent_contribution
    (initial current : Word) (field : Nat) (rest write : Word)
    (operandE premiseE resultE : List Nat) (input output : Word)
    (blocked : operandE.contains field = true) :
    ¬ parent initial current field rest write operandE premiseE resultE input output := by
  intro hit
  obtain ⟨suffix,residual,_,allowed,_,_,_,_⟩ :=
    (complete_child_cover_with_arbitrary_real_exclusions initial current field rest write
      operandE premiseE resultE input output).mp hit
  simp only [permits,blocked,Bool.not_true,Bool.false_eq_true] at allowed

/-- Same original paired Dp, marks, ports, context and literal protection
    are arbitrary fixed filters on the witnessed output, not new permissions. -/
theorem coverage_preserves_any_fixed_qualified_output_service
    (initial current : Word) (field : Nat) (rest write : Word)
    (operandE premiseE resultE : List Nat) (input output : Word)
    (allowed : Word → Prop) :
    (parent initial current field rest write operandE premiseE resultE input output ∧ allowed output) ↔
      (child initial current field rest write operandE premiseE resultE input output ∧ allowed output) :=
  and_congr (complete_child_cover_with_arbitrary_real_exclusions initial current field rest write
    operandE premiseE resultE input output) Iff.rfl

theorem exact_and_nonempty_child_are_constructively_complete (suffix : Word) :
    suffix = [] ∨ ∃ first rest, suffix = first :: rest :=
  child_point_and_suffix_are_constructively_complete suffix

/-- A real field cut does not discard the selected child's concrete suffix.
    The remaining forgotten word is nonempty, even with an exact old tail. -/
theorem truncation_keeps_every_concrete_extension
    (kept : Word) (first : Nat) (rest suffix : Word) :
    NonEmptyMay.rooted kept .nonEmpty (kept ++ (first :: rest) ++ suffix) :=
  NonEmptyMay.real_cut_is_nonempty kept first rest suffix

/-- E stays at its original scope. Excluding g at p does not exclude g at
    p.f after selecting f != g. -/
theorem first_field_outside_exclusion_allows_every_child_suffix
    (excluded : List Nat) (field : Nat) (suffix : Word)
    (outside : excluded.contains field = false) :
    permits excluded (field :: suffix) = true := by
  simp only [permits,outside,Bool.not_false]
end ExclusionChildCover
#print axioms ExclusionChildCover.complete_child_cover_with_arbitrary_real_exclusions
#print axioms ExclusionChildCover.excluded_first_field_has_no_concrete_parent_contribution
#print axioms ExclusionChildCover.coverage_preserves_any_fixed_qualified_output_service
#print axioms ExclusionChildCover.exact_and_nonempty_child_are_constructively_complete
#print axioms ExclusionChildCover.truncation_keeps_every_concrete_extension
#print axioms ExclusionChildCover.first_field_outside_exclusion_allows_every_child_suffix

import Std

namespace TruncationEvidence

abbrev Path := List Nat

structure Suffix where
  path : Path
  openTail : Bool
  deriving DecidableEq, Repr

def accepts (p : Suffix) (w : Path) : Prop :=
  w = p.path ∨ (p.openTail = true ∧ ∃ rest, w = p.path ++ rest)

-- none is unknown, not an empty set of witnesses.
abbrev Evidence := Option (List Suffix)

def denotes : Evidence → Path → Prop
  | none, _ => True
  | some ps, w => ∃ p ∈ ps, accepts p w

def mayEmpty : Evidence → Bool
  | none => true
  | some ps => ps.any (fun p => p.path.isEmpty)

def merge : Evidence → Evidence → Evidence
  | some a, some b => some (a ++ b)
  | _, _ => none

theorem accepts_empty (p : Suffix) : accepts p [] ↔ p.path = [] := by
  constructor
  · intro h
    rcases h with same | ⟨_, rest, same⟩
    · exact same.symm
    · exact (List.append_eq_nil_iff.mp same.symm).1
  · intro h
    exact Or.inl h.symm

theorem mayEmpty_exact (e : Evidence) : mayEmpty e = true ↔ denotes e [] := by
  cases e with
  | none => simp [mayEmpty, denotes]
  | some ps =>
    simp only [mayEmpty, denotes, List.any_eq_true]
    constructor
    · rintro ⟨p, hp, he⟩
      exact ⟨p, hp, (accepts_empty p).mpr (List.isEmpty_iff.mp he)⟩
    · rintro ⟨p, hp, he⟩
      exact ⟨p, hp, List.isEmpty_iff.mpr ((accepts_empty p).mp he)⟩

theorem merge_denotes (a b : Evidence) (w : Path) :
    denotes (merge a b) w ↔ denotes a w ∨ denotes b w := by
  cases a <;> cases b <;> simp [merge, denotes, List.mem_append, or_and_right,
    exists_or]

theorem merge_empty (a b : Evidence) :
    mayEmpty (merge a b) = (mayEmpty a || mayEmpty b) := by
  cases a <;> cases b <;> simp [merge, mayEmpty, List.any_append]

-- Completeness is an explicit obligation on the capture adapter. This
-- theorem does not assume that an observed sample is complete.
def Complete (e : Evidence) (actual : Path → Prop) : Prop :=
  ∀ w, actual w → denotes e w

theorem reject_exact_empty (e : Evidence) (actual : Path → Prop)
    (complete : Complete e actual) (nonempty : mayEmpty e = false) :
    ¬ actual [] := by
  intro h
  have he := (mayEmpty_exact e).mpr (complete [] h)
  simp [nonempty] at he

-- A real field cut removes at least one concrete accessor. Every binding
-- of its old tail still starts with that accessor.
theorem lost_field_excludes_empty (field : Nat) (rest : Path) (tail : Bool) :
    ¬ accepts ⟨field :: rest, tail⟩ [] := by
  intro h
  have := (accepts_empty ⟨field :: rest, tail⟩).mp h
  cases this

def sampleEvidence : Evidence := some [⟨[1, 2], true⟩, ⟨[3, 4], true⟩]

theorem example_no_empty : mayEmpty sampleEvidence = false := by decide
theorem example_deeper : denotes sampleEvidence [1, 2] := by
  exact ⟨⟨[1, 2], true⟩, by simp, Or.inl rfl⟩

-- A STAR with an empty concrete chain is a symbolic frame. It can bind
-- a NONempty suffix. It is not the singleton exact position [].
def bindStar (start suffix : Path) : Path := start ++ suffix

theorem star_root_has_relevant_binding :
    ∃ suffix, suffix ≠ [] ∧ denotes sampleEvidence (bindStar [] suffix) := by
  exact ⟨[1, 2], by decide, example_deeper⟩

def emptyChainFilter (e : Evidence) (known : Path) : Bool :=
  mayEmpty e || !known.isEmpty

theorem rejecting_star_by_known_chain_is_not_binding_safe :
    emptyChainFilter sampleEvidence [] = false ∧
    ∃ suffix, denotes sampleEvidence (bindStar [] suffix) := by
  exact ⟨by decide, [1, 2], example_deeper⟩

theorem deeper_star_can_match :
    ∃ suffix, denotes sampleEvidence (bindStar [1] suffix) := by
  exact ⟨[2], example_deeper⟩

theorem unrelated_field_has_no_binding (tail : Path) :
    ¬ denotes sampleEvidence (9 :: tail) := by
  rintro ⟨p, hp, h⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with same | same
  · subst p
    rcases h with h | ⟨_, _, h⟩ <;> cases h
  · subst p
    rcases h with h | ⟨_, _, h⟩ <;> cases h

-- Dropping a known prefix does not justify discarding suffixes. A wrapper
-- which receives only MAY (and no evidence) must report unknown.
theorem unpropagated_is_unknown : mayEmpty (none : Evidence) = true := rfl
theorem unknown_absorbs (e : Evidence) : merge e none = none := by
  cases e <;> rfl

#print axioms mayEmpty_exact
#print axioms merge_denotes
#print axioms merge_empty
#print axioms reject_exact_empty
#print axioms lost_field_excludes_empty
#print axioms star_root_has_relevant_binding
#print axioms rejecting_star_by_known_chain_is_not_binding_safe
#print axioms deeper_star_can_match
#print axioms unrelated_field_has_no_binding
end TruncationEvidence

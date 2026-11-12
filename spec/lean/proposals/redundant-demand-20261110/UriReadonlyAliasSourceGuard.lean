import Std

namespace UriReadonlyAliasSourceGuard
/- A position denotes actual positive input storage, not a DSU may-object.
   Payload is opaque. Source/GEN actions are outside this nonzero FLOW lane. -/
structure Positive where
  cell : Nat
  word : List Nat
  payload : Nat
  deriving DecidableEq, Repr
abbrev State := List Positive

/- A source adapter must classify every positive primitive event. Value
   copies into fresh storage remain enabled. Real reference binding is keep;
   an already present positive may be emitted again. Deletions are allowed. -/
inductive Step (entryCells : List Nat) : State → State → Prop
  | keep (old : State) : Step entryCells old old
  | erase (old next : State) (subset : ∀ p, p ∈ next → p ∈ old) : Step entryCells old next
  | duplicate (old : State) (p : Positive) (existing : p ∈ old) : Step entryCells old (p :: old)
  | freshCopy (old : State) (p : Positive) (fresh : p.cell ∉ entryCells) : Step entryCells old (p :: old)

inductive Run (entryCells : List Nat) (entry : State) : State → Prop
  | entry : Run entryCells entry entry
  | next (old new : State) (before : Run entryCells entry old) (step : Step entryCells old new) :
      Run entryCells entry new

theorem step_creates_no_protected_positive (entryCells : List Nat) (old next : State)
    (step : Step entryCells old next) (p : Positive) (cell : p.cell ∈ entryCells)
    (present : p ∈ next) : p ∈ old := by
  cases step with
  | keep => exact present
  | erase next subset => exact subset p present
  | duplicate q existing =>
    rcases List.mem_cons.mp present with equal | earlier
    · simpa [equal] using existing
    · exact earlier
  | freshCopy q fresh =>
    rcases List.mem_cons.mp present with equal | earlier
    · subst q
      exact False.elim (fresh cell)
    · exact earlier

theorem run_creates_no_protected_positive (entryCells : List Nat) (entry now : State)
    (run : Run entryCells entry now) (p : Positive) (cell : p.cell ∈ entryCells)
    (present : p ∈ now) : p ∈ entry := by
  induction run with
  | entry => exact present
  | next old new before step ih =>
    exact ih (step_creates_no_protected_positive entryCells old new step p cell present)

/- A genuine reference equality preserves the entire word. It cannot turn a
   copied value in a fresh builder or Replacement field into an input write. -/
theorem genuine_alias_is_entry_covered (entryCells : List Nat) (entry now : State)
    (run : Run entryCells entry now) (source target : Nat) (word : List Nat) (payload : Nat)
    (protectedTarget : target ∈ entryCells) (sameReference : source = target)
    (positive : Positive.mk source word payload ∈ now) : Positive.mk target word payload ∈ entry := by
  subst source
  exact run_creates_no_protected_positive entryCells entry now run _ protectedTarget positive

theorem fresh_copy_has_no_protected_reference (entryCells : List Nat) (fresh target : Nat)
    (newStorage : fresh ∉ entryCells) (oldStorage : target ∈ entryCells) : fresh ≠ target := by
  intro same
  subst fresh
  exact newStorage oldStorage

/- Caller entry aliases remain arbitrary. Equal entryCells input references
   already denote the same positive; this theorem does not add a runtime cache. -/
theorem equal_entry_references_share_positive (entry : State) (a b : Nat) (word : List Nat) (payload : Nat)
    (sameReference : a = b) (present : Positive.mk a word payload ∈ entry) :
    Positive.mk b word payload ∈ entry := by
  subst a
  exact present

theorem new_feedback_needs_a_non_genuine_reference (entryCells : List Nat) (entry now : State)
    (run : Run entryCells entry now) (source target : Nat) (word : List Nat) (payload : Nat)
    (protectedTarget : target ∈ entryCells) (positive : Positive.mk source word payload ∈ now)
    (notAtEntry : Positive.mk target word payload ∉ entry) : source ≠ target := by
  intro same
  exact notAtEntry (genuine_alias_is_entry_covered entryCells entry now run source target word payload
    protectedTarget same positive)

/- An ordinary new write to entryCells storage is outside the guard. -/
example : ¬ Step [0] [] [⟨0,[],1⟩] := by
  intro step
  have impossible := step_creates_no_protected_positive [0] [] [⟨0,[],1⟩] step
    ⟨0,[],1⟩ (by simp) (by simp)
  simp at impossible
end UriReadonlyAliasSourceGuard
#print axioms UriReadonlyAliasSourceGuard.step_creates_no_protected_positive
#print axioms UriReadonlyAliasSourceGuard.run_creates_no_protected_positive
#print axioms UriReadonlyAliasSourceGuard.genuine_alias_is_entry_covered
#print axioms UriReadonlyAliasSourceGuard.fresh_copy_has_no_protected_reference
#print axioms UriReadonlyAliasSourceGuard.equal_entry_references_share_positive
#print axioms UriReadonlyAliasSourceGuard.new_feedback_needs_a_non_genuine_reference

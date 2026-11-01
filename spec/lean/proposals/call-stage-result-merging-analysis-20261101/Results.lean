import Keys

/-!
A finite reference collection. Its list lookup is executable but is not a
complexity model of Kotlin LinkedHashMap. Only equal full keys can join.
-/
namespace CallStageMerge
set_option autoImplicit false

/-- The first occurrence keeps its position; protection is a monotone value. -/
def insert (incoming : Row) : List Row → List Row
  | [] => [incoming]
  | old :: rest => if incoming.key = old.key
      then joinRows old incoming :: rest
      else old :: insert incoming rest

def observe : List Row → Observation → Bool
  | [], _ => false
  | row :: rest, observation => rowObservation row observation || observe rest observation

def collect : List Row → List Row → List Row
  | [], stored => stored
  | row :: rest, stored => collect rest (insert row stored)

def normalize (rows : List Row) : List Row := collect rows []

theorem insert_observation (incoming : Row) (rows : List Row) (observation : Observation) :
    observe (insert incoming rows) observation =
      (observe rows observation || rowObservation incoming observation) := by
  induction rows with
  | nil => simp [insert, observe]
  | cons old rest ih =>
    by_cases same : incoming.key = old.key
    · simp only [insert, if_pos same, observe]
      rw [joined_observation old incoming same.symm]
      exact bool_shuffle_right _ _ _
    · simp only [insert, if_neg same, observe]
      rw [ih]
      exact bool_associate _ _ _

theorem collect_observation (rows stored : List Row) (observation : Observation) :
    observe (collect rows stored) observation =
      (observe stored observation || observe rows observation) := by
  induction rows generalizing stored with
  | nil => simp [collect, observe]
  | cons row rest ih =>
    rw [collect, ih, insert_observation]
    simp only [observe]
    exact (bool_associate _ _ _).symm

theorem normalize_observation (rows : List Row) (observation : Observation) :
    observe (normalize rows) observation = observe rows observation := by
  simpa [normalize, observe] using collect_observation rows [] observation

def ordinaryMember (rows : List Row) (key : Key) (slot : Slot) : Prop :=
  observe rows ⟨key, slot, false⟩ = true

def protectedMember (rows : List Row) (key : Key) (slot : Slot) : Prop :=
  observe rows ⟨key, slot, true⟩ = true

theorem ordinary_membership_preserved (rows : List Row) (key : Key) (slot : Slot) :
    ordinaryMember (normalize rows) key slot ↔ ordinaryMember rows key slot := by
  simp only [ordinaryMember, normalize_observation]

theorem protected_membership_preserved (rows : List Row) (key : Key) (slot : Slot) :
    protectedMember (normalize rows) key slot ↔ protectedMember rows key slot := by
  simp only [protectedMember, normalize_observation]

def plain (key : Key) : Row := ⟨key, Bits.zero⟩

theorem plain_protected_observation (key query : Key) (slot : Slot) :
    rowObservation (plain key) ⟨query, slot, true⟩ = false := by
  simp [rowObservation, plain, Bits.zero_test]

theorem unprotected_duplicate_cannot_clear_protection (key query : Key)
    (rows : List Row) (slot : Slot) :
    observe (insert (plain key) rows) ⟨query, slot, true⟩ =
      observe rows ⟨query, slot, true⟩ := by
  rw [insert_observation, plain_protected_observation]
  simp

theorem protected_input_is_retained (incoming : Row) (rows : List Row) (observation : Observation)
    (present : rowObservation incoming observation = true) :
    observe (insert incoming rows) observation = true := by
  rw [insert_observation, present]
  simp

theorem existing_protection_is_retained (incoming : Row) (rows : List Row) (observation : Observation)
    (present : observe rows observation = true) :
    observe (insert incoming rows) observation = true := by
  rw [insert_observation, present]
  rfl

theorem different_full_mark_cannot_replace (incoming : Row) (rows : List Row)
    (key : Key) (slot : Slot) (flagged : Bool)
    (different : incoming.key.payload.mark ≠ key.payload.mark) :
    observe (insert incoming rows) ⟨key, slot, flagged⟩ =
      observe rows ⟨key, slot, flagged⟩ := by
  have unequal : incoming.key ≠ key := fun same =>
    different (congrArg (fun k : Key => k.payload.mark) same)
  rw [insert_observation]
  simp [rowObservation, unequal]

theorem different_fact_kind_cannot_replace (incoming : Row) (rows : List Row)
    (key : Key) (slot : Slot) (flagged : Bool)
    (different : incoming.key.payload.kind ≠ key.payload.kind) :
    observe (insert incoming rows) ⟨key, slot, flagged⟩ =
      observe rows ⟨key, slot, flagged⟩ := by
  have unequal : incoming.key ≠ key := fun same =>
    different (congrArg (fun k : Key => k.payload.kind) same)
  rw [insert_observation]
  simp [rowObservation, unequal]

theorem different_complete_scope_cannot_replace (incoming : Row) (rows : List Row)
    (key : Key) (slot : Slot) (flagged : Bool)
    (different : incoming.key.scope ≠ key.scope) :
    observe (insert incoming rows) ⟨key, slot, flagged⟩ =
      observe rows ⟨key, slot, flagged⟩ := by
  have unequal : incoming.key ≠ key := fun same =>
    different (congrArg (fun k : Key => k.scope) same)
  rw [insert_observation]
  simp [rowObservation, unequal]

end CallStageMerge

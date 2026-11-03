import Std

namespace ScopedRequestClimbs

/- Only immutable transport coordinates are modeled. Slot matching is supplied unchanged. -/
inductive Scope where
  | root
  | block (blockId entryPort : Nat)
  deriving DecidableEq, Repr

structure Owner where
  method : Nat
  scope : Scope
  deriving DecidableEq, Repr

structure Slot where
  base : Nat
  fields : List Nat
  tail : Nat
  deriving DecidableEq, Repr

structure Key where
  owner : Owner
  slot : Slot
  deriving DecidableEq, Repr

structure Request where
  key : Key
  mark : Nat
  deriving DecidableEq, Repr

structure Row where
  slot : Slot
  marks : List Nat
  deriving DecidableEq, Repr

structure Event where
  owner : Owner
  rows : List Row
  deriving DecidableEq, Repr

def insert {α : Type} [DecidableEq α] (x : α) (xs : List α) : List α :=
  if x ∈ xs then xs else x :: xs

theorem mem_insert {α : Type} [DecidableEq α] (x y : α) (xs : List α) :
    y ∈ insert x xs ↔ y = x ∨ y ∈ xs := by
  unfold insert
  split <;> simp_all [List.mem_cons]

def unique {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | x :: xs => insert x (unique xs)

theorem mem_unique {α : Type} [DecidableEq α] (x : α) (xs : List α) :
    x ∈ unique xs ↔ x ∈ xs := by
  induction xs with
  | nil => simp [unique]
  | cons y ys ih => simp only [unique, mem_insert, List.mem_cons, ih]

def marksAt (rows : List Row) (slot : Slot) : List Nat :=
  rows.flatMap fun row => if row.slot = slot then row.marks else []

def addRow (rows : List Row) (slot : Slot) (mark : Nat) : List Row :=
  match rows with
  | [] => [{ slot, marks := [mark] }]
  | row :: rest =>
      if row.slot = slot then { row with marks := insert mark row.marks } :: rest
      else row :: addRow rest slot mark

theorem mem_marksAt_cons (r : Row) (rs : List Row) (s : Slot) (m : Nat) :
    m ∈ marksAt (r :: rs) s ↔ (r.slot = s ∧ m ∈ r.marks) ∨ m ∈ marksAt rs s := by
  simp only [marksAt, List.flatMap_cons, List.mem_append]
  split <;> simp_all

theorem addRow_membership (rows : List Row) (slot query : Slot) (mark value : Nat) :
    value ∈ marksAt (addRow rows slot mark) query ↔
      (query = slot ∧ value = mark) ∨ value ∈ marksAt rows query := by
  induction rows with
  | nil => simp [addRow, marksAt, eq_comm]
  | cons row rest ih =>
      simp only [addRow]
      split
      next same =>
        simp only [mem_marksAt_cons, mem_insert]
        constructor
        · intro h
          rcases h with ⟨hslot, hvalue | hold⟩ | hrest
          · exact Or.inl ⟨hslot.symm.trans same, hvalue⟩
          · exact Or.inr (Or.inl ⟨hslot, hold⟩)
          · exact Or.inr (Or.inr hrest)
        · intro h
          rcases h with ⟨hslot, hvalue⟩ | ⟨hslot, hold⟩ | hrest
          · exact Or.inl ⟨same.trans hslot.symm, Or.inl hvalue⟩
          · exact Or.inl ⟨hslot, Or.inr hold⟩
          · exact Or.inr hrest
      next different =>
        rw [mem_marksAt_cons, ih, mem_marksAt_cons]
        constructor
        · intro h
          rcases h with hrow | hnew | hrest
          · exact Or.inr (Or.inl hrow)
          · exact Or.inl hnew
          · exact Or.inr (Or.inr hrest)
        · intro h
          rcases h with hnew | hrow | hrest
          · exact Or.inr (Or.inl hnew)
          · exact Or.inl hrow
          · exact Or.inr (Or.inr hrest)

def addForOwner (owner : Owner) (request : Request) (rows : List Row) : List Row :=
  if request.key.owner = owner then addRow rows request.key.slot request.mark else rows

def batchRows (owner : Owner) : List Request → List Row
  | [] => []
  | request :: rest => addForOwner owner request (batchRows owner rest)

theorem batchRows_membership (owner : Owner) (requests : List Request) (slot : Slot) (mark : Nat) :
    mark ∈ marksAt (batchRows owner requests) slot ↔
      ∃ request ∈ requests, request.key.owner = owner ∧ request.key.slot = slot ∧ request.mark = mark := by
  induction requests with
  | nil => simp [batchRows, marksAt]
  | cons request rest ih =>
      unfold batchRows addForOwner
      split
      next same =>
        rw [addRow_membership, ih]
        constructor
        · intro h
          rcases h with ⟨hslot, hmark⟩ | ⟨r, hr, ho, hs, hm⟩
          · exact ⟨request, List.mem_cons_self, same, hslot.symm, hmark.symm⟩
          · exact ⟨r, List.mem_cons_of_mem _ hr, ho, hs, hm⟩
        · rintro ⟨r, hr, ho, hs, hm⟩
          rcases List.mem_cons.mp hr with hr | hr
          · subst r; exact Or.inl ⟨hs.symm, hm.symm⟩
          · exact Or.inr ⟨r, hr, ho, hs, hm⟩
      next different =>
        rw [ih]
        constructor
        · rintro ⟨r, hr, ho, hs, hm⟩
          exact ⟨r, List.mem_cons_of_mem _ hr, ho, hs, hm⟩
        · rintro ⟨r, hr, ho, hs, hm⟩
          rcases List.mem_cons.mp hr with hr | hr
          · subst r; exact False.elim (different ho)
          · exact ⟨r, hr, ho, hs, hm⟩

def owners (requests : List Request) : List Owner := unique (requests.map fun r => r.key.owner)

def batches (requests : List Request) : List Event :=
  (owners requests).map fun owner => { owner, rows := batchRows owner requests }

def delivered (events : List Event) (request : Request) : Prop :=
  ∃ event ∈ events, event.owner = request.key.owner ∧
    request.mark ∈ marksAt event.rows request.key.slot

theorem batching_preserves_every_owner_slot_mark (requests : List Request) (request : Request) :
    delivered (batches requests) request ↔ request ∈ requests := by
  constructor
  · rintro ⟨event, hevent, howner, hmark⟩
    rcases List.mem_map.mp hevent with ⟨owner, hmem, heq⟩
    subst event
    simp only at howner hmark
    rcases (batchRows_membership owner requests request.key.slot request.mark).mp hmark with
      ⟨r, hr, ho, hs, hm⟩
    have hkey : r.key = request.key := by
      cases r with | mk rk rm =>
        cases request with | mk qk qm =>
          cases rk; cases qk; simp_all
    have heq : r = request := by cases r; cases request; simp_all
    simpa only [heq] using hr
  · intro hmem
    refine ⟨{ owner := request.key.owner, rows := batchRows request.key.owner requests }, ?_, rfl, ?_⟩
    · apply List.mem_map.mpr
      refine ⟨request.key.owner, ?_, rfl⟩
      apply (mem_unique _ _).mpr
      exact List.mem_map.mpr ⟨request, hmem, rfl⟩
    · apply (batchRows_membership _ _ _ _).mpr
      exact ⟨request, hmem, rfl, rfl, rfl⟩

def eraseScope (key : Key) : Key := { key with owner := { key.owner with scope := .root } }

theorem old_projection_erases_destination_scope (key : Key) : (eraseScope key).owner.scope = .root := rfl

theorem old_projection_collapses_distinct_scopes (method : Nat) (a b : Scope) (slot : Slot) :
    eraseScope ⟨⟨method, a⟩, slot⟩ = eraseScope ⟨⟨method, b⟩, slot⟩ := rfl

def climb (owner : Owner) (slot : Slot) (marks : List Nat) : List Request :=
  marks.map fun mark => { key := { owner, slot }, mark }

theorem climb_preserves_scope (owner : Owner) (slot : Slot) (marks : List Nat) (r : Request)
    (h : r ∈ climb owner slot marks) : r.key.owner = owner := by
  rcases List.mem_map.mp h with ⟨mark, _, eq⟩
  subst r; rfl

theorem climb_preserves_slot (owner : Owner) (slot : Slot) (marks : List Nat) (r : Request)
    (h : r ∈ climb owner slot marks) : r.key.slot = slot := by
  rcases List.mem_map.mp h with ⟨mark, _, eq⟩
  subst r; rfl

theorem climb_contains_all_full_marks (owner : Owner) (slot : Slot) (marks : List Nat) (mark : Nat) :
    { key := { owner, slot }, mark : Request } ∈ climb owner slot marks ↔ mark ∈ marks := by
  simp [climb]

/- Only ROOT admits the existing read-side R prefilter. Local owners defer dedup to their actor. -/
def prefilter (rootR : Owner → Slot → List Nat) (request : Request) : Bool :=
  match request.key.owner.scope with
  | .root => decide (request.mark ∉ rootR request.key.owner request.key.slot)
  | .block _ _ => true

def filteredClimb (rootR : Owner → Slot → List Nat) (offered : List Request) : List Request :=
  offered.filter (prefilter rootR)

theorem nonroot_prefilter_never_reads_peer_rows (rootR : Owner → Slot → List Nat)
    (method block entry : Nat) (slot : Slot) (mark : Nat) :
    prefilter rootR ⟨⟨⟨method, .block block entry⟩, slot⟩, mark⟩ = true := rfl

theorem root_prefilter_keeps_exactly_unadmitted_marks (rootR : Owner → Slot → List Nat)
    (method : Nat) (slot : Slot) (mark : Nat) :
    prefilter rootR ⟨⟨⟨method, .root⟩, slot⟩, mark⟩ = true ↔
      mark ∉ rootR ⟨method, .root⟩ slot := by simp [prefilter]

def insertRequest (history : List Request) (request : Request) : List Request := insert request history

theorem destination_dedup_keeps_every_new_scoped_request (history : List Request) (request : Request) :
    request ∈ insertRequest history request := by simp [insertRequest, mem_insert]

theorem destination_dedup_is_idempotent (history : List Request) (request : Request) :
    insertRequest (insertRequest history request) request = insertRequest history request := by
  simp only [insertRequest, insert]
  split <;> simp_all

theorem destination_dedup_cannot_suppress_another_scope (history : List Request)
    (old request : Request) (different : old.key.owner.scope ≠ request.key.owner.scope)
    (fresh : request ∉ history) : request ∉ insertRequest history old := by
  intro h
  rcases (mem_insert old request history).mp h with same | hold
  · subst request; exact different rfl
  · exact fresh hold

theorem batching_joins_same_scope_marks_without_loss (owner : Owner) (slot : Slot)
    (left right : List Nat) (mark : Nat) :
    delivered (batches (climb owner slot left ++ climb owner slot right))
      ⟨⟨owner, slot⟩, mark⟩ ↔ mark ∈ left ∨ mark ∈ right := by
  rw [batching_preserves_every_owner_slot_mark, List.mem_append]
  simp only [climb_contains_all_full_marks]

theorem same_slot_different_scopes_are_both_delivered (method a b : Nat) (slot : Slot)
    (marks : List Nat) (mark : Nat) (h : mark ∈ marks) :
    delivered (batches (climb ⟨method, .block a 1⟩ slot marks ++
      climb ⟨method, .block b 1⟩ slot marks)) ⟨⟨⟨method, .block a 1⟩, slot⟩, mark⟩ ∧
    delivered (batches (climb ⟨method, .block a 1⟩ slot marks ++
      climb ⟨method, .block b 1⟩ slot marks)) ⟨⟨⟨method, .block b 1⟩, slot⟩, mark⟩ := by
  constructor
  · apply (batching_preserves_every_owner_slot_mark _ _).mpr
    exact List.mem_append_left _ (climb_contains_all_full_marks _ _ _ _ |>.mpr h)
  · apply (batching_preserves_every_owner_slot_mark _ _).mpr
    exact List.mem_append_right _ (climb_contains_all_full_marks _ _ _ _ |>.mpr h)

/- Opaque slot matching: the correction copies its existing selected slot and full mark list. -/
def matchedClimb (slotMatches : Slot → Bool) (owner : Owner) (slot : Slot) (marks : List Nat) : List Request :=
  if slotMatches slot then climb owner slot marks else []

theorem unmatched_slots_still_emit_nothing (slotMatches : Slot → Bool) (owner : Owner) (slot : Slot)
    (marks : List Nat) (h : slotMatches slot = false) : matchedClimb slotMatches owner slot marks = [] := by
  simp [matchedClimb, h]

theorem matched_slots_keep_the_same_fields_and_tail (slotMatches : Slot → Bool) (owner : Owner) (slot : Slot)
    (marks : List Nat) (h : slotMatches slot = true) : matchedClimb slotMatches owner slot marks = climb owner slot marks := by
  simp [matchedClimb, h]

def fresh (history offered : List Request) : List Request :=
  offered.filter fun request => decide (request ∉ history)

theorem fresh_membership (history offered : List Request) (request : Request) :
    request ∈ fresh history offered ↔ request ∈ offered ∧ request ∉ history := by
  simp [fresh]

theorem nonroot_filtered_climb_keeps_all_marks (rootR : Owner → Slot → List Nat)
    (method block entry : Nat) (slot : Slot) (marks : List Nat) :
    filteredClimb rootR (climb ⟨method, .block block entry⟩ slot marks) =
      climb ⟨method, .block block entry⟩ slot marks := by
  unfold filteredClimb climb
  induction marks with
  | nil => rfl
  | cons mark rest ih => simp only [List.map_cons, List.filter_cons, prefilter,
      ↓reduceIte, List.cons.injEq, true_and]; exact ih

theorem receiver_only_observes_its_exact_owner (event : Event) (request : Request)
    (h : event.owner ≠ request.key.owner) : ¬ delivered [event] request := by
  rintro ⟨found, hfound, howner, _⟩
  have same : found = event := by simpa using hfound
  subst found
  exact h howner

theorem scoped_dedup_membership_is_order_independent (history : List Request) (a b query : Request) :
    query ∈ insertRequest (insertRequest history a) b ↔ query ∈ insertRequest (insertRequest history b) a := by
  simp only [insertRequest, mem_insert]
  constructor
  · intro h
    rcases h with hb | ha | old
    · exact Or.inr (Or.inl hb)
    · exact Or.inl ha
    · exact Or.inr (Or.inr old)
  · intro h
    rcases h with ha | hb | old
    · exact Or.inr (Or.inl ha)
    · exact Or.inl hb
    · exact Or.inr (Or.inr old)

theorem batching_does_not_add_a_new_mark (offered : List Request) (request : Request)
    (h : delivered (batches offered) request) : request ∈ offered :=
  (batching_preserves_every_owner_slot_mark offered request).mp h

theorem batching_does_not_drop_a_mark (offered : List Request) (request : Request)
    (h : request ∈ offered) : delivered (batches offered) request :=
  (batching_preserves_every_owner_slot_mark offered request).mpr h

/- The same scoped-cell identity applies independently to receiver R and receiver P. -/
def receiverHas (owner : Owner) (history : List Request) (slot : Slot) (mark : Nat) : Prop :=
  { key := { owner, slot }, mark : Request } ∈ history

theorem receiver_R_at_another_scope_is_not_an_answer (a b : Owner) (slot : Slot) (marks : List Nat)
    (different : a ≠ b) (mark : Nat) : ¬ receiverHas a (climb b slot marks) slot mark := by
  intro h
  exact different (climb_preserves_scope b slot marks _ h)

theorem receiver_P_at_another_scope_cannot_deduplicate_an_initial
    (a b : Owner) (slot : Slot) (marks : List Nat) (different : a ≠ b) (mark : Nat) :
    { key := { owner := a, slot }, mark : Request } ∈
      fresh (climb b slot marks) (climb a slot [mark]) := by
  apply (fresh_membership _ _ _).mpr
  constructor
  · exact (climb_contains_all_full_marks _ _ _ _).mpr (List.mem_cons_self)
  · exact receiver_R_at_another_scope_is_not_an_answer a b slot marks different mark

/- Fully executable loss witness and correction, including ROOT using the same field slot. -/
def sampleSlot : Slot := ⟨27, [4, 9], 2⟩
def ownerA : Owner := ⟨3, .block 47 6⟩
def ownerB : Owner := ⟨3, .block 51 8⟩
def ownerRoot : Owner := ⟨3, .root⟩
def fullMarks : List Nat := [11, 29, 71]
def requests : List Request := climb ownerA sampleSlot fullMarks ++ climb ownerB sampleSlot fullMarks

theorem old_keys_are_identical_but_new_keys_differ :
    eraseScope ⟨ownerA, sampleSlot⟩ = eraseScope ⟨ownerB, sampleSlot⟩ ∧
      (⟨ownerA, sampleSlot⟩ : Key) ≠ ⟨ownerB, sampleSlot⟩ := by decide

theorem new_batch_retains_both_owners_and_every_mark :
    delivered (batches requests) ⟨⟨ownerA, sampleSlot⟩, 11⟩ ∧
    delivered (batches requests) ⟨⟨ownerA, sampleSlot⟩, 29⟩ ∧
    delivered (batches requests) ⟨⟨ownerA, sampleSlot⟩, 71⟩ ∧
    delivered (batches requests) ⟨⟨ownerB, sampleSlot⟩, 11⟩ ∧
    delivered (batches requests) ⟨⟨ownerB, sampleSlot⟩, 29⟩ ∧
    delivered (batches requests) ⟨⟨ownerB, sampleSlot⟩, 71⟩ := by
  repeat' rw [batching_preserves_every_owner_slot_mark]
  decide

theorem root_history_cannot_answer_a_local_request :
    (⟨⟨ownerA, sampleSlot⟩, 11⟩ : Request) ∉ climb ownerRoot sampleSlot fullMarks := by decide

theorem root_prefilter_does_not_remove_either_local_owner :
    filteredClimb (fun _ _ => fullMarks) requests = requests := by decide

end ScopedRequestClimbs

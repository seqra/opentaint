import SelectedCore

/-! Exact NORMAL owned-row delta protocol. Full method/premise payloads are
opaque keys; no AP prefix or ReportId-only dedup is used. Pending publications
are durable logical obligations: duplicate suppression cannot erase them. -/
namespace OwnedDelta
open SelectedCore
set_option autoImplicit false

structure Key (P : Type) where
  method : Nat
  premise : P
  id : Nat
  deriving DecidableEq, Repr
structure State (P : Type) where
  retained : List (Key P)
  seen : List (Key P)
  pending : List (Key P)
  deriving DecidableEq, Repr
structure Result (P : Type) where
  state : State P
  delta : List (Key P)
  deriving DecidableEq, Repr

def offer {P : Type} [DecidableEq P] (state : State P) (key : Key P) : Result P :=
  if key ∈ state.retained ∨ key ∈ state.seen then ⟨state,[]⟩
  else ⟨{state with seen := key :: state.seen, pending := key :: state.pending},[key]⟩
def offerNormalInDirection {P : Type} [DecidableEq P] (direction : Direction) (state : State P) (key : Key P) : Result P :=
  match direction with | .forward => offer state key | .backward => ⟨state,[]⟩
theorem no_backward_normal_owned_emission {P : Type} [DecidableEq P] (state : State P) (key : Key P) :
    offerNormalInDirection .backward state key = ⟨state,[]⟩ := rfl

theorem retained_or_seen_no_effect {P : Type} [DecidableEq P] (state : State P) (key : Key P)
    (old : key ∈ state.retained ∨ key ∈ state.seen) : offer state key = ⟨state,[]⟩ := if_pos old
theorem fresh_exact_delta {P : Type} [DecidableEq P] (state : State P) (key : Key P)
    (fresh : ¬ (key ∈ state.retained ∨ key ∈ state.seen)) :
    offer state key = ⟨{state with seen := key :: state.seen,pending := key :: state.pending},[key]⟩ :=
  if_neg fresh

theorem pending_never_erased_by_offer {P : Type} [DecidableEq P] (state : State P) (key old : Key P)
    (pending : old ∈ state.pending) : old ∈ (offer state key).state.pending := by
  unfold offer
  split
  · exact pending
  · exact List.mem_cons.mpr (.inr pending)

theorem full_relation_membership_after_offer {P : Type} [DecidableEq P]
    (state : State P) (key query : Key P) :
    query ∈ (offer state key).state.retained ++ (offer state key).state.seen ↔
      query ∈ state.retained ++ state.seen ∨ query = key := by
  by_cases old : key ∈ state.retained ∨ key ∈ state.seen
  · rw [retained_or_seen_no_effect state key old]
    constructor
    · intro member; exact .inl member
    · rintro (member | same)
      · exact member
      · subst query; exact List.mem_append.mpr old
  · rw [fresh_exact_delta state key old]
    simp only [List.mem_append, List.mem_cons]
    constructor
    · rintro (retained | same | seen)
      · exact .inl (.inl retained)
      · exact .inr same
      · exact .inl (.inr seen)
    · rintro ((retained | seen) | same)
      · exact .inl retained
      · exact .inr (.inr seen)
      · exact .inr (.inl same)

theorem delta_is_fresh {P : Type} [DecidableEq P] (state : State P) (key row : Key P)
    (emitted : row ∈ (offer state key).delta) :
    row = key ∧ row ∉ state.retained ∧ row ∉ state.seen := by
  unfold offer at emitted
  split at emitted
  · cases emitted
  · rename_i fresh
    have same := List.mem_singleton.mp emitted
    subst row
    exact ⟨rfl,fun h => fresh (.inl h),fun h => fresh (.inr h)⟩

theorem second_identical_offer_has_empty_delta {P : Type} [DecidableEq P]
    (state : State P) (key : Key P) : (offer (offer state key).state key).delta = [] := by
  by_cases old : key ∈ state.retained ∨ key ∈ state.seen
  · rw [retained_or_seen_no_effect state key old,retained_or_seen_no_effect state key old]
  · rw [fresh_exact_delta state key old]
    have seen : key ∈ (key :: state.seen) := List.mem_cons.mpr (.inl rfl)
    rw [retained_or_seen_no_effect _ key (.inr seen)]

/-- A different caller key is independent of a saved callee relation. -/
theorem new_caller_key_still_emits {P : Type} [DecidableEq P] (state : State P)
    (saved caller : Key P) (_saved : saved ∈ state.retained)
    (fresh : caller ∉ state.retained ∧ caller ∉ state.seen) :
    (offer state caller).delta = [caller] := by
  rw [fresh_exact_delta state caller (fun h => h.elim fresh.1 fresh.2)]

theorem retained_unchanged {P : Type} [DecidableEq P] (state : State P) (key : Key P) :
    (offer state key).state.retained = state.retained := by unfold offer; split <;> rfl
theorem existing_relation_preserved {P : Type} [DecidableEq P] (state : State P) (key query : Key P)
    (old : query ∈ state.retained ++ state.seen) :
    query ∈ (offer state key).state.retained ++ (offer state key).state.seen :=
  (full_relation_membership_after_offer state key query).mpr (.inl old)
theorem offered_relation_present {P : Type} [DecidableEq P] (state : State P) (key : Key P) :
    key ∈ (offer state key).state.retained ++ (offer state key).state.seen :=
  (full_relation_membership_after_offer state key key).mpr (.inr rfl)
def offerBatch {P : Type} [DecidableEq P] : State P → List (Key P) → State P
  | state, [] => state
  | state, key :: rest => offerBatch (offer state key).state rest
theorem batch_retained_unchanged {P : Type} [DecidableEq P] (state : State P) (keys : List (Key P)) :
    (offerBatch state keys).retained = state.retained := by
  induction keys generalizing state with
  | nil => rfl
  | cons key rest ih => exact (ih _).trans (retained_unchanged state key)
theorem batch_preserves_relation {P : Type} [DecidableEq P] (state : State P) (keys : List (Key P))
    (query : Key P) (old : query ∈ state.retained ++ state.seen) :
    query ∈ (offerBatch state keys).retained ++ (offerBatch state keys).seen := by
  induction keys generalizing state with
  | nil => exact old
  | cons key rest ih => exact ih _ (existing_relation_preserved state key query old)
theorem batch_contains_every_offer {P : Type} [DecidableEq P] (state : State P) (keys : List (Key P))
    (query : Key P) (offered : query ∈ keys) :
    query ∈ (offerBatch state keys).retained ++ (offerBatch state keys).seen := by
  induction keys generalizing state with
  | nil => cases offered
  | cons key rest ih =>
      rcases List.mem_cons.mp offered with same | later
      · subst query; exact batch_preserves_relation _ rest key (offered_relation_present state key)
      · exact ih _ later

def SeenCovered {P : Type} (published : List (Key P)) (state : State P) : Prop :=
  ∀ key ∈ state.seen, key ∈ state.pending ∨ key ∈ published
theorem offer_preserves_seen_coverage {P : Type} [DecidableEq P] (published : List (Key P))
    (state : State P) (key : Key P) (covered : SeenCovered published state) :
    SeenCovered published (offer state key).state := by
  unfold offer
  split
  · exact covered
  · intro query member
    rcases List.mem_cons.mp member with same | old
    · subst query; exact .inl (List.mem_cons.mpr (.inl rfl))
    · rcases covered query old with pending | done_
      · exact .inl (List.mem_cons.mpr (.inr pending))
      · exact .inr done_
theorem batch_preserves_seen_coverage {P : Type} [DecidableEq P] (published : List (Key P))
    (state : State P) (keys : List (Key P)) (covered : SeenCovered published state) :
    SeenCovered published (offerBatch state keys) := by
  induction keys generalizing state with
  | nil => exact covered
  | cons key rest ih => exact ih _ (offer_preserves_seen_coverage published state key covered)

structure SeedState (Seed : Type) where
  targets : List Nat
  seeds : List Seed
  deriving DecidableEq, Repr
/-- Seeds are observed before anonymous Target membership is tested. -/
def observeSeed {Seed : Type} [DecidableEq Seed] (state : SeedState Seed) (id : Nat) (seed : Seed) : SeedState Seed :=
  ⟨if id ∈ state.targets then state.targets else id :: state.targets,
   if seed ∈ state.seeds then state.seeds else seed :: state.seeds⟩
theorem every_observed_seed_retained {Seed : Type} [DecidableEq Seed]
    (state : SeedState Seed) (id : Nat) (seed : Seed) : seed ∈ (observeSeed state id seed).seeds := by
  change seed ∈ (if seed ∈ state.seeds then state.seeds else seed :: state.seeds)
  split
  · assumption
  · exact List.mem_cons.mpr (.inl rfl)
theorem older_seed_not_erased {Seed : Type} [DecidableEq Seed]
    (state : SeedState Seed) (id : Nat) (seed old : Seed) (present : old ∈ state.seeds) :
    old ∈ (observeSeed state id seed).seeds := by
  change old ∈ (if seed ∈ state.seeds then state.seeds else seed :: state.seeds)
  split
  · exact present
  · exact List.mem_cons.mpr (.inr present)

namespace Controls
def callee : Key Premise := ⟨0,.ap .a,7⟩
def caller : Key Premise := ⟨1,.ap .b,7⟩
theorem saved_callee_does_not_globally_block_id :
    (offer ⟨[callee],[],[]⟩ caller).delta = [caller] := by decide
theorem two_seed_descriptors_survive_duplicate_target :
    (observeSeed (observeSeed (⟨[],[]⟩ : SeedState Nat) 0 10) 0 11).seeds = [11,10] := by decide
end Controls
end OwnedDelta

namespace AuditKernel
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

-- A rule has one complete positive premise. No executable ND rule is split.
structure Rule (α : Type) where
  premises : List α
  conclusion : α

inductive Derives (rules : List (Rule α)) (seed : α → Prop) : α → Prop where
  | initial (a : α) (present : seed a) : Derives rules seed a
  | apply (r : Rule α) (present : r∈rules)
      (inputs : ∀ a∈r.premises,Derives rules seed a) : Derives rules seed r.conclusion

def SeedCover (rules : List (Rule α)) (old new : α → Prop) : Prop :=
  ∀ a,old a → Derives rules new a

theorem positive_ND_closure_preserves_every_derivation
    (rules : List (Rule α)) (old new : α → Prop)
    (cover : SeedCover rules old new) (a : α) (before : Derives rules old a) :
    Derives rules new a := by
  induction before with
  | initial a present => exact cover a present
  | apply r present inputs ih => exact Derives.apply r present ih

theorem a_substitution_never_needs_a_weaker_ND_condition
    (rules : List (Rule α)) (old new : α → Prop)
    (cover : SeedCover rules old new) (r : Rule α) (present : r∈rules)
    (allOld : ∀ a∈r.premises,Derives rules old a) : Derives rules new r.conclusion := by
  apply Derives.apply r present
  intro a ha
  exact positive_ND_closure_preserves_every_derivation rules old new cover a (allOld a ha)

theorem seed_coverage_is_transitive (rules : List (Rule α)) (a b c : α → Prop)
    (ab : SeedCover rules a b) (bc : SeedCover rules b c) : SeedCover rules a c := by
  intro x hx
  exact positive_ND_closure_preserves_every_derivation rules b c bc x (ab x hx)

theorem every_normal_claim_is_valid_under_valid_seeds_and_transfers
    (rules : List (Rule α)) (seed valid : α → Prop)
    (seedValid : ∀ a,seed a → valid a)
    (transferValid : ∀ r∈rules,(∀ a∈r.premises,valid a) → valid r.conclusion)
    (a : α) (derived : Derives rules seed a) : valid a := by
  induction derived with
  | initial a ha => exact seedValid a ha
  | apply r hr inputs ih => exact transferValid r hr ih

-- Simulation includes query/control services if these are atoms of α.
-- Data-point coverage alone does not prove the service instance.
theorem changing_a_policy_requires_seed_and_rule_simulation
    (oldRules newRules : List (Rule α)) (oldSeed newSeed : α → Prop)
    (seeds : ∀ a,oldSeed a → Derives newRules newSeed a)
    (rules : ∀ r∈oldRules,
      (∀ a∈r.premises,Derives newRules newSeed a) → Derives newRules newSeed r.conclusion)
    (a : α) (before : Derives oldRules oldSeed a) : Derives newRules newSeed a := by
  induction before with
  | initial a ha => exact seeds a ha
  | apply r hr inputs ih => exact rules r hr ih

theorem translated_service_simulation_can_replace_queries_with_other_proved_service
    (oldRules : List (Rule α)) (newRules : List (Rule β))
    (oldSeed : α → Prop) (newSeed : β → Prop) (translate : α → β)
    (seeds : ∀ a,oldSeed a → Derives newRules newSeed (translate a))
    (rules : ∀ r∈oldRules,
      (∀ a∈r.premises,Derives newRules newSeed (translate a)) →
        Derives newRules newSeed (translate r.conclusion))
    (goal : α) (before : Derives oldRules oldSeed goal) :
    Derives newRules newSeed (translate goal) := by
  induction before with
  | initial a ha => exact seeds a ha
  | apply r hr inputs ih => exact rules r hr ih

def Closed (rules : List (Rule α)) (seed stored : α → Prop) : Prop :=
  (∀ a,seed a → stored a) ∧
  (∀ r∈rules,(∀ a∈r.premises,stored a) → stored r.conclusion)

theorem every_closed_store_contains_the_least_positive_result
    (rules : List (Rule α)) (seed stored : α → Prop)
    (closed : Closed rules seed stored) (a : α) (derived : Derives rules seed a) : stored a :=
  every_normal_claim_is_valid_under_valid_seeds_and_transfers rules seed stored
    closed.1 closed.2 a derived

theorem quiescent_sound_stores_are_order_independent
    (rules : List (Rule α)) (seed first second : α → Prop)
    (closed1 : Closed rules seed first) (closed2 : Closed rules seed second)
    (sound1 : ∀ a,first a → Derives rules seed a)
    (sound2 : ∀ a,second a → Derives rules seed a) (a : α) : first a ↔ second a := by
  constructor
  · intro h
    exact every_closed_store_contains_the_least_positive_result rules seed second closed2 a (sound1 a h)
  · intro h
    exact every_closed_store_contains_the_least_positive_result rules seed first closed1 a (sound2 a h)

-- A final retained witness basis prevents cyclic or mutually deleting covers.
theorem final_basis_replacement_preserves_all_positive_observations
    (rules : List (Rule α)) (packet kept : List α)
    (witness : ∀ a∈packet,Derives rules (fun b => b∈kept) a)
    (observation : α) (old : Derives rules (fun a => a∈packet) observation) :
    Derives rules (fun a => a∈kept) observation :=
  positive_ND_closure_preserves_every_derivation rules _ _ witness observation old

theorem cumulative_effects_cannot_be_retracted_by_later_data_compaction
    (earlier later : List α) (effect : α) (seen : effect∈earlier) :
    effect∈earlier++later := List.mem_append_left _ seen

end AuditKernel

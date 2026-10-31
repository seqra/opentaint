import AdmissionStore

namespace ExactDemand.AdmissionBounds
open ExactDemand AdmissionStore
set_option autoImplicit false

theorem offer_preserves_nodup (state : State) (seed : Seed) (unique : state.seen.Nodup) :
    (offer state seed).1.seen.Nodup := by
  unfold offer
  split
  · exact unique
  next fresh =>
    have notSeen : seed ∉ state.seen := by
      intro member
      have accepted : state.seen.any (fun old => covers old seed) = true :=
        List.any_eq_true.mpr ⟨seed,member,same_seed_covers_itself seed.initial seed.layer⟩
      exact fresh accepted
    apply List.nodup_append.mpr
    refine ⟨unique, by simp, ?_⟩
    intro old oldMember incoming incomingMember same
    have incomingEq : incoming = seed := List.mem_singleton.mp incomingMember
    have oldIsSeed : old = seed := same.trans incomingEq
    exact notSeen (oldIsSeed ▸ oldMember)

theorem offer_preserves_key_universe (keys : List InitialKey) (state : State) (seed : Seed)
    (old : ∀ member ∈ state.seen, member.initial ∈ keys) (added : seed.initial ∈ keys) :
    ∀ member ∈ (offer state seed).1.seen, member.initial ∈ keys := by
  unfold offer
  split
  · exact old
  · intro member inNew
    rcases List.mem_append.mp inNew with earlier | latest
    · exact old member earlier
    · have same := List.mem_singleton.mp latest
      cases same
      exact added

inductive Reachable (keys : List InitialKey) : State → Prop where
  | empty : Reachable keys ⟨[],[]⟩
  | step {state : State} (previous : Reachable keys state) (seed : Seed)
      (key : seed.initial ∈ keys) : Reachable keys (canonicalOffer state seed).1

theorem reachable_seen_nodup (keys : List InitialKey) (state : State)
    (reachable : Reachable keys state) : state.seen.Nodup := by
  induction reachable with
  | empty => exact List.nodup_nil
  | step previous seed key ih => exact offer_preserves_nodup _ _ ih

theorem reachable_keys_are_in_universe (keys : List InitialKey) (state : State)
    (reachable : Reachable keys state) : ∀ member ∈ state.seen, member.initial ∈ keys := by
  induction reachable with
  | empty => intro member impossible; cases impossible
  | step previous seed key ih => exact offer_preserves_key_universe keys _ _ ih key

def laneUniverse (keys : List InitialKey) : List Seed :=
  keys.flatMap fun key => [⟨key,.normal⟩,⟨key,.demand⟩]

theorem seed_is_in_two_lane_universe (keys : List InitialKey) (seed : Seed)
    (key : seed.initial ∈ keys) : seed ∈ laneUniverse keys := by
  apply List.mem_flatMap.mpr
  refine ⟨seed.initial,key,?_⟩
  cases seed with
  | mk initial layer => cases layer <;> simp

theorem lane_universe_length (keys : List InitialKey) : (laneUniverse keys).length = 2 * keys.length := by
  induction keys with
  | nil => rfl
  | cons key rest ih =>
    have split : laneUniverse (key :: rest) = [⟨key,.normal⟩,⟨key,.demand⟩] ++ laneUniverse rest := by
      simp only [laneUniverse, List.flatMap_cons]
    rw [split, List.length_append]
    change 2 + (laneUniverse rest).length = 2 * (rest.length + 1)
    rw [ih, Nat.mul_succ]
    exact Nat.add_comm _ _

/-- Constructive removal avoids the classical finite-list subset theorem. -/
def removeSeed (wanted : Seed) : List Seed → List Seed
  | [] => []
  | head :: rest => if head = wanted then rest else head :: removeSeed wanted rest

theorem remove_seed_length_successor (wanted : Seed) (seeds : List Seed)
    (member : wanted ∈ seeds) : (removeSeed wanted seeds).length + 1 = seeds.length := by
  induction seeds with
  | nil => cases member
  | cons head rest ih =>
    by_cases same : head = wanted
    · simp only [removeSeed, same, ↓reduceIte, List.length_cons]
    · have tailMember : wanted ∈ rest := by
        rcases List.mem_cons.mp member with first | later
        · exact False.elim (same first.symm)
        · exact later
      simp only [removeSeed, same, ↓reduceIte, List.length_cons]
      exact congrArg Nat.succ (ih tailMember)

theorem different_member_survives_removal (wanted other : Seed) (seeds : List Seed)
    (different : other ≠ wanted) (member : other ∈ seeds) : other ∈ removeSeed wanted seeds := by
  induction seeds with
  | nil => cases member
  | cons head rest ih =>
    by_cases same : head = wanted
    · simp only [removeSeed, same, ↓reduceIte]
      rcases List.mem_cons.mp member with first | later
      · exact False.elim (different (first.trans same))
      · exact later
    · simp only [removeSeed, same, ↓reduceIte]
      rcases List.mem_cons.mp member with first | later
      · exact List.mem_cons.mpr (Or.inl first)
      · exact List.mem_cons.mpr (Or.inr (ih later))

theorem constructive_nodup_subset_length (small big : List Seed)
    (unique : small.Nodup) (included : small ⊆ big) : small.length ≤ big.length := by
  induction small generalizing big with
  | nil => exact Nat.zero_le _
  | cons head rest ih =>
    have info := List.nodup_cons.mp unique
    have headMember : head ∈ big := included List.mem_cons_self
    have restIncluded : rest ⊆ removeSeed head big := by
      intro seed member
      have different : seed ≠ head := by
        intro same
        exact info.1 (same ▸ member)
      exact different_member_survives_removal head seed big different
        (included (List.mem_cons_of_mem _ member))
    have restBound := ih (removeSeed head big) info.2 restIncluded
    have bound := Nat.succ_le_succ restBound
    change rest.length + 1 ≤ (removeSeed head big).length + 1 at bound
    rw [remove_seed_length_successor head big headMember] at bound
    exact bound

/-- Every fresh enqueue injects into (key,layer). No scheduler assumption is
    used: from an empty store there are at most two admissions per finite key. -/
theorem reachable_admissions_are_bounded_by_two_times_keys (keys : List InitialKey) (state : State)
    (reachable : Reachable keys state) : state.seen.length ≤ 2 * keys.length := by
  have unique := reachable_seen_nodup keys state reachable
  have included : state.seen ⊆ laneUniverse keys := by
    intro seed member
    exact seed_is_in_two_lane_universe keys seed (reachable_keys_are_in_universe keys state reachable seed member)
  have bounded := constructive_nodup_subset_length state.seen (laneUniverse keys) unique included
  rw [lane_universe_length] at bounded
  exact bounded

end ExactDemand.AdmissionBounds

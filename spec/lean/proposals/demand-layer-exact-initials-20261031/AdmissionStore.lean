import ExactAdmission

/- Per-initial, per-layer admission history. NORMAL and DEMAND are separate
   memberships. An earlier NORMAL execution cannot replace the DEMAND lane:
   its NormalTarget cannot be downgraded for a later uncertain caller. -/
namespace ExactDemand.AdmissionStore
open ExactDemand
set_option autoImplicit false

/-- Deduplicate only the same initial AND starting layer. -/
def covers (old incoming : Seed) : Bool := decide (old = incoming)

structure State where
  seen : List Seed := []
  pending : List Seed := []
  deriving DecidableEq, Repr

def offer (state : State) (seed : Seed) : State × Bool :=
  if state.seen.any (fun old => covers old seed) then (state, false)
  else (⟨state.seen ++ [seed], state.pending ++ [seed]⟩, true)

theorem covered_offer_creates_no_work (state : State) (seed : Seed)
    (covered : state.seen.any (fun old => covers old seed) = true) :
    offer state seed = (state, false) := by simp only [offer, covered, ↓reduceIte]

theorem fresh_offer_preserves_pending (state : State) (seed : Seed)
    (fresh : state.seen.any (fun old => covers old seed) = false) :
    (offer state seed).1.pending = state.pending ++ [seed] := by
  simp only [offer, fresh, Bool.false_eq_true, ↓reduceIte]

theorem pending_work_is_never_erased (state : State) (seed : Seed) (job : Seed)
    (pending : job ∈ state.pending) : job ∈ (offer state seed).1.pending := by
  unfold offer
  split
  · exact pending
  · exact List.mem_append_left _ pending

theorem old_admission_is_never_erased (state : State) (seed old : Seed)
    (seen : old ∈ state.seen) : old ∈ (offer state seed).1.seen := by
  unfold offer
  split
  · exact seen
  · exact List.mem_append_left _ seen

theorem same_seed_covers_itself (key : InitialKey) (layer : Layer) :
    covers ⟨key, layer⟩ ⟨key, layer⟩ = true := by simp only [covers, decide_true]

theorem demand_does_not_cover_normal (key : InitialKey) :
    covers ⟨key, .demand⟩ ⟨key, .normal⟩ = false := by
  simp [covers]

theorem normal_does_not_cover_demand (key : InitialKey) :
    covers ⟨key, .normal⟩ ⟨key, .demand⟩ = false := by
  simp [covers]

theorem demand_first_then_normal_starts_upgrade (key : InitialKey) :
    offer ⟨[⟨key,.demand⟩], [⟨key,.demand⟩]⟩ ⟨key,.normal⟩ =
      (⟨[⟨key,.demand⟩, ⟨key,.normal⟩], [⟨key,.demand⟩, ⟨key,.normal⟩]⟩, true) := by
  simp only [offer, List.any_cons, List.any_nil, demand_does_not_cover_normal,
    Bool.or_self, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append]

theorem normal_first_then_demand_starts_separate_lane (key : InitialKey) :
    offer ⟨[⟨key,.normal⟩], [⟨key,.normal⟩]⟩ ⟨key,.demand⟩ =
      (⟨[⟨key,.normal⟩, ⟨key,.demand⟩], [⟨key,.normal⟩, ⟨key,.demand⟩]⟩, true) := by
  simp only [offer, List.any_cons, List.any_nil, normal_does_not_cover_demand,
    Bool.or_self, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append]

theorem duplicate_admission_does_not_requeue (key : InitialKey) (layer : Layer) :
    offer ⟨[⟨key,layer⟩], []⟩ ⟨key,layer⟩ = (⟨[⟨key,layer⟩], []⟩, false) := by
  simp only [offer, List.any_cons, List.any_nil, same_seed_covers_itself,
    Bool.true_or, ↓reduceIte]

theorem both_lanes_suppress_all_later_duplicates (key : InitialKey) (layer : Layer) :
    offer ⟨[⟨key,.normal⟩,⟨key,.demand⟩], []⟩ ⟨key,layer⟩ =
      (⟨[⟨key,.normal⟩,⟨key,.demand⟩], []⟩, false) := by
  cases layer <;>
    simp only [offer, List.any_cons, List.any_nil, same_seed_covers_itself,
      normal_does_not_cover_demand, demand_does_not_cover_normal,
      Bool.true_or, Bool.false_or, ↓reduceIte]

/-- The production boundary uses canonical final start-layer descriptors. -/
def canonicalOffer (state : State) (seed : Seed) : State × Bool := offer state (canonicalSeed seed)

theorem star_normal_descriptor_is_counted_in_demand_lane (base mark : Nat) (path : List Nat) :
    canonicalSeed ⟨.data ⟨base,path,.star,.concrete mark,[]⟩,.normal⟩ =
      ⟨.data ⟨base,path,.star,.concrete mark,[]⟩,.demand⟩ := rfl

theorem canonical_star_offers_do_not_create_two_demand_jobs (base mark : Nat) (path : List Nat) :
    let key := InitialKey.data ⟨base,path,.star,.concrete mark,[]⟩
    let afterNormal := (canonicalOffer ⟨[],[]⟩ ⟨key,.normal⟩).1
    canonicalOffer afterNormal ⟨key,.demand⟩ = (⟨[⟨key,.demand⟩],[⟨key,.demand⟩]⟩,false) := by
  simp only [canonicalOffer, canonicalSeed, intrinsicInitialLayer, join, offer,
    List.any_nil, Bool.false_eq_true, ↓reduceIte, List.nil_append,
    List.any_cons, same_seed_covers_itself, Bool.true_or]

end ExactDemand.AdmissionStore

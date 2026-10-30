import InputAdmission

/-! Proposal model only. A route includes the full method/caller/origin/stage/header.
Coordinates retain paths, tails, marks, layers and protection annotations.
`lookup` is the complete fixed-run admission function, not a compatibility test.
-/
namespace SelectedCallPolicy
open InputAdmission

abbrev Lookup (n k : Nat) := Root n → Root k

def admitted (lookup : Lookup n k) (actual : Root n) : Bool :=
  !isEmpty (lookup actual)

def liveNext (lookup : Lookup n k) (old actual : Root n) : Root n :=
  if admitted lookup actual then union old actual else old

def liveDelta (lookup : Lookup n k) (old actual : Root n) : Root n :=
  if admitted lookup actual then difference actual old else empty

def newPackets (lookup : Lookup n k) (actual : Root n) : List (Root k) :=
  if admitted lookup actual then [lookup actual] else []

def packetInitials : List (Root k) → Root k
  | [] => empty
  | packet :: rest => union packet (packetInitials rest)

def receive (started packet : Root k) : Root k × Root k :=
  (union started packet, difference packet started)

theorem rejected_retains_no_live_input (lookup : Lookup n k) (old actual : Root n)
    (h : admitted lookup actual = false) :
    liveNext lookup old actual = old ∧ liveDelta lookup old actual = empty := by
  simp [liveNext, liveDelta, h]

theorem rejected_sends_no_packet (lookup : Lookup n k) (actual : Root n)
    (h : admitted lookup actual = false) : newPackets lookup actual = [] := by
  simp [newPackets, h]

theorem accepted_keeps_full_actual (lookup : Lookup n k) (old actual : Root n)
    (h : admitted lookup actual = true) :
    liveNext lookup old actual = union old actual := by
  simp [liveNext, h]

theorem accepted_replay_is_fresh (lookup : Lookup n k) (old actual : Root n)
    (h : admitted lookup actual = true) :
    liveDelta lookup old actual = difference actual old := by
  simp [liveDelta, h]

theorem moved_lookup_exact (lookup : Lookup n k) (actual : Root n) :
    packetInitials (newPackets lookup actual) = lookup actual := by
  unfold newPackets admitted
  split
  · funext c
    simp [packetInitials, union, empty]
  · rename_i h
    have he : isEmpty (lookup actual) = true := by
      cases hi : isEmpty (lookup actual) <;> simp_all
    have hz := (isEmpty_exact _).1 he
    simp [packetInitials, hz]

theorem receive_starts_exactly_fresh (started packet : Root k) :
    (receive started packet).2 = difference packet started := rfl

theorem repeat_start_has_no_fresh (started packet : Root k) :
    (receive (receive started packet).1 packet).2 = empty := by
  funext c
  cases hs : started c <;> cases hp : packet c <;>
    simp [receive, union, difference, empty, hs, hp]

theorem start_gate_retains_old (started packet : Root k) :
    included started (receive started packet).1 := by
  intro c h
  simp [receive, union, h]

def routeLive (lookup : Lookup n k) (state : Fin r → Root n)
    (route : Fin r) (actual : Root n) : Fin r → Root n :=
  fun other => if other == route then liveNext lookup (state other) actual else state other

theorem other_route_unchanged (lookup : Lookup n k) (state : Fin r → Root n)
    (route other : Fin r) (actual : Root n) (h : other ≠ route) :
    routeLive lookup state route actual other = state other := by
  simp [routeLive, h]

def heldLive (lookup : Lookup n k) : List (Root n) → Root n
  | [] => empty
  | actual :: rest =>
      union (if admitted lookup actual then actual else empty) (heldLive lookup rest)

theorem failed_offer_is_not_activated_by_later_passed_offer
    (lookup : Lookup n k) (failed passed : Root n)
    (hf : admitted lookup failed = false) (hp : admitted lookup passed = true) :
    heldLive lookup [failed, passed] = passed := by
  funext c
  simp [heldLive, hf, hp, union, empty]

inductive Phase where
  | persisted | demand | register | currentReplay | initialSend
  deriving DecidableEq, Repr

def trace (eligible : Bool) : List Phase :=
  [.persisted, .demand] ++
    if eligible then [.register, .currentReplay, .initialSend] else []

theorem saved_replay_precedes_demand (eligible : Bool) :
    (trace eligible).take 2 = [.persisted, .demand] := by
  cases eligible <;> rfl

theorem failed_gate_has_only_saved_replay_and_lookup :
    trace false = [.persisted, .demand] := rfl

theorem registration_precedes_current_replay_and_send :
    trace true = [.persisted, .demand, .register, .currentReplay, .initialSend] := rfl

/-- Linearization points for unchanged registration, publication and replay.
    The chosen channel is an executable witness, not classical choice. -/
inductive DeliveryChannel where
  | replay | notification
  deriving DecidableEq, Repr

def deliveryChannel (publication replay : Nat) : DeliveryChannel :=
  if publication ≤ replay then .replay else .notification

theorem publication_has_delivery_channel (registration publication replay : Nat)
    (h : registration ≤ replay) :
    publication ≤ replay ∨ registration ≤ publication := by
  rcases Nat.le_total publication replay with before | after
  · exact Or.inl before
  · exact Or.inr (Nat.le_trans h after)

theorem chosen_channel_is_valid (registration publication replay : Nat)
    (h : registration ≤ replay) :
    match deliveryChannel publication replay with
    | .replay => publication ≤ replay
    | .notification => registration ≤ publication := by
  by_cases hp : publication ≤ replay
  · simp [deliveryChannel, hp]
  · simpa [deliveryChannel, hp] using
      Nat.le_trans h (Nat.le_of_lt (Nat.lt_of_not_ge hp))

theorem late_registration_still_has_replay (registration publication replay : Nat)
    (h : registration ≤ replay) (hp : publication ≤ registration) :
    deliveryChannel publication replay = .replay := by
  simp [deliveryChannel, Nat.le_trans hp h]

theorem after_replay_has_notification (registration publication replay : Nat)
    (h : registration ≤ replay) (hp : replay < publication) :
    deliveryChannel publication replay = .notification ∧ registration ≤ publication := by
  constructor
  · simp [deliveryChannel, Nat.not_le_of_gt hp]
  · exact Nat.le_trans h (Nat.le_of_lt hp)

/-- `saved` is evaluated for every offer, with no retained replay-input set. -/
def savedObservations (saved : Root n → Root o) : List (Root n) → Root o
  | [] => empty
  | actual :: rest => union (saved actual) (savedObservations saved rest)

theorem saved_replay_does_not_use_demand (saved : Root n → Root o)
    (actual : Root n) : savedObservations saved [actual] = saved actual := by
  funext c
  simp [savedObservations, union, empty]

theorem repeated_saved_replay_has_equal_observation_set (saved : Root n → Root o)
    (actual : Root n) : savedObservations saved [actual, actual] = saved actual := by
  funext c
  cases h : saved actual c <;> simp [savedObservations, union, empty, h]

/-- This counts replay invocations, not AP-operation or wall-clock cost. -/
def savedReplayCalls (offers : List (Root n)) : Nat := offers.length

theorem repeated_saved_replay_still_runs_twice (actual : Root n) :
    savedReplayCalls [actual, actual] = 2 := rfl

/-- The caller evaluates the exact same function that the callee used before. -/
def lookupAtCallee (lookup : Lookup n k) : List (Root n) → Root k
  | [] => empty
  | actual :: rest => union (lookup actual) (lookupAtCallee lookup rest)

def lookupAtCaller (lookup : Lookup n k) : List (Root n) → Root k
  | [] => empty
  | actual :: rest => union (packetInitials (newPackets lookup actual)) (lookupAtCaller lookup rest)

theorem moved_lookup_exact_over_all_offers (lookup : Lookup n k) (offers : List (Root n)) :
    lookupAtCaller lookup offers = lookupAtCallee lookup offers := by
  induction offers with
  | nil => rfl
  | cons actual rest ih => simp [lookupAtCaller, lookupAtCallee, moved_lookup_exact, ih]

/-- Delivery state contains keys only. Every accepted packet is eventually received. -/
def receiveAll (started : Root k) : List (Root k) → Root k
  | [] => started
  | packet :: rest => receiveAll (union started packet) rest

theorem receive_union_assoc (a b c : Root k) :
    union (union a b) c = union a (union b c) := by
  funext i
  simp [union, Bool.or_assoc]

theorem receiveAll_exact (started : Root k) (packets : List (Root k)) :
    receiveAll started packets = union started (packetInitials packets) := by
  induction packets generalizing started with
  | nil =>
      funext c
      simp [receiveAll, packetInitials, union, empty]
  | cons packet rest ih =>
      simp only [receiveAll, packetInitials]
      rw [ih]
      exact receive_union_assoc _ _ _

/-- This state is a proof observation, not an extra runtime store. `saved` is
    the union of completed semantic outputs; the implementation uses its existing
    output/observation stores. Routes hold only inputs whose own gate passed. -/
structure State (r n k o : Nat) where
  live : Fin r → Root n
  started : Root k
  saved : Root o

/-- Selected concept with the complete lookup repeated at the destination. -/
def referenceStep (lookup : Lookup n k) (saved : Root n → Root o)
    (state : State r n k o) (route : Fin r) (actual : Root n) : State r n k o :=
  ⟨routeLive lookup state.live route actual,
   union state.started (lookup actual), union state.saved (saved actual)⟩

/-- Same selected policy, with the caller's completed key packet consumed. -/
def handoffStep (lookup : Lookup n k) (saved : Root n → Root o)
    (state : State r n k o) (route : Fin r) (actual : Root n) : State r n k o :=
  ⟨routeLive lookup state.live route actual,
   receiveAll state.started (newPackets lookup actual), union state.saved (saved actual)⟩

theorem selected_handoff_refines_reference (lookup : Lookup n k)
    (saved : Root n → Root o) (state : State r n k o) (route : Fin r) (actual : Root n) :
    handoffStep lookup saved state route actual = referenceStep lookup saved state route actual := by
  simp only [handoffStep, referenceStep, receiveAll_exact, moved_lookup_exact]

/-- Applying current answers can inspect the complete unchanged actual for any
    eligible route. Equal callee initials do not identify caller inputs. -/
theorem handoff_preserves_live_routes (lookup : Lookup n k)
    (saved : Root n → Root o) (state : State r n k o) (route : Fin r) (actual : Root n) :
    (handoffStep lookup saved state route actual).live =
      (referenceStep lookup saved state route actual).live := rfl

theorem handoff_preserves_saved_observations (lookup : Lookup n k)
    (saved : Root n → Root o) (state : State r n k o) (route : Fin r) (actual : Root n) :
    (handoffStep lookup saved state route actual).saved = union state.saved (saved actual) := rfl

/-- Byte-free operation counts: a naive extra gate performs two lookups on
    eligible offers; moving the completed result retains only the caller lookup. -/
def naiveCallerGateLookups (eligible : Bool) : Nat := 1 + if eligible then 1 else 0
def selectedLookups (_eligible : Bool) : Nat := 1
def selectedCalleeLookups (_eligible : Bool) : Nat := 0

theorem one_lookup_per_offer (eligible : Bool) : selectedLookups eligible = 1 := rfl

theorem no_callee_lookup (eligible : Bool) : selectedCalleeLookups eligible = 0 := rfl

theorem eligible_avoids_second_lookup :
    selectedLookups true < naiveCallerGateLookups true := by decide

/-- A packet must be sent even when live-input admission has no fresh delta.
    No distributivity premise is required: the full original offer is queried. -/
def initialSend (lookup : Lookup n k) (actual : Root n) (_liveDelta : Root n) :
    List (Root k) := newPackets lookup actual

theorem packet_independent_of_live_freshness (lookup : Lookup n k) (actual : Root n)
    (leftDelta rightDelta : Root n) :
    initialSend lookup actual leftDelta = initialSend lookup actual rightDelta := rfl

/-- An executable witness: both offers have the same callee initial but
    still occupy different caller routes. -/
def first : Root 2 := fun c => c.val == 0
def second : Root 2 := fun c => c.val == 1
def oneInitial : Root 1 := fun _ => true
def sameInitial (_ : Root 2) : Root 1 := oneInitial

#guard (newPackets sameInitial first).length == 1
#guard isEmpty (liveDelta sameInitial first first)
#guard (newPackets sameInitial first).length == 1
#guard !isEmpty (liveDelta sameInitial empty first)
#guard !isEmpty (liveDelta sameInitial empty second)
#guard isEmpty (packetInitials ([] : List (Root 1)))
#guard trace false == [Phase.persisted, Phase.demand]
#guard trace true == [Phase.persisted, Phase.demand, Phase.register, Phase.currentReplay, Phase.initialSend]

def needsFirst (actual : Root 2) : Root 1 := fun _ => actual 0
#guard !admitted needsFirst second
#guard admitted needsFirst first
#guard heldLive needsFirst [second, first] 0
#guard !heldLive needsFirst [second, first] 1
#guard heldLive needsFirst [second, union first second] 1

end SelectedCallPolicy

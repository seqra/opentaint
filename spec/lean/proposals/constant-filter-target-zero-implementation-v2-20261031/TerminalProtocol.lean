import OwnedDelta

/-! Typed terminal register/replay/publish/receipt protocol. The matcher includes
the complete same-call premise and selected layer/native classification. Each
operation is one logical linearization step. Failed sends keep pending work;
only a completed state with no pending work yields final receipt certificates.
Kotlin locks, required sends and worker completion must refine these operations.
No AP overlap theorem is used as a receipt proof. -/
namespace TerminalProtocol
open OwnedDelta
set_option autoImplicit false

structure Subscription (P : Type) where
  id : Nat
  caller : Nat
  callee : Nat
  original : P
  deriving DecidableEq, Repr
abbrev Delivery (P : Type) := Subscription P × Key P
structure State (P : Type) where
  registered : List (Subscription P)
  ready : List (Subscription P)
  published : List (Key P)
  pending : List (Delivery P)
  received : List (Delivery P)
  started : List Nat
  deriving DecidableEq, Repr

def forSub {P : Type} (matchRow : Subscription P → Key P → Bool)
    (sub : Subscription P) (rows : List (Key P)) : List (Delivery P) :=
  rows.filterMap fun row => if matchRow sub row then some (sub,row) else none
def forRow {P : Type} (matchRow : Subscription P → Key P → Bool)
    (subs : List (Subscription P)) (row : Key P) : List (Delivery P) :=
  subs.filterMap fun sub => if matchRow sub row then some (sub,row) else none
theorem forSub_contains {P : Type} (matchRow : Subscription P → Key P → Bool)
    (sub : Subscription P) (rows : List (Key P)) (row : Key P)
    (present : row ∈ rows) (matched : matchRow sub row = true) : (sub,row) ∈ forSub matchRow sub rows :=
  List.mem_filterMap.mpr ⟨row,present,by simp only [matched,↓reduceIte]⟩
theorem forRow_contains {P : Type} (matchRow : Subscription P → Key P → Bool)
    (subs : List (Subscription P)) (sub : Subscription P) (row : Key P)
    (present : sub ∈ subs) (matched : matchRow sub row = true) : (sub,row) ∈ forRow matchRow subs row :=
  List.mem_filterMap.mpr ⟨sub,present,by simp only [matched,↓reduceIte]⟩

def register {P : Type} (state : State P) (sub : Subscription P) : State P :=
  {state with registered := sub :: state.registered}
def replay {P : Type} (matchRow : Subscription P → Key P → Bool) (state : State P)
    (sub : Subscription P) (_registered : sub ∈ state.registered) : State P :=
  {state with ready := sub :: state.ready, pending := forSub matchRow sub state.published ++ state.pending}
def start {P : Type} (state : State P) (sub : Subscription P) (_ready : sub ∈ state.ready) : State P :=
  {state with started := sub.callee :: state.started}
def publish {P : Type} (matchRow : Subscription P → Key P → Bool) (state : State P) (row : Key P) : State P :=
  {state with published := row :: state.published, pending := forRow matchRow state.registered row ++ state.pending}
def drain {P : Type} (state : State P) : State P :=
  {state with pending := [], received := state.pending ++ state.received}
def failedSend {P : Type} (state : State P) : State P := state

structure Invariant {P : Type} (matchRow : Subscription P → Key P → Bool) (state : State P) : Prop where
  readyRegistered : ∀ sub ∈ state.ready, sub ∈ state.registered
  covered : ∀ sub ∈ state.ready, ∀ row ∈ state.published, matchRow sub row = true →
    (sub,row) ∈ state.pending ++ state.received

theorem register_preserves {P : Type} (matchRow : Subscription P → Key P → Bool)
    (state : State P) (sub : Subscription P) (valid : Invariant matchRow state) :
    Invariant matchRow (register state sub) where
  readyRegistered := by intro other present; exact List.mem_cons.mpr (.inr (valid.readyRegistered other present))
  covered := valid.covered

theorem prefix_pending_preserves {A : Type} (new old done_ : List A) (value : A)
    (member : value ∈ old ++ done_) : value ∈ (new ++ old) ++ done_ := by
  rcases List.mem_append.mp member with pending | received
  · exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inr pending)))
  · exact List.mem_append.mpr (.inr received)

theorem replay_preserves {P : Type} (matchRow : Subscription P → Key P → Bool)
    (state : State P) (sub : Subscription P) (registered : sub ∈ state.registered)
    (valid : Invariant matchRow state) : Invariant matchRow (replay matchRow state sub registered) where
  readyRegistered := by
    intro other present
    rcases List.mem_cons.mp present with same | old
    · exact same ▸ registered
    · exact valid.readyRegistered other old
  covered := by
    intro other prepared row published matched
    rcases List.mem_cons.mp prepared with same | old
    · subst other
      exact List.mem_append.mpr (.inl (List.mem_append.mpr
        (.inl (forSub_contains matchRow sub state.published row published matched))))
    · exact prefix_pending_preserves _ _ _ _ (valid.covered other old row published matched)

theorem publish_preserves {P : Type} (matchRow : Subscription P → Key P → Bool)
    (state : State P) (row : Key P) (valid : Invariant matchRow state) :
    Invariant matchRow (publish matchRow state row) where
  readyRegistered := valid.readyRegistered
  covered := by
    intro sub prepared other published matched
    rcases List.mem_cons.mp published with same | old
    · subst other
      exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inl
        (forRow_contains matchRow state.registered sub row (valid.readyRegistered sub prepared) matched))))
    · exact prefix_pending_preserves _ _ _ _ (valid.covered sub prepared other old matched)

theorem start_preserves {P : Type} (matchRow : Subscription P → Key P → Bool)
    (state : State P) (sub : Subscription P) (prepared : sub ∈ state.ready)
    (valid : Invariant matchRow state) : Invariant matchRow (start state sub prepared) where
  readyRegistered := valid.readyRegistered
  covered := valid.covered
theorem drain_preserves {P : Type} (matchRow : Subscription P → Key P → Bool)
    (state : State P) (valid : Invariant matchRow state) : Invariant matchRow (drain state) where
  readyRegistered := valid.readyRegistered
  covered := valid.covered
theorem failed_send_keeps_required_work {P : Type} (state : State P) :
    (failedSend state).pending = state.pending := rfl

theorem completed_receipt {P : Type} (matchRow : Subscription P → Key P → Bool)
    (state : State P) (valid : Invariant matchRow state) (complete : state.pending = [])
    (sub : Subscription P) (ready : sub ∈ state.ready) (row : Key P) (published : row ∈ state.published)
    (matched : matchRow sub row = true) : (sub,row) ∈ state.received := by
  have covered := valid.covered sub ready row published matched
  simpa only [complete,List.nil_append] using covered

def prepare {P : Type} (matchRow : Subscription P → Key P → Bool)
    (state : State P) (sub : Subscription P) : State P :=
  let registered := register state sub
  let replayed := replay matchRow registered sub (List.mem_cons.mpr (.inl rfl))
  start replayed sub (List.mem_cons.mpr (.inl rfl))
theorem prepare_preserves {P : Type} (matchRow : Subscription P → Key P → Bool)
    (state : State P) (sub : Subscription P) (valid : Invariant matchRow state) :
    Invariant matchRow (prepare matchRow state sub) :=
  start_preserves matchRow _ sub (List.mem_cons.mpr (.inl rfl))
    (replay_preserves _ _ _ _ (register_preserves _ _ _ valid))

theorem register_before_start_receives_fresh_terminal {P : Type}
    (matchRow : Subscription P → Key P → Bool) (state : State P) (sub : Subscription P)
    (row : Key P) (valid : Invariant matchRow state) (matched : matchRow sub row = true) :
    (sub,row) ∈ (drain (publish matchRow (prepare matchRow state sub) row)).received := by
  apply completed_receipt matchRow _ (drain_preserves _ _ (publish_preserves _ _ _ (prepare_preserves _ _ _ valid))) rfl
  · exact List.mem_cons.mpr (.inl rfl)
  · exact List.mem_cons.mpr (.inl rfl)
  · exact matched

theorem current_replay_receives_existing_terminal {P : Type}
    (matchRow : Subscription P → Key P → Bool) (state : State P) (sub : Subscription P)
    (row : Key P) (valid : Invariant matchRow state) (published : row ∈ state.published)
    (matched : matchRow sub row = true) : (sub,row) ∈ (drain (prepare matchRow state sub)).received := by
  apply completed_receipt matchRow _ (drain_preserves _ _ (prepare_preserves _ _ _ valid)) rfl
  · exact List.mem_cons.mpr (.inl rfl)
  · exact published
  · exact matched

theorem missing_receipt_prevents_completion {P : Type} (matchRow : Subscription P → Key P → Bool)
    (state : State P) (valid : Invariant matchRow state) (sub : Subscription P)
    (prepared : sub ∈ state.ready) (row : Key P) (published : row ∈ state.published)
    (matched : matchRow sub row = true) (missing : (sub,row) ∉ state.received) : state.pending ≠ [] := by
  intro complete
  exact missing (completed_receipt matchRow state valid complete sub prepared row published matched)

def publishAll {P : Type} (matchRow : Subscription P → Key P → Bool) : State P → List (Key P) → State P
  | state, [] => state
  | state, row :: rest => publishAll matchRow (publish matchRow state row) rest
theorem publishAll_preserves_old_rows {P : Type} (matchRow : Subscription P → Key P → Bool)
    (state : State P) (rows : List (Key P)) (row : Key P) (old : row ∈ state.published) :
    row ∈ (publishAll matchRow state rows).published := by
  induction rows generalizing state with
  | nil => exact old
  | cons fresh rest ih => exact ih _ (List.mem_cons.mpr (.inr old))
theorem publishAll_contains_every_new_row {P : Type} (matchRow : Subscription P → Key P → Bool)
    (state : State P) (rows : List (Key P)) (row : Key P) (fresh : row ∈ rows) :
    row ∈ (publishAll matchRow state rows).published := by
  induction rows generalizing state with
  | nil => cases fresh
  | cons head rest ih =>
      rcases List.mem_cons.mp fresh with same | later
      · subst row; exact publishAll_preserves_old_rows _ _ rest head (List.mem_cons.mpr (.inl rfl))
      · exact ih _ later
theorem publishAll_preserves_protocol {P : Type} (matchRow : Subscription P → Key P → Bool)
    (state : State P) (rows : List (Key P)) (valid : Invariant matchRow state) :
    Invariant matchRow (publishAll matchRow state rows) := by
  induction rows generalizing state with
  | nil => exact valid
  | cons row rest ih => exact ih _ (publish_preserves _ _ _ valid)

/-- A successful required flush transfers the owned outbox to the publication
    store before clearing it. A failed/cancelled send uses failedSend, not this. -/
def flushOwned {P : Type} (matchRow : Subscription P → Key P → Bool)
    (owned : OwnedDelta.State P) (protocol : State P) : OwnedDelta.State P × State P :=
  ({owned with pending := []},publishAll matchRow protocol owned.pending)
theorem successful_flush_publishes_every_seen {P : Type}
    (matchRow : Subscription P → Key P → Bool) (owned : OwnedDelta.State P) (protocol : State P)
    (covered : OwnedDelta.SeenCovered protocol.published owned)
    (row : Key P) (seen : row ∈ owned.seen) :
    row ∈ (flushOwned matchRow owned protocol).2.published := by
  rcases covered row seen with pending | published
  · exact publishAll_contains_every_new_row _ _ _ _ pending
  · exact publishAll_preserves_old_rows _ _ _ _ published

/-- The terminal lane has no AP/CFG mutation in the formal machine. Production
    must dispatch to this typed lane instead of an AP return/alias stage. -/
def terminalOnly {P A : Type} (apState : A) (protocol : State P) (transition : State P → State P) : A × State P :=
  (apState,transition protocol)
theorem terminal_has_no_ap_or_cfg_effect {P A : Type} (apState : A) (protocol : State P)
    (transition : State P → State P) : (terminalOnly apState protocol transition).1 = apState := rfl

end TerminalProtocol

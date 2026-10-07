/-
  ApSpec.Pipeline — the communication pipeline of the analyzer (analyzer-core.md §5, §6).

  The analyzer is a set of ACTORS (one per method of a run; a unit runner hosts several actors and
  runs one event at a time). An actor owns objects: its initial facts, edges, added facts, links,
  requests, subscriptions and publications. Actors exchange objects by messages, and they meet in
  one shared structure: the STORAGE WITH SUBSCRIPTION (today `SummaryEdgeStorageWithSubscribers`
  with the caller-side `SummaryEdgeSubscriptionManager`).

  The model is an interleaving (sequentially consistent) transition system. Each step is one
  atomic shared action:

    proc      an actor takes an object from the in-flight list, stores it, and fires every LOCAL
              rule that has the object as a premise. A subscription also registers the handler of
              its actor on its topic and schedules its replay. A publication is inserted into the
              storage and schedules its notification.
    replay    the subscriber reads the storage and fires every join of the subscription with a
              stored publication (today: the synchronous replay in `subscribeOnMethodSummary`).
    notify    the publisher reads the handler list and sends one delivery per handler (today: the
              loop over `subscribers` in `SummaryEdgeStorageWithSubscribers.addEdges`).
    deliver   the subscriber matches a delivered publication against its subscriptions at THAT
              moment (today: `NewSummaryEdgeEvent.processMethodSummary`).

  The replay and the notification are separate steps, so other actors can act between the two
  halves of a subscription and between the two halves of a publication. This is more than the
  real schedules allow (a runner does not run another event of the same actor in between), so a
  theorem for this model holds for the real schedules.

  The definitions of this file are FROZEN: `PipelineAP.lean` and the spec use them by name.

  All proofs are constructive (`propext`, `Quot.sound` only).
-/

namespace ApSpec.Pipeline

/-! ## 1. The rule system -/

/-- A rule system with owners, subscriptions and publications.

    * `owner x`: the actor that stores and processes the object `x`.
    * `roots`: the objects that the driver gives at the start of a run.
    * `rule ps c`: a LOCAL rule instance with the premises `ps` and the conclusion `c`. All premises
      have one owner (`Sys.WF`); the conclusion can have another owner (then it is a message).
    * `isSub`, `isPub`, `topic`: a subscription and a publication meet on a topic (the callee).
    * `join ss p c`: a JOIN instance: the subscriptions `ss` (one actor, one topic; a summary with
      several premises needs one subscription per premise) and the publication `p` give `c`. -/
structure Sys (Obj Actor Topic : Type) where
  owner : Obj → Actor
  roots : List Obj
  rule  : List Obj → Obj → Prop
  isSub : Obj → Bool
  isPub : Obj → Bool
  topic : Obj → Topic
  join  : List Obj → Obj → Obj → Prop

variable {Obj Actor Topic : Type}

/-- Well-formedness: a local rule has premises of one owner and at least one premise; a join has
    at least one subscription, all of one owner and of the topic of the publication. -/
structure Sys.WF (S : Sys Obj Actor Topic) : Prop where
  rule_ne    : ∀ ps c, S.rule ps c → ps ≠ []
  rule_local : ∀ ps c, S.rule ps c → ∀ p ∈ ps, ∀ q ∈ ps, S.owner p = S.owner q
  join_ne    : ∀ ss p c, S.join ss p c → ss ≠ []
  join_sub   : ∀ ss p c, S.join ss p c → ∀ s ∈ ss, S.isSub s = true ∧ S.topic s = S.topic p
  join_pub   : ∀ ss p c, S.join ss p c → S.isPub p = true
  join_owner : ∀ ss p c, S.join ss p c → ∀ s ∈ ss, ∀ s' ∈ ss, S.owner s = S.owner s'

/-- The concept: the least set of objects closed under the roots, the local rules and the joins. -/
inductive Cl (S : Sys Obj Actor Topic) : Obj → Prop where
  | root {x} : x ∈ S.roots → Cl S x
  | rule {ps c} : S.rule ps c → (∀ p ∈ ps, Cl S p) → Cl S c
  | join {ss p c} : S.join ss p c → (∀ s ∈ ss, Cl S s) → Cl S p → Cl S c

/-! ## 2. The implementation state and its steps -/

/-- The global state of one run.

    * `known`: the objects that their owners have processed (the union of the actor stores).
    * `inbox`: the objects in flight to their owners (messages and actor worklists).
    * `store`: the publications in the storage with subscription.
    * `handlers`: the registered subscriber handlers `(actor, topic)`.
    * `replays`: the subscriptions whose replay read is pending.
    * `notifies`: the publications that are in the storage but not yet notified.
    * `deliv`: the deliveries in flight `(subscriber actor, publication)`. -/
structure St (Obj Actor Topic : Type) where
  known    : List Obj
  inbox    : List Obj
  store    : List Obj
  handlers : List (Actor × Topic)
  replays  : List Obj
  notifies : List Obj
  deliv    : List (Actor × Obj)

/-- The start of a run: the roots are in flight, everything else is empty. -/
def St.init (S : Sys Obj Actor Topic) : St Obj Actor Topic :=
  ⟨[], S.roots, [], [], [], [], []⟩

/-- No work anywhere: nothing in flight, no pending replay, notification or delivery. -/
def St.Quiescent (st : St Obj Actor Topic) : Prop :=
  st.inbox = [] ∧ st.replays = [] ∧ st.notifies = [] ∧ st.deliv = []

/-- What `proc x` must send: every conclusion of a local rule that has `x` as a premise and all
    premises processed (complete), and nothing that no such rule gives (sound). -/
structure ProcOut (S : Sys Obj Actor Topic) (known : List Obj) (x : Obj) (out : List Obj) :
    Prop where
  complete : ∀ ps c, S.rule ps c → x ∈ ps → (∀ p ∈ ps, p ∈ x :: known) → c ∈ out
  sound    : ∀ c ∈ out, ∃ ps, S.rule ps c ∧ x ∈ ps ∧ ∀ p ∈ ps, p ∈ x :: known

/-- What `replay s` must send: every join of `s` with the other processed subscriptions and a
    stored publication. -/
structure ReplayOut (S : Sys Obj Actor Topic) (known store : List Obj) (s : Obj)
    (out : List Obj) : Prop where
  complete : ∀ ss p c, S.join ss p c → s ∈ ss → (∀ s' ∈ ss, s' ∈ known) → p ∈ store → c ∈ out
  sound    : ∀ c ∈ out, ∃ ss p, S.join ss p c ∧ (∀ s' ∈ ss, s' ∈ known) ∧ p ∈ store

/-- What `deliver (A, p)` must send: every join of `p` with processed subscriptions of `A`. -/
structure DeliverOut (S : Sys Obj Actor Topic) (known : List Obj) (A : Actor) (p : Obj)
    (out : List Obj) : Prop where
  complete : ∀ ss c, S.join ss p c → (∀ s ∈ ss, s ∈ known ∧ S.owner s = A) → c ∈ out
  sound    : ∀ c ∈ out, ∃ ss, S.join ss p c ∧ ∀ s ∈ ss, s ∈ known

/-- The deliveries of a notification: one per handler on the topic of the publication. -/
def notifyOut [DecidableEq Topic] (S : Sys Obj Actor Topic) (handlers : List (Actor × Topic))
    (p : Obj) : List (Actor × Obj) :=
  (handlers.filter (fun h => decide (h.2 = S.topic p))).map (fun h => (h.1, p))

/-- One atomic step of the pipeline (the protocol of today's storage with subscription). -/
inductive Step [DecidableEq Obj] [DecidableEq Actor] [DecidableEq Topic]
    (S : Sys Obj Actor Topic) : St Obj Actor Topic → St Obj Actor Topic → Prop where
  /-- an object that its owner has already processed: drop it (duplicate delivery). -/
  | dup {st x} : x ∈ st.inbox → x ∈ st.known →
      Step S st { st with inbox := st.inbox.erase x }
  /-- process a new object: store it, fire the local rules; a subscription registers its
      handler and schedules its replay; a publication is inserted and schedules its
      notification. -/
  | proc {st x out} : x ∈ st.inbox → x ∉ st.known → ProcOut S st.known x out →
      Step S st
        { known    := x :: st.known
          inbox    := st.inbox.erase x ++ out
          store    := if S.isPub x then x :: st.store else st.store
          handlers := if S.isSub x then (S.owner x, S.topic x) :: st.handlers else st.handlers
          replays  := if S.isSub x then x :: st.replays else st.replays
          notifies := if S.isPub x then x :: st.notifies else st.notifies
          deliv    := st.deliv }
  /-- the replay read of a subscription. -/
  | replay {st s out} : s ∈ st.replays → ReplayOut S st.known st.store s out →
      Step S st { st with replays := st.replays.erase s, inbox := st.inbox ++ out }
  /-- the notification of a publication: read the handler list, send the deliveries. -/
  | notify {st p} : p ∈ st.notifies →
      Step S st { st with notifies := st.notifies.erase p,
                          deliv := st.deliv ++ notifyOut S st.handlers p }
  /-- a delivery: match the publication against the subscriptions of the actor now. -/
  | deliver {st A p out} : (A, p) ∈ st.deliv → DeliverOut S st.known A p out →
      Step S st { st with deliv := st.deliv.erase (A, p), inbox := st.inbox ++ out }

/-- The states that a run reaches from its start. -/
inductive Reach [DecidableEq Obj] [DecidableEq Actor] [DecidableEq Topic]
    (S : Sys Obj Actor Topic) : St Obj Actor Topic → Prop where
  | init : Reach S (St.init S)
  | step {st st'} : Reach S st → Step S st st' → Reach S st'

/-! ## 3. Main theorems (proved in `PipelineProofs.lean`)

  * `reach_sound`: every object in `known`, `inbox`, `store`, `replays`, `notifies` and every
    publication in `deliv` of a reachable state is in `Cl S`.
  * `quiescent_complete`: `S.WF` → `Reach S st` → `st.Quiescent` → `Cl S x` → `x ∈ st.known`.
  * `quiescent_exact`: under the same hypotheses, `x ∈ st.known ↔ Cl S x`.
  * `no_lost_join` (the summary edge is never lost): at a reachable quiescent state, for every
    join instance `ss p c` whose subscriptions and publication are processed, `c ∈ st.known`.

  ## 4. Counterexamples (protocol conditions)

  Four variants of `Step` (in `PipelineProofs.lean`), each with one protocol condition removed, and
  a concrete system with a reachable quiescent state that misses an object of `Cl`:

  * P1 register-before-read: the replay reads the storage BEFORE the handler is registered.
  * P2 insert-before-notify: the notification reads the handler list BEFORE the publication is
    in the storage.
  * P3 linearizable read: the replay may miss a publication that is in the storage.
  * P4 one match function: the delivery matches with a smaller relation than the replay.

  ## 5. Quiescence detection

  An abstract model of the in-flight counter (`TaintAnalysisUnitRunnerManager.handleEventEnqueued`
  / `handleEventProcessed`): items, running handlers, the counter; increment before a send,
  decrement after the handler ends. Theorem: the counter is zero exactly when no item is pending and
  no handler runs. Counterexample: a decrement at the start of a handler declares completion while
  the handler still sends.

  ## 6. Subsumption (dominance)

  A variant of `proc` that drops an object dominated by a processed object of the same owner. With
  a dominance preorder that the rules and joins simulate, every object of `Cl` is dominated by a
  processed object at a quiescent state.
-/

end ApSpec.Pipeline

/-
  ApSpec.PipelineProofs — the proofs for the communication pipeline (`ApSpec.Pipeline`).

  `Pipeline.lean` fixes the model: a rule system `Sys` with owners, local rules and k-ary joins
  of subscriptions with a publication, its closure `Cl`, and the interleaving transition system
  `Step` of today's storage with subscription. This file proves the theorems of its §3 – §6 and
  gives the counterexamples of its §4. It changes no definition of `Pipeline.lean`.

  Parts:
    0. Helpers: list membership through `List.erase`, `if … then x :: l else l`, `notifyOut`;
       the generic closure `ReachBy` of a step relation; `ListRel` (pointwise relation of two
       lists; core Lean has no `List.Forall₂`).
    1. Soundness: `reach_sound` — every object of `known`, `inbox`, `store`, `replays`,
       `notifies` and every publication of `deliv` of a reachable state is in `Cl S`.
    2. Completeness: the coverage invariant `CovInv` (generic in what "covered" means) and
         `quiescent_complete`  S.WF → Reach S st → st.Quiescent → Cl S x → x ∈ st.known
         `quiescent_exact`     … → (x ∈ st.known ↔ Cl S x)
         `no_lost_join`        … → S.join ss p c → ss, p processed → c ∈ st.known
       The invariant (for `P = KnownOrInbox`):
         (H) a processed subscription has its handler registered; a processed publication is
             in the storage;
         (L) the roots, and the conclusion of every local rule instance with processed premises,
             are processed or in flight;
         (J) the conclusion of every join instance with processed subscriptions and a stored
             publication is processed or in flight, OR a replay of one of its subscriptions,
             the notification of its publication, or a delivery of its publication to its
             subscriber is pending.
       At a quiescent state every alternative of (J) except the first is empty, and induction on
       `Cl` closes. `List.erase` removes one occurrence: every case of the proof that consumes a
       pending item looks at the item that is erased and keeps the others.
       `WF` fields used: `rule_ne` (a rule without premises never fires: no `proc` has it as a
       premise), `join_ne`, `join_sub`, `join_pub`, `join_owner`. `rule_local` is not used
       (`known` is global). Soundness needs no `WF`.
    3. Counterexamples (§4). One concrete system `PCex.sys` (one subscription `sub` of the actor
       `caller`, one publication `pub` of the actor `callee`, one join `[sub] pub ⟶ edge`, roots
       `[sub, pub]`; it is `WF`, and `Step` finds `edge`: `PCex.step_finds_edge`). Each variant
       removes one protocol condition and reaches a quiescent state without `edge`:
         `cex_P1` (register before read): the subscriber reads the storage when it processes
             the subscription and registers its handler only at the deferred step. The callee
             inserts and notifies in the window: the read saw no publication, the notification
             saw no handler.
         `cex_P2` (insert before notify): the publisher reads the handler list when it processes
             the publication and inserts it into the storage only at the deferred step. The
             caller subscribes and replays in the window.
         `cex_P3` (linearizable read): the replay may read any sublist of the storage; it misses
             the publication that was inserted and notified before the handler was registered.
         `cex_P4` (one match predicate): the delivery matches with a smaller join relation than
             the replay (today: the push path filters with a literal-accessor index that misses a
             caller fact with `[any]`, the replay treats `[any]` as a wildcard). The subscription
             is processed first, so only the delivery can make the join, and it misses it.
       NOTE on P1/P2 (argued, not proved here): one ATOMIC step that reads and then registers
       (or computes the deliveries and then inserts) has no counterexample — inside one atomic
       step the order is not observable, and the invariant of part 2 still holds with (H)
       weakened to "handler registered OR replay pending" (resp. "stored OR insertion
       pending"). The condition is about two separate actions, so the variants place the read
       in the first half (`proc`) and the write in the deferred half; between the halves the
       other actor runs.
    4. Quiescence detection (§5): the counter model `Quiesce`. The driver is a phantom handler
       (counted, running) while it submits the roots; `cnt = items + running` and
       `done ↔ cnt = 0` are invariant (`creach_inv`); `done_final`: when `done` is set, no item is
       pending, no handler runs and no step is enabled. `bad_early_done`: with the decrement at
       the start of a handler, `done` is set while the handler still sends an item.
    5. Dominance (§6): `StepD` = `Step` + `drop` (an in-flight object dominated by a processed
       object of the same owner). `reach_soundD`: soundness is kept. `quiescent_dominates`:
       with a preorder that the local rules and the joins simulate, every object of `Cl` is
       dominated by a processed object at a quiescent state. No extra hypothesis is needed: the
       simulated join instance is an instance of `S`, so `S.WF` applies to it. The preservation
       of `owner`, `isSub`, `isPub`, `topic` by the dominance is NOT used by the proof.

  All proofs are constructive (`propext`, `Quot.sound` only). Each main theorem has a
  `#print axioms` audit.
-/
import ApSpec.Pipeline

namespace ApSpec.Pipeline

variable {Obj Actor Topic : Type}

/-! ## 0. Helpers -/

section ListHelpers
variable {α : Type}

/-- `List.mem_erase_of_ne` of core uses `Classical.choice`; this is the constructive form. It is
    stated for any lawful `BEq`: `Step` erases from `deliv` with the `BEq` of a product. -/
private theorem mem_erase_of_ne' [BEq α] [LawfulBEq α] {a b : α} :
    ∀ {l : List α}, a ≠ b → a ∈ l → a ∈ l.erase b
  | [], _, h => absurd h List.not_mem_nil
  | c :: l, hne, h => by
    rw [List.erase_cons]
    cases hcb : (c == b)
    · show a ∈ c :: l.erase b
      rcases List.mem_cons.1 h with h | h
      · exact h ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_erase_of_ne' hne h)
    · show a ∈ l
      rcases List.mem_cons.1 h with h | h
      · exact absurd (h.trans (beq_iff_eq.1 hcb)) hne
      · exact h

private theorem mem_erase_or [BEq α] [LawfulBEq α] {a b : α} {l : List α} (h : a ∈ l) :
    a = b ∨ a ∈ l.erase b := by
  cases hab : (a == b)
  · exact Or.inr (mem_erase_of_ne' (ne_of_beq_false hab) h)
  · exact Or.inl (beq_iff_eq.1 hab)

private theorem mem_ite_cons {b : Bool} {x y : α} {l : List α}
    (h : y ∈ (if b then x :: l else l)) : y = x ∨ y ∈ l := by
  cases b
  · exact Or.inr h
  · exact List.mem_cons.1 h

private theorem mem_ite_cons_of_mem {b : Bool} {x y : α} {l : List α} (h : y ∈ l) :
    y ∈ (if b then x :: l else l) := by
  cases b
  · exact h
  · exact List.mem_cons_of_mem _ h

private theorem mem_ite_cons_self {b : Bool} {x : α} {l : List α} (hb : b = true) :
    x ∈ (if b then x :: l else l) := by
  subst hb
  exact List.mem_cons_self

private theorem false_of_mem_nil {l : List α} (hl : l = []) {a : α} (h : a ∈ l) : False := by
  subst hl
  exact List.not_mem_nil h

end ListHelpers

theorem mem_notifyOut [DecidableEq Topic] {S : Sys Obj Actor Topic}
    {hs : List (Actor × Topic)} {p : Obj} {d : Actor × Obj} :
    d ∈ notifyOut S hs p ↔ ∃ h ∈ hs, h.2 = S.topic p ∧ d = (h.1, p) := by
  unfold notifyOut
  rw [List.mem_map]
  constructor
  · rintro ⟨h, hm, rfl⟩
    rw [List.mem_filter] at hm
    exact ⟨h, hm.1, of_decide_eq_true hm.2, rfl⟩
  · rintro ⟨h, hm, ht, rfl⟩
    exact ⟨h, List.mem_filter.2 ⟨hm, decide_eq_true ht⟩, rfl⟩

/-- The states that a step relation `R` reaches from the start of a run. `Reach S` is
    `ReachBy S (Step S)` (`reach_iff_reachBy`); the variants of §4 – §6 use `ReachBy`. -/
inductive ReachBy (S : Sys Obj Actor Topic) (R : St Obj Actor Topic → St Obj Actor Topic → Prop) :
    St Obj Actor Topic → Prop where
  | init : ReachBy S R (St.init S)
  | step {st st'} : ReachBy S R st → R st st' → ReachBy S R st'

theorem ReachBy.next {S : Sys Obj Actor Topic} {R : St Obj Actor Topic → St Obj Actor Topic → Prop}
    {st st' st'' : St Obj Actor Topic} (h : ReachBy S R st) (hs : R st st') (e : st' = st'') :
    ReachBy S R st'' :=
  e ▸ ReachBy.step h hs

theorem reach_iff_reachBy [DecidableEq Obj] [DecidableEq Actor] [DecidableEq Topic]
    {S : Sys Obj Actor Topic} {st : St Obj Actor Topic} : Reach S st ↔ ReachBy S (Step S) st := by
  constructor
  · intro h
    induction h with
    | init => exact ReachBy.init
    | step _ hs ih => exact ReachBy.step ih hs
  · intro h
    induction h with
    | init => exact Reach.init
    | step _ hs ih => exact Reach.step ih hs

/-- Two lists related pointwise (core Lean has no `List.Forall₂`). -/
inductive ListRel {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : ListRel R [] []
  | cons {a b l l'} : R a b → ListRel R l l' → ListRel R (a :: l) (b :: l')

/-! ## 1. Soundness -/

/-- Every component of the state holds objects of the concept (for `deliv`: the publication). -/
structure InCl (S : Sys Obj Actor Topic) (st : St Obj Actor Topic) : Prop where
  known    : ∀ x ∈ st.known, Cl S x
  inbox    : ∀ x ∈ st.inbox, Cl S x
  store    : ∀ x ∈ st.store, Cl S x
  replays  : ∀ x ∈ st.replays, Cl S x
  notifies : ∀ x ∈ st.notifies, Cl S x
  deliv    : ∀ d ∈ st.deliv, Cl S d.2

theorem inCl_init (S : Sys Obj Actor Topic) : InCl S (St.init S) :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => Cl.root h,
   fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
   fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩

theorem inCl_step [DecidableEq Obj] [DecidableEq Actor] [DecidableEq Topic]
    {S : Sys Obj Actor Topic} {st st' : St Obj Actor Topic}
    (h : Step S st st') (hI : InCl S st) : InCl S st' := by
  cases h with
  | dup _ _ =>
    exact ⟨hI.known, fun y hy => hI.inbox y (List.mem_of_mem_erase hy), hI.store, hI.replays,
      hI.notifies, hI.deliv⟩
  | @proc x out hx _ hout =>
    have hxc : Cl S x := hI.inbox x hx
    have hc : ∀ y, y ∈ x :: st.known → Cl S y := fun y hy => by
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hxc
      · exact hI.known y hy
    refine ⟨hc, ?_, ?_, ?_, ?_, hI.deliv⟩
    · intro y hy
      rcases List.mem_append.1 hy with hy | hy
      · exact hI.inbox y (List.mem_of_mem_erase hy)
      · obtain ⟨ps, hr, -, hps⟩ := hout.sound y hy
        exact Cl.rule hr (fun p hp => hc p (hps p hp))
    · intro y hy
      rcases mem_ite_cons hy with rfl | hy
      · exact hxc
      · exact hI.store y hy
    · intro y hy
      rcases mem_ite_cons hy with rfl | hy
      · exact hxc
      · exact hI.replays y hy
    · intro y hy
      rcases mem_ite_cons hy with rfl | hy
      · exact hxc
      · exact hI.notifies y hy
  | @replay s out _ hout =>
    refine ⟨hI.known, ?_, hI.store, fun y hy => hI.replays y (List.mem_of_mem_erase hy),
      hI.notifies, hI.deliv⟩
    intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · exact hI.inbox y hy
    · obtain ⟨ss, p, hj, hss, hp⟩ := hout.sound y hy
      exact Cl.join hj (fun s' h => hI.known s' (hss s' h)) (hI.store p hp)
  | @notify p hp =>
    refine ⟨hI.known, hI.inbox, hI.store, hI.replays,
      fun y hy => hI.notifies y (List.mem_of_mem_erase hy), ?_⟩
    intro d hd
    rcases List.mem_append.1 hd with hd | hd
    · exact hI.deliv d hd
    · obtain ⟨_, _, _, rfl⟩ := mem_notifyOut.1 hd
      exact hI.notifies p hp
  | @deliver A p out hd hout =>
    refine ⟨hI.known, ?_, hI.store, hI.replays, hI.notifies,
      fun d h => hI.deliv d (List.mem_of_mem_erase h)⟩
    intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · exact hI.inbox y hy
    · obtain ⟨ss, hj, hss⟩ := hout.sound y hy
      exact Cl.join hj (fun s h => hI.known s (hss s h)) (hI.deliv (A, p) hd)

/-- **Soundness.** Every object of `known`, `inbox`, `store`, `replays`, `notifies` and every
    publication of `deliv` of a reachable state is in `Cl S` (no `WF` needed). -/
theorem reach_sound [DecidableEq Obj] [DecidableEq Actor] [DecidableEq Topic]
    {S : Sys Obj Actor Topic} {st : St Obj Actor Topic} (hR : Reach S st) : InCl S st := by
  induction hR with
  | init => exact inCl_init S
  | step _ hs ih => exact inCl_step hs ih

#print axioms reach_sound

/-! ## 2. Completeness -/

/-- `x` is processed or in flight. -/
def KnownOrInbox (st : St Obj Actor Topic) (x : Obj) : Prop := x ∈ st.known ∨ x ∈ st.inbox

/-- The join instance `ss p c` is covered (`P st c`) or one of its three pending ways is open:
    a replay of one of its subscriptions, the notification of its publication, a delivery of its
    publication to its subscriber. -/
def JoinPending (S : Sys Obj Actor Topic) (P : St Obj Actor Topic → Obj → Prop)
    (st : St Obj Actor Topic) (ss : List Obj) (p c : Obj) : Prop :=
  P st c ∨ (∃ s ∈ ss, s ∈ st.replays) ∨ p ∈ st.notifies ∨ ∃ s ∈ ss, (S.owner s, p) ∈ st.deliv

/-- The coverage invariant, generic in what "covered" means (`P`): `KnownOrInbox` for `Step`,
    `Covered dom` for `StepD` (§5 of this file). -/
structure CovInv (S : Sys Obj Actor Topic) (P : St Obj Actor Topic → Obj → Prop)
    (st : St Obj Actor Topic) : Prop where
  hand  : ∀ s ∈ st.known, S.isSub s = true → (S.owner s, S.topic s) ∈ st.handlers
  store : ∀ p ∈ st.known, S.isPub p = true → p ∈ st.store
  root  : ∀ r ∈ S.roots, P st r
  rule  : ∀ ps c, S.rule ps c → (∀ p ∈ ps, p ∈ st.known) → P st c
  join  : ∀ ss p c, S.join ss p c → (∀ s ∈ ss, s ∈ st.known) → p ∈ st.store →
            JoinPending S P st ss p c

section Coverage
variable [DecidableEq Obj] [DecidableEq Actor] [DecidableEq Topic] {S : Sys Obj Actor Topic}

/-- `KnownOrInbox` is kept by every step: an object leaves the inbox only when it is processed
    (`proc`) or already processed (`dup`). -/
theorem koi_step {st st' : St Obj Actor Topic} (h : Step S st st') {x : Obj}
    (hx : KnownOrInbox st x) : KnownOrInbox st' x := by
  cases h with
  | @dup y _ hk =>
    rcases hx with hx | hx
    · exact Or.inl hx
    · rcases mem_erase_or (b := y) hx with rfl | hx
      · exact Or.inl hk
      · exact Or.inr hx
  | @proc y out _ _ _ =>
    rcases hx with hx | hx
    · exact Or.inl (List.mem_cons_of_mem _ hx)
    · rcases mem_erase_or (b := y) hx with rfl | hx
      · exact Or.inl List.mem_cons_self
      · exact Or.inr (List.mem_append_left _ hx)
  | replay _ _ =>
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (List.mem_append_left _ hx)
  | notify _ => exact hx
  | deliver _ _ =>
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (List.mem_append_left _ hx)

omit [DecidableEq Obj] [DecidableEq Actor] [DecidableEq Topic] in
private theorem jp_mono {P : St Obj Actor Topic → Obj → Prop} {st st' : St Obj Actor Topic}
    {ss : List Obj} {p c : Obj}
    (hP : ∀ x, P st x → P st' x) (hr : ∀ s, s ∈ st.replays → s ∈ st'.replays)
    (hn : ∀ q, q ∈ st.notifies → q ∈ st'.notifies) (hd : ∀ d, d ∈ st.deliv → d ∈ st'.deliv) :
    JoinPending S P st ss p c → JoinPending S P st' ss p c
  | Or.inl h => Or.inl (hP c h)
  | Or.inr (Or.inl ⟨s, hs, h⟩) => Or.inr (Or.inl ⟨s, hs, hr s h⟩)
  | Or.inr (Or.inr (Or.inl h)) => Or.inr (Or.inr (Or.inl (hn p h)))
  | Or.inr (Or.inr (Or.inr ⟨s, hs, h⟩)) => Or.inr (Or.inr (Or.inr ⟨s, hs, hd _ h⟩))

omit [DecidableEq Obj] [DecidableEq Actor] [DecidableEq Topic] in
theorem covInv_init (hWF : S.WF) {P : St Obj Actor Topic → Obj → Prop}
    (hKI : ∀ st x, KnownOrInbox st x → P st x) : CovInv S P (St.init S) := by
  refine ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    fun r hr => hKI _ r (Or.inr hr), ?_, fun _ _ _ _ _ hp => absurd hp List.not_mem_nil⟩
  intro ps c hr hps
  obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil ps (hWF.rule_ne ps c hr)
  exact absurd (hps p hp) List.not_mem_nil

/-- The coverage invariant is kept by every step of `Step`, for every `P` that contains
    `KnownOrInbox` and is kept by that step. -/
theorem covInv_step (hWF : S.WF) {P : St Obj Actor Topic → Obj → Prop}
    (hKI : ∀ st x, KnownOrInbox st x → P st x) {st st' : St Obj Actor Topic}
    (h : Step S st st') (hP : ∀ x, P st x → P st' x) (hI : CovInv S P st) : CovInv S P st' := by
  cases h with
  | dup _ _ =>
    exact ⟨hI.hand, hI.store, fun r hr => hP r (hI.root r hr),
      fun ps c hr hps => hP c (hI.rule ps c hr hps),
      fun ss p c hj hss hp => jp_mono hP (fun _ h => h) (fun _ h => h) (fun _ h => h)
        (hI.join ss p c hj hss hp)⟩
  | @proc x out _ hk hout =>
    refine ⟨?_, ?_, fun r hr => hP r (hI.root r hr), ?_, ?_⟩
    · -- (H) the new subscription registers its handler
      intro s hs hsub
      rcases List.mem_cons.1 hs with rfl | hs
      · exact mem_ite_cons_self hsub
      · exact mem_ite_cons_of_mem (hI.hand s hs hsub)
    · -- (H) the new publication is inserted
      intro p hp hpub
      rcases List.mem_cons.1 hp with rfl | hp
      · exact mem_ite_cons_self hpub
      · exact mem_ite_cons_of_mem (hI.store p hp hpub)
    · -- (L) a rule with `x` as a premise fires now; the others were covered before
      intro ps c hr hps
      by_cases hxp : x ∈ ps
      · exact hKI _ c (Or.inr (List.mem_append_right _ (hout.complete ps c hr hxp hps)))
      · refine hP c (hI.rule ps c hr (fun p hp => ?_))
        rcases List.mem_cons.1 (hps p hp) with e | h
        · exact absurd (e ▸ hp) hxp
        · exact h
    · -- (J) a join with `x` as a subscription: its replay is pending now; with `x` as the
      -- publication: its notification is pending now; otherwise: as before
      intro ss p c hj hss hp
      by_cases hxs : x ∈ ss
      · exact Or.inr (Or.inl ⟨x, hxs, mem_ite_cons_self (hWF.join_sub ss p c hj x hxs).1⟩)
      · have hss' : ∀ s ∈ ss, s ∈ st.known := fun s hs => by
          rcases List.mem_cons.1 (hss s hs) with e | h
          · exact absurd (e ▸ hs) hxs
          · exact h
        rcases mem_ite_cons hp with e | hp
        · subst e
          exact Or.inr (Or.inr (Or.inl (mem_ite_cons_self (hWF.join_pub ss _ c hj))))
        · exact jp_mono hP (fun _ h => mem_ite_cons_of_mem h) (fun _ h => mem_ite_cons_of_mem h)
            (fun _ h => h) (hI.join ss p c hj hss' hp)
  | @replay s out _ hout =>
    refine ⟨hI.hand, hI.store, fun r hr => hP r (hI.root r hr),
      fun ps c hr hps => hP c (hI.rule ps c hr hps), ?_⟩
    intro ss p c hj hss hp
    rcases hI.join ss p c hj hss hp with h | ⟨s', hs', hr⟩ | h | h
    · exact Or.inl (hP c h)
    · by_cases e : s' = s
      · exact Or.inl (hKI _ c (Or.inr (List.mem_append_right _
          (hout.complete ss p c hj (e ▸ hs') hss hp))))
      · exact Or.inr (Or.inl ⟨s', hs', mem_erase_of_ne' e hr⟩)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  | @notify p0 _ =>
    refine ⟨hI.hand, hI.store, fun r hr => hP r (hI.root r hr),
      fun ps c hr hps => hP c (hI.rule ps c hr hps), ?_⟩
    intro ss p c hj hss hp
    rcases hI.join ss p c hj hss hp with h | h | hn | ⟨s', hs', hd⟩
    · exact Or.inl (hP c h)
    · exact Or.inr (Or.inl h)
    · by_cases e : p = p0
      · subst e
        obtain ⟨s', hs'⟩ := List.exists_mem_of_ne_nil ss (hWF.join_ne ss p c hj)
        obtain ⟨hsub, htop⟩ := hWF.join_sub ss p c hj s' hs'
        exact Or.inr (Or.inr (Or.inr ⟨s', hs', List.mem_append_right _
          (mem_notifyOut.2 ⟨(S.owner s', S.topic s'), hI.hand s' (hss s' hs') hsub, htop, rfl⟩)⟩))
      · exact Or.inr (Or.inr (Or.inl (mem_erase_of_ne' e hn)))
    · exact Or.inr (Or.inr (Or.inr ⟨s', hs', List.mem_append_left _ hd⟩))
  | @deliver A p0 out _ hout =>
    refine ⟨hI.hand, hI.store, fun r hr => hP r (hI.root r hr),
      fun ps c hr hps => hP c (hI.rule ps c hr hps), ?_⟩
    intro ss p c hj hss hp
    rcases hI.join ss p c hj hss hp with h | h | h | ⟨s', hs', hd⟩
    · exact Or.inl (hP c h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · by_cases e : (S.owner s', p) = (A, p0)
      · have hA : S.owner s' = A := congrArg Prod.fst e
        have hp0 : p = p0 := congrArg Prod.snd e
        subst hp0
        exact Or.inl (hKI _ c (Or.inr (List.mem_append_right _ (hout.complete ss c hj
          (fun s hs => ⟨hss s hs, (hWF.join_owner ss p c hj s hs s' hs').trans hA⟩)))))
      · exact Or.inr (Or.inr (Or.inr ⟨s', hs', mem_erase_of_ne' e hd⟩))

theorem reach_covInv (hWF : S.WF) {st : St Obj Actor Topic} (hR : Reach S st) :
    CovInv S KnownOrInbox st := by
  induction hR with
  | init => exact covInv_init hWF (fun _ _ h => h)
  | step _ hs ih => exact covInv_step hWF (fun _ _ h => h) hs (fun _ hx => koi_step hs hx) ih

end Coverage

theorem koi_quiescent {st : St Obj Actor Topic} (hQ : st.Quiescent) {x : Obj} :
    KnownOrInbox st x → x ∈ st.known
  | Or.inl h => h
  | Or.inr h => (false_of_mem_nil hQ.1 h).elim

theorem jp_quiescent {S : Sys Obj Actor Topic} {P : St Obj Actor Topic → Obj → Prop}
    {st : St Obj Actor Topic} (hQ : st.Quiescent) {ss : List Obj} {p c : Obj} :
    JoinPending S P st ss p c → P st c
  | Or.inl h => h
  | Or.inr (Or.inl ⟨_, _, h⟩) => (false_of_mem_nil hQ.2.1 h).elim
  | Or.inr (Or.inr (Or.inl h)) => (false_of_mem_nil hQ.2.2.1 h).elim
  | Or.inr (Or.inr (Or.inr ⟨_, _, h⟩)) => (false_of_mem_nil hQ.2.2.2 h).elim

section Main
variable [DecidableEq Obj] [DecidableEq Actor] [DecidableEq Topic] {S : Sys Obj Actor Topic}

/-- **Completeness.** At a reachable quiescent state every object of the concept is processed. -/
theorem quiescent_complete (hWF : S.WF) {st : St Obj Actor Topic} (hR : Reach S st)
    (hQ : st.Quiescent) {x : Obj} (hx : Cl S x) : x ∈ st.known := by
  have hI := reach_covInv hWF hR
  induction hx with
  | @root r hr => exact koi_quiescent hQ (hI.root r hr)
  | @rule ps c hr _ ih => exact koi_quiescent hQ (hI.rule ps c hr ih)
  | @join ss p c hj _ _ ihs ihp =>
    exact koi_quiescent hQ (jp_quiescent hQ
      (hI.join ss p c hj ihs (hI.store p ihp (hWF.join_pub ss p c hj))))

#print axioms quiescent_complete

/-- **Exactness.** At a reachable quiescent state the processed objects are the concept. -/
theorem quiescent_exact (hWF : S.WF) {st : St Obj Actor Topic} (hR : Reach S st)
    (hQ : st.Quiescent) {x : Obj} : x ∈ st.known ↔ Cl S x :=
  ⟨(reach_sound hR).known x, quiescent_complete hWF hR hQ⟩

#print axioms quiescent_exact

/-- **No lost join** (a summary edge is never lost): at a reachable quiescent state, a join
    instance whose subscriptions and publication are processed has its conclusion processed. -/
theorem no_lost_join (hWF : S.WF) {st : St Obj Actor Topic} (hR : Reach S st)
    (hQ : st.Quiescent) {ss : List Obj} {p c : Obj} (hj : S.join ss p c)
    (hss : ∀ s ∈ ss, s ∈ st.known) (hp : p ∈ st.known) : c ∈ st.known := by
  have hI := reach_covInv hWF hR
  exact koi_quiescent hQ (jp_quiescent hQ
    (hI.join ss p c hj hss (hI.store p hp (hWF.join_pub ss p c hj))))

#print axioms no_lost_join

end Main

/-! ## 3. Counterexamples: the protocol conditions (§4) -/

section Variants
variable [DecidableEq Obj] [DecidableEq Actor] [DecidableEq Topic]

/-- P1 without "register before read": the subscriber READS the storage when it processes the
    subscription (`proc` sends the joins of `x` with the stored publications) and REGISTERS its
    handler only at the deferred step `register` (in this variant `replays` holds the pending
    registrations). The other steps are the steps of `Step`. -/
inductive StepP1 (S : Sys Obj Actor Topic) : St Obj Actor Topic → St Obj Actor Topic → Prop where
  | dup {st x} : x ∈ st.inbox → x ∈ st.known →
      StepP1 S st { st with inbox := st.inbox.erase x }
  | proc {st x out rout} : x ∈ st.inbox → x ∉ st.known → ProcOut S st.known x out →
      ReplayOut S (x :: st.known) st.store x rout →
      StepP1 S st
        { known    := x :: st.known
          inbox    := st.inbox.erase x ++ out ++ rout
          store    := if S.isPub x then x :: st.store else st.store
          handlers := st.handlers
          replays  := if S.isSub x then x :: st.replays else st.replays
          notifies := if S.isPub x then x :: st.notifies else st.notifies
          deliv    := st.deliv }
  | register {st s} : s ∈ st.replays →
      StepP1 S st { st with replays := st.replays.erase s,
                            handlers := (S.owner s, S.topic s) :: st.handlers }
  | notify {st p} : p ∈ st.notifies →
      StepP1 S st { st with notifies := st.notifies.erase p,
                            deliv := st.deliv ++ notifyOut S st.handlers p }
  | deliver {st A p out} : (A, p) ∈ st.deliv → DeliverOut S st.known A p out →
      StepP1 S st { st with deliv := st.deliv.erase (A, p), inbox := st.inbox ++ out }

/-- P2 without "insert before notify": the publisher READS the handler list when it processes
    the publication (`proc` sends the deliveries) and INSERTS the publication into the storage
    only at the deferred step `insert` (in this variant `notifies` holds the pending
    insertions). The other steps are the steps of `Step`. -/
inductive StepP2 (S : Sys Obj Actor Topic) : St Obj Actor Topic → St Obj Actor Topic → Prop where
  | dup {st x} : x ∈ st.inbox → x ∈ st.known →
      StepP2 S st { st with inbox := st.inbox.erase x }
  | proc {st x out} : x ∈ st.inbox → x ∉ st.known → ProcOut S st.known x out →
      StepP2 S st
        { known    := x :: st.known
          inbox    := st.inbox.erase x ++ out
          store    := st.store
          handlers := if S.isSub x then (S.owner x, S.topic x) :: st.handlers else st.handlers
          replays  := if S.isSub x then x :: st.replays else st.replays
          notifies := if S.isPub x then x :: st.notifies else st.notifies
          deliv    := if S.isPub x then st.deliv ++ notifyOut S st.handlers x else st.deliv }
  | replay {st s out} : s ∈ st.replays → ReplayOut S st.known st.store s out →
      StepP2 S st { st with replays := st.replays.erase s, inbox := st.inbox ++ out }
  | insert {st p} : p ∈ st.notifies →
      StepP2 S st { st with notifies := st.notifies.erase p, store := p :: st.store }
  | deliver {st A p out} : (A, p) ∈ st.deliv → DeliverOut S st.known A p out →
      StepP2 S st { st with deliv := st.deliv.erase (A, p), inbox := st.inbox ++ out }

/-- P3 without a linearizable read: `Step`, plus a replay that reads any SUBLIST of the storage
    (it can miss a stored publication). -/
inductive StepP3 (S : Sys Obj Actor Topic) : St Obj Actor Topic → St Obj Actor Topic → Prop where
  | step {st st'} : Step S st st' → StepP3 S st st'
  | replaySub {st s store' out} : s ∈ st.replays → store'.Sublist st.store →
      ReplayOut S st.known store' s out →
      StepP3 S st { st with replays := st.replays.erase s, inbox := st.inbox ++ out }

/-- P4 without one match predicate: the delivery matches with the join relation `join'` (the
    push path), the replay with `S.join`. The other steps are the steps of `Step`. -/
inductive StepP4 (S : Sys Obj Actor Topic) (join' : List Obj → Obj → Obj → Prop) :
    St Obj Actor Topic → St Obj Actor Topic → Prop where
  | dup {st x} : x ∈ st.inbox → x ∈ st.known →
      StepP4 S join' st { st with inbox := st.inbox.erase x }
  | proc {st x out} : x ∈ st.inbox → x ∉ st.known → ProcOut S st.known x out →
      StepP4 S join' st
        { known    := x :: st.known
          inbox    := st.inbox.erase x ++ out
          store    := if S.isPub x then x :: st.store else st.store
          handlers := if S.isSub x then (S.owner x, S.topic x) :: st.handlers else st.handlers
          replays  := if S.isSub x then x :: st.replays else st.replays
          notifies := if S.isPub x then x :: st.notifies else st.notifies
          deliv    := st.deliv }
  | replay {st s out} : s ∈ st.replays → ReplayOut S st.known st.store s out →
      StepP4 S join' st { st with replays := st.replays.erase s, inbox := st.inbox ++ out }
  | notify {st p} : p ∈ st.notifies →
      StepP4 S join' st { st with notifies := st.notifies.erase p,
                                  deliv := st.deliv ++ notifyOut S st.handlers p }
  | deliver {st A p out} : (A, p) ∈ st.deliv →
      DeliverOut { S with join := join' } st.known A p out →
      StepP4 S join' st { st with deliv := st.deliv.erase (A, p), inbox := st.inbox ++ out }

abbrev ReachP1 (S : Sys Obj Actor Topic) := ReachBy S (StepP1 S)
abbrev ReachP2 (S : Sys Obj Actor Topic) := ReachBy S (StepP2 S)
abbrev ReachP3 (S : Sys Obj Actor Topic) := ReachBy S (StepP3 S)
abbrev ReachP4 (S : Sys Obj Actor Topic) (join' : List Obj → Obj → Obj → Prop) :=
  ReachBy S (StepP4 S join')

end Variants

namespace PCex

/-- The objects: one subscription, one publication, one summary edge. -/
inductive O | sub | pub | edge
  deriving DecidableEq

/-- The actors: the caller (subscriber) and the callee (publisher). -/
inductive Ac | caller | callee
  deriving DecidableEq

/-- One join `[sub] pub ⟶ edge`, no local rule, roots `[sub, pub]`, one topic. -/
def sys : Sys O Ac Unit where
  owner o := match o with
    | .pub => .callee
    | _ => .caller
  roots := [.sub, .pub]
  rule _ _ := False
  isSub o := match o with
    | .sub => true
    | _ => false
  isPub o := match o with
    | .pub => true
    | _ => false
  topic _ := ()
  join ss p c := ss = [.sub] ∧ p = .pub ∧ c = .edge

theorem wf : sys.WF where
  rule_ne _ _ h := False.elim h
  rule_local _ _ h := False.elim h
  join_ne ss p c h := by
    have h' : ss = [O.sub] ∧ p = O.pub ∧ c = O.edge := h
    rw [h'.1]
    exact List.cons_ne_nil _ _
  join_sub ss p c h s hs := by
    have h' : ss = [O.sub] ∧ p = O.pub ∧ c = O.edge := h
    rw [h'.1] at hs
    rw [List.mem_singleton.1 hs, h'.2.1]
    exact ⟨rfl, rfl⟩
  join_pub ss p c h := by
    have h' : ss = [O.sub] ∧ p = O.pub ∧ c = O.edge := h
    rw [h'.2.1]
    rfl
  join_owner ss p c h s hs s' hs' := by
    have h' : ss = [O.sub] ∧ p = O.pub ∧ c = O.edge := h
    rw [h'.1] at hs hs'
    rw [List.mem_singleton.1 hs, List.mem_singleton.1 hs']

theorem cl_edge : Cl sys O.edge :=
  Cl.join (ss := [O.sub]) (p := O.pub) ⟨rfl, rfl, rfl⟩
    (fun s hs => by rw [List.mem_singleton.1 hs]; exact Cl.root (by decide))
    (Cl.root (by decide))

/-- The correct protocol finds `edge` at every reachable quiescent state. -/
theorem step_finds_edge {st : St O Ac Unit} (hR : Reach sys st) (hQ : st.Quiescent) :
    O.edge ∈ st.known :=
  quiescent_complete wf hR hQ cl_edge

#print axioms step_finds_edge

theorem procOut_nil {k : List O} {x : O} : ProcOut sys k x [] :=
  ⟨fun _ _ h _ _ => False.elim h, fun _ h => absurd h List.not_mem_nil⟩

theorem replayOut_nil {k : List O} {s : O} : ReplayOut sys k [] s [] :=
  ⟨fun _ _ _ _ _ _ hp => absurd hp List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩

/-- P1 trace: `proc sub` (reads the empty storage), `proc pub`, `notify pub` (no handler yet),
    `register sub`. -/
def p1s1 : St O Ac Unit := ⟨[.sub], [.pub], [], [], [.sub], [], []⟩
def p1s2 : St O Ac Unit := ⟨[.pub, .sub], [], [.pub], [], [.sub], [.pub], []⟩
def p1s3 : St O Ac Unit := ⟨[.pub, .sub], [], [.pub], [], [.sub], [], []⟩
def p1s4 : St O Ac Unit := ⟨[.pub, .sub], [], [.pub], [(.caller, ())], [], [], []⟩

theorem cex_P1 :
    ∃ st, ReachP1 sys st ∧ st.Quiescent ∧ Cl sys O.edge ∧ O.edge ∉ st.known := by
  have h1 : ReachP1 sys p1s1 := ReachBy.next ReachBy.init
    (StepP1.proc (x := O.sub) (out := []) (rout := []) (by decide) (by decide)
      procOut_nil replayOut_nil) rfl
  have h2 : ReachP1 sys p1s2 := ReachBy.next h1
    (StepP1.proc (x := O.pub) (out := []) (rout := []) (by decide) (by decide)
      procOut_nil replayOut_nil) rfl
  have h3 : ReachP1 sys p1s3 := ReachBy.next h2 (StepP1.notify (p := O.pub) (by decide)) rfl
  have h4 : ReachP1 sys p1s4 := ReachBy.next h3 (StepP1.register (s := O.sub) (by decide)) rfl
  exact ⟨p1s4, h4, ⟨rfl, rfl, rfl, rfl⟩, cl_edge, by decide⟩

#print axioms cex_P1

/-- P2 trace: `proc pub` (reads the empty handler list), `proc sub`, `replay sub` (the storage
    is still empty), `insert pub`. -/
def p2s1 : St O Ac Unit := ⟨[.pub], [.sub], [], [], [], [.pub], []⟩
def p2s2 : St O Ac Unit := ⟨[.sub, .pub], [], [], [(.caller, ())], [.sub], [.pub], []⟩
def p2s3 : St O Ac Unit := ⟨[.sub, .pub], [], [], [(.caller, ())], [], [.pub], []⟩
def p2s4 : St O Ac Unit := ⟨[.sub, .pub], [], [.pub], [(.caller, ())], [], [], []⟩

theorem cex_P2 :
    ∃ st, ReachP2 sys st ∧ st.Quiescent ∧ Cl sys O.edge ∧ O.edge ∉ st.known := by
  have h1 : ReachP2 sys p2s1 := ReachBy.next ReachBy.init
    (StepP2.proc (x := O.pub) (out := []) (by decide) (by decide) procOut_nil) rfl
  have h2 : ReachP2 sys p2s2 := ReachBy.next h1
    (StepP2.proc (x := O.sub) (out := []) (by decide) (by decide) procOut_nil) rfl
  have h3 : ReachP2 sys p2s3 := ReachBy.next h2
    (StepP2.replay (s := O.sub) (out := []) (by decide) replayOut_nil) rfl
  have h4 : ReachP2 sys p2s4 := ReachBy.next h3 (StepP2.insert (p := O.pub) (by decide)) rfl
  exact ⟨p2s4, h4, ⟨rfl, rfl, rfl, rfl⟩, cl_edge, by decide⟩

#print axioms cex_P2

/-- P3 trace: `proc pub`, `notify pub` (no handler yet), `proc sub`, `replay sub` reading the
    empty sublist of the storage `[pub]`. -/
def p3s1 : St O Ac Unit := ⟨[.pub], [.sub], [.pub], [], [], [.pub], []⟩
def p3s2 : St O Ac Unit := ⟨[.pub], [.sub], [.pub], [], [], [], []⟩
def p3s3 : St O Ac Unit := ⟨[.sub, .pub], [], [.pub], [(.caller, ())], [.sub], [], []⟩
def p3s4 : St O Ac Unit := ⟨[.sub, .pub], [], [.pub], [(.caller, ())], [], [], []⟩

theorem cex_P3 :
    ∃ st, ReachP3 sys st ∧ st.Quiescent ∧ Cl sys O.edge ∧ O.edge ∉ st.known := by
  have h1 : ReachP3 sys p3s1 := ReachBy.next ReachBy.init
    (StepP3.step (Step.proc (x := O.pub) (out := []) (by decide) (by decide) procOut_nil)) rfl
  have h2 : ReachP3 sys p3s2 := ReachBy.next h1
    (StepP3.step (Step.notify (p := O.pub) (by decide))) rfl
  have h3 : ReachP3 sys p3s3 := ReachBy.next h2
    (StepP3.step (Step.proc (x := O.sub) (out := []) (by decide) (by decide) procOut_nil)) rfl
  have h4 : ReachP3 sys p3s4 := ReachBy.next h3
    (StepP3.replaySub (s := O.sub) (store' := []) (out := []) (by decide) (List.nil_sublist _)
      replayOut_nil) rfl
  exact ⟨p3s4, h4, ⟨rfl, rfl, rfl, rfl⟩, cl_edge, by decide⟩

#print axioms cex_P3

/-- The push-path match of P4: it misses the pair `[sub] pub` (a subset of `sys.join`). -/
def joinP4 : List O → O → O → Prop := fun _ _ _ => False

theorem deliverOut_none {k : List O} {A : Ac} {p : O} :
    DeliverOut { sys with join := joinP4 } k A p [] :=
  ⟨fun _ _ h _ => False.elim h, fun _ h => absurd h List.not_mem_nil⟩

/-- P4 trace: `proc sub`, `replay sub` (the storage is empty), `proc pub`, `notify pub` (one
    delivery to the caller), `deliver (caller, pub)` matched with `joinP4`. -/
def p4s1 : St O Ac Unit := ⟨[.sub], [.pub], [], [(.caller, ())], [.sub], [], []⟩
def p4s2 : St O Ac Unit := ⟨[.sub], [.pub], [], [(.caller, ())], [], [], []⟩
def p4s3 : St O Ac Unit := ⟨[.pub, .sub], [], [.pub], [(.caller, ())], [], [.pub], []⟩
def p4s4 : St O Ac Unit :=
  ⟨[.pub, .sub], [], [.pub], [(.caller, ())], [], [], [(.caller, .pub)]⟩
def p4s5 : St O Ac Unit := ⟨[.pub, .sub], [], [.pub], [(.caller, ())], [], [], []⟩

theorem cex_P4 :
    (∀ ss p c, joinP4 ss p c → sys.join ss p c) ∧
    ∃ st, ReachP4 sys joinP4 st ∧ st.Quiescent ∧ Cl sys O.edge ∧ O.edge ∉ st.known := by
  refine ⟨fun _ _ _ h => False.elim h, ?_⟩
  have h1 : ReachP4 sys joinP4 p4s1 := ReachBy.next ReachBy.init
    (StepP4.proc (x := O.sub) (out := []) (by decide) (by decide) procOut_nil) rfl
  have h2 : ReachP4 sys joinP4 p4s2 := ReachBy.next h1
    (StepP4.replay (s := O.sub) (out := []) (by decide) replayOut_nil) rfl
  have h3 : ReachP4 sys joinP4 p4s3 := ReachBy.next h2
    (StepP4.proc (x := O.pub) (out := []) (by decide) (by decide) procOut_nil) rfl
  have h4 : ReachP4 sys joinP4 p4s4 := ReachBy.next h3
    (StepP4.notify (p := O.pub) (by decide)) rfl
  have h5 : ReachP4 sys joinP4 p4s5 := ReachBy.next h4
    (StepP4.deliver (A := Ac.caller) (p := O.pub) (out := []) (by decide) deliverOut_none) rfl
  exact ⟨p4s5, h5, ⟨rfl, rfl, rfl, rfl⟩, cl_edge, by decide⟩

#print axioms cex_P4

end PCex

/-! ## 4. Quiescence detection (§5) -/

namespace Quiesce

/-- The counter model: pending items, running handlers, the in-flight counter, the flag. -/
structure CSt where
  items   : Nat
  running : Nat
  cnt     : Nat
  done    : Bool

/-- The protocol: increment before a send, decrement after the handler ends; the decrement that
    reaches zero sets `done`. -/
inductive CStep : CSt → CSt → Prop where
  | start  {st : CSt} : 0 < st.items →
      CStep st ⟨st.items - 1, st.running + 1, st.cnt, st.done⟩
  | send   {st : CSt} : 0 < st.running →
      CStep st ⟨st.items + 1, st.running, st.cnt + 1, st.done⟩
  | finish {st : CSt} : 0 < st.running →
      CStep st ⟨st.items, st.running - 1, st.cnt - 1, decide (st.cnt - 1 = 0)⟩

/-- The start of a run: the driver is a phantom handler, counted and running, while it submits
    the roots (`send`); its `finish` releases the guard (`runAnalysis`). -/
def CSt.init : CSt := ⟨0, 1, 1, false⟩

inductive CReach : CSt → Prop where
  | init : CReach CSt.init
  | step {st st'} : CReach st → CStep st st' → CReach st'

/-- The invariant: the counter is the number of pending items plus running handlers, and the
    flag is set exactly when the counter is zero. -/
theorem creach_inv {st : CSt} (h : CReach st) :
    st.cnt = st.items + st.running ∧ (st.done = true ↔ st.cnt = 0) := by
  induction h with
  | init => exact ⟨rfl, by decide⟩
  | @step s _ _ hs ih =>
    obtain ⟨hc, hd⟩ := ih
    cases hs with
    | start hi => exact ⟨by simp only; omega, hd⟩
    | send hr =>
      have hd' : s.done = false := by
        cases e : s.done
        · rfl
        · have := hd.1 e; omega
      refine ⟨by simp only; omega, ?_⟩
      show s.done = true ↔ s.cnt + 1 = 0
      rw [hd']
      exact ⟨fun h => (by cases h), fun h => (by omega)⟩
    | finish hr =>
      refine ⟨by simp only; omega, ?_⟩
      exact decide_eq_true_iff

#print axioms creach_inv

/-- The counter is zero exactly when no item is pending and no handler runs. -/
theorem cnt_zero_iff {st : CSt} (h : CReach st) :
    st.cnt = 0 ↔ st.items = 0 ∧ st.running = 0 := by
  have hc := (creach_inv h).1
  constructor
  · intro h0
    exact Nat.eq_zero_of_add_eq_zero (hc.symm.trans h0)
  · intro ⟨h1, h2⟩
    rw [hc, h1, h2]

/-- The flag is set exactly when no item is pending and no handler runs. -/
theorem done_iff {st : CSt} (h : CReach st) :
    st.done = true ↔ st.items = 0 ∧ st.running = 0 :=
  (creach_inv h).2.trans (cnt_zero_iff h)

/-- **Quiescence detection.** When the flag is set, no item is pending, no handler runs, and no
    step is enabled (so the flag stays set and the declared completion is final). -/
theorem done_final {st : CSt} (h : CReach st) (hd : st.done = true) :
    st.items = 0 ∧ st.running = 0 ∧ ∀ st', ¬ CStep st st' := by
  obtain ⟨hi, hr⟩ := (done_iff h).1 hd
  refine ⟨hi, hr, fun st' hs => ?_⟩
  cases hs with
  | start h => omega
  | send h => omega
  | finish h => omega

#print axioms done_final

/-- The wrong protocol: the handler decrements when it STARTS (before its sends). -/
inductive BStep : CSt → CSt → Prop where
  | start  {st : CSt} : 0 < st.items →
      BStep st ⟨st.items - 1, st.running + 1, st.cnt - 1, decide (st.cnt - 1 = 0)⟩
  | send   {st : CSt} : 0 < st.running →
      BStep st ⟨st.items + 1, st.running, st.cnt + 1, st.done⟩
  | finish {st : CSt} : 0 < st.running →
      BStep st ⟨st.items, st.running - 1, st.cnt, st.done⟩

/-- The state after the guarded submission of one root (`creach_oneRoot`: the correct protocol
    reaches it). The wrong protocol starts here. -/
def CSt.oneRoot : CSt := ⟨1, 0, 1, false⟩

theorem creach_oneRoot : CReach CSt.oneRoot :=
  CReach.step (CReach.step CReach.init (CStep.send (st := CSt.init) (by decide)))
    (CStep.finish (st := ⟨1, 1, 2, false⟩) (by decide))

inductive BReach : CSt → Prop where
  | init : BReach CSt.oneRoot
  | step {st st'} : BReach st → BStep st st' → BReach st'

/-- **Counterexample.** With the decrement at the start, the root's handler sets `done` when it
    starts, and then sends an item: completion is declared while work remains. -/
theorem bad_early_done : ∃ st, BReach st ∧ st.done = true ∧ 0 < st.items :=
  ⟨⟨1, 1, 1, true⟩,
   BReach.step (BReach.step BReach.init (BStep.start (st := CSt.oneRoot) (by decide)))
     (BStep.send (st := ⟨0, 1, 0, true⟩) (by decide)),
   rfl, by decide⟩

#print axioms bad_early_done

end Quiesce

/-! ## 5. Dominance (§6) -/

section Dominance
variable [DecidableEq Obj] [DecidableEq Actor] [DecidableEq Topic]

/-- `Step` plus `drop`: an in-flight object dominated by a processed object of the same owner
    may be removed from the inbox. -/
inductive StepD (S : Sys Obj Actor Topic) (dom : Obj → Obj → Prop) :
    St Obj Actor Topic → St Obj Actor Topic → Prop where
  | step {st st'} : Step S st st' → StepD S dom st st'
  | drop {st x y} : x ∈ st.inbox → y ∈ st.known → dom x y → S.owner x = S.owner y →
      StepD S dom st { st with inbox := st.inbox.erase x }

abbrev ReachD (S : Sys Obj Actor Topic) (dom : Obj → Obj → Prop) := ReachBy S (StepD S dom)

/-- `x` is dominated by an object that is processed or in flight. -/
def Covered (dom : Obj → Obj → Prop) (st : St Obj Actor Topic) (x : Obj) : Prop :=
  ∃ y, dom x y ∧ KnownOrInbox st y

variable {S : Sys Obj Actor Topic} {dom : Obj → Obj → Prop}

theorem inCl_stepD {st st' : St Obj Actor Topic} (h : StepD S dom st st') (hI : InCl S st) :
    InCl S st' := by
  cases h with
  | step hs => exact inCl_step hs hI
  | drop _ _ _ _ =>
    exact ⟨hI.known, fun y hy => hI.inbox y (List.mem_of_mem_erase hy), hI.store, hI.replays,
      hI.notifies, hI.deliv⟩

/-- **Soundness with drops.** Dropping keeps soundness. -/
theorem reach_soundD {st : St Obj Actor Topic} (hR : ReachD S dom st) : InCl S st := by
  induction hR with
  | init => exact inCl_init S
  | step _ hs ih => exact inCl_stepD hs ih

#print axioms reach_soundD

theorem covered_stepD (htrans : ∀ x y z, dom x y → dom y z → dom x z)
    {st st' : St Obj Actor Topic} (h : StepD S dom st st') {x : Obj}
    (hx : Covered dom st x) : Covered dom st' x := by
  obtain ⟨y, hxy, hy⟩ := hx
  cases h with
  | step hs => exact ⟨y, hxy, koi_step hs hy⟩
  | @drop x0 y0 _ hy0 hd _ =>
    rcases hy with hy | hy
    · exact ⟨y, hxy, Or.inl hy⟩
    · rcases mem_erase_or (b := x0) hy with rfl | hy
      · exact ⟨y0, htrans _ _ _ hxy hd, Or.inl hy0⟩
      · exact ⟨y, hxy, Or.inr hy⟩

theorem reachD_covInv (hWF : S.WF) (hrefl : ∀ x, dom x x)
    (htrans : ∀ x y z, dom x y → dom y z → dom x z) {st : St Obj Actor Topic}
    (hR : ReachD S dom st) : CovInv S (Covered dom) st := by
  have hKI : ∀ (st : St Obj Actor Topic) x, KnownOrInbox st x → Covered dom st x :=
    fun _ x h => ⟨x, hrefl x, h⟩
  induction hR with
  | init => exact covInv_init hWF hKI
  | step _ hs ih =>
    have hP := fun x hx => covered_stepD htrans hs (x := x) hx
    cases hs with
    | step hs => exact covInv_step hWF hKI hs hP ih
    | drop _ _ _ _ =>
      exact ⟨ih.hand, ih.store, fun r hr => hP r (ih.root r hr),
        fun ps c hr hps => hP c (ih.rule ps c hr hps),
        fun ss p c hj hss hp => jp_mono hP (fun _ h => h) (fun _ h => h) (fun _ h => h)
          (ih.join ss p c hj hss hp)⟩

omit [DecidableEq Obj] [DecidableEq Actor] [DecidableEq Topic] in
private theorem choose_rel {R : Obj → Obj → Prop} {Q : Obj → Prop} :
    ∀ {ps : List Obj}, (∀ p ∈ ps, ∃ y, Q y ∧ R p y) → ∃ qs, ListRel R ps qs ∧ ∀ q ∈ qs, Q q
  | [], _ => ⟨[], ListRel.nil, fun _ h => absurd h List.not_mem_nil⟩
  | p :: ps, h => by
    obtain ⟨y, hq, hy⟩ := h p List.mem_cons_self
    obtain ⟨qs, hr, hqs⟩ := choose_rel (ps := ps) (fun p' hp' => h p' (List.mem_cons_of_mem _ hp'))
    refine ⟨y :: qs, ListRel.cons hy hr, fun q hq' => ?_⟩
    rcases List.mem_cons.1 hq' with rfl | hq'
    · exact hq
    · exact hqs q hq'

omit [DecidableEq Obj] [DecidableEq Actor] [DecidableEq Topic] in
private theorem covered_quiescent {st : St Obj Actor Topic} (hQ : st.Quiescent) {x : Obj} :
    Covered dom st x → ∃ y ∈ st.known, dom x y
  | ⟨y, hxy, hy⟩ => ⟨y, koi_quiescent hQ hy, hxy⟩

/-- **Dominance.** With a preorder `dom` that the local rules and the joins simulate, at a
    reachable quiescent state of `StepD` every object of the concept is dominated by a
    processed object. -/
theorem quiescent_dominates (hWF : S.WF) (hrefl : ∀ x, dom x x)
    (htrans : ∀ x y z, dom x y → dom y z → dom x z)
    (hrule : ∀ {ps qs c}, S.rule ps c → ListRel dom ps qs → ∃ c', S.rule qs c' ∧ dom c c')
    (hjoin : ∀ {ss ts p q c}, S.join ss p c → ListRel dom ss ts → dom p q →
      ∃ c', S.join ts q c' ∧ dom c c')
    {st : St Obj Actor Topic} (hR : ReachD S dom st) (hQ : st.Quiescent)
    {x : Obj} (hx : Cl S x) : ∃ y ∈ st.known, dom x y := by
  have hI := reachD_covInv hWF hrefl htrans hR
  induction hx with
  | @root r hr => exact covered_quiescent hQ (hI.root r hr)
  | @rule ps c hr _ ih =>
    obtain ⟨qs, hrel, hqs⟩ := choose_rel ih
    obtain ⟨c', hr', hcc⟩ := hrule hr hrel
    obtain ⟨y, hy, hcy⟩ := covered_quiescent hQ (hI.rule qs c' hr' hqs)
    exact ⟨y, hy, htrans _ _ _ hcc hcy⟩
  | @join ss p c hj _ _ ihs ihp =>
    obtain ⟨ts, hrel, hts⟩ := choose_rel ihs
    obtain ⟨q, hq, hpq⟩ := ihp
    obtain ⟨c', hj', hcc⟩ := hjoin hj hrel hpq
    obtain ⟨y, hy, hcy⟩ := covered_quiescent hQ (jp_quiescent hQ
      (hI.join ts q c' hj' hts (hI.store q hq (hWF.join_pub ts q c' hj'))))
    exact ⟨y, hy, htrans _ _ _ hcc hcy⟩

#print axioms quiescent_dominates

end Dominance

end ApSpec.Pipeline

/-
  ApSpec.LoopReplayOnce — rule P2 of spec/next-iteration-p1-p3.md: a loop block replays the saved
  records for one (link, value) offer once per run (engine/MethodBlockRuntime.kt `offerChild`).

  Model. An offer `o` is a (LocalLink, Facts) pair. `R o` is what the saved replay of `o` produces:
  completions and terminal rows. In production `R` reads only frozen run inputs (the read-only
  record view, the saved targets, the frozen demand snapshot, the pure admission policy) and pure
  caches, so it is a function of `o` alone. The stores only grow in a run: an output that is already
  stored gives no fresh delta (`ScopedEdgeStore.addAll`, `rawTargetRows.add`, `KaryJoin.add`).
  A fresh output can make new offers (`routeCompleted` → `routeInside` → `offerChild`); `next` may read
  the current store (production reads `starts` at that moment).

  The worklist step pops one offer. `stepNative` replays it; `stepOnce` (P2) skips an offer that it
  replayed before. Theorem `runOnce_eq`: from the same state, both give the same store and the same
  worklist after every number of steps. So P2 changes no result and no later work, it only removes
  replays that give nothing.

  Constructive: no classical axioms beyond `propext` (simp).
-/

namespace ApSpec.LoopReplayOnce

set_option linter.unusedSectionVars false

variable {Offer Out : Type} [DecidableEq Offer] [DecidableEq Out]
variable (R : Offer → List Out) (next : List Out → Out → List Offer)

/-- Store and worklist. -/
structure St (Offer Out : Type) where
  store : List Out
  work  : List Offer

/-- Replay one offer: add the outputs that are not stored, and queue the offers of the fresh ones. -/
def replay (s : St Offer Out) (o : Offer) (rest : List Offer) : St Offer Out :=
  let fresh := (R o).filter (fun x => !(s.store.contains x))
  let store' := s.store ++ fresh
  ⟨store', rest ++ fresh.flatMap (next store')⟩

def stepNative (s : St Offer Out) : St Offer Out :=
  match s.work with
  | [] => s
  | o :: rest => replay R next s o rest

/-- P2 state: the native state and the offers already replayed in this run. -/
structure StOnce (Offer Out : Type) where
  st   : St Offer Out
  done : List Offer

def stepOnce (s : StOnce Offer Out) : StOnce Offer Out :=
  match s.st.work with
  | [] => s
  | o :: rest =>
    if s.done.contains o then ⟨⟨s.st.store, rest⟩, s.done⟩
    else ⟨replay R next s.st o rest, o :: s.done⟩

def runNative : Nat → St Offer Out → St Offer Out
  | 0, s => s
  | n + 1, s => runNative n (stepNative R next s)

def runOnce : Nat → StOnce Offer Out → StOnce Offer Out
  | 0, s => s
  | n + 1, s => runOnce n (stepOnce R next s)

/-- Every output of a replayed offer is stored. -/
def Inv (s : StOnce Offer Out) : Prop := ∀ d ∈ s.done, ∀ x ∈ R d, x ∈ s.st.store

theorem filter_nil_of {α : Type} (p : α → Bool) :
    ∀ (l : List α), (∀ x ∈ l, p x = false) → l.filter p = []
  | [], _ => rfl
  | x :: xs, h => by
    have hx : p x = false := h x (List.mem_cons_self ..)
    have ih := filter_nil_of p xs (fun y hy => h y (List.mem_cons_of_mem _ hy))
    rw [List.filter_cons, hx]
    exact ih

/-- A replay whose outputs are all stored changes nothing but the worklist head. -/
theorem replay_stored (s : St Offer Out) (o : Offer) (rest : List Offer)
    (h : ∀ x ∈ R o, x ∈ s.store) : replay R next s o rest = ⟨s.store, rest⟩ := by
  unfold replay
  have hf : (R o).filter (fun x => !(s.store.contains x)) = [] := by
    apply filter_nil_of
    intro x hx
    have hc : s.store.contains x = true := List.elem_eq_true_of_mem (h x hx)
    rw [hc]
    rfl
  rw [hf]
  show (⟨s.store ++ [], rest ++ ([] : List Out).flatMap (next (s.store ++ []))⟩ : St Offer Out) = ⟨s.store, rest⟩
  rw [List.append_nil, List.flatMap_nil, List.append_nil]

theorem replay_store_mono (s : St Offer Out) (o : Offer) (rest : List Offer) :
    ∀ x ∈ s.store, x ∈ (replay R next s o rest).store := by
  intro x hx
  unfold replay
  simp only
  exact List.mem_append_left _ hx

theorem replay_covers (s : St Offer Out) (o : Offer) (rest : List Offer) :
    ∀ x ∈ R o, x ∈ (replay R next s o rest).store := by
  intro x hx
  unfold replay
  simp only
  by_cases hs : x ∈ s.store
  · exact List.mem_append_left _ hs
  · apply List.mem_append_right
    rw [List.mem_filter]
    exact ⟨hx, by simp [hs]⟩

/-- One P2 step is the native step on the native part, and keeps the invariant. -/
theorem stepOnce_sim (s : StOnce Offer Out) (h : Inv R s) :
    (stepOnce R next s).st = stepNative R next s.st ∧ Inv R (stepOnce R next s) := by
  unfold stepOnce stepNative
  cases hw : s.st.work with
  | nil => exact ⟨rfl, h⟩
  | cons o rest =>
    simp only
    by_cases hd : s.done.contains o = true
    · simp only [hd, if_true]
      have hmem : o ∈ s.done := by simpa [List.contains_iff_mem] using hd
      refine ⟨(replay_stored R next s.st o rest (h o hmem)).symm, ?_⟩
      intro d hdm x hx
      exact h d hdm x hx
    · rw [if_neg hd]
      refine ⟨rfl, ?_⟩
      intro d hdm x hx
      simp only [List.mem_cons] at hdm
      rcases hdm with rfl | hdm
      · exact replay_covers R next s.st d rest x hx
      · exact replay_store_mono R next s.st o rest x (h d hdm x hx)

/-- P2 is exact: after any number of steps the store and the worklist are the native ones. -/
theorem runOnce_eq (n : Nat) (s : StOnce Offer Out) (h : Inv R s) :
    (runOnce R next n s).st = runNative R next n s.st := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [runOnce, runNative]
    obtain ⟨hst, hinv⟩ := stepOnce_sim R next s h
    rw [← hst]
    exact ih _ hinv

/-- The run starts with no replayed offer. -/
theorem runOnce_eq_start (n : Nat) (s : St Offer Out) :
    (runOnce R next n ⟨s, []⟩).st = runNative R next n s :=
  runOnce_eq R next n ⟨s, []⟩ (by intro d hd; cases hd)

end ApSpec.LoopReplayOnce

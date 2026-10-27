import Std

/- Source-only finite authorization model. Lists denote finite sets through
   membership. `admit` returns a duplicate-free fresh set. No AP geometry,
   sources, records, scheduling, aliases or whole-engine result is assumed. -/
namespace QueryReplay

variable {α : Type} [DecidableEq α]

def subset (p q : List α) : Prop := ∀ x, x ∈ p → x ∈ q

def permits (q p : List α) : Bool := p.all (fun x => q.contains x)

theorem permits_iff (q p : List α) : permits q p = true ↔ subset p q := by
  simp [permits, List.all_eq_true, subset]

def unique : List α → List α
  | [] => []
  | x :: xs => x :: (unique xs).filter (fun y => decide (y ≠ x))

theorem unique_mem (xs : List α) (x : α) : x ∈ unique xs ↔ x ∈ xs := by
  induction xs with
  | nil => simp [unique]
  | cons y ys ih =>
      by_cases h : x = y
      · simp [unique, h]
      · simp [unique, h, ih]

theorem unique_nodup (xs : List α) : (unique xs).Nodup := by
  induction xs with
  | nil => simp [unique]
  | cons x xs ih =>
      apply List.nodup_cons.mpr
      exact ⟨by simp [List.mem_filter], ih.filter _⟩

def admit (q offered : List α) : List α :=
  unique (offered.filter (fun x => !q.contains x))

theorem mem_admit (q offered : List α) (x : α) :
    x ∈ admit q offered ↔ x ∈ offered ∧ x ∉ q := by
  simp [admit, unique_mem]

theorem admit_disjoint (q offered : List α) (x : α)
    (h : x ∈ admit q offered) : x ∉ q :=
  ((mem_admit q offered x).mp h).2

theorem admit_nodup (q offered : List α) : (admit q offered).Nodup := by
  exact unique_nodup _

def disjoint (q f : List α) : Prop := ∀ x, x ∈ f → x ∉ q

theorem admitted_batch_disjoint (q offered : List α) :
    disjoint q (admit q offered) := admit_disjoint q offered

def transition (q f p : List α) : Prop :=
  permits q p = false ∧ permits (q ++ f) p = true

def findMissing (p q : List α) : Option α :=
  match p with
  | [] => none
  | x :: xs => if x ∈ q then findMissing xs q else some x

theorem findMissing_none (p q : List α) :
    findMissing p q = none ↔ subset p q := by
  induction p with
  | nil => simp [findMissing, subset]
  | cons x xs ih =>
      by_cases h : x ∈ q
      · simp [findMissing, h, ih, subset] at *
      · simp [findMissing, h, subset]

theorem findMissing_sound (p q : List α) (x : α)
    (h : findMissing p q = some x) : x ∈ p ∧ x ∉ q := by
  induction p with
  | nil => simp [findMissing] at h
  | cons y ys ih =>
      by_cases hy : y ∈ q
      · have hx := ih (by simpa [findMissing, hy] using h)
        exact ⟨by simp [hx.1], hx.2⟩
      · have eq : y = x := by simpa [findMissing, hy] using h
        subst y
        exact ⟨by simp, hy⟩

/- Executable choice: no finite-set choice or Classical witness extraction. -/
theorem transition_fresh_witness (q f p : List α) (h : transition q f p) :
    ∃ x, findMissing p q = some x ∧ x ∈ p ∧ x ∈ f := by
  cases missing : findMissing p q with
  | none =>
      have old : permits q p = true := (permits_iff q p).mpr ((findMissing_none p q).mp missing)
      simp [transition, old] at h
  | some x =>
      have hx := findMissing_sound p q x missing
      have member := (permits_iff (q ++ f) p).mp h.2 x hx.1
      have hf : x ∈ f := by
        rcases List.mem_append.mp member with old | fresh
        · exact False.elim (hx.2 old)
        · exact fresh
      exact ⟨x, rfl, hx.1, hf⟩

theorem newly_authorized_iff (q f p : List α) (fresh : disjoint q f) :
    transition q f p ↔ (∃ x, x ∈ p ∧ x ∈ f) ∧ subset p (q ++ f) := by
  constructor
  · intro h
    obtain ⟨x, _, hp, hf⟩ := transition_fresh_witness q f p h
    exact ⟨⟨x, hp, hf⟩, (permits_iff _ _).mp h.2⟩
  · rintro ⟨⟨x, hp, hf⟩, all⟩
    have oldFalse : permits q p = false := by
      cases h : permits q p with
      | false => rfl
      | true => exact False.elim (fresh x hf ((permits_iff _ _).mp h x hp))
    exact ⟨oldFalse, (permits_iff _ _).mpr all⟩

theorem unary_exact_borrow (q f : List α) (x : α) (fresh : disjoint q f) :
    transition q f [x] ↔ x ∈ f := by
  rw [newly_authorized_iff q f [x] fresh]
  constructor
  · rintro ⟨⟨y, hy, hf⟩, _⟩
    have eq : y = x := by simpa using hy
    simpa [eq] using hf
  · intro hf
    exact ⟨⟨x, by simp, hf⟩, fun y hy => by
      have eq : y = x := by simpa using hy
      subst y
      exact List.mem_append_right _ hf⟩

/- `keys` enumerates the current store tuples, and `members k` is one
   complete tuple premise. Harvesting per fresh member may visit k twice;
   unique makes one authorization candidate for that tuple. -/
def candidates (keys : List Nat) (members : Nat → List α) (f : List α) : List Nat :=
  unique (f.flatMap fun x => keys.filter (fun k => (members k).contains x))

theorem candidate_membership (keys : List Nat) (members : Nat → List α)
    (f : List α) (k : Nat) :
    k ∈ candidates keys members f ↔
      k ∈ keys ∧ ∃ x, x ∈ members k ∧ x ∈ f := by
  simp only [candidates, unique_mem, List.mem_flatMap, List.mem_filter,
    List.contains_iff_mem]
  constructor
  · rintro ⟨x, hf, hk, hp⟩
    exact ⟨hk, x, hp, hf⟩
  · rintro ⟨hk, x, hp, hf⟩
    exact ⟨x, hf, hk, hp⟩

theorem candidate_once (keys : List Nat) (members : Nat → List α) (f : List α) :
    (candidates keys members f).Nodup := unique_nodup _

def replay (keys : List Nat) (members : Nat → List α) (q f : List α) : List Nat :=
  (candidates keys members f).filter (fun k => permits (q ++ f) (members k))

theorem replay_exact (keys : List Nat) (members : Nat → List α)
    (q f : List α) (fresh : disjoint q f) (k : Nat) :
    k ∈ replay keys members q f ↔ k ∈ keys ∧ transition q f (members k) := by
  rw [replay, List.mem_filter, candidate_membership]
  rw [newly_authorized_iff q f (members k) fresh]
  simp only [permits_iff]
  exact and_assoc

theorem replay_once (keys : List Nat) (members : Nat → List α) (q f : List α) :
    (replay keys members q f).Nodup :=
  (candidate_once keys members f).filter _

theorem complete_nd_required (q f p : List α) (x : α)
    (member : x ∈ p) (missing : x ∉ q ++ f) : ¬ transition q f p := by
  intro h
  exact missing ((permits_iff _ _).mp h.2 x member)

theorem unrelated_query_no_backfill (q f p : List α)
    (fresh : disjoint q f) (unrelated : ∀ x, x ∈ f → x ∉ p) :
    ¬ transition q f p := by
  intro h
  obtain ⟨⟨x, hp, hf⟩, _⟩ := (newly_authorized_iff q f p fresh).mp h
  exact unrelated x hf hp

theorem already_permitted_no_backfill (q f p : List α)
    (old : permits q p = true) : ¬ transition q f p := by
  simp [transition, old]

inductive Direction | forward | backward deriving DecidableEq, Repr

/- ZERO is a special premise, not the empty conjunction. Backward publication
   already permits ZERO independently of query admission. Forward ZERO uses
   StrongQueries' nonempty-admitted-set rule. -/
def zeroPublished (direction : Direction) (q : List α) : Bool :=
  direction == .backward || !q.isEmpty

def zeroTransition (direction : Direction) (q f : List α) : Prop :=
  zeroPublished direction q = false ∧ zeroPublished direction (q ++ f) = true

omit [DecidableEq α] in
theorem backward_zero_no_backfill (q f : List α) :
    ¬ zeroTransition .backward q f := by
  simp [zeroTransition, zeroPublished]

omit [DecidableEq α] in
theorem forward_zero_first_nonempty (q f : List α) :
    zeroTransition .forward q f ↔ q = [] ∧ f ≠ [] := by
  cases q <;> cases f <;> simp [zeroTransition, zeroPublished]

structure Value where
  ordinary : Bool
  annotation : Bool
  deriving DecidableEq, Repr

def regularRawDelta (old offered : Value) : Bool :=
  (offered.ordinary && !old.ordinary) || (offered.annotation && !old.annotation)

theorem late_annotation_regular_path :
    regularRawDelta ⟨true,false⟩ ⟨true,true⟩ = true := rfl

theorem annotation_not_authorization (q p : List α) (old : permits q p = true) :
    ¬ transition q [] p ∧ regularRawDelta ⟨true,false⟩ ⟨true,true⟩ = true :=
  ⟨already_permitted_no_backfill q [] p old, rfl⟩

/- Optional cumulative observation law. The premise `currentOldVisible`
   requires delivery of regular raw deltas, including late annotations, for
   every already-authorized current tuple. This is NOT an engine theorem. -/
theorem cumulative_replay_equivalent (q f p : List α) (seen : Prop)
    (currentOldVisible : permits q p = true → seen) :
    (seen ∨ transition q f p) ↔ (seen ∨ permits (q ++ f) p = true) := by
  constructor
  · rintro (old | new)
    · exact Or.inl old
    · exact Or.inr new.2
  · rintro (old | now)
    · exact Or.inl old
    · cases h : permits q p with
      | false => exact Or.inr ⟨h, now⟩
      | true => exact Or.inl (currentOldVisible h)

def controls : List (String × Bool) := [
  ("admit removes old and duplicate offered initials", admit (α := Nat) [1] [1,2,2,3] == [2,3]),
  ("partial ND is not authorized", !(permits (α := Nat) ([1] ++ [2]) [1,2,3])),
  ("complete ND becomes authorized", permits (α := Nat) ([1] ++ [2]) [1,2]),
  ("two fresh members harvest one tuple", candidates (α := Nat) [7] (fun _ => [1,2]) [1,2] == [7]),
  ("two fresh members replay one complete tuple", replay (α := Nat) [7] (fun _ => [1,2]) [] [1,2] == [7]),
  ("partial ND candidate does not replay", replay (α := Nat) [7] (fun _ => [1,2]) [] [1] == []),
  ("unrelated fresh member produces no candidate", replay (α := Nat) [7] (fun _ => [1]) [] [2] == []),
  ("already permitted tuple gets no backfill", replay (α := Nat) [7] (fun _ => [1]) [1] [2] == []),
  ("fresh-member witness is executable", findMissing (α := Nat) [1,2,3] [1] == some 2),
  ("unary exact borrow", replay (α := Nat) [1,2,3] (fun k => [k]) [1] [2] == [2]),
  ("backward ZERO already published", zeroPublished .backward ([] : List Nat)),
  ("forward ZERO old empty was not published", !(zeroPublished .forward ([] : List Nat))),
  ("forward ZERO first fresh batch publishes", zeroPublished .forward ([1] : List Nat)),
  ("late flag remains regular raw delta", regularRawDelta ⟨true,false⟩ ⟨true,true⟩),
  ("repeated protected raw offer has no delta", !(regularRawDelta ⟨true,true⟩ ⟨true,true⟩))
]

def checkControls : IO Unit := do
  for entry in controls do
    if !entry.2 then throw (IO.userError s!"Control failed: {entry.1}")
  IO.println s!"Query replay controls: {controls.length} passed"

#eval checkControls

end QueryReplay

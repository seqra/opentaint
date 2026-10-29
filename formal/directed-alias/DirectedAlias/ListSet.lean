/-!
# Lists as finite sets, and function update

The model uses `List` as a finite set with decidable membership.
Order and duplicates have no meaning. Only membership has meaning.
-/

namespace DirectedAlias

/-- Union of two lists. The result keeps `m` and adds each element of `l` that is not in `m`. -/
def uni {α : Type} [DecidableEq α] (l m : List α) : List α :=
  l.foldr List.insert m

/-- Union of a list of lists. -/
def uniAll {α : Type} [DecidableEq α] (ls : List (List α)) : List α :=
  ls.foldr uni []

/-- Union of `f a` over all `a` in `l`. -/
def uniMap {α β : Type} [DecidableEq β] (f : α → List β) (l : List α) : List β :=
  l.foldr (fun a acc => uni (f a) acc) []

/-- Boolean subset test: each element of `l` is in `m`. -/
def subB {α : Type} [DecidableEq α] (l m : List α) : Bool :=
  l.all (fun a => decide (a ∈ m))

/-- Boolean intersection test: some element of `l` is in `m`. -/
def meetB {α : Type} [DecidableEq α] (l m : List α) : Bool :=
  l.any (fun a => decide (a ∈ m))

/-- If all elements of `l` are one value `o`, and `l` is not empty, give `o`. -/
def single? {α : Type} [DecidableEq α] : List α → Option α
  | [] => none
  | o :: rest => if rest.all (fun a => decide (a = o)) then some o else none

/-- Update of a function at one point. -/
def fupd {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun a' => if a' = a then b else f a'

/-- Update of a two-argument function at one point. -/
def fupd2 {α β γ : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β → γ) (a : α) (b : β) (c : γ) : α → β → γ :=
  fun a' b' => if a' = a ∧ b' = b then c else f a' b'

section lemmas
variable {α β γ : Type} [DecidableEq α] [DecidableEq β]

/-- An element is in the union if and only if it is in one of the two lists. -/
theorem mem_uni {a : α} {l m : List α} : a ∈ uni l m ↔ a ∈ l ∨ a ∈ m := by
  induction l with
  | nil => simp [uni]
  | cons x xs ih =>
    simp only [uni, List.foldr_cons] at ih ⊢
    rw [List.mem_insert_iff, ih]
    simp [or_assoc]

/-- An element is in `uniAll ls` if and only if it is in some list of `ls`. -/
theorem mem_uniAll {a : α} {ls : List (List α)} : a ∈ uniAll ls ↔ ∃ l ∈ ls, a ∈ l := by
  induction ls with
  | nil => simp [uniAll]
  | cons l ls ih =>
    simp only [uniAll, List.foldr_cons] at ih ⊢
    rw [mem_uni, ih]
    simp

/-- An element is in `uniMap f l` if and only if it is in `f x` for some `x` in `l`. -/
theorem mem_uniMap {γ : Type} {f : γ → List α} {a : α} {l : List γ} :
    a ∈ uniMap f l ↔ ∃ x ∈ l, a ∈ f x := by
  induction l with
  | nil => simp [uniMap]
  | cons x xs ih =>
    simp only [uniMap, List.foldr_cons] at ih ⊢
    rw [mem_uni, ih]
    simp

/-- `subB` is true if and only if the first list is a subset of the second. -/
theorem subB_iff {l m : List α} : subB l m = true ↔ ∀ a ∈ l, a ∈ m := by
  simp [subB, List.all_eq_true]

/-- `meetB` is true if and only if the two lists have a common element. -/
theorem meetB_iff {l m : List α} : meetB l m = true ↔ ∃ a, a ∈ l ∧ a ∈ m := by
  simp [meetB, List.any_eq_true]

/-- `meetB` is symmetric. -/
theorem meetB_comm (l m : List α) : meetB l m = meetB m l := by
  cases h : meetB m l
  · cases h' : meetB l m
    · rfl
    · obtain ⟨a, h1, h2⟩ := meetB_iff.mp h'
      have : meetB m l = true := meetB_iff.mpr ⟨a, h2, h1⟩
      rw [h] at this; exact this.symm
  · obtain ⟨a, h1, h2⟩ := meetB_iff.mp h
    exact meetB_iff.mpr ⟨a, h2, h1⟩

/-- If `single? l = some o`, then `l` is not empty and each element of `l` is `o`. -/
theorem single?_spec {l : List α} {o : α} (h : single? l = some o) :
    o ∈ l ∧ ∀ a ∈ l, a = o := by
  cases l with
  | nil => simp [single?] at h
  | cons x rest =>
    simp only [single?] at h
    split at h
    · rename_i hall
      cases h
      refine ⟨List.mem_cons_self, ?_⟩
      intro a ha
      cases List.mem_cons.mp ha with
      | inl h1 => exact h1
      | inr h1 => exact of_decide_eq_true (List.all_eq_true.mp hall a h1)
    · cases h

/-- `fupd` gives the new value at the updated point. -/
@[simp] theorem fupd_same (f : α → γ) (a : α) (c : γ) : fupd f a c a = c := by
  simp [fupd]

/-- `fupd` keeps the old value at other points. -/
theorem fupd_ne (f : α → γ) {a a' : α} (c : γ) (h : a' ≠ a) : fupd f a c a' = f a' := by
  simp [fupd, h]

/-- `fupd2` gives the new value at the updated point. -/
@[simp] theorem fupd2_same (f : α → β → γ) (a : α) (b : β) (c : γ) : fupd2 f a b c a b = c := by
  simp [fupd2]

/-- `fupd2` keeps the old value at other points. -/
theorem fupd2_ne (f : α → β → γ) {a a' : α} {b b' : β} (c : γ) (h : ¬ (a' = a ∧ b' = b)) :
    fupd2 f a b c a' b' = f a' b' := by
  unfold fupd2
  split
  · contradiction
  · rfl

end lemmas

end DirectedAlias

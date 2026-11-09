/-
# The caller-side subscription storage: exact keying, and why it has to be exact

This models `MethodTreeAccessPathSubscription.add` on `saloed/conductor-minimal`.

## What went wrong first

The shipped compression keyed rows by `(base, access)` and DROPPED `exclusions` from the key, so one
bucket held several rows and `add` scanned it. Measured on CI (CLAIMS Claim 144) that costs 8.1x the
access facts and OOMs, and neither way of resolving the scan is exact:

* merging a row whose FINAL matches widens that row's exclusions toward `Empty` via `intersect`, so
  the row begins matching callers it should not -- rows drift to maximally permissive;
* not merging gives every exclusion set its own row emitting a FULL subscription instead of a delta.

Both are sound -- neither can drop a subscription -- and both multiply facts. The defect is upstream
of the choice: **the exclusions belong in the key**.

## What is modelled here

The repaired algorithm: exactly one row per distinct `AccessPath`, that is per
`(base, access, exclusions)`, always merged. That is what `saloed/5-default-get` did with an
`object2IntMap<AccessPath>`.

Because the exclusions are part of the key, no order on exclusion sets appears anywhere below --
equality suffices. The `subA`/`interA` machinery the previous version of this file needed, to say
that `intersect` only widens a row, is GONE, because the widening is gone.

The theorem that separates the repaired algorithm from the broken one is
`add_preserves_other_keys`: an add at one key leaves every other key untouched. The scan violated
exactly that -- its first branch could fire on a row with DIFFERENT exclusions and mutate it.
-/

namespace FactExplosion.SubscriptionRows

abbrev Acc := Nat
abbrev Path := List Acc
abbrev Excl := List Acc
abbrev Tree := List Path

def memP (p : Path) : Tree → Bool
  | [] => false
  | q :: qs => decide (p = q) || memP p qs

/-- `subT a b`: every path of `a` is already in `b`, so adding `a` to `b` contributes nothing. -/
def subT : Tree → Tree → Bool
  | [], _ => true
  | p :: ps, b => memP p b && subT ps b

/-! ## Tree containment -/

theorem memP_cons {p q : Path} {b : Tree} (h : memP p b = true) : memP p (q :: b) = true := by
  simp [memP, h]

theorem subT_weaken : ∀ (a b : Tree) (q : Path), subT a b = true → subT a (q :: b) = true
  | [], _, _, _ => rfl
  | p :: ps, b, q, h => by
      rw [subT, Bool.and_eq_true] at h
      rw [subT, Bool.and_eq_true]
      exact ⟨memP_cons h.1, subT_weaken ps b q h.2⟩

theorem subT_refl : ∀ a : Tree, subT a a = true
  | [] => rfl
  | p :: ps => by
      rw [subT, Bool.and_eq_true]
      exact ⟨by simp [memP], subT_weaken ps ps p (subT_refl ps)⟩

theorem memP_append_left : ∀ (a g : Tree) (p : Path), memP p a = true → memP p (a ++ g) = true
  | [], _, _, h => by simp [memP] at h
  | q :: qs, g, p, h => by
      rw [memP, Bool.or_eq_true] at h
      rw [List.cons_append, memP, Bool.or_eq_true]
      cases h with
      | inl he => exact Or.inl he
      | inr ht => exact Or.inr (memP_append_left qs g p ht)

theorem subT_append_left : ∀ (x a g : Tree), subT x a = true → subT x (a ++ g) = true
  | [], _, _, _ => rfl
  | p :: ps, a, g, h => by
      rw [subT, Bool.and_eq_true] at h
      rw [subT, Bool.and_eq_true]
      exact ⟨memP_append_left a g p h.1, subT_append_left ps a g h.2⟩

theorem memP_append_right : ∀ (a g : Tree) (p : Path), memP p g = true → memP p (a ++ g) = true
  | [], _, _, h => h
  | q :: qs, g, p, h => by
      rw [List.cons_append, memP, Bool.or_eq_true]
      exact Or.inr (memP_append_right qs g p h)

theorem subT_weaken_append : ∀ (y x a : Tree), subT y x = true → subT y (a ++ x) = true
  | [], _, _, _ => rfl
  | p :: ps, x, a, h => by
      rw [subT, Bool.and_eq_true] at h
      rw [subT, Bool.and_eq_true]
      exact ⟨memP_append_right a x p h.1, subT_weaken_append ps x a h.2⟩

theorem subT_append_right (x a : Tree) : subT x (a ++ x) = true :=
  subT_weaken_append x x a (subT_refl x)

/-! ## The storage -/

/-- The whole `AccessPath`. `exclusions` is part of the KEY -- that is the repair. -/
structure Key where
  base : Nat
  access : Path
  excl : Excl
deriving DecidableEq

/-- One final tree per key, exactly as `object2IntMap<AccessPath>` gave. -/
abbrev Store := List (Key × Tree)

def find (k : Key) : Store → Option Tree
  | [] => none
  | (k', t) :: rest => if k' = k then some t else find k rest

def upd (k : Key) (t : Tree) : Store → Store
  | [] => [(k, t)]
  | (k', t') :: rest => if k' = k then (k, t) :: rest else (k', t') :: upd k t rest

/-- `MethodTreeAccessPathSubscription.add`. `none` is the shipped `return null`. -/
def add (k : Key) (f : Tree) (s : Store) : Option Store :=
  match find k s with
  | none => some ((k, f) :: s)
  | some t => if subT f t then none else some (upd k (t ++ f) s)

/-! ## `find` against `upd` -/

theorem find_upd_same : ∀ (s : Store) (k : Key) (t : Tree), find k (upd k t s) = some t := by
  intro s
  induction s with
  | nil => intro k t; simp [upd, find]
  | cons hd tl ih =>
      intro k t
      obtain ⟨a, b⟩ := hd
      by_cases h : a = k
      · subst h; simp [upd, find]
      · rw [upd, if_neg h, find, if_neg h]; exact ih k t

theorem find_upd_other : ∀ (s : Store) (k k' : Key) (t : Tree), k' ≠ k →
    find k' (upd k t s) = find k' s := by
  intro s
  induction s with
  | nil =>
      intro k k' t hne
      have hkk : ¬ (k = k') := fun hh => hne hh.symm
      simp [upd, find, hkk]
  | cons hd tl ih =>
      intro k k' t hne
      obtain ⟨a, b⟩ := hd
      have hkk : ¬ (k = k') := fun hh => hne hh.symm
      by_cases h : a = k
      · subst h
        rw [upd, if_pos rfl]
        simp only [find]
        rw [if_neg hkk, if_neg hkk]
      · rw [upd, if_neg h]
        simp only [find]
        by_cases h2 : a = k'
        · rw [if_pos h2, if_pos h2]
        · rw [if_neg h2, if_neg h2]; exact ih k k' t hne

/-! ## No false negative, and no cross-key interference -/

/-- Every `return null` is justified: the row for this exact key already contains the tree. -/
theorem add_none_is_covered (k : Key) (f : Tree) (s : Store) :
    add k f s = none → ∃ t, find k s = some t ∧ subT f t = true := by
  intro h
  cases hf : find k s with
  | none => simp [add, hf] at h
  | some t =>
      by_cases hle : subT f t = true
      · exact ⟨t, rfl, hle⟩
      · simp [add, hf, hle] at h

/-- When a subscription is emitted, the installed store holds the tree at this key. -/
theorem add_some_is_covered (k : Key) (f : Tree) (s s' : Store) :
    add k f s = some s' → ∃ t, find k s' = some t ∧ subT f t = true := by
  intro h
  cases hf : find k s with
  | none =>
      simp [add, hf] at h
      subst h
      exact ⟨f, by simp [find], subT_refl f⟩
  | some t =>
      by_cases hle : subT f t = true
      · simp [add, hf, hle] at h
      · simp [add, hf, hle] at h
        subst h
        exact ⟨t ++ f, find_upd_same s k (t ++ f), subT_append_right f t⟩

/-- **The property the scan violated.** An add at one key changes no other key. The broken version
keyed on `(base, access)`, and its first branch could fire on a row with DIFFERENT exclusions and
widen it; here the exclusions are in the key, so that cannot happen. -/
theorem add_preserves_other_keys (k : Key) (f : Tree) (s s' : Store) (k' : Key) (hne : k' ≠ k) :
    add k f s = some s' → find k' s' = find k' s := by
  intro h
  have hkk : ¬ (k = k') := fun hh => hne hh.symm
  cases hf : find k s with
  | none =>
      simp [add, hf] at h
      subst h
      simp only [find]
      rw [if_neg hkk]
  | some t =>
      by_cases hle : subT f t = true
      · simp [add, hf, hle] at h
      · simp [add, hf, hle] at h
        subst h
        exact find_upd_other s k k' (t ++ f) hne

/-- A key's tree only ever grows: no row is replaced by a smaller one, and none is widened. -/
theorem add_is_monotone (k : Key) (f : Tree) (s s' : Store) (t : Tree) :
    add k f s = some s' → find k s = some t →
      ∃ t', find k s' = some t' ∧ subT t t' = true := by
  intro h hf
  by_cases hle : subT f t = true
  · simp [add, hf, hle] at h
  · simp [add, hf, hle] at h
    subst h
    exact ⟨t ++ f, find_upd_same s k (t ++ f), subT_append_left t t f (subT_refl t)⟩

/-- The pair is held by the storage whichever branch `add` takes: no false negative. -/
theorem always_covered (k : Key) (f : Tree) (s : Store) :
    (add k f s = none → ∃ t, find k s = some t ∧ subT f t = true) ∧
    (∀ s', add k f s = some s' → ∃ t, find k s' = some t ∧ subT f t = true) :=
  ⟨add_none_is_covered k f s, fun s' h => add_some_is_covered k f s s' h⟩

end FactExplosion.SubscriptionRows

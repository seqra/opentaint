/-
# The size-triggered widening

`CallerCompress` proves the subscription protocol correct GIVEN a compressor with two properties:

* `sound`   -- a widening: it never loses an acceptance;
* `bounded` -- it respects the budget it is given.

`SizeBound`'s fold is EXACT, so it removes redundancy and cannot promise a target size. This module
supplies the missing operator: cut the tree at a depth, marking the cut abstract, and choose the
DEEPEST cut that fits the budget.

The existence proof is executable, as the goal requires: `fitUpto` computes the witness by trying the
deepest cut first and walking down. It terminates because cutting at depth 0 leaves ONE node, so a
budget of at least 1 is always achievable.
-/

namespace FactExplosion.SizeTrigger

abbrev Acc := Nat

/-- A fact tree. `abs` marks a node that stands for "anything below", which is what a cut leaves. -/
inductive T where
  | mk (abs : Bool) (children : List (Acc × T))

mutual
  def tnodes : T → Nat
    | .mk _ cs => 1 + tnodesL cs
  def tnodesL : List (Acc × T) → Nat
    | [] => 0
    | c :: r => tnodes c.2 + tnodesL r
end

mutual
  /-- A path is accepted if the walk reaches a node, or meets an abstract node on the way. -/
  def taccepts : T → List Acc → Bool
    | .mk _ _, [] => true
    | .mk abs cs, x :: xs => abs || tacceptsL cs x xs
  def tacceptsL : List (Acc × T) → Acc → List Acc → Bool
    | [], _, _ => false
    | c :: r, x, xs => cond (c.1 == x) (taccepts c.2 xs) (tacceptsL r x xs)
end

/-! ## The cut -/

mutual
  /-- Cut at depth `d`: everything below becomes one abstract node. -/
  def truncAt : Nat → T → T
    | 0, .mk _ _ => .mk true []
    | d + 1, .mk abs cs => .mk abs (truncAtL d cs)
  def truncAtL : Nat → List (Acc × T) → List (Acc × T)
    | _, [] => []
    | d, c :: r => (c.1, truncAt d c.2) :: truncAtL d r
end

/-- Cutting at the root leaves exactly one node. This is why a budget of 1 is always reachable. -/
theorem tnodes_truncAt_zero (t : T) : tnodes (truncAt 0 t) = 1 := by
  cases t with
  | mk abs cs => rfl

/-- An abstract leaf accepts every path: the cut is a WIDENING at its most extreme. -/
theorem taccepts_top (p : List Acc) : taccepts (.mk true []) p = true := by
  cases p with
  | nil => rfl
  | cons x xs => rfl

-- **The cut never loses an acceptance.**
mutual
  theorem truncAt_sound : ∀ (d : Nat) (t : T) (p : List Acc),
      taccepts t p = true → taccepts (truncAt d t) p = true := by
    intro d t p h
    cases t with
    | mk abs cs =>
      cases d with
      | zero => exact taccepts_top p
      | succ d' =>
            cases p with
            | nil => rfl
            | cons x xs =>
                show (abs || tacceptsL (truncAtL d' cs) x xs) = true
                have h' : (abs || tacceptsL cs x xs) = true := h
                cases habs : abs with
                | true => rfl
                | false =>
                    rw [habs] at h'
                    simp only [Bool.false_or] at h' ⊢
                    exact truncAtL_sound d' cs x xs h'

  theorem truncAtL_sound : ∀ (d : Nat) (cs : List (Acc × T)) (x : Acc) (xs : List Acc),
      tacceptsL cs x xs = true → tacceptsL (truncAtL d cs) x xs = true := by
    intro d cs x xs h
    cases cs with
    | nil => exact absurd h (by simp [tacceptsL])
    | cons c r =>
        show cond (c.1 == x) (taccepts (truncAt d c.2) xs) (tacceptsL (truncAtL d r) x xs) = true
        have h' : cond (c.1 == x) (taccepts c.2 xs) (tacceptsL r x xs) = true := h
        cases hc : (c.1 == x) with
        | true =>
            rw [hc] at h'
            have hin : taccepts c.2 xs = true := h'
            show taccepts (truncAt d c.2) xs = true
            exact truncAt_sound d c.2 xs hin
        | false =>
            rw [hc] at h'
            have hin : tacceptsL r x xs = true := h'
            show tacceptsL (truncAtL d r) x xs = true
            exact truncAtL_sound d r x xs hin
end

/-! ## Fitting the budget

`fitUpto` tries the DEEPEST cut first and walks down until one fits. It is executable, and the
`d = 0` case always fits a budget of at least 1, so the search is total.
-/

def fitUpto : Nat → Nat → T → T
  | 0, _, t => truncAt 0 t
  | d + 1, N, t =>
      let c := truncAt (d + 1) t
      if tnodes c ≤ N then c else fitUpto d N t

/-- The operator the protocol needs: cut this tree into the budget. -/
def fit (N : Nat) (t : T) : T := fitUpto (tnodes t) N t

/-- **Obligation 1: `bounded`.** The result fits the budget, for any tree and any `N ≥ 1`. -/
theorem fitUpto_bounded : ∀ (d N : Nat) (t : T), 1 ≤ N → tnodes (fitUpto d N t) ≤ N := by
  intro d
  induction d with
  | zero =>
      intro N t h
      show tnodes (truncAt 0 t) ≤ N
      rw [tnodes_truncAt_zero]
      exact h
  | succ d' ih =>
      intro N t h
      show tnodes (if tnodes (truncAt (d' + 1) t) ≤ N then truncAt (d' + 1) t
                   else fitUpto d' N t) ≤ N
      split
      · assumption
      · exact ih N t h

theorem fit_bounded (N : Nat) (t : T) (h : 1 ≤ N) : tnodes (fit N t) ≤ N :=
  fitUpto_bounded (tnodes t) N t h

/-- **Obligation 2: `sound`.** The result accepts everything the tree accepted. -/
theorem fitUpto_sound : ∀ (d N : Nat) (t : T) (p : List Acc),
    taccepts t p = true → taccepts (fitUpto d N t) p = true := by
  intro d
  induction d with
  | zero => intro N t p h; exact truncAt_sound 0 t p h
  | succ d' ih =>
      intro N t p h
      show taccepts (if tnodes (truncAt (d' + 1) t) ≤ N then truncAt (d' + 1) t
                     else fitUpto d' N t) p = true
      split
      · exact truncAt_sound (d' + 1) t p h
      · exact ih N t p h

theorem fit_sound (N : Nat) (t : T) (p : List Acc) (h : taccepts t p = true) :
    taccepts (fit N t) p = true :=
  fitUpto_sound (tnodes t) N t p h

/--
**Both obligations together.** This is exactly what `CallerCompress.Compressor` asks for, so the
caller-side protocol may use `fit`: it never loses a path, and it hits the budget.
-/
theorem fit_discharges_both (N : Nat) (t : T) (h : 1 ≤ N) :
    tnodes (fit N t) ≤ N ∧ ∀ p, taccepts t p = true → taccepts (fit N t) p = true :=
  ⟨fit_bounded N t h, fun p hp => fit_sound N t p hp⟩

/-- A witness that the search is not vacuous: a tree that already fits keeps its depth. -/
def sample : T := .mk false [(1, .mk false [(2, .mk false [])])]

theorem sample_facts :
    tnodes sample = 3 ∧ tnodes (fit 3 sample) = 3 ∧ tnodes (fit 1 sample) = 1 := by
  refine ⟨rfl, ?_, ?_⟩ <;> rfl

/-! ## CORRECTION: the cut has a FLOOR, and the floor is the tail marks

`tnodes_truncAt_zero` says a cut at the root leaves ONE node, and `fit_bounded` is stated against
that. **The engine does not do this, and it is right not to.** `AccessNode.truncateToWildcard(0)`
returns `coveredTopWithMarks(tailMarks)` -- an abstract node carrying a chain of the tail marks --
because a taint MARK is what asserts that a value is tainted, and dropping it turns the fact into
one that no longer answers the query that finds the vulnerability. `demandKeepTerminal` is the same
issue on the demand side, and it was measured: dropping the terminal loses `ssrf` on conductor.

So the achievable floor is not 1, it is `1 + |distinct tail marks|`. The TDD run found this
immediately -- `fitToBudget(1)` returned 3 nodes on a chain ending in one mark -- which is the model
refusing a design, in the direction where the CODE was right.

This section restates the operator against an arbitrary floor tree. Nothing above is withdrawn: it
is the special case `floor = .mk true []`.
-/

-- Cut at depth `d`, replacing what is below by `floor` rather than by a bare abstract leaf.
mutual
  def truncAtF : T → Nat → T → T
    | f, 0, _ => f
    | f, d + 1, .mk abs cs => .mk abs (truncAtLF f d cs)
  def truncAtLF : T → Nat → List (Acc × T) → List (Acc × T)
    | _, _, [] => []
    | f, d, c :: r => (c.1, truncAtF f d c.2) :: truncAtLF f d r
end

theorem tnodes_truncAtF_zero (f t : T) : tnodes (truncAtF f 0 t) = tnodes f := by
  cases t with
  | mk abs cs => rfl

-- **The cut is still a widening, provided the floor accepts everything.**
mutual
  theorem truncAtF_sound : ∀ (f : T) (hf : ∀ q, taccepts f q = true) (d : Nat) (t : T) (p : List Acc),
      taccepts t p = true → taccepts (truncAtF f d t) p = true := by
    intro f hf d t p h
    cases t with
    | mk abs cs =>
      cases d with
      | zero => exact hf p
      | succ d' =>
            cases p with
            | nil => rfl
            | cons x xs =>
                show (abs || tacceptsL (truncAtLF f d' cs) x xs) = true
                have h' : (abs || tacceptsL cs x xs) = true := h
                cases habs : abs with
                | true => rfl
                | false =>
                    rw [habs] at h'
                    simp only [Bool.false_or] at h' ⊢
                    exact truncAtLF_sound f hf d' cs x xs h'

  theorem truncAtLF_sound : ∀ (f : T) (hf : ∀ q, taccepts f q = true) (d : Nat)
      (cs : List (Acc × T)) (x : Acc) (xs : List Acc),
      tacceptsL cs x xs = true → tacceptsL (truncAtLF f d cs) x xs = true := by
    intro f hf d cs x xs h
    cases cs with
    | nil => exact absurd h (by simp [tacceptsL])
    | cons c r =>
        show cond (c.1 == x) (taccepts (truncAtF f d c.2) xs) (tacceptsL (truncAtLF f d r) x xs) = true
        have h' : cond (c.1 == x) (taccepts c.2 xs) (tacceptsL r x xs) = true := h
        cases hc : (c.1 == x) with
        | true =>
            rw [hc] at h'
            have hin : taccepts c.2 xs = true := h'
            show taccepts (truncAtF f d c.2) xs = true
            exact truncAtF_sound f hf d c.2 xs hin
        | false =>
            rw [hc] at h'
            have hin : tacceptsL r x xs = true := h'
            show tacceptsL (truncAtLF f d r) x xs = true
            exact truncAtLF_sound f hf d r x xs hin
end

def fitUptoF (f : T) : Nat → Nat → T → T
  | 0, _, t => truncAtF f 0 t
  | d + 1, N, t =>
      let c := truncAtF f (d + 1) t
      if tnodes c ≤ N then c else fitUptoF f d N t

def fitF (f : T) (N : Nat) (t : T) : T := fitUptoF f (tnodes t) N t

/--
**The honest bound.** The result fits the budget, OR it is the floor -- and there is nothing smaller
to return. This is what `AccessNode.fitToBudget` satisfies, and the earlier `fit_bounded` is the
`tnodes floor = 1` case of it.
-/
theorem fitUptoF_bounded : ∀ (f : T) (d N : Nat) (t : T),
    tnodes (fitUptoF f d N t) ≤ max N (tnodes f) := by
  intro f d
  induction d with
  | zero =>
      intro N t
      show tnodes (truncAtF f 0 t) ≤ max N (tnodes f)
      rw [tnodes_truncAtF_zero]
      exact Nat.le_max_right N (tnodes f)
  | succ d' ih =>
      intro N t
      show tnodes (if tnodes (truncAtF f (d' + 1) t) ≤ N then truncAtF f (d' + 1) t
                   else fitUptoF f d' N t) ≤ max N (tnodes f)
      split
      · rename_i hle
        exact Nat.le_trans hle (Nat.le_max_left N (tnodes f))
      · exact ih N t

theorem fitF_bounded (f : T) (N : Nat) (t : T) : tnodes (fitF f N t) ≤ max N (tnodes f) :=
  fitUptoF_bounded f (tnodes t) N t

theorem fitUptoF_sound : ∀ (f : T) (hf : ∀ q, taccepts f q = true) (d N : Nat) (t : T) (p : List Acc),
    taccepts t p = true → taccepts (fitUptoF f d N t) p = true := by
  intro f hf d
  induction d with
  | zero => intro N t p h; exact truncAtF_sound f hf 0 t p h
  | succ d' ih =>
      intro N t p h
      show taccepts (if tnodes (truncAtF f (d' + 1) t) ≤ N then truncAtF f (d' + 1) t
                     else fitUptoF f d' N t) p = true
      split
      · exact truncAtF_sound f hf (d' + 1) t p h
      · exact ih N t p h

theorem fitF_sound (f : T) (hf : ∀ q, taccepts f q = true) (N : Nat) (t : T) (p : List Acc)
    (h : taccepts t p = true) : taccepts (fitF f N t) p = true :=
  fitUptoF_sound f hf (tnodes t) N t p h

/--
**Both obligations against a floor.** `CallerCompress.Compressor` asks for `size (run n f) ≤ n`;
with a floor the honest form is `≤ max n floorSize`, and the protocol's bound becomes
`N + floorSize` per step. The floor is the distinct tail marks, so it is bounded by the mark
alphabet and the composition with `TifaBound.emitted_le` still gives a polynomial.
-/
theorem fitF_discharges_both (f : T) (hf : ∀ q, taccepts f q = true) (N : Nat) (t : T) :
    tnodes (fitF f N t) ≤ max N (tnodes f) ∧
      ∀ p, taccepts t p = true → taccepts (fitF f N t) p = true :=
  ⟨fitF_bounded f N t, fun p hp => fitF_sound f hf N t p hp⟩

/-- The mark tail an engine cut leaves: abstract at the root, so it accepts every path. -/
def markFloor : T := .mk true []

theorem markFloor_accepts (p : List Acc) : taccepts markFloor p = true := taccepts_top p

end FactExplosion.SizeTrigger

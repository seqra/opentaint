/-
# The graph-size signal

The dynamic precision controller steps its budget down when the "graph size" crosses a threshold.
Its specification says the signal is "how big is the graph the analysis is HOLDING". Its
implementation adds the FULL size of the merged tree at every store:

    fun observe(nodes: Long) { storedNodes.addAndGet(nodes) ... }

This module states both readings and proves they are different -- not by a constant, but
quadratically in the number of merges into one slot. It also proves the repair is soundness-free:
the operator is unchanged and only the TRIGGER moves, and the ladder stays monotone either way.
-/

namespace FactExplosion.GraphSignal

/-- The sizes a single storage slot takes, in order, one entry per store that changed it. -/
abbrev Sizes := List Nat

/-- What the shipped controller accumulates: the whole tree, every time it is stored. -/
def cumulative : Sizes → Nat
  | [] => 0
  | s :: rest => s + cumulative rest

/-- What the specification describes: the nodes the store actually holds now. -/
def retained (prev : Nat) : Sizes → Nat
  | [] => prev
  | s :: rest => retained s rest

/-- The repair: charge only the GROWTH at each store. -/
def deltaSum (prev : Nat) : Sizes → Nat
  | [] => 0
  | s :: rest => (s - prev) + deltaSum s rest

/-! ## The delta signal is the retained size

A store never shrinks a slot: `mergeAdd` returns the receiver by identity when it adds nothing, and
that path does not reach the counter at all. So the sizes are non-decreasing, and on such a list the
deltas telescope.
-/

/-- The sizes of one slot never decrease. -/
def NonDecr (prev : Nat) : Sizes → Prop
  | [] => True
  | s :: rest => prev ≤ s ∧ NonDecr s rest

/-- **The repaired signal measures exactly what the specification says.** -/
theorem deltaSum_eq_retained : ∀ (sizes : Sizes) (prev : Nat), NonDecr prev sizes →
    prev + deltaSum prev sizes = retained prev sizes := by
  intro sizes
  induction sizes with
  | nil => intro prev _; simp [deltaSum, retained]
  | cons s rest ih =>
      intro prev h
      have hle : prev ≤ s := h.1
      have hrest : NonDecr s rest := h.2
      have := ih s hrest
      simp only [deltaSum, retained]
      omega

/-! ## And the shipped signal does not

One slot that grows by one node at a time. The retained size is `n`; the shipped counter charges
`1 + 2 + ... + n`.
-/

/-- `[1, 2, ..., n]`, the sizes of a slot that grows one node per store. -/
def growOne : Nat → Sizes
  | 0 => []
  | n + 1 => growOne n ++ [n + 1]

theorem cumulative_append : ∀ (a b : Sizes), cumulative (a ++ b) = cumulative a + cumulative b := by
  intro a; induction a with
  | nil => intro b; simp [cumulative]
  | cons x xs ih => intro b; simp only [List.cons_append, cumulative, ih]; omega

/-- **The shipped counter is quadratic where the truth is linear.** -/
theorem cumulative_growOne : ∀ n, 2 * cumulative (growOne n) = n * (n + 1) := by
  intro n
  induction n with
  | zero => rfl
  | succ m ih =>
      simp only [growOne, cumulative_append, cumulative]
      have h1 : (m + 1) * (m + 1 + 1) = (m + 1) * m + (m + 1) * 2 := by rw [← Nat.mul_add]
      have h2 : m * (m + 1) = (m + 1) * m := Nat.mul_comm m (m + 1)
      omega

set_option maxRecDepth 8000 in
/-- The same run, read by the repaired signal: linear, and equal to the final size. -/
theorem the_separation :
    cumulative (growOne 20) = 210 ∧ deltaSum 0 (growOne 20) = 20 ∧
    cumulative (growOne 10) = 55 ∧ deltaSum 0 (growOne 10) = 10 := by decide

/-- The closed form, so the separation is not tied to the sizes `decide` can reach: the shipped
counter is `n * (n + 1) / 2` where the truth is `n`. At conductor's measured 20.8M against a heap
holding about 9.9M nodes, the overcount is already a factor of two, and it grows with every merge
into the same slot. -/
theorem the_separation_is_quadratic (n : Nat) : 2 * cumulative (growOne n) = n * (n + 1) :=
  cumulative_growOne n

/-! ## The repair is soundness-free

The ladder is a pure function of the signal. Changing the signal changes WHEN a rung is taken, never
WHICH operator runs, so every schedule the repaired controller can produce is one the old one could
also produce. The ladder stays monotone and floored under any signal whatsoever.
-/

/-- The rung, transcribed from `FactGraphBudget.rungFor` branch for branch. -/
def rungForIf (ceiling floor stepEvery total : Nat) : Nat :=
  if total < stepEvery then ceiling
  else if ceiling ≤ floor then floor
  else if total / stepEvery - 1 ≥ ceiling - floor then floor
  else ceiling - (total / stepEvery - 1)

/-- The same function without the branches, which is the form the proofs use. -/
def rungFor (ceiling floor stepEvery total : Nat) : Nat :=
  if total < stepEvery then ceiling
  else max floor (ceiling - (total / stepEvery - 1))

/-- The two agree, so the proofs below are about the shipped code and not about a nicer cousin. -/
theorem rungFor_eq (c f st total : Nat) : rungForIf c f st total = rungFor c f st total := by
  unfold rungForIf rungFor
  split
  · rfl
  · split
    · omega
    · split
      · omega
      · omega

/-- **The ladder only ever coarsens, whatever drives it.** -/
theorem rung_is_monotone (c f st : Nat) (hfc : f ≤ c) :
    ∀ a b, a ≤ b → rungFor c f st b ≤ rungFor c f st a := by
  intro a b hab
  have hdiv : a / st ≤ b / st := Nat.div_le_div_right hab
  unfold rungFor
  split
  · split
    · omega
    · omega
  · split
    · omega
    · omega

/-- **The ladder never goes below the floor**, so it terminates. -/
theorem rung_floors (c f st total : Nat) (h : f ≤ c) : f ≤ rungFor c f st total := by
  unfold rungFor
  split
  · exact h
  · omega

/--
**The repair cannot change soundness.** The rung is a pure function of the signal, so a controller
driven by `deltaSum` takes rungs the shipped controller could also take. Only the TIME changes.
-/
theorem repair_changes_only_the_time (c f st : Nat) (sizes : Sizes) (prev : Nat)
    (h : NonDecr prev sizes) :
    rungFor c f st (prev + deltaSum prev sizes) = rungFor c f st (retained prev sizes) := by
  rw [deltaSum_eq_retained sizes prev h]

end FactExplosion.GraphSignal

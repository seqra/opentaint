/-
# Compress on the CALLER side, before subscribing

The pipeline is `subscribeOnMethodSummary` -> `methodSubscriptions.addFactToFact` -> the callee's
TIFA sees `callerPathEdge.factAp.rebase(calleeInitialFactBase)`. So the caller holds the fact before
the callee ever sees it, and it can read the callee's current state (a concurrent READ is safe) and
shrink its own fact first.

Why this placement and not a budget inside the callee: MEASURED, a budget applied where a fact is
BUILT governs what is built, never what is HELD -- a live budget reaching depth 2 got 764,443 events
where a CONSTANT depth 1 got 4,676,422. Compressing before the insert governs what is held.

This module proves the protocol correct GIVEN a compressor with two properties, which is the right
level: the operator itself is supplied elsewhere (`SizeBound`, `Absorption`), and the protocol must
not care which one.

The result that matters for the design: the bound is HARD only if read-compress-insert is atomic.
With `k` callers reading the same state concurrently it degrades to `k * N`, and
`concurrent_can_exceed` is an executable witness of that.
-/

namespace FactExplosion.CallerCompress

abbrev Path := List Nat

/-- A fact, as the finite set of paths it answers. `size` stands for the node count. -/
abbrev Fact := List Path

def accepts (f : Fact) (p : Path) : Bool := f.any (fun q => q == p)

def merge (a b : Fact) : Fact := a ++ b

def size (f : Fact) : Nat := f.length

theorem merge_accepts (a b : Fact) (p : Path) :
    accepts (merge a b) p = (accepts a p || accepts b p) := by
  unfold accepts merge
  rw [List.any_append]

theorem merge_size (a b : Fact) : size (merge a b) = size a + size b := by
  unfold size merge
  rw [List.length_append]

/--
Any compressor the caller may use. It must ADD acceptances (never lose one) and it must respect the
budget it is given. `SizeBound.absorbNode'_sound` is the shape of the first obligation.
-/
structure Compressor where
  run : Nat → Fact → Fact
  /-- A widening: nothing the fact answered becomes unanswerable. -/
  sound : ∀ (n : Nat) (f : Fact) (p : Path), accepts f p = true → accepts (run n f) p = true
  /-- It fits the budget. -/
  bounded : ∀ (n : Nat) (f : Fact), size (run n f) ≤ n

/-! ## One caller, reading the current state -/

/-- Read the callee's state, compress into the room that is left, then subscribe. -/
def stepSeq (C : Compressor) (N : Nat) (s f : Fact) : Fact :=
  merge s (C.run (N - size s) f)

/-- **No false negative.** Everything the callee's state answered, it still answers. -/
theorem step_keeps_state (C : Compressor) (N : Nat) (s f : Fact) (p : Path)
    (h : accepts s p = true) : accepts (stepSeq C N s f) p = true := by
  unfold stepSeq
  rw [merge_accepts, h]
  rfl

/-- **No false negative.** Everything the SUBSCRIBED fact answered, the callee answers. -/
theorem step_keeps_subscribed (C : Compressor) (N : Nat) (s f : Fact) (p : Path)
    (h : accepts f p = true) : accepts (stepSeq C N s f) p = true := by
  unfold stepSeq
  rw [merge_accepts, C.sound (N - size s) f p h]
  exact Bool.or_true _

/-- **The bound is preserved.** A state within `N` stays within `N`. -/
theorem step_bound (C : Compressor) (N : Nat) (s f : Fact) (h : size s ≤ N) :
    size (stepSeq C N s f) ≤ N := by
  unfold stepSeq
  rw [merge_size]
  have := C.bounded (N - size s) f
  omega

/-- Every caller in turn, each reading the state the previous one left. -/
def runSeq (C : Compressor) (N : Nat) (s : Fact) : List Fact → Fact
  | [] => s
  | f :: rest => runSeq C N (stepSeq C N s f) rest

/-- **The invariant holds for any number of callers, in any order.** -/
theorem runSeq_bound (C : Compressor) (N : Nat) :
    ∀ (fs : List Fact) (s : Fact), size s ≤ N → size (runSeq C N s fs) ≤ N := by
  intro fs
  induction fs with
  | nil => intro s h; exact h
  | cons f rest ih =>
      intro s h
      exact ih (stepSeq C N s f) (step_bound C N s f h)

/-- **And nothing is lost along the way.** -/
theorem runSeq_keeps_state (C : Compressor) (N : Nat) :
    ∀ (fs : List Fact) (s : Fact) (p : Path), accepts s p = true →
      accepts (runSeq C N s fs) p = true := by
  intro fs
  induction fs with
  | nil => intro s p h; exact h
  | cons f rest ih =>
      intro s p h
      exact ih (stepSeq C N s f) p (step_keeps_state C N s f p h)

/-! ## Concurrency: the read is stale, and the bound is not hard

`k` callers read the SAME state `s0` -- which is what a lock-free concurrent read gives -- and each
computes its budget from it. Each result fits, and together they need not.
-/

def runConc (C : Compressor) (N : Nat) (s0 : Fact) : List Fact → Fact
  | [] => s0
  | f :: rest => merge (C.run (N - size s0) f) (runConc C N s0 rest)

/-- **The degraded bound: `N` plus one budget per concurrent caller.** -/
theorem runConc_bound (C : Compressor) (N : Nat) (s0 : Fact) :
    ∀ fs : List Fact, size (runConc C N s0 fs) ≤ size s0 + fs.length * (N - size s0) := by
  intro fs
  induction fs with
  | nil => simp [runConc, size]
  | cons f rest ih =>
      have hb := C.bounded (N - size s0) f
      have hmul : (rest.length + 1) * (N - size s0)
          = rest.length * (N - size s0) + (N - size s0) := by
        rw [Nat.add_mul, Nat.one_mul]
      simp only [runConc, merge_size, List.length_cons]
      omega

/-- A compressor that only truncates. It satisfies `bounded`, which is all the size argument uses. -/
def truncate : Nat → Fact → Fact := fun n f => f.take n

theorem truncate_bounded (n : Nat) (f : Fact) : size (truncate n f) ≤ n := by
  unfold truncate size
  simp only [List.length_take]
  omega

/--
**THE DESIGN BUG, exhibited.** Two callers read the same empty state, each is given the whole budget
`N = 2`, each fits it, and the merged state is `4`. So the caller-side protocol gives a HARD bound
only when read-compress-insert is atomic per callee; with a plain concurrent read the guarantee is
`k * N`, not `N`.
-/
theorem concurrent_can_exceed :
    (merge (truncate 2 [[1], [2]]) (merge (truncate 2 [[3], [4]]) [])).length = 4 := by decide

/-- The same statement as the bound that DOES hold: `k` callers, `k * N`. -/
theorem concurrent_bound_is_k_times_N (C : Compressor) (N : Nat) (fs : List Fact) :
    size (runConc C N [] fs) ≤ fs.length * N := by
  have := runConc_bound C N [] fs
  simpa [size] using this

end FactExplosion.CallerCompress

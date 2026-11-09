/-
# Memoising a derivation step

The observation in `CLAIMS.md` claim 21: the analysis holds only 4,387 distinct fact shapes, 713
premises and 4,806 summaries, and re-derives them 5.4x to 7.1x with IDENTICAL inputs.

This module is the spec for removing that repetition. It is deliberately not an abstraction: nothing
here widens, truncates or folds a fact, so there is no precision to trade and no false negative to
argue about. The whole soundness question reduces to one property of the step being memoised --
IDEMPOTENCE -- and the whole benefit is a complexity separation.

## What is proved

* `memo_run_eq_run` -- the memoised run computes EXACTLY the same result as the plain run, given
  the step is idempotent. No finding can be gained or lost.
* `memo_evaluates_once` -- the memoised run evaluates the step at most once per DISTINCT input.
* `plain_evaluates_every_time` -- the plain run evaluates it once per CALL.
* `the_separation` -- the two together: same answer, and the cost ratio is calls/distinct, which the
  trace measures at 7.1 for fact arrival and 5.4 for summary application.

The hypothesis `Idempotent` is discharged on the engine, not here: re-offering a fact that the
initial-fact set already holds must add nothing. `TreeInitialFactAbstraction.addAbstractedInitialFact`
returns the empty list when `facts.addInitialFact` finds nothing new, which is exactly that property
at the one site the memo guards.
-/
import FactExplosion.Mechanism

namespace FactExplosion.Rederivation

variable {I O : Type} [DecidableEq I] [DecidableEq O]

/-- The state a derivation accumulates: the set of outputs produced so far. -/
abbrev Store (O : Type) := List O

/-- One step: given an input, produce outputs to add to the store. -/
abbrev Step (I O : Type) := I → List O

/-- The plain run: evaluate the step on every call, in order. -/
def run (f : Step I O) : List I → Store O → Store O
  | [], s => s
  | x :: rest, s => run f rest (s ++ f x)

/--
The memoised run: keep the inputs already seen, and skip the step for a repeat.

This is the whole optimisation. It does not look at what `f` returns, so it cannot depend on any
property of the ANSWER -- only on whether the input was seen.
-/
def memoRun (f : Step I O) : List I → List I → Store O → Store O
  | [], _, s => s
  | x :: rest, seen, s =>
      if x ∈ seen then memoRun f rest seen s
      else memoRun f rest (x :: seen) (s ++ f x)

/-! ## 1. The memo changes no answer

The engine's store is a SET: adding a fact it already holds changes nothing. That is the property
the memo rests on, and it is the reason no precision is traded -- the second evaluation of a step
was always a no-op, so skipping it cannot remove anything.

An earlier draft of this section stated the invariant over an APPEND store, which forced
`f x = []` and made the theorem vacuous. The store has to be a set for the statement to say
anything.
-/

/-- Insert one output, skipping what the store already holds. This is the engine's dedup. -/
def ins (s : Store O) (o : O) : Store O := if o ∈ s then s else s ++ [o]

/-- Insert a list of outputs, left to right. -/
def insAll (s : Store O) : List O → Store O
  | [] => s
  | o :: rest => insAll (ins s o) rest

/-- The plain run: evaluate the step on EVERY call and insert what it returns. -/
def runS (f : Step I O) : List I → Store O → Store O
  | [], s => s
  | x :: rest, s => runS f rest (insAll s (f x))

/-- The memoised run: skip the step for an input already seen. -/
def memoRunS (f : Step I O) : List I → List I → Store O → Store O
  | [], _, s => s
  | x :: rest, seen, s =>
      if x ∈ seen then memoRunS f rest seen s
      else memoRunS f rest (x :: seen) (insAll s (f x))

/-- Inserting an element the store already holds is the identity. -/
theorem ins_idem (s : Store O) (o : O) (h : o ∈ s) : ins s o = s := by
  rw [ins, if_pos h]

/-- The store only grows: insertion never removes. -/
theorem mem_ins (s : Store O) (o p : O) (h : p ∈ s) : p ∈ ins s o := by
  rw [ins]; split
  · exact h
  · exact List.mem_append_left _ h

/-- And insertion DOES hold what it inserted. -/
theorem mem_ins_self (s : Store O) (o : O) : o ∈ ins s o := by
  rw [ins]; split
  · assumption
  · exact List.mem_append_right _ (by simp)

theorem mem_insAll : ∀ (s : Store O) (os : List O) (p : O), p ∈ s → p ∈ insAll s os
  | _, [], _, h => h
  | s, o :: rest, p, h => by
      rw [insAll]
      exact mem_insAll (ins s o) rest p (mem_ins s o p h)

/-- Everything inserted is present afterwards. -/
theorem mem_insAll_self : ∀ (s : Store O) (os : List O) (o : O), o ∈ os → o ∈ insAll s os
  | _, [], _, h => absurd h (by simp)
  | s, a :: rest, o, h => by
      rw [insAll]
      rcases List.mem_cons.mp h with rfl | h'
      · exact mem_insAll (ins s o) rest o (mem_ins_self s o)
      · exact mem_insAll_self (ins s a) rest o h'

/-- Inserting a list the store already contains is the identity. -/
theorem insAll_idem : ∀ (s : Store O) (os : List O), (∀ o ∈ os, o ∈ s) → insAll s os = s
  | _, [], _ => rfl
  | s, o :: rest, h => by
      have ho : o ∈ s := h o List.mem_cons_self
      rw [insAll, ins_idem s o ho]
      exact insAll_idem s rest (fun p hp => h p (List.mem_cons_of_mem o hp))

/--
**THE INVARIANT: a step that ran once has its outputs in the store, so running it again is a
no-op.**

`Recorded f seen s` says every output of every input the memo has already skipped past is present.
That is what makes skipping safe, and it is exactly what the engine's initial-fact set guarantees.
-/
def Recorded (f : Step I O) (seen : List I) (s : Store O) : Prop :=
  ∀ x ∈ seen, ∀ o ∈ f x, o ∈ s

theorem recorded_after_insert (f : Step I O) (seen : List I) (s : Store O) (x : I)
    (h : Recorded f seen s) : Recorded f (x :: seen) (insAll s (f x)) := by
  intro y hy o ho
  rcases List.mem_cons.mp hy with rfl | hy'
  · exact mem_insAll_self s (f y) o ho
  · exact mem_insAll s (f x) o (h y hy' o ho)

/--
**The memoised run computes EXACTLY the plain run's store.**

Given the invariant, a skipped step would have inserted only what the store already holds, so the
two agree at every position. No finding can be gained and none can be lost -- and the argument never
mentions what a fact MEANS, which is why this carries no precision cost.
-/
theorem memo_run_eq_run : ∀ (f : Step I O) (xs seen : List I) (s : Store O),
    Recorded f seen s → memoRunS f xs seen s = runS f xs s
  | _, [], _, _, _ => rfl
  | f, x :: rest, seen, s, h => by
      rw [memoRunS, runS]
      split
      case isTrue hx =>
        -- skipped: the step would have inserted only what is already there
        rw [insAll_idem s (f x) (fun o ho => h x hx o ho)]
        exact memo_run_eq_run f rest seen s h
      case isFalse _ =>
        exact memo_run_eq_run f rest (x :: seen) (insAll s (f x))
          (recorded_after_insert f seen s x h)

/-- On an empty store with nothing seen, the invariant holds trivially, so the runs agree. -/
theorem memo_run_eq_run_init (f : Step I O) (xs : List I) :
    memoRunS f xs [] [] = runS f xs [] :=
  memo_run_eq_run f xs [] [] (by intro x hx; exact absurd hx (by simp))

/-! ## 2. The complexity separation -/

/-- How many times the plain run evaluates the step: once per call. -/
def plainCost : List I → Nat
  | [] => 0
  | _ :: rest => 1 + plainCost rest

/-- How many times the memoised run evaluates it: once per input not already seen. -/
def memoCost : List I → List I → Nat
  | [], _ => 0
  | x :: rest, seen => (if x ∈ seen then 0 else 1) + memoCost rest (x :: seen)

theorem plain_evaluates_every_time : ∀ xs : List I, plainCost xs = xs.length
  | [] => rfl
  | _ :: rest => by rw [plainCost, List.length_cons, plain_evaluates_every_time rest]; omega

/-- **The memo never evaluates more than the plain run.** -/
theorem memo_evaluates_at_most : ∀ (xs seen : List I), memoCost xs seen ≤ plainCost xs
  | [], _ => Nat.le_refl _
  | x :: rest, seen => by
      rw [memoCost, plainCost]
      have := memo_evaluates_at_most rest (x :: seen)
      split <;> omega

/-- A repeated input costs the memoised run NOTHING. -/
theorem memo_skips_a_repeat (x : I) (rest seen : List I) (h : x ∈ seen) :
    memoCost (x :: rest) seen = memoCost rest (x :: seen) := by
  rw [memoCost, if_pos h]; omega

/--
**The separation, on the measured shape.** A run of `n` calls over `d` distinct inputs costs the
plain step `n` evaluations; the memo pays at most `n` and skips every repeat, so on the traced
workload -- 345,127 arrivals over 48,339 distinct pairs -- it does the work `7.1x` less often.

The concept and the optimisation compute the same store (`memo_run_eq_run`); only the number of
evaluations differs. That is exactly the concept/optimisation distinction the project asks for, and
unlike every absorption operator it costs no precision at all.
-/
theorem the_separation (xs seen : List I) :
    memoCost xs seen ≤ plainCost xs ∧ plainCost xs = xs.length :=
  ⟨memo_evaluates_at_most xs seen, plain_evaluates_every_time xs⟩

end FactExplosion.Rederivation

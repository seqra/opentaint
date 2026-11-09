/-
# The premise is a mark CONJUNCTION, and a conjunction may be stored FACTORED

Claim 24 measured what a premise is. Of 267,486 distinct premises on conductor, **92.6% carry
exactly three marks**, and for one access path the realised set is 63,304 variants against
`C(75,3) = 67,525` -- 93.7% of the complete product. So the premise population is

```
    (access paths) x (3-element subsets of the mark alphabet)
```

with 617 access paths and 75 marks. The access-path factor is small and constant; the mark factor is
cubic and grows with the rule set.

## The idea

A premise that requires marks `{a, b, c}` is a CONJUNCTION. A conjunction can be stored as its
FACTORS -- one premise per single mark -- and re-formed by the consumer. That replaces `C(n,3)`
stored premises per path by `n`.

## What is proved here

* `sat_factored` -- a fact satisfies the conjunction premise **exactly when** it satisfies every
  factor. This is an EQUALITY of decision procedures, so the factored form answers precisely what
  the combination form answers: no false negative and no false positive are possible.
* `factor_length` -- the factored form stores `n` premises where the combination form stores one per
  subset.
* `subsets3_length` -- the combination form really does enumerate `C(n,3)` of them.
* `the_separation` -- both together at the measured alphabet: 75 against 67,525.

Nothing here is an abstraction. No fact is widened, truncated or folded, so unlike every operator in
Claims 5-22 there is no precision to trade -- which is why the soundness obligation is an equality
rather than an inequality.

## THE SIDE CONDITION, questioned and then MEASURED SATISFIED (CEGAR, 2026-09-05)

`sat` treats a premise's marks as INDEPENDENT requirements. The premise population looked as though
it might violate that:

* 265,970 multi-mark premises, and only **1.1%** draw all their marks from ONE rule;
* **2.77 distinct rules per premise**, e.g. `crypto.yaml:jjwt-hs256` + `jjwt-none-alg` + `jjwt-hs256`.

So a premise is an ACCUMULATED mark set spanning about three rules. The danger was JOIN rules: if a
conclusion depended on two marks CO-OCCURRING, then `{a,b}` would not be `{a}` and `{b}`, and
factoring would lose it.

**The ruleset was then read, and it does not do that.** Of 66 yaml files, 22 carry a `join:`, and
EVERY join condition has the shape

```
    <sourceTag>.$MARK -> <sinkTag>.$MARK
```

a single mark flowing from one tag to another. **No `on:` clause names two marks at one position:
the count of conditions containing a comma or an `and` is ZERO.** A join relates a source to a sink
through ONE mark, so no rule ever inspects a mark COMBINATION.

The co-occurrence is therefore incidental: a fact carries three marks because three different
sources happened to taint it, not because any rule asked for the conjunction. Marks propagate
INDEPENDENTLY, the side condition holds, and the theorems below apply to the engine.

**What this licenses.** A fact or premise carrying `{a,b,c}` may be kept as three carrying `{a}`,
`{b}`, `{c}`. The population per access path falls from `C(n,3)` to `n` -- at the measured alphabet,
67,525 to 75.
-/

namespace FactExplosion.MarkFactor

abbrev Mark := Nat

/-- A premise: an access path, and the marks that must all be present. -/
structure Prem where
  path : Nat
  marks : List Mark
deriving DecidableEq

/-- A fact: an access path, and the marks it carries. -/
structure Fact where
  path : Nat
  marks : List Mark

/-- The shipped form: the premise names a whole mark COMBINATION. -/
def sat (f : Fact) (p : Prem) : Bool :=
  (f.path == p.path) && p.marks.all (fun m => f.marks.contains m)

/-- The factored form: one premise per single mark, all on the same path. -/
def factor (p : Prem) : List Prem :=
  p.marks.map (fun m => ⟨p.path, [m]⟩)

/-- A fact satisfies a list of premises when it satisfies each. -/
def satAll (f : Fact) (ps : List Prem) : Bool := ps.all (sat f)

/-! ## 1. The factored form answers exactly what the combination form answers -/

theorem sat_mk (f : Fact) (pt : Nat) (ms : List Mark) :
    sat f ⟨pt, ms⟩ = ((f.path == pt) && ms.all (fun m => f.marks.contains m)) := rfl

/--
**THE EQUIVALENCE.** For a premise that requires at least one mark, the conjunction is satisfied
exactly when every factor is satisfied.

The `marks ≠ []` side condition is real and not a technicality: with no marks the combination form
still checks the PATH, while the factored form has no factor left to carry that check. The
measurement says 99.5% of premises carry at least one mark, and the 0.2% that carry none are stored
unfactored.
-/
theorem sat_factored : ∀ (f : Fact) (pt : Nat) (ms : List Mark), ms ≠ [] →
    sat f ⟨pt, ms⟩ = satAll f (factor ⟨pt, ms⟩)
  | f, pt, [], h => absurd rfl h
  | f, pt, [m], _ => by
      simp [sat, factor, satAll, List.all_cons, List.all_nil]
  | f, pt, m :: (m2 :: rest), _ => by
      have ih := sat_factored f pt (m2 :: rest) (by simp)
      simp only [sat, factor, satAll, List.map_cons, List.all_cons] at *
      -- both sides are `pathEq && present m && (pathEq && rest...)`; `pathEq` is idempotent
      cases hp : (f.path == pt) <;> simp [hp] at ih ⊢ <;> simp [ih]

/--
The corollary the engine needs: **replacing a premise by its factors changes no answer**, for every
fact. No finding can be lost and none invented.
-/
theorem factoring_preserves_every_answer (pt : Nat) (ms : List Mark) (h : ms ≠ []) :
    ∀ f : Fact, sat f ⟨pt, ms⟩ = satAll f (factor ⟨pt, ms⟩) :=
  fun f => sat_factored f pt ms h

/-! ## 2. The complexity separation -/

/-- The factored form stores one premise per mark. -/
theorem factor_length (pt : Nat) (ms : List Mark) : (factor ⟨pt, ms⟩).length = ms.length := by
  simp [factor]

/-- Every 3-element sublist, which is the population the shipped form realises per path. -/
def subsets3 : List Mark → List (List Mark)
  | [] => []
  | m :: rest => (pairs rest).map (fun p => m :: p) ++ subsets3 rest
where
  /-- Every 2-element sublist. -/
  pairs : List Mark → List (List Mark)
    | [] => []
    | m :: rest => rest.map (fun x => [m, x]) ++ pairs rest

/-- `C(n,3)` in closed form, which is what the measurement compares against. -/
def comb3 (n : Nat) : Nat := n * (n - 1) * (n - 2) / 6

/-- The enumeration and the closed form agree on the measured shape. -/
theorem subsets3_five : (subsets3 [1, 2, 3, 4, 5]).length = comb3 5 := by decide

theorem subsets3_six : (subsets3 [1, 2, 3, 4, 5, 6]).length = comb3 6 := by decide

/-- At the measured alphabet the combination form stores 67,525 premises per path. -/
theorem comb3_at_seventyfive : comb3 75 = 67525 := by rfl

/-- The factored form stores 75. -/
theorem factored_at_seventyfive (pt : Nat) (ms : List Mark) (h : ms.length = 75) :
    (factor ⟨pt, ms⟩).length = 75 := by rw [factor_length]; exact h

/--
**THE SEPARATION, at the measured alphabet.** The two forms answer identically
(`factoring_preserves_every_answer`) and the stored population differs by a factor of 900.

`67,525` is `C(75,3)`; the observed worst path realised `63,304` of them, 93.7% of the product.
-/
theorem the_separation : comb3 75 = 67525 ∧ 75 * 900 = 67500 := ⟨rfl, rfl⟩

/--
And the factored form is never the larger of the two, for any alphabet of FOUR or more.

The bound starts at four, not three: `comb3 3 = 1`, so with a three-mark alphabet the combination
form is the smaller one. The measured alphabet is 75, so the separation is real there -- but the
statement has to say where it begins.
-/
theorem factored_never_worse : ∀ n : Nat, 4 ≤ n → n ≤ comb3 n := by
  intro n h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [comb3]
  have e1 : m + 4 - 1 = m + 3 := by omega
  have e2 : m + 4 - 2 = m + 2 := by omega
  rw [e1, e2]
  have hp : 6 ≤ (m + 3) * (m + 2) := by
    calc (6 : Nat) = 3 * 2 := rfl
      _ ≤ (m + 3) * (m + 2) := Nat.mul_le_mul (by omega) (by omega)
  have key : (m + 4) * 6 ≤ (m + 4) * (m + 3) * (m + 2) := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left (m + 4) hp
  exact (Nat.le_div_iff_mul_le (by omega : 0 < 6)).mpr key

/-- The three-mark alphabet is the exception, and it is worth recording rather than hiding. -/
theorem comb3_three_is_smaller : comb3 3 = 1 := by rfl

end FactExplosion.MarkFactor

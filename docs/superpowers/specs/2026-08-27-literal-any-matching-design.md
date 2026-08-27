# Literal `[any]` matching: delta, concat and the premise ladder

> **The invariant.** A fact's premises are its literal prefixes. `a.f.[any].*` yields at most
> `a`, `a.f`, `a.f.[any]` — three, not `Σ n!/(n−k)!`. Nothing anywhere synthesises a concrete
> accessor out of an `[any]` in order to *match* a premise.

---

## 1. The situation this corrects

`2026-08-26-tifa-never-unroll-design.md` removed the fact **materialisation**: no accessor is copied
out of an `[any]` into `added` any more. It did not remove the premise **enumeration**. Two rules
survived to keep the ladder walking:

- **R3c** emits a concrete `p.a` for an accessor `a` that is demanded at this level, covered by
  `[any]`, and present in no concrete branch of the fact.
- **R4** descends into it on the next walk through `AccessTree.AccessNode.getChild(a)`, whose third
  term SYNTHESISES `a` out of the `[any]` edge.

The implementation note records the consequence in one line: *"`AnyUnrollGrowthPatternTest` passes
UNCHANGED, 4/15/64 and all. R3c hands out `p.a`, R4 descends, the caller refines, R3c hands out
`p.a.b` — the same `Σ n!/(n−k)!` family, reached by reading instead of copying."* The synthesis arm
fires **25–34M times** on the frontier conductor arm, every one of them `fromNothing`.

The same arm is what closes the round trip on the fact side, pinned by `AnyDeltaConcatRoundTripTest`:

```
fact arg0.[any].*   premise arg0.a   ->  delta consumes NOTHING, remainder is still [any].*
conclusion ret.a.*  concat            ->  ret.a.[any].*        one concrete link longer, [any] intact
```

Every lap adds a link and re-arms the next one. `filterStartsWith` has the same shape on the
subscription channel, where it rebuilds the matched premise as a spine on top and bypasses
`limitFieldAccess` entirely.

R3c/R4 and the delta synthesis are one loop: R3c emits the premise, the synthesis arm matches it
back. Cutting either end alone leaves the other end doing useless work. This design cuts both.

---

## 2. The rule

`[any]` is read two different ways depending on the question being asked. Today it is read the same
way for both.

| question | operations | `[any]` reading |
|---|---|---|
| what does this fact **denote**? | `readAccessor`, `startsWithAccessor`, `contains`/`equalTo` — cleaners, rule preconditions, alias, side effects, trace resolution | zero-or-more covered steps. **Unchanged.** |
| which premise does this fact **match**? | `AccessTree.delta`, `AccessNode.filterStartsWith`, `AccessBasedStorage` premise lookup, TIFA's descent | **literal.** |

`AccessNode.getChild` has three terms. The matching reader keeps two and drops one:

```
literal(a)                  the fact holds `a` as an edge of its own                 KEEP
any().literal(a)            `[any]` taken ZERO times, `a` on the node below it       KEEP
any().reinstalled_below(a)  `a` SYNTHESISED out of the `[any]`                       DROP
```

The dropped term is the unique step that **consumes a premise link without descending the fact**.
Dropping it gives:

> **Progress.** Every premise link consumed by `delta` strictly descends the fact's DAG.

From which: `delta(a.[any].*, a.f) = ∅`, `delta(a.[any].*, a.f.[any]) = ∅`, the round trip is
unconstructible, `filterStartsWith`'s spine re-prepend is unconstructible, and `maxDepth` is an exact
upper bound on reachable depth again — so the prefilter that `[any]` disabled at
`AccessTree.kt:2528` becomes valid unconditionally.

### 2.1 Why the zero-step term stays

Not symmetry — it is load-bearing, and the argument is measured rather than reasoned.

R3b emits `p.u` for a taint mark `u` inside an `[any]` subtree, and its comment names the mechanism:
*"`AccessTree.getChild` hoists the `[any]`'s child up, so `p.u` matches the fact that produced it."*
That hoist **is** the zero-step term. R3b off is measured at conductor `Total vulnerabilities: 2 → 0`
plus two lost `CleanerFieldSensitivityAnalysisTest` cases. A stricter literal-only delta would take
the same loss by the back door.

The zero-step term is also exact, not a widening: it descends strictly, so it cannot re-arm anything.

### 2.2 Why partial measures are out

Synthesising only when the premise is one link longer than the fact, or capping the synthesis depth,
slows the ratchet without removing it. Every cap arm (`L` = 0, 3, 10, 100) has already been measured
and each either failed to converge or lost findings.

### 2.3 What TIFA emits afterwards

R0, R2, R3a, R3b remain; **R3c and R4 are deleted**. What remains emits only literal prefixes:

```
fact  a.f.[any].*      premises ⊆ { a , a.f , a.f.[any] }         |premises(F)| ≤ |nodes(F)|
```

`AnyUnrollGrowthPatternTest` goes from `Σ n!/(n−k)!` (4, 15, 64 for demand sets of 2, 3, 4) to linear.

### 2.4 Concat

**No semantic change**, and that is a finding rather than an omission: the ratchet lived entirely in
`delta`. Concat was its amplifier — it relocated a remainder that should never have existed.

Both absorptions stay exactly as they are. `absorbCoveredByAnyPrefix` is a sound widening firing 60
times in 29M graft points. `absorbBeyondAnyEntries` carries 2.83M of 2.84M absorptions and still
fires, because a remainder legitimately carries an `[any]` when the caller's fact literally has one
below the premise.

What concat gains is a **checkable postcondition**, false today:

```
depth(concat(C, delta(F, p))) ≤ depth(C) + depth(F) − len(p)
```

### 2.5 Soundness

**State the awkward half first: the new `delta` is deliberately an UNDER-approximation of
denotation.** A fact `arg0.[any].*` really does denote `arg0.g.p`, so a summary keyed on `arg0.g`
really does apply to it, and the literal rule declines to apply it. Matching is no longer *"the fact
denotes the premise"*; it is *"the fact holds the premise literally"*, which is strictly smaller.

Completeness is recovered on the **supply** side, not the matching side, and this is why TIFA and
`delta` had to change in the same commit:

> Every fact emits a premise that covers it. R3a emits `p.[any]` at every level with demand; where
> demand is `null` R0 emits the bare `p`, which is coarser still; where demand is empty a premise
> ending there has already been emitted and its `.*` covers the rest. So for any fact `F` reaching a
> call site there is always an emitted premise `q` with `delta(F, q) ≠ ∅` and `q` at least as coarse
> as anything the old reader would have matched.

The flow is therefore obtained through a coarser premise rather than lost. What is given up is
precision — and the residual risk is not unsoundness but SCHEDULING: the coarse premise's summary has
to be computed, and on a run that is cut short by the IFDS budget a summary that has not arrived is
indistinguishable from one that does not exist. The change makes every arm cheaper, which pushes that
risk the right way, but it is the one channel by which a finding could move.

The entry fact itself moves the safe way. A fact that reaches a callee only through its `[any]` now
enters as `p.[any].*` rather than `p.a.*`: strictly coarser, so false positives, never false
negatives — with two named exceptions, both already accepted:

- A cleaner that bites on a concrete path stops biting under an `[any]`. Accepted 2026-08-26; pinned
  by `TreeCleanerFieldSensitivityAnalysisTest`.
- Fewer empty deltas means fewer `SummaryExclusionRefinement`s, so exclusion sets refine more slowly.

The premise set only shrinks — R3a already emits `p.[any]` at every level R3c fired at, and the
callee's result under `p.[any].*` subsumes its result under `p.a.*`. **Losing a finding remains the
line**: the gate is findings unchanged.

### 2.6 The cleaner coupling — found by measurement, not by design

**§2.5's completeness argument has an exception, and the suite found it.** With the rule on,
`CleanerDslAnalysisTest`'s AnyField matrix lost **every** finding at every depth: an `[any]` source
through a *plain* cleaner reached no sink at all. `-Dopentaint.literalAnyMatch.premises` attributed
it to the R3c/R4 removal, and `.premises.r3c` / `.premises.r4` showed each rule was independently
necessary. The control that named the mechanism was the neighbouring test
`without cleaners AnyField sources reach both sink forms at every depth`, which **passes** — so the
depth ladder was never the problem; the cleaner was.

The mechanism, in `Cleaner.cleanConcrete`'s `TaintCleanReach.Exact` arm:

> An exact cleaner cleans `x.![m]` and nothing deeper. The fact's `[any]` node carries the mark for
> EVERY step count at once — zero steps, which the cleaner does clean, and one-or-more, which it
> must not. `[any]` is zero-or-more, there is no one-or-more accessor, and the mark sits on a single
> node, so the two readings cannot be separated. The code cleared the mark and kept whatever
> concrete rungs sat under the `[any]` — which was only ever non-empty because **R3c/R4 put them
> there**. Remove the ladder and clearing collapses the whole fact.

So the cleaner's precision was resting on the premise ladder. Three options were measured:

| | result |
|---|---|
| clear, as before | every AnyField-matrix finding lost — **FN**, not acceptable |
| keep the `[any]` branch | every finding recovered; **exactly one extra shape**, `AnyField-Plain-Plain-field-depth0`, plus its twin in `returning exact cleaner…` |
| separate the two readings | not available: it needs a one-or-more accessor the representation does not have |

Keeping the branch ships (`EXACT_CLEANER_KEEPS_ANY`, defaulting to `literalAnyMatch` since the two
are one decision). It is the FP direction, it is the same line already taken for
`TreeCleanerFieldSensitivityAnalysisTest` on 2026-08-26, and the **688-test rule-level suite is
byte-identical across all three arms** — the entire cost falls on the cleaner DSL's own precision
specification, not on any rule.

**And the limit is the tree representation, not the semantics.** `FactCleanerContractTest` made this
visible by failing on the *automata* backend after the tree backend was fixed:

| backend | `[any]` as | can it separate zero-step from one-or-more? |
|---|---|---|
| automata | a self-loop on the initial state, with the mark reachable through it AND directly | **yes** — delete the loop and the zero-step path remains, so the alternative really is removed |
| tree | one node below one `[any]` edge, standing for every step count at once | **no** — clearing the mark discards the `≥1`-step readings with it |

So `removedAlternative` is not a uniform contract and asserting it as one was wrong. The property
every backend must hold — and the one the findings depend on — is that an exact cleaner **keeps the
mark reachable behind the `[any]`**, while `ExactAndAnyField` removes it. That is what the contract
test pins now. It also says plainly what a one-or-more accessor would buy the tree backend, which is
the cleanest statement of what this representation is missing.

### 2.7 What this does not fix

The conductor explosion measured on 2026-08-26 is `java.lang.Object`-typed model accessors defeating
the type filter — 86.7% of allowed field steps are type-vacuous
(`2026-08-26-frontier-fact-explosion-anatomy.md`). That is a different mechanism and this design does
not touch it. This design removes the `[any]` ladder, which is the star / thingsboard mechanism.

---

## 3. Surface

Tree backend only. `ApMode.Tree` is the only production backend; automata and cactus are unchanged
and the cross-backend expectations fork (§4).

| file | change |
|---|---|
| `AccessTree.kt` | split the reader: `getChild`/`getChildRecording` keep the three terms (DENOTATION); new `getChildMatching` has two (MATCHING). `deltaImpl` and `filterStartsWithImpl` switch to it. `filterStartsWithImpl`'s `maxDepth` prefilter loses its `containsAnyInThisOrDeepNodes` escape. |
| `TreeInitialFactAbstraction.kt` | delete the R3c block and the R4 block. |
| `AccessBasedStorage.kt` | `collectNodesContainsAnyAccessor` drops the **expansion** arm (re-entering every covered-accessor trie child with the same `[any]`-rooted pattern); keeps the zero-step and structural arms. |
| `TreeApManager.kt` | `literalAnyMatch` flag, constructor parameter over a system property, following `anyUnrollLimit`; plus `reader` / `lookup` / `premises` / `premises.r3c` / `premises.r4` overrides for ablation. |
| `Cleaner.kt` | `EXACT_CLEANER_KEEPS_ANY` — an exact cleaner no longer clears a mark from under an `[any]`. §2.6. |
| `DefaultConfiguration.kt` | the new properties added to `FORWARDED_TEST_PROPERTIES`. **Required**: a test worker inherits nothing, and without the declared input a run with a different value is UP-TO-DATE and silently reports the previous run's results — which invalidated the first bisect. |
| `ApOpDiagnostics.kt` / `TifaDiagnostics.kt` | count what the new rule refused, so the cost is measured rather than inferred. |

### 3.1 The flag

`-Dopentaint.literalAnyMatch` — **default true**, i.e. the new behaviour is the behaviour. The flag
exists to restore the old reader for a controlled A/B on the harness, and follows the established
pattern: build the ablation, measure it, delete it. It is a `TreeApManager` constructor parameter so
a test can pin it without touching global state.

### 3.2 Diagnostics

- `matchRefusedAnySynthesis` — incremented in `getChildMatching` at exactly the condition where the
  old reader would have synthesised and returned non-null (`isCoveredByAny(a)`, no literal child, no
  zero-step child, an `[any]` edge present). This is the whole cost of the change, counted.
- `emitsSynthesised` (R3c) and `virtualDescents` (R4) keep incrementing at the point of suppression,
  so the effect size is readable from the new arm without running the old one.
- Premise-count histogram: `|premises(F)| / |nodes(F)|`, which is the invariant itself, observed.

---

## 4. Tests

**Inverts — these are the acceptance tests.**

- `AnyDeltaConcatRoundTripTest` — all three cases. "reading a concrete accessor off an `[any]`-carrying
  fact consumes nothing" becomes "yields no delta"; the round trip yields nothing to graft; the
  ratchet's depth sequence becomes constant.
- `AnyUnrollGrowthPatternTest` — 4/15/64 becomes linear. The headline.
- `AnyAccessorCollapseTest` `filterStartsWith matches a premise longer than the any depth charge`.
- `AccessBasedStorageAnyLookupTest` — the expansion arm's cases.

**Forks.** `InitialFactAbstractionTest` `any accessor scenario 1…7` and `scenario 36` assert a premise
naming an accessor present in no concrete branch. The tree subclass expects `p.[any]`; the automata
subclass keeps `p.a`. This is the same pattern already used for the cleaner divergence on 2026-08-26,
so the split reads as a backend difference rather than a suppression.

**Must stay green — the findings gate.** The rule-level suites, the Go sample suites,
`CleanerFieldSensitivityAnalysisTest`, `StarOperatorTest`, `FactCleanerContractTest`, and the full
`gate.sh` run at its current baseline (3,484 tests, 2 pre-existing failures in
`JIRFactTypeCheckerUnrollFilterTest`, which belong to the type-vacuity finding and not to this one).

---

## 5. Validation

0. **Before touching code**, run the frontier arm with `TifaDiagnostics` and `ApOpDiagnostics` on and
   record R3a/R3b/R3c/R4, `B-getChildAny`, `deltaThroughAny*` and the premise count. That is the
   predicted effect size; without it the result is unattributable.
1. Unit gate, then the rule and sample suites: findings unchanged.
2. Harness A/B on the conductor single-entry-point / single-rule arm, `single-rule` and
   `single-rule-nostar`, `-Dopentaint.literalAnyMatch` true vs false, two replicates. Conductor's
   `Total vulnerabilities: 2` and the `single-rule-nostar` SARIF sha256 are the invariants.
3. The star arm and thingsboard, where the `[any]` ladder is expected to actually bite.
4. Confirm the invariant empirically from the premise histogram, not from the design.

---

## 6. Open

1. `absorbBeyondAnyEntries` short-circuits on the `[any]` manager being enabled, yet it is a pure
   widening that needs no budget. Once nothing unrolls anywhere, its gate should become
   unconditional — deferred, because it changes behaviour at the shipped `L=-1` default.
2. With no unroll left anywhere, `AnyUnroll.kt` — state, budget, kind policy, rescore, `L` — has no
   client but the two absorptions. Deleting it is a follow-up, deliberately not in this change.
3. R3b still emits only `p.u`, never the speculative `p.[any].u`. **Tried and measured during this
   change: it moves nothing.** With the ladder gone it looked like the only rule that could name a
   mark below an `[any]`, but adding it — gated and ungated — left `CleanerDslAnalysisTest`
   identical, and `AnyPremiseAbstractionTest`'s `a demanded mark below an any is named at this
   prefix` pins the deliberate refusal to emit it speculatively. Reverted. Recorded so the next
   person does not re-derive it.
4. A **one-or-more accessor** would let the tree backend separate the two readings an `[any]` folds
   together, and would recover the precision §2.6 gives up. That is a representation change, not a
   fix, and it is the cleanest statement of what the tree access-path language is missing.

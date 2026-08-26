# The any-manager: implementation review and the performance investigation

`saloed/7-fact-explosion-report`, 2026-08-26. Frontier analyzer throughout:
`anyUnrollLimit=100`, `anyUnrollKindPolicy=rescore`, `anyUnrollRescoreStrategy=bfs`, conductor,
one Spring handler (`WorkflowResource#rerun`), one taint rule.

**How to read this.** Four questions were asked, two about the implementation and two about
performance. Each gets its own section and each section states its verdict first. Where a section
overturns something an earlier document asserted, §9 lists it. Numbers are quoted with the run they
came from; ranges span replicates.

Contents: §1 the question · §2 findings · §3 concat as bulk tree prepend · §4 the greedy predecessor
· §5 the performance arithmetic · §6 the fixed point · §7 the measurements (7.1 graft anatomy · 7.2
the two `⊑` holes · 7.3 the telescope · 7.4 the selector · 7.5 **the profile** · 7.6 the abstract
cancellation · 7.7 **the memo**) · §8 what changed in the code · §9 what this leaves ·
§10 corrections · §11 caveats

---

## 1. The question

1. **Concat.** In `this.concat(delta)` with an `[any]` in the delta, the manager's absorption should
   also absorb accessors from `this`. Concat's semantics should be stated as a **bulk tree prepend**.
   Review how that absorption is implemented.
2. **The predecessor pick.** `absorbInto` chooses greedily (lowest id) among several predecessors.
   The design was written for forks. Returning the single predecessor is right when there is one;
   otherwise a forked state, not a greedy pick.
3. **Fixed point.** Does the manager violate the fixed-point guarantee, so the analysis never ends?
4. **Cost.** Or is the degradation the cost of massive operations — many absorptions, concat of huge
   facts? Profile it.

---

## 2. Findings

**The absorption the question asks for exists.** It is `absorbBeyondAnyEntries`, reached from
concat's spine rebuild, and it is **2,833,189 of 2,835,513 absorptions (99.9%)** on the frontier arm.
The other direction — `absorbCoveredByAnyPrefix`, the receiver's `[any]` eating the delta's prefix —
is the near-dead one: its guard held at **60 of 29,388,226 graft points**. The review question is
therefore how well (b) works, and the measured ceiling on making it work better is **+14.5%**: of
11.4M declined absorptions, 78.5% would absorb into a self-loop that rewrites nothing and 17.9% have
no incoming edge, leaving 3.6% that would move. §3.

**One thing the shipped default does not have.** Direction (b) short-circuits on
`!manager.anyUnroll.enabled`, and the shipped default is `anyUnrollLimit = -1` = off. Direction (a)
needs no manager. So at the default configuration concat has **no** delta-side absorption at all, and
the surviving direction is the one that fires at 0.0002% of graft points. §3.2.

**The greedy pick is imprecise, never unsound**, and the harm one would most want to attribute to it
is structurally impossible: `mint` gives a child its parent's dag and only `union` fuses dags, so a
state's dag **is** its reachability component and every candidate predecessor is already inside it.
The pick cannot move a fact between pots, cannot change the charge, cannot change which origin pays.
The only thing it can change is the **kind** of the position the fact lands on — which is what gates
the next prepend. §4.

**Two counters that were evidence and were not.** `witnessDisagreesWithThreadedState` was declared
and reported and **never incremented**; every result document that read its zero as "Lemma 9.2 holds
in production" read nothing. And `telescopeStalls` counted probes that had no `[any]` position to
start from, which is why 97–98% of stalls looked like first-link stalls. Both fixed. §4.3, §9.

**The performance question has an arithmetic answer, and it is not a performance problem.**
Differencing the frontier arm's counters between 0–228 s and 228–793 s:

| | 0 → 228 s | 228 → 793 s | |
|---|---|---|---|
| events | 877,371 (3,855 ev/s) | 109,533 (**194 ev/s**) | **19.9× slower** |
| node touches | 658,001,505 (2.89 M/s) | 1,437,865,812 (**2.54 M/s**) | **1.14× slower** |
| concat result nodes / event | 222.17 | 3,572.38 | 16.1× |
| E-delta fact nodes / event | 373.56 | 8,994.19 | 24.1× |
| graft points / concat call | 15.72 | 109.1 | 6.9× |

**Node-touch throughput is conserved to within 14% while event throughput collapses 20×.** The engine
is not getting slower. Each event is 20× more expensive because the facts are 16–24× bigger, and the
product of the two is flat. §5.

**And `pointsPerCall` is mostly a re-visit, not a fan-out.** The sampled receiver holds **8.0 distinct
nodes of which 2.1 are abstract**, against **15.7 graft points per call** — a 7.5× re-visit factor.
`manager.abstractNode` is a process-wide singleton, so every `*` leaf in a receiver is the same
object, and `concatToLeafAbstractNodes` memoises the delta side and never its own result. Measured
directly: **87.8% of graft points re-offer the delta to a node already grafted in the same call.**
§3.3, §7.1.

**The one thing in the engine that is superlinear in fact size — and nobody had ever profiled it.**
`AccessTreeAnySuffixMatcher.getNonMatchingNode` is **0 of 3,440 execution samples in the first 60 s
and 73.6% of all analyser CPU in the late window**, plus **83.5% of all heap allocation** (254 GB of
`Object[]` and 24.9 GB of boxed `Integer` in 120 s, from two lines). Its cost per event grows ~1,120×
while the number of merge pairs grows 20.7× — **≈54× more cost per pair**. Everything else in the
engine grew 7–15× against that 20.7×, i.e. linear or better. It is the `[any]` subsumption walk, it
has no memo, and a fact is a DAG. §7.5.

**Three suspects refuted with numbers**: the manager's global lock (**zero** contended monitor-enter
events at a 1 ms threshold across the whole late window, 0 blocking stacks), interning and hashing
(9.07% → **0.83%**, it *falls*), and GC pauses (2.07%). And one thing nobody had looked at: the
solver runs on **1.16 of 10 worker threads** late — real, structural, and not the collapse. §7.5.

**Memoising that walk is worth 1.4–1.8× and proves the point it was meant to disprove.** The memo hit
rate is **79–82%** — four of every five visits were re-deriving a shared subtree — and findings are
unchanged. But every memoised arm now ends on the **low-memory stop instead of the timeout**, at 8 GB
*and* at 16 GB. Removing the single largest constant factor in the engine buys a minute of curve and
moves the wall. §7.7.

---

## 3. (I.1) Concat is a bulk tree prepend, and which absorption fires

### 3.1 The semantics, stated

Write `Σ` for the accessors `isCoveredByAny` accepts, `L(N)` for the language of accessor sequences a
node denotes, `A(R)` for the root-to-node sequences of the receiver `R` whose endpoint is
`isAbstract` — **counted with multiplicity**, because the receiver is a DAG — and `R⁻` for `R` with
every abstract marker cleared. Then

```
L(R.concat(D))  =  L(R⁻)  ∪  ⋃_{w ∈ A(R)}  w · L( Φ_w(D) )
```

`w · L(·)` **is** the bulk prepend: grafting at `w = a₁…a_k` is `prependAccessor(a₁) ∘ … ∘
prependAccessor(a_k)` applied to the conditioned delta, done in one pass instead of `k` passes.
`Φ_w` is that conditioning, and its order is the C0 comment's:

```
Φ_w(D) = filterDeepExclusion_w ∘ limitElementAccess_{e(w)} ∘ [absorb_w] ∘ filterTypes_{filter(w)} ∘ limitFields_{fields(w)} (D)
```

Where each part lives, in `AccessTree.kt`:

| formula part | code |
|---|---|
| the graft point test `w ∈ A(R)` | `:2347` `if (isAbstract && other != null)`; counted at `:2335` |
| `Φ_w` | `:2354-2364`, the **C0** block |
| `fields(w)`, `e(w)` accumulating down the path | `:2368-2376` |
| the descent that enumerates `A(R)` | `:2379-2386`, **unconditional** — a graft point can sit below another |
| **`w · (…)`, the prefix re-installed** | `:2393-2400` `manager.create(isAbstract = false, …).bulkMergeAddAccessors(nestedAccessors, anyId)` — one accessor of `w` per frame, bottom-up |
| `L(R⁻) ∪ …` | `:2402`; note `isAbstract = false`: the graft consumes the receiver's abstraction |

The prefix is materialised nowhere as a list; it is the recursion stack, and
`bulkMergeAddAccessors` is the single-link prepend applied once per frame as the stack unwinds. That
is why the absorbing prepend had to be installed *there* and not in `installAbove`: **concat never
reaches `installAbove`.** Both of its constructions go to the array factory `create(isAbstract,
isFinal, exclusion, accessors, accessorNodes, anyState)`.

### 3.2 The two directions, and which one is alive

| | (a) `absorbCoveredByAnyPrefix` | (b) `absorbBeyondAnyEntries` |
|---|---|---|
| what it folds | the **delta's** leading covered accessors, into the **receiver's** `[any]` | the **receiver's** spine link, into the **delta's** `[any]` |
| where | `AccessTree.kt:1256`, called at `:2356` under `parentEdgeIsAny` | `AccessTree.kt:1562`, called from `bulkMergeAddAccessors` `:1501` |
| consults the automaton | **no** — no `writesAbove`, no `absorbInto`, no kind, no pot | yes: `writesAbove` gate + `absorbInto` backward step |
| works at the shipped default `L = -1` | **yes** | **no** — `:1573` short-circuits on `!manager.anyUnroll.enabled` |
| telescopes | yes, to a fixpoint, within one call | yes, one link per frame, as the stack unwinds |
| §4.3 subtree GUARD | absent | present (`:1704`) |
| **fired on the frontier arm** | **60 of 29,388,226 graft points** | **2,833,189 of 2,835,513 absorptions** |

So **the absorption the question asks for is (b), and it is implemented.** It is reached from the
spine rebuild, its `[any]` is the delta's, and the accessor it eats is the receiver's. `graftAbsorbs`
is incremented there and only there.

The asymmetry is real and it is the other way round from the intuition: `receiverCarriesAny` is
**17 of 1,868,960 calls**, because on conductor the receiver is the summary CONCLUSION (a concrete
prefix) and the delta is the caller's REMAINDER (which carries the `[any]`). `graftFilterAnyTail`
uses the identical predicate to `parentEdgeIsAny` and reads **60**. Direction (a) is dead here.

**The one gap worth naming**: direction (b) needs the manager, and the manager ships off. At
`anyUnrollLimit = -1` concat has no delta-side absorption at all, and the surviving direction fires
at 0.0002% of graft points.

### 3.3 The ceiling on making (b) fire more, and why `pointsPerCall` is the real quantity

Of the 11,410,480 prepends the kind gate declined, the counterfactual probe says what would have
happened had it been open:

```
outcome=[guardBlocked:0, uncovered:0, noPredecessor:2,037,244, wouldStay:8,962,678, wouldMove:410,558]
```

**78.5% would absorb into a self-loop and rewrite nothing; 17.9% have no incoming edge; 3.6% would
move.** Opening the gate completely takes absorption from 2,833,189 to at most 3,243,747 — **+14.5%**
— on a mechanism already measured not to reduce node mass. And 83.1% of all declines come from a
single automaton state. **Opening the gate is not the lever.**

The quantity that runs away is `k`, the graft multiplier in `|result| ≈ |receiver| + k·|delta|`. It
grows **15.7 → 109.1** between the early and late windows (§5). And the sampled receiver holds

```
C-sample n=3650  recv size/distinct/abstract = 130,856 / 29,243 / 7,698
                 → per call        35.85    /   8.01   /  2.11
C-graft  pointsPerCall = 15.72
```

**2.11 distinct abstract nodes against 15.72 graft points — a 7.5× re-visit factor.** `size` counts
nodes with path multiplicity while `countNodes()` counts distinct ones. `manager.abstractNode` is a
process-wide singleton, so every `*` leaf in a receiver is literally the same object, and
`concatToLeafAbstractNodes` memoises the **delta** side (`FilteredNode`'s `cache`, `typeFilterCache`,
`absorbCache`) and never its own result.

Two mechanisms make `k` large, and they have different fixes:

- **re-visitation** — the same receiver node grafted again in the same call. Answered by a memo.
- **nesting** — a graft point strictly below another. Answered by a subsumption rule.

Neither had ever been measured; both are counted now (§8).

### 3.4 The deep-graft subsumption: sound only under a precondition

If the delta's root owns an `[any]` covering `a`, then `a·L(D) ⊆ L(D)`, hence `w.a·L(D) ⊆ w·L(D)` and
the deep graft is subsumed by the shallow one. The algebra holds. Three things qualify it:

1. **The predicate the code tests is the wrong one.** `concatAnyDeltaCalls` uses
   `containsAnyInThisOrDeepNodes` (121,015 calls, 6.5%). The subsumption needs *root-level*
   `anyId != null`. The rendered big deltas put their `[any]` at depth 6–8 behind a concrete spine.
   Nothing measured the root predicate; it is counted now.
2. **A weaker form already runs, post-hoc.** `mergeAdd`'s default `foldToAny = true` drives
   `trimAnyCoveredAndPushChildren`, which deletes from each side every branch the other's `[any]`
   suffix language denotes. So the redundant deep grafts are **built and then deleted** — the
   optimisation exists on the result, not on the work. Except that the trim **never cancels
   `isAbstract`** (§6.2), and deep grafts on conductor end abstract.
3. **The eager skip is UNSOUND without a precondition.** `filterTypes` runs per graft point with
   `path`, and the descent passes the *unfiltered* delta to children — filters do not accumulate.
   `JIRFactTypeChecker.accessorActualType` reads only the last accessor and returns unconditional
   accept for an empty path and for a path ending in `[any]`. So a deeper point is routinely **more
   permissive** than its ancestor, and skipping it would drop paths the deep filter admits. That is a
   lost flow, not a coarsening. The skip is sound only where the shallow point's type filter was the
   identity — a population that is measured and large (`emptyPath` = 1,110,261 points carrying 48.8%
   of all delta mass).

**Verdict: the mechanism the question names is implemented and works; its ceiling is +14.5%; the
lever is `k`, and `k` is mostly re-visitation.**

---

## 4. (I.2) The greedy predecessor

### 4.1 Sound, and provably so

`[any]@r` denotes `Σ*` for **every** `r`. The state is a budget and provenance annotation, not a
language restriction: in `AccessTree.kt`, `anyId` is read only by `hash`, `equals`, and the manager
entry points. So the rewrite `a.[any]ˢ.R ⟼ [any]ᵗ.R` produces the identical language for every `t`,
and the pick cannot under-approximate at the moment of the rewrite.

The one place a state is consumed semantically is the pot: `readChildPaidOnly` refuses on
`dag.total >= limit`, and `budgetExhausted` switches the initial-fact abstraction between emitting a
concrete enumeration and emitting the coarse `[any]` premise. **The pick cannot reach it.**
`putTransition` has two callers: `mint`, which gives the child `current.dag.find()`, and
`mergeStates`'s incoming remap, which runs *after* `union` has already fused the dags. DSU links are
permanent. Therefore

> every predecessor of a state shares that state's dag representative,

so the pick is invisible to `budgetExhausted`, to the charge, and to which origin pays. The design's
own worry — that a greedy pick "can move a fact's `[any]` into the automaton of an unrelated program
location" — is true about the *automaton* and false about the *pot*: once fused they are one pot.

**Greedy is imprecise, never unsound.** Both branches of the remaining consumer, the kind gate, are
sound: writing `a.[any].R` is exact, absorbing to `[any].R` is a superset.

### 4.2 And it is not a fixed-point violation either

Write `δ(p,a)` for the forward step (`readChild`, total — it mints when absent) and `σ(t,a)` for the
backward selector. The forward re-check at `AnyUnroll.kt:1445` gives

> **(F)** `δ(σ(t,a), a) = t` for every non-null answer,

and the selector is a function of `(t,a)` alone — it does not consult the fact's history — giving
**(D)**. From F and D:

- **Lemma.** With `Σ(p) = σ(δ(p,a), a)`, `Σ∘Σ = Σ`. *Let `s = δ(p,a)`, `q = σ(s,a)`. By F,
  `δ(q,a) = s`, so `Σ(q) = σ(s,a) = q`.*
- **Theorem.** For a word `w = a₁…a_k` the fold — backward from `a_k`, writing literally from the
  first refusal — is **idempotent**. *By repeated F the second lap reaches the same `v = δ*(p,w)`;
  by D the backward fold from `v` over `w` stalls at the same index and yields the same state.*

**So the round trip closes after at most one extra lap, at a fact at most `j` links longer than the
ideal.** Greedy costs a link, permanently; it does not cost termination. The worked fork
(`r --b--> p --a--> t₁`, `q --a--> t₂` with `q.id < p.id`, then `union(t₁,t₂)`) confirms it: lap 1
stalls and writes `b`; lap 2 produces a byte-identical fact and the merge guard fires.

This holds under a stable automaton. Unions change `σ` — but 209 unions against 2.8M absorbs.

### 4.3 The counter that decided this question does not measure it

`telescopeStalls` was read as "a fold that had a path and did not find it". The arithmetic says
otherwise:

```
filterStartsWith calls        754,042
minus telescopeStalls        -581,726
                            = 172,316   non-stalling descents
[any] reads, whole run        163,923
```

**172,316 ≈ 163,923.** A descent telescopes iff its tail crossed an `[any]`; the stall count is
essentially `filterStartsWith calls − [any] reads`. And the probe's own code makes it so: it entered
the loop with `probe = filteredTreeNode.anyId`, which is routinely `null`, and recorded the immediate
`null` result as a first-link stall. With **2,325 forks in the whole run**, forks can account for at
most 0.4% of the 581,726 stalls.

There is also a first-principles reason a first-link stall cannot be evidence of an earlier mis-pick:
`readChild` **never refuses**, so after any `[any]`-crossing forward step the child has the position
in its `parents`, and the first backward step cannot stall whatever state the fact was standing on.

So the 2026-08-25 decision not to build the subset construction was **right, for the wrong reason**,
and right again on the frontier arm for an independent one: 2,325 forks against ~14.2M backward
queries, max width 4.

### 4.4 What was changed, and what was not

Shipped: **self-loop first, then min id.** A self-loop `p --a--> p` is the automaton saying `a` is
already folded into this `[any]`; absorbing there is the exact inverse of the read that put the fact
in place, and min-id could walk away from one for no reason beyond allocation order.

Not shipped, and why:

- **DSU-union of the predecessors.** Sound, but the design forbids it by name (it pushes a local
  ambiguity into the global automaton), it erodes the targeting that is the feature's measured value,
  and it would put `mergeStates` plus the `pending` drain under the global monitor on a path that is
  lock-free today — `absorbInto`, `writesAbove`, `peekChild`, `kindOf` and `budgetExhausted` take no
  lock, and no caller in `AccessTree.kt` holds one.
- **A rank on "stay inside this pot".** It would be dead code (§4.1).
- **The real subset construction.** It is the correct design and it is what "return a forked state"
  means. Its blast radius is the node identity: `AccessNode.anyId` would widen from a state to a
  position, taking `hash`, `equals`, the node invariant, `AccessTreeInterner`, every manager entry
  point and the ten production `union(anyId, …)` sites with it. Its measured reachable benefit on
  this arm is ≤ 2,325 absorbs — 0.08%. **It is gated on `telescopeStallAfterFork`, added now**: if
  that comes back in the hundreds the design has an evidence base; near zero closes the question.

---

## 5. (II.2) The performance arithmetic: node throughput is conserved

Nobody had differenced the counters over time. They are cumulative, and the two frontier arms differ
only in their IFDS budget, so treating the 300 s arm's totals as the state at t = 228 s gives a clean
late window. Same jar sha (`fbb37563342fdab6`), same flags, and the two runs' progress ladders track
each other to within 3% at the crossover.

Script: `scratchpad/anymgr/window-diff.py`. Arms: `scoped-runs/p2-bfs-1` (forward scan 228 s) and
`scoped-runs/long-bfs-1000` (forward scan 793 s).

```
window A   0 -> 228s    877,371 events    3,855 ev/s
window B  228 -> 793s   109,533 events      194 ev/s        events/s x19.9 slower

node touches (concat resultNodes + E-delta factNodes + fsw inNodes + getChildAny resultNodes)
  A    658,001,505  = 2.89 M/s
  B  1,437,865,812  = 2.54 M/s                              node touches/s x1.14 slower

                       per event A   per event B   growth
  concat calls                2.13          5.80     2.7x
  concat resultNodes        222.17       3572.38    16.1x
  graft points               33.50        632.62    18.9x
  E-delta calls               4.21          7.47     1.8x
  E-delta factNodes         373.56       8994.19    24.1x
  fsw inNodes               142.28        444.58     3.1x
  getChildAny calls           0.23          8.09    35.8x

  graft points PER CONCAT CALL     15.7 -> 109.1   (6.9x)
  result nodes PER CONCAT CALL    104.3 -> 616.1   (5.9x)
  concat calls with >=23 graft points   9.7% -> 45.0%
```

**Node-touch throughput is conserved to within 14% while event throughput collapses 20×.** The
product events/s × nodes/event is flat. The engine is not degrading; each event is 20× more expensive
because the facts it handles are 16–24× bigger.

Two consequences:

- **The earlier reading was an artefact.** "Per-event cost grows 222 → 594" compared *cumulative
  averages* across the two arms. Differenced properly it is 16–24×, and it accounts for the entire
  collapse rather than 2.7% of it.
- **The collapse is not a performance problem at all.** It is a direct observation of an ascending
  chain that has not converged after 13 minutes, and it is still ascending at the end.

The structural reason per-event cost is `Θ(accumulated tree)` and not `Θ(delta)`: every store returns
the **whole merged accumulator**, not the increment — `EdgeNonUniverseExclusionMergingStorage.add`
returns `AccessWithExclusion(mergedAccess, …)`, and `MethodTreeAccessPathSubscription.find` hands the
graft `storageFinalFacts[storageIdx]`. A later event does the same operations on a bigger object by
construction.

---

## 6. (II.1) The fixed point

### 6.1 The manager does not break it

The fact store is not a set of facts keyed by structural identity. It is **one merged tree per
storage slot**, and "already known" is `merged === stored` after a `mergeAdd` that *unions* the
arrival into the accumulator:

| store | the guard |
|---|---|
| F2F path edges | `MethodEdgesInitialToFinalTreeApSet.kt:99-101` `mergeAdd`, then `mergedAccess === currentAccess` |
| Z2F path edges | `MethodEdgesFinalTreeApSet.kt:32-34` |
| summary conclusions | `MergingTreeSummaryStorage.kt:23,29` `mergeAddDelta`, `delta == null` |
| caller subscriptions | `MethodTreeAccessPathSubscription.kt:77-83, 148-150, 298` |
| summary **premises** | `AccessBasedStorage.kt:21-34` — a trie of distinct keys, **no subsumption** |
| "unchanged" re-propagation | `MethodAnalyzer.kt:618` → `ObjectOpenHashSet<Edge>` — structural equality |

**And that guard is blind to the manager.** `mergeAddStep` performs
`manager.anyUnroll.union(this.anyId, other.anyId)` and then tests only `isAbstract`, `isFinal`,
`deepAccessorExclusion` and `mergedAccessors == null` before `return this`. A DSU union, a kind flip
or a rescore therefore **cannot make a re-derived fact look new**: re-deriving structure already
stored returns the receiver object and `add` returns null.

That disposes of the two hypotheses the question suggests:

- **Non-deterministic transformers → re-propagation.** The transformer *is* non-deterministic —
  `installAbove` keys on the current kind, and kinds are mutable. But the signature is wrong:
  re-propagation predicts **more events**, and events grew **12.5% for 3.4× the clock** while
  events/s fell 19.9× and per-event cost rose 16–24×. And the change count is tiny: the frontier arm
  reports `rescore=[n:6, visited:426, demote:94, promote:0]` — **94 transformer changes against
  986,904 events** — with `promote:0` meaning the PAID set only shrinks, which makes the rescore
  monotone and bounded (`O(log total)` fires per dag by the doubling threshold). **The rescore cannot
  be the driver, and it is not the default policy anyway.**
- **Interning keyed on mutable identity.** Confirmed as a fact — `equals` compares the stored `anyId`
  reference, never `find()`, so two nodes whose states have since been united stay unequal — but it
  buys work only through `enqueuedUnchangedEdges`, one re-enqueue per flip. The premise key,
  `AccessPath`, carries no `anyId` at all.

**The strongest control:** with the manager fully off (`L = -1`: no states, `anyId` always null,
`writesAbove` always true, `absorbTargetFor` always null) concat-created nodes are **131,623,220**
versus **138,410,824** at `L = 100` and 136,023,638 at `L = 0` — conserved to 5% while the operation
the budget governs (`unrollAnyAccessors` nodes into `added`) goes 2,681,364 → 1,397 → 0, and while
concat *calls* move 5,199,708 → 1,814,122 → 1,337,884 (`2026-08-25-why-the-budget-does-not-help.md`
§C, an earlier build). Every manager-side hypothesis is structurally inert at `L = -1`.
**The growth is not the manager's.**

### 6.2 What is actually missing: a bound on breadth, and a `⊑` test with a hole

The `[any]` subsumption operator **exists and works**. `trimAnyCoveredAndPushChildren` builds an
`AccessTreeAnySuffixMatcher` from one side's `[any]` subtree and deletes from the other every branch
that suffix language denotes, in **both directions**, at any depth. So `[any].X` does kill a stored
`a.[any].X` — on every path-edge, summary and subscription channel, which all merge with the default
`foldToAny = true`.

Three holes, in decreasing order of measured relevance:

1. **It is switched off on the accumulator that grows.** `foldToAny = false` appears at exactly two
   call sites in the module, `TreeInitialFactAbstraction.kt:307` and `:609`, and its `added` tree is
   the one measured at 40,262 nodes, 90% of whose distinct nodes own an `[any]`, `.[any]` its
   commonest accessor, out-degree 10.5 against 1.47. That is precisely the tree where an `[any]` and
   the concrete enumerations it denotes sit side by side.
2. **It cannot cancel `isAbstract`.** `AccessTreeAnySuffixMatcher.kt:151-155` computes
   `thisFinal = node.isFinal && !trie.isFinal` and has **no mirror for `isAbstract`** — `trie.isAbstract`
   is constructed and never read by `getNonMatchingNode`, and the rebuild passes `node.isAbstract`
   through. So `[any].*` does not subsume a sibling `f.*` whose node is abstract, though it denotes a
   superset. **Abstract nodes are exactly the graft points**, and graft points per concat call is the
   quantity that runs away 15.7 → 109.1.
3. **The premise trie has no subsumption at all.** Premises `p.a.b` and `p.[any]` coexist and both
   fire, which is why the store holds 54,169 premises that are concrete enumerations of what a
   wildcard denotes.

Holes 1 and 2 need no new theory: the ⊑ test exists and is already wired into the merge. Hole 1 is a
flag; hole 2 is a predicate completed. Both are **measured, not changed** here (§8) — enabling
`foldToAny` on the accumulator converts concrete premises into `[any]` premises, a direction with a
known trace-resolution cost, and completing the abstract predicate is a denotation change on every
storage channel.

### 6.3 And nothing bounds breadth

Depth has bounds — `SUBSEQUENT_ARRAY_ELEMENTS_LIMIT = 2`, `limitFieldAccess`, the `[any]` round trip
(§4.2). Breadth does not. Every breadth-reducing operator in the module:

| operator | effect |
|---|---|
| `trimAnyCoveredAndPushChildren` | **the only real reducer** — and see the three holes above |
| `MergingTreeSummaryStorage.compressNode` | fires only above 10,000 nodes, removes accessor chains in SCCs; a heuristic, not a ⊑ test |
| `installAbove` | removes a level of **depth**, never a child |
| `absorbCoveredByAnyPrefix` | removes one child and **adds** the consumed node's children |
| `limitFieldAccess` | hoists occurrences of a field to the root — **increases** root breadth |
| the type filter | accepts everything past a `java.lang.Object` edge |

And the depth limit that does exist is a **scheduling delay, not a bound**: `factDepthLimit` starts at
3 and `resumeDelayedAnalyzers` does `++factLimit` with **no ceiling**, posted exactly when the unit
would otherwise go idle. The bound is raised precisely when it binds. There is no widening operator
anywhere in the engine.

**Verdict: the manager does not violate the fixed-point guarantee. The lattice has no finite-height
argument once `[any]` is in play, because nothing bounds children per node, and the one operator that
would supply the bound is switched off where it is needed and incomplete where it runs.**

### 6.4 One thing that is not fixed-point but should be recorded

The pre-existing interner data race is present on this branch and reaches the manager's hottest path.
`ConcurrentReadSafeInt2ObjectMap` and `MapUtils.forEachEntry` still carry the broken shape, and that
map is `AnyUnrollState.children` and `.parents`. The lock-free readers are `readChild`'s fast path
(99.9% of all reads), `readChildPaidOnly`, `peekChild` and `absorbInto`. Soundness holds — the
forward re-check turns a torn read into a MISS, which declines to absorb, the sound direction — but
**determinism does not**, which is the standing explanation for volume counters spanning 5× across
replicates of the same jar and arm. The fix is on `saloed/8-interner-race` and is not in this branch.

---

## 7. The measurement

`scoped-runs/rev-bfs-1`, jar `review2-eccccc09cf52d6a5`, same arm and flags as `p2-bfs-1`.
rc 254, forward scan 3m53s, **901,084 events** (vs 877,371), **SARIF 2**, `lowmem_stop=0`,
`foreign_overlap_pct=0`. Throughput and findings are unchanged, which is what the selector change
predicted.

### 7.1 The graft, anatomised — 88% of graft points are a re-visit

```
C-graft points=30,313,433 max=3,746 pointsPerCall=15.93
C-graft revisited=26,607,585  nested=14,393,618
        revisitedShare=87.77%  nestedShare=47.48%  deltaRootCarriesAny=122,522
```

**87.8% of graft points offer the delta to a receiver node that was already grafted in the same
call.** That is the ceiling on a receiver-side memo, and it is the largest single number this
investigation has produced. It follows from the sampled shape — 8.0 distinct receiver nodes, 2.1 of
them abstract, against 15.9 graft points — and from `manager.abstractNode` being a process-wide
singleton, so every `*` leaf of a receiver is one object visited many times.

**47.5% of graft points sit strictly below another**, so nesting is real as well; the two populations
overlap and the memo subsumes most of the nesting.

`deltaRootCarriesAny = 122,522` against `concatAnyDelta = 164,283`: **74.6% of deltas that contain an
`[any]` carry it at the root**, so the root predicate — which every fold of the receiver's spine into
the delta's `[any]` needs, and which nothing had measured — is available three times in four. Both my
earlier guess (that the two predicates barely differ) and the counter-guess from rendered samples
(that the `[any]` sits deep behind a concrete spine) were wrong in the same direction: it is a
majority, not all and not few.

### 7.2 The two `⊑` holes: one refuted, one enormous

```
J-trimCF      tifaCalls=6,587 noAny=906,779 inNodes=63,631 keptNodes=62,316
              wouldDropAll=168 keptFraction=0.98
J-abstractHole keptForAbstract=2,226,846,361 nodesKept=2,226,846,361
```

**Hole 1 — `foldToAny = false` on the initial-fact accumulator — is refuted as a lever.** In 906,779
of 913,366 arrivals (99.3%) the accumulator has no root `[any]` for the trim to work from, and where
it does the trim would keep **98%** of the arrival and drop the whole thing 168 times. The switched-off
subsumption is not what lets that tree grow. (Root-level probe, so a lower bound — but a keptFraction
of 0.98 leaves little room.)

**Hole 2 — the trim never cancelling `isAbstract` — fires 2,226,846,361 times.** `nodesKept` equals
`keptForAbstract` exactly, so every branch kept this way is a **single node**: a bare `*` leaf that
the `[any]`'s own abstract position already denotes. It is therefore a **breadth** opportunity, not a
mass one — each occurrence is one accessor edge that could have been removed from its parent — and
breadth is the dimension §6.3 shows nothing bounds. Deleting such a branch is **exact**, not even a
coarsening: `f.*` ⊆ `[any].*` for covered `f`.

**Correction, from §7.7: 2.2 billion is the number of VISITS, and 99.9% of them are re-visits.** With
the walk memoised the same counter reads **2,121,017–2,441,266** — a factor of a thousand lower. The
hole's real size is about two million distinct occurrences per run. It is still the largest
breadth-reducing opportunity found, but the headline figure was measuring the missing memo, not the
missing predicate. Both readings are in this document because the second one only exists because the
first one was taken.

### 7.3 The telescope, re-measured after separating the null position

```
                            p2-bfs-1 (before)   rev-bfs-1 (after)
telescopeNoPosition                 —             486,024
telescopeStalls                 581,726               7,853
telescopeStallsAfterStep         10,081               7,818
  → share of stalls after a step     1.7%              99.6%
telescopeStallAfterFork             —                   630
```

**The earlier reading inverts.** Once the probes that had no `[any]` position are counted separately,
genuine stalls fall by 74× and **99.6% of them happen after at least one backward step** — the exact
population the earlier document concluded was 1.7% and therefore not worth rescuing. So the shape of
the evidence was wrong.

The conclusion still holds, on a number that now measures the right thing: **`telescopeStallAfterFork`
= 630.** A fold that had a genuine choice one step back and then dead-ended happens 630 times in a run
of 901,084 events. That is the entire opportunity of the subset construction — against an edit that
would widen `AccessNode.anyId` and take `hash`, `equals`, the interner and every manager entry point
with it. **The question is closed on evidence rather than on an artefact.**

### 7.4 The ranked selector

Two replicates, `rev-bfs-1` and `rev-bfs-2`. **The fork counters are wildly unstable across
replicates of the same jar and arm** — the interner race of §6.4 — so they are quoted as ranges and
nothing is concluded from a single value.

```
                     rev-bfs-1     rev-bfs-2     (p2-bfs-1, old selector)
fork hits               17,957         2,643                      2,325
selfLoopAvailable       17,755         2,454                          —
choiceChanged           14,682         1,944                          —
kindSplit                  365         1,952                          —
absorbStay              91,291            39                        549
absorbExact          2,827,678     3,318,132                  2,834,964
absorptions          2,918,969     3,318,171                  2,835,513
pointsPerCall            15.93         16.89                      15.72
events                 901,084       905,190                    877,371
```

What survives the variance:

- **A self-loop was on offer in 92.8–98.9% of forks**, and the old min-id pick walked away from it in
  **73.6–81.8%** (`choiceChanged`). The arbitrariness the question names was real and frequent, in
  both replicates.
- **`kindSplit` is 2.0–73.9% of forks** — the one counter whose two readings disagree qualitatively,
  so the "in 98% of forks the pick is invisible downstream" claim from `rev-bfs-1` **does not hold**
  and is withdrawn. §4.1's argument stands on the structural proof, not on this number.
- `absorptions` moves +2.9% / +17.0% and `pointsPerCall` 15.72 → 15.93 / 16.89. The selector changes
  *where* a fork lands, not *whether* it absorbs.
- `absorbStay` is 39–91,291. Even the low replicate is not evidence against the change; the high one
  is not evidence for it. This counter is not usable at this variance.

**Findings unchanged in both**: `Total vulnerabilities: 2`, SARIF 2, rc 254, forward scan 3m53s.

**Lemma 9.2 now has a real witness.** Wired naively it read 454; once the self-loop pick is excluded
— the rank prefers one deliberately, so landing off the threaded predecessor is the selector working —
it reads **`disagrees:1` with `selfLoopPreferred:1406`**. So the identity the design asserts holds in
production, on a counter that can now fail.

### 7.5 The profile: one function is 73.6% of late CPU

`scoped-runs/jfrdeep`, jar `frontier-fbb37563342fdab6` (the pre-change build, so this profiles the
frontier arm as it stood), `IFDS_TIMEOUT=420`, JFR with a custom `.jfc` (10 ms execution samples,
600/s allocation samples, **1 ms** monitor thresholds so nothing is thresholded away), plus 66
independent `jcmd Thread.print` snapshots. rc 254, 942,738 events, SARIF 2 — JFR did not distort the
arm (it processed slightly *more* events at equal wall time than the diag arms).

**Containing-frame share, early (scan 0–60 s, n=3,440) vs late (208.5–328.5 s, n=7,980):**

| late % | early % | frame |
|---|---|---|
| **73.62** | **1.74** | `AccessNode.trimAnyCoveredAndPushChildren` |
| **71.33** | **0.00** | `AccessTreeAnySuffixMatcher.getNonMatchingNode` (0 of 3,440 samples) |
| 49.36 | 6.42 | `AccessNode.mergeAdd` |
| 28.17 | 1.10 | `AccessorInterner`, via `coveredByAny()` |
| 7.17 | 5.64 | `concatToLeafAbstractNodes` |
| **0.83** | 9.07 | `AccessTreeInterner` — *falls 11×* |
| **0.51** | 10.20 | any `hashCode` — *falls 20×* |
| ~0.4 | ~0.15 | `AnyUnrollManager` |

The ramp is the plateau: `getNonMatchingNode`'s inclusive share over eight disjoint windows runs
`0 → 0 → 0 → 7.0 → 39.0 → 74.2 → 73.4 → 70.4%`. **The throughput collapse and the saturation of this
one function are the same event.**

**Allocation.** Late, 83.5% of all heap allocation is two lines —
`AccessTreeAnySuffixMatcher.kt:146` and `:147` — 254 GB of `Object[]` plus **24.9 GB of boxed
`Integer`** in 120 s. Those are `mutableListOf<AccessorIdx>()` and `mutableListOf<AccessNode>()`: an
`ArrayList<Int>` boxes every accessor index, and both grow from the default capacity on a walk that
visits every node. Allocation rate 1.07 → **2.79 GB/s**, from a single mutator thread.

**Three candidates refuted, with numbers:**

- **Lock contention.** **Zero** `jdk.JavaMonitorEnter` events at a 1 ms threshold in the entire 120 s
  late window; 0.273 s total early, none of it the manager. `AnyUnrollManager`'s global lock appears
  in **0** blocking stacks in either window, and `jcmd` sampling shows **0 of 190** worker
  observations BLOCKED. The manager's lock is exonerated outright.
- **Hashing and interning of large structures.** Interner cost *falls*, 9.07% → 0.83%.
- **GC.** 919 pauses / 6.80 s over the 328.5 s scan = **2.07%**, confirming the earlier figure. What
  does cost is not pause but **1.86 cores of G1 concurrent refinement** servicing 2.79 GB/s — more
  CPU than the analysis itself uses.

**And one thing nobody had looked at: the solver runs on about one core of twenty.** 1.16 of 10 IFDS
workers RUNNABLE late (0.90 of 20 machine cores), all the rest parked on an empty queue. It is
structural — the pool is `availableProcessors()/2` and parallelism is bounded by the number of
simultaneously live *analysis units*, not by events, and `queued` sits at 1–11 all run. **It is not
the collapse**: perfect 10× parallelism turns 289 ev/s into 2,890, still 12× below the 31,058 ev/s
start, and per-event work keeps growing. Worth knowing; not the lever.

**The superlinearity test.** Normalising by events in each window:

| per IFDS event | early | late | growth |
|---|---|---|---|
| mutator CPU | 120 µs | 3,190 µs | 26.6× |
| heap allocated | 110 KB | 9.64 MB | 87.6× |
| `AccessNodeMergePair` allocated (∝ fact size) | 4,853 B | 100,576 B | **20.7×** |
| **trim CPU** | 2.1 µs | 2,348 µs | **≈1,120×** |
| everything-but-trim CPU | 118 µs | 841 µs | **7.1×** |

So **§5's "node throughput is conserved" holds for everything except this one function**: the rest of
the engine grew 7–15× against a 20.7× growth in data, i.e. linear or better. The trim grew ~1,120×
against 20.7× — **≈54× more cost per merge pair**. That is the superlinear exception, and it is the
collapse.

**The mechanism, in source.** `mergeNodeLoop` is a work-list over merge *pairs*; for each pair popped
for the first time, `foldToAny` (the default) calls `trimAnyCoveredAndPushChildren`
(`AccessTree.kt:1899`), which whenever either side owns an `[any]` runs a **full recursive walk of
the other side's entire subtree** (`:1948`, `:1957`). `getNonMatchingNode` has **no memo**: a fact is
a DAG, so a shared subtree is re-derived once per path that reaches it. Composition is
`O(merge pairs) × O(subtree per pair)` — quadratic in the fact tree — executed on every `mergeAdd`
on every storage channel. Early it short-circuits (no `[any]` edge, return unchanged); late nearly
every merge node owns an `[any]`, so nearly every pair pays.

**This reframes §6 rather than contradicting it.** The chain being unbounded is why the trees grow;
the trim being quadratic in the trees is why growth converts into a 20× throughput collapse instead
of a 20× slowdown.

### 7.6 Completing the abstract cancellation: measured, mixed, not shipped

`-Dopentaint.anyTrimAbstract=true` (added, default **off**) makes the trim cancel `isAbstract` the way
it already cancels `isFinal`. Deleting such a branch is exact — `f.*` ⊆ `[any].*` for covered `f`.

| | control (`rev-bfs-2`) | `rev-trimabs` |
|---|---|---|
| events | 905,190 | **1,072,494** (+18.5%) |
| `Total vulnerabilities` | 2 | **2** |
| SARIF | 2 | **0** — traces time out (`Filter out 2 vulnerabilities without traces`) |
| concat calls | 1,936,648 | 3,010,315 (+55%) |
| concat resultNodes | 211,234,584 | 410,027,195 (+94%) |
| **pointsPerCall** | 16.89 | **50.57** (3.0×) |
| revisitedShare | 88.10% | 94.50% |
| `writtenPaid` | 13,167,024 | **129,551,881** (9.8×) |
| `J-abstractHole` occurrences | 2,143,815,407 | 309,153,134 (7× fewer) |
| `J-trimCF keptFraction` | 0.97 | **0.19** |

**It does not converge and it is not a clean win.** More events get processed, and the branches the
hole was keeping do fall 7×, but the receiver trees grow 4.3× and the graft multiplier triples. The
one genuinely new fact is the last row: **with the abstract cancellation on, the trim the initial-fact
accumulator switches off would drop 81% of each arrival** (`keptFraction` 0.97 → 0.19,
`wouldDropAll` 164 → 37,482). **The two `⊑` holes interact** — hole 1 is inert only *because* hole 2
is open. That is worth knowing before either is judged again, and it is not something either
measurement alone could have shown.

Left off by default: it changes the denotation of an operator every storage channel's merge runs, and
its effects are mixed.

### 7.7 The memo: 1.4–1.8× throughput, and the failure mode changes

The profile's own recommendation, implemented: memoise `getNonMatchingNode` on
`(trie, node, prefixCoveredByAny)` for the duration of one walk, and replace the two `mutableListOf`
accumulators with a presized `IntArrayList` (no boxing) and a presized `ArrayList`. The walk is a pure
function of those three arguments, so the memo is **denotation-neutral** — it changes what the engine
*does*, never what it *computes*.

```
                8 GB                                       16 GB
          control        memo-1      memo-2         control        memo
rc          254           253         253             254           253
lowmem        0             1           1               0             1
scan     233.3 s       147.4 s     124.8 s         233.5 s       179.7 s
events   905,190       931,694     868,802         754,386       810,947
ev/s       3,880         6,320       6,961           3,231         4,513
Total vulns    2             2           2               2             2
SARIF          2             2           2               2             2
J-trimMemo hitRate  —      80.62%      79.26%           —          81.59%
J-abstractHole  2.14e9    2.12e6      2.44e6          2.65e9      1.14e7
```

**The memo hit rate is 79–82%.** Four of every five visits in the `[any]`-trim walk were re-deriving
a shared subtree the walk had already answered for. That is the DAG re-visit hypothesis, confirmed
directly, and it is the same shape as the 87.8% graft re-visit in §7.1: **this engine's dominant cost
is walking a DAG as if it were a tree.**

**Throughput rises 1.63–1.79× at 8 GB and 1.40× at 16 GB**, with `Total vulnerabilities` and SARIF
unchanged in every arm.

**And the failure mode changes from timeout to memory.** Every memoised arm ends on the low-memory
stop — the first time any manager-on arm has done so — at 8 GB *and* at 16 GB. Doubling the heap
moved the wall from 125–147 s to 180 s; it did not remove it. Nothing leaks: the memo is per-walk and
transient, the peak RSS matches the control's at the same `Xmx`, and the stop is graceful (no
`OutOfMemoryError`, findings intact). The run simply reaches bigger facts sooner.

**Which is the whole thesis in one experiment.** Removing 73.6% of the CPU cost buys 1.4–1.8× of the
curve and moves the wall a minute to the right. A constant-factor lever cannot end a run whose cost
per event grows without bound — and the fact that the biggest constant factor yet found behaves
exactly like all the smaller ones is the strongest evidence for §6's conclusion that the missing piece
is a bound on breadth, not a faster engine.

Note also that the 16 GB *control* is **slower** than the 8 GB control (3,231 vs 3,880 ev/s): more
heap means more live facts means more work per event. More memory is not a lever either.

---

## 8. What changed in the code

Two behaviour changes, both small; everything else is instrumentation. All counters sit behind the
existing `-Dopentaint.anyManagerDiag=true` / `-Dopentaint.apOpDiag=true` flags, which default off.

### Behaviour

**`AnyUnroll.absorbInto` — ranked selection instead of greedy min-id.** A self-loop, when one is a
candidate, now wins over any other predecessor; min-id remains the tie-break. The forward re-check
stays ahead of the ranking, so a predecessor inside the `mergeStates` drain window can never outrank
a real one. `absorbInto` stays lock-free. This changes only *where* a fork lands, never *whether* it
absorbs, so `absorptions` is unaffected by construction.

A rank on "prefer a predecessor in the same component" was written and then removed: it would be dead
code, because a state's dag is its reachability component and every candidate is already inside it
(§4.1). That is worth more than the rank was — it is the structural reason the pick cannot do the
harm the design attributed to it.

**`AccessTree.filterStartsWithImpl`'s telescope probe — the null position is no longer a stall.** A
descent that ended on a node carrying no `[any]` used to enter the loop, get `null` at once and be
recorded as a first-link stall. It is counted as `telescopeNoPosition` now.

**`AccessTreeAnySuffixMatcher.getNonMatchingNode` — memoised, and its two accumulators unboxed.** A
per-walk `(trie, node, prefixCoveredByAny)` memo on identity keys, plus a presized `IntArrayList` in
place of an `ArrayList<Int>` that boxed every accessor index. The walk is a pure function of those
three arguments, so this is **denotation-neutral**: 1.4–1.8× throughput, findings byte-identical,
79–82% memo hit rate. **It changes the failure mode on conductor from timeout to the low-memory stop**
(§7.7) — the one change here worth revisiting if a timeout is preferable to a graceful memory stop.

**`-Dopentaint.anyTrimAbstract=true`, default off.** Completes the trim's abstract cancellation to
mirror its `isFinal` cancellation. Measured (§7.6) and left off: mixed effects, denotation change.

### Instrumentation

| counter | where | question it answers |
|---|---|---|
| `witnessDisagreesWithThreadedState` | wired at last, in the telescope probe | Lemma 9.2 in production. **It was declared, reported, and never incremented** — every reading of its zero was vacuous |
| `telescopeNoPosition` | the same probe | how much of `telescopeStalls` was "there was nothing here". Predicted to take it from 581,726 to ≈172,000 |
| `telescopeStallAfterFork` | the same probe | the only population a subset construction rescues. **This is the gate on §5.8** |
| `absorbForkChoiceChanged` | `absorbInto` | how often the ranked selector lands somewhere min-id would not |
| `absorbForkKindSplit` | `absorbInto` | whether a fork's candidates disagree on kind — the only thing the pick can move |
| `absorbForkSelfLoopPreferred` | `absorbInto` | how often "absorb and stay" was on offer |
| `graftPointsRevisited` | `concatToLeafAbstractNodes` | graft points whose receiver node was already grafted **in this call** — the ceiling on a receiver-side memo |
| `graftPointsNested` | the same | graft points strictly below another — the population a subsumption rule could skip |
| `concatDeltaRootCarriesAny` | the concat entry | the ROOT `[any]` predicate, which every fold of the receiver's spine needs and which nothing measured |
| `tifaTrim*` (`J-trimCF`) | `TreeInitialFactAbstraction.addInitialFact` | what the disabled `[any]` trim would delete from the accumulator that grows. Root-level, so a **lower bound** |
| `trimKeptForAbstract` (`J-abstractHole`) | `AccessTreeAnySuffixMatcher` | branches the ⊑ test kept only because the node was abstract |
| `trimMemoHits` / `trimMemoMisses` (`J-trimMemo`) | the same | how much of the trim walk was re-deriving a shared subtree — 79–82% |

Two new unit tests pin the change: a self-loop beating a lower-id predecessor, and the structural
claim that every member of a fork shares the target's pot.

**Gate**: 3,480 tests, 3,447 passed, 31 skipped. The only 2 failures are the pre-existing
`JIRFactTypeCheckerUnrollFilterTest` pair, verified pre-existing at the base commit in an earlier
session. Both new tests pass.

---

## 9. What this leaves, ranked

1. **The DAG re-visit, in the two places it dominates.** 79–82% of the `[any]`-trim walk and **87.8%**
   of concat's graft points are re-derivations of a node already handled in the same call. The trim
   half is done and worth 1.4–1.8×. **The concat half is not done**: a per-call memo on
   `(receiver node, delta node, subsequentArrayElementLimit, parentEdgeIsAny, type-filter object)` is
   the same shape of fix against the same shape of waste, and `revisitedShare` sizes it at 88%. Note
   it will not move `resultNodes`, which counts with multiplicity and is therefore invariant under
   sharing — which is probably why every earlier lever looked like it "relocated work at unchanged
   mass".
2. **A bound on breadth.** Nothing bounds children per node, the one operator that would is switched
   off on the accumulator that grows and incomplete where it runs, and the depth limit is raised
   exactly when it binds. This is the only thing measured here that could make the run *converge*
   rather than get further before stopping. §6.
3. **The two `⊑` holes, now known to interact.** Hole 1 is inert at 0.97 kept-fraction only because
   hole 2 is open; close hole 2 and the same probe reads 0.19. Neither should be judged alone again.
   §7.6.
4. **The solver's parallelism.** 1.16 of 10 workers RUNNABLE late, bounded by simultaneously-live
   analysis units rather than by events. Worth at most 10× and it is not the collapse, but it is
   free-standing and nothing else in this investigation touches it. §7.5.
5. **Not worth building**: the subset construction (`telescopeStallAfterFork` = 630–1,697 per run),
   opening the absorption kind gate (+14.5% ceiling, 78.5% of the opportunity is a self-loop that
   rewrites nothing), and more heap (the 16 GB control is *slower* than the 8 GB one).

---

## 10. Readings this document corrects

| claim | where it was made | what is actually true |
|---|---|---|
| `witnessDisagreesWithThreadedState=0` shows "Lemma 9.2 holds in production, where no test reaches" | `2026-08-25-any-unroll-absorbing-prepend-results.md` §3; `absorbing-prepend-outcome` memory | The counter was **never incremented**. The zero was guaranteed by construction and said nothing — the exact failure mode the design warns about for `tifaAbsorbSuppressed`. Wired now |
| "97–98% of telescope stalls happen on the FIRST link, where the position is a single state" — therefore the subset construction cannot help | `…-absorbing-prepend-results.md` §5; `absorbing-prepend-outcome` memory | The **conclusion holds**; the evidence does not. `telescopeStalls` counted probes with no `[any]` position at all: `filterStartsWith calls − telescopeStalls = 172,316` against `163,923` `[any]` reads. The share was inflated by construction; the absolute after-step count is the number that should have been quoted. The conclusion survives independently: 2,325 forks against ~14.2M backward queries |
| "concat result nodes per event 222–241 → 594, i.e. per-event cost grows 2.7×" | `conductor-throughput-collapse` memory; `…-at-L100.md` §17 | An artefact of comparing **cumulative averages** across two arms. Differenced over windows it is **16–24×**, which accounts for the whole 20× collapse instead of 3% of it |
| A greedy predecessor pick "can move a fact's `[any]` into the automaton of an unrelated program location" | `2026-08-25-any-unroll-absorbing-prepend-design.md` §5.8(a) | True of the automaton, **false of the pot**. A state's dag is its reachability component, so every candidate already shares the target's pot. The pick cannot change `budgetExhausted`, the charge, or which origin pays |
| The largest untested levers are the depth-1 type filter and the `ClassStatic` broadcast | `…-at-L100.md` §18 | Still worth testing, but they are no longer the largest. The receiver-side memo (`pointsPerCall` 15.7 with 2.1 distinct abstract nodes) and the two `⊑` holes (`foldToAny = false` on the accumulator; the matcher not cancelling `isAbstract`) are bigger and are now instrumented |
| The absorption in `this.concat(delta)` folds the delta's prefix into the receiver's `[any]` | implicit in the design's framing of the graft | That direction exists but is **60 of 29,388,226 graft points** here. The direction that carries 99.9% of absorptions is the mirror one, `absorbBeyondAnyEntries`, and it needs the manager enabled — which the shipped default is not |

---

## 11. Caveats

- **The window differential is a cross-run subtraction.** The two arms are separate runs of the same
  jar with the same flags; the late window uses the 300 s arm's totals as the state at t = 228 s.
  Their progress ladders track within 3% at the crossover, but they are not the same process.
- **The APOP counters cover the whole run**, prescan and trace resolution included, not the forward
  scan alone. The trace phases are comparable (~50 s vs ~58 s) so they largely cancel in the
  subtraction, but the windows are not exactly the forward scan.
- **Volume counters span up to 5× across replicates** of the same jar and arm — the interner race in
  §6.4 is the standing explanation. Only structural ratios (points per call, distinct vs multiplicity)
  are stable enough to argue from.
- **The `J-trimCF` probe is root-level**, so it is a lower bound on what the trim would remove: the
  real merge trims recursively at every pair.
- **`graftSeen` assumes one concat per thread at a time**, the same assumption `graftPointCounter`
  already makes. A re-entrant concat would under-count re-visits.
- **The closure theorem (§4.2) assumes a stable automaton.** Unions change the selector; they are
  finite and rare here (209 against 2.8M absorbs) but the theorem is about a quiescent automaton.
- **Forks were measured on this arm.** An earlier `L = 8` arm recorded 92,039 fork hits with width up
  to 10, against 2,325 and width 4 here. The conclusion is arm-specific; the soundness argument is not.
- **The two `⊑` holes were measured, not fixed.** Enabling `foldToAny` on the initial-fact accumulator
  converts concrete premises into `[any]` premises — a direction with a measured trace-resolution
  cost — and completing the matcher's abstract predicate is a denotation change on every storage
  channel. Neither is a free win and neither should ship on a code reading.
- **`absorbCoveredByAnyPrefix` has no §4.3 subtree GUARD** where `absorbBeyondAnyEntries` does. It is
  60 sites on this workload so it is not urgent, but it is untested territory rather than a checked
  path.
- **Nothing here changes the finding count.** Every arm that reaches the sink still reports
  `Total vulnerabilities: 2`; SARIF counts vary only with trace-resolution time.
- **The fork counters are not usable at this variance.** Two replicates of the same jar and arm gave
  2,643 and 17,957 fork hits, 39 and 91,291 `absorbStay`, and `kindSplit` at 2.0% and 73.9%. Anything
  argued from a single reading of them is worthless; §4.1's conclusion rests on the structural proof.
- **The profile is one arm, without diagnostic flags, and JFR's execution sampler under-samples.**
  Sample *rate* stayed flat (~55–70/s) while mutator CPU fell 3×, so absolute sample counts must not
  be read as parallelism — the CPU figures come from `ThreadCPULoad` and `jcmd` per-thread differencing
  instead. Within-window shares should be unbiased but that was not proved.
- **`getNonMatchingNode` was 0 of 3,440 early samples**, so "0.00% → 71.33%" is really
  "<0.09% → 71.33%" at 95%.
- **The memo's effect on the failure mode is a trade, not a free win.** It is denotation-neutral and
  findings are identical, but conductor now stops on memory rather than the clock at both 8 and 16 GB.
- **The 16 GB arms were run once each.** The control being slower than at 8 GB is a single
  observation, consistent with the mechanism but not replicated.


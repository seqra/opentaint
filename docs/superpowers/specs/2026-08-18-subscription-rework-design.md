# Subscription mechanism rework — design proposal

> **C2 was implemented and measured. It is correct but delivers no speed-up — see §0.**

## 0. Measured result of C2 (`emptyDeltaRequired` in the tree storage)

Implemented as six lines in `SummaryEdgeFactAbstractTreeSubscriptionStorage.find`, gating each row on
`callerExitAp.contains(summaryInitialFact)`.

**Correctness: confirmed.** 3,343 tests; the only two failures are a pre-existing untracked
characterization test unrelated to subscriptions. A per-test A/B over 1,786 tests (change stashed vs
applied) showed **zero** differences. Tree and Automata stay in lock-step on the two suites that run
both, and the Go late-arrival tests (`mutualRecursion`, `recursive`, `deepCall`) all pass.

**Performance: no effect.** Eight alternating repeats per side, isolated, ThingsBoard / `ssrf`:

| | baseline `4888917f0` | fix |
|---|---:|---:|
| runs | 8 | 8 |
| outcome | 8/8 `analyzer_timeout` | 8/8 `analyzer_timeout` |
| mean wall | 282.4 s | 286.2 s |
| median wall | 279.0 s | 279.5 s |
| processed events (run 1) | 5,083,935 | 4,488,104 |
| top `pass:` (run 1) | 1,055,248 | 1,043,520 |

Every run on both sides times out. The median difference is 0.18% — noise. The fix processed ~12%
*fewer* events in the same wall time while `pass:` moved ~1%, i.e. throughput got slightly worse.

**Why, most likely.** The predicate is expensive on this representation.
`AccessNode.contains` walks with `getChild` (`AccessTree.kt:415-433`), which merges the ANY branch and,
when `isCoveredByAny(accessor)` holds, also does `clearChild` + `addParentIfPossible` + a second
`mergeAddMaybeNull` — up to two `mergeAdd` calls per accessor step. So `contains` is
O(|path| x merge), not O(|path|). And `isCoveredByAny` is `anyAccessorUnrollStrategy.unrollAccessor`
(`TreeApManager.kt:50-51`), which commit `0e394952a` made unconditionally true for every
`FieldAccessor` — so the expensive branch fires on every step. The automata backend can afford this
filter because `containsAllAccessPaths` is O(|E|) hash lookups; the tree backend cannot.

This is a hypothesis consistent with the numbers, not a measured attribution. It would be settled by
profiling `contains` under the fix, or by the cheaper variant below.

**The index variant was tried and rejected.** The `AccessTreeIndex` was extended with two BitSets per
node — `abstractIndex` (structurally abstract at this prefix) and `anyOnPathIndex` (an any-accessor at
or above it) — so that most rows could be decided without `contains`. Result over 6 alternating
repeats per side: baseline median 278.7 s, fix median 279.5 s, **12/12 `analyzer_timeout`**, throughput
+0.0% (median events/s 21,050 vs 21,053). Baseline-side throughput alone spans 4.69 M-6.40 M events
across its own six runs, roughly 40x the median difference — the change is invisible against variance.

Worse, review falsified the soundness argument in two places, both dropping rows the plain `contains`
version keeps:

1. **FINAL-terminated requirements are unconditionally rejected.** `AccessTreeIndexImpl.add` sets
   `index` and `anyOnPathIndex` on the synthetic `FINAL_ACCESSOR_IDX` child but never `abstractIndex`,
   while `contains` short-circuits on FINAL with `return node.isFinal` — true for exactly the rows
   whose `index` bit was set. With >=10 rows every matching row is dropped.
2. **`anyOnPathIndex` under-approximates on the incremental path, so the answer depends on GC.**
   `AccessTreeIndex.add` feeds only the *delta* tree while `rebuildIndex` walks the *merged* tree.
   `abstractIndex` accumulates correctly under OR; `anyOnPath` does not. If one delta carries the
   any-accessor and a later delta supplies the literal child below it, neither walk records the
   combination — yet the merged tree has both, so `contains` could accept. Clearing the
   `SoftReference` and rebuilding flips the answer.

Both changes have been reverted. The minimal `contains` version is retained.

**Why neither version helped — the premise was wrong.** C2 was justified as removing wasted fan-out,
and the fan-out *is* wasted: the receiver discards rows with a non-empty delta. But it discards them
via an early return — `handleMethodSideEffectRequirement` computes `emptyDeltaExclusionRefinementOrNull`
per requirement and returns immediately when none survive (`MethodAnalyzer.kt:838-841`). The pruned
rows therefore cost an early return, not real work. The expensive work — `registerNewInitialFact` ->
`TreeInitialFactAbstraction.addAbstractInitialFact` -> `createNodeFromReversedAp`, which JFR put at
62-71% of stall-window CPU — happens only for rows that *pass* the filter, and pruning does not reduce
those. Filtering the subscription cannot move a cost that lives past the filter.

This also lowers the expected value of C1 (batching the per-requirement traversals): the throughput
data shows the traversal itself is not where the time goes.

**Status of the change:** correct, regression-free, and retained as a semantic fix (it makes the tree
backend honour a flag it was ignoring, matching automata). It is not a performance fix.

---

Status: proposal. C2 implemented and measured; C1, C3, C4 not implemented.
Criterion, as set: **maximum profit for minimal code change.**
Target: the ThingsBoard/SSRF full-scan stall on `saloed/5-default-get` (`4888917f`).
Supporting analysis: `issue-explore.md`.

## 1. What the evidence says the bottleneck is

From the diagnostic run's active-event snapshots (10 s cadence over the full scan):

- **25 of 26 sampled active events are `NewSideEffectRequirementEvent`**; exactly one is a
  `NewSummaryEdgeEvent`.
- The two large requirement events carry **`requirements=8687`** and **`requirements=8761`**. The 8,687
  one appears in five consecutive snapshots, i.e. **one event held a worker for >42 seconds**.
- The single summary event carries `batch=23487` but reports **`summaries=1 subscriptions=1 fanout=1`**.

That last number matters: for that batch the subscription fan-out was *one*. The cross-product
blow-up (callee premises x caller rows) is therefore **not** what this run is doing, at least in that
sample. The workers are sitting on the side-effect-requirement path.

Corroborating, from thread dumps taken during the stall:
`NewSideEffectRequirementEvent.processMethodSummary -> handleMethodSideEffectRequirement ->
registerNewInitialFact -> TreeInitialFactAbstraction.addAbstractInitialFact`.

Caveat kept in view: active-event snapshots are time-weighted samples, not a census, and `fanout=1` is
one observation. The 25:1 population split is the robust part.

## 2. Two defects compound on exactly that path

### D1 — the requirement path is the only notification path that does not group

Every sibling groups before scanning. `processMethodFactSummary` (`SummaryEdgeSubscription.kt:546-559`):

```kotlin
val sameInitialFactEdges = summaryEdges.groupBy { it.initialFactAp }
for ((summaryInitialFact, summaries) in sameInitialFactEdges) { applySummaries(...) }
```

`NewSideEffectRequirementEvent.processMethodSummary` (`:629-643`) does not:

```kotlin
sideEffectRequirements.forEach { sideEffectRequirement ->
    methodSubscriptions.findFactEdgeSub(sideEffectRequirement, emptyDeltaRequired = true).forEach { (ep, subscriptions) ->
        val analyzer = processingCtx.getMethodAnalyzer(ep)
        for (subscription in subscriptions) {
            analyzer.handleMethodSideEffectRequirement(
                subscription.callerPathEdge, subscription.calleeInitialFactBase,
                listOf(sideEffectRequirement)          // delivered one at a time
            )
        }
    }
}
```

`findFactEdgeSub` is a full traversal of every caller entry point x call statement x caller exit base
(`:325-338` -> `CommonAPSub.kt:53-64`, `:116-128`). So an 8,687-requirement event performs **8,687 full
subscriber traversals**.

### D2 — `emptyDeltaRequired` is ignored in tree mode, so each of those traversals returns everything

`SummaryEdgeFactAbstractTreeSubscriptionStorage.find` (`MethodTreeAccessPathSubscription.kt:166-186`)
declares `emptyDeltaRequired` at `:169` and never reads it. When the requirement premise has no
accessors it takes:

```kotlin
if (summaryInitialFact == null) {
    storageInitialFacts.forEachIndexed { index, callerInitialAp ->
        dst.add(storageFinalFacts[index], callerInitialAp)     // every row, unpruned
    }
}
```

Automata implements the flag properly (`MethodAutomataAccessPathSubscription.kt:81-95`), branching to
`collectEmptyDelta`, which narrows via `localizeIndexedGraphContainsAllGraph` and then checks
`final.containsAllAccessPaths(...)`. Cactus also ignores it (`MethodCactusAccessPathSubscription.kt:48`).

Each returned row costs roughly five allocations (`FactEdgeSubBuilder` -> `AccessTree` ->
`FactEdgeSummarySubscription` -> `FactToFact` -> `FactToFactSub`).

**And the filter is applied downstream anyway.** `MethodAnalyzer.handleMethodSideEffectRequirement`
(`:827-849`) computes `emptyDeltaExclusionRefinementOrNull` per requirement and returns immediately when
none survive. So tree mode over-delivers and the receiver discards — **wasted fan-out, not wrong
results**. That is what makes the repair safe.

## 3. Proposal

Four changes, ordered by profit-per-line. None changes the `Storage` interface. None affects
serialization (subscriptions are never serialized).

### C1 — Share the subscriber traversal across requirements

*One file, `SummaryEdgeSubscription.kt:629-643`.*

Group `sideEffectRequirements` by premise base so that requirements sharing a base share the partition
traversal, mirroring the shape `processMethodFactSummary` already uses. Row matching stays
per-requirement (it depends on the requirement's access path), and **delivery stays per-requirement**.

This is the strictly semantics-preserving subset. It removes the `8,687 x (caller EPs x call statements
x exit bases)` partition walk and replaces it with one walk per distinct base.

**Deliberately not proposed: batching the delivery.** `handleMethodSideEffectRequirement` folds
`ExclusionSet::union` across its list (`MethodAnalyzer.kt:832-844`), so passing all 8,687 at once
produces **one** premise carrying the unioned exclusion, whereas the current singleton delivery produces
up to 8,687 premises with individual exclusions. Union means narrower. That may well be the intended
semantics — the function takes a `List` and folds it — but it is a behaviour change, not an
optimisation, and it should be a separate decision. See open question 1.

### C2 — Honour `emptyDeltaRequired` in the tree storage

*One file (`MethodTreeAccessPathSubscription.kt:166-186`); a second if Cactus is included.*

Add the `emptyDeltaRequired` branch, mirroring the automata reference implementation. The predicate
already exists in tree form: `AccessTree.AccessNode.contains(otherAccess)` (`AccessTree.kt:488-499`) is
the semantic, ANY-expanding containment test, and `FactAp.hasEmptyDelta` (`access/FactAp.kt:73-74`) is
what the receiver uses.

Why this is the safest change on the list:

- the parameter is already plumbed end-to-end; no interface change;
- **it cannot change results** — the receiver re-applies the identical predicate and discards
  (`MethodAnalyzer.kt:833-841`), so this only removes work that was going to be thrown away;
- Automata is a working reference implementation of the same branch.

Expected effect is multiplicative with C1: C1 cuts the number of traversals, C2 cuts the rows returned
per traversal.

### C3 — Hoist loop-invariant work out of the per-subscriber loop

*One file, `MethodAnalyzer.kt`.*

```kotlin
1025  for (sub in summarySubs) {
1028      val handler = analysisManager.getMethodCallSummaryHandler(apManager, analysisContext, sub.currentEdge.statement)
1032      val summariesToApply = applicableSummaries.flatMap { handler.prepareFactToFactSummary(it) }
```

`summariesToApply` depends only on `sub.currentEdge.statement` and `applicableSummaries` — never on the
sub's caller fact — yet is recomputed once per subscriber. On the Go path each recomputation allocates a
fresh handler and rewrites the whole rule config
(`GoCallRuleBasedSummaryRewriter` -> `prepareCallStatementRules`). The required count is
`(#distinct statements) x E`; the actual is `(#subs) x E`.

The same shape recurs at `:995` (Z2F), `:1071` (ND2F), `:1180`, at
`MethodCallSummaryHandler.kt:110` (`mapMethodExitToReturnFlowFact`, dependent only on statement and
summary final AP), and at `MethodAnalyzer.kt:1141` (`groupByTo` rebuilt per sub although
`SummaryEdgeSubscription.kt:550` already grouped).

This is not a lower-order optimisation: `R x E` is the *same asymptotic order* as the inherent cross
product, so removing it is worth roughly as much as the cross product itself when `R` is large. Its
value is small when fan-out is small (as in the one sampled summary event) and large when it is not —
which is precisely why C1 and C2 come first.

### C4 — Guard `collectZeroEdge`

*One line, `SummaryEdgeSubscription.kt:375`.*

`collectFactEdge` (`:335`) and `collectFactNDEdge` (`:356`) guard with `isNotEmpty()`;
`collectZeroEdge` appends unconditionally, allocating a `Pair` + `ArrayList` per (group, caller EP) that
is discarded at `:585`. Trivial, and it is inside the hot traversal.

## 4. Explicitly rejected, with reasons

**Coarser row keying — dropping `exclusions` from the subscription row key.** This looked like the
biggest memory win (the JFR-attributed `Object[65537]`/`int[65537]` arrays are exactly the
`initialApIndex` key/value spines). **Merging variants by intersection is unsound — it produces false
negatives.**

The reason is that a premise's exclusion set is not merely a coverage restriction; it is a **refinement
obligation**. `handleInputFactChange` -> `registerNewInitialFact` converts the exclusions to accessor
indices (`TreeInitialFactAbstraction.kt:54-65`), `AccessPathTrieNode.add` accumulates them as a union in
`terminals` (`:359-378`), and `abstractAccessPath` then seeds a refined fact exactly when the accessor is
excluded (`:240-249`):

```kotlin
if (!exclusions.contains(accessor)) return                  // covered, no new seed
createAbstractAp(ReversedApNode(accessor, currentAp))       // excluded -> seed prefix.accessor.*
```

Counterexample: two rows share `(arg(0), .descriptor)`; row 1 came through callee A with `E1 = {f}`, row
2 through callee B with `E2 = {g}`. Intersecting gives `E = {}`, so neither `arg(0).descriptor.f.*` nor
`arg(0).descriptor.g.*` is ever seeded, while the merged row claims coverage with `T_A ⊔ T_B` — trees
produced by *different callees*. A flow existing only as `arg(0).descriptor.f.<mark>` through A is
silently lost.

Union **is** the sound join (and is what `MethodEdgesInitialToFinalTreeApSet.kt:95` and
`MethodInitialToFinalApSummaries.kt:271` already do for non-identity edges; intersection is legal only
for identity edges, `:150`, where the conclusion *is* the premise). But union merging costs cross-talk
precision, touches three files, and is a precision decision rather than a minimal change. All three AP
modes independently key on the full premise including exclusions — and the automata mode is finer still
— so this looks deliberate, not an oversight.

**Per-row delivery watermark.** The pairing is already a correct, non-redundant incremental cross
product: direction (i) is `delta_caller x full_callee`, direction (ii) is `full_caller x delta_callee`,
and the short-circuit at `MethodTreeAccessPathSubscription.kt:147-150` genuinely prevents re-pull. A
watermark would address only three delta-integrity defects (see §5), each cheaper to fix at source. It
would also require a `Storage` contract change, a Cactus restructure (no dense row indices there), and
would make `find` non-idempotent — colliding with the subscribe-time replay path that deliberately
re-reads everything.

**Indexing the `summaryInitialFact == null` case.** A no-op. `null` means the summary premise is
abstract — the whole base — and `filterStartsWith(null)` returns `this` unconditionally, so every row
genuinely matches. The set can only shrink by changing semantics, i.e. via C2.

**Making subscription storage soft-referenceable.** The rows are the *only* record of which caller edges
are waiting; there is no re-derivation path and no re-scan. Dropping them mid-run loses flows.

**Event coalescing.** Cheap by callee entry point, but `NewSummaryEdgeEvent` does not know the caller
until `findFactEdgeSub` runs, so a `(callee, caller)` key needs the event restructured. It also has a
sharp edge: event accounting feeds global quiescence, which gates the delayed-edge replay — miscount and
the analysis either hangs or terminates early.

## 5. Delta-integrity defects found along the way (separate fixes)

Not part of this proposal, but they cause genuine re-processing of already-processed pairs:

1. **Compression re-emits the whole tree as a delta.** `MergingTreeSummaryStorage.kt:36` sets
   `edgesDelta = interned` (the entire tree) after compression, so every caller row is re-paired with
   every summary edge already processed.
2. **Id-storage re-emits on exclusion narrowing.** `MethodInitialToFinalApSummaries.kt:156` emits the
   *merged* exclusion, not a delta; since `AccessPath.equals` includes exclusions, each re-emission is a
   fresh `groupBy` group at `SummaryEdgeSubscription.kt:550` and costs a full traversal.
3. **Store-then-notify race.** The summary is inserted under `synchronized` and is immediately visible to
   `findFactSummaryEdges` (`:887-893`), while the notification is only enqueued (`:793-795`). A caller
   subscribing in that window pulls the summary, and the later queued event applies it again.

Also still open from the storage-layout investigation: the tree side has no equivalent of Cactus's
re-emit-on-exclusion-change (pinned by `CactusAccessTest`), and `getSummaries()` never serializes
`ndF2FSummaryEdges`.

## 6. Test plan

**There are zero direct tests of the subscription mechanism** — no test source references
`MethodAccessPathSubscription`, `CommonAPSub`, any of the three mode classes,
`SummaryEdgeSubscriptionManager`, `emptyDeltaRequired`, or any of the three event classes.

The invariant most at risk is **late arrival**: a caller must still be resumed when the callee's summary
appears *after* the caller subscribed. The only tests that genuinely exercise it:

- `AdvInterproceduralTest.mutualRecursion001T/002F` — mutual recursion, so the callee summary cannot
  exist at subscribe time. The single best probe in the repo.
- `EdgeCaseTest.recursive001T/002F` — direct self-recursion.
- `AdvInterproceduralTest.multiCaller001T/002F` (fan-out), `advSideEffect001T/002F` (the side-effect
  path C1 and C2 touch).
- `InterproceduralTest.deepCall001T/002T/003T`, `deepCallClean001F` — multi-hop subscription chains.

For **dropped notifications**, the two suites that run identical assertions under Tree *and* Automata —
which is exactly the comparison C2 makes meaningful:

- `DeepCleanSummaryAnalysisTest` (Tree + Automata subclasses) — emits two summary edges from one initial
  fact.
- `CleanerFieldSensitivityAnalysisTest` — its four **non-vacuity** controls are the ones that catch a
  dropped edge rather than an over-broad one.

Blast radius: `GoMassiveSampleTest` (214 tests) and `GoSampleBasedTest` (104), whose shared driver
asserts `traceResolved` separately from `vulnerabilityReported` — the only coverage of the backward
reader over subscription-delivered summaries.

**New tests this work should add**, since none exist:

1. A direct unit test of `SummaryEdgeFactAbstractTreeSubscriptionStorage.find` with
   `emptyDeltaRequired = true`, asserting it returns exactly the rows for which
   `hasEmptyDelta` holds — and a differential test asserting Tree and Automata agree on the same input.
2. A late-arrival regression test at the storage level: subscribe, then add a summary, and assert the
   subscriber is notified — the invariant with no direct coverage today.
3. A counter-based test for C1 asserting the number of subscriber traversals is proportional to distinct
   premise bases rather than to requirement count.

**Measurement gate.** Before/after on the isolated SSRF matrix
(`opentaint-w3-benchmark-results/post-rebase/run-measurement.sh`, 12 GiB, 300 s IFDS timeout, quiet
gate). The specific signal to watch is not wall time (censored by the timeout) but the active-event
snapshots: the 25:1 requirement-to-summary event ratio, and whether any single event still holds a worker
for tens of seconds.

## 7. Open questions

1. **Is batched delivery of side-effect requirements intended?** `handleMethodSideEffectRequirement`
   takes a `List` and folds `ExclusionSet::union` across it, which suggests it was written to receive the
   whole batch — but the only caller passes singletons. Batching would produce one narrower premise
   instead of many wider ones, which would also directly reduce the exclusion-variant premise growth. It
   is a behaviour change and needs your call.
2. **Should Cactus get C2 as well?** It ignores `emptyDeltaRequired` and additionally does no filtering
   at all in `find` (`// todo: filter`). It has no e2e test coverage in this repo, so changing it is
   unverifiable here.
3. Was the store-then-notify visibility window (§5.3) considered? It is the only defect of the three that
   could double-apply a summary rather than merely re-deliver it.

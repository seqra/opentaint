# Next iteration: avoid repeated demand queries

Historical proposal. The [current proposal](bidirectional-joined-state-and-loop-consumers-next-iteration-20261103.md)
uses the later `050b83cfb` campaign, including the run-1 Thingsboard OOM.
Use that proposal for the next selection. The measurements below remain
specific to `1e6c4396`.

3 November 2026. Status: proposal, not selected for implementation.

Use the measurements from
[the loop-block report](../reports/bidirectional-loop-blocks-performance-20261103.md).
The measured runtime is `1e6c43963868dde6f652a4b9fa0284c95c818b2c`.
OWASP completes **run-5**, Conductor completes **run-7**, Thingsboard stops
in **run-2** with **run-1** accepted, and Stirling-PDF stops in **run-8**
with **run-7** accepted.

The finding comparison fails. Resolve the new missing findings before
accepting a speedup as a correct result. The existing NORMAL ND contributor
fix recovers 17 of the previous 18 OWASP losses. It does not explain all
remaining losses. Keep this correctness work separate from the following
performance proposals.

## 1. Rank and expected effect

| Rank | Change | Main target | Why it can remove substantial work |
| --- | --- | --- | --- |
| 1 | Select terminal origins before static graph traversal | Thingsboard run-2 | About 91.23% of sampled Java CPU includes the terminal-origin walker. Current C5 repeats a query that ignores the provided DATA until its final callback. |
| 2 | Reuse complete loop-query work at the same context | Stirling run-7 and run-8 | The observer is 96.12% of run-7 Java samples. One logged method causes over 11 million observations. Batch equal queries, then prepare the fixed part of C5 if distinct queries still dominate. |

These are work-removal proposals. A twofold improvement is a measurement
target, not a proved project speedup. Do not optimize atomic counters,
array allocation, or trie traversal as the principal next change.

Thingsboard's exact CPU capture attributes 71.73% to C5 and 24.84% to native
GC. Its 95.02% C5 share in JFR uses Java samples only. Stirling's exact
run-7 CPU capture attributes 94.04% to the observer and 1.03% to GC. Keep
these denominators separate.

## 2. Select terminal origins before static traversal

### Current and new behavior

Current:

```kotlin
fun intersect(original, raw) {
    visitControlPairs(includeDerived = original.isZero) { pair ->
        // The static walker has already found this complete pair.
        restrictWithPair(original, raw, pair)
    }
}

fun visitDerivedControlPairs(...) {
    walkTargetOriginsFromEveryTerminal { origin ->
        emit(PairedDemand(TargetEntry, exitFor(origin)))
    }
}
```

New:

```kotlin
sealed interface ControlExitSelection {
    data object Any : ControlExitSelection
    data object Zero : ControlExitSelection
    data class Data(val rawLeaves: List<Pattern>) : ControlExitSelection
}

// Keep the existing local paired rows first.
C2(actualZero)              -> Any
C5(zeroOriginal, Reach)     -> Zero
acceptsTarget(...)          -> Zero
C5(zeroOriginal, DATA)      -> Data(rawLeaves)
C5(nonzeroOriginal, ...)    -> no derived terminal query
```

`Any` preserves the existing ZERO admission rule. A real terminal input
already proves one complete Target-entry pair. C2 can stop at that input;
it does not need every predecessor origin. This grants no output permission.
C5 still checks the complete pair.

For `Zero`, consider actual ZERO origins. For `Data`, select exact primitive
origins that can restrict the current DATA result. Then ask whether those
origins can reach a terminal. Do not enumerate all other origins first.

### Example and facts

```java
void setA(Box p) { C.a = p; }
void hop()       { C.b = C.a; }
void consume()   { sinkT(C.b); }
void root(Box p) { setA(p); hop(); consume(); }
```

Relevant run-1 guidance:

```text
p.*/T         -> C.a.*/T       DEMAND
C.a.*/FLOW    -> C.b.*/FLOW    DEMAND
C.b.*/T       -> DemandTarget DEMAND
```

The backward candidate is `ZERO -> p.$/T`. Other methods can have many
unrelated static fields and terminal readers.

```text
before:
    walk backward from every terminal
    derive origins for p, q, unrelated fields and marks
    C5 discards all origins that cannot restrict p.$/T

after:
    origin index selects actual p.*/T -> C.a.*/T
    existing C5 restricts p.$/T with the actual p.*/T origin
    forward continuation: C.a/T -> C.b/T -> terminal
    use the same complete (Target, p.*/T) pair
```

### Use exact first endpoints

```kotlin
data class TerminalOriginSeed(
    val origin: Pattern,        // Actual first row.from.
    val afterFirstRow: Pattern, // Actual first row.to.
)

for (origin in indexedDirectTerminalOrigins(selection)) {
    offerExistingPair(origin)
}
for (seed in indexedOriginSeeds(selection)) {
    val selected = restrictWithExactOrigin(raw, seed.origin)
    if (selected.isEmpty()) continue
    if (reachesTerminal(seed.afterFirstRow, exactView)) {
        offerExistingPair(seed.origin)
    }
}
```

An arbitrary overlapping input is not an actual origin. Replacing a stored
origin by the submitted fact can change its field length and the C5 budget.
Keep the exact first origin, its mark and geometry. Use the existing
static-anchor, overlap and mark-composition rules for later steps.

Use existing bridge-start and writer-source indexes. Add an input index
for direct terminal patterns. Select ancestors and descendants when the
current AP restriction can accept both. Select full input labels before
owner checks. The current FLOW-only `outgoing` API is not enough; the new
continuation query must also see mapped concrete-mark edges.

For one origin with several possible first rows, a single successful
continuation proves the same pair. This is an existence query. It does not
replace an executable ND join by an OR.

### Cache continuation questions, not all pairs

```text
(snapshot, method, block entry, selected exit, visibility, endpoint pattern)
    -> reaches a real terminal: true / false
```

The endpoint keeps its concrete mark, path, tail and exclusions. Keep the
exact immutable view identity. A new temporary wrapper is not a new graph.
Cache only questions that occur. Do not materialize every method's static
origin closure or every writer-reader product.

A finite worklist handles cycles. Cache false only after exhaustive failure.
Cache true only for a witnessed successful continuation. An in-progress or
cancelled query is not false. Eviction can cause recomputation; it cannot
change the answer. Do not add a new weak identity cache or change the soft
reference manager as part of this proposal.

### Proof and measurement requirements

Prove selected-origin completeness and equivalence to the old reverse walk.
Preserve whole pairs, owner/port visibility, directional mark composition,
per-origin C5 budgets, and all DATA results. DATA cannot stop after its first
successful origin. Prove cache equivalence under cancellation and cycles.

Measure query counts by `Any/Zero/Data`, selected origins before and after
C5, distinct continuation keys, graph states/labels/owner tests, cache hits,
retained bytes, and emitted pairs. Compare exact results with the old query
on finite graphs and native static/Target cases before project experiments.

## 3. Reuse complete loop-query work

### Evidence and the current cost

Stirling run-7 takes 855.159 seconds for 115,571 processed statement packets.
Its whole-phase JFR has 44,842 Java samples; 96.12% are in the observer.
Within that observer population, C5 is 54.75%, C2 is 20.30%, saved AP
application is 11.57%, and saved-row enumeration is 4.50%.

Ten logged owners perform 11,114,534 observations, including 6,370,979
proper-prefix trials on 4,743,555 raw scalars. Most are in
`decodeMimeHeader(StringBuilder)`. These are logged-owner counters, not a
complete population census. They do not prove that all query keys repeat.

Current:

```kotlin
for (scalar in appliedLoopResult) {
    val required = observe(scalar) // AL C2 + saved AL/B C5 + L C2.
    if (required.isEmpty) continue
    for (prefix in properPrefixes(scalar)) {
        if (observe(prefix) == required) {
            emit(prefix)
            break
        }
    }
    // Otherwise emit the original scalar.
}
```

Each observation replays saved adjacent relations and intersects their
results with enclosing demand. It also calculates the same direct C2
admissions twice: once without labels, then once with scope/family labels.

### First remove equal queries within an owner batch

```kotlin
data class LoopQueryKey(
    val parent: BlockScope,
    val loop: BlockId,
    val entry: PortId,
    val exit: PortId,
    val original: PremiseKey,
    val scalar: Pattern,
    val layer: Layer,
    val nonSubsumable: Boolean,
)

// Scope/mode/policy/snapshot are fixed by the owning runtime or explicit key.
temporaryQueries.putIfAbsent(key, request)

fun flushQueries() {
    for ((key, request) in temporaryQueries) {
        val selected = ordinaryLoopRestriction(request)
        deliverThroughExistingCompletionStorage(key, selected)
    }
    temporaryQueries.clear()
}
```

Batch only equal scalar queries with equal complete contexts. Preserve
protection explicitly: `Facts.equals` omits that annotation. Do not merge
two field shapes, marks, layers, originals or control ports. A query is pure
and its snapshots are fixed during the run, so equal queries have equal
results. Keep the existing restriction function and output deduplication.

This temporary collection has a use: avoid repeated pure queries before
delivery. It is not a new persistent raw-fact or raw-summary history. Flush
it at an existing owner work boundary. Pending query work must use the
existing counted Work protocol and must prevent an early freeze. Test late
callbacks and the case with no fresh initial or post-statement output.

If substantial duplication crosses batches, consider an evictable query
memo only after measuring its working set and memory. Do not assume a
packet count equals a scalar-query count. If most complete keys are unique,
batching alone is not the main optimization.

### Then prepare the fixed part of the observer

```kotlin
val plan = prepareObservation(
    snapshot, parentScope, loop, ports, wholeOriginal, policy
)
val observation = plan.observe(actualScalar)
```

Build one scope-labelled C2 result per family and derive the unlabelled
sets from it. This removes duplicate lookups with exact equality.

For C5, the enclosing original and paired demand view stay fixed while many
raw and prefix facts are tested. Prepare original-entry eligibility once.
Select compatible saved AL outputs and paired exit rows before creating
intermediate AP results. Use their exact input/output geometry and budgets.
Keep actual incoming suffix handling in the existing AP applicator. A plan
must not turn input eligibility into an independent exit permission.

The more ambitious follow-up is a lazy composed consumer: saved AL relation
followed by enclosing C5. It must produce the same complete observation,
including layers, exclusions, protection, physical ports and Target IDs.
Do not enumerate every possible relation/demand product at transition time.
Prove the exact composition before replacing the ordinary application path.

### Example and facts

```java
Node step(Node x) {
    Node y = new Node();
    y.a = x;
    return y;
}
Node finish(Node x) { return x; }

Node decode(Node x) {
    while (again()) {
        x = step(x);
    }
    return finish(x);
}
```

```text
Loop result:       P -> x.a.b.c.$/T
Saved AL:          x.*/FLOW -> ret.*/FLOW
Enclosing demand:  ret.a.b.[any]/T paired with P
```

Before, every repeated offer and every trial prefix applies the saved AL
relation, rechecks P against paired entry demand, builds a ret result, and
runs C5. After batching, an equal complete query executes once per batch.
After planning, P's eligibility and compatible relation/demand descriptors
are reused while the actual suffix still goes through the same AP rules.
The selected loop result is unchanged.

### Required evidence and proofs

Record total and distinct complete query keys, batch duplicate counts,
scalars per packet, saved rows applied, C5 pairs tested, prefix trials,
and time/allocation in each observer component. Use an explicit bounded
measurement window if exact uniqueness instrumentation would distort heap
usage. State the coverage of that window.

Prove query purity, snapshot identity, exact-key equality, batch equivalence,
metadata preservation and scheduling completion. For a prepared C5 plan,
prove entry selection is independent of raw output and preserve the complete
paired restriction. For a composed consumer, prove equality with ordinary
native application plus ordinary C5, including both directions.

The target is at least a twofold reduction in run-7 time with equal quality.
A high duplicate rate supports batching; a low rate supports preparing the
C5/native composition. Do not claim a measured benefit for either before
collecting those counts.

## 4. Smaller items and exclusions

A proper-prefix cut is DEMAND. A NORMAL enclosing DATA result or a
NormalTarget can prove that no such cut preserves the full observation,
provided every observer transfer is layer-monotone. This can avoid some
failed trials. A NORMAL FLOW initial alone is not that proof: the existing
C2 policy can emit intrinsic NORMAL FLOW from a DEMAND input.

Even if every logged run-7 raw fallback qualified, at most five trials per
fallback give an observation-count upper bound of about 16.7% in these hot
owners. Its actual eligibility and CPU savings are unknown. Keep it as a
secondary item, not the principal twofold-performance claim. Duplicate C2
lookup removal is also smaller than the measured C5 problem.

Do not change IR storage, mark representation, field grammar, normal/demand
layers, ZERO admission, source permissions, complete ND execution, static
ownership, or Target composition. Do not disable loop restriction as an
unreviewed shortcut. These proposals preserve the selected observations;
any required semantic change needs a separate explicit decision and proof.

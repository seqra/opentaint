# Next iteration: reduce repeated summary work

Date: 30–31 October 2026. Status: design candidates only. No runtime change.
Base: `e090118e5f9603f1973c0578a3e04998035f4508`.
Use the [latest performance report](../reports/bidirectional-selected-call-policy-performance-20261030.md).

Latest closed commands are OWASP **run-5/5/5**, conductor **run-4/3/3** and
thingsboard **run-2/1/1** (reached / complete / accepted). Stirling closes with
TIMEOUT at **run-7/6/5**. All four analyzer commands are closed. The report
states the fresh heap measurements and their separate decoder limits.

## 1. Selection and expected impact

The caller gate works. It removes 82.22% of conductor run-4 offers and 99.78%
of Stirling run-6 offers. Conductor still times out. Thingsboard still OOMs
at 16 GB. Do not add another input-admission cache as a presumed solution.
The measured remaining work has different owners and stages.

| Rank | Candidate | Current behavior | New behavior | Expected saving and limit |
|---|---|---|---|---|
| 1 | Share joined writer selection | Each pending writer repeats the same input query | Select once per complete pending query; apply every destination writer | Remove repeated candidate visits and matches. Target thingsboard's 236.104-second transition. Bound images and outputs remain required. |
| 2 | Merge equal current-summary images before return processing | Equal images traverse the return suffix separately | For one delivery batch, retain one equal image per full return context and union its protection | Target conductor's measured return and late output work. The two-input case halves suffix calls. The project duplicate ratio is not yet measured. |
| 3 | Stop subtraction below an inherited complete cover | Subtraction descends even when inherited cover already contains a whole subtree | Return no remainder for that subtree before visiting its children | Target Stirling point storage after the caller bottleneck is removed. This removes tree visits, not fact semantics. Coverage-hit frequency remains unmeasured. |

These targets reduce operations. They do not change tree or IR storage formats.
A two-to-one example is not a twofold project speedup. Measure the relevant
query, image and subtree ratios before making such a claim. The third target
has a smaller measured whole-run upper bound and must not be presented as the
complete fix for Stirling.

## 2. Semantic scope

Keep the current selected call policy: persisted replay on **every offer**,
then complete caller demand admission, then current subscription and initial
key delivery. Keep all initial shapes, tails, E, mark exclusions, layers,
protection rules, source/sink identities, ND origin sets, aliases and stopping.
Do not add grounding support, class-wide mark abstraction, weak identity
caches, reference-manager rewrites or input supplier histories.

No new approximation is selected. The intended semantic outputs and rule
occurrences stay equal. Two operational changes need explicit review:

1. Joined writer processing visits pending destination IDs in query batches.
   Output order changes from writer-first to selected-input-first.
2. Equal current-summary images can traverse return stages once instead of
   several times. Duplicate callbacks can disappear.

For both changes, verify that callback order preserves semantic observations.
Duplicate diagnostic callback counts can differ. For the second change, also
prove the actual return-stage and observation adapters. A finite set-union
theorem alone does not prove arbitrary stateful callbacks.
Do not restore correctness by changing a rule, a field transfer or a demand.

## 3. Share the joined writer query

### 3.1 The repeated work

Thingsboard completed run-1, then spent 236.104 seconds in joined binding.
It processed 2,351,008 writer items, visited 222,615,530 candidate inputs,
accepted 28,045,257 matches and emitted 27,942,954 bound outputs. In its
closed binding sample, matching is 38.43% of Java samples and 60.24% of
allocation weight. Native GC workers account for 62.84% of CPU samples.

```java
void set(Box p) {
    C.f = p;
    C.g = p;
}
// Run-1 primitive writer relations:
// p.*/FLOW -> S.C.f.*/FLOW DEMAND
// p.*/FLOW -> S.C.g.*/FLOW DEMAND
```

This queries **nonstatic p**, not a propagated static fact. Run-1 still does
not relay static facts through method bodies.

```text
before: writer C.f -> scan N frozen inputs -> M matches -> M images for C.f
        writer C.g -> scan N frozen inputs -> M matches -> M images for C.g
new:    query (set, p.*/FLOW) -> scan N inputs -> M matches
                                          -> M images for C.f and C.g
```

The new version halves selection in this example. It retains both destinations
and all their outputs. With W pending destinations sharing one query, selection
changes from W*N to N visits. Destination image application remains W*M.

### 3.2 Pending storage and pipeline

```kotlin
data class Query(val owner: MethodKey, val original: InitialAp)
val pending = LinkedHashMap<Query, IntArrayList>()
val queue = ArrayDeque<Query>()
val ap = ops.manager
// Keep the existing admitted (owner, writerId) set.

fun offer(owner: MethodKey, id: Int) {
    if (!admitted.getOrPut(owner, ::IntOpenHashSet).add(id)) return
    val q = Query(owner, keys.row(id).original)
    pending.getOrPut(q) { queue.addLast(q); IntArrayList() }.add(id)
}

while (queue.isNotEmpty()) {
    val q = queue.removeFirst()
    val ids = checkNotNull(pending.remove(q)) // detach before callbacks
    val first = keys.row(ids.getInt(0))
    val representative = Publication(q.original,
        ap.factsOf(first.result.fact, first.result.exclusion, Layer.DEMAND))
    val visited = HashSet<InputKey>()
    borrow(q.owner, representative) { part ->
        check(part.callee == q.owner)
        check(part.ref.premise is InitialAp)
        check((part.added is FlowTree) == part.ref.premise.isFlow)
        if (!visited.add(InputKey(part.ref, part.added.groupKey, part.zeroOnly)))
            return@borrow
        if (q.original.isZero && (!part.ref.premise.isZero || part.added !is Reach))
            return@borrow
        val selected = matches(part, representative, 0, ops, mode) ?: return@borrow
        for (id in ids) applyWriter(part, selected, keys.row(id))
    }
}
```

The instance fixes manager, direction, run mode, field limit and member index.
InitialAp keeps the complete base, path, tail, E and mark. Source inspection
shows that input selection reads this original premise and owner, not the
static destination. Preserve full selected Facts and full CallerRef headers.
The snippet keeps the existing `borrow(MethodKey, Publication, visitor)` API.
The representative conclusion is required by that API, but neither candidate
selection nor matching reads it. Apply each writer's own conclusion afterward.

A writer discovered while processing q creates a new pending batch for q.
There is no completed-query set. Never lose a late destination. Pending IDs
replace the old pending writer items. Reuse a selected actual only inside its
borrow callback. Do not retain matched Facts or copy the frozen N2 input store.

### 3.3 Two independent matching reductions

A complete FULL-mode premise `p.*/FLOW` with empty path, Empty E and empty
mark exclusions accepts the complete same-base canonical input. Return that
input directly instead of rebuilding it through applicable/inside selection
and mark mapping. Keep its own E, mark exclusions, layer and protection.

```kotlin
if (mode.markMode == MarkMode.FULL && j.base == actual.base &&
    j.base != AccessPathBase.Zero && j.base != STATIC &&
    j.base !is AccessPathBase.CleanerTemporary &&
    j.pathData.isEmpty() && j.tail == Tail.STAR &&
    j.exclusion == ExclusionSet.Empty && j.mark == MarkSlot.STAR) {
    return actual
}
return currentSatisfying(actual, j, mode)
```

This first scope excludes GROUP TAINT: the generic operation can project a
full mark and demote the input there. It also excludes static, ZERO and cleaner
temporary routes. No empty-exclusion requirement is imposed on the actual fact.

For a concrete T premise in FULL mode, reject a TAINT input immediately if
its cached whole-tree mark union lacks T. Use the existing fold cache; do not
add a new mark table census or matched-input cache. Keep the full matcher for
all remaining inputs and headers. FLOW cannot satisfy concrete T and already
has a cheap rejection. Measure that path separately.

The universal case is not automatically most candidates. Every universal
visit must be a match. Therefore its count is at most 28,045,257, or 12.60%
of the 222,615,530 visits. Rejected visits need a different test. Add counts
for premise kind, query batches, destinations per batch and fast-path hits.

## 4. Merge equal images before the return stages

Conductor run-4 still times out with run-3 accepted. The full engine attributes
69.96% of Java samples and 87.83% of allocation to current delivery. In the
closed late window, return resumption is 48.63% of Java and 47.37% of allocation;
post-statement admission is nested within it. This is not a cleaner explosion.

```java
Object m(Box p) {
    return p.a.b.c.d;
}
// Backward run-4, limit 3. Demand entry: ret.[any]/FLOW.
// Same complete caller reference at statement S:
// F1 = ret.f.$/T DEMAND; F2 = ret.f.[any]/T DEMAND.
// Both emit J = ret.f.*/FLOW.
// Current publication: J -> p.a.b.c.[any]/FLOW DEMAND.
// Both selected applications yield p.a.b.c.[any]/T DEMAND.
```

F1 and F2 have different typed input headers and correctly survive existing
N2 input admission. For this publication their **images** are equal.

```text
before: 2 input groups -> 2 images -> 2 return traversals -> 1 post-S result
new:    2 input groups -> 2 images -> 1 return traversal  -> 1 post-S result
```

Keep input matching, current subscriptions, ND member registration and AP
image construction. For the first scope, collect current results of one
Delivery event, then drain equal-image groups. Saved records, run-1 static
replies and request effects retain their paths. Do not add cross-event history
or merge merely compatible input trees.

```kotlin
data class ReturnKey(
    val ref: CallerRef,                 // context, initial, caller layer, S, stage
    val resultPremise: PremiseKey,      // includes the complete ND origin union
    val identityCandidate: Boolean?,
    val pendingDemotion: Boolean,
    val ordinaryImage: Facts,           // kind, layer, base, tail, E, mx, root
)

fun ordinaryImage(image: Facts): Facts =
    if (image is TaintTree) image.withProtection(null) else image

fun addImage(key: ReturnKey, image: Facts) {
    val old = images[key]
    images[key] = if (old is TaintTree && image is TaintTree) {
        // withProtection REPLACES a mask. Union before attachment.
        val mask = unionNullable(old.nonSubsumable, image.nonSubsumable)
        old.withProtection(mask)
    } else old ?: image
}
// Drain each retained full context through the existing resumeCallees path.
```

Two equal ordinary images with different masks must keep their exact mask
union. Do not protect the whole tree merely because one leaf is protected.
Different contexts, premises, identity flags, layers, E or tails must remain
separate. Keep register-before-replay and counted delivery through collection
and drain. New inputs registered by a drain callback get their ordinary replay.

The checked kernel preserves annotated membership union and counts N images
versus K distinct signatures. The Kotlin suffix, rule/ND observation and owner
adapters remain validation gates. The production AP example control passes. The actual delivery and suffix
adapters must still pass before implementation is accepted. Count N and K
in real deliveries; do not claim a twofold project saving from the example.

## 5. Prune a subtree already covered by inherited marks

Stirling now completes run-6 and reaches run-7. In the closed run-6 sample,
post-output admission is 42.86% of Java samples. TaintGroup subtraction alone
is 22.80% of Java and 26.96% of allocation. The old caller-accumulation hotspot
has nearly disappeared. Protection merging is much smaller in this window.

```java
Box id(Box p) {
    return p;
}
Box caller(Box input) {
    // Storage-control inputs at S, with the same original premise I:
    // input.[any]/T DEMAND; input.a.b.c.$/T DEMAND; both unprotected.
    // These are supplied valid inputs, not a claim that this code creates them.
    Box x = id(input); // S
    // First result stored: I -> x.[any]/T DEMAND, unprotected.
    // Later result:       I -> x.a.b.c.$/T DEMAND, unprotected.
    // Existing subtraction returns no new fact for the later result.
    return x;
}
```

The existing walker carries inherited cover in SubtractKey.above. It never
removes that cover in a child. When cached foldAll(node) is contained in above,
no descendant leaf can survive. Stop there.

```kotlin
val folded = key.node.allLeaves // first scope: use an existing immutable cache only
if (folded != null && !key.above.isEmpty && fullyCoveredByInherited(folded, key.above)) {
    memo[key] = null
    stack.removeLast()
    continue
}
// Existing at/below/exclusion logic remains unchanged otherwise.
```

`fullyCoveredByInherited` must default to false in the generic algebra API.
Enable it only for proved FLOW and TAINT leaf algebras. FLOW uses Boolean
coverage; TAINT checks the exact and span mark sets separately. Other algebras
keep the old walker. The generic interface alone does not imply set laws.

This changes the subtraction algorithm, not its coverage relation. The ordinary
and protection passes remain separate. An unprotected MAY T cannot consume
an incoming protected EXACT T: its protected pass has no corresponding inherited
cover and must retain that dependency.

Use only a valid immutable cached fold. The first scope falls back when the
fold is absent; it does not force a cold full-tree fold. Prove the concrete FLOW
and TAINT leaf laws, cancellation behavior and DAG memo adapter. Do not infer
that all sampled subtractions are no-ops. Count warm-fold hits, pruned roots,
skipped node estimates and negative checks. Any later cold-fold variant needs
its own cost measurement.

## 6. Proof and implementation gates

The [constructive kernels](../../spec/lean/proposals/summary-work-next-20261030/README.md)
cover complete-query sharing, universal-root matching, equal return-image
membership compaction and inherited-cover pruning. Their receipt states exact theorem
counts and scope: 47 named theorems and 99 audited public declarations, using
only propext and Quot.sound. They do not verify Kotlin or whole-project gains.

All seven prepared production-AP controls passed after the project commands
closed: one return-image control, three universal-match controls and three
inherited-cover controls. The full rerun passed 2,133 core tests and 452 JVM
tests. These controls check the existing AP operations and the candidate laws;
they do not test an implemented optimization. The [portable pruning control](../../spec/lean/proposals/summary-work-next-20261030/controls/README.md)
has the same source bytes as its passing external control.

Before implementation acceptance, extend these controls to FULL/GROUP
boundaries, all legal tails and exclusions, partial protection,
ZERO/static exceptions, ND full origins, native pending demotion and callbacks
which create new subscriptions. Differentially compare every annotated result
and semantic observation, not only a count. Keep the old generic paths as test
oracles. A required new field or rule policy needs a separate design decision.

For writer selection, compare exact bound outputs and the completed closure,
including late same-query writers and recursive calls. For return batching,
prove that no permitted suffix or rule occurrence depends on duplicate invocation.
For pruning, compare every remainder against the old walker on shared DAGs.

Add bounded aggregate measurements only. Do not retain per-fact diagnostic
histories. Repeat only the selected current project configuration after the
chosen changes, and report reached / complete / accepted iterations each time.

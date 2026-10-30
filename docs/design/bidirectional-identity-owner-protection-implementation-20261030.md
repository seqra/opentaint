# Implementation proposal: identity storage, owner visibility and protection admission

Date: 30 October 2026. Status: implemented at
`edb2e06cdb17eecafbe03415236bf56c57910239` and measured.
See the [closed campaign report](../reports/bidirectional-identity-owner-protection-performance-20261030.md)
for current results. The design and base measurements below describe the
implementation contract; they do not describe the next iteration.

Base analyzer: `c98d12582a138d5898e94908ee6690dda73998ca`.
The documentation commit `24b83a094` contains the measurements and the selected
[next-iteration proposal](bidirectional-demand-stop-static-labels-cfg-delivery-next-iteration-20261030.md).
This document makes its three changes concrete. It excludes the later candidates
in that proposal's section 5.

Latest measured reached / complete / accepted iterations:

| Project | Reached | Complete | Accepted | Status |
|---|---|---|---|---|
| OWASP | run-5 | run-5 | run-5 | OK |
| conductor | run-6 | run-5 | run-5 | TIMEOUT |
| thingsboard | run-2 | run-1 | run-1 | OOM |
| Stirling-PDF | run-6 | run-5 | run-5 | TIMEOUT |

See the [measurement report](../reports/bidirectional-demand-stop-static-labels-cfg-delivery-performance-20261030.md)
for the full data and their limits. No new project measurement is part of this
proposal task.

## 1. Semantic contract and selected work

**There are no selected analyzer semantic changes.** Each optimization must
return the same complete results and fresh deltas as the base implementation.
Protection is part of this comparison even though `TaintTree.equals` ignores
it. Object addresses, internal counters and memory layout can differ.
Equivalence compares the same inputs and completed work. A fixed time/memory
budget can permit a different final iteration after an optimization. This is
not a change to the transfer or stopping rules.

| Selected change | Current implementation | Proposed implementation | Must stay equal |
|---|---|---|---|
| Literal identity storage | A complete scalar group at each occupied point | Point bits for exact identity images; full group on promotion | Current rows and every emitted ordinary/protection delta |
| Static owner visibility | Graph search and a byte memo in each inherited view | One frozen component/family bit relation | Each original row's exact owner Boolean |
| Protection admission | Repeated mask intersection during construction | Private construction after a proved coordinate-inclusion operation | Ordinary root, protected root and canonical header |

Keep these rules:

```text
Store a completed result at its producing statement S.
Do not store an initial/resumed input as a completed result.
Keep the current CFG cache, delivery order and output gate locations.
Keep NORMAL and DEMAND separate.
Keep field/mark exclusions and all tail kinds.
Keep protection creation, transport, coverage and upgrades.
Keep rule, cleaner, alias and static-write callbacks at their current sites.
Keep static label selection, C2 emission and C5 restriction.
Keep exact local W/R attachment scope by full MethodKey.
Keep the outgoing-demand stop rule and field limits 1,1,2,3,... .
```

There is no new approximation, rule reduction, grounding label, input-history
gate, alias policy, query policy or IR storage change. Keep semantic equality
and hashing unchanged. Proof certificates in the Lean model are not new
runtime edge metadata.

If implementation cannot preserve this contract, present the failing code and
fact trace for a decision. Do not close the gap by changing the analyzer rules.

## 2. Source map and ownership

Paths below are relative to
`core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/`.

| File | Change |
|---|---|
| `ap/LiteralInitialImage.kt` — new | Recognize and reconstruct the exact canonical image of one initial |
| `store/MethodEdges.kt` | Add compact scalar point ownership and one-way promotion |
| `ap/Groups.kt` | Add the private certified admission constructor and replace proved constructor chains |
| `store/FrozenOwnerVisibility.kt` — new | Build iterative SCCs, the quotient DAG and frozen family rows |
| `store/StaticGuidance.kt` | Expose read-only graph operations; collect existing owner families; use the frozen index |
| `engine/RunMethodAnalyzer.kt` | Copy optional point-store scalar statistics before release; no transfer changes |
| `engine/RunManager.kt`, `driver/IterationDriver.kt` | Aggregate/log optional new statistics if needed; no completion or stop changes |

Unchanged production APIs include `MethodEdgeStore.add`, `addDiagonal`, both
`edgesAt` overloads, `C5StaticDemandView`, the demand-store query APIs and the
source/sink interfaces.

| Storage | Owner | Lifetime | Stored data |
|---|---|---|---|
| Compact scalar points | One MethodEdgeStore, one writer | Current method actor; released at freeze | Initial key, point bits, layer/protection bits and promoted groups |
| Visibility index | FrozenStaticCompletion | Existing frozen run-1-to-run-2 snapshot | Component IDs and immutable family words |
| SCC/DAG build scratch | Visibility builder | Build only | Integer arrays, reverse edges, DFS stacks and quotient edges |
| Certified protection result | Existing AP/store owner | Same as today | The same ordinary tree and mask; no certificate object |

Keep the existing managed trie interner. Do not add a global fact/root cache
or change SoftReferenceManager.

## 3. Literal identity storage

### 3.1 Why this shape is selected

Thingsboard's run-2 heap has 7,514,636 occupied scalar cells. Of these,
5,923,972 contain only literal identities. Static identity-only cells total
5,325,214. The complete point-store retained union is 3,431,625,208 bytes.
The current private wrappers for those static cells alone need at least
809,432,528 shallow bytes, before tables, lists or fact trees. This is not a
net saving estimate for the proposed representation.

All measured literal TAINT identity headers have no protection mask. The new
storage must still preserve a later protected identity. Do not use this
measurement to remove annotation support.

### 3.2 Define the exact image

An identity has one nonzero `InitialAp`. Compare the complete image, not just
semantic coverage or one path in a larger tree. A `PremiseSet`, ZERO, mixed
tree, different header or unsupported mask uses the full scalar group.

| Initial slot/tail | Required conclusion leaf/header |
|---|---|
| FLOW, any legal initial tail K | One FlowLeaf.LEAF at the full initial path; tail K; same E; empty mark exclusion |
| Concrete T, EXACT | One exact T leaf; no any leaf; canonical E=Empty and anyTail=ANY_TAINT |
| Concrete T, STAR/ANY/ANY_TAINT | One any T leaf; no exact leaf; same effective tail and canonical E |

Layer is not part of shape recognition. It selects a separate bit set. No
new mode restriction is needed. The scalar path can use this optimization in
any run. The existing packed `flowBacked` path remains unchanged.

Use an integer result to avoid an allocation per admission:

```kotlin
internal const val NOT_IDENTITY = -1
internal const val PLAIN_IDENTITY = 0
internal const val PROTECTED_IDENTITY = 1

internal fun ApManager.identityKind(initial: InitialAp, f: Facts): Int {
    if (initial.isZero || f.base != initial.base) return NOT_IDENTITY
    // Match the complete typed header and the entire one-path tree.
    // For TAINT, match the canonical image from the table above.
    if (!sameCanonicalInitialImage(initial, f)) return NOT_IDENTITY
    if (f !is TaintTree || f.nonSubsumable == null) return PLAIN_IDENTITY
    return if (sameSingleCoordinate(initial, f.nonSubsumable))
        PROTECTED_IDENTITY else NOT_IDENTITY
}
```

`sameSingleCoordinate` uses the initial's full path, leaf kind and singleton
mark. It is not `isSubsetOf` under AP prefix coverage. Do not compare ordinary
Facts equality and then ignore its mask.

Walk the immutable trie without constructing a Pattern, copied path array,
leaf list or temporary Facts value:

```kotlin
private fun <P : TrieLeaf> ApManager.singleLeafAt(root: TrieNode<P>, path: IntArray): P? {
    var node = root
    for (accessor in path) {
        cancellation.checkpoint()
        if (!node.leaf.isEmpty) return null
        val edges = node.accessorData ?: return null
        if (edges.size != 1 || edges[0] != accessor) return null
        node = node.childData!![0]
    }
    if (node.accessorData != null || node.leaf.isEmpty) return null
    return node.leaf
}
```

The actual helper is inside the AP package and uses `InitialAp.pathData`.
For TAINT it tests `MarkSet.size == 1` and the one mark ID. For FLOW it tests
`FlowLeaf.LEAF`. A root exact leaf has no `any` membership even though the
canonical `anyTail` header is ANY_TAINT. A second leaf, child or mark rejects
the fast path. Keep valid field exclusions; do not replace them with Empty.

```kotlin
private fun ApManager.sameSingleCoordinate(i: InitialAp, root: TaintNode): Boolean {
    val mark = (i.mark as? MarkSlot.Concrete)?.mark ?: return false
    val leaf = singleLeafAt(root, i.pathData) ?: return false
    return if (i.tail == Tail.EXACT)
        leaf.any.isEmpty && leaf.exact.size == 1 && mark in leaf.exact
    else leaf.exact.isEmpty && leaf.any.size == 1 && mark in leaf.any
}

private fun ApManager.sameCanonicalInitialImage(i: InitialAp, f: Facts): Boolean =
    when (i.mark) {
        is MarkSlot.Star -> f is FlowTree &&
            f.tail == i.tail && f.exclusion == i.exclusion && f.markExclusion.isEmpty &&
            singleLeafAt(f.root, i.pathData) == FlowLeaf.LEAF
        is MarkSlot.Concrete -> {
            val tail = if (i.tail == Tail.EXACT) Tail.ANY_TAINT else i.tail
            val e = if (i.tail == Tail.EXACT || i.tail == Tail.ANY)
                ExclusionSet.Empty else i.exclusion
            f is TaintTree && f.anyTail == tail && f.exclusion == e &&
                sameSingleCoordinate(i, f.root)
        }
    }
```

The outer `identityKind` checks the base first. These helpers check geometry
and headers only. The mask then needs the same coordinate test, not a weaker
ordinary-tree equality test.

Reconstruction is needed only for promotion or inspection. Construct the
literal image directly with the existing prepend and typed factories:

```kotlin
internal fun initialImage(m: ApManager, i: InitialAp, layer: Layer, isProtected: Boolean): Facts {
    return when (val slot = i.mark) {
        is MarkSlot.Star -> {
            check(!isProtected)
            val root = FlowAlgebra.prepend(m, i.path, FlowAlgebra.LEAF_NODE)
            m.flowTree(i.base, layer, i.exclusion, MarkExclusions.EMPTY, root, i.tail)
        }
        is MarkSlot.Concrete -> {
            val marks = m.markSetOf(slot.mark)
            val leaf = if (i.tail == Tail.EXACT) m.taintLeaves(marks, MarkSet.EMPTY)
                else m.taintLeaves(MarkSet.EMPTY, marks)
            val root = m.taintAlg.prepend(m, i.path, m.taintAlg.leafNode(leaf))
            m.taintTree(i.base, layer, root, i.exclusion,
                if (i.tail == Tail.EXACT) Tail.ANY_TAINT else i.tail,
                nonSubsumable = if (isProtected) root else null)
        }
    }
}
```

Do not call the general `factsOf`/`normalize` admission pipeline here. It can
reapply abstraction. This operation restores an existing exact stored image;
it does not emit or normalize a new initial. It adds no request or callback.

### 3.3 Per-premise scalar storage

Replace the scalar `groups` value type, not its identity-based key policy:

```kotlin
private val groups = IdentityHashMap<PremiseKey, ScalarPremiseRows>()

private class ScalarPremiseRows(val initial: InitialAp?) {
    var normal: BitSet? = null
    var demand: BitSet? = null
    var protectedNormal: BitSet? = null
    var protectedDemand: BitSet? = null
    var full: Array<ConclusionGroup?>? = null
}
```

Create the owner only after a scalar non-REACH result arrives. `initial` is
null for an unsupported premise. Allocate each `BitSet()` only on its first
membership; do not allocate a method-sized bit array for every layer in
advance. Allocate `full` only when one point needs a full group. This avoids
a second large premise directory and a per-point wrapper.

For one point/layer, the states are:

```text
ABSENT:    present bit=0, protected bit=0
PRESENT:   present bit=1, protected bit=0
PROTECTED: present bit=1, protected bit=1
```

A protected bit must imply a present bit. FLOW never sets a protected bit.
The two layers do not subsume each other.

Use these small bit operations inside `ScalarPremiseRows`:

```kotlin
private fun bits(layer: Layer, mask: Boolean, allocate: Boolean): BitSet? {
    val old = when (layer) {
        Layer.NORMAL -> if (mask) protectedNormal else normal
        Layer.DEMAND -> if (mask) protectedDemand else demand
    }
    if (old != null || !allocate) return old
    val fresh = BitSet()
    when (layer) {
        Layer.NORMAL -> if (mask) protectedNormal = fresh else normal = fresh
        Layer.DEMAND -> if (mask) protectedDemand = fresh else demand = fresh
    }
    return fresh
}

fun present(layer: Layer, S: Int) = bits(layer, mask = false, allocate = false)?.get(S) == true
fun isProtected(layer: Layer, S: Int) = bits(layer, mask = true, allocate = false)?.get(S) == true
fun setPresent(layer: Layer, S: Int) { bits(layer, mask = false, allocate = true)!!.set(S) }
fun setProtected(layer: Layer, S: Int) { bits(layer, mask = true, allocate = true)!!.set(S) }
fun ensureFull(size: Int): Array<ConclusionGroup?> =
    full ?: arrayOfNulls<ConclusionGroup>(size).also { full = it }
fun clearIdentityBitsAt(S: Int) {
    normal?.clear(S); demand?.clear(S)
    protectedNormal?.clear(S); protectedDemand?.clear(S)
}
```

### 3.4 Admission order and fresh delta

Keep the current checks, REACH branch and packed branch before scalar work:

```kotlin
fun add(node: CommonInst, premise: PremiseKey, f: Facts): Facts? {
    cancellation.checkpoint()
    validateExistingKindAndDepthChecks(premise, f) // Existing checks, unchanged.
    val S = lm.getInstIndex(node)                 // Producing statement.
    if (f is Reach) return addExistingReachBits(S, premise, f)
    packed?.let { return addExistingPacked(it, S, premise, f) }

    val rows = groups.getOrPut(premise) {
        ScalarPremiseRows((premise as? InitialAp)?.takeUnless { it.isZero })
    }
    rows.full?.get(S)?.let { return it.add(f) }  // Full state stays full.
    val kind = rows.initial?.let { m.identityKind(it, f) } ?: NOT_IDENTITY
    if (kind == NOT_IDENTITY) return promoteAndAdd(rows, S, f)

    val seen = rows.present(f.layer, S)
    val oldProtected = rows.isProtected(f.layer, S)
    val newProtected = kind == PROTECTED_IDENTITY
    if (seen && (!newProtected || oldProtected)) return null
    rows.setPresent(f.layer, S)
    if (newProtected) rows.setProtected(f.layer, S)
    return f  // The complete single-coordinate fresh delta, with its mask.
}
```

The first unprotected fact is fresh. Repeating it is not fresh. An unprotected
fact after a protected one is not fresh. A new protected membership is fresh
even if ordinary content is unchanged. This matches the current TaintGroup
behavior for an exact one-coordinate image.

Leave the caller's transfer, rule, request, writer and subscription callbacks
before/after this gate exactly where they are. Do not deduplicate incoming
work at another instruction. Do not make promotion a new reason to enqueue.

### 3.5 One-way promotion

Promote only point S. Other points of the same initial can remain compact.
Do not recompress a full point later in this iteration.

```kotlin
fun promoteAndAdd(rows: ScalarPremiseRows, S: Int, offered: Facts): Facts? {
    val group = ConclusionGroup(m, interners)
    for (layer in Layer.entries) {
        cancellation.checkpoint()
        if (rows.present(layer, S)) {
            val old = initialImage(m, checkNotNull(rows.initial), layer,
                rows.isProtected(layer, S))
            group.add(old) // Restore only; discard this return, no enqueue.
        }
    }
    cancellation.checkpoint()
    rows.ensureFull(size)[S] = group
    rows.clearIdentityBitsAt(S)
    return group.add(offered)
}
```

Restoring at most one literal image per layer into an empty group is exact:
layers are independent, and no other header exists at that point. Do not
restore arbitrary historical facts. On interruption, the run is incomplete
under the existing cancellation policy. Do not convert interruption into a
published empty answer or successful completion.

`edgesAt(node,premise)` must expand compact images and enumerate full groups.
The all-premise variant keeps the same key support, including REACH and packed
keys. The pattern overload must apply its current `leavesNear`/`overlap` tests
to complete reconstructed values. Do not return only the matched leaf.

### 3.6 Before/after trace

```java
// Schematic CFG, not recovered source for every measured statement index.
void helper() {
    a(); // S1 completes I -> I / NORMAL; I=S.C.f.*/T.
    b(); // S2 completes the same literal relation at another producer.
    c(); // S3 completes the same literal relation at another producer.
}
```

```text
Before: three complete group/container trees, one at each producing S.
After:  rows[I].normal={S1,S2,S3}; no full group at these points.

At S2, offer I->I/NORMAL again: null in both implementations.
At S2, offer protected I->I/NORMAL: same protection delta in both.
At S2, offer I->x/T: restore S2's old image, then use old group.add.
At S3, store state stays unchanged during S2's promotion.
```

The measured `TbKafkaProducerTemplate.addAnalyticHeaders(List)` context has
617 static premises and 28 identity statement indices: 17,104 identity-only
cells. The new representation keeps these memberships; it removes most
per-cell objects. It does not remove static flow or summary application.

## 4. Shared static owner visibility

### 4.1 Exact predicate and scopes

For the querying common method q and the **original** owner family F:

```text
VISIBLE(q,F) = q in F.outsideGraph
               OR some o in F.graphIds has a path q -> o

LOCAL(q,F)   = q in F.outsideGraph
               OR graph.id(q) is directly in F.graphIds
```

Paths include length zero. A method absent from the graph has no graph path.
Keep outside membership as the existing exact set lookup. Keep `ownBridges`
as exact common-method membership, and local W/R attachments as exact full
MethodKey lookup. Sharing an SCC does not make two methods the same local
owner. Sharing geometry does not make two label rows have the same family.

### 4.2 Read-only graph access and new index

Keep the detached graph's immutable IDs and adjacency. Add read-only integer
accessors so the builder cannot mutate or retain an escaped adjacency array:

```kotlin
internal fun outDegree(methodId: Int): Int = adjacency[methodId].size
internal fun calleeAt(methodId: Int, position: Int): Int = adjacency[methodId][position]

internal class FrozenOwnerVisibility private constructor(
    private val componentOfMethod: IntArray,
    private val wordsByComponent: Array<LongArray>,
    val familyCount: Int,
    val statistics: BuildStatistics,
) {
    fun contains(methodId: Int?, familyId: Int): Boolean {
        if (methodId == null) return false
        val row = wordsByComponent[componentOfMethod[methodId]]
        return (row[familyId ushr 6] and (1L shl (familyId and 63))) != 0L
    }
}
```

IDs are existing valid dense method/family IDs. Word arrays are private and
frozen. They store no marks, facts, premises, rules or contexts. Do not change
family assignment or deduplicate existing family IDs by owner-set equality.

### 4.3 Build iterative components

Use iterative Kosaraju passes. All loops have cancellation checkpoints. Do
not use recursive JVM DFS on a project call graph.

```kotlin
// Pass 1: original caller -> callee graph.
for (root in 0 until N) {
    if (seen[root]) continue
    push(root); seen.set(root)
    while (stackNotEmpty()) {
        checkpoint()
        val v = top()
        if (cursor[v] < graph.outDegree(v)) {
            val child = graph.calleeAt(v, cursor[v]++)
            if (!seen[child]) { seen.set(child); push(child) }
        } else {
            pop(); finish[finished++] = v
        }
    }
}

// Build exact reverse adjacency with count, allocate, fill passes.
// Pass 2: decreasing finish order, traverse reverse edges.
for (i in finished - 1 downTo 0) {
    val root = finish[i]
    if (component[root] != UNASSIGNED) continue
    val id = componentCount++
    component[root] = id; push(root)
    while (stackNotEmpty()) {
        checkpoint()
        val v = pop()
        for (parent in reverse[v])
            if (component[parent] == UNASSIGNED) {
                component[parent] = id; push(parent)
            }
    }
}
```

The second pass uses vertices in decreasing finish order, not decreasing
numeric method IDs. Mark a vertex when it is pushed. Use arrays
for DFS frames/cursors and a finite visited set. Empty and disconnected graphs
are valid. Dispose of reverse edges, cursors and stacks after the build.

Build the quotient caller-to-callee DAG from every original cross-component
edge. Sort/deduplicate each integer child row. Then use Kahn's algorithm to
produce an explicit topological order. Do not rely on incidental component ID
order. Every child must be processed before its parent in the visibility fold.

```kotlin
val dag = quotientEdges(graph, component) // Self-component edges omitted.
val callerFirst = kahnTopologicalOrder(dag)
check(callerFirst.size == componentCount) // Internal algorithm invariant.
```

There is no new timeout/fuel cutoff or permissive fallback. Component
construction must establish the invariants in section 6. A failed invariant
is an implementation defect; it does not authorize an empty visibility index.

### 4.4 Seed the unchanged family IDs and fold rows

Collect each existing Owners object at its current `freezeOwners` call:

```kotlin
val families = ArrayList<Owners>()
fun freezeOwners(methods: Set<CommonMethod>): Owners {
    val result = Owners(families.size,
        existingSortedGraphIds(methods), existingOutsideGraphSet(methods))
    families += result
    return result
}

// Freeze all B labels and all projected entry families first.
val builder = FrozenOwnerVisibility.Builder(graph, families.size, cancellation)
for (family in families)
    for (owner in family.graphIds) builder.seed(family.familyId, owner)
val visibility = builder.finish()
return FrozenStaticCompletion(/* old payloads, scopes and IDs */, visibility)
```

The family list is build scratch. The final index does not retain it. Keep
Owners objects in the same row payloads as today. Do not seed outside owners
into a component or invent a vertex for them.

```kotlin
val wordCount = familyCount / 64 + if (familyCount % 64 == 0) 0 else 1
val words = Array(componentCount) { LongArray(wordCount) }

fun seed(family: Int, owner: Int) {
    words[component[owner]][family ushr 6] =
        words[component[owner]][family ushr 6] or (1L shl (family and 63))
}

for (parent in callerFirst.reversed()) {
    checkpoint()
    for (child in dag[parent])
        for (word in 0 until wordCount) {
            checkpoint()
            words[parent][word] = words[parent][word] or words[child][word]
        }
}
```

Avoid `familyCount + 63` integer overflow. An empty graph can have nonempty
outside-only families. In that case component rows are empty and outside
membership still works. Zero families need no visibility query or graph
build. Publish the immutable index only after the complete build. Allocation
failure/cancellation follows the existing run failure path and must not create
a successful snapshot.

### 4.5 View query and removal

```kotlin
private fun eligible(owners: Owners): Boolean {
    ap.cancellation.checkpoint()
    if (!inherited) return method.method in owners.outsideGraph ||
        (ownId != null && owners.graphIds.binarySearch(ownId) >= 0)
    return method.method in owners.outsideGraph ||
        visibility.contains(ownId, owners.familyId)
}
```

Keep all original selection stages and exact predicates around this Boolean.
No C2 or C5 transfer/composition code changes. No SCC bit union is used for
LOCAL or W/R scope. The index is built at the existing run-1 handoff and is
used only where inherited run-2 visibility is already allowed. Later runs keep
local-only demand lookup.

After all production callers use this index, remove:

```text
View.reach lazy scratch
View.eligibility ByteArray
ELIGIBLE_NO / ELIGIBLE_YES
DetachedStaticCallGraph.scratch and Reachability (no other production caller today)
old ownerMemoViews/ownerMemoAllocatedBytes counter meanings
```

Keep an independent finite BFS in tests. Do not retain production query
scratch just to validate every lookup at runtime. Keep the detached graph's
ID mapping, own-row index and full local attachment rows.

### 4.6 Example and resource bound

```java
void A() { wrapper(); }
void wrapper() { reader(); }
void reader() { C.b = C.a; }
// Frozen demand B: S.C.a.*/T -> S.C.b.*/T, original owner reader.
```

```text
Current: each new inherited view at A can search A -> wrapper -> reader.
New: seed reader's family bit; OR it into wrapper and A; read that bit.
Both: the same full T row is visible. An unreachable U owner stays invisible.
```

For current thingsboard run-2, N=51,953, E=117,581 and F=16,414. Before SCC
reduction, the word rows need at most 106,815,368 payload bytes. Actual SCC/DAG
counts, array headers and build time must be measured. This adds a shared
retained index while it removes repeated allocation. The old 30.38 GB memo
capacity counter is cumulative allocation, not retained memory to subtract.

The build costs `O(N+E + owner memberships + (C+Ec)*ceil(F/64))`. A graph-family
query is one word test. Do not promise that its 54.88% Java sample region is
the same fraction of wall time, or that this change alone fixes OOM.

## 5. Certified protection admission

### 5.1 Exact invariant

For a TaintTree, let R be its ordinary coordinates and P its mask coordinates.
A coordinate is `(full field path, EXACT-or-ANY leaf kind, full mark)`.

```text
P is a coordinate subset of R.
```

This is not AP overlap or STAR/ANY prefix coverage. The proposed private
constructor uses the same base, layer, exclusion and tail canonicalization.
It changes no protection-creation rule. Keep general `withRoot`,
`withProtection`, `ApManager.taintTree`, `intersectTaintMask` and transport
behavior unchanged outside the proved admission paths below.

### 5.2 One private helper in Groups.kt

```kotlin
// Only audited TaintGroup admission branches may call this helper.
// Caller proof: includedMask is a coordinate subset of root.
private fun admittedTree(
    m: ApManager, header: TaintTree, root: TaintNode,
    includedMask: TaintNode?, exclusion: ExclusionSet = header.exclusion,
): TaintTree = TaintTree(
    header.base, header.layer, root,
    if (!root.hasAny || header.anyTail == Tail.ANY) ExclusionSet.Empty
        else m.intern(exclusion),
    if (root.hasAny) header.anyTail else Tail.ANY_TAINT,
    includedMask,
)
```

No runtime certificate, support label, new edge flag or semantic-key field is
needed. Do not run an expensive subset assertion in the hot helper. Prove its
callers and check coordinate inclusion in tests. Preserve admission/loop
cancellation checkpoints; do not remove cancellation from AP operations.

### 5.3 Replace only these construction chains

| TaintGroup branch | Root and included mask | Inclusion reason |
|---|---|---|
| Ordinary merge, stored result | R0∪R1 and P0∪P1 | P0⊆R0 and P1⊆R1 |
| Emitted delta | ordinaryDelta∪rest.nonSubsumable and rest.nonSubsumable | Mask is an explicit union term |
| Changed `subtractSubsumed` result | ordinaryRest∪protectedRest and protectedRest | Mask is an explicit union term |
| Equal root, changed exclusion | Existing root and union of two valid masks | Both masks are included in that same root |
| Equivalent interned root | Interned R and its existing valid P | Interning preserves all coordinates |

Common merge branch:

```kotlin
val (merged, delta) = alg.mergeAddDelta(stored.root, rest.root, cancellation)
val protection = mergeProtection(stored.nonSubsumable, rest.nonSubsumable)
val deltaRoot = mergeProtection(delta, rest.nonSubsumable) ?: return null

// Before:
// stored.withRoot(intern(merged)).withProtection(protection)
// m.taintTree(..., deltaRoot, ...).withProtection(rest.nonSubsumable)

// After:
list[i] = admittedTree(m, stored, interner.internIfRequired(merged), protection)
return admittedTree(m, rest, deltaRoot, rest.nonSubsumable)
```

Subtraction branch:

```kotlin
val ordinary = subtract(t.root, t, others, protectedOnly = false)
val protection = t.nonSubsumable?.let {
    subtract(it, t, others, protectedOnly = true)
}
val root = mergeProtection(ordinary, protection) ?: return null
if (root === t.root && protection === t.nonSubsumable) return t
return admittedTree(m, t, root, protection)
```

Keep both subtraction procedures, coverage tests and leaf/tail/exclusion
logic unchanged. For the equal-root exclusion branch, pass the **new**
intersected exclusion to `admittedTree`. For a fresh stored result, replace
only the equivalent-root interning construction. Keep the same emitted rest.

For the common protected merge, three normalization calls become zero. For
the changed subtraction result, two become zero. Union, subtraction, delta
formation and mask merging remain. This is a local operation count, not a
predicted whole-engine speedup.

### 5.4 Negative boundary: an arbitrary delta

Do not change generic `ApManager.mergeAddDelta` in TrieOps.kt by reusing its
merged mask:

```text
old ordinary={a/T}, old mask={a/T}
new ordinary={a/T,b/U}, merged mask={a/T}
ordinary delta={b/U}
```

The merged mask is not included in that delta. Keep its current trim. The
selected TaintGroup delta is different: its root explicitly includes the
whole remaining offered mask. Do not add the separate exact-duplicate fast
guard in this iteration; its hit frequency is not measured.

### 5.5 Example

```java
// seedT/seedU/seedV: unconditional sources at arg0.
// copyT(a,b): CM(arg0,T) -> AssignMark(arg1,T).
// copyU(a,b): CM(arg0,U) -> AssignMark(arg1,U).
Box build() {
    Box p = new Box();
    seedT(p.left); seedU(p.right);
    Box x = new Box();
    seedV(x.shared);
    copyT(p.left, x.left);
    copyU(p.right, x.right);
    return x;
}
```

For one complete premise and typed header at S, consider the following
admission. This is a legal packed example, not a recovered Stirling trace.

```text
stored ordinary={left/T,shared/V}; mask={left/T}
offered ordinary={right/U,shared/V}; mask={right/U}

Both implementations retain ordinary={left/T,right/U,shared/V},
mask={left/T,right/U}; emit ordinary={right/U}, mask={right/U}.

Before: trim old mask against merged root, discard it, trim merged mask,
        then trim the mask already included in the emitted delta root.
After:  use the proved included masks; all returned coordinates are equal.
```

## 6. Constructive proofs and their implementation connection

The [checked Lean package](../../spec/lean/proposals/identity-owner-protection-20261030/README.md)
contains executable models and proofs. It uses Lean 4.33.1. The only audited
axiom dependencies are `propext` and `Quot.sound`; there is no proof hole,
Classical.choice, custom axiom or noncomputable definition.

Reproduce from the repository root:

```sh
python3 spec/lean/proposals/identity-owner-protection-20261030/check.py
```

### 6.1 Identity storage proof

`IdentityCells.scalarAdd` models the ordinary/preserved-mask update for one
complete coordinate. `add` implements ABSENT/PRESENT/PROTECTED. Case analysis
proves `exact_state_and_delta`. Lifting it by layer proves `layers_exact` and
`other_layer_unchanged`; lifting by producer proves isolation of other keys.
Induction over the event list proves `trace_exact`, including every emitted
delta. `replay_present` proves exact layer/mask reconstruction.

Promotion and full fallback call the same supplied scalar admission function
on the exact restored state. `promotion_state_and_delta`,
`promotion_never_restores_as_delta` and `full_fallback_exact` prove this
delegation for arbitrary full-group behavior. The model does not assume that
all AP groups are one coordinate. Unsupported geometry always delegates.

The source adapter must show that `identityKind` accepts exactly the image in
section 3.2 and that reconstruction restores it. The whole one-path walk
excludes hidden siblings/marks; the canonical leaf/header cases exclude the
EXACT versus ANY_TAINT error. For that image, the current FlowGroup/TaintGroup
subtract/merge laws reduce to the checked one-coordinate state table. Test
those reductions against the production groups before changing the store.

### 6.2 Owner index proof

`OwnerVisibility.findPath` reuses the prior total finite graph search.
`certify` is an executable reference verifier for a proposed partition and
quotient. It checks finite original reachability inside a component, exact
projection of original edges and a real original edge for every quotient edge.
It returns actual path/boundary witnesses. It rejects a false partition which
merges disconnected vertices. It is a test/model tool, not a proposed cubic
runtime check.

`projectPath` maps an original path to a quotient path. `liftPath` constructs
an original path from quotient edges plus within-component paths. No Boolean
reachability oracle replaces these witnesses.

`rows` defines the terminating recursive DAG reference. Each recursive child
has a strictly smaller topological rank. `buildPrefix`/`table` fill component
rows once in that order; `prefix_exact` and `table_exact` prove equality to
the reference. Runtime arrays implement this table, not repeated recursive
row expansion. `rows_sound` proves that every family
bit has a path to a seed. `path_rows_in_start` proves that every such path sets
the caller bit. `owner_seed_exact` ties seeds to actual family owners.
`indexed_exact` then proves equality to the old finite owner reachability
predicate. `ownerWitness` returns an actual listed owner and original path.
`outside_or_exact` preserves the existing outside-membership OR.

The runtime uses word OR instead of finite lists. For each family f,
`set(f)` inserts exactly that bit and a word OR has bit f exactly when either
operand has it. Induction over the unchanged DAG order transfers the model
proof to packed rows. Families 63/64 and 127/128 are required packing controls.

The Lean package does **not** prove the Kotlin Kosaraju implementation or
the machine-level word operations. Before implementation passes, its adapter
must establish this component contract:

```text
Every original vertex has one component.
Vertices in one component have executable paths in both directions.
Every original edge is internal or appears in the quotient.
Every quotient edge has an original-edge witness.
The topological order contains every component once, parent before child.
```

Kosaraju's first pass finishes a distinct downstream component before its
upstream predecessor, unless the downstream component was already finished.
Processing reverse edges in decreasing finish order therefore cannot cross
into another unassigned component. It reaches the whole current component.
This proves the two within-component directions and complete partition.
Building quotient edges from every original edge proves the two edge
conditions. Kahn's indegree update proves the topological condition. Verify
these certificates independently on all small finite graphs in the adapter
tests, then test long chains and large recursive components without JVM stack
recursion. This source connection is an implementation gate, not a claim that
the current proof checker compiles or verifies Kotlin.

### 6.3 Protection construction proof

The inclusion invariant already holds at the base analyzer's production
construction sites. The source audit finds these raw TaintTree constructors:

| Constructor path | Why the output mask is valid |
|---|---|
| `ApManager.taintTree` | Intersects the offered mask with the new root |
| `TaintTree.withRoot` | Intersects the old mask with the new root |
| `withProtection` | Intersects the offered mask with the existing root |
| `withoutProtection`, `protectedPart` | New annotation is empty |
| `Facts.withLayer` | Copies the same ordinary root and valid mask |

`restoreCurrent` restores an already valid stored snapshot. Induction over
these constructors, existing stored values and the new proved admission cases
preserves inclusion. This is the existing well-formed-state invariant, not a
new input filter. Keep arbitrary-mask trimming at the general helpers. Tests
must include an offered mask with coordinates outside the ordinary root and
verify that these general helpers still trim it.

`ProtectionAdmission` represents exact coordinates by finite Boolean arrays.
`trim_identity` proves `trim(P,R)=P` when P⊆R. `union_included` proves
`P0∪P1⊆R0∪R1`. The delta and subtraction roots explicitly contain their
remaining masks. Coordinate-equivalent interning preserves inclusion.

Substitution proves `stored_union_exact`, `taint_group_delta_exact`,
`subtraction_result_exact`, `exclusion_only_exact` and
`interned_result_exact`. Header canonicalization is the same function in both
constructors. `discarded_intermediate` proves that the first normalized mask
in the old chain cannot affect the final mask.

The source adapter must compare full typed headers and protected coordinates,
not ordinary Facts equality. `merged_mask_not_delta` proves the negative
case in section 5.4. `same_ordinary_different_protection` prevents an ordinary
equality shortcut from dropping a protection-only update.

### 6.4 Composition of the three changes

For each offered output, identity storage returns the same fresh delta or
delegates to the same scalar function. Certified scalar construction returns
the same annotated value as that function's old constructor chains. Thus
their combination returns the same state and delta by substitution. Owner
visibility supplies an equal Boolean at the existing row filter, so the same
complete C2/C5 rows reach the unchanged AP operations.

The implementation connection must preserve producing S, callback sites,
full MethodKey scope, cancellation and snapshot publication. Equality of
these kernels does not authorize changing those adapters, all field transfers
or the analyzer scheduler. The formal check is not a project-performance or
no-FN certificate.

## 7. Tests before implementation

Write the tests before replacing each production path. Tests must compare the
base algorithm and the proposed one, including fresh deltas, not just final
ordinary denotation. Use an independent finite coordinate/path model as well.

| Test file | Required cases |
|---|---|
| `LiteralInitialImageTest` — new | Full path, exact/STAR/ANY/ANY_TAINT, field E, FLOW mx, all bases including named static/class markers, singleton/multiple marks, hidden parent/child/sibling, partial/invalid masks, nonzero/single premise, canonical exact header |
| `MethodIdentityStorageTest` — new | First plain, duplicates, protection upgrade/downgrade attempts, both layers/orders, other S isolation, promotion with competing tail/E/base/tree, full fallback permanence, exact `edgesAt` and pattern results |
| `MethodEdgeStoreTest` | Existing scalar admission cases remain; compare complete ordinary/protection state after each event |
| `CfgDeliveryEngineTest`, `Run1StaticExitRoutingTest` | Same producer S, output delta/fanout, writer hooks, callbacks, freeze and packed-path controls |
| `FrozenOwnerVisibilityTest` — new | Independent BFS for every method/family on exhaustive graphs up to 3 vertices; chain, diamond, recursion, disconnected graph, empty graph/families, length-zero, several family owners, word boundaries |
| `StaticSelectorIndexTest`, demand lookup tests | Different owners per label, projected entries, local false/visible true, two contexts with different W/R, FULL/GROUP/FLOW repair, unchanged complete C2/C5 outputs |
| `TaintAdmissionProtectionTest` — new | Each constructor branch, partial/whole/null mask, late mask upgrade, interning, exact-only canonical header, field E and tail changes, both layers, invalid generic-delta certificate |

Run a test variant with the current `intersectTaintMask` constructor as the
reference. Test instrumentation must show zero normalization calls in the
certified branches and retained calls at general restriction/transport
boundaries. Do not add production exact-repeat profiling or a new hot global
cache for this test.

No new analyzer run is needed to validate this document. The future runtime
change must pass the complete core and JVM suites and the formal check.

## 8. Implementation plan and removals

1. Accept this semantic contract. Keep the checked models and turn the adapter
   cases above into failing tests. Update the model if a finite counterexample
   exposes an incomplete kernel.
2. Implement identity recognition/reconstruction and compact scalar rows.
   Keep REACH/packed behavior and producer delivery unchanged. Add promotion,
   view expansion and frozen scalar statistics. Commit this atomic change.
3. Implement the owner visibility builder and independent BFS tests. Integrate
   it only after all current family IDs exist. Remove the unused view memo and
   production reachability scratch. Commit this atomic change.
4. Implement the private certified constructor and only the audited TaintGroup
   call sites. Keep general helpers and generic delta trimming. Commit this
   atomic change.
5. Run all required checks on the combined implementation. Inspect the diff
   for changes outside these storage/build/construction paths. Recheck data
   equality/hashing and actor/snapshot release.
6. Run the authorized current configuration and publish the measurements
   below. Update source/proof bindings to the measured commit. Do not silently
   add another optimization because one project is still slow.

In addition to the owner removals in section 4.5, remove the old scalar direct
`PremiseKey -> Array<ConclusionGroup?>` path only after the new owner covers
all its callers. Full promoted groups remain. Remove only the proved redundant
constructor chains in Groups.kt. Keep all general AP factories, mask
intersection, current protection rules, summary stores and demand stores.

## 9. Measurements and completion gates

Use the same four projects and configuration as the base report: Gradle
`runProjectAnalyzer`, 16 GB, FULL, aliases/statics enabled, limits `1,1,2,...`.
Use OWASP's CI model and 1,000-second IFDS budget; use 1,080 seconds for each
real project. The outer 1,200-second budget starts at analyzer JVM launch.
Reuse the saved `f945f92c5ae554ff4f5fc7696ee5a269210478bb` finding baseline.
Do not rerun the legacy baseline or use another configuration.

Keep current source/input audits, JFR/native captures, actual GC memory data
and guard-triggered heap capture. Clean old closed raw captures with receipts;
preserve hashes and parsed evidence. Keep the raw current snapshot/profile
outside Git and embed the measured tables and data in the report.

Add only optional scalar statistics at existing lifecycle boundaries:

```text
Identity storage:
  current compact points by kind/layer/protection; full/promoted points;
  compact bit words and scalar array capacity; fallback reasons.
  Do not sum these end-state gauges as cumulative work.

Owner index:
  component/DAG/family counts; seed memberships; build time;
  allocated word count; graph-bit/outside queries and hits.
  Do not label new bit tests as old BFS/memo operations.

Certified admission:
  optional construction counts by proved branch and general fallback.
  No mandatory atomic counter in each trie node operation.
```

Copy point-store counters before `edgeStore=null`; keep only scalar snapshots
after actor freeze. No diagnostic may retain Facts, premise rows or a released
actor. Report index preparation inside joined run-1 binding separately from
engine time and the report barrier.

```kotlin
// Actor-owned counters; no per-membership atomics are needed.
// In the existing freeze/finally block, before edgeStore is released:
identityStatistics = edgeStore?.statisticsSnapshot() // Scalars only.
edgeStore = null
// RunManager/IterationDriver sum snapshots at the existing run-end boundary.
```

Count first full cells separately from promotions of a compact cell. Decrease
current compact-point gauges when S is promoted. Count a new protected bit as
an annotation upgrade, not a new ordinary point. With statistics disabled,
do not allocate fallback-reason maps or scan all stored values at freeze.
For an incomplete engine, use a quiescent live snapshot or the heap census.
If only frozen-actor totals exist, label missing active-actor data unavailable;
do not report those missing counts as zero.

Required result tables:

1. Latest reached, complete and accepted run labels; final OOM/timeout/OK.
2. Every iteration's engine time, field limit and selected outgoing demand.
3. Run-1 engine, joined binding/index build, and report barrier separately.
4. Strict baseline/current and base/current locations and occurrences, including
   export rejects, the three existing Stirling misses and added candidates.
5. Thingsboard run-2 retained point-store/index/cache/queue owners, compact and
   promoted shapes, and the reason for every important fallback category.
6. Owner graph searches removed, index bytes/build cost and allocation profile.
7. Stirling run-6 mask-normalization work and complete annotated output controls.

The success evidence must show fewer full identity containers, no per-view
graph search, and fewer unnecessary mask walks. Check protected/nonprotected
summary shapes again after run-1, with reasons for remaining nonsubsumed
relations. Preserve the reporting vocabulary from the current shape studies.

Faster partial timeout endpoints alone are not fixed-work speedups. Do not
claim an OOM fix from allocation samples. Compare actual retained memory and
completed run behavior. Equal reports to the current analyzer are required
regression evidence; they do not close its older accuracy limits.

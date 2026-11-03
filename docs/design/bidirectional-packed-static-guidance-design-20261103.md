# Packed static guidance and terminal inputs

3 November 2026. **Selected design. Not implemented.**

Reference runtime: `050b83cfb7b2e75856ea113c44d0a2d6b707250d`.
This document implements point 3 of the selected
[joined-state and loop-consumer proposal](bidirectional-joined-state-and-loop-consumers-next-iteration-20261103.md).
Use the [campaign report](../reports/bidirectional-loop-blocks-scoped-requests-performance-20261103.md).
Its latest reached/complete/accepted results are OWASP `run-5/run-5/run-5`,
Conductor `run-6/run-5/run-5`, Thingsboard `run-1/none/none`, and Stirling
`run-8/run-7/run-7`. Thingsboard has no accepted report.

The [constructive model](../../spec/lean/proposals/packed-static-guidance-20261103/README.md)
precedes this implementation design. It proves finite representation and
ordered-query equivalence. It does not verify Kotlin or promise a heap saving.

## 1. Scope

There is **no selected analyzer semantic change**. Change the storage of frozen
W/R rows and anonymous terminal inputs. Keep the current B graph and the
current static query and composition algorithms.

| Part | Current | Selected change |
| --- | --- | --- |
| W/R builder | Rich `StaticGuidanceEdge` sets per owner and exit | One geometry pool and primitive rows per exact attachment |
| Terminal builder | One marked `Pattern` per input membership | Shared input geometry and primitive mark IDs |
| Frozen W/R | Rich row lists and integer indexes | Primitive row arrays and the same index order |
| B graph | Geometry, packed mark pairs, owner families | Reuse as is |
| Query | Return rich rows from retained rich lists | Create only rows selected by the query |
| Static binding | Apply current AP operations to actual links | Reuse as is; append exact bound extras to the catalog |

Do not change field transfers, mark requests, mark eligibility, FLOW
replacement, ND witnesses, source permission, exits, static visibility,
summary restriction, Target IDs or report identity. Do not change equality
or hashing of `Pattern`, `Facts`, `InitialAp`, `MethodKey` or `ScopedSummaryKey`.
Do not select candidate-directed pruning as part of this change.

## 2. Select a detached compact catalog

Use a **detached compact reference catalog**, not a borrowed live store.
`RunSummaryStore.borrow()` currently permits use on its actor owner before
mutation. `PortSummaryStores.entries()` has the same live-owner constraint.
Neither is a frozen run-2 attachment contract. A stored lambda that calls
`state.summaries` also retains the state and defeats execution release.

Keep native admitted stores in the temporary sealed export inventory from
point 1. After execution release, read them once to construct the catalog.
Do not retain these readers in `FrozenStaticCompletion`.

```kotlin
// Proposed types. These do not exist in the reference runtime.
class PackedGuidanceCatalog(
    val geometries: Array<BoundaryGeometry>,
    val endpointGeometries: Array<EndpointGeometry>,
    val rootAttachments: Map<MethodKey, PackedAttachments>,
    val scopedAttachments: Map<ScopedSummaryKey, PackedAttachments>,
    val rootTerminals: Map<MethodKey, PackedTerminalInputs>,
    val scopedTerminals: Map<ScopedSummaryKey, PackedTerminalInputs>,
    val enteredProducerPorts: Set<ScopedSummaryKey>,
)

class PackedRows(
    val geometry: IntArray, // One cell per old local row ordinal.
    val label: LongArray,   // Same ordinal; exact input/output relation.
)
class PackedTerminalInputs(val geometry: IntArray, val inputMark: IntArray)
class PackedAttachments(val writers: PackedRows, val readers: PackedRows)
```

Select attachment keys as the current builder does:

```kotlin
sealed interface AttachmentKey {
    data class Root(val method: MethodKey) : AttachmentKey
    data class Scoped(val producer: ScopedSummaryKey) : AttachmentKey
}
fun key(owner: OwnedScope, exit: PortId): AttachmentKey =
    if (owner.local == BlockScope.ROOT) AttachmentKey.Root(owner.method)
    else AttachmentKey.Scoped(ScopedSummaryKey(owner.method, owner.local, exit))
```

The root has its existing method attachment, not a new per-exit family.
There is no need for a new global raw-row interner. The catalog shares geometry
across owners. Each exact owner keeps a primitive membership array in the old
first-insertion order. The query indexes use these **local ordinals**.
This keeps W and R row-ID domains separate, as the current `pairs()` requires.

The final object graph can reach only immutable geometry, primitive arrays,
index objects, complete owner keys, the AP manager and the detached call graph.
It cannot reach an actor, `BlockRunState`, `MethodContextSource`, live service,
subscription manager, input callback, or a closure that captures them.

## 3. Lifetime and input pipeline

Point 1 owns the lifecycle transition. Point 3 consumes its sealed inventories.
Do not enumerate survivors or expand rows during the seal step.

```kotlin
joinAllRunners()                         // Existing counted-Work barrier.
val exports = captureSealedInventories() // Retain admitted native export stores.
val inputs = moveJoinedInputDirectories()
val staticSources = joinedStaticSourceReaders(exports) // No enumeration here.
releaseClosedExecutionAndDeliveryState()

val catalog = PackedGuidanceBuilder(ap, graph)
val binder = existingJoinedWriterBinder(inputs) { owner, original, output ->
    catalog.addSeed(owner, original.toPattern(), output, STATIC_SHORTCUT)
}

// Same actor/scope/source order as completeJoinedStaticGuidance today.
for (state in staticSources.statesInExistingOrder()) {
    checkpoint()
    catalog.registerProducerIfScoped(state.owner, STATIC_SHORTCUT)
    val writes = state.freezeStaticCandidatesExactlyAsBefore()
    for (id in writes.lostIdsInExistingOrder()) {
        val raw = rawWriteKeys.row(id)
        catalog.addSeed(state.owner, raw.original.toPattern(), raw.result,
                        STATIC_SHORTCUT)
    }
    for (id in writes.observedIdsInExistingOrder())
        if (rawWriteKeys.row(id).original.base != STATIC)
            binder.offer(state.owner, id)
    for (row in state.privateBridgesInExistingOrder())
        catalog.addSeed(state.owner, row.from, row.to, STATIC_SHORTCUT)
    for (terminal in state.outgoingDemandTargetsInExistingOrder())
        catalog.addTarget(state.owner, ROOT_EXIT, terminal.premise)
    for ((exit, summaries) in state.admittedExitStoresInExistingOrder()) {
        catalog.registerProducerIfScoped(state.owner, exit)
        for ((original, facts) in summaries.demandEdges(FORWARD))
            for (leaf in ops.leaves(facts)) {
                catalog.addSeed(state.owner, original.toPattern(), leaf, exit)
                if (leaf.fact.base == STATIC && original.base != STATIC)
                    binder.offer(state.owner, rawWriteKeys.intern(original, leaf))
            }
    }
}
binder.complete()                       // Same AP application and queue.
val completion = catalog.freeze()        // No rich W/R or terminal catalog.
inputs.close()                          // Drop the moved actual-input lease.
staticSources.close()                   // Drop temporary reader references only.
return JoinedEngineResult(exports, completion)

// Existing driver barrier, after the engine returns:
commitExistingHandoff(exports, completion)
```

Closing the lease and temporary readers drops their references. It does not
clear shared admitted native stores, exported summary/Target/contributor data,
or AP/static key interners. The existing driver finalizer owns key-directory
release after its consumers finish. The engine returns frozen exports plus
completion; only the existing driver barrier commits them.

This is pipeline pseudocode. The implementation must retain the current root
versus scoped branch: the root does not receive a synthetic scoped boundary.
For scoped seeds, boundary registration still occurs **before** domain and
anchor filtering, as `addScopedSeed()` does now. Preserve empty entered ports. Traverse only states that entered during the run,
not every potential block in the layout tree.

Raw observations remain raw until current pruning and actual-input application
finish. Keep `StaticWriteKeyInterner`, lost IDs and observed IDs distinct from
the new normalized catalog. Distinct raw IDs can have one normalized key.
Their raw counters and binder admission still use the old IDs.

The prune reads `all()` from the root summary store, or from all scoped port
stores, plus private B: both layers remain visible there. Catalog attachments
read only the current `demandEdges(FORWARD)` and outgoing DEMAND terminals.
Do not replace the prune's both-layer source with the attachment filter.

Do not call `normalizeFlowSummaryPatterns()` at a new site. The old survivor
prune uses it; `completeJoinedStaticGuidance.seed()` does not. Lost, private-B,
summary and bound-extra seeds must pass through exactly their current adapters.

## 4. Normalize once, then encode

Keep the exact `StaticGuidanceEdge.of()` normalization law. Do not construct
that rich object during ingestion.

```kotlin
fun addSeed(owner: OwnedScope, a0: Pattern, b0: Pattern, exit: PortId) {
    registerProducerAsBefore(owner, exit)
    if (!sameDomainChecksAsBefore(a0, b0)) return
    val kind = classifyAnchorsExactlyAsBefore(a0, b0) ?: return
    val a = guidancePattern(a0)
    val b = guidancePattern(b0)
    val relation = marksExactlyAsStaticGuidanceEdgeOf(a, b)
    if (kind == B) {
        existingBBuilder.addBridge(owner.method, a, b, relation)
        return
    }
    val geometry = geometryPool.intern(metadataOf(a), metadataOf(b))
    val label = packBoundaryEndpoints(a, b)
    attachments(owner, exit, kind).addFirstOccurrence(geometry, label)
}
```

The proposed B adapter may accept parts instead of a rich temporary edge.
Its geometry, label order, common-method owner sets and build algorithm remain
unchanged. Do not copy B into the W/R catalog as a second graph.

`metadataOf()` creates a private mark hole only **after normalization**:

```kotlin
fun metadataOf(p: Pattern): Pattern =
    p.copy(fact = p.fact.copy(mark = MarkSlot.STAR))
// The actual endpoint mark slots, including control ZERO, are in the row word.
```

Do not run `guidancePattern()` on this metadata a second time. That would
mistake a concrete row's mark hole for abstract FLOW and could erase its
field exclusion. Metadata is not a legal runtime initial or a published fact.

The unchanged normalizer has these effects:

| Input property | Catalog property |
| --- | --- |
| Concrete mark T or pair T/U | Preserve the exact mark IDs and pairing |
| FLOW mark exclusion `mx` | Drop it where `guidancePattern()` drops it now |
| Abstract STAR field exclusion | Use the existing demand normalization |
| Concrete field exclusion | Preserve it, except the existing MUST conversion |
| `ANY_TAINT` | Normalize to `ANY` and empty field exclusion, as now |
| Class marker `S.C.$/T` | Preserve exact class geometry; do not make class-wide STAR |
| Broad invalid static attachment | Apply the old anchor rejection; do not widen it |

Define W as an edge from a non-static or ZERO endpoint to a named static.
Define R as the reverse endpoint kinds, and B as named static to named static. The current anchor
also accepts an EXACT class marker. An endpoint with broad STATIC base but
no valid anchor does not become a non-static endpoint. Keep all these current
classification checks before normalization.

Canonical paths and exclusions remain immutable. A geometry hash key contains
all normalized endpoint geometry, including tail kind and field exclusion.
No owner, scope or exit is removed from an attachment key.

## 5. Encode exact labels and typed terminals

W/R rows can have a real ZERO endpoint. Pack the **actual endpoint mark
slots**, as `StaticWriteKeyInterner` already does. Do not pack the nullable
`GuidanceMarks.Mapped` fields as a replacement for these slots.

```kotlin
fun code(mark: TaintMark): Long = mark.id.toLong() + 1L
fun packBoundaryEndpoints(a: Pattern, b: Pattern): Long =
    if (a.fact.mark is MarkSlot.Star && b.fact.mark is MarkSlot.Star) 0L
    else (code(concreteMark(a)) shl 32) or
         (code(concreteMark(b)) and 0xffff_ffffL)

fun relation(a: Pattern, b: Pattern): GuidanceMarks =
    if (a.fact.mark is MarkSlot.Star) GuidanceMarks.Flow
    else GuidanceMarks.Mapped(
        if (a.fact.base == Zero) null else concreteMark(a),
        if (b.fact.base == Zero) null else concreteMark(b))
```

A mapped word stores both full slot IDs, including the concrete control ZERO
slot. Each code is nonzero, so it cannot collide with FLOW word `0`. Decode the
actual slots first; then derive nullable data-mark endpoints from the typed
bases. A null `GuidanceMarks` endpoint is not itself a runtime fact or mark.
The old mixed FLOW/concrete rejection remains an eager ingestion check.

This preserves both callback forms: mark-free geometry, including ZERO,
for `mappedGeometryAllowed`; full endpoint Patterns for W/R `keep` callbacks
and returned rows. No caller receives a metadata-only ZERO/STAR Pattern as
an actual value. Reuse the current mark-ID bounds and test native bitwise
round trips, including the control ZERO ID and maximum legal IDs.

Keep current FULL/GROUP selector policy; this representation change does not
repair or remove GROUP mode. B keeps its current label codec and owner graph.

Terminal inputs use a separate typed array. They have one static input mark
and no AP output. Preserve only the old anonymous DEMAND terminal attachment.
`NormalTarget(id)`, local/non-static terminal rows and real ZERO inputs keep
their current handoff rules; this catalog grants them no new static attachment.

```kotlin
fun addTarget(owner: OwnedScope, exit: PortId, initial: InitialAp) {
    registerProducerAsBefore(owner, exit)
    val p = initial.toPattern()
    if (!sameTargetDomainAndStaticAnchorAsBefore(p)) return
    check(p.fact.mark is MarkSlot.Concrete)
    val normalized = guidancePattern(p)
    terminals(owner, exit).addFirstOccurrence(
        endpointPool.intern(metadataOf(normalized)), concreteMark(normalized))
}
```

Never turn `C.f/T -> DemandTarget` into `C.f/T -> Zero`. Never interpret
`Zero -> C.f/T` as a terminal input. The label and endpoint types make this
separation explicit.

## 6. Reuse query plans and materialize selected values

`FrozenCompletion`, `StaticDemandView`, `C5StaticDemandView`,
`StaticPairLookup` and `UnionStaticDemandView` retain their contracts.
Replace only the W/R and terminal backing row access.

```kotlin
interface PackedRowsRead {
    val size: Int
    fun geometry(ordinal: Int): BoundaryGeometry
    fun marks(ordinal: Int): GuidanceMarks
    fun from(ordinal: Int): Pattern       // Marked endpoint, created on demand.
    fun to(ordinal: Int): Pattern
    fun edge(ordinal: Int): StaticGuidanceEdge
}

// The same candidate order, geometry groups and label selectors.
for (id in boundaryDirectory.ids(base, path, prefixesOnly, query)) {
    checkpoint()
    val row = packedRows.cursor(id)
    val marks = row.marks()
    val from = row.from()
    val to = row.to()
    if (keep == null || keep.keep(from, to, marks))
        yield(StaticGuidanceEdge(from, to, marks))
}
```

W/R `keep` callbacks currently receive full marked Patterns. Preserve that.
B callbacks currently receive private geometry plus separate mark metadata;
preserve that too. Do not replace one callback contract with the other.
Selected candidates can need marked endpoint objects even when `keep` rejects
them. The saving is that the whole relation is not a standing rich catalog.
Only accepted results need a `StaticGuidanceEdge` object.

| Query operation | Required unchanged behavior |
| --- | --- |
| `targetInputs` | Same normalized terminal inputs and first-insertion order |
| `entries` | Same geometry/mark selection, local W/R choice, B projections and owner checks |
| `targets`, selected/filtered targets | Same candidate ordinals, prefix policy, callback arguments/order and accepted rows |
| `flowTargets` | Same FLOW-only family and row sequence |
| `pairs` | Same separate W/R row-ID domains and source/target intersection |
| `incoming`, selected/filtered incoming | Same B-before-W order, label selection and callback short circuit |
| `outgoing` | Same B FLOW-start query; no new W/R result family |
| `markedOutputs` | Same exact/GROUP selectors, coverage checks and owner visibility |
| `estimatedMarkedOutputs` | Same index count, including existing conservative estimates before visibility |
| `hasMarkedOutput` | Same joins and first accepted result; no FLOW-as-concrete replacement |
| `hasComposedEndpoints`, selected/filtered variants | Same two-endpoint envelope and callback behavior |
| `visitPossibleTargets` | Same full entry Pattern/boolean stream and immediate false return |
| `mayNeedInheritedEntries/Pairs` | Same conservative flags and local-versus-visible distinction |
| `scopedViews`, `selectExit` | Same reversed producer scope, exact selected exit, empty entered ports and union order |

Build `BoundaryDirectory`, source indexes, `StaticOutputOrdinals`, selector
postings and projected entry indexes in the old ordinal order. Adapt their
builders to field readers; do not first call `map(edge)` over the catalog. Geometry groups follow first occurrence
inside each owner bucket, not global geometry-ID order. For example, if the
pool has `[G1,G2]` but one owner first stores `[G2,G1]`, its query group order
remains `[G2,G1]`. Preserve the current sorted original label ordinals,
unknown-selector fallback and exact/GROUP posting merges.
For entry projection, deduplicate `(endpointGeometryId, mark)` in the same
first-occurrence order as the old marked `Pattern.distinct()`.

`StaticPairLookup` stays unchanged. Its BFS receives the same ordered row
streams, so it has the same visited edges, mark composition, endpoint joins,
coverage stop and real-ZERO handling. This is stronger than set equality:
early-stop callbacks and bounded query traversal are preserved too.

## 7. Ownership, statistics and freeze

Root W/R and terminals use the full `MethodKey`. Scoped attachments also keep
the full `ScopedSummaryKey`, including producer entry and exit. Reuse the
current scoped reverse-key adapter. `STATIC_SHORTCUT`, `ROOT_EXIT`, feedback
ports, normal exits and exception ports remain distinct.

Only B owner visibility uses the current `CommonMethod` family. Shared
geometry does not grant a row to another method context or scope.

```kotlin
class CatalogStatistics { // One instance for the entire FrozenCompletion.
    val ownerQueries = existingOwnerQueryCounters
    val storedWRows: Long
    val storedRRows: Long
    val terminalMemberships: Long
    val geometryCount: Int
    val primitiveRowCells: Long
    val materializedQueryRows: Long // Optional statistics only.
}
```

Keep old logical `writerAttachments`, `readerAttachments`, terminal counts,
B owner memberships, projected-entry counts and entered-port counts. Count
memberships, not only distinct global geometry. All root/scoped/selected
views share the same snapshot counter owner. Do not sum the full catalog
again when a new view is created. Timing and allocation counters can differ;
the logical relation counts must match the old builder.

Discard builder-only hash maps and dedup sets after freeze. Keep the geometry
arrays, primitive memberships and read indexes. Publish only after the old
successful join/binding barrier. Cancellation produces no partial completion.

## 8. Examples and failure checks

```java
// Configured source rules at remap(a):
// CM(a,T) -> assign U to C.f; CM(a,V) -> assign W to C.f.
void root(Box a) {
    remap(a);
    sinkU(C.f);
}
```

For rows `a/T -> C.f/U` and `a/V -> C.f/W` with equal geometry, store two
ordered labels `(T,U)` and `(V,W)`. Do not store independent input/output
mark sets; that would invent `(T,W)` and `(V,U)`.

```java
void set() { C.f = sourceT(); }
void read() { sinkT(C.f); }
```

Keep the writer `Zero -> C.f/T` and terminal input `C.f/T` as different typed
entries. The static path still composes to the existing `Zero -> Target`
guidance through the unchanged lookup. No new ZERO permission is inferred.

```java
void set(Box p) {
    C.f = p;
    // Exit rule clears C.f before its exported summary.
}
```

The lost/pre-exit raw writer is not in the common summary. Keep it as an
extra catalog input after the current prune. Binding still uses the actual
caller/local input and raw FLOW exclusions before guidance normalization.
The compact catalog does not replace that binder input with a guessed mark.

For a scoped raw write, producer exit `STATIC_SHORTCUT` remains that port.
A genuine completed source result uses `ROOT_EXIT`. They cannot merge solely
because their endpoint Patterns match.

## 9. Proof scope and remaining implementation obligations

The finite model has an executable geometry interner and catalog compiler.
For every finite input sequence, decoding the compiled catalog returns the
**same complete ordered rows**. It preserves full owners, all endpoint
metadata, exact mark pairs and typed terminals.

The model proves query-stream equality for every old ordered candidate plan
and executable keep predicate. It proves equality of early-stop callback
traces and all finite composition prefixes that use that oracle. It also
proves radix-pair round trips/bounds, no fabricated mark cross-product,
exact port reversal and a metadata/reference allocation-unit saving.

The model does not prove the AP normalizer, Kotlin trie/index builders,
bitwise JVM adapter, source-domain filters, callback purity, cancellation
latency, byte savings, GC release or whole-driver convergence. The index
migration must pass differential native tests against the reference builder.
Do not call the Kotlin adapter proved before those gates pass.

## 10. Source migration

| Source | Planned edit |
| --- | --- |
| New `store/PackedGuidanceCatalog.kt` | Exact normalized geometry, primitive W/R rows, terminal rows, builder dedup and immutable catalog |
| `store/StaticGuidance.kt` | Replace rich attachment/terminal sets and lists; use packed field readers for existing indexes/views |
| `engine/JoinedStaticGuidance.kt` | Consume point-1 detached inventory in the old order; send bound extras to the packed builder |
| `RunSummaryStore`/scoped exports | Use the point-1 seal/transfer contract; do not add another raw-fact store |
| `StaticSelectorIndex.kt` | Reuse selector semantics; change only builder input access if needed |
| `StaticPairLookup.kt`, `C5StaticDemandView.kt`, `UnionStaticDemandView.kt` | No semantic or graph-walk change |
| `KilledStaticWriteStore.kt`, `OwnedJoinedStaticWriterBinding.kt` | Reuse current prune and AP binding; do not change their candidate/permission laws |

Remove the old W/R `LinkedHashSet<StaticGuidanceEdge>` builder fields, rich
`writerRows/readerRows` lists and marked terminal lists only after differential
controls cover their replacements. Keep the existing B geometry/owner graph.
No new weak cache, reference manager, field policy or static algorithm is needed.

## 11. Implementation and verification plan

1. Keep the current builder available as a test reference. Model the detached
   catalog first; run its constructive and axiom checks before Kotlin edits.
2. Add the catalog/codec and terminal types. Add RED tests for typed ZERO,
   crossed mark pairs, exact field exclusions and full context/port isolation.
3. Adapt attachment and projected-entry indexes to field readers. Compare all
   query operations above, including ordered callbacks and false short circuit.
4. Replace rich W/R/terminal builder sets. Keep B, pruning and binding unchanged.
5. Integrate the point-1 sealed inventories after execution release. Add a
   reachability/lifetime control that rejects actor/service capture.
6. Run whole handoff/driver controls and the four fixed project experiments.
   Do not accept a faster result that loses an identity or lacks an accepted run.

Required native differential cells include FULL and GROUP labels, diagonal
FLOW, mapped T/U, real ZERO on either legal endpoint, static class markers,
STAR/EXACT/ANY/MUST normalization, nonempty field/mark exclusions at the raw
adapter, repeated normalized seeds, context/scoped producer ports, private B,
lost pre-exit writes, caller-bound extra rows, terminal versus DATA ZERO,
multiple scoped exits, owner graph cycles and owners outside the prescan graph.

Compare complete sequences for `entries/targets/flowTargets/pairs/incoming/
outgoing/markedOutputs/targetInputs`; compare booleans, estimates, callback
traces, scoped view keys, logical counters and final composed demand rows.
Include incomplete/cancelled construction: it must not publish a catalog.

Measure builder/final geometry and row counts, primitive capacities, rich
query materializations, catalog heap, peak across bind/freeze and post-release
GC occupancy. Compare the same query outputs and final project identities.
The allocation-unit proof does not set a promised percentage of the measured
1.37 GB builder. Extra output rows and required native stores can still dominate.

No Kotlin file, analyzer run or project measurement is changed by this design.

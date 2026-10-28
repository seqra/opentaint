# Demand storage and predefined summaries: implementation proposal

Date: 28 October 2026. Status: proposal only. Do not change runtime code in this task.

This proposal implements [demand storage and Spring cleanup](../../spec/demand-storage-and-spring-cleanup.md)
and [demand lookup](../../spec/demand-storage-lookup.md). It follows
[impl-proposal-guide.md](../../spec/impl-proposal-guide.md) and
[proof-guide.md](../../spec/proof-guide.md). Kotlin is pseudocode unless a
section names an existing function.

Source reviewed: `6d5bd83216c16f3755391c149b3a6bfacdeea106`.
The latest [measured runtime](../reports/bidirectional-restricted-demand-performance-20261028.md)
is `53991b7483b062b0287152130cbbbfc87623093b`:

| Project | Latest reached | Latest complete | Accepted forward report |
|---|---|---|---|
| OWASP | run-12 | run-11 | run-11 |
| conductor | run-4 | run-3 | run-3 |
| thingsboard | run-2 | run-1 | run-1 |
| Stirling-PDF | run-5 | run-4 | run-3 |

No new analyzer run was made for this proposal. Do not use these measurements
as results for the proposed code.

## 1. Selected changes and fixed behavior

| Part | Current implementation | Proposed implementation | Semantic scope |
|---|---|---|---|
| C2 initial admission | `DemandStore.near` constructs paired candidates, including paired static walks; the actor uses their entries | `DemandStorage.initials` uses a distinct entry index and query-directed static existence search | Same original AP C2 results |
| C5 summary restriction | `covering` returns paired candidates; the actor applies restriction | `DemandStorage.intersect` selects complete pairs and applies AP restriction | Same original AP C5 results, layers and protection |
| Static lookup | Both consumers use `FrozenStaticCompletion.lookup` | Direct local rows, local composition, then visible callee rows; two-frontier C2, labelled paired C5 | Same frozen demand relation |
| Generated cleanup | Save registry fields, call a blanket cleaner, restore registry fields | Apply a complete predefined registry-preserving model | New trusted model; same concrete save/clear/restore value effect |
| Predefined method body | A normal callee can get an analyzer and defaults | A predefined model is always complete; create no method analyzer; add no default or unresolved fallback for that target | Selected model boundary |
| Predefined method rules | A cleanup ZERO analyzer can evaluate method entry/exit rules | Skip method entry and exit rules for predefined methods | **Explicit user-selected semantic change** |

The last row is intentional. For example, a generic method-exit sink with
condition `true` no longer reports inside modeled cleanup. Call-site rules
still run. Controller entry and exit rules still run because controllers
have no predefined model. Do not add a boundary observer to recover the
removed method-boundary observations.

Keep these parts unchanged:

```text
AP emit/restrict tables; actual-input mark gates; field limits and transfer
abstract STAR demand E normalization; actual/concrete/native E
FULL/GROUP selectors; FLOW mark exclusions mx; protection transport
native NORMAL persistence; demand selection; whole original ND premise
run-1 abstraction and requests; immediate static write supply
joined caller binding; run-1 static summary suppression; static pool rules
ordinary alias handling; source/sink identities outside predefined boundaries
backward summary bypass only when the ORIGINAL premise is ZERO
```

Run-1 has no ND summary. A later forward run can have one. A backward run
has no ND premise. Do not introduce StrongQueries, grounding support, a new
cache policy, writer replay changes, or IR storage changes.

Do not add fields to `MethodKey`, `InitialAp`, rule occurrence identities or
ordinary fact equality. `TaintTree.equals` omits protection. Handle that
annotation in the query result accumulator, not in a global equality change.

## 2. Code map and ownership

Use these source roots:

```text
B = core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi
J = core/opentaint-dataflow-core/opentaint-jvm-dataflow/src/main/kotlin/org/opentaint/dataflow/jvm/bidi
S = core/src/main/kotlin/org/opentaint/jvm/sast/project/spring
```

| File or component | Change |
|---|---|
| `B/store/DemandStore.kt` | Replace paired consumer API with `DemandStorage.initials/intersect`; keep builder validation |
| `B/store/PathTrie.kt` | Add a read-only sealed view and callback visits if needed; preserve prefix/extension semantics |
| `B/store/StaticGuidance.kt` | Keep seed capture, geometry/label packing and owner sets; expose immutable primitive indexes |
| New `B/store/StaticEntryLookup.kt` | Implement staged C2 and compatible-T two-frontier search |
| New `B/store/StaticPairLookup.kt` | Implement staged C5 paired walk |
| New `B/store/DemandResultCoverage.kt` | Implement exact initial-key bounds and conservative summary coverage |
| `B/engine/RunMethodAnalyzer.kt` | Replace C2/C5 consumer loops; retain limiting, validation, raw storage and publication ownership |
| `B/driver/HandOff.kt`, `IterationDriver.kt` | Build/seal demand during the existing transition; preserve seed/report/persistence order |
| New `B/interp/PredefinedSummaries.kt` | Define complete models, schemas and provider contract |
| `B/interp/CallPlan.kt`, `B/engine/RunMethodCallServices.kt` | Add a known-model stage; execute without a callee actor or subscription |
| `J/interp/JIRCallPlanBuilder.kt` | Separate predefined targets from analyzed targets before entrypoint resolution |
| `J/interp/JIRMethodEntries.kt`, JVM prescan | Read model effects; skip modeled body and method-boundary rule collection |
| `S/SpringWebProject.kt` | Select new-core cleanup generation; remove save/restore only on that path |
| `S/SpringGeneratedMethod.kt`, `SpringRuleProvider.kt` | Register the actual cleanup model; remove both cleanup cleaner routes on the modeled path |

The demand snapshot owns immutable AP data and detached graph data only.
It owns no analyzer, runner, subscription, caller input store, statement
worklist or mutable summary store. A query owns its temporary queues and
visited sets. The AP manager keeps its existing interning ownership.

The model provider owns immutable method-model descriptions. The call planner
compiles them with the current AP manager. The caller executes them. There is
no modeled-method `SummaryStorage`, `MethodEdgeStore` or rule worklist.

## 3. Demand relation and storage

### 3.1 Reference relation

Keep a reference relation independent of the optimized query:

```text
W: ordinary or genuine ZERO -> static
B: static -> static
R: static -> ordinary

D(M) = ordinary inferred demand
     + implicit ZERO and same-actual-static-carry families
     + direct local W/R and own B projections
     + visible inherited B projections
     + valid static-middle compositions of frozen W/B/R
```

For a forward seed `a -> b`, its demand pair is `(Dc=b, Dp=a)`.
W/R belong to complete `MethodKey` M. Own B belongs to `M.method`, including
the existing same-method rows from other contexts. Inherited B is visible if
its owner is a transitively reachable **callee** of M. Keep the current
outside-graph exact-owner rule. Test ownership per geometry-and-label row.

Static graph positions include named fields and the existing legal EXACT
global class markers. Root/class FLOW carry is a separate implicit family.
Reuse `staticAnchor`; do not reduce static positions to fields only.

Attach this skipped-static relation only to incoming run-2. Later snapshots
use their new inferred demand. Same-actual-static-carry is a demand family,
not an executable identity which can bypass a complete cleanup model.

The special logic is exclusive to run-1-to-run-2: build its indexes at that
transition and query them lazily during run-2. For run-3 and all later runs,
both API operations use direct method-local demand only, including static
demand rows. Do not run either local composition BFS or call-graph lookup.
Do not retain W/B/R indexes or shared static carry in these later snapshots.

### 3.2 Public API and builder

```kotlin
class DemandStorage private constructor(
    private val explicit: Map<MethodKey, MethodDemandIndex>,
    private val skipped: StaticDemandIndex?,
    private val sharedStaticCarry: Boolean,
    private val ap: ApOps,
) {
    fun initials(method: MethodKey, boundedActual: Facts): Set<InitialAp>
    fun intersect(method: MethodKey, raw: SummaryCandidate): List<SummaryCandidate>

    class Builder(private val ap: ApManager) {
        fun add(method: MethodKey, pair: DemandPattern): Boolean
        fun attachSkippedStatics(index: StaticDemandIndex)
        fun enableSameActualStaticCarry()
        fun seal(): DemandStorage
    }
}

data class SummaryCandidate(val premise: PremiseKey, val conclusion: Facts)
```

Keep the current `DemandStore.Builder.add` checks. Copy/own path data and
normalize with `guidancePattern` at the existing projection boundary:

```text
abstract STAR demand: E becomes empty; mark exclusions become empty
concrete STAR demand: keep E
MUST endpoint: existing guidance conversion to ANY
CleanerTemporary: reject
illegal demand tail/mark combination: reject as now
native records: do not normalize or move them through this builder
```

The AP emitter and reducer do not need a separate store mode. Keep the active
mode at the actor/AP call boundary. If the final API stores next-run mode as
metadata, compute it once with `IterationPolicy`; do not call a configurable
field-limit policy twice or add a second field-limit rule.

### 3.3 Explicit indexes

```kotlin
class MethodDemandIndex(
    val entries: ImmutableRows<Pattern>,       // EntryId -> complete Dc
    val entriesByLocation: ReadOnlyPathTrie<EntryId>,
    val pairs: ImmutableRows<DemandPattern>,  // PairId -> correlated Dc,Dp
    val pairsByEntry: ReadOnlyPathTrie<PairId>,
    val pairsByExit: ReadOnlyPathTrie<PairId>, // absent Dp is not indexed here
)

fun addOwnedPair(pair: DemandPattern) {
    val entryId = entries.intern(pair.entry)
    entriesByLocation.addOnce(location(pair.entry), entryId)
    val pairId = pairs.intern(pair)
    pairsByEntry.addOnce(location(pair.entry), pairId)
    pair.exit?.let { pairsByExit.addOnce(location(it), pairId) }
}
```

Entry identity includes base, full path, tail, E and selector. Several Dp
values can share one EntryId. Pair identity includes both complete patterns.
Do not use an entry/exit cross product. Keep the IDs local to their immutable
index. A missing Dp still admits an entry but cannot keep a C5 output.

Seal the builder once. Transfer owned rows or copy them, then discard mutable
builder directories. Expose no `PathTrie.add` through the read view. Do not
retain both builder maps and frozen duplicates for the run lifetime.

### 3.4 Static indexes

The current `FrozenStaticCompletion` has bridge-target adjacency only. Add
the following indexes over the same immutable seed rows:

```kotlin
class StaticDemandIndex(
    val writers: Map<MethodKey, LocalWriterIndex>,
    val readers: Map<MethodKey, LocalReaderIndex>,
    val bridgeRows: SharedBridgeRows, // existing geometry + packed labels + owners
    val ownBridges: Map<CommonMethod, BridgeRowIds>,
    val flowByInput: EndpointIndex<BridgeRowId>,
    val flowByOutput: EndpointIndex<BridgeRowId>,
    val allByOutput: EndpointIndex<BridgeRowId>, // C5 and direct B targets
    val allByInput: EndpointIndex<BridgeRowId>,  // C5 source envelope
    val markedBridgeOutputs: SelectorOutputIndex<BridgeRowId>,
    val targetGeometryEnvelope: TargetGeometryIndex,
    val graph: DetachedStaticCallGraph,
)

class LocalWriterIndex {
    val byOutput: EndpointIndex<WriterId>
    val byInput: EndpointIndex<WriterId>
    val markedOutputs: SelectorOutputIndex<WriterId>
}
```

Build reader target indexes for all labels and for FLOW only. Share geometry
rows; indexes store row IDs. Keep packed B labels and their separate owner
lists. Do not copy B into every caller. References in `ownBridges` use common
method ownership, not complete-context W/R ownership.

`SelectorOutputIndex` has exact-FULL and GROUP selector buckets. For actual
full T, probe the exact-T bucket and its existing `MarkTable.groupOf(T)` bucket,
then call `coversAtom(outputSelector, T)`. Do not call `MarkTable.group()` to
create hypothetical group atoms. Do not enumerate known members or bind rules.

The target envelope keeps the geometry and row family needed for coverage.
A mapped-only EXACT target must not acquire an abstract EXACT/FLOW entry.
The envelope can ignore visibility conservatively; actual candidate emission
cannot ignore it.

### 3.5 Local view over explicit and seed rows

The local view combines index references. Do not copy seed projections into
every explicit method table. Use tagged row references when intersecting IDs
from several backing indexes:

```kotlin
sealed interface LocalPairRef {
    class Explicit(val id: PairId) : LocalPairRef
    class Writer(val id: WriterId) : LocalPairRef
    class Reader(val id: ReaderId) : LocalPairRef
    class OwnBridge(val id: BridgeRowId) : LocalPairRef
}

fun localView(M): LocalDemandView = LocalDemandView(
    explicit[M], writers[M], readers[M], ownBridges[M.method],
)
```

The view exposes `entryCandidates`, `pairsByEntry`, `pairsByExit` and row
access. Its pair indexes return the same tagged reference for the same seed
row; an Explicit PairId cannot collide with a BridgeRowId. A seed projection
reads Dc from the forward target and Dp from the source. C2 reads only Dc;
it does not allocate a DemandPattern for each seed. C5 materializes the pair
after candidate-ID intersection. Implicit ZERO/carry remain direct families.
This establishes the required primitive local coverage for every M, including
a MethodKey first queried after sealing.

## 4. Snapshot build and actor integration

```kotlin
// Existing completed-run barrier; retain this order.
fun barrier(config, result, report): Next {
    require(result.status == COMPLETE)
    if (config.forward) report.add(config, result)
    records.persist(config.direction, result.nativeSummaryStores())

    val builder = DemandStorage.Builder(shared.ap)
    forEachExistingSelectedDemand(result) { owner, premise, piece ->
        addExistingDirectionalProjection(builder, owner, premise, piece)
    }
    if (config.run1) {
        // Real runs supply the joined, pre-release frozen inventory.
        builder.attachSkippedStatics(checkNotNull(result.staticCompletion).asIndex())
        builder.enableSameActualStaticCarry()
    }
    val handoff = HandOff(builder.seal(), existingSeedCapture(result, report))
    return existingStopDecisionOrNextConfig(config, result, handoff, report)
}
```

Keep the existing local-seed fallback for synthetic test `RunResult` values
which have no runner-owned joined phase. Do not use it for real runs. Joined
caller binding still finishes before live N2/caller stores are released.
The transition builds indexes; it does not enumerate composed static paths.

Do not add a native-record transaction or rollback mechanism. If sealing is
cancelled, expose no partial DemandStorage and start no next run. Keep the
current barrier failure and accepted-report policy.

Replace the restricted branch in `RunMethodAnalyzer.addLink`:

```kotlin
ops.limit(added, limit, object : ApOut {
    override fun result(bounded: Facts) {
        for (leaf in ops.leaves(bounded)) {
            if (checkRun2StaticAnchors) validateRun2StaticFullInput(ap, leaf)
        }
        for (initial in config.demand!!.initials(key, bounded)) addInitial(initial)
    }
    override fun markRequest(mark: TaintMark) = error("A field cut cannot request a mark")
})
```

Keep run-1 `Run1Abstraction.emit` unchanged. Keep actual-input validation and
the existing initial-fact store. The demand storage returns permitted initials;
it does not start, store or enqueue them itself.

Replace `RunMethodAnalyzer.published` only after raw summary admission:

```kotlin
fun published(original: PremiseKey, raw: Facts): List<Facts> = when {
    config.run1 -> listOf(raw)
    !forward && original.isZero -> listOf(raw)
    else -> config.demand!!.intersect(key, SummaryCandidate(original, raw))
        .map { it.conclusion }
}
```

Keep `retainSummary`, demand selection, native persistence and publication
batching in their existing owners. A ZERO conclusion does not trigger the
backward bypass. A restricted result always retains the whole original premise.

## 5. C2: actual fact to initial facts

### 5.1 Three stages for the whole packet

```kotlin
fun initials(M: MethodKey, A: Facts): Set<InitialAp> {
    val q = InitialQuery(M, A, localView(M), skipped)
    q.emitAllDirectLocal() // all leaves, ordinary + direct W/R/own B + implicit
    if (skipped == null) return q.results // run-3 onward: direct local only
    if (q.fullyCovered()) return q.results

    q.searchLocalCompositions()
    if (q.fullyCovered() || !q.mayNeedInheritedRows()) return q.results

    q.searchVisibleCompositions() // restart is allowed; see 5.5
    return q.results
}

fun InitialQuery.offer(entry: Pattern) {
    if (!offeredEntries.add(entry)) return
    results += ops.emit(DemandPattern(entry, null), actualPacket)
}
```

`localView(M)` references frozen seeds; it does not duplicate their payloads.
Direct local admission must finish for all actual leaves before a static BFS
starts. A nonempty result is not full coverage.

Use the selected guards:

```text
nonstatic actual FLOW: local only
static actual FLOW: local + eligible direct visible FLOW B targets; no color BFS
nonstatic actual T: color BFS only for matching local FLOW R targets
static actual T: inspect eligible direct B targets; color BFS for FLOW targets
mapped rightmost R/B: offer its conclusion selector directly
FLOW rightmost R/B: offer abstract entry, then test the actual T if still needed
```

Use same-base ancestor/descendant location candidates. Full AP tests decide
tail, E and marks. A concrete demand cannot emit T from actual FLOW.

### 5.2 Result coverage without speculative interning

```kotlin
data class PotentialInitialKey(
    val base: AccessPathBase,
    val path: ImmutablePath,
    val tail: Tail,
    val exclusion: ExclusionSet,
    val mark: MarkSlot,
)

fun InitialQuery.fullyCovered(): Boolean =
    targetEnvelope.visitPossibleKeys(actualPacket) { potential ->
        potential in structuralKeysOfRealResults
    } // false at the first uncovered possible key
```

For each candidate target geometry, consider its legal FLOW entry family and
its compatible actual-mark entry family. Use the scalar `Reference.emit` to
compute possible result Patterns. It performs the current AP intersection
without `ApManager.initial`. Compare structural keys to real returned initials.
Do not use InitialAp object identity for hypothetical keys. Do not intern a
mark, path node or initial solely to test this bound.

Include ordinary/implicit endpoints and possible inherited B targets. Ignore
visibility in this bound if needed; that only delays stopping. Do not add an
abstract entry for a mapped-only EXACT target. Keep the complete result path,
tail and E, including any descent/rebase performed by AP emission.

```text
A = ret.* / T
possible result keys = { I(ret.* / FLOW), I(ret.* / T) }
direct local results = both keys
=> return before local BFS or call-graph work

A = C.g.* / T
local keys = STAR/FLOW and STAR/T
possible inherited target = C.g.$ / T
=> local keys do not cover the EXACT result; continue
```

Memoize only query-local facts about this bound. Keep a streaming immutable
endpoint view; do not build all method/static/mark combinations at seal time.
If the bound cannot prove coverage, exhaust the eligible search.

### 5.3 Two-frontier query for one actual T

For a FLOW reader, ask:

```text
Is there a local marked W or eligible marked B whose output accepts T,
followed by zero or more FLOW B transfers into the reader input?
```

Apply the same procedure to a FLOW B used as the rightmost target.

```kotlin
fun joins(output: Geometry, input: Geometry): Boolean =
    staticAnchor(output) == staticAnchor(input) && existingGeometryOverlap(output, input)

fun forwardNext(output: Geometry, scope): Sequence<Geometry> =
    flowByInput.around(output).filter { eligible(it, M, scope) && joins(output, it.from) }
        .map { it.to }

fun backwardNext(input: Geometry, scope): Sequence<Geometry> =
    flowByOutput.around(input).filter { eligible(it, M, scope) && joins(it.to, input) }
        .map { it.from }
```

Forward states are output geometries. Backward states are input geometries.
Each step crosses one real FLOW B. The meeting test is one directed
output-to-input join. Geometric overlap is not a transitive transfer.

```kotlin
fun existsT(targetInput: Geometry, T: TaintMark, scope: Scope): Boolean {
    val fwd = OutputFrontier()
    val back = InputFrontier()
    val roots = markedOutputs(M, T, scope).lazyCursor()
    back.admit(targetInput)

    while (roots.hasPending() || fwd.hasWork() || back.hasWork()) {
        checkpoint()
        roots.admitNextIfAny { root ->
            if (back.hasJoinFrom(root.output)) return true
            fwd.admit(root.output)
        }
        if (!fwd.hasWork() && !back.hasWork()) continue
        val side = chooseNonemptySideWithLessEstimatedWork(fwd, back)
        for (next in side.expandOneFifo(scope)) {
            if (side.oppositeHasDirectedJoin(next)) return true
            side.admit(next)
        }
    }
    return false // complete only for this scope
}
```

The lambda return denotes immediate search completion in this pseudocode.
Implement it with an explicit result value if the Kotlin callback is not
inline. Check opposite **visited** states, not just pending queue entries.
At each backward input, first probe the eligible marked-output index at that
location. This can find a root without materializing all producers of T.

```text
W p/T -> C.a/T; FLOW B C.a -> C.b; FLOW B C.b -> C.c; FLOW R C.c -> ret
forward C.b output meets backward C.b input
=> offer ret/T; AP emits the T initial from actual ret/T
```

Mapped edges are roots only, not transfer steps:

```text
W p/T -> C.a/T; mapped B C.a/T -> C.b/U; FLOW R C.b -> ret
actual ret/T: this branch has no T witness
actual ret/U: B's output is a U root and supplies the witness
```

Do not walk through the mapped B to claim that its old input T reaches ret.
A genuine `ZERO -> C.a/T` W is a valid root. Its private ZERO input is not a
runtime full mark.

Deduplicate complete geometry states per side, including anchor, full bounded
chain, tail and E. Root state identity does not include its original source or
input mark: C2 needs the existence of an output T, not all origin products.
Keep a constructive path witness in the formal/debug adapter; the production
query need not retain every path.

### 5.4 Visibility and exhaustion

```kotlin
fun eligible(row: BridgeRowId, M: MethodKey, scope: Scope): Boolean =
    when (scope) {
        LOCAL -> row.owners.contains(M.method)
        VISIBLE -> row.owners.outsideGraph.contains(M.method) ||
            queryReachability.reachesAny(row.owners.graphIds)
    }
```

Initialize `queryReachability` only when the visible stage starts. Its root is
the original querying M, even when a path crosses rows owned by other methods.
Do not re-root reachability at the current B owner.

A local false answer means `LOCAL_NOT_FOUND`. Return a final false answer only
after complete eligible root/adjacency coverage in VISIBLE scope. A complete
backward closure plus negative producer probes, or a complete forward closure
with all roots and no meeting, can certify early absence. An empty queue with
unexamined roots cannot do so. A first valid witness can always stop this
target/key query.

### 5.5 Stage implementation choice

Use a **fresh visible search** in the first implementation. This is the
simplest selected adapter: retain output results, discard local query queues,
then search the full visible relation with fresh visited sets if still needed.
It repeats at most the local search for that query; it cannot hide newly
enabled inherited adjacency behind local visited bits.

Keep the primary spec's state-preserving alternative for a later measured
implementation change. That alternative needs separate local/inherited
expansion bits and must reactivate old states. Do not implement it implicitly.

The visible search uses both own and inherited B links. It must handle:

```text
local W -> inherited B -> own B -> inherited B -> local R
```

Also admit direct inherited B targets, including mapped EXACT targets. A
Boolean search around an existing local R does not discover a missing target.

## 6. C5: raw summary to restricted summaries

### 6.1 Local pair selection and exact result accumulation

```kotlin
fun intersect(M: MethodKey, raw: SummaryCandidate): List<SummaryCandidate> {
    val out = ExactProtectedResults(ap.manager)
    val local = localView(M)
    for (j in raw.premise.members) {
        for (id in intersectIds(
            local.pairsByEntry.prefixes(j.location),
            local.pairsByExit.aroundAllLeaves(raw.conclusion),
        )) offer(j, local.pairs[id], raw.conclusion, out)
        offerImplicitCarry(j, raw.conclusion, out)
    }
    if (skipped == null) return out.withOriginal(raw.premise) // run-3 onward
    if (summaryCovered(raw.conclusion, out)) return out.withOriginal(raw.premise)

    walkPairs(M, raw, LOCAL, out)
    if (!summaryCovered(raw.conclusion, out) && mayNeedInheritedPairs(M, raw))
        walkPairs(M, raw, VISIBLE, out) // fresh search, same output accumulator
    return out.withOriginal(raw.premise)
}

fun offer(j, pair, G, out) {
    for (kept in ops.restrict(j, G, pair)) out.add(kept)
}

class ExactProtectedResults(private val manager: ApManager) {
    private val values = LinkedHashMap<Facts, Facts>()
    fun add(f: Facts) {
        val old = values[f] // existing ordinary payload equality
        values[f] = if (old == null) f else unionProtectionOnly(old, f)
    }
}
```

`unionProtectionOnly` retains the exact ordinary payload and ORs the
`TaintTree.nonSubsumable` mask. Reuse `ApManager.mergeAddDelta` only for the
already-equal payload case after checking its exact geometry/header contract.
Do not use `ConclusionGroup`: it can merge or compact different payloads.
FLOW/REACH have no TAINT protection mask to join.

The two positional indexes only intersect **PairIds**. Then AP tests complete
whole-member containment in Dc and output intersection with the same Dp.
Apply this for each j but reattach the whole original J. Null Dp keeps no
output. Do not require the whole J to fit one scalar Dc.

### 6.2 Paired BFS

```kotlin
data class PairState(val from: Pattern, val target: Pattern, val label: GuidanceMarks)

fun walkPairs(M, raw, scope, out) {
    for (j in raw.premise.members) {
        if (!pairEndpointGuard(M, j, raw.conclusion)) continue
        val pending = ArrayDeque<PairState>()
        val seen = HashSet<PairState>()
        fun admit(s: PairState) { if (seen.add(s)) pending.addLast(s) }
        for (last in matchingReadersAndBridges(M, j, scope)) admit(stateOf(last))
        while (pending.isNotEmpty()) {
            checkpoint()
            val s = pending.removeFirst()
            offer(j, DemandPattern(s.target, s.from), raw.conclusion, out)
            if (summaryCovered(raw.conclusion, out)) return
            if (s.from.fact.base != STATIC) continue
            for (left in incomingWritersAndBridges(M, s.from, scope)) {
                if (!joins(left.to, s.from)) continue
                val relation = composeMarks(left.marks, s.label) ?: continue
                admit(canonicalState(left.from, s.target, relation))
            }
        }
    }
}
```

Traverse mapped as well as FLOW prefixes. Keep complete source/target
patterns and symbolic mark relation. After composition, set both endpoint
selectors from that relation. Keep a canonical genuine ZERO endpoint rather
than interning a sentinel full mark.

```text
FLOW ; FLOW = FLOW
FLOW ; M(a,b) = M(a,b)
M(a,b) ; FLOW = M(a,b)
M(a,b) ; M(c,d) = M(a,d) when the existing FULL/GROUP middle test accepts b,c
```

A state whose source does not yet match G can still reach a useful earlier
W. Do not prune it on source mismatch. A cycle changes no path-length key.
Do not use the C2 Boolean result as permission for C5.

### 6.3 Pair guards and coverage

```text
target possible:
  j static    -> shared B target prefix candidate
  j nonstatic -> local R target prefix candidate, all labels
source possible:
  G static    -> shared B source near a G leaf
  G nonstatic -> local W source near a G leaf, including genuine ZERO
extra pair lookup requires both
```

Own B counts as shared B. W-R composition is possible with no B row.
Negative guards skip only the composed/inherited part, not direct local pairs
or implicit families. Native record permission remains separate.

For STAR/EXACT raw output leaves, stop if every raw typed membership is
retained with its original layer, E, mx and protection. Use a protection-aware
membership comparison. For ANY/MUST, use exhaustive lookup in this iteration:
another Dp can produce an EXACT or rebased result even when a broad raw
packet was kept. Do not claim `Facts.equals(raw, result)` proves completion.

```text
W p/T -> C.a/U; R C.a/U -> ret/V
query ret/V -> p/T
R alone does not match output p/T; W-R yields pair (ret/V,p/T) and keeps it

d1=(ret/T,p/T), d2=(ret/U,q/U); query ret/T -> q/U
pair IDs cannot be crossed; result is empty
```

## 7. Complete predefined summaries

### 7.1 Descriptor and resolution tag

Do not use an `isComplete` or `staticRelationIsComplete` flag. The presence
of a predefined descriptor means that the method body model is complete.

```kotlin
sealed interface ResolvedBody {
    class Analyze(val entries: List<MethodKey>) : ResolvedBody
    class Predefined(val method: CommonMethod, val model: CompleteMethodSummary) : ResolvedBody
}

class CompleteMethodSummary(
    val normal: List<SummarySchema>,
    val exceptional: List<SummarySchema>,
    val touched: Set<AccessPathBase>,
)

sealed interface SummarySchema {
    data object ZeroIdentity : SummarySchema
    class PrefixFlowIdentity(val base: AccessPathBase, val prefix: AccessorPath) : SummarySchema
}

fun interface PredefinedSummaryProvider {
    fun forMethod(method: CommonMethod): CompleteMethodSummary?
}
```

These are the schemas required for cleanup. Do not invent general callback
execution, argument GEN, exceptions or body rules to support unused model
kinds. A later model can extend this closed schema set with its own proof.

Keep registered model descriptions separate from `MethodKey`, generated
method equality and rule equality. Match the actual registered generated
method, not every method named `__cleanup__`. Use an owned identity-keyed
catalog or a marker on that registered method. Do not add model data to
`SpringGeneratedMethod.equals/hashCode`.

```kotlin
val cleanupModel = CompleteMethodSummary(
    normal = listOf(
        ZeroIdentity,
        PrefixFlowIdentity(STATIC, registryClassAccessorPath),
    ),
    exceptional = emptyList(),
    touched = setOf(STATIC),
)

catalog.registerExact(generatedCleanupMethod, cleanupModel)
```

Resolve a descriptor before reading `instList`, testing for an empty body,
creating method entrypoints, or choosing an unresolved/default method model.
No model match means use the current normal resolution. A matched model with
no data result means no data result, not fallback.

### 7.2 Call plan and ordinary rules

Add `CallStage.Predefined` at the same ADDED-to-RETURNED body boundary as
`CallStage.Callees`:

```kotlin
class Predefined(
    override val from: CallPoint,
    override val to: CallPoint,
    val target: CommonMethod,
    val model: CompleteMethodSummary,
) : CallStage {
    override fun reversed(): CallStage = Predefined(to, from, target, model.reversed())
}

fun resolveTarget(method): ResolvedBody =
    provider.forMethod(method)?.let { ResolvedBody.Predefined(method, it) }
        ?: ResolvedBody.Analyze(resolveEntryPointsAsNow(method))
```

For each resolved dispatch target, choose one body branch. Keep union across
mixed analyzed/predefined targets. Keep genuinely unresolved branches only
where the existing resolver reports an unknown target. A fully modeled target
must not also get an unresolved identity, constructor fallback or analyzer.

```text
BEFORE -> BOUND         existing bind-in and call-site sink evaluation
BOUND -> REWRITTEN      existing call-site sources
BOUND -> ADDED          existing ordered call cleaners
ADDED -> RETURNED       predefined model OR ordinary callee branch per target
RETURNED -> REWRITTEN   existing return rewriter
REWRITTEN -> AFTER      existing bind-back and alias stages
```

Do not bypass the whole call plan on a model hit. Preserve call-site source,
sink, cleaner, rewriter and alias order. `END_FACTS` remains ignored as now.
Keep STATIC in touched bases in both directions. An ordinary pass-over lane
must not preserve an external static which the complete model kills.
Caller-local facts retain their current caller-local unchanged route.

Update exhaustive visitors in `CallPlan.reversed`, form-storage statistics,
`FormsReference`, ZERO call handling and `RunMethodCallServices.applyStage`.
New stage equality includes the semantic target/model descriptor. Existing
stage and fact keys do not gain provenance or compiler cache fields.

### 7.3 Apply a schema without a class-shaped initial

Compile the prefix identity to a transient `PathEdge` using current AP
accessors. Its source and target are the same prefix with KEEP/STAR suffix
behavior. This is an executable schema, not a stored `InitialAp`.

```kotlin
fun applyModel(stage, original, actual, mode, emitKnownResult) {
    val schemas = stage.model.normal // CallPlan.reversed already selects the reverse model
    for (schema in schemas) when (schema) {
        ZeroIdentity -> if (actual is Reach) emitKnownResult(original, actual)
        is PrefixFlowIdentity -> {
            if (actual is Reach || actual.base != schema.base) continue
            ops.applyEdge(
                actual, original, compilePrefixIdentity(schema),
                statementEdge = false, mode = mode,
                out = knownModelOut(original, emitKnownResult),
                ruleAssignment = false,
            )
        }
    }
}
```

The schema evaluator uses the existing AP edge transfer, including admitted
descent and exclusion rebasing. It calls no micro-operation read/write hook.
The pure identity schema cannot create a mark request. Assert that contract
in its `ApOut` adapter.

For the run-1 static result, reuse the known-summary result discipline:

```kotlin
fun acceptKnownResult(original, result, identityClassification) {
    if (config.run1 && result.base == STATIC)
        core.routeStaticResultToExit(original, result)
    else
        returned += PlanFact(original, result, identityClassification)
}
```

Preserve the existing identity classification and alias policy. Do not add
a new memory-effect test. `routeStaticResultToExit` keeps computed-group supply
separate from writer registration. The caller's exit rules and ordinary C5
still run later. The method being modeled has no boundary rules.

Do not use inferred-summary ZERO-static activation for this schema. ZERO
satisfies `ZeroIdentity` only. It cannot satisfy the registry prefix and cannot
create a registry fact. The model creates no local static writer, static-pool
read, request or method initial. Actual computed-result supply keeps its
existing separate policy.

Do not put the schema into `PersistentRecordStore` or publish it through all
transitive callers. Apply the immutable model at the actual call. A resulting
ordinary caller summary follows normal storage and restriction. The model
itself is a trusted relation and is not an inferred C5 candidate.

### 7.4 Reverse relation and control

Cleanup has no exceptional return row. Keep its normal control ZERO identity.
Its registry data relation is a partial identity, so its backward relation is
the same registry filter. A normal model row does not promote an incoming
DEMAND fact to NORMAL. In run-1, the existing static policy still yields
DEMAND static results.

Reverse each model using its proved relation, not by replacing it with a
broad static default. The first schema set supports only identities, so
`model.reversed()` retains those identity rows and completeness. If the core
needs an explicit exceptional lane, the empty exceptional set must produce
no branch. Do not reinterpret it as unknown exception behavior.

Guard ordinary `RunnerPort.analyzer`, root entry and subscription creation
against predefined targets. Normal calls resolve the tag before those
operations. A modeled root, if supplied, uses its explicit ZERO/control model;
it must not fall back to body analysis. Tests must fail if actor construction,
body graph loading, or entry/exit rule binding occurs for a model.

The current `zeroAtCall` unconditionally calls `emitUnchanged` before its
callee logic. `JIRCallPlanBuilder.sources` also has an internal `keepZero`
edge. Neither path can create return control for a complete model which has
no ZERO return row. Add a call-control decision for the resolved target union:

```kotlin
fun zeroCanReturn(orientedTargets): Boolean = orientedTargets.any { target ->
    when (target) {
        is AnalyzedOrUnresolved -> true // preserve current ordinary approximation
        is Predefined -> target.model.normal.hasZeroIdentity() // model already oriented
    }
}

// Replace only zeroAtCall's old unconditional control bypass:
if (ctx.zeroCanReturn) core.emitUnchanged(item)

// When building the forward SOURCES stage:
if (resolvedTargetUnionCanKeepZero) keepZero()
// Build every actual call-site source rule as before.
```

Gate only these unconditional control lanes. Do not reject every Reach
result at the call-plan exit. A reversed call-site source can produce a
legitimate `T -> ZERO` dependency even when the body model has no ZERO row.
Keep that source result and its ordinary backward processing. Remove only
the internal `ZERO_KEEP` identity, not real source actions. This requires no
new fact flag or provenance label.

Evaluate common call-site rules as before even when the model has no body
control row. Orient the model and its control decision once with the plan.
In the backward ZERO branch, retain subscriptions/`ZeroIn` only for analyzed
targets. Evaluate each predefined target's oriented control row locally;
never send it a `ZeroIn` event. Cleanup explicitly has `ZeroIdentity`, so its
ordinary control behavior is unchanged. Test an empty predefined normal
relation with no call-site effect to ensure that the hidden unconditional
ZERO paths are closed. Also test a reversed source which legitimately yields
ZERO and a mixed ordinary/predefined target union.

`JIRBidiAnalysis.gather` currently resolves root entrypoints early. Recognize
a predefined root before that operation. Use a root-start tag with Analyze
and Predefined cases; the latter runs the explicit model on the root control
input without a method entrypoint or actor. Do not create a dummy MethodKey,
change its equality, or query the target body to manufacture a root key.

## 8. Spring generation and prescan

### 8.1 Generate the selected cleanup path

Read `options.common.ifdsBidirectional` before Spring generation. Pass a
generation policy into `SpringWebProjectContext`. It does not participate
in generated method equality. Select one path:

```kotlin
enum class CleanupGeneration { LEGACY_SAVE_RESTORE, PREDEFINED_REGISTRY }

val cleanupGeneration = if (options.common.ifdsBidirectional)
    PREDEFINED_REGISTRY else LEGACY_SAVE_RESTORE
```

In `SpringWebProject.ndMethodDispatch`, keep the cleanup call. For the new
path, omit both registry assignment loops and their `%reg_...` temporaries.
Set `loopEnd`, the switch/default and completed-controller **join target**, to
`cleanupLoc` when no save instruction exists. Keep the actual loop backedge
to `loopStart` unchanged. Preserve switch cases, controller wrappers, return
values and exits.

```java
// Old, per dispatcher:
Object savedA = Registry.A;
Object savedB = Registry.B;
__cleanup__();
Registry.A = savedA;
Registry.B = savedB;

// New core:
__cleanup__();
```

In `generateCleanup`, register the model and omit the blanket
`SpringGeneratedMethod.callCleaners` value on the modeled path. In
`SpringRuleProvider.cleanerRulesForMethod`, do not emit the dynamic cleanup
cleaner for that modeled method. Keep the legacy block and its cleaners for
the old engine. Do not modify cleaners of unrelated generated methods.

Method entry/exit rules are skipped by predefined-target dispatch, not by a
global rule-provider filter for every Spring method. Controllers remain
ordinary analyzed methods with their annotations and exit rules.

### 8.2 Prescan adapter

Prescan currently uses the legacy engine with `AnyAccessorDisabled`. It also
carries lambda type-information facts used to resolve the full call graph.
Skipping the modeled body must not remove that information.

```kotlin
fun prescanResolvedTarget(caller, target, context) {
    val model = predefined.forMethod(target)
    if (model == null) return existingPrescanTarget(caller, target, context)

    resolvedGraph.recordModeledTarget(caller, target) // metadata only
    collectCallSiteRuleRelevanceAsNow(caller, target, context.statement)
    propagateExistingPrescanControlAndTypeInfo(context)
    // No target body graph, summary subscription or entry/exit rule relevance.
}
```

Current `TaintAnalysisUnitRunner.copyResolvedGraph` derives edges from summary
subscriptions. Add a metadata-only inventory for modeled calls and union it
into that export. Keep the caller-to-cleanup edge even though no cleanup
subscription exists. Do not add fake outgoing cleanup calls.

Use the current prescan type-info policy; do not apply the cleanup taint kill
to `TypeInfoGroup/TypeInfoAccessor` facts. A conservative type-info pass is
prescan metadata, not a `S.* -> S.*` taint model in the new core. Compare the
resolved graph and lambda targets against the current generated path.

Do not collect modeled target entry/exit source/sink IDs in
`JIRTaintAnalysisContext.handlePhase`. Keep call-site rule relevance in
`prepareCallStatementRules`. Executable rule selection and mark reduction
then see the selected rule set, rather than a rule that can never execute.
An identical generic boundary rule used by another analyzed method remains
eligible through that method.

### 8.3 Principal transfer examples

| Actual caller data at cleanup | Model result | Reason |
|---|---|---|
| ZERO | ZERO only | Explicit normal control row |
| `S.Registry.bean.child.* / T [D]` | Same path, mark, E and protection, still D | Registry identity |
| `S.Other.temp.* / T` | None | Complete model has no matching static row |
| Packed registry and nonregistry STATIC leaves | Registry part only | Per-subtree AP selection |
| Broad `S.* / FLOW` | Existing admitted registry-prefix projection only | Prefix identity, with correct E rebasing |
| EXACT synthetic class marker outside the registry | None | It is not a registry field or its descendant |
| Caller local x/T | Existing caller-local bypass | No cleanup parameter or return position |

The reserved registry class is not a synthetic EXACT class-marker position.
The schema admits registry fields and descendants. It does not introduce
class-wide concrete taint or relax initial-fact grammar. An incoming E that
excludes the registry class must block broad descent. A deeper field's own E
must survive. Preserve FLOW mx and every surviving protection membership.

For K registry fields and D dispatcher cleanup sites, generation removes
exactly `2*K*D` assignment instructions and their temporary carriers. Do not
claim an equal runtime reduction. The model is applied to actual facts only;
it does not expand K method summaries at each site.

## 9. Required proofs and concrete adapter checks

### 9.1 Checked constructive models

All sources below are under `spec/lean/proposals/demand-storage-next`.

| Model | Audited declarations | Established result |
|---|---:|---|
| [SpringCleanup](../../spec/lean/proposals/demand-storage-next/SpringCleanup.lean) | 11 | Save/clear/restore and registry filter have equal concrete value and backward relations; layers/control and instruction count |
| [DemandQueries](../../spec/lean/proposals/demand-storage-next/DemandQueries.lean) | 31 | Broad endpoint guards, entry projection, explicit/lazy results, pointwise mask union |
| [LookupStrategies](../../spec/lean/proposals/demand-storage-next/LookupStrategies.lean) | 25 | Local coverage, tighter guards, mapped-terminal and actual-FLOW cases |
| [StagedDemandLookup](../../spec/lean/proposals/demand-storage-next/StagedDemandLookup.lean) | 25 | Local/remote path equivalence, exact-bound stopping, positive and negative contracts |
| [BidirectionalDemandExists](../../spec/lean/proposals/demand-storage-next/BidirectionalDemandExists.lean) | 20 | Directed two-frontier witnesses and typed closure, remote-join and overlap cases |
| [PredefinedSummaryDispatch](../../spec/lean/proposals/demand-storage-next/PredefinedSummaryDispatch.lean) | 14 | Complete tag has no body/default/unresolved/boundary lane; external call-site reports remain; identity-key selection; intentional boundary difference |

Total: **126 axiom-free audits**. Their sibling `*-checks.json` files record
source hashes, Lean commands and proof scope. Do not count the unselected
FLOW-only certificate or rule-footprint proposals as support for this design.
The old Spring value-model receipt predates the boundary-rule decision.
Its value proofs still apply; its old observation-preservation gate is
superseded by the explicit skip and the new complete-dispatch model.

### 9.2 Constructive correctness argument

Use these lemmas as adapter contracts, with executable row/path witnesses:

```text
Index soundness:  each returned ID names a frozen eligible row in D(M)
Index coverage:   each useful row/path in D(M) survives its positional guard
Entry projection: projected full paths = direct entries + mapped-output/FLOW-suffix witnesses
Stage equality:   local closure then visible mixed closure = full eligible closure
C2 meeting:       forward witness ; oriented join ; backward witness = valid T prefix
C2 exhaustion:    complete roots/adjacency + no meeting => no valid T prefix
C2 coverage:      real results <= reference results <= possible keys <= real results
C5 paths:         each pair state has one valid path; each valid path has a state
C5 output:        union the same AP.restrict over complete pairs and original members
Protection:       equal-payload masks join by OR; arrival order cannot remove a flag
Model dispatch:   matched complete model => exactly model outcomes, no fallback/body rules
Cleanup values:   save/clear/restore(input) = registryFilter(input), forward and backward
```

For C2, take the last mapped edge of any completed path with output T. Its
remaining suffix is FLOW. Its output is an eligible forward root, and reverse
FLOW traversal from the reader reaches it. Conversely, a verified meeting
joins two actual path fragments. A mapped-only rightmost row supplies its
entry directly. An all-FLOW path adds only its rightmost abstract entry.
Apply the unchanged emitter on both sides. Thus C2 returns the same initials;
it does not authorize T from an abstract actual input.

For C5, each initial state is a primitive rightmost seed. Each step adds one
eligible primitive left seed with the existing geometry and mark join.
Induction gives a full path witness and reaches every relevant finite path
state. Projection keeps its correlated endpoints. The same AP reducer then
returns the same outputs for every original member. Union protection only
after equal ordinary-payload checks. Reattach unchanged J.

For staged search, local rows are a subset of visible rows. A fresh visible
restart cannot lose the local states. Every mixed path remains present,
including alternating own/inherited links. Deduplication removes repeated
states, not an unexamined adjacency phase. Stop only at the stated exact-key
or exact-output coverage certificate.

For cleanup, split an input into ZERO, caller-local, registry field and other
static field. The old block and the model keep the first three and kill the
last. The partial identity is its own reverse. This proves values, not equal
artificial intermediate DEMAND rows or old method-boundary reports. The latter
are explicitly removed by the selected model contract.

### 9.3 Adapter obligations before runtime replacement

The local Lean models do not verify Kotlin, AP tree indexes or JVM lowering.
Close the following concrete adapters in proof-first/TDD order:

| Adapter | Proof obligation | Counterexample/test witness |
|---|---|---|
| Seed indexes | Returned IDs and owner masks equal the frozen primitive relation; own-B uses CommonMethod | Same geometry with disjoint labels/owners, same method across contexts |
| Two queues | Every admitted state has a witness; complete exhaustion covers every successor/root; finite FIFO work | Late root, directed meet across visited states, local/remote alternation |
| AP geometry | Indexed joins equal the current anchor/overlap predicate | Same anchor but disjoint or excluded geometry; EXACT class marker |
| Selector buckets | Exact-T plus group bucket equals directional `coversAtom` eligibility | T and U in the same group, GROUP output accepts T, unrelated group |
| C2 bound | Every reference emitted key is in the non-interning possible-key view | Inherited EXACT, deeper target, nonempty concrete E, packed actual leaves |
| C5 results | Exact-payload union and mask transport equal leaf-level reference output | Plain/protected both arrival orders; ANY yields another EXACT result |
| Snapshot ownership | Sealing shares no mutable builder state; native records stay separate | Query/rebuild old snapshot; incomplete transition; mutation attempts |
| Schema AP | Prefix identity keeps exactly admitted registry subtree with same annotations | Mixed tree, ancestor E, own E, FLOW mx, protected subset |
| Call dispatch | Every resolved target has exactly its selected body branch and explicit control | Empty modeled output, hidden ZERO identities, empty body, mixed targets, modeled root, same-name nonmodel |
| Prescan | Graph/type-info coverage remains complete without a body subscription | Modeled call edge plus lambda target after cleanup; boundary relevance omitted |
| Generation | New block has same control and value relation in both directions | Empty registry, multiple dispatchers, cleanup join, unchanged loop backedge and normal return |

Implement these checks against a **finite explicit reference**, not against
the optimized query's own candidate list. For finite BFS, bound work by the
number of admitted complete geometry states on each side and the finite
eligible row adjacency. For C5, use finite source/target/label states. The
existing field limit bounds paths; do not include path length as a state key.

Do not enable an adapter whose contract is false or unknown. Refine its
implementation or formal abstraction first. Do not alter a field rule, demand
gate or observation policy to make a proof pass.

## 10. Test plan and implementation sequence

Use small red tests for each required case before changing runtime code.
The storage change is substantial; differential tests are required. Do not
add performance tests which only restate implementation counters.

### 10.1 Demand tests

Extend the existing `DemandSelectionTest`, `RestrictedDemandPipelineTest`,
`RestrictedDemandBoundaryTest`, `FrozenStaticCompletionTest` and
`StaticProducerGrammarTest`. Add `DemandStorageQueriesTest` for whole-packet
differential tests and `BidirectionalEntryLookupTest` for queue/visibility cases.

```kotlin
for (fixture in finiteFrozenGraphsWithMarksAndCycles()) {
    val reference = explicitlyEnumerateDemandClosure(fixture)
    val optimized = buildDemandStorage(fixture)
    for (actual in fixture.actualPackets) {
        assertInitialKeysEqual(reference.emit(actual), optimized.initials(M, actual))
    }
    for (raw in fixture.rawSummaries) {
        assertExactPayloadAndProtectionEqual(
            reference.restrict(raw), optimized.intersect(M, raw),
        )
    }
}
```

Include these finite cases:

```text
direct local FLOW+T covers the C2 bound; zero graph queries
actual FLOW never emits T; inherited direct FLOW target still works
mapped rightmost R emits its OUTPUT U, not its input T
mapped B is a C2 root/barrier but a C5 transfer
own B plus W without inherited rows; W-R with no B at all
inherited EXACT/deeper target defeats premature STAR coverage
absent actual T; genuine ZERO W vs null Dp; no ZERO-conclusion bypass
cross-context W/R separation; common-method own-B sharing
disconnected endpoints; per-label visibility; outside-graph owner
cycles, late roots, multiple targets, both search directions
C5 unmatched intermediate source must continue
original ND J retained in later forward runs
run-3 and later: static/nonstatic C2/C5 use local demand only; zero BFS/graph calls
run-2-to-run-3 snapshot owns no previous W/B/R completion or static-carry family
protection-only upgrade in both arrival orders
ANY/MUST C5 exhaustive; STAR/EXACT completion includes masks/layers/E/mx
```

Count AP initial interning during a coverage-only miss. It must create no
hypothetical InitialAp or mark atom. Verify that `initials` never constructs
paired origin products and that no composition runs during `seal`.

### 10.2 Predefined and Spring tests

Add core `PredefinedSummaryTest` and JVM `PredefinedCallPlanTest`. Extend
`SpringDispatcherFormsTest` and `SpringDispatcherAcceptanceTest` for both
generation modes. Keep the existing legacy expectations under the legacy
mode instead of replacing them globally.

```text
model hit: no body load, actor, summary subscription, entry/exit rule binding
empty model result: no unresolved/default identity; ZERO still follows its row
model without ZERO row: neither fast unchanged nor source keepZero creates control
reversed call-site source T -> ZERO remains a valid source dependency
backward ZERO and predefined root: no ZeroIn/analyzer/entrypoint resolution
registry full-mark/GROUP/FLOW paths and protected/mixed packets preserved
nonregistry static killed; caller locals unchanged; reverse model same filter
ZERO does not create a registry fact or activate a static reader
same-name unregistered method remains ordinary
call-site rule still fires; predefined boundary rule deliberately does not
controller annotation/exit rules still fire
no static read/write/pool registration from model application
computed-result supply and caller summary handling retain current policy
prescan graph includes modeled call; lambda type-info remains available
no modeled boundary relevance IDs; other methods' same rule still selected
new generation has exactly 2*K*D fewer assignments; cleanup call remains
legacy generation and cleaners unchanged
```

Use a provider spy which throws if the engine asks for modeled entry/exit
rules, and an actor-factory spy which throws if the model is analyzed. Keep
call-site methods on that spy enabled. These checks detect an accidental
ZERO-only actor as well as an ordinary nonzero analyzer.

### 10.3 Commit-sized order

1. Keep the checked formal models and add adapter tests against current
   reference AP functions. Add immutable seed-view/index tests first.
2. Introduce `DemandStorage` behind the current consumers with direct local
   AP results. Keep a test-only exhaustive reference path for differential use.
3. Add separate C2 entries, C5 pair indexes and exact protection accumulation.
   Keep native records and publication batching unchanged.
4. Add local-first stages and non-interning C2 bounds. Add the fresh visible
   bidirectional search and paired C5 walk. Pass finite differential tests.
5. Add the complete model tag/provider and call stage. Test models without
   Spring before changing generated code. Prove schema AP adapter cells.
6. Add prescan graph/type-info adapter and selected boundary-rule exclusion.
   Test complete resolved graph export before using the new generation path.
7. Select modeled Spring cleanup for the new core. Remove only its generated
   save/restore instructions and two cleaners. Test both engines' paths.
8. Remove unused runtime APIs and reference-only production code. Run the
   relevant module and acceptance suites. Commit runtime changes before
   project measurement, when implementation is separately authorized.

From `core/opentaint-dataflow-core`, use the existing Gradle test tasks for
`:opentaint-dataflow:test` and `:opentaint-jvm-dataflow:test`. From `core`, run
the Spring and bidirectional acceptance tests through the root `test` task
with their fully qualified class filters. Confirm wrapper/task names from
the build before executing. This proposal does not execute runtime tests.

## 11. Removal list

Remove these only after their replacements pass the differential/adapter tests:

| Old entity or work | Replacement |
|---|---|
| Consumer `DemandStore.near/covering` API | `initials/intersect`; test-only reference may keep exhaustive pairs |
| Actor loops which collect paired C2 guides then ignore Dp | Entry-only admission inside demand storage |
| Top-level `restrictBy` actor helper | Paired restriction inside demand storage |
| Shared paired `FrozenStaticCompletion.lookup` used for C2 | Query-directed compatible-mark existence search |
| Production construction of all C2 origin/mark pairs | Output geometry roots plus FLOW B frontiers |
| Blanket cleanup `callCleaners` on modeled generated method | Complete registry model |
| Dynamic Spring cleanup cleaner on modeled path | Complete registry model |
| New-core registry save/restore instructions and locals | One modeled cleanup call |
| Modeled target analyzer/subscription/default branch | Direct predefined stage |
| Modeled method entry/exit rule collection and evaluation | Explicit selected skip; no boundary observer |
| `staticRelationIsComplete` and ZERO-only-actor proposal variants | Always-complete tagged descriptor |

Keep `StaticGuidanceInterner`, frozen seed capture, killed-writer inventory,
joined caller binding, graph visibility scratch and shared actual-static carry.
They are still used. Keep `DemandPattern` for C5, ordinary AP emit/restrict,
native-record stores, controller rules, and legacy Spring save/restore code.
Do not remove method-body rule APIs used by ordinary analyzed methods.

## 12. Measurement after implementation

Use the fixed campaign and configurations in `task.md`. Reuse the saved
baseline; do not rerun it or add analyzer configurations. Run OWASP and the
selected conductor, thingsboard and Stirling-PDF projects using the configured
`runProjectAnalyzer` task, memory and time limits.

Report these separately:

```text
run-1 engine time
run-1 -> run-2 joined caller binding, index seal time and peak memory
run-2 and each later reached iteration: engine time, result and memory
C2 direct/local/visible calls; coverage stops; roots/states/joins visited
C5 pair candidates/states/restrict calls; coverage stops
entry rows vs paired rows; shared static indexes and owner membership counts
generated assignments removed; modeled calls and surviving schema memberships
predefined actor/body/boundary-rule calls: must be zero
```

Use aggregate optional statistics, not a retained log of every path or row.
Measure whether the new indexes cost more retained heap than the paired work
they remove. At OOM, capture and inspect the configured memory snapshot.
At timeout, distinguish root/index enumeration, queue work and AP reduction.

Compare vulnerability identities and locations against the saved baseline.
Report the selected removal of predefined boundary observations separately;
do not describe it as a transfer-regression fix or silently count it as an
unexplained FN. For each project always state latest reached, complete and
accepted forward report iteration. Do not claim a fixed factor of speedup:
C2 can stop at a witness, but a negative query or C5 can still visit the full
relevant finite component.

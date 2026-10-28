# Demand storage: local and transitive lookup

Date: 28 October 2026. Status: design proposal; no runtime change.

This document specifies the two lookup operations in
[demand-storage-and-spring-cleanup.md](demand-storage-and-spring-cleanup.md).
It replaces that document's earlier broad lookup choice with the strategies
below. AP emission, paired restriction, layers and field handling stay as
specified. The lookup change adds no semantic demand.

## 1. Fixed relation and method-local coverage

Use the existing forward-oriented frozen static seeds:

```text
W: ordinary or genuine ZERO -> static
B: static -> static
R: static -> ordinary
```

A path composes only at a static internal position. W/R belong to the
complete querying `MethodKey`. B visibility uses the existing detached
call graph and common-method owners. An own B row is visible by a path of
length zero from the method to itself. An inherited B row has another
reachable owner. Owners outside the graph keep the existing exact-owner rule.
Here a primitive row means a frozen input seed of static completion. It can
include a row already produced by actual caller binding. Query traversal does
not repeat that binding or treat a composed static path as a new binding seed.

For an owner M, let `Local(M)` contain:

1. Ordinary inferred demand pairs from the preceding run.
2. Direct projections of every frozen local W and R seed.
3. Direct projections of M's own B seeds.
4. The existing implicit ZERO and same-actual-static-carry families.

For a direct forward seed `a -> b`, its demand projection is `(D_c=b, D_p=a)`.
Use the existing mark, tail, ZERO and exclusion projection. A primitive seed
is already part of the specified frozen relation; this local view does not
create another relation.

```kotlin
fun localDemand(M) = LocalDemandView(
    ordinary = ordinaryDemand[M],
    writers = frozenWriters[M],
    readers = frozenReaders[M],
    ownBridges = sharedBridgeOwners[M.method],
    implicit = existingImplicitFamilies,
)
```

The own-B owner index is shared by common method, as in the existing B
visibility contract. It does not need a separate copy for every context.
This view's contents are fixed at seal time, including for a method key
first queried later. A query constructs no new demand.

This is a required **local coverage invariant**. Build the relevant indexes
at the completed transition. Index local W/R and own B with references to
their immutable seed rows. Do not duplicate each B row into all callers.
Direct inherited B rows and composed rows remain in the lazy component.

If this invariant is not established, use the previous broad conservative
guard. The tighter negative decisions below would otherwise be unsound.

The complete demand relation is:

```text
D(M) = Local(M)
       union visible inherited B projections
       union valid static-path compositions
```

Native records remain separate. Run-1 still has no incoming demand snapshot.
In the current protocol, only incoming run-2 has the skipped-static component;
later restricted runs use their new ordinary demand snapshots.

## 2. Lookup strategy for each operation

Both operations always query `Local(M)`. A transitive lookup adds candidates;
it does not replace local lookup. A nonempty local result is not a stopping
condition.

Use location indexes for the cheap tests. Ignore marks, tails and exclusions
in those tests. The complete query and AP operation apply them later.

For C2, `near` means equal, ancestor or descendant paths on the same base.
For C5's entry test, use candidate targets whose path is a prefix of the
whole initial's path. For its output test, use `near` against every relevant
conclusion leaf. Empty paths include possible descendant candidates.
These are candidate tests, not the full AP containment/intersection rules.

The shared B indexes include **own and inherited** B rows. Ignoring their
visibility in the cheap test gives false positives, which are safe. The
actual traversal must check each row's visibility, including its mark-pair
owner set.

### 2.1 Operation 1: actual fact to initial facts

For each bounded actual leaf A:

| Condition | Lookup |
|---|---|
| No skipped-static component | Local only |
| A is a nonstatic actual FLOW leaf | Local only; colored entries cannot emit from FLOW |
| A is a static actual FLOW leaf | Local plus visible FLOW B direct targets, if any; no prefix traversal |
| A is nonstatic; no matching local FLOW R target | Local only |
| A is nonstatic; a local FLOW R target is near A | Local plus FLOW-prefix color search for those readers |
| A is static; no shared B target is near A | Local only |
| A is static; a shared B target is near A | Local plus visible B target lookup; extend only FLOW targets for colors |

```kotlin
fun entryPlan(M, A): EntryPlan {
    if (skipped == null) return LOCAL_ONLY
    if (A.isActualFlow) {
        if (A.base != STATIC || allFlowBridgeTargets.near(A).isEmpty())
            return LOCAL_ONLY
        return LOCAL_AND_SHARED_DIRECT
    }
    return if (A.base == STATIC) {
        if (allBridgeTargets.near(A).isEmpty()) LOCAL_ONLY else LOCAL_AND_STATIC
    } else {
        if (localFlowReaderTargets[M].near(A).isEmpty()) LOCAL_ONLY
        else LOCAL_AND_STATIC
    }
}
```

The remaining table rows apply when the actual FLOW shortcut does not apply.
`isActualFlow` means a real FLOW leaf, not ZERO/Reach. Keep the existing ZERO
adapter. A positive static FLOW test needs only inherited one-edge entries;
all longer paths either have a colored output, which cannot emit from FLOW,
or have the same abstract target as their rightmost FLOW B seed.
The shared-direct route checks call-graph visibility. It performs no static
relation composition.

Why a mapped local R target needs no prefix search for C2: in
`C.f/T -> ret/U`, the output U and target geometry are fixed. Its direct
local projection already supplies `ret/U`. Earlier prefixes can change the
paired output requirement, but cannot add a new C2 target from this last edge.

Why a FLOW target differs: `C.f/* -> ret/*` can gain `ret/U` from a preceding
mapped writer or bridge. The direct abstract entry emits shared FLOW, not
a concrete U initial. It does not replace the colored entry.

Direct W targets need no C2 prefix search. W starts at a nonstatic position,
so another static path cannot compose before it. An inherited B target can
add a direct entry even if no composition is needed. Include this one-edge
case in the static route.

### 2.2 Operation 2: summary to restricted summaries

Let the offered summary be `J -> G`. Apply the choice below to every member
`j` of J, retaining the whole J on all returned results.

```kotlin
fun pairPlan(M, j, G): PairPlan {
    if (skipped == null) return LOCAL_ONLY

    val targetPossible = if (j.base == STATIC)
        allBridgeTargets.hasPrefixCandidate(j)
    else
        localReaderTargets[M].hasPrefixCandidate(j) // FLOW and mapped

    val sourcePossible = if (G.base == STATIC)
        allBridgeSources.nearAnyLeaf(G)
    else
        localWriterSources[M].nearAnyLeaf(G) // includes genuine ZERO

    return if (targetPossible && sourcePossible) LOCAL_AND_STATIC else LOCAL_ONLY
}
```

| Entry j | Conclusion G | Extra lookup is possible only when |
|---|---|---|
| Nonstatic | Nonstatic | A local R target can contain j, and a local W source can affect G |
| Nonstatic | Static | A local R target can contain j, and a shared B source can affect G |
| Static | Nonstatic | A shared B target can contain j, and a local W source can affect G |
| Static | Static | A shared B target can contain j, and a shared B source can affect G |

ZERO is nonstatic in this table. Preserve its private selectors and existing
AP rules. The original backward-ZERO seed return stays outside C5; it is not
implemented by this table.

A new composed path must start with W or B and end with R or B. A direct
inherited B path also meets both static endpoint tests. Thus, no new result
is possible if either test fails. A positive answer does not prove that the
two endpoints connect: the traversal must supply one complete path.

Use all R labels in the C5 target index. A mapped R fixes its C2 entry, but
its earlier writer still matters to the pair. Do not reuse the C2 FLOW-only
reader test here. W-to-R composition needs no B row; the first table row
must still take the transitive route when the B graph is empty.

## 3. Local lookup

### 3.1 Initial admission

```kotlin
fun localEntries(M, A): Sequence<Pattern> =
    ordinaryEntries[M].around(A) +
    directLocalSeedEntries(M).around(A) +
    implicitZeroEntryForActual(A) +
    sameActualStaticCarryEntry(A)
```

Deduplicate complete entry patterns independently of Dp. Null Dp remains
valid for C2. After local and any transitive candidates have been collected,
run the unchanged AP emitter against the bounded actual packet.

Do not infer T from actual FLOW. Abstract Dc emits shared FLOW. A concrete
or GROUP Dc must pass the existing directional actual-mark test.

### 3.2 Summary restriction

```kotlin
fun localPairs(M, j, G): Sequence<DemandPattern> =
    intersectIds(
        directAndOrdinaryPairs[M].byEntry.lookupPrefixes(j),
        directAndOrdinaryPairs[M].byExit.aroundAllLeaves(G),
    ).map(::completePair) + sameActualStaticCarryPairs(j)
```

The output index omits absent Dp. The implicit ZERO entry alone cannot
authorize a C5 result. Each returned row retains its original Dc/Dp pairing.
Apply `AP.restrict(j, G, pair)`; indexes cannot grant publication permission.

## 4. Shared traversal primitives

All traversals operate on immutable seeds accepted at transition. They do
not bind writers through callers again, run a CFG, evaluate rules, subscribe
to the static pool or propagate a request.

```kotlin
fun incoming(M, requiredStatic): Sequence<Seed> =
    localWriters[M].byTarget.around(requiredStatic) +
    sharedBridges.byTarget.around(requiredStatic).filter { visible(M, it) }

fun geometryJoins(left, current): Boolean =
    staticAnchor(left.to) == staticAnchor(current) &&
    existingGeometryOverlap(left.to, current)
```

Use the current static anchor and overlap operations. Class EXACT markers
are distinct from the fields of a class. Root/class carry is a separate
implicit family and is not a vertex in this named-static graph.

Composition adds one primitive seed on the left of the current suffix.
It preserves the suffix's target geometry and the primitive seed's source
geometry. It composes their symbolic mark relation as specified below.
Do not recursively call initial emission to perform a graph step. Do not
invent a new suffix geometry from an intersection or assume that arbitrary
AP summary applications can be reassociated.

Query method, direction and snapshot are fixed. W/R use complete MethodKey
ownership. B visibility is checked per geometry/label row, not once for the
union of all owners of that geometry. Share reachability scratch within
the query.

## 5. Transitive lookup for initial admission

C2 needs only a target entry. It must not enumerate all possible original
sources and input marks for that target.

### 5.1 Select rightmost seeds

For a nonstatic actual A, select local FLOW readers with targets near A.
Their abstract entries already come from local lookup; search only for
additional output colors.

For a static actual A, select visible shared B rows with targets near A.
Mapped B gives its direct colored entry. FLOW B gives its abstract entry
and can gain colors from prefixes. Own B can duplicate a local entry;
deduplicate the result. Do not exclude own FLOW B from prefix search.

```kotlin
fun transitiveEntries(M, A, emitEntry) {
    if (A.isActualFlow) {
        if (A.base == STATIC) {
            for (b in visibleFlowBridgesEndingNear(M, A)) emitEntry(b.to)
        }
        return // no colored entry can emit from this actual input
    }
    if (A.base != STATIC) {
        for (r in localFlowReaders[M].byTarget.around(A))
            colorsBefore(M, r.from) { U -> emitEntry(withMark(r.to, U)) }
    } else {
        for (b in visibleBridgesEndingNear(M, A)) {
            when (val label = b.label) {
                FLOW -> {
                    emitEntry(b.to) // abstract, still needs the AP emitter
                    colorsBefore(M, b.from) { U -> emitEntry(withMark(b.to, U)) }
                }
                is Mapped -> emitEntry(withMark(b.to, label.output))
            }
        }
    }
}
```

`withMark` changes only the target selector. Preserve its field chain, tail
and E. ZERO output uses the existing ZERO adapter, not a new runtime mark.

### 5.2 Find colors through FLOW prefixes

```kotlin
fun colorsBefore(M, startStatic, emitColor) {
    val pending = ArrayDeque<Pattern>()
    val visited = HashSet<StaticGeometry>()
    val colors = SelectorSet()

    fun offer(p) {
        if (visited.add(completeGeometry(p))) pending.addLast(p)
    }
    offer(startStatic)

    while (pending.isNotEmpty()) {
        checkpoint()
        val current = pending.removeFirst()
        for (left in incoming(M, current)) {
            if (!geometryJoins(left, current)) continue
            when (val label = left.label) {
                FLOW -> if (left.from.base == STATIC) offer(left.from)
                is Mapped -> if (colors.add(label.output)) emitColor(label.output)
            }
        }
    }
}
```

All suffix steps represented in this search are FLOW. The first mapped
prefix fixes the target's output color. Emit that color and stop that branch.
An earlier prefix cannot change it, and the mapped seed alone is a valid
prefix witness. FLOW W has a nonstatic source, so that branch gives no color
and stops. A genuine ZERO-to-static mapped writer supplies its output color
normally; its ZERO input is not interned as a full mark.

The visited geometry includes base/anchor, full bounded chain, tail and E.
Do not use only `C.f` as the key. Output colors retain FULL/GROUP identity.
For multiple rightmost targets, either complete each `colorsBefore` search
separately or include the target in shared worklist state. A global visited
set across unfinished target searches can lose a result.

Do not cache an incomplete or empty intermediate color set while a cycle
is still being explored. Only reuse a completed result for the same snapshot,
method and complete starting geometry.

## 6. Transitive lookup for summary restriction

C5 needs the original source and target, so it follows both FLOW and mapped
prefixes. It must not use the C2 stop-at-first-mapped rule.

For each summary member j, start from:

- Local R rows, FLOW or mapped, whose targets are candidate prefixes of j.
- Visible shared B rows whose targets are candidate prefixes of j.

Direct W rows are already local and cannot be the last edge of a longer
static path. They need no traversal start. Own B is included: its direct
pair can be local while its longer compositions are not.

```kotlin
data class PairState(
    val from: Pattern,
    val target: Pattern,
    val label: GuidanceMarks,
)

fun transitivePairs(M, j, G, emitPair) {
    val pending = ArrayDeque<PairState>()
    val visited = HashSet<PairState>()

    fun offer(s) { if (visited.add(s)) pending.addLast(s) }
    for (last in rightmostReadersAndVisibleBridges(M, j))
        offer(stateOf(last))

    while (pending.isNotEmpty()) {
        checkpoint()
        val state = pending.removeFirst()
        val pair = directionalDemand(state) // Dc=target, Dp=from
        if (couldRestrict(j, G, pair)) emitPair(pair)

        if (state.from.base != STATIC) continue
        for (left in incoming(M, state.from)) {
            if (!geometryJoins(left, state.from)) continue
            val label = composeMarks(left.label, state.label) ?: continue
            offer(stateWithEndpoints(left.from, state.target, label))
        }
    }
}
```

`couldRestrict` can use the same complete AP tests as restriction, or a
conservative prefilter. Every offered pair is still passed to the unchanged
`AP.restrict`. Preserve the real ZERO endpoint and private selectors during
directional projection.

### 6.1 Mark composition

```text
FLOW ; FLOW             = FLOW
FLOW ; mapped(a,b)      = mapped(a,b)
mapped(a,b) ; FLOW      = mapped(a,b)
mapped(a,b) ; mapped(c,d)
    = mapped(a,d), only if b and c are compatible by the existing FULL/GROUP rule
```

Use the existing compatibility test, not full-name equality or group-only
equality. FLOW remains diagonal; do not enumerate every full mark to compose
it. A private ZERO selector is valid only at its actual ZERO endpoint.

The pair state retains complete source and target patterns plus the composed
mark relation. FLOW and mapped(T,T) remain distinct. Deduplicating by static
field alone, by output mark alone, or by one endpoint loses required pairs.

`stateWithEndpoints` must set **both** endpoint marks from the composed label,
as the existing `FrozenStaticCompletion.compose` does. It must not copy an
old FLOW mark while changing only the label:

```kotlin
fun stateWithEndpoints(from, target, label): PairState = when (label) {
    FLOW -> PairState(withMark(from, STAR), withMark(target, STAR), FLOW)
    is Mapped -> PairState(
        if (from.base == ZERO) canonicalZeroPattern(from)
        else withMark(from, requireNotNull(label.input)),
        if (target.base == ZERO) canonicalZeroPattern(target)
        else withMark(target, requireNotNull(label.output)),
        label,
    )
}

fun directionalDemand(s): DemandPattern =
    DemandPattern(entry = s.target, exit = s.from)
```

Keep endpoint geometry and E during relabeling. Nullable selectors belong
only to their actual ZERO endpoints; a nullable selector cannot join at a
static middle. Reuse the existing canonical ZERO representation, without
allocating a runtime full mark for a sentinel.

For `p/T -> C.f/U` followed by FLOW `C.f/* -> ret/*`, the canonical state is
`p/T -> ret/U`. Directional demand is `(ret/U, p/T)`. Neither endpoint may
retain the old FLOW selector.

### 6.2 Safe and unsafe stopping

Stop a branch when its source becomes nonstatic, when no incoming seed can
join, or when the complete state has already been visited. Cancellation uses
the existing resource policy. Do not stop at a mapped edge.

Do not stop merely because the current source does not match G:

```text
W: p/T -> C.f/U
R: C.f/U -> ret/V

query: summary ret/V -> p/T
first state: C.f/U -> ret/V
```

The first state does not match the offered output p/T. The next step through
W does. The source envelope is a query-level possibility test; it is not
permission to discard unmatched intermediate static vertices.

A target-location containment failure can reject an entire branch because
composition preserves the target geometry. Do not apply this claim to target
marks: a FLOW suffix can acquire a concrete mark from its prefix.

## 7. Cases that distinguish the strategies

Assume the listed rows are available at M and no other row matches the query.

| Rows and query | Initial admission | Summary restriction |
|---|---|---|
| Local mapped R: `C.f/T -> ret/U` | Actual `ret/U`: local entry is sufficient | `ret/U -> C.f/T`: local pair is sufficient |
| Local FLOW R: `C.f/* -> ret/*`; actual FLOW at ret | Local abstract entry is sufficient; do not search colors | Use the separate paired rules; do not reuse this C2 shortcut |
| Add local W: `p/T -> C.f/T` | Actual `ret/U`: still local | `ret/U -> p/T`: traverse W-R, even with no B |
| FLOW R: `C.f/* -> ret/*`; mapped W ends in U | Actual `ret/U`: traverse to obtain colored entry | Traverse to preserve the writer's source and input mark |
| Direct W: `p/T -> C.f/U`; no B target at C.f | Actual `C.f/U`: local | `C.f/U -> p/T`: local |
| Own FLOW B: `C.f/* -> C.g/*`; mapped W ends at C.f/U | Actual `C.g/U`: traverse own B for U | Traverse W-B for the pair to p/T |
| Inherited mapped B: `C.f/T -> C.g/U` | Actual `C.g/U`: retrieve the visible one-edge B | `C.g/U -> C.f/T`: retrieve that same pair |
| No R target near an unrelated local | Local only | Local only if the relevant endpoint test fails |

Local ordinary demand is retained in every row of this table. Static carry
also works without W/B/R seeds; it is a direct implicit family, not a reason
to search the graph.

## 8. Correctness and finite work

**Local-only choice.** A useful row absent from Local is either an inherited
one-edge B, or a path with at least two seeds. Such a path has a static
internal vertex, a first W/B seed and a last R/B seed. Its outer locations
are in the corresponding indexes. Thus a negative endpoint test excludes
every extra C5 pair. For C2, a mapped last local R already fixes a covered
local entry; only a FLOW local R or a shared B target can add another entry.
For actual FLOW, colored entries emit no result. An all-FLOW path has the
same abstract target as its last seed. Thus nonstatic FLOW needs only local
entries, and static FLOW needs at most visible direct FLOW B targets.

**C2 traversal.** Follow the current primitive composition from right to left.
Each collected color has a mapped-prefix-plus-FLOW-suffix witness. Conversely,
take the last mapped seed on any relevant path. The remaining suffix is FLOW,
so the search reaches that seed and emits its output color. An all-FLOW path
adds only the direct abstract target. No AP reassociation is used.

**C5 traversal.** Each offered state starts at a primitive seed or adds one
valid primitive left edge. It therefore has a complete path witness. Induction
on the number of primitive prefixes reaches every relevant path state.
The AP reducer, not endpoint membership, decides its final result.

The reference summary result is the union over every member j of the original
J and every complete pair d in D(M) of `AP.restrict(j,G,d)`, reattaching the
unchanged J. Preserve layer and union protection masks for equal ordinary
payloads. Do not require whole-J containment or invent independent pair
combinations.

On a frozen bounded seed set, C2 visits complete FLOW-prefix geometries and
collects only existing mapped output selectors. C5 visits complete finite
endpoint/label states. A cycle cannot create a new path-length coordinate or
a new mark. State deduplication bounds work per query; it does not imply
constant time on a large connected component. Do not enumerate this state
space eagerly at transition.

The existing [DemandQueries model](lean/proposals/demand-storage-next/DemandQueries.lean)
proves the broad guards, targeted projection and explicit/lazy query contracts.
The tighter local-only choices are modeled in
[LookupStrategies.lean](lean/proposals/demand-storage-next/LookupStrategies.lean).
Its [receipt](lean/proposals/demand-storage-next/lookup-strategies-checks.json)
records 25 audited declarations with no axioms. The model constructs local
witnesses when a tighter gate is false, classifies the first/last static edge,
and proves the FLOW-actual shortcut under the unchanged emitter contract.
It includes own-B, W-R-without-B, mapped-reader and carry witnesses.
Local primitive coverage is an explicit assumption, not a fact inferred from
an arbitrary partial index. AP geometry, visibility, ZERO/carry, mask transport
and concrete worklist adapters remain production proof gates.

Required negative controls include: own FLOW B; W-R with empty B; mapped R
local for C2 but transitive for C5; absent actual T; unrelated local G; unmatched
intermediate source; equal geometry with distinct labels; broad input paths;
ND member union; both protection arrival orders; and cycles with a late mapped
seed. Runtime code and project measurements are unchanged by this proposal.

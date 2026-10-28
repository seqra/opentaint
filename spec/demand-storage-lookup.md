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

All W/B/R composition and call-graph lookup in this document is specific to
the snapshot built at run-1-to-run-2 and queried during run-2. From run-3
onward, `Local(M)` contains only the new method-local inferred demand and
the ordinary implicit ZERO family. Both operations return after direct local
AP processing. They perform no static composition BFS or transitive lookup,
even for static facts or summaries, and retain no old completion component.

## 2. Lookup strategy for each operation

Both operations always query `Local(M)`. A transitive lookup adds candidates;
it does not replace local lookup. A nonempty local result is not a stopping
condition.

### 2.0 Ordered stages and result coverage

Use this order for the whole provided fact or summary:

1. Check direct local demand, including direct local seed views and the
   existing implicit families. Apply AP emission/restriction immediately.
2. If the result is not complete, run query-specific local composition by
   BFS. Use local W/R and own B only. Stop when result coverage is complete.
3. Only then use call-graph transitive visibility for inherited B rows and
   continue the query over the full eligible graph.

```kotlin
fun lookup(query): Results {
    val results = query.emptyResults()
    query.checkDirectLocal(results)
    if (!query.hasStaticCompletion) return results // run-3 and later: local only
    if (query.fullyCovered(results)) return results

    val search = query.startLocalSearch()
    search.runLocalBfs { candidate ->
        query.applyExistingAp(candidate, results)
        query.fullyCovered(results)
    }
    if (query.fullyCovered(results)) return results

    search.enableInheritedRows() // call-graph work starts here
    search.runVisibleBfs { candidate ->
        query.applyExistingAp(candidate, results)
        query.fullyCovered(results)
    }
    return results
}
```

Complete coverage can stop a stage or the entire lookup. Exhausting local
BFS means only “no more local results”; it is not a final negative answer.
The previous endpoint tests still skip impossible work. They do not change
the order or authorize a result.

“Local composition” means the specified static-middle composition of frozen
W/B/R guidance. Do not compose arbitrary ordinary demand pairs through
nonstatic positions or bind a caller again. Own B uses common-method ownership,
including the existing same-method rows from other contexts. W/R keep the
complete MethodKey.

#### Initial-result coverage

For C2, coverage concerns exact emitted InitialAp keys: base, path, tail,
E and mark. Use a conservative bound on the possible result keys from the
relevant rightmost target geometries. It can inspect the frozen target index
without resolving call-graph visibility or composing paths.

For each such geometry, the bound considers the legal abstract entry, if
the row family has one, and the compatible actual-mark entry. An actual FLOW
input has no colored result. A mapped-only EXACT target has no abstract
EXACT/FLOW entry. Do not manufacture one for the bound.

```text
actual: ret.* / T
local entries: ret.* / FLOW, ret.* / T
all possible matching rightmost targets have this same STAR geometry

local results: I(ret.* / FLOW), I(ret.* / T)
coverage: complete
next action: return; no BFS and no call-graph search
```

Another possible `ret.f.*` target or an explicit EXACT target can add a
different key. A STAR result does not cover those keys. For static inputs,
include potential inherited B target geometries in the bound, with visibility
ignored conservatively. Otherwise an inherited EXACT demand could be missed.

Implement the bound as a short-circuit query over immutable geometry metadata,
not a materialized set of all static combinations. Use non-interning potential
keys; do not create hypothetical marked initials merely to test coverage.
An over-approximate bound may delay stopping. It never authorizes emission,
and lookup can still finish by exhaustive search without covering that bound.

#### Summary-result coverage

For C5, equal entry patterns alone do not prove completeness. Results must
retain the full original J and all offered output memberships, with the same
layer, E, mx, tails and protection.

For a packet of STAR/EXACT output leaves, the existing restriction retains
or rejects each typed leaf. Once accumulated results retain every raw leaf
and its protection, further pairs cannot add an output. Use the same canonical
payload representation for this test.

For ANY/MUST leaves, another Dp can yield an EXACT or rebased output. Keep
exhaustive lookup unless a separate conservative output-key bound proves
those results covered too. `Facts.equals` does not compare protection and
cannot serve as this completion test.

#### Entering the call-graph stage

Stage 3 uses M-to-callee reachability, transitively. It does not follow callers
or import another method's formal W/R rows into M. Caller-bound W has already
been attached at the completed transition.

Preserve the local witnesses, either by keeping the states or by finding them
again in a fresh visible search. Stage 3 must:

- Admit newly visible marked-output producer roots.
- Admit matching inherited B terminal rows, including direct mapped/EXACT rows.
- Check inherited adjacency from states already reached during local BFS.
- Apply local closure to every state newly reached through an inherited row.

Track discovery separately from local/remote expansion, or restart the full
visible search with a fresh visited set. Reusing a local visited set as
“fully expanded” would lose remote paths. Each new state needs both eligible
adjacency classes. A negative cache from stage 2 remains local-only.

The call-graph query and producer/terminal admission can be lazy. A final
negative answer requires all relevant pending roots, goals and visible
adjacency to be exhausted. Do not return false merely because one queue
is empty while eligible remote rows remain unexamined.

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
valid for C2. Run the unchanged AP emitter against the bounded actual packet
as each stage supplies candidates. Accumulate its exact result keys before
testing coverage; candidate presence alone does not prove coverage.

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
fun incoming(M, requiredStatic, scope = VISIBLE): Sequence<Seed> =
    localWriters[M].byTarget.around(requiredStatic) +
    sharedBridges.byTarget.around(requiredStatic).filter {
        if (scope == LOCAL) ownedBy(M.method, it) else visible(M, it)
    }

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
the query. The default VISIBLE scope describes the full reference relation.
The local stage must pass LOCAL explicitly and perform no call-graph lookup.

## 5. Transitive lookup for initial admission

C2 needs only a target entry. It must not enumerate all possible original
sources and input marks for that target.

### 5.1 Reader mark rule

Use the reader R, not the writer W, to select the output entry:

```text
R conclusion has selector T:
    offer R.target/T directly

R is FLOW:
    offer its abstract target
    offer R.target/T if a composable marked predecessor concludes T,
    followed by zero or more FLOW B edges into R's input
```

T in this rule is the reader's **conclusion** selector. For a mapped reader
`C.f/U -> ret/T`, offer `ret/T`. For `C.f/T -> ret/U`, offer `ret/U`, not T.
The reader's concrete input mark does not determine the emitted output mark.

The marked predecessor is a local W or visible B. A genuine
`ZERO -> C.f/T` writer is valid. “Zero or more” counts FLOW edges; it does
not exclude ZERO as a real writer origin. W/R retain complete MethodKey
ownership; B uses the existing per-label owner visibility.

This is conservative edge-based completion. It does not try to infer
protected assignments, cleaner survival or internal observations from shape.
It adds no residual classifier, rule-footprint census or permission to omit
a genuinely new marked body.

Offering an entry still uses the actual-input gate. If actual FLOW arrives,
no colored entry emits a concrete initial. For actual full T, a marked output
selector must accept T by the existing directional FULL/GROUP test. No actual
T is manufactured merely because a predecessor mentions it.

### 5.2 Select rightmost seeds

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

### 5.3 Find colors through FLOW prefixes

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

### 5.4 Query one actual mark and stop on a witness

The preceding color-set walk defines all candidate entries. A query for one
actual full T needs only the existence of a compatible predecessor. The
following one-direction walk is a reference procedure; section 5.6 specifies
the selected bidirectional implementation and the staged search order:

```kotlin
fun hasMarkedPrefixFor(M, startStatic, actualT): Boolean {
    val pending = ArrayDeque<Pattern>()
    val visited = CompleteGeometrySet()
    pending.addLast(startStatic)

    while (pending.isNotEmpty()) {
        checkpoint()
        val current = pending.removeFirst()
        if (!visited.add(current)) continue
        for (left in incoming(M, current)) {
            if (!geometryJoins(left, current)) continue
            when (val label = left.label) {
                FLOW -> if (left.from.base == STATIC) pending.addLast(left.from)
                is Mapped -> {
                    if (coversAtom(label.output, actualT)) return true
                    // Stop this branch even if its output does not match T.
                }
            }
        }
    }
    return false
}
```

`coversAtom` is directional selector acceptance. Do not substitute symmetric
mapped-middle compatibility or same-group equality for this test. The static
output selector is real; nullable ZERO selectors cannot occur at this output.

For each complete reader target geometry, compute the potential T initial
with the unchanged AP emitter. Skip the prefix query if that key set is empty
or already included in the accumulated result. Otherwise stop after the first
compatible witness and add those exact emitted keys. Keep the abstract entry
separately. Distinct tails, paths and E require separate coverage checks.

This optimization preserves the exact initial set. It stops redundant search;
it does not discard the marked execution for a newly admitted T key.

### 5.5 A mark-changing predecessor ends the color branch

```text
W: p/T -> C.f/T
B: C.f/T -> C.g/U
R: C.g/FLOW -> ret/FLOW
```

R can gain U from B's conclusion. It cannot gain T by continuing through
that mapped B to W. The suffix from W to R contains a mark change, not only
FLOW edges. A search for actual T stops at the incompatible U output; a
search for U succeeds there. The T search still checks other predecessor
branches. C5 can continue through B and W to obtain
the complete pair `(ret/U, p/T)`.

Without B's mark change, `W: p/T -> C.f/T` followed by a FLOW B chain and
a FLOW reader offers ret/T. Without any compatible marked predecessor, the
FLOW reader supplies only its abstract entry. This does not suppress a
marked entry from another ordinary local demand.

### 5.6 Bidirectional BFS for the Boolean reader query

For a FLOW reader and an actual T, ask only:

```text
Does an eligible marked edge concluding T reach R.input
through zero or more FLOW B edges?
```

Use two frontiers of complete static geometries:

- Forward: output positions of eligible local W or visible B whose conclusion
  selector accepts actual T. These are marked predecessor roots.
- Backward: the FLOW reader's static input position.

Mapped rows are roots only. Each traversal step uses a real FLOW B. The root's
input color is not enumerated. Do not build a complete composed relation merely
to decide this Boolean.

```kotlin
fun forwardStep(output, scope): Sequence<Pattern> =
    flowBridgesByInput(scope, output)
        .filter { joinEndpoints(output, it.from) }
        .map { it.to }

fun backwardStep(input, scope): Sequence<Pattern> =
    flowBridgesByOutput(scope, input)
        .filter { joinEndpoints(it.to, input) }
        .map { it.from }

fun meet(forwardOutput, backwardInput): Boolean =
    joinEndpoints(forwardOutput, backwardInput)

fun joinEndpoints(output, input): Boolean =
    staticAnchor(output) == staticAnchor(input) &&
    existingGeometryOverlap(output, input)
```

The helper takes two Pattern endpoints. It uses the same static-anchor
and overlap test as the existing edge/current helper. The forward side always
denotes an output; the backward side always denotes an input. A meeting must
be one valid oriented output-to-input join. Do not join two inputs, two outputs,
or an arbitrary chain of overlapping geometries without an intervening FLOW B.
Use matching anchor buckets for meeting tests; do not form a frontier Cartesian
product. No additional IR or stored port objects are required.

```kotlin
fun needsT(reader, actualT, scope): SearchResult {
    val forward = OutputFrontier()
    val backward = InputFrontier()
    forward.openEligibleMarkedOutputs(scope, actualT) // lazy root iterator
    backward.admit(reader.input)
    if (frontiersHaveValidJoin()) return FOUND

    while (hasPendingEligibleRootsOrExpandableFrontier(scope)) {
        if (admitNextRootAndCheckJoins(scope)) return FOUND
        if (!hasExpandableFrontier(scope)) continue // more roots may remain
        val side = chooseSmallerExpandableFrontier()
        val state = side.popFifo()
        for (next in side.steps(state, scope)) {
            if (side.discover(next) && joinsOppositeVisited(next)) return FOUND
        }
    }
    return if (scope == LOCAL) LOCAL_NOT_FOUND else COMPLETE_NOT_FOUND
}
```

This function shows a fresh search for one scope. A visible-stage restart
may use it directly. A state-preserving implementation instead retains these
frontiers and reactivates their inherited expansions as specified above.

All admission routines check joins, including a root admitted after its
opposite frontier was visited. Expand complete states once per side and
adjacency phase. When stage 3 enables inherited rows, old local states gain
their inherited expansions and new states receive local expansions too.
The queue contract must account for that reactivation; a discovered bit
alone is insufficient.

The logical forward root set contains all eligible conclusions for this
actual T in the selected scope. Use the existing output-selector index, not
a scan of every mark. It can be represented lazily; a membership check against
a backward-reached position can establish a witness before all roots are
materialized. A negative result still needs complete root/adjoining-row
coverage. Do not treat an unexamined root iterator as an empty source set.
Root admission and expansion must both progress while work remains. For a
backward state, first probe compatible marked outputs in its location bucket.
This can answer the query without allocating all T roots. The logical root
set is unchanged. The query does not build a retained per-T graph or enumerate
all full marks or group members.

The loop above is a complete reference scheduler. A stricter exhaustion
certificate can stop it earlier: a fully closed backward frontier with
complete producer-index probes has no matching root, or a fully closed
forward frontier containing all eligible roots has no join to the reader.
These certificates apply only to the current scope. An empty queue with
pending eligible roots or unexpanded inherited adjacency is not a certificate.

Choose the smaller frontier or lower estimated adjacency work to expand.
No shortest path is required. Return true at the first verified meeting;
the witnesses on its two sides form the required primitive path. A false
answer is final only for the complete visible scope on the fixed snapshot.

Local phase roots are local marked W and own marked B. Local transfer rows
are own FLOW B. The call-graph phase adds visible inherited marked B roots
and FLOW B transfers. Ordinary direct mapped readers still use their direct
entry; inherited direct mapped B targets still use direct AP emission.
Neither case needs this Boolean prefix search.

For multiple readers or targets which can emit the same exact initial key,
one witness is enough to admit that key. Keep target/key association when
sharing work; another geometry may require a different initial. Check whole
fact coverage before starting or resuming any remaining reader search.

## 6. Transitive lookup for summary restriction

C5 needs the original source and target, so it follows both FLOW and mapped
prefixes. It must not use the C2 stop-at-first-mapped rule or replace paired
restriction with the unlabelled bidirectional Boolean. Use the same ordered
direct-local, local-BFS, then visible-call-graph stages. Complete summary
coverage can stop after any stage or accepted result.

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

fun transitivePairsReference(M, j, G, scope, emitPair) {
    val pending = ArrayDeque<PairState>()
    val visited = HashSet<PairState>()

    fun offer(s) { if (visited.add(s)) pending.addLast(s) }
    for (last in rightmostReadersAndBridges(M, j, scope))
        offer(stateOf(last))

    while (pending.isNotEmpty()) {
        checkpoint()
        val state = pending.removeFirst()
        val pair = directionalDemand(state) // Dc=target, Dp=from
        if (couldRestrict(j, G, pair)) emitPair(pair)

        if (state.from.base != STATIC) continue
        for (left in incoming(M, state.from, scope)) {
            if (!geometryJoins(left, state.from)) continue
            val label = composeMarks(left.label, state.label) ?: continue
            offer(stateWithEndpoints(left.from, state.target, label))
        }
    }
}
```

This is the complete walk for one fixed scope. The staged implementation
first runs it with LOCAL. If result coverage is incomplete, it enables the
VISIBLE rows. Preserve states with separate expansion bits, or restart this
reference walk with a fresh visited set. Stage 3 can use local and inherited
rows in any order. A remote-only continuation is insufficient.

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

**Staging and coverage.**
[StagedDemandLookup.lean](lean/proposals/demand-storage-next/StagedDemandLookup.lean)
has [25 axiom-free audits](lean/proposals/demand-storage-next/staged-demand-lookup-checks.json).
It converts each mixed local/remote path constructively to initial local
closure followed by repeated remote steps with local closure, and back.
It proves equal result sets, safe stopping under a complete output-key bound,
and the distinction between a first positive witness and an exhausted
negative answer. Its finite examples show why remote images need local
closure and why local discovery does not imply remote expansion.

**Bidirectional existence.**
[BidirectionalDemandExists.lean](lean/proposals/demand-storage-next/BidirectionalDemandExists.lean)
has [20 axiom-free audits](lean/proposals/demand-storage-next/bidirectional-demand-exists-checks.json).
The proof graph has directed output-to-input joins. Only a real FLOW B gives
an input-to-output transfer. Append the forward witness, the meeting join,
and the backward witness to obtain the required marked-output-to-reader path.
Conversely, complete typed frontier closure reaches a meeting for every such
path. A complete frontier with no valid meeting proves absence in that scope.
The model includes an inherited join between previously reached local states
and a negative example where undirected overlap would invent a false path.
These logical proof ports require no new runtime representation.

Each query has a finite set of roots and complete geometry states. Each side
expands a state at most once per adjacency phase; a late visible phase can
reactivate it once. Fair root admission and queue expansion therefore end.
These are design obligations for the concrete BFS adapter, not claims that
the local Lean graph models verify a production scheduler or index. The
two-frontier search can reduce visited states before a witness. Its worst
case can still visit the entire relevant component; no measured speedup is
claimed.

Required negative controls include: own FLOW B; W-R with empty B; mapped R
local for C2 but transitive for C5; absent actual T; unrelated local G; unmatched
intermediate source; equal geometry with distinct labels; broad input paths;
ND member union; both protection arrival orders; and cycles with a late mapped
seed. Runtime code and project measurements are unchanged by this proposal.

## 9. Worked examples

These examples instantiate the lookup rules above. They do not change them.
Each example is independent. The displayed rows determine the stated result;
another path with the same result does not add a second initial or publication.
A listed reader is already activated by a corresponding write. That write
need not be a local W row for the querying method. Read activation and caller
binding have finished before these frozen-demand lookups.

Notation:

```text
p, q             method arguments
ret              method return base
C.f              static base S, class C, named static field f
x.* / T          field tail STAR, concrete full mark T
x.* / FLOW       field tail STAR, abstract mark slot *, not a concrete mark
x.$ / T          field tail EXACT, concrete full mark T
(Dc, Dp)         one complete demand pair
I(x.* / T)       an initial key returned by initials(), not a summary edge
D                 DEMAND layer of an offered or returned conclusion
```

Field E and FLOW mx are empty unless shown. T, U and V are full marks.
Different full marks do not match merely because they have the same group.
All shown field paths fit the iteration's field limit.

Examples use incoming run-2 unless stated otherwise. Its static carry family
is enabled. Every static example includes that family's contribution.
Initial keys have no layer. Existing initial emission assigns a layer to
their body facts; in particular, a concrete EXACT key and a concrete STAR key
are distinct. C5 examples return the supplied DEMAND layer unless stated
otherwise. Protection is empty except in example 9.14.

### 9.1 Ordinary local demand: both operations

Stored ordinary pair:

```text
d1 = (ret.* / U, p.* / T)
No matching W, B or R.
```

Provided fact: `ret.* / U`.

1. The local entry index returns `ret.* / U`.
2. No FLOW reader target matches. Select local-only lookup.
3. AP emission intersects that entry with the actual marked fact.

Result: `{ I(ret.* / U) }`.

Provided summary: `ret.* / U -> p.* / T [D]`.

1. The local entry/output indexes select the same row d1.
2. The whole initial lies inside d1.Dc; its output meets d1.Dp.
3. No skipped-static endpoint matches. AP restriction keeps the conclusion.

Result: the supplied summary, including its original premise and D layer.
For `ret.* / U -> q.* / T [D]`, d1's output base does not match. Result: empty.

### 9.2 An entry with no output demand

Stored ordinary demand: `(ret.* / U, no Dp)`. No matching static seeds.

Provided fact: `ret.* / U`.

1. Local entry lookup includes this row even though Dp is absent.
2. The local-only AP emission matches U.

Result: `{ I(ret.* / U) }`.

Provided summary: `ret.* / U -> p.* / T [D]`.

1. The row has no output-index entry.
2. It cannot pass C5; no transitive path applies.

Result: empty. Permission to start an initial is not permission to publish
every result inferred under that initial.

### 9.3 A mapped reader: local C2, transitive C5

Frozen local seeds:

```text
W: p.* / T   -> C.f.* / T
R: C.f.* / T -> ret.* / U
B: empty

Local direct pairs:
    (C.f.* / T, p.* / T)
    (ret.* / U, C.f.* / T)
```

Provided fact: `ret.* / U`.

1. Local R already supplies the complete entry `ret.* / U`.
2. Its last relation is mapped, so an earlier prefix cannot change U.
3. Use local-only C2; do not visit W.

Result: `{ I(ret.* / U) }`.

Provided summary: `ret.* / U -> p.* / T [D]`.

1. The direct R pair requests output `C.f.* / T`, not p. It gives no result.
2. The R-target and W-source tests both succeed. B can remain empty.
3. Start the reverse walk at `C.f.* / T -> ret.* / U`.
4. Continue through W, although the intermediate source C.f does not match p.
5. Obtain `p.* / T -> ret.* / U`, hence pair `(ret.* / U, p.* / T)`.

Result: the supplied summary. Retain the full original `ret.* / U` premise.
Do not change the result to `p.* / U` or stop at the intermediate C.f source.

### 9.4 FLOW reader and a longer static path

Frozen seeds, visible at M:

```text
W: p.* / T   -> C.f.* / U
B: C.f.* / U -> C.g.* / V
B: C.g.* / FLOW -> C.h.* / FLOW
R: C.h.* / FLOW -> ret.* / FLOW
```

Provided fact: `ret.* / V`.

1. Local R supplies `ret.* / FLOW`. AP emission gives `I(ret.* / FLOW)`.
2. The local FLOW reader target matches. Start color search at C.h.
3. The FLOW B predecessor moves the search to C.g.
4. The mapped B predecessor outputs V. Offer entry `ret.* / V`.
5. Stop that branch at the mapped predecessor. C2 does not need W's source T.
6. AP emission matches the actual V.

Result: `{ I(ret.* / FLOW), I(ret.* / V) }`.

Provided summary: `ret.* / V -> p.* / T [D]`.

1. Local R and all intermediate static-source pairs fail the output-base test.
2. Both endpoint guards succeed. Walk R, FLOW B, mapped B, then W.
3. The successive forward-oriented states are:

```text
C.h.* / FLOW -> ret.* / FLOW
C.g.* / FLOW -> ret.* / FLOW
C.f.* / U    -> ret.* / V
p.* / T      -> ret.* / V
```

4. The final state yields `(ret.* / V, p.* / T)` and passes C5.

Result: the supplied summary. C5 continues past the mapped B that ended
the C2 color search. The composed label sets both endpoint marks.

### 9.5 Actual FLOW and a different actual full mark

Use the seed inventory from 9.4.

Provided fact: `ret.* / FLOW`, optionally with `mx={V}`.

1. Local R supplies the abstract entry.
2. The actual FLOW shortcut selects local-only lookup. Do not visit B or W.
3. AP emission returns the shared abstract initial; it does not copy mx
   from the actual into the initial key.

Result: `{ I(ret.* / FLOW) }`. No concrete V initial is created.

Provided fact instead: `ret.* / U`, with U distinct from V.

1. Local abstract emission still gives `I(ret.* / FLOW)`.
2. The color search offers the V entry as in 9.4.
3. The actual full U does not satisfy a full V entry. AP emission rejects it.

Result: `{ I(ret.* / FLOW) }`. A location match alone cannot supply V.

### 9.6 Own FLOW B: include carry and deduplication

Frozen seeds at M:

```text
W: p.* / T -> C.f.* / U
own B: C.f.* / FLOW -> C.g.* / FLOW
```

Provided fact: `C.g.* / U`.

1. Own B's direct local entry emits `I(C.g.* / FLOW)`.
2. Same-slot static carry has entry `C.g.* / U`; it emits `I(C.g.* / U)`.
3. The shared B target index includes own B. Search its FLOW prefix at C.f.
4. W outputs U, so the search offers `C.g.* / U` again.
5. Deduplicate the repeated initial key.

Result: `{ I(C.g.* / FLOW), I(C.g.* / U) }`.
The transitive candidate does not create a second U initial. Carry already
provided that key.

Provided summary: `C.g.* / U -> p.* / T [D]`.

1. Carry's Dp is C.g, and the direct B pair's Dp is C.f. Neither matches p.
2. The B-target and W-source guards succeed.
3. Compose W with own B to obtain `(C.g.* / U, p.* / T)`.

Result: the supplied summary. Carry does not replace this cross-position pair.

### 9.7 An inherited EXACT target adds a distinct initial

One B row is owned by reachable callee N, not M:

```text
B at N: C.f.* / T -> C.g.$ / U
```

The concrete EXACT target is legal under a concrete premise. It denotes
the named field C.g, not a class-wide mark. No new rule-literal grammar is used.

Provided fact: `C.g.* / U`.

1. Local same-slot carry emits `I(C.g.* / U)`.
2. The shared B target is near the actual. Check that M can reach owner N.
3. Retrieve the one-edge mapped B; no prefix color traversal is needed.
4. Its Dc is `C.g.$ / U`. AP tail intersection with the actual STAR yields
   the EXACT key.

Result: `{ I(C.g.* / U), I(C.g.$ / U) }`.
The EXACT key follows an explicit EXACT demand. It is not automatic
completion of an ANY or STAR query. Its body fact uses the existing EXACT
initial-emission rule.

Provided summary: `C.g.$ / U -> C.f.* / T [D]`.

1. Carry cannot connect C.g to C.f.
2. The target and source B indexes match. Retrieve the same visible B row.
3. C5 accepts its pair `(C.g.$ / U, C.f.* / T)`.

Result: the supplied summary.

If the supplied initial is instead `C.g.* / U`, that whole STAR initial is
not inside this EXACT Dc. With no other connecting pair, C5 returns empty.
If N is unreachable, the B row is invisible: C2 returns only the carry STAR
key, and the cross-position C5 query returns empty. The cheap indexes can
still be positive; visibility is checked during lookup.

### 9.8 Static FLOW: shared direct lookup without color search

Use an inherited B row visible at M and a local or actual-caller-bound W at M:

```text
B: C.f.* / FLOW -> C.g.* / FLOW
W: p.* / T -> C.f.* / U
```

Provided fact: broad abstract `S.* / FLOW` in a restricted run.
This is a FLOW input, not an invalid broad concrete static input. Run-1
still does not propagate this root fact.

1. Same-slot carry at S emits `I(S.* / FLOW)`.
2. The shared FLOW B target C.g is below the provided root. Select the
   shared-direct route and check B visibility.
3. The B target entry emits `I(C.g.* / FLOW)`.
4. Do not follow W or collect U: a colored entry cannot emit from actual FLOW.

Result: `{ I(S.* / FLOW), I(C.g.* / FLOW) }`.
For a provided named-field `C.g.* / FLOW` instead, both routes emit the same
named-field key. The final result then has one key after deduplication.

### 9.9 Positive endpoint tests but no connected path

Local seeds:

```text
W: p.* / T -> C.a.* / T
R: C.b.* / T -> ret.* / U
No B connects C.a and C.b.
```

Provided summary: `ret.* / U -> p.* / T [D]`.

1. Local R's output demand is C.b, so local restriction returns nothing.
2. The R target and W source both match the query's endpoint tests.
3. Start at `C.b.* / T -> ret.* / U`.
4. No incoming row ends at C.b. W ends at C.a and cannot join.

Result: empty. Never combine the R target with the disconnected W source.

### 9.10 A matching field with incompatible full marks

Local seeds:

```text
W: p.* / T -> C.f.* / U
R: C.f.* / V -> ret.* / T
U and V are distinct full marks, even if their group is equal.
```

Provided summary: `ret.* / T -> p.* / T [D]`.

1. The local direct pairs do not connect ret to p.
2. The location guards succeed; start from R.
3. W's endpoint has the right static anchor and overlapping geometry.
4. Mark composition fails at U versus V. Do not enqueue a combined state.

Result: empty. Group membership alone does not make two different FULL
selectors equal. With a compatible GROUP selector, use the existing
FULL/GROUP composition rule instead; do not change it for this lookup.

### 9.11 Preserve the row pairing in ordinary demand

Stored pairs:

```text
d1 = (ret.* / T, p.* / T)
d2 = (ret.* / U, q.* / U)
No matching static seeds.
```

Provided fact: `ret.* / T`.

1. Local positional lookup can return both entries.
2. The full-mark AP test accepts T and rejects U.

Result: `{ I(ret.* / T) }`.

Provided summary: `ret.* / T -> q.* / U [D]`.

1. Positional entry lookup can select both IDs. Output lookup at q selects
   only d2, so their ID intersection is `{d2}`.
2. AP rejects d2 because its complete entry requires U, not T.
3. d1 would match the entry mark, but its p output removed its ID before
   restriction. The transitive guards add nothing.

Result: empty. Combining d1.Dc with d2.Dp would create an invalid result.

### 9.12 AP boundary cases: FLOW output and field exclusions

First, use this valid ordinary AP demand pair, without a W/B/R graph:

```text
d = (ret.* / FLOW, p.* / T)
provided summary = ret.* / FLOW -> p.* / FLOW, mx={U}, layer D
T is not U.
```

This is an ordinary AP boundary example, not a mixed-label static seed.

1. The whole abstract initial is inside d.Dc.
2. `marksMeet` accepts d.Dp's T because the provided FLOW excludes U, not T.
3. The conclusion has the same p location and STAR tail. C5 retains it whole.

Result: the supplied FLOW summary, still with `mx={U}` and layer D.
No concrete T conclusion is generated. If the provided mx is `{T}` instead,
the mark test fails and the result is empty.

For field exclusions, consider a later restricted run that can have nonempty E:

```text
d = (p.* / T, E={left}; ret.* / U)
provided summary = p.* / T, E={} -> ret.* / U [D]
```

1. Positional indexes find d; the locations overlap.
2. The whole initial includes p.left, but d.Dc excludes it.
3. Whole-member containment fails before output restriction.

Result: empty. The demand is concrete: its E remains meaningful. An abstract
STAR demand would have its E normalized to empty and is not this example.

### 9.13 ZERO input, genuine ZERO writer and engine bypass

With only implicit `(ZERO, no Dp)`, provide actual ZERO.

1. Local lookup returns its implicit entry.
2. AP emission returns `I(ZERO)`.

Result: `{ I(ZERO) }`. A restricted forward summary `ZERO -> p.* / T [D]`
has no output permission from that entry and returns empty if no other pair
applies.

Now use genuine frozen seeds:

```text
W: ZERO -> C.f.* / T
R: C.f.* / FLOW -> ret.* / FLOW
```

Provided fact: `ret.* / T`.

1. Local R emits `I(ret.* / FLOW)`.
2. Color search meets W and offers T at ret. Its input selector remains ZERO.
3. AP emission accepts the actual T.

Result: `{ I(ret.* / FLOW), I(ret.* / T) }`.

Provided backward summary: `ret.* / T -> ZERO [D]`.

1. Its premise is not ZERO, so it has no backward-ZERO bypass.
2. The R-target and genuine ZERO W-source tests succeed.
3. Compose W-R and obtain the actual pair `(ret.* / T, ZERO)`.
4. C5 retains the ZERO conclusion through that pair.

Result: the supplied summary. Without that pair or another valid output
demand, a ZERO conclusion alone would not authorize publication.

By contrast, a backward summary whose **original premise is ZERO** follows
the existing engine seed-return branch before this API. It is not a lookup
result and does not turn every ZERO conclusion into an exception.

### 9.14 Later forward run: keep ND premises and protection

This example is for a later restricted forward run, such as run-3. Run-1
still has no ND edges. Use ordinary local demand only:

```text
d1 = (p.* / T, ret.a.* / V)
d2 = (q.* / U, ret.b.* / V)

provided summary:
    J = { p.* / T, q.* / U }
    J -> { ret.a.* / V, ret.b.* / V } [D]
    ret.b/V is protected; ret.a/V is unprotected.
```

1. For member p, d1 keeps the a part. Reattach the whole J.
2. For member q, d2 keeps the b part. Reattach the same whole J.
3. No skipped-static component is attached in this later snapshot.
4. AP restriction transports the b protection to its surviving part.

Result:

```text
J -> ret.a.* / V [D], unprotected
J -> ret.b.* / V [D], protected
```

The API does not replace J with singleton premises or require J as a whole
inside either scalar Dc. If equal ordinary output payloads reach its result
accumulator with different protection masks, their masks are unioned.

### 9.15 A cycle with a reachable mapped writer

Visible seeds:

```text
W: p.* / T -> C.g.* / U
B: C.f.* / FLOW -> C.g.* / FLOW
B: C.g.* / FLOW -> C.f.* / FLOW
R: C.f.* / FLOW -> ret.* / FLOW
```

Provided fact: `ret.* / U`.

1. Local R emits the shared FLOW initial.
2. Color search visits C.f, then C.g through the incoming FLOW B.
3. W offers U. The other FLOW B returns to the already visited C.f state.
4. Suppress that repeated state, not W's newly found color.

Result: `{ I(ret.* / FLOW), I(ret.* / U) }`.

For `ret.* / U -> p.* / T [D]`, the C5 walk also reaches W and keeps the
summary. Its repeated FLOW state is suppressed. It does not store path length
as a new state coordinate or enumerate an unbounded sequence of cycle paths.

### 9.16 Direct local coverage stops the whole query

```text
actual: ret.* / T
local demands: (ret.* / FLOW, p.* / FLOW), (ret.* / T, q.* / T)
possible matching rightmost geometry: ret.* only
```

Direct AP emission gives `I(ret.* / FLOW)` and `I(ret.* / T)`.
Those are all legal keys in this query's result bound. Return both. Do not
start local composition, enumerate T producer roots or query the call graph.
If another target geometry can emit a distinct initial, coverage is not
complete and this stop is unavailable.

### 9.17 A local bidirectional meeting

```text
W local: p.* / T -> C.a.* / T
B own:   C.a.* / FLOW -> C.b.* / FLOW
B own:   C.b.* / FLOW -> C.c.* / FLOW
R local: C.c.* / FLOW -> ret.* / FLOW
actual:  ret.* / T
```

1. Direct local R emits `I(ret.* / FLOW)`. The T key is still missing.
2. The forward root is W's `C.a` output. The backward root is R's `C.c` input.
3. A forward step through the first B reaches its `C.b` output. A backward
   step through the second B reaches its `C.b` input.
4. Their oriented geometry join is valid. The two path fragments give
   `W; B; B; R`, so the reader offers T. AP emits `I(ret.* / T)`.
5. If these two keys cover the bound, return. No call-graph query is needed.

No composed W-B-B-R row is stored. The query needs only the witness and
the resulting initial key.

### 9.18 The visible stage must reuse local links

```text
W local:     p.* / T -> C.a.* / T
B inherited: C.a.* / FLOW -> C.c.* / FLOW
B own:       C.c.* / FLOW -> C.d.* / FLOW
B inherited: C.d.* / FLOW -> C.e.* / FLOW
R local:     C.e.* / FLOW -> ret.* / FLOW
actual:      ret.* / T
```

Direct lookup emits the FLOW initial. Local BFS finds no T path. This is
only `LOCAL_NOT_FOUND`.

After inherited visibility is enabled, the forward search can reach C.c
through the first inherited B. It must expand the own C.c-to-C.d B, then
the second inherited B. The backward frontier can meet the C.e output.
The result includes `I(ret.* / T)`. A remote-only continuation would miss
the middle local link. A local visited bit must not suppress newly enabled
inherited adjacency on an old state.

### 9.19 A local STAR key does not cover an inherited EXACT target

```text
actual: C.g.* / T
own B:       C.a.* / FLOW -> C.g.* / FLOW
inherited B: C.b.* / U -> C.g.$ / T
```

1. Direct local demand and static carry emit the legal STAR initials,
   including `I(C.g.* / FLOW)` and `I(C.g.* / T)`.
2. Immutable target metadata also contains the distinct EXACT target C.g.$.
   Its mapped row has a possible `I(C.g.$ / T)` result. The local keys do
   not cover this key, so lookup cannot stop on STAR coverage.
3. In the visible stage, the inherited row passes its owner test. Its direct
   target offers T; AP emits `I(C.g.$ / T)` from the supplied actual STAR/T.

The inherited row needs direct-target admission, not a Boolean search around
an already known local R. No `C.g.$ / FLOW` key is invented for this mapped
EXACT row.

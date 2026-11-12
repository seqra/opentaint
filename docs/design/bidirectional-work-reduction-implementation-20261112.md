# Analyzer work reduction: implementation proposal

**Proposal. No runtime change.** This document implements
[Analyzer work reduction](../../spec/in-handoff-edge-compaction.md).
Source reviewed: `e078dd49545f21e2e377e7f8932aab2a871eda58`.
Follow [the proof guide](../../spec/proof-guide.md) before each runtime edit.
Code below is pseudocode unless it names an existing API.

## 1. Scope and acceptance

| Part | Current work | Proposed work | Semantic contract |
| --- | --- | --- | --- |
| Handoff | Deduplicate identical projected rows. | Remove outgoing origins covered by retained origins. | R1/R2 and exact R4 preserve complete demand services. New residual MAY cases require the progress proof below. |
| C2 | Visit strict descendants of STAR/EXACT inputs, then reject them. | Do not visit those descendants. | Same complete ordered initial families. |
| Loop probe | Finish C2 and enclosing observation for every trial. | Stop a losing trial at its first extra admission; reuse completed C2 results. | Same chosen cut, drop or raw fallback. |
| Disabled diagnostics | Retain inputs before a callback with no tracker. | Do not create that diagnostic archive. | Same semantic output; enabled diagnostic behavior stays the same. |
| FULL caller inputs | Retain one qualified packet per original mark. | Share geometry; retain diagonal sets and exact changing-mark pairs. | Same complete snapshots, fresh deltas and delivery. |

Keep initial emission, paired C5, field limits, marks, GROUP mode, aliases,
cleaners, protection, rules, source permissions, Targets and reports unchanged.
Keep the selected call policy: saved summaries, demand admission, current
summaries and subscriptions. Packing changes storage, not rule execution.
Private keys and certificates must not enter public equality or hashing.

**Activation boundary.** Implement R1, R2 and exact-service R4 first. The spec
also selects residual cross-lane MAY coverage, R3, and broader R4 arms. Their
native eventual-refinement proof is still open. Do not enable those removals
until it is checked. Do not replace that proof with a run-11 experiment, an
unrelated extra supplier, or a change to C2. This is a development gate, not
a new runtime option.

Notation:

```text
P -> C          complete original premise and conclusion packet
N, D           NORMAL and DEMAND
$, *, MAY, MUST EXACT, STAR, [any], [any-taint]
E, mx          field exclusions and FLOW mark exclusions
T, U           full concrete marks, with their existing metadata
H              literal plain/protected membership
scope          complete method/context, direction, block and physical ports
G(X)           existing complete next-demand projection of origin X
```

## 2. Handoff compaction

### 2.1 Owner and data

Run the compactor after all workers join. It is private to `HandOff.of`.
It reads frozen current summaries and outgoing DemandTargets. It does not
modify them. Persist NORMAL records through the existing record store.

```kotlin
// Private driver types. IDs are local array addresses, never semantic keys.
data class GuidanceOrigin(
    val scope: CompleteScope,
    val source: FrozenSummaryOrDemandTarget,
    val protection: DataHOrTypedControl,
)
data class ProjectedRow(
    val origin: OriginId,
    val native: NativeDemandRow, // includes the complete owner/ports
)
data class ServiceWitness(val provider: OriginId, val row: RowId)
data class RowCover(val c2: ServiceWitness, val c5: ServiceWitness)
data class RemovalCertificate(val removed: OriginId, val rows: List<RowCover>)

class HandoffCompactor {
    val origins: FrozenOriginTable
    val rows: CompleteProjectionIndex
    val kept: MutableOriginSet
    val certificates: Map<OriginId, RemovalCertificate>
    val dependents: Map<OriginId, Set<OriginId>>
}
```

Capture all existing outgoing origins: method rows, generated block rows,
NORMAL ND rows selected for guidance, and DemandTargets. Capture every
premise member and conclusion leaf. NormalTarget does not supply guidance.
Do not reduce ND premises to a representative or a Cartesian product.
Typed ZERO/Target rows have their existing control keys, not DATA prefix keys.

Use complete decoded equality after every hash match. Include marks, E/mx,
H, context and physical ports. A private geometry key must not erase these
coordinates from a service key. In particular, plain cannot cover protected,
and protected cannot cover plain.

Keep references to immutable origins and shared row payloads. Do not make a
second snapshot of every packet or build an uncompacted `DemandStore` first.
Release the origin index and certificates after the final store is built.

### 2.2 Rules and comparison keys

These are outgoing-guidance rules, not executable transfer rules:

```text
R1: X = a.f.MUST/T -> C,D
    Y = a.f.*   /T -> C,D
    same complete C; empty E on the compared projected premise selectors
    => Y can replace X's guidance

R2: X = P -> a.p.$/T,D
    Y = P -> a.p.*/T,D
    same complete P; EXACT E empty; STAR E legal
    => Y can replace X's guidance

R4, exact service form:
    X = {I1,...,In} -> C
    for EVERY Ii and EVERY leaf c in C:
        find retained C2 and C5 witnesses for (g(c),g(Ii))
    => omit X's guidance, keeping its executable ND meaning unchanged

R3, after the progress gate:
    X = P -> Cx,D; Y = P -> Cy,D
    same P/scope/H/full mark/static anchor; adapter E empty
    Req(Cx) subset Req(Cy)
    => retain Y and omit X's guidance
```

For R3, `Req(point.$/T) = Req(point.*/T) = {point.$/T}`.
`Req(point.MAY/T)` includes all legal exact suffixes. An ancestor STAR is
not a wildcard for descendant points. Require an actual retained Y; do not
construct a wider row. Same-premise MAY coverage within the scalar store
already exists. The new case is coverage between surviving storage lanes.

Use the existing service laws through these private adapters:

```text
entryKey(p):
    if legal late FULL concrete STAR/T or empty-E EXACT/T:
        return same complete head with tail EXACT and empty E
    return literal p

outputKey(p):
    if empty-E DATA MAY: return same complete head with tail STAR
    return literal p

c2Covers(q, z):
    return same entry owner/port && entryKey(q.entry) == entryKey(z.entry)

c5Covers(q, y):
    return same owner/physical exit && outputKey(q.output) == outputKey(y.output)
       && (entryKey(q.entry) == entryKey(y.entry)
           || provedNativePointToMayImageContains(y.entry, q.entry))
```

The point adapter supports This, Argument, Return, LocalVar, Exception and
legal ClassStatic anchors. It excludes FLOW, GROUP, literals and cleaner
temporaries. The C5-only point-to-MAY adapter supports This/Argument/Return/
LocalVar, at the same path or the first counted extension: CLASS accessors,
then one FIELD/ELEMENT, then end. Retain its existing shape/budget guards.
Do not apply this C5 adapter to C2.

Each exact-service removal needs nonempty complete G(X), with a retained
witness for both services of every row. The two witnesses can differ.
Retain complete initial families, layers, companions and precision support.
An absent or self witness cannot justify a removal.

### 2.3 Selection and final witnesses

Use the existing projection as the one source of native row contents.
Refactor it to an emitter shared by method/block collection and final
insertion. Keep the old block-port reversal and run-1 completion callbacks.

```text
handoff(config, completed):
    assert completed.status == COMPLETE and workersJoined
    keep existing report preparation and NORMAL persistence
    if config.mode.markMode != FULL or destinationRun < 3:
        return existingHandoff(completed)

    O = collectExistingOutgoingOrigins(completed)
    rows = existingProjection(O)       // every member, leaf and typed control
    index = indexCompleteServiceKeys(rows)
    K = all O; certs = {}; dependents = {}

    for X in stableDecodedFullKeyOrder(O):
        trial = K without X
        affected = dependents[X]       // removed origins whose flat proof uses X
        replacements = {}
        for old in affected plus X:
            proof = findProofClosedCover(old, trial, index)
            if proof is absent: reject this removal; break
            replacements[old] = proof
        if every required proof exists:
            remove X from K/index
            replace affected certificates and reverse dependencies atomically
            certs[X] = replacements[X]

    assert every certificate names actual rows of final K
    builder = existing DemandStore.Builder
    counts = empty
    for Y in stable order of K:
        for q in rows[Y]:
            if existingNormalizedAdd(builder, q): counts[q.method] += 1
    return existingHandoffState(builder.build(), counts, unchangedSeeds)
```

Index C2/output service keys by complete scope and full-key hash. Store a
bucket of distinct active provider origins, with an actual row witness per
origin, in the same stable decoded-key order. For exact-key lookup, exclude
X before selecting a provider. For the
bounded point-to-MAY adapter, visit only its legal path prefixes. Retain a
full-key comparison; a hash or an interner ID alone is not a proof.

Certificates name final providers directly. If A covers B and B covers C,
then deleting B must rebind C to A or reject the deletion. Do not retain a
chain through a deleted provider. Two equivalent origins cannot delete each
other. A stable order of decoded values makes the retained basis independent
of arrival order; it need not be the smallest basis.

The full-reference algorithm rechecks every prior certificate at each trial.
The indexed algorithm rechecks only `dependents[X]` plus X. An unaffected
certificate still names kept providers. The new constructive model proves
this update law. Keep the reference algorithm in tests and compare final
valid certificates and service sets, not allocation IDs.

### 2.4 Integration and cost

`IterationDriver.barrier` keeps its existing report/persistence/commit order.
`RunSummaryStore` and `PersistentRecordStore` keep their existing behavior.
No second NORMAL compaction pass is needed: literal union, aligned NORMAL
FLOW specialization, FLOW-backed T coverage and saved-record merging already
exist. Keep all NORMAL contributors, source hits, seeds and report IDs.

For n origins and r projected rows, projection is O(r), plus decoded-key
sorting. Index space is O(r + certificates). A trial costs its own row
lookups plus certificates which use that origin. A large dependency set can
still require much work. Do not claim a linear worst-case selection pass.
Count certificate changes and projection memory in the experiment.

Examples:

```text
ND X: {p.$/T,q.$/U} -> ret.$/V,D
   Y: p.$/T -> ret.$/V,D
   Z: q.$/U -> ret.*/V,D
Before: project X,Y,Z. After: project Y,Z; preserve both member services.
Remove Z too: reject the plan unless another final provider covers q.

Residual R3:
X: p.*/T -> ret.f.g.$/T,D        // scalar lane
Y: p.*/T -> ret.MAY/T,D          // diagonal lane
Input ret.f.g.$/T,N:
    X emits ret.f.g.$/T,N
    Y emits ret.f.*/T,D plus FLOW companions
Request inclusion holds, but these native families differ.
Activation needs eventual progress, not an assertion of equal C2 answers.
```

## 3. C2 candidate traversal

### 3.1 One stoppable traversal

Add an internal control result to `FrozenDemandTrie`. Ordinary Unit visitors
wrap this API and always return CONTINUE. The same core walker serves C2
and C5; only the C2 descendant branch changes.

```kotlin
enum class Visit { CONTINUE, STOP }
enum class Scan { COMPLETED, STOPPED, UNSUPPORTED }

fun visitCountedUntil(actual, kind, catalog, counts, visit): Scan {
    cancellation.checkpoint()
    node = roots[actual.base] ?: return completedWithZeroCounts()
    try {
        for (accessor in actual.path) {
            if (visitValuesInNativeOrder(node, visit) == STOP) return STOPPED
            node = node.child(accessor) ?: return COMPLETED
        }
        if (kind == INITIAL_C2 && !actual.tail.isAny) { // STAR or EXACT
            return visitSameNodeOnly(node, visit)
        }
        return existingNativeOrderDfs(node, visit)
    } finally {
        counts?.accept(visitedNodes, testedProfiles, visitedTerminals)
    }
}
```

Retain raw path order, including CLASS accessors. Preserve native fastutil
child order, profile guards and terminal ordinals. Check STOP at every
terminal and unwind the entire DFS. STOP is not cancellation; exceptions
and cancellation still propagate through `finally`.

The proof is the emitter's existing branch:

```text
demand.path strictly extends actual.path
    actual STAR/EXACT => no primary => no companions => empty family
    actual MAY/MUST  => retain the current descendant traversal
```

Use the walker in both local `offer` and run-2 `requireFamily`. Keep static
completion/carry, control admission, OUTPUT_C5 and precision cursors intact.
No alternate approximate walker or new matching predicate is needed.

### 3.2 Non-creating emission scan

Expose an optional local capability through scope demand views. It uses
the same emitter and deduplication as materialized local C2.

```kotlin
interface LocalAdmissionView {
    fun supportsScan(actual: Facts, policy: RestrictedInitialPolicy): Boolean
    fun visitInitialEmissions(actual, policy, visit: (InitialEmission) -> Visit): Scan
}

scanLocal(actual, visit):
    offeredPairs = nativePairDedup()
    emittedKeys = orderedSet()
    for actualLeaf in nativeLeafOrder(actual):
        status = visitCountedUntil(actualLeaf, INITIAL_C2): demandEntry ->
            if offeredPairs.add(demandEntry, actualLeaf):
                family = policy.emitAdmissions(demandEntry, actualLeaf, actual.layer)
                keep existing admission statistics for this offered pair
                for emission in family:
                    if emittedKeys.add(emission):
                        if visit(emission) == STOP: return STOP
            return CONTINUE
        if status == STOPPED: return STOPPED
    return COMPLETED
```

Implement only frozen local DATA queries at run-3 or later without shared
static carry/completion. Other views return UNSUPPORTED before scanning.
Run-2 still uses its existing full mechanism. Use the current complete
emission family: primary and both possible FLOW companions, at their exact
layers. The scan must not call `ap.initial`, intern facts, or publish effects.
Materialization calls this same emission core, not a second emitter.

For a path of length h with d strict descendant nodes, pruning removes
those d node/profile visits and rejecting emitter calls. It does not improve
MAY/MUST traversal by itself.

## 4. Loop probe integration

### 4.1 Complete observations and trial output

Retain the existing loop growth gate, ZERO/Reach/run-1 bypasses, scalar H
memberships and ascending proper-prefix budgets. `certifiedFirstBudget`
continues to return null. Do not skip ranges or accept from a partial proof.

```kotlin
data class AdmissionDescriptor(
    val scope: BlockScope,        // includes the physical entry
    val family: LoopAdmissionFamily,
    val pattern: Pattern,        // complete mark/mx/E
    val layer: Layer,
)
sealed interface AdmissionProbe {
    data class Rejected(val extra: AdmissionDescriptor) : AdmissionProbe
    data class Complete(val bundle: LoopAdmissionBundle) : AdmissionProbe
    data object Unsupported : AdmissionProbe
}
```

Use the actual adjacent/repeat scope order and liveness from
`MethodBlockRuntime.observe`. Expose those frozen consumers to the probe;
do not infer routes from AP shape. Preflight all views for local-scan support
before doing any work. A generic/unlabelled view uses the existing observer.

The baseline is always complete. Decode its initials with `toPattern`.
An admission descriptor has no protection flag; packet H and the complete
original remain in the query context and enclosing results.

```text
restrict(raw, original, views):
    apply existing bypasses
    baseline = observer.observe(original, raw)
    if baseline.isEmpty: return DROP
    expected = baseline.completeLabelledAdmissionDescriptors

    for budget in existingProperPrefixOrder(raw):
        candidate = existingLimit(raw, budget)
        trial = probeAllConsumers(candidate, expected, views)
        if trial is Rejected: continue
        bundle = trial.bundle if Complete else null
        full = observer.observe(original, candidate, completedBundle = bundle)
        if full == baseline: return candidate
    return raw

probeAllConsumers(candidate, expected, views):
    if any view unsupported: return Unsupported
    completed = ordered per-consumer answers
    for V in actualAdjacentAndRepeatOrder:
        if nativeBoundaryLivenessRejects(V,candidate): save empty V; continue
        scan existing complete cached answer, or stream local C2 descriptors:
            d = (V.scope,V.family,emission.pattern,emission.layer)
            if d not in expected: STOP all trial scans; return Rejected(d)
            save emission in V's ordered answer
    return Complete(bundleFromCompleteAnswers(completed))
```

An extra membership cannot disappear from an exact set union. It rejects
this budget. Absence of an extra is insufficient: candidate `{a}` still
differs from baseline `{a,b}`. Run the full enclosing observer after every
completed non-rejected probe. Keep its saved-record/Target composition,
paired C5, normalization, liveness, original, exit, layer and H unchanged.
The observer remains pure; it cannot run rules or send requests/effects.

### 4.2 Reuse and lifetime

Add `LoopQueryScratch.peekInitials`: it returns only an already complete
answer, with the current view/policy identity and full packet/H key. A miss
must not materialize C2. On a miss, use the descriptor stream. On a hit,
decode the complete cached answer for the same check.

Extend `LoopAdmissionBundle` with a factory for complete per-consumer
descriptors. Materialize each legal `(Pattern,layer)` at most once when a
full observer needs its native `AdmittedInitial`. Reuse the same answer for
adjacent, repeat and labelled projections. Pass the bundle as an optional
override to `LoopConsumerObservation.observe`; preserve its current path
when no override is supplied.

Never cache aborted answers. An oversized completed answer can remain in
this one bundle without entering the existing 128-answer/32-query cache.
Keep the existing owner-quantum release. Failed-trial descriptors become
unreachable before the next trial. There is no cross-run probe archive.

The legal round trip `ap.initial(p).toPattern() == p` permits comparison
before interning. It does not permit omission of companions or comparison
by only the primary tail. A late extra companion, changed layer or another
physical scope must reject the trial.

Let A be complete trial admissions and S the saved enclosing-observer work.
A rejected probe visits only its prefix through the first extra member and
skips the rest of A and S. A surviving probe still needs S, but performs C2
once. This change does not reduce real saved replay outside the observer.

## 5. Disabled unresolved-call diagnostics

The JVM interpreter implements the observer even when its nullable tracker
is absent. Remove work from that disabled path, not from AP transfer.

The spec's default-enabled capability must preserve Java and Kotlin SAM
use. This build uses Kotlin 2.1 and has no dataflow `-Xjvm-default=all`
setting. Do not add a property directly to the fun interface and assume a
Java default getter. Use a separate capability and an extension instead:

```kotlin
fun interface UnresolvedCallObserver {
    fun reached(call: CommonCallExpr, position: AccessPathBase, plan: CallPlan)
}
interface UnresolvedCallObserverState { val enabled: Boolean }
val UnresolvedCallObserver.enabled: Boolean
    get() = (this as? UnresolvedCallObserverState)?.enabled ?: true

// JIRInterpreter implements both interfaces; externalMethodTracker is immutable.
override val enabled: Boolean get() = externalMethodTracker != null

// SharedObjects retains the same observer object; generic observers default to true.
val unresolvedObserver: UnresolvedCallObserver?
    get() = (interpreter as? UnresolvedCallObserver)?.takeIf { it.enabled }
```

This implements the specified capability without a compiler-setting change
or wrapper callback. Configuration stays fixed for the run.

```text
observed = null

observeUnresolved(ctx, facts):
    observer = shared.unresolvedObserver ?: return
    if no existing ADDED unresolved stage: return
    for fact in facts:
        if fact is not TAINT: continue
        archive = observed ?: oldAddedFactAccumulator().also { observed = it }
        ref = existingCallerRef(ctx,fact)     // preserve its present coordinates
        if archive.add(ref, fact.layer, fact) is fresh:
            observer.reached(ctx.call, fact.base, ctx.plan)

freeze(): observed = null; keep existing release logic
```

Keep the existing run-1/ADDED caller guard, ignored-method checks, delta
deduplication and callback counts when enabled. Do not delete the generic
`AddedFactAccumulator`; other owners still need it. Disabled tracking has
no archive, mark-tree updates or callbacks. The unresolved call still runs
its normal AP transfer.

## 6. Exact FULL caller-input storage

### 6.1 Backend and literal keys

Replace only `CalleeSubscriptions.values` with an internal directory which
can store either packed FULL TAINT or the existing scalar representation.
Keep one stable logical handle and insertion ordinal per old native key.
Do not change `Subscription`, `CallerRef`, `Facts` or their equality.

```kotlin
interface CallerInputValues {
    fun add(ref, linkLayer, offered): Update?
    fun snapshot(handle): Snapshot
    val size: Int                         // logical old native groups
    fun clear()
}
data class LogicalSlot(val oldKey: NativeInputKey, val ordinal: Int, var location: Location)
sealed interface Location {
    data class Packed(val family: FamilyId, val source: FullMarkId) : Location
    data class Scalar(val value: ScalarEntry) : Location
}

data class FamilyKey(
    val exactOwnerAndCaller: OwnerCallerCallStageScope,
    val originalGeometry: OriginalGeometry, // manager/base/path/tail/E, without mark
    val offeredGroup: GroupKey,             // kind/layer/base/E/mx/tail/H
)
class Family {
    val geometry: Trie<Path, ExactAndAny<MarkRelation>>
    val handlesBySource: Map<FullMarkId, Handle>
    val cellsBySource: Map<FullMarkId, OrderedCellIds>
}
class MarkRelation {
    var diagonal: MarkSet
    val changingByTarget: Map<FullMarkId, MarkSet> // target -> exact source IDs
}
```

The enclosing SubscriptionManager directory already fixes the exact callee.
Keep that coordinate in the effective family key. Include the full caller
context, call/stage, caller layer and scope/ports. Do not merge distinct
header/H classes. Geometry is a private descriptor, not a synthetic FLOW
initial. Use full runtime mark identities, including primitive metadata.

Pass the immutable `port.config.mode.markMode` into each new directory.
Pack legal singleton nonzero FULL originals with legal FULL TAINT outputs.
Keep ND, ZERO/Reach, FLOW, GROUP and unsupported shapes scalar. Preserve the
native uniform-protection/domain checks; storage does not make an invalid
mixed-H packet legal. LocalInputDirectory and loop input storage stay as is.

```text
contains(s,t) = (s==t and diagonal.contains(s))
            or (s!=t and changingByTarget[t].contains(s))
add(s,t):
    if s==t: diagonal = diagonal + s
    else: changingByTarget[t] = changingByTarget[t] + s

P/T1 -> Q/T1, P/T3 -> Q/T3, P/T1 -> Q/T2, P/T3 -> Q/T4
stored at P -> Q:
    diagonal = {T1,T3}; changingByTarget = {T2:{T1}, T4:{T3}}
T1->T4 and T3->T2 remain absent.
```

Use native immutable sorted `MarkSet`; off-diagonal buckets contain no self
pair. Mark-set size is not a bitmap byte estimate.

### 6.2 Snapshot and delta protocol

The old accumulator's key uses the ORIGINAL offered group, not its fresh
delta. Exact-only deltas can clear E or change their retained any-tail
header. Preserve that key and replay the native fresh header unchanged.

```text
readNativeGroup(family,s):
    tree = empty native TAINT root
    for cell in family.cellsBySource[s] in native coordinate order:
        targets = exactTargets(cell.relation,s)
        restore targets at this cell's path and EXACT/any slot
    return Snapshot(completeOriginalRef(s), originalGroup, nativeHeaderH(tree))

admit(sub):
    perform existing domain/layer validation
    k = NativeInputKey(sub.ref, sub.added.groupKey)
    slot = handles[k]
    if slot is scalar or offered shape is ineligible:
        return scalarAdmitOrMigrate(slot,sub)
    old = readNativeGroup(slot.family,slot.source) if slot exists else absent
    merged,fresh = existingNativeAddOrMergeAddDelta(old,sub.added)
    if fresh is absent: return NO_CHANGE
    allocate logical handle/family if this is the first native group
    factor fresh into literal (path,slot,target) cells
    add (source,target) to each exact relation under ORIGINAL family key
    update source-cell and geometry candidate postings
    return oldProtocolUpdate(handle, fresh, newGroup)
```

Keep `Admission.fresh` as the immutable native delta captured at enqueue
time. Its `current` getter reads the cumulative logical snapshot. If a
second offer arrives before replay, do not replace the first queued delta
with the enlarged union. `growth` and `newGroup` keep their old meaning.

The invariant after every offer is:

```math
decode(packed, nativeKey) = scalarCurrent(nativeKey)
freshPacked(offer) = freshScalar(offer)
```

Use native `mergeAddDelta` as the first implementation. It reconstructs one
transient old group, computes the existing delta and writes literal fresh
cells. It need not retain `merged` as a second full packet. A direct cell
delta fast path is later work unless it has the same native delta proof.

Do not broadcast target sets between positions:

```text
P/T1 -> {Q.f.$/T2, Q.g.$/T4}
    f exact stores (T1,T2); g exact stores (T1,T4)
    no f/T4, g/T2, or product of source and target sets
```

If an existing packed native key later needs scalar fallback, migrate once:

```text
migrateToScalar(handle,offered):
    old = snapshot(handle)
    merged,fresh = nativeMerge(old,offered)
    remove only this source's packed cell memberships/source-cell postings
    keep all other sources and their ordinals
    replace this handle's location with Scalar(merged)
    keep the SAME handle, key and ordinal; route later offers to this slot
    return the same fresh delta, or no change
```

There is one authority for each native key. Do not retain packed and scalar
copies together. Geometry and request indexes must still resolve the same
logical handle. Preserve its existing path/handle posting ordinals and path
nodes during migration; replace their backend reference without a remove/
reinsert cycle. Add only genuinely new positions from the native delta.
A new legal native key is a new slot, not a migration.

### 6.3 Candidates, replay and ownership

Share geometry postings by family/cell. Retain a thin first-posting ordinal
for each `(path,logical handle)` membership. This ordinal records the first
successful native position insertion, which can occur after handle creation.
At each visited path node, merge cell expansions in that posting order.
Do not group delivery by family or sort all candidates by handle: either
can change the old order when families or late positions interleave.
Keep the existing path-node creation and child traversal order.
Deduplicate by handle, not family. Preserve the
existing prefix/extension policy for run-1, later runs and reversed records.
Initially use the existing full matcher for every selected handle. Exact
target buckets may narrow mark candidates only where the selector is known;
other selectors must remain conservative.

```text
visitPublicationOrRequest(query):
    candidates = existingGeometricCandidateOrder(query,sharedPostings)
    ids = expandToLogicalHandlesAndDeduplicate(candidates)
    snapshots = [snapshot(id) for id in ids] // BEFORE callbacks can grow inputs
    for immutable sub in snapshots:
        existingScalarMatcherAndConsumer(sub,query)
```

Keep one `seen` handle set for the entire request batch, as today. A selected
mark or cell does not replace the complete snapshot used by an ND join,
request hook or source. Keep the `visitingQuestion` guard and its `finally`
reset. Request visitors still queue every effect until the finite visit
ends; snapshot construction does not permit reentrant directory mutation.
`JoinedCallerInputs` borrows this same frozen
directory after worker join; it does not build another retained mirror.

Decode before summary application, rules, cleaners, aliases, primitive
filters, requests and joined static-writer binding. Keep existing neutral
bulk execution guards. In `P/T -> Q/U` then `U -> T`, the scalar composer
must see original T and make its existing protection decision.

The caller runner owns the mutable table. Notifications stay queued.
Freeze/move it at the existing joined boundary. Clear packed relations,
fallback, handles and postings together at the existing release point.
No queued callback may retain a mutable relation or cell-ID view.

### 6.4 Cost and distinction from subsumption

At common geometry, retain d diagonal IDs, t changing target keys and c
source memberships, plus thin handles and postings. Source-to-cell postings
avoid scanning unrelated geometry. A target-first relation can still scan
several target buckets to decode one source. An exact derived reverse index
is allowed; it must not become another authority. Measure that cost before
adding it. Native AP nodes may already share memory, so logical packing
does not predict heap savings.

| Lookup | Cost and bound |
| --- | --- |
| Native key to logical handle; family lookup | Expected hash lookup plus full checked-key comparison. |
| Source to geometry | O(k) cell postings for that source; no unrelated path scan. |
| Targets in one cell for a source | Diagonal membership plus membership tests in that cell's changing target buckets. This can still grow with target count. |
| Publication/request geometry | Existing prefix/subtree node traversal plus visited postings. Merge per-cell handle lists by first-posting ordinal at each node; do not scan all families. |
| Complete snapshot | Selected source cells/target memberships plus native tree construction. There is no independent callback per mark pair. |
| Scalar fallback | Existing native accumulation/matching cost; migration reads and removes that one logical source. |

FLOW subsumption removes redundant summary results. This table records
which marks actually arrived. For `CM(arg,T2) -> assign U to ret`, a later
T2-to-U summary still needs the T2 input even when a NORMAL FLOW identity
covers T1-to-T1 and T2-to-T2 results. Packing keeps these exact witnesses;
it does not infer that FLOW supplies T2.

## 7. Files and ownership

Paths below are relative to
`core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/`
unless a different root is stated.

| File | Change and reason |
| --- | --- |
| `driver/HandoffCompactor.kt` — new | Frozen origin collection, service indices, rule certificates and final retained selection. |
| `driver/HandoffServiceKeys.kt` — new | Private complete keys and existing C2/C5 service adapters. Keep native rows literal. |
| `driver/HandOff.kt` | Insert selection before local demand construction; preserve seeds, controls, completion bypass and counts. |
| `driver/BlockHandOff.kt` | Share complete projection with the collector and final builder; retain all members/ports and old run-1 callbacks. |
| `store/FrozenDemandTrie.kt` | Single stoppable traversal and C2 STAR/EXACT descendant pruning. |
| `store/DemandResultCoverage.kt` | Share ordered complete emission enumeration with materialization; do not intern rejected probes. |
| `store/DemandStore.kt` | Expose optional supported local emission scan on scope views; retain run-2 completion and C5. |
| `engine/LoopRestrictionSession.kt` | Add negative-probe hook; keep the dormant first-budget shortcut disabled. |
| `engine/LoopOutputRestriction.kt` | Reject a trial from its witness, then reuse complete bundle for full equality. |
| `engine/LoopConsumerObservation.kt` | Accept an optional complete bundle; keep enclosing semantics and purity. |
| `engine/LoopQueryScratch.kt` | Non-creating cache peek and complete-bundle construction; no partial cache entries. |
| `engine/MethodBlockRuntime.kt` | Supply actual routed/liveness-checked adjacent/repeat consumers to probes. |
| `interp/UnresolvedCallObserver.kt` | Separate stable capability plus default-enabled extension, preserving SAM. |
| `engine/SharedObjects.kt` | Return only an enabled observer, retaining the same object. |
| `engine/RunMethodCallServices.kt` | Create diagnostic archive on first enabled eligible TAINT input only. |
| `core/opentaint-dataflow-core/opentaint-jvm-dataflow/src/main/kotlin/org/opentaint/dataflow/jvm/bidi/interp/JIRInterpreter.kt` | Implement capability from immutable tracker availability. |
| `store/CallerInputValues.kt` — new | Stable logical slots, scalar fallback, native delta protocol and migration. |
| `store/CallerMarkRelations.kt` — new | Private geometry families, exact diagonal/changing relations and derived postings. |
| `engine/CalleeSubscriptions.kt` | Use the new value backend and shared geometry candidate postings; preserve replay order and current/fresh API. |
| `engine/SubscriptionManager.kt` | Pass the immutable current mark mode into the directory; retain subscription/replay algorithms. |
| Test sources | Add the differential controls in §9 and retain the old scalar/reference algorithms in test scope. |

Reuse the algorithms in `SubscriptionManager`, `JoinedCallerInputs`, `AddedFactAccumulator`,
`FlowBackedSummaries`, record stores, AP transfer, mark interning and rule
providers. Update their callers/types only if the new private backend needs
it; do not change their semantic algorithms. Remove the unconditional
diagnostic allocation and redundant per-source geometry/full-packet storage
from the selected owners, not the general classes or fallback.

## 8. Proofs and implementation binding

The [proof package](../../spec/lean/proposals/in-handoff-compaction-20261112/README.md)
contains these constructive local models:

| Model | Checked claims | Implementation obligation |
| --- | ---: | --- |
| `HandoffCompaction.lean` | 17 | Bind complete native origins/service keys to retained final witnesses. R3 progress is not proved here. |
| `WorkReduction.lean` | 23 | Bind strict-descendant emptiness, descriptor round trip, exact labelled sets and diagnostic independence. |
| `CallerMarkRelations.lean` | 26 | Restore complete native packets/deltas and all keys before scalar consumers. |
| `ImplementationAlgorithms.lean` — new | 13 | Bind exact reverse dependencies and one-source fallback migration to the native directories. |

The new model proves that a certificate which does not use removed X stays
valid, and that repairing affected certificates plus X preserves the final
provider invariant. It also proves exact source partition, preservation of
other packed sources, complete migrated value, stable handle and removal
of the migrated packed source. Native join itself stays the old operation.
The model does not prove Kotlin index maintenance from source code.

All successful audits use only `propext`/`Quot.sound`, or no axioms.
Failed-attempt diagnostics remain separate from successful receipts. The
existing native controls have 182 C2/interner assertions, 8,325 native
MarkSet assertions and eight current-store inventory checks. They do not
replace tests of the future runtime integration.

Before each implementation phase, add its failing native tests and bind:

```text
complete native scope/key -> injective model key
native legal emission     -> descriptor with exact decoding round trip
whole stored packet      -> literal coordinate/source/target memberships
native mergeAddDelta     -> same union and exact fresh delta
index candidate set      -> every old candidate, in existing delivery order
ownership/release        -> no live mutable state in frozen results
```

For R3, construct an uncapped native refinement simulation in both
directions. It must preserve eventual findings, source/ND permissions,
NORMAL replay, cleaners, H, ports/statics and empty-demand stopping.
The different first-field families in §2.4 are a principal proof case.
Broader MAY R4 arms use the same gate. No iteration cap or bounded passing
fixture is a substitute. Leave these new removals inactive if it is open.

## 9. Tests and implementation order

Land independently reviewable phases. Each phase first adds differential
tests, then the implementation, then focused checks. Use existing reference
semantics; do not update expected findings merely to make a test pass.

| Phase | Work | Required controls |
| --- | --- | --- |
| 1 | C2 traversal | All tails, marks, E/mx, layers and directions; same node, ancestor, absent branch, CLASS path; ordered primary/companions; run-2 requireFamily/completion unchanged; C5 and precision cursors unchanged; STOP/final counts/cancellation. |
| 2 | Disabled diagnostics | Disabled tracker creates no archive/update/callback; enabled/generic observer parity; ignored/static calls; Java lambda and Kotlin SAM compilation; same findings and enabled counts. |
| 3 | Loop probe | Late-extra companion; same geometry with another scope/family/layer; missing-only and enclosing-only differences; empty baseline; all bypasses; unsupported/run-2 fallback; completed cache hit/miss; one C2 pass per completed view; no partial cache retention. |
| 4 | Caller storage | Scalar differential after EVERY offer: mixed diagonal/changing, one-to-many/many-to-one, positions/slots, E/mx, H, primitive IDs/statics and all fallbacks; original-group/exact-only deltas; packed-to-scalar migration and stable handle. |
| 5 | Caller consumers | Later summary publication/request, full ND packets, T-to-U-to-T protection, fresh/current timing, interleaved families and late-position posting order, callback growth, joined borrow and release. |
| 6 | Exact handoff compaction | R1/R2/all ND members and leaves; final/transitive witnesses, mutual cover, arrival permutations, typed controls, static/exception anchors, H, E and port separation; run-1/GROUP bypass; unchanged persistence/seeds/reports; builder insertion counts and empty-stop behavior. |
| 7 | Residual MAY activation | First discharge §8 progress proof, then test exact eventual findings with natural continuation and no cap. Keep the phase separate from exact-service compaction. |

Use exhaustive small mark-relation sets and packet/header permutations for
the storage tests. Compare whole native snapshots and the exact fresh
sequence for each fixed offer order. Different arrival permutations must
have equal final memberships; they need not have the same callback sequence.
For handoff, check stable retained basis across permutations and actual
complete C2/C5 service images, not row counts alone.

Run the common and JVM test modules through the source composite build:

```sh
./core/gradlew -p core :opentaint-dataflow-core:opentaint-dataflow:test
./core/gradlew -p core :opentaint-dataflow-core:opentaint-jvm-dataflow:test
```

During each phase, select the new tests plus relevant existing controls:
`FrozenDemandTrieTest`, `DemandStorageDifferentialTest`,
`RestrictedDemandProtocolTest`, `LoopRestrictionSessionTest`,
`LoopConsumerObservationTest`, `LoopQueryScratchTest`,
`CumulativeSubscriptionEquivalenceTest`, `AddedFactStoreTest`,
`HandOffTest`, `BlockHandOffTest` and `OutgoingDemandStopTest`.
Then run the broader gates once the independent phases pass.
Run the [source-only Gradle rules pipeline](../rule-testing.md), including
its bidirectional arguments and result gate. Keep known failures and
collection limits visible. Do not present disabled/uncollected samples as
passed cases. Verify the actual engine from its run markers.

Recheck all four Lean sources named in §8 and record source/output hashes.
No production test or project experiment is claimed by this proposal.

## 10. Post-implementation experiments

Use the existing FULL configuration, rule/model set, aliases/statics, heap,
timeout and field schedule `1,1,2,...`. Run heavy jobs sequentially. Pin the
source and configuration for each phase. Do not change limits to make a
comparison pass. The existing run-11 cutoff stays a runtime setting only.

Existing report controls, not new measurements:

| Project | Latest reached | Latest completed | Accepted forward | Findings |
| --- | --- | --- | --- | --- |
| OWASP | run-11 | run-11 | run-11 | 2,633 confirmed |
| Conductor | run-8 | run-7 | run-7 | 7 confirmed |
| Stirling-PDF | run-11 | run-10 | run-9 | 32 confirmed |
| Thingsboard | run-1 | none: OOM | none | no accepted forward result |

Recheck the exact finding identities/status from the
[cutoff validation report](../reports/bidirectional-run11-cutoff-validation-20261109.md).
Compare at common completed frontiers. A later reached frontier is not an
equal-frontier regression. Report reached/completed/accepted-forward labels
and EMPTY_DEMAND/RUN_LIMIT/TO/OOM separately in every result table.

Measure each phase against its parent, then the combined version:

| Area | Required measurements |
| --- | --- |
| Handoff | Origins/projected rows/accepted builder rows before and after, per rule/method/block; actual final witnesses; rebind counts; peak index memory/time; persisted NORMAL counts unchanged. |
| C2 | Nodes/profiles/terminals visited, rejected emitter calls avoided, complete initial family equality and allocations. Separate STAR/EXACT from MAY/MUST. |
| Loops | Budgets tested, first-extra position and kind, full observations/saved applications avoided, complete C2 families reused, interning avoided, unsupported fallbacks and chosen cut parity. |
| Diagnostics | Tracker state, archives allocated, retained groups/deltas/callbacks; disabled counts must be zero; enabled semantic/count parity. |
| Caller storage | Logical native groups, geometry cells, diagonal IDs, changing pairs/targets, handles/postings, scalar fallbacks/migrations, decoded snapshots, native-merge allocations, decode CPU, retained heap and release. |

For the largest remaining workload, capture exact facts and their pipeline:

```text
owner/block/ports and run-N
complete original -> offered packet (path/tail/mark/layer/E/mx/H)
admission -> retained logical group/cell counts
publication/request selector -> candidate handles -> native match results
fresh replay/current snapshot -> loop probes -> C5 -> summaries/handoff
operation count, allocation share and retained owner at each step
```

Use that trace to distinguish retained memory from transient reconstruction,
and candidate enumeration from actual propagation. Verify whether caller
geometry sharing saves heap or moves cost into decoding. Verify whether
loop probes avoid enclosing work or whether real saved replay still
dominates. Do not infer a speed factor from logical compression ratios.

Store bulky raw evidence outside the repository. Link a small receipt and
embed representative facts and aggregate counts in the report. A data
directory whose total size exceeds 10 MB is also bulky. The final report
must identify the next source of work from the new measurements, with the
latest reached iteration, even when a run ends in TO/OOM.

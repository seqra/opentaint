# Restricted demand: next optimization proposal

Date: 28 October 2026. Status: proposal only. No runtime change is selected here.
Measured runtime: `53991b7483b062b0287152130cbbbfc87623093b`.

Use the [performance report](../reports/bidirectional-restricted-demand-performance-20261028.md)
as the evidence for this proposal. The latest reached, completed and accepted
forward runs are:

| Project | Reached | Completed | Accepted forward |
|---|---|---|---|
| OWASP | run-12 | run-11 | run-11 |
| conductor | run-4 | run-3 | run-3 |
| thingsboard | run-2 | run-1 | run-1 |
| Stirling-PDF | run-5 | run-4 | run-3 |

## Scope and order

The first two proposals avoid operations. They do not change the selected AP
semantics. They keep actual-input admission, paired summary restriction, marks,
field limits, exclusions, rule evaluation and the static pool unchanged.
They do not add StrongQueries. IR storage is out of scope.

| Rank | Proposal | Current behavior | Proposed behavior | Expected effect |
|---|---|---|---|---|
| 1 | Do not replay completed raw writer bindings | At the run-1 boundary, bind observed writers again, including writers already handled by the live engine | Keep every guide seed. Bind only raw keys whose caller work is not certified complete | Remove repeated caller matching and summary application from Thingsboard's 251.337 s completion phase |
| 2 | Use an entry-only view for initial admission | C2 queries construct complete paired closure rows, then use only their entry | Compute target entry patterns directly. Keep paired closure for C5 | Remove source-by-target closure work from repeated run-2 initial selection |
| 3, investigate | Avoid repeated generated registry save/restore work | Every generated Spring dispatcher saves and restores the whole registry around cleanup | First attribute the large static point population to fields; then design an equivalent bulk transfer if this block dominates | Potentially remove repeated static instructions and local copies; the eligible workload is not yet measured |
| 4, reserve | Share current program-point fact carriers | Later runs store many small general-purpose containers | After a separate occupancy census, share or pack eligible immutable carriers | Reduce retained heap, but this does not remove logical propagation |

Ranks 1 and 2 are the proposed next design work. Their local models pass, but
their production adapters still need proofs and tests. Their measured saving is
unknown. Rank 3 needs a causal measurement before design. Rank 4 is a technical
reserve; its eligible population is not measured.
No claim of a two-times speedup is made. The current profiles identify large
cost regions, not the fraction that each new algorithm will remove.

## 1. Do not replay completed raw writer bindings

### Evidence

Thingsboard completes run-1 in 378.990 s of engine time. It then spends
251.337 s in joined completion. Writer binding takes 244.196 s. The binder
visits 222,531,429 input candidates, matches 28,035,102 and emits 27,933,247
bound outputs. Only 12.60% of candidate inputs match.

The phase admits 2,351,008 writer keys from 26,395,364 offers. It starts from
all observed primitive writers and surviving writer summaries. Much of this
work can repeat live summary application. Zero duplicate-input counter entries
do not disprove repetition: that counter covers one writer's input identities,
not whether the live engine already performed the binding.

The current candidate inventory has 2,706,439 observed keys and 467,941 lost
guides. **Do not seed the new queue from `lostRows()` alone.** That test compares
normalized guidance; it does not certify completion of raw AP applications.

### Example and fact annotations

```java
void set(Object p) { C.f = p; }
void wrap(Object q) { set(q); }
void main(Object a) { wrap(a); }
```

```text
set:   p/* -> C.f/*       primitive writer, DEMAND
wrap:  q/* -> C.f/*       actual caller-bound writer, DEMAND
main:  a/* -> C.f/*       actual caller-bound writer, DEMAND
```

Before: the live engine binds `set` to `wrap`, then `wrap` to `main`.
Joined completion starts at `set` again and can perform both bindings again.
After: retain all three known keys as seeds. If their live publication is
certified complete, do not expand them again. A writer removed by an exit rule
has no such certificate. Bind that writer at the boundary and continue until
its image reaches a key whose caller work is already complete.

### Storage and pipeline

Use an owned key `(complete MethodKey, raw ID)` from `StaticWriteKeyInterner`.
The interner can share a raw ID between method owners; that ID alone is not
a replay or exhaustion identity. The raw row keeps the premise, conclusion,
field geometry, tail, E and mark exclusions `mx`.
It also keeps its input/output mark pair. `mx` is the set of excluded marks
on a FLOW value. Do not remove it before actual AP application.

```kotlin
// Proposal pseudocode. These are not new executable summaries.
class WriterReplayState {
    val known: RawWriterIdsByMethod
    val exhausted: RawWriterIdsByMethod
    val expanded: RawWriterIdsByMethod
    val pending: ArrayDeque<OwnedRawWriterId>
}

// At the successful joined barrier, before N2 inputs are released:
captureExistingBaseGuidanceSeeds() // existing lost W/B, private B and selected W/R policy
for (key in allObservedAndSurvivingRawWriters) {
    known.add(key)
}
for (key in known) {
    if (!exhausted.contains(key)) pending.addLast(key)
}

while (pending.isNotEmpty()) {
    checkpoint()
    val key = pending.removeFirst()
    if (exhausted.contains(key) || !expanded.add(key)) continue
    forEachExistingActualInput(key.owner, key) { actual ->
        applyExistingAPBinding(key, actual) { image ->
            captureExistingGuidance(image)
            if (image.original.base == STATIC) return@applyExistingAPBinding
            if (known.add(image)) pending.addLast(image)
        }
    }
}
```

The initial writer collection excludes static-original keys. The explicit
stop above sends a bound static-original image to B without replaying it.
This pseudocode omits the existing real-ZERO check, projection, cover and
field-cut calls. Reuse all of them as they stand in
`JoinedStaticWriterBinding`. Do not replace them with path equality.
Static-original relations enter the bridge closure; they do not enter this queue.

An `exhausted` certificate has this exact meaning at the frozen barrier:

```text
key is in known
AND
for every current actual N2 binding image of key:
    the complete raw image is already in known
```

A live-publication flag alone is insufficient. Before implementation, prove
that the selected ordinary publication path covers all current subscriptions,
that all resulting static images are captured before exit handling, and that
the worker join drains those callbacks. Retired FLOW-backed rows require the
same proof. Certify only the paths for which these facts hold. Other keys use
the current full replay. Do not retain every `(writer,input)` pair merely to
make a certificate; that would create another large store.

Raw reachability equivalence alone does not prove equal guidance. The adapter
must also prove that the unchanged base guidance inventory already contains
the existing guidance projection of each initial `known` key. Derive this
from final capture/prune and selected-summary invariants. Do not replace that
inventory with a new seed policy or use normalized guide membership as the
raw exhaustion test. Every newly bound image still uses the existing guidance
capture, including a static-original image that stops at B.

Keep the state inside run-1 completion. Release it after immutable guidance is
built. Keep the existing deadline and memory checks. A failed phase must not
export a partial accepted handoff.

### Why raw equality is required

```text
FLOW A: p/* -> C.f/* excluding T
FLOW B: p/* -> C.f/* excluding nothing
```

These rows can have equal normalized guidance. They have different results
when bound to an actual T input. A certificate for A is not a certificate for B.
Using normalized guide equality can stop before a required marked image is
created. The proposal model includes this counterexample.

### Proof and verification

The [WriterReplay model](../../spec/lean/proposals/restricted-demand-next/WriterReplay.lean)
has 19 audited declarations with no axioms. Under the explicit exhaustion
certificate, it constructs conversions between full replay and sparse replay.
Thus, both produce the same reachable raw writer keys. Sparse replay expands
only uncertified keys. The admission operation is idempotent for each raw key;
an exhausted known key is neither initial seed work nor requeued work. The
model does not prove the complete production worklist scheduler or its
fairness. The implementation must initialize from a set of raw owned keys
and drain every admitted pending key within the existing resource boundary.

The model represents a finite frozen AP-binding graph. It does not prove that
the production adapter supplies the complete graph or valid certificates.
Required implementation checks are:

- A surviving published writer, an exit-killed writer, and both in one wrapper chain.
- A key that loses its FLOW-backed live row before the barrier.
- Different raw E, `mx`, tails, input/output marks and complete method contexts.
- Real ZERO input controls; no static-original key in writer binding.
- Exact seed and demand equality against full replay on finite test graphs.
- Cancellation and deadline failure without partial publication.

Measure raw known/exhausted/expanded keys, candidate inputs and bound outputs.
Do not derive a saving from the 17.29% normalized-lost ratio. The raw exhausted
population is not yet counted.

## 2. Use an entry-only view for initial admission

### Evidence and distinction

In Thingsboard run-2, `DemandStore.near` accounts for 64.34% of Java execution
samples and 69.54% of sampled allocation weight. Total frozen lookup accounts
for 78.82% and 85.44%, respectively. In conductor run-2, virtual lookup takes
74.55% of Java samples; reachability alone takes 65.56%.

The current `near` call walks paired static closure rows and constructs
`DemandPattern(entry, exit)` objects. Initial emission uses the entry only.
Summary restriction has a different need: C5 must keep the pair. Do not weaken
C5 to independent sets of entries and exits.

Use `D_c` for the entry into the current backward method, and `D_p` for its
paired demanded output. A forward guidance relation `p -> ret` supplies the
backward demand pair `(D_c=ret, D_p=p)`.

### Example and fact annotations

```java
Object read() { return C.c; }
void write1(Object p) { C.a = p; }
void copy1() { C.b = C.a; }
void copy2() { C.c = C.b; }
```

Suppose the existing owner and call-graph visibility rules admit these seeds
at method M. Its full closure can contain:

```text
p/*   -> C.a/* -> C.b/* -> C.c/* -> ret/*
q/*   -> C.a/* -> C.b/* -> C.c/* -> ret/*
...
```

Before: each C2 lookup for actual `ret/T` can revisit many left endpoints and
construct `(ret/*, p/*)`, `(ret/*, q/*)`, and other paired guides. Each has the
same C2 entry. After: use the single applicable `ret/*` entry for C2. C5 still
uses the complete paired closure when it restricts a result with a particular
original and conclusion.

### Entry fixed point

Build a separate immutable/lazy view of entries from the same frozen seeds.
Key each result by the complete querying method, target geometry and output
mark selector. Keep existing owner visibility. Do not build a dense
method-by-edge Cartesian product.

```kotlin
sealed interface EntryMark {
    data object Abstract : EntryMark
    data class Colored(val selector: MarkAtomKey) : EntryMark
}

// Only seeds visible to this complete method key may contribute.
for (seed in visibleFrozenSeeds(method)) {
    when (val label = seed.marks) {
        FLOW -> entries.offer(seed.to.geometry, Abstract)
        is Mapped -> entries.offer(seed.to.geometry, Colored(label.output))
    }
}

while (entries.hasDelta()) {
    val entry = entries.popDelta()
    if (!entry.target.isStatic || entry.mark !is Colored) continue
    for (flow in visibleFlowSeedsStartingAt(entry.target)) {
        if (existingGeometryCompositionAllows(entry.target, flow.from)) {
            entries.offer(flow.to.geometry, entry.mark)
        }
    }
}

// C2 needs all current demand entries, including ordinary stored pairs.
fun entryNear(method, actual): Set<Pattern> = union(
    storedPairedDemand.entryProjectionNear(method, actual), // keep entries even when Dp is absent
    staticCompletion.entryNear(method, actual),
    existingImplicitZeroEntry(actual),
    existingSameActualStaticCarryEntry(actual)
)

// Keep the current order: cut the actual packet, find candidate entries,
// then run the unchanged AP emitter against that bounded packet.
for (bounded in existingFieldLimit(actual)) {
    val candidates = union(existingLeaves(bounded).map { entryNear(method, it) })
    for (entry in candidates) emitExistingInitial(entry, bounded)
}

// C5: unchanged paired authority.
for (pair in demand.covering(method, initial)) restrictExistingSummary(pair, result)
```

The fixed point describes the nonzero symbolic static kernel. It does not
replace the ordinary paired-demand entry projection or the AP emitter.
The implicit ZERO entry remains conditional on the actual zero base. Static
carry remains conditional on `hasSharedStaticCarry` and the same actual
position/mark; it is not a precomputed broad root/class entry.

A genuine `ZERO -> C.f/U` seed must still add the colored `C.f/U` entry. Its
left NoInput selector is discarded only for this target projection; it is
not a reason to drop the seed or to allocate a runtime mark. A real ZERO
target uses the existing ZERO adapter. Keep all paired ZERO relations for
C5. These ZERO/carry adapters are outside the local nonzero model. Preserve
abstract-demand E normalization, actual E, location intersection and the
actual-mark gate.

A mapped seed fixes its output selector. Thus, its target entry already
exists even when an earlier mapped path can compose with it. A FLOW suffix
does not fix that selector: it must transport colors from preceding mapped
seeds. This is why indexing primitive targets alone is wrong.

```text
W: p/T -> C.f/U
R: C.f/* -> ret/*

Required C2 entries: C.f/U, ret/*, ret/U
```

Omitting `ret/U` can miss the marked backward initial. A standalone FLOW
reader does not enumerate every full mark. It emits an abstract entry; the
unchanged emitter therefore starts the shared FLOW form on an admitted
overlap, even when the actual input has a concrete mark. Only a colored entry
intersects an actual marked input to produce a concrete initial. GROUP
selectors accept real FULL members in that group and preserve the actual
FULL member. A FULL selector does not manufacture a full member from a GROUP
input, and a colored entry cannot obtain a concrete mark from FLOW.

### Shared visibility

The present lookup creates a fresh reachability scratch object for each query.
Within the immutable completion lifetime, reuse the method's reachability
answer or an SCC-based owner-visibility directory. It must answer the same
`reachesAny` relation, including owners outside the graph. Do not substitute
global visibility. Local W/R attachments still use complete `MethodKey` owners.

Choose a sparse or shared owner-set representation after measuring retained
size. Limit its lifetime to the incoming run-2 demand snapshot. Do not introduce
a general weak cache or rewrite the soft-reference manager for this proposal.

### Proof and verification

The [EntryProjection model](../../spec/lean/proposals/restricted-demand-next/EntryProjection.lean)
has 20 audited declarations with no axioms. It constructs both directions
between full symbolic closure target projection and the entry fixed point.
It also proves actual-selector admission equivalence, preserves visibility
witnesses and proves that every colored entry has a primitive mapped-seed
origin. It includes the required FLOW color-transport counterexample.

Its scope is finite compatible nonzero seed rows. Production AP overlap,
index completeness, ZERO/carry adapters and prescan reachability are not proved
by that file. Close those adapters before replacing C2. C5 remains unchanged;
the model does not authorize any C5 relaxation.

Test exact C2 initial-set equality against the current paired implementation,
not only finding counts. Include STATIC/nonstatic targets, overlapping paths,
different tails, field E, FULL/GROUP directions, cycles, owner contexts, absent
actual marks, outside-graph owners, ZERO and static carry. Retain paired C5
tests with two equal entries but different exits.

Count entry memberships, delta states, paired rows avoided, reachability
traversals, C2/C5 lookup time, allocation samples and retained index size.
State reduction is expected when many left endpoints share an output entry.
It can be small when each pair has a distinct entry. The current profile does
not measure that ratio; benchmark it rather than promise a fixed speedup.

## 3. Investigate the generated Spring registry block

Stirling's largest point owners include many per-controller dispatchers, each
with about 35,000 occupied rows. The current source has this generated pattern
in each dispatcher, including per-controller dispatchers:

```java
// For every componentRegistryField, not only the selected controller's fields:
savedA = Registry.componentA;
savedB = Registry.componentB;
// ...
__cleanup__(); // clear static state
Registry.componentA = savedA;
Registry.componentB = savedB;
// ... then choose the next loop iteration
```

`SpringWebProject.ndMethodDispatch` generates all registry reads and writes.
`generateCleanup` adds an all-static cleaner. This is a concrete source of
repeated instructions, local copies and static writes. The heap classifier
has not counted field names, so it does not prove how much of the 9.61 million
named-field TAINT population comes from registry fields.

First count registry-field headers and occupied rows in these blocks. If this
work dominates, design a composed transfer for the generated block, or an
equivalent generator operation that preserves registry state without all local
copies. Before: execute and store each save/cleanup/restore step. After: compute
the same block effect without those internal copies, where equivalence holds.

This is not permission to skip the cleanup or change static order/context.
The proof must preserve intermediate rule observations, aliases, cleaner
effects, immediate run-1 pool supply, writer registration, exit rules and
summary demands. If any of those observations cannot be preserved by a bulk
operation, keep the original block. A source-generation or cleaner semantic
change must be stated as a major change and selected separately. No proof or
measured saving is claimed for this investigation.

## 4. Later heap work and unresolved correctness

Conductor reaches run-4 OOM with 7.65 GB of live objects. Active method-state
and subscription owner unions are large; its run-1 completion graph is gone.
Stirling reaches run-5 OOM with 7.62 GB of live objects, including 7.45 million
`ConclusionGroup` and 7.44 million `TaintGroup` wrappers. Most static TAINT
headers represent named fields. ND premises and protection trees are rare.

Do not assume that each conclusion group is a singleton from these totals.
A later census must count group occupancy and shared ownership. A direct
small carrier that promotes on a second incompatible group can then preserve
all logical facts while removing eligible maps/lists. The unused-kind-map
estimate alone is about 0.35 GB, not a two-times heap reduction.
This is a technical reserve, after the algorithmic work above.

The report identifies three strict Stirling baseline differences. Two involve
exit-location export without trace provenance. One has a local loss mechanism
in the explicitly selected D23 source-output reset policy. These need separate
correctness designs. Changing reset semantics or reporting provenance is a
major change; neither is hidden in an optimization above.

Do not stop OWASP iterations merely because finding counts are stable. Its
backward demand and local-state growth still require a valid stopping proof.
Do not add a new mark-abstraction policy or later-run static approximation to
fix the present memory failures.

## Implementation order and acceptance

1. Establish production raw exhaustion certificates. Keep conservative replay
   for uncertified paths. Prove exact guidance equality and measure omitted work.
2. Add the entry view beside the paired view. Check exact C2 admission equality
   in local tests. Then route C2 to it and retain C5 on the paired path.
3. Reuse immutable visibility after its reachability equivalence is checked.
4. Commit each selected runtime change before measurement. Use only the four
   fixed project configurations in `task.md`; reuse the saved baseline.

Keep phase times separate: run-1 engine, joined binding, graph freeze, report
barrier and each later run. Report latest reached/completed/accepted forward
runs. Compare exact sink identities and locations. Preserve the three known
strict gaps as failures until their correctness fixes have separate evidence.
An optimization is accepted only when it preserves the selected semantics and
reduces its measured target work without a larger retained-state problem.

Proof receipts are beside the two Lean models. All 39 audits are constructive
and use no axioms. They are proposal-level contracts, not a whole-analyzer proof
or measured performance result. No runtime source was changed for this proposal.

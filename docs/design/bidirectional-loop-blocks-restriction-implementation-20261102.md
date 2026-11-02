# Implementation proposal: method-owned loop blocks and loop restriction

Date: 2 November 2026. Status: implementation requires the boundary-span
correction in section 0.1. Native controls reproduce missing entry-source
and exit-sink effects. The latest measured revision completes OWASP **run-5**
with 51 missing baseline sink identities. The final project campaign and
performance acceptance are not complete.

### 0.1 Boundary-span correction and acceptance gate

Use the [selected boundary coverage contract](../../spec/method-owned-loop-blocks.md#61-required-coverage-of-an-original-method-boundary)
and the [native gap report](../reports/bidirectional-loop-boundary-source-gap-20261102.md).
The current root executes the actual entry and exit rules. Its saved child
BL rows start after entry rules. The loop observer's saved AL probe stops
before exit rules. Thus it can apply enclosing C5 to an incomplete result.

The correction must provide genuine boundary-inclusive NORMAL records and
selected DEMAND/Target guidance from run-1. Use the original handler and
normal record replay. Keep the complete original and actual control ports.
Include the required ancestor boundary when the adjacent region is nested.
Do not add another rule evaluator or change field transfer, C2, source
permissions, ND execution or original-ZERO-dependent exit adjustment.

A root completion snapshot is not a complete correction. In the exit-sink
control, run-1 has a public `ZERO -> DemandTarget`, but no scoped AL Target.
Run-2 computes `ZERO -> x.f.$/T` through the exit sink seed and AL body. A
new full-suffix scope has no paired guidance that can admit this row at C5.
The corrected ownership must provide that guidance from its genuine run-1
derivation. Relabelling a body row or inserting an unrestricted snapshot
does not supply it.

The standalone boundary model proves finite relation laws. It does not
verify this runtime adapter. Before accepting the correction, require the
entry and exit native loop controls to pass, preserve their no-feedback
controls, refresh native/source correspondence checks, and rerun the four
fixed project configurations from the final commit.
Section 6.1 uses the existing discovery graph and the selected narrow
exceptional-ZERO demand lookup.
Language: ASD-STE100 Simplified Technical English.

Implement [method-owned-loop-blocks.md](../../spec/method-owned-loop-blocks.md)
and [loop-fragments-and-demand-collapse.md](../../spec/loop-fragments-and-demand-collapse.md).
Follow [impl-proposal-guide.md](../../spec/impl-proposal-guide.md) and
[proof-guide.md](../../spec/proof-guide.md).
The [implementation proof dossier](../../spec/loop-blocks-implementation-proofs.md)
states the checked reference laws and the production correspondence tests.

Source baseline: `7b59054ef`. Its analyzer runtime is unchanged from
`8213756108af9cd278668db871fc77428caec64a`. The proof package records the
reviewed source hashes. Recheck those hashes before implementation.

The [latest measurement](../reports/bidirectional-demand-relative-summary-restriction-performance-20261101.md)
reaches Conductor **run-6**, with **run-5** complete/accepted;
Stirling-PDF **run-8**, with **run-7** complete/accepted;
Thingsboard **run-2**, with **run-1** complete/accepted; and OWASP
**run-5**, complete/accepted. These are reference results, not new runs.

## 1. Result and semantic scope

```text
one RunMethodAnalyzer per original MethodKey
    immutable block layout
    local state per block entry port
    existing method-owned work reservation
    public method summaries at the root only

B1 = BL1 ; L1 ; AL1
AL1 = B2 = BL2 ; L2 ; AL2       // AL is a complete recursive region.

loop traversal result
    -> existing block summary application
    -> strict summary-shape test, FL(Zero)=0
    -> growing: AL/BL C2 + composed enclosing-B C5 + L C2
    -> preserve every selected image; cut only to MAY/DEMAND
    -> fresh post-output admission
    -> actual repeat/leave destination
```

`N` means NORMAL, `D` means DEMAND, `$` means EXACT, `*` means STAR,
`[any]` means MAY, and `[any-taint]` means MUST. FL counts concrete field
and element accessors. Its ZERO=0 convention is only for the loop shape
test. It does not change typed ZERO/Target matching.

These are selected semantic changes:

| Part | Current runtime | Proposed runtime |
|---|---|---|
| Analysis boundary | One method boundary | Additional local block C2/C5 boundaries |
| Cyclic work | Distinct paths repeat through the method CFG | Reuse one-traversal block summaries and restrict growing outputs |
| Loop output | Global field limit and post-S deduplication | The selected three-family restriction before repeat and leave delivery |
| Refinement scope | Method-owned rows | Method-owned collection of separately scoped block rows |
| Summary bases | Public method interface only | Internal rows can conclude at original locals; the root keeps the public filter |
| Backward ZERO at an exceptional block exit | No separate scoped normal-exit lookup | Apply unchanged normal control demand; address its outgoing ZERO DemandTarget by the borrowed normal invocation in handoff metadata only; section 6.1 |

Additional cuts can delay a NORMAL record or finding. This is not a
claim of equal per-run findings. Every relevant cut must retain its
selected refinement guidance. Exact CFG decomposition alone does not
prove that approximation contract.

Keep unchanged:

```text
original IR, methods, calls, registers, instructions and configured rules
physical source/sink IDs, GeneratedMark IDs and source-permission policy
all field reads/writes, cleaners, exclusions, marks and protection laws
AP C2, paired C5, demand-relative C5 limits and FLOW normalization
complete ND execution; unary ND arms are restriction metadata only
actual-call alias handling and the original alias query context
saved NORMAL replay before demand; no new standing raw-input history
run-1 static effects, static shortcut and typed Target policies,
except the explicit exceptional-ZERO lookup in section 6.1
ignored END_FACTS stages; actual method entry/exit rules only at their
original physical boundaries, with summary publication at the nearest block
FULL acceptance, known GROUP limitations, schedule 1,1,2,3,…
```

No generated method, synthetic call plan, argument packing or alias
translation is needed. A no-loop method uses the existing single-root
path. Do not add GroundingSupport, StrongQueries, a NORMAL graph service,
a raw summary cache, or another field/mark policy to implement this work.

## 2. Source map and owned data

Paths in this table are under
`core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/`.
New file names are proposed names.

| File | Work |
|---|---|
| `graph/MethodBlockLayout.kt` (new) | Immutable region tree, physical ports, instruction ownership and local point directories |
| `graph/MethodBlockLayoutBuilder.kt` (new) | SCC decomposition, recursive AL, loop feedback cuts and certificate validation |
| `bidi/engine/MethodContextCache.kt` | Access/cache the layout beside the original graph; share it across directions |
| `bidi/engine/BlockRunState.kt` (new) | Local stores, initials, local services and pending work under the method owner |
| `bidi/engine/RunMethodAnalyzer.kt` | Keep the actor; route block work, root rules, real-call results and freeze |
| `bidi/engine/BlockSummaryLinks.kt` (new) | Owner-local subscriptions, parent composition and request delivery |
| `bidi/engine/LoopOutputRestriction.kt` (new) | Shape classifier and the complete three-family observation/projection |
| `bidi/engine/CfgDeliveryCache.kt` | Stop at local boundaries; keep empty-result caching |
| `bidi/store/MethodEdges.kt` | Parameterize point indexing; preserve admission and packed storage laws |
| `bidi/store/DemandStore.kt`, `RecordStore.kt` | Provide scoped views of existing C2/C5 and saved record indexes |
| `bidi/store/RunSummaries.kt` | Reuse admitted storage separately for each entry/exit scope |
| `bidi/store/AddedFacts.kt`, `engine/RunMethodCallServices.kt` | Carry the waiting block scope in real-call continuation references |
| `bidi/engine/RunMethodLocalServices.kt`, `EngineAlgebra.kt` | Bind explicitly to local block services, keeping the original method context |
| `bidi/engine/Run1PointResume.kt` | Route a method-owned resume ticket to its original block scope |
| `bidi/driver/HandOff.kt`, `Frontier.kt`, `IterationDriver.kt` | Freeze/persist every block; aggregate selected outgoing frontiers by original method |
| `bidi/engine/JoinedStaticGuidance.kt`, `JoinedStaticWriterBinding.kt` | Traverse local parent links before real callers and freeze scoped static guidance |

Use these identities:

```kotlin
@JvmInline value class BlockId(val ordinal: Int) // Deterministic tree preorder.
data class BlockScope(val block: BlockId, val entry: PortId)
data class OwnedScope(val method: MethodKey, val local: BlockScope)
data class BlockRowKey(val scope: BlockScope, val exit: PortId, val premise: PremiseKey)
```

A BlockId ordinal encodes a unique deterministic tree path in its immutable
layout. Derive the readable path from parent links only for diagnostics;
do not copy the full path into every deeply nested AL node. MethodKey
remains the public method identity. Block scope is storage/control metadata; it is not part of
Facts, InitialAp, rule identity, mark identity or their equality/hashing.

| Entity | Scope |
|---|---|
| Edge/initial stores, summaries, request rows, current joins, saved block rows | Block + entry port; summary rows also retain exit port |
| Real-call waiting reference and static resume ticket | Original method plus waiting block scope |
| Source permissions | Existing physical method/site/source key; aggregate local hits without adding a new permission predicate |
| Static pool | Existing field/mark key; only its return ticket carries local scope |
| ReportId | Existing physical sink location and rule ID |
| Public method summary | Original MethodKey, root scope only |

## 3. Immutable layout construction

### 3.1 Graph and boundary points

Use `MethodInstGraph` and its original instruction indexes. Do not load
or bind every rule to find loops. The graph, not rule specialization,
determines the layout.

```kotlin
sealed interface LocalPoint {
    data class Instruction(val originalIndex: Int) : LocalPoint
    data class ChildResult(val child: BlockId, val exit: PortId) : LocalPoint
    data class Boundary(val port: PortId) : LocalPoint
}

data class Port(
    val fromOriginal: Int,
    val toOriginal: Int,
    val kind: ExitKind,
    val loop: BlockId?,
)
```

A boundary is between physical instruction transfers. Its forward edge
connects `after(u)` to `before(v)`. Backward routing reverses that edge;
it does not execute a second copy of either instruction. Keep the
original source/destination and return/throw/handler kind on each port.
The frontend's existing method entry and post-return exit handlers remain
at their original physical points. Their completed results and Target rows
belong to the nearest block summary interface. Parent summary propagation
then reaches the original method. Do not copy a method boundary rule to an
ordinary internal block entry or exit.

A composite has local child-completion points. It does not duplicate
its children's original instruction points. Do not create fake
CommonInst values or negative LanguageManager indexes for routing.

### 3.2 Builder

Use the existing `IntGraph` SCC algorithm, but include isolated vertices
explicitly in the region directory: `IntGraph.allSccs()` currently gets
its vertex set from edges. A one-node self-edge is a loop.

```text
buildRegion(R, inheritedBoundaryEdges):
    compute SCCs of R after removing inherited boundary edges
    order the SCC condensation DAG deterministically
    choose its first cyclic SCC core

    if none:
        return SequentialLeaf(R)

    headers = core vertices with an external entry into core
    include original region start vertices that lie in core
    if headers is empty:
        choose core's least original index as a layout header
        // Structural choice only. Do not seed a fact or add an edge.

    repeat = existing core-internal edges whose target is in headers
    plan = certifyNormalLeaveTails(core, R, inheritedBoundaryEdges,
                                  enclosingHeaders, normalExit, exceptionalExit)
    L = core + plan.tails  // The actual common join stays outside L.
    BL = the preceding acyclic SCCs
    AL = all remaining vertices outside BL and L
    iteration = buildRegion(L, inheritedBoundaryEdges + repeat)

    return SequentialComposite(
        before = SequentialLeaf(BL),
        loop = Loop(iteration, repeat, plan.normalInterface, original typed outlets),
        after = buildRegion(AL, inheritedBoundaryEdges)
    )
```

`MethodBlockLayoutBuilder.expandNormalTails` uses the condensation DAG to
find the nearest common normal postdominator. Include the real leave tails
before that join. Keep divergent tail SCCs in the traversal; the recursive
builder handles their own loops. Do not move a method normal exit into the
loop. Use the frontend's actual normal and exceptional endpoint metadata.
An exception-only tail stays a typed outlet.

An enclosing loop header can be the real join when local leave tails all
reach that same existing boundary. For example:

```text
inner core={2,3}; tails={4,5,6}; actual join=outer header 1
inner repeat: 3->2
inner normal family: 5->1, 6->1
outer view of those same edges: the original outer repeat ports
inner AL={}
```

Keep header 1 outside the inner body. The port view depends on the current
interface; the physical graph and feedback owner do not change. An inner
normal completion must recover the actual outer repeat ports at the outer
boundary. Do not replace them with a new edge or enter the outer header
before the outer traversal restriction runs. If no real common normal
boundary can be certified, retain an explicit `normalExitGaps` certificate.
Do not choose one target or add an all-target dispatch.

Assign one stable `J` ID for each certified normal interface, after the
physical-port range. Start backward discovery IDs after that reserved
range. `J -> original routes` is an immutable directory. Ordinary forward
normal delivery has one actual target. Reverse native/demand delivery
recovers every original predecessor and its original role.

Use a stable topological order, with original instruction index as a tie
break. Every cyclic SCC has an internal incoming edge to a selected
header. Cutting those edges removes at least one current edge. Inner
cyclic SCCs avoid the selected headers and are decomposed recursively.
Use `(vertex count, current internal edge count)` as the decreasing
lexicographic measure. The AL region also has fewer vertices than R. Implement the builder and
freeze walk with explicit frame stacks, so a deep AL chain does not consume
the JVM call stack. Assign compact preorder IDs after construction.

The iteration plan is the loop block's own in-block graph. If it is
acyclic, L owns those physical points directly. Do not add an unconditional
second body-admission layer just to mark the block as a loop. Nested loops
use the selected recursive region plan within this traversal.

For an ordered body:

```text
prefix ; loop1 ; loop2 ; suffix

B1 = { BL1=prefix; L1=loop1;
       AL1=B2={ BL2={}; L2=loop2; AL2=suffix } }
```

For general branches, retain the original bypass and multi-entry ports.
A route may enter the appropriate descendant directly. The topological
partition does not mean that every path must execute L. A multi-entry
SCC retains all its entry ports. Never choose one input as a semantic
replacement for another.

An empty BL is an identity region. Keep its stable logical ID and do not
create a physical instruction. If it is the first logical method span,
execute the original method entry rules there once, then return their
results through that identity interface. The actual first instruction can
belong to L and executes there on each real loop traversal. Other empty
regions do not copy method boundary rules. They need no new argument
binding or alias expansion. Use the ordinary
entry/replay policy, identity transfer for an admitted initial, and the
same local C5. Eliding its empty physical control step must preserve those
logical admission and entry/exit scopes; it is not a C2 bypass.

### 3.3 Validate before use

```text
check every original transfer is assigned exactly once
check every physical CFG edge has one exact labelled route
check every route starts/ends at that edge's original endpoints
check the containment parent/depth certificate
check non-feedback local edges have increasing local topological rank
check ordinary backward ports reverse the physical forward ports
check existing backward-only discovery edges are retained in that view only
check method start/normal exit/exceptional boundaries retain their roles
```

A rejected certificate is a decomposition bug. Correct it before shipping;
do not silently drop a region, merge ports or switch to another field
policy. Cache immutable topology with the existing form/graph lifecycle.
Do not add a strong global cache of forms, rules or run facts.

## 4. Block runtime and method scheduler

```kotlin
class BlockRunState(
    val scope: BlockScope,
    val points: LocalPointDirectory,
    val edges: ScopedEdgeStore,
    val initials: InitialFactStore,
    val summaries: PortSummaryStores,
    val demand: ScopeDemandView,
    val persisted: ScopeRecordView,
    val work: DeltaWorklist,
    val local: BlockLocalServices,
    val calls: BlockCallServices,
    val admission: Run1Abstraction?,
)
```

Allocate mutable state on first entry, not by eagerly resolving every
block's instructions or rules. One method actor owns all these objects.
There is no actor, thread, UnitRunner or inter-runner event stream per
block. Existing local/call service factories accept an explicit
`BlockRuntime` interface; do not select a mutable global "active block".
Callbacks capture the scope that owns their work.

Refactor `MethodEdgeStore` indexing through a point directory:

```kotlin
interface PointDirectory<P> {
    val size: Int
    fun index(point: P): Int
}

// Existing rows/bitsets/ConclusionGroup logic, with a local point count.
class ScopedEdgeStore<P>(points: PointDirectory<P>, /* existing AP arguments */)
```

Do not allocate a method-sized point array for every block. Lowest blocks
index their own physical points. Composites index their child completions
and boundaries. The no-loop root directory maps existing instruction
indexes directly, so its current fast path stays available.

Allocate a child-completion payload store only after that completion is
reached. Use a one-point `ScopedEdgeStore` for each reached `ChildResult`.
This reuses the existing global field cap, packed rows, protection transport
and output deduplication. Do not replace these laws with a separate map of
unbounded AP payloads.

The method schedules ready scopes. Preserve the existing ZERO-first and
configured FLOW-first lanes across ready scopes. Batches include scope
and point in their key; equal AP packets from different entries must not
merge into one batch.

```text
method work quantum:
    drain queued original static/call resumes in their captured scope
    drain fresh local summary/Target/request deliveries
    process ready scoped instruction work under existing priority
    commit pending local publications
    at an empty-body barrier: commit existing request/static batches
    idle only if all of the above are empty
```

Keep the method's existing Work reservation through commits and local or
external sends. A local delivery uses the owner queue and can make the
method ready again. It never waits for an external runner to wake it.
An external static-boundary reply must secure that reservation when it
adds a fresh local input or replay delivery. The child may already have
the same concrete initial. Initial deduplication therefore cannot replace
the enqueue required for new link work. The post-join static-guidance
phase only borrows inputs and builds frozen rows; it must not create live
deliveries after runner completion.

## 5. Scoped demand and persistence adapters

```kotlin
interface ScopeDemandView {
    fun initials(actual: Facts, policy: RestrictedInitialPolicy): Set<AdmittedInitial>
    fun intersect(original: PremiseKey, raw: Facts,
                  policy: RestrictedInitialPolicy): List<Facts>
    fun acceptsTarget(original: PremiseKey, policy: RestrictedInitialPolicy): Boolean
}
```

Extract the existing method-indexed C2/C5 code into a scope-indexed core.
The public MethodKey API delegates to the root view. The internal view
supplies its scope's exact entry index, complete paired rows, control rows
and permitted run-2 static-completion adapter. The AP matching and cut
functions stay the same. Do not implement a second C2 table.

```text
current DemandStore.initials -> shared core + selected scope indexes
current DemandStore.intersect -> shared paired core + same per-row budget
current RecordStore indexes -> shared core + selected saved scope
current NormalTarget store -> root or local scope with the existing rules
```

All newly inferred block summaries pass normalization and complete paired
C5 before `RunSummaryStore.addAdmitted`. They use the same per-row
`min(runLimit, FL(demand.exit)+1)` rule. No raw candidate collection is
stored. Root summaries are not exempt.

The current `retainSummary` calls `interpreter.isSummaryBase(facts.base)`.
Keep that filter at the public root only. An internal region must retain
LocalVar conclusions, or a row such as `x.f.* -> x.*` disappears before
loop sharing starts. Internal bases still pass RuntimeDataDomain and
exclude CleanerTemporary and constant facts. This is the selected local
interface, not a change to public method arguments or mark matching.

Normal records retain producer direction, complete premise, E and
protection exactly as now. Opposite-direction views use the current
`Record.forEachReversedAt` law. Keep the native-record eligibility test.
A saved port row is indexed by both producer entry and producer exit.
For an opposite-direction read, its entry is the reversed producer exit
and its exit is the reversed producer entry. `Record.forEachReversedAt`
reverses the AP payload; the scoped adapter reverses these control ports.
Handoff uses the same port swap along with its existing endpoint reversal.
It cannot keep only the producer's forward entry key.

Snapshots store BlockId, entry/exit port and layout identity; they do not
retain actors or bound forms. Root views remain compatible with existing
method consumers and complete predefined method models.

## 6. Entry, local links and one-traversal summaries

```kotlin
fun enterChild(link: LocalLink, actual: Facts) {
    val child = state(link.childScope)
    replaySavedRows(child.persisted, actual, link) // Every complete offer.
    replaySavedTargets(child, actual, link)        // Existing NT policy.

    if (config.run1) {
        subscribeLocal(child, link, actual)
        child.admission!!.emit(link, actual)
        return
    }
    val initials = child.demand.initials(actual, config.admissionPolicy)
    if (initials.isEmpty()) return
    subscribeLocal(child, link, actual) // Before a same-owner publication.
    child.start(initials)              // Do not repeat C2 in start().
}
```

`Run1Abstraction` gets a small input-origin interface instead of requiring
that every input is a physical CallerRef. Its input/answer rules remain
unchanged. Real calls use the real-caller variant; block entries use a
local-link variant. Do not fabricate a call instruction for this adapter.

```kotlin
data class LocalLink(
    val parentScope: BlockScope,
    val parentPoint: LocalPoint,
    val parentOriginal: PremiseKey,
    val parentLayer: Layer,
    val childScope: BlockScope,
    // parentPoint is J for a shared normal invocation, otherwise the exact port.
    // The layout directory stores J's original physical labels.
)
```

Use the current exact accumulation/live delta and membership rules for
active links. Saved replay does not require retained fresh-only input
history. No link key contains an iteration counter.

On `I -> C`, match the complete offered input with `ops.satisfying`, then
apply `ops.applySummary(..., original=link.parentOriginal)`. Reuse native
record/MUST handling and complete KaryJoin binding from call services in
a shared AP relation applicator. The internal result sink replaces only
the physical-call suffix; it runs no BIND_IN/BIND_BACK or extra alias pass.
Apply existing pending MUST demotion before committing the block result,
since an internal boundary has no call-action suffix to execute first.
Apply the existing global field limit to the actual composed result before
it enters the parent's `ChildResult` store or another local input link.
Native application can append the caller's suffix to a stored row and thus
exceed that limit even when the stored row itself is bounded. This is the
existing W3 bound; it is not an extra loop-specific field policy. Classify
growth from the stored applied row before this cap. The read-only observer
in section 8 still composes a saved row exactly and then applies enclosing
paired C5; it does not add an actual-delivery cap to that observation.

A loop row ends one traversal at a labelled repeat or leave port. The
waiting parent prefix and this row produce `F = P -> result`. Keep P;
never substitute the child's I. The loop output handler receives both
that F and the applied row geometry. Root/nested B C5 uses its own P.

For ND rows, the full join must finish before a result is offered. Retain
the complete joined original. For restriction metadata, flatten the
applied ND row into real unary arms. The union of arm results is
conservative; an equal/shrinking arm can retain the complete valid result.
Do not enumerate origin products for this metadata or execute a unary
arm as if it were the ND rule.

### 6.1 Existing discovery and selected exceptional-ZERO demand lookup

The current backend already handles a loop without a normal leave.
`JIRMethodEntry.graph(BACKWARD)` returns the reverse of
`JIRExitWiredGraph`, not merely the reverse of the raw forward graph.
That wrapper connects each node that cannot reach an original exit to the
exceptional exit before reversal. Backward ZERO starts at both original
exits through `DirectedForms.startNodes(key, zero=true)`.
This is the existing interpreter I11(e)/AP S11 contract.

```kotlin
val tree = buildLayout(contexts.graph(key, Direction.FORWARD))
val forwardView = routeView(tree, contexts.graph(key, Direction.FORWARD))
val backwardView = routeView(tree, contexts.graph(key, Direction.BACKWARD))
// backwardView retains the existing exceptional discovery edges.
```

Classify a backward edge as ordinary reversed control or existing
backward-discovery control by comparing it with the raw forward edge
set. Store that classification in layout/view metadata. It is not an AP
mark, extra forward edge or normal loop leave. The tree and register
namespace remain the same in both views.

Keep Target conclusions at the logical normal exit. Publish them through
the current terminal channel without waiting for a normal loop leave.
The selected compatibility hack is a demand lookup exception:

```kotlin
fun controlDemand(at: ReachedBoundary, input: Facts): PairedRows {
    val own = demand.at(at.actualPort)
    return if (!forward && input is Reach && at.isExceptionalExit)
        own.unionCompleteRows(demand.atNormalExit())
    else own
}
```

`ReachedBoundary` must come from the existing start/routing operation.
It is not a scan of stored demand. Keep each borrowed row's complete
entry, exit and annotations. The existing typed matcher must admit ZERO;
later publication still tests that row's paired exit. Do not turn
normal Target guidance into an unpaired ZERO permission.

When a reached discovery edge enters a block, preserve its actual target
instruction and route through the supplied backward CFG. The exception
does not alias Target control rows to all physical entries. It does not
change DATA admission or native record entry/exit ports. Forward lookup,
non-ZERO packets and non-exceptional boundaries use their ordinary view.
The existing exceptional-start set is unchanged. No copied method
entry/exit rule is added.

```text
B: while (true) { sourceFFFF(x); x=x.f; sinkRootT(x); }

forward view:     the body repeats; no edge to either original exit
backward view:    exceptional exit -> original non-exiting body points
run-2 ZERO:       admitted by Target guidance; visits the sink/source
run-3 FULL:       limit 2 can still leave a DEMAND candidate
run-5 FULL:       limit 4 can represent the exact four-field source path
```

Do not start every locally demanded block through a new direct-start
scan. Do not put discovery edges into the forward view or turn them into
NORMAL return summaries. Reuse the supplied oriented graph and its
existing policy. The new lookup borrows normal demand at an already
reached exceptional ZERO; it adds no backward-ZERO start policy.

Keep a witness when that ZERO is admitted by a normal control row. A
backward-only discovery port must not become a required forward address.
Normalize only the outgoing ZERO DemandTarget handoff metadata:

```kotlin
fun targetHandoffScope(actual: BlockScope, original: PremiseKey,
                       target: Target, normalBorrowed: Boolean): BlockScope =
    if (!forward && normalBorrowed && original.isZero && target == DemandTarget)
        actual.copy(entry = ROOT_EXIT) // Borrowed normal invocation.
    else actual
```

`normalBorrowed` records actual admission by one complete normal control
row at the exceptional/discovery ZERO route. It is not graph membership
or a scan result. Keep the row's complete pair, actual logical exit and
annotations. Only the later handoff address changes. Current/live scopes,
DATA/native physical ports, persisted NormalTarget and non-ZERO Target
rows remain unchanged.

For example, backward `(entry=d, ZERO -> DemandTarget, exit=ROOT_ENTRY)`
is handoff-addressed as `(entry=ROOT_EXIT, ZERO -> DemandTarget,
exit=ROOT_ENTRY)`. Reversal gives the next forward normal control pair.
Keeping backward-only `d` loses the run-3 continuation before run-5 can
resolve `sourceFFFF`. This law closes the continuation of the same
borrowed normal demand; it creates no new initial or source permission.

The [native control record](../../spec/lean/proposals/loop-fragments-and-demand-collapse-20261102/controls.md#existing-backward-discovery-with-no-loop-leave)
records four historical passing checks. Its two-field FULL control completes **run-3**,
with one report and no forward visit to either exit. The `Discovery` model
constructs the exceptional reachability witness and proves that normal
backward starts gain no new route.

### 6.2 Genuine original boundary spans

The original method actor admits its initial once. Route its pre-rule
input into the first logical span. Use the existing rule handler, not a
query-time rule evaluator or a copied source summary.

```kotlin
// BlockRunState.addInitial, after the existing root initial admission:
for (node in forms.startNodes(key, zero = initial.isZero))
    rootRouting?.start(node, initial, start) ?: startAt(initial, node, start)

// The first actual leaf, or an empty first BL:
state.startAt(original, actualMethodStart, value)

// The same captured continuation handles initial and static-point resumes:
override fun startResult(state: BlockRunState, node: CommonInst,
                         original: PremiseKey, value: Facts) {
    if (isEmptyBlock(scope.block)) state.retainBlockSummary(scope.entry, original, value)
    else routeInside(entry, actualIndex(node), original, value, scope.entry)
}

// At the real original end, after its original physical transfer:
override fun methodBoundary(state: BlockRunState, node: CommonInst,
                            original: PremiseKey, value: Facts, summary: Boolean) {
    state.endAt(original, node, value, summary)
}
```

These local spans include the real entry/exit rules. Their NORMAL rows use
ordinary native persistence; their DEMAND and Target rows use ordinary
scoped handoff. A saved span which already includes the original boundary
must not execute that boundary again after replay. Fully saved spans can
therefore finish with no physical instruction processing.

Keep the selected backward exceptional-ZERO adapter: an actually reached
original exceptional start executes its existing root handler and actual
discovery successors. Do not put an empty AL C2/C5 gate before that already
admitted original control transfer. This exception does not admit DATA,
scan demanded blocks, or create a forward leave.

Canonical normal invocations use the same `J` in `BlockScope.entry` and
`LocalLink.point`. This lets the ordinary complete ND join combine the
accepted normal leave paths. Feedback and typed outlets keep their own
interfaces. Different actual predecessors of a reverse `J` share that
certified input; dispatch each admitted initial to those real predecessors.
Do not generalize this rule to arbitrary multi-target DATA entries.

## 7. Physical processing, CFG delivery and external returns

```kotlin
fun process(scope: BlockScope, input: EdgeDelta) {
    // Original method, instruction, statement/call forms and rule IDs.
    runtime(scope).processOriginal(input)
}

fun completeOutput(scope: BlockScope, point: LocalPoint,
                   original: PremiseKey, value: Facts) {
    val fresh = state(scope).edges.add(point, original, value) ?: return
    deliverWithinScopeOrToBoundary(scope, point, original, fresh)
}
```

The row at S is the result after processing S. Do not store that result
at every successor. Original relevance checks still use the original
instruction and method. A local CFG cache stops at boundary vertices
regardless of base relevance. It returns typed destinations:

```kotlin
sealed interface DeliveryTarget {
    data class Statement(val originalIndex: Int) : DeliveryTarget
    data class Boundary(val port: PortId) : DeliveryTarget
}
```

Cache by immutable layout, scope/direction, start point and base. Cache
empty answers too. Cancelled BFS never publishes a partial answer. ZERO
can keep its existing direct lane, but that lane also routes through
explicit boundaries; it cannot jump over block control.

A real call keeps its original CallPlan, stage order and alias logic.
Add the waiting block scope to CallerRef as continuation metadata, with
the root scope as the compatibility default. Current subscriptions, ND
join keys, unresolved-observation keys and resumed call frames use that
scope. Reports and CallPlan identity do not. Audit every constructor and
copy of CallerRef. In particular, static-input rebinding must preserve
the waiting scope: `ref.copy(premise = selected)`, rather than constructing
a new reference that silently defaults to root. Use one scope-aware
reference factory for real call entry.

When the original method actor receives a real callee result, resume its
captured scope/stage. A static resume token is unique across the method;
its method-owned table contains the block scope and existing point-resume
state. Separate block counters must not generate colliding global tokens.

## 8. Read-only loop observation and bounded projection

### 8.1 Classifier and consumer scope

```kotlin
fun countFields(initial: InitialAp): Int =
    if (initial.isZero) 0 else initial.pathData.count { it.isCounted() }

fun grows(member: InitialAp, conclusion: Pattern): Boolean =
    conclusion.fact.path.count { it.isCounted() } > countFields(member)
```

Use each scalar output path. Typed Targets use their existing terminal
channel and do not enter this geometry classifier. A non-growing row
passes unchanged. Run-1 keeps its existing first-run/global-limit policy;
there is no empty previous-demand rejection on run-1.

For forward use `(next=AL, enclosing=B, repeat=L)`. Backward uses
`(next=BL, enclosing=B, repeat=L)` on the same tree. For L1 in a two-loop
body, next is all of AL1/B2. For L2, enclosing is B2, not B1.

### 8.2 Exact observer

```kotlin
data class Observation(
    val nextInitials: Set<AdmittedInitial>,
    val enclosingResults: AnnotatedResultSignature,
    val loopInitials: Set<AdmittedInitial>,
) {
    val empty get() = nextInitials.isEmpty() &&
        enclosingResults.isEmpty && loopInitials.isEmpty()
}

fun observe(ctx: LoopGateContext, F: ScopedEdge): Observation {
    val next = ctx.next.demand.initials(F.value, policy)
    val full = ExactScopedResults()
    for (record in ctx.next.persisted.applicableRows(F.value, mode)) {
        applyNativeReadOnly(F, record) { composed ->
            offerAtEnclosing(ctx, F.original, composed, full)
        }
    }
    for (target in ctx.next.savedTargets.candidates(F.value, mode)) {
        applyTargetReadOnly(F, target) { composed ->
            offerAtEnclosing(ctx, F.original, composed, full)
        }
    }
    val repeat = ctx.loopEntry.demand.initials(F.value, policy)
    return Observation(next, full.freezeAnnotatedSignature(), repeat)
}

fun offerAtEnclosing(ctx, original, value, out) {
    when (value) {
        is DataResult -> {
            if (ctx.enclosing.isRoot && !interpreter.isSummaryBase(value.facts.base)) return
            val n = normalizeFlowSummary(ap, original, value.facts)
            for (kept in ctx.enclosing.demand.intersect(n.premise, n.facts, policy))
                out.addData(ctx.enclosing.scope, n.premise, kept)
        }
        is DemandTargetResult -> if (ctx.enclosing.demand.acceptsTarget(original, policy))
            out.addTerminal(original, value)
        is NormalTargetResult -> if (forward && value.normalBinding &&
                !ctx.enclosing.savedTargets.contains(original, value.id))
            out.addTerminal(original, value)
    }
}
```

The DATA probe follows the actual summary boundary: public-base selection
at root, existing complete FLOW-pair normalization, then C5. Point initials
stay unchanged. Normalization can canonicalize an EXACT/FLOW header to
STAR; retain that resulting complete header in the observation signature.
Do not compare against a C5 call made on the pre-normalized pair.

`applicableRows` performs the existing forward/reversed NORMAL candidate
lookup, matching and protection-aware union. It uses every relevant saved
row, not an arbitrary first witness. `applyNativeReadOnly` uses the shared
AP relation applicator from section 6, including native MUST lanes and
backward ZERO-to-Target result typing, with a query-local result sink.
It executes no call suffix, rule, source-hit callback, static supply,
subscription, report or real exit handler. Include the existing saved
NormalTarget candidates in this read-only composition too. Typed composition results use the existing matching probe
for that endpoint: DemandTarget uses `acceptsTarget`; NormalTarget is
forward-only, requires a NORMAL binding, and keeps its existing saved-row
suppression. This is the typed part of the same saved-summary composition
family, not another DATA demand or a report callback. They are not encoded
as ordinary DATA or discarded just because `ExactScopedResults` also stores
DATA images.

The result signature retains the consumer scope, complete parent original,
layer, tail, fields, E/mx, marks and protection. ND Target candidates use
the selected per-member guidance view in this pure query; actual Target
replay still requires its complete join. A query match emits nothing.

`Facts.equals` intentionally ignores protection. Use an explicit annotated
signature after existing exact geometry/annotation union:

```kotlin
data class ObservedMember(
    val scope: BlockScope,
    val original: PremiseKey,
    val port: PortId,
    val pattern: Pattern,  // Includes base, path, tail, mark/mx and E.
    val layer: Layer,
    val nonSubsumable: Boolean,
)
```

Serialize each surviving membership and its clipped protection bit.
Typed results use their existing endpoint/report key. Do not compare two
Sets of ordinary Facts and assume that their annotations are equal.
Do not compare diagnostic callback counts. A cut must preserve each image, not only the fact that at least one family is nonempty.

### 8.3 Implementable reference projection

Use the constructive shortest-safe-prefix reference as the first
implementation. This avoids inventing an unproved AL preimage algorithm.

```kotlin
fun restrictScalar(ctx: LoopGateContext, raw: ScopedEdge): ScopedEdge? {
    val baseline = observe(ctx, raw) // Compute once in this invocation.
    if (baseline.empty) return null
    for (budget in 1 until countedDepth(raw.value)) {
        val candidate = limitOnly(raw, budget) // Existing ops.limit.
        if (observe(ctx, candidate) == baseline) return candidate
    }
    return raw // No shorter image preserves every selected observation.
}
```

`limitOnly` uses `ops.limit`, not `RunMethodAnalyzer.cut`: no instruction
hook, source permission, request or publication runs. The original,
control port and parent link remain fixed. A positive proper-prefix cut
becomes MAY/DEMAND, clears E on the cut, and uses existing protection
transport. Uncut data keeps its original annotations. Static anchors
remain indivisible under the existing AP limit law.

Split a packed value into annotated scalar memberships before differing
cuts, then merge by the existing exact annotation-aware union:

```kotlin
fun annotatedScalars(packet: Facts): Sequence<Facts> = sequence {
    if (packet is Reach) { yield(packet); return@sequence }
    for (leaf in ops.leaves(packet)) {
        val plain = ap.factsOf(leaf.fact, leaf.exclusion, packet.layer)
        val scalar = if (packet is TaintTree && plain is TaintTree)
            plain.withProtection(packet.nonSubsumable, ap.cancellation)
        else plain
        yield(scalar)
    }
}
```

`withProtection` already intersects the supplied mask with this scalar's
exact surviving coordinates and marks. The observer therefore sees the
annotation before selection. `ops.limit` then uses its existing
`transportProtection` implementation for a selected prefix cut. Do not
strip the bit before observing, or flag all siblings because one is
protected.

Equality of the complete frozen observation is the conservative reference
condition. A trie/pullback optimization can replace the trial loop only
with the same preservation proof. Do not add that second algorithm in
this iteration. All trials use query-local scratch. There is no global
NORMAL query graph, rejected-input history or retained raw-output cache.

For scalar depth d, there are at most d-1 proper positive trials, plus
one raw observation. If only raw preserves the required images, keep it.
This design does not promise a constant-depth bound for every legal fact.
Measure observer cost and the fraction of raw fallbacks explicitly.

## 9. Output admission and effect channels

```kotlin
fun onLoopOutput(ctx: LoopGateContext, row: AppliedBlockRow, F: ScopedEdge) {
    val kept = when {
        config.run1 -> listOf(F)
        row.hasNonGrowingArm -> listOf(F)
        else -> restrictAnnotatedOutputs(ctx, row, F)
    }
    for (edge in kept) {
        val fresh = ctx.parent.edges.add(ctx.actualOutputPoint, edge.original, edge.value) ?: continue
        routeActualPort(ctx.actualPort, edge.original, fresh)
    }
}
```

Invoke this handler separately for each stored output geometry from the
row. Do not let a short path bypass restriction for a different growing
path in the same packed publication.

For ND metadata, evaluate every arm and union its permitted images. The
shortcut above means "a real bounded arm retains this full result"; it
must not mean "one growing arm forces all other arms to drop". Both
repeat and leave use this output path. It runs when that loop traversal
ends, not on an ordinary instruction or child completion inside the loop.
No consumer check changes the actual destination.

All source/sink/static effects already executed at original physical
points remain executed. Existing nonreturning sink Target delivery does
not wait for a loop leave. Publish a block-local terminal or run-1 static
shortcut at the nearest boundary. Lift that admitted summary through its
valid parent composition links. Do not publish directly at the original
method level. The original method exit rules run once at their actual
physical point; an ordinary internal block exit does not execute those
rules. A shortcut is not a normal CFG return from the loop.

Internal static-premise summary application uses the selected existing
run-1 static policy, including ZERO satisfaction only on run-1. The global
pool does not get synthetic call subscriptions for block boundaries.
Only original static-read micro-edges register read interests, and only
original write micro-edges register write points. Derived supplied values
retain the current publication rules. Keep disabled-static measurement
mode effective inside all blocks.

The run-2 reverse of a run-1 write shortcut must also keep its paired
publication permission. For example, a stored local writer with producer
`(entry=p, ZERO -> C.f.[any]/T, exit=ROOT_EXIT)` supplies the reverse pair
`(entry=ROOT_EXIT, C.f.[any]/T -> ZERO, exit=p)`. A run-2 static initial
which actually reaches this block through the CFG can reach its source
and produce `C.f.[any]/T -> DemandTarget`. Its Target check must consult
that exact registered shortcut pair at output `p`, even though its live
DATA ingress is a physical port. Use the existing lazy W/B lookup and
paired restriction for this check. Require run-2 backward mode, a concrete
STATIC original, a registered W derivation with a ZERO origin, and the
exact output port. Shared carry alone grants no such permission. This
result check changes no C2 lookup, DATA/native port, ordinary AP
publication, live scope or Target handoff address. Do not alias arbitrary
normal-entry DATA demand into the physical invocation.

Block publication follows:

```text
completed local edge
    -> existing summary normalization
    -> local complete paired C5, unless existing first-run policy
    -> addAdmitted in that scope/exit store
    -> queue fresh local delivery
    -> root only: existing external publication
```

This is the AP publication path. Typed Target publication retains its
existing separate rules: NormalTarget has its NORMAL-only/saved-row checks,
and DemandTarget has its paired control check.

The loop projection is not C5 permission. A NORMAL result can be kept only
with its original exact evidence; a lossy projection cannot create it.

### 9.1 Actual port restoration and method metadata

Use the same context output adapter for actual delivery and pure
AL-to-B observation:

```kotlin
fun outputPort(actual: PortId, current: BlockId): PortId =
    layout.normalExitsForRoute(actual)
        .filter { normal ->
            val adjacent = layout[normal.loop].parent?.let { layout[it].after }
            layout.isAncestor(normal.loop, current) ||
                adjacent?.let { layout.isAncestor(it, current) } == true
        }
        .maxByOrNull { layout[it.loop].depth }?.id ?: actual

fun enclosingPorts(exit: PortId, current: BlockId): List<PortId> =
    if (exit.ordinal < 0) listOf(exit)
    else deliveryRoutes(exit).map { outputPort(it.port, current) }.distinct()
```

The reverse exit from AL uses the same J as the forward L-to-AL entry.
Do not require AL to be inside L; AL is its sibling. Otherwise real reverse
AL rows miss the previous iteration's canonical paired demand.

A child inner-J record can complete an empty AL and then the enclosing
repeat. The observer includes that empty AL when the actual edge either
leaves the parent region or is the parent's repeat. The enclosing header
can lie inside the parent region. Map that J to the actual enclosing feedback outputs before paired
B C5. Otherwise the observer rejects a result which the live parent can
use. Empty-AL delivery must complete that parent traversal, not re-enter
its header before the parent gate.

Local actual end rules run before parent binding. The DATA-only G2 and
entry-mark metadata instead use the complete original method premise:

```kotlin
// The real no-loop/root rule handler already has the original callback parts.
finishMethodData(ops, mode, original, value, exit, actualParts = triggers.parts)

// A bound local span has already run the real rules. Apply metadata only.
root.finishBoundMethodBoundary(methodOriginal, actualEnd, boundValue, summary)

// The pure root observer uses the same ordered DATA-only operation.
root.adjustObservedMethodExit(methodOriginal, observedValue)
```

For deferred/query use, select the same positive CM parts from the original
concrete value, in the original sink/literal order. Then subtract them in
that order and apply entry-mark removal. Do not union the parts, recompute
them after subtraction, run actions or joins, or emit source/report events.
The `original.isZero` test uses the restored method origin, not a local
canonical initial. Observe existing killed-static-write candidates before
these metadata removals.

Run-1 static shortcuts use the existing real normal-exit operation through
its owning AL subtree. `ROOT_EXIT` is its operation-local continuation
address, not a method-entry seed:

```kotlin
// A raw write has not executed the real exit-rule handler.
state.retainBlockSummary(PortId.STATIC_SHORTCUT, original, suppliedStaticValue)

// Preserve that typed output through each ancestor. At the original root:
when (exit) {
    PortId.STATIC_SHORTCUT -> routeStaticBoundaryInput(parent, original, value)
    PortId.ROOT_EXIT -> root.finishBoundMethodBoundary(original, actualEnd, value, true)
}

// At the real exit's owning leaf, reuse the existing operation resume.
state.installPoint(canonicalStaticInitial, actualStaticValue,
    ResumeSite.BoundaryInput(state.operation(actualNormalExit), atStart = false))
```

The completed output port `ROOT_EXIT` certifies that real exit rules already
ran. This applies both to an ordinary AL/J result and to the private static
operation continuation. Root finalization applies metadata only, for every
base. Do not classify a completed output from its input scope or from its
STATIC base; that would execute the ordinary AL/J exit rules again.

`STATIC_SHORTCUT` is a separate internal output port (`-5`). Only this raw
channel can enter the real exit handler. Its run-1 STATIC rows are DEMAND,
so there is no NORMAL native record for this raw channel. Scoped handoff
reverses its exact output into the raw W/completion entry `-5`. It creates
no real CFG entry, C2 alias, or new seed. The existing narrow run-2 backward
STATIC Target check reads that raw paired completion, with the actual
physical output unchanged. Public method addresses and genuine AL/J
normal-exit rows keep `ROOT_EXIT`.

A real static point mark
request also follows matching installed identity links to the outer input
through `StaticBoundaryInputRequests`. Reuse `LocalStaticInputRequests` to
materialize that original input. An outer `C.f/T -> C.g/T` reply keeps C.f
on its outer link, then supplies canonical C.g/T through the inner identity
continuations. This preserves `C.f/T -> ret/U` without a static entry seed,
a new pool producer, or method exit rule evaluation at a virtual L exit.

The operation-only `ROOT_EXIT` row is not a whole AL record. Do not alias
its paired permission to J. The ordinary AL/J static-condition span uses
the existing production rule lowering:

```kotlin
// Existing JIRRuleForms.source / JIRBoundaryForms.exitRules behavior.
MicroEdgeBuilder().apply {
    keepZero()
    keep(STATIC)
    source(exitSource)
    staticOperation(StaticOperation.MarkInput(
        OperationId(form, action = ActionId(occurrence, ActionRole.MARK_INPUT, 0)),
        staticCondition))
}.build()
```

When actual ZERO reaches the real normal exit through AL, that MarkInput
registers the existing static condition point. Its answer produces the
ordinary J-to-normal-exit source row. Run-2 reverses this genuine row and
uses its complete pair at J. The private write continuation keeps its
separate C.f-to-C.g correlation. Native fixtures must include both the
source rule and this existing static metadata, as the real provider does.
No new static subscription policy or whole-AL permission is inferred from
the private operation row.

## 10. Handoff, static completion and release

```kotlin
fun freezeMethod(): FrozenMethod {
    check(allBodyAndLocalQueuesEmpty())
    return FrozenMethod(layout.id, instantiatedScopes.map { scope ->
        FrozenBlock(scope.id, scope.admittedSummaries, scope.targets,
                    scope.sourceHits, scope.staticGuidance)
    })
}

for (method in completedRun.methods) {
    for (block in method.blocks) {
        persistEligibleNormal(block.scope, block.admitted)
        projectSelectedGuidance(block.scope, block.admitted, block.targets)
    }
    aggregateExistingSourcePermissions(method) // Physical identities stay unchanged.
}
```

No unentered block gets new demand merely because it exists in the layout.
Use the existing opposite-direction handoff and normalized endpoint rules.
Keep the existing root `nonZeroInitial` diagnostic meaning; report internal
entry counts separately. Method keys and physical instruction callbacks
remain original.

The method frontier is the union of selected scoped frontiers; only root
rows are public method summaries. Empty-frontier stopping reads that
union. Do not continue merely because a local MAY object exists.

For run-1, preserve the current `RunManager` order: stop/join runners,
complete joined writer guidance while local and external input links are
still available, freeze the completion, then release live block services.
Generalize joined writer binding from a MethodKey owner to an OwnedScope.
For a local writer, borrow its exact waiting block inputs first and bind
up through local parent links. At the root use the existing real-caller
subscriber index. Identity local binding adds no aliases or call stages.
Only this joined read traverses live inputs; no second input history is
created. Keep killed-write candidates in their original block scopes.

Run-1 static completion remains special only at run-1 -> run-2. Its local
query graph now identifies an internal boundary by scoped block ports,
and its external visibility still follows the original method call graph.
Expose the existing shared static-carry guidance through internal scope
views too, using the same static initial grammar. Do not rely only on the
root default when an internal static read needs a run-2 guide. Represent
that carry as a shared view, not one copied relation per register/block.
Identity block links do not bind arguments or add aliases. Fold only
actually admitted block/static rows and the existing lost-write guidance;
do not manufacture an unrestricted Cartesian summary closure. After
run-2, all block C2/C5 lookup is local as specified. The root MethodKey
adapter remains the existing public static-completion interface.

### 10.1 Nearest static publication and existing handoff

Retain an internal run-1 static-to-static row until ordinary parent summary
application has used it. Erase that row only at the public method boundary.
This is the same public static-summary policy with an explicit scope guard:

```kotlin
val erasePublicStaticBridge = isRootScope && erasesRun1StaticSummary(premise, facts)
if (erasePublicStaticBridge) {
    staticGuidanceSeeds.add(premise, facts)
    return
}
// Internal rows continue through the existing local normalization,
// RunSummaryStore admission, publication and BlockSummaryLinks path.
```

Do not erase `C.f -> C.g` inside L before its parent can apply it. That row
can be needed by a later real exit rule on `C.g`. Its run-1 layer remains
DEMAND, including when it carries a full concrete mark. A local summary
application registers no physical read or write point and does not supply
a new mark merely because it crosses a block boundary. Keep the existing
physical operation ownership and computed-supply rules.

The generic scoped handoff already handles these rows. For a genuine
producer key and admitted row:

```text
producer: M, scope=(B, p), exit=q, A -> C DEMAND
next run: M, scope=(B, q), exit=p, demand entry=C, demand exit=A
```

For a static shortcut, `q=ROOT_EXIT` is the existing logical shortcut port.
It does not identify every physical CFG ingress. Use `guidancePattern` and
the existing complete paired C2/C5 rules; do not add an AP matching exception.
`projectBlockHandOff` has no static-to-static exclusion. Normal record
persistence still rejects DEMAND rows, so these run-1 rows are not forced
into native records.

The joined static completion also visits admitted local stores. An internal
static-to-static row becomes a shared B bridge under the original method
owner, and its actual producer ports remain a scoped boundary. Equal bridge
geometry, labels and method owners use the existing deduplication. A public
erased row continues to enter the existing root static-guidance seed store.
No new static closure, method identity or caller history is needed.

The correctness argument uses the existing transfer and handoff laws. The
nearest admitted row is the base case. At each ancestor, a complete ordinary
local binding composes that row with the actual parent original and layer.
Induction gives the same valid dependency at every reached ancestor. Before
release, every selected scoped row reverses both ports and both AP endpoints
through the generic handoff above. Public S-S erasure occurs after this local
propagation and retains its existing static bridge seed. This argument does
not grant an unmatched input, a missing ND arm, a normal layer or a new writer.

A native regression must include `C.f -> C.g` in L and a real exit rule that
checks `C.g/T` and assigns U or reports. Check the local and ancestor static
rows, the resulting nonstatic/Target dependency, and the absence of public
S-S rows. Check physical writer registrations separately. A final finding
alone can be insufficient because the global pool can also deliver `C.g/T`
through an independent path.

Freeze normal Targets with their block scope for local replay and retain
the existing root report collection. Ignore backward NormalTargets and
redundant saved ZERO -> NormalTarget replay as now. A previously saved
P -> NormalTarget suppresses only the same scoped row.

Release current link inputs, work queues, edge stores, local services,
point tickets and form references through the normal run lifecycle. Keep
only admitted immutable records, selected guidance and scalar reports.
Do not retain a frozen analyzer just to keep its block directory alive.

## 11. Replaced paths and retained services

```text
Move into BlockRunState:
  method-wide edgeStore, initialStore and one inferred summary collection
  local conjunction/source-predicate joins and scoped initial request state
  pending local Target/summary deliveries and current link memberships

Replace for loop methods:
  whole-CFG successor delivery -> local delivery plus explicit boundary routing
  direct method-field service access -> explicit BlockRuntime service access
  one method-only snapshot -> admitted snapshots for each scoped block

Retain:
  one original method actor and runner reservation
  original forms/alias queries, real CallPlans and external SummaryStorage
  existing AP interners, admission laws, stores and protection transport
  method-owned static service/ticket directory and physical report/source IDs
```

Compatibility root getters can delegate to root state during migration.
They must not keep duplicate flat stores for a loop method. Internal
publication can reuse `PublicationIndex` and existing match/join code on
the owner queue; it does not need a global locked SummaryStorage entry per
block. No generated helper-method or recursive-call mechanism is added.

Original instruction diagnostics still fire for physical operations only.
Child completion and block routing use separate counters. Do not count
those points as unresolved external calls or new source/sink locations.

## 12. Required controls and implementation order

Implement these steps in order. Keep each intermediate test result tied
to its exact runtime revision.

1. Add immutable layout/port construction and its certificate checker.
   Test no loop, self loop, two successive loops, nested loops, a bypass,
   irreducible multi-entry flow, break/return/throw/finally and an empty BL.
2. Add scoped point indexes, stores and saved/demand views. Keep the
   no-loop root on the current path. Test that equal facts under different
   block entries do not merge, and that post-S storage stays at S.
3. Add local links and explicit BlockRuntime service binding. Test saved
   replay with empty current demand, late same-owner summaries, complete
   ND joins, current request deltas and scoped external call resumes.
4. Add the loop-output observer and reference projection. Test both port
   categories, both directions, strict growth, ZERO=0, packed protection,
   FLOW/TAINT, E/mx, MUST native replay and exact no-match dropping. Include T -> U -> T
   across a block boundary and unchanged non-subsumable flag transport.
5. Add the scoped handoff/static/Target adapters. Run the existing AP,
   method-driver and JVM quality suites. Then run the fixed project campaign.

Principal regression cases:

```java
// Shrinking row must bypass the new gate through several iterations.
Node reads(Node x) {
    while (again()) x = x.f;
    return x;
}
// Body row x.f.*/FLOW -> x.*/FLOW; input x.f.f.$/T.
// First repeat x.f.$/T; next repeat x.$/T; real leave then ret.$/T.
```

```java
// Third consumer is required; a void B exit has no local DATA permission.
void internalSink(Node x) {
    while (again()) {
        sourceFF(x); // T at x.f.f.$ only; preserve old x.f.$.
        x = x.f;
        sinkRootT(x);
    }
}
// First result ZERO -> x.f.$/T grows, but L demand admits it.
// Second read reaches x.$/T. Preserve the existing run-3 FULL finding.
```

```java
// Repeat and leave summaries cannot lose their port.
while (true) {
    if (exit()) { c.v = clean(); break; }
    c.v = sourceT(); // Repeat only; must not reach leave without its write.
}
sinkT(c.v);
```

```text
Two-loop source: prefix; loop1; loop2; suffix
Expected tree:   (prefix, loop1, ({}, loop2, suffix))
L1 next query:   AL1/B2 demand and saved AL1/B2 rows
L2 B query:      B2 demand after AL2 composition
Backward:       same physical hierarchy and reversed ports
```

For each control, assert final reports/Targets as well as selected
initials, paired summary rows and port-tagged stored outputs. Include a static write in L1 and a static sink in L2, with L2 inside
AL1. Assert the required scoped carry/composition guidance at run-1 ->
run-2 and the later finding. A positive
local observer test alone is not an end-to-end finding test.

## 13. Post-implementation measurements and acceptance

Use the projects, memory limit, timeout, field schedule and direct Gradle
task selected in task.md. Do not add another project configuration or
loop policy experiment in this change. Clean earlier captures as required
by that task. Use the latest runtime commit, not this documentation SHA.

For OWASP, Conductor, Stirling-PDF and Thingsboard record:

```text
latest reached / complete / accepted run; engine and barrier times
findings against the immediate prior runtime and the fixed quality baseline
original method keys; block counts, depth and instantiated entry scopes
per-run retained edges and summaries, split by block kind and layer
raw loop outputs, non-growing bypasses, drops, cuts and raw fallbacks
raw/retained path depth, distinct path images and top physical loop sites
summary-shape growth versus actual growth, including MAY-ancestor bypasses
subsumed/unsubsumed and protected edge counts after run-1 and slow runs
local link/input memberships; actual-call subscriptions and deliveries
saved replay count/time; observer calls/trials/time and scratch peak
method/block outgoing demand, Targets, record counts and stop reason
post-freeze memory, peak RSS, retained link/store/record layout
```

Revisit Conductor run-6 and Stirling run-6/run-8. Determine whether their
binary path families disappear before in-loop call subscription, or move
to observer/replay work. Check deeply nested AL regions for repeated
composition costs. Also inspect Thingsboard run-2; do not attribute its
static-query workload to CFG loops without new evidence.

Acceptance requires no new missed finding relative to the immediate prior
accepted results, and explicit comparison with the fixed baseline. Keep
already reported quality gaps separate from new regressions. Require
empty internal-work barriers, complete block handoff and unchanged no-loop
controls. Do not claim a twofold improvement from the finite eight-to-two
model witness alone. Report actual avoided operations and total time.

## 14. Proof boundary

The checked models cover labelled finite control traces, recursive AL
source order, one method owner, identity register transport, separate
post-S stores, complete ND execution, strict shape classification,
finite concrete C2 cells, existing exceptional backward discovery,
and the conservative observation-preserving
projection. The implementation model composes shape selection, scoped
projection and independent complete-row publication; it also proves that
pending local delivery prevents an idle barrier.

The Kotlin SCC builder, full AP observation adapter and work accounting
must correspond to those models. Their exact validation steps are above
and in the proof dossier. The receipt does not claim that unimplemented
Kotlin code is kernel verified, or that all possible programs terminate.

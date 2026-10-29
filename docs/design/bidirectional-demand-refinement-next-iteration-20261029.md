# Next work: remove repeated summary and fact work

Status: candidate proposal. Do not implement these changes in the current campaign.
The measured runtime is `bb74cef6cf483db167c161020a8a4cca576ca005`.
Use the final [performance report](../reports/bidirectional-demand-refinement-workload-20261029.md)
and its embedded data for the measurements.

All four project runs are closed. All end on TIMEOUT. Latest reached/complete/accepted
reports are OWASP run-12/run-11/run-11, conductor run-6/run-5/run-5, thingsboard
run-2/run-1/run-1, and Stirling-PDF run-6/run-5/run-5. The order below uses the
measured hot work and source-confirmed repeated operations.

## 1. Scope

The intended semantic change is none. Each candidate removes repeated processing
of an exact relation union. Keep the same marks, paths, layers, exclusions,
protected memberships, complete premises, source/sink identities and demand guide.
Keep the current stop policy. Batch-dependent callback diagnostics can change.

Do not change field transfer, rule conditions, source-output reset, static supply,
static reachability or the backward ZERO exception as part of this work.
In particular, do not remove joined writer binding because a write already supplies
the static pool. The two operations have different results.

The three strict Stirling baseline losses remain separate correctness work.
D23 source-output reset and witnessed method-exit location need their own designs.
Changing these contracts can change analyzer or report semantics. Do not hide such
a change inside a batching or index optimization. The report gives the exact sites.

The proofs below are required implementation gates. This candidate proposal is not
a claim that all concrete engine operators already satisfy the required union laws.
Use the constructive Lean and TDD workflow in [the proof guide](../../spec/proof-guide.md)
before implementation. A finite packet-union proof alone does not prove call or rule
schedule equivalence.

## 2. Expected impact order

| Order | Candidate | Main target | Current evidence | Expected effect |
|---|---|---|---|---|
| 1 | Select relevant static-demand labels before owner checks | thingsboard run-2 | 412.7 million fixed-filter rejection calls and 603.4 million owner evaluations | Skip colored rows in FLOW-only queries; use exact mark and geometry selectors |
| 2 | Compute frozen owner visibility once | thingsboard run-2 | Call-graph reachability contains 47.68% of whole-run Java samples and 50.94% of sampled allocation weight | Replace per-query graph traversal and memo arrays with one immutable family-reachability index |
| 3 | Keep proved protection containment through exact unions | OWASP run-12 and Stirling run-6 | Protection contains about 55% of whole-run Java samples; Stirling mask intersection contains 28.35% of late native samples | Remove full validation walks when union already proves mask containment |
| 4 | Share joined writer input selection | thingsboard run-1 completion | 230.023 s joined phase; 222,495,546 candidate input visits | Select and match once for several writer outputs with one owner/original |
| 5 | Merge pending summary replay inputs | thingsboard run-1 engine | Immediate replay contains 26.38% of the normal CPU samples | Scan existing summaries and apply them once to a compatible input union |
| 6 | Merge fresh summary publications | conductor run-4 | Delivery contains 65.24% of the middle-window samples | Match and resume each subscriber once for a compatible conclusion union |
| 7 | Merge pending changed method facts | OWASP later runs | Run-12 taint admission 34.64%; GC workers 52.75% | Process a compatible pending tree once after a fan-in |
| Conditional | Skip certified neutral instruction chains | Stirling-PDF run-5 | Unchanged routing 33.21%; call detection 27.19%; GC 0.98% | Deliver unchanged data to the next relevant operation |

The CPU shares are inclusive and overlap. A 30-second window is not a complete-run
CPU distribution. The counts do not give the number of mergeable keys. The project
packing ratios and wall-time gains remain unknown. Do not claim a two-times project
gain from the examples below.

Thingsboard run-1 has 349.927 s of engine work and 230.023 s of joined completion
(224.352 s of writer binding within that phase).
Removing all joined binding would still leave the engine. Thus writer selection
alone cannot halve this complete interval. Writer selection and replay merging
target different parts of that interval.

## 2.1 First target: select static-demand rows

Thingsboard reaches run-2, completes run-1 and accepts the run-1 report. Run-2
ends on timeout after 367.234 seconds. Its late profile contains 41.66% static
completion, 30.08% C5 and 13.99% C2. These shares overlap.

The current FLOW-only path has this order:

```kotlin
for (ordinal in row.labels.indices) {
    val label = row.labels[ordinal]
    val allowed = eligible(row.owners[ordinal])
    if ((!flowOnly || label == FLOW_LABEL) && allowed) yield(decode(label))
}
```

A geometry row has at most one FLOW label. Freeze its ordinal and select it directly:

```kotlin
if (flowOnly) {
    val ordinal = row.flowOrdinal
    if (ordinal >= 0 && eligible(row.owners[ordinal])) yield(decode(FLOW_LABEL))
    return
}
```

For n colored labels plus one FLOW label, owner checks change from n+1 to at most
one. The removed labels could never be returned. Removing their pure reachability
queries must preserve later Boolean answers, even if graph scratch is expanded later.

The [detailed row-selection proposal](bidirectional-static-demand-row-selection-20261029.md)
also specifies exact full-mark adjacency indexes, an early C2 mark test and one
conservative geometry precheck before mapped labels. Keep the complete final AP
predicate. Keep every compatible input/output mark pair, FLOW repair, GROUP
asymmetry, ZERO and exact owner scope. Never replace FULL T with its group or
collapse different FULL marks from the same group.

The whole run-2 JFR window gives a different phase view from the late native window.
C2 contains 58.24% of Java execution samples, call-graph reachability 47.68%, and C5
17.41%. Sampled allocation weight is about 2,006.675 GiB, with 50.94% inside call-graph
reachability. This is an allocation estimate, not retained heap. The late C5 share
must not be applied to the entire run.

The 412.7 million rejections include geometry and image checks. They are not all
mark mismatches. Add a reason split and selected-ordinal counts before claiming the
project reduction. The direct FLOW selector has a source-proved repeated-work case;
the aggregate fraction of this case is not logged.

The per-view owner memo allocates 41,639,806,658 byte payload bytes across 2,536,847
views. This is cumulative traffic, not retained memory. Select relevant rows first.
The measured graph traversal and allocation make a frozen owner-visibility index
a high-priority second stage. Select rows first, then measure the remaining owner
questions. Its bit payload upper bound for the current graph is 106,815,368 bytes
before overhead. It is a finite index for this snapshot, not a growing query cache.

```text
For each call-graph SCC:
  ownFamilies = families that have an owner in this SCC
In reverse topological order:
  visibleFamilies = ownFamilies union each child.visibleFamilies
Query(method, family) = visibleFamilies[SCC(method)].contains(family)
```

This uses the existing common-method call graph. It does not change caller-context
approximation. Keep exact local W/R attachment scope. An outside-graph root gets
only its direct outside-graph owner families, as now. Do not invent outgoing calls
for it. Build once, freeze before concurrent reads, and release with run-2 demand
storage. Prove both directions with executable graph-path witnesses. For this graph,
the edge count bounds the word-OR work by 30,218,317 before SCC construction cost.
Include every frozen owner family: both bridge-label owners and projected-entry
owners. Omitting the second family source would lose C2 entry visibility.
If the selector stage removes this cost, keep the extra index unbuilt; do not add
its memory merely to follow the plan.

## 2.2 Keep proved protection containment through exact unions

Protection stays pointwise and unchanged. This candidate changes how the store
constructs an already-valid value. It must not remove a protected membership.

Current `TaintGroup.add` merges ordinary roots and masks, then can call:

```kotlin
stored.withRoot(mergedRoot).withProtection(mergedMask)
```

`withRoot` intersects the old mask with the new root. `withProtection` intersects
the new mask again. The pointer-equality fast path exists, but a larger merged root
need not have the same pointer as either mask. Both operations can walk the tree.

For an exact-header union, containment is already proved:

```text
oldMask subset oldRoot
newMask subset newRoot
therefore oldMask union newMask subset oldRoot union newRoot
```

This is structural containment of exact path, leaf-kind and mark coordinates.
Use the structural `taintAlg.mergeAdd` union. AP coverage or cross-header
`ConclusionGroup` subsumption does not establish this mask invariant.

Add a narrow union constructor that merges both components and preserves this
proof. Do not add a generic public unchecked mask setter. Keep ordinary validation
for operations that remove or move memberships.

```kotlin
fun mergeSameHeader(a: TaintTree, b: TaintTree): TaintTree {
    require(a.groupKey == b.groupKey)
    val ordinary = mergeOrdinary(a.root, b.root)
    val protection = unionMasks(a.nonSubsumable, b.nonSubsumable)
    return constructContainedUnion(a, ordinary, protection)
}
```

The delta constructor needs its own containment proof. In the current store,
annotation-only updates are included in `deltaRoot` as well as in its mask.
Retain that behavior. Do not use ordinary tree equality to discard an update.

If a store adds one new path to a large protected tree, current validation can
revisit the old protected paths for each addition. The new constructor still merges
the real delta, but does no extra mask/root intersection. A finite test must count
these walks and verify identical ordinary roots, masks, layers and headers.

Stirling's late run-6 profile places 12.85% of samples in a store path through
`withRoot` and 11.52% through `withProtection`. These are nested inclusive shares,
not an additive speedup. The whole OWASP run-12 and Stirling run-6 recordings have
large protection shares. The exact share of removable union validations must still
be measured separately from necessary transfer-mask operations.

## 3. Share joined writer input selection

### 3.1 Current and new work

The current binder processes one scalar writer key at a time:

```kotlin
data class WriterKey(
    val owner: MethodKey,
    val original: InitialAp,
    val output: Pattern,
)

for (writer in pendingWriters) {
    for (input in borrowCandidates(writer.owner, writer.original)) {
        val selected = matches(input, writer.original) ?: continue
        applyWriterOutput(input, selected, writer.output)
    }
}
```

Candidate selection and premise matching do not depend on `output`. Share those
operations for outputs with the same complete owner and original:

```kotlin
data class WriterInputKey(val owner: MethodKey, val original: InitialAp)

// Keep the existing exact per-output admission/deduplication rule.
fun admit(writer: WriterKey) {
    if (!seenWriterOutputs.add(writer)) return
    pending.getOrPut(WriterInputKey(writer.owner, writer.original)) {
        ArrayList()
    }.add(writer.output)
}

fun process(key: WriterInputKey) {
    val outputs = pending.remove(key) ?: return
    // Remove before callbacks. A new recursive output can create another block.
    val visited = HashSet<CompleteInputKey>()
    for (input in borrowCandidates(key.owner, key.original)) {
        cancellation.checkpoint()
        // Keep the existing CallerRef/group/zeroOnly deduplication and ZERO guard.
        if (!visited.add(completeInputKey(input))) continue
        if (!validExistingZeroCell(key.original, input)) continue
        val selected = matches(input, key.original) ?: continue
        for (output in outputs) {
            cancellation.checkpoint()
            // Retain the existing scalar AP application and recursive onBound.
            applyWriterOutput(input, selected, output)
        }
    }
}
```

Do not retain all matched input snapshots in another standing cache. Inputs are
already frozen at this joined phase. Borrow them once for the current output block.
Keep the existing cover/cut/cover sequence, raw mark exclusions until application,
output admission and recursive fixed point. A resulting static original enters B;
it does not enter the writer-binding queue. The guide keeps the existing mark
relation, not a new runtime protection flag. Executable protection stays unchanged.

### 3.2 Why binding remains necessary

```java
// Source rule: sourceT() assigns T at its return.
// Sink rule: sinkT(x) checks T at x.$.
// Exit rule for writeRead(): RemoveAllMarks(C.f).
void main() {
    Box x = sourceT();
    Box r = wrap(x);
    sinkT(r);
}
Box wrap(Box q) {
    return writeRead(q);
}
Box writeRead(Box p) {
    C.f = p;       // Pre-exit W: p.*/FLOW -> C.f.*/FLOW, DEMAND.
                   // Actual p/T supplies C.f/T to the pool immediately.
    Box x = C.f;  // R: C.f.*/FLOW -> x.*/FLOW, DEMAND.
    return x;
}
// The exit rule kills the outgoing W to C.f. The returned R remains.
```

Pool availability activates the read. It does not create the caller-owned writer
pair needed by the run-2 guide. In `wrap`, the lost writer must bind through the
actual call to give `q -> C.f`. The propagated reader is `C.f -> ret`. Their local
composition gives the required `q -> ret` guide. A call graph or pool availability
bit cannot rename the callee formal `p` to the caller formal `q`.

Keep this binding as guidance only. Do not restore the killed executable writer,
add a NORMAL record, or keep only writers that survive the exit. This principal
case is covered by the existing returning-wrapper exit-routing tests.

### 3.3 Work example

```java
void distribute(Box p) {
    C.f0 = p; // p.* / FLOW -> C.f0.* / FLOW, DEMAND
    C.f1 = p; // p.* / FLOW -> C.f1.* / FLOW, DEMAND
    // ... n different static fields ...
}
```

For one complete original and `m` frozen candidate inputs, the current binder does
`n*m` candidate visits and premise tests. A block does `m` visits and tests, then
the same required writer-output applications. With 100 outputs and 100 inputs,
this is 10,000 candidate tests before, 100 after. It does not remove the required
output relations.

### 3.4 Proof and measurement gates

- Prove candidate selection and complete premise matching are output-independent.
- Prove every old scalar output has the same application witness in a block and
  every block result has an old scalar witness. Preserve protection.
- Prove recursive callbacks and repeated/cyclic writers reach the same bounded
  fixed point, including new outputs for a currently detached key.
- Test ZERO and nonzero originals, GROUP/FULL, killed exit writers, wrappers,
  static-to-static bridges and exact global markers. Keep all lost-write tests.
- Measure output keys per owner/original block, candidate visits, tests and actual
  applications. Do not derive this ratio from `writerOffers/admittedWriters`:
  duplicate offers are already removed by the current binder.

## 4. Merge pending summary replay inputs

### 4.1 Current and new work

Current input storage already merges standing values. Each fresh update still
executes a summary replay immediately with production `ProtocolSteps.Inline`.

```text
fresh input
 -> register subscriber and admit current input
 -> scan existing publications for the fresh delta
 -> match, apply, and resume caller
 -> run-1 request matching against the current input
```

For the first implementation, select run-1 summary replay only. Keep registration,
current input admission, ordinary callee initial admission and request matching
immediate. Leave native record replay in later runs unchanged.

```text
fresh input
 -> register subscriber and admit current input, as now
 -> union fresh summary-replay delta in the caller-owned pending store
 -> run-1 request matching immediately, as now

caller fact queue becomes empty
 -> detach pending replay values
 -> replay each compatible union against current summary storage
 -> process any caller facts that these callbacks enqueue
 -> use the existing publication/request/static barriers
```

Do not add a global barrier. The pending key must retain the full callee key,
complete `CallerRef` including call stage and caller context, link layer,
`zeroOnly`, admitted input header and fresh delta header. The two headers can
differ when a fresh tree contains exact leaves only. Do not merge them by base alone.

```kotlin
data class PendingReplayKey(
    val callee: MethodKey,
    val ref: CallerRef,       // Complete caller original, layer, call and stage.
    val linkLayer: Layer,
    val zeroOnly: Boolean,
    val admittedHeader: GroupKey,
    val freshHeader: GroupKey,
)

fun subscribe(sub: Subscription) {
    val admitted = registerAndAdmitAsNow(sub) ?: return
    if (!config.run1) {
        replayAsNow(admitted) // Keep later-run and native replay unchanged.
        return
    }
    matchRun1RequestsAsNow(admitted.current, admitted.growth)
    pendingReplay.addExact(exactReplayKey(admitted), admitted.fresh.added)
    ensureCountedCallerWork(sub.caller)
    // Existing caller code still sends LinkIn immediately after subscribe returns.
}

fun drainReplayAtExistingBarrier(caller: MethodKey, quantum: Int) {
    val batch = pendingReplay.detachForCaller(caller)
    // Detach only this caller's keys. Other actors keep their own barrier.
    for (slot in batch.withinBudget(quantum)) {
        // Pending remainder and delayed test callbacks retain the caller Work.
        replayCurrentSummaries(slot.subscriptionWithMergedFreshFacts)
    }
    pendingReplay.retainUnprocessed(caller, batch)
}
```

These names describe the boundary, not existing API declarations. Expose the
stable admitted header from admission; do not derive it from the fresh header.
Use exact-header `mergeAddDelta(...).first`, including protection OR, for pending
values. Do not substitute cumulative current inputs or use cross-header compaction.
The current ZERO-only admission rule also stays unchanged.

The detailed implementation must preserve `ProtocolSteps` testing hooks, work
quantum remainders and reentrant growth. New input during a detached replay goes
into a new pending delta. The actor cannot return complete while pending or
detached replay remains, or while replay-generated fact/publication work remains.
Keep its Work reservation through callback completion and secured successor work.
No new initial permission comes from a pending packet. LinkIn/C2 operations retain
the same facts and permission, although they can now run before a formerly inline
summary replay. This is a scheduling change that needs a quiescent-equivalence proof.

### 4.2 Work example

```java
// Source rule: sourceT() assigns T exactly at its returned root ($).
Box identity(Box p) { return p; }
// Already published NORMAL FLOW summary: p.*/FLOW -> ret.*/FLOW.

Box caller(boolean b0, boolean b1, boolean b2) {
    Box x = new Box();
    if (b0) x.f0 = sourceT();
    if (b1) x.f1 = sourceT();
    if (b2) x.f2 = sourceT();
    return identity(x); // One call instruction and stage.
}
```

Assume the identity summary is already published when fresh input fragments reach
this call. The unconditional sources have the same caller original ZERO. The
callee input deltas `p.f0.$/T`, `p.f1.$/T` and `p.f2.$/T` have one complete
CallerRef and typed header, but different paths. They can therefore share a pending
key if they arrive before the same barrier.

Current storage admits all three immediately, then scans the existing identity
summaries three times. The pending store retains all three admissions and LinkIn
operations, then scans those summaries once for their fresh union. It keeps the
same returned paths. If each delta has a different original, context or stage,
or reaches a different barrier, this example gives no merge.

A read of `p.left` versus `p.right` from one uniformly tainted source is not this
example: both reads can produce the same root fact at the actual argument and
already be deduplicated before replay. Distinct fresh memberships are required.

### 4.3 Proof and measurement gates

- Exact-key union must preserve ordinary relation memberships and OR the pointwise
  `nonSubsumable` mask. Never use `Facts.equals` to drop annotation-only updates.
- Prove publication-first, input-first and concurrent publication/input arrival
  completeness. Registration and the current input index must precede delay.
- Prove request-first/input-first completeness with immediate request joins and
  the existing later request notification. Do not delay request delivery silently.
- Prove detached and pending replays retain Work reservations, including delayed
  hooks, exceptions, cancellation and freeze. Queue-empty alone must not close the run.
- Prove same-key union has the same final rule bindings, source/sink identities,
  call results, aliases and protection. Keep whole ND premise sets intact.
- Count replay deltas, distinct pending keys, union hits, replayed summary candidates
  and caller continuations. Current accepted-input/group counts do not measure
  per-barrier mergeability.

## 5. Merge fresh summary publications

The method queue-empty publication barrier already exists. Do not change it.
`PublicationIndex.addAll` admits fragments in order and removes fragments covered
by late FLOW. It returns separate fresh values for notification.

Add exact-key union only after those operations:

```kotlin
data class PublicationKey(val premise: PremiseKey, val header: GroupKey)

fun packFresh(current: List<Publication>): List<Publication> {
    val packed = LinkedHashMap<PublicationKey, Facts>()
    for (pub in current) {
        cancellation.checkpoint()
        val key = PublicationKey(pub.premise, pub.conclusion.groupKey)
        val old = packed[key]
        packed[key] = if (old == null) pub.conclusion
            else ap.mergeAddDelta(old, pub.conclusion).first
    }
    return Collections.unmodifiableList(
        packed.map { (key, value) -> Publication(key.premise, value) })
}
```

Use the complete canonical premise, including all ND members. `GroupKey` fixes
kind, layer, base, field exclusion, mark exclusion and tail. Union protection
point by point. Do not use cross-header `ConclusionGroup` compaction here.

Keep current authoritative admission order. Do not first replace the method's
pending array with a map: that would move union before T2 and late-FLOW admission.
The final packet map can still reorder notification `A1,B1,A2` to `A1 union A2,B1`.
Its downstream schedule proof remains necessary.

```java
// Backward initial: ZERO.
void scan(Box p) {
    sinkT(p.f0); // ZERO -> p.f0.$/T, NORMAL
    sinkT(p.f1); // ZERO -> p.f1.$/T, NORMAL
    // ... 100 fields ...
}
```

At one flush, 100 same-header publications become one packed publication. For
`m` eligible caller references, this changes 100m matches and continuations to m.
It still carries all 100 marked paths. Backward `zeroOnly` application forwards
the packed conclusion; it does not execute 100 compiled mark transfers today.
For an ordinary summary with one output mark, packing also permits one input
selection/compiled transfer before the output graft.

Required gates:

- Constructive relation-union and protection-union proofs with original-fragment
  and output-leaf witnesses in both directions.
- Distribution of plain transfer, field limit, cleaners and pointwise protection.
  Complete saturation proofs for stateful source/sink predicates and ND joins.
- Preserve `summaryParts` identity/effect splitting and the input-alias-closure
  invariant. A mixed packet is not uniformly an identity or an effect.
- Preserve publication/input arrival orders, current-state replay, publisher failure
  handling, cancellation, Work reservations and the backward ZERO exception.
- Preserve final demand-presence decisions and selected frontiers. Callback counts
  may decrease; the stop policy does not change.
- Measure normalized fresh fragments versus exact packed keys, mark/path width,
  callbacks and continuations. Include an all-distinct-key overhead control.

## 6. Merge pending changed method facts

Later runs queue each fresh `EdgeDelta` separately. An `EdgeDelta` can already
contain many paths; it is not necessarily one scalar leaf. `MethodEdgeStore`
merges cumulative state but does not unite separate pending work values.
Run-1 FULL diagonal batching is a different operation and does not pack
ZERO-premise marked trees.

For the first scope, keep run-1 batching unchanged. Add a later-run pending map
for the changed data lane after current store admission:

```kotlin
data class PendingKey(
    val node: CommonInst,
    val premise: PremiseKey,
    val header: GroupKey,
)

fun addChanged(delta: EdgeDelta) {
    if (delta.facts is Reach) return addOriginalControl(delta)
    val key = PendingKey(delta.node, delta.premise, delta.facts.groupKey)
    pending[key]?.let { old ->
        old.facts = ap.mergeAddDelta(old.facts, delta.facts).first
        return
    }
    queueNewSlot(key, delta.facts)
}
```

Remove a slot from the map before processing its immutable value. New recursive
work can then create another slot. Keep ZERO control, unchanged lanes, their repeat
gate and the existing phase/priority policy unchanged. ZERO-to-marked is data,
not ZERO control. Keep original admission-based counters before pending union.

```java
Box left(Box p) { return p.left; }
Box right(Box p) { return p.right; }
void consume(Box p) {
    Box x = p;
    while (more()) x = choose() ? left(x) : right(x);
    sinkT(x); // Backward seed: ZERO -> x.$/T.
}
```

At a join, `ZERO -> x.left.w.$/T` and `ZERO -> x.right.w.$/T` can coexist.
Current code processes two fresh packets through the next operations. A pending
tree processes their exact union once. This is a mechanism example, not a claim
that these are the unrecorded paths in OWASP.

This does not remove legitimate path words. A depth-first chain can leave no
coexisting packets to merge. A later leaf enumerator can still visit every word.
The unchanged immediate store admissions also remain. Do not present this change
as a proof of convergence or polynomial path work.

Prove exact union, protection upgrades, operator distribution, complete nonlinear
rule bindings, call/alias behavior, fair queue coverage, reservations and unchanged
stop decisions. Test multiple quanta and delivery orders. Measure offered packets,
pending-key hits, processed packets and output work by ZERO/nonzero and FLOW/TAINT.

## 7. Later native replay candidate

`Record.forEachReversedAt` enumerates all output leaves before filtering by the
provided path. A later change can use the output trie to select nearby leaves first.
Conductor's late run-6 profile contains 11.44% native replay and 4.21% reversed-leaf
work. This is relevant, but the measured window does not support a two-times
project gain from this candidate alone.

The proof must cover the whole packed input, not one candidate leaf in isolation.
Preserve productive EXACT, STAR/E, MUST, transient MUST-to-ANY/DEMAND, ZERO and
protected reverse views. An old view omitted for one input leaf can still apply
to another leaf in the same input packet. Every productive old witness must be
selected by some actual input leaf and the existing output index.

Keep native record-slot consolidation separate. Current records can retain old
delta fragments. Replacing them with the current cumulative store needs a reverse
application theorem for T2 exclusion reduction and superseded headers. Do not drop
historical normal effects merely because the current forward store has a cover.

## 7.1 Conditional Stirling target: skip neutral instruction chains

Stirling completes run-5 and reaches run-6. Its 30-second run-5 profile has 3,056
weighted samples. `emitUnchanged` contains 33.21%, successor routing 29.71%,
call detection 27.19%, and unchanged repeat admission 13.09%. GC workers account
for 0.98%. These shares overlap. This window does not show ND products, cleaners,
C5 or GC as the main cause.

The unchanged path already avoids a changed transfer and repeated store admission.
It still visits each instruction. Changed-work packet merging does not remove these
unchanged hops.

```java
Box x = sourceT(); // ZERO -> x.$/T.
int a0 = 0;
int a1 = 1;
// ... 100 local operations that do not read or write x ...
sinkT(x);         // Same ZERO -> x.$/T.
```

A first safe design builds a route through a certified linear noncall CFG region,
then delivers the same immutable fact to its next relevant boundary. Stop at calls,
field writes, aliases, rule observations, branches, joins and exits. Reuse the plain
form certificate and add a complete untouched-base check. Do not infer neutrality
from a local-variable name or liveness alone.

For k compatible traversals of n certified instructions, current work has k*n
instruction visits. New work has one route construction plus k boundary deliveries.
The route is method/direction owned and must use the actual selected forms. It is
not an IR storage rewrite.

Keep ZERO control and its phase unchanged. Preserve the unchanged repeat gate,
pointwise protection and original exit/summary handlers. A route with no boundary
needs an executable closed-neutral-cycle or dead-end witness. Prove path simulation
in both directions, no omitted observation, no invented normal return and fair work
reservations before implementation. Measure actual certified region lengths and
traffic first. The current profile does not prove this project's packing or jump ratio.

## 8. Acceptance

First discharge the selected candidate's proof and finite differential tests.
Then use the same fixed four-project controls as the current campaign. Report:

- The runtime source and exact inputs; latest reached, complete and accepted run.
- Engine, joined completion and report barrier time separately.
- Required relation and protected-membership equality on finite references.
- Exact baseline source/sink locations, all missing locations and extra identities.
- Component operation counts, packet ratios, whole-run time, GC and memory.

Do not infer project savings from a toy's 100-to-1 work ratio. Select the next
implementation only after its proof boundary and measured repeat opportunity are clear.

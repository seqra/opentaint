# Next work: remove repeated summary and fact work

Status: candidate proposal. Do not implement these changes in the current campaign.
The measured runtime is `bb74cef6cf483db167c161020a8a4cca576ca005`.
Use the final [performance report](../reports/bidirectional-demand-refinement-workload-20261029.md)
and its embedded data for the measurements.

All four project runs are closed. All end on TIMEOUT. Latest reached/complete/accepted
reports are OWASP run-12/run-11/run-11, conductor run-6/run-5/run-5, thingsboard
run-2/run-1/run-1, and Stirling-PDF run-6/run-5/run-5. The order below uses the
measured hot work and source-confirmed repeated operations.

**New decision after the report:** fix the stopping criterion. OWASP must stop
after its complete run-5, which has no selected outgoing demand. Run-5 then
becomes the reached, complete and accepted forward iteration. This is the
proposed result, not a new measured run. The historical report remains unchanged.

## 1. Scope

There is one selected major semantic change: the driver uses the final outgoing
refinement demand to decide whether another backward/forward pair is needed.
It does not use the count of DEMAND work observed during the completed run.
This can change the last iteration and the accepted report. It does not confirm
an unresolved candidate or claim that a later run could produce no facts.

All other candidates remove repeated processing of an exact relation union.
Keep the same marks, paths, layers, exclusions, protected memberships, complete
premises, source/sink identities and demand guide within each executed run.
Batch-dependent callback diagnostics can change. Those optimizations must
preserve the new outgoing-demand stop decision.

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
| 1 | Stop when outgoing refinement demand is empty | OWASP run-5 | Selected outgoing demand is zero in run-5, run-7, run-9 and run-11 | Accept run-5 and do not start run-6 or any later run |
| 2 | Select relevant static-demand labels before owner checks | thingsboard run-2 | 412.7 million fixed-filter rejection calls and 603.4 million owner evaluations | Skip colored rows in FLOW-only queries; use exact mark and geometry selectors |
| 3 | Compute frozen owner visibility once | thingsboard run-2 | Call-graph reachability contains 47.68% of whole-run Java samples and 50.94% of sampled allocation weight | Replace per-query graph traversal and memo arrays with one immutable family-reachability index |
| 4 | Keep proved protection containment through exact unions | OWASP run-12 and Stirling run-6 | Protection contains about 55% of whole-run Java samples; Stirling mask intersection contains 28.35% of late native samples | Remove full validation walks when union already proves mask containment |
| 5 | Share joined writer input selection | thingsboard run-1 completion | 230.023 s joined phase; 222,495,546 candidate input visits | Select and match once for several writer outputs with one owner/original |
| 6 | Merge pending summary replay inputs | thingsboard run-1 engine | Immediate replay contains 26.38% of the normal CPU samples | Scan existing summaries and apply them once to a compatible input union |
| 7 | Merge fresh summary publications | conductor run-4 | Delivery contains 65.24% of the middle-window samples | Match and resume each subscriber once for a compatible conclusion union |
| 8 | Merge pending changed method facts | OWASP later runs | Run-12 taint admission 34.64%; GC workers 52.75% | Process a compatible pending tree once after a fan-in |
| Stirling design | Cache CFG delivery by instruction and base | Stirling-PDF run-5 | Unchanged routing 33.21%; call detection 27.19%; GC 0.98% | Skip neutral CFG traversal; retain post-statement fact admission |

The CPU shares are inclusive and overlap. A 30-second window is not a complete-run
CPU distribution. The counts do not give the number of mergeable keys. The project
packing ratios and wall-time gains remain unknown. Do not claim a two-times project
gain from the examples below.

Thingsboard run-1 has 349.927 s of engine work and 230.023 s of joined completion
(224.352 s of writer binding within that phase).
Removing all joined binding would still leave the engine. Thus writer selection
alone cannot halve this complete interval. Writer selection and replay merging
target different parts of that interval.

## 2.1 First target: stop on empty outgoing refinement demand

### Current versus new behavior

The measured driver stops a restricted forward run only when the report has no
DEMAND candidate, its observed DEMAND counter is zero, or the policy stops it.
The observed counter includes incoming DEMAND before C2, internal deltas and
raw summary deltas before C5. It can remain positive after all selected outgoing
demand has disappeared.

```text
Current, OWASP run-5:
    outgoing demand = 0
    observed DEMAND counter > 0; unresolved candidates remain
    -> start backward run-6

New, OWASP run-5:
    complete forward run; final outgoing demand = 0
    -> accept the run-5 report and end with NO_DEMAND_EDGE
    -> do not start run-6
```

Replace the observed-counter condition. Do not leave it as a second stop rule
that can stop a run with nonempty selected outgoing demand.

```kotlin
// IterationDriver.barrier, after the existing complete-run barrier work.
if (forward) report.add(config, result)
shared.records.persist(/* existing native NORMAL summary persistence */)
val handOff = HandOff.of(config, result, report, shared)
val frontier = frontierOf(config, result, handOff, report)
frontierLog += frontier
frontier.log()

if (forward && !report.hasDemandVulnerability())
    return Next.End(RunStatus.COMPLETE, EndReason.STOP_RULE)

if (forward && !config.run1) {
    check(!handOff.demand.hasStaticCompletion)
    check(!handOff.demand.hasSharedStaticCarry)
    if (handOff.demandEdges.isEmpty())
        return Next.End(RunStatus.COMPLETE, EndReason.NO_DEMAND_EDGE)
}

if (forward && !policy.continueAfter(config, result, frontiers))
    return Next.End(RunStatus.COMPLETE, EndReason.POLICY)

return Next.Run(nextConfig(config, handOff))
```

The existing `HandOff.demandEdges` map counts exactly the newly admitted,
normalized explicit demand patterns. Every stored count is positive. Its
emptiness is the stop predicate; no closure or leaf enumeration is needed.
Prove that this map and the outgoing snapshot agree. Count all selected demand
patterns, including selected NORMAL relations such as unresolved ND support.
Do not replace this test with a scan of `Layer.DEMAND` summaries alone.

The scope is complete restricted forward runs: run-3, run-5 and later odd runs.
Keep the run-1 exclusion. Its run-2 handoff can have virtual static completion
and shared static carry that the explicit count does not represent. Backward
runs still proceed to the next forward run. Incomplete runs keep the existing
abnormal-end behavior and the last accepted forward report.

When unresolved candidates remain, the decision is:

| Observed DEMAND counter | Final outgoing demand | New decision after a complete restricted forward run |
|---|---|---|
| Zero | Empty | Stop |
| Positive | Empty | Stop; incoming or discarded work cannot force another run |
| Zero | Nonempty | Continue, subject to the existing policy and budget |
| Positive | Nonempty | Continue, subject to the existing policy and budget |

Keep `demandLayerEdges` as diagnostic data. Do not remove or redefine its
producer counters as part of this change. Log the stop inputs separately:

```text
BIDI_STOP_CHECK run=5 outgoingDemand=0 observedDemandCounter=...
BIDI_ANALYSIS_END run=5 status=COMPLETE reason=NO_DEMAND_EDGE
```

### Report and ZERO behavior

Accept the complete run-5 report as it stands. Keep unresolved entries as
`ReportState.DEMAND`; do not turn them into CONFIRMED or drop them. Persist the
normal summaries and record the final frontier before returning. A seed list
alone does not require another iteration when outgoing refinement demand is
empty. Do not start a new backward ZERO/sink-seed analysis just to regenerate
requirements in that case.

Do not remove the backward ZERO publication exception or change seed handling
inside a run that is executed. The measured run-6 produces 326,227 outgoing
demands despite its empty incoming demand snapshot. Thus empty outgoing forward
demand is not a proof that the next backward run could do no work. The selected
contract ends refinement at that boundary and retains unconfirmed candidates.
It does not promise equality with all reports from hypothetical later runs.

### Expected work removed on OWASP

The first empty outgoing forward frontier is run-5: run-3 still has 85 demand
memberships. The saved engine times for run-1 through run-5 sum to 242.041
seconds; their full iteration times sum to 247.461 seconds. The engines from
run-6 through the interrupted run-12 consume a further 710.440 seconds.

These are sums of the recorded intervals, not a new wall-time measurement.
The expected new terminal labels are run-5/run-5/run-5 instead of the measured
run-12/run-11/run-11. Do not add old prescan or export times to claim a measured
new command duration. Recheck report locations and memory in the next campaign.

This stop removes OWASP's measured later tree-growth workload altogether.
The protection and pending-tree proposals remain useful for projects and
iterations with nonempty outgoing demand; do not use skipped OWASP run-12 as
their next-campaign speedup evidence.

### Required proofs and regression tests

Before implementation, model this driver decision in constructive Lean.
Prove the following contracts and connect them to the production barrier:

- The positive count map is empty exactly when its explicit outgoing snapshot
  has no selected demand. Restricted forward handoffs have no virtual family.
- A complete restricted forward run with empty outgoing demand returns
  `NO_DEMAND_EDGE` and cannot invoke the next engine or the policy callback.
- With nonempty outgoing demand, this stop cannot fire, including when the
  observed counter is zero. Keep the existing policy and report-empty rules.
- The final report is exactly the report accepted at that barrier. DEMAND
  entries keep their state, identities and witnesses. Persistence and the
  frontier finish first. An earlier confirmed entry remains confirmed.
- Run-1, backward runs, cancellation, barrier failure, timeout and OOM retain
  their existing control paths. Do not expose a partial snapshot as empty.

Add a driver regression with the recorded OWASP frontier sequence
`111374, 112217, 85, 200801, 0`. Require engine calls only for run-1 through
run-5, the complete run-5 report, and no invocation of run-6. Add finite code
fixtures with rejected C2 input, a C5-discarded raw summary, an internal demand,
unresolved sink candidates, and nonempty selected outgoing demand.

Review `DemandLinkTest` and other tests that use the observed counter to force
continuation. If their outgoing demand is empty, update the expected stop and
keep the unresolved sink in the accepted report. Do not invent an outgoing
edge to preserve their old iteration count. Keep separate tests for the
backward ZERO mechanism when a backward run is actually started.

The next implementation must update the stop tables and driver examples in
`spec/ap.md`, `spec/analyzer-core.md`, and `spec/implementation-background.md`.
The current definitions there use observed work. This proposal explicitly
replaces that termination contract; it does not claim the old rule already
used the outgoing frontier. The historical performance report describes the
old behavior and remains a valid measurement of that runtime.

## 2.2 Select static-demand rows

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

## 2.3 Keep proved protection containment through exact unions

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
- Preserve selected frontiers and the outgoing-demand stop decision in §2.1.
  Callback counts may decrease; publication packing adds no further stop change.
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
rule bindings, call/alias behavior, fair queue coverage, reservations and preservation
of the outgoing-demand stop decision in §2.1. Test multiple quanta and delivery orders. Measure offered packets,
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

## 7.1 Stirling target: cache CFG delivery by instruction and base

The later [small-demand investigation](../reports/bidirectional-stirling-small-demand-workload-20261029.md)
identifies the owner. Its isolated diagnostic run-5 records 1,581,415,551
processed items in `PipelineProcessor.runPipelineAgainstFiles`, from 147
initials. Of those items, 1,575,082,922 are unchanged. This is 99.961% of all
method `process()` calls in that diagnostic run. The largest spatial packet
tree in that owner has seven logical node occurrences, with no protected
packet. These figures do not bound cumulative stored trees or mark-set width.

The current repeat set clears when unchanged work empties, even if changed
work remains. It clears 6,190,624 times with changed work pending in this
owner. A bounded full-equality probe records 7,751,326 exact revisits across
clears. Its biased sample does not estimate a global duplicate percentage.
The diagnostic run has different frontier counts from the clean campaign;
retain the clean timing below and do not calculate a speedup between them.

The [relevant-input clarification](../reports/bidirectional-relevant-input-dedup-20261030.md)
adds an important limit: relevant transfer outputs are still durably deduplicated.
A repeated unchanged prefix can end at a relevant copy whose outputs are already
stored. The production-actor diamond test confirms two equal relevant-input
evaluations but one admitted returned output. This is not evidence of an open
duplicate-output cycle. The existing counters do not identify the producer of
every repeated prefix or prove that most unchanged work is removable. The design
below skips neutral traversal for required new packets too. Its saving does not
require a high global duplicate rate.

**Design decision, 30 October:** remove the unchanged queue and cache the next
relevant instruction indices by start instruction and fact base. After processing
an edge at statement S, admit its result once into the result store for S. Then
deliver the fresh delta through S's CFG successors using the route cache.
The store key is S, not an immediate successor or a farther relevant destination.
Repeated evaluation at a destination remains permitted. Do not add a standing
cache of complete processed inputs in this iteration.

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

Extend the method form with a base relevance query. It uses the selected
direction and rule view, and does not depend on the incoming mark set or path.

```kotlin
fun MethodForms.isBaseRelevant(direction, instruction, base, view): Boolean
```

Non-call relevance uses the instruction's normalized operand/result locations,
including its bound rule locations. Call relevance also includes the static
base. ZERO source/control effects and normal/exceptional boundaries must be
included. The query must cover every effect and observation of the current
interpreter. `StatementSummary.touched` alone is insufficient because the
untouched path can still evaluate sources, conjunctions and static-operation
hooks. Use frontend relevance metadata instead of evaluating mark conditions
or materializing all bound rules for each cache lookup.

Use the existing alias-expanded locations in the selected direction. For
example, a forward write can emit an alias target `c.f` which becomes an input
of its backward form, although `c` is not a literal operand of the original
write. This is an existing transfer effect, not a new alias policy.

The route cache is sparse and owned by a fixed method context, run, direction
and rule view. It holds only instruction indices:

```kotlin
// start is before execution of this instruction.
cache: Map<InstIndex, Map<Base, Set<InstIndex>>>

fun deliverAt(start, premise, facts) {
    val targets = cache.getOrCompute(start, facts.base) {
        val todo = dequeOf(start)
        val visited = mutableSetOf<InstIndex>()
        val result = mutableSetOf<InstIndex>()
        while (todo.isNotEmpty()) {
            cancellation.checkpoint()
            val n = todo.removeFirst()
            if (!visited.add(n)) continue
            if (isRelevantBoundary(n) || forms.isBaseRelevant(direction, n, facts.base, view))
                result += n
            else
                todo.addAll(orientedCfg.successors(n))
        }
        result // Publish only after BFS completes. Empty is a valid cached value.
    }
    for (target in targets)
        worklist.add(EdgeDelta(premise, instruction(target), facts))
    if (targets.isNotEmpty()) requestWork()
    // No destination input-store admission here.
}

// Result storage belongs to the statement which produced the result.
// Called after the current cuts, operation hooks and exit handling.
fun admitOutputsAfter(processed, premise, facts) {
    val fresh = edges.add(processed, premise, facts) ?: return
    for (next in orientedCfg.successors(processed)) {
        deliverAt(next, premise, fresh)
    }
}
```

This changes the current implementation's store key from the successor to the
producer. Admission occurs once before fan-out; every successor receives the
same fresh delta. Apply the same producer key to scalar and packed output
admission. Preserve the complete premise, layer, exclusions and protection.
Inputs arriving from different producers can reach a common relevant statement
more than once. Its equal outputs are deduplicated in its own result store.

Initial and resumed inputs must not prepopulate this result store before the
statement executes. Keep initial admission in the existing initial-fact store,
and preserve the existing entry/boundary and continuation handlers. In particular,
the current `startAt` write at the entry node must not make an unchanged first
result look already processed. Audit every direct scalar/packed store write and
distinguish an incoming work item from a completed statement result.
This includes statement-input resumes and the run-1 direct-to-normal-exit
delivery: neither may prepopulate the destination's result row. Preserve
immediate static write supply and execute the exit rules before admitting the
completed exit result. Secure one admitted delta's complete fan-out before
yielding or reaching a completion barrier.

Stop BFS at the first relevant node on each path. Traverse branches and joins
without enumerating paths. A local visited set handles neutral cycles. A closed
neutral component or dead end can produce an empty set. Cache only the queried
start's completed result; other visited nodes need not have the same result.

**Required termination detail:** every output of a processed relevant node,
including its forwarded identity, uses the post-statement admission above.
Today `emitUnchanged` bypasses that store. Retaining this bypass while removing
the unchanged repeat set can make an identity loop infinite. For example,
an operand-based relevance check can stop at `while (x != null)`, while its
current statement form forwards the x fact unchanged. Cached routing then
returns to the same branch. The post-statement gate closes that cycle. This
stores the forwarded result under the processed branch statement; it does not
add an input gate at the cached destination. Do not repeat rules, cuts or
transfers while sharing this gate.

Keep the existing ZERO phase, pointwise protection, static direct-to-exit
shortcut, internal call/cleaner continuations and boundary handlers. Route only
completed statement results through the ordinary CFG. Cache computation and
all destination enqueues stay inside the counted owner work reservation.

For k packets sharing a start/base and n neutral instruction visits, current
work can require k*n visits. New work has one CFG search plus k deliveries to
its first relevant destinations. This also helps when all k packets are new.
Measure destination-set width, BFS misses, relevant evaluations, post-statement
admissions, time and retained metadata. No project speedup is measured yet.

Prove constructive path simulation in both directions, no skipped observation,
preserved post-statement output relations and protection, no invented normal
return from a closed component, identity-cycle termination and fair completion.
Test both diamond controls with permitted repeated destination evaluations and
deduplicated producer outputs. Also test first-entry identity propagation,
fan-out from one admitted result, packed/scalar parity, a relevant identity loop,
an empty cached result, backward alias inputs, ZERO/source behavior, late
joins/publications and static exit routing. Implementation remains unchanged;
these proof and test gates precede implementation.

## 8. Acceptance

Implement and test the stopping correction first. On the OWASP sequence above,
require `COMPLETE / NO_DEMAND_EDGE` after run-5 and no later engine start.
Compare its accepted source/sink locations with the required baseline and the
saved run-11 output. Equal finding counts alone do not prove equal identities.
Do not mark an unresolved candidate CONFIRMED to make this check pass.

First discharge the selected candidate's proof and finite differential tests.
Then use the same fixed four-project controls as the current campaign. Report:

- The runtime source and exact inputs; latest reached, complete and accepted run.
- Engine, joined completion and report barrier time separately.
- Required relation and protected-membership equality on finite references.
- Exact baseline source/sink locations, all missing locations and extra identities.
- Component operation counts, packet ratios, whole-run time, GC and memory.

Do not infer project savings from a toy's 100-to-1 work ratio. Select the next
implementation only after its proof boundary and measured repeat opportunity are clear.

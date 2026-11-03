# Implementation proposal: joined state, loop consumers and static guidance

3 November 2026. **Selected for design. Not implemented.**

This is the complete implementation proposal for all three ranked changes in
[the next-iteration proposal](bidirectional-joined-state-and-loop-consumers-next-iteration-20261103.md).
It follows [the implementation guide](../../spec/impl-proposal-guide.md) and
[the proof guide](../../spec/proof-guide.md). It includes the full component
contracts below; the companion design files preserve the source audits and
proof links. No Kotlin change or project experiment is part of this document.

The source reference is `050b83cfb7b2e75856ea113c44d0a2d6b707250d`.
Checkout `b5fbae2400516e90beb9e17aec6a4bb8a2ac3162` has the same runtime.
Its archived forward-ZERO draft is not selected. The secondary
candidate-directed static-pruning proposal is also not selected.

The selected loop-query work also includes the instruction-only dead-local
pre-filter in section D. It drops `tmp` in `while (...) { tmp = x; ... }`
before boundary summary or demand work, when old `tmp` is dead on repeat.

## Selected result and limits

| Change | Current behavior | Required new behavior |
| --- | --- | --- |
| Release closed state at join | Execution and publication indexes remain while static binding builds its output | Capture required exports, move actual input directories, then release execution/current-delivery owners before pruning or binding |
| Prepare and reuse loop queries | Repeat C2 projections and the same C5 input predicate for new outputs and trial prefixes | Reuse ordered C2 answers and checked local C5 entry plans; keep native output restriction and native fallback |
| Drop dead boundary locals within the loop work | Send dead temporaries through summary and consumer processing | Use CFG live-local bit sets to drop their conclusions before summary emission and demand checks |
| Pack static guidance | Retain rich W/R and terminal sets, then build another frozen index | Retain shared geometry and primitive exact labels/owner memberships; create rich rows only for selected query candidates/results |

**Selected major analyzer semantic changes: none.** Required results remain
the same when execution succeeds. Preserve fact grammar, field limits,
exclusions, full/group mark behavior, protection, initial emission, ND
execution, static visibility, source permission, normal/demand layers,
Targets, stopping rules and report identities. Preserve the scoped mark
request correction. Do not change IR storage or the reference manager.

The lifecycle and query metadata belong to their owners. They do not become
fields of semantic AP/rule keys. Do not change equality or hashing of
`Facts`, `InitialAp`, `PremiseKey`, `DemandPattern`, `Record`, `CallerRef`,
`LocalLink`, `MethodKey` or scoped summary keys. Preserve the complete
protection annotation where ordinary `Facts.equals` omits it.

Resource-limited outcomes can improve when work or retention is removed.
The proof target is semantic equality under the component contracts, not
equal OOM/timeout timing, callback counts or JVM allocation. No proof below
establishes a project speedup, a JVM byte saving or global convergence.
Dead local boundary summaries and their internal demand rows can disappear.
For this pre-filter, preservation means observations and live results, not
equality of the deleted internal row inventories. Keep live carried values
on the existing path. No new direct-repeat mechanism is selected.

## Measurement reference

Use [the current report](../reports/bidirectional-loop-blocks-scoped-requests-performance-20261103.md)
and its embedded data. No new measurement is made for this design.

| Project | Latest reached / complete / accepted | Result |
| --- | --- | --- |
| OWASP | run-5 / run-5 / run-5 | Complete; 4,112 exact baseline identities |
| Conductor | run-6 / run-5 / run-5 | Timeout; accepted run-5 has all 7 identities |
| Thingsboard | run-1 / none / none | OOM during joined preparation; no accepted report |
| Stirling-PDF | run-8 / run-7 / run-7 | Timeout; accepted run-7 has all 22 identities from 86ad |

Thingsboard's selected closed-field removal simulation is 4,268,877,960
bytes, or 3.976 GiB. The captured builder retains about 1.37 GB. These are
separate ownership observations, not an additive promised saving.
Conductor run-6 and Stirling run-7 place about 94% and 96% of sampled Java
stacks in loop observation. Native GC has a separate denominator.

## Common pipeline and ownership

Use this order for real complete method runs. The code is proposed internal
pseudocode. Keep the existing generic/synthetic actor path source-compatible;
do not force-cast every `RunActor` to a method analyzer.

```kotlin
val joined = stopAndJoinExistingRunners()
if (!joined || status != COMPLETE) return existingAbortedRunPath()

fun prepareCompletedRun(): RunResult<RunMethodAnalyzer> {
    val preparation = JoinedRunPreparation()
    try {
        assertExistingWorkAndCallbackQuiescence()
        val exports = captureFrozenMethodExports()  // Non-destructive.
        val sources = detachNativeStaticSources() // No prune or row expansion.
        val inputs = if (run1) moveJoinedInputDirectories() else null
        val lease = preparation.seal(sources, inputs)

        releaseClosedExecutionAndCurrentDelivery()
        releaseStoppedRunnerDirectories()

        val completion = if (run1) {
            // Same source order, prune and AP writer binding as before.
            completeJoinedStaticGuidance(lease, PackedGuidanceBuilder(ap, graph))
        } else null

        checkRunStillComplete()
        preparation.closeTemporaryInputsAndReaders()
        // Close drops temporary ownership, not exports' native summary rows
        // or shared AP/static-key directories.
        return completedRunResult(exports, completion)
    } finally {
        preparation.closeAllAcquiredOwnersOnce()
    }
}
return if (run1) withExistingJoinedDeadlineAndMemoryGuard {
    prepareCompletedRun()
} else prepareCompletedRun() // Keep the later-run guard coverage unchanged.
// Existing IterationDriver barrier: persist, hand off, stop and report.
// Existing driver finally: release shared run-1 catalog/key coverage.
```

The existing run-1 joined guard must cover capture, seal, release and static completion.
It does not restart the configured budget. Keep existing terminal-status
selection and the late-callback resource gate. A preparation failure does
not publish summaries, contributors, a partial catalog or a new report.
This proposal does not add a new post-join guard policy to later runs.

Keep the legacy formula `engineTime = runCallElapsed - joinedStaticBindingTime`.
`joinedStaticBindingTime` still covers the whole static completion operation:
prune, writer binding and catalog freeze. Add `joinedSealReleaseTime` as a
separate reported duration; do not subtract it again from the legacy engine
time. Explain moved capture/cleanup work in the report. Whole-iteration time
and the configured deadline remain intact.

| Owner/data | Lifetime in the new pipeline |
| --- | --- |
| Live instruction/rule/delivery state | Until quiescence and exact export/diagnostic capture |
| Owner-quantum C2 scratch/C5 plans | Only inside `MethodBlockRuntime.work`; cleared in `finally`, before seal |
| Actual local and physical inputs | Move without copying; keep until joined binding finishes |
| Native admitted stores, raw Targets, source/sink seeds and contributors | Frozen export; keep until the existing driver consumers finish |
| Raw write candidates/private seeds | Detach before release; current prune/bind reads them afterward |
| Packed frozen catalog | Detached immutable result for the existing run-1 -> run-2 lookup lifetime |
| Shared AP and static-key directories | Keep their existing owner/release point |

The final catalog cannot capture an input lease, actor, runtime, runner,
subscription manager, live port or callback to those owners. Conversely,
the closed execution stores must not remain reachable through a moved
input directory. Keep immutable AP and caller key objects unchanged.

The synthetic `RunResult` fallback is still required by existing tests.
Its raw lost-write APIs remain available. A real early-released run must
provide its completed static result and must not enter that fallback.

## Constructive proof package

| Contract | Checked theorems / audited declarations | Model report |
| --- | --- | --- |
| Lifecycle, exports, exact routing and moved ownership | 87 / 117 | [Joined state](../../spec/lean/proposals/joined-state-release-selected-design-20261103/REPORT.md) |
| Query reuse, prepared entry, annotations and fallback | 71 / 127 | [Loop queries](../../spec/lean/proposals/loop-consumer-query-reuse-20261103/REPORT.md) |
| Packed rows, ordered queries and finite composition | 48 / 84 | [Static catalog](../../spec/lean/proposals/packed-static-guidance-20261103/REPORT.md) |
| Composition of the three contracts | 8 / 12 | [Combined pipeline](../../spec/lean/proposals/joined-state-modular-composition-20261103/REPORT.md) |
| Instruction-only dead-local pre-filter | 42 / 72 | [Boundary live locals](../../spec/lean/proposals/block-boundary-live-locals-20261103/REPORT.md) |

All 256 theorems are constructive. The audits allow only `propext` and
`Quot.sound`; no choice, unproved axiom or native-evaluation proof is used.
The component/source/index adapters and the real quiescence/read-footprint
contracts remain native implementation obligations. These models do not
kernel-verify Kotlin, JVM identity, concurrency, GC or performance.

The [design validation receipt](bidirectional-joined-state-loop-consumers-packed-guidance-validation-20261103.json)
records the five proof receipts, component/source hashes, unchanged runtime
and local-link checks. It records no native test or project experiment.

The combined result uses these exact premises: release preserves the
retained source/export streams; the catalog preserves ordered query answers;
the observer preserves its complete signature for every raw/trial input.
Then the existing adaptive shortest-prefix decision and deterministic
handoff/report projections have the same result. Do not weaken this to a
set of marks, independent entry/exit permission, or an unordered graph.
The extra local-erasure model proves the observation projection for dead
old values and exact route filtering. It does not change the three imported
composition models or prove native Kotlin AP observation equivalence. The
instruction classifier and boundary/observer adapters have explicit native
test gates in section D.

## A. Release closed state at the successful join

Component source: [bidirectional-joined-state-release-design-20261103.md](bidirectional-joined-state-release-design-20261103.md).
Frozen design SHA-256: `4ca9febe1220bdd846c3fc3f3e81d49ac6f21e104e102fd74c2d41b6ac371441`.

### 1. Result and semantic scope

Release closed execution and current-delivery stores **before** run-1 static
binding starts. Keep the exact data that binding and the driver read.

| Part | Current | Selected design |
| --- | --- | --- |
| Instruction transfer and local rule joins | Live stores remain reachable during binding | Capture their required exports, then release them |
| Actual local and physical caller inputs | Binding borrows live owner objects | Move the same input directories to read-only owners |
| Publication and current-delivery indexes | Remain reachable through actors/subscriptions | Release after all events and callbacks have ended |
| Admitted summaries and Target inventories | Read by binding and the driver | Retain the same native data and exact owner/port keys |
| Raw static writes and private seeds | Pruned/read during binding | Detach first; prune after execution release |
| Diagnostics and NORMAL rule contributors | Captured during final actor freeze | Capture before release; publish at the same driver barrier |

There is **no major analyzer semantic change**. Keep initial emission,
field limits, exclusions, mark slots, full mark sets, protection, ND premises,
normal/demand layers, static visibility, source permission, predefined
summaries, Targets, stopping rules, and report identities unchanged. Keep
the scoped physical request fix. Do not add ZERO inheritance, seed replay,
new support metadata, or writer validation. Do not change AP equality,
hashing, canonical IDs, IR storage, or the soft-reference manager.

This is a lifetime change. The read adapters, release order, and cleanup
contract below are part of the design. A proof about a smaller retained
interface does not permit an implementation to discard a later read.

### 2. Evidence and limit of the memory claim

The [current report](../reports/bidirectional-loop-blocks-scoped-requests-performance-20261103.md)
contains the portable heap evidence. Thingsboard finishes engine work in
699.248 s. It fails during static-binding preparation, before recursive
binding starts. The snapshot contains `processedWriters == 0`,
`candidateInputs == 0`, and `boundOutputs == 0`.

MAT parses 15,309,242,544 reachable bytes. Its explicit retained-set removal
simulation for selected execution/current-delivery roots contains
4,268,877,960 bytes, or 3.976 GiB. This is **not an observed release saving**.
The simulation excludes required input directories, admitted summaries,
raw/outgoing Targets, raw writes, private seeds, contributors, `bodyWork`,
and `runContext`. Do not add independent retained subtrees to that union.
The patch must remove the real paths before any saving follows.

Required local-link inputs retain about 773 MB. Public published summaries
retain about 1.18 GB, but `SummaryStorage.visitJoinedInputs` reads only its
subscriber directory and those subscribers' actual input indexes. Removing
the subscriber/input directory would change binding results.

Capture the existing diagnostic snapshots. In particular, do not claim the
597 MB `bodyWork` subtree as free memory: its copied bounded sample records
can remain in snapshots. This design does not reduce diagnostic fidelity.
It also does not promise that binding or run-2 will fit in 16 GiB.

### 3. Exact read audit

All paths are under
`core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/`.
The proof package pins these files at the reference revision.

#### 3.1 Reads during joined static completion

| Existing reader | Exact retained input | Data that it does not need |
| --- | --- | --- |
| `JoinedStaticGuidance.completeJoinedStaticGuidance` state traversal | Ordered `(MethodKey, BlockScope)` owners, admitted root/port stores, outgoing DEMAND Targets, private seed rows, raw candidate inventory | Instruction edge store, initials, worklists, forms, rule/action stores |
| `KilledStaticWriteStore.freeze` | Raw candidate IDs, key interner, `summaries.all()` or all actual port stores, private seed rows | Current publication/delivery indexes |
| `OwnedJoinedStaticWriterBinding` local borrow | Exact child scope, each `LocalLink`, current merged `Facts` | Child completion stores, CFG cache, local publication/Target index, local ND delivery joins |
| `SummaryStorage.visitJoinedInputs` physical borrow | Subscriber order, exact complete callee key, each subscriber's indexed actual inputs | `SummaryStorage.published`, request rows |
| `CalleeSubscriptions.visitJoinedCandidates` | Existing accumulator, callee IDs, path index, `zeroParts`; same matching mode | `SubscriptionPort`, live replay/notification callbacks |
| `FrozenStaticCompletion.Builder` | The same admitted W/R rows, private/lost/bound rows, outgoing Target attachments and control boundaries | Actors, runner ports, contexts or live callback closures |

Only outgoing DEMAND Targets feed static attachment. Keep raw Targets too:
the driver later reads NORMAL Target IDs. These inventories are distinct.
Do not replace both with a single DEMAND-only view.

#### 3.2 Reads after `RunManager.run` returns

| Reader | Retain in the frozen method export |
| --- | --- |
| `IterationDriver.runOnce` diagnostic logs | Steps and scalar counters; neutral-batch counters; CFG/scalar snapshots; block diagnostic text; exact existing `BodyWorkSnapshot` |
| `IterationDriver.barrier` census and native persistence | Root admitted `RunSummaryStore`; actual `ScopedRunSummary` keys and stores |
| `ReportBuilder.prepare` | Root and scoped raw Target inventories, full premises, NORMAL IDs; method key and configured roots |
| `HandOff.toBackward` | Outgoing root/scoped DEMAND Targets, root/scoped outgoing summary view, sink seeds, finished static completion |
| `HandOff.toForward` | Outgoing root/scoped summaries/Targets, backward `SourceHitStore.occurrences()` |
| `frontierOf` | `nonZeroInitial`, edge deltas, record crossings, root/scoped outgoing Target counts |
| Forward FULL contributor publication | Frozen root and child `NormalRuleContributorRow` lists, including protection updates and semantic site keys |

The complete real run always supplies its joined completion. Keep the
synthetic `RunResult` fallback in `HandOff.toBackward` for tests. It reads
private seeds and `freezeStaticWriteCandidates().lostRows()` from synthetic
frozen actors. Do not route a real early-released result through that fallback.
Do not remove its APIs as if they were unused.

### 4. State ownership and phases

```text
LIVE
  -> JOINED       all runner jobs ended; successful COMPLETE; every queue idle
  -> CAPTURED     diagnostics/exports/contributors prepared; exact read lease sealed
  -> RELEASED    execution and current-delivery owners detached
  -> BOUND        run-1 completion prepared under existing deadline/memory guard
  -> RETURNED     frozen result exported; joined input lease released
  -> DRIVER       existing record/report/handoff preparation and commit

Any failure -> no new complete RunResult or contributor/report publication
             -> best-effort release of every acquired owner
```

The driver does not read the joined input lease. It reads the frozen method
exports. Thus the lease can end when binding finishes, before `RunResult`
returns. Keep the native admitted stores in the method export until the
driver has consumed them. Point 3 may keep its detached compact catalog
longer; it must not keep the lease or a callback to an actor.

**Join success is not enough by itself.** Also require:

```kotlin
check(status == COMPLETE)
check(allRunnerJobsJoined)
check(inFlight.pending == 0L)
check(!admitting)
for (method in methods) {
    check(!method.hasLocalWork)
    method.blockRuntime?.requireIdle()
}
// Test protocol steps must also prove that their delayed callbacks drained.
```

Keep all current counted-Work producers. Never replace the idle check with
an all-state scan that silently drains missed work. A failed check fails the
run. It must not drop pending data or manufacture quiescence.

### 5. Concrete detached read APIs

These are proposed internal APIs. They are not present in the reference
runtime. Preserve `RunResult<RunMethodAnalyzer>` and its frozen actor read
surface to avoid a separate driver migration.

```kotlin
interface JoinedBindingLease : AutoCloseable {
    fun sources(): Sequence<JoinedStaticSource>
    fun visitLocalInputs(owner: OwnedScope,
                         visit: (LocalLink, Facts) -> Unit)
    fun visitCallerInputs(method: MethodKey, writer: Publication,
                          mode: ApMode, visit: (Subscription) -> Unit)
}

// A top-level value owner. It is not an inner class of an actor/runtime.
class JoinedStaticSource internal constructor(
    val owner: OwnedScope,
    val admitted: JoinedAdmittedStores, // root or exact port stores
    val outgoingDemandTargets: TargetReadView,
    val privateSeeds: StaticSeedReadView,
    private val rawWrites: KilledStaticWriteStore?,
) {
    fun freezeWrites(): FrozenStaticWrites // unchanged prune algorithm
}

class JoinedLocalInputs internal constructor(/* moved input table */) {
    fun visit(visit: (LocalLink, Facts) -> Unit)
    fun close()
}

class JoinedCallerInputs internal constructor(/* moved byCallee directory */) {
    fun visit(callee: MethodKey, writer: Publication, mode: ApMode,
              visit: (Subscription) -> Unit)
    fun close()
}
```

`JoinedAdmittedStores` holds direct references to the native stores. Its
read methods call the existing `all`, `demandEdges`, and port traversal.
It does not call owner-only `borrow()` from a new thread or retain a closure
over `state`. No mutation is possible after join. Do not clone the relation
into rich row sets to seal it. `RunSummaryStore` is not redesigned here;
the read adapter and method export retain it as a stopped-owner value.

#### 5.1 Local inputs: move the table

Extract the current input map from `BlockSummaryLinks` into one top-level
`LocalInputDirectory`. It must contain only the current `InputKey`,
`LocalLink`, group, and merged immutable `Facts` values. Keep the same
insertion order. The live `offer` method uses that directory. At seal:

```kotlin
fun BlockSummaryLinks.detachJoinedInputs(): JoinedLocalInputs {
    checkNoPendingDeliveries()
    check(phase == LIVE)
    phase = JOINED
    return JoinedLocalInputs(moveInputDirectory()) // old field becomes null
}
```

The returned object must not contain `BlockSummaryLinks`, `Binding`, `Entry`,
`MethodBlockRuntime`, an actor, or any of the three live callbacks. This is
one moved table, not a second standing `Facts` store. Keep complete parent
and child scopes, point, original premise, link layer, and group key.

Move inputs from **every existing `Entry`**, including a saved-only entry
whose `stateOrNull` is null. The current `forEachLocalInput(scope)` can read
such an entry. `states()` lists only instantiated analysis states and is
not a complete input-directory inventory. Source enumeration can keep its
current instantiated-state set; input enumeration must not use that set.

After this move, discard local publication indexes, Target delivery indexes,
delivery queues, `joins`, and `terminalJoins`. Retain actual method/block
summary stores and raw Target rows separately. The two data sets have
different purposes.

#### 5.2 Physical inputs: move the existing index

```kotlin
fun SubscriptionManager.detachJoinedInputs(): JoinedCallerInputs {
    checkJoinedOwner()
    val result = JoinedCallerInputs(moveByCalleeDirectory())
    port = null // removes anonymous SubscriptionPort -> handler -> runner
    return result
}
```

`CalleeSubscriptions` already owns its accumulator and path index without
an actor reference. Keep its existing `visitJoinedCandidates` logic and
candidate order. Preserve `zeroParts`, full callee keys, `CallerRef.scope`,
call/stage, premise, layer, and annotations. Do not recompute subscriptions
from admitted initials or summary premises.

`SummaryStorage` seals its subscriber list to references to the detached
readers. A run-local identity map obtains each reader once when a subscriber
occurs under several callees. Drop the live `published` index and request
rows only after that seal. Do not clear a shared subscriber reader from
one callee while another callee still uses it. Close each moved owner once
in the enclosing lease.

The seal copies only a small directory of owner/reader references. It does
not copy Facts or build a second input path index. Live APIs fail after the
phase changes. `visitJoinedInputs` is available only through the lease.

### 6. Capture and release order

```kotlin
// In RunManager, after the existing successful stopAndJoin.
val preparation = JoinedRunPreparation(config)
try {
    assertCompleteAndIdle()
    val exports = captureFrozenMethodExports() // existing snapshots, no publication
    val sources = detachStaticSources()        // no prune and no W/R expansion
    val local = detachLocalInputDirectories()
    val callers = detachCallerInputDirectories()
    val lease = preparation.seal(sources, local, callers)

    releaseClosedExecutionAndCurrentDelivery() // all owners, before pruning
    releaseJoinedRunnerDirectories()          // no callbacks can now run

    val completion = if (config.run1) {
        withExistingJoinedResourceGuards {
            completeJoinedStaticGuidance(config, shared, lease, checkpoint)
        }
    } else null
    checkRunStillComplete()
    return completeResult(exports, completion) // same frozen actor API
} finally {
    preparation.closeAll() // idempotent; release all owners even if one fails
}
```

The capture call is a new non-destructive phase. Do not implement it by
calling today's `RunMethodAnalyzer.freeze()` before input/source detach:
that method clears child links and the runtime. Split its existing capture
and cleanup work, and preserve the capture order before any clear.

Keep the existing run-1 joined deadline/memory guard active around the
whole capture/seal/release/bind phase, not just `binding.complete()`. The
pseudocode abbreviates that outer guard. The configured time and memory
limits do not restart at release. Snapshot failure or cancellation rejects
the run; cleanup still has no cancellation checkpoints. Keep static-service
statistics available until their existing log, and retain shared run-1
catalog/key coverage until the existing driver handoff release point.

For later complete runs, use the same capture/release path, but no static
input lease is needed. No live protocol store is carried into the next
iteration. The driver keeps its current persistence, handoff, stopping,
report, and contributor-publication sequence.

**Do not call `freezeStaticWriteCandidates()` during capture.** Move its
plain inventory and exact admitted/private source views. The current
`freeze` enumerates normalized survivors. It must run only after release.
Candidate-directed pruning is a separate proposal and is not selected by
this design.

Point 3 builds its detached compact guidance catalog after execution
release, from the same native sources and bound additions. It must not
retain `JoinedStaticSource` in the final completion when the final catalog
is sufficient. This document does not choose a new static lookup algorithm.

#### 6.1 Field and API change plan

| File | Required change |
| --- | --- |
| `BlockSummaryLinks.kt` | Extract/move only current input directory; gate live APIs; release all other indexes after idle |
| `SubscriptionManager.kt`, `CalleeSubscriptions.kt` | Detach `byCallee` with existing indexes; separate live port from joined read owner; retain current visit logic |
| `SummaryStorage.kt` | Seal subscriber readers, then drop `published` and request rows; reject live publish/commit/subscribe/replay reads |
| `MethodBlockRuntime.kt` | Capture scope/port exports, counters, scalar and CFG snapshots; move input directories; release completions/caches/observers/routes/entries |
| `BlockRunState.kt` | Split capture from release; detach raw write source; release local/call/point-resume/worklist/initial/edge/applier/temporary owners |
| `RunMethodAnalyzer.kt` | Capture child exports/contributors before runtime release; retain only frozen result fields; clear static reply directories |
| `RunMethodHandlers.kt`, `UnitRunner.kt` | Detach physical inputs before handler/runner release; make final release safe after partial preparation |
| `JoinedStaticGuidance.kt` | Read `JoinedBindingLease` and exact `JoinedStaticSource`; remove actor traversal and live storage callback |
| `RunManager.kt` | Place capture/seal/release before joined binding; keep existing resource guard and status selection |
| New `JoinedBindingInputs.kt` / `JoinedRunPreparation.kt` | Top-level moved read owners, phase checks, identity-based close-once registry |
| Driver code | Keep the existing result read APIs; add contract tests, not new AP policy |

Use nullable owner fields or replace the owning object when release must
drop a backing array. `worklist.clear()` alone can leave its array capacity;
`Run1PointResume.clear()` alone keeps the object and its maps. Release the
old owning references after their required snapshots. Do not clear mutable
fields inside a `LocalLink`, `CallerRef`, `InitialAp`, `Facts`, or other hash
key. Do not clear shared AP interners or native summary storage.

Remove or replace these post-join paths after their callers migrate:

```text
completeJoinedStaticGuidance(actors, storageCallback)
actor.joinedBlockStates() as a binder dependency
actor.forEachJoinedLocalInput() as a binder dependency
SubscriptionManager.visitJoinedInputs() through a live port-bearing owner
the late-only execution release inside freeze()
```

Keep compatibility adapters only where existing synthetic tests need them.
Do not remove frozen export APIs, `freezeStaticWriteCandidates` fallback,
`RunActor.freeze`, or `SubscriptionHandler.freeze`. The final APIs must be
idempotent for cleanup, without calling `NormalRuleContributors.freezeRows`
twice. A closed actor's live accessors must fail; its frozen read APIs must
continue to work.

### 7. Diagnostics, contributors and failure

Capture root/child counter totals, scalar-store gauges, existing block text,
CFG counts, and the existing root `BodyWorkSnapshot` before releasing their
inputs. Do not initialize an unused lazy CFG cache to get a zero snapshot.
Children share root diagnostics; count the same snapshots once, as today.
Keep bounded sample IDs and immutable numeric/path copies, not Facts,
instruction stores, compiled rules, or owner callbacks.

Freeze root and child NORMAL contributor rows exactly once before local
condition services close. Keep their full premise, Facts annotations, rule
descriptor, semantic site, and owner. Detach the old-view/dedup references.
Do not publish the rows at join. The current successful forward FULL driver
barrier remains the only publisher. A failed binding must leave that
persistent snapshot unchanged.

| Failure point | Required action |
| --- | --- |
| Engine timeout/OOM, successful physical join | No complete export or static binding. Capture only existing aborted diagnostics. Dispose stopped owners and moved pieces. Do not publish contributors |
| Runner join fails | Do not read, move, clear or freeze runner-owned state. Return failure with no stores. Do not claim cleanup while an owner can still mutate |
| Idle precondition fails | Fail with the pending-work diagnostic. Do not release pending state as a valid result |
| Snapshot/seal fails partway | Dispose every acquired piece once; release all stopped owners. Do not bind from a partial lease |
| Binding times out/OOM/fails | Existing guard changes COMPLETE to the terminal status. Discard partial guidance and contributor rows; keep prior accepted report |
| Driver preparation fails | Keep existing abnormal termination behavior and prior report. This design adds no record rollback or new transactional record store |
| Final cleanup throws | Continue other cleanup, preserve the first failure, add distinct suppressed failures; do not reinterpret it as successful completion |

Release cleanup has no cancellation checkpoints. Binding, catalog building,
and existing driver reads keep their checkpoints. A late memory callback
must not invalidate an already closed phase; retain the current resource
gate. Closing the input lease must release all unique owners even if one
owner's close method fails.

### 8. Examples and exact results

```java
void root(Box p) {
    wrap(p);
    consume();
}
void wrap(Box p) { set(p); }
void set(Box p) {
    C.f = p;                // Raw writer p.*/FLOW -> C.f.*/FLOW.
    clearStaticOnExit();    // May remove the admitted static summary.
}
void consume() { sinkT(C.f); }
```

At successful join, keep the actual `root -> wrap -> set` input links and
the raw writer ID. If a loop owns the write, also keep every exact local
parent link. Before and after release, binding reads the same input Facts
and raw writer and emits the same caller-bound guidance. The absent normal
exit summary does not authorize removal of the raw write.

```java
void main() {
    Object x = sourceT();
    sinkT(x);               // ZERO -> NormalTarget(id), raw inventory.
    refineElsewhere();      // Keeps another DEMAND frontier alive.
}
```

Keep `NormalTarget(id)` in the raw inventory for reporting and later native
Target views. Only outgoing DemandTarget enters static attachment and
refinement demand. Releasing the delivery index changes neither inventory.

```java
Object make(Object p, Object q) {
    // Rule: CM(p,T) AND CM(q,U) -> assign V to ret.
    // A prior NORMAL p/T leaf is a saved certificate with its full premise.
    return combine(p, q);
}
```

Capture that leaf before the live condition store closes. Its later reuse
still needs the existing current Holds activation and complete ND binding.
Release does not rewrite its premise to ZERO, run source actions, or grant
source permission.

### 9. Proofs and implementation gates

The selected-design [proof package](../../spec/lean/proposals/joined-state-release-selected-design-20261103/REPORT.md)
extends the prior 35-law conditional model. It has executable phases,
finite pending-work checks, exact scoped local/caller read functions,
ordered finite binding enumeration, complete export preservation, moved
input-directory ownership, failure/cleanup laws, and finite retained-alias
counterexamples. It uses no classical choice or unproved axioms.

Its prerequisites are explicit: Kotlin must implement the sealed read
footprint and existing AP eligibility predicate; the real counted-Work join
must be complete; immutable keys must not change. The model does not verify
Kotlin, concurrent callbacks, JVM identity, garbage collection, bytes freed,
full AP transfer, global convergence, or project quality/performance.

Use the current binder and driver as native reference oracles. Write these
RED controls before the corresponding release patch; then require GREEN:

| Native control | Required assertion |
| --- | --- |
| `JoinedReadFootprintTest` | Close execution accessors before binding; binding and driver still produce exact reference rows, full marks, layers, exclusions, protection, Target IDs and seeds |
| `JoinedInputOwnershipTest` | Move local and physical input tables; same ordered values and canonical key references; no duplicate standing table; recursive callees and same callee across runners remain distinct |
| `JoinedScopePortTest` | Preserve different block/call scopes, canonical normal interfaces, actual ports, STATIC_SHORTCUT versus completed ROOT_EXIT, reverse ports and exceptional ZERO hack |
| `JoinedSourceInventoryTest` | Killed exit write and private S-S seed survive; no prune/row expansion occurs before release; no new pool registration/supply |
| `JoinedDiagnosticsTest` | Exact before/after snapshots and counters; no lazy cache initialization; one root diagnostic owner, same bounded samples |
| `JoinedContributorLifetimeTest` | Prior NORMAL partial certificate, annotation-only protection growth, site/owner isolation and failed-binding nonpublication |
| `JoinedTargetInventoryTest` | Raw NORMAL ID, raw DEMAND and outgoing DEMAND remain distinct; same report/frontier/native Target view |
| `JoinedReleaseProtocolTest` | Existing late static answer, duplicate call suffix, saved Target replay and fresh current offer cannot cross the idle barrier with pending Work |
| `JoinedPartialFailureTest` | Fail each capture/seal/bind/close step; close every acquired owner once, no partial result, old report survives, no release before physical join |
| `JoinedAliasTest` | Detached readers contain no actor/runtime/binding/runner/context/port callback path; shared AP/immutable key references remain valid |

Exercise no-loop methods, empty BL/AL, nested loops, predefined callees,
complete ND callers, backward source hits, and FULL run-1/later runs. Keep
GROUP behavior as before; do not reinterpret GROUP certificates as FULL.
Run the existing common/JVM suites after the focused controls. Native test
execution and project experiments are future work, not receipts for this
design task.

After implementation, repeat only the selected four configurations. Record
heap before/after release and after GC, required input rows, compact-catalog
size, binding candidates/output, engine/binding/barrier times, exact status,
and reached/complete/accepted iterations. Verify baseline finding identities.
Keep GC/RSS/heap/retained-set units separate. A shorter failing run is not
an improvement, and a simulated retained union is not measured reclamation.

## B. Prepare and reuse loop-consumer queries

Component source: [bidirectional-loop-consumer-query-design-20261103.md](bidirectional-loop-consumer-query-design-20261103.md).
Frozen design SHA-256: `26074dd10050f0d846157e92afcfad0d5f8742391c50b1e773054f532bf095c6`.

### Scope

Selected major semantic changes: **none**. Keep the complete loop observation,
restriction choice, native saved application, work accounting and output order.
Change only repeated query work. No ZERO, Target, source permission, layer,
protection, field, C2/C5, mark-owner, report or publication policy changes occur.
Do not change equality/hash fields of Facts, DemandPattern, Record or PremiseKey.
Private plan/key objects carry the new metadata.

Use two mechanisms:

1. Compute each scope's C2 admissions once. Use that ordered result for both
   labelled and unlabelled families. Add a bounded synchronous C2 memo for the
   current method-owner quantum.
2. For a fixed complete original, actual exit, policy and frozen local view,
   check each C5 entry predicate once. Retain a private checked ticket or rejected
   decision. Apply the unchanged output restriction for every new raw output.

Do not cache complete LoopObservation/enclosingResults values in this design.
They may be large; their hit rate is unknown. Full-query result caching is
**deferred**. The selected mechanisms remove duplicate C2 calls and repeated
fixed-entry checks even when every complete raw-output query key is different.
They do not promise a project speedup.

### Current native path

`MethodBlockRuntime.observe` builds adjacent and repeat ScopeDemandViews from the
run's frozen DemandStore. It calls each family through `initials`, then calls both
again through the labelled-admission callback. `LoopConsumerObservation.observe`
also composes saved adjacent records through LocalRelationApplication, applies
the enclosing metadata adapter, normalizes the full pair, runs enclosing C5, and
checks saved Target metadata. All three families enter LoopObservation equality.

`DemandStore.intersect` keeps paired rows and actual scope exit. For each original
member it visits by-entry row IDs that match the current raw output's by-exit IDs.
`offerDataPair` calls `ops.restrict` and then applies the row's existing budget:

```text
budget = if exitDepth >= policy.fieldLimit then policy.fieldLimit else exitDepth + 1
```

`ApOps.restrict` calls Demand.kt `restrictFacts`. Protection transport invokes the
plain restriction on its parts. `restrictRaw` calls Reference.kt `restrict` for
each leaf. That scalar function first calls the raw-output-independent predicate
`policy.canStoreInitial(d.entry, member.toPattern())`, then calls the already
existing `restrictConclusionOnly`. This repeats the entry test across leaves,
protection parts and new raw outputs of the same fixed original/row.

### Owner quantum and bounds

Use the existing `MethodBlockRuntime.work(quantum)` ownership interval. A private
scratch object is active only during that call; clear and detach it in `finally`.
The work reservation stays held. No new queue, deferred action, coroutine, weak
cache, global cache, rejected-fact archive or pending-work counter is added.
If observation occurs outside an active owner quantum, execute the native path
synchronously. Do not add a new assertion or failure for that case.

Use separate insertion-ordered scratch maps. On capacity exhaustion clear the
map on the owner thread before inserting the current entry. A miss always runs
the native query/plan creation now. A failed/oversize preparation returns the
native fallback now; it never publishes a partial plan.

| Scratch | Entry limit | Per-entry admission limit | Lifetime |
| --- | ---: | ---: | --- |
| C2 answers | 32 | 128 AdmittedInitial references | one owner quantum |
| C5 entry plans | 32 | 2,048 candidate member/row references | one owner quantum |

C2 stores at most 4,096 admission references. C5 stores at most 65,536 row
decisions/references. These are reference-count bounds, not byte or GC bounds.
A C2 answer above the limit is used for this observation but is not retained.
An oversize C5 plan is discarded and uses native intersect; a bounded negative
plan marker may prevent a repeat preparation attempt in the same quantum.
Do not copy DemandPattern rows or retain raw output/result histories in a plan.

Every logical query keeps its entry cancellation checkpoint, including hits.
Exceptions and cancellation propagate through the same owner call. The scratch
is then discarded. Cache work does not add, remove or postpone actor work units.
The existing ready/pending/link queues and `used++`/completion checks stay intact.

### C2: one ordered answer bundle

Use the existing ScopeDemandView.initials API. Change only the internal
LoopConsumerViews admission callbacks to a `beginAdmissions(actual)` factory.
It returns a private per-observation `C2Answers` with `adjacent()`, `repeat()` and
`labels()` getters. Each family getter executes its scope loop once and stores
that family's unlabelled set plus labels. The label getter concatenates those
two ordered label sets. It does not issue another C2 query. Keep the observer's
current phase order: adjacent getter, saved AL/Target work, repeat getter, then
labels getter. This avoids moving the repeat query ahead of saved application.

Create this bundle even without an active quantum memo. A family result above
the memo weight limit still supplies both projections within its current
observation. The scratch limit controls reuse across observations, not whether
the two projections share the current native answer. No extra result history
survives the observation.

Preserve the current native AdmittedInitial order and layer. Each family getter
builds both projections from the same ordered native answers before freezing:

```kotlin
for ((scope, view) in adjacentDemands) {
    val answer = quantumC2?.getOrCompute(view, policy, exactKey(actual)) {
        view.initials(actual, policy)
    } ?: view.initials(actual, policy)
    for (admitted in answer) {
        adjacent += admitted
        labels += LoopLabelledAdmission(scope, ADJACENT, admitted)
    }
}
// Repeat the same loop for repeatDemands, filling repeat and REPEAT labels.
```

This is proposed pseudocode, not an implementation. The cache returns a present
empty answer as a hit; it must not use empty or null as a miss marker. Cached
answers use an unmodifiable LinkedHashSet copy after the size check. Keep exact
first-occurrence order when building both unlabelled and labelled sets. A match
in adjacent does not skip repeat, enclosing composition or Target metadata.

A C2 memo key has the exact frozen ScopeDemandView identity, policy identity,
method-owner quantum identity and complete input packet key. Identity wrappers
compare references with `===`; hash collisions alone never establish identity.
A packet key contains ordinary Facts equality **plus** the full
TaintTree.nonSubsumable mask. A non-null Boolean is not enough: two positive masks
can protect different memberships. Ordinary equality already includes layer,
shape/tail, fields, full mark payload, field E and FLOW mx. Do not erase them.
Use immutable canonical objects; never mutate a packet/key after insertion.

### C5: actual fixed-entry planning

The new APIs are private/internal capabilities. They do not add methods to the
public FrozenCompletion/StaticDemandView/ScopeDemandView contracts. Point 3 may
change frozen storage while preserving those contracts and iteration order.

#### Checked AP ticket

Add an internal factory beside Demand.kt's restriction functions. Its ticket has
a private constructor and immutable `(memberPattern, pair, policy, AP/catalog)` fields.
It is accepted only by the **same** existing predicate:

```kotlin
EntryDecision prepareEntry(ops, memberPattern, pair, policy) {
    return if (!policy.canStoreInitial(pair.entry, memberPattern)) Rejected
           else Accepted(EntryRestrictionTicket(memberPattern, pair, policy, ops.manager))
}
```

Do not replace `canStoreInitial` with `canEmitInitial`, `insideDemand`, an initial
membership lookup or a new preimage test. `canStoreInitial` restores the existing
NORMAL FLOW EXACT preimage of a stored STAR summary key. Keep that fallback.

Factor the existing native body, without changing it:

```text
restrictRawAfterAcceptedEntry(ticket, part):
    for leaf in ops.leaves(part), in the same order:
        restrictConclusionOnly(Conclusion(leaf.fact, leaf.exclusion,
                                        part.layer == DEMAND), ticket.pair.exit, ap.marks)

restrictFacts(ticket, raw):
    transportProtection(raw) { part ->
        pack exactly as current restrictPlainFacts:
            restrictRawAfterAcceptedEntry(ticket, part)
            normalizeFlowSummaryConclusion
            factsOf + existing GroupKey mergeAddDelta
    }
```

Keep transportProtection outside the same plain-part packing operation. Do not
replace it with a protected/unprotected flag. The existing scalar `restrict` and
ordinary non-prepared callers retain their entry guard. Only the private accepted
ticket may call the factored no-entry body. A rejected decision returns the same
empty selection without walking leaves/protection parts.

#### DemandStore local plan factory

Implement preparation inside DemandStore, where Query, MethodDemandIndex,
ScopedDemandIndex and rowPorts are already private. It can read these exact
native structures without a new graph/preimage API. An internal capability on
its anonymous scope-view object exposes preparation to the internal consumer.
An unknown view returns `NoPlan`, then calls its original intersect.

Prepare only when `policy.run >= 3`, `!hasStaticCompletion` and
`!hasSharedStaticCarry`. Keep exact native fallback for run 2, static carry or
completion, unsupported views, ZERO/control originals and Reach/Target queries.
These are performance gates, not permission gates. Unsupported cells still run
the identical native operation. No static closure is built eagerly.

For eligible DATA, bind the actual normalized **complete** original, method,
physical scope, actual exit, policy/catalog and frozen snapshot identities. This
occurs after the current enclosing metadata adjustment and
`normalizeFlowSummary(ap, original, adjusted)` call. Keep the raw complete original
for native saved application/cycle protection and enclosing-result headers.
Do not merge different originals solely because a summary normalizes to STAR.
Ordinary post-application preparation takes each actual normalized member's
`toPattern()`. The pre-application shortcut below uses Pattern-only templates and
checks that the actual normalized member has the same pattern before it uses a
ticket. It does not call `ap.initial` for a hypothetical result.

Build ordered plan entries as follows:

```text
for member in completeOriginal.forEachMember order:
    for id in local.byEntry.lookupPrefixes(member.base, member.path) order:
        retain the current exact scope/rowPorts exit test
        row = local.rows[id]                       // keep original row reference
        store (member, id, row, existing exit guard,
               prepareEntry(ops, member.toPattern(), row, policy))
        stop and return NoPlan if the row-reference bound is exceeded
```

Do not collapse IDs, members or normalized keys. A row reached through two ND
members keeps both positions. Keep nullable/typed-ZERO exit guards and their
current outer `offer` behavior; only ordinary DATA exits use a prepared ticket.
The plan key includes the actual complete normalized original, actual exit,
view/snapshot identity, policy identity and owner. Plan equality adds no field to
DemandPattern or the row's existing equality/hash.

#### Apply to each raw output

For each apply, run the unchanged RuntimeDataDomain guard and native control
handling. Compute `outputIds` from the existing by-exit visitAround calls on the
new raw output leaves. Walk the plan in native member/row-ID order and test
`id in outputIds`. This preserves output-dependent prefix compatibility; entry
preparation is not a geometry hit or C5 permission shortcut.

For each output-matched plan row, keep the current outer statistics/sample hook,
paired row and row-specific budget. Rejected decisions take the existing rejected
row result path. Accepted tickets call the factored restriction above, then apply
the **same** FL+1 clamp, `ops.limit`, protection-aware ExactDemandResults insertion
and sample hooks. Data must exhaust every row; do not add a first-hit stop.

This plan stores entry decisions even for rejected rows so diagnostic row-attempt
order/meaning can stay unchanged. Native entry-check counts now differ; add
explicit plan-check/hit/miss/fallback counters. C2 native-call counters remain
native-call counters; logical query counts and cache hits use separate counters.
Do not interpret fewer callbacks as fewer semantic rows or actor work units.

#### Root and BlockBoundaryDemandView composition

Root plans use the same DemandStore Query(method) as root intersect. Non-root
plans use the exact physical scope and exit. BlockBoundaryDemandView retains its
physical-then-normal ExactDemandResults composition. ZERO/control originals and
all `acceptsTarget` calls use the current native path, including its normal-output
port union, exceptional normal-ZERO HACK and run-2 static-shortcut checks. No DATA
port alias or new ZERO route is introduced. This explicit fallback avoids a new
control planner while optimizing later local DATA C5.

#### Empty local DATA plan before saved replay

An entry-rejected row cannot produce C5 DATA for any raw output. A plan with no
accepted DATA row for a known output base therefore has an empty DATA result for
every output path, layer, field E, mark and protection mask at that base. This is
an entry proof, not a failed output lookup or a new field-preimage algorithm.
Retain exact paired IDs and actual enclosing ports in this certificate. If one
relevant plan is unsupported, oversize or nonempty, replay natively for that port.
Do not treat `NoPlan` or a cache miss as an empty certificate.

Use the certificate to omit saved-record AP application only in this first
DATA-only cell:

```text
run >= 3; local C5 with no static completion/carry
non-root enclosing scope; adjustEnclosingData is the native identity adapter
record.direction == mode.direction; record.premise.tail != ANY_TAINT
original is non-ZERO; actual is FlowTree or TaintTree
every original member is non-ZERO
actual kind agrees with complete original.isFlow
record is an admitted native DATA record, with valid K6 kind and non-ZERO base
record conclusion is FlowTree or TaintTree; its output base is known
every relevant exact enclosing-port DATA plan has an empty certificate
```

Here `Summary.kt.leafKinds` compiles every edge to the record conclusion's base.
`EdgeApplication`/`Results` preserve that non-ZERO base for DATA results. Grafting
and protection attachment keep the DATA kind. With no MUST or run-1 policy lane,
the LocalRelationApplication sink cannot turn this cell into Reach or Target.
The observer's `markRequest` callback has no effect; actual replay is unchanged.
These native adapter facts are source-backed design obligations, not a claim
that Lean verifies the Kotlin code. `RuntimeDataDomain.packet` checks legal
bases; the K6 record kind check is in `RecordStore.checkNativeRecord`.

Before AP application, make only immutable Pattern templates for the complete
parent original. If the guarded input/output kind is FLOW, change its single
EXACT member tail to STAR, as `normalizeFlowSummary` does. Keep its base, path,
mark and E. Otherwise keep the complete non-FLOW/ND original unchanged. Call the
exact `canStoreInitial` predicate on these templates. Do not intern hypothetical
InitialAp, Facts, query roots or graph nodes. Plan membership uses each template
in the same native member order; member geometry is unchanged by this tail step.
If application runs, compare the actual normalized member patterns with the
templates before using their tickets, and pass the actual normalized whole
premise into EnclosingResults. A failed validation takes the native guarded
restriction path; it does not drop an output.

Keep native replay for reversed views, MUST records, Reach/Target-capable cells,
ZERO originals, root metadata adapters and any unknown kind/output base. In
particular, backward non-ZERO Reach can become DemandTarget in the native sink;
an empty DATA plan gives no permission to suppress that callback. Saved Target
iteration, adjacent/repeat C2 and their labels always run, even if every DATA
replay has an empty certificate. Keep their order. The per-record cancellation
checkpoint and dedup position still run before the shortcut. Count the shortcut
separately from native application calls.

Preparation can inspect entry rows that no raw output would visit. It can cost
more on a one-off all-miss query. The bounds limit that work; a negative marker
only avoids repeated failed preparation. The proven work reduction applies to
duplicate C2 projections and repeated eligible entry checks/empty DATA replay,
not every call or the total project run.

### Saved AL application and complete observation

Do not replace saved-record application with a matching Boolean or C5 plan.
Keep LocalRelationApplication.applyRecord/applyRecordView, native MUST lanes,
pending demotion, opposite-direction record views, cycle protection and the
**whole** B original. Keep `(RecordLeafView, protected)` dedup and each real
record/enclosing exit. The observer's markRequest callback remains a no-op;
actual replay keeps its ordinary request behavior.
The preceding empty-DATA certificate is the sole permission to omit an observer
application in this design. Its narrow cell does not alter these native paths.

Saved ND Target arms are metadata only. Actual local ND execution still joins all
arms through applyCombination. Saved ZERO -> NormalTarget adds no new effect.
NormalTarget still needs FORWARD, NORMAL and the current not-already-saved test.
DemandTarget still needs exact enclosing paired acceptance through native target
APIs. Preparing a DATA C5 row does not grant Target or publication permission.

Keep EnclosingResults headers `(scope, exit, complete original)` and exact
`LoopObservedMember(pattern, layer, nonSubsumable)` union. Do not use Facts.equals
as full observation equality or drop protection before union. All adjacent,
enclosing, repeat and labelled families remain in the signature. The existing
LoopOutputRestriction still drops an empty observation, tests positive budgets
in ascending order, chooses the first equal complete signature and otherwise
keeps raw. Bounds, bypasses and Work completion remain unchanged.

### Proof and implementation gates

The [constructive model](../../spec/lean/proposals/loop-consumer-query-reuse-20261103/README.md)
proves entry factoring for arbitrary native output/protection/normalization
functions, ordered row equality, exact C2 projections, complete signature
preservation, bounded synchronous memo correctness and finite adaptive-query
program equivalence. Its CEGAR witnesses cover normal FLOW preimages, crossed
pairs, ND metadata versus AND execution, masks omitted by Facts.equals, complete
cycle originals, ZERO/Target and fallback gates. It proves Pattern-template
equality under the explicit kind guard and empty-DATA replay removal while
exhibiting the Target-capable counterexample. No unique-hit premise is used.

The finite model does not kernel-verify Kotlin AP stores, native concurrency or a
future adapter. During implementation, use native tests first for all witness
cells and fixed-context plan/public/native fallback differential checks. Include
multiple compatible rows/exits, multiple original members, varying FL+1 depths,
all protection masks/layers and exception cleanup. Check memo all-miss/eviction/
oversize/empty-hit cases and both owner-quantum boundaries. Then run the required
DATA-only empty-plan differential tests, native Target-capable/MUST/reverse/root
fallback controls and exact template/actual normalization tests. Then run the
required native suites and project quality/performance gates. No Kotlin implementation,
Gradle/analyzer run, profile experiment or commit is part of this design work.

## C. Reuse packed static guidance and terminal inputs

Component source: [bidirectional-packed-static-guidance-design-20261103.md](bidirectional-packed-static-guidance-design-20261103.md).
Frozen design SHA-256: `fb871ac6c82ee48c9b27565bc7274cfe120e06cdf2bb43cb8c53c22314f56f86`.

### 1. Scope

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

### 2. Select a detached compact catalog

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

### 3. Lifetime and input pipeline

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

### 4. Normalize once, then encode

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

### 5. Encode exact labels and typed terminals

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

### 6. Reuse query plans and materialize selected values

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

### 7. Ownership, statistics and freeze

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

### 8. Examples and failure checks

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

### 9. Proof scope and remaining implementation obligations

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

### 10. Source migration

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

### 11. Implementation and verification plan

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


## D. Drop dead local conclusions before boundary work

Component source: [bidirectional-block-boundary-live-locals-design-20261103.md](bidirectional-block-boundary-live-locals-design-20261103.md).
Frozen design SHA-256: `eacb7f40449296a0db35a675070e2180dc9420c8fa9a88c33b427fad08da18c2`.

### 1. Contract

Compute forward and backward live-local bit sets when the method block
metadata is built. At an outgoing boundary, drop a DATA edge if its
conclusion is a local variable that is dead on that continuation. Perform
this test **before summary construction, publication, C5 intersection and
loop-consumer demand checks**.

Use CFG instructions only. Do not load rules, inspect rule conditions,
enumerate aliases or call alias analysis. A rule cannot access a local
that its instruction does not mention. An inaccessible local does not
need an alias check.

A loop-body temporary whose old value is dead on repeat and on every
leaving route has no boundary summary. It does not escape the loop body.
This test uses values and CFG uses, not variable names or declaration text.

| Current behavior | New behavior |
| --- | --- |
| Unchanged delivery brings a temporary to a boundary, then constructs a local summary and checks its consumers | One bit test drops a dead local conclusion before this work |
| A temporary can enter parent completion, publication and demand stores although the continuation cannot read its value | The temporary stays inside its useful block scope |
| Live loop-carried values use the ordinary block path | The same path remains for live loop-carried values |

**Major analyzer semantic changes: none.** The selected change removes
unobservable local rows. Internal local summaries, demand rows, callbacks
and work counters can decrease. They are not required to be equal to the
unfiltered inventories. Preserve observations, live results, method
summaries, reports, source permission and static effects. Do not change
field transfer, marks, layers, protection, ND joins, CFG reachability,
loop restriction, initial emission or method exit rules.

Only test the conclusion base. Keep the complete premise and all retained
fact annotations unchanged. Never drop ZERO, Target, static, argument,
`this`, return or exception facts through this test. Keep effects already
produced inside the block, including Targets and NORMAL rule contributors.
Do not infer a new lexical variable identity or rename method registers.

### 2. Principal pattern

```java
x = ...;
while (true) {
    var tmp = x;          // Reads x. Replaces the old tmp.
    use(tmp);            // Reads the new tmp.
}
```

```text
At the copy:             P -> x.$/T produces P -> tmp.$/T.
At repeat, before:       tmp enters summary/demand processing.
At repeat, after:        drop P -> tmp.$/T immediately.
Reason:                  the next copy kills old tmp before any read.
Retain x:                the next copy reads x before overwriting it.
```

The same test applies to FLOW and DEMAND facts with this local base.
The field chain and mark do not make an inaccessible local accessible.
An effect from `use(tmp)`, such as `P -> Target`, is already separate and
remains. The filter does not undo the instruction.

This is different from a live carried value:

```java
Node tmp = null;
while (again()) {
    if (choose()) tmp = sourceT();
    else sinkT(tmp);      // Can read a previous iteration's tmp.
}
// AL does not use tmp.
```

The repeat continuation keeps `tmp`: there is a path to a read before an
overwrite. The existing summary and restriction path handles that value.
The leaving continuation drops `tmp` if it is dead in AL. Do not add a
direct repeat path or drop live carried values.

### 3. Instruction metadata and fixed point

Add a small metadata API next to method forms. It must inspect operands
without compiling or specializing a rule. Do not reuse
`isBaseRelevant`: its current backward footprint can query aliases.

```kotlin
data class LocalAccess(
    val uses: BitSet,
    val definiteDefinitions: BitSet,
    val mentions: BitSet,
)

// Proposed API. All indices are the existing LocalVar.idx indices.
fun localAccess(instruction: CommonInst): LocalAccess
```

Forward `uses` contains RHS locals, call receiver/arguments, address and
index locals of a memory LHS, and return/throw operands. A direct local
LHS is a definition, not a read, unless it also occurs in an operand.
For `tmp = x`, USE is `{x}` and DEF is `{tmp}`. For `x = x.f`, USE
contains `x` whether or not the overwrite can be certified. A field/array
write does not define its base local.
`JIRAssignInst.operands` includes the LHS. Do not collect that array as
forward USE without separating the direct local LHS from the RHS.

A definition kills the old local only if the overwrite is definite on
all successors of that CFG instruction. If an assignment can throw before
it commits, use an empty kill set unless the existing graph already has
a separate committed-write node. Do not add a graph rewrite or a new
exception policy to make the mask smaller.
The initial classifier can certify plain local/constant copies, including
`tmp = x`. An unknown or potentially throwing RHS has no certified kill.
`LanguageManager.producesExceptionalControlFlow == false` is not a commit
certificate: its JVM implementation does not classify every throwing RHS.

Use ordinary forward USE/DEF liveness. Backward analysis must include
definitions as accesses: it must reach the instruction that defines the
demanded local. Use all instruction mentions and no kills for the backward
mask. This conservative backward calculation needs no reverse-transfer,
rule or alias analysis. It can keep extra locals; it cannot drop a needed
one. In particular, do not swap USE and DEF and kill RHS locals: the
reverse of `a = b` also preserves existing `b` facts.

```kotlin
// Temporary solver state. graph is the actual graph for this direction,
// including its exceptional/discovery edges and the loop feedback edges.
val liveIn = Array(graph.size) { BitSet(localCount) }
val queue = allInstructionIndices()

while (queue.isNotEmpty()) {
    val s = queue.removeFirst()
    val next = if (forward) access[s].uses.cloneBits()
               else access[s].mentions.cloneBits()
    graph.forEachSuccessor(s) { to ->
        val carried = liveIn[to].cloneBits()
        if (forward) carried.andNot(access[s].definiteDefinitions)
        next.or(carried)
    }
    if (next != liveIn[s]) {
        liveIn[s] = next
        graph.forEachPredecessor(s) { queue.addIfAbsent(it) }
    }
}
```

Initialize **all** nodes, including non-returning SCCs. Starting only from
method exits misses `while (true)`. The equations compute the least fixed
point from empty sets. They do not inspect current facts or demand.

### 4. Masks at real boundary continuations

Retain immutable bit sets for block output interfaces in both directions.
The bit set for a real directed route `s -> to` is `liveIn[to]`: the
instruction at `s` has already run. Do not use the input mask of `s`.

```kotlin
// Proposed sidecar for the existing immutable layout/form owner.
class BlockLiveLocals {
    fun mayLeave(direction: Direction, block: BlockId,
                 exit: PortId, local: Int): Boolean
    fun mayFollow(direction: Direction, route: MethodBlockRoute,
                  local: Int): Boolean
}
```

For the existing single logical normal exit, union the masks of its real
leaving routes. Keep feedback separate. Before actual delivery, check
each real route again. A union must not leak a value from a live route
onto a dead route.

```text
Loop repeat output:    union of genuine repeat continuations.
Loop leaving output:   union of genuine leaving continuations only.
Actual route delivery: liveIn of that route's destination.
```

Use the same rule for backward routes, empty identity blocks and nested
blocks. A child result kept for one continuation can become dead when it
crosses the next parent boundary. Check that boundary too. Preserve the
single loop exit and its existing join scope.

Build this sidecar with the existing method decomposition metadata, once
per actual graph direction. Cache it with that form/layout owner, not
with each run, scope, fact, mark or caller. Release instruction solver
arrays after retaining the required boundary masks. No fact or callback
belongs in this metadata. Treat stored bit sets as immutable.
An unsupported synthetic output role keeps the native path until its
actual target is known. A missing mask is not an empty live set.

### 5. Boundary integration

```kotlin
fun keepLocalConclusion(block: BlockId, exit: PortId, value: Facts): Boolean {
    val local = value.base as? AccessPathBase.LocalVar ?: return true
    return liveLocals.mayLeave(direction, block, exit, local.idx)
}

// BlockRunState: early guard avoids boundedSummaryResult work.
fun retainBlockSummary(exit: PortId, original: PremiseKey, value: Facts) {
    if (binding?.keepLocalConclusion(exit, value) == false) return
    existingRetainBlockSummary(exit, original, value)
}

// Central guard also covers endAt's direct retainSummary path.
fun retainSummary(original: PremiseKey, value: Facts, exit: PortId) {
    if (binding?.keepLocalConclusion(exit, value) == false) return
    existingNormalizeCountRestrictAndPublish(original, value, exit)
}

// MethodBlockRuntime.onApplied: applies to saved and current child results.
fun onApplied(link: LocalLink, exit: PortId, original: PremiseKey, value: Facts) {
    if (!keepLocalConclusion(link.child.block, exit, value)) return
    existingLimitRestrictAndStoreCompletion(link, exit, original, value)
}

// Before routing one actual completion branch.
for (route in deliveryRoutes(exit)) {
    val local = value.base as? AccessPathBase.LocalVar
    if (local != null && !liveLocals.mayFollow(direction, route, local.idx)) continue
    existingRouteCompleted(route, original, value)
}
```

Use the same producer guard for leaf delivery, empty identities and
parent forwarding. Do not add an independent fact store or replace
post-statement deduplication. Leave unchanged delivery inside a block.
It can deliver a dead temporary to the boundary; the bit test stops it
before the expensive boundary work.

Apply the same masks inside loop observation. Adjacent and repeat C2
families use their own continuation masks. Saved-AL replay checks its
completed local output against the enclosing output mask before
normalization/C5. Do not let observer-only replay reintroduce a row that
actual boundary delivery drops. All nonlocal observation families keep
their existing order and behavior.

Physical method entry/exit rules still run at their existing instruction.
Do not put a dead-local shortcut ahead of those handlers. Filter only
their completed DATA output. The direct `endAt`/`retainSummary` path must
use the same final output guard; do not bypass it accidentally. The
STATIC shortcut and Target path have nonlocal conclusions and pass.

Save completed effects and existing contributor snapshots as before.
An edge with a dead local **premise** and a live conclusion remains.
This feature does not remove inputs needed by joined writer binding or
the inventories retained by point 1.

| Source | Proposed change |
| --- | --- |
| `JIRMethodEntry`, `JIRMethodForms` and method-context metadata access | Extract raw local operands; own the decomposition-side liveness metadata; do not use the alias-aware relevance API |
| `MethodBlockLayout` sidecar | Hold immutable per-direction interface and real-route masks; leave block/port IDs unchanged |
| `BlockRunState.retainBlockSummary` and `retainSummary` | Early and central conclusion-only guards |
| `MethodBlockRuntime.onApplied` and `routeCompleted` | Guard saved/current results before observer work and before each actual route |
| `MethodBlockRuntime.observe` | Use the same continuation and enclosing-output filters in observer-only replay |

The metadata API must have a conservative default for unsupported
backends. It must not silently return an empty mask for an unclassified
instruction or interface. The selected JVM path must classify the plain
copy in section 2 exactly.

### 6. Proof and implementation gates

The [constructive model and proof report](../../spec/lean/proposals/block-boundary-live-locals-20261103/REPORT.md)
cover finite CFG liveness, forward read-before-kill paths, conservative
backward mentions, boundary masks and dead-local observation removal.
The checker passes 42 theorems and audits 72 declarations. Its source
pins use `c7ed16e99c599ca926812c067df0b6608b6185f2`, which has the same
runtime as the combined proposal's reference revision.
The native instruction classifier and insertion sites remain implementation
obligations. The model does not prove a JVM speedup or a byte saving.

The proof chain is:

```text
finite monotone equations -> executable least fixed point
read before definite kill -> local is in liveIn
local absent from liveIn -> no observation of that old value
each boundary mask covers its actual continuations
drop dead conclusion -> same remaining observations and live results
nonlocal/premise/annotation/completed effects -> unchanged
```

Do not claim equality of all internal summary streams after removing dead
rows. The three original component proofs still apply to their retained
inputs. The new erasure proof establishes the observation projection for
the pre-filter. Kernel checking does not establish the Kotlin adapter.

Add native RED controls before implementation, then make them GREEN:

| Control | Required check |
| --- | --- |
| `x=...; while(true){ tmp=x; use(tmp); }` | No `tmp` boundary summary, completion or observer call; retain `x` |
| Dead copy with FLOW, FULL T and DEMAND | Same drop for all annotations; surviving facts stay bit-for-bit equal |
| Conditional assignment then use on another traversal | Keep live carried local on repeat; preserve sink |
| Dead AL local but live repeat | Keep repeat; no DATA delivery to AL |
| Live AL local | Preserve its output and later sink |
| Two leaving routes, local live on one | Shared exit keeps it; actual dead route drops it |
| Nested loop local | Recheck child and parent exits; no leak into an unrelated suffix |
| `x=x.f`, field/array write, exceptional assignment | Read-before-write and uncommitted overwrite preserve old-value liveness |
| Backward `a=b` and definition reached before a read | Keep required definitions and preserved RHS facts |
| ZERO, Targets, statics, arguments, return, exception | Existing paths, exit effects and inventories unchanged |
| Live conclusion with a dead premise | Keep full original premise and annotations |
| Non-returning SCC, empty block, backward discovery | Valid fixed point and exact route coverage |

Compare reports, live/method outputs, source permissions and required
guidance with the unfiltered oracle. Check dead-row absence separately.
Do not require old diagnostic work counts or dead local demand rows.

Run this pre-filter before the query-reuse optimization in point 2.
Counters can record local boundary offers/drops and avoided summary or
observer entries. Do not perform a demand lookup to count avoided work.
In the selected campaign, report those counts with the latest reached,
complete and accepted run-N. The current measurement frontiers remain:
OWASP run-5/5/5; Conductor run-6/5/5; Thingsboard run-1/none/none;
Stirling-PDF run-8/7/7. No new measurement is part of this design update.

## Combined implementation order

The following is the future implementation plan. This design task changes
no Kotlin implementation and runs no Gradle/analyzer experiment.

1. **Keep the reference oracles.** Pin the current binder, observer,
   restriction and static builder in test helpers. Run the four constructive
   component model checkers and the dead-local checker. Add the named RED controls before
   changing its production path.
2. **Add detached read owners and frozen exports.** Keep native summaries,
   targets, source/sink seeds, contributors and exact diagnostics. Move every
   local entry directory, including saved-only entries. Move each physical
   subscriber directory once. Keep the old binder/result behavior initially.
3. **Move release to the successful join.** Gate every live API after seal.
   Add exception injection at each acquisition, capture and close step.
   Run the same binder through the detached lease after execution release.
   Keep current pruning, guards and driver publication. Commit this feature
   separately when the focused controls and common/JVM suites pass.
4. **Replace rich static attachments.** Add the compact codec, geometry pools
   and owner-local ordinals. Migrate every query/index consumer against the
   ordered reference oracle. Keep B, AP writer binding and graph traversal.
   Check that the frozen result has no live-owner closure. Commit separately.
5. **Filter dead locals and prepare loop queries.** First add instruction-only
   forward/backward live-local metadata and boundary guards from section D.
   Verify `tmp=x` drops old `tmp` before summaries/demand, keeps `x`, and keeps
   live carried locals on the native path. Then add the ordered C2 answer bundle. Add the
   checked AP entry ticket and local C5 plan next. Add the bounded C2
   owner-quantum memo, bounded C5 plan cache (32 contexts, at most 2,048 row
   references per plan), and the proved narrow empty-DATA shortcut. Preserve all
   native fallbacks. No full-observation memo is selected. Commit separately.
6. **Run integration gates.** Test A/B/C alone and together on deterministic
   native fixtures. Compare normal/demand summaries modulo dead local
   conclusions, full marked geometry,
   protection, raw NORMAL IDs, outgoing DEMAND Targets, source/sink seeds,
   contributor rows, exact scoped/port keys and composed handoff queries.
   Test late callbacks, empty regions, nested loops, predefined summaries,
   recursive callers, reverse/MUST records and partial failures. Check dead
   local row absence and observable/live-result equality separately.
7. **Repeat the selected project campaign.** Use the existing direct Gradle
   harness and only the four unchanged configurations below. Do not rerun
   saved baselines or disable statics/aliases to claim a speedup.

The coding order puts lifetime release before catalog construction. Query
reuse is independent of catalog storage, but its scratch cleanup must be
part of the new lifecycle. Separate commits keep review and rollback clear;
they do not require a new runtime feature flag.

## Required removals and retained paths

Remove the old actor/storage callback dependency from real joined binding,
late-only release of execution/current-delivery state, duplicate labelled
C2 calls, repeated entry checks in the selected prepared path, and rich
W/R/terminal builder/frozen row catalogs after their replacements pass.
Remove dead local boundary rows before their summary, completion and demand
work. Keep existing handling for locals live on the actual route.

Keep actual input history, admitted native summary stores, raw Target and
source/sink inventories, contributor snapshots, raw pre-exit write IDs and
the current prune. Keep the existing B graph, static composition/BFS,
fallback control/Target/native replay, `RunActor.freeze` compatibility and
synthetic handoff paths. Secondary candidate-directed pruning, full
observation caching, IR storage and new mark/field policies are excluded.

## Post-implementation measurements and acceptance

Use FULL, 16 GiB, aliases/statics enabled, limits `1,1,2,3,...`, and direct
`runProjectAnalyzer` for OWASP, Conductor, Thingsboard and Stirling-PDF.
Keep their existing 1,000/1,080 s analysis and 1,200 s outer timeouts.
Reuse f945 and 86ad reports. Clean older raw captures only after preserving
their derived evidence; capture a new OOM before cancellation.

Report these units separately:

```text
Every project: reached / complete / accepted run-N, status, engine/static/
              seal/barrier times, exact finding identities and demand frontier.
Thingsboard:  heap before release, post-GC heap, required input rows,
              retained native stores, compact geometry/label/terminal counts,
              binding candidates/output, builder/freeze peak, later run-2 work.
Conductor:    run-4/run-5/run-6 physical packets, local offers, observations,
              C2 calls/hits, plan checks/hits/rows, empty replay skips,
              native fallbacks, prefix trials, Java/all-thread CPU and GC.
Stirling:     the same query/work census for run-6/run-7/run-8.
Loop locals:  per run-N boundary offers/drops, retained mask size,
              avoided summary/observer entries, live carried controls.
```

A shorter failing run or a result with fewer findings is not a success.
The three strict legacy Stirling differences and the censored Thingsboard
report are not waived by this proposal. Verify non-regression against 86ad
and report the strict f945 comparison without replacing fingerprints by
unproved per-return equivalence.

For memory, measure actual release and the subsequent binding/freeze peak;
do not reuse MAT's 3.976 GiB simulation as a patch result. Completing the
old first failure does not prove that later binding or run-2 fits. For
query work, target at least a twofold reduction in the slow iterations,
but report actual rates even if the target is missed. Distinct-key counts
and fallback rates must explain a low reuse effect.

The design does not establish the 60 s run-1 engine target or convergence
on every project. It removes the measured retention overlap and redundant
query/catalog work while keeping the current analyzer contract.

# Release closed state at the successful run join

3 November 2026. Status: **SELECTED DESIGN; not implemented**.

This document specifies point 1 of
[the selected next-iteration design](bidirectional-joined-state-and-loop-consumers-next-iteration-20261103.md).
The user selected all three points. This document does not authorize Kotlin
changes, project runs, or commits. The runtime reference is
`050b83cfb7b2e75856ea113c44d0a2d6b707250d`. Checkout `b5fbae2400516e90beb9e17aec6a4bb8a2ac3162`
has the same runtime. Its archived ZERO-control draft is not selected here.

## 1. Result and semantic scope

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

## 2. Evidence and limit of the memory claim

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

## 3. Exact read audit

All paths are under
`core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/`.
The proof package pins these files at the reference revision.

### 3.1 Reads during joined static completion

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

### 3.2 Reads after `RunManager.run` returns

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

## 4. State ownership and phases

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

## 5. Concrete detached read APIs

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

### 5.1 Local inputs: move the table

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

### 5.2 Physical inputs: move the existing index

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

## 6. Capture and release order

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

### 6.1 Field and API change plan

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

## 7. Diagnostics, contributors and failure

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

## 8. Examples and exact results

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

## 9. Proofs and implementation gates

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

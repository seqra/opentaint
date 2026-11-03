# Next iteration: finish engine lifetimes and avoid repeated consumer work

3 November 2026. Status: **all three ranked points selected for detailed design;
not implemented**.
Reference runtime: `050b83cfb7b2e75856ea113c44d0a2d6b707250d`.

The [complete implementation proposal](bidirectional-joined-state-loop-consumers-packed-guidance-implementation-20261103.md)
specifies the concrete owners, APIs, lookup paths, constructive proofs,
native test gates and implementation order. The secondary pruning candidate
in section 5 is not selected.

Use the [current campaign report](../reports/bidirectional-loop-blocks-scoped-requests-performance-20261103.md)
and its embedded CPU and heap evidence. The earlier static-terminal/query
proposal used `1e6c4396`. It is historical. In the current campaign,
Thingsboard does not reach run-2.

| Project | Latest reached / complete / accepted | Result |
| --- | --- | --- |
| OWASP | run-5 / run-5 / run-5 | Complete; all 4,112 baseline identities |
| Conductor | run-6 / run-5 / run-5 | Timeout; accepted report has all 7 baseline identities |
| Thingsboard | run-1 / none / none | OOM during static-binding preparation; no accepted report |
| Stirling-PDF | run-8 / run-7 / run-7 | Timeout; all 22 identities from 86ad; three strict differences from f945 remain |

The block-request correction restores all five newly missing identities from
the previous campaign. Keep that correction. Do not recover the shorter
times by dropping the newly reachable work.

## 1. Scope and rank

The required contract preserves analyzer semantics. The proposals do not change initial
emission, field limits, exclusions, marks, ND premises, static visibility,
normal/demand layers, source permission, Target rules or report identities.
They do not change IR storage or the soft-reference manager.

| Rank | Proposal | Current behavior -> proposed behavior | Expected impact |
| --- | --- | --- | --- |
| 1 | Release closed execution and delivery state at join | Retain live-engine stores through binding -> retain only the state that binding and handoff read | Remove a measured multi-GiB lifetime overlap at the run-1 barrier |
| 2 | Prepare and reuse loop-consumer queries | Repeat admission, native replay and paired restriction for each offer and prefix -> share their fixed query parts | Target at least a twofold reduction in the slow Conductor and Stirling iterations |
| 3 | Reuse packed static guidance instead of copying rich rows | Copy existing W/R and terminal rows into builder sets -> borrow sealed views or retain compact row references | Remove much of the builder's measured 1.37 GB and avoid a second row catalog |

Rank 1 addresses the first OOM. Rank 2 addresses the dominant time cost on
two other projects. Rank 3 removes another part of the same handoff memory
overlap. A measured saving and an expected saving are different quantities.
None of these changes has been benchmarked yet.

## 2. Release closed state at the successful join

### Evidence

Thingsboard's engine finishes after 699.248 s. It fails 53.411 s into static
binding preparation. The interrupted stack is in
`KilledStaticWriteStore.freeze`, before `binding.complete()`.
The heap confirms `processed == 0`, `candidateInputs == 0` and
`boundOutputs == 0` in the joined binder.

MAT finds 15,309,242,544 bytes of reachable heap. An explicit retained-set
removal simulation for selected execution and delivery roots contains
104,324,750 objects and **4,268,877,960 bytes: 3.976 GiB, or 27.88%**.
This is not a measured saving from a patch. The implementation must remove
the relevant strong paths to obtain the saving.

The selected roots include execution edge stores, local/call services,
point resumes, initial stores, worklist containers, completion/cache state
and closed publication/delivery indexes. The simulation excludes required
inputs, admitted summaries, Targets, raw write inventories, `bodyWork` and
`runContext`. Do not claim that all 5.70 GB attributed to actors is freeable.

`SummaryStorage.visitJoinedInputs` reads its subscribers and their input
indexes. It does not read `SummaryStorage.published`. The latter retains
about 1.18 GB. Local binding reads `Entry.links` inputs, about 773 MB;
those inputs must stay. Its local publication and Target delivery indexes
are separate from the admitted summary and Target stores.

### Pipeline

Current:

```kotlin
joinAllRunners()
completeJoinedStaticGuidance(liveActors, liveSubscriptions)
exportHandoff()
releaseActorsAndSubscriptions()
```

Proposed:

```kotlin
joinAllRunners()                  // Existing counted-Work barrier.
check(noPendingWorkOrEvents())

val diagnostics = captureExistingDiagnostics()
val contributors = captureNormalRuleContributors()
val binding = sealJoinedReadInputs()

releaseClosedExecutionState()    // No changes to immutable key objects.
releaseCurrentDeliveryIndexes()  // Keep subscriber/input directories.

val guidance = completeJoinedStaticGuidance(binding)
commitExistingHandoff(guidance, diagnostics, contributors)
releaseBindingInputs()
```

The owner performs release. `MethodEdgeStore` must not acquire static,
binding or support responsibilities. Do not create a second standing store
of actual input facts. The read facade borrows the existing immutable input
links and summaries after join.

```kotlin
interface JoinedBindingInputs {
    fun states(): Sequence<JoinedStateView>
    fun visitLocalInputs(owner: OwnedScope, visit: (OwnedWriterInput) -> Unit)
    fun visitCallerInputs(method: MethodKey, writer: Publication,
                          visit: (OwnedWriterInput) -> Unit)
}

interface JoinedStateView {
    val owner: OwnedScope
    val admittedSummaries: SummaryReadView
    val targetsForHandoff: TargetReadView // Keep NORMAL and DEMAND rows.
    val outgoingDemandTargets: TargetReadView // Existing static-attachment input.
    val rawStaticWrites: StaticWriteReadView
    val privateStaticSeeds: StaticSeedReadView
}
```

These are proposed interfaces, not existing APIs. Prove the actual read
footprint before choosing their implementation. Keep full caller keys,
scope/port coordinates and immutable AP values. Do not clear fields inside
objects used as hash keys. Do not clear shared AP interners or rebuild
canonical identities as part of release.

### Example and fact trace

```java
void root(Box p) {
    set(p);
    consume();
}
void set(Box p) {
    C.f = p;
    // Raw writer: p.*/FLOW -> C.f.*/FLOW, DEMAND.
    // An actual T input supplies T at this write, as before.
}
void consume() {
    sinkT(C.f);
    // Static reader/Target guidance remains owned by this method/block.
}
```

Before, binding keeps instruction facts and delivery indexes while it
borrows the actual `root -> set` input and the raw writer. After, it borrows
the same input and writer without retaining the closed instruction stores.
It produces the same bound static row. Clearing all local links would be
incorrect: the writer would lose its actual input. Clearing raw pre-exit
writes would also be incorrect when an exit rule kills the exported summary.

### Proof and native gates

Prove that successful join prevents further execution/delivery, that every
post-join read uses the retained facade, and that binding returns the same
ordered semantic results. Preserve diagnostics and NORMAL contributors
before release; publish neither early. A timeout or OOM must not commit a
partial forward barrier.

Native controls must cover local and physical inputs, recursive callers,
killed exit writes, predefined summaries, complete scope/port keys, ND
contributors, late callbacks and exceptional ZERO guidance. Add lifecycle
assertions so an invalid post-join execution read fails in tests. Measure
actual post-release GC occupancy; the MAT simulation is not that test.

The [unselected lifecycle model](../../spec/lean/proposals/post-join-execution-root-release-20261103/REPORT.md)
passes 35 constructive theorems. It proves result equality only under its
retained-read-footprint contract. It includes counterexamples for a binder
that reads released state and for a retained alias. It does not prove Kotlin
read safety, GC reclamation, canonical identity or a project memory saving.

## 3. Prepare and reuse loop-consumer queries

### Evidence

Current whole-phase Java samples place loop observation at 61.70% in
Conductor run-4, 76.86% in run-5, 93.63% in run-6, and 95.74% in Stirling
run-7. These are Java stack shares. They exclude native GC CPU.

Conductor run-4 performs 842,344 physical processing events, versus
8,185,369 in 86ad, but takes 249.455 s versus 76.862 s. Its logged hot owners
perform 19.63 million observations and 11.19 million prefix trials.
`ParametersUtils.replace` and `replaceList` account for 98.94% of the
logged observations. The sample is not an all-method census.

The local demand logger records 79.20 million C2 lookups and 22.51 million
C5 row attempts. Of those attempts, 14.89 million reject the exact input
condition. No static transitive expansion occurs in this run.

### Current and proposed query

```kotlin
// Current: repeated for a raw scalar and its trial prefixes.
val adjacent = adjacentC2(value)
val full = applySavedAdjacentThenC5(wholeOriginal, value)
val repeat = repeatC2(value)
val labelled = labelledC2(value) // Calculates adjacent and repeat again.
```

```kotlin
// Proposed: the snapshot, owner, direction and ports are fixed.
val labelled = admissionPlan.lookup(value)
val adjacent = labelled.family(ADJACENT).initials()
val repeat = labelled.family(REPEAT).initials()
val full = observeSavedAdjacent(value) { exit, original, output ->
    val normalized = normalizeAsExistingBoundary(original, output)
    enclosingPlans.exact(exit, normalized.premise, policy, frozenView)
        .intersect(normalized.facts)
}
```

First compute the labelled C2 result once and derive the unlabelled sets.
Then prepare the C5 input condition once for the fixed complete original.
Keep only rows that can pass that condition. Continue to apply the exact
paired exit restriction and its field budget to each actual output.
Input eligibility alone is not output permission.

The C5 plan key uses the actual normalized complete original, exact exit,
admission policy and frozen view. Preserve the existing normalization and
preimage rules, including NORMAL FLOW EXACT-to-STAR normalization. An
earlier saved-row filter must retain every possible normalized case; it
must not reject a row using only its unnormalized premise.

C2 depends on the provided value and frozen demand view, not the caller's
complete original. Reuse equal C2 queries across different originals in
the same owner batch. A full observation still depends on the original.
Do not cache it by value alone.

```kotlin
data class AdmissionQuery(val view: FrozenViewId, val value: AnnotatedScalar)
data class FullQuery(val scope: BlockScope, val loop: BlockId,
                     val entry: PortId, val exit: PortId,
                     val original: PremiseKey, val value: AnnotatedScalar)
```

These temporary keys live in an owner whose mode, policy and snapshots are
fixed. Include those coordinates explicitly if a cache crosses that scope.

Keep exclusions, layer and protection in the value key unless a proof
establishes that a component is irrelevant. `Facts.equals` alone does not
include protection. Use temporary owner-local work, not a new permanent
raw-fact archive or a new weak-cache manager. Measure distinct complete and
partial query keys before choosing any longer-lived memo.

### Example and trace

```java
Node wrap(Node x) {
    Node n = new Node();
    n.a = x;
    return n;
}
Node scan(Node x) {
    while (again()) x = wrap(x);
    return x;
}
```

For a representative later forward query, assume the saved adjacent
identity is `x.*/FLOW -> ret.*/FLOW`, and the paired enclosing demand is
`P -> ret.a.b.[any]/T`. An applied loop image is
`P -> x.a.b.c.$/T`. These are schematic query annotations, not extracted
Conductor AP rows.

Before, each repeated image and prefix rechecks C2, applies the adjacent
identity, builds a return image and rechecks P against paired demand.
After, equal C2 work is shared, P's entry condition is prepared once, and
native application/C5 examine only relevant rows. The selected fact and
its layer remain unchanged.

### Proof and performance gates

Prove equality of the complete observation: adjacent admission, repeat
admission, enclosing DATA and Targets, layers, exclusions, protection,
scope/ports and Target IDs. Preserve normalization and local/summary cycle
protection. The observer remains a pure query; it grants no mark request
or source permission.

Prove counted-Work completion for batching. Test late callbacks and cases
with no fresh initial or output. Test empty views, ND metadata arms,
backward ZERO, MUST facts and NORMAL FLOW admission from a DEMAND input.
Keep the current observer as the native reference oracle.

Report observations, distinct keys, native rows applied, C2 calls, C5 rows,
prefix trials, allocation and time. The objective is to remove large
categories of query work, not make a trie operation 20% faster. A twofold
iteration improvement is an acceptance target, not an established result.

## 4. Do not build a second rich static row catalog

The heap's frozen-completion builder retains about 1.37 GB before recursive
binding starts. Its main parts are local W/R rows (681 MB), terminal inputs
(368 MB), scoped W/R rows (195 MB), and scoped terminal inputs (111 MB).
The static B bridge part is about 15 MB. Optimize the large attachments.

Current:

```kotlin
for ((exit, summaries) in scopeSummaryStores)
    for ((initial, values) in summaries.demandEdges(FORWARD))
        for (leaf in ops.leaves(values))
            seed(owner, initial.toPattern(), leaf, exit)
// Builder stores rich StaticGuidanceEdge/Pattern sets, then builds indexes.
```

Proposed:

```kotlin
builder.attachSummaries(owner, exit, sealedSummaries.demandReadView())
builder.attachTargets(owner, sealedOutgoingTargets.readView())
builder.addExtraPreExitWrites(owner, compactLostWriteIds)
// Query an existing packed relation, or its compact immutable catalog.
// Materialize only the selected result row, not every logical mark pair.
```

Prefer borrowing the sealed data already required by demand storage.
If a separate index is necessary, index geometry and packed mark labels;
do not first expand all rows into object sets. Keep extra lost/pre-exit and
caller-bound rows when they are absent from common storage. They are not
redundant merely because a normal exit has no matching summary.

For `set(p) { C.f = p; }` called through several wrappers, the common stores
already hold the promoted W rows. Before, the builder copies their endpoint
objects into another catalog. After, it selects the same rows from a sealed
view. Method context, block scope and producer exit remain part of ownership.
Do not replace them with only a common method or a static-field key.

Prove view equality with the existing builder for W, R, B and terminal
queries, including both-layer source views where applicable and the current
DEMAND-only attachment selection. Preserve guidance normalization, real
ZERO, mark-pair correlation, owner visibility, private B and physical ports.
Do not add a new static propagation algorithm or change the run-1 -> run-2
composition rules.

The 1.37 GB observation is not a promised saving. Measure the compact catalog,
borrowed-store retention and final freeze peak. A borrowed view must not keep
the entire actor alive through an accidental callback closure.

## 5. Secondary candidate: prune only observed writes

`KilledStaticWriteStore.freeze` builds all normalized survivors and asks
whether each candidate belongs to them. An exact candidate-directed
membership API can avoid that full enumeration. Empty candidates need no
survivor lookup at all.

The [unselected finite model](../../spec/lean/proposals/candidate-directed-static-pruning-20261103/REPORT.md)
proves ordered result equality under an explicit exact-oracle prerequisite.
It does not prove a Kotlin packed-store oracle or project speedup. The heap
has 1,353 candidates in the interrupted store and does not show a large
current survivor set. Therefore this is not the primary OOM explanation.

Do not call a colored row a survivor merely because FLOW covers it. Match
exactly what the old normalized `all()`/private-B union contains. Preserve
raw observed IDs even when two IDs have the same normalized guidance key.

## 6. Experiment and acceptance plan

Implement only features selected after review, with the required constructive
models and RED/GREEN native controls first. Keep each feature in a separate
commit so its effect can be measured.

Repeat only the same four configurations: FULL, 16 GiB, aliases/statics on,
limits `1,1,2,3,...`, the selected project timeouts and direct
`runProjectAnalyzer`. Reuse f945 and 86ad reports; do not rerun them.

For Thingsboard, measure engine time separately from binding, peak before
and after release, committed heap after GC, builder size, raw input rows,
binding candidates/outputs and the latest complete/accepted run. Completing
the current binding preparation does not prove that later binding or run-2
will fit; test those phases too.

For Conductor and Stirling, compare the same iteration windows and their
demand frontiers. Keep physical packets, local offers, observations, CPU,
GC and allocation in separate units. Do not accept a shorter run that loses
a finding. Capture OOM before cancellation and profile under actual workload.

These proposals do not establish the 60 s run-1 engine target. Thingsboard's
699 s engine remains a separate performance problem. First remove the
observed handoff failure and repeated consumer work; use the resulting
complete runs to choose the next engine or static-lookup change.

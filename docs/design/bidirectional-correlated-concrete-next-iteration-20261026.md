# Reduce redundant work after correlated concrete initials

Date: 27 October 2026. Proposal based on runtime
`fcfe2e90558665d813bd74207832d4ae3fc83aec`, core
`57ca8d4940e8fb52e7eed6151928d4025c7d7ad9`.
The fixed Thingsboard run reaches **run-2**, completes **run-1** and accepts
**run-1**. Conductor and PDF have the same progress. OWASP reaches
**run-9**, completes **run-8** and accepts **run-7**.

The selected optimization is implemented. This document proposes the next
work; it does not authorize another runtime change. Use the [final report](../reports/bidirectional-correlated-concrete-performance-20261026.md)
and its [machine-readable evidence](../reports/bidirectional-correlated-concrete-performance-20261026.json), rather than the superseded candidate,
to rank and test the proposals.

## Priority and semantic scope

| Order | Proposal | Measured target | Contract |
| --- | --- | --- | --- |
| 1 | Replay only newly authorized summaries | 11.43m pending publication entries; at least 8.19m exact duplicate entries on Thingsboard run-2 | Preserve current query admission and semantic observations |
| 2 | Bypass certified unchanged run-1 statement chains | 71.9m pure unchanged scalar callbacks on Thingsboard; 28.6m on OWASP | Preserve the existing transfer and observations |
| 3 | Share run-2 body work through demand guides | 1.50m concrete current queries; no current FLOW method relations in the Thingsboard snapshot | Major admission/publication change; separate selection and proof |
| 4 | Project known static results directly | 20.6m scalar direct-supply leaf callbacks on Thingsboard run-1 | Exact ordered supply equality |
| 5 | Reuse equal payload and protection images | Large whole-mask retained population; repeated pure trie operations | Exact value and annotation-delta equality |

The first proposal has direct evidence of duplicate queued work and a small
exact replacement law. The second targets the largest measured run-1
dispatch population. The third can remove colored body computations but
has a larger semantic and proof scope. No table entry is an end-to-end
speedup or byte-saving prediction.

## 1. Replay only newly authorized summaries

**Current:** when `StrongQueries.admit` returns any new initial, `addLink`
walks every raw summary and queues every summary permitted by the complete
admitted-query set. Already permitted answers are queued again. For selected
pieces, the selected store deduplicates later, but its return delta is ignored when the pending
publication is appended. The final publication index deduplicates only after
the method queue becomes empty.

**Proposed:** backfill a raw answer only when its premise first becomes
authorized. New raw answer deltas keep their normal publication path. Keep
the existing actual-input query policy, guide intersections and static
completion. This proposal does not restore demand-only admission.

The actual Thingsboard run-2 snapshot has 11,428,775 pending entries and
3,242,057 distinct per-actor premise-object/conclusion-object pairs.
Therefore 8,186,718 entries, 71.63%, repeat an exact identity pair. Equivalent
values in different objects are not counted as duplicates. The pending-list
retained union is 807,352,840 bytes. Shared facts can remain reachable from
other stores, so neither 71.63% nor 807 MB is a predicted whole-heap saving.
The census does not attribute every duplicate to this one source path.

Measured `BasePageDataIterable.next()` holds 2,009,360 pending offers for
836,430 identity pairs. `hasNext()` holds 707,139 for 184,069. These are
pending inventories, not historic CPU-operation counts.

Schematic fact handling, independent of the method body's Java code:

```java
Object next() {
    if (!hasNext()) throw new NoSuchElementException();
    return currentItems.get(currentIdx++);
}
```

```text
raw answers:    I1/T1 -> A1, I2/T2 -> A2, I3/T3 -> A3
query arrivals: I1, I2, I3

current:   I1 arrives: queue A1
           I2 arrives: queue A1 again, A2
           I3 arrives: queue A1 again, A2 again, A3
proposed:  queue each newly authorized answer once: A1, then A2, then A3
later change: a new result or protection delta still queues normally
```

Let Q be the previous admitted initial set, F the fresh set returned by
`admit`, and Q' = Q union F. They are disjoint. For a nonzero complete premise
P, current authorization is exactly `members(P) subset Q'`. Therefore:

```text
newlyAuthorized(P) = members(P) intersects F
                    AND members(P) subset Q'
```

This is equivalent to `permitsAfter(P) AND NOT permitsBefore(P)`. It is an
exact finite-set identity. It is not a heuristic based on mark, output shape
or record coverage.

A first general implementation can retain the scan and change only its
predicate:

```kotlin
val wasEmpty = currentQueries.isEmpty
val starts = currentQueries.admit(added, guides)
if (starts.isNotEmpty()) {
    val fresh = starts.toHashSet() // Temporary set for this admitted batch.
    for ((premise, facts) in summaries.all()) {
        val newlyAuthorized = when {
            premise.isZero -> forward && wasEmpty
            else -> premise.anyMember { it in fresh } &&
                    currentQueries.permits(premise) // All members, never one.
        }
        if (newlyAuthorized) queuePublications(premise, facts)
    }
    starts.forEach(::addInitial)
}
```

`isEmpty` and `anyMember` are pseudocode interfaces for the existing set
and complete premise; they need no permanent answered set or new fact
index. Do not deduplicate on ordinary `Facts.equals`, which omits protection.
The optimization changes authorization replay, not annotation-delta admission.

For run-2's proved singleton-premise scope, remove the complete-summary scan
and avoid decoding unrelated summary rows. `RunSummaryStore.borrow` already exists:

```kotlin
// After proving that every run-2 raw premise is an InitialAp.
for (initial in starts) {
    if (initial.isZero) continue
    for (facts in summaries.borrow(initial)) {
        queuePublications(initial, facts)
    }
}
starts.forEach(::addInitial)
```

Consume each borrowed view on its actor before changing the raw store.
Queueing selected output mutates a separate owner. Keep the original
start-after-backfill ordering. For later runs with ND premises, keep the
general transition predicate until a separate complete-premise index is
proved. Several fresh members of one ND premise must cause one replay,
and a partially admitted premise must cause none.

ZERO has two exact cases. In backward runs, `published` already allows
every computed ZERO-premise answer regardless of queries, so query admission
needs no ZERO backfill. In a restricted forward run, ZERO authorization
changes only when the admitted set first becomes nonempty. Keep that one
backfill. This does not create, drop or weaken a source/GEN outcome.

The proof must include the following delivery invariant: every raw delta
computed while its premise is authorized is pending or already delivered;
when authorization first changes, every current raw answer is queued.
Existing publication-index replay supplies late subscribers. If the first
answer is still pending, the existing counted batch must deliver it to
those subscribers after the unchanged method-empty barrier. Replaying an
already authorized raw row is therefore not required for a new caller.
Keep late protection upgrades on the regular raw-delta path.

With n independently admitted queries and n available answers, the current
example has n(n+1)/2 authorization offers. The proposed path has n, plus
legitimate later raw deltas. Direct singleton borrowing avoids repeated
full-row decoding of unrelated summaries. Existing `DiagonalRelations.borrow`
still scans scope headers and filters by initial; no header-index rewrite is
selected. Actual saved CPU, peak memory and time to the
next barrier must be measured; pending identity duplicates are not an
end-to-end performance ablation.

The scan is not just a cheap key test: `FlowBackedSummaries.all()` also
decodes current diagonal rows into scalar per-mark values before the
permission test. Direct borrowing avoids constructing unrelated values.
This is a second source of avoided work, separate from the pending-wrapper
duplicates. The current profile does not give an exact CPU share for this
combined path, so the proposal must measure replay visits, decoded rows,
authorization offers and allocations directly.

Controls: an old-demand-rejected answer becoming newly authorized; repeated
and unrelated queries; a late subscriber before/after flush; backward ZERO;
first and later forward admissions; partial/full ND authorization and two
fresh members in one batch; a late flag with unchanged ordinary content;
and legal tail/E/layer variants. Prove old/new semantic observations and
normal/selected relations equal under fair delivery. Preserve the queue
reservation and report barrier. No new field, source, cleaner, alias, static
or query-admission behavior is selected.

The [standalone constructive model](../../spec/lean/proposals/query-replay/README.md) already checks 24 theorems and 15 executable
controls. Its direct audit covers 37 theorem/pure definitions, with only
`propext` and `Quot.sound`, no Classical choice or `sorry`. It proves the
finite authorization law, unary borrowing, complete ND candidate dedup and
ZERO cases, and keeps late annotations on the regular raw-delta path. Its
cumulative-delivery equivalence is conditional on the pending-or-delivered
invariant; it does not claim that the complete Kotlin engine adapter or a
speedup is proved. Those adapter obligations remain part of implementation.

## 2. Reduce run-1 statement visits for unchanged nonstatic facts

**Current:** `emitUnchanged` avoids `MethodEdgeStore.add`, but it still adds
one scalar work item per successor. `process` acquires the statement form,
calls the interpreter and reaches the same unchanged callback again.

**Proposed:** route a fact to the next relevant method point across a region
which is proved to be an identity for that fact's base. Do not create work
items for the intervening identity points. Keep the same premise, payload,
layer and protection mask.

Thingsboard's diagnostic counts 143,907,111 physical method-edge invocations.
There are 71,897,409 pure unchanged scalar callbacks: 49.96% of that total.
The current stored summary count is only 1,800,397 concrete memberships.
Making the existing store operation faster cannot remove these visits,
because unchanged already bypasses that store operation.

This is the largest measured run-1 operation population that a new
algorithm may avoid. The measured count is an upper bound on eligible
visits, not a bypass proof and not a 2x engine-time prediction. All pure
visits together are near half of physical method-edge invocations; the
remaining call, matching, rule, IR and summary work still costs time.
Excluding ZERO-original work leaves 70,768,235 visits (49.18%). The first
single-successor scope below can cover less than this measured population.

Schematic code under analysis:

```java
void consume(Object p, int n) {
    int a = n + 1;
    int b = a * 2;
    int c = b + 3;
    sink(p);
}
```

```text
fact:       initial p.*/T -> current p.*/T, DEMAND, with its original mask
current:    process arithmetic 1 -> enqueue -> process 2 -> enqueue -> process 3
proposed:   route this same fact directly to the sink call input
ZERO:       keeps control/source processing under the existing policy
```

An eligible point must be a non-call, non-exit point with no source,
conjunction, static operation or fact-dependent observation; the fact base
must be absent from its touched set. A first scope can keep ZERO on the
existing path. Resume sites and diagnostic observer hooks need their own
fallback. A point with an untouched base but a rule is not eligible.

Possible owner API, to refine and prove before implementation. Keep the
existing exit check on the current node and route each actual successor:

```kotlin
fun emitUnchanged(item: EdgeDelta) {
    exitRulesAt(item.premise, item.node, item.facts)
    context.forEachSuccessor(item.node) { successor ->
        enqueueUnchangedThroughRoute(item.copy(node = successor))
    }
}
```

The first scope contracts only certified single-successor chains. Branches,
joins selected as boundaries, cycles, unknown forms and resume/observer
boundaries use the existing handler. Detect a cycle before any queue/store
mutation, then fall back on the original input. Do not recursively route an
unchanged branch-stop without processing it. A later full branching frontier
needs a separate cycle and memory proof.

Do not build a cache for every theoretical node/base pair or retain a
fact/mark-specific route index. Bound and measure structural route metadata
under the method owner, keyed by stable method/context/form/rule view. A
route build or continuation must retain counted work, quanta and cancellation
checks before yields; pending routes cannot create a false queue-empty
barrier. This is analyzer scheduling data, not a change to IR storage.

Required proof: contract each finite identity path to its boundary and
expand each new boundary delivery into an old path. Preserve typed facts,
all rule/static/call/exit observations, required resumptions and the least
fixed point. Prove finite traversal for identity SCCs and fair delivery
across actor yields, ZERO phases and queue-empty request commits. Exact
diagnostic callback counts may change; report/source/sink identities and
rule occurrences must remain valid.

Controls must include branches, loops, field writes, a source or cleaner
on an otherwise untouched base, exception and normal exits, both flag
arrival orders, a dynamic request commit, and cancellation. Count removed
physical visits and route-state bytes, as well as engine time.

## 3. Share backward body work through actual demand guides

**Major admission and publication contract change.** This returns a selected
run-2 scope to the original AP demand-guided algorithm. It is not a small
extension of FLOW-backed storage. The completed run-2 heap census establishes
the current population; a scoped design must determine the eligible share
before selection.

The completed Thingsboard snapshot has 1,501,686 concrete queries and no
current FLOW relations in method-point, raw, selected or publication stores.
Its 77,944 persisted forward NORMAL FLOW memberships are a separate owner.
Thus an all-run coverage implementation cannot compact current backward
TAINT rows when no current FLOW witness is produced. Query identities retain
only 77.5 MB; the proposal targets their induced body work, rather than
claiming that removing the query set alone fixes memory.

Conductor has 744,646 concrete queries, 88.17% static, including 323,335
named-field ANY and 323,796 named-field EXACT queries. Its static completion
exception is therefore central. Simply adding ordinary abstract guides
while keeping all actual static starts can perform both computations.
Retaining the current group-valued static completion does not prove shared
FLOW execution for these queries. A different static FLOW-guidance policy
would be another explicit major design with a mark-demand and strong-update
proof. Do not include that policy silently in this proposal or predict a
Conductor memory reduction from nonstatic sharing.

**Current:** `StrongQueries.admit` starts concrete queries from actual marked
inputs even without a matching old demand. It discards abstract guide
entries when choosing guide-based starts. A current-query permission then
publishes raw summaries and can backfill them when another query arrives.
Applying a persistent FLOW record does not close that separate query.

**Proposed:** emit method initials from complete old demand entries, including
FLOW entries; retain marked initials at marked barriers. Instantiate shared
FLOW answers against actual caller marks in the existing subscriptions.
Restrict publication by the complete entry/exit demand pair. Keep the
balanced ZERO control path and the selected static completion exception.

```kotlin
// Current conceptual path.
for (actual in incomingMarkedFacts) {
    start(canonicalConcreteQuery(actual)) // Not conditional on an old guide.
}
publish(raw, if (currentQueries.permits(raw.premise)) UNRESTRICTED else OLD_DEMAND)

// Proposed run-2 path.
for (guide in demand.near(method, actual)) {
    for (initial in ops.emit(guide.entry, actual)) startOnce(initial)
}
for (guide in demand.matchingCompletePairs(raw.premise)) {
    restrictWholePremise(raw, guide)?.let(::publish)
}
```

```java
Object identity(Object p) { return p; }
// Callers need the same returned geometry with T1, ..., Tk.
```

```text
current:    k concrete originals traverse the neutral callee and its calls
proposed:   one demanded FLOW original traverses the body;
            caller subscriptions instantiate each necessary Ti result
barrier:    CM(Ti), cross-mark assignment or protected dependency retains
            its concrete demand and required colored body work
```

This can remove a factor k from the eligible neutral callee-body computation.
It does not remove the marked caller answers or all N2 input state.

Do not substitute this unsafe shortcut:

```text
some persistent FLOW record covers the incoming T region -> skip the query
```

A record is one relation, not a complete method answer. For
`if (b) return p; else return p.f;`, an identity record can cover the input
while another demanded branch still needs a result. Execute the complete
shared guide, not one convenient stored record.

Required proof scope: original AP C2 emission and C5 whole-premise
restriction; native/reversed NORMAL record replay with legal E; K6 mark
transport; inherited protection and restored-atom cycles; positive input
alias closure; balanced ZERO/source and sink-seed behavior; and explicit
same-field FULL static query completion. The implicit static group pair
can still require individual FULL static queries and must remain valid.
Later forward ND restriction is a separate major scope: the current
per-member fallback is not a proof of whole-ND C5. A first implementation
should isolate run-2 rather than silently change all later runs.

## 4. Remove scalar replay when projecting a known static result

**Current:** a known named-static STAR premise constructs its canonical
input, decodes every result leaf and applies that leaf as a summary to the
same input, then limits and projects the output into static pool supplies.

**Proposed:** after the existing known-input, runtime-atom and bounded-result
gates, project the complete result directly. The ordered supply list is
equal. Writer registration, requests and emitted demand relations stay on
their current paths.

```kotlin
if (hasKnownStaticGroupInput(premise)) {
    if (premise.tail == STAR) {
        staticBatch.supplies += staticSlices(value)
    } else {
        oldKnownInputProjection(premise, value)
    }
}
```

Schematic method relation:

```text
known initial: C.f.*/T
bounded result: C.g.[any]/U, DEMAND, Empty E
current: self-match C.f.*/T, apply one scalar T->U relation, limit, project C.g/U
new:     project the already computed C.g/U result directly
```

The final Thingsboard run records 20,605,072 direct-supply leaf callbacks,
within 20,772,547 total static supply offers. There are 745,024 fresh
memberships within temporary batches, summed across batch commits. This is
not a count of globally fresh pool memberships. Direct projection removes
per-leaf AP composition; it does not claim to remove all offered or fresh
memberships. Existing temporary pool merging and three-set request handling
remain in force.

Prove ordered `RegionGroups` list equality for same/cross output atoms,
STAR/ANY/EXACT/must results and mixed output trees. Keep the exact-class
fallback: an EXACT class initial with a nonexact STAR target currently
fails the S8 check; the new path must not turn that failure into a supply.
Known-input support remains mandatory. An arbitrary symbolic nonstatic
writer is not an unconditional static pool supply.

## 5. Compute equal payload and protection images once

**Current:** AP transfer, summary application and scalar admission can walk
ordinary output and protection output separately even when both inputs
denote the same complete tree. Interning can then retain two structurally
equal roots.

**Proposed:** when equality is already proved, compute one pure image and
use its post-interner root as both payload and mask. Partial-mask cases
keep the existing path. Preserve every emitted protection delta.

```text
whole offered input + all relevant stored rows whole:
  subtract(ordinary, ordinary rows) = subtract(mask, mask rows)
  -> compute once, reuse as ordinary residual and mask
```

The final Thingsboard diagnostic has 1,720,875 memberships in whole-mask
trees with different root identities, versus only 61 in identity-shared
whole trees. This is a stored eligibility population, not the joint
frequency of the scalar subtraction guard. Runtime identity-only counters
are lower bounds and are small; retaining equality through constructors
and interning is part of this proposal. Do not add structural comparisons
to every hot call simply to discover fullness.

The run-2 snapshot has only 227 protected method-point memberships and
74 protected raw/selected summary memberships. Run-1's high protected share
does not show that whole-mask reuse can remove run-2's normalization hotspot.
Offered/transient masks need their own operation measurements.

The eligible subtraction/image kernel removes one of two equal walks. A
global 2x speedup is not established. Prove equality of old/new stored values
and metadata deltas, including late flag upgrades, ANY coverage of STAR
siblings, mixed exact leaves and E merge canonicalization. `TaintGroup`'s
emitted whole residual is not always just its ordinary merge delta. Use
the exact residual law, not a guessed delta shortcut.

## 6. Correctness follow-up for Spring findings

The performance proposal must not hide the nine native-main PDF misses.
The same-core catalog control reproduces them before any bidirectional
core change. Current root/array-element response guards omit marked Map
values and DTO descendants which the native starred guard accepts. Two
marked return sites also need precise exporter/witness review. Keep these
as a separate catalog/export correctness proposal and preserve controller
annotation handling. A ZERO-only exit restriction remains out of scope.

## Evidence and completion gates

The ordering uses the completed actual run-2 heap census and fresh before/
after run-1 classification. The proposals are source-audited opportunities,
not measured ablations. Do not rank a cross-header adapter rewrite as a primary
fix: it has only 0.246% of sampled Thingsboard run-1 CPU and no sampled run-2
stack in the selected prefix.

For each selected change, first add constructive Lean models and controls
under `spec/proof-guide.md`. State each major semantic difference before
implementation. Preserve field bounds and grammar, exclusion/layer laws,
source and cleaner behavior, static request/demand completion, mark identity,
IR storage and cache-manager ownership unless a separate major change is
explicitly selected.

Repeat the exact four fixed project commands after implementation. Include
native-main finding identity/strict-location comparison, each iteration time
and status, latest reached/completed/accepted run, profiles and actual guard
heap diagnosis. Repeat the joined run-1 subsumed/protected/other shape
investigation with complete representative FLOW witnesses. Keep diagnostic
and timed invocations separate. Do not add unrelated flags or experiments
to explain a failed gate.

The [run-1 shape census](../reports/bidirectional-correlated-concrete-run1-shapes-20261026.md) and [work comparison](../reports/bidirectional-correlated-concrete-run1-work-20261026.md) preserve before/after invocation and unit boundaries. The [proposal proof receipt](../../spec/lean/proposals/query-replay/checks.json) records the finite replay model controls. Run `python3 spec/lean/proposals/query-replay/check.py` from the repository root to repeat that check without a JVM.

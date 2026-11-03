# Demand output selection and static writer binding: next iteration

3 November 2026. Design proposal only. No change in this document is implemented.
Base: `e558b496acf82de6ff136325d58f3d90ee5b8559`.

The [current performance report](../reports/bidirectional-joined-state-loop-consumers-packed-guidance-performance-20261103.md)
and its linked repository data are the measurement source. The latest reached,
completed and accepted runs are:

| Project | Reached | Completed | Accepted forward report |
| --- | --- | --- | --- |
| OWASP | run-5 | run-5 | run-5 |
| Conductor | run-6 | run-5 | run-5 |
| Thingsboard | run-1 | None | None |
| Stirling-PDF | run-8 | run-7 | run-7 |

## 1. Selected scope and rank

These proposals remove repeated work. They do not change AP transfer, initial
admission, demand-relative field budgets, mark identity, subsumption protection,
Target rules, physical block ports, aliases, or source permissions. They do not
add a new static propagation policy. GROUP-mode known issues stay out of scope.
There is no proposed major semantic change in points 1–3.

| Rank | Proposal | Current behavior | New behavior | Expected effect and limit |
| --- | --- | --- | --- | --- |
| 1 | Select C5 outputs from the prepared plan | Every result scans the method-wide output index, creates an ID set, then scans its cached entry plan | Search only the plan's eligible exit rows; reuse output candidate selection for repeated geometry | Removes irrelevant row enumeration and repeated temporary ID joins; strongest evidence in Conductor run-6 and Stirling run-8 |
| 2 | Match joined static inputs once per complete premise | Each static writer output repeats caller/local candidate selection and full AP matching | Reuse the same exact selected inputs for all outputs with the same owner and complete premise | Removes repeated input joins during Thingsboard static completion; repeated-key frequency is not yet measured |
| 3 | Omit pure saved observer replay with an empty output plan | Reverse and MUST records still run AP application even when that output base has no accepted C5 row | Use the existing empty-plan proof for these additional closed DATA cases | Removes whole saved AP applications; applicability frequency must be measured before an impact claim |

Rank 1 has measured repeated allocation and intersection work. Rank 2 targets
the stage that prevents Thingsboard from finishing run-1. Rank 3 has a narrower
proof and less certain workload coverage. These ranks are not predicted speed
ratios. Do not promise a twofold whole-run gain from sample shares.

Before implementation, create a complete implementation spec and finite Lean
models under [proof-guide.md](../../spec/proof-guide.md). Then use native oracle
tests. The equations below state the required equivalence; they are not new
kernel-checked models. Do not implement an unselected behavior to close a proof.

## 2. Select C5 outputs from the prepared plan

### Evidence

Conductor's partial run-6 has 79,421 Java samples. Loop observation accounts
for 94.28%; C5 accounts for 75.12% of observer samples. A prepared-plan lambda
which inserts output demand IDs into a new `HashSet` accounts for 36.31% of all
sampled allocation weight. This is churn, not retained memory.

Fine classification puts output-path index selection at 31.15% of all Java
samples in Conductor run-6, versus 2.88% for entry preparation and lookup.
The output-path stage is 28.76% in Stirling run-8. Outer callback frames are
excluded from this classification; these are not inclusive protection costs.
The [fine CPU data](../reports/data/bidirectional-joined-state-query-fine-cpu-20261103.json)
includes the classifier and exact window totals.

Stirling's partial run-8 has C5 at 66.87% of observer samples. The same ID-set
site accounts for 23.98% of all sampled allocation weight. Its completed run-7
still attempts 502.471 million C5 rows, despite a 99.972% C5 memo hit rate.

Current source:
`DemandStore.prepareLocalDataPlan`, its returned `intersect`, and
`DemandStore.offerDataPair`. The entry plan cache works; the output query is
still built for every result.

```kotlin
// Current outline. local.byExit contains every row for this owner.
val outputIds = HashSet<Int>()
for (leaf in ops.leaves(raw))
    local.byExit.visitAround(leaf.base, leaf.path) { outputIds += it }
for (row in preparedRows) {
    if (row.id in outputIds)
        offerDataPair(row.ticket, row.pair, raw)
}
```

### Proposed organization

Keep the same immutable demand rows. Build an output index over the eligible
rows of this exact plan. A row with a null entry ticket cannot emit a result.
Do not give it an output posting. Keep original plan ordinals so selected
rows can run in the existing order.

```kotlin
class OutputPlan(
    val originalTemplates: List<Pattern>,
    val rows: List<PlannedRow>,
    val byOutput: PathTrie<Int>, // plan ordinals, not method-wide IDs
) {
    fun candidates(raw: Facts): IntArray {
        // Same path-neighborhood operation as current byExit.
        // Use a primitive ordinal scratch set. Return sorted plan ordinals.
        // A repeated geometry can reuse this array within the bounded owner quantum.
    }

    fun intersect(original: PremiseKey, raw: Facts): List<Facts>? {
        if (!sameSupportedContext(original, raw)) return null // native fallback
        val result = ExactDemandResults(ap)
        for (ordinal in candidates(raw)) {
            val row = rows[ordinal]
            offerDataPair(row.ticket, row.pair, raw, result)
        }
        return result.all()
    }
}
```

The candidate cache stores row ordinals, not intersected Facts. A geometry-only
cache must remain a conservative candidate selector. It must not reuse a
final result across marks, exclusions, layers or protection masks. Include
the complete owner/scope/exit and immutable plan identity in its ownership.
Use the current bounded quantum lifetime. A large or unsupported query must
use native C5. Do not add a second global demand store.

An optional second selector can reject incompatible marks before AP work.
Its predicate must be exactly the current `marksMeet`, including FLOW mark
exclusions and catalog group coverage. It must never narrow a FLOW row to
only one arbitrary concrete mark. The current campaign does not count
wrong-mark rejects separately, so this extension is not a measured saving yet.

### Example

```java
Node B(Node p) {
    while (again()) p = p.next;
    return p;
}
// At a loop observation:
// enclosing original: p.f.*/T
// saved AL result:     ret.f.$/T
// eligible plan exit: ret.[any]/T
// other owner rows:   q.*/U -> ret.[any]/U; q.*/U -> tmp.[any]/U
```

Before: every offered result enumerates owner-wide exit IDs near `ret.f`,
including the q-to-ret row whose entry this plan already rejected. The
existing base index already skips the q-to-tmp row. It creates a new
ID set and scans all plan rows. It then runs the exact AP restriction.

After: search the plan's `ret` geometry directly. Check only the selected
eligible ordinals, in the same order. Run the same ticket restriction and
the same row-specific `FL(exit demand)+1` cut. The accepted facts and their
protection remain identical. Nearby T/U rows can still be candidates until
the exact mark check rejects them.

### Equivalence and tests

Let `E` be the prepared row list, including repeated ordinals for ND members.
Let `around(r,F)` be the current output-index neighborhood predicate.
The old effective set is:

```text
{ r in E | around(r,F) and ticket(r) is not null }
```

The new index must return exactly that set, or a superset filtered by the
same final tests. Null tickets produce no output. Replaying surviving rows
in the same ordinal order and using the same exact restriction and cut gives
the same result list. This proof depends on complete paired rows: entry
permission from one row must never combine with another row's exit budget.

Native controls must cover multiple leaves, ancestor/descendant paths, empty
answers, same geometry with different marks, FLOW exclusions, concrete MUST,
full protection upgrades, multiple ND members, scope/exit isolation, row order
and capacity fallbacks. ZERO, Target and static-completion cases keep native
handling. Compare exact results with current C5 on every generated finite case.

Work counters and diagnostic samples can decrease because rejected rows are
not visited. State that change explicitly. Semantic observations, exact facts,
report identities and source permissions must not change.

## 3. Match joined static inputs once per complete premise

### Evidence and current pipeline

Thingsboard's run-1 engine takes 686.278 s. Static completion consumes another
240.471 s and times out. Of 16,759 Java samples in that completion window,
98.28% include `OwnedJoinedStaticWriterBinding.complete`; 85.98% include its
caller-input visit. Full AP satisfying selection is 46.02% and summary
application is 23.72%, as overlapping inclusive shares.

This stage binds actual input packets through primitive writer relations.
Run-1 does not relay ordinary static facts through the call chain. That does
not remove this joined operation: a relation such as `p/T -> C.f/T` must still
be bound to the caller's actual `p` input to create caller-owned guidance.

The source already indexes physical caller candidates. It does not scan every
caller in the project. Local inputs use their moved directory. Both paths
repeat the full premise selection for each distinct output writer.

```kotlin
for (writer in writerQueue) {
    val row = keys.row(writer.id)
    borrow(writer.owner, Publication(row.original, row.result)) { input ->
        val actual = ops.satisfying(input.actual, row.original, mode)
        if (actual != null) applyThisWriter(row, input, actual)
    }
}
```

`CalleeSubscriptions.visitJoinedCandidates` uses `pub.premise`, not its result.
All borrowed inputs are fixed after join. Thus the matching result can be
shared across writer outputs with the same complete premise.

### Proposed operation

```kotlin
data class SelectionKey(val owner: OwnedScope, val premise: InitialAp)
data class SelectedInput(val input: OwnedWriterInput, val matched: Facts)

fun process(writer: Writer) {
    val row = keys.row(writer.id)
    val selected = selectionFor(SelectionKey(writer.owner, row.original)) {
        // Same borrow order and same per-input-key/group duplicate filter.
        // Same ZERO/source-authority and zeroOnly checks.
        // Same complete ops.satisfying, including raw FLOW mx.
        selectNativeInputs(writer.owner, row.original)
    }
    for (input in selected) applyThisWriter(row, input.input, input.matched)
}
```

Keep the existing writer queue, exact raw writer IDs, `onBound` order and
parent offers. A match cache entry is valid only inside this joined phase,
before its input lease closes. It cannot capture an actor or survive into
the frozen completion. Use a bounded cache with native recomputation on
eviction. An empty exact selection is a cacheable answer. Do not merge
different caller links or choose one representative packet.

The key includes owner MethodKey, BlockScope and the entire raw InitialAp:
base, path, tail, full mark and its legal exclusion state. A FLOW initial
cannot carry mark exclusions. The selected input retains its own complete
Facts, including mx, protection, original, key, group, layer and `zeroOnly`.
Writer outputs with different raw mx can share this premise selection, but
each must apply its own unchanged raw output mx. Guidance normalization must
not merge the distinct raw writer IDs or their applications.
An arbitrary reached ZERO packet remains insufficient source authority.

### Example

```java
void set(Node p) {
    C.a = p;
    C.b = p;
    C.c = p;
}
// Writer rows under the same owner:
// p.*/FLOW -> C.a.*/FLOW
// p.*/FLOW -> C.b.*/FLOW
// p.*/FLOW -> C.c.*/FLOW
// One actual caller input: q.g.$/T, mapped to p.g.$/T.
```

Before: the same indexed input selection and full `satisfying(p.*/FLOW)`
run three times. Each output then applies its distinct writer relation.

After: select that exact caller packet once. Apply the three distinct
relations in their original writer order. Produce the same parent-owned
`q -> C.a`, `q -> C.b` and `q -> C.c` guidance. No alias suffix, request,
static pool supply or new writer registration is introduced.

### Equivalence and acceptance

For fixed owner `o`, raw premise `P` and joined input directory `I`, define
`select(o,P,I)` as the old ordered, deduplicated sequence of matching inputs
and their exact satisfying projections. `I` and AP mode cannot change during
binding. The borrow selector depends on `o` and `P`; it does not depend on the
writer result. Reusing this sequence therefore gives each writer the same
ordered arguments as before. Unchanged writer order and application produce
the same bound rows and parent queue.

Prove this for both moved local inputs and physical caller inputs. Verify
ZERO/zeroOnly, saved-only local links, cross-scope isolation, mixed marks,
raw mx, duplicate keys, all real ports, protection and cancellation cleanup.
Compare exact ordered binding rows with the old joined binder. Cache eviction
must change work only. Do not retain matched Facts after the lease closes.

Measure distinct complete selection keys, repeat counts, candidate visits,
matches and application outputs. Current samples prove matching is expensive;
they do not prove how many exact selections repeat. If repeats are rare, this
proposal must not be sold as the Thingsboard solution.

## 4. Extend the pure observer empty-DATA shortcut

The selected patch skips supported direct saved applications when the prepared
output plan is empty for their output base. Reverse and MUST applications use
the native path. They can still do complete AP work before C5 returns empty.

The extension is for the pure observer only. Actual persisted-summary replay,
live delivery and separate saved Target evaluation keep their current paths.

```kotlin
val outputBase = if (record.reversed) record.premise.base
                 else record.conclusion.base
if (supportedDataRecord(record, original) &&
    plan != null && plan.emptyForBase(outputBase)) {
    // Do not apply this DATA record merely to discover its rejection.
    return
}
applySavedRecordAsNow()
```

Keep all current supported-context checks: run at least 3, no static completion
or carry, non-root enclosing owner, non-ZERO original and record endpoints,
known DATA output base and exact prepared scope/exit plan. A reverse record's
output base is its premise base. Its view must not be mistaken for a direct
record. MUST view demotion changes a layer; it must not change the output base.

### Example

```java
Node AL(Node x) { return x; }
// Saved forward relation: x.*/FLOW -> ret.*/FLOW, NORMAL.
// Reverse observer offers: ret.f.$/T -> x.f.$/T.
// Exact enclosing plan: no eligible row with output base x.
```

Before: reverse the record, perform AP application and protection transport,
then run C5 and get no accepted DATA result.

After: the same exact empty-base test proves rejection before AP application.
Separate Target handling still runs. No raw or admitted edge is added or
removed from actual analysis.

Proof obligation: every result of the supported application has the derived
output base, or there is no result. There is no synthesized unchanged result,
Reach or Target. Its plan accepts no DATA result on that base. The composition
of application with C5 is therefore empty. Do not apply this proof to reverse
ZERO source records: they can create DemandTarget. Such records stay excluded.

Add native controls for reversed direct/MUST views, unmatched residual lanes,
empty results, protection, source/Target exclusions and live replay unchanged.
Count the newly skipped reverse/MUST records in real runs. The current zero
skip count for dominant `decodeMimeHeader` is motivation to inspect these
cells, not proof that this extension will skip them.

## 5. Deferred opportunities and separate correctness work

Candidate-directed static survivor pruning can replace a full survivor set
with matching only observed candidate keys. It is exact when normalized key
equality, both layers, private B, raw ID order and all scopes are preserved.
An empty candidate set can return before survivor enumeration. However,
Thingsboard's measured completion cost is writer binding, so this is not the
first static proposal now. The stronger native membership query needs a
separate complete design; `borrow(rawOriginal)` is not a sufficient oracle.

`BlockSummaryLinks.publish` can also test fresh rows against all standing
inputs. An inverse input selector could remove impossible local pairs. Use
this only if fine profiles show a material candidate scan. The current B4
current-delivery share alone does not prove the entire share is that scan.

The [Stirling receiver-reset defect](../reports/bidirectional-stirling-command-receiver-reset-20261103.md)
is separate correctness work. A fix can change source/cleaner semantics and
report identities. It needs its own selected spec and proofs. It is not an
optimization hidden inside points 1–3.

## 6. Measurement and quality gates

Repeat only the selected FULL/16 GiB configurations after implementation.
Reuse f945 and the saved current report; never rerun the fixed baseline.
Capture run markers, frontiers, CPU samples, allocation weights and OOM
snapshots under the same contract. Always report reached/completed/accepted
run labels. Do not compare two partial timeout durations as a speed ratio.

For C5, count owner-wide output IDs visited, eligible plan rows, selected row
ordinals, null-ticket rejects avoided, candidate-cache hits, exact AP calls
and admitted results. Preserve full field/mark/protection results against the
native oracle. For joined binding, count exact selection reuse separately
from distinct writer applications. For observer skipping, count direct,
reverse and MUST cells separately and verify no actual replay is skipped.

Conductor B4 receives 6.62% more demand after current run-3 than in 050b and
performs more work. Current artifacts do not establish its unique upstream
first difference. Add bounded same-input optimized/native C2/C5 comparisons
and stable per-scope frontier signatures, before interpreting a timing change
as pure overhead. Include protection in comparison keys. Do not add another
unbounded transient history.

Accept a performance claim only with both workload and CPU evidence. Exact
finding identities must remain equal to the current accepted snapshots.
Keep the three pre-existing Stirling strict gaps visible. Thingsboard needs
an accepted run-1 report before its no-FN gate can be assessed. A timeout-to-
timeout timing change alone is not success.

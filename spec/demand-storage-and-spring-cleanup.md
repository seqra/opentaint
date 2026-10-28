# Demand storage and the Spring cleanup summary

Date: 28 October 2026. Status: design proposal. Runtime code is unchanged.

This proposal selects two changes:

1. Replace the generated Spring registry save/cleanup/restore block with a
   predefined cleanup summary.
2. Put restricted-run initial admission and summary restriction behind one
   demand-storage API. Use separate entry and paired views. Resolve skipped
   run-1 static relations only when a query can use them.

The base contract is [restricted-demand-static-closure.md](restricted-demand-static-closure.md),
with the AP rules in [ap.md](ap.md). Follow [proof-guide.md](proof-guide.md).
The measured runtime is `53991b7483b062b0287152130cbbbfc87623093b`.
The [measurement report](../docs/reports/bidirectional-restricted-demand-performance-20261028.md)
has these latest results:

| Project | Reached | Completed | Accepted forward |
|---|---|---|---|
| OWASP | run-12 | run-11 | run-11 |
| conductor | run-4 | run-3 | run-3 |
| thingsboard | run-2 | run-1 | run-1 |
| Stirling-PDF | run-5 | run-4 | run-3 |

Thingsboard run-2 spends 64.34% of Java execution samples in `DemandStore.near`.
Stirling run-5 has 9,611,483 named-static-field TAINT headers, with many large
dispatcher point stores. The registry-field share of that population is not
yet measured. These observations justify the two designs; they do not prove
a speedup before implementation.

## 1. Selected semantic scope

| Part | Current behavior | Proposed behavior | Contract |
|---|---|---|---|
| Generated Spring cleanup | Save every registry static to a local, clear statics, restore every saved static | Apply a complete predefined static summary that preserves the registry | New model of the generated method; prove its concrete block effect |
| Cleanup static default | An empty body or unresolved call can admit a broad identity unless its cleaner removes it | No broad static identity. The predefined model is the complete static return relation | Required part of the new model |
| Restricted initial admission | Actor obtains paired demand candidates, then uses only each entry | Demand storage returns the same initial set from an entry view | Original AP C2; representation and work change only |
| Restricted summary publication | Actor obtains paired candidates and applies AP restriction | Demand storage applies the same paired restriction and returns the result | Original AP C5; no relaxation |
| Skipped run-1 statics | Both lookups can walk full paired closure | Entry-only traversal for C2; paired traversal for C5; skip virtual lookup when endpoint indexes prove it irrelevant | Same virtual demand relation |
| Lookup order and C2 search | A lookup can start shared traversal before all local results are known | Check direct local rows, then local composition, then visible callee rows. For a FLOW reader, use bidirectional compatible-mark existence search | Same exact C2/C5 results; complete result coverage can stop search |
| Predefined method boundary | Ordinary body analysis can evaluate method entry/exit rules | A predefined model is complete; analyze no body and skip its method entry/exit rules | Explicit user-selected semantic change; call-site rules remain |
| Run transition | Persist native records; build the next demand snapshot | Keep that order. Fill and seal the new storage during the transition | Existing behavior |

The Spring model is a selected semantic boundary. It must not be hidden in
a cache or a demand index. The intended concrete effect is unchanged, but
the model can remove artificial intermediate DEMAND edges and diagnostic
callbacks from the generated block. Do not claim equal internal edge counts.

Predefined methods also skip configured method entry and exit rules. This is
an explicit selected behavior, not an optimization-equivalence claim. A generic
exit sink on cleanup can therefore stop reporting there. Keep call-site rules
and all controller rules. Do not retain a ZERO-only analyzer or add a boundary
observer for a predefined method.

Keep the following mechanisms unchanged:

- Run-1 mark mode, field transfer and field limits; all-run FLOW subsumption.
- Actual-input mark gates, concrete STAR grammar, E and mark exclusions.
- Source, sink, cleaner and controller-annotation behavior outside generated cleanup.
- Immediate static write supply, summary processing and original caller binding.
- The original backward-ZERO seed-return route.
- Native-record persistence and the demand-selection rule.
- Alias closure, rule occurrence identities and complete method contexts.

Do not add StrongQueries, grounding support, a new weak cache, a new static
order approximation, or a stopping rule that can omit a result. Exact
result-coverage stopping is specified below. The writer-replay optimization
from the previous proposal is not selected by this document. IR storage is
outside the scope. Generated Spring instruction removal is inside the scope.

## 2. Terms

`S` is the static base. `R` is the reserved generated class
`__spring_registry__`. `S.R.*` is a FLOW summary schema for registry fields
and their descendants. It is not a new concrete class-wide taint fact.

`E` is a field exclusion. `mx` is a FLOW mark exclusion. `T` and `U` are
concrete marks or existing GROUP selectors, as permitted by the run.

A demand pair is `(D_c, D_p)`. `D_c` is an entry into the next run's method;
`D_p` is its paired output requirement. `D_p` can be absent. For example,
a forward relation `p -> ret` gives the next backward demand `(ret, p)`.

For run-1 static completion, use the existing frozen seed families:

```text
W: ordinary or genuine ZERO -> static
B: static -> static
R: static -> ordinary
```

The letter R in this seed list means reader, not the registry class.
W/R attachments have complete `MethodKey` owners. B rows share geometry and
mark relations; their visibility uses the detached prescan call graph.

## 3. Predefined Spring cleanup

### 3.1 Complete summary

The registered generated cleanup method has this model:

```text
ZERO -> ZERO                         NORMAL control
S.__spring_registry__.* ->
    S.__spring_registry__.*          NORMAL FLOW schema

No S.* -> S.* schema.
No other static return relation.
```

The schema is independent of a full mark inventory. Apply it with ordinary
AP summary matching. Preserve admitted field paths, marks, exclusions and
protection data. A NORMAL model does not erase a DEMAND layer on its input.
The existing run-1 static result policy still produces DEMAND results.
For a broad FLOW input, registry projection must use the existing admitted
descent and exclusion-rebasing rules. Do not copy an ancestor E onto a deeper
field or clear a field's own E.

In later runs, a nonregistry static requirement cannot cross cleanup.
A registry requirement crosses with the same mark and location. Use the
same identity relation in both directions; do not reverse it into a broad
static identity.

```java
Registry.bean = taintedBean;
C.temp = taintedValue;
__cleanup__();
use(Registry.bean); // may still be tainted
use(C.temp);        // no incoming taint survives cleanup
```

Caller-local facts use the existing caller-local unchanged path. They are
not static returns from cleanup. The cleanup method has no parameters and
no returned value. The separate ZERO relation preserves normal control.

### 3.2 Generated code: before and after

Current code in every dispatcher:

```java
savedA = Registry.componentA;
savedB = Registry.componentB;
// ... all registry fields ...
__cleanup__();
Registry.componentA = savedA;
Registry.componentB = savedB;
```

Proposed code:

```java
__cleanup__(); // predefined complete static summary
```

Remove both directions of the temporary assignments. Remove the blanket
`SpringGeneratedMethod.callCleaners` entry for this model. Remove the
dynamic `SpringRuleProvider` cleaner for this model. Do not leave a second
cleaner that kills the registry after the identity summary is applied.

Keep registry initialization, controller calls, dispatch choices, loops and
normal returns. Keep controller source and exit rules. This proposal does
not move controller checks into a synthetic entrypoint.

The reserved registry class is not a class used for a synthetic EXACT mark
position. Well-formed concrete registry facts name registry fields. The
class-scoped FLOW schema does not relax concrete initial-fact validation.

### 3.3 Provider and engine boundary

Introduce a predefined-summary provider. Match the actual registered
generated method identity, not an arbitrary method with the same name.
The following types are proposal pseudocode:

```kotlin
class CompleteMethodSummary(
    val normal: List<SummarySchema>,
    val exceptional: List<SummarySchema>,
    val touched: Set<AccessPathBase>,
)

fun springSummary(method: CommonMethod): CompleteMethodSummary? =
    if (method === springContext.generatedCleanupMethod)
        CompleteMethodSummary(
            normal = listOf(ZeroIdentity, prefixFlowIdentity(STATIC, registryClassPath)),
            exceptional = emptyList(),
            touched = setOf(STATIC),
        )
    else null
```

The provider recognizes the actual registered method identity. Descriptor
presence means that the body model is always complete. There is no completeness
flag or partial-model mode. A missing matching static schema means no static
result. It must not mean unresolved, unknown or identity.
Disable broad static defaults and static unchanged bypasses for this call.
The prescan and call planner must know this static effect even though the
generated body now contains no static assignments or cleaner rule.

Execute matching schemas through the existing summary-result path. Retain
ordinary AP application, layer handling and caller result restriction.
Do not register a local writer or a static-pool read for a schema. A summary
application is not a write micro-edge. Existing computed-result supply is
separate and keeps its current policy.

The predefined relation is a trusted method model, not an inferred answer
admitted by StrongQueries. It does not start a class-shaped method initial.
Keep ordinary inferred summaries under C5. Keep the resulting caller edge
under ordinary caller restriction. The exact catalog-to-publication adapter
must be proved before implementation.

Use a predefined stage instead of the callee-body stage:

```kotlin
Predefined(ADDED, RETURNED, cleanupMethod, completeCleanupModel)
// No Callees stage, method analyzer, subscription or boundary-rule lane for this target.
```

Use a transient prefix identity or a proved pure subtree selector on actual
`Facts`. It must not construct a class-shaped `InitialAp`. Route its result
through the known-summary result lane, not a statement micro-edge callback
that drops a non-write run-1 static result. Keep STATIC in the call's touched
bases in both directions, so an ordinary pass-over lane cannot undo the kill.

Keep the cleanup call. Create no cleanup method analyzer, including a ZERO-only
analyzer. Apply control and registry identity in the caller's defined-summary
lane. Skip the modeled method's entry/exit source and sink rules. Keep the
common call-site rule stages around the model and the ordinary caller's own
exit rules. This replaces the earlier ZERO-actor proposal. Generic cleanup
boundary observations are deliberately removed; no equivalence proof for
those observations is required or claimed.

ZERO satisfies only the control relation here. The run-1 rule that activates
static reader summaries from ZERO must not fabricate a registry fact from
this identity schema. This model is not a static read operation.
For a complete predefined model without a ZERO return row, the call's fast
unchanged lane and internal source-stage ZERO identities cannot fabricate
return control. Keep the existing conservative control policy for ordinary
analyzed/unresolved targets. Cleanup has an explicit ZERO row.

Do not publish the registry identity to every transitive caller in run-1.
It is used at the cleanup call. The shared run-1-to-run-2 static-carry demand
is admission guidance, not an executable summary. It cannot override the
complete cleanup relation in run-2.

The run-1 static pool remains conservative. Removing the generated restore
writes must not remove real initialization or application write supplies.
The pool can still yield run-1 candidates after cleanup. Later propagation
must use the complete cleanup model to reject an invalid nonregistry flow.

Do not break the legacy analyzer when changing shared Spring generation.
Either implement the same predefined contract in both engines, or keep the
current generated block and cleaners for the legacy path. Never select the
new block while an engine still lacks the predefined model.
The existing `options.common.ifdsBidirectional` choice is available before
Spring generation; it can select these two generation paths. This does not
need a new measurement flag. Keep the model descriptor outside existing
method/rule equality and hashing keys.

Prescan also skips the modeled body and its method-boundary rule relevance.
Record its resolved target in metadata without a summary subscription.
Preserve the existing prescan control/type-information propagation so lambda
resolution and the exported call graph do not shrink accidentally. This is
not a broad static taint summary. The implementation proposal specifies the
separate graph-export adapter.

For K registry fields and D generated cleanup sites, the new generation
removes exactly `2*K*D` save/restore assignment instructions. It also removes
their temporary facts and read/write registrations. The cleanup call remains.
This is a count of removed instructions, not an equal bound on saved runtime.

## 4. Demand-storage lifecycle

The storage is one immutable logical snapshot for one restricted run.
It is filled during the previous run's successful transition. Queries do
not add demand, publish summaries, send requests or change the static pool.
This is not run-1 `RequestStorage`. Run-1 still starts with no incoming
demand snapshot and uses its existing abstraction and mark requests.
The current implementation already freezes factored seeds instead of all
static combinations. Keep that property. The new work reduction is in lookup,
especially avoiding paired closure for C2.

```kotlin
fun transition(completed: RunResult, nextMode: ApMode): NextRun {
    require(completed.status == COMPLETE)

    // Already completed before actors release: actual caller binding and
    // frozen primitive W/B/R inventory for the run-1 boundary.
    val skipped = completed.staticCompletion

    records.persistNativeRecords(completed) // raw normal data, existing policy
    val builder = DemandStorage.Builder(nextMode, ap)
    forEachSelectedDemand(completed) { owner, premise, conclusion ->
        builder.addExistingDirectionalProjection(owner, premise, conclusion)
    }
    if (completed.index == 1) {
        builder.attachSkippedStatics(skipped)
        builder.enableSameActualStaticCarry()
    }
    val demand = builder.seal()
    return NextRun(records.readView(), demand, existingSeeds(completed))
}
```

This does not defer actual caller binding until after release. The joined
phase still runs before N2 input storage and actor services release. The
builder borrows no live runner, subscription, statement or mutable fact store.

Native NORMAL records stay in `PersistentRecordStore`. Preserve their raw
field exclusions and mark data. Selected demand moves into the next snapshot
through the existing direction projection and normalization. Moving means
ownership transfer or immutable copy, not clearing another persistent store.

Run-1 has no ND premise. Later forward runs can have ND premises. Preserve
the existing member projection at handoff and original premise at publication.
A backward run still has no ND premise.

Only run-1-to-run-2 attaches skipped-static completion and shared static carry.
The same API is used on later transitions, with ordinary inferred demand.
Do not retain the old completion in all later snapshots without a new design.
An incomplete run cannot replace the accepted snapshot or report.

## 5. Storage organization

```kotlin
class DemandStorage private constructor(
    val mode: ApMode,
    private val explicit: Map<MethodKey, MethodDemandIndex>,
    private val skipped: LazyStaticDemand?,
    private val sharedStaticCarry: Boolean,
    private val ap: ApOps,
) {
    fun initials(method: MethodKey, arrived: Facts): Set<InitialAp>
    fun intersect(method: MethodKey, summary: SummaryCandidate): List<SummaryCandidate>
}

// AP/store-level value; no engine publisher or actor reference.
data class SummaryCandidate(val premise: PremiseKey, val conclusion: Facts)

class MethodDemandIndex {
    // Deduplicate complete Dc patterns independently of Dp.
    val entries: PathTrie<EntryId>
    // A bucket owns complete correlated pairs, including absent Dp.
    val pairsByEntry: PathTrie<PairBucketId>
    val pairsByExit: PathTrie<PairId>
    val pairs: ImmutablePairRows
}

class LazyStaticDemand {
    val frozenSeeds: FrozenPrimitiveStaticSeeds
    val targetEnvelope: EndpointIndex
    val sourceEnvelope: EndpointIndex
    val visibility: ImmutableStaticVisibility
}
```

The entry index stores each complete `D_c` pattern once, including its mark,
tail and remaining concrete E. Ten pairs with equal entries give one C2
candidate. Pair buckets retain all ten `D_p` relations for C5. A null `D_p`
still contributes its entry to C2, but cannot authorize a summary under C5.
Index each present `D_p` by its output location too. For C5, intersect the
entry-prefix candidate IDs with the conclusion-location candidate IDs, then
apply AP restriction to those complete rows. Do not form a Cartesian product
of entry and output patterns. Candidate indexes may ignore tails, marks and
E conservatively; the stored pair keeps all of them.

The static store keeps primitive W/B/R, shared B owners and graph adjacency.
It does not store all caller copies, all transitive B paths, or all W-by-R
combinations. Its query states are temporary derived views, not new demand.
Keep local attachments under complete `MethodKey`; do not merge their contexts.

Indexes locate candidates. AP intersection is the authority. Base/path
compatibility alone does not decide mark, E, whole-entry containment or layer.

The method-local query view includes ordinary inferred demand and direct
projections of its frozen primitive W/R and own B seeds. Use references to
shared rows; do not copy B to transitive callers. These primitive projections
already belong to the specified demand relation. Indexing them locally adds
no semantic demand. This coverage invariant is required by the precise lookup
strategies in [demand-storage-lookup.md](demand-storage-lookup.md).

## 6. Operation 1: actual fact to initial facts

```kotlin
// The caller keeps the current field-limit and grammar-validation boundary.
fun onArrived(arrived: Facts) {
    limitAsNow(arrived, mode.fieldLimit) { bounded ->
        validateInputsAsNow(bounded)
        for (initial in demand.initials(method, bounded)) addInitial(initial)
    }
}

fun initials(method: MethodKey, bounded: Facts): Set<InitialAp> {
    val query = InitialQuery(method, bounded) { entry ->
        // Same AP emit as before; Dp is irrelevant to this operation.
        ap.emit(DemandPattern(entry, null), bounded)
    }
    return lookup(query) // staged helper in demand-storage-lookup.md, section 2.0
}
```

`InitialQuery` checks direct local entries and the existing implicit entries
for **all** actual leaves before starting composition. Its local BFS uses
local W/R and own B. Only then can it enable inherited B visibility. Apply
the emitter as each candidate arrives; deduplicate complete emitted initial
keys. Stop when a conservative bound proves that no further key can be added.
If the bound is not covered, complete the eligible search. The companion
spec defines this bound and the exact state/visibility rules.

Keep field limiting before candidate lookup. Preserve packed-fact leaves and
the existing initial deduplication. An abstract demand emits the shared FLOW
form. It does not copy an actual T mark into that form. A concrete demand
requires a matching actual marked input; FLOW input cannot supply T.

Normalize abstract STAR demand E to empty. Do not clear actual E, concrete
demand E, native-record E or summary E. Preserve STAR correlation and all
other current AP intersection rows. There is no new EXACT/ANY/STAR rewrite.

### 6.1 Entry-only static traversal

Start at primitive seed targets comparable with the actual location. Do not
construct all `(D_c, D_p)` rows and discard `D_p` afterwards.
For a reader R, offer its conclusion mark directly if it is mapped. A FLOW R
offers T when a composable local W or visible B concludes T and reaches R
through zero or more FLOW B edges. Use the conclusion selector, not R's input
selector. Every offered entry still needs the unchanged actual-input AP test.

```text
for each eligible rightmost seed a -> b matching the actual target:
    if its relation is mapped T -> U:
        offer entry b/U
    if its relation is FLOW:
        offer abstract entry b/*
        if a is static:
            for the actual marked T only:
                search backward from a and forward from marked static outputs
                traverse only FLOW B between them
                if a valid directed meeting exists: offer entry b/T
```

Stop a color search at a mapped seed: that seed already fixes its output.
Continue through FLOW prefixes because they transport a preceding color.
This is a Boolean query for the actual T, not enumeration of all colors.
The forward frontier holds static outputs; the backward frontier holds
static inputs. They meet only at a valid output-to-input geometry join.
Each transfer across an input and output requires a real FLOW B row.
Use the current static-anchor, geometry-overlap and visibility conditions.
Do not replace them with class or group equality alone. The visited state
retains every geometry and owner coordinate needed by those conditions.

```text
W: p/T -> C.f/U
R: C.f/* -> ret/*

C2 entries include ret/* and ret/U.
They do not require paired rows ret/U -> p/T for admission.
```

A genuine `ZERO -> C.f/U` writer also contributes the U color. ZERO is not a
full mark to intern. A standalone FLOW reader does not enumerate all concrete
marks. No global mark inventory or rule binding is needed for this traversal.

The entry fixed-point model in
[EntryProjection.lean](lean/proposals/restricted-demand-next/EntryProjection.lean)
proves the nonzero symbolic projection. `DemandQueries.lean` also proves the
symbolic target-directed traversal. Production scheduler, ZERO and AP-geometry
adapters still need their own proofs. The exact local/transitive choice and
worklist keys are specified in [demand-storage-lookup.md](demand-storage-lookup.md).

## 7. Operation 2: summary to restricted summaries

```kotlin
fun intersect(method: MethodKey, s: SummaryCandidate): List<SummaryCandidate> {
    val query = SummaryQuery(
        method, s, results = ProtectionPreservingResults(),
    ) { member, pair ->
        ap.restrict(member, s.conclusion, pair)
    }
    val kept = lookup(query)
    return kept.values().map { s.copy(conclusion = it) } // keep the original premise
}
```

`SummaryQuery` checks direct local pairs and static-carry pairs for all
original members first. Then it runs local paired BFS. Only then can it
enable visible inherited B rows. Every candidate keeps its original member
and complete pair. Its result accumulator deduplicates exact payloads and
unions protection. Whole-result coverage can stop further search only under
the C5 output-bound rule in the companion spec. The C2 Boolean witness does
not replace this paired walk.

C5 uses complete `(D_c, D_p)` pairs. Its guard requires the whole member
inside `D_c`, with the existing location and mark tests. Then intersect the
conclusion against that pair's `D_p`. Do not use separate endpoint sets as
permission to publish. Do not mix `D_c` from one path with `D_p` from another.

An absent `D_p` yields no C5 result. The implicit `(ZERO, no exit)` demand
therefore does not authorize arbitrary ZERO summaries. The original backward
ZERO return is still outside this API:

```kotlin
val publications = when {
    mode.run1 -> listOf(rawSummary)
    mode.backward && rawSummary.premise.isZero -> listOf(rawSummary)
    else -> demand.intersect(method, rawSummary)
}
```

Keep raw summary storage, demand selection, native persistence and publication
batching in their existing owners. This API returns restricted candidates;
it does not insert or publish them itself.

Result deduplication must preserve the existing monotone protection contract.
`TaintTree.equals` excludes `nonSubsumable`; a plain `Set<Facts>` can therefore
keep the weaker annotation when equal payloads arrive in another order.
For equal ordinary payloads, union their protection masks. Do not change
global fact equality, merge different geometries, or perform new subsumption
inside this accumulator. The reference comparison must include the masks.
This is a required preservation check, not a claim that a runtime failure
from this cause has been reproduced.

For lazy C5, start from visible primitive targets that can contain the queried
member. Follow the existing paired reverse walk through B and local W.
Keep the complete mark relation and both outer endpoints in each state.
Return a pair only when its output can affect the offered conclusion, then
apply AP C5. Whole-premise and conclusion checks remain distinct.

The entry mark gate cannot be reused for the output. A concrete `D_c/T`
requires an appropriate marked premise. A concrete `D_p/T` can retain a FLOW
conclusion if T is not excluded, as specified by `marksMeet`. Preserve the
existing whole STAR conclusion, layer and protection behavior.

This query does not enumerate closure at transition time. It can still visit
many states for a large relevant static component. No constant-time bound or
fixed speedup is claimed for C5.

## 8. Select normal or transitive lookup

The complete decision tables and both traversal algorithms are specified in
[demand-storage-lookup.md](demand-storage-lookup.md). They require the local
primitive coverage invariant from section 5. Check direct local rows for the
whole query, then local composition by BFS, then inherited rows visible
through the call graph. Stop when the exact result-coverage test succeeds.
The last stage must also follow local links reached through inherited rows.
Local exhaustion alone cannot prove a final negative result.

For initial admission, a nonstatic fact needs additional lookup only if a
local FLOW reader target can match it. A static fact needs additional lookup
only if a shared B target can match it. Shared B includes own B: an own FLOW
bridge can gain a concrete output color from an earlier writer.
Apply the actual-FLOW shortcut first: a nonstatic FLOW input needs only local
entries; a static FLOW input needs at most direct visible FLOW B entries.
Neither case needs the transitive color traversal.

For summary restriction, test each original member. A new paired path must
end at R or B and start at W or B. Both endpoint tests must succeed before
transitive traversal. Use all R labels here, not only FLOW. A mapped reader
can need an earlier writer for C5 even though its direct C2 entry is complete.

The cheap tests are location-only and conservative. Negative tests skip only
the transitive component; ordinary rows, direct seed views, implicit ZERO and
static carry still apply. Positive tests do not authorize an initial or a
summary. Complete visibility, mark, tail, E and AP tests remain mandatory.

If primitive local coverage is not established, retain the broader safe
fallback: test all primitive target endpoints, and also source endpoints for
C5. Do not apply the tighter negative decisions to a partial local view.

Share query reachability scratch. Do not materialize every method/seed pair
or every static path at transition. Do not stop because local lookup already
returned a result; a transitive path can add a different color or paired exit.

### 8.1 One query through a skipped path

```java
Object m(Object p) {
    set(p);       // set(q) { C.a = q; }
    copy();       // copy() { C.b = C.a; }
    return get(); // get() { return C.b; }
}
```

Assume the ordinary run-1 binding and visibility rules give M these frozen
relations. The example uses one mark T; FLOW counterparts remain symbolic.

```text
W: p/T   -> C.a/T       local caller-bound writer
B: C.a/T -> C.b/T       visible shared bridge
R: C.b/T -> ret/T       local reader
```

At transition, retain W, B and R. Do not enumerate `p/T -> ret/T` for each
caller. The incoming run-2 storage denotes the demand `(ret/T, p/T)` through
the frozen path.

```text
initials(M, actual ret/T):
    target envelope matches ret
    entry query returns ret/T
    existing AP emission returns the T initial

intersect(M, summary ret/T -> p/T):
    both endpoint envelopes match
    paired traversal witnesses the same W-B-R path
    C5 retains the required summary part

intersect(M, summary ret/T -> unrelatedLocal/T):
    no matching source envelope and no ordinary pair
    no summary part
```

For an actual FLOW input at `ret`, the colored entry does not manufacture T.
For a fact at an unrelated local, skip the virtual component and use ordinary
demand only. If a query has a real ordinary pair, it still works even when
both virtual envelope tests are false.

The [worked examples](demand-storage-lookup.md#9-worked-examples) specify full
provided facts and summaries, local lookup, shared/transitive steps and final
results. They include static carry deduplication, explicit EXACT demand,
visibility, disconnected endpoints, mark mismatch, exclusions, ZERO, ND and
cycles.

## 9. Correctness contracts and required proofs

Use an explicit reference demand relation for each owner:

```text
D = ordinary inferred pairs
    union existing implicit ZERO/carry families
    union the existing run-1 skipped-static closure, when attached

Initials(M, A) = union AP.emit(Dc, bounded(A)) for each applicable Dc in D
Restricted(M, J, G) = union AP.restrict(j, G, (Dc,Dp))
                     for each member j of J and each complete pair in D
                     with the unchanged whole J reattached
```

The production implementation need not enumerate D. The proof must not
define D as whatever the optimized lookup happens to return.

Prove the following contracts constructively:

1. **Cleanup concrete transfer.** Save every registry slot, clear statics,
   then restore those slots has exactly the registry-only static return
   relation. Prove both forward and backward directions and control return.
2. **Cleanup model adapter.** The class schema preserves well-formed registry
   field facts, not class-wide concrete facts. No broad default, local-write
   effect or false ZERO activation is added. Prove the selected layer and
   run-1-to-run-2 guidance behavior separately from concrete transfer.
3. **Snapshot separation.** Building/sealing transfers selected demand only;
   native records keep their original data. Queries preserve the snapshot.
4. **Entry projection.** Entry-only lookup gives the same C2 initial set as
   projection of D, including colors, genuine ZERO writers and absent Dp.
5. **Paired lookup.** Lazy C5 returns every relevant pair of D and no pair
   formed from unrelated paths. AP restriction outputs equal the reference.
6. **Fast-path guard.** Every useful virtual entry/pair has primitive endpoint
   witnesses. A false envelope test cannot remove a result.
7. **AP adapters.** Preserve field-limit order, abstract E normalization,
   actual/concrete E, marks, STAR/FULL intersections, layers and protection.
8. **Finite query work.** On frozen bounded seed data, admit each complete
   query state once. Cycles cannot produce an unbounded worklist. Do not
   infer finiteness from a dedup key that omits a required semantic coordinate.
   In staged search, track local and inherited expansion separately.
9. **Staged and bidirectional lookup.** Prove that reordering local and
   visible work preserves results. Prove that complete output coverage
   permits stopping. For C2, a meeting must yield a real marked-prefix path;
   a negative result needs complete eligible roots and adjacency. Keep the
   Boolean C2 proof separate from the full C5 pair proof.

The existing EntryProjection model has 20 audited declarations with no
axioms. New local models for the cleanup kernel and query guards are stored
under `lean/proposals/demand-storage-next`. Their receipts must state their
scope. Local graph and slot models do not prove all AP or JVM adapters.
Do not implement an adapter whose stated proof condition is still false or
unknown; refine its design first. Do not change an unselected semantic rule
to make a proof pass.

### 9.1 Completed local proof checks

| Model | Audits | Established scope | Receipt |
|---|---:|---|---|
| [SpringCleanup.lean](lean/proposals/demand-storage-next/SpringCleanup.lean) | 11 | Atomic save/clear/restore value transfer and its backward converse; control, layers and instruction count | [Checks](lean/proposals/demand-storage-next/spring-cleanup-checks.json) |
| [DemandQueries.lean](lean/proposals/demand-storage-next/DemandQueries.lean) | 31 | Endpoint-guard witnesses; explicit/lazy query result equivalence; targeted FLOW-prefix traversal; ordinary fallback; ZERO dispatch; pointwise protection union | [Checks](lean/proposals/demand-storage-next/demand-queries-checks.json) |
| [LookupStrategies.lean](lean/proposals/demand-storage-next/LookupStrategies.lean) | 25 | Tighter local/transitive guards under primitive coverage; mapped-terminal locality; FLOW-actual shortcuts and edge cases | [Checks](lean/proposals/demand-storage-next/lookup-strategies-checks.json) |
| [StagedDemandLookup.lean](lean/proposals/demand-storage-next/StagedDemandLookup.lean) | 25 | Local-first/full-path equivalence; exact output-bound stopping; positive witness and exhausted negative; mixed local/remote cases | [Checks](lean/proposals/demand-storage-next/staged-demand-lookup-checks.json) |
| [BidirectionalDemandExists.lean](lean/proposals/demand-storage-next/BidirectionalDemandExists.lean) | 20 | Directed meeting witnesses, typed-frontier exhaustion, overlap and late inherited-join cases | [Checks](lean/proposals/demand-storage-next/bidirectional-demand-exists-checks.json) |
| [PredefinedSummaryDispatch.lean](lean/proposals/demand-storage-next/PredefinedSummaryDispatch.lean) | 14 | Complete dispatch without body/default/unresolved/boundary rules; external call-site reports; identity-key catalog; intentional boundary observation difference | [Checks](lean/proposals/demand-storage-next/predefined-summary-dispatch-checks.json) |

All 126 audits in these six models pass without axioms. They import or use the earlier
constructive entry-projection kernel where stated. They do not execute the
analyzer or establish a measured saving.

For cleanup, case analysis on ZERO, caller-local, registry-field and
nonregistry-field input gives the same value result for both transfers.
Their backward relations are equal by substitution of this forward equality.
Payload preservation does not assert identical old intermediate AP layers.

For queries, a full path supplies explicit first/last primitive seed witnesses.
Those witnesses satisfy the conservative endpoint guards. Thus a useful
virtual result cannot take the false branch. A false branch keeps all ordinary
and implicit results. A mapped final edge already fixes its output color;
a FLOW final edge transports the color from a mapped prefix. This yields
constructive conversions between projected full paths and targeted entry
derivations. No arbitrary path is selected by classical choice.

The result-set equivalence uses the **same** AP emitter and paired reducer,
with their stated locality contracts, on both sides. It is not a proof of a
new AP intersection table. The mask laws are pointwise OR; production tree
mask transport, payload-key equality, visibility, index completeness, ZERO/carry
adapters and worklist execution remain implementation proof obligations.
The two new graph models establish 45 of these audits. They do not prove
that a production BFS implements the declared adjacency, coverage bound or
fair scheduling. Verify those adapters before enabling the optimized lookup.

The complete-dispatch model adds 14 audits for the selected predefined-model
boundary. It does not prove JVM prescan, AP schema lowering or call-plan
integration. Skipping predefined boundary rules is the intended difference;
ordinary external call-site observations remain in the common call path.

## 10. Implementation order and checks

1. Add the predefined-summary seam and the complete cleanup model. Prove and
   test it with the existing generated block before removing that block.
2. Remove save/restore and both cleanup rule paths only for engines with the
   model. Test controller annotations, loops, initialization and return control.
3. Introduce the demand API over the current implementation first. Check
   exact initial and publication sets. Then separate explicit entry/pair indexes.
4. Add endpoint envelopes and staged local/visible lookup. Use bidirectional
   compatible-mark search for C2 FLOW readers and the paired walk for C5.
   Compare exact results, including protection, with finite explicit closure.
   Check local coverage stopping, inherited EXACT targets, mapped barriers,
   remote joins between old frontiers and alternating local/remote paths.
5. Commit selected runtime changes before the fixed project campaign. Reuse
   the saved baseline; do not add another analyzer configuration.

See the detailed [implementation proposal](../docs/design/bidirectional-demand-storage-predefined-summaries-implementation-20261028.md)
for code seams, schemas, indexes, staged queries, removal list and test gates.

Required cases include registry/nonregistry mixed inputs; nested paths; FULL
and GROUP; NORMAL/DEMAND; E and mx; exact class markers; no actual T; T-to-U
paths followed by FLOW; cycles; ZERO writers; different method contexts;
ND member union; absent Dp; concrete output demand with FLOW conclusion;
backward ZERO; cancellation; and attempted mutation after seal.
Test duplicate protected/unprotected output payloads in both arrival orders;
the protected membership must survive in each order.

Check terminal findings and exact sink locations, not only callback counts.
Do not weaken the three known Stirling comparison gaps or the existing cleaner
precision checks to make this optimization pass.

Measure:

- Generated save/restore instructions removed and active point rows in dispatchers.
- Cleanup model applications, rejected nonregistry facts and absence of fallback.
- Run-1 engine time and separate joined completion/freeze/report times.
- Ordinary versus virtual queries; guard negatives; C2 entry states and C5 pair states.
- Initial/publication result counts; shared reachability traversals and retained indexes.
- Latest reached, completed and accepted forward run; CPU, allocation and OOM layout.

No performance result is claimed by this proposal. The registry field-name
share of the last heap is still unmeasured. The expected work reduction comes
from removing generated copies and avoiding paired closure in C2, not from
making every existing operation slightly faster.

# Next iteration: demand refinement and run-2 work removal

Date: 29 October 2026. Reviewed source: `71156f061`.
Status: proposal only. Production code is unchanged.
Use FULL marks by default and the selected `1,1,2,3,...` field-limit schedule.

The [implementation draft](bidirectional-summary-demand-workload-implementation-20261029.md)
defines the code boundaries, pure filtering API, packed-row control flow,
private eligibility memo, and additional formal contracts. It keeps the
selected FLOW summary normalization, write exclusions and whole-position
RemoveAll explicit. No runtime change is included.

The iteration has three ordered parts. First implement the selected
[one-step demand refinement and entry intersection](bidirectional-one-step-initial-refinement-20261029.md).
Then remove impossible C5 static branches. Then remove repeated owner
eligibility checks. The last two parts must preserve the rewritten demand
handling. Compare them with a reference taken after that rewrite.

## 1. Evidence, priority, and latest iterations

The [workload report](../reports/bidirectional-summary-demand-workload-20261029.md#8-next-design-targets)
provides the measurements. Its complete data is
[embedded](../reports/data/bidirectional-summary-demand-workload-20261029.json).
The measured runtime is `c2bc5e78dfdb13f95bda970c5f4e0c247acbac29`.
The reviewed branch adds tests, documentation and formal models; its
production kernel is unchanged. No new analyzer experiment was run for
this proposal.

| Project, primary 16g campaign | Latest reached | Latest complete | Accepted forward | Outcome |
|---|---|---|---|---|
| OWASP | run-12 | run-11 | run-11 | TIMEOUT |
| conductor | run-4 | run-3 | run-3 | TIMEOUT |
| thingsboard | run-2 | run-1 | run-1 | TIMEOUT |
| Stirling-PDF | run-6 | run-5 | run-5 | TIMEOUT |

The isolated thingsboard counter run also reaches **run-2**, completes
**run-1**, and accepts **run-1**. It times out in run-2 without OOM. Counts
include partial queries up to timeout. They are not completed-run totals.

| Order | Change | Current work | New behavior and expected effect |
|---|---|---|---|
| Prerequisite | Selected demand rewrite | Abstract ANY demand restarts broad FLOW analysis; entry containment accepts initials outside the new emitter's output set | Refine one field, preserve selected exact cases, and accept only emittable summary initials |
| First performance target | Stop impossible fixed-entry C5 branches | 3,741,361 of 3,992,093 popped states have an incompatible fixed mapped output; 2,893,937 predecessor expansions follow such a rejection | Reject the branch before owner lookup, predecessor enumeration, and queue admission |
| Second performance target | Reuse owner-family eligibility within each query view | At least 1,358,983,156 repeated C5 reachability checks, 80.06% of the captured call stream | Evaluate each owner family at most once per visible view; reuse true and false answers |

Thingsboard run-2 profiles place 47.13% of Java samples in C5 and 29.49% in
C2. `StaticPairLookup.walk` alone accounts for 47.02%. The counter run has
930,415,459 composition attempts, 905,957,561 expanded call-graph vertices,
and 2,050,447,072 examined graph edges. Remove branches and repeated
questions before tuning those individual operations.

The percentages are operation bounds or inclusive sample shares. They do
not establish a runtime speedup. The two savings overlap and must not be
added. The demand rewrite can change their populations substantially.

## 2. Semantic scope

| Part | Semantic status |
|---|---|
| One-step initial refinement, abstract EXACT/MUST, concrete STAR coverage, and emittable-entry intersection | Previously selected semantic changes; complete their domain and application proofs first |
| STAR demand phase rule | Run-2 may answer with requested STAR; later FLOW STAR entries are invalid; later concrete STAR answers remain precise |
| Summary normalization, write E and whole RemoveAll | Explicit selected semantic changes; normal STAR summaries retain E; partial all-mark cleaners are prohibited |
| Fixed-entry C5 pruning | Work removal only; same complete query results as the rewritten reference |
| Query-local eligibility answers | Work removal only; same answers and incremental reachability state for the same remaining request stream |

The selected rewrite includes these rules:

```text
p.ANY/FLOW + p.f.g.EXACT/T -> p.f.STAR/FLOW
p.ANY/T    + p.f.g.EXACT/T -> p.f.STAR/T, DEMAND
p.ANY/T    + p.f.EXACT/T   -> p.f.EXACT/T
concrete demand U + supplied T, U != T -> no initial
run-2: p.STAR/M + compatible submitted p.f.... -> requested p.STAR/M
run-2 onward: outgoing FLOW demand conclusion is ANY, not STAR

EntryIntersection(Dc, J) nonempty
    -> Emit(Dc, a) = I and NormalizeSummaryInitial(I) = J for some supplied a
```

Concrete STAR starts and stays DEMAND. Coverage matching does not promote
its result to NORMAL. Entry intersection retains A; it does not project a
summary under a different initial.

The run-2 exception does not make raw self-emission a valid image test. Use
the explicit output-template witness and current field budget. Later FLOW
STAR entry demands are invalid; a paired exit may still reference STAR.

The rewrite still needs complete abstract EXACT/MUST point-transfer and
adapter proofs. The selected summary normalization stores STAR rather than
EXACT/FLOW records, preserves write E, and uses the normalized C5 image.
Abstract MUST native views still need their selected input/matching proofs.
Do not remove S8 without the new point-domain and boundary contracts.
Finish the selected semantic contract before using it as the performance
reference.

The two work-removal changes keep these mechanisms:

```text
call-graph direction and context visibility; full MethodKey W/R ownership
static anchors, including existing legal exact class markers
canonical ZERO and its private guidance selectors
FULL/GROUP composition compatibility; actual-input concrete mark gates
tails, E, mark exclusions, protection, and normal/demand layers
complete paired demand rows and original ND premise sets
source/sink identities and rule occurrences; native record reuse
local -> local composition -> visible search order and valid coverage stops
```

They add no input history, fact provenance, mark census, global result
cache, summary transport change, source replay mechanism, or IR storage.
No field limit, cleaner rule, exception rule, or stop policy changes here.

## 3. First target: prune C5 branches with an impossible fixed entry

### 3.1 Current and proposed pipeline

The current C5 walk uses a frozen path state `left -> right`:

```text
related target rows
  -> owner eligibility
  -> decode state
  -> queue and deduplicate
  -> offer (entry=right, exit=left) to final restriction
  -> even after entry failure, enumerate predecessors and prepend them
```

The proposed walk is:

```text
related candidate geometry and label
  -> if the right entry is fixed and impossible: stop this branch
  -> owner eligibility
  -> decode, deduplicate and queue
  -> final paired restriction
  -> prepend only predecessors with a potentially useful fixed right entry
```

The fixed endpoint is `state.to`, which becomes demand entry `D_c`.
`state.from` becomes exit demand and can change with every prepend.

### 3.2 Why the rejection remains valid

For every valid `compose(left, right)`, current composition preserves the
right endpoint's base, path, tail and field exclusion. If `right.marks` is
already Mapped, it preserves its output mark too. Thus it preserves the
complete right entry descriptor.

Use the canonical guard from the demand rewrite:

```kotlin
fun mayKeep(member: InitialAp, right: Pattern, marks: GuidanceMarks): Boolean {
    return when (marks) {
        GuidanceMarks.Flow -> true
        is GuidanceMarks.Mapped -> {
            val fixedEntry = endpointWithExistingOutput(right, marks.output)
            canStoreInitial(fixedEntry, member)
        }
    }
}
```

`endpointWithExistingOutput` preserves a genuine ZERO endpoint. A null
selector never becomes a new ZERO mark or an ordinary full-mark sentinel.
The entry test reads the complete descriptor. It is not a raw mark-ID or
group-name comparison.
Apply the real mapped output label before demand normalization. The FLOW
mark in stored geometry is a metadata placeholder. Normalizing it first
could erase E that belongs to a concrete STAR endpoint.

If the test fails for a Mapped right endpoint, it fails after every number
of left prepends. The branch cannot produce an accepted C5 result. The new
entry-intersection invariant is the reason this rejection is authoritative.

### 3.3 Move the check before expensive work

Add an internal, pure candidate filter to the C5 view operations. Default
it to acceptance for existing consumers. Supply it to C5 target lookup,
endpoint preflight, and incoming-row enumeration.

```kotlin
fun rows(id: Int, flowOnly: Boolean, keep: CandidateFilter) = sequence {
    val row = bridges[id]
    for (i in row.labels.indices) {
        cancellation.checkpoint()
        val label = row.labels[i]
        if (flowOnly && label != FLOW_LABEL) continue
        if (!keep(row.geometry, label)) continue
        val allowed = if (inherited) eligible(row.owners[i])
            else ownRows.binarySearch(packRowReference(id, i)) >= 0
        if (!allowed) continue
        yield(decode(row.geometry, label))
    }
}
```

This is pseudocode for the existing packed view. The filter reads immutable
endpoint geometry and the packed mark relation. It need not intern an AP,
construct a Facts tree, or materialize the full composed edge.

Apply the same condition to method-local rows before yielding them. The
preflight target test must use it too; otherwise it still performs owner
lookups for a target set that is entirely impossible.
Only the target side of `hasComposedEndpoints` receives this filter. Its
separate output-side search tests possible left writers; applying the target
filter to each writer's own right endpoint would reject valid compositions.
Keep that output check unchanged. Incoming candidates use the prospective
composition's right endpoint below, not the predecessor's own endpoint.
If all targets fail before ownership, the view needs neither a reachability
scratch nor an eligibility memo for that query.

For an incoming candidate, compute the prospective relation using the
existing composition rule:

```kotlin
fun keepIncoming(left: Candidate, state: StaticGuidanceEdge): Boolean {
    val relation = composeMarks(left.marks, state.marks) ?: return false
    return mayKeep(member, state.to, relation)
}

fun admit(state: StaticGuidanceEdge) {
    if (!mayKeep(member, state.to, state.marks)) return
    if (seen.add(state)) pending.addLast(state)
}

for (state in view.targets(member, keepTarget)) admit(state)
while (pending.isNotEmpty()) {
    cancellation.checkpoint()
    val state = pending.removeFirst()
    offerCompletePair(member, state.to, state.from)
    if (covered()) return
    if (!isStatic(state.from)) continue
    for (left in view.incoming(state.from, keepIncoming = { keepIncoming(it, state) })) {
        compose(left, state)?.let(::admit)
    }
}
```

Keep one canonical `composeMarks` implementation. Preserve the existing
full/group compatibility checks and geometry join. Extracting the pure
label calculation does not authorize a different join rule.

The final C5 restriction remains the authority. The early filter does not
replace conclusion restriction, layer handling, protection, or coverage.
`offerCompletePair` executes that full restriction and adds only retained
pieces to `ExactDemandResults` before `covered()` is tested. Passing the
early filter is not a coverage certificate.

### 3.4 Required examples

**Remove a fixed-mark branch.**

```java
writeT() { C.f = sourceT(); }
read()   { return C.f; }
```

```text
provided backward initial A: ret.f.STAR/FLOW
state:                      C.f.STAR/T -> ret.ANY/T
entry:                      ret.ANY/T

Before: reject offer, then inspect predecessors of C.f.
After:  reject before eligibility/queue; no predecessor work.

Any prepend still ends at ret.ANY/T and cannot emit A/FLOW.
```

**Keep FLOW until a writer supplies the mark.**

```java
set(p) { C.f = p; }
get()  { return C.f.payload; }
main() { set(sourceAllT()); sinkT(get().f); }
```

```text
A:       ret.f.EXACT/T
prefix:  C.f.STAR/FLOW -> ret.ANY/FLOW
writer:  p.STAR/T -> C.f.STAR/T
compose: p.STAR/T -> ret.ANY/T
```

The FLOW entry cannot itself emit the concrete A. The mapped predecessor
can fix the right mark, and the concrete exact exception can then emit A.
Do not prune FLOW on its current entry failure, including a failure whose
shape test depends on whether the demand mark is concrete.

**Keep a left endpoint that needs an earlier writer.**

```text
A:                 ret.STAR/T
provided raw B:     p.STAR/U
prefix:            C.f.STAR/T -> ret.STAR/T
earlier writer:    p.STAR/U -> C.f.STAR/T
composed demand:   entry=ret.STAR/T, exit=p.STAR/U
```

The prefix's exit C.f does not match raw B/p. The earlier writer repairs
that endpoint. Skip an unsuccessful final offer if possible, but retain its
traversal. The measured stream has 194,725 such bridge expansions without a
fixed-entry rejection; they are not all removable.

### 3.5 Expected work reduction

For the captured stream, 93.72% of popped states have a fixed-mark failure,
and 93.68% of predecessor expansions follow such a failure. Early rejection
removes the associated branch work. It also prevents many duplicate
admission attempts before they reach `seen`.

The report does not attribute each composition attempt to that class.
Do not infer a 93% CPU reduction or an exact number of saved compositions.
Measure the new post-rewrite stream. The intended gain is removal of large
search subtrees, not a small improvement in the cost of each composition.

## 4. Second target: one eligibility evaluation per view and owner family

### 4.1 Current and new behavior

Each visible `FrozenStaticCompletion.View` owns one lazy incremental
reachability scratch. Repeated rows call `eligible(Owners)` again. The
graph and owner family are immutable for the view, but each call repeats
owner-membership checks and may revisit the same completed question.

Add a query-local tri-state table. Cache both true and false only after a
completed evaluation. Keep the first evaluation unchanged.

```kotlin
private const val UNKNOWN: Byte = 0
private const val NO: Byte = 1
private const val YES: Byte = 2

private class Owners(
    val familyId: Int,
    val graphIds: IntArray,
    val outsideGraph: Set<CommonMethod>,
)

private inner class View(/* existing fixed method and inherited flag */) {
    private val reach by lazy { graph.scratch(method.method, cancellation) }
    private var eligibility: ByteArray? = null

    private fun eligible(owners: Owners): Boolean {
        cancellation.checkpoint()
        if (!inherited) return existingLocalTest(owners)
        val memo = eligibility ?: ByteArray(ownerFamilyCount).also { eligibility = it }
        when (memo[owners.familyId]) {
            YES -> return true
            NO -> return false
        }
        val answer = method.method in owners.outsideGraph ||
            reach.reachesAny(owners.graphIds)
        memo[owners.familyId] = if (answer) YES else NO
        return answer
    }
}
```

The outside-graph short circuit still avoids creating reachability scratch.
Cancellation or another incomplete evaluation does not write an answer.
When outsideGraph is false, an empty graph-owner array must still execute
the first existing `reachesAny`: it exhausts pending traversal. Returning false early for that first call
would not preserve the incremental state.

### 4.2 IDs, storage, and lifetime

Assign family IDs during the existing freeze operation:

```kotlin
var nextOwnerFamily = 0
fun owners(methods: Set<CommonMethod>) = Owners(
    familyId = nextOwnerFamily++,
    graphIds = existingSortedGraphIds(methods),
    outsideGraph = existingOutsideGraphMethods(methods),
)
// Use this factory for each bridge label and each projected-entry Owners.
// Seal ownerFamilyCount = nextOwnerFamily.
```

The ID is local to this frozen completion. It is not a graph vertex ID,
method ID, static class ID, mark ID, or MethodKey context. Equal owner sets
can have different IDs. No owner-set interning or new census is required.

`Owners` remains an ordinary private class with identity equality. Adding
its immutable ID does not change fact, rule, summary, or MethodKey equality.
The frozen snapshot stores the ID and count as immutable metadata. It holds
no mutable answer table. A visible view owns its table and scratch; they
become unreachable when that lookup returns or is cancelled. Local views
keep their existing direct owner test.

With F owner families, each active visible view uses F memo bytes. The
captured F is 16,414: about 16 KiB plus the array header per active view.
The bound depends on simultaneous views, not the total number of queries.
No result is retained for the lifetime of the whole run. Later run-3 and
subsequent local-only demand lookups allocate no such table.

### 4.3 Why cached answers preserve state

```text
true via outsideGraph:
    constant for this method; reachability was not touched

true via reachesAny:
    an owner is in the monotone seen set
    all later identical questions return at the initial seen check

false:
    outsideGraph was false and pending traversal was exhausted
    later questions cannot add vertices with pending empty
```

These facts remain true after queries for other owner families. Therefore,
replacing a repeated call with its answer preserves both the result and the
scratch state that the repeated call would have produced. This is stronger
than checking only two adjacent identical calls.

First misses retain current iteration order and graph traversal. Hits still
execute the surrounding cancellation checkpoints. C5 pruning can remove
questions from the stream; the memo proof applies to that remaining stream.
It does not claim that the pruned algorithm has the same private graph
scratch as the old unpruned algorithm.

### 4.4 Expected reduction and the remaining root-tour cost

For Q requests in a view, at most `min(Q,F)` calls execute the eligibility
body. Each remaining request uses one tri-state lookup. Across the captured
20,621 C5 views, at most 338,473,094 distinct view/family questions exist;
at least 1,358,983,156 of 1,697,456,250 calls repeat a question.

This removes repeated questions. It does not remove the first traversal for
a new root/view. The report also measures repeated roots and at least
89.05% repeated root/vertex visits across views. That remains a separate
cost to remeasure after the rewrite and C5 pruning.

Do not add cross-query root reuse in this change. A completed-root bitset
with runner ownership is a possible later design. It needs its own lifetime,
retention bound, hit-rate evidence, and result-equivalence proof. The exact
state proof above does not automatically cover that different provider.

## 5. Implementation order and validation

Use these existing components. The paths are relative to the dataflow
module's `src/main/kotlin/org/opentaint/dataflow/bidi` directory.

| File | Work |
|---|---|
| `store/StaticPairLookup.kt` | Create per-member fixed-entry filters; keep current composition, seen scope and final offer order |
| `store/StaticGuidance.kt` | Filter packed candidates before owner tests; preserve LOCAL admission; assign immutable owner-family IDs; add the private query-view memo |
| `store/DemandStore.kt` | Preserve local/primitive/composed lookup order and accumulation only after final restriction |
| `ap/Reference.kt`, `ap/Demand.kt` | Reuse the rewritten canonical entry predicate and restriction; no additional AP table changes for these optimizations |
| `store/DemandResultCoverage.kt` | Keep exact semantic/protection coverage; rejected candidates add nothing |

Add focused pruning and eligibility tests beside the existing demand
workload tests. Do not replace the graph relation, method actor, subscription,
or persistent-record store.

### 5.1 Work sequence

```text
1. Finish selected demand semantics and proofs; run its regression suite.
2. Record post-rewrite reference output/workload under repository project configs.
3. Add fixed-entry C5 pruning; validate against that reference.
4. Add query-local owner eligibility; validate against step 3.
5. Run the selected project campaign and report engine/transition results.
6. Reassess remaining graph tours before proposing cross-query storage.
```

Keep separate commits for semantic rewrite, C5 work removal, and eligibility
reuse. Do not combine a new cache policy or summary delivery rewrite with them.

### 5.2 Required tests

| Test | Required observation |
|---|---|
| Fixed mapped entry mismatch with many predecessors | Same empty output; zero predecessor expansions for that state |
| FLOW prefix repaired by a mapped predecessor | Same concrete demand and summary result as the reference |
| Current left mismatch repaired by an earlier writer | Required writer-reader composition retained |
| Cycles and duplicate bridge paths | Same merged demand results; finite query; rejected state not queued |
| Full/group relations, ZERO, exact class anchors | Existing canonical composition and endpoint rules retained |
| One-step admissible and inadmissible initial shapes | Early predicate agrees with final new entry guard for fixed endpoints |
| Protection and later-run ND premise sets | Same masks and whole original premise set |
| Eligibility true/false interleaved with other families | Same answers and scratch state after each call |
| Empty graph owners, unknown root, outside-graph owner | Same first-call behavior, laziness, and exact method match |
| Cancellation during eligibility | No cached false or partial answer |
| Multiple visible views and snapshots | Answers do not leak across roots, contexts, or frozen completions |

Use the existing finite explicit demand reference and scalar AP restriction
after adapting them to the selected rewrite. Test result sets and operation
counts, not elapsed-time thresholds. The old packet-fanout and summary
workload tests remain controls; this iteration does not optimize those paths.

### 5.3 Counters and project comparison

```text
C5: candidates seen; fixed-entry rejects before owners; owner calls;
    queued/popped/duplicate states; predecessor expansions; compositions;
    FLOW states retained; complete pairs offered; accepted scalar cells

Eligibility: requests; first evaluations; true/false hits; family count;
             active visible views; memo bytes; graph vertex/edge visits
```

For fixed mapped entries, rejected branches must perform zero predecessor
expansions. For each visible view/family, first evaluations must be at most
one. These are direct work-removal acceptance criteria.

Repeat OWASP, conductor, thingsboard and Stirling-PDF with repository memory,
timeout, alias, static and field-limit settings, using `runProjectAnalyzer`.
Reuse the saved required baseline; do not rerun it. Record finding identities,
normal/demand/protection results in completed test queries, iteration times,
run-1-to-run-2 transition time, memory, and latest reached/complete/accepted
iterations. Compare stage 3 and 4 with the post-rewrite reference, not only
with the older counter run. Partial timeout operation totals are context,
not matched completed-run speedups.

The goal is a large workload reduction. Check whether C5 composition work
falls by at least a factor of two on a matched query workload. If not, identify
the remaining candidate population before adding small per-operation tuning.
This is a validation target, not a promised speedup. Do not add the two old
rejection percentages to predict combined runtime.
Use identical finite query fixtures, matched completed queries, or completed
run-2 phases for operation ratios. Different partial timeout prefixes are
not a matched workload.

## 6. Proof contract

The new formal model is
[DemandWorkPruning.lean](../../spec/lean/proposals/demand-work/DemandWorkPruning.lean).
Its scope is immutable right-endpoint composition and a fixed-graph
incremental eligibility provider. It does not replace the AP, ownership, or
whole-analyzer proofs for the semantic rewrite.

Required preservation facts:

```text
P1. Valid left composition preserves an already fixed right endpoint.
P2. A failed final-entry predicate on that endpoint stays failed.
P3. Removing that subtree loses no accepted complete query result.
P4. Evaluating the pure predicate before ownership keeps the same eligible rows.

E1. A completed owner-family answer remains valid after intervening queries.
E2. Repeating it leaves incremental scratch unchanged.
E3. Memoized query sequences preserve answers and final scratch.
E4. Stored answers are bounded by distinct queried families, at most F/view.
```

The eligibility predicate is a fixed call-graph relation. Removing calls for
impossible C5 branches may alter how far a scratch advanced, but cannot
change the Boolean answer to a later owner question. Preserve that relation
when integrating the pruning proof with the actual graph implementation.

No proof in this document authorizes pruning an unfixed FLOW state or a
repairable left endpoint. No memo proof authorizes cross-query mutable state.

The standalone model contains 29 constructive theorem declarations. It
proves accepted-output equivalence for all finite composition walks and
answer/scratch equivalence for arbitrary interleaved family-query sequences,
under the stated immutable-graph laws. It also proves the finite family
storage bound and includes executable FLOW/left-bridge and memo controls.
The scalar AP and JVM ownership integrations remain explicit validation
obligations above.

From `spec/lean`:

```sh
lake env lean proposals/demand-work/DemandWorkPruning.lean
```

The executable check returns `true`. All-theorem axiom audits use only
`propext` and `Quot.sound`; no classical choice or unproved placeholder is
used. Commands, source hashes, selected measurements, and validation output
are embedded in
[the proposal evidence](../reports/data/bidirectional-next-demand-work-20261029.json).

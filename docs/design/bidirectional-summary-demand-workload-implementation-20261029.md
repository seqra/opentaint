# Summary and demand workload: implementation proposal

Date: 29 October 2026. Source reviewed: `7b0a3eed5`.
Status: review draft. One new EXACT application rule is pending.
Production code is unchanged.

This proposal implements the selected first and second targets in
[the workload report](../reports/bidirectional-summary-demand-workload-20261029.md#8-next-design-targets),
as specified in
[the next-iteration design](bidirectional-next-demand-work-20261029.md).
It follows [the implementation proposal guide](../../spec/impl-proposal-guide.md)
and [the proof guide](../../spec/proof-guide.md).
Code below is Kotlin pseudocode unless identified as current code.

The implementation order is fixed:

```text
selected demand rewrite and entry-admission contract
    -> record the reference for that rewrite
    -> C5 fixed-entry pruning
    -> query-local owner eligibility answers
```

The demand rewrite has its own selected
[one-step specification](bidirectional-one-step-initial-refinement-20261029.md).
Sections 2 and 3 define the exact integration boundary. They do not turn its
unresolved AP application cases into hidden implementation choices.

## 1. Scope, evidence, and semantic changes

| Part | Before | After | Status |
|---|---|---|---|
| Demand admission and C5 entry guard | FLOW-form emission and geometric entry containment | Selected one-step emission and possible-output entry guard | Prior selected semantic changes; dependency |
| C5 graph lookup | Visit mapped states that can never admit the current initial | Drop those branches before owner tests and expansion | Same results as the rewritten reference |
| Eligibility | Re-evaluate fixed owner families within one view | Reuse completed true and false answers | Same answers and incremental graph state for the same request stream |

No summary replay grouping, admitted-delta link suppression, cross-query
cache, new source replay, new grounding support, IR storage, field-write
policy, or stop policy is included. Keep ordinary field and cleaner rules.
Keep ZERO, aliases, protection, full ND premises, rule identities, native
record semantics, and FULL/GROUP composition compatibility.

The recorded runtime is `c2bc5e78dfdb13f95bda970c5f4e0c247acbac29`.
The source changes since that runtime are tests, documents and formal models.
No new project run was made for this implementation proposal.

| Project, recorded 16g campaign | Latest reached | Latest complete | Accepted forward | Result |
|---|---|---|---|---|
| OWASP | run-12 | run-11 | run-11 | TIMEOUT |
| conductor | run-4 | run-3 | run-3 | TIMEOUT |
| thingsboard | run-2 | run-1 | run-1 | TIMEOUT |
| Stirling-PDF | run-6 | run-5 | run-5 | TIMEOUT |

The isolated thingsboard counter run also reaches **run-2**, completes and
accepts **run-1**, then times out. Its 3,741,361 fixed mapped-output failures
occur among 3,992,093 popped states. It performs 2,893,937 predecessor
expansions after that failure and 930,415,459 composition attempts in total.
At least 1,358,983,156 C5 reachability questions repeat a view/family pair.

These are historical interrupted-run counts, not measured improvements.
Use the reference after the demand rewrite for each performance comparison.
Do not add the old pruning and memo percentages to predict runtime.

## 2. Demand rewrite dependency

### 2.1 Selected rules

The rewrite must provide these behaviors before the performance changes:

```text
p.ANY/FLOW + p.f.g.EXACT/T -> p.f.STAR/FLOW
p.ANY/T    + p.f.g.EXACT/T -> p.f.STAR/T, DEMAND
p.ANY/T    + p.f.EXACT/T   -> p.f.EXACT/T
p.ANY/FLOW + p.EXACT/T    -> p.EXACT/FLOW
p.ANY/FLOW + p.ANY/T      -> p.ANY/FLOW
p.ANY/FLOW + p.MUST/T     -> p.MUST/FLOW
concrete U demand + supplied T, U != T -> reject
```

Use the fact after existing field limiting. Class accessors do not count as
refinement fields. Preserve static field anchors and exact class markers;
never create a class-wide `S.C.STAR` mark by taking the first array element
of a raw static path.

Concrete STAR always starts in DEMAND. The selected coverage direction can
match a deeper supplied fact, but it cannot promote the result to NORMAL.
The exact-input exception ends after the first new field. It does not keep
an arbitrary deeper exact path.

### 2.2 Canonical policy API

Add a pure internal policy, separate from stores and method actors:

```kotlin
internal interface RestrictedInitialPolicy {
    // Input is already limited; entry demand is canonically normalized.
    fun emit(entry: Pattern, actual: Pattern): Pattern?

    // True only if some valid actual can make emit(entry, actual) return initial.
    fun canEmitInitial(entry: Pattern, initial: Pattern): Boolean
}
```

Make scalar `Reference.emit` delegate to this policy. Production C2 uses
`InitialDemandResults.offer`, `has`, and `requireFamily`, not only the
standalone `emitInitials` helper. Route all three methods through that same
entry point. Use the image classifier in C5 `Reference.restrict` and in the
early C5 filter. A wrapper must not implement another tail/mark table.

```kotlin
fun restrict(initial: Pattern, raw: Conclusion, demand: DemandPattern): Conclusion? {
    val entry = normalizeDemandFieldExclusion(demand.entry)
    if (!policy.canEmitInitial(entry, initial)) return null
    if (!insideDemand(initial, entry)) return null
    return existingConclusionRestriction(initial, raw, demand)
}
```

`canEmitInitial` tests a complete initial descriptor. The earlier partial
emitter could not use self-emission. The completed scalar policy now proves
idempotence and exact image classification. That proof permits a structural
`emit(entry, initial) == initial` implementation for that policy; it is not an
assumption. Prove the corresponding law for static, E and mark-mode adapters
before using the shortcut there. Do not enumerate marks or intern hypothetical
APs. The formal emission witness is proof data, not a runtime store.

The entry guard retains the original initial. It never rewrites an existing
summary under a coarser initial. Only retained final pieces enter
`ExactDemandResults` before its `covered()` test. The current run-1 and
backward-ZERO publication bypasses remain outside ordinary C5 restriction.

### 2.3 New FLOW tails and explicit decisions

The new abstract EXACT and MUST shapes require a typed extension. Retain one
tail in `FlowTree`; no per-leaf payload bit is required. Existing `GroupKey`
already includes the tail. Extend the tail dispatch in these components:

| Component | Required dependency work |
|---|---|
| `Premise.kt`, `Demand.kt`, `ApManager.kt` | Admit the selected abstract initial shapes and define their starts |
| `Conclusions.kt`, `LeafViews.kt` | Preserve the header; an exact ancestor cannot supply a deeper position |
| `EdgeApplication.kt`, `Reference.kt` | Add proved EXACT/MUST rows without weakening ordinary IR/binding validation |
| `Summary.kt` | Select and compile the actual tail; non-STAR must not fall through to ANY |
| `ap/Groups.kt` (`FlowGroup`) | Preserve old STAR/ANY subsumption; do not let new tails use the old non-ANY-as-STAR shortcut |
| `DemandStore.Builder` | Admit new legal demand endpoints; preserve normal handoff normalization |
| `RecordStore.kt` and call replay | Validate, persist, reverse and apply the new record shapes with their actual certainty |

Keep ordinary statement and binding validators separate from summary/read-view
validators. Do not globally delete S8. New exact/must summary validation must
not admit arbitrary new IR micro-edges. Do not add runtime Universe exclusions.

Selected application rule: an abstract MUST premise requires a definite MUST
input covering the premise scope, including E. Ordinary STAR, MAY or exact-only
taint does not prove uniform taint of the whole subtree.

Selected subsumption rule: a retained NORMAL `p.STAR/FLOW -> ret.STAR/FLOW`
can subsume the corresponding `p.EXACT/FLOW -> ret.EXACT/FLOW` relation.
The implementation must verify actual coverage in the same method/direction;
the existence of such a covering NORMAL relation is not automatic.

Check this before applying a covered exact row. Existing summary and record
groups use `InitialAp` keys; same-key deduplication does not perform this
cross-premise subsumption. Extend candidate planning for live summaries and
native read views, rather than relying on a later caller-result merge:

```kotlin
fun planExactReplay(exact: Summary, actual: Pattern, visible: Summaries): ReplayPlan {
    val cover = visible.retainedNormalStarCoverOf(exact)
    if (cover != null) return ReplayPlan.useCover(cover, actual)
    return planUncoveredExactBySelectedRule(exact, actual) // Pending decision.
}
```

`useCover` ensures that the retained cover is applied through the ordinary
suffix-preserving path, at most once in that candidate plan. Do not merely
drop the exact candidate when its covering relation is absent from delivery.
Do not assume that a future cover will repair an already emitted NORMAL
result. A caller row with STAR premise and EXACT result is not subsumed by
the ordinary correlated STAR/STAR row. New-tail application still needs the
uncovered case below even after this planning change.

The user requested a complete trace before selecting an uncovered exact
application rule. The
[closed trace](bidirectional-exact-flow-replay-trace-20261029.md) derives the
exact record, the broad caller input and raw persistence through modeled
runs 1–3. It uses ordinary field reads, writes and returns, plus source/sink
rules. An inferred Box summary and a real field-limit cut keep the B demand.
It has no predefined summaries or custom pass models. The wrapper A sink
constructs the exact helper record at its single helper callsite; a separate
direct helper probe is not required.
The application rule for this uncovered case remains pending. Do not silently
choose demotion, rejection, or a new correlation representation.

The remaining emitter examples were resolved as follows:

```text
Dc=p.f.STAR/T,       actual=p.f.g.EXACT/T  -> no initial
Dc=p.ANY/T,          actual=p.STAR/T D    -> no initial
Dc=p.f.ANY/FLOW,     actual=p.ANY/T D     -> p.f.ANY/FLOW
```

STAR and EXACT demands have no unresolved ANY tail. They admit only an exact
initial at their demanded prefix; a longer supplied path does not start a new
refinement. For an ANY demand, a same-prefix STAR does not supply a new
refinement. The ancestor STAR rejection in the model is the inferred
extension of this rule, not an additional explicit user decision. A known
descendant field supplies a refinement. A broader ANY/MUST input can
descend conditionally to the demand prefix, respecting actual field E.

### 2.4 Canonical templates and total scalar selection

Use small structural templates so C2 and C5 share one executable policy:

```kotlin
sealed interface InitialTemplate {
    data object ExactAtDemand : InitialTemplate
    data object AnyAtDemand : InitialTemplate
    data object MustAtDemand : InitialTemplate
    data class StarAtNextField(val prefix: List<AccessorIdx>) : InitialTemplate
    data class ExactAtNextField(val prefix: List<AccessorIdx>) : InitialTemplate
}

fun chooseTemplate(d: Pattern, a: Pattern): InitialTemplate? {
    require(d.fact.tail in setOf(Tail.STAR, Tail.EXACT, Tail.ANY))
    require(isLegalAdmissionActual(a)) // Valid certainty, E, and base grammar.
    if (!compatibleInputMark(d.fact.mark, a.fact.mark)) return null
    if (d.fact.base != a.fact.base) return null
    val relation = relate(d.fact.path, a.fact.path)

    if (d.fact.tail != Tail.ANY) {
        if (relation.isProperDescendant || relation.isApart) return null
        if (relation.isAncestor && !a.tailAdmits(relation.remainder)) return null
        return ExactAtDemand
    }

    return when (relation) {
        Same -> when (a.fact.tail) {
            Tail.EXACT -> ExactAtDemand
            Tail.ANY -> AnyAtDemand
            Tail.ANY_TAINT -> MustAtDemand
            Tail.STAR -> null
        }
        is Descendant -> {
            val step = nextLegalRefinementField(d, a, relation.remainder)
            if (isConcreteFullDemand(d) && a.fact.tail == Tail.EXACT && step.atActualEnd)
                ExactAtNextField(step.prefix)
            else StarAtNextField(step.prefix)
        }
        is Ancestor -> when (a.fact.tail) {
            Tail.ANY -> AnyAtDemand
            Tail.ANY_TAINT -> if (a.tailAdmits(relation.remainder)) MustAtDemand else null
            Tail.EXACT, Tail.STAR -> null
        }
        Apart -> null
    }
}
```

These relation names are specification notation, not new retained runtime
objects. Implement with the existing prefix walk and immutable path helpers.
Demand entries cannot have a MUST tail. Validate this before the precise-tail
branch. Validate actual certainty flags before selection; a MUST flag on an
EXACT or STAR descriptor is invalid, not another matching case.
`nextLegalRefinementField` includes uncounted static class accessors until the
next counted field. Exact global class markers use the existing direct-marker
adapter. Validate legal static input/initial forms before interning.

Render the template with the selected demand mark. A concrete full U requires
the same supplied full T, U=T. A supplied abstract mark cannot supply a
concrete T. Preserve the existing GROUP-selector-to-full-mark binding before
this FULL-mode check; do not rename a distinct full U into T or introduce a
mark census. Run-2 and later still evaluate full marks.

Preserve actual own E on a same-prefix MUST initial. Check E before descending
from an ancestor; consume ancestor E after an admitted descent. A first-field
STAR abstraction has the selected empty E, rather than moving an exclusion
from an unconsumed deeper prefix up to that field. Carry actual exclusions in
ordinary call application as before.

```kotlin
fun canEmitInitial(d: Pattern, initial: Pattern): Boolean {
    val emitted = emitWithoutInterning(d, initial) ?: return false
    return emitted == initial // Complete key, including tail/MUST and E.
}
```

The scalar projection and image theorem is in
`RestrictedInitialPolicy.emission_is_idempotent` and
`RestrictedInitialPolicy.image_classifier_sound_and_complete`. Full adapter
proofs remain necessary; do not substitute the old partial table or an
overlap check for this invariant.

Image classification is not a global no-loss theorem. The new policy rejects
some inputs which overlap the demand, including same-prefix STAR under ANY
and a proper descendant under a precise demand. The old local emission-cover
theorem does not apply unchanged to these cells. Before implementation, prove
that reusable records or another retained analysis route cover every required
observation for each rejected cell. If this requires another behavior rule,
show a closed trace and ask for that rule. Do not add admission history,
grounding support, or a hidden source replay channel to make the proof pass.

### 2.5 Tail-aware storage and transport

```kotlin
// Preserve this header in withRoot, withLayer, grouping and interning.
class FlowTree(/* existing fields */, val tail: Tail) {
    init {
        require(tail in setOf(Tail.STAR, Tail.EXACT, Tail.ANY, Tail.ANY_TAINT))
        require(tail == Tail.STAR || tail == Tail.ANY_TAINT || exclusion.isEmpty)
        require(tail != Tail.ANY || layer == Layer.DEMAND)
    }
}
```

Keep backward MUST initials forbidden. Native MUST read views become the
existing STAR read premise/ANY demand result shapes, with their mark reversal
and exclusion laws proved for the new abstract case. Never start a backward
MUST initial or persist a DEMAND view as a new NORMAL record.

Make each FLOW selector explicit:

```kotlin
fun selectFlowFlag(tail: Tail, star: Boolean, any: Boolean, exact: Boolean) =
    when (tail) {
        Tail.STAR -> star
        Tail.EXACT -> exact
        Tail.ANY, Tail.ANY_TAINT -> any
    }
```

MUST uses its own E in the `anyExclusion` slot. EXACT uses empty E. Summary
packing emits the real header tail, not `tail != STAR ? ANY : STAR`.
EXACT contributes no ancestor match. MUST contributes an ancestor match only
after its exclusion admits the descent; its uniform taint remains MUST.
MAY targets and field cuts remain ANY/DEMAND.

Apply definite-MUST admission only to the new abstract MUST premise. Select
only uniform MUST leaves from mixed concrete TaintTrees. Keep the existing
concrete MUST record/view rules unchanged, including their pending demotion.

Selected-mark FLOW cleaners keep their existing mark-exclusion behavior.
All-mark cleaners reuse the existing EXACT/MUST spatial outcomes. Tail-aware
adapters change payload representation, not field-write or cleaner policy.
Keep new tail groups separate from existing STAR/ANY subsumption until their
own coverage laws are proved.

## 3. Components and ownership

Let `B` be
`core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi`.

| File | Change for P1/P2 |
|---|---|
| New `B/store/C5StaticDemandView.kt` | Internal filter capability and compatibility dispatch; no public API expansion |
| `B/store/StaticGuidance.kt` | Implement filtered private view; preserve packed storage; assign owner-family IDs and query-local answer array |
| `B/store/StaticPairLookup.kt` | Per-member fixed-entry filters, prospective mark checks, queue guard |
| `B/store/DemandStore.kt` | Keep result accumulation after full C5 restriction; no new query-history store |
| `B/store/StaticEntryLookup.kt` | Keep C2 calls on the existing unfiltered public API |
| `B/store/DemandResultCoverage.kt` | Keep exact result/protection coverage unchanged |

The frozen completion owns immutable geometries, labels, owner sets, IDs and
the detached graph. Each lookup owns its queues and seen sets. Each visible
view owns its memo and lazy reachability scratch. No new mutable answer
state belongs to the snapshot, a method actor, or a persistent record.

Do not change equality or hashing of facts, initial APs, rule occurrences,
MethodKeys or static edges. `Owners` is an ordinary private class with
identity equality; its new immutable ID does not change that equality.

## 4. P1: internal C5 filtering API

`GuidanceGeometry` and packed-label helpers are private to `StaticGuidance.kt`.
Do not expose those private types through the public `StaticDemandView` API.
Use an internal capability built only from existing public descriptors:

```kotlin
internal fun interface StaticCandidateFilter {
    fun keep(from: Pattern, to: Pattern, marks: GuidanceMarks): Boolean
}

internal interface C5StaticDemandView : StaticDemandView {
    fun c5Targets(
        actual: Pattern, prefixesOnly: Boolean,
        keep: StaticCandidateFilter,
    ): Sequence<StaticGuidanceEdge>

    fun c5Incoming(
        input: Pattern, flowOnly: Boolean,
        keep: StaticCandidateFilter,
    ): Sequence<StaticGuidanceEdge>

    fun c5HasComposedEndpoints(
        initial: InitialAp, outputs: List<Pattern>,
        keepTarget: StaticCandidateFilter,
    ): Boolean
}
```

The private production `View` implements this capability. Existing public
methods delegate to private implementations with `keep=null`. C2 continues
to call those public methods. This preserves its current request stream.

Reference and test views may use an internal fallback:

```kotlin
internal fun StaticDemandView.filteredTargets(
    actual: Pattern, prefixesOnly: Boolean, keep: StaticCandidateFilter,
): Sequence<StaticGuidanceEdge> = when (this) {
    is C5StaticDemandView -> c5Targets(actual, prefixesOnly, keep)
    else -> targets(actual, prefixesOnly).filter {
        keep.keep(it.from, it.to, it.marks)
    }
}
```

Provide the equivalent incoming dispatch. For preflight, the production
capability filters target existence early. A reference fallback may keep the
old coarse preflight and let filtered target enumeration return no states;
it remains correct but makes no early-owner-work guarantee.

### 4.1 Packed bridge rows

Add the overloads inside the existing private `GuidanceGeometry` class.
Replace its current `edge(label)` body with a delegation. Do not add a
shadowed extension function. The new overload reuses decoded marks:

```kotlin
private fun GuidanceGeometry.edge(marks: GuidanceMarks): StaticGuidanceEdge =
    existingEndpointConstructionWith(marks)

private fun GuidanceGeometry.edge(label: Long): StaticGuidanceEdge =
    edge(unpackBridgeMarks(label))
```

Keep current ZERO handling and exact full/group label encoding.

```kotlin
private fun rows(
    id: Int, flowOnly: Boolean = false,
    keep: StaticCandidateFilter? = null,
) = sequence {
    val row = bridges[id]
    for (i in row.labels.indices) {
        cancellation.checkpoint()
        val label = row.labels[i]
        val marks = if (keep != null) unpackBridgeMarks(label) else null

        if (keep != null) {
            if (flowOnly && label != 0L) continue
            if (!keep.keep(row.geometry.from, row.geometry.to, marks!!)) continue
        }

        val allowed = if (inherited) eligible(row.owners[i])
            else ownRows.binarySearch(packRowReference(id, i)) >= 0

        // Preserve the exact existing unfiltered order for C2.
        if ((!flowOnly || label == 0L) && allowed) {
            yield(if (marks == null) row.geometry.edge(label)
                  else row.geometry.edge(marks))
        }
    }
}
```

Rejected C5 labels allocate no complete static edge, initial AP or Facts tree.
Accepted labels decode their marks once. The null path preserves existing
eligibility-before-flowOnly behavior and does not decode new label objects
before owner selection.

Method-local W/R rows are already decoded and belong to the exact MethodKey.
Apply `keep` to each such row before yielding it. Do not broaden their owner
scope to a common method.

### 4.2 Target and source preflight are different

```kotlin
private fun hasComposedEndpointsImpl(
    initial: InitialAp, outputs: List<Pattern>,
    keepTarget: StaticCandidateFilter?,
): Boolean {
    val targetExists = existingTargetLookup(initial, keep = keepTarget)
    if (!targetExists) return false
    return existingSourceEndpointLookup(outputs) // No target filter here.
}
```

Keep the existing target split: static initials use bridge targets;
nonstatic initials use local readers. Direct local W pairs are handled in
the primitive phase. Do not expand preflight ownership or use the target
predicate on isolated source/writer rows. Their own output is not the final
right endpoint of a future composition.

## 5. P1: fixed-right pruning and composition

Extract the existing pure label composition into one helper. Keep its current
full/group compatibility test; do not introduce another equality rule.

```kotlin
fun composeMarks(left: GuidanceMarks, right: GuidanceMarks): GuidanceMarks? =
    when (left) {
        GuidanceMarks.Flow -> right
        is GuidanceMarks.Mapped -> when (right) {
            GuidanceMarks.Flow -> left
            is GuidanceMarks.Mapped ->
                if (existingCompatible(left.output, right.input))
                    GuidanceMarks.Mapped(left.input, right.output)
                else null
        }
    }
```

The helper retains the existing null-selector conditions. Geometry joining
still uses the existing static-anchor and overlap tests.

```kotlin
fun mayKeep(member: InitialAp, right: Pattern, relation: GuidanceMarks): Boolean =
    when (relation) {
        GuidanceMarks.Flow -> true
        is GuidanceMarks.Mapped -> {
            val entry = withActualOutputMarkOrCanonicalZero(right, relation.output)
            policy.canEmitInitial(normalizeDemandFieldExclusion(entry), member.toPattern())
        }
    }
```

Apply the real output label before demand normalization. The abstract mark
in packed geometry is a placeholder. Normalizing that placeholder first can
erase a concrete STAR endpoint's E.

```kotlin
forEachOriginalMember { member ->
    val keepTarget = StaticCandidateFilter { _, to, marks ->
        mayKeep(member, to, marks)
    }
    if (!view.filteredHasComposedEndpoints(member, outputs, keepTarget)) return@forEachOriginalMember

    val pending = ArrayDeque<StaticGuidanceEdge>()
    val seen = HashSet<StaticGuidanceEdge>()
    fun admit(state: StaticGuidanceEdge) {
        cancellation.checkpoint()
        if (!mayKeep(member, state.to, state.marks)) return
        if (seen.add(state)) pending.addLast(state)
    }

    for (seed in view.filteredTargets(member.toPattern(), true, keepTarget)) admit(seed)
    while (pending.isNotEmpty()) {
        cancellation.checkpoint()
        val state = pending.removeFirst()
        offerThroughFullC5(member, state.to, state.from)
        if (covered()) return // Return from the complete walk, across members.
        if (state.from.fact.base != STATIC) continue

        val keepIncoming = StaticCandidateFilter { _, _, leftMarks ->
            val marks = composeMarks(leftMarks, state.marks)
            marks != null && mayKeep(member, state.to, marks)
        }
        for (left in view.filteredIncoming(state.from, false, keepIncoming)) {
            existingCompose(left, state)?.let(::admit)
        }
    }
}
```

Each member retains a separate queue and seen set. Keep local composition
before visible composition. C5 receives complete correlated pairs. It adds
only retained result pieces before `covered()` can stop the walk.

For Mapped right states, every prepend preserves the full right descriptor.
A rejection cannot be repaired. For FLOW, the mark is not fixed; a mapped
predecessor can make the entry admissible. Always keep such FLOW states in
this implementation.

Do not prune because the current left endpoint fails raw-output restriction.
A writer can repair that endpoint. The final offer may return nothing while
its predecessor traversal remains necessary.

## 6. P2: immutable family IDs and private byte memo

### 6.1 Freeze-time construction

```kotlin
private class Owners(
    val familyId: Int,
    val graphIds: IntArray,
    val outsideGraph: Set<CommonMethod>,
)
```

Use one factory at the two current Owners construction sites:

```kotlin
var nextFamilyId = 0
fun owners(methods: Set<CommonMethod>) = Owners(
    familyId = nextFamilyId++,
    graphIds = existingSortedGraphIds(methods),
    outsideGraph = existingOutsideGraphOwners(methods),
)
// Existing bridge-label loop: owners(methods)
// Existing projected-entry loop: owners(methods)
// Final snapshot: ownerFamilyCount = nextFamilyId
```

Do not renumber graph methods, intern equal owner sets, reorder labels, or
change row references. Each constructed Owners has one stable ID in `[0,F)`.
The ID belongs only to this snapshot. It does not enter any fact or rule key.

### 6.2 Query-local lookup

```kotlin
private const val UNKNOWN: Byte = 0
private const val NO: Byte = 1
private const val YES: Byte = 2

private var eligibility: ByteArray? = null

private fun eligible(owners: Owners): Boolean {
    cancellation.checkpoint()
    if (!inherited) return existingLocalOwnerTest(owners)

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
```

Keep `reach` lazy. The outside-graph test can still return without creating
a graph scratch. Write the memo only after a normal completed answer.
An exception or cancellation installs no false result.

If outsideGraph is false, the first query for an empty graph-owner array still
calls the current `reachesAny`. It must exhaust pending work as before.
Later identical queries can reuse false.

All existing eligible sites in this view share the same table. Do not add
another memo for entries, marked outputs, or each bridge row. Local direct
owner tests remain unchanged. The view, array and scratch do not escape the
lookup. They are released together on return or cancellation.

### 6.3 Storage bound

```text
immutable metadata: one Int per Owners, one family count per snapshot
visible-view memo:   F bytes plus one array header, allocated lazily
stored answers:     at most one per family, including false
```

The captured F is 16,414, about 16 KiB per simultaneously active visible view.
The bound depends on live views, not total query count. Run-3 and later use
local-only demand and allocate no static-completion view memo.

The memo removes repeated questions, not the first graph tour of a new view.
Cross-query root reuse remains outside this implementation.

## 7. Required tests and work counters

Extend existing tests before modifying runtime loops:

| Test file | Cases |
|---|---|
| `FrozenStaticCompletionTest.kt` | IDs, own/visible ownership, outside-graph owners, exact context W/R |
| `DemandStorageDifferentialTest.kt`, `DemandSnapshotReference.kt` | Same finite explicit relation after early filtering |
| `BidirectionalEntryLookupTest.kt` | C2 uses the unchanged public/unfiltered path |
| New `StaticPairPruningTest.kt` | Fixed mapped failure, FLOW repair, left repair, ZERO, cycles, GROUP labels, concrete E normalization |
| New `StaticEligibilityMemoTest.kt` | True/false hits, A/B/A queries, empty owner array, unknown root, cancellation, view/snapshot isolation |
| `DemandCandidateWorkloadTest.kt`, `DemandLinkTest.kt` | Coverage after final restriction, protection, DEMAND presence |

Use a nonempty concrete STAR exclusion in a packed mapped row. Assert the
output label is restored before normalization and before the entry test.
Include a target-invalid/source-valid preflight case and a target-valid/
repairable-source case. The latter must not be filtered with the target test.

Use operation assertions rather than time assertions:

```text
fixed rejected state -> no queue insertion, no predecessor expansion
rejected packed label -> no owner test, no complete edge decode
first view/family evaluation -> unchanged provider call
repeated view/family evaluation -> one byte lookup, no provider call
accepted pieces -> same tails, marks, E, layers, protection, whole premise
```

No raw-output deduplication may hide a missing composition in the reference
comparison. Compare merged semantic results and required observations, not
only final counts.

## 8. Proof-to-code contract

| Contract | Formal model | Code boundary |
|---|---|---|
| Total scalar selection is a projection, and the entry guard has an executable witness | `RestrictedInitialPolicy.emission_is_idempotent`, `image_classifier_sound_and_complete`, `entry_intersection_exactly_matches_emitter_image` | Canonical policy and final C5 guard |
| Concrete STAR starts/stays DEMAND | `OneStepRefinement.current_concrete_star_starts_demand` and layer lemmas | Initial start, transfer and summary application |
| An actual NORMAL STAR cover subsumes its exact relation | `AbstractTailContracts.normal_star_identity_geometry_covers_exact`, `dropping_exact_preserves_union_when_cover_is_present` | Same-method summary subsumption |
| New abstract MUST needs definite MUST input | `AbstractTailContracts.only_definite_must_is_admitted`, `layer_does_not_create_must` | New abstract MUST premise matching |
| Ordinary code can produce the disputed NORMAL raw record under the unchanged new-domain replay cell | `RestrictedInitialPolicy.CodeOnlyExactReplay.code_only_false_normal_is_persisted`, `code_only_false_pair` | Pending EXACT application rule; regression certificate |
| Fixed right endpoint cannot be repaired by prepend | `DemandWorkPruning.prepend_preserves_fixed_right` | `composeMarks`, immutable right geometry |
| Pruning preserves accepted finite-walk outputs | `DemandWorkPruning.c5_fixed_right_pruning_keeps_outputs` | Per-member queue and seen set |
| Early pure filtering preserves row order and output | `DemandImplementationContracts.early_filter_preserves_rows`, `early_filter_preserves_decoded_outputs` | Packed rows and local candidates |
| Memo preserves answers and exact scratch for interleaved queries | `DemandWorkPruning.memo_execution_preserves_results_and_scratch` | Private visible view |
| 0/1/2 encoding implements the logical memo | `DemandImplementationContracts.byte_step_refines_logical_step`, `write_preserves_representation` | ByteArray lookup and update |
| IDs preserve payload and identify distinct families | `DemandImplementationContracts.owner_id_injective`, `owner_payload_unchanged` | Freeze factory |
| Memo size is bounded | `DemandWorkPruning.memo_defined_cells_bound_by_distinct_families` | F-byte array and query lifetime |

The three support files contain 58 checked theorems: 40 in the scalar policy
and two trace certificates, seven in abstract-tail contracts, and 11 in
implementation contracts. The active code-only trace has 11 theorems. The
earlier declared-transfer trace stays in the model as historical evidence;
the active trace uses ordinary code and source/sink rules only.
The scalar policy is total within its stated scope: FULL marks,
ordinary nonstatic bases, counted fields, and empty exclusions. Static
anchors, ZERO, GROUP adapters, exclusions, complete new-tail application,
and global no-loss discharge remain separate obligations. The EXACT
counterexample certifies a gap; it does not prove a repair.

Run these commands from `spec/lean`:

```sh
lake env lean proposals/initial-emission/RestrictedInitialPolicy.lean
lake env lean proposals/initial-emission/AbstractTailContracts.lean
lake env lean proposals/demand-work/ImplementationContracts.lean
lake env lean proposals/demand-work/DemandWorkPruning.lean
```

All three support files compile. Their five executable checks return `true`.
All-theorem axiom audits contain only `propext` and `Quot.sound`; they contain
no classical choice, unproved axiom, or `sorry`. Commands, hashes, theorem
names and complete audit output are in the
[implementation evidence](../reports/data/bidirectional-summary-demand-workload-implementation-20261029.json).
This is formal validation within the stated scope, not JVM or project-run
validation. Do not infer missing integration proofs from generic pruning
and memo theorems.

For the graph bridge, preserve these source invariants:

```text
true answer: an outside-graph match, or an owner in monotone seen
false answer: no outside-graph match and pending exhausted
other family calls cannot remove seen hits or restart exhausted traversal
```

Thus a repeated answer would not advance scratch even after intervening
families. P1 can remove questions from the stream; it need not preserve the
old unpruned scratch. P2 preserves scratch for its own remaining stream.

## 9. Commits, measurements, and completion

```text
1. Resolve prerequisite choices; complete demand/domain/image proofs and tests.
2. Implement selected demand rewrite; capture its reference results.
3. Add internal C5 capability and pure filter controls.
4. Add fixed-entry C5 pruning; run differential and pipeline tests.
5. Add immutable family IDs and query-local memo; test state equivalence.
6. Run selected project campaign; compare against step 2 and saved baseline.
```

Keep semantic and work-removal commits separate. Use the repository project
memory/time settings, FULL default, statics and aliases enabled, and the
selected `1,1,2,3,...` schedule. Use `runProjectAnalyzer`, not the CLI. Reuse
the saved required baseline; do not rerun it.

Report run-1 time, transition time, each iteration's time, memory, OOM/timeout,
findings, and latest reached/complete/accepted iteration. For work ratios use
identical finite query fixtures, matched completed queries, or completed
phases. Different timeout prefixes are not a matched performance comparison.

Record C5 candidates before/after filtering, owner calls, decoded edges,
queued/popped/duplicate states, predecessor expansions, compositions, final
offers and accepted pieces. Record memo requests, first evaluations, true/
false hits, F, simultaneously live views, bytes, vertices and graph edges.

The direct criteria are zero predecessor work for fixed rejected states and
at most one first evaluation per view/family. The performance target is at
least a twofold C5 workload reduction on a matched workload. It is not a
promised wall-time improvement or evidence that thingsboard run-2 completes.

Only declare the implementation complete after the prerequisite decisions,
proofs, meaningful tests and selected project validation have completed.
No unresolved behavior may be supplied as an implicit default.

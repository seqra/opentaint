# Implementation proposal: demand-relative summary restriction

Date: 1 November 2026. Status: implementation proposal; runtime unchanged.
Language: ASD-STE100 Simplified Technical English.

Implement [demand-relative-summary-restriction.md](../../spec/demand-relative-summary-restriction.md).
Follow [impl-proposal-guide.md](../../spec/impl-proposal-guide.md) and
[proof-guide.md](../../spec/proof-guide.md).
The [implementation proof dossier](../../spec/demand-relative-summary-restriction-implementation-proofs.md)
records the checked adapter laws and their limits.

Design baseline: `4bafc8f6b233125f87f08da0afe6887cc26add00`.
Its runtime files are identical to measured runtime
`c4a71246519ee5432879ce82518823f1703f3aa4`.
If runtime changes before implementation, review that source difference
before using this mapping.

Latest measured reached/completed/accepted iterations are Stirling-PDF
**run-8/7/7**, conductor **run-4/3/3**, thingsboard **run-2/1/1**, and OWASP
**run-5/5/5**. These are the unchanged FULL, 16 GiB campaign results. No
project run or analyzer implementation is part of this document.

## 1. Result, semantic changes, and fixed scope

```text
Previous selected edge: Dp -> Dc
Current demand row:    entry=Dc, exit=Dp

new candidate A -> B
    -> existing summary normalization
    -> existing complete paired C5
    -> field cut at min(runLimit, FL(that row's Dp)+1)
    -> admitted-summary deduplication and permitted FLOW replacement
    -> publication of the fresh admitted delta

completed barrier:
    admitted NORMAL -> existing eligible native records
    admitted selected rows -> existing next-run demand
```

`N` means NORMAL, `D` means DEMAND, `$` means EXACT, `*` means STAR,
`[any]` means MAY, and `[any-taint]` means MUST. `E` is a field exclusion.
`mx` is a FLOW mark-exclusion set. `FL` counts concrete field/element
accessors. ZERO and Target are typed control endpoints, not DATA of depth zero.

This is a semantic change. It can turn a precise NORMAL result into
MAY/DEMAND. It can delay native-record creation and a later report.
It is not equivalent to the old raw NORMAL persistence policy.

| Part | Before | After |
|---|---|---|
| C5 DATA result | Keep every permitted descendant up to the global limit | Cut each selected row result at its own Dp-relative limit |
| Summary store | Raw relation plus a separate selected relation | One admitted relation and filtered views |
| Publication | Deduplicate raw candidate before C5 | Deduplicate final admitted results |
| Native persistence | Read eligible raw NORMAL rows | Read eligible admitted NORMAL rows |
| Outgoing guidance | Classify raw layer before restriction | Classify final stored layer and the existing control cases |
| DATA lookup completion | Raw coverage can stop later row searches | Enumerate all relevant complete rows |

Keep the following behavior:

```text
C2 emission and its normalized-preimage check
NORMAL/DEMAND initial lanes and their start layers
global body field limit and all instruction transfers
post-S MethodEdgeStore admission and cached CFG delivery
current rule, cleaner, alias, mark, exclusion, protection and ND rules
saved-record replay on every offer before current demand admission
predefined method models and their existing boundary-rule policy
run-1 static effects, lost-write collection, and lazy run-2 static completion
local-only demand lookup after run-2
typed ZERO/Target behavior, source hits, report IDs, stop policy and schedule
```

Do not implement the candidate local widening or previous-point guidance
from the [intra-procedural analysis](bidirectional-intraprocedural-growth-control-analysis-20261101.md).
Measure those opportunities after this implementation. Do not add raw
caches, new source permissions, GroundingSupport, or a new demand-save API.

## 2. Code map and ownership

All paths below are relative to
`core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/`.

| File | Proposed work |
|---|---|
| `store/DemandStore.kt` | Exact C5 then per-row cut, for local, control, carry and virtual DATA rows |
| `store/DemandResultCoverage.kt` | Keep exact-result/protection union; remove DATA raw-coverage machinery |
| `store/StaticPairLookup.kt` | Keep the existing row traversal; its stop callback is false for DATA collection |
| `engine/RunMethodAnalyzer.kt` | Restrict before summary admission; publish only admitted deltas |
| `store/RunSummaries.kt` | Remove the raw/selected split; expose admitted and outgoing views |
| `ap/Demand.kt` | Extract the existing final-header selection predicate without changing its truth table |
| `store/RecordStore.kt` | Read admitted rows; retain current eligibility checks |
| `driver/HandOff.kt` | Pass direction to the filtered view; preserve endpoint projection |
| `engine/JoinedStaticGuidance.kt` | Read the run-1 admitted outgoing view with FORWARD direction |
| `driver/IterationDriver.kt` | Label admitted/outgoing counts correctly; retain barrier order |
| `store/FlowBackedSummaries.kt`, `store/DiagonalRelations.kt` | Optional filtered census traversal over existing packed storage; no new coverage law |

The actor owns demand admission. RunSummaryStore owns the admitted relation.
Do not give that store a DemandStore, caller history, or method analyzer.
The AP layer continues to own field-cut and protection transport.

## 3. Per-row DATA limit

Use the exit selector of the complete row that selected the result.
`FL` counts field and element accessors, not static class accessors.

```kotlin
private fun conclusionBudget(exit: Pattern, policy: RestrictedInitialPolicy): Int {
    val depth = exit.fact.path.count { it.isCounted() }
    val global = policy.fieldLimit
    check(global >= 1)
    // Clamp before addition. The default policy can use Int.MAX_VALUE.
    return if (depth >= global) global else depth + 1
}
```

Do not use `path.size`, the current premise depth, a maximum over other
rows, or an ND member chosen only for its depth. A JVM static class anchor
costs zero; its named field costs one. A typed ZERO exit has no budget.

Keep `ApOps.restrict` and `ApOps.limit` as the exact and abstraction steps:

```kotlin
private fun offerDataPair(
    member: InitialAp,
    raw: Facts,
    pair: DemandPattern,
    policy: RestrictedInitialPolicy,
    out: ExactDemandResults,
) {
    val exit = pair.exit ?: return
    val budget = conclusionBudget(exit, policy)
    for (selected in ops.restrict(member, raw, pair, policy)) {
        ops.limit(selected, budget, object : ApOut {
            override fun result(f: Facts) { out.add(f) }
            override fun markRequest(mark: TaintMark) =
                error("A field cut must not emit a mark request")
        })
    }
}
```

This helper is for a DATA exit. Control ZERO exits use section 4.2.
For legacy AP-form ZERO endpoint views inside the existing static walker,
dispatch ZERO as control before computing a field budget. Do not count
the `ap.zero` adapter as a depth-zero DATA selector.

The current `ops.restrict` packs exact results and transports protection.
The current `ops.limit` separates uncut and cut pieces and transports the
same annotation. Reuse both. Do not enumerate full marks or replace the
field cut with manual tail/mark edits.

```text
uncut piece: preserve tail, layer, E, mx and protection
cut piece:   MAY, DEMAND, empty field E; preserve base, mark/mx and protection
```

Do not call `RunMethodAnalyzer.cut` here. That method applies instruction
policy, hooks, and the global body limit. C5 needs only the AP field cut
with this complete row's budget.

## 4. DemandStore lookup

### 4.1 DATA rows

Keep the current complete-row indexes and candidate guards. Change the
consumer of each selected row:

```kotlin
fun offer(member: InitialAp, pair: DemandPattern) {
    cancellation.checkpoint()
    val exit = pair.exit ?: return
    if (exit.fact.base == AccessPathBase.Zero) {
        if (raw is Reach) {
            for (selected in ops.restrict(member, raw, pair, policy)) result.add(selected)
        }
    } else {
        offerDataPair(member, raw, pair, policy, result)
    }
}

// These routes continue to call the SAME offer function:
local indexed complete pairs
shared run-2 static carry pair
local primitive completion pairs
local transitive completion pairs
visible transitive completion pairs
```

Use the same `ops.restrict` adapter where the static walker already
provides AP-form ZERO endpoints. A Reach result is retained as Reach.
A DATA result cannot satisfy that typed ZERO exit.

Do not cut a raw candidate before exact C5. That could make an unrelated
or excluded result appear compatible. Do not cap the union using one
shared budget after different rows have selected their results.

Keep the full original on every return from `intersect`. Its member is
only the existing C2-image witness. An ND output keeps the complete ND key.

### 4.2 Control rows and Reach saturation

Use the existing control entry matching. For a DATA exit, first perform
its AP restriction, then use its DATA budget:

```kotlin
visitControlPairs(method, policy, includeDerived = original.isZero) { pair ->
    if (!entryAccepts(pair.entry, original, policy)) return@visitControlPairs true
    when (val exit = pair.exit) {
        DemandExit.Zero -> if (raw is Reach) result.add(raw)
        is DemandExit.Data -> if (raw !is Reach) {
            offerDataPair(ap.zero, raw,
                DemandPattern(ap.zero.toPattern(), exit.pattern), policy, result)
        }
    }
    !saturated()
}
```

The only selected early-stop predicate in this implementation is:

```kotlin
fun saturated(): Boolean = raw is Reach && result.hasResults
```

For fixed `raw = Reach(layer)`, every accepted complete row returns that
same Reach. After one such result, more rows cannot add a new result.
The [adapter proof](../../spec/demand-relative-summary-restriction-implementation-proofs.md)
establishes this set-saturation law.

For DATA, `saturated()` is always false. Replace all old
`result.covers(raw)` calls in `intersect`, including the static-walk stop
callbacks, with this predicate. Retain structural impossibility guards,
visited-state sets, and the existing local/visible order. Do not build the
full static closure at handoff.

Keep `acceptsTarget` as the current read-only Reach probe through the same
lookup machinery. It can stop after its first complete Reach result.
Do not replace it with a local-control-only query: virtual static paths
can supply the missing complete ZERO permission.

This preserves the selected Target protocol. It does not add a new
NormalTarget gate or a terminal field limit.

### 4.3 Query-local result union

Remove raw-coverage tracking from ExactDemandResults. Keep its current
exact Facts union and protection OR:

```kotlin
internal class ExactDemandResults(private val ap: ApManager) {
    private val values = LinkedHashMap<Facts, Facts>()
    val hasResults: Boolean get() = values.isNotEmpty()

    fun add(value: Facts) {
        // Keep the existing exact-payload match and monotone protection merge.
        // Facts equality itself still omits protection.
        mergeExactPayloadAndProtection(values, value)
    }

    fun all(): List<Facts> = values.values.toList()
}
```

`mergeExactPayloadAndProtection` denotes the existing body of `add`; do
not create a new merge law. Remove `coverage`, `coverageChecked`,
`RawCoverage`, and `covers`. Do not change InitialDemandResults or C2's
separate fully-covered rule.

Two compatible rows can retain both a precise NORMAL result and a
shorter DEMAND result. Exact-result union must not remove either merely
because the first result covers the raw input. Existing permitted
FLOW-backed replacement runs later in the admitted-summary store.

## 5. Actor admission and publication

### 5.1 Preserve the surrounding producer pipeline

Keep the existing order through the normal exit:

```text
instruction or existing run-1 static shortcut
    -> exit rules, observations and existing adjustments
    -> existing global producer bound
    -> post-exit MethodEdgeStore fresh delta
    -> retainSummary
```

Do not suppress a local writer registration or accepted source callback
because its later summary is rejected. Run-1 static supplies remain
independent of summary persistence. Keep exceptional-exit behavior.

The post-instruction store remains unchanged. It does not destructively
replace concrete memberships with raw FLOW. Its fixed pure gate can
consume fresh leaf/annotation deltas; the adapter model proves the
corresponding finite leaf-union law.

### 5.2 Restrict before RunSummaryStore mutation

Rewrite `retainSummary` around its current validation and run-1 hooks:

```kotlin
private fun retainSummary(rawPremise: PremiseKey, rawFacts: Facts) {
    if (!RuntimeDataDomain.packet(rawPremise, rawFacts)) return
    val normalized = normalizeFlowSummary(ap, rawPremise, rawFacts)
    val premise = normalized.premise
    val facts = normalized.facts
    validateExistingSummaryCandidate(premise, facts)
    if (!context.shared.interpreter.isSummaryBase(facts.base)) return

    // Keep the current run-1 computed-supply and erased-static-seed hooks here.
    if (run1StaticHooksConsume(premise, facts)) return

    val admitted = if (config.run1) listOf(facts) else
        checkNotNull(config.demand).intersect(key, premise, facts, config.admissionPolicy)

    for (piece in admitted) {
        ap.cancellation.checkpoint()
        validateExistingSummaryResult(premise, piece)
        val delta = summaries.addAdmitted(premise, piece) ?: continue
        edgeDeltas++
        if (delta.layer == Layer.DEMAND) demandLayerEdges++
        pending += Publication(premise, delta)
    }
    if (pending.isNotEmpty()) requestWork()
}
```

The validation and hook names in this snippet abbreviate current code.
They do not authorize new behavior or a helper with another owner.
Keep canonical FLOW normalization, runtime-domain checks, legal tails,
summary-base checks, and the exact current static seed/supply effects.

Run-1 has no previous demand. Its candidate still passes the same actor
admission boundary, under its existing first-run policy. Do not introduce
a finite artificial Dp or blanket FULL TAINT demotion.

Remove `published` and the old `queuePublications` split. No raw `selected`
Boolean is computed. Keep the existing flush barrier, detached batch,
work reservation, and exception/requeue behavior.

### 5.3 One admitted collection

```kotlin
class RunSummaryStore(private val m: ApManager, flowBacked: Boolean = false) {
    private val groups = IdentityHashMap<PremiseKey, ConclusionGroup>()
    private val interners = m.newInterners()
    private val backed = if (flowBacked) FlowBackedSummaries(m) else null

    // The actor is the production writer. Call only AFTER admission.
    fun addAdmitted(premise: PremiseKey, facts: Facts): Facts? {
        if (!RuntimeDataDomain.packet(premise, facts)) return null
        checkShape(premise, facts)
        backed?.let { return it.add(premise, facts) }
        return groups.getOrPut(premise) { ConclusionGroup(m, interners) }.add(facts)
    }

    fun all(): Sequence<Pair<PremiseKey, Facts>> = backed?.all() ?: entries(groups)

    fun demandEdges(direction: Direction): Sequence<Pair<PremiseKey, Facts>> =
        all().filter { (premise, facts) ->
            selectedForHandoff(premise, facts.layer, direction)
        }
}
```

Do not interpret a null delta from an enabled backend as permission to
insert into the scalar fallback. Null means no fresh admitted effect.
There must be one authoritative relation, not two competing copies.

Remove `demand`, `backedDemand`, and `addDemand`. `all`, `borrow`, census,
and native persistence now describe admitted state. Rejected candidates
leave no summary state. Do not add a deduplication history for them.

Keep current FLOW-backed coverage and protection rules. Only admitted
FLOW can become a provider. A cut FLOW cannot act as a NORMAL provider,
but an admitted DEMAND FLOW can still cover an unprotected DEMAND concrete
counterpart in the existing permitted cell.

## 6. Handoff, census, persistence, and frozen actors

### 6.1 Final-header selection

Extract the current selection truth table in `ap/Demand.kt`:

```kotlin
internal fun selectedForHandoff(premise: PremiseKey, layer: Layer, direction: Direction): Boolean {
    if (layer == Layer.DEMAND) return true
    val single = premise as? InitialAp ?: return true // current NORMAL ND case
    return direction == Direction.BACKWARD && single.isZero
}

internal fun selectDemand(m: ApManager, premise: PremiseKey, facts: Facts,
                          direction: Direction): Facts? {
    m.cancellation.checkpoint()
    return facts.takeIf { selectedForHandoff(premise, it.layer, direction) }
}
```

This is a mechanical extraction. It does not delete NORMAL ND or NORMAL
backward-ZERO guidance. The predicate reads final admitted headers.

Pass direction from stable run inputs:

```kotlin
// HandOff: add direction to forEachDemandPiece's arguments.
for ((premise, facts) in actor.summaries.demandEdges(direction)) { /* existing projection */ }

// JoinedStaticGuidance is run-1 only.
actor.summaries.demandEdges(Direction.FORWARD)
```

Do not read `actor.config.direction` after freeze. `config` is reached
through the actor's released context. HandOff already has the completed
RunConfig/direction; pass that value into its helper.

Keep endpoint reversal, exclusion/mark normalization, full ND projection,
Target projection, physical seeds, explicit-row counts, and the stop test.
No `saveDemandForNextRun` call or new incremental demand collection exists.

### 6.2 Census without a second store

Keep `census()` for all admitted rows. Implement
`demandCensus(direction)` as a filtered traversal of the same store.
Use the same selector as `demandEdges`.

For scalar groups, test the existing premise and final Facts header.
For diagonal rows, test the scope's final layer and nonzero-singleton
header before counting its existing geometry and mark masks. Such rows
cannot be ZERO or ND. Their selection does not depend on a decoded mark.
The adapter proof checks this key independence.

Do not decode one scalar tree per mark to collect the census. The existing
`DiagonalRelations.census(counter)` loop can accept a header predicate and
skip unselected scopes. Retain its logical-membership and protection weights.
This traversal is numeric and read-only; it is not another admitted index.

```kotlin
// FlowBackedSummaries: scalar groups and packed diagonal scopes use one predicate.
fun census(include: (PremiseKey, Layer) -> Boolean = { _, _ -> true }): RelationCensus

// RunSummaryStore: delegate to the existing backend or scalar traversal.
fun demandCensus(direction: Direction): RelationCensus =
    census { premise, layer -> selectedForHandoff(premise, layer, direction) }
```

Change the driver log labels from `raw/selected` to `admitted/outgoing`.
Do not compare the new admitted census with the old raw census as if they
were the same population. Candidate-offer counters are separate.
For the enabled experiment diagnostics, collect this census at every
completed run, not only run-1. Log its scan time as a separate barrier
cost. It must not become an unconditional hot-path scan.

### 6.3 Native records

Keep `PersistentRecordStore.persist` eligibility code. Its input `all()`
now returns admitted rows:

```kotlin
for ((premise, facts) in store.all()) {
    if (facts.layer == Layer.DEMAND) continue
    val initial = premise as? InitialAp ?: continue
    if (direction == Direction.BACKWARD && initial.isZero) continue
    checkNativeRecord(direction, initial, facts)
    mergeAndIndexExistingNormalRecord(method, direction, initial, facts)
}
```

Update raw-storage comments. Do not restore an uncut NORMAL record when
restriction rejects or demotes a candidate. Do not purge older valid
records. Saved replay and predefined-summary application keep their current
matching and order. Any new inferred caller summary uses the caller gate.

Keep barrier order: report preparation, admitted NORMAL persistence,
handoff, frontier/stop decision, and terminal/report commit. Retain the
existing cancellation and completed-run checks.

### 6.4 Targets and first-run statics

Reuse existing `emitTarget`, Target storage, report catalog, source hits,
and native ZERO-to-Target conversion. NormalTarget keeps its normal-only,
forward-only, retained-key skip rules. DemandTarget uses its existing
paired Reach probe, with the proved Reach saturation above.

Run-1 static survivor inspection now reads admitted first-run summaries.
That first-run admission policy is unchanged. Preserve erased static
seeds and immediate writer supplies. The requested feature does not add
static relays, static field requests, or a new closure store.

## 7. Remove obsolete state and assumptions

Remove or rewrite these entities together:

```text
RunSummaryStore.demand
RunSummaryStore.backedDemand
RunSummaryStore.addDemand
RunMethodAnalyzer's raw-layer selected Boolean
RunMethodAnalyzer.published / old queuePublications split
ExactDemandResults.RawCoverage, coverage, coverageChecked and covers
DATA C5 raw-coverage early returns
comments/log labels that describe raw NORMAL persistence
tests that require rejected raw summaries to remain in all()
```

Keep MethodEdgeStore, InitialFactStore, RequestStorage, current subscription
storage, static completion, native records, and typed Target storage.
Do not remove the generic static-walk stop callback: Reach queries still
have a proved saturation condition. DATA calls pass a predicate that is
always false.

Do not add a new field to Facts, InitialAp, PremiseKey, Publication,
Subscription, or CallerRef. Row provenance, budgets, and diagnostic labels
are query/instrumentation state, not semantic equality or hashing fields.

## 8. Proof-first and TDD work

### 8.1 Constructive reference

Run the existing specification proof checker, then the implementation
adapter checker linked from the dossier. The latter reuses the actual
scalar C5/cut gate and adds:

```text
packed finite-leaf reference and fixed-gate delta distribution
complete paired provenance through that reference
Reach singleton-output saturation and Target-probe equivalence
final admitted filtered-view laws and diagonal-key independence
measurement accounting and counterexamples to attribution from C5 counts alone
```

The finite reference is the correctness target. It does not verify Kotlin
DAG packing, all FLOW/MUST cells, or general convergence. Required adapter
tests close those concrete correspondences within the selected scope.

### 8.2 Red tests before runtime edits

Use production AP, actor, store, persistence, and handoff fixtures.
Do not test only `min(depth+1, limit)`.

| Test group | Required checks |
|---|---|
| C5 per-row limit | Existing C5 keeps depth 3; Dp depth 0 cuts to depth 1; deeper Dp preserves the precise NORMAL result |
| Multiple rows | Deep precise NORMAL plus shallow DEMAND, both row orders, all relevant local/visible rows, no crossed entry/exit permission |
| Packed fields | Mixed kept/cut leaves, shared suffixes, arrays, uncounted class accessor, marks and protection OR |
| Exclusions | Preserve uncut later-run E/mx; clear only cut field E; retain mark exclusions; honor exact C5 rejection before cut |
| Admission/persistence | Rejected NORMAL is absent from summary/publication/native state; cut NORMAL is DEMAND and in the frontier; uncut eligible NORMAL persists |
| Replacement | Rejected FLOW cannot cover; cut FLOW is not a NORMAL provider; existing admitted D-to-D replacement and protected survivors still work |
| Controls | ZERO-original DATA is capped; Reach only meets ZERO exit; NormalTarget behavior is unchanged; final NORMAL ND/backward-ZERO rows still guide |
| Frozen state | Build handoff after actor.freeze without consulting released config/context |
| Call paths | Current publications and both directions of saved replay; every-offer replay stays before C2; no-demand route remains unchanged |
| Full pipelines | Actual source permission recovery, two-field wrap/unwrap, conditional producer with good/bad callers, static-to-Target completion |

Update `RestrictedDemandProtocolTest` cases that assert raw storage after
rejection. Their new expected result is no admitted summary and no native
record. Preserve their negative publication assertions. Update synthetic
fixtures that currently call both `add` and `addDemand`: insert one
explicitly pre-admitted row instead.

Add an independent small scalar enumerator: exact C5 for each complete row,
then scalar limit, then annotated union. Compare its result with packed
DemandStore.intersect over a finite test matrix. Include nonempty E/mx,
different row budgets and protection upgrades. Compare semantic leaf sets
and annotations, not only group counts or Facts equality.

For Reach, compare the early-stop implementation with exhaustive row
enumeration, including lazy static paths and cycles. For DATA, include the
known precise-NORMAL/shorter-DEMAND counterexample; an early stop must fail it.

Run the complete common-core and JVM suites, then the selected OWASP and
project campaign. Do not weaken a failed source/Target test by adding a
raw NORMAL fallback. If a new behavior choice is required, provide the
code and fact trace for a user decision before changing the contract.

## 9. Post-implementation experiments: locate the remaining blow-up

The experiment must answer the user's question without assuming a local
or inter-method cause. In particular, many C5 cuts do not prove that body
growth caused the time: call application can generate the same deep shapes.

### 9.1 Fixed comparison and runs

Use the latest implementation commit and record its full hash. Reuse the
saved same-runtime FULL/16 GiB campaign for the immediate comparison and
the fixed legacy baseline receipts for finding identities. Do not rerun
the legacy baseline.

Use OWASP as in its CI workflow and the selected real projects through
the direct `runProjectAnalyzer` Gradle task. Keep the selected model/input
hashes, FULL mode, statics/aliases enabled, limits `1,1,2,3,…`, and 16 GiB.
Use the saved selected budgets: 1,000 seconds IFDS for OWASP and 1,080 for
each real project, with the 1,200-second outer command budget. If the
selected configuration changes before execution, record that change and
qualify the comparison; do not silently mix experiments.

Use the saved project-specific init scripts with the same direct task:

```sh
# From core/; the selected init script supplies the model and JVM parameters.
./gradlew :runProjectAnalyzer --console=plain \
  -I <selected-project>/bidi/benchmark.init.gradle \
  -x :opentaint-ir:go:buildGoServer
```

Do not enable local point guidance, cycle widening, GROUP mode, or another
field schedule in this campaign. The new summary gate is the only selected
analysis change. Report any diagnostic overhead separately.

Prioritize these windows, but report every reached iteration:

```text
Stirling-PDF: backward run-6 and run-8; adjacent forward run-5/run-7 controls
conductor:    backward run-4; forward run-3 control
thingsboard: run-2 C5/static lookup; retain run-1 and handoff measurements
OWASP:       complete findings, outgoing frontier, and stopping behavior
```

The new iteration path can differ. Do not force an old frontier or claim
a missing old run is a failure: earlier convergence may be an improvement.
Conversely, lower per-run time with more iterations is not sufficient.
Report total engine/barrier time and all demand frontiers.

Require no new missed findings against the current-runtime receipts.
Also account for every fixed legacy-baseline identity. Existing missing
findings remain open issues; do not relabel them as passing because this
patch preserves them. OWASP must retain its 4,112 baseline identities.

### 9.2 Measurements and populations

Use separate cumulative event counts and retained-set censuses:

| Population | Required data |
|---|---|
| Body | Processed packets, fresh post-statement memberships, depth/tail/mark-kind distribution, base class, full-original kind, protection upgrades |
| Candidate offers | Summary candidate packets and logical membership attempts, before C5; no claim that these are a retained unique raw set |
| C5 | Visited complete-row attempts, exact rejects/results, row source, Dp depth, selected depth, budget, extra-cut input/output memberships, NORMAL-to-DEMAND cuts |
| Admitted summaries | Fresh admitted deltas, retained memberships, publication packets, final NORMAL/DEMAND split, protection and FLOW replacement |
| Inter-method work | Current delivery notifications, candidate subscriptions tested, applied matches, saved matches, caller continuations, fresh caller outputs |
| Barrier | New NORMAL native records, outgoing AP/control/Target frontiers, source hits, completed report identities, phase time and memory |

Separate FLOW annotations from concrete-mark memberships. Record static
field, exact static class-marker, nonstatic and typed control populations.
Do not count a FLOW wildcard as one membership per full mark. A packed
packet is not one scalar fact. Shared DAG nodes are not the number of
logical field paths.

For C5 sampled leaf attempts, use this decision partition:

```text
visited row/leaf attempts = exact rejects + selected uncut + selected cut
selected results         = selected uncut + selected cut
```

These are per-row attempts. Different rows can select the same result.
Do not subtract them from unique admitted rows to claim an exact number
of dead facts. Count annotation-only upgrades separately from new ordinary
memberships. The measurement model checks this partition and the ambiguity
between local generation and inter-method generation.
Attach Dp/budget samples to the exact per-row cut. A later merged admitted
group or publication can contain leaves from several rows; it has no single
Dp or last-row budget against which all its leaves must be checked.

### 9.3 Correlate body growth with later C5 collapse

Collect, by run, method, oriented CFG component and producing point:

```text
fresh point memberships and their counted-depth histogram
instruction transfers and call-stage executions
growth on cycle re-entry versus acyclic points
same-payload/protection-only repeats versus different paths
```

Assign points to CFG components once from the existing graph. Identify
cycle components by a multi-node SCC or a self-loop; do not infer a loop
from a repeated field name. A component ID is diagnostic graph state,
not a new fact property.

At the summary gate, collect a separate histogram:

```text
(run, method, direction, full-original kind,
 base kind, FLOW/TAINT, raw layer/tail,
 FL(raw), FL(Dp), FL(exact-selected), budget, FL(admitted),
 selected tail, admitted tail, protected?, local/virtual row)
```

Use shared method IDs to correlate the expensive body components with
their candidate and cut distributions. A high body count and high cut
count in one method is evidence to investigate, not a per-fact ancestry
proof. Do not retain full provenance on every live fact to obtain it.

For the leading methods, capture bounded diagnostic event traces and
construct reduced tests from the real instructions/rules. Trace:

```text
input/initial -> changing field paths at relevant points
             -> candidate A -> B
             -> matching complete Dc/Dp row
             -> exact C5 result
             -> MAY/DEMAND collapse
             -> admitted/publication/native/handoff effects
```

The report must show code under analysis with inline facts and all relevant
FLOW providers for representative protected/subsumed cases. It must state
which part is a captured value, which is a replay, and which is a reduced
model. Do not replace unavailable project shapes with an illustrative
method and call it a measured project cause.

### 9.4 Separate intra-procedural and inter-method causes

Use both event counters and disjoint profile scopes. Separate current
delivery, saved replay, direct call stages outside those callbacks,
ordinary non-call transfer, C5 lookup/cut, and other work. If inclusive
stack percentages overlap, show them as inclusive and do not add them.
Use the same classification for before/after captures.

| Hypothesis | Evidence needed | Evidence that points elsewhere |
|---|---|---|
| Body path explosion later collapsed to MAY | Many fresh distinct paths in growing CFG cycles; body CPU/allocation dominates; sampled candidates map many deep paths to shallow Dp-relative results | Few body memberships or mostly equal output attempts; time is in delivery or C5 |
| Inter-method join explosion | Many producer alternatives times caller suffixes/origins; high applied-match count and fresh caller path growth; summaries can individually fit their budgets | Most applications converge to equal results without fresh growth |
| Repeated equal call-stage work | High shared-stage/resume count and few fresh caller outputs, with equal full states after matching annotations | Most outputs are different paths or protection upgrades |
| C5/virtual static enumeration | Time/allocations in row selection/composition, high visited states/rows per query after removal of DATA coverage stops | Growth occurs before C5 and C5 is a small time share |
| New refinement/native-cache cost | Fewer admitted NORMAL records, more DEMAND frontiers, repeated later analysis/native misses, extra iterations | Iteration count/frontiers and native coverage remain stable |

The first two can coexist. A deep local candidate can have been produced
by a call. Report the creation stage and later propagation separately.
Do not infer that every post-change blow-up is intra-procedural merely
because summary depths now satisfy their bounds.

### 9.5 Required reduced controls

Use production engine/AP controls in addition to the project profiles:

1. **Read loop, fixed inputs:** limits 1/3/5/7, one admitted key and fixed
   boundary demand. Compare body work and C5 output. This is a negative
   control: an output-only gate need not reduce already performed body work.
2. **Many deep results sharing one prefix:** verify C5 depth compliance,
   fresh admitted/publication compression, protection, and no raw NORMAL
   record. Compare caller delivery counts, not only summary count.
3. **Small summaries, large join:** apply `ret.* -> {p.left.*,p.right.*}`
   to several caller suffixes and several callers. Show that input/result
   products can remain despite bounded summary depth.
4. **Convergent reverse aliases/native views:** show equal continuation
   results and output deduplication. This separates duplicate stage work
   from distinct field paths. Do not change every-offer native replay.
5. **Refinement progress:** exact-DEMAND, wrap/unwrap, source permissions,
   conditional source, and typed Target cases through later forward runs.
   Verify findings and native-record recovery, not only a nonempty frontier.
6. **Two row budgets and Reach:** DATA must preserve the N+D union; Reach
   must retain its existential early exit, including static completion.

For a suspected real-project root cause, derive one additional small
production test from a captured hot method/pattern. A general loop model
alone is not sufficient to label a whole project timeout.

### 9.6 Observer cost, snapshots, and report contents

Use existing statistics/profile switches and optional diagnostic counters.
Default execution must not keep whole candidate histories. Use numeric
counters, fixed depth bins, and bounded samples of copied scalar descriptors.
Release query/point references before actor freeze. Do not add diagnostic
metadata to Facts or semantic keys. Capture point statistics before freeze
because MethodEdgeStore is then released.

Use DAG-aware count operations for packed censuses. Do not enumerate every
scalar mark on every hot event merely to count it. For expensive shape
data, document the deterministic sampling rule, denominator, cap and drops.
Label exact counters and estimates separately. A diagnostic rerun must use
the same analysis configuration and be reported separately from the main
timing if instrumentation changes its cost.

Capture profiles under the target iteration, not merely at command wall
time. Use normal-load and near-limit windows when the iteration lasts long
enough; record run markers and capture intervals. Close all captures.
Collect GC/resource data. On an actual MemoryManager OOM, capture and
analyze its fresh heap snapshot. Do not use an old heap as evidence for
the new implementation. Clean previous experiment profiles/snapshots as
required by task.md before new captures.

Write a report that embeds its principal tables and representative shapes;
do not depend on an untracked `shape-probe-results` directory. Include:

```text
implementation/config/model hashes
latest reached, completed and accepted run labels
all iteration engine/barrier times and incoming/outgoing frontiers
finding identity comparison and traced differences
body, C5, admitted, native and inter-method populations with exact definitions
subsumable/protected/non-covered shape examples and relevant FLOW edges
disjoint CPU/allocation scopes and current live-memory evidence
one or more reproduced hot patterns, with observed versus inferred claims
the supported root cause, remaining uncertainty, and next algorithmic target
```

If performance regresses, classify whether the cause is more body work,
more joins, more exhaustive C5 search, lost native reuse, or more refinement
iterations. Do not propose a local widening fix until the evidence supports
that cause. The next recommendation should avoid a large family of work,
not only make one operation somewhat faster.

## 10. Implementation order and completion gates

1. Run and bind the constructive specification and adapter checks. Add the
   failing production tests from section 8 against the pinned runtime.
2. Add per-complete-row C5 cuts and the DATA/Reach completion distinction.
   Keep C2 and static traversal semantics unchanged.
3. Reorder actor summary admission, remove the duplicate raw/selected
   summary state, and retain publication/barrier ownership.
4. Update final-header selection, frozen handoff, packed census and native
   consumers. Remove old raw assumptions and update focused tests.
5. Run packed/scalar differential tests, source/Target/ND regressions,
   complete common-core/JVM checks, and the selected project campaign.
6. Complete the post-implementation root-cause report. State whether the
   new gate reduced work, moved work to later runs, or exposed another
   pattern. Report limits and unresolved findings before acceptance.

Implementation is complete only when source-bound checks, required tests,
finding comparison, and the experiment report are available. Passing the
Lean kernel alone is not implementation or project acceptance.

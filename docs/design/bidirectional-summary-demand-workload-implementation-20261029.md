# Next iteration: implementation proposal

Date: 29 October 2026. Source reviewed: `6ed31830f`.
Status: proposal only. No production code changes are included.
Use ASD-STE100 Simplified Technical English.

This document replaces the earlier implementation draft. It implements:

- [One-step initial emission](bidirectional-one-step-initial-refinement-20261029.md), with the latest STAR-demand correction below.
- [FLOW summary normalization and write exclusions](bidirectional-flow-summary-normalization-20261029.md).
- [The selected C5 and owner-eligibility work removal](bidirectional-next-demand-work-20261029.md).

It follows [the implementation guide](../../spec/impl-proposal-guide.md) and
[the proof guide](../../spec/proof-guide.md). Code blocks are Kotlin pseudocode
unless marked as code under analysis. Use the existing manager and interner
APIs where a sketch shows a descriptive helper name.

Notation: STAR (`*`) preserves a correlated field suffix; EXACT (`$`) names
only the stated position. ANY (`[any]`) is an uncertain suffix. MUST
(`ANY_TAINT`, `[any-taint]`) means uniform taint. FLOW is the abstract mark
slot; T and U are full marks. E excludes fields; mx excludes marks. C2 is
initial admission. C5 is paired summary restriction. Dc is the demand entry
for the current run; Dp is its paired exit.

## 1. Scope and selected semantic changes

Implement the semantic changes first. Then capture a reference. Compare the
two performance changes with that reference.

| Part | Before | Selected behavior |
|---|---|---|
| Restricted C2 | Abstract demand emits its FLOW form | ANY demand resolves one field; retain selected exact and uniform cases |
| STAR demand | Earlier proposal rejected a marked child | Run-2 emits the requested STAR; later answers are precise, as below |
| Outgoing FLOW demand | A partial operation can retain STAR/DEMAND | From run-2, FLOW demand conclusions are ANY; no STAR/DEMAND export |
| New EXACT/FLOW | Rejected by typed factories | Read barrier; field effects retain E through point transfer |
| Summary boundary | Raw point premise is also the storage key | Normalize each pure FLOW EXACT endpoint to STAR before storage |
| C5 | Geometric containment | Normalized emitter image, then the existing conclusion restriction |
| RemoveAll | Terminal AnyField can mean below-only removal | Whole selected position only; named fields are valid |
| C5 search | Expand fixed impossible right endpoints | Reject those branches before owner tests and expansion |
| Owner eligibility | Repeat graph questions in a view | One completed answer per immutable family per view |

Keep full marks by default, mark compatibility, mark-group selection,
source/sink identities, ZERO rules, ND semantics after run-1, protection,
alias closure, field limits and stop policy. Keep the existing run-1
field-write rule: updating E moves the affected result to DEMAND and clears
E. This is not a weak-write policy.

The new EXACT/FLOW exclusion is an explicit new-tail contract. It does not
change concrete EXACT/T. Whole-position-only RemoveAll is also an explicit
semantic change. No grounding support, source replay channel, origin store,
completed-query cache, cross-query graph cache or IR storage is added.

### Evidence and latest iterations

The saved runtime is `c2bc5e78dfdb13f95bda970c5f4e0c247acbac29`. Production
sources are unchanged. No new project run is claimed here.

| Saved 16g campaign | Latest reached | Latest complete | Accepted forward | Result |
|---|---|---|---|---|
| OWASP | run-12 | run-11 | run-11 | TIMEOUT |
| conductor | run-4 | run-3 | run-3 | TIMEOUT |
| thingsboard | run-2 | run-1 | run-1 | TIMEOUT |
| Stirling-PDF | run-6 | run-5 | run-5 | TIMEOUT |

The thingsboard counter run reaches run-2 and completes run-1. It has
3,992,093 popped C5 states, 3,741,361 fixed-right failures, 2,893,937
predecessor expansions after failure and 930,415,459 compositions. At least
1,358,983,156 owner questions repeat a view/family pair. These are historical
interrupted-run counts, not matched speedup measurements.

## 2. Ownership, APIs and implementation files

Let B be `core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi`.
Let J be `core/opentaint-dataflow-core/opentaint-jvm-dataflow/src/main/kotlin/org/opentaint/dataflow/jvm/bidi`.

| File | Change |
|---|---|
| New B/ap/RestrictedInitialPolicy.kt | Pure run-aware emission and explicit image classifier |
| New B/ap/FlowSummaryNormalization.kt | Normalize a complete pair and a selected conclusion; assert normal form |
| B/ap/Premise.kt, Conclusions.kt, ApManager.kt, Reference.kt | New EXACT/MUST FLOW guards, raw query starts, latent write E |
| B/ap/EdgeApplication.kt, LeafViews.kt, Summary.kt, Groups.kt | Tail-aware transfer, matching, header selection and safe grouping |
| B/ap/Clean.kt, Primitives.kt; J/interp/JIRRuleForms.kt | Whole-position RemoveAll; field lowering; direct FLOW residuals |
| B/ap/Demand.kt; B/store/DemandResultCoverage.kt | C2 policy delegation, normalized C5 pieces, conservative coverage |
| B/engine/RunMethodAnalyzer.kt | Canonical summary admission before storage and publication |
| B/store/RunSummaries.kt; B/engine/PublicationIndex.kt | Assert canonical summary pairs; retain exact keys and protection |
| B/engine/CalleeSubscriptions.kt, PublicationIndex.kt | STAR coverage candidates in both delivery orders |
| B/store/RecordStore.kt; B/ap/Reference.kt | Native canonical FLOW and abstract MUST read views |
| B/driver/HandOff.kt, engine/RunConfig.kt | Validate receiving-run demand grammar; keep source/sink seed handling |
| New B/store/C5StaticDemandView.kt | Internal filtered lookup capability |
| B/store/StaticPairLookup.kt, StaticGuidance.kt | Fixed-right pruning; owner-family IDs; per-view memo |

Point state owns raw query initials and their exact tails. Summary storage
owns canonical pairs. Demand snapshots own immutable query indexes. Each
lookup owns its queues. Each visible static view owns its graph scratch and
memo. No mutable query answers belong to a snapshot or a native record.

EXACT -> STAR intentionally merges summary keys. Do not change rule IDs,
MethodKey equality, or fact equality to attach compiler metadata. E, tail,
layer and mark exclusions already belong to FLOW group keys. Owner IDs do
not enter fact or rule keys.

## 3. Run-aware C2 admission

### 3.1 Mode and the demand grammar

```kotlin
data class AdmissionMode(
    val run: Int,
    val direction: Direction,
    val fieldLimit: Int,
    val markMode: MarkMode,
)

interface RestrictedInitialPolicy {
    fun emit(entry: Pattern, boundedActual: Pattern): Pattern?
    fun canEmitInitial(entry: Pattern, rawInitial: Pattern): Boolean
}
```

Create one immutable policy for the run. Pass it to `DemandStore.initials`,
`InitialDemandResults`, scalar `Reference.emit`, and C5. It is not a cache.
Keep run-1 `Run1Abstraction` unchanged. Its first limit is 1.
The restricted policy requires `run >= 2`.

The latest restriction applies to the outgoing DEMAND conclusion, which
becomes the next demand entry Dc. It does not prohibit STAR in the paired
exit Dp or in a NORMAL summary.

```kotlin
fun validateIncoming(mode: AdmissionMode, d: DemandPattern) {
    if (d.entry.isFlow) {
        require(d.entry.tail == Tail.ANY ||
            (mode.run == 2 && d.entry.tail == Tail.STAR))
        require(d.exit == null || d.exit.isFlow)
        require(d.exit == null || d.exit.tail in setOf(Tail.STAR, Tail.ANY))
    }
}

fun assertRestrictedFlowResult(mode: AdmissionMode, facts: Facts) {
    if (mode.run >= 2 && facts is FlowTree && facts.layer == Layer.DEMAND)
        check(facts.tail == Tail.ANY && facts.exclusion.isEmpty)
}
```

ANY here means MAY, with no uniform-MUST certainty. Use this at the actual
producer/boundary. Do not silently change a broken
STAR/DEMAND result to ANY at export. Fix the producer. Run-1 may export
STAR/FLOW DEMAND. The run-1 static completion and shared static carry are
installed for run-2 only. A later FLOW Dc=STAR is an invalid snapshot, not
an unanswered later-prefix choice.

Concrete STAR/T demands remain a separate domain. They can request STAR on
run-2. Later they use precise EXACT answers at the demanded position; the
former precise descendant rejection applies there. ANY-demand first-field
STAR initials remain legal on later runs: they start NORMAL for FLOW and
are not STAR/FLOW DEMAND results.

### 3.2 Complete ordinary scalar table

Use the fact after the existing field cut. Match base and mark first. A
concrete U demand rejects T when U differs from T. FLOW accepts the
compatible actual mark but renders the selected demand mark.

| Demand | Actual position/tail | Raw initial |
|---|---|---|
| ANY/M | Same prefix, EXACT | EXACT/M |
| ANY/M | Same prefix, ANY | ANY/M |
| ANY/M | Same prefix, MUST | MUST/M |
| ANY/M | Same prefix, STAR | None |
| ANY/M | Proper descendant | Stop after first new counted field; STAR/M |
| ANY/T | Descendant ends EXACT at that first new field | EXACT/T exception |
| ANY/M | Broader ANY/MUST | Demand prefix, retain actual ANY/MUST certainty |
| ANY/M | Broader STAR or EXACT | None |
| STAR/M, run-2 | Proper descendant | Requested STAR/M at demand prefix |
| STAR/T, later | Proper descendant | None |
| STAR/M or EXACT/M | Same prefix | EXACT/M |
| STAR/M or EXACT/M | Broader admitted non-EXACT actual | EXACT/M at demand prefix |
| EXACT/M | Proper descendant | None |
| Any | Different base, incompatible mark, excluded descent, or apart paths | None |

Later STAR/FLOW rows are outside the incoming grammar. Preserve all
unmodified cells above; do not change same-prefix STAR to STAR merely to
make self-emission idempotent.

```kotlin
fun choose(d: Pattern, a: Pattern): InitialTemplate? {
    val entry = normalizeDemandFieldExclusion(d)
    if (!sameBase(entry, a) || !compatibleInputMark(entry.mark, a.mark)) return null
    val r = relate(entry.path, a.path)
    if (!admittedPrefixRelation(entry, a, r)) return null

    if (entry.tail == Tail.STAR && r.isProperDescendant) {
        if (mode.run == 2) return RequestedStar(entry.path, entry.exclusion)
        check(!entry.isFlow) // Later FLOW STAR entries are invalid.
        return null
    }
    return selectedUnchangedCells(entry, a, r) // The complete table above.
}
```

Concrete demand E is retained and checked before admitting a child. Only
existing abstract STAR demand E normalization clears E. Do not lift an
actual's deeper E to the broader requested STAR. Concrete STAR initials
always start DEMAND; FLOW STAR starts NORMAL. EXACT starts NORMAL. ANY
starts DEMAND. MUST is forward-only and starts NORMAL. Caller DEMAND still
joins into every applied result.

### 3.3 Static, exclusion and mark adapters

Run the existing static FULL-anchor validator before generic refinement.
Class accessors do not consume the field budget; fields and elements do.
A static field initial keeps `[class, field]` together. Never select a raw
array element as a refinement and create class-wide `S.C.*`.

Keep exact global class markers in their direct concrete-marker protocol.
They stay EXACT/T; they are not normalized as FLOW or converted to a
class-wide STAR. The legal abstract root `S.* / FLOW` default is separate:
on run-2 it can accept a named descendant through the requested-STAR rule.
Keep the static input validator's named-field, root-default and exact-marker
cases distinct. Test them before implementing the generic path walk.

MUST means explicit uniform taint, not a synonym for DEMAND or ANY. At a
same-prefix MUST admission preserve its own E. Consume ancestor E only
after it admits a real descent; keep the demanded prefix's own constraints.
A first-new-field STAR has selected Empty E. GROUP selectors first use the
existing selector-to-full-mark binding; do not invent a mark census or
rename a distinct full U to T.

### 3.4 Explicit raw emitter image

The new run-2 requested STAR has an actual descendant witness. It need not
emit itself: the unchanged same-prefix STAR cell emits EXACT. Therefore
remove the old self-emission shortcut.

```kotlin
fun canEmitInitial(entry: Pattern, initial: Pattern): Boolean =
    legalRawInitial(initial) && classifyOutputTemplate(entry, initial).any { template ->
        template.hasValidSubmittedWitness(mode.fieldLimit, staticGrammar, markPolicy)
    }
```

Implement structural template tests, not a runtime enumeration of actual
facts. Exact/ANY/MUST and one-field templates use the table's executable
witness classes. Requested STAR at the demand prefix needs a legal proper
child after limiting. In the ordinary counted-field model this requires
`demandDepth < fieldLimit`; at the cap there is no such witness. Static
anchors use the existing class/field grammar. No possible key is interned.

Use the same policy in `InitialDemandResults.offer`, `has`, and
`requireFamily`. Their existing keys deduplicate actual initials. Missing
families are structural possible-output keys, not another answer history.

## 4. New FLOW tails and point transfer

Keep one tail per FLOW header. No per-leaf payload flag is needed.

```kotlin
// InitialAp: EXACT/FLOW and MUST/FLOW are now query shapes.
require(tail != Tail.EXACT || exclusion.isEmpty)
require(mark !is MarkSlot.Star || mark.excluded.isEmpty)

// FlowTree / scalar Conclusion:
require(tail in setOf(STAR, EXACT, ANY, ANY_TAINT))
require(tail != ANY || (layer == DEMAND && exclusion.isEmpty))
// EXACT/FLOW conclusions may carry E. Concrete EXACT/T may not.
```

`initialFacts` must use the actual tail and explicit layer, not the factory's
layer-derived default. Preserve tail/E/mx in manager conversion, `withRoot`,
`withLayer`, leaf views and result grouping. A raw EXACT query starts with
Empty E. Its derived FLOW result can acquire a field-effect exclusion.

### 4.1 Read versus write-preserve effect

```kotlin
fun PathEdge.isExcludedIdentityKeep(): Boolean =
    from.base == to.base && from.path == to.path &&
    from.tail == STAR && to.tail == STAR && exclusion.isNotEmpty()

fun exactFlowTransfer(c: Conclusion, e: PathEdge): Conclusion? {
    return when (val r = relate(e.from.path, c.path)) {
        is Same -> exactTailCopy(e.to.base, e.to.path,
            c.exclusion.union(e.exclusion)) // Retain incoming EXACT, not target STAR.
        is ActualBelowPremise -> admittedSuffixCopy(c, e, r.suffix) // Keep c's own E.
        is ActualAbovePremise -> if (e.isExcludedIdentityKeep())
            mayAt(e.to.base, e.to.path) // Proper-prefix write residual; DEMAND, Empty E.
        else null           // Ordinary field read: preserve the EXACT read barrier.
        Apart -> null
    }
}
```

This sketch covers the STAR-target FLOW cell. Keep the complete existing
mark gate, target tail and exclusion tests around it. Use the same rules in
scalar `Reference.below/above/normalize` and typed `EdgeApplication.flow`.
The excluded identity keep already describes the write effect; add no new
stored origin label. Real field reads must not be promoted by this test.

For `p.f.g = value`, retain the existing residual split:

```text
p.$/FLOW -> p.$/FLOW, output E={f}, NORMAL
p.$/FLOW -> p.f.[any]/FLOW, DEMAND, Empty E
```

The first normalizes to a STAR summary with E={f}. The inner demand preserves
work for unaffected suffixes below f. Do not replace it with a NORMAL p.f
STAR continuation or drop it because an ordinary read would be blocked.
Run-1's exclusion policy still demotes and clears E.

`nearLeafViews` and summary selectors must not match a new EXACT header as
an ordinary ancestor leaf. Flow-tail selection is explicit:

```kotlin
when (actual.tail) {
    STAR -> selectStar()
    EXACT -> selectExact()
    ANY -> selectMay()
    ANY_TAINT -> selectUniformMust(actual.exclusion)
}
```

### 4.2 MUST matching

A new abstract MUST premise requires a definite MUST actual covering its
scope and exclusions. STAR, MAY and root-only EXACT do not establish it.
Select only the MUST leaves of a mixed TaintTree. Preserve the input layer
join and the existing concrete-MUST matching/demotion policy. No backward
MUST initial is admitted.

Make `FlowGroup` tail dispatch explicit. The old non-ANY branch must not
classify a new EXACT or MUST header as STAR. Keep unproved cross-tail
subsumption out of point groups. Canonical STAR summaries continue through
the existing all-run FLOW-backed replacement rules, including protection.
Do not extend those rules to a MUST premise without its definite-input law.

## 5. Whole-position RemoveAll and the restricted FLOW grammar

```kotlin
// JIR rule validation; keep existing rejection scope/diagnostics.
is RemoveAllMarks -> if (resolvedPosition.any)
    reject("RemoveAll requires a whole position")

// For an admitted root or named field:
Cleaner(p.base, p.path, CleanReach.AT_AND_BELOW, mark = null)

// Bidi primitive constructor, including generated CallCleaners:
require(mark != null || reach == CleanReach.AT_AND_BELOW)
```

`RemoveAll(p.f)` is valid: remove p.f and descendants, preserve p and p.g.
Reject a terminal AnyField below-only all-mark action. Keep selected
RemoveMark reach, mark requests and mark exclusions unchanged. Existing
Spring generated whole-position cleaners remain valid.

Keep named-field read/temporary-clean/strong-write lowering. The final write
records E even if an EXACT/FLOW read of the child produced no temporary
fact. The preserved parent continues through that sequence.

For a legal direct all-mark primitive, use the same whole-subtree kill
residuals. Whole-root cleaning kills. A whole-field clean at f has a normal
outer exclusion; nested cleaning keeps the existing inner ANY/DEMAND
residual. If a direct conservative partial cell remains, its uncertain
result is ANY/DEMAND: never restore EXACT over that DEMAND result. Concrete
selected-mark cleaner handling is unchanged.

Audit all restricted FLOW producers:

| Producer | Result class |
|---|---|
| FLOW initial STAR/EXACT/MUST | NORMAL |
| FLOW initial ANY | ANY/DEMAND |
| Copy, filter, selected-mark cleaner | Preserve class/header |
| Same-prefix strong write | NORMAL/E, or preserve incoming ANY/DEMAND |
| Nonuniform ancestor read or proper-prefix loss | ANY/DEMAND |
| Admitted uniform MUST descent | MUST/NORMAL; consume ancestor E, retain target E |
| Field cut | ANY/DEMAND |
| Whole-position RemoveAll | Kill, preserve normal residual/E, or ANY/DEMAND |
| Native abstract-MUST backward view | ANY/DEMAND result |
| Reversed may pass | Generic revTails maps STAR->ANY to ANY->ANY |

Do not change generic micro-edge reversal. Its existing tail table already
keeps reversed MAY output uncorrelated. Run-1-only static demotion and
STAR/DEMAND remain guarded by run-1. ND/combinations are TAINT-only.
Assert the restricted FLOW result invariant at summary/publication and
handoff boundaries; use producer tests to find violations, not a silent
STAR-to-ANY boundary coercion.

## 6. Normalize summaries and C5 results

### 6.1 One complete boundary pair

```kotlin
data class SummaryForm(val premise: PremiseKey, val facts: Facts)

fun normalizeSummary(p: PremiseKey, f: Facts): SummaryForm {
    if (!p.isFlow || f !is FlowTree) return SummaryForm(p, f)
    val i = p as InitialAp
    val stored = if (i.tail == EXACT)
        manager.initial(i.base, i.path, STAR, i.exclusion, i.mark) else i
    val result = if (f.tail == EXACT)
        manager.flowTree(f.base, f.layer, f.exclusion, f.markExclusion, f.root, STAR)
    else f
    return SummaryForm(stored, result)
}

fun retainSummary(rawInitial: PremiseKey, rawFacts: Facts) {
    val s = normalizeSummary(rawInitial, rawFacts)
    assertCanonicalSummary(s)
    // Keep existing summary-base/disabled-static filters and computed supplies.
    if (erasesRun1StaticSummary(s.premise, s.facts)) {
        staticGuidanceSeeds.add(s.premise, s.facts)
        return
    }
    val delta = summaries.add(s.premise, s.facts) ?: return
    queuePublications(s.premise, delta)
}
```

Point MethodEdgeStore premises remain raw EXACT. Do not rekey the method
analysis. Normalization preserves bases, field chains, E, mx and layer. It is
idempotent. TAINT, ND, ZERO and concrete exact class markers are unchanged.
Deduplication uses the canonical pair before notification.

Assert canonical FLOW in `RunSummaryStore.add/addDemand`, the real summary
publication index, predefined schema admission and native record storage.
Do not put this assertion in the generic `Publication` constructor: joined
static writer binding also uses it as a raw point adapter.

Keep static write points and killed-write observation keys raw. When those
rows become guidance, canonicalize both observed and surviving comparison
keys. Otherwise normalization could look like a killed write. Do not change
raw static supplier facts or normalize instantiated predefined outputs.

### 6.2 C5 uses the normalized raw-query image

```kotlin
fun canStoreInitial(entry: Pattern, stored: Pattern): Boolean {
    fun fits(raw: Pattern): Boolean =
        policy.canEmitInitial(entry, raw) && insideDemand(raw, entry) &&
            normalizeFlowInitial(raw) == stored
    if (fits(stored)) return true
    return stored.isFlow && stored.tail == STAR && stored.exclusion.isEmpty &&
        fits(stored.withTail(EXACT))
}
```

The raw candidate uses the current run's table and budget. Keep its legality
and mark/E tests. There are at most two raw preimages. Test raw containment,
not whole canonical STAR containment against an EXACT query. Never use
self-emission as the image classifier.

### 6.3 Normalize selected pieces before keys and coverage

```kotlin
// Reference.kt: replace the old first premise-containment guard.
fun restrictStored(initial: Pattern, raw: Conclusion, pair: DemandPattern): Conclusion? {
    val entry = normalizeDemandFieldExclusion(pair.entry)
    if (!canStoreInitial(entry, initial)) return null
    return restrictConclusionOnly(raw, pair.exit) // Existing mark/base/path rules.
}

// Demand.kt: restrictRaw uses restrictStored, not the old double-guard path.
// Demand.kt: restrictPlainFacts
for (selected in restrictRaw(ops, canonicalInitial, canonicalRaw, pair)) {
    val kept = normalizeFlowSummaryConclusion(selected)
    val piece = manager.factsOf(kept.fact, kept.exclusion, kept.layer)
    mergeByGroupKey(piece)
}
// Every DemandStore.offer path receives canonical pieces here.
```

The order is mandatory:

```text
raw point relation
 -> normalize pair -> raw store
 -> full C5 paired restriction
 -> normalize each kept FLOW conclusion
 -> Facts/group-key merge -> ExactDemandResults.add -> coverage test
 -> Publication / addDemand
```

Extract the conclusion-only helper from the code after the former
`insideDemand` check. Do not call that old guard again on canonical STAR.
Raw containment is already tested on a possible raw query by `canStoreInitial`.

When C5 takes an EXACT root slice of a same-prefix MUST/FLOW result, preserve
its latent E. A concrete EXACT/T slice still has Empty E. On an admitted
descent, consume ancestor E at its old prefix; never move it onto the new
prefix. The STAR/E result must remain covered by the uniform source result.

Actual paired FLOW Dp is STAR or ANY after canonicalization and MUST handoff
projection. Keep that grammar. A restricted raw ANY/DEMAND stays ANY under
those pairs. Unsupported arbitrary mixed test snapshots must not manufacture
a late STAR/FLOW DEMAND result.

Keep `ExactDemandResults.covers` based on the original canonical raw packet.
ANY and MUST always exhaust: another pair can rebase or select a distinct
piece. For STAR/EXACT raw packets, retain exact leaf, layer, E, mx and
protection equality. Do not substitute geometric STAR coverage for this
query-completion test.

## 7. Summary delivery and native records

### 7.1 Concrete STAR coverage in both delivery orders

```kotlin
fun supportsDescendantActual(j: Pattern): Boolean =
    j.mark is MarkSlot.Star || j.tail == STAR
```

Use this alongside existing restrictions in scalar `satisfies`, typed
`Summary.satisfyingPart`, and both candidate indexes. A concrete STAR initial
must cover a deeper actual with the same mark and admitted suffix. Its
summary/result remains DEMAND.

```text
PublicationIndex: a new deep actual must find an existing STAR premise prefix.
CalleeSubscriptions: a new STAR publication must find existing deep actuals.
Final AP match: check mark, tail, E and the whole original ND premise.
```

Keep candidate snapshotting and callback ownership. Updating only the final
predicate loses deliveries. Do not extend the STAR fallback to concrete
ANY/MUST indiscriminately.

### 7.2 Native FLOW normal form and MUST views

The persistent record store (R1) takes canonical NORMAL singleton pairs from
raw summary storage, before C5. No FLOW EXACT record is stored. Retain
nonempty E on NORMAL records. The previous covered-EXACT replay planner and
abstract EXACT native-record extension are removed from the implementation
plan.

New abstract MUST initials/results still need native read views:

```text
forward native FLOW (MUST/Ei) -> (MUST/Eg or canonical STAR/Eg), NORMAL
backward read premise: old result scope as STAR/Eg
backward result:       old MUST input scope as ANY/DEMAND, Empty E

forward native FLOW STAR/Ei -> MUST/Eg, NORMAL
backward read premise: old result scope as STAR/Eg
backward result:       old input scope as ANY/DEMAND, Empty E
```

The view preserves existing mark reversal. It forgets the old MUST-input E
only where the existing demand projection does. It is transient: do not
start, intern or persist it as a new NORMAL record. If a canonical STAR
result came from a MUST exact slice, it still needs this MUST-input view;
the old concrete-only EXACT/MUST guard is insufficient.

Keep concrete native record cases and generic `revEdge` unchanged. A
backward record has no MUST initial. Definite-MUST forward application is a
separate gate. Record availability does not suppress C2 or add a completed
query cache.

## 8. C5: internal C5 filtering API

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

### 8.1 Packed bridge rows

Add the overloads inside the existing private `GuidanceGeometry` class.
Replace its current `edge(label)` body with a delegation. Do not add a
shadowed extension function. The new overload reuses decoded marks:

```kotlin
private data class GuidanceGeometry(/* existing endpoint fields */) {
    fun edge(marks: GuidanceMarks): StaticGuidanceEdge =
        existingEndpointConstructionWith(marks)

    fun edge(label: Long): StaticGuidanceEdge = edge(unpackBridgeMarks(label))
}
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

### 8.2 Target and source preflight are different

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

## 9. C5: fixed-right pruning and composition

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
            canStoreInitial(normalizeDemandFieldExclusion(entry), member.toPattern())
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

## 10. Owner eligibility: immutable family IDs and private byte memo

### 10.1 Freeze-time construction

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

### 10.2 Query-local lookup

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

### 10.3 Storage bound

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

## 11. Principal regression traces

The code-under-analysis convention is fixed: demand and submitted facts go
above the declaration; summaries go after the closing brace.

### 11.1 Run-1: an overwrite produces a precise STAR demand

```java
// Source rule in main: assign exact T to q.g. Sink: check T at m(q).g.
// f != g. Aliases can be disabled for this regression.
// Previous demand: none. Submitted: p.g.$/T.
// Emitted initial: p.*/FLOW; start NORMAL.
Root m(Root p) {
    p.f = new Leaf();
    // The preserve edge needs E={f} on p.*.
    // Run-1 policy: p.*/FLOW, DEMAND, Empty E.
    return p;
    // ret.*/FLOW, DEMAND, Empty E.
}
// Produced NORMAL return summaries: none.
// Produced DEMAND return summary: p.*/FLOW -> ret.*/FLOW.
// Run-2 entry demand: ret.*/FLOW; exit: p.*/FLOW.
```

The new Leaf has no mark. The concrete mark on g really survives the
write. No usable NORMAL return record exists to answer the backward call.

### 11.2 Run-2: answer the requested STAR and find the source

```java
// Previous demand: entry ret.*/FLOW; exit p.*/FLOW.
// Submitted backward fact: ret.g.$/T, DEMAND.
// Run-2 emitted initial: ret.*/FLOW; start NORMAL.
Root m(Root p) {
    p.f = new Leaf();
    // Backward keep: p.*/FLOW, NORMAL, E={f}.
    return p;
    // Backward from ret.* to p.* first; preserve its NORMAL layer.
}
// Produced NORMAL: ret.*/FLOW -> p.*/FLOW, output E={f}.
// Produced DEMAND return dependency: none.
// Applying the NORMAL answer to ret.g/T gives q.g/T (caller layer DEMAND).
// g is not excluded. The backward source hit enables the next forward source.
```

The old descendant-rejection diagnostic stays in Lean as historical evidence.
The selected run-2 policy now proves this route reaches the source. Its
NORMAL record later maps q.g/T to ret.g/T with suffix g intact.

### 11.3 Exact query, write E, canonical summary

```java
// Previous demand: entry p.[any]/FLOW; exit ret.*/FLOW.
// Submitted: p.$/T. Emitted raw initial: p.$/FLOW, NORMAL, E={}.
Root keepOtherFields(Root p) {
    p.f = new Leaf();
    // p.$/FLOW, NORMAL, E={f}. Exact read barrier remains.
    return p;
    // ret.$/FLOW, NORMAL, E={f}.
}
// Raw point relation: p.$/FLOW -> ret.$/FLOW, NORMAL, output E={f}.
// Stored NORMAL summary: p.*/FLOW -> ret.*/FLOW, output E={f}.
// No input at p.f can pass through this NORMAL row; p.g can.
```

### 11.4 Whole-position field removal

```java
// Previous demand: entry p.[any]/FLOW; exit ret.*/FLOW.
// Submitted: p.$/T. Emitted raw initial: p.$/FLOW, NORMAL.
Root clearField(Root p) {
    removeAll(p.f);
    // Legal: clear p.f and its descendants.
    // Lowering is read/clean/strong-write. Parent write effect E={f} survives.
    return p;
}
// Stored NORMAL summary: p.*/FLOW -> ret.*/FLOW, output E={f}.
// Keep parent/sibling flow. RemoveAll(p.f.AnyField) is rejected.
```

Use real code and source/sink rules in the JVM regression. Do not replace
these operations with predefined summaries. Predefined schemas have their
own isolated tests.

## 12. Tests, proof contracts and validation

Write failing tests before changing runtime loops. Separate semantic tests
from work-removal tests. A counter example must name its actual producer,
emitted initial, stored row, publication and receiving iteration.

| Test area | Required checks |
|---|---|
| Scalar initial matrix | Complete table; exact mark mismatch; ANY first field; exact-input exception; run-2 requested STAR; later phase grammar |
| Bounded image | Executable witness; requested STAR needs remaining counted-field budget; canonical FLOW STAR can still have EXACT raw preimage at cap |
| Static adapters | Named field plus class anchor; fields/elements counted; exact global class markers; root S.* distinct from S.C.* |
| E adapters | Demand E checked; actual prefix E consumed at admitted descent; no deeper-mask lift; raw EXACT query Empty E |
| New FLOW tail factories | EXACT/MUST starts; layer independent of tail; EXACT/E point grouping; leaf views; withRoot/withLayer/conversion |
| Transfers | Ordinary EXACT child read absent; same-prefix write E; nested proper-prefix ANY demand; return/binding E; run-1 demotion |
| Whole RemoveAll | Root and p.f valid; named subtree removed; sibling survives; terminal AnyField rejected; generated partial all-mark primitive rejected |
| C5 | Canonical raw preimage plus containment; MUST-to-EXACT slice keeps E; normalization before group keys/coverage; all member premises retained |
| Summary delivery | Existing/new deep actual and old/new concrete STAR publication, both orders; mark/E rejection; concrete STAR remains DEMAND |
| Native records | No FLOW EXACT; nonempty E persists; abstract MUST->STAR and MUST->MUST views are pending ANY; no backward MUST start |
| Mode closure | Run-1 STAR/FLOW demand allowed; every restricted producer emits valid FLOW classes; no later STAR/FLOW demand entry |
| Static integration | Write-point keys stay raw; canonical survivor comparison; no false killed-write row; actual labels restored before normalization |
| P1 | Fixed mapped rejection; unfixed FLOW repair; repairable left endpoint; ZERO; groups; cycles; raw target/source preflight distinction |
| P2 | True/false hits; A/B/A interleaving; empty owners; outside-graph root; cancellation; separate views/snapshots |

Extend `BidirectionalEntryLookupTest`, `DemandStorageDifferentialTest`,
`DemandSnapshotReference`, `FrozenStaticCompletionTest`,
`DemandCandidateWorkloadTest`, `DemandLinkTest`, and the JIR cleaner mapping,
validation and lowered-effect tests. Add focused tests for new point tails,
canonical summaries, late FLOW grammar, P1 pruning and P2 memoization.
Update tests that deliberately construct now-prohibited partial all-mark
cleaners to assert rejection. Keep selected-mark and generic geometry tests.

For P1/P2 use operation assertions, not timing assertions:

```text
fixed rejected state: no enqueue, no predecessor expansion
rejected packed label: no owner query or complete edge decode
view/family first evaluation: the existing graph/outside-root test
repeat evaluation: one byte-table hit, no graph question
semantic output: equal normalized facts, E/mx/layers, protection and whole premise
```

### 12.1 Constructive proof-to-code map

`DemandStarPolicy` below is short for
`RestrictedInitialPolicy.DemandStarPolicy`.

| Law | Model / theorem | Implementation boundary |
|---|---|---|
| Selected run-2 image has an executable witness | `DemandStarPolicy.image_classifier_sound_and_complete` | Raw template classifier |
| Current budget is part of witness validity | `DemandStarPolicy.bounded_image_has_executable_witness` | Field-limit adapter |
| Requested STAR is not a raw self-projection | `DemandStarPolicy.requested_STAR_is_emittable_but_is_not_a_fixed_point` | Remove the old image shortcut |
| Full U/T mismatch rejects | `DemandStarPolicy.mismatching_full_marks_are_still_rejected` | Existing mark selector |
| Concrete STAR starts DEMAND | `DemandStarPolicy.concrete_requested_STAR_starts_DEMAND` | Initial layer and application join |
| Corrected overwrite route finds source/sink | `DemandStarPolicy.ClosedWrite` | Whole call/seed regression |
| Exact canonical image includes raw containment | `FlowSummaryNormalization.Integration.normalized_entry_witness_checks_emission_and_raw_containment` | C5 and early fixed-entry filter |
| Normalization preserves metadata and is idempotent | `FlowSummaryNormalization` structural laws | Complete boundary pair |
| Layer join cannot turn DEMAND into NORMAL | `FlowSummaryNormalization.Integration.boundary_never_promotes_DEMAND` | Summary/record application |
| Outer write mask and inner demand are both needed | `FlowSummaryNormalization.Integration.nested_write_uses_effect_geometry_and_keeps_proper_prefix_DEMAND` | Write-preserve operation split |
| C5 exact slice retains E | `FlowSummaryNormalization.Integration.same_prefix_exact_piece_keeps_E_before_and_after_normalization` | Scalar restriction and selected-piece packing |
| Selected canonical piece remains within uniform output | `FlowSummaryNormalization.Integration.canonical_C5_piece_is_covered_by_same_prefix_uniform_result` | MUST result selection |
| Abstract MUST native views cover the transposed relation | `FlowSummaryNormalization.NativeMustView` | Transient STAR-to-ANY/DEMAND view; pure FLOW selector |
| Whole-position cleaner is allowed; partial all-mark reaches are not | `FlowSummaryNormalization` admission/effect laws | Rule and primitive guards |
| Fixed right survives prepend | `DemandWorkPruning.prepend_preserves_fixed_right` | P1 mark/geometry composition |
| Pruning preserves all accepted finite-walk outputs | `DemandWorkPruning.c5_fixed_right_pruning_keeps_outputs` | P1 queues and early filtering |
| Early pure filtering preserves row order | `DemandImplementationContracts.early_filter_preserves_rows` | Packed rows / local candidates |
| Memo preserves answers and scratch | `DemandWorkPruning.memo_execution_preserves_results_and_scratch` | Visible-view eligible |
| Byte encoding refines logical memo | `DemandImplementationContracts.byte_step_refines_logical_step` | 0/1/2 array |
| IDs preserve immutable payload | `DemandImplementationContracts.owner_id_injective`, `owner_payload_unchanged` | Freeze-time factory |

The scalar admission model covers FULL marks, empty E, ordinary nonstatic
bases and counted accessors. Its bounded version proves the exact image in
that scope. Static, E and GROUP adapters must refine the same contracts;
do not infer their proof from a scalar example. The new transfer model
checks nested-write, C5-mask, layer and cleaner cells, plus the outgoing mode
grammar. It does not claim a complete JVM/alias implementation proof or a
whole-analyzer termination theorem.

The inherited historical models retain the rejected EXACT replay and former
STAR admission as regression evidence. Their old idempotence theorem is not
the selected requested-STAR image theorem. Keep the selected namespace and
mode wrapper explicit in tests and documentation.

Run from `spec/lean`:

```sh
lake env lean proposals/initial-emission/RestrictedInitialPolicy.lean
lake env lean proposals/initial-emission/FlowSummaryNormalization.lean
lake env lean proposals/initial-emission/AbstractTailContracts.lean
lake env lean proposals/demand-work/DemandWorkPruning.lean
lake env lean proposals/demand-work/ImplementationContracts.lean
```

All models are constructive. Audit every theorem for `sorryAx`, unproved
axioms and classical choice. Complete commands, output, theorem names and
source hashes are embedded in
[the implementation evidence](../reports/data/bidirectional-summary-demand-workload-implementation-20261029.json).
The five files contain 174 checked theorem declarations and 11 true
executable checks. Their axiom audits use only `propext` and `Quot.sound`.
The ordinary closed examples reach modeled **run-3**. No new project
measurement or full JVM domain execution is claimed by those models.

## 13. Implementation sequence and experiment plan

Implement the new semantics as one reviewable unit with its tests: C2 mode
policy, point tails/E, whole RemoveAll, canonical summaries/C5, matching and
native MUST views. Do not expose the new EXACT point shape while still
storing/replaying an unsafe EXACT/FLOW summary in an intermediate runnable
commit. Add no unselected feature flag to hide incomplete semantics.

Then use separate commits:

```text
1. Selected semantic rewrite + formal contracts + meaningful tests.
2. Capture the semantic reference results and operation counts.
3. Internal C5 filtered capability + fixed-right pruning + differential tests.
4. Immutable owner-family IDs + per-view byte memo + state tests.
5. Required project campaign and reports.
```

Before the campaign, complete the focused core/JIR tests and the existing
semantic suites. Use `runProjectAnalyzer` directly for OWASP, conductor,
thingsboard and Stirling-PDF. Keep the selected FULL mode, statics/aliases,
16g comparison campaign and `1,1,2,3,...` schedule. Use the current project
timeout settings. Reuse the saved `f945f92c5ae554ff4f5fc7696ee5a269210478bb`
baseline; do not rerun it or add an unrequested configuration.

Report finding locations versus baseline, candidate/report states, run-1
engine time, transition time, each iteration time, OOM/timeout, memory and
latest reached/complete/accepted iteration. The run-1 engine target remains
60 seconds. Profile the selected workload and inspect any OOM snapshot.
Clean prior task-owned snapshots before the actual campaign; do not delete
unrelated user files.

Record these work counters:

```text
C2: offered/accepted initials by demand/actual/result tail and run
mode: rejected stale late FLOW STAR entries; invalid outgoing FLOW shapes
summary: raw EXACT candidates; canonical rows; E retained; deduplicated rows
C5: candidates, fixed rejects, owner tests, decoded rows, enqueue/pop/duplicates,
    predecessor expansions, compositions, offers and retained pieces
memo: first evaluations, true/false hits, family count F, active views/bytes,
      graph vertices and edges visited
```

Compare P1/P2 with the captured post-semantic reference. Use identical finite
fixtures, matched completed queries or completed phases for operation ratios.
Different timeout prefixes are not a matched speedup. Aim for at least a
factor-of-two C5 workload reduction; do not add overlapping rejection/memo
percentages or promise the same factor in wall time.

Implementation is complete only after the selected behavior, proofs in their
stated scope, required tests, source/sink comparison and selected project
campaign pass. If an adapter needs a new behavior rather than a code change,
show its exact code/facts and obtain the behavior decision first. Do not
close a proof by introducing grounding support or changing field semantics
outside the explicit scope above.

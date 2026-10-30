# Implementation: outgoing-demand stop, static labels, and cached CFG delivery

Date: 30 October 2026. Status: implementation proposal only.
Source reviewed: `9d997343a83469e67540083fb12bc0a839d54779`.
The reviewed analyzer core is unchanged from measured runtime
`bb74cef6cf483db167c161020a8a4cca576ca005`.

This proposal implements exactly these selections from the
[next-iteration design](bidirectional-demand-refinement-next-iteration-20261029.md):

1. Stop when outgoing refinement demand is empty.
2. Select relevant static-demand labels before owner checks.
3. Cache CFG delivery by instruction and base.

It follows [the implementation guide](../../spec/impl-proposal-guide.md) and
[the proof guide](../../spec/proof-guide.md). Code is Kotlin pseudocode unless
stated otherwise. New helper names describe proposed APIs. No production code
or new project measurement is included.

## 1. Selected scope and evidence

| Part | Current behavior | Proposed behavior | Contract |
|---|---|---|---|
| Restricted forward stop | Observed DEMAND work can force continuation | Final selected outgoing demand decides the fixed empty-demand stop | Selected major termination change |
| Frozen static lookup | Inspect unrelated labels, decode them, and sometimes ask their owners | Select necessary original ordinals before those operations | Same C2 initials and C5 results |
| Point-store key | Changed results are admitted at immediate successors | Completed results are admitted once under the producing statement S | Explicit storage and work-management change |
| Neutral CFG delivery | Queue and process each untouched hop | Cache and deliver to first relevant instructions | Same effects and observations within an executed run |
| Relevant input | No universal input gate | Still no destination input gate | Repeated relevant evaluation is permitted |
| Identity output at a relevant node | Can bypass durable storage | Uses the same post-S output gate | Required when the unchanged repeat set is removed |

The stop can change the last iteration and the accepted report. It does not
confirm an unresolved candidate. The other two changes must preserve method
relations, selected demand, protection, and source/sink identities after
quiescence. Packet counts, callback counts and instruction visits can change.

Keep AP field transfer, field limits, mark modes, mark exclusions, cleaners,
source-output reset, complete ND premises after run-1, aliases, current C2/C5
emission, native-record reuse, static supply, and backward ZERO behavior.
Run-1 still cannot produce an ND edge. Do not add grounding support, query
authorization, a completed-input cache, new mark atoms, or an IR rewrite.

The separate frozen owner-visibility/SCC index is **not selected**. Keep the
current lazy graph scratch and per-view owner memo. Do not implement protection
constructor changes, replay/publication batching, new alias pruning, or repairs
for the three known Stirling baseline losses in this iteration.

### Latest measured iterations

Use the [clean campaign report](../reports/bidirectional-demand-refinement-workload-20261029.md)
and the [Stirling diagnostic report](../reports/bidirectional-stirling-small-demand-workload-20261029.md).
Do not merge their different frontier counts.

| Project, clean runtime | Latest reached | Latest complete | Accepted forward | Result |
|---|---|---|---|---|
| OWASP | run-12 | run-11 | run-11 | TIMEOUT |
| conductor | run-6 | run-5 | run-5 | TIMEOUT |
| thingsboard | run-2 | run-1 | run-1 | TIMEOUT |
| Stirling-PDF | run-6 | run-5 | run-5 | TIMEOUT |

OWASP first has empty selected outgoing forward demand at run-5. The expected
new terminal labels are run-5/run-5/run-5; this is not a new measurement.
Thingsboard run-2 performs 603,417,178 owner evaluations and 412,725,931 C5 fixed
reject calls. These calls are not distinct semantic rows or all wrong marks.
The Stirling diagnostic run-5 has 1,581,415,551 process items in one method,
including 1,575,082,922 unchanged items from 147 initials. Its bounded probe
proves 7,751,326 exact revisits. It does not estimate the global duplicate rate.
Cached delivery also removes neutral visits for new facts.

## 2. Files, ownership and equality

Let B be `core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi`.
Let J be `core/opentaint-dataflow-core/opentaint-jvm-dataflow/src/main/kotlin/org/opentaint/dataflow/jvm/bidi`.

| File or group | Implementation change |
|---|---|
| B/driver/IterationDriver.kt | Replace the fixed observed-counter stop |
| B/driver/HandOff.kt | Keep construction; assert/test count-key support binding |
| New B/store/StaticSelectorIndex.kt | Immutable selector descriptors and original-ordinal indexes |
| B/store/StaticGuidance.kt | Freeze selector indexes; select entries and labels before owners |
| B/store/C5StaticDemandView.kt | Internal selected-query overloads and conservative fallback |
| B/store/StaticEntryLookup.kt, StaticPairLookup.kt | Pass necessary query descriptors; retain final predicates |
| B/interp/FormsCache.kt | Add MethodForms/DirectedForms base-relevance query |
| J/interp/JIRMethodForms.kt | Cheap normalized base footprints, including reverse alias inputs |
| New B/engine/CfgDeliveryCache.kt | Actor-owned lazy BFS result cache |
| B/engine/MethodContextCache.kt | Expose oriented graph/relevance and cache lifecycle |
| B/engine/RunMethodAnalyzer.kt | Producer-keyed output admission, cached delivery, input/boundary separation |
| B/engine/RunMethodCallServices.kt | Pass producer S to static result shortcuts; retain internal stages |
| B/engine/DeltaWorklist.kt, NeutralBatchWorklist.kt | Remove unchanged lanes/repeat state; retain ordinary priority and batches |
| B/store/MethodEdges.kt | Document post-S result meaning; retain its admission algebra |

There is one existing method result store, not separate before/after stores.
InitialFactStore still owns admitted initial identities. Existing conjunction,
subscription and static stores still own their standing inputs. The route cache
owns only base identifiers and instruction indices.

Do not add relevance/index metadata to semantic data-class keys. Keep equality
and hashing of Facts, PremiseKey, MethodKey, rule/action IDs, subscription keys
and report keys. Protection remains a separate annotation where current equality
omits it. Reuse the current store's annotation-aware delta law.

## 3. Stop on the completed outgoing snapshot

### 3.1 Use HandOff.of's selected support

The production construction already couples normalized insertion and counting:

```kotlin
val pattern = DemandPattern(entry, from)
if (demand.add(method, pattern)) counts.merge(method, 1, Int::plus)
```

`Builder.add` owns/normalizes the complete pair, removes duplicates and excludes
the implicit ZERO demand. The count map gets a method key on exactly that
successful branch. `build` does not remove accepted rows. Therefore:

```text
handOff.demandEdges.keys is empty
    iff its successfully built explicit selected snapshot is empty.
```

This binds to `HandOff.of`, not every manually constructed HandOff used in
tests. Test the support invariant; do not redesign its public constructor.
Use map emptiness, not a diagnostic sum or a scan of DEMAND-layer summaries.
Selected NORMAL ND support also contributes patterns. Numeric count sums are
not needed for this decision.

### 3.2 Barrier patch

```kotlin
// Complete run only; existing owners have joined and frozen.
if (forward) report.add(config, result)
shared.records.persist(config.direction,
    result.analyzers.asSequence().map { it.key to it.summaries })
val handOff = HandOff.of(config, result, report, shared)
val frontier = frontierOf(config, result, handOff, report)
frontierLog += frontier
frontier.log()

if (forward && !report.hasDemandVulnerability())
    return Next.End(COMPLETE, STOP_RULE)

if (forward && !config.run1) {
    check(!handOff.demand.hasStaticCompletion)
    check(!handOff.demand.hasSharedStaticCarry)
    logStopInputs(config.index, handOff.demandEdges, result.demandLayerEdges)
    if (handOff.demandEdges.isEmpty())
        return Next.End(COMPLETE, NO_DEMAND_EDGE)
}

if (forward && !policy.continueAfter(config, result, frontiers))
    return Next.End(COMPLETE, POLICY)
return Next.Run(nextConfig(config, handOff))
```

Remove `result.demandLayerEdges == 0L` as a stop. Keep that counter as diagnostic
data. Do not leave both stop conditions active.

Keep run-1 excluded: its handoff can contain virtual static completion and
shared static carry. Backward runs continue normally. Do not stop incomplete
runs, skip barrier persistence/seed creation, or convert a late guard failure
to COMPLETE. Current OOM/cancellation/exception paths keep precedence.

```kotlin
if (result.status != COMPLETE) return Next.End(result.status)
val next = try {
    guardBarrier(shared) { barrier(config, result, report) }
} catch (error: Cancellation.Cancelled) {
    Next.End(OOM)
}
if (!shared.cancellation.isActive()) return Next.End(OOM)
return next
```

Keep unresolved report entries DEMAND. Nonempty seeds do not override the
selected empty-demand stop. This contract does not assert that an omitted
backward run could do no work. Saved OWASP run-6 does produce new demands.

### 3.3 Principal controls

| Complete barrier, report still has DEMAND | Expected decision |
|---|---|
| run-5; selected output empty; observed counter positive | NO_DEMAND_EDGE; no policy or run-6 call |
| run-5; selected output nonempty; observed counter zero | Continue, subject to existing policy/budget |
| run-1; explicit output empty; virtual static family present | Keep run-1 transition |
| Backward run; output empty | Keep transition to forward |
| Failed/partial engine or cancelled barrier | Existing abnormal end |

For the recorded OWASP outgoing sequence `111374, 112217, 85, 200801, 0`, run
only engines 1 through 5. Preserve the complete run-5 report and frontier.
The old first-five engine intervals sum to 242.041 seconds; later intervals
sum to 710.440 seconds. These are saved sums, not new command timings.
Stirling run-5 has 1,304 outgoing patterns, so this stop does not apply there.

## 4. Select frozen static labels before owners

### 4.1 Preserve existing payload and scope

```text
spatial geometry candidates
    -> necessary original label ordinals
    -> current final keep predicate
    -> current owner Boolean
    -> reconstruct complete edge
    -> unchanged AP matching/composition/restriction
```

Current C5 already rejects with its P1 predicate before owners. Its selector
saves label decoding and exact predicate calls. Current C2 FLOW and entry paths
also save owner questions. Do not count all C5 rejects as saved owner calls.

Keep the complete `(input, output)` relation and each ordinal's own owner set.
B visibility stays common-method based. Local W/R attachments stay scoped to
their full MethodKey. Do not change graph reachability, the lazy scratch or the
per-view memo. Run-3 and later still use local-only demand lookup.

### 4.2 Selector domain and immutable postings

Read each stored MarkAtomKey once during freeze and each query key once before
its label loop. A descriptor uses existing immutable keys; it does not create
an atom or enumerate a group.

```kotlin
sealed interface Selector {
    data object Zero : Selector               // genuine nullable endpoint only
    data class Full(val atom: TaintMark, val exact: ExactMark) : Selector
    data class Group(val atom: TaintMark, val id: GroupId) : Selector
}

fun covers(guide: Selector, actual: Selector): Boolean = when (guide) {
    Zero -> actual == Zero
    is Full -> actual is Full && guide.exact == actual.exact
    is Group -> when (actual) {
        Zero -> false
        is Full -> guide.id == actual.exact.group
        is Group -> guide.id == actual.id
    }
}

fun composable(output: Selector, input: Selector): Boolean =
    output != Zero && input != Zero && (covers(output, input) || covers(input, output))
```

The null guard matches current `composeMarks`. Endpoint ZERO can cover ZERO;
mapped rows cannot compose through null ZERO. A nonnull atom with ID 0 must
not be converted into a null endpoint. Classify real ZERO from endpoint/base
context. Use the old `All` loop for unclassified queries or blocks; do not
reject or normalize a previously accepted row to make indexing easier.

```kotlin
class OutputOrdinals(
    val full: Map<TaintMark, IntArray>, // exact FULL output atom -> original ordinals
    val group: Map<GroupId, IntArray>,
    val fullInGroup: Map<GroupId, IntArray>,
    val zero: IntArray,                // local real-ZERO endpoint cases
)

class BridgeRows(
    val geometry: GuidanceGeometry,
    val labels: LongArray,             // existing complete packed pairs
    val owners: List<Owners>,          // one original family per ordinal
    val flowOrdinal: Int,              // -1 or exactly one
    val outputs: OutputOrdinals,
)
```

Build sorted ordinal postings in original row order. FULL adds one exact posting
and one group-member posting. GROUP adds one group-output posting. ZERO adds
only a local ZERO posting. FLOW adds no mark posting. Merge selected streams
and the optional FLOW ordinal without scanning all labels or returning an
ordinal twice. Inline empty/singleton cases instead of allocating empty maps
for each sparse geometry.

| Query | Output covers query | Output composes with query |
|---|---|---|
| FULL T in G | exact T + GROUP G | exact T + GROUP G |
| GROUP G | GROUP G | GROUP G + all stored FULL outputs in G |
| Genuine ZERO | ZERO endpoints | No mapped ordinal |

Different FULL marks in one group remain different. The group-member posting
contains only rows already in this snapshot; it is not a global mark census.

Every frozen row already enters via `StaticGuidanceEdge.of -> guidancePattern`.
That boundary canonicalizes FLOW mx and abstract demand E today. Unique packed
labels therefore give at most one `0L` FLOW label per complete geometry. Reuse
this invariant; do not introduce new normalization. Actual input mx still goes
through the unchanged final `markSub` check.

### 4.3 C2 entries and FLOW adjacency

Freeze an entry geometry directory beside the existing full entry payloads:

```kotlin
class EntryGeometryRows(
    val geometry: PatternGeometry, // full base/path/tail/E; no mark normalization
    val entries: IntArray,         // original full EntryRows IDs
    val flowOrdinal: Int,
    val outputs: OutputOrdinals,
)
```

The spatial trie returns geometry IDs. Restore the full concrete mark before
demand-E normalization. Preserve concrete exclusions and exact owner payloads.
Use equivalent ordinal selection within the existing local W/R attachments.

```kotlin
fun entries(actual: Pattern): Sequence<Pattern> = sequence {
    val select = entrySelection(actual) // FULL/GROUP key once; unknown -> All
    for (block in spatialEntryCandidates(actual)) {
        for (i in block.selectedOrdinals(select)) {
            val entry = originalEntry(block.entries[i])
            if (!markSub(entry.pattern.fact.mark, actual.fact.mark, ap.marks)) continue
            if (entry.isBridgeProjection && !eligible(entry.owners)) continue
            yield(entry.pattern)
        }
    }
}
```

A marked actual T selects FLOW plus covering concrete/group entries. An abstract
actual selects FLOW only. Real ZERO keeps its private exact and implicit ZERO
paths. Keep `InitialDemandResults.offer -> policy.emit` as the final authority.
Ordinary method-local demand rows are unchanged.
Local W/R rows already passed the exact full MethodKey attachment lookup.
Do not add a transitive owner check to those rows. The owner check shown above
applies only to a bridge projection.

Use `flowOrdinal` directly in `flowTargets`, FLOW-only `incoming`, and current
FLOW-only `outgoing`. Use output coverage in `hasMarkedOutput`, which requires
a mapped row and therefore does not include FLOW. Preserve `markedOutputs`'s
directional coverage law.

Select necessary entries in `visitPossibleTargets` before `requireFamily`, but
retain every compatible FLOW repair family. Otherwise coverage can become
vacuously complete and stop the search too soon. Keep conservative inherited
search hints and the exact final coverage/emitter checks.

### 4.4 C5 query capabilities

Extend only the internal C5 capability. Opaque/reference views keep their old
enumeration and exact predicate fallback.

```kotlin
sealed interface LabelSelection {
    data object All : LabelSelection
    data object FlowOnly : LabelSelection
    data class OutputCovers(val actual: Selector) : LabelSelection
    data class OutputComposesWith(val input: Selector) : LabelSelection
}
data class StaticRowQuery(
    val labels: LabelSelection,
    val mappedGeometryAllowed: (Pattern) -> Boolean = { true },
)

interface C5StaticDemandView : StaticDemandView {
    fun selectedTargets(actual, prefixesOnly, query, keep) = c5Targets(actual, prefixesOnly, keep)
    fun selectedIncoming(input, query, keep) = c5Incoming(input, false, keep)
    fun selectedHasComposedEndpoints(initial, outputs, query, keep) =
        c5HasComposedEndpoints(initial, outputs, keep)
}
```

The frozen view overrides these operations. Its row visitor selects ordinals,
applies the existing keep predicate, asks the same owner, then creates the edge.
`All` remains available where no necessary selector has been proved.

| C5 operation | Mapped-row selector | FLOW ordinal |
|---|---|---|
| Target seed, legal FULL original M | Output covers M | Retain |
| Target seed, abstract FLOW original | None | Retain |
| Predecessor of `Mapped(U,T)` | Left output composes with U | Retain |
| Predecessor of FLOW, FULL original M | Left output covers M | Retain |
| Predecessor of FLOW, abstract original | None | Retain |
| Unknown selector case | All | Retain |

Use the same query for target existence preflight and target enumeration.
The isolated source/writer existence half stays conservative `All`.

```kotlin
val targetLabels = outputCoveringOriginal(member)
val targetQuery = StaticRowQuery(targetLabels) { right -> mappedRightMayEmit(member, right) }
val keepTarget = StaticCandidateFilter { _, to, marks -> mayKeep(member, to, marks) }
if (!view.selectedHasComposedEndpoints(member, outputs, targetQuery, keepTarget)) return
for (edge in view.selectedTargets(member.toPattern(), true, targetQuery, keepTarget)) admit(edge)

// Existing queue and state.from == STATIC guard remain.
val incomingLabels = when (val marks = state.marks) {
    Flow -> if (mappedRightMayEmit(member, state.to)) targetLabels else FlowOnly
    is Mapped -> outputComposable(marks.input)
}
val keepIncoming = StaticCandidateFilter { _, _, left ->
    composeMarks(left, state.marks)?.let { mayKeep(member, state.to, it) } == true
}
for (left in view.selectedIncoming(state.from, StaticRowQuery(incomingLabels), keepIncoming))
    compose(left, state)?.let(::admit)
```

```kotlin
fun outputComposable(input: TaintMark?): LabelSelection {
    if (input == null) return FlowOnly // Real ZERO cannot join a mapped row.
    val key = selectorOfNonNullAtom(input) ?: return All
    return OutputComposesWith(key)
}
// An unclassified nonnull atom, including ControlZero, uses All.
// It is not the nullable ZERO endpoint.
```

Keep complete anchor equality, overlap, `composeMarks`, endpoint reconstruction,
`mayKeep`, deduplication, `canStoreInitial`, restriction and coverage. An index
does not replace any of these predicates.

### 4.5 One conservative geometry test

```kotlin
fun mappedRightMayEmit(member: InitialAp, geometry: Pattern): Boolean {
    val key = selectorOfInitial(member)
    if (key !is FullInitial || geometry.fact.base == ZERO) return true
    val sameMark = geometry.copy(fact = geometry.fact.copy(mark = member.mark))
    return policy.canStoreInitial(normalizeDemandFieldExclusion(sameMark), member.toPattern())
}
```

For a legal FULL member M and nonzero mapped target, successful old `mayKeep`
requires the same geometry tests and an output selector covering M. Replacing
that selector with M makes the mark test reflexive. Concrete kind, base, paths,
tails, E, budget and raw-emitter image stay the same. Thus old success implies
this precheck succeeds. A false precheck can discard all mapped ordinals at
that geometry. It cannot discard FLOW or an unproved ZERO/abstract case.

Run it once per geometry per pass, not once per label. For a FLOW right state,
use the fixed final `state.to`, not each predecessor's geometry. It does not
intern a hypothetical InitialAp, emit a fact, or change a field tail.

### 4.6 Examples which the selectors must preserve

```text
Mark-changing source path:
    ZERO -> C.a/U; C.a/U -> C.b/T; C.b/T -> ret/T
    The source U is necessary although it does not cover requested T.

FLOW repair:
    C.a/U -> C.b/T; C.b/FLOW -> ret/FLOW; original is ret/T
    Keep the FLOW reader so the bridge can produce C.a/U -> ret/T.
```

For one geometry with FLOW and 100 `Ti -> Ti` rows, a FLOW-only request visits
one ordinal instead of 101. A FULL T7 target visits FLOW and T7, plus a covering
GROUP row if present. For a K-by-K `Ui -> Tj` matrix, a Tj selector retains all
K complete input/output pairs, rather than inspecting K squared labels. These
are finite work examples, not measured project speedups.

## 5. Cache CFG delivery; store completed results under S

### 5.1 Base relevance in MethodForms

```kotlin
interface MethodForms {
    fun isBaseRelevant(direction: Direction, s: CommonInst,
                       base: AccessPathBase, view: RuleView): Boolean = true
}
class DirectedForms(/* existing state */) {
    fun isBaseRelevant(key, s, base) =
        forms(key).isBaseRelevant(direction, s, base, ruleView)
}
```

A false answer certifies identity transfer and no observation or registration
for every fact on that base. It cannot depend on the incoming mark, path,
premise, layer, E or protection. A conservative true answer is valid.

JIRMethodForms supplies cheap immutable base footprints:

```text
noncall: normalized operand/result bases + bound rule positions
call:    receiver + arguments + result + STATIC
reverse: also include existing alias target bases which become reverse inputs
boundary: relevant for every base
ZERO fact base: relevant at every instruction in this first implementation
```

This uses current normalized locations and existing aliases. It does not add a
new alias policy. For current JVM noncall rules, static-field-read sources use
ZERO and the read lhs. Call rules use their rewritten operand/result/static
positions. For an uncertain provider/alias case return true; do not guess a
negative answer. The default keeps other providers and fixtures functional.

Do not construct every bound rule or enumerate marks to answer relevance.
Derive a base footprint from normalized IR and existing alias metadata. Keep it
separate from semantic form/key equality. Verify it against compiled forms in
tests. `touched` alone is not sufficient for arbitrary providers: untouched
statements can still evaluate conjunctions, sources and static hooks.

### 5.2 Sparse metadata cache and total BFS

```kotlin
class CfgDeliveryCache(private val context: RunMethodContext) {
    // Context fixes method, run, direction, view and oriented CFG.
    private val rows = mutableMapOf<InstIndex, MutableMap<Base, IntArray>>()

    fun targets(start: InstIndex, base: Base): IntArray {
        rows[start]?.get(base)?.let { return it } // Empty array is a hit too.
        val todo = IntQueue(start)
        val visited = BitSet()
        val result = IntArrayList()
        while (!todo.isEmpty) {
            cancellation.checkpoint()
            val n = todo.removeFirst()
            if (visited[n]) continue
            visited.set(n)
            if (context.isBoundary(n) || forms.isBaseRelevant(key, instruction(n), base))
                result.add(n)
            else
                context.forEachSuccessor(instruction(n)) { todo.add(index(it)) }
        }
        val complete = result.toIntArray()
        rows.getOrPut(start) { HashMap() }[base] = complete
        return complete
    }
}
```

Stop at the first relevant instruction on each path. Use the current oriented
CFG, including its exceptional edges. Visited nodes stop neutral cycles. An
empty frontier is valid for a neutral dead end or closed component. Publish
only after the whole search succeeds; cancellation leaves no empty placeholder.
Cache only the queried start. A visited branch node need not have the start's
complete frontier.

The cache holds indices and base IDs only. Do not retain full forms, facts,
premises, rules or historical input trees. Release it with its owner context.
Proof paths exist in the Lean model; runtime caches need not retain those paths.

ZERO is always relevant, so enqueue it directly at the current start without
building redundant singleton cache rows. Keep the exact existing `zeroToZero`
priority predicate; a ZERO premise carrying a nonzero fact base still benefits
from cached routing.

### 5.3 Separate input queueing from result admission

```kotlin
private fun enqueueInput(node, premise, facts) {
    worklist.add(EdgeDelta(premise, node, facts))
    requestWork()
    // No MethodEdgeStore admission and no result-admission counter here.
}

private fun deliverAt(start, premise, facts) {
    if (facts.base == ZERO) { enqueueInput(start, premise, facts); return }
    for (target in delivery.targets(index(start), facts.base))
        enqueueInput(instruction(target), premise, facts)
}

private fun completeOrdinaryOutput(S, premise, boundedResult) {
    val fresh = edges.add(S, premise, boundedResult) ?: return
    recordResultAdmission(fresh) // Existing diagnostic category; once per producer delta.
    context.forEachSuccessor(S) { deliverAt(it, premise, fresh) }
}
```

The store for S contains the result **after processing S**. Admit once before
fan-out. Deliver the same returned T2/T4 delta to all original successors and
their cached frontiers. There is no input admission at a relevant destination.
Repeated relevant evaluation is permitted.

Do not reuse current `push` unchanged: it increments admission counters on each
queued item. Split post-result accounting from input queueing. Do not change
stop behavior using the new internal counter values; section 3 uses the final
selected snapshot. Keep protection-only and exclusion-annotation growth fresh.

Every completed result of a processed relevant instruction, including its
forwarded identity, uses this gate. Reuse the existing cut/cover and operation
hooks once. Do not reapply them just to route an untouched result.

```java
while (x != null) { unrelated = 1; }
// The branch can be relevant by operand but have an EMPTY transfer form.
// First identity output enters the branch's result row.
// A repeated equal output has no fresh delta and cannot circulate forever.
```

### 5.4 Entry, resume and boundary seams

| Current write/path | Proposed handling |
|---|---|
| `emitCovered` at an ordinary node | Complete result -> admit at producing S -> cached fan-out |
| `emitUnchanged` | Same post-S gate, without repeating transfer/cut |
| `startAt` pre-write at entry | Remove that pre-write; keep InitialFactStore and start rules; enqueue input |
| StatementInput resume | Execute that continuation; do not pre-store it as a result |
| ReadOutput/CallStageInput/CleanerInput | Finish exact internal continuation; do not restart the whole statement |
| End-boundary input | Preserve ordinary transfer and existing rules/sinks; admit only completed boundary output |
| Static shortcut pre-write at NormalExit | Remove ingress write; store at its producer and enqueue exit input |

An incoming initial must not prepopulate its producer result row. Otherwise an
identity first result would look like a duplicate and never propagate.

Split ordinary transfer completion from terminal completion:

```text
ordinary S:
  transfer -> current cut/cover/hooks -> post-S admission -> cached fan-out

normal end S:
  existing ordinary statement/return transfer -> current cut/cover/hooks
  -> end rules -> sink observations -> existing global/entry-mark adjustment
  -> existing boundedSummaryResult -> post-S admission of completed result
  -> existing retainSummary normalization/intersection/publication

existing run-1 static normal-exit shortcut:
  skip the return transfer, as today -> same terminal rule/summary pipeline

exceptional boundary:
  existing ordinary transfer and current rules/observations
  -> completed boundary handling
  -> no newly invented normal-return summary
```

The JVM synthetic exit has no return transfer. A generic end instruction can
have one, such as `p -> ret`. Keep that transfer before end rules. The existing
run-1 static shortcut is the only transfer bypass shown here.

Current `emitCovered` calls `exitRulesAt` then still refers to its pre-boundary
input. Do not store that input as the completed exit result. Keep the summary
store separate and its normalization at the same semantic boundary.

All rule checks, source-hit capture, static operation hooks and late-support
registration run before completed output admission. Equal outputs from different
rule occurrences do not erase their distinct observation IDs.

### 5.5 Static direct-to-exit delivery

Thread the producing statement through `routeStaticResultToExit` and all six
call-service call sites. Use the actual call/operation statement from the saved
continuation, not the current cached destination.

```kotlin
fun routeStaticResultToExit(S, premise, value) {
    boundedSummaryResult(premise, value) { pr, bounded ->
        pointResumes.computedGroups(pr, bounded) // Existing call-result supply.
        val fresh = edges.add(S, pr, bounded) ?: return@boundedSummaryResult
        recordResultAdmission(fresh)
        enqueueInput(context.normalExit, pr, fresh) // no ingress pre-write
    }
}
```

An executed local micro-write still calls `localWrite` immediately before result
admission. It supplies the pool even if exit rules later kill the summary.
A call-created result still supplies computed groups without registering a new
write point. Keep killed-write guidance. A static write inside exit rules
finishes that boundary pipeline; it does not schedule the exit again or admit
an intermediate write as the completed exit output.

### 5.6 Packed output and ordinary queue

Admit a diagonal packet once at S. Decode an unsupported scalar fallback once
at S, outside the successor loop. Then deliver each returned fresh result.

```kotlin
val freshPackets = edges.addDiagonal(S, offered)
for (delta in requireNotNull(freshPackets)) {
    recordResultAdmission(delta)
    context.forEachSuccessor(S) { next ->
        for (target in delivery.targets(index(next), delta.base)) {
            // Each destination owns its mutable remaining-mark wrapper.
            enqueuePackedInput(instruction(target), NeutralRelationBatch.fromDiagonal(ap, delta))
        }
    }
}

fun enqueuePackedInput(node, ownedBatch) {
    worklist.addBatch(node, ownedBatch)
    requestWork()
}
```

The pseudocode shows the supported path. Preserve the existing null-means-
unsupported versus empty-means-duplicate distinction and scalar fallback.
Do not share one mutable batch wrapper between destinations. Retain the queued
remainder before a quantum yield. This does not select a new batching policy.

Remove unchanged lanes and their repeat state. Keep ordinary ZERO priority,
the existing FULL run-1 FLOW-before-TAINT priority, and pending changed batches.
An owner reservation covers cache construction and complete fresh-result fanout.
Do not yield after admission but before securing every successor: retrying the
already-admitted result could lose unsent work. Check cancellation during BFS,
posting merge and fanout; abnormal cancellation cannot publish partial caches
or claim a completed iteration.

### 5.7 Principal routing controls

```text
Diamond:
  S1 produces F; S2 produces the same F
  each producer admits once and delivers to relevant join J
  J may evaluate F twice; J admits its equal result once

Relevant identity loop:
  R produces F -> cached route returns to R
  repeated R output is rejected at R's result store

Closed neutral cycle:
  BFS completes with {} -> cache the empty result -> no invented exit

Initial identity:
  initial admitted in InitialFactStore -> entry input queued
  entry's first completed output is new in its post-state store
```

```java
void example(Object x) {
    use(x);       // S: completed output is I -> x/T, stored under S.
    int n = 1;    // Neutral for base x.
    n = n + 1;    // Neutral for base x.
    sink(x);      // R: relevant for base x.
}
// Before: route I -> x/T through both neutral statements, then process R.
// After: the first query finds R; later packets with base x use that cache row.
// R still executes its current rules. Its result is stored under R.
```

For one queried start/base, a cache miss visits at most V vertices and E edges.
A hit costs the number of relevant destinations delivered. For P packets on a
neutral chain of length L, routing work changes from P times L to one search
plus P deliveries. This does not remove processing at relevant instructions.
The cache uses space proportional to the sum of cached frontier sizes. Its
worst case is proportional to the number of bases times V squared. Sparse
construction does not remove this risk. Measure live cache rows, widths and
bytes before claiming a memory improvement.

## 6. Required proofs and checked formal artifacts

The constructive Lean package is
[selected-work-20261030](../../spec/lean/proposals/selected-work-20261030/README.md).
Run `python3 spec/lean/proposals/selected-work-20261030/check.py`.
The receipt records toolchain, source hashes, declarations and axiom dependencies.
It builds only these models and the existing demand-frontier dependency.

### 6.1 Stop correctness

The existing normalized builder model proves count/row coupling. The new
`SelectedStop` model derives method-key support emptiness, then proves the
complete-barrier decision. It includes report-empty precedence, observed-counter
independence, run-1 exclusion, backward continuation, report/persistence/frontier
payload retention, and guard failure precedence. Production binding is the
same `HandOff.of -> Builder.add/counts.merge` branch and barrier order in §3.
The public synthetic constructor is outside that coupling theorem.

### 6.2 Selector equivalence

`SelectedStaticLabels` proves exact directional coverage/composition buckets,
including the null-ZERO join guard. Every selected row is the original complete
row with its ordinal, geometry and owner. For any final predicate K and pure
owner Boolean O, if `K(row)` implies necessary selection, filtering by selection
before O/K yields the same ordered final row list. This provides an executable
same-ordinal witness in both directions.

The C2 first mark gate is necessary by the first branch of `policy.emit`.
The legal-FULL mapped-right lemma factors existing geometry checks from selector
coverage. Replacing an admitted output selector by the original full mark keeps
all concrete-kind geometry cells and makes the mark test reflexive. The proof
is scoped to that case; other cases use fallback. The old final predicate stays.

For C5, target and productive-predecessor lemmas prove each old productive
composition retains its same ordinal. FLOW repair has an explicit control.
Induction on each finite composition path preserves path results; conversely
every new result still has an old path and old final AP witness. Coverage sees
the same possible emitter images, so early completion cannot discard a family.

Owner answers remain fixed graph predicates. Current scratch records reachable
vertices; a positive answer has an owner witness, and a completed negative
exhausts reachable vertices. Skipped impossible queries change scratch progress,
not a later completed Boolean. The implementation keeps the owner algorithm.
The formal owner-history lemma is conditional on truthful completed answers;
query-order source tests establish this adapter condition.

### 6.3 Routing and result admission

`CachedCfgDelivery` implements total FIFO BFS over finite graphs with a visited
set. Returned targets carry executable neutral-prefix paths. Its completeness
proof covers cycles without a fuel cutoff or an unexplained closure oracle.
Any valid cache hit has the same target set as fresh search. Empty-frontier
safety proves that a closed neutral component cannot manufacture an exit.

The producer store model keeps full-key identity separate from an ordered
ordinary/protected annotation. Admission is idempotent, changes no other
producer, preserves protection upgrades, and sends each fresh output to every
successor's relevant frontier. Repeated relevant identity output has empty
fanout. Each fixed ordinary/protection cell has at most two fresh levels.
This is not a bound on an entire project or on all T2 header changes.

The model includes computed diamond, identity-cycle, empty-cycle and first-entry
controls. Runtime caches store only indices; constructive proof paths are not
new retained runtime state.

### 6.4 Source adapters and end-to-end proof boundary

The models do not prove an unwritten Kotlin patch or the whole AP engine.
The following adapter arguments are required before implementation can pass:

1. **Neutrality:** case-check each frontend footprint. A false result must give
   identity AP output and no rule, source, sink, static or boundary observation
   for every packet on that base. Default true is the conservative fallback.
2. **Transfer preservation:** compare completed outputs using the existing AP
   operations, T2/T4 annotation behavior and scalar/packed adapters. Post-S
   admission cannot drop a protection-only upgrade or normalize a point tail.
3. **Path simulation:** replace each reference neutral prefix with its cached
   target witness. Every cached delivery expands to such a reference prefix.
   At the next relevant node, run the same semantic handler.
4. **Standing dependencies:** a later join member/publication must activate
   existing conjunction/subscription support without needing a discarded new
   output. Retain those stores and qualified continuation identities. Test
   both registration/delivery orders and all contributing ND origins.
5. **Observation preservation:** run source-hit, sink and static hooks before
   post-result admission. Final report/source/sink identities and complete
   premises are the semantic observations; callback counts are not.
6. **Completion:** secure full fanout and queued batch remainder under the
   counted owner reservation. Complete caches publish atomically after search;
   request/static/publication barriers wait for all counted work.

Use these statements to connect the checked kernels to source cases. Do not
replace them with an opaque claim that all handlers are confluent. If a finite
counterexample fails, extend the Lean model and design first. If repair would
change an unselected field/rule/mark/static contract, show the code/facts and
ask for the intended behavior before adding that change.

## 7. Removal and migration inventory

```text
Driver:
  remove observed-demand counter as the NO_DEMAND_EDGE predicate
  keep the diagnostic counter and existing EndReason

Static lookup:
  replace full FLOW-only label scans with flowOrdinal
  replace selected C2/C5 mark scans with ordinal streams
  retain All fallback, exact predicates, owner scratch and memo

CFG worklist:
  remove Unchanged wrapper, unchanged/flowUnchanged/taintUnchanged lanes
  remove RepeatKey, seen, sequence, zeroUnchanged and latestUnchanged
  remove addUnchanged and afterProcess reset calls
  remove PendingWork.MarkedBatch.unchanged and its obsolete retention paths

Point storage:
  remove successor-keyed result admission and ingress pre-writes
  use producer S for scalar/packed completed outputs
  keep initial, join, subscription, summary and static stores
```

Do not remove pure `unchanged` concepts from the scalar/reference AP interpreter.
They still define the behavior being skipped. Keep NeutralRelationBatch and
its existing changed-cohort capability. Historical queue-order tests may remain
as test-only reference code; they must not keep a production unchanged queue alive.

Update the original/current stop clauses in `spec/ap.md`, `spec/analyzer-core.md`
and `spec/implementation-background.md` before changing runtime. Update their
point-store/queue descriptions and `spec/interpreter.md` relevance adapter
contract for §5. Keep prior reports as measurements of their pinned runtime.
Audit the current tests which read `edgesAt`: those reads describe post-S
results after migration, not input admission. Update each semantic assertion
explicitly rather than accepting new snapshots in bulk.

Update the current-mode test oracle in `fixtures/DirectCurrentIteration.kt`.
Its stop currently inspects processed facts, raw summaries and links. Make its
decision use its independently built normalized outgoing snapshot. Do not call
the new production stop helper from the oracle. Keep historical reference modes
unchanged.

## 8. Proof-first TDD and implementation plan

1. Run the checked Lean package and review its source-adapter limits. Update
   authoritative spec clauses for the selected contracts and their proofs.
2. Add failing driver tests, then implement §3 in a small isolated change.
   Keep observed-positive/empty-selected and observed-zero/nonempty-selected
   controls, selected NORMAL ND support, virtual families and abnormal barriers.
3. Add slow full-loop selector oracles in tests. Test FULL/GROUP/ZERO direction,
   complete pair/owner fidelity, actual mx, concrete E, raw preimages, FLOW repair,
   mark-changing chains, source preflight, cycles and query-order permutations.
   Implement immutable freeze/indexing, direct FLOW, C2, then C5 selected APIs.
4. Add cache/relevance tests before switching delivery. Cover branches, joins,
   cycles, relevant start, empty hit, backward graph, cancellation, actual
   compiled observer footprints and alias-expanded reverse inputs.
5. Add post-S entry/identity/fanout tests. Refactor completed-output seams,
   boundary completion and all static producer arguments. Then connect cached
   delivery and remove unchanged lanes. Test one-item quanta and late callbacks.
6. Validate field/mark exclusion reductions, normal/demand separation,
   protection-only growth and protected EXACT under an older ordinary ANY row.
   Compare packed/scalar paths and independent mutable destination wrappers.
7. Run the required core/JVM suites and classes build. Existing reference
   receipts have 2,058 core tests and 445 JVM tests; record actual new totals.
   Review the diff for every excluded semantic change and all direct store writes.
8. Repeat the authorized four-project campaign on one pinned implementation.
   Commit implementation before measurement as the task requires. Reuse the
   f945 baseline reports; do not rerun that analyzer.

Unit tests compare final relation/annotation sets and observation identities,
not old packet counts or forced iteration counts. Update DemandLink driver
expectations when selected output is empty; do not invent output demand to
retain an old run count. Keep independent backward-ZERO tests for executed runs.

## 9. Measurement and acceptance

Use `runProjectAnalyzer` through Gradle with the same audited campaign controls:
16g, FULL run-1 marks, statics enabled, aliases enabled, field limits 1,1,2,...;
OWASP 1,000 seconds and conductor/thingsboard/Stirling 1,080 seconds. Preserve
the configured outer limits. Do not add other configurations in this iteration.

| Part | Required measurements |
|---|---|
| Stop | Last accepted run; selected outgoing count; observed counter; first skipped engine |
| Labels | Original/selected ordinals; mark/other fixed rejects; owner calls; graph work; index build time and retained bytes |
| Delivery | Cache misses/hits/empty hits; BFS nodes/edges; frontier widths; relevant evaluations; post-S fresh/duplicate results; scalar/packed deliveries |
| Whole project | Iteration engine/barrier times, transition time, memory/GC, OOM/TIMEOUT and required report identities |

Freeze only primitive counter snapshots before releasing cache/result-store
state. Do not retain packet trees or rule forms for measurement. Capture CPU
under normal and late workload, and heap snapshots on memory-manager OOM as
the task requires. Check result-store and cache memory while their owners are
live; a post-freeze census cannot recover released point state.

Report latest reached, latest complete and accepted forward iteration in every
project row. OWASP should end at run-5 on the recorded empty-frontier case.
Other projects need actual results. Compare final locations against both the
required f945 baseline and the current pinned report. Keep the three known
Stirling baseline losses explicit; these optimizations do not repair them.
No new loss is acceptable from static selectors or cached delivery. Report the
intentional earlier-stop boundary separately from a lost executed-run relation.

Accept only when the formal/source gates and meaningful tests pass, selected
static query results and routed semantic observations match their references,
the new stop has the selected behavior, and measurements show the actual work
removed without a hidden memory regression. No two-times project gain is
claimed from an inclusive CPU share or a finite example.

# Implementation proposal: constant filtering and Target-guided ZERO, version 2

Date: 31 October 2026. Status: implementation proposal. No runtime change.

The specification is the final
[constant filtering and Target-guided ZERO proposal](bidirectional-constant-filter-target-zero-implementation-20261031.md).
Its SHA-256 is
`8ae901c30188e81a09030491291dbb86a749e017a6d0b4b3218664821494c21a`.
This document replaces the implementation instructions in that document.
It repeats the selected contract, so implementation does not depend on
earlier drafts or discussion.

Follow [impl-proposal-guide.md](../../spec/impl-proposal-guide.md) and
[proof-guide.md](../../spec/proof-guide.md). Use the checked, constructive
models linked in section 15. Their scope and runtime adapter tests are
separate. No classical choice, proof hole, or new axiom is permitted.

Base runtime: `e090118e5f9603f1973c0578a3e04998035f4508`. Repository head
`3d8116a1a131a96f8423ef96d2b4a5d643dc46fc` adds reports and controls.
No Gradle build, project analysis, or new performance measurement is made
for this proposal.

## 1. Selected contract and semantic scope

AP means access path. `$` is an exact position; `[any]` is an unresolved
MAY suffix; `[any-taint]` is a definite uniform MUST suffix. FLOW has an
abstract mark. T and U are full concrete marks. ZERO is control.

**The changes below affect analyzer semantics.** Keep them explicit in
the runtime PR and its tests.

| Part | Current runtime | Selected next iteration |
|---|---|---|
| Constant-base data | Can propagate, trigger callbacks, and enter records/demand | Drop before runtime effects in every direction/run |
| Exact C2 admission | `[any]` can create `$` initial | `$` demand rejects submitted `[any]`, including an ancestor MAY |
| Unanswered demand | Empty emission skips current-call admission | Keep the no-op, including when every offer fails during the iteration |
| Sink observation | A local witness becomes a report candidate | A complete witness creates a typed terminal summary |
| NORMAL terminal | No current type | `NormalTarget(id)`; forward application requires complete NORMAL support |
| DEMAND terminal | No current type | Anonymous `DemandTarget`; paired C5 and handoff guide later ZERO |
| Backward actual GEN | Records its source occurrence | Also emits DemandTarget under its original premise |
| Restricted ZERO | Virtual/direct admission and a backward C5 exception | Explicit local demand admission and ordinary paired restriction |
| Final report | Local candidate replacement and confirmation flag | IDs reached by configured-root `ZERO -> NormalTarget(id)` |
| NORMAL terminal reuse | No current record kind | Persist full owned keys; ignore backward and skip settled ZERO replay |

The final rules are:

```text
Constant data or Constant premise member -> reject the whole runtime packet

demand p.[any]/T + submitted p.$/T       -> initial p.$/T
demand p.$/T     + submitted p.[any]/T   -> no initial
no satisfying offer in this iteration  -> no extra action

complete NORMAL sink binding -> NormalTarget(reportId)
complete DEMAND sink binding -> DemandTarget
successful reverse actual GEN -> DemandTarget

NormalTarget(id) + all-NORMAL valid support -> same NormalTarget(id)
NormalTarget(id) + any effective DEMAND     -> no result
NormalTarget in backward                   -> ignored
DemandTarget + permitted complete support  -> DemandTarget

persisted owned P -> NormalTarget(id) -> no new insertion/publication
persisted ZERO -> NormalTarget(id)   -> skip replay; retain settled report

report id <- configured-root ZERO -> NormalTarget(id)
future Target guidance <- DemandTarget only
```

Keep ordinary AP field transfer, mark semantics, exclusions, cleaner
semantics, aliases, native record matching, source permissions, static
pools and post-processing, predefined summaries, field limits, and the
selected call policy. The only ordinary C2 change is the stated MAY-to-
EXACT rejection. Do not change generic `inside`, `applicable`, `overlap`,
`satisfying`, or AP C5 exit intersection to implement it.

Run-1 still emits atomic executable origins. It has no ND edge. Later
FULL runs keep full same-call ND support. Do not add GroundingSupport,
IR changes, rejected-offer history, late no-demand subscriptions, copied
incoming demand, forced continuation, or backward NormalTarget lookup.

## 2. Types, identity, and storage ownership

### 2.1 Keep AP and terminal results separate

Do not add Target to `Facts`. Existing `Publication`, `EdgeDelta`,
`Subscription`, `CallerRef`, and AP key equality remain unchanged.

```kotlin
@JvmInline value class ReportId(val value: Int)

sealed interface Target {
    data class NormalTarget(val id: ReportId) : Target
    data object DemandTarget : Target
}

data class TargetSummary(val premise: PremiseKey, val target: Target)
data class OwnedNormalTarget(
    val method: MethodKey,
    val premise: PremiseKey,
    val id: ReportId,
)

class TargetBatch(rows: Collection<TargetSummary>) {
    val rows = Collections.unmodifiableList(ArrayList(rows))
}
```

Target has no AP base, path, tail, mark, exclusion, or protection mask.
It never becomes an initial or premise. Do not put it in a trie leaf,
construct a fake TAINT result, or send it through `MethodEdgeStore`.
Snippets import the short names `Target.NormalTarget` and
`Target.DemandTarget`; NORMAL/DEMAND and tail constants use the existing
enum imports. `runtimePacket`, `runtimePremise`, and `runtimeProducer`
below are aliases of the RuntimeDataDomain functions, not new policies.

### 2.2 Report catalog

```kotlin
data class SinkKey(
    val method: CommonMethod,
    val statement: CommonInst,
    val ruleId: String,
)
data class ReportDescriptor(
    val key: SinkKey,
    val rule: CommonTaintConfigurationSink,
    val representativeMethodKey: MethodKey,
)

class ReportCatalog {
    private val lock = Any()
    private val byKey = HashMap<SinkKey, ReportId>()
    private val descriptors = ArrayList<ReportDescriptor>()

    fun intern(key: SinkKey, rule: CommonTaintConfigurationSink,
               context: MethodKey): ReportId = synchronized(lock) {
        check(context.method == key.method)
        check(rule.id == key.ruleId)
        byKey[key] ?: ReportId(descriptors.size).also { id ->
            descriptors += ReportDescriptor(key, rule, context)
            byKey[key] = id
        }
    }
    fun descriptor(id: ReportId): ReportDescriptor = synchronized(lock) {
        descriptors[id.value]
    }
}
```

Use the configured `CommonTaintConfigurationSink.id`. Do not use full bound
rule equality: it also includes condition and metadata. A source line alone
does not identify a statement. Witness, context, proof, run, and allocation
order do not enter `SinkKey`. A repeated key reuses its ID. The catalog
lives for the full analysis, including form-cache rebuilds. Do not retain
compiled forms or old AP witness trees for report export.

The representative context supplies the current Simple JVM exporter.
It is descriptor metadata, not part of report/Target equality. Validate
that its method is the sink method.

### 2.3 Store inventory

| Store | Owner/life | Contents and use |
|---|---|---|
| ReportCatalog | Shared; whole analysis | Stable sink keys and immutable descriptors |
| MethodTargetStore | One method actor; one run | Exact raw terminal memberships |
| Pending Target batches | Same actor | Accepted publications which still require a send |
| TargetPublicationIndex | SummaryStorage lock; one run | Published premise/Target pairs and premise-member postings |
| Existing CalleeSubscriptions | Caller runner; one run | Only offers admitted by the selected call policy |
| Target ND joins | Caller service; one run | Header bindings for known full terminal premises at one call |
| Static Target continuations | Run1PointResume actor | Existing static-interest IDs with typed terminal payload |
| NormalTargetView | Immutable run input | Persisted full owned NORMAL keys; forward conditional replay |
| SinkSeedStore | Method actor; one run | Complete DEMAND sink occurrence descriptors |
| Existing SourceHitStore | Backward actor; one run | Exact source/action permissions |
| DemandStore | Immutable next-run input | AP pairs plus typed ZERO/Target entry and ZERO exit cells |
| Committed terminal state | Driver barrier | NormalTargetView and accumulated root report IDs together |

No Target store owns ordinary method-edge processing. A report ID does
not replace the full owner or premise in a summary key.

## 3. Constant-domain implementation

Add one `RuntimeDataDomain` helper under the BIDI core. Generic AP factories,
IR conversion, and inert rule templates remain general.

```kotlin
object RuntimeDataDomain {
    fun base(b: AccessPathBase) = b !is AccessPathBase.Constant
    fun initial(i: InitialAp) = base(i.base)
    fun premise(p: PremiseKey) =
        (0 until p.size).all { initial(p.member(it)) }
    fun packet(p: PremiseKey, f: Facts) = premise(p) && base(f.base)
    fun producer(e: PathEdge) = base(e.from.base) && base(e.to.base)
    fun producer(e: MicroEdge) = producer(e.edge) && producer(e.forward)
}
```

Each Facts value has one base. If any ND member is Constant, reject the
complete packet before adding any join slot. Never remove the member or
reduce the arity.

```kotlin
fun offer(p: PremiseKey, f: Facts, sink: ResultSink) {
    if (!RuntimeDataDomain.packet(p, f)) return
    sink(p, f)
}

fun collect(at: OperationInput, sink: ResultSink): ApOut = object : ApOut {
    override fun result(f: Facts) {
        if (!RuntimeDataDomain.packet(at.premise, at.facts)) return
        if (!RuntimeDataDomain.packet(at.premise, f)) return
        existingCoverAndLayerPolicy(f) { admitted -> sink(at.premise, admitted) }
    }
    override fun markRequest(mark: TaintMark) {
        if (RuntimeDataDomain.packet(at.premise, at.facts)) needGroups(at, mark)
    }
}
```

`collect(premise,input)`, `collect(at)`, and `collectAfterRun1Policy` all
need the guard. Keep their present covering conventions; do not apply
run-1 covering twice.

### 3.1 Required boundary patch map

Paths are relative to BIDI `src/main/kotlin/org/opentaint/dataflow/bidi/`.

| Boundary | Patch |
|---|---|
| `UnitRunner.link/startInitials/subscribe`, `RunMethodHandlers.handle` | Reject before sending and before actor creation; discard an empty atomic-key packet |
| `RunMethodAnalyzer.addInitial/addLink/installPoint/process` | Reject before initial dedup, abstraction, callbacks, queueing or resume state |
| `cut/emitAfter/emitUnchanged/emitOperationResult` | Reject before diagnostics, boundary rules, static effects or store admission |
| `EngineAlgebra.reached/applyEdge/applyEdgeAt` | Check input and active producer before operations or source hooks |
| `RunMethodLocalServices` rule/ND inputs | Reject complete invalid premises before binding storage; guard direct action `targetTree` outputs |
| Call `PlanFacts` and `offerPlan` | Reject before merge, sink checks, unresolved observers and all direct stage results |
| Direct predefined `ApOut` | Guard before a result bypasses the ordinary collector |
| Current/native/reversed summary application | Guard actual input, full premise and data result before application/join/resumption |
| `Run1PointResume` registration/supplies | Guard original/input before PointKey, writer, interest or pool storage |
| `JoinedStaticWriterBinding` | Guard original premise and matched caller input, not only the STATIC output |
| `NeutralRelationBatch` and packed encode/decode/apply | Guard source shape, active producer and result base before packed effects |
| Executable edge/initial/input/request/summary/publication stores | Return their ordinary no-delta result for an invalid packet |
| Native record/demand/seed/frozen static builders | Reject active Constant endpoints before indexing/counting/materialization |

An invalid packed batch is **consumed with no output**. Do not return an
unsupported result which invokes scalar fallback or requeues it. A valid
unsupported batch retains the existing scalar fallback.

Reject one active transfer/action, not its whole statement. Literal writes,
kills, comparisons, nulls, type predicates and call resolution still run.
For example `p.value = "safe"` must still overwrite the old value. Static
final and enum fields have a STATIC base and remain in scope.

This is a selected domain restriction. The preservation proof requires
every executable intermediate packet in the compared route to be
nonconstant. It does not assert equality with every old finding.

## 4. Directed C2 and explicit ZERO admission

### 4.1 Exact demand correction

Insert one guard in `RestrictedInitialPolicy.emit`, after normalized
base/mark/budget checks and before both path branches:

```kotlin
val d = normalizeDemandFieldExclusion(demand)
if (d.fact.base != actual.fact.base || !markSub(d.fact.mark, actual.fact.mark, catalog)) return null
if (!fitsBudget(d) || !fitsBudget(actual)) return null
if (d.fact.tail == Tail.EXACT && actual.fact.tail == Tail.ANY) return null
// Continue with the existing path/tail cells.
```

Use `== Tail.ANY`, not `isAny`: the latter also includes MUST. Apply this
in both restricted directions. Run-1 abstraction remains unchanged.

| Demand | Submitted | Result, with existing base/mark/budget guards |
|---|---|---|
| `p.[any]/T` | `p.$/T` | `p.$/T` |
| `p.$/T` | `p.[any]/T` | none |
| `p.f.$/T` | `p.[any]/T` | none |
| `p.$/T` | `p.$/T` | existing exact initial |
| `p.f.$/T` | `p.[any-taint]/T` | existing exact result if E admits f |
| `p.$/U` | T, U different from T | none |

Keep STAR and other ANY-demand cells. `canEmitInitial`/`canStoreInitial`
describe the structural image: an exact actual can still witness an exact
initial. Keep that valid shape. A generic geometric meet is not C2
permission after this correction.

`InitialDemandResults.offer`, `has`, and `requireFamily` use the same
corrected policy. A pair which cannot emit contributes no required family.
Do not record it as unanswered work.

### 4.2 Typed control demand rows

Target has no path, so store its control entry separately from AP tries.

```kotlin
sealed interface DemandEntry {
    data class Data(val pattern: Pattern) : DemandEntry
    data object Zero : DemandEntry
    data object Target : DemandEntry
}
sealed interface DemandExit {
    data class Data(val pattern: Pattern) : DemandExit
    data object Zero : DemandExit
}
data class PairedDemand(val entry: DemandEntry, val exit: DemandExit)
```

Normalize canonical AP ZERO endpoints to the typed Zero constructor at
the builder boundary. Every new handoff row has both endpoints. An entry
Target contains no report ID.

```kotlin
fun controlInitials(method: MethodKey, actual: Facts): Set<InitialAp> {
    if (actual !is Reach) return emptySet()
    return if (localRows(method).any {
        it.entry == DemandEntry.Zero || it.entry == DemandEntry.Target
    })
        setOf(ap.zero) else emptySet()
}
```

The ordinary entry index and existing run-2 static completion keep their
current lookup. Add the local control result for actual ZERO only. Remove
the virtual `zeroDemand` permission. Do not turn a nonzero actual into ZERO.

### 4.3 Starts and no-op behavior

```kotlin
fun startRoot(root: MethodKey) {
    val keys = if (config.run1) setOf(ap.zero)
        else config.demand.initials(root, Reach.NORMAL, config.admissionPolicy)
    if (keys.isEmpty()) return
    val actor = port.analyzer(root)
    for (initial in keys) actor.addInitial(initial)
}

fun admitCurrentCall(part: Subscription) {
    val keys = emitRestrictedInitials(config, ops, part.callee, part.added)
    if (keys.isEmpty()) return
    port.subscribe(part) // registration precedes replay and any same-unit start
    port.startInitials(part.callee, keys)
}
```

The existing counted Start event executes this receiver-side helper.
Do not create the actor before an empty query or apply a second lookup.
InitialFactStore still starts each key once.
Delete unconditional backward `ZeroIn/addZeroEntry`. Backward ZERO calls
use the explicit query/subscribe/start arm in section 8.4, with
`zeroOnly=true` only for canonical caller ZERO. Preserve the
current early return for nonzero-original backward REACH: it is not
discovery ZERO. Keep ZERO's ordinary CFG pass-through and zeroCanReturn.

An empty emission creates no current subscription, initial packet,
Target, seed, retry, demand copy, or forced iteration. An all-unsatisfied
iteration needs no special completion action. Saved replay already done
before this gate retains its legitimate results.

## 5. Local terminal producers

### 5.1 Complete sinks

Keep the existing predicate/condition evaluator and all mark requests.
Change only the complete witness consumer:

```kotlin
fun completedSink(sink: SinkRule, at: CommonInst, binding: CompleteSinkBinding) {
    if (!runtimeBinding(binding)) return
    val target = if (binding.layer == Layer.NORMAL) {
        NormalTarget(catalog.intern(SinkKey(key.method, at, sink.rule.id), sink.rule, key))
    } else {
        for (descriptor in buildSinkSeedDescriptors(sink, key, at))
            sinkSeeds.add(descriptor)
        DemandTarget
    }

    if (config.run1) for (p in run1Origins(binding)) emitTarget(p, target)
    else emitTarget(fullPremise(binding), target)
}
```

Use the existing full compatible binding and aggregate layer. A partial
cube, one literal, or a request is not a sink witness. In run-1, retain
the current full-binding/all-ZERO test and atomic nonzero-origin emission.
Never project a later ND premise to independently sufficient members.

The adapter to the existing complete sink callback is:

```kotlin
fun runtimeBinding(b: CompleteSinkBinding): Boolean = b.inputs.all { input ->
    RuntimeDataDomain.packet(input.premise, checkNotNull(input.facts))
}
fun fullPremise(b: CompleteSinkBinding): PremiseKey {
    var result: PremiseKey = ap.zero
    for (input in b.inputs) result = ap.union(result, input.premise)
    return result
}
fun run1Origins(b: CompleteSinkBinding): List<InitialAp> {
    val origins = b.inputs.map { it.premise as InitialAp }.distinct()
    val nonzero = origins.filterNot { it.isZero }
    return if (nonzero.isEmpty()) listOf(ap.zero) else nonzero
}
```

Call this only for one complete accepted binding, never for pooled partial
OR alternatives. `ap.union` uses the current ZERO-drop/full-premise rules.
The aggregate layer is NORMAL only if every checked input is NORMAL.
Predicate and conjunction stores keep their existing complete-binding
enumeration; this proposal does not change their rule semantics.
The current TRUE/unconditional callback includes a ZERO/REACH input.
The total ZERO-fold helper does not create a new callback for an empty
partial binding.

Capture each DEMAND sink descriptor before anonymous Target dedup. Two
sinks can share one DemandTarget membership and still need different
backward seeds. A NORMAL sink creates no backward seed.
Install the consumer at the existing completed `witness(...)` callback,
including local sinks and exceptional boundary checks. Do not put it only
at normal summary exit. `trackFactsReachAnalysisEnd` stays ignored; Target
does not restore the old sink end-action GEN outputs.

### 5.2 Actual reverse GEN

The source callback needs the original premise and input. Replace the
untyped `(node,edge)` hook with a typed accepted-application value:

```kotlin
data class AcceptedSource<P,F>(
    val at: Place, val edge: MicroEdge,
    val original: P, val input: F,
    val resultPremise: P, val rawResult: F,
)
```

Migrate EngineAlgebra, FormsReference and test algebra adapters together.

```kotlin
// Inside FormApplier.micro, after accepted raw output, before resultFilters:
if (observeActualSource && !hit) {
    hit = true
    alg.acceptedSource(AcceptedSource(at, edge, premise, input, rp, raw))
}
sink(rp, raw)

// EngineAlgebra/owner:
fun acceptedSource(a: AcceptedSource<PremiseKey,Facts>) {
    check(runtimePacket(a.original, a.input))
    check(runtimePacket(a.resultPremise, a.rawResult))
    check(runtimeProducer(a.edge))
    if (forward) return
    checkNotNull(sourceHits).add(key, a.at.node, a.edge.forward, a.edge.actionId)
    if (a.edge.isSource) emitTarget(a.original, DemandTarget)
}
```

Guard input, active producer and raw result before this callback. Preserve
the existing source permission and callback-before-result-filter ordering.
`isSource` means forward ZERO to nonzero AP. Conditional mark transforms
keep their ordinary backward prerequisites and SourceHit action permission;
they create no terminal GEN Target. Opposite/native record application
creates neither an actual GEN hit nor this Target.

Do not use `SourceHitStore.add`'s fresh Boolean as Target permission. The
same source/action can be hit under several original premises.

## 6. Owned terminal emission and C5

### 6.1 Method-owned raw and pending state

```kotlin
class MethodTargetStore {
    private val seen = HashSet<TargetSummary>()
    fun add(row: TargetSummary): Boolean = seen.add(row)
    fun rows(): Sequence<TargetSummary> = seen.asSequence()
}

fun emitTarget(p: PremiseKey, target: Target) {
    if (!RuntimeDataDomain.premise(p)) return
    if (!forward && target is NormalTarget) return
    check(p.members.none { it.isFlow }) // existing typed producer invariant
    if (target is NormalTarget && config.normalTargets.contains(key, p, target.id)) return
    val row = TargetSummary(p, target)
    if (!rawTargets.add(row)) return

    if (target is NormalTarget || config.run1 || config.demand.acceptsTarget(key, p)) {
        pendingTargets.add(row)
        if (target == DemandTarget) outgoingTargets.add(row)
        requestWork()
    }
}
```

The retained check is exact `(MethodKey, full PremiseKey, ReportId)` and
comes before raw insertion, counting, or publication. Keep the retained
view immutable for a run. Same-run seen membership and pending work are
different: a duplicate must not delete an earlier pending publication.

Target emission is immediate summary work. It does not traverse remaining
instructions, require normal exit, create a return value, run an exit rule,
or cancel the original AP derivation. No AP cut or normalization applies.

### 6.2 Paired restriction

```kotlin
fun entryAccepts(dc: DemandEntry, member: InitialAp): Boolean = when (dc) {
    DemandEntry.Zero, DemandEntry.Target -> member.isZero
    is DemandEntry.Data -> policy.canStoreInitial(dc.pattern, member.toPattern())
}

fun acceptsTarget(method: MethodKey, original: PremiseKey): Boolean =
    localRowsWithZeroExit(method).any { pair ->
        original.members.any { member -> entryAccepts(pair.entry, member) }
    }
```

Keep the full original premise after a per-member entry query, as AP C5
does today. The test is one complete pair, not the union of separate entry
and exit permissions. No raw DEMAND Target bypasses it after run-1.

| `D_p` | Actual conclusion | Result |
|---|---|---|
| ZERO | ZERO | ZERO |
| ZERO | NormalTarget(id) | same constructor/id |
| ZERO | DemandTarget | DemandTarget |
| ZERO | ordinary AP | none |
| AP pattern | Target | none |
| AP pattern | AP | existing AP exit restriction |

For ordinary AP publications, use the same `entryAccepts` dispatch and
existing `restrictConclusionOnly` for Data exits. A Zero exit keeps Reach
only. Target/Zero entries can admit only original ZERO. Remove the backward
ZERO C5 bypass. NORMAL terminals use their selected raw forward lane;
the structural table does not enable backward NORMAL processing.

The existing AP static completion is consulted only by its existing
ordinary lookup paths. Do not add graph lookup for control Target rows.

## 7. Terminal publication and delivery

### 7.1 Separate typed event

Add a parallel protocol, rather than changing AP publication equality:

```kotlin
interface TargetPublicationSink {
    fun publishTargets(method: MethodKey, batch: TargetBatch)
}
interface TargetApplier {
    fun applyTarget(part: Subscription, row: TargetSummary, member: Int)
    fun applyStaticTarget(part: Subscription, row: TargetSummary, member: Int)
    fun staticTargetSupply(part: Subscription, row: TargetSummary,
                           member: Int, supply: RegionGroups)
}
class TargetDelivery(val callee: MethodKey, batch: TargetBatch) : RunEvent {
    val rows = batch.rows // detached immutable membership list
}
```

Extend RunnerPort/SubscriptionPort post methods, RunMethodHandlers and
RunEvent dispatch. TargetDelivery is addressed to its subscribed runner,
like Delivery. Count it with the existing in-flight protocol and queue
priority; it is not an uncounted callback or a method-owner start event.
Inject TargetPublicationSink as a parallel required constructor service;
keep the existing AP PublicationSink fun interface. Have MethodCallServices
also implement TargetApplier. The actor dispatches Target calls through
its configured call-service interface, as it dispatches AP calls today.
SubscriptionPort exposes that actor as TargetApplier. Migrate decorators
and fixtures explicitly; do not bypass them with a cast to the concrete
RunMethodCallServices or add a default silent-drop implementation.

### 7.2 Locked publisher, runner-owned subscriber

SummaryStorage gains a `TargetPublicationIndex` behind its existing lock.
It maps full premise to a set of exact Target constructors. Index each
premise member once. No conclusion Facts, mark tree or fake Publication
is constructed.

```kotlin
fun publishTargets(batch: TargetBatch) {
    val (delta, recipients) = synchronized(lock) {
        targetIndex.addAll(batch.rows) to subscribers.toList()
    }
    if (delta.isEmpty()) return
    steps.notify {
        for (subscriber in recipients) {
            cancellation.checkpoint()
            check(subscriber.notifyTargets(method, TargetBatch(delta)))
        }
    }
}
```

`notifyTargets` posts only. On TargetDelivery, the caller runner queries
its current CalleeSubscriptions and invokes its actor TargetApplier.
Do not inspect caller-owned directories on the publisher thread.

Extract premise-position candidate lookup from PublicationIndex and
CalleeSubscriptions into helpers which accept `(PremiseKey,member)`.
Have existing AP functions delegate to them without changing the selected
prefix/extension rules. Terminal matching uses the same candidates and
full AP predicate. Add a run-1 static candidate arm in section 9.

SubscriptionManager.subscribe must replay both AP and Target candidates
after recording the accepted input. Keep register-before-replay/start.
If publication precedes registration, replay finds it. If registration
precedes publication, delivery finds it. Both paths can occur; exact
caller-owned output dedup handles that duplicate.

### 7.3 No lost pending send

```kotlin
fun flushTargetPublications() {
    if (pendingTargets.isEmpty()) return
    val detached = pendingTargets
    pendingTargets = ArrayList()
    try {
        targetSink.publishTargets(key, TargetBatch(detached))
    } catch (failure: Throwable) {
        pendingTargets.addAll(0, detached)
        throw failure
    }
}
```

Include pendingTargets in actor work/freeze checks. A seen row still owns
its pending obligation until publication is accepted. Required delivery
rejection fails/cancels the run. Never select COMPLETE or commit retained
rows after a lost delivery. Do not remove seen membership and invent a
second semantic row to recover a failed send.

## 8. Caller matching, ND, and retained replay

### 8.1 Ordinary singleton

```kotlin
fun matchTargetMember(part: Subscription, member: InitialAp,
                      target: Target, saved: Boolean): TargetBinding? {
    if (!runtimePacket(part.ref.premise, part.added)) return null
    if (part.zeroOnly && !member.isZero) return null
    val recordMatch = saved && member.tail != Tail.ANY_TAINT
    val selected = ops.satisfying(part.added, member, mode, record = recordMatch) ?: return null
    // MUST uses the existing inside subset; applicable-only residue is not NORMAL.
    val layer = join(part.ref.callerLayer, selected.layer, part.linkLayer)
    if (target is NormalTarget && layer != NORMAL) return null
    return TargetBinding(part.ref, layer)
}

fun applyTarget(part: Subscription, row: TargetSummary, member: Int, saved: Boolean) {
    if (!forward && row.target is NormalTarget) return
    if (!runtimePremise(row.premise)) return
    val binding = matchTargetMember(part, row.premise.member(member), row.target, saved) ?: return
    if (row.premise is InitialAp) emitMatchedTarget(listOf(binding), row.target)
    else targetJoin(part, row, saved).add(member, binding).forEach { emitMatchedTarget(it, row.target) }
}
```

The three-argument TargetApplier override delegates to this internal
helper with `saved=false`. Only retained replay calls it with `saved=true`.
The actor's three-argument method forwards through injected callServices;
it does not duplicate matching or bypass a service decorator.

`join` is ordinary layer disjunction. A NORMAL Target requires every
effective contributor to be NORMAL, including native MUST classification.
It emits nothing when this guard fails. An existing DemandTarget remains
DEMAND. No failed NORMAL application creates a seed or an anonymous Target.

```kotlin
fun emitMatchedTarget(bindings: List<TargetBinding>, target: Target) {
    if (target is NormalTarget && bindings.any { it.layer != NORMAL }) return
    val original = bindings.map { it.ref.premise }.reduce(ap::union)
    emitTarget(original, target)
}
```

Retain full caller origins. Do not call resumeCallees, bindBack/bindOut,
return cleanup, aliases, or CFG successor delivery for a terminal. Input
binding and complete premise satisfaction still apply.

### 8.2 Complete same-call ND

Use a terminal-specific header join, not NdSummaryJoin's TaintTree cast:

```kotlin
data class TargetJoinKey(
    val callee: MethodKey, val premise: PremiseKey, val target: Target,
    val call: CommonInst, val stageOrdinal: Int, val saved: Boolean,
)
data class TargetBinding(val ref: CallerRef, val layer: Layer)

class TargetCallJoin(arity: Int, cancellation: Cancellation) {
    private val members = KaryJoin<TargetBinding>(arity, cancellation)
    fun add(slot: Int, binding: TargetBinding): List<List<TargetBinding>> =
        members.add(slot, binding)
}
```

The caller service is one method owner, and the key fixes callee, call,
stage, full premise, result constructor/id and read lane. All required
slots must be present. Union original caller premises only after this
complete join. Do not pool different calls or reduce the arity.

Payloads are immutable. A new ID uses a new exact join key and is replayed
against current eligible member inputs. A new member creates new complete
tuples through KaryJoin. No full-result product archive or protection-
upgrade mechanism is needed for Target payloads. Retained ND replay stores
only matched headers for known records, not all rejected input facts.

### 8.3 Selected call order

```kotlin
fun offerCalleeInput(part: Subscription) {
    check(!part.zeroOnly) // the canonical backward ZERO arm is below
    if (!runtimePacket(part.ref.premise, part.added)) return
    if (config.run1) {
        port.subscribe(part)
        port.link(part.callee, part.ref, part.linkLayer, part.added)
        return
    }
    replayPersistedApSummaries(part)     // unchanged; every original offer
    replayPersistedNormalTargets(part) // forward, nonzero saved records only
    admitCurrentCall(part)             // complete lookup; empty means no-op
}
```

Keep the original complete offer for all three steps. Do not admit live
inputs or subscribe because a saved record happens to match. Do not add
a compatibility query for hypothetical current summary premises. The
callee receives final canonical initial keys and performs no second query.

Retained NORMAL lookup skips backward and ZERO rows before matching. It
does not republish the callee's old row. A resulting caller row is offered
to that caller's exact retained/seen dedup. A new caller key remains
eligible; no extra durable replay-input history is added.

### 8.4 Guided backward ZERO calls

```kotlin
fun backwardZeroAtCall(item: EdgeDelta, ctx: CallContext) {
    if (ctx.plan.zeroCanReturn) core.emitUnchanged(item)
    if (!item.premise.isZero) return // preserve existing nonzero-REACH behavior
    check(item.facts is Reach)
    fireExistingLocalSinkSeedsAndBoundStages(item.node, ctx)
    for (callee in ctx.plan.callees) {
        val ref = CallerRef(key, ap.zero, ctx.callerLayer, item.node, ctx.calleeOrdinal)
        val part = Subscription(callee, ref, item.facts.layer, item.facts, zeroOnly = true)
        admitCurrentCall(part)
    }
    applyExistingPredefinedZeroStages(item, ctx)
}
```

This replaces only the unconditional backward callee start. Local seed
timing, predefined stages and ordinary zeroCanReturn pass-through remain.
Do not pass zeroOnly to replayPersistedApSummaries: that existing helper
requires an ordinary subscription. Native backward ZERO AP records are
excluded; the only valid opposite-forward record at ZERO is control
ZERO-to-ZERO, already covered by the existing pass-through. NormalTarget
is ignored backward. No marked saved data transfer is removed by keeping
the existing zeroOnly saved-replay exclusion.

## 9. Run-1 STATIC-premise delivery

Ordinary AP member lookup is not the whole run-1 call protocol. A genuine
caller ZERO/REACH port also activates conditional static summaries today.
Extend that path to typed Target rows; do not silently lose static sinks.

The typed producer invariant is useful here: a held sink input is Reach
or TAINT, not FLOW; existing K6 ties that input to a non-FLOW origin.
Actual reverse GEN also requires a concrete marked input. Thus valid
Target support has canonical ZERO or concrete non-FLOW AP members.
Check that invariant at the producer adapter. It is not permission to
reinterpret a FLOW request as a held sink condition.

```kotlin
fun applyStaticTarget(part: Subscription, row: TargetSummary, member: Int) {
    check(config.run1 && part.ref.premise.isZero && part.added is Reach && !part.zeroOnly)
    val initial = row.premise.member(member)
    check(initial.base == STATIC && initial.mark is MarkSlot.Concrete)
    if (core.dropsStaticField(initial)) return

    if (core.hasKnownStaticGroupInput(row.premise)) {
        applyStaticTargetInput(part, row, member, core.knownStaticInput(initial))
    } else {
        pointResumes.targetCallInterest(part, row, member)
    }
}
```

Add typed Target candidates to the existing run-1 static-control scans in
SubscriptionManager replay and delivery. A direct static input or a pool
reply must use the same selected-original constructor as AP static input:

```kotlin
fun applyStaticTargetInput(part: Subscription, row: TargetSummary,
                           member: Int, actual: Facts) {
    val initial = row.premise.member(member)
    val matched = ops.satisfying(actual, initial, mode) ?: return
    for (leaf in ops.leaves(matched)) {
        val path = leaf.fact.path.take(2)
        val selected = ap.initial(Pattern(leaf.fact.copy(
            path = path,
            tail = if (leaf.fact.tail == EXACT && leaf.fact.path.size <= 2) EXACT else STAR,
        ), ExclusionSet.Empty))
        val selectedInput = core.forceRun1Layer(selected, ops.startFact(selected, mode))
        val ref = part.ref.copy(premise = selected)
        applyTarget(part.copy(ref = ref, linkLayer = selectedInput.layer, added = selectedInput),
            row, member, saved = false)
    }
}
```

Keep the exact global-class marker checks and field anchors from
`applyStaticInput`; extract their shared constructor instead of copying
and later changing one branch. All run-1 static support remains DEMAND.
No new STATIC fact initial is delivered to a method entry.

For a late supply, add a typed row to Run1PointResume:

```kotlin
data class StaticTargetKey(
    val callee: MethodKey, val ref: CallerRef, val linkLayer: Layer,
    val row: TargetSummary, val member: Int,
)
class StaticTargetContinuation(val key: StaticTargetKey,
                               val part: Subscription,
                               val row: TargetSummary, val member: Int) {
    var waiting = MarkSet.EMPTY
}

private val terminalCallIds = HashMap<StaticTargetKey, Long>()
private val terminalCalls = HashMap<Long, StaticTargetContinuation>()

fun targetCallInterest(part: Subscription, row: TargetSummary, member: Int) {
    val initial = row.premise.member(member)
    val key = StaticTargetKey(part.callee, part.ref, part.linkLayer, row, member)
    val id = terminalCallIds.getOrPut(key) {
        nextResumeId().also { terminalCalls[it] = StaticTargetContinuation(key, part, row, member) }
    }
    val continuation = terminalCalls.getValue(id)
    val atom = (initial.mark as MarkSlot.Concrete).mark
    val requested = MarkSet.of(core.ap.marks.runtimeAtom(atom, core.mode.markMode))
    val fresh = requested - continuation.waiting
    if (fresh.isEmpty) return
    continuation.waiting += fresh
    core.staticBatch.interests += StaticInterest(core.key, id, initial.toPattern(), fresh)
    core.requestWork()
}
```

Use the existing unique resume-ID allocator. Add this arm to actor-owned
PointReady dispatch, after the service lock is released:

```kotlin
terminalCalls[effect.id]?.let { continuation ->
    continuation.waiting -= effect.supply.groups
    if (continuation.waiting.isEmpty) {
        terminalCallIds.remove(continuation.key)
        terminalCalls.remove(effect.id)
    }
    core.staticTargetCallSupply(continuation.part, continuation.row,
        continuation.member, effect.supply)
    return
}

// RunMethodAnalyzer forwards through the injected MethodCallServices:
internal fun staticTargetCallSupply(part: Subscription, row: TargetSummary,
                                    member: Int, supply: RegionGroups) =
    callServices.staticTargetSupply(part, row, member, supply)

// RunMethodCallServices implements the required TargetApplier operation:
override fun staticTargetSupply(part: Subscription, row: TargetSummary,
                                member: Int, supply: RegionGroups) {
    val core = active()
    if (core.dropsStaticField(row.premise.member(member))) return
    val actual = core.staticFacts(supply)
    if (!runtimePacket(part.ref.premise, actual)) return
    applyStaticTargetInput(part, row, member, actual)
}
```

Migrate MethodCallServices decorators and fixtures for this required
callback as well. Do not call the private concrete service from
Run1PointResume. Other
AP/static continuations retain their behavior. No fake AP conclusion,
extra static write point, new static request kind, or static return suffix
is introduced. Targets do not enter frozen static AP composition.

## 10. Retained NORMAL storage and replay suppression

### 10.1 Exact owned membership

```kotlin
interface NormalTargetView {
    fun contains(method: MethodKey, p: PremiseKey, id: ReportId): Boolean
    fun candidates(method: MethodKey, actual: Facts): Sequence<OwnedNormalTarget>
    fun zeroRows(): Sequence<OwnedNormalTarget>
}
```

Implement an immutable per-method map of full premise to ID set plus
premise-member postings. Retain one full owned record for ND. The run
never mutates this view. The barrier merges fresh NORMAL rows and builds
the next view. Use this same index for the check in emitTarget; no second
cross-run seen cache is needed.

```kotlin
fun replayPersistedNormalTargets(part: Subscription) {
    if (!forward) return
    for (record in config.normalTargets.candidates(part.callee, part.added)) {
        if (record.premise.isZero) continue
        for (member in candidateMemberSlots(record.premise, part.added))
            applyTarget(part, TargetSummary(record.premise, NormalTarget(record.id)),
                member, saved = true)
    }
}
```

`candidateMemberSlots` uses the same premise-position scan as the AP
saved record reader, followed by the full saved matching predicate in
section 8. Do not skip every saved nonzero relation because it exists;
that would disable useful replay. Suppress re-emission of its **callee
owned key**, then test any resulting caller owned key independently.

```text
retained: (checkContext, p.$/T, id=4)
rediscover that same key inside check -> no row/publication
new NORMAL caller input -> may produce (callerContext, callerOriginal, 4)
that caller key already retained -> no row/publication
that caller key new -> publish once
```

Do not use only ID, method name, premise base, or a premise prefix as a
dedup key. Adding a run/witness/batch field would defeat this rule.

### 10.2 Settled ZERO and final reports

For every retained ZERO-premise NORMAL row, require:

```text
retained(method, ZERO, id) => id is in the committed root report IDs
```

This includes nonroot method rows. A NormalTarget carries only a report
effect; it gives no AP result or backward demand. Reapplying a retained
ZERO row therefore adds no report ID. Skip its replay, keep the row for
exact duplicate rejection, and retain the reported ID across later runs.

Establish the invariant by induction on finite first forward ZERO
admission routes. Roots start normal ZERO. A child's first ZERO start
comes from an earlier reached caller and register-before-start. A fresh
ZERO NormalTarget follows that finite normal caller route upward. At each
owner either a fresh row propagates, or a retained duplicate already has
its reported ID by induction over completed barriers. The configured root
collects the ID before the next retained view is exposed. Recursive calls
do not create an infinite first-admission ancestry.

Required adapter conditions are explicit: no detached/imported forward
ZERO starts; normal forward ZERO control; pending Target work and delivery
included in completion; raw NORMAL publication; caller NORMAL matching;
and report/record publication at one completed boundary. Test all of
them. A ZERO premise alone is not a settlement certificate.

```kotlin
data class CommittedTerminals(
    val normal: NormalTargetView,
    val rootReports: Set<ReportId>,
)

fun prepareTerminals(result: CompleteRun, old: CommittedTerminals): CommittedTerminals {
    check(result.targetPublicationsQuiescent)
    val ids = old.rootReports.toMutableSet()
    if (result.forward) {
        for (root in config.roots)
            for (row in result.rawTargets(root))
                if (row.premise.isZero && row.target is NormalTarget) ids += row.target.id
    }
    val merged = old.normal.mergeFreshNormalRows(result)
    check(merged.zeroRows().all { it.id in ids })
    return CommittedTerminals(merged, immutableCopy(ids))
}
```

Backward produces no new NORMAL row and preserves this state. Build the
whole new view and ID set before one driver-owned reference swap. A failed
or incomplete run cannot expose half of that pair. Existing AP record
persistence remains its own selected operation; do not redesign that
store to add this terminal snapshot.

## 11. Handoff, seeds and driver integration

### 11.1 Exact paired projection

```kotlin
fun project(method: MethodKey, p: PremiseKey, conclusion: DemandEntry) {
    for (member in p.members)
        builder.add(method, PairedDemand(conclusion, exitOf(member)))
}

fun projectTargets(actor: RunMethodAnalyzer) {
    for (row in actor.outgoingTargets) {
        check(row.target == DemandTarget)
        project(actor.key, row.premise, DemandEntry.Target)
    }
}
```

`exitOf(canonical ZERO)` is DemandExit.Zero. Other members become existing
normalized AP exit patterns. There is no ZERO-to-null exception. The full
ND relation remains full inside the run; member projection is guidance
for the next run, as before.

For AP rows, preserve current selection: DEMAND, NORMAL ND, and NORMAL
backward-ZERO guidance. Remove only the backward-ZERO C5 bypass and
unpaired handoff. Keep the separate exclusion of backward-ZERO AP rows
from native records. Target selection precedes ordinary AP exceptions;
NormalTarget is never exported as refinement demand.

### 11.2 Seeds independent of reports and Target deltas

```kotlin
data class SinkSeedDescriptor(val seed: Seed) {
    init { require(seed is Seed.Sink || seed is Seed.PredicateSink) }
    val method get() = seed.method
    val statement get() = seed.statement
}
```

SinkSeedStore is a set of those descriptors. It has no witness AP trees.
Capture on complete local DEMAND sink observation, before Target dedup.
Freeze full predicate handles as `Seed.PredicateSink`; use existing exact
`Seed.Sink` patterns for the legacy nonpredicate form. Resolve through
DirectedForms at the reached seed statement, preserving full condition
and all selected positive requirements. Constant-based materializations
are rejected by RuntimeDataDomain.

Construct the descriptors at the observation point, using existing owned
Seed types instead of retaining a bound SinkRule or compiled form:

```kotlin
fun buildSinkSeedDescriptors(sink: SinkRule, method: MethodKey,
                             at: CommonInst): List<SinkSeedDescriptor> = (when {
    sink.predicate != null && !sink.unconditional ->
        listOf(Seed.PredicateSink(checkNotNull(sink.occurrenceId), method, at))
    sink.predicate != null -> emptyList() // existing unconditional predicate rule
    else -> sink.seedPatterns().map { Seed.Sink(sink.rule, method, at, it) }
}).map(::SinkSeedDescriptor)
```

The descriptor holds the predicate handle or owned pattern seed directly.
The actor owns its frozen seed set through the
driver barrier. Do not clear it in RunMethodLocalServices.freeze. Raw
Target rows likewise survive actor freeze; subscription indexes and
transient caller joins can be released after required deliveries join.

```kotlin
fun toBackwardSeeds(result: CompleteForwardRun): SeedIndex =
    SeedIndex.of(result.actors.flatMap { it.sinkSeeds }.map { it.seed })

fun toForwardSeeds(result: CompleteBackwardRun): SeedIndex =
    SeedIndex.of(result.actors.flatMap { actor ->
        actor.sourceHits.occurrences().map { hit ->
            Seed.Source(hit.method, hit.statement, hit.forward, hit.action)
        }
    })
```

No final report entry is used to build seeds. A stored descriptor does not
start its method: actual admitted ZERO must reach that statement. NormalTarget
replay creates no sink descriptor. Existing action identity and conditional
source permission remain unchanged.

### 11.3 Completed barriers and stopping

```kotlin
fun barrier(config: RunConfig, result: RunResult): Next {
    require(result.status == COMPLETE)
    val nextTerminals = prepareTerminals(result, committedTerminals)
    val handoff = buildPairedApAndTargetDemandAndSeeds(result)
    val frontier = buildFrontier(result, handoff, nextTerminals)
    persistExistingNativeApRecords(result)
    val next = if (config.forward && handoff.refinementMemberships == 0) Complete
        else existingBudgetAndPolicyDecision(config, result, handoff,
            normalTargets = nextTerminals.normal)
    recordFrontier(frontier)
    // All allocation, validation and fallible work precede exposure.
    // The reference assignment and return below do not call another service.
    committedTerminals = nextTerminals
    return next
}
```

Include all actor Target publication queues, all counted TargetDelivery
events, and required static replies in engine quiescence. Freeze requires
those queues empty. Join runners before reading owner state.

Outgoing refinement memberships include selected AP guidance and
DemandTarget. A NormalTarget or retained report ID does not require
another iteration. A rejected offer adds nothing to that count. Preserve
existing explicit budgets, OOM/timeout/failure results, and forward-only
policy checks. Remove hasDemandVulnerability as an early stop input.

Do not commit a new terminal/report snapshot after an abnormal barrier.
If native AP persistence fails during preparation, end through the
existing failure path and retain the previous terminal/report snapshot;
do not run another iteration with a partial next snapshot.
Any prepared next RunConfig takes `normalTargets` from the explicit
`nextTerminals.normal` argument. It must not read the old global
`committedTerminals` while the next decision is prepared.

## 12. Final report and JVM export

The report holds only committed root-normal IDs and descriptors:

```kotlin
data class FinalReportEntry(val id: ReportId, val descriptor: ReportDescriptor)
fun finalEntries(): List<FinalReportEntry> = committedTerminals.rootReports.map { id ->
    FinalReportEntry(id, catalog.descriptor(id))
}

fun toVulnerabilities(report: Report): List<VulnerabilityWithTrace> =
    report.entries.map { entry ->
        val d = entry.descriptor
        val node = TaintVulnerabilityRuleNode.Unconditional(d.representativeMethodKey)
        VulnerabilityWithTrace(
            TaintVulnerability(d.key.statement, d.key.ruleId, hashMapOf(d.rule to node)),
            TracePathGenerationResult.Simple,
        )
    }
```

Only configured-root ZERO NormalTarget rows add IDs. A nonroot ZERO row,
a conditional nonzero root premise, or DemandTarget is not a final report.
Deduplicate IDs across witnesses, contexts, roots and iterations. Keep the
existing RunStatus-to-export-status mapping. Replace CONFIRMED/DEMAND
candidate logging with final report and outgoing refinement counts.

Delete the final-report dependency on persistent SinkWitness lists and
`witnesses.first()`. Keep transient complete binding/proof inputs required
to check a condition. Report IDs do not claim that every old local
candidate must remain an exported report under this selected contract.

## 13. Principal traces and differential controls

### 13.1 Direct source, sink and terminal shortcut

```java
// Rules: src() assigns T at result.$; sinkT(x) checks x.$/T.
void root() {
    Object x = src();
    // An admitted exact NORMAL source image: ZERO -> x.$/T, NORMAL.
    sinkT(x);
    // Complete NORMAL witness publishes ZERO -> NormalTarget(id).
    while (true) { }
}
// Final id can be collected; Target did not invent a normal return.
```

The source image can be DEMAND in a coarser iteration. Then the complete
sink binding emits DemandTarget and no report ID. The rule actions and
field cut decide that layer; Target does not upgrade it.

### 13.2 Shared identity and different conditional premises

```text
method M: arg(0)/T -> NormalTarget(7)
method M: arg(1)/U -> NormalTarget(7)
```

One catalog ID, two full relations. NORMAL actuals can apply each at its
own call. A DEMAND actual produces no NORMAL terminal effect. Two final
root ZERO paths collapse to one report ID.

### 13.3 Directed admission and unanswered iteration

```text
Dc=p.[any]/T, actual=p.$/T -> p.$/T initial
Dc=p.$/T, actual=p.[any]/T -> no initial, no current subscription
every offer fails Dc -> no completion action for that demand
```

Saved replay still precedes the current gate. It is not rolled back.
There is no blocked-demand store or fallback Target.

### 13.4 DEMAND sink cycle with a ZERO pair

```text
F: p/T -> DemandTarget
F to B: (Target, p/T)
B: Target admits actual ZERO; reached sink seed produces ZERO -> p/T
B C5: Dc Target accepts ZERO; Dp p/T accepts result p/T
B to F: (p/T, ZERO), including a selected NORMAL backward-ZERO result
F: actual p/T admits its initial
F C5: Dp ZERO accepts a produced DemandTarget
```

If no actual p/T satisfies that forward demand, emit no initial and do
nothing special. The cycle is a permitted route, not a forced retry.

### 13.5 Actual GEN and source permission

```text
selected AP forward guidance: ZERO -> ret/T gives (ret/T, ZERO)
B: ret/T requirement reaches actual reverse GEN
B: record source/action permission; emit ret/T -> DemandTarget
B to F: (Target, ret/T)
F: actual ZERO is admitted; allowed GEN gives ZERO -> ret/T
```

Only an actually selected AP guidance row starts this trace. A saved
NORMAL ZERO-to-ret record is a separate existing replay path and does
not need a fabricated actual source hit.

### 13.6 ND and seed dedup

```text
later FULL relation: {arg(0)/T, arg(1)/U} -> NormalTarget(9)
same call has both NORMAL inputs -> caller full-origin union -> NT(9)
one input DEMAND or a missing member -> no NORMAL result
inputs from different calls -> no complete tuple

sink A and sink B each produce same P -> DemandTarget
raw Target has one membership; SinkSeedStore retains A and B
```

### 13.7 Run-1 static sink

```java
void root() { setStatic(); consume(); }
void consume() { sinkT(C.f); }
```

The existing static pool/mark mechanism supplies the concrete static
premise. The complete run-1 sink emits a DEMAND static-premise Target.
The caller ZERO control port visits the typed static candidate, obtains
the existing selected static original from known/pool input, and publishes
that caller terminal directly. No AP return suffix or new write point is
created. Keep exact class markers and the statics diagnostic flag.

### 13.8 Persisted dedup and ZERO settlement

```text
retained (M, p/T, id) + rediscovered same owned key -> no publication
saved nonzero relation + new NORMAL caller -> caller row offered once
caller row already retained -> no publication
retained (M, ZERO, id) -> no replay; committed id remains reported
backward sees a NORMAL terminal -> no action
```

## 14. File plan, removals and test order

Use the existing BIDI main Kotlin root unless a JVM path is stated.

| Part | Required edits |
|---|---|
| new RuntimeDataDomain | One active-base/packet/producer rule; no IR adapter change |
| RestrictedInitialPolicy | Exact/MAY guard only; shared policy clients retained |
| FormApplier, FactAlgebra, EngineAlgebra | Typed AcceptedSource context, constant guards before hooks |
| RunMethodLocalServices | Complete sink consumer, local seed set, preserved condition checks |
| RunMethodAnalyzer | Raw/pending Target store, C5 branch, explicit root ZERO lookup and work checks |
| new TargetPublicationIndex | Premise-only postings and typed terminal memberships |
| SummaryStorage, SubscriptionManager, CalleeSubscriptions | Typed replay/delivery using existing subscription ownership |
| RunEvent, RunnerPort, SubscriptionPort, UnitRunner, handlers | Immutable counted TargetDelivery, required-send failure handling |
| MethodServices, RunMethodCallServices | Required terminal and static-supply interface, singleton/ND Target matching, saved replay, guided backward ZERO |
| Run1PointResume | Typed static Target continuation on existing pool mechanism |
| new NormalTargetStore and ReportCatalog | Exact retained keys and stable immutable descriptors |
| DemandStore and handoff | Typed controls, paired ZERO exit, no virtual/bypass ZERO |
| IterationDriver, Report, Frontier | Completed terminal/report snapshot, outgoing-demand stop/counts |
| packed, predefined, joined static, record/seed builders | All constant-domain funnels from section 3 |
| JVM JIRBidiAnalysis | Descriptor export and final report logging |

Remove after migrating their production users:

```text
virtual DemandStore.zeroDemand and unconditional offer
unconditional restricted root/backward-callee ZERO start and ZeroIn
backward-ZERO C5 bypass
ZERO-to-null handoff conversion
report.demandEntries as sink-seed source
ReportBuilder local-candidate replacement and confirmed flags/states
persistent ConcurrentVulnerabilityStore wiring in SharedObjects/RunResult
mandatory final witness lists and witnesses.first() exporter
hasDemandVulnerability stop and old frontier confirmation counts
```

Move any still-used RuleId alias to a small type file instead of retaining
the old persistent witness store for it. Keep Reach, initial-start dedup,
normal backward-ZERO AP guidance, backward-ZERO native-record exclusion,
AP publication types, complete binding proofs, source occurrences,
static pool semantics, and the selected call policy.

Implement in proof-first/TDD order:

1. Run the v2 constructive models. Add failing runtime domain/C2 tests.
2. Add constant funnels, including rejected-packed-batch consumption.
3. Add catalog/raw/retained Target stores and exact owned-key tests.
4. Add typed producers, callbacks, publication/receipt and caller matching.
5. Add the static adapter and complete same-call Target ND tests.
6. Replace ZERO admission/C5/handoff and seed source. Test no-op rejection.
7. Add the completed terminal/report commit and export migration.
8. Remove old paths. Run complete core/JVM suites and source-delta audit.
9. Commit the implemented change, then run the configured project campaign.

Required tests include:

```text
RuntimeDataDomainTest: all tails/layers, Constant input/output/producer,
  full ND rejection, static final positive, literal overwrite effect.
InitialEmissionContractTest: ANY cannot answer EXACT at equal/ancestor
  paths; EXACT/MUST positive; marks/E/budgets; all other cells unchanged.
SourceApplicationTest: original premise retained; callback before result
  filter; Constant creates no hit; conditional and record reads no GEN Target.
TargetStoreTest: same/different id, full P, full MethodKey, retained/current
  dedup and earlier pending send not erased by duplicate rediscovery.
TargetProtocolTest: publication before/after registration; same/cross unit;
  late input; required-send rejection; duplicate receipt; cancellation.
TargetCallTest: NORMAL-only, MUST inside subset, ignored backward,
  full ND/cross-call/partial controls, direct terminal no return/suffix.
StaticTargetTest: ZERO control candidate, known input, late pool supply,
  class marker, disableRun1Statics, original static premise preserved.
TargetHandoffTest: both paired ZERO cycles, NORMAL backward-ZERO AP row,
  C5 same-pair test, Target count in stop, no-op rejected/all-rejected offers.
TargetReportTest: root+ZERO only, stable catalog context-independent IDs,
  kept IDs after ZERO replay skip, failed barrier no partial snapshot,
  every retained ZERO id already reported.
```

Use historical expected results only in explicitly named old-reference
controls. They are not the selected new admission/reporting contract.

## 15. Proof package and implementation evidence

The new [proof package](../../spec/lean/proposals/constant-filter-target-zero-implementation-v2-20261031/README.md)
is under `spec/lean/proposals/constant-filter-target-zero-implementation-v2-20261031/`.
It contains selected rules only. It does not import the old hypothetical
NORMAL-to-DEMAND promotion controls or the withdrawn source-permission
workaround as an implementation requirement.

The checker binds this document, the specification hash, the maintained
Lean modules, and reviewed runtime source bytes. Run:

```sh
python3 spec/lean/proposals/constant-filter-target-zero-implementation-v2-20261031/check.py
```

The check passes for 12 modules and 193 theorems. It audits 369 public
declarations, including 174 executable definitions and 2 abbreviations.
Only `propext` and `Quot.sound` occur. The final theorem map and input hashes
are in the package's README and receipt. The models establish:

| Obligation | Model/evidence |
|---|---|
| Constant-free packets, stores and safe-route preservation | ConstantBoundary |
| Directed MAY/EXACT C2 and all-unsatisfied no-op | InitialEmissionExact, UnansweredDemand |
| Control C2/C5, paired handoff, source scope, normal-only application | SelectedCore, SelectedTargetApplication |
| Stable report IDs and complete ND layer/origin rules | TargetZeroRegistry, TargetZeroND |
| Arbitrary-arity complete Target tuples and full origins | TargetJoin |
| Exact owned retained/seen delta and pending obligation preservation | OwnedDelta |
| Register/replay/start, counted accepted delivery and completion | TerminalProtocol |
| Finite rooted ZERO settlement and complete-barrier report invariant | ZeroSettlement |
| Non-FLOW Target producer kind and unchanged static descriptors | ProducerDomain |

No proof assumes a fresh nonroot ZERO row was already reported. It needs
an executable finite admission/receipt route to a root or a prior settled
row. No proof equates a seen key with accepted delivery.

AP geometry, K6 producer typing, actual call/static binding, cache/context
identity, coroutines and cancellation are runtime adapters. Test them at
the listed boundaries; finite Boolean examples alone do not verify them.
The selected domain, admission and reporting changes are not a theorem
of equality with the old report set. Do not claim whole-program no-FN,
convergence or a measured speedup from the model check.

## 16. Project validation and measurements

The latest campaign remains:

| Project | Reached | Complete | Accepted forward | Result |
|---|---|---|---|---|
| OWASP | run-5 | run-5 | run-5 | OK |
| conductor | run-4 | run-3 | run-3 | TIMEOUT |
| thingsboard | run-2 | run-1 | run-1 | OOM |
| Stirling-PDF | run-7 | run-6 | run-5 | TIMEOUT |

Use current configured Gradle runProjectAnalyzer commands: FULL run-1,
statics/aliases on, 16 GB, limits `1,1,2,3,...`, current project budgets.
Use OWASP's CI setup and the three selected real projects. Reuse the saved
fixed baseline; do not rerun it or add another project/configuration.

Measure per iteration:

```text
reached / complete / accepted-forward iteration, direction, limit, status
engine and barrier time, heap/RSS, OOM retained owners and profile hot paths
Constant rejects by input/producer/ND/packed/static/record/seed boundary
explicit ZERO offers/admission/rejection and ZERO-only method/edge counts
raw/published/retained Target memberships, stable IDs and final report IDs
retained-key suppression, same-run suppression, pending publications/receipts
NORMAL support rejections, backward ignores, persisted ZERO replay skips
AP vs DemandTarget outgoing memberships and owners; sink/source seed counts
current and saved summary application counts; static Target activation counts
```

Capture configured profiles and OOM snapshots, analyze them, and clean
closed task-owned captures according to task.md. Preserve user debug
directories. Compare final finding identities by sink location/rule with
the saved baseline and current runtime. Distinguish selected constant/C2/
report-contract differences from lost delivery, bad matching or export
defects. Do not present removal of old local candidates as a proved speedup
or automatic evidence of no FN.

Expected savings are avoided constant propagation, explicit ZERO gating,
and once-only owned terminal publication. Their net effect remains a
measurement. The separate conductor run-4 infeasible-context join and
thingsboard run-2 nonterminal work are outside this change.

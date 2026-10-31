# Implementation proposal: constant filtering and Target-guided ZERO, version 2

Date: 31 October 2026. Status: implementation proposal. No runtime change.

The base specification is the final
[constant filtering and Target-guided ZERO proposal](bidirectional-constant-filter-target-zero-implementation-20261031.md).
Its SHA-256 is
`43fce6a3ff0adaac7361124dbe531ce2933e19437b743b22faf6d6c9b24a8a50`.
The selected amendment is
[exact initial facts on the DEMAND layer](../../spec/demand-layer-exact-initials.md),
with its [proof dossier](../../spec/demand-layer-exact-initials-proofs.md).
It supersedes the base specification's concrete MAY-to-EXACT rejection
and its unchanged run-1 origin-arm layer policy. The user selected concrete
marks only. FLOW keeps its existing behavior.

This document replaces the implementation instructions in the base document.
It repeats the selected contract, so implementation does not depend on
earlier drafts or discussion.

Follow [impl-proposal-guide.md](../../spec/impl-proposal-guide.md) and
[proof-guide.md](../../spec/proof-guide.md). Use the checked, constructive
models linked in section 15. Their scope and runtime adapter tests are
separate. No classical choice, proof hole, or new axiom is permitted.

Base runtime: `e090118e5f9603f1973c0578a3e04998035f4508`. The original
documentary head `3d8116a1a131a96f8423ef96d2b4a5d643dc46fc` added reports
and controls. The current worktree contains the partial implementation
described in the [validation report](../reports/bidirectional-target-zero-implementation-validation-20261031.md).
The validation report separates the earlier split-NORMAL counterexample
from the amended implementation results. This document states the
selected contract; the report tracks its runtime validation status.
No Gradle build, project analysis, or new performance measurement is made
for this proposal.

## 1. Selected contract and semantic scope

AP means access path. `$` is an exact position; `[any]` is an unresolved
MAY suffix; `[any-taint]` is a definite uniform MUST suffix. FLOW has an
abstract mark. T and U are full concrete marks. ZERO is control.

**The changes below affect analyzer semantics.** Keep them explicit in
the runtime PR and its tests.

| Part | Behavior replaced in this iteration | Selected behavior |
|---|---|---|
| Constant-base data | Can propagate, trigger callbacks, and enter records/demand | Drop before runtime effects in every direction/run |
| Concrete exact C2 admission | Rejects MAY after the earlier v2 correction | Matching same-prefix or ancestor MAY emits the requested exact key in DEMAND |
| Concrete initial layer | Initial key delivery can lose DEMAND | Carry the admitted layer through delivery and start; later exact NORMAL input can discharge old guidance |
| Initial deduplication | One membership per initial key | One membership per key and final starting layer |
| Unanswered demand | Empty emission skips current-call admission | Keep the no-op, including when every offer fails during the iteration |
| FULL TAINT | Latest narrow override preserves computed layer only for ZERO originals | Keep computed layer for ordinary ZERO and nonzero FULL; retain GROUP and independent static overrides |
| Weakened run-1 source/sink arm | A NORMAL cube can publish unary NORMAL arms after dropping another required origin | Publish DEMAND arms unless one origin plus ZERO retains a complete NORMAL binding |
| Sink observation | A local witness becomes a report candidate | A complete witness creates a typed terminal summary |
| NORMAL terminal | No current type | `NormalTarget(id)`; forward application requires complete NORMAL support |
| DEMAND terminal | No current type | Anonymous `DemandTarget`; paired C5 and handoff guide later ZERO |
| Backward actual GEN | Records its source occurrence | Also emits DemandTarget under its original premise |
| Backward source-summary result | Accepted nonzero-to-ZERO application dispatches AP REACH | Emit DemandTarget under complete caller original; balanced ZERO remains AP control |
| Restricted ZERO | Virtual/direct admission and a backward C5 exception | Explicit local demand admission and ordinary paired restriction |
| Final report | Local candidate replacement and confirmation flag | IDs reached by configured-root `ZERO -> NormalTarget(id)` |
| NORMAL terminal reuse | No current record kind | Persist full owned keys; ignore backward and skip settled ZERO replay |

The final rules are:

```text
Constant data or Constant premise member -> reject the whole runtime packet

demand p.[any]/T + submitted p.$/T,N     -> initial p.$/T,N
demand p.$/T     + submitted p.[any]/T,D -> initial p.$/T,D
demand p.f.$/T   + submitted p.[any]/T,D -> initial p.f.$/T,D
demand p.$/T     + submitted p.$/T,D     -> initial p.$/T,D
demand p.$/T     + submitted p.$/T,N     -> initial p.$/T,N
no satisfying offer in this iteration  -> no extra action

complete NORMAL sink binding with retained dependencies -> NormalTarget(reportId)
complete DEMAND sink binding -> DemandTarget
weakened run-1 source/sink arm -> DEMAND data / DemandTarget
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

Except for the explicit layer corrections in sections 1.2 and 4, the
source-summary dispatch in section 1.3, and the run-1 origin projection in
sections 4.6 and 5.1, keep ordinary AP
field transfer, mark semantics, exclusions, cleaner
semantics, aliases, native record matching, source permissions, static
pools and post-processing, predefined summaries, field limits, and the
selected call policy. Concrete C2 adds provisional exact admission and
retains its input layer. Do not change generic `inside`, `applicable`,
`overlap`, `satisfying`, or AP C5 exit intersection to implement it. C5
keeps the exact structural entry image and the raw result layer.

Run-1 still emits atomic executable origins. It has no ND edge. Later
FULL runs keep full same-call ND support. Do not add GroundingSupport,
IR changes, rejected-offer history, late no-demand subscriptions, copied
incoming demand, forced continuation, or backward NormalTarget lookup.

### 1.1 Reuse existing mechanisms

Use the existing implementation when it already performs the required
operation. Add the Target value or branch at its current owner. Do not
build a second implementation of that operation.

| Operation | Existing mechanism to use | Required addition |
|---|---|---|
| Complete sink condition | `RunMethodLocalServices.witness`, predicate and conjunction stores | Consume the complete binding as a Target |
| Initial admission and start dedup | `emitRestrictedInitials`, `InitialFactStore`, counted Start events | Explicit ZERO/Target demand, layered concrete admissions and two seen bits per key |
| Premise indexing and candidate selection | `PublicationIndex`, `CalleeSubscriptions`, their PathTrie lookups | Typed Target memberships under the same premise postings |
| Publication and replay | `SummaryStorage`, `SubscriptionManager`, `ProtocolSteps` | Typed Target payload and terminal result dispatch |
| Pending batch flush and failure | `RunMethodAnalyzer.flushPublications`, existing in-flight accounting | Include the Target batch in the same flush and completion checks |
| Complete same-call products | `KaryJoin` | A Target result key and immutable matched headers |
| Run-1 static premise resolution | `applyStaticSummary`, `applyStaticInput`, `Run1PointResume.callInterest`, `staticSupply`, PointReady | Carry Target through the same continuation and dispatch its terminal result |
| Backward sink seeds | Existing `Seed.Sink`, `Seed.PredicateSink`, `SeedIndex` and seed evaluator | Collect these values at complete DEMAND sink observation |
| Forward source seeds | Existing `HandOff.toForward` and `SourceHitStore` | No new conversion or seed type |
| Iteration completion | Existing runner join, driver barrier and stop decision | Include Target demand and commit the selected retained/report state |

The required new state is Target membership, retained NORMAL Target
records, stable report IDs, typed control demand, and two admission/result
lane memberships per existing key. These values use
the current actors, locks, queues and stores. There is no new static
service, scheduler, receipt service, or join engine. The Lean protocol
models state obligations on these existing operations; they do not
require runtime classes for each model operation or certificate.

### 1.2 Authorized FULL computed-layer correction

This explicit user-selected change supersedes the earlier ZERO-only
release. Ordinary FULL results keep the layer computed by AP transfer,
for both ZERO and nonzero originals. Remove the blanket TAINT-kind test
in FULL. Keep GROUP and the separately selected static approximation.

```kotlin
internal fun forceRun1Layer(premise: PremiseKey, value: Facts): Facts {
    if (!config.run1) return value
    return run1Layer(premise, ops.runtimeFact(value, mode))
}

private fun run1Layer(premise: PremiseKey, value: Facts): Facts =
    if ((value is TaintTree && mode.markMode == MarkMode.GROUP) ||
        value.base == STATIC || Run1StaticService.hasStaticMember(premise))
        value.withLayer(Layer.DEMAND)
    else value
```

Keep the intrinsic `initialFacts` table, field transfer, cleaners, CM checks,
cuts, summary matching and source permissions. Join the admitted concrete
layer at the actor's start boundary as specified in section 4. Existing
concrete EXACT/MUST initials intrinsically compute NORMAL. Concrete
STAR/MAY initials intrinsically compute DEMAND.
Run1Abstraction can produce an exact empty-path concrete initial, so a
nonzero run-1 FULL input can naturally be NORMAL. A computed DEMAND
result remains DEMAND; the override never promotes it.

Run-1 still waits for complete compatible conditions and emits unary arms.
The selected amendment now corrects their layers: an arm that drops a
required origin is DEMAND. Section 4.6 gives the factored support test.
`FullComputedLayer.NDArmRisk` remains a historical counterexample to the
uncorrected split-NORMAL implementation. Keep both its two-input positive
and one-input negative runtime controls. Do not add an ND support label
or an origin-product search to close this gap.

Use the existing `PersistentRecordStore.persist` for eligible NORMAL
singleton AP rows. `selectDemand` does not export the NORMAL forward
singleton as demand. Do not add another record store or guidance row.

```text
F1 FULL: ZERO -> ret.$/U, NORMAL -> existing native record
B2: ret.[any]/U -> existing reverse-record replay before C2
    empty current demand -> no initial, subscription or callee actor
F3: ZERO -> saved forward record -> ret.$/U, NORMAL
    empty current demand -> keep the saved result, skip current analysis
```

The backward read is not C2 emission. Preserve its existing matching,
uncertainty layer and caller support. Dispatch its accepted ZERO result
as specified in section 1.3. Record reads do not invoke actual GEN
callbacks. Forward native replay needs no new source permission.
If current concrete demand exists, C2 can now admit an exact DEMAND
initial from MAY. If it does not exist, saved replay alone remains enough;
no unanswered-demand action is added. GROUP and static-dependent results keep DEMAND. Ordinary
nonzero FULL results can now be NORMAL if AP transfer computes NORMAL.
Native eligibility and complete guard support remain separate checks.
A computed DEMAND producer still has no NORMAL native fallback. A saved
backward identity does not replace a missing forward producer.

The [FULL conditional-source regression](../reports/bidirectional-target-zero-nonzero-source-admission-gap-20261031.md)
reached and completed run-3 without its positive finding under the old
narrow policy. The broad computed-layer policy now completes run-3 with both the
required two-input report and an invalid one-input report. Its positive
is restored, and its negative control fails due to a NORMAL weakened arm. Do not keep the obsolete claim that every
nonzero FULL producer is DEMAND. The amendment must make the negative
control pass while preserving the positive finding. Its checked model
does so by run-3; this is not yet a new JVM result. Paired C5 exit matching
stays unchanged.

One existing cleanup adapter needs the new collector-fixed header cell.
Extend only NORMAL ZERO-origin TAINT whose leaves are all EXACT and
whose field exclusion is Empty. Preserve its spatial scalar/bulk
algorithm, selected-mark protection, block geometry and effect order:

```kotlin
internal fun fullCleanupCollectorFixed(premise: PremiseKey, facts: Facts): Boolean {
    if (facts is FlowTree && facts.exclusion != ExclusionSet.Empty) return false
    if (facts is TaintTree && (facts.exclusion != ExclusionSet.Empty ||
        facts.layer != Layer.DEMAND && (!premise.isZero || facts.root.hasAny))) return false
    if ((facts.base == STATIC || Run1StaticService.hasStaticMember(premise)) &&
        facts.layer != Layer.DEMAND) return false
    return true
}
```

This function is already used only by the selected FULL run-1 cleanup
schedule. NORMAL MUST/STAR inputs stay on the existing scalar fallback.
Their partial-cleaning callback image can include additional DEMAND
exact rows. Do not generalize the new header cell to them or to nonzero
NORMAL inputs. For the all-EXACT cell, each leaf is kept or removed; no
partial spatial split is needed. The existing protection upgrades must
still be the same for scalar and bulk execution.

The `FullComputedLayer` model proves the selected layer scope and the
initial-layer distinctions. `FullZeroSourceReplay` retains the historical
ZERO-only override and the unchanged exact
NORMAL source/native route, and the bounded cleanup extension. It does
not prove arbitrary AP geometry, all cleanup headers, or whole-project
no-FN. Runtime controls must check FULL/GROUP, ZERO/nonzero, static
current/origin, exact/MUST/cut layers, saved replay with empty demand,
and scalar/bulk exact-leaf protection.

### 1.3 Authorized backward source-summary result dispatch

After existing matching accepts a source-summary result, use one result
dispatch at `applyParts` and `applyRecordView`:

```kotlin
// Called only for an accepted, well-typed summary/record application.
if (!core.forward && !summaryPremise.isZero && result is Reach) {
    core.emitTarget(callerOriginal, DemandTarget)
} else {
    existingApResultDispatch(callerOriginal, result)
}
```

`summaryPremise` is the matched callee premise, including the transient
premise of a reversed record view. `callerOriginal` is the complete
existing caller premise. Existing K6/domain checks exclude an abstract
FLOW premise from this source-result case. Keep those checks; do not
add a FLOW Target branch.

Use the same dispatch for current summaries, same-direction backward
native records, and reversed forward native records. A balanced
`ZERO -> ZERO` summary stays AP control. Forward application and nonzero
AP results keep their existing dispatch. Do not modify micro-edge
transfer or the actual-GEN callback.

The converted result goes directly to existing terminal emission; it
does not resume the caller's call suffix. Keep exact ownership/dedup,
counted delivery, and paired C5. It creates no fake SourceHit or source
seed. Existing actual source/action occurrences remain separate.

```text
NORMAL saved source: ZERO -> ret.$/U
backward MAY offer:  ret.[any]/U, under caller original P
accepted native read result: ZERO
selected caller result:      P -> DemandTarget, DEMAND
current C2 remains empty:    no exact initial and no new callee actor
```

This example assumes empty current demand. With a matching concrete
exact guide, the new C2 cell can also start the callee in DEMAND.

The `SourceSummaryCompletion` model proves this dispatch after accepted
matching, original preservation, balanced-ZERO control, no fabricated
source hit, and native replay before the unchanged demand gate. Runtime
matching, complete premise kind checks and terminal delivery remain
adapter obligations. No blanket caller-terminal C5 permission is added.

### 1.4 Authorized run-1 static Target completion

This corrects a missing run-1-to-run-2 guidance route. It keeps paired C5.
The completed virtual relation `ZERO -> DemandTarget` projects to one
`(Target,ZERO)` row. It does not change the C5 table or permit a Target
through separate reader-entry and writer-exit rows.

Extend the existing frozen static completion with terminal reader seeds.
Use a typed endpoint, not a fake Pattern, base, mark or report ID:

```kotlin
// Inside the existing FrozenStaticCompletion, separate from AP endpoints:
private val terminalReaders: Map<MethodKey, List<Pattern>>

// Existing view: the default keeps old small reference adapters valid.
interface StaticDemandView {
    fun targetInputs(): Sequence<Pattern> = emptySequence()
}

// During completeJoinedStaticGuidance, before builder.build() and release:
for (actor in actors) for (row in actor.outgoingTargets) {
    check(row.target == DemandTarget)
    val initial = checkNotNull(row.premise as? InitialAp) // run-1 has no ND
    builder.addTarget(actor.key, initial.toPattern())
}
```

`addTarget` filters unsupported/nonstatic initials with the current
static-anchor test. Keep the exact MethodKey and canonical input
descriptor. Keep it as a
typed extension of the frozen builder; it stores no live actor, fact or
subscription. The synthetic handoff fallback freezes the same readers
before build. NormalTarget contributes no reader seed.

Reuse the current lookup stages and owner-visibility code:

```text
local complete rows
  then own W/B/R composition
  then visible inherited B composition, only if needed

W: P -> C.f
B*: C.f -> ... -> C.g      // each middle uses current AP/mark join
R: C.g -> DemandTarget    // typed terminal endpoint
result: P -> DemandTarget
project: (Dc=Target, Dp=P), using typed Zero if P is ZERO
```

Static B ownership and label selection remain unchanged. W and R stay
exact-context local. A query can start at a static vertex without W.
FLOW preserves the selected mark; mapped labels require a compatible
middle mark. Carry the reader's required FULL/GROUP input selector
backward without giving Target an output selector. The finite Lean
reference expands group selectors over known full marks; runtime lookup
can keep the existing selector indexes.

`StaticPairLookup.walkTargetOrigins` starts at `view.targetInputs()`.
It follows the same compatible incoming W/B relations, uses the existing
`composeMarks`, `staticAnchor` and `overlap`, and reports the actual
source Pattern. A terminal mark relation has a typed missing output
selector. This is not a runtime AP ZERO or a fake mark. Keep visited
states per lookup view; restart them for inherited lookup so a local
negative answer cannot hide an inherited bridge.

`DemandStore.visitControlPairs` shares row lookup across all control
clients. It first visits explicit local rows. If not covered and a
run-2 completion exists, it asks local virtual lookup, then inherited
virtual lookup. Convert each complete source endpoint once:

```kotlin
// Origin callback from walkTargetOrigins, not a published runtime edge:
val exit = if (origin.fact.base == AccessPathBase.Zero) DemandExit.Zero
    else DemandExit.Data(origin)
visit(PairedDemand(DemandEntry.Target, exit))
```

C2 and C5 use this same complete derived control row:

```text
initials(M, actual ZERO):
  use a local Zero/Target entry, or a witnessed run-2 Target-entry pair

intersect(M, original ZERO, raw AP):
  derive (Target, Data(exit)), then use existing AP exit restriction

acceptsTarget(M, original ZERO):
  derive (Target, Zero), then apply the unchanged paired Target C5
```

No Target has an initial or AP trie entry. No Zero or Target is a static
middle. No lookup emits an executable summary, source hit, new source
permission or copied runtime Target. A covered query stops through the
existing coverage check. Only run-2 carries this frozen completion;
run-3 and later use local demand.

`StaticTargetClosure` extends the existing static factorization model.
It constructively translates eager derivations to factored paths and
back, and preserves actual source/target seed witnesses. Direct W/R and
multibridge inherited examples give a paired `(Target,ZERO)` guide that
passes ordinary C5. NormalTarget seeds are absent. The model does not
solve complete FULL conditional-source and caller-context correctness. GROUP
mode remains available with recorded issues; acceptance currently focuses
on FULL mode.

### 1.5 Read-only ZERO-exit probe for terminal C5

The implementation of section 1.4 must also retain ordinary AP virtual
rows whose paired exit is ZERO. For example, the existing composition
`ZERO -> C.f/T ; C.f/FLOW -> ret/FLOW` supplies `(ret/T,ZERO)` to the
backward getter or returning wrapper. Its source-completion terminal
has original `ret/T`. That original passes the entry; Target passes the
ZERO exit. A control-only scan misses this valid row.

Reuse the full existing C5 query:

```kotlin
fun acceptsTarget(method: MethodKey, original: PremiseKey,
                  policy: RestrictedInitialPolicy): Boolean =
    intersect(method, original, Reach.DEMAND, policy).isNotEmpty()
```

This is a query-only ZERO exit probe. It does not encode Target as an AP
fact, publish Reach, start a method, execute a rule, or create a source
hit. Use the real original and the same policy. `intersect` already
checks runtime domain, explicit controls, AP rows, own static closure
and inherited static closure. It also reuses the typed terminal pairs
from section 1.4. Each successful result comes from one complete pair.
No new recursive path is added: `intersect` does not call `acceptsTarget`.

`c5_target_equals_zero_probe` proves the per-pair equality for all paired
exit kinds and any owner/original. `any_target_equals_any_zero_probe`
lifts it to a row collection. ZERO exits accept both conclusions; AP
exits accept neither. Owner and entry checks stay identical. This is an
adapter correction, not a new demand or C5 policy. NormalTarget keeps
its existing separate forward lane. The FULL conditional-source C2
regression remains open.

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

typealias TargetBatch = List<TargetSummary>
```

Freeze a detached Target batch with the existing immutable-list
convention before publishing or posting it. No batch wrapper is needed.

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
| Raw Target set | Existing method actor; one run | Exact raw terminal memberships |
| Pending Target batches | Same actor | Accepted publications which still require a send |
| Target memberships in PublicationIndex | Existing SummaryStorage lock; one run | Published premise/Target pairs using the existing premise-member postings |
| Existing CalleeSubscriptions | Caller runner; one run | Only offers admitted by the selected call policy |
| Target ND joins | Caller service; one run | Header bindings for known full terminal premises at one call |
| Existing Run1PointResume call continuations | Same actor; one run | Existing static-interest IDs; the result payload can also be Target |
| NormalTargetView | Immutable run input | Persisted full owned NORMAL keys; forward conditional replay |
| Sink seed set | Existing method actor; one run | Existing Seed values for complete DEMAND sink observations |
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

Keep `RestrictedInitialPolicy.emit` as the pure structural emitter. Replace
the concrete EXACT/ANY rejection with the new directed exact cell. Keep
the old FLOW cell:

```kotlin
if (demand.fact.tail == Tail.EXACT && demand.fact.mark is MarkSlot.Concrete &&
    demand.exclusion != ExclusionSet.Empty) return null
val d = normalizeDemandFieldExclusion(demand)
if (d.fact.base != actual.fact.base || !markSub(d.fact.mark, actual.fact.mark, catalog)) return null
if (!fitsBudget(d) || !fitsBudget(actual)) return null
if (d.fact.tail == Tail.EXACT && actual.fact.tail == Tail.ANY &&
    d.fact.mark is MarkSlot.Star) return null // FLOW policy is unchanged
// Continue with the existing path/tail cells.
```

Use `== Tail.ANY`, not `isAny`: the latter also includes MUST. Apply this
in both restricted directions. For an exact concrete demand, reject a
nonempty demand exclusion before demand normalization. Keep actual
exclusions and the static anchor/budget checks. MAY admits the requested
point only when its path is equal to, or an ancestor of, that point.
Apply the same invalid exact/E rejection to `canEmitInitial` and
`canStoreInitial`. Do not let their normalization accept an illegal key.

| Demand | Submitted | Result, with existing base/mark/budget guards |
|---|---|---|
| `p.[any]/T` | `p.$/T` | `p.$/T` |
| `p.$/T` | `p.[any]/T, D` | `p.$/T, D` |
| `p.f.$/T` | `p.[any]/T, D` | `p.f.$/T, D` |
| `p.$/T` | `p.$/T, D` | `p.$/T, D` |
| `p.$/T` | `p.$/T, N` | `p.$/T, N` |
| `p.f.$/T` | `p.[any-taint]/T` | existing exact result if E admits f |
| `p.$/T` | `p.f.$/T` or `p.f.[any]/T` | none |
| `p.$/U` | T, U different from T | none |

Keep STAR and other ANY-demand cells. `canEmitInitial`/`canStoreInitial`
describe the structural image: an exact actual can still witness an exact
initial in either layer. Keep that valid shape and C5's raw result layer.
The new MAY route adds an actual-input witness, not a new structural key.
A generic geometric meet is not C2 permission.

`InitialDemandResults.offer`, `has`, and `requireFamily` use the same
geometry and canonical admission layer. A pair which cannot emit
contributes no required family. Do not record it as unanswered work.

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
fun controlInitials(method: MethodKey, actual: Facts): Set<AdmittedInitial> {
    if (actual !is Reach) return emptySet()
    var admitted = false
    visitControlPairs(method, policy) { pair ->
        admitted = pair.entry == DemandEntry.Zero || pair.entry == DemandEntry.Target
        !admitted
    }
    return if (admitted) setOf(existingZeroAdmission(ap.zero)) else emptySet()
}
```

The ordinary entry index and existing run-2 static completion keep their
current lookup. For actual ZERO, `visitControlPairs` checks explicit local
rows, then the run-2 witnessed terminal rows in section 1.4 if needed.
Later it visits local rows only. Remove
the virtual `zeroDemand` permission. Do not turn a nonzero actual into ZERO.

### 4.3 Starts and no-op behavior

```kotlin
fun startRoot(root: MethodKey) {
    val seeds = if (config.run1) setOf(existingZeroAdmission(ap.zero))
        else config.demand.initials(root, Reach.NORMAL, config.admissionPolicy)
    if (seeds.isEmpty()) return
    val actor = port.analyzer(root)
    for (seed in seeds) actor.addInitial(seed)
}

fun admitCurrentCall(part: Subscription) {
    val seeds = emitRestrictedInitials(config, ops, part.callee, part.added)
    if (seeds.isEmpty()) return
    port.subscribe(part) // registration precedes replay and any same-unit start
    port.startInitials(part.callee, seeds)
}
```

The existing counted Start event executes this receiver-side helper.
Do not create the actor before an empty query or apply a second lookup.
InitialFactStore starts each canonical `(key, layer)` once. Section 4.5
specifies its two memberships.
Delete unconditional backward `ZeroIn/addZeroEntry`. Backward ZERO calls
use the explicit query/subscribe/start arm in section 8.4, with
`zeroOnly=true` only for canonical caller ZERO. Preserve the
current early return for nonzero-original backward REACH: it is not
discovery ZERO. Keep ZERO's ordinary CFG pass-through and zeroCanReturn.

An empty emission creates no current subscription, initial packet,
Target, seed, retry, demand copy, or forced iteration. An all-unsatisfied
iteration needs no special completion action. Saved replay already done
before this gate retains its legitimate results.

### 4.4 Layered delivery without a new premise type

Add one immutable command value in `ap`. Keep Layer outside InitialAp:

```kotlin
data class AdmittedInitial(val initial: InitialAp, val layer: Layer)
data class InitialEmission(val pattern: Pattern, val layer: Layer)

// Pseudocode: join is the existing NORMAL/DEMAND disjunction.
fun admissionLayer(emitted: Pattern, actual: Pattern, supplied: Layer): Layer {
    val intrinsic = existingIntrinsicLayer(emitted)
    if (isCanonicalZero(emitted)) return intrinsic // existing ZERO policy
    if (emitted.fact.mark is MarkSlot.Star) return intrinsic // FLOW unchanged
    val loss = if (emitted.fact.tail == EXACT && actual.fact.tail == ANY) DEMAND else NORMAL
    return join(intrinsic, supplied, loss)
}
```

The demand row's old layer is not an operand. An exact NORMAL actual can
start NORMAL even if the guide came from a DEMAND edge. Demand rows are
permissions for the next analysis, not permanent approximation labels.

`RestrictedInitialPolicy.emitAdmission` returns a transient InitialEmission
without interning an AP. `InitialDemandResults` uses this value for its
emitted and missing sets. Its offered pairs include the actual layer, or
the accumulator fixes that layer for the whole query. Reuse its current
structural emitter and coverage algorithm:

```kotlin
fun offer(entry: Pattern, actual: Pattern, actualLayer: Layer) {
    val pattern = policy.emit(entry, actual) ?: return
    val layer = admissionLayer(pattern, actual, actualLayer)
    val emission = InitialEmission(pattern, layer)
    if (emitted.add(emission))
        admitted.add(AdmittedInitial(ap.initial(pattern), layer))
    missing.remove(emission)
}
// has and requireFamily compute the same transient emission, with no AP interning.
```

Carry `Collection<AdmittedInitial>` through all these existing boundaries:

```text
DemandStore.initials -> emitRestrictedInitials -> caller startInitials
InitialsIn -> runner handler -> RunMethodAnalyzer.addInitial
forEachConcreteAnswer -> Run1Abstraction.answer
SubscriptionManager answer accumulator -> InitialAnswersIn -> addInitial
```

`forEachConcreteAnswer` attaches the concrete input layer to its answer.
Keep its current EXACT/STAR shape policy. An exact DEMAND answer cannot
start NORMAL. Keep the abstract run-1 STAR/FLOW schema seed unchanged.
ZERO uses `existingZeroAdmission`: its current permission and starting
policy are separate from data coercion. No data descriptor creates ZERO.

Keep the caller's actual Facts in its Subscription. Do not replace MAY
input by the canonical exact hypothesis. Saved replay still occurs before
the C2 query. Existing selected-input, caller and link layers govern
summary application. Legal MAY offers already have DEMAND layer.

### 4.5 Canonical start and two membership bits

Use the existing intrinsic fact constructor and run-1 mode/static policy
before entry deduplication. Do not change the intrinsic table:

```kotlin
fun addInitial(offered: AdmittedInitial) {
    val intrinsic = ops.startFact(offered.initial, mode)
    val started = forceRun1Layer(offered.initial,
        intrinsic.withLayer(join(intrinsic.layer, offered.layer)))
    val canonical = AdmittedInitial(offered.initial, started.layer)
    if (!initials.add(canonical)) return
    emitAtEntry(offered.initial, started) // existing entry/CFG delivery
}

class InitialFactStore {
    private val seen = HashMap<InitialAp, Int>()
    fun add(seed: AdmittedInitial): Boolean {
        if (!RuntimeDataDomain.initial(seed.initial)) return false
        val bit = if (seed.layer == NORMAL) 1 else 2
        val old = seen[seed.initial] ?: 0
        if (old and bit != 0) return false
        seen[seed.initial] = old or bit
        return true
    }
}
```

Canonicalize before query coverage and before actor admission. In
particular, supplied STAR/N and STAR/D both start as D and count once.
Do not add a fictitious NORMAL lane for static/GROUP initials which the
selected run-1 policy always demotes. Applying the same canonicalization
at both boundaries is idempotent and does not perform a second lookup.

For an exact key, both `D -> N` and `N -> D` arrival orders start two
jobs. Same-layer repeats start none. NORMAL cannot suppress DEMAND:
`check(p) { sinkT(p); }` can need a DemandTarget for a MAY caller after a
NORMAL caller already created NormalTarget. Existing edge storage keeps
post-statement N/D deduplication. Do not change InitialAp equality, ND
member identity, or report identity.

### 4.6 Factored run-1 source projection

Keep complete predicate/header matching and the current factored origin
domains. The rule owner computes the output arm's layer. MethodEdgeStore
does not inspect support and receives no GroundingSupport label.

For one complete compatible proof/header partition:

```kotlin
fun armLayer(origin: InitialAp, cubeLayer: Layer,
             columns: Collection<OriginDomain>): Layer {
    if (cubeLayer == DEMAND) return DEMAND
    val complete = columns.all { column ->
        column.contains(origin) || column.contains(ap.zero)
    }
    return if (complete) NORMAL else DEMAND
}

// Only after a complete condition is available:
for (origin in existingOriginUnion) {
    if (origin.isZero) continue
    val layer = armLayer(origin, completeHeaderLayer, columns)
    emitArm(origin, layer, existingProtection(origin))
}
if (columns.all { it.contains(ap.zero) })
    emitArm(ap.zero, completeHeaderLayer, existingZeroProtection())
```

The union must contain the origin. Do not invent an arm merely because
every column has ZERO. A partial condition produces no arm. Compatibility
partitions and repeated canonical-leaf intersections stay unchanged.
Source rules with one retained origin plus ZERO can stay NORMAL. Two
distinct necessary origins produce separate DEMAND arms. Later forward
runs retain their existing full ND premise and same-call binding.

Extend `ReadyCube.emitProtectedOrigins` to provide `(InitialAp, Layer,
Boolean)`. Its result membership is `(action, origin, outputLayer)` with
the existing monotone protection bit. A later complete NORMAL arm must
not be hidden by a prior DEMAND arm with the same action and origin.
Apply the same rule to `Run1OriginConjunctionStore`.

An update can make a previously emitted D origin complete in N. Retest
affected origins when domains grow. Keep the existing incremental scan:

```kotlin
when {
    !consecutiveVersion || protectionGrew || ap.zero in addedOrigins -> revisitAllOrigins()
    else -> for (origin in addedOrigins) offer(origin)
}
```

A new nonzero P can change only P's membership test. A new ZERO can
change that test for every existing origin. Thus ZERO growth must revisit
the current union. Header changes use their separate existing partitions.
Keep per-lane result deduplication and do not enumerate origin tuples.

### 4.7 C5 and concrete exact demand storage

Keep concrete exact DEMAND summaries legal through summary admission,
paired intersection, handoff, and the next C2 query. They are not NORMAL
native records. Keep exact field exclusion empty. Do not normalize their
`$` into STAR or MAY as a new behavior.

For each accepted C5 exact entry `(I,L)`, the constructive C2 witness is
the exact actual at I with layer L. Thus the structural image stays the
same. C5 preserves the raw output layer and uses the existing paired
exit test. The new MAY-to-EXACT route supplies an additional D witness;
it does not grant a fallback entry permission or broaden AP exit matching.

### 4.8 Target safety and convergence limit

A dependent D chain stays D. Its sink produces DemandTarget and its full
physical seed. It cannot produce NormalTarget. A cached NormalTarget
rejects D caller support; do not downgrade it to an anonymous target.
Admission itself creates no source permission. Only real reverse actions
and existing native replay perform their respective source operations.

The intrinsic-MAY counterexample remains provisional at every field
limit. It can repeat DemandTarget and the same frontier indefinitely.
Keep existing time/iteration policy; do not stop on equal counts or
promote a provisional result. The fixed finite entry universe admits at
most two canonical start jobs per key in one run. This local bound does
not prove convergence across runs.

## 5. Local terminal producers

### 5.1 Complete sinks

Keep the existing predicate/condition evaluator and all mark requests.
Use its existing `witness(core, sink, node, edges, proof)` callback.
`edges` is the existing complete `List<SinkEdge>`; no new binding type
or condition evaluator is needed. Replace the local report insertion:

```kotlin
// In the existing completed witness callback:
if (edges.any { !runtimePacket(it.premise, checkNotNull(it.facts)) }) return
val origins = edges.map { it.premise }.distinct()
val cubeLayer = if (edges.any { it.layer == DEMAND }) DEMAND else NORMAL
fun emitSinkArm(p: PremiseKey, layer: Layer) {
    val target = if (layer == NORMAL) {
        NormalTarget(catalog.intern(SinkKey(key.method, node, sink.rule.id), sink.rule, key))
    } else {
        sinkSeeds.addAll(sinkSeedsFor(sink, key, node)) // full physical predicate
        DemandTarget
    }
    emitTarget(p, target)
}
if (config.run1) {
    val nonzero = origins.filterNot { it.isZero }
    for (p in nonzero.ifEmpty { listOf(ap.zero) }) {
        val keptWholeBinding = origins.all { it.isZero || it == p }
        emitSinkArm(p, if (keptWholeBinding) cubeLayer else DEMAND)
    }
} else {
    var original: PremiseKey = ap.zero
    for (p in origins) original = ap.union(original, p)
    emitSinkArm(original, cubeLayer)
}
```

Use the existing full compatible binding and aggregate layer. A partial
cube, one literal, or a request is not a sink witness. In run-1, retain
the current full-binding/all-ZERO test and atomic nonzero-origin emission.
Never project a later ND premise to independently sufficient members.
`ap.union` uses the current ZERO-drop/full-premise rules. Predicate and
conjunction stores keep their existing complete-binding enumeration.
The TRUE/unconditional callback includes the existing ZERO/REACH input.

This callback sees a concrete complete witness. Classify its arms from
that witness. Do not compute NormalTarget once from the cube and then
reuse it for weakened arms. Source output uses the equivalent factored
test in section 4.6. Both owners preserve each arm's result layer and its
full seed. No field-sensitive writer validation is added.

Capture each DEMAND sink's existing Seed values before anonymous Target
dedup. Two sinks can share one DemandTarget membership and still need
different backward seeds. A NORMAL sink creates no backward seed.
Install the consumer at all existing completed witness call sites,
including local sinks and exceptional boundary checks. Keep the
transient binding/proof inputs used by the current condition checks.
`trackFactsReachAnalysisEnd` stays ignored; Target does not restore the
old sink end-action GEN outputs.

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
they create no terminal merely because they assign a mark. Summary and
record application does not invoke this actual-GEN callback or create
its source hit. Its accepted backward nonzero-to-ZERO result instead
uses the source-summary Target dispatch in section 1.3.

Do not use `SourceHitStore.add`'s fresh Boolean as Target permission. The
same source/action can be hit under several original premises.

## 6. Owned terminal emission and C5

### 6.1 Method-owned raw and pending state

Add raw Target membership to the existing method actor as an ordinary
set. It needs no store wrapper:

```kotlin
private val rawTargets = LinkedHashSet<TargetSummary>()

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
    intersect(method, original, Reach.DEMAND, policy).isNotEmpty()
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

Extend the existing run-2 static completion with the typed terminal
reader lookup from section 1.4. The read-only ZERO-exit probe in section
1.5 tests derived control and ordinary AP pairs through the same complete
C5 query. AP endpoints retain their existing lookup and restriction.
Later snapshots have no static completion.

## 7. Terminal publication and delivery

### 7.1 Typed payload in the existing delivery protocol

Keep existing AP publication equality. Add only its typed Target payload
and dispatch:

```kotlin
interface TargetPublicationSink {
    fun publishTargets(method: MethodKey, batch: TargetBatch)
}
interface TargetApplier {
    fun applyTarget(part: Subscription, row: TargetSummary, member: Int)
    fun applyStaticTarget(part: Subscription, row: TargetSummary, member: Int)
}
class TargetDelivery(val callee: MethodKey, val rows: TargetBatch) : RunEvent
```

Wire the TargetPublicationSink adapter beside the existing PublicationSink
in RunMethodHandlers. It calls the same method's SummaryStorage. Keep
PublicationSink's existing AP function interface. Use the existing
RunnerPort/SubscriptionPort, RunEvent dispatch, ProtocolSteps, queue
priority and in-flight counter for TargetDelivery. A typed event does
not require another scheduler or publication service.

Have MethodCallServices also implement TargetApplier. The actor delegates
through that existing injected interface, as for AP summaries. Extend
decorators and fixtures for the required methods. Static supply uses
the existing `staticSupply` callback with a typed result payload, as
specified in section 9.

### 7.2 Existing index, lock, subscriptions and replay

Extend PublicationIndex with a map from full premise to exact Target
constructors. Reuse its current `indexed` and `byMember` premise postings;
do not create a second TargetPublicationIndex or a second premise trie.
Extract the existing premise insertion and candidate selection bodies
into local helpers so AP and Target readers call the same code. Keep
the prefix/extension rules unchanged. Target-only premises return no AP
publication; AP-only premises return no Target row.

Reuse SummaryStorage's existing lock, subscribers and publish procedure:

```kotlin
// Target counterpart of SummaryStorage.publish, using the same fields:
val (delta, recipients) = synchronized(lock) {
    published.addTargets(batch) to subscribers.toList()
}
// Use the existing steps.notify and required-post handling for delta.
```

`notifyTargets` is a typed post through the existing protocol. On receipt,
SubscriptionManager uses its existing CalleeSubscriptions and candidate
selection to dispatch the Target result on the caller runner. Extract
the premise-only lookup from its current AP entry point. Keep ownership
and snapshot timing unchanged.

Use SubscriptionManager.subscribe's existing register, admit and replay
sequence. Include typed Target rows in the replay. Keep the existing
register-before-replay/start order and output deduplication. The run-1
static-control arm also uses the existing procedure in section 9.

### 7.3 Existing pending-batch flush and failure handling

Use `RunMethodAnalyzer.flushPublications`' current detach, immutable batch,
publish and restore-on-exception procedure for pending Target rows. Add
the Target batch to that existing flush service opportunity and to the
actor's existing work/freeze checks. There is no separate retry queue,
receipt registry, or durable outbox service.

A duplicate seen membership must not erase a pending send. Keep the
existing required-post failure/cancellation path: a rejected send fails
the run, and an incomplete run cannot commit new retained/report state.
The Lean pending/receipt model describes these obligations on the
existing actor queues and in-flight accounting.

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

Use the existing `KaryJoin` directly. Only its result key and matched
header are new. `NdSummaryJoin`'s growing TAINT-conclusion archive is
not needed for an immutable terminal result.

```kotlin
data class TargetJoinKey(
    val callee: MethodKey, val premise: PremiseKey, val target: Target,
    val call: CommonInst, val stageOrdinal: Int, val saved: Boolean,
)
data class TargetBinding(val ref: CallerRef, val layer: Layer)

private val targetJoins = HashMap<TargetJoinKey, KaryJoin<TargetBinding>>()

fun targetJoin(part: Subscription, row: TargetSummary,
               saved: Boolean): KaryJoin<TargetBinding> {
    val key = TargetJoinKey(part.callee, row.premise, row.target,
        part.ref.call, part.ref.stageOrdinal, saved)
    return targetJoins.getOrPut(key) {
        KaryJoin(row.premise.size, ap.cancellation)
    }
}
```

The caller service is one method owner, and the key fixes callee, call,
stage, full premise, result constructor/id and read lane. All required
slots must be present. Union original caller premises only after this
complete join. Do not pool different calls or reduce the arity.

Payloads are immutable. A new ID uses a new exact join key and is replayed
against current eligible member inputs. A new member creates new complete
tuples through the existing KaryJoin. No TargetCallJoin wrapper or new
product algorithm is needed. Retained ND replay stores only matched
headers for known records, not all rejected input facts.

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
callee receives layered admitted initials and performs no second query.

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

## 9. Reuse run-1 static summary delivery

Use the existing run-1 static-summary procedure for `S.C.f -> Target`,
as for `S.C.f ->` an AP conclusion. Static premise resolution is unchanged.

| Step | Existing code to use |
|---|---|
| Find static rows for a ZERO/REACH call port | `SubscriptionManager.isStaticControl`, PublicationIndex's static premise postings, `CalleeSubscriptions.staticControlCandidates` |
| Resolve an already known concrete static input | `RunMethodCallServices.applyStaticSummary`, `hasKnownStaticGroupInput`, `knownStaticInput` |
| Wait for a later pool supply | `Run1PointResume.callInterest`, its existing call directory, waiting mark set and resume-ID allocator |
| Receive the supply | Existing PointReady dispatch, actor forwarding, and `MethodCallServices.staticSupply` |
| Match and select the caller original | `RunMethodCallServices.applyStaticInput`, including its exact class-marker check, field anchor and `forceRun1Layer` |

Extend the existing static call continuation's result payload to include
a typed TargetSummary. Keep the same directory, waiting-set updates,
PointReady path and service owner. Its semantic key must distinguish
the AP result from the terminal result and include the exact Target
constructor/ID. Keep all current callee, caller, call, stage, full-premise
and member key fields. Existing AP keys keep their current equality.
The payload wrapper itself is not the key. AP results keep the current
per-leaf Pattern/layer key and its existing protection-upgrade behavior.

```kotlin
// Payload of the existing static call continuation:
sealed interface StaticCallResult {
    data class Ap(val publication: Publication) : StaticCallResult
    data class Terminal(val summary: TargetSummary) : StaticCallResult
}

// At the existing applyStaticInput completion point, after the common
// matcher constructs the subscription with its selected STATIC original:
when (result) {
    is StaticCallResult.Ap -> applyExistingApResult(selectedInput, result.publication, member)
    is StaticCallResult.Terminal -> applyTarget(selectedInput, result.summary, member, saved = false)
}
```

`applyExistingApResult` names the current AP application/continuation
body at this point; it is unchanged. `selectedInput` is the existing
Subscription after static original/input selection. The new code is
the typed result branch, not a new resolver. `applyStaticTarget` enters
this shared procedure. Extend `callInterest` and the existing
`staticSupply` payload type to carry either result; add no separate
staticTargetSupply callback or terminal waiting directory. Keep AP leaf
splitting and protection upgrades in their existing AP branch.

For a terminal result, retain the selected STATIC original and emit the
caller's Target summary directly. All run-1 static support remains
DEMAND. Preserve late-supply wakeup, known-input activation, class
markers, and disableRun1Statics. No method-entry static propagation or
static write registration is added. Targets remain outside AP Patterns.
Anonymous terminal reader endpoints enter frozen static completion as
specified in section 1.4.

The existing K6 and held REACH/TAINT producer checks imply that Target
premise members are ZERO or concrete non-FLOW values. Use that existing
invariant; no abstract FLOW Target branch is needed.

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
NormalTarget is never exported as refinement demand. At the completed
run-1 barrier, freeze outgoing static-premise DemandTarget readers before
actor release and builder finalization, as in section 1.4.

### 11.2 Seeds independent of reports and Target deltas

Reuse the existing `Seed.Sink`, `Seed.PredicateSink`, `SeedIndex`, and
seed evaluator. Store their existing Seed values in the actor's sink
seed set. No SinkSeedDescriptor wrapper or new seed store class is
needed. Capture each complete local DEMAND sink observation before
Target dedup.

Extract the current sink-to-seed conversion from `HandOff.toBackward`
without changing it, and call it at that observation point:

```kotlin
fun sinkSeedsFor(sink: SinkRule, method: MethodKey,
                  at: CommonInst): List<Seed> = when {
    sink.predicate != null && !sink.unconditional ->
        listOf(Seed.PredicateSink(checkNotNull(sink.occurrenceId), method, at))
    sink.predicate != null -> emptyList() // existing unconditional predicate rule
    else -> sink.seedPatterns().map { Seed.Sink(sink.rule, method, at, it) }
}

fun toBackwardSeeds(result: CompleteForwardRun): SeedIndex =
    SeedIndex.of(result.actors.flatMap { it.sinkSeeds })
```

Use `HandOff.toForward`'s current SourceHitStore-to-Seed.Source conversion
unchanged. Resolve predicate handles at the reached seed statement with
the current DirectedForms/seed evaluator. Constant-domain checks still
apply at their selected boundaries.

The actor retains its seed set and raw Target rows through the existing
driver barrier. No final report entry is used to build seeds. A saved
Seed does not start its method; admitted ZERO must reach its statement.
NORMAL Target replay creates no sink seed. Existing source/action
identity and conditional source permission remain unchanged.

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

### 13.3 Directed layered admission and unanswered iteration

```text
Dc=p.[any]/T, actual=p.$/T,N -> p.$/T,N initial
Dc=p.$/T, actual=p.[any]/T,D -> p.$/T,D initial
Dc=p.f.$/T, actual=p.[any]/T,D -> p.f.$/T,D initial
Dc=p.$/T, actual=p.$/T,D -> p.$/T,D initial
Dc=p.$/T, actual=p.$/T,N -> p.$/T,N initial, even after D guidance
Dc=p.$/T, actual=p.f.[any]/T,D -> no initial
Dc=p.$/U, actual=p.[any]/T,D, T!=U -> no initial
every offer fails Dc -> no completion action for that demand
```

Saved replay still precedes the current gate. It is not rolled back.
There is no blocked-demand store or fallback Target.

### 13.3.1 Conditional producer and Target control

```java
// sourceA assigns T1; sourceB assigns T2.
// make: CM(p,T1) AND CM(q,T2) -> assign U at ret.$.
// sinkU: CM(value,U).
void main() {
    Object a = sourceA(), b = sourceB();
    Object r = make(a,b);
    Box z = new Box(); z.g = r;
    Box y = new Box(); y.f = z;
    Object bad = make(a,new Object());
    sinkU(y.f.g); // positive
    sinkU(bad);   // negative
}
```

```text
run-1, forward, limit 1:
  complete make witness: {p/T1,q/T2}, N
  summaries: p/T1 -> ret.$/U,D; q/T2 -> ret.$/U,D
  good cut result and bad provisional result -> DemandTarget, never NT

run-2, backward, limit 1:
  good physical sink seed is cut to ret.[any]/U,D
  exact return demand admits ret.$/U,D; the reverse rule runs
  bad uncut physical sink seed can admit ret.$/U,N
  both start lanes run; actual reverse actions keep source permissions

run-3, forward, limit 2:
  actual exact N inputs can start N despite prior D guidance
  complete ND relation binds only the good call -> NormalTarget(good)
  bad call lacks T2 -> no U and no NormalTarget(bad)
```

The checked model reaches the good report by run-3. It does not prove a
global stop at run-3. Use the same positive/negative runtime test. Also
test a direct joint sink with two crossed incomplete callers; its run-1
arms must be DemandTarget and retain the full physical predicate seed.

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
raw Target has one membership; the existing Seed values retain A and B
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
| RestrictedInitialPolicy | Concrete exact MAY admission, transient InitialEmission layer; unchanged FLOW and structural C5 image |
| new AdmittedInitial, InitialFacts | Immutable layer-bearing command, canonical two-bit entry membership; unchanged InitialAp identity |
| DemandResultCoverage, StaticEntryLookup, RestrictedInitialEmission | Layer-aware result/missing memberships, caller-owned query result, no hypothetical AP interning |
| FormApplier, FactAlgebra, EngineAlgebra | Typed AcceptedSource context, constant guards before hooks |
| RunMethodLocalServices | Per-origin source layer, per-origin sink Target, full local seed set, preserved condition checks |
| Run1OriginPredicateStore, Run1OriginConjunctionStore | Complete-support arm layer, per-layer result/protection membership, ZERO-growth candidate rescan; no origin tuples |
| RunMethodAnalyzer | Raw/pending Target store, C5 branch, explicit root ZERO lookup and work checks; ordinary FULL computed-layer policy and canonical layered starts |
| PublicationIndex | Typed terminal memberships; shared existing premise postings and candidate lookup |
| SummaryStorage, SubscriptionManager, CalleeSubscriptions | Typed replay/delivery using existing subscription ownership |
| RunEvent, RunnerPort, SubscriptionPort, UnitRunner, handlers | Immutable counted TargetDelivery and layered initial commands, required-send failure handling |
| MethodServices, RunMethodCallServices | Typed terminal dispatch and existing static-supply payload, KaryJoin use, saved replay, guided backward ZERO; bounded NORMAL ZERO all-EXACT cleanup header |
| Run1PointResume | Extend the existing call continuation's result payload; keep its directory and pool-reply procedure |
| Run1RequestMatching, Run1Abstraction, SubscriptionManager answers | Preserve exact concrete supplier layer in answer batches; abstract schema seed unchanged |
| new NormalTargetStore and ReportCatalog | Exact retained keys and stable immutable descriptors |
| DemandStore and handoff | Typed controls, paired ZERO exit, no unconditional ZERO permission or C5 bypass; run-2 typed terminal closure lookup |
| JoinedStaticGuidance, FrozenStaticCompletion | Freeze local static DemandTarget readers; query W/B/R composition with the existing visibility and mark rules |
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
concrete-only EXACT/ANY rejection in RestrictedInitialPolicy
shape-only initial/result seen membership which hides the other layer
cube-global NORMAL target reused for weakened run-1 sink arms
```

Move any still-used RuleId alias to a small type file instead of retaining
the old persistent witness store for it. Keep Reach, initial-start dedup,
normal backward-ZERO AP guidance, backward-ZERO native-record exclusion,
AP publication types, complete binding proofs, source occurrences,
static pool semantics, and the selected call policy.

Implement in proof-first/TDD order:

1. Run both constructive packages. Add failing runtime concrete exact-D,
   layer delivery, two-lane, weak-source and weak-sink controls.
2. Add constant funnels, including rejected-packed-batch consumption.
3. Add catalog/raw/retained Target stores and exact owned-key tests.
4. Add typed producers, callbacks, publication/receipt and caller matching.
5. Extend the existing static result dispatch and test it with Target;
   use KaryJoin for complete same-call Target ND tests.
6. Replace ZERO admission/C5/handoff and seed source. Keep its explicit
   control policy. Implement layered C2/query/request-answer delivery.
7. Add canonical entry lanes and per-arm source/sink projection. Test
   ZERO-growth upgrades, result protection, and both start arrival orders.
8. Add the completed terminal/report commit and export migration.
9. Remove old paths. Run complete core/JVM suites and source-delta audit.
10. Commit the implemented change, then run the configured project campaign.

Required tests include:

```text
RuntimeDataDomainTest: all tails/layers, Constant input/output/producer,
  full ND rejection, static final positive, literal overwrite effect.
InitialEmissionContractTest: concrete ANY answers EXACT only in D at
  equal/ancestor paths; exact D stays D, later exact N stays N;
  descendant/sibling/mark/base/E/budget negatives; FLOW unchanged.
InitialDeliveryTest: query result reused, caller keeps actual input,
  Start and request-answer events preserve layer, no second lookup.
InitialLaneTest: N then D and D then N both run, same-layer duplicate
  suppression, canonical STAR collapse, coverage does not hide a lane.
Run1OriginProjectionTest: P+Q becomes D, same P and P+ZERO can stay N,
  complete all-ZERO only, no partial emission, ZERO-growth D-to-N replay,
  per-lane protection upgrades, factored/eager result equivalence.
SourceApplicationTest: original premise retained; callback before result
  filter; Constant creates no hit; conditional transforms keep prerequisites;
  record reads create no actual-GEN hit; accepted backward source-summary
  ZERO results use Target dispatch, with balanced ZERO unchanged.
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
FullZeroSource controls: computed NORMAL exact/MUST sources remain NORMAL;
  computed cuts/DEMAND, GROUP and static dependencies remain DEMAND;
  exact nonzero FULL retains its admitted/computed layer; weak-ND arms
  are D while unary complete exact N stays N;
  native backward MAY replay and forward ZERO replay precede empty C2;
  exact empty-E ZERO cleanup matches scalar/bulk, including protection;
  normal MUST/STAR cleanup uses scalar fallback.
ConcreteConditionalSourceTest: proposed F1/B2/F3 trace reports good only
  by run-3, source permissions from actual reverse actions, no fake hits.
DirectNDSinkTest: crossed partial callers do not report, full sink seed
  preserved, mixed N/D admission produces both terminal constructors.
IntrinsicMayTest: repeated frontier stays provisional, no false normal
  report and no claim of general cross-run convergence.
StaticTargetClosure: direct ZERO writer plus terminal reader, inherited B
  chains, class markers, exact full-mark/group mismatch, no NormalTarget
  seed, paired AP exit and paired ZERO exit, run-2-only control lookup,
  ordinary AP virtual ZERO-exit acceptance through getter/wrapper chains.
TargetReportTest: root+ZERO only, stable catalog context-independent IDs,
  kept IDs after ZERO replay skip, failed barrier no partial snapshot,
  every retained ZERO id already reported.
```

Use historical expected results only in explicitly named old-reference
controls. They are not the selected new admission/reporting contract.
For static delivery and protocol tests, extend the existing fixtures
with a Target result. Exercise the same matching, waiting and completion
code used by AP summaries. Do not create a second delivery test harness.

## 15. Proof package and implementation evidence

The base [proof package](../../spec/lean/proposals/constant-filter-target-zero-implementation-v2-20261031/README.md)
is under `spec/lean/proposals/constant-filter-target-zero-implementation-v2-20261031/`.
It contains reusable Target/domain rules and labeled historical admission
and layer comparisons. Those comparisons do not select their superseded
concrete MAY rejection or old nonzero demotion policy. The package does not import the old hypothetical
NORMAL-to-DEMAND promotion controls or the withdrawn source-permission
workaround as an implementation requirement.

The checker binds this document, the specification hash, the maintained
Lean modules, and reviewed runtime source bytes. Run:

```sh
python3 spec/lean/proposals/constant-filter-target-zero-implementation-v2-20261031/check.py
```

The checker covers 16 modules and 293 theorems. It audits 543 public
declarations, including 248 executable definitions and 2 abbreviations.
The amended receipt binds the selected source snapshot after runtime
source freeze. These hashes do not verify Kotlin implementation behavior.
Only `propext` and `Quot.sound` occur. The final theorem map and input hashes
are in the package's README and receipt. The models establish:

| Obligation | Model/evidence |
|---|---|
| Constant-free packets, stores and safe-route preservation | ConstantBoundary |
| Historical concrete MAY rejection; reusable generic empty-emission no-op | InitialEmissionExact, UnansweredDemand; MAY-specific rejection controls are superseded |
| Control C2/C5, paired handoff, source scope, normal-only application | SelectedCore, SelectedTargetApplication |
| Stable report IDs and complete ND layer/origin rules | TargetZeroRegistry, TargetZeroND |
| Arbitrary-arity complete Target tuples and full origins | TargetJoin |
| Exact owned retained/seen delta and pending obligation preservation | OwnedDelta |
| Register/replay/start, counted accepted delivery and completion | TerminalProtocol |
| Finite rooted ZERO settlement and complete-barrier report invariant | ZeroSettlement |
| Non-FLOW Target producer kind and unchanged static descriptors | ProducerDomain |
| Historical ZERO-only boundary and MAY rejection; reusable native replay order and bounded exact cleanup | FullZeroSourceReplay |
| Ordinary FULL computed layer and static/GROUP overrides; historical weak-ND-arm counterexample corrected by the amendment | FullComputedLayer |
| Accepted backward source-summary ZERO becomes Target under the caller original; historical rejection-only current-C2 controls | SourceSummaryCompletion |
| Typed static Target W/B/R completion, eager/factored equivalence, complete paired C2/C5, ZERO-exit probe equivalence and precise mark labels | StaticTargetClosure |

The selected [exact-DEMAND package](../../spec/lean/proposals/demand-layer-exact-initials-20261031/README.md)
supersedes those concrete admission and projected-arm slices. Run it too:

```sh
python3 spec/lean/proposals/demand-layer-exact-initials-20261031/check.py
```

| Amendment obligation | Model |
|---|---|
| Directed exact C2, actual-layer preservation, nonsticky guide, exclusion/budget/mark guards | ExactAdmission |
| Constructive exact C2/C5 image witness, raw layer preservation | C2C5Image |
| Separate N/D membership, canonical start, finite per-run key bound | AdmissionStore, AdmissionBounds |
| Complete source/sink arm support, ZERO precision, full physical seed | NDProjection |
| Factored support equals eager existence; executable choice and work bound | FactoredOrigins |
| Result layers and protection upgrades remain distinct | ResultLanes |
| Demand cannot produce a normal report; normal-only cached Target application | TargetLayers |
| Actual source permissions and same-call positive/negative coverage by run-3 | Pipeline |
| Repeated finite intrinsic-MAY frontier; no general convergence guarantee | IntrinsicMayCycle |

The new package's receipt binds this proposal and its concrete-only spec.
Its README gives the exact audited inventory. Both receipts certify model
laws, not complete conformance of the Kotlin worktree. Keep historical
kernels as regression evidence. Do not rewrite their assumptions to make
them appear to prove the amended contract.

No proof assumes a fresh nonroot ZERO row was already reported. It needs
an executable finite admission/receipt route to a root or a prior settled
row. No proof equates a seen key with accepted delivery.

AP geometry, K6 producer typing, actual call/static binding, cache/context
identity, coroutines and cancellation are runtime adapters. Test them at
the listed boundaries; finite Boolean examples alone do not verify them.
The selected domain, admission and reporting changes are not a theorem
of equality with the old report set. Do not claim whole-program no-FN,
convergence or a measured speedup from the model check. The receipt records
`kernelSelectedLaws=PASS` separately from
`composedRuntimeCoverage=NOT_ESTABLISHED`. The supplementary package proves
the selected finite FULL conditional-source model. Runtime delivery,
source/caller-context adapters and known GROUP routes remain separate
coverage obligations. FULL is the campaign acceptance scope. Record GROUP
failures as known issues; do not remove GROUP or change its semantics.
The static C5 counterexample is a control for the missing closure: the
new static Target completion must supply its complete paired row. Runtime
closure adapters and whole-program coverage still need validation. Binding a positive red regression's source hash does not
claim that the regression passes.

The earlier sharing review changed implementation structure only.
Sections 1.2 through 1.4 add the explicit user-selected FULL computed-layer
correction, its bounded cleanup adapter, backward source-summary
result dispatch, and typed static Target completion in section 1.4.
Section 1.5 corrects the adapter by reusing the existing full paired C5
query; it adds no new semantic rule. Section 4 and the sink-arm amendment
add the explicit concrete admission and support-layer changes. FLOW,
field transfer, cleaner semantics and static writer validation do not
change with that amendment. The shared PublicationIndex,
KaryJoin, static call continuations, publication flush and Seed values
must satisfy the same existing proof obligations. No model certificate
requires a new runtime store or service.

## 16. Project validation and measurements

The last recorded pre-change campaign is historical. It does not measure
this amended implementation:

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
concrete exact MAY admissions, N/D start memberships and canonical duplicates
weak run-1 arm counts, complete NORMAL arm upgrades, full sink-seed counts
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

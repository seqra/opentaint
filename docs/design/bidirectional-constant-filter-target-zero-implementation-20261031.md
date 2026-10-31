# Implementation proposal: constant filtering and Target-guided ZERO

Date: 31 October 2026. Status: proposal for the selected next iteration.
No runtime change is made here.

This proposal follows [impl-proposal-guide.md](../../spec/impl-proposal-guide.md)
and [proof-guide.md](../../spec/proof-guide.md). It includes both selected
changes. It does not include the alias or call-context fixes from the latest
investigation.

Base runtime: `e090118e5f9603f1973c0578a3e04998035f4508`. Repository head
`3d8116a1a131a96f8423ef96d2b4a5d643dc46fc` adds reports and controls.
The [selected call policy](bidirectional-selected-call-policy-implementation-20261030.md)
remains the reference for ordinary call admission.

The user also selected a required initial-emission correction: MAY
`[any]` cannot answer an exact `$` demand. Section 10 specifies this
correction and withdraws the earlier backward-NormalTarget workaround.
An unsatisfied demand emits no initial and requires no special action,
including at the end of an iteration. NORMAL Target summaries compose
only with NORMAL complete support. These selected rules are specified
below; there is no blocked-demand continuation mechanism.

## 1. Evidence and selected semantic scope

The [latest investigation](../reports/bidirectional-backward-demand-delivery-investigation-20261031.md)
finds 184,756 ZERO-origin unpaired rows out of 186,048 rows in the Stirling
run-6 diagnostic. It finds 89,698 constant-base rows in that same diagnostic.
These sets overlap. Do not add their counts or treat them as a speedup bound.

The latest [completed campaign](../reports/bidirectional-selected-call-policy-performance-20261030.md)
has these reached / complete / accepted-forward iterations:

| Project | Status | Reached | Complete | Accepted forward |
|---|---|---|---|---|
| OWASP | OK | run-5 | run-5 | run-5 |
| conductor | TIMEOUT | run-4 | run-3 | run-3 |
| thingsboard | OOM | run-2 | run-1 | run-1 |
| Stirling-PDF | TIMEOUT | run-7 | run-6 | run-5 |

No project is run for this document. The figures do not measure the proposed
implementation.

**These are semantic changes. They are not only storage optimizations.**

| Part | Current behavior | Selected behavior | Proof obligation |
|---|---|---|---|
| Constant-base AP facts | Can enter backward work, summaries and demand | Reject them at runtime boundaries in every run | Constant-free store closure; state the restricted equivalence scope |
| Exact-demand C2 | MAY `[any]` can create an exact initial | Reject MAY actuals for exact demands, including ancestor MAY actuals | No invented exact initial or helper witness; preserve other emission cells |
| Unsatisfied C2 | An empty query skips current-call admission | Keep that no-op; no blocked-offer store, copied demand or forced continuation | Rejected offers and all-rejected batches create no admission work |
| Restricted ZERO admission | Roots and backward callees can start ZERO without a local demand; demand lookup supplies a virtual ZERO row | Admit actual ZERO through explicit local demand only | No unguided restricted ZERO start; retain selected control routes |
| Sink observation | Store a local witness as a report candidate | Emit `NormalTarget(id)` or anonymous `DemandTarget` from a complete binding | Preserve complete support and layer; never report a partial binding |
| Final report | Replace unconfirmed local candidates at each complete forward run | Collect IDs from `ZERO -> NormalTarget(id)` at configured roots | Exact root/premise/constructor test; stable IDs |
| NORMAL terminal application | Target has no current implementation | Apply NormalTarget only with all-NORMAL complete support; otherwise no terminal result | No report ID or synthetic DemandTarget from a failed NORMAL application |
| Retained NORMAL terminals | No current Target record kind | Ignore in backward; skip persisted ZERO rows on replay; suppress re-emission of every persisted exact owned row | Forward-only reuse, settled report IDs, complete-key deduplication |
| Backward actual GEN | Record a source occurrence | Also emit anonymous DEMAND Target at the successful reverse-GEN point | Keep occurrence identity and existing source permission |
| Backward ZERO result | Bypasses C5; handoff can remove its paired exit | Apply C5; preserve the paired ZERO exit | Both directional Target cycles; no unpaired permission |
| Continuation | Uses report candidates and outgoing AP demand | Count outgoing AP demand and DemandTarget; do not count NormalTarget | No stop while an outgoing Target obligation exists |

Except for the explicit C2 correction, keep these mechanisms as they are:
AP field transfer, tails, exclusions,
mark matching, FULL/GROUP configuration, field limits, cleaners, FLOW-backed
relations, non-subsumable flags, alias analysis, static pools, static
post-processing, predefined method contracts, rule conditions and source
action permissions. Do not add GroundingSupport, a weak cache, or an IR
storage change.

Run-1 still has no executable ND edge. Keep its selected per-contributing-
origin approximation and its all-ZERO test. Later FULL runs keep complete
same-call ND joins.

## 2. Types and identity

Target is a terminal effect. It is not an AP fact, mark, field, base, or
initial. Do not insert it into `FlowTree`, `TaintTree`, `Reach`, or an AP trie.

```kotlin
@JvmInline value class ReportId(val value: Int)

data class SinkKey(
    val method: CommonMethod,
    val statement: CommonInst,
    val ruleId: StableSinkRuleId,
)

sealed interface Target {
    data class NormalTarget(val id: ReportId) : Target
    data object DemandTarget : Target
}

fun Target.layer(): Layer = when (this) {
    is Target.NormalTarget -> Layer.NORMAL
    Target.DemandTarget -> Layer.DEMAND
}

data class TargetSummary(val premise: PremiseKey, val target: Target)
```

`StableSinkRuleId` names the same configured sink rule across runs. Use the
existing stable rule identity. Do not allocate a new identity for each bound
condition or mark. A physical location includes its method and instruction;
a source line alone is not a unique location.

```kotlin
fun reportId(sink: BoundSink, at: CommonInst): ReportId =
    reportCatalog.intern(SinkKey(sink.method, at, sink.stableRuleId))
```

The same location and rule have the same ID for all witnesses, method
contexts, and iterations in one analysis. Different locations or rules have
different IDs. IDs remain valid while retained summaries can refer to them.
Do not require the integer allocation order to be equal across schedules.

The ID does not replace a premise key. Keep distinct conditional relations:

```text
arg(0)/T -> NormalTarget(7)
arg(1)/T -> NormalTarget(7)   // a separate relation
```

Do not put a witness, proof, run index, or method form into Target equality.
Keep `NormalTarget(7)`, `NormalTarget(8)`, and `DemandTarget` distinct.
One does not subsume another.

## 3. Stores and ownership

| Store | Key and value | Owner and life | Purpose |
|---|---|---|---|
| Report catalog | `SinkKey -> ReportId`; ID to immutable sink descriptor | Shared analysis owner; all runs | Resolve a final ID to its location and rule |
| Raw Target summaries | Full `PremiseKey -> {normal IDs, demand bit}` | Method actor; one run | Deduplicate terminal relations and retain NORMAL relations for persistence |
| Published Target summaries | Full premise and exact Target constructor | Existing summary owner; one run | Replay or notify caller subscriptions |
| Retained NORMAL Target summaries | Full `MethodKey`, full premise, normal IDs | Barrier writes; run reads a fixed view | Reuse complete terminal relations without a method analysis |
| Outgoing Target demand | Method, anonymous Target entry, original premise exit | Handoff builder; next run | Guide ZERO admission and C5 |
| Sink seed descriptors | Full method context, statement, bound condition/rule occurrence for a DEMAND sink binding | Reached observation owner and handoff | Preserve backward seed permissions independently of anonymous Target deduplication |
| Source hits | Existing method, statement, forward edge, action ID | Existing backward actor and handoff | Preserve next-forward source permissions |
| Root report IDs | Configured root, ZERO premise, normal ID | Completed barrier; analysis result | Retain final report identities |

Use one actor-owned table for raw Target membership. The compact shape can
be:

```kotlin
class TargetBucket {
    val normalIds: MutableSet<ReportId>
    var demand: Boolean
}

class MethodTargetStore {
    // Premise keys retain their existing canonical equality.
    private val rows: MutableMap<PremiseKey, TargetBucket>

    fun add(premise: PremiseKey, target: Target): Boolean // true for a new member
    fun rawRows(): Sequence<TargetSummary>
}
```

The raw table and the publication protocol have different roles. Do not
publish a raw DEMAND relation until C5 accepts it. NORMAL terminal relations
must remain available for reuse and reporting; do not put root report
collection behind the future-demand selector.

Retained NORMAL terminal relations need their own typed record store.
`PersistentRecordStore` accepts AP `Facts` and singleton initials. A Target
has neither an AP conclusion nor that singleton-only restriction. In later
runs, a complete NORMAL ND sink relation must retain its full premise and
must use a same-call join on replay. Do not weaken it to one record per
member.

The catalog holds only report metadata needed by the current JVM exporter.
It must not retain every old `SinkWitness` or compiled method form. The
exporter currently reads a witness's `MethodKey`; replace that dependency
with an explicit sink descriptor. The report ID still excludes context.
If a representative context is needed for the current simple export, keep
it as descriptor metadata, outside Target equality.

### 3.1 Retained NORMAL index

Use the retained index itself for cross-run emission deduplication. Do not
add a second historical publication cache.

```kotlin
interface NormalTargetView {
    fun contains(method: MethodKey, premise: PremiseKey, id: ReportId): Boolean
    fun byPremise(method: MethodKey, actual: Facts): Sequence<NormalTargetRecord>
    fun zeroIds(method: MethodKey): Set<ReportId>
}

data class NormalTargetRecord(
    val method: MethodKey,
    val premise: PremiseKey,
    val id: ReportId,
)
```

The exact record key is `(full MethodKey, full PremiseKey, ReportId)`.
Run index, sink witness, and publication batch are not key fields. ZERO
and nonzero premises are distinct. Keep all ND members in one key.

One completed barrier writes the index; the next run reads a fixed view.
Index AP premise members for lookup, with one shared record identity for
an ND row. Target itself has no AP position. Use the existing same-call
ND join rules for matching a known retained ND record. Its transient
join state belongs to the caller service; it is not a general input
history or a reason to start the callee.

## 4. Constant-base rejection

Apply the filter in all directions and runs.

```kotlin
fun runtimeBase(base: AccessPathBase): Boolean =
    base !is AccessPathBase.Constant

fun runtimePremise(premise: PremiseKey): Boolean =
    premise.members.all { runtimeBase(it.base) }

fun runtimePacket(premise: PremiseKey, facts: Facts): Boolean =
    runtimePremise(premise) && runtimeBase(facts.base)
```

`Facts` has one base, so its base test is constant time. Test each member
of an ND premise. If one member has a Constant base, reject the complete
packet. Never remove that member and retain a weaker premise.

```kotlin
fun admitOutput(at: CommonInst, p: PremiseKey, f: Facts): Facts? {
    if (!runtimePacket(p, f)) {
        counters.constantOutputRejected++
        return null
    }
    return existingAdmitOutput(at, p, f)
}

fun admitInitial(initial: InitialAp) {
    if (!runtimeBase(initial.base)) return
    existingInitialStart(initial)
}
```

Gate before storage, queueing, request collection, and semantic callbacks.
Filtering only the final queue is too late:

```kotlin
// FormApplier.micro: a successful source callback precedes result filtering.
applyEdgeAt(edge, input, premise, place) { resultPremise, result ->
    if (!runtimePacket(resultPremise, result)) return@applyEdgeAt
    if (!runtimeProducer(edge.forward)) return@applyEdgeAt
    if (!hit) {
        hit = true
        actualSourceHit(premise, input, edge, place)
    }
    downstream(resultPremise, result)
}
```

`runtimeProducer` rejects an active producer whose AP source or destination
is Constant. It does not inspect literal values in a condition. Apply the
same rule before conditional-source callbacks and sink binding admission.

Audit all paths, including packed paths which bypass scalar callbacks:

| Boundary | Required check |
|---|---|
| `addRootZero`, `addInitial`, `InitialsIn`, run-1 abstraction answers | No Constant initial |
| `FormApplier` and `EngineAlgebra` result/observation hooks | Reject before source hit or Target creation |
| `RunMethodLocalServices` source and sink bindings | Reject Constant facts and complete premises before binding storage |
| Local queue, post-statement edge store, resume queue | No Constant fact or premise |
| Call offers, saved-record application, current-summary application | Reject before replay, subscription, join and resumption |
| `NeutralRelationBatch` packed encode/apply/decode | Apply the same domain test; no scalar-only filter |
| `JoinedStaticWriterBinding` and static computed supplies | Reject a Constant origin before a static result enters the pool |
| Summary, native record, demand and seed builders | No active Constant endpoint or premise |
| Target production and replay | No Constant premise, including any ND member |

Also check direct predefined `ApOut` results, multi-action `targetTree`
callbacks, `zeroOnly` summary delivery, and the ZERO branch of static
summary composition. These paths can bypass the ordinary scalar collector.
Reject a native or reversed saved record before applying either view if
the record has an active Constant endpoint.

Keep literal IR and rule metadata. For example:

```java
void clear(Box p) {
    p.value = "safe"; // keep this write and its kill/exclusion effect
    return;
}
```

The string instruction still executes. A runtime AP fact based on the
literal `"safe"` does not propagate. Keep nulls, primitive/type predicates,
call resolution, and literal comparison logic. A static final or enum field
has the STATIC base; this filter does not remove it.

This is a selected domain restriction. It is not a proof that every old
derivation survives. The proof preserves routes whose intermediate packets
all have nonconstant bases. A route through a Constant packet can disappear.
Classify such a report difference in the campaign; do not hide it as a
diagnostic count change.

## 5. Sink Target production

Call the Target producer only after the existing full sink check succeeds.
Keep NNF evaluation, condition selection, mark requests, and layer aggregation.

```kotlin
fun completeSink(sink: BoundSink, at: CommonInst, binding: CompleteSinkBinding) {
    if (!runtimeBinding(binding)) return

    val target = if (binding.layer == Layer.NORMAL)
        Target.NormalTarget(reportId(sink, at))
    else {
        // Preserve each DEMAND sink seed before anonymous Target dedup.
        sinkSeeds.observe(key, at, sink.occurrence)
        Target.DemandTarget
    }

    if (config.run1) {
        binding.emitRun1Origins { origin -> emitTarget(origin, target) }
    } else {
        emitTarget(binding.completePremise, target)
    }
}
```

`emitRun1Origins` is the current selected origin policy. It emits each
contributing nonzero atomic origin after the full binding is satisfied. It
emits ZERO only if a complete permitted all-ZERO binding exists. It must
not emit ZERO merely because the last contributor has a ZERO premise.

Later ND Target application requires all premise members in the same call
route. Do not cast Target to `TaintTree` in `ndMatch`. Add a terminal-result
branch after the existing complete join, with no AP result construction.

```kotlin
fun emitTarget(premise: PremiseKey, target: Target) {
    if (!runtimePremise(premise)) return
    if (!forward && target is Target.NormalTarget) return
    if (target is Target.NormalTarget &&
        config.normalTargets.contains(key, premise, target.id)) return
    if (!rawTargets.add(premise, target)) return

    when (target) {
        is Target.NormalTarget -> publishNormalTerminal(premise, target)
        Target.DemandTarget ->
            if (config.run1 || demand.acceptsTarget(key, premise))
                publishDemandTerminal(premise)
    }
}
```

The NORMAL branch is a new terminal-summary lane. Its purpose is to retain
and deliver an already complete sink relation. It does not grant any AP
initial or AP summary permission. The DEMAND branch uses the paired C5
rule in section 8. There is no blanket DEMAND Target bypass.

Check the retained NORMAL key before inserting, counting, queueing or
publishing the row. If the exact owned `P -> NormalTarget(id)` is already
persisted, emit no current row or publication for it. Same-run duplicates
are rejected by `rawTargets.add`. Seed dedup for a separate DEMAND binding
remains independent of this NORMAL-row check.

Target publication is immediate. It does not walk the remaining CFG, enter
an AP cleaner, execute return transfer, or require a reachable normal exit.
The original AP derivation continues under its existing rules.

```java
void check(Box p) {
    sinkT(p);     // p/T -> Target is published here
    while (true) { }
}                 // no fabricated normal return is needed
```

## 6. Backward source Target production

Use the successful reverse of an actual GEN. `MicroEdge.isSource` already
means `forward.from == ZERO && forward.to != ZERO`.

```kotlin
fun acceptedSourceHit(
    at: CommonInst, edge: MicroEdge, original: PremiseKey, input: Facts,
) {
    sourceHits.add(key, at, edge.forward, edge.actionId)
    if (!forward && edge.isSource) emitTarget(original, Target.DemandTarget)
}
```

Extend the source callback with the original premise/input or add a typed
callback at the same point. A callback with only `(node, edge)` cannot
construct the required original premise. Preserve the existing ordering:
successful GEN application, source hit/Target, then downstream result
filtering. First apply the constant-domain test from section 4.

Do not use generic `SourceHitStore.add` as the Target trigger. Conditional
source transfers also record hits there. A conditional transformation
`p/T -> q/U` continues its ordinary backward prerequisite `p/T`; it does
not become a terminal merely because it assigns a mark. Keep its action
permission in the existing source-hit store. Reading an opposite-direction
AP record is not an actual GEN application and creates no new source hit.

The selected backward terminal Target has no report ID and is DEMAND.
Do not extend NORMAL sink IDs to sources.

## 7. Caller application and NORMAL reuse

Target is terminal at the caller too. Match the complete callee premise to
actual call inputs through the existing input bindings and matching rules.
Retain original caller support. Then publish the caller terminal result.

```kotlin
fun composeTarget(target: Target, matchedLayer: Layer): Target? = when (target) {
    is Target.NormalTarget -> target.takeIf { matchedLayer == Layer.NORMAL }
    Target.DemandTarget -> Target.DemandTarget
}

fun applyTarget(part: Subscription, summary: TargetSummary) {
    if (!forward && summary.target is Target.NormalTarget) return
    matchCompletePremiseAtThisCall(part, summary.premise) { matched ->
        val target = composeTarget(summary.target, matched.completeLayer)
            ?: return@matchCompletePremiseAtThisCall
        caller.emitTarget(matched.originalCallerPremise, target)
    }
}
```

`matched.completeLayer` includes the caller control layer and every matched
ND contributor. A NORMAL callee result does not make a DEMAND input NORMAL.
For a retained must-premise, also preserve the existing native-record
`inside` versus `applicable` classification. An applicable-only match can
require DEMAND even if the offered header is NORMAL. Include that demotion
in `matched.completeLayer` before checking NORMAL terminal applicability.
An applicable-only DEMAND result cannot use a NormalTarget. A terminal has
no return suffix at which to postpone this decision.

```text
NormalTarget(id) + all-NORMAL valid support -> same NormalTarget(id)
NormalTarget(id) + any DEMAND support       -> no terminal result
DemandTarget    + permitted complete support -> DemandTarget
```

Do not convert a failed NormalTarget application into anonymous DemandTarget,
create sink seeds from a saved NormalTarget, or read it backward. It is a
retained forward report relation. These guards do not alter ordinary saved
AP-summary matching. They are explicit terminal-specific behavior.

Do not send Target through `bindBack`, `bindOut`, aliases, cleanup actions,
field cuts or the instruction after the call. Terminal publication from a
nonreturning callee does not create a returned data fact or a normal return.

Keep ordinary selected call order:

```kotlin
for (part in originalCallOffers) {
    rejectConstantPacketOrContinue(part)
    replayPersistedApSummaries(part)       // every offer, as now
    replayPersistedNormalTargets(part)    // terminal match and direct publication
    val initials = demand.initials(part.callee, part.added, policy)
    if (initials.isEmpty()) continue
    subscribeBeforeCurrentReplay(part)    // includes typed current Target results
    startInitials(part.callee, initials)   // no repeated callee query
}
```

Do not retain every rejected input or add a no-demand subscription for AP
facts. No extra live Target subscription policy is selected here. Check the
late-publication case in the adapter tests. If a production-reachable lost
Target requires a new subscription policy, show the exact trace and obtain
the behavior decision before implementation.

Persist NORMAL terminal relations at a completed barrier. Retain complete
ND support, unlike the singleton-only AP record path. DEMAND Target is not
a persistent NORMAL record. NORMAL and DEMAND terminal memberships can
coexist under one premise.

### 7.1 Forward-only saved replay and ZERO suppression

```kotlin
fun replayPersistedNormalTargets(part: Subscription) {
    if (config.direction == Direction.BACKWARD) return
    for (record in config.normalTargets.byPremise(part.callee, part.added)) {
        if (record.premise.isZero) continue
        applyTarget(part, TargetSummary(record.premise,
            Target.NormalTarget(record.id)))
    }
}
```

Persisted `ZERO -> NormalTarget(id)` has already established its terminal
effect at a completed forward fixed point. Keep its exact membership for
deduplication and keep the report ID already collected at a root. Skip
its application and publication in later runs. Do not remove that final
report because a later run skips its ZERO row.

For nonzero `P`, distinguish the saved relation from its application:

```text
saved check: p.$/T -> NormalTarget(4)
new NORMAL caller input matches p.$/T
  -> apply the saved relation
  -> offer caller's original premise -> NormalTarget(4)
  -> suppress that caller row too if its exact owned key is persisted
```

Do not publish the saved callee row again. A newly eligible NORMAL caller
can still use it through saved replay. A new caller result is a different
owned key; test that key at the caller. Deduplication is not a global ban
on using an ID or on applying a conditional saved relation to a new input.

The ZERO optimization requires the settled-effect invariant: completed
forward publication, call delivery and root report collection precede
the barrier which exposes a ZERO row as persisted. No pending publication
can be dropped by that barrier. Publish the retained root-ID snapshot and
new terminal-record view as one committed boundary state. Incomplete runs
expose neither as a new completed snapshot. The zero-row proof models this
invariant explicitly; ZERO in a row alone is not its proof.

Check this invariant at the completed-barrier adapter:

```text
for every persisted (method, ZERO, id): id is in committed root report IDs
```

This applies to nonroot method rows too. A NormalTarget has no AP or
backward-demand effect; once its ID is reported, reapplying a ZERO row
cannot add a new final report identity. Keep a constructive normal call
route or a root-report membership certificate in the formal adapter.
The implementation needs only the existing committed ID membership;
do not add runtime grounding labels to ordinary facts.

The engine adapter establishes this invariant by induction on first
forward ZERO admission. A first admission has a finite route from a
configured root: either it is that root or an already started caller
submitted ZERO. Forward ZERO control is NORMAL. Register-before-start
therefore supplies the NORMAL caller subscription before a fresh ZERO
terminal is published. Follow that admission route upward. A fresh row
continues toward the root; a suppressed retained row already has a
reported ID by the prior invariant. At the root, collect the fresh ID
before publishing the completed record/report snapshot. Recursion does
not create an infinite proof route: the first-admission parent is an
earlier event. This argument excludes detached imported ZERO rows and
incomplete barriers; the runtime adapter tests must check those exclusions.

## 8. C2 and C5 control cells

Use a typed control side index in `DemandStore`. Target has no AP base or
path, so an AP `PathTrie` query for ZERO cannot find a Target row by itself.
Keep the complete `(D_c, D_p)` pair for C5.

### 8.1 Initial emission

| Demand entry `D_c` | Submitted fact | Result |
|---|---|---|
| Target | actual ZERO/REACH | canonical ZERO |
| Target | nonzero AP | none |
| ZERO | actual ZERO/REACH | canonical ZERO, if the explicit row exists |
| ZERO | nonzero AP | none |
| Ordinary AP | ordinary AP | existing emission policy |

No runtime submitted Target exists. Target never becomes a premise.

```kotlin
fun emitControlInitial(entry: ControlEntry, actual: Facts): InitialAp? {
    if (actual !is Reach) return null
    return when (entry) {
        ControlEntry.ZERO, ControlEntry.TARGET -> ap.zero
    }
}
```

Run-1 keeps discovery ZERO. In restricted runs, use the same explicit
lookup for roots and callees:

```kotlin
fun startRoot(root: MethodKey) {
    if (config.run1) startInitial(root, ap.zero)
    else startInitials(root, demand.initials(root, Reach.NORMAL, policy))
}
```

Replace backward `ZeroIn`/`addZeroEntry` admission with this lookup and the
existing immutable initial packet. A sink seed does not start an owner
without an admitted route. Do not add a fresh unconditional ZERO in each
callee after a caller's demand lookup rejected it.

Remove the virtual `(ZERO, no-exit)` permission from `DemandStore.initials`.
Explicit `(ZERO, ZERO)` rows remain valid.

### 8.2 Summary intersection

C5 first checks the produced **premise** against `D_c`. It then intersects
the produced **conclusion** with `D_p`.

| `D_c` | Actual premise | Entry result |
|---|---|---|
| Target | ZERO | accept |
| Target | ordinary AP or ND AP premise | reject |
| ZERO | ZERO | accept |
| Ordinary AP | ordinary original member | existing complete-initial test |

| `D_p` | Actual conclusion | Exit result |
|---|---|---|
| ZERO | ZERO | ZERO |
| ZERO | NormalTarget(id) | preserve the exact NormalTarget(id) |
| ZERO | DemandTarget | DemandTarget |
| ZERO | ordinary AP | none |
| Ordinary AP | Target of either kind | none |
| Ordinary AP | ordinary AP | existing intersection |

The NORMAL terminal lane in section 5 retains complete NORMAL relations
independently of AP demand restriction. The table defines control C5; it
does not turn rejected DEMAND Target into a NORMAL one or manufacture a
report ID.

For a full ND original premise, retain that full premise after the existing
per-member demand query. Never publish a singly supported Target by
dropping its other required origins.

## 9. Handoff, seeds and stopping

Use the same paired projection in both directions:

```kotlin
fun handoff(method: MethodKey, premise: PremiseKey, conclusion: GuidanceEnd) {
    for (member in premise.members) {
        demand.add(method, DemandPair(
            entry = guidance(conclusion),
            exit = guidance(member),      // ZERO stays ZERO; never null here
        ))
    }
}
```

```text
DEMAND P -> Q/AP          => (D_c=Q,      D_p=P)
DEMAND P -> DemandTarget  => (D_c=Target, D_p=P)
NORMAL P -> NormalTarget  => no next-run demand
selected B ZERO -> Q/AP   => (D_c=Q,      D_p=ZERO)
```

Filter Target by its constructor **before** the ordinary demand selector.
The current selector also keeps NORMAL ND AP rows and NORMAL backward-ZERO
AP rows. Keep those ordinary exceptions. They must not export a NORMAL
Target merely because its premise is ND or ZERO.

Remove the backward-ZERO C5 bypass. Keep the separate backward-ZERO AP
selection rule and its native-record exclusion. A seed-dependent backward
`ZERO -> p/T` NORMAL requirement is still guidance; it is not an
unconditional persisted data transfer.

Create backward sink seeds from reached DEMAND sink descriptors, not from
final reports or saved NORMAL terminal relations. Final reports contain only
root-normal IDs. They cannot replace the current run's refinement seeds.
Preserve the bound condition occurrence, full method context, statement,
positive requirements, and existing permission. Two sinks which merge
into one anonymous DemandTarget must retain both seed descriptors.

```kotlin
fun completedForwardBarrier(result: RunResult): Next {
    persistNormalApAndTerminalRelations(result)
    collectRootNormalReports(result)
    val outgoing = buildPairedDemandAndSeeds(result)
    if (outgoing.refinementRows.isEmpty()) return Complete
    return existingBudgetAndPolicyDecision(outgoing)
}
```

Count both AP guidance and DemandTarget in `refinementRows`. Do not use
`ReportBuilder.hasDemandVulnerability()` for this test. Do not continue
merely because a NormalTarget exists. Preserve budget, timeout, OOM and
explicit policy stops. An incomplete run does not commit new records,
new reports or a demand frontier.

## 10. Directed initial emission and unsatisfied demands

The user selected this correction after review of the earlier example:

```text
demand p.[any]/T + actual p.$/T       => initial p.$/T
demand p.$/T + actual p.[any]/T       => no initial
demand p.f.$/T + actual p.[any]/T     => no initial
```

This relation has a direction. The submitted fact can resolve an unknown
part of the demand. An unresolved submitted fact cannot establish an exact
position required by the demand. The first two rows assume matching base,
prefix and concrete mark, and the existing field-budget checks. Do not use
a symmetric geometric meet as the initial-admission rule.

The previous example used the old C2 cell to start a NORMAL exact helper
initial from an unresolved MAY input. That example is withdrawn as a
justification for backward NormalTarget lookup or special sink routing.
Do not add those mechanisms to repair the superseded emission behavior.

The current AP controls still record the old implementation. Their PASS
means the old cell exists; it does not make that cell the selected policy.
`InitialEmissionExact.lean` states the selected rejection instead.

### 10.1 Precise scope

```kotlin
fun emit(entry: Pattern, actual: Pattern): Pattern? {
    val d = normalizeDemandFieldExclusion(entry)
    if (!sameBase(d, actual) || !compatibleMark(d, actual)) return null
    if (!fitsFullBudget(d, actual)) return null
    if (d.tail == EXACT && actual.tail == ANY) return null
    return existingOtherEmissionCells(d, actual)
}
```

Apply this gate in both restricted directions and at every path depth.
It rejects the same-prefix and actual-ancestor successful cells. Other
path relations already fail for an exact demand. Keep run-1 abstraction
unchanged. Do not use a ZERO fallback for a rejected nonzero offer.

| Demand | Submitted fact | Selected result |
|---|---|---|
| `p.[any]/T` | `p.$/T` | `p.$/T`; the submitted exact position refines the demand |
| `p.$/T` | `p.[any]/T` | none |
| `p.f.$/T` | `p.[any]/T` | none |
| `p.$/T` | `p.$/T` | existing exact initial |
| `p.f.$/T` | `p.[any-taint]/T` | existing exact initial if E admits f |
| `p.$/U` | any T fact, U different from T | none |
| `p.$/T` | `p.f.$/T` | none; the exact paths differ |

Apply the ANY rejection to abstract exact demands too, where that
selected grammar permits them. Do not reinterpret `[any-taint]` as MAY.
Keep existing marks, full budget, exclusions, and source action checks.
Do not silently change the generic STAR cells.

### 10.2 Shared policy and proof changes

```text
DemandStore.initials -> the corrected emitter
caller current gate -> that same complete lookup
callee start -> only keys actually emitted by the corrected lookup
C5 initial image -> possible keys of the corrected emitter
```

`canEmitInitial` and `canStoreInitial` describe possible initial shapes,
not whether one particular actual input can emit them. An exact input can
still witness an exact initial under an exact demand. Do not delete all
exact keys from these structural image tests. Keep their equivalence
proof with the corrected emitter and its actual-input guards.

The old generic geometric intersection can still be nonempty for MAY
and EXACT. That overlap is no longer sufficient C2 admission. State the
new admissibility guard in the C2 contract and proofs. Do not claim that
the old unrestricted common-location coverage theorem proves this new
rejection. The original `spec/ap.md` table's ANY-to-EXACT cell is superseded
for this next iteration.

This selected change does not, by itself, narrow ordinary current or saved
AP-summary matching. In particular, replay-before-demand remains the
selected call policy. Audit those paths separately before claiming that
all NORMAL local sink relations have only NORMAL actual caller support.

### 10.3 Unsatisfied demand is a no-op

The user selected no special handling for an unsatisfied demand. If no
submitted fact satisfies that demand during the complete iteration, no
completion action is required either.

```kotlin
fun admitCurrentCall(part: Subscription) {
    val initials = demand.initials(part.callee, part.added, policy)
    if (initials.isEmpty()) return
    subscribeBeforeCurrentReplay(part)
    startInitials(part.callee, initials)
}

fun finishAdmissionIteration() = Unit
```

For an unsatisfied offer, do not create a current input subscription,
initial packet, sink witness, Target, blocked-offer store, retry, synthetic
seed, copied demand row, or forced next iteration. Do not keep the incoming
demand merely because nothing answered it. The next frontier contains
only the selected results actually produced during the iteration.

This no-op applies to current-run admission. Ordinary saved AP summaries
and saved NORMAL terminal summaries still replay first, as section 7
requires. Their valid results are retained; rejection does not undo them.

```text
demand p.[any]/T + submitted p.$/T:
  emit p.$/T and continue through ordinary current-call admission

demand p.$/T + submitted p.[any]/T:
  emit nothing; return from the current-run admission arm

all submitted facts fail this demand:
  no extra action when the iteration ends

outgoing AP and DemandTarget frontier is empty:
  use the selected ordinary empty-demand stop rule
```

Do not reopen the previous normal-helper example as a backward Target
problem. The selected C2 rule rejects its premise-generating step.
`UnansweredDemand.lean` models admission after saved replay. Its batch
proof does not claim that a complete call offer has no saved-record effects.

## 11. Final report collection

```kotlin
fun collectRootNormalReports(snapshot: CompleteForwardSnapshot) {
    for (root in config.roots) {
        for (row in snapshot.rawAndRetainedNormalTargets(root)) {
            if (!row.premise.isZero) continue
            val target = row.target as? Target.NormalTarget ?: continue
            reports.add(target.id) // idempotent across roots and iterations
        }
    }
}

fun finalReport(): List<ReportEntry> =
    reports.map { id -> reportCatalog.descriptor(id).toReportEntry() }
```

Collect raw/retained NORMAL root relations before future-run selection.
That selection intentionally removes every NormalTarget. A nonroot
`ZERO -> NormalTarget(id)` is not yet a final report. A root
`p/T -> NormalTarget(id)` is conditional and is not a final report.
`ZERO -> DemandTarget` has no ID and is not a report.

Keep completed root report IDs across later iterations. If a later
iteration does not analyze that path, its report does not disappear. This
is reuse of an established root-normal terminal relation, not a mutation
of `SinkWitness.confirmed`.

Replace the old BIDI candidate/confirmation report path with this rule.
Update the JVM exporter to resolve a report descriptor; do not call
`entry.witnesses.first()` when report entries no longer contain witnesses.
Keep the sink location, configured rule identity, and existing status
export. A DEMAND-only hit is refinement state, not a final report under
the newly selected contract. This can change reports at timeout; measure
that change explicitly.

## 12. Principal execution controls

### 12.1 Demand sink and paired ZERO

```text
F: p/T -> DemandTarget
   handoff: (Target, p/T)
B: actual ZERO is admitted by Target
   sink seed and reverse body produce ZERO -> p/T
   C5: Target accepts ZERO; p/T accepts p/T
   handoff: (p/T, ZERO), including a NORMAL backward requirement
F: actual p/T is admitted
   a remaining DEMAND hit produces p/T -> DemandTarget
   C5: p/T accepts the premise; ZERO accepts DemandTarget
```

### 12.2 Actual GEN and paired ZERO

```text
F: a selected ZERO -> ret/T row gives (ret/T, ZERO)
B: an accepted reverse actual GEN emits ret/T -> DemandTarget
   C5: ret/T accepts its original; ZERO accepts DemandTarget
   handoff: (Target, ret/T)
F: actual ZERO is admitted; the preserved source permission enables GEN
   ZERO -> ret/T satisfies the complete pair
```

The first row must actually be selected AP guidance. A NORMAL forward
singleton GEN record is not selected merely because its premise is ZERO.
Keep its existing record route separate; the integration tests must cover
that case.

### 12.3 NORMAL sink through a caller

```text
check: p/T -> NormalTarget(4)
root:  ZERO -> actual argument/T, NORMAL
apply: ZERO -> NormalTarget(4), NORMAL
report: ID 4, once
handoff: no Target row for this normal relation
```

If a caller's support is DEMAND, this NormalTarget application emits
nothing. It creates neither a report ID nor an anonymous Target. Section
10 states the separate no-op rule for unsatisfied initial admission.

### 12.4 Same location, different witnesses

```text
arg(0)/T -> NormalTarget(4)
arg(1)/U -> NormalTarget(4)
```

The catalog contains one ID. The method store contains both conditional
relations. Their ZERO-root applications collapse to one final report.

### 12.5 Two anonymous sinks

```text
same premise -> DemandTarget    // sink A
same premise -> DemandTarget    // sink B; Target add is duplicate
```

One Target membership is sufficient. Keep seed A and seed B, including
their contexts and condition occurrences. Record seeds before Target add.

### 12.6 ND support

```text
{arg(0)/T, arg(1)/U} -> NormalTarget(4)
```

Both actuals must match at the same call. An unrelated call cannot supply
the second member. For a NormalTarget summary, every contributor must
have effective NORMAL support; otherwise application emits nothing.
An existing DemandTarget summary remains DEMAND. A local DEMAND sink
binding still creates DemandTarget under section 5. Run-1
continues to use its existing atomic-origin approximation instead.

### 12.7 No control reachability from a terminal

```java
void root(Box p) {
    checkAndLoop(p); // a terminal result can reach root's summary
    anotherSink(p);  // Target must not make this instruction reachable
}
```

### 12.8 Constant origin

```text
ZERO -> Constant(".")/T -> arg(0).f/T
```

The first Constant result is rejected before source/Target observation.
It cannot create the later AP demand. This is the selected restricted
domain; do not claim the old derivation survives.

## 13. Production changes and removals

Paths below are relative to
`core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/`.

| File or part | Required change |
|---|---|
| `interp/FormApplier.kt` | Producer-domain check before observations; carry original input/premise to actual-GEN hook |
| `engine/EngineAlgebra.kt` | Constant checks, typed actual-GEN Target callback |
| `engine/RunMethodLocalServices.kt` | Complete sink Target emission; separate seed descriptors; reject constants before binding |
| `engine/RunMethodAnalyzer.kt` | Actor Target table, immediate terminal publication, explicit root ZERO admission, no backward-ZERO C5 bypass |
| `engine/RunMethodCallServices.kt` | Typed Target application; complete ND join; saved NORMAL terminal replay; demand-gated backward ZERO calls |
| `engine/SummaryStorage.kt` and publication protocol | A separate terminal type/index; no Target casts to AP Facts |
| `store/DemandStore.kt` | Explicit ZERO/Target control index; paired C2/C5; no virtual ZERO permission |
| `store/RecordStore.kt` | Keep AP records and their old eligibility; use a separate NORMAL terminal store |
| new `store/NormalTargetStore.kt` | Fixed-run read view, exact owned-key membership, nonzero forward replay and settled ZERO suppression |
| `store/SourceHitStore.kt`, `driver/Seeds.kt` | Preserve source/action permissions; reject active Constant endpoints; keep sink seed routing separate from final report IDs |
| `driver/HandOff.kt` | Paired ZERO exit, Target-specific layer selection, new seed source |
| `driver/Report.kt` | Catalog-backed final root reports; no local-candidate replacement protocol |
| `driver/IterationDriver.kt`, `driver/Frontier.kt` | Terminal persistence, root collection and outgoing-demand continuation counters |
| `NeutralRelationBatch`, `JoinedStaticWriterBinding` | Constant-domain checks on packed and joined routes |
| JVM `JIRBidiAnalysis.toVulnerabilities` | Descriptor-based export; no witness-first dependency |

Remove or replace these BIDI paths after their users migrate:

```text
DemandStore.zeroDemand and its unconditional initials offer
HandOff.toForward: premise ZERO -> exit null
RunMethodAnalyzer.published: backward-ZERO restriction bypass
unconditional backward ZeroIn / addZeroEntry start path
report.demandEntries as the source of backward sink seeds
ReportBuilder's per-forward replacement of local candidates
ReportBuilder.hasDemandVulnerability as an early stop input
SinkWitness.confirmed and CONFIRMED/DEMAND final-report state in this path
mandatory report-entry witness lists and exporter witnesses.first()
```

Do not remove `Reach`, ZERO's ordinary CFG preservation, complete sink
binding proofs, source occurrences, AP native records, the backward-ZERO
AP record exclusion, NORMAL backward-ZERO AP guidance selection, or the
initial-start deduplication gate. Retain test-only legacy reference models
as clearly named comparison controls; do not make them the new runtime.

## 14. Proof and implementation gates

The constructive models are proposal models. Their checked scope and
remaining Kotlin adapters must be stated in the proof package. A proof
over a changed rule does not select that rule.

Required model claims:

1. Accepted initials, packets, stores and routes have no Constant base.
   Whole ND rejection does not weaken a premise. Constant-free derivations
   are preserved under the explicit safe-intermediate assumption.
2. Target has no AP initial/premise constructor. Control admission accepts
   actual ZERO only; it cannot reset a nonzero origin to ZERO.
3. C5 checks entry against premise and exit against conclusion. ZERO exit
   accepts ZERO and Target while preserving the exact Target constructor.
4. Both handoffs retain the full ZERO pair. NORMAL backward-ZERO AP
   selection and Target-only selection remain separate.
5. Complete layer aggregation is NORMAL only if every contributor is
   NORMAL. A NormalTarget application with DEMAND support emits nothing.
   An existing DemandTarget remains anonymous and DEMAND.
6. Catalog growth preserves all old IDs; distinct keys have distinct IDs.
   Same-ID dedup does not merge different conditional premises.
7. A final report exists exactly for a configured root's ZERO-premise
   NormalTarget. A DemandTarget, nonroot, or nonzero premise cannot report.
8. Target publication does not imply a normal return or reach a later CFG
   instruction. A complete same-call ND join is required before application.
9. Seed accumulation is independent of anonymous Target membership. A
   duplicate Target cannot erase another sink's seed.
10. MAY actuals cannot emit an exact initial, including from an ancestor
    prefix. Unsatisfied current admission leaves its state unchanged;
    all-unsatisfied batches require no iteration-end action or fallback.
11. Backward never applies a NormalTarget. Persisted ZERO replay is empty
    under the settled-effect invariant. An already persisted owned row
    cannot produce a new NORMAL emission/publication; a different caller
    key remains eligible for saved conditional replay.

Run the maintained proof package with:

```sh
python3 spec/lean/proposals/constant-filter-target-zero-20261031/check.py
```

The [proof README](../../spec/lean/proposals/constant-filter-target-zero-20261031/README.md)
maps the checked claims and their limits. The receipt binds the proposal
and model bytes. A PASS is a kernel-check result, not a verification of
the future Kotlin implementation or a whole-project no-FN result.

No whole-program equivalence or convergence claim follows from a finite
control table. The constant restriction and root-normal reporting are
explicit selected semantic changes. The retained AP algorithm and runtime
adapters still need executable tests.

### Implementation order

```text
1. Check the selected constructive model and its runtime adapter obligations.
2. Add failing boundary tests for constant admission, ND packets and packed paths.
3. Add the constant filter; run the focused core tests.
4. Add typed Target storage, catalog, publication and retained NORMAL records.
5. Add full sink/actual-GEN hooks and caller/ND terminal application tests.
6. Replace restricted ZERO admission, C5, handoff and seed routing.
7. Replace final report collection/export and continuation inputs.
8. Run the full core and JVM suites; audit unchanged AP semantics and keys.
9. Commit the runtime change. Run the configured project campaign and profiles.
10. Write the new report with reached/complete/accepted iterations and regressions.
```

Test the two changes separately before their combined sequence. Add a
negative test for each former bypass, not only a positive Target test.
Include exact, ANY, STAR, concrete, FLOW, exclusions, NORMAL/DEMAND,
FULL/GROUP run-1, run-2 and later limits at the existing AP adapter seam.
Do not change any of their ordinary intersection results.

Required integration controls include: a local killed before return;
nonreturning callee; nested wrappers; source and sink at one statement;
same-ID multiple witnesses; distinct IDs; two duplicate anonymous Targets;
complete/partial/cross-call ND; mixed ZERO/nonzero run-1 origins; repeated
saved replay; a NORMAL terminal record with no fresh demand; source action
identity; conditional sources; opposite AP record reads; explicit ZERO
identity; no local demand; an iteration with an unanswered demand and no
fallback action; late current publication; cancelled sends; and
an incomplete barrier which commits no new state.
Also test persisted owned-row rediscovery, a new NORMAL caller for a saved
nonzero row, ignored backward replay, skipped saved ZERO rows, retained
report IDs across skipped methods, and full ND key separation.

## 15. Campaign and workload checks

Use the current project configuration: FULL run-1, statics and aliases on,
16 GB, limits `1,1,2,3,...`. Run OWASP as in its CI workflow and conductor,
thingsboard and Stirling-PDF with Gradle `runProjectAnalyzer`. Keep current
configured budgets. Do not add another project/configuration or rerun the
fixed legacy baseline.

Report per iteration:

```text
run index, direction, field limit, engine seconds, status
latest reached / complete / accepted-forward iteration
constant rejects by input, producer, ND packet, seed and packed path
explicit ZERO offers, admitted ZERO starts, rejected ZERO offers
raw/published/persisted NORMAL Target memberships and report IDs
NORMAL rows rejected by persisted-key membership; saved ZERO replay skips
raw/published DemandTarget memberships and outgoing control rows
sink seed descriptors before and after Target dedup
AP outgoing rows separately from Target outgoing rows
ZERO-only owners, edge deltas, call offers and summary applications
heap/RSS; OOM retained owners; profile hot paths
```

Compare final identities by location and rule with the saved baseline and
the current runtime. Also retain a diagnostic count of reached local sink
candidates, so a reporting-contract change is not presented as an
algorithmic no-FN result. Explain each missing final identity: constant
restriction, unresolved DEMAND at timeout, a missing Target route, or an
export defect. A missing route is an implementation failure.

Expected savings are avoided work: no constant-base propagation and no
ZERO exploration outside explicit demand. Do not predict a fixed speedup
from the current row ratios. The normal terminal store and report IDs add
work; measure their retained size and delivery count. There is no new
backward NormalTarget query or unanswered-demand retry route.
The change is not a fix for the separate infeasible-context join measured
in conductor run-4. No bound on total iterations or runtime is claimed.

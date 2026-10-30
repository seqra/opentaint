# Implementation proposal: persisted summaries, demand, current summaries

Date: 30 October 2026. Status: implemented and tested.

The implementation uses the selected policy below. The complete core suite
passes 2,126 tests; the JVM suite passes 452 tests. The constructive model
passes 58 named theorems, including its dependency. The
[source and test receipt](../../spec/lean/proposals/selected-call-policy-20261030/implementation-checks.json)
binds the implementation adapters. These checks do not prove whole-project
finding completeness. The project campaign remains a separate gate.

Base runtime: `edb2e06cdb17eecafbe03415236bf56c57910239`.
Use the selected policy in the
[input-admission investigation](../reports/bidirectional-restricted-input-admission-investigation-20261030.md).
The user also selected replay of persisted summaries **on every offer**, with
existing output deduplication. No persisted-replay input history is required.

Latest measured reached / complete / accepted iterations are conductor
**run-4 / run-3 / run-3** and Stirling-PDF **run-6 / run-5 / run-5**.
Both commands timed out. The
[campaign report](../reports/bidirectional-identity-owner-protection-performance-20261030.md)
contains their measurements. No new project run was made for this proposal.

## 1. Selected changes and fixed scope

| Part | Current implementation | Proposed implementation |
|---|---|---|
| Persisted summaries | Replay after caller input admission and current-summary replay; only a fresh input delta reaches replay | Replay the whole original offer first, on every offer |
| Demand gate | The callee queries demand after the caller has subscribed and sent the actual input | The caller runs the existing emission query; an empty result ends this current-run route |
| Current summaries | An input can join an applicable current publication even if its demand admission is empty | Replay and subscribe only after nonempty demand admission |
| Callee input | Full actual Facts, CallerRef and link layer; callee repeats emission work if a caller gate is added | Immutable final initial keys; the callee only starts unseen keys |
| Caller input history | Includes inputs used only for persisted replay or rejected by demand | Holds only actual offers which passed the demand gate |
| Initial-start gate | InitialFactStore admits a key before boundary rules | Keep it unchanged |

**Two selected execution-policy changes must remain visible:**

1. Applicable current summaries are not permission to bypass an empty demand
   admission result. Their old callbacks outside that permission may disappear.
2. A repeated input can replay persisted summaries and the return pipeline
   again. Output and observation stores remain responsible for semantic
   deduplication. Raw callback counts need not remain equal.

Keep field and mark transfer, tails, exclusions, protection, cleaners, aliases,
rule occurrences, ND origins, C5 restriction, persistent-record eligibility,
field limits and stopping unchanged. Keep existing semantic equality and
hashing of Facts, Subscription, CallerRef and premise keys. No gate token or
compiler metadata becomes part of those keys.

Run-1, predefined methods, unresolved-call stages, explicit backward ZERO
control and run-1 request handling keep their existing routes. This proposal
does not remove InitialFactStore or redesign MethodEdgeStore. It does not
include generic mask-merge optimization, mark packing, a replay cache, new
barriers, reference-manager changes or IR storage work.

The proof reference is the selected policy, not every callback of the current
unconditional subscription path. A matching normalized FLOW summary does not
add another admission test. No hypothetical-summary compatibility query is
allowed.

## 2. Complete caller algorithm

Modify only the ordinary `CallStage.Callees` path in
`RunMethodCallServices.enterCallees`. The surrounding call stages stay as now.

```kotlin
private fun enterCallees(ctx: CallContext, stage: CallStage.Callees, fact: PlanFact) {
    val core = active()
    val ref = CallerRef(core.key, fact.premise, ctx.callerLayer,
        ctx.node, ctx.plan.stages.indexOf(stage))

    for (callee in stage.callees) {
        core.ap.cancellation.checkpoint()
        val part = Subscription(callee, ref, fact.facts.layer, fact.facts)
        check(part.added.base !is AccessPathBase.CleanerTemporary)
        check(part.linkLayer == part.added.layer)

        if (core.config.run1) {
            core.runnerPort.subscribe(part)
            core.runnerPort.link(callee, ref, part.linkLayer, part.added)
            continue
        }

        // Phase 1. Every offer, including repeats. No standing input admission.
        replayPersistedSummaries(core.config, core.ops, part, applier = core)

        // Phase 2. Query the original full offer, not a merge delta or a
        // post-replay result. The helper makes the same bounded query as before.
        val initials = emitRestrictedInitials(core.config, core.ops, callee, part.added)
        if (initials.isEmpty()) continue

        // Phase 3. Existing register-before-replay protocol; only live inputs
        // enter the caller's accumulated input store.
        core.runnerPort.subscribe(part)

        // Submit even if subscribe rejected a duplicate live input.
        // The callee start gate handles duplicate keys.
        core.runnerPort.startInitials(callee, initials)
    }
}
```

Use the method actor as the SummaryApplier. It dispatches through the existing
method-call service, including its configured wrappers. Do not bypass that
dispatch by passing this service directly.

Persisted replay must finish before phase 2 begins. It can produce ordinary
return-stage work. It does not replace or mutate `part.added` for the next
phases. Apply demand admission to the original offered input.

The gate is on the complete offered Facts value. If it has several paths or
marks, keep that value for an accepted subscription. Do not silently project
it to demanded leaves, merge offers before the gate, or substitute the emitted
initial for it. A previous rejected offer does not enter the live store merely
because a later different offer passes.

## 3. Persisted replay without input history

### 3.1 Extract the existing replay body

Move `SubscriptionManager.replayRecords` into a stateless helper, for example
`engine/PersistedSummaryReplay.kt`. Preserve its matching and application code.

```kotlin
internal fun replayPersistedSummaries(
    config: RunConfig,
    ops: ApOps,
    part: Subscription,
    applier: SummaryApplier,
) {
    check(config.restricted && !part.zeroOnly)
    val records = config.records
    val cancellation = ops.manager.cancellation
    val seen = HashSet<Record>()
    val seenViews = HashMap<RecordLeafView, Boolean>()

    for (leaf in ops.leaves(part.added)) {
        cancellation.checkpoint()
        for (record in records.byEntry(part.callee, leaf)) {
            cancellation.checkpoint()
            if (record.direction != config.direction || !seen.add(record)) continue
            val matched = ops.satisfying(part.added, record.premise,
                config.mode, record = true) ?: continue
            applier.applyRecord(part.copy(added = matched), record)
        }
        for (record in records.byExit(part.callee, leaf)) {
            cancellation.checkpoint()
            if (record.direction == config.direction) continue
            record.forEachReversedAt(leaf) { view, protected ->
                cancellation.checkpoint()
                val old = seenViews[view]
                if (old == true || old == false && !protected) return@forEachReversedAt
                seenViews[view] = old == true || protected
                val matched = ops.satisfying(part.added, view.premise,
                    config.mode, record = true) ?: return@forEachReversedAt
                applier.applyRecordView(part.copy(added = matched), view, protected)
            }
        }
    }
}
```

The two seen collections are temporary and local to one invocation. They
retain the existing protection-upgrade rule. Release them when replay returns.
They are not a history of offered inputs.

The persisted store is the run's read-only view of eligible NORMAL records
from earlier completed runs. Use both native and opposite-direction reads.
Do not demand-filter these records. Do not reinterpret a transient reversed
record premise as an initial key. Keep native must-record splitting and its
demotion after the return actions in `RunMethodCallServices.applyRecord`.

Keep original caller premises, layers, call/stage, protection and identity
classification in `applyRecord` and `applyRecordView`. Repeated replay may
invoke those methods again. It must not create a new rule occurrence ID or
change a witness key to make a repeated result distinct.

### 3.2 Remove the second replay

Delete this branch from `SubscriptionManager.replay` after extracting the body:

```kotlin
if (!part.zeroOnly && port.config.restricted) replayRecords(part)
```

Current-summary replay then contains only current publications plus the
unchanged run-1 static/request branches. Do not apply persisted records again
after phase 3. No new `AddedFactAccumulator` is created for phase 1.

## 4. Move the complete initial-emission query

Add a stateless helper, for example `engine/RestrictedInitialEmission.kt`.
Move the restricted branch of `RunMethodAnalyzer.addLink` into it.

```kotlin
internal fun emitRestrictedInitials(
    config: RunConfig,
    ops: ApOps,
    callee: MethodKey,
    actual: Facts,
): List<InitialAp> {
    check(config.restricted)
    val ap = ops.manager
    val result = LinkedHashSet<InitialAp>()
    ops.limit(actual, config.fieldLimit, object : ApOut {
        override fun markRequest(mark: TaintMark): Nothing =
            error("A field cut cannot request a mark")

        override fun result(bounded: Facts) {
            for (leaf in ops.leaves(bounded)) {
                ap.cancellation.checkpoint()
                if (config.index == 2)
                    validateRun2StaticFullInput(ap, leaf, config.fieldLimit)
            }
            result.addAll(checkNotNull(config.demand).initials(
                callee, bounded, config.admissionPolicy))
        }
    })
    return result.toList()
}
```

Use the target callee MethodKey, not the caller key. Keep the actual's current
layer and annotations during limiting. The initial keys and their start-fact
layers remain determined by the existing AP policy.

Run-2 uses its current virtual static completion. Later runs use local demand.
Keep the complete query, including its early coverage stop and entry lookup.
Do not replace it with a raw path overlap or an existence-only query and then
run emission again in the callee.

The helper queries the whole original offer. This first implementation does
not require a distributivity theorem for fresh input deltas. It does not use
`CalleeSubscriptions.admit` results to decide which initials to send.

## 5. Transfer initial keys to their owner

### 5.1 Event and port

Add `RunEvent.InitialsIn` for restricted call input:

```kotlin
class InitialsIn(val callee: MethodKey, initials: Collection<InitialAp>) : RunEvent {
    val initials: List<InitialAp> =
        Collections.unmodifiableList(ArrayList(initials))
    init { require(this.initials.isNotEmpty()) }
}

// RunEvent.target():
is RunEvent.InitialsIn -> callee

// RunnerPort:
fun startInitials(callee: MethodKey, initials: Collection<InitialAp>)
```

The copied collection is immutable. Its elements are canonical keys owned by
the current shared AP manager. The event contains no actual Facts, CallerRef,
demand rows or caller-layer field. No run ID or eligibility flag is added to
Subscription equality or hashing. An event stays within its RunManager.

Use the existing link routing policy in `UnitRunner`: same-unit handling on
the current owner, or counted delivery to another unit. Preserve the current
callee/unit eligibility rules. Use cancellation checkpoints and required-send
handling; a rejected send must not be treated as successful completion.

```kotlin
override fun startInitials(callee: MethodKey, initials: Collection<InitialAp>) {
    check(!run.ended && !closed.get())
    shared.cancellation.checkpoint()
    val event = RunEvent.InitialsIn(callee, initials)
    if (shared.unitResolver.resolve(callee.method) == unit) {
        handler.handle(event)
    } else {
        val accepted = send(event)
        shared.cancellation.checkpoint()
        check(accepted) { "An active run rejected initial delivery" }
    }
}
```

### 5.2 Callee handler

```kotlin
is RunEvent.InitialsIn -> {
    check(port.config.restricted)
    val actor = port.analyzer(event.callee)
    for (initial in event.initials) {
        port.shared.cancellation.checkpoint()
        actor.addInitial(initial)
    }
}
```

Keep `addInitial` and InitialFactStore unchanged. This gate runs before
boundary rules, handles empty/changed boundary output, and starts all required
normal exits in a backward run. The callee performs no second limit, demand
lookup or admission test.

The caller subscribes before invoking `startInitials`. A same-unit callee
can therefore publish immediately without losing the caller. A publication
made earlier is available to replay. A later publication uses notification.
The existing at-least-once replay/notification protocol stays unchanged; this
proposal does not promise exactly-once pair application.

An already-started initial does not cancel a new caller subscription. Two
callers can share one analysis while retaining separate answer bindings.

## 6. Storage, removal and unchanged routes

| Entity | Required state after the change |
|---|---|
| Caller CalleeSubscriptions | Existing exact actual-input accumulation and positional index, only for offers whose own demand gate passed |
| AddedFactAccumulator | Existing implementation; no native-only second instance or raw-input history |
| SummaryStorage / PublicationIndex | Existing publications and subscriber managers; create/register for this input only after the gate |
| InitialsIn | Temporary immutable list of canonical keys, released after handling |
| Callee InitialFactStore | Existing once-per-key start state |
| MethodEdgeStore, vulnerability/source-hit/conjunction stores | Existing output and observation admission, including repeated persisted results |
| DemandStore / RecordStore | Existing immutable per-run views |

Remove or narrow these runtime paths:

- Remove persisted replay from `SubscriptionManager.replay` and move its body
  into the stateless helper. No persisted behavior is deleted.
- Remove restricted raw LinkIn delivery from ordinary calls.
- Remove the restricted limit/demand branch of `RunMethodAnalyzer.addLink`.
  Make that raw-input method run-1-only and assert this scope.
- Keep LinkIn, `RunnerPort.link` and the run-1 branch for request abstraction.
- Keep InitialAnswersIn for run-1 answers; do not silently change that event's
  meaning. Keep Start, ZeroIn and backward zero-only subscription handling.
- Keep predefined-summary and unresolved-call stages. They do not enter this
  ordinary resolved-callee path.

There is no new negative lookup cache, replay history, hypothetical-initial
index, callee added-fact store or pending batching barrier. Query results are
used in this call and then released or delivered.

## 7. Principal cases

### 7.1 Saved normal summary with no current demand

```java
Box id(Box p) { return p; }
// Retained NORMAL record: p.*/FLOW -> ret.*/FLOW.
```

```text
forward offer p.$/T:  persisted result ret.$/T; empty demand; no live subscription.
backward offer ret.$/T: reversed result p.$/T; empty demand; no live subscription.
repeat the same offer: persisted replay runs again; existing outputs deduplicate.
```

No CalleeSubscriptions input row or callee initial event is created for this
route if it has no other demanded offer. The persisted store does not require
a callee analyzer.

### 7.2 Different actual inputs share one initial

```java
Box get(Box p) { return p.f; }
// run-3 / limit 2 demand entry: p.[any]/FLOW.
```

```text
offer p.f.a.$/T -> initial p.f.*/FLOW -> subscription keeps original T input.
offer p.f.b.$/U -> initial p.f.*/FLOW -> subscription keeps original U input.
callee starts p.f.*/FLOW once.
summary p.f.*/FLOW -> ret.*/FLOW gives ret.a.$/T and ret.b.$/U respectively.
```

Do not key caller input by the emitted initial or replace original caller
premises with the callee initial.

### 7.3 Two branch writes reach one call

```java
void caller(Box p, boolean b) {
    if (b) p.f = new Box(); else p.f = new Box();
    blocked(p);
}
// Both writes retain exact root p.$/T and can submit the same call input.
```

Persisted replay and demand lookup run on both offers. If demand is empty,
neither offer creates live input state or a callee packet. If demand passes,
the existing live accumulator admits only fresh current-replay work. Both
offers can still send the same initial key; the callee starts it once.
Do not claim that every nonfresh offer now disappears as a message.

### 7.4 An applicable normalized summary cannot reopen the gate

```text
current demand: p.[any]/FLOW -> ret.[any]/FLOW
offer:         p.*/FLOW
initial emission: empty
an existing current p.*/FLOW -> ret.*/FLOW publication may match geometrically.
```

Apply persisted summaries, then return at the empty demand gate. Do not replay
that current publication and do not subscribe. Applicability alone is not
necessity. This selected case supersedes the earlier compatibility proposal.

### 7.5 Packed input and protection upgrade

If an offered tree contains T and U and its demand emission is nonempty,
retain the complete offered tree as now. If U alone failed an earlier offer,
that earlier row is not installed retrospectively. A later offer that actually
contains both marks is processed as that complete offer.

If ordinary content is unchanged but protection grows, persisted replay uses
the full upgraded offer. The existing live accumulator must emit its fresh
annotation delta. Facts equality alone must not discard that upgrade.

### 7.6 ZERO, ND and run-2 statics

- A normal REACH offer with ZERO origin uses the implicit zero demand and its
  normal route. Do not classify it as zeroOnly by origin alone.
- The explicit backward zero-only subscription and ZeroIn path stay as now.
- Preserve a full PremiseSet in CallerRef and every current ND member binding.
  Sending singleton InitialAp keys to start a callee does not flatten caller ND.
- Run-2 static completion runs in the caller query with the same full callee
  key and owner rules. The callee consumes the result without graph lookup.

## 8. Proofs and their scope

The constructive [Lean package](../../spec/lean/proposals/selected-call-policy-20261030/README.md)
checks **30 new named theorems**, plus the earlier 28-theorem input kernel:
**58 named theorems and 112 audited declarations** in total. It uses only
`propext` and `Quot.sound`, with no custom axiom, proof hole or Classical.choice.
It does not verify Kotlin or whole-program report completeness.

### P1. Demand controls new-summary input

For offer F, let E(F) be the complete current fixed-run initial-emission
result. The selected reference retains F for live matching iff E(F) is
nonempty. `rejected_retains_no_live_input`, `rejected_sends_no_packet`,
`accepted_keeps_full_actual` and `failed_offer_is_not_activated_by_later_passed_offer`
prove this finite state transition. The branch in section 2 implements it.
No hypothetical compatibility predicate appears in the model or implementation.

This proves adherence to the selected authorization contract. It does not
claim equality with old callbacks outside demand. The AP argument that incoming
demand identifies required new work is the analysis contract, not a consequence
of matching one arbitrarily injected publication.

### P2. Moving lookup preserves all emitted initial keys

Demand, records, field limit, direction and mark policy are fixed during a
run. Move the exact same function E, with the exact same actual and callee key,
from receiver to sender. Its result is therefore unchanged. `moved_lookup_exact`
and `moved_lookup_exact_over_all_offers` prove this for any deterministic E;
they need no distribution over deltas. `selected_handoff_refines_reference`
proves equality of initial, live-route and saved-observation states for the
selected concept and the handoff implementation kernel.

The Kotlin adapter obligation is literal extraction of the current limit and
complete demand query, with no extra narrowing or policy replacement.

### P3. Starting a key remains once-only

For started set S and packet J, the receiver retains S ∪ J and starts J \\ S.
`receive_starts_exactly_fresh`, `repeat_start_has_no_fresh`,
`start_gate_retains_old` and `receiveAll_exact` prove this. Existing addInitial
performs this admission before boundary work. Packet immutability and shared
manager keys preserve the existing identity contract.

Send the key packet even if live admission returns no delta. This avoids
assuming that the input merge history is a complete history of sent initials.
`packet_independent_of_live_freshness` and an executable duplicate-offer control
pin that separation. No new sent-initial set is introduced in the caller.

### P4. Caller binding and live replay stay exact

Only the transport payload changes. The eligible subscription still owns
the original full actual and ref. `other_route_unchanged`,
`handoff_preserves_live_routes` and the existing two-path AP diagnostic control
show why equal initial keys cannot merge caller routes. `accepted_replay_is_fresh`
models the existing fresh live delta. The unchanged annotated accumulator
retains its protection-only upgrade behavior.

### P5. Persisted replay is independent of demand and idempotent in observations

The new first phase has no demand predicate or stored offered-input set.
`saved_replay_does_not_use_demand` and `handoff_preserves_saved_observations`
prove that ordering-independent membership property. Repeating the same saved
effect does not add a new semantic observation, but invokes replay twice:
`repeated_saved_replay_has_equal_observation_set` and
`repeated_saved_replay_still_runs_twice` make both facts explicit.

Source adapters must keep existing observation keys: SourceHitStore uses a
set of source occurrence keys; ConcurrentVulnerabilityStore merges equal
complete support shapes; method outputs admit fresh annotated relations.
Keep rule/ND input admission and protection upgrades intact. Integration
tests must include full return rules, alias lanes and native must demotion,
not just an AP output union. The finite observation proof does not certify
arbitrary stateful callbacks or promise unchanged diagnostic counts.

### P6. Publication delivery remains complete

Use the existing register-before-replay protocol. A publication before
registration is in replay's storage snapshot. A publication after registration
is delivered by notification, replay, or both. Register before starting a
same-unit callee. These are the existing P1–P6 protocol cases; add the new
outer demand gate to their tests. The model's trace theorems pin persisted
replay, lookup, registration, current replay and initial send in that order.
`publication_has_delivery_channel` and `chosen_channel_is_valid` give an
executable replay/notification witness for every publication with registration
before replay. The linearization points must come from the unchanged storage
lock and owner protocol; this finite proof is not a verification of coroutines.

Required sends retain the existing in-flight accounting. The receive theorem
assumes accepted packets are actually handled before a completed fixed point;
cancelled or rejected delivery is not a complete run. No new lost-wakeup
argument depends on retaining native-only inputs.

### P7. No hidden transfer or key change

Source diffs must show moved query/replay bodies and changed control flow,
not new AP tables. The source binding in the checker identifies the reviewed
base. Verify unchanged equality/hash code, normalization, layers, exclusions,
record views, stage ordering and ND keys. A proof of the selected finite kernel
does not authorize a changed field or mark abstraction.

## 9. Implementation plan and validation gates

Before runtime changes, align the affected canonical descriptions:

| Specification | Required update | Keep unchanged |
|---|---|---|
| analyzer-core.md initial/input handlers | Caller emits restricted initials; callee consumes InitialsIn | Once-per-initial admission and boundary transfer |
| analyzer-core.md call handling and subscription manager | Persisted replay per offer, demand gate, then current replay/subscription | Caller refs, stage suffix and register-before-replay protocol |
| ap.md caller subscription storage description | Restricted live storage contains only offers that passed demand | AP matching, emission tables, C5 and record transfer tables |
| ap-impl.md affected driver/transport examples | Reflect the new helper and event placement | Data identity, exclusions, layer and protection rules |

The user-selected call policy supersedes unconditional restricted subscription
and fresh-only persisted replay at these integration points. Do not leave an
old conflicting description as the implementation's normative contract.

1. Add a selected-policy reference harness and tests before runtime edits.
   Exercise the real AP query and replay adapters; the phase-order oracle is
   independent of the optimized caller implementation.
2. Extract persisted replay without changing native matching/application.
   Prove per-invocation equality with the old body, then call it per offer as
   selected. Remove its call from current-summary replay.
3. Extract complete restricted emission. Differentially compare old receiver
   and new helper for all tested tails, marks, E, masks, field limits, directions,
   run-2 static completion and ZERO. Use exact initial key sets, not counts.
4. Add InitialsIn and owner delivery. Compare full initial-start and boundary
   observations with the selected reference. Test same-unit immediate and
   cross-unit queued delivery, immutable payloads, cancellation and empty gates.
5. Change ordinary call entry to the three phases. Assert raw LinkIn is run-1
   only. Audit every production subscribe/link call site, including ZERO and
   predefined routing. Do not silently rewrite test demands to evade the gate.
6. Run complete core/JVM suites and formal checks. Then measure the latest
   authorized FULL/statics/aliases/16 GB/`1,1,2,...` project configuration,
   focusing first on conductor and Stirling. Reuse the saved legacy reports.
   No new project configuration or baseline rerun is part of this proposal.

Required cases include:

```text
saved record + empty demand             -> saved result, no live row/packet
same offer twice                       -> saved replay twice, live replay fresh-only
two actuals with one initial           -> both caller results, one callee start
empty emission + matching current FLOW  -> no current replay/subscription
rejected offer followed by accepted one -> no historical rejected-input activation
packed accepted offer                  -> preserve complete original actual
protection-only upgrade                -> keep fresh annotated effect
native must / reversed native / ND      -> original geometry and origin/layer rules
publication at every registration step  -> every authorized applicable pair found
run-1 / ZERO / predefined / unresolved  -> unchanged existing paths
```

The current five diagnostic tests establish baseline mechanisms only. They
do not already test the new runtime policy. Keep their old measured evidence;
add or update selected-policy assertions with explicit old/new expectations.

## 10. Measurement and limits

Record these aggregate counts without retaining per-fact diagnostic archives:

```text
call input offers
persisted replay invocations / candidates / matches / result memberships
demand lookup invocations / empty results / nonempty results
eligible live admissions / fresh deltas / stored groups / index postings
initial packets / offered keys / newly started keys
caller initial queries / callee initial queries (must be zero for InitialsIn)
native return-suffix entries / fresh post-statement outputs
```

Separate initial-key packets from old raw LinkIn counts. Remove the restricted
raw-input-presence contribution to `sawDemandInput`; do not guess its old input
layer from an initial's start layer. Keep outgoing-demand and stop counts
derived from their existing selected-summary stores. Run-1 raw input counters
remain meaningful on their existing path.

For N offers and M nonempty demand results, only M offers can now enter live
input accumulation and current-summary replay. Zero demand means no live row,
subscriber registration or callee packet for that input. Callee demand queries
are zero. Compared with the current runtime, the one emission query moves;
it is not a claimed twofold lookup reduction. Compared with naively adding a
caller gate while retaining receiver lookup, it avoids the second query.

Persisted replay can increase from fresh offers to all N offers. If nearly
all offers pass demand, little live work may disappear while native replay
grows. The current counters do not measure M or that tradeoff. The 2.42 million
conductor and 1.31 million Stirling nonfresh-offer bounds are not predictions
of removed packets or whole-project speedup.

This proposal can remove generic input merging on rejected routes, which is
relevant to Stirling's caller-admission hotspot. It does not optimize generic
mask merging on accepted routes. Measure native replay, live admission,
allocations, retained input rows and completed outputs separately. Report
every latest reached/complete/accepted run label and incomplete engine.
If replay growth offsets the saving, report it; do not silently add another
input-history cache or change the selected replay policy.

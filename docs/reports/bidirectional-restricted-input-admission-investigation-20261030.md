# Restricted input admission: causes and mitigation

Date: 30 October 2026. Runtime under review:
`edb2e06cdb17eecafbe03415236bf56c57910239`.
Status: investigation with five passing diagnostic tests. No production code
was changed. No new project analyzer command was run.

Latest measured reached / complete / accepted iterations:

| Project | Reached | Complete | Accepted | Status |
|---|---|---|---|---|
| conductor | run-4 | run-3 | run-3 | TIMEOUT |
| Stirling-PDF | run-6 | run-5 | run-5 | TIMEOUT |

Use the [closed campaign report](bidirectional-identity-owner-protection-performance-20261030.md)
for the project measurements. This note tests the proposed general design
changes. It does not assign the whole conductor regression to one mechanism.

## 1. Arrivals are not distinct facts or distinct initials

| Current partial engine | Input arrivals | New method initials | Nonfresh offer lower bound |
|---|---:|---:|---:|
| conductor run-4 | 4,856,738 | 28,965 | 2,417,368 |
| Stirling run-6 | 2,334,947 | 7,988 | 1,305,886 |

The lower bounds use input arrivals minus all accepted subscription deltas,
including control admissions. They count offers, not exact AP coordinates.
They do not mean that every remaining offer is necessary.

Three mechanisms explain why arrivals can greatly exceed initial starts:

1. Different producer statements can deliver the same call input. The caller
   storage can reject the repeated subscription, but the caller still sends
   the original input to the callee.
2. Different actual paths, marks, callers and stages can map to one method
   initial. Their caller answer routes can still be different.
3. Every normal call offer enters subscription admission before checking
   whether the callee demand can use it. Demand lookup currently occurs only
   after delivery to the callee. Native record replay shares this admission
   path with subscriptions to new summaries.

The current counters do not separate the last two populations. In particular,
`restrictedIntersections` counts emitted initial candidates, not lookup calls.
It cannot measure the fraction of offers with irrelevant demand.

### 1.1 A repeated input with no repeated producer output

```java
void caller(Box p, boolean b) {
    // Initial I = p.$/T.
    if (b) {
        p.f = new Box(); // At S1: I -> p.$/T, NORMAL.
    } else {
        p.f = new Box(); // At S2: I -> p.$/T, NORMAL.
    }
    blocked(p);         // At S3: both branch outputs arrive.
}
```

Assume no answer from `blocked` has arrived yet. S1 and S2 each store a fresh
output. Their producing statements differ. The same caller/ref/input reaches
the call twice. The diagnostic fixture uses the actual field exclusion
micro-edge; the root T survives the write in both branches.

```text
subscription offers:       2
fresh subscriptions:       1
callee links:              2
completed outputs at S3:   0
```

Post-S3 output deduplication cannot prevent these two submissions. There is
no completed S3 output yet. This example needs no static propagation or ND edge.

### 1.2 Different actuals with one initial

```java
Box get(Box p) {
    return p.f;
}
```

For a run-3 admission with limit 2, the diagnostic control uses:

```text
demand entry: p.[any]/FLOW
actual F1:    p.f.a.$/T        emitted I: p.f.*/FLOW
actual F2:    p.f.b.$/U        emitted I: p.f.*/FLOW

summary:     p.f.*/FLOW -> ret.*/FLOW
apply F1:    ret.a.$/T
apply F2:    ret.b.$/U
```

Both arrivals can reuse one method analysis. Both actual answer routes still
matter. Do not deduplicate caller inputs by the emitted initial alone.

## 2. The initial set and the actual-fact accumulator have different jobs

| Storage | Current key/content | Purpose |
|---|---|---|
| InitialFactStore | Canonical InitialAp identities | Start each method initial once, before boundary rules and work scheduling |
| MethodEdgeStore | Original premise, producing statement, complete annotated result | Admit fresh completed statement outputs |
| Caller AddedFactAccumulator | Full CallerRef and typed actual-fact group | Admit fresh actual input and replay saved/new answers |

The expensive Stirling mask walk is in the third storage, not the first set.
Removing the first set does not remove that walk.

Currently `addInitial` tests its set before `startAt`. `startAt` applies the
entry boundary rules and sends their results to the relevant instructions.
It does not first store the raw initial in the entrypoint's output row.
The control confirms that an initial has been started while the entrypoint
has no completed edge row. Repeating that initial does no boundary work only
because InitialFactStore rejects it.

Entry rules can change or kill the initial image. Backward analysis can also
start at several normal exits. A result after one such boundary is not a
complete record that the method initial has already been started.

The separate set can be replaced by an explicit start-admission bit owned by
MethodEdgeStore. That bit must be set before boundary effects or queueing. It
must also represent a started initial whose boundary kills every output.
Keep the current post-statement row meaning. Do not insert an unprocessed
initial as if it were a completed output.

This can unify storage ownership. It is not the main measured performance
fix. The larger target is unnecessary caller admission, replay and submission.

## 3. Selected call policy: persisted summaries, demand, current summaries

### 3.1 Saved records are still needed without new demand

```java
Box id(Box p) { return p; }
```

A previous run can retain the NORMAL record
`p.*/FLOW -> ret.*/FLOW`. With empty current callee demand:

```text
forward actual:   p.$/T       native result:   ret.$/T
backward actual:  ret.$/T     reversed result: p.$/T
```

The diagnostic tests confirm both replay routes. Therefore, an empty demand
can omit new method analysis and standing subscriptions to new answers. It
cannot omit native and reversed record application. Keep ZERO/REACH control
and the backward-ZERO publication rule as separate cases too.

Make record replay an explicit operation. Do not call the whole subscription
path only to obtain it. The selected policy replays persisted summaries on
every offer and relies on existing output deduplication. It keeps no native-only
input history. Temporary seen-record/view sets stay local to each replay.
Repeated return processing is an explicit cost tradeoff to measure.

### 3.2 Applicability does not authorize current-run work

The following current policy/normalization control passes:

```text
run-3 demand: p.[any]/FLOW -> ret.[any]/FLOW

another actual: p.$/T
  emitted initial: p.$/FLOW
  raw NORMAL summary used by the control: p.$/FLOW -> ret.$/FLOW
  stored/publication form:                p.*/FLOW -> ret.*/FLOW

provided actual: p.*/FLOW
  initial emission from demand: empty
  match with that normalized publication: nonempty
```

The control establishes applicability, not necessity. It is not evidence that
the caller needs this current-run result. The selected policy applies saved
normal summaries first. If the actual input then fails the current demand
admission test, it must not use current-run summaries or retain a subscription
to them. A summary inferred for another input cannot bypass this gate.

The previous version of this note proposed a second test over hypothetical
normalized summary premises. That proposal is withdrawn. Do not enumerate
possible initials or add a new summary-compatibility lookup.

For restricted runs, the selected logical order is:

```kotlin
fun handleCallInput(callee: MethodKey, ref: CallerRef, actual: Facts) {
    // Same-direction records and opposite-direction read views.
    // Use the original actual input, with all existing annotations.
    applyPersistedSummaries(callee, ref, actual)

    // The same bounded-input policy and demand lookup as initial emission.
    val initials = emitFromCurrentDemand(callee, limitForInitialEmission(actual))
    if (initials.isEmpty()) return

    // Register before replay to preserve the existing delivery protocol.
    subscribeAndReplayCurrentSummaries(callee, ref, actual)
    submitInitials(callee, initials)
}
```

These are logical operations, not new runtime APIs. The persisted store keeps
eligible NORMAL summaries from earlier completed runs, in both native
directions; it is not limited to the immediately preceding run. Replay the
whole original offer each time. Keep native must-record demotion and existing
output/observation admission. Current-summary replay remains fresh-only.

An initial already started by the callee is still a demand match. Do not use
the callee's initial-deduplication result as this gate. A new caller/ref can
need answers even when the method initial is already active.

The change applies to restricted runs. Run-1 keeps its request protocol.
Run-2 demand lookup includes the existing virtual static completion; run-3
onward uses local demand. ZERO has its implicit demand and existing control
route. The gate must preserve these cases and full ND caller premises.

This modifies current-summary admission: the current implementation can apply
an applicable current summary before checking this caller input's demand.
The selected behavior forbids that when demand admission is empty. Persisted
replay also changes from fresh-only input to every offered input. Field,
mark, cleaner, alias, normalization and layer transfer rules stay unchanged.
The correctness target is preservation of required demand and observations,
not equality of every old callback outside current demand.

### 3.3 Pass the completed admission result to the callee

The caller must send the final canonical initial keys from the lookup. Do
not send only candidate demand rows: the callee would still need to compute
initial emission from the actual input. The demand and run policy are fixed
for this run, so the callee does not need to repeat the query.

```kotlin
// Proposed payload. Copy the collection; the caller cannot change it later.
class InitialsIn(val callee: MethodKey, initials: Collection<InitialAp>) {
    val initials: List<InitialAp> =
        Collections.unmodifiableList(ArrayList(initials))
}

// Caller, after persisted summaries and the nonempty demand gate:
subscribeAndReplayCurrentSummaries(callee, ref, actual)
sendRequired(InitialsIn(callee, initials))

// Callee owner:
fun handle(event: InitialsIn) {
    val method = analyzer(event.callee)
    for (initial in event.initials) method.addInitial(initial)
}
```

`addInitial` retains its existing start-admission gate and start-fact
construction. It runs boundary rules only for an initial not already started.
The callee does not limit the original input, scan its leaves, or query demand
again. No second check of demand eligibility is needed.

The event targets the full callee MethodKey and belongs to the same run.
Its initial keys come from that run's shared AP manager and admission policy.
Use the existing required-delivery and cancellation rules; an accepted batch
must not disappear before the callee processes it.

Keep the original actual Facts, full CallerRef, layers and stage on the caller
side for summary matching and application. They are not needed in the callee
initial-start payload. Two callers can send the same initial; the callee starts
it once while both caller subscriptions can receive answers. This change
removes a repeated lookup, not caller separation or initial-start admission.

## 4. Mitigation order

1. Apply persisted normal summaries before the demand gate, on every offer.
   Preserve their original input, native/reversed handling and return effects.
   Keep no persisted-replay input history.
2. Reuse initial-emission demand admission before current-summary replay and
   subscription allocation. On an empty result, skip all current-summary work
   and raw callee submission for that input.
3. Compute initial emission once and pass the small emitted initial set to
   the callee. Keep one callee-owned start gate. For eligible subscriptions,
   retain full caller/ref/layer/stage and actual geometry; do not replace the
   actual by its emitted initial. Avoid repeated raw links after admission
   rejects unchanged input, including the branch example.
4. Remove full accumulated-mask reconstruction for a no-op actual merge.
   This is needed separately: a fresh-link gate alone leaves Stirling's 75%
   caller-admission hotspot in place.

The resulting responsibilities are:

```text
caller:
  apply saved normal summaries
  run initial-emission demand lookup once
  stop this current-run route if its demand result is empty
  otherwise register/replay current summaries and submit emitted initials

callee:
  consume the completed admission result without another limit or lookup
  admit each canonical initial once, before boundary rules
  run the method and publish answers as now
```

The detailed [implementation proposal](../design/bidirectional-selected-call-policy-implementation-20261030.md)
defines the source changes, transport, proofs and test gates. Before changing
code, prove the selected gate preserves demand-required results and
observations after persisted-summary application. Include FLOW normalization,
full ND origins, ZERO controls and run-2 static completion. Move the unchanged
complete emission query, keep native must-record demotion, and check repeated
native replay against existing output/observation admission. Do not close a
proof gap by restoring the withdrawn compatibility test or silently changing
transfer rules.

Measure offers by: empty demand admission; nonempty demand admission; new
callee initial; repeated started initial. Separately measure native record
candidates, matches and resumed outputs. The current saved counters cannot
determine the project-wide hit rate of the new demand gate.

## 5. Validation

[RestrictedSubscriptionEligibilityTest](../../core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/RestrictedSubscriptionEligibilityTest.kt)
has five passing tests. They use production admission, matching, normalization,
call processing and record replay. The fixture is finite; the tests are not
new project performance measurements or a proof of the whole analyzer.

```sh
cd core
./gradlew :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.RestrictedSubscriptionEligibilityTest
```

The [evidence receipt](data/bidirectional-restricted-input-admission-20261030.json)
contains test/source hashes, observed controls and the current project count
bindings. The normalized-publication test records current applicability only;
it does not require a subscription under the selected policy. No production
transfer, field, mark, alias, layer, demand or stop rule was changed.

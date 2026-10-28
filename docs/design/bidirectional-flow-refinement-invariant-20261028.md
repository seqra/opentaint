# When a marked execution can use FLOW

Date: 28 October 2026. Status: **not selected**. Runtime code is unchanged.

The selected approach has returned to the conservative
[reader mark rule](../../spec/demand-storage-lookup.md#51-reader-mark-rule):
keep a reader's conclusion mark, or obtain it from a marked predecessor
through a FLOW-only suffix. Do not implement this document's body-reuse
certificate, residual classifier or internal-effect footprint in this
iteration. Its exact lookup shortcuts remain compatible with the selected
rule and are specified in the lookup document.

This proposal follows the accepted wrapper counterexample in the
[policy review](bidirectional-demand-policy-review-20261028.md). It keeps
ordinary AP emission, runtime FLOW application and the complete demand relation.
It does not select the rejected unconditional `mapped ; FLOW` prohibition.

There are no new measurements. The last fixed campaign used runtime
`53991b7483b062b0287152130cbbbfc87623093b`:

| Project | Reached | Completed | Accepted forward |
|---|---|---|---|
| OWASP | run-12 | run-11 | run-11 |
| conductor | run-4 | run-3 | run-3 |
| thingsboard | run-2 | run-1 | run-1 |
| Stirling-PDF | run-5 | run-4 | run-3 |

## 1. The invariant

For a fixed method/context, query geometry, mark T, direction and field limit:

> A separate T execution is unnecessary if every effect it can contribute
> is already supplied by a retained FLOW execution, instantiated with the
> same actual T at the same caller boundary, or by an independently retained
> execution which handles that effect.

Effects include returned relations, source hits, rule observations, protected
dependencies and the guidance needed by the next run. Equal final geometry
alone is insufficient. Reaching the caller boundary before a concrete gate
matters: a caller can instantiate a returned FLOW answer, but cannot repair
an unpassed concrete gate inside the method.

Call this **FLOW replay for T**. It is specific to the queried mark and geometry.
A method can satisfy it for T but fail it for U, or satisfy it for one return
region but fail it for another.

An independently retained execution must actually be scheduled under the
ordinary protocol, or served by a valid retained record/model. Two omitted
marked executions cannot cite one another as their only coverage. Replay
witnesses must end at a retained service.

The useful sufficient form is:

```text
All relevant T effects are either:
    certified transport/effects replayed by retained FLOW,
or:
    explicit marked residuals, handled by a retained marked execution.

No unhandled residual or internal marked obligation can affect this query.
```

A residual is an effect for which FLOW replay is not proved. It is not a
new fact annotation or grounding-support label. Unknown cases remain residual
or unknown; absence of evidence is not a replay certificate.

## 2. Two different work reductions

### 2.1 Avoid duplicate lookup; preserve the exact C2 initial set

For one actual full T and one rightmost FLOW target geometry q, only two
classes of initial key can result:

```text
AP.emit(q/FLOW, actual T)  // shared FLOW
AP.emit(q/T, actual T)     // compatible marked entry, if a prefix witnesses it
```

A GROUP entry that accepts actual full T also preserves that actual T.
Another full U does not produce an extra T key merely because its group is equal.

Therefore:

```kotlin
val possibleTKeys = existingEmit(targetWithActualMark, actual)
if (initials.containsAll(possibleTKeys)) skipColorSearch()
else if (hasCompatibleColorBefore(method, target, actualMark))
    initials.addAll(possibleTKeys)
```

The existential search stops at its first compatible mapped witness. It does
not enumerate all output colors, original input marks or source endpoints.
Check each complete target geometry separately. An EXACT key is not covered
by an existing STAR key; different paths, E and tails can produce other keys.

This reduction changes lookup work only. An already admitted T key still
starts or shares its existing marked execution. No new replay theorem is
needed to omit duplicate candidate work.

### 2.2 Avoid a genuinely new marked body execution

This is stronger. It needs the invariant in section 1 and a new admission
proof. Keep the conceptual C2 initial set unchanged and place the optimization
at the boundary that schedules a new initial:

```kotlin
for (initial in demand.initials(method, boundedActual)) {
    when {
        alreadyAdmitted(initial) -> Unit
        canReplayByAdmittedFlow(method, initial) -> countFlowReplayed(initial)
        else -> addInitial(initial)
    }
}
```

The FLOW peer must be legal under the existing incoming demand and actual
input, and must already be admitted or scheduled in this run. Do not fabricate
a FLOW query. Keep the actual caller subscription, so ordinary matching and
summary application still instantiate its T.

This does **not** assert that the same marked body seeds are processed. The
old exact-initial-set/queue equivalence proof cannot justify it. The new proof
is boundary simulation of the omitted work. The existing specification's
warning against deleting an unprocessed marked seed remains valid unless
this stronger certificate has been established.

A conservative first implementation uses a legal peer with the same complete
initial base, path, tail and E, differing only in the mark. Keep EXACT/MUST
initials and unsupported ANY/correlation cells on the existing path. A broader
peer is possible only with an additional AP application proof; spatial coverage
alone does not establish it.
Start with ordinary singleton, non-ZERO demand entries in incoming backward
run-2. Keep direct source/sink seed starts and the balanced backward-ZERO
protocol unchanged. Later forward/ND cases need their own admission proof.
The first executable transfer kernel handles FULL marks and the STAR peer
cell. GROUP and unsupported tail cells retain the existing marked path.

## 3. Transport and residual effects

Classify effects before guidance normalization, using the current raw AP
relation and its applicable binding boundary.

| Effect | Decision |
|---|---|
| Ordinary copy/read/write | Replayable only in the proved geometry, layer, cut and caller-binding cells |
| `p/T -> C.f/T` with a valid unprotected FLOW counterpart | Does not introduce a new T need by itself |
| `p/T -> C.f/U`, T different from U | Residual output U; a diagonal FLOW row cannot perform the mark change |
| `ZERO -> C.f/T` | Residual source output T; no generic FLOW writer can create that mark/source hit |
| Same-T rule assignment | Protected under the existing rule; retain its marked obligation unless independently handled |
| A selected cleaner's surviving T | Residual if FLOW cannot reproduce the survivor and its protection |
| A restored `T -> U -> T` cycle | Residual despite its final diagonal shape |
| Insufficient FLOW tail, E, mx or layer coverage | Residual or unknown |
| Internal mark-sensitive observation or an incomplete rule footprint | Keep T until the obligation is proved covered |

Use the existing application/coverage tests: same complete scope and binding,
supported initial/output geometry, sufficient layer, permitted suffixes and
T not excluded by the covering FLOW. Do not substitute input/output mark
equality for those tests. A DEMAND FLOW cannot replace a NORMAL marked proof.

The generic service can be either an ordinary FLOW body with retained paired
C5 permission, or an applicable normal FLOW record. It need not already be a
NORMAL run-1 summary. Do not discard generic FLOW paths from the closure when
they are the witness for replay.

### 3.1 Cleaners are mark-specific, not a blanket rejection

A complete selected-T kill can be replayable:

```text
concrete T execution:  T -> no result
FLOW execution:        FLOW -> FLOW excluding T
caller instantiation: instantiate T -> no result
```

This requires the whole relevant concrete region to be killed and no omitted
observation before that kill. It does not prove that every selected-T cleaner
is safe.

For `removeTBelow(x)`, concrete root T can survive and become protected.
The FLOW branch can exclude T. That survivor is a residual. A selected U
cleaner can be transparent for T when its actual FULL/GROUP selection does
not cover T; the resulting FLOW exclusion still admits T.

Do not screen a selected cleaner using only the path written in the rule.
The current selected nonstatic FLOW cleaner can exclude T across the same
base without a spatial test, while concrete cleaning uses spatial cases.
A same-base cleaner written on another field can therefore remain relevant.
Use the actual compiled FLOW effect footprint and concrete cleaner contract.

## 4. A demand-directed negative test

For the skipped static graph, a useful export-side test is:

```text
NeedExport(M, Q, T) =
    a residual visible inside this method boundary can output T
    and a retained compatible FLOW suffix connects it to query target Q
```

Only the queried output T is needed. There is no need to enumerate the
residual's input marks or all colored static compositions.

```kotlin
fun mayNeedConcreteExport(M, Q, T): Decision {
    if (!rawEffectClassificationComplete(M, Q)) return UNKNOWN
    if (directResidualCanEmitThisInitial(M, Q, T)) return NEED_T

    val pending = matchingFlowSuffixSources(M, Q)
    val visited = CompleteGeometrySet()
    while (pending.isNotEmpty()) {
        checkpoint()
        val current = pending.removeFirst()
        if (!visited.add(current)) continue

        for (row in incomingLocalWAndVisibleB(M, current)) {
            if (!mayJoinExistingGeometry(row.to, current)) continue
            when (classifyForActualT(row, T)) {
                RESIDUAL_MATCHING_T -> return NEED_T
                UNKNOWN -> return UNKNOWN
                REPLAYED_BY_FLOW -> offerRetainedFlowPredecessor(row, pending)
                IRRELEVANT -> Unit
            }
        }
    }
    return NO_EXPORT_RESIDUAL
}
```

`REPLAYED_BY_FLOW` must supply the retained FLOW counterpart, including its
ordinary T admission/exclusion law. A backed diagonal row is not a reason
to stop: an earlier source or mark change can still feed it.

W/R are scoped to the complete MethodKey. B uses the existing per-label
owner visibility. Include own B, inherited B, lost/intermediate writers and
the completed actual-caller-bound W inventory. Do not repeat caller binding
inside this query. Do not use every globally reached static mark as a local
residual: a source outside a getter can be handled by its caller.

This search preserves the existing primitive geometry-composition contract.
It does not assume that arbitrary AP applications can be reassociated.
Cycles use complete geometry state; negative results are valid only after
the whole search and evidence snapshot are complete.

## 5. Export absence is not the full certificate

W/B/R summaries omit effects which leave no useful method summary. A source
hit, sink, cleaner, negative CM condition, ND guard or end-fact GEN can still
require T inside the method. A log of fired rules alone can omit an applicable
guard that did not fire under shared FLOW.

The full decision therefore requires:

```kotlin
fun canReplayByAdmittedFlow(M, I_T): Boolean =
    legalFlowPeerAlreadyAdmitted(M, I_T) &&
    evidenceSnapshotComplete(M) &&
    completeRelevantEffectAndObservationFootprint(M, I_T) &&
    mayNeedConcreteExport(M, I_T.geometry, I_T.mark) == NO_EXPORT_RESIDUAL &&
    allInternalMarkedObligationsCovered(M, I_T) &&
    genericApplicationAndHandoffRetained(M, I_T)
```

The footprint must account for effective selected rules, positive/negative
conditions, ND inputs, sources, cleaners, entry/exit and call-site effects,
source hits, primitive mark policy and relevant callee/model effects. For an
unknown or unmaterialized owned rule scope, use the existing marked path.

Use already built effective forms or conservative provider metadata. Do not
eagerly bind every rule in the project for a new census. Footprints can be
small immutable effect/position/selector keys; do not retain Facts, input
histories, origin products or another live writer directory.

A safe first version can certify pure read/copy cones and complete trusted
calls. It can keep T whenever another relevant effect is not classified.
A finer version can prove a check on another region independent, using the
actual alias and rule-dependency footprint. A method-wide `hasCM` test is
safe as a conservative rejection, but can reject many useful pure cones.

Do not check only the spelling `CM(T)`. Input T can cause `T -> U`, then an
internal `CM(U)` sink with dead output. That entire effect chain matters even
if no marked return row remains.

### 5.1 Do not replace K body walks with K equally large proof walks

Try an all-mark transport certificate for a pure cone first. Once its complete
effects and binding cells are proved transparent for every supported mark,
reuse that certificate for T1, T2 and the other actual marks. This needs one
uncolored cone check, not enumeration of all marks.

For a selective cone, a certificate can describe a mark domain, for example
marks not selected by a particular U cleaner. Use existing FULL/GROUP selector
tests. Only remaining queries need the per-actual-mark residual search.
Do not use a universal certificate when a source, protected result or unknown
effect has only been checked for one mark.

For K marks transported through L body steps, the certified pure case can
reduce K concrete body walks to one FLOW body walk, plus certificate and
ordinary per-caller application work. The best-case body work changes from
`O(K*L)` to `O(L)`; delivery of K actual marked answers is still required.
This is a complexity example, not a measured project speedup.

## 6. Principal examples

### 6.1 Source outside a pure getter: omit the new T body

```java
void caller() {
    C.f = sourceT();
    sinkT(get());
}
Object get() { return C.f; }
```

At get, the retained service is `C.f/FLOW -> ret/FLOW`. No relevant residual
is inside get's method boundary. Its backward FLOW body returns the C.f/FLOW
dependency; caller application to actual ret/T produces C.f/T. The caller
then reaches the preceding real source. No extra get/T body is needed under
the replay certificate.

### 6.2 Copy through a static: a diagonal writer need not block

```java
Object echo(Object p) {
    C.f = p;
    return C.f;
}
```

Retain FLOW W `p/FLOW -> C.f/FLOW`, FLOW R `C.f/FLOW -> ret/FLOW`, and their
generic paired guide. Any relevant unprotected diagonal marked writer with
proved matching FLOW coverage introduces no residual. The backward FLOW
answer reaches p/FLOW. Its caller instantiates p/T.

Do not require “no static writer.” Require transport coverage of the writer.
If its raw tail/E/mx/caller cell is unsupported, keep T instead.

### 6.3 Source inside the wrapper: keep T

```java
Object wrap() {
    seedStaticT(); // configured void source: assign T to C.f
    return C.f;
}
```

The local `ZERO -> C.f/T` producer is a residual. The FLOW reader suffix
connects it to ret. `NeedExport(wrap,ret,T)` is true. A FLOW backward initial
cannot fire the source's concrete T reverse gate; keep ret/T.
Calling the source through helpers inside wrap does not make it external:
the joined caller binding must preserve that residual at the wrapper boundary.

### 6.4 Accepted mark-changing counterexample: keep U

```java
Object wrap(Object p) {
    C.f = p;
    C.g = convert(C.f); // CM(T) -> assign U to a fresh result
    return C.g;
}
```

`C.f/T -> C.g/U` is a residual output U. The FLOW suffix to ret makes
`NeedExport(wrap,ret,U)` true. Keep the marked U initial so the reversed
conversion can reach T. A diagonal FLOW answer cannot replace this relation.

### 6.5 A selected cleaner

```java
Object keepT(Object p) {
    removeU(p);
    return p;
}
```

For a full T not selected by the U cleaner, generic FLOW excluding U can
still carry T. This can satisfy the certificate. It need not satisfy it for U.
For a whole-region selected-T kill, FLOW excluding T can represent the empty
T result. A below-only T cleaner with a surviving protected root fails the
certificate and keeps T.

### 6.6 A hidden observation: do not infer safety from W/B/R

```java
Object checkAndReturn(Object p) {
    sinkT(p);
    return unrelated;
}
```

The sink need not leave a useful p/T-to-return relation. A summary-only
negative search cannot justify removing the p/T execution. The observation
must have an independently retained route, or the footprint keeps T.

## 7. Evidence, ownership and lifecycle

Normalized static guidance is insufficient to establish replay. It clears
FLOW mx and does not retain the raw layer or `nonSubsumable` mask. A normalized
`T -> T` row can have come from a protected assignment or cleaner survivor.

Classify using raw evidence before normalization. Preserve conservative
classification upgrades when equal rows gain protection. Do not infer lost
writer properties from their thin Pattern keys after the flags are gone.
Only claim a FLOW counterpart that remains available through the selected
generic demand or normal-record route.

Seal the evidence after counted engine work and joined actual writer binding
finish, before their borrowed inputs release. A method queue alone being
empty is insufficient. Partial or cancelled classification cannot issue a
negative certificate. The actual replay execution uses the current run's
strong field rules, direction and limit, not the old run-1 weak field policy.

No new semantic fact flag, grounding support, request archive, mark inventory,
soft-reference rewrite or IR storage change is selected here. Query decisions
are snapshot/method/geometry/mark specific. Add caller layer/protection to a
cache key only if the certificate depends on them; preserve their ordinary
binding metadata in all cases. Caching is optional and not the invariant.
A certificate shared by several actual arrivals must cover every supported
actual-input cell represented by its key. Otherwise include the differing
actual tail/E/layer/protection scope in the decision. Do not reuse a proof
for one actual input as a proof for all arrivals with a similar field name.

## 8. Proof and measurement obligations

The local [FlowOnlyCertificate model](../../spec/lean/proposals/demand-storage-next/FlowOnlyCertificate.lean)
constructs a last-residual decomposition: a marked result either comes from
an actual marked boundary input through FLOW, or from a last residual through
FLOW. Excluding the latter gives an executable generic transport witness.
It also states the separate hidden-observation obligation. Its five audited
declarations are axiom-free. This graph theorem does not prove completeness
of a JVM footprint or the AP replay adapters.

The separate [FlowRefinementInvariant model](../../spec/lean/proposals/demand-storage-next/FlowRefinementInvariant.lean)
adds 19 axiom-free audits. It proves a bounded local transfer law, then an
ordered-program replay theorem including protection and events. Its admission
certificate requires the legal admitted FLOW peer, complete relevant footprint
and retained application/handoff services. Controls accept copies, unrelated
selected operations and complete T kills; reject source generation, cross-mark
change, protected survivors, relevant checks and unknown operations.

The [graph receipt](../../spec/lean/proposals/demand-storage-next/flow-only-certificate-checks.json)
and [transfer receipt](../../spec/lean/proposals/demand-storage-next/flow-refinement-invariant-checks.json)
record 24 combined audited declarations. They do not prove the production
metadata adapter or whole-JVM equivalence.

Required adapters include ordinary AP matching/application, supported initial
and tail cells, E/mx/layers, protection, type/primitive filters, alias closure,
complete rule effects, caller bindings and next-run handoff. Preserve backward
ZERO/source-hit routes and all actual T gates; do not relax a gate to make
FLOW replay succeed.

Run controls should include getter/echo positives, source outside/inside a
wrapper, the accepted conversion, protected same-mark and cycle cases,
complete/partial cleaners, hidden observations, missing metadata, and late
raw protection upgrades. No runtime test or project run is claimed here.

Measure exact-lookup savings separately from omitted marked bodies. Record
queries, first compatible witnesses, covered-key stops, replayed initials,
residual/unknown reasons, retained generic guides and source/report equality.
There is no measured two-times saving yet; the residual share of the workload
must be counted before estimating the benefit.

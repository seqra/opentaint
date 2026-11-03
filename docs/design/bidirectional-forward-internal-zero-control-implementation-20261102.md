# Draft implementation: forward internal ZERO control

Date: 2 November 2026. **Status: DRAFT / UNSELECTED.**
Superseded on 3 November by
[NORMAL ND contributor retention](bidirectional-normal-nd-contributors-implementation-20261103.md).
Do not implement this ZERO-control proposal.

Use [forward-internal-zero-control.md](../../spec/forward-internal-zero-control.md)
as the draft contract. Follow
[impl-proposal-guide.md](../../spec/impl-proposal-guide.md) and
[proof-guide.md](../../spec/proof-guide.md).
Language: ASD-STE100 Simplified Technical English.

This draft changes a major analysis policy. It permits an actual forward
ZERO to enter an internal block without a local ZERO demand. The original
method ZERO must already be admitted. This draft is not a technical-only
optimization. It does not have project acceptance results.

## 1. Problem and proposed behavior

```java
void method(Request request) {
    // Entry metadata assigns REQUEST to request.
    Cookie[] cookies = request.getCookies();
    // Source: CM(this,REQUEST) assigns DATA to the returned array.
    String param = null;
    while (again()) {
        param = cookies[index()].getValue();
        if (match(param)) break;
    }
    Session session = request.getSession();
    // Independent source: ZERO assigns SESSION to the returned object.
    session.setAttribute(param, "value");
    // Sink: CM(this,SESSION) AND CM(arg0,DATA).
}
```

The native exact-array control has these run-3 inputs:

```text
method ZERO:                       admitted
actual AL input:                   Reach, NORMAL
AL local C2 for ZERO:               empty
AL local C2 for param.$/DATA:       param.$/DATA, NORMAL
saved AL relation:                 ZERO -> session.$/SESSION, NORMAL
permission for the session source: present
```

The current AL rejects ZERO. Its DATA input cannot make the independent
SESSION source execute. Saved AL replay emits SESSION at the AL exit. It
does not send SESSION to the earlier sink instruction inside AL. The
complete sink cube is therefore absent.

The proposed behavior is:

```text
admitted method ZERO
  -> actual forward control path
  -> actual Reach offer at AL
  -> admit local ZERO
  -> execute existing AL instructions and permitted source actions
  -> join SESSION and DATA at the real sink
  -> apply the unchanged Target C5 rule
```

Do not create ZERO at every block. Do not use a DATA input as evidence
that ZERO reached the block. Do not generate another source permission.

## 2. Semantic change ledger

| Part | Current behavior | Draft behavior |
|---|---|---|
| Restricted forward internal ZERO C2 | Requires a local ZERO or Target entry demand | Also accepts a genuine Reach offer derived from the admitted original method ZERO |
| Internal ZERO identity with no local C5 result | Stops at the internal boundary | Returns through a private live control interface |
| Internal ZERO identity already admitted by C5 | Uses the ordinary summary path | Same |
| DATA C2 and DATA C5 | Uses complete AP demand rules | Same |
| Target C5 | Uses complete paired Target demand | Same; no Reach probe grants a Target |
| Public method ZERO admission and C5 | Uses current method demand | Same |
| Backward admission, completion, and saved replay | Uses current rules | Same; private control returns are not persisted |
| No-loop methods and run-1 | Use current execution | Same |

Forward execution can now perform more current block work. It can produce
additional source facts and complete a sink cube that the old internal
ZERO gate missed. Those DATA and Target results still use their ordinary
rules. Do not describe the change as equal per-run observations.

Unchanged admission and backward policy do not mean unchanged event or
work counts. A newly reached real call can offer another input, which the
existing global C2 can legitimately admit. Additional ordinary C5-admitted
AP rows can also change later backward inputs. The bypass ControlExit is
not persisted. No AP store, read API, or permission rule changes.

## 3. Keep the control interface separate from AP summaries

A C2-only change is insufficient. An admitted local ZERO can reach the
block exit, but ordinary C5 can reject its `ZERO -> ZERO` result. Then no
actual Reach reaches the next block.

Do not solve this by adding unrestricted ZERO rows to `RunSummaryStore`,
`PublicationIndex`, `PersistentRecordStore`, or the demand handoff. Such
rows would add new native backward replay authority. This rule applies
only to the bypass completion. An ordinary C5-admitted AP row can still
be stored and persisted. New current execution can produce legitimate
new AP derivations; do not suppress them.

Use a private, current-run control return instead:

```kotlin
// Transport metadata. This is not a Publication or a Record.
data class ForwardControlExit(
    val scope: BlockScope,
    val exit: PortId,
    val layer: Layer,
)

// A parent completion key keeps the complete bound original.
data class ForwardControlCell(
    val child: BlockId,
    val exit: PortId,
    val original: PremiseKey,
    val layer: Layer,
)
```

The control interface has no field path, mark, exclusion, source action,
or report ID. It is not visible to AP summary lookup, native record lookup,
static completion, or `acceptsTarget`.

## 4. Method admission and actual path evidence

`MethodBlockRuntime.start` already runs after the original method initial
was admitted. Record that event once:

```kotlin
private var admittedMethodZero = false

// Called by the existing root routing hook, after root.addInitial.
fun start(node: CommonInst, original: InitialAp, value: Facts) {
    if (forward && original.isZero) admittedMethodZero = true
    existingStart(node, original, value)
}
```

The Boolean alone is not an offer. The actual input and its exact local
link must also exist:

```kotlin
fun canEnterControl(link: LocalLink, actual: Facts): Boolean =
    config.restricted && forward && admittedMethodZero &&
        link.original.isZero && actual is Reach
```

Require the actual offered link to have a ZERO original. The generic
runtime domain can also represent nonzero-origin Reach, so the root flag
and Reach type are not sufficient. Keep the complete bound original in
the link and in every returned control cell. Do not replace another
supplied original with ZERO. Do not accept a fabricated Reach from a
DATA offer.

The witness is the existing root admission plus the actual routed input.
It is not a new mark, fact annotation, GroundingSupport object, or seed.
A normal saved control transfer can supply an actual Reach through its
existing native application. It still needs a real incoming link.

## 5. Internal entry pipeline

Change `MethodBlockRuntime.offerChild`. Keep saved AP and saved Target
replay first. Add live control replay at the same actual input boundary.
Then perform ordinary C2 and the proposed ZERO exception:

```kotlin
fun offerChild(parent, child, target, original, actual, arrival) {
    val scope = exactChildScope(parent, child, arrival)
    val entry = entries.getOrCreate(scope)
    val link = LocalLink(parent.scope, scope.entry, original, actual.layer, scope)

    replaySaved(entry, link, actual)        // Existing policy.
    replayLiveControl(entry, link, actual) // Current-run control returns only.

    val ordinary = entry.demand.admission(actual, policy)
    val initials = ordinary.initials.toMutableSet()
    if (canEnterControl(link, actual) && initials.none { it.initial.isZero })
        initials += AdmittedInitial(ap.zero, actual.layer)
    if (initials.isEmpty()) return

    val state = entry.ensureState()
    admitActualTarget(entry, target, original, actual)
    entry.links.offer(link, actual)
    reserveWorkIfLocalDeliveriesExist(entry)
    initials.forEach(state::addInitial)
}
```

This is pseudocode for the restricted path. Keep the current run-1 branch.
Keep the current normal-J late-target replay and the empty-region identity
adapter. Keep actual method-start handling and source rules in their
existing owners.

Keep an existing ordinary C2 ZERO admission unchanged. Only the inherited
branch adds `AdmittedInitial(ap.zero, actual.layer)`. A DEMAND Reach must
start this local ZERO as DEMAND. Otherwise, its generated mark can lose
the ZERO contributor layer inside a mixed ND cube and produce a wrong
NormalTarget. Keep the actual input and `LocalLink.layer` unchanged too.
The existing parent composition combines input and result layers.

Do not allocate all block states when method ZERO arrives. Allocate a
state only when an actual input reaches its interface and is admitted.

## 6. Internal completion pipeline

Keep ordinary normalization and complete C5 first. Only a rejected
internal ZERO identity may use the private fallback:

```kotlin
fun retainInternal(exit, original, raw) {
    val normalized = existingNormalizeAndValidate(original, raw)
    val admitted = demand.intersect(exit, normalized.original, normalized.value, policy)
    if (admitted.isNotEmpty()) {
        existingStoreAndPublish(exit, normalized.original, admitted)
        return
    }
    if (original.isZero && raw is Reach &&
        binding.tryReturnLiveControl(exit, original, raw)) return
    // Existing rejection. No unrestricted summary is stored.
}
```

The proposed binding hook is narrow:

```kotlin
interface BlockRuntimeBinding {
    // false outside this selected, actual forward control lane.
    fun tryReturnLiveControl(exit: PortId, original: PremiseKey, actual: Reach): Boolean
}
```

The method runtime must validate method ZERO admission, forward direction,
actual local execution, and the preserved original. Borrow its existing
standing input links and require at least one matching actual ZERO-origin
Reach offer. A scope flag alone is not that input witness. Return false
when the witness is absent. A leaf emits a return only after its existing
physical transfer or empty identity completes.
An ancestor emits a return only after its genuine child completion.

The root has no fallback. It retains the current method C5 rule. DATA
from ZERO and every Target still require their current complete paired
rows. In particular, do not test Target permission by substituting
`Reach.DEMAND` into C5.

## 7. Live storage and replay

Keep two small ledgers in each existing runtime entry:

```kotlin
class Entry {
    val liveControlExits = linkedSetOf<ForwardControlExit>()
    val completedControlCells = linkedSetOf<ForwardControlCell>()
    // Existing DATA stores, local inputs, and block state stay unchanged.
}
```

Use existing standing local inputs. Do not add another raw input history:

```kotlin
fun returnLiveControl(entry, exit, original, result: Reach) {
    checkForwardActualControl(entry, original, result)
    // The binding calls here only after it found actual matching input links.
    val returned = ForwardControlExit(entry.scope, exit, result.layer)
    if (!entry.liveControlExits.add(returned)) return
    entry.links.forEachInput { link, actual ->
        if (canEnterControl(link, actual))
            deliverControl(link, returned, actual as Reach)
    }
}

fun replayLiveControl(entry, link, actual) {
    if (!canEnterControl(link, actual)) return
    for (returned in entry.liveControlExits)
        deliverControl(link, returned, actual as Reach)
}
```

Compose the layer by the existing ZERO identity law. Preserve the complete
parent original, exact child, and exact exit:

```kotlin
fun deliverControl(link, returned, actual: Reach) {
    val result = actual.withLayer(actual.layer or (returned.layer == DEMAND))
    val parent = entries.getValue(link.parent)
    val cell = ForwardControlCell(link.child.block, returned.exit,
                                  link.original, result.layer)
    if (!parent.completedControlCells.add(cell)) return
    queue { routeCompleted(parent, layout[link.child.block], link,
                           returned.exit, link.original, result) }
}
```

`routeCompleted` remains the common physical and logical port adapter.
Its normal-J expansion, empty BL identity, nested ancestor return, typed
exception outlet, and original-method finalization stay unchanged. Do not
choose one representative physical route. Do not add a route to an
unvisited block.

The ledger is finite for a finite layout: exact live scopes, exact exit
ports, existing originals, and two layers. It does not enumerate field
paths or marks. Clear it with the existing runtime entries after idle.
Do not export it from freeze, `scopedSummaries`, `scopedTargets`, or the
handoff builder. It cannot add a backward record or initial.

## 8. Loop observation and complete ND behavior

Keep consumer scope and family labels. A pure control projection needs
the same actual original and Reach evidence as live routing:

```kotlin
fun observedControlInitials(original, actual): Set<AdmittedInitial> =
    if (forward && admittedMethodZero && original.isZero && actual is Reach)
        setOf(AdmittedInitial(ap.zero, actual.layer))
    else emptySet()
```

This projection does not create an actual input. Do not infer its original
from the root flag or block scope. Do not project ZERO from a DATA query.
Keep an ordinary C2 ZERO result unchanged before adding the inherited one.

`LoopOutputRestriction` already bypasses every `appliedValue is Reach`.
No production growing-DATA observation can therefore need this projection
under the current gate. Keep its DATA views and complete enclosing C5 as
now. Do not widen the existing `(Facts) -> initials` view using a global
flag. If a control-query API is added for tests or later use, pass the
original explicitly with the Reach witness. This control path needs no
new gate or source rule evaluator. The observer must not manufacture a
DATA result from a live control exit.

Complete ND execution stays in the existing block-local joins. For the
example, actual ZERO makes the existing SESSION source run at its real
call. Existing DATA input reaches the same sink. Both conditions must hold
before the sink emits its Target. Unary arm views remain restriction
metadata only.

Do not treat a saved `ZERO -> SESSION` AL record as a fact at the sink.
It is a complete span relation. Do not insert its output at an arbitrary
internal instruction.

## 9. Work tradeoff: saved replay versus current execution

There are two distinct choices. This draft describes the first choice
without reducing its scope silently:

| Choice | Work | Result for the example |
|---|---|---|
| Admit actual ZERO into current block execution | Executes the actual permitted source actions and lets their generated DATA meet current DATA at the sink | Can recover the complete sink cube |
| Replay only saved ZERO-premise block rows | Applies complete saved span relations at the block output | The saved SESSION output does not meet the current mid-block DATA input |

A ZERO-only saved replay is not a complete substitute for the proposed
current execution. A new stage-local record service could have different
behavior, but it is outside this draft.

Current ZERO execution can generate DATA. Therefore, control-only
transport does not mean ZERO-only work. The source-permission gate still
limits source actions. Existing intra-procedural storage, field limits,
loop restriction, and DATA C5 still limit their results.

This proposal does not promise a performance improvement. It can add
current work in restricted forward runs. Measure actual ZERO visits,
source evaluations, generated DATA, ND joins, and resulting findings.
Do not infer that few control cells imply few generated DATA facts.

## 10. Required proofs

The separate draft spec defines the formal obligations. Its
[standalone check receipt](../../spec/lean/proposals/forward-internal-zero-control-20261102/checks.json)
and [constructive audit](../../spec/lean/proposals/forward-internal-zero-control-20261102/audit.txt)
cover the conditional model. They do not verify an implementation or
select this policy. Production correspondence must establish each of
these points:

1. **Origin.** An inherited control offer has the original method ZERO
   admission and an actual path of matching local links. The Boolean
   admission flag alone cannot make an offer.
2. **Routes.** Every returned control uses its exact scope and exit.
   Parent delivery uses only the existing routing adapter. Normal-J
   reverse expansion remains a property of that adapter.
3. **Layer.** Ordinary C2 ZERO admissions stay unchanged. An inherited
   local ZERO preserves the actual Reach layer. The captured actual input
   and returned control combine by the existing layer law.
4. **Separation.** The fallback does not enter an AP summary index, native
   store, demand handoff, or Target acceptance query.
5. **No new starts.** No loop, block, method, source action, or backward
   initial is started without its existing actual input or permission.
6. **Replay.** An input before a control result and an input after that
   result obtain the same one-time control completion. Duplicate offers
   do not repeat the physical work for an admitted local ZERO.
7. **ND.** Source and sink operations execute in their existing owners.
   The complete cube remains required. Saved span outputs are not
   inserted into a current intra-block join.
8. **Finite protocol.** Deduplication keys are exact and finite for a
   finite input set. A fresh queued delivery secures counted method Work.
   Strict idle checks remain enabled.

These are conditional adapter proofs. They do not prove that every other
DATA loop restriction or rule provider is complete. Do not use this
change to claim that an unrelated missing finding is resolved.

## 11. Native controls before implementation acceptance

```text
positive:
  faithful exact-array loop + independent ZERO session source + ND sink
  same rules without feedback
  actual ZERO crosses empty BL and successive loops at exact normal J
  input-before-control-result and input-after-control-result
  NORMAL and DEMAND input layers

negative:
  no admitted method ZERO => no inherited control
  actual DATA offer => no inherited ZERO
  ZERO -> DATA with no paired demand => no fallback DATA summary
  Target with no paired permission => no fallback Target
  backward Reach => no inherited control
  bypass control returns absent from NORMAL records and handoff
  ordinary C5-admitted AP rows can still persist normally
  public root C5 unchanged
```

Retain the Conductor empty reverse-J regression. A late admitted target
must use the empty identity, without a physical point in that region.
It is an independent protocol fix, not evidence that this new ZERO policy
is selected.

## 12. Measurements and rollout gate

Add numeric counts at owner barriers:

```text
actualInheritedZeroOffers
freshInheritedZeroInitials
liveControlReturns
liveControlReplays
freshControlCells
zeroPhysicalVisits
zeroSourceEvaluations
zeroGeneratedData
ndCubeCompletions
```

Keep these separate from local demand hits, AP summary counts, and native
records. Do not retain facts or forms only for diagnostics.

After the user selects the policy and native controls pass, refresh the
source/proof correspondence. Run the four configurations from `task.md`
from one final commit. Compare findings and each accepted iteration with
the fixed baseline. Record OOM, timeout, FAILED, and aborted runs as
separate outcomes. Do not accept project results from the earlier
stopped campaigns as results of this draft.

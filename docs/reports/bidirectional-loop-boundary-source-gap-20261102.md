# Loop restriction: missing boundary-inclusive saved summary

Date: 2 November 2026. **Status: historical diagnosis, followed by a tested correction.**
Sections 1–5 describe the failed `10957156a` campaign and its investigation.
They retain the evidence from before the correction. Section 6 records the
new native validation. The corrected project campaign remains a separate check.
This is not the final four-project performance report. The current measured
revision is `10957156a4359321cdbc60f0fac375d8d8ba9a5e`.

OWASP reaches, completes and accepts **run-5**, but reports 4,061 sink identities.
Both the fixed `f945f92c5` baseline and the immediate `86ad3b70b` report have 4,112.
There are **51 new missing identities and no additions**. The benchmark labels
32 of those identities expected-positive and 19 expected-negative. These labels
are benchmark evidence, not a separate security assessment.

The [embedded data](data/bidirectional-loop-boundary-source-gap-20261102.json)
contains all 51 identities, source families, labels and the qualified diagnosis.
The small native controls prove the mechanism below. They do not claim that a
complete internal fact trace was captured for each of the 51 project findings.

## 1. The field is not the cause

`[]` and `.f` each add one field to FL. The same gate issue applies to an ordinary
field read. Consider this equivalent shape:

```java
// Entry rule: assign T to p and all its descendants.
void example(Box p) {
    Box out = null;
    while (again()) {
        out = p.f;
        if (stop()) break;
    }
    sinkT(out);
}
```

The real OWASP path includes a saved pass from the request to a cookie array,
an element read, `getValue`, decoding and a later sink. Those extra passes do not
change the missing saved-summary boundary.

## 2. Exact backward loss

Run-1 has a DEMAND sink result whose method original is ZERO. It therefore gives
run-2 the typed pair `(entry=Target, exit=ZERO)`.

The native cookie control then has this run-2 path:

```text
actual sink seed:                 ZERO -> param.$/T             NORMAL
stored loop FLOW relation:       param.*/FLOW -> cookies.[].*/FLOW
apply to the actual seed:        ZERO -> cookies.[].$/T         NORMAL
stored relation growth:          0 -> 1; invoke the loop gate
saved BL relation:               cookies.*/FLOW -> request.*/FLOW
hypothetical BL result:          ZERO -> request.[].$/T         NORMAL
```

The current observer applies method C5 to that last DATA result immediately.
The demand's exit is ZERO, so it rejects DATA. The adjacent BL has no current
demand; it has saved NORMAL relations. The repeat-body demand does not accept
the cookie-array base. The observer is empty and the gate drops the fact.

The source stage exists in the real execution. It is missing from the saved BL relation used by the observer:

```text
request.[].$/T
    -> original method entry-source handler
    -> DemandTarget and a source-hit record
    -> typed method C5 accepts the Target result
    -> source permission for the next forward run
```

The root applies the original method-entry rule in the forward run. The root
then composes the resulting value with the BL completion. Thus the real run
already computes the source effect. However, the frozen scoped export contains
the child BL rows, whose initials start **after** that entry rule. It does not
export a genuine BL relation from before the rule to the loop input.

The saved BL result above is therefore only an after-rule body result. It is
not the complete relation that the observer needs. With the current early drop,
run-2 never reaches the real source handler with DATA. Run-3 has no source
permission and the finding is lost. Replacing `[]` with `.f` does not change
this summary-boundary problem.

The old flat engine delivered DATA through the original boundary handler before
summary restriction. The new gate uses a saved local relation that does not
include the same boundary stage. The source rule, field transfer and C5 rules
themselves did not change.

## 3. Native and JVM evidence

The investigation controls use the real driver, FULL mode and limits
`1,1,2,3,4`. They contain code transfers and source/sink rules, not predefined
summaries.

| Control | Result |
|---|---|
| EXACT source, copy in loop, break, flat following sink | PASS |
| Uniform source, copy in loop, break, flat following sink | PASS |
| Uniform request source, pass to array, element read in loop, later sink | FAIL; completes run-3 without the expected report |
| Same with an additional named value-field read | FAIL; completes run-3 without the expected report |
| Replace the element read with an ordinary `.f` read | FAIL with the same lost source permission |
| Remove only the feedback edge from each array control | Both PASS in run-1 |

The simple copies have non-growing body relations and bypass the gate. The
reads produce growing backward relations. The no-feedback controls establish
that the source, mark and AP transfers work when the new gate is absent.

A separate JVM graph check loads the original pinned class files for
`BenchmarkTest00001` and retained `BenchmarkTest00947`. The former has 96
instructions and four blocks, including a flat AL. The latter has 122
instructions and seven blocks, with a second loop in recursive AL. The graph
certificate was retained externally; its temporary test was removed because it
depended on an external investigation jar.

### 3.1 Independent forward exit-rule control

The symmetric native control now also reproduces a gap. It reaches, completes
and accepts **run-3**, then stops with `NO_DEMAND_EDGE` and no finding. This is a
native control result. The OWASP campaign above remains **run-5 / run-5 / run-5**.

```java
// Original entry rule: assign T to p and all descendants.
// Run-2 reaches this source; run-3 has the required source permission.
Box example(Box p) {
    while (again()) {
        x.f = p;
        if (stop()) break;
    }
    return x.f;
}
// Original normal-exit sink rule: CM(ret.$, T).
```

The failing run-3 trace is:

```text
actual source input:          p.[any-taint]/T             NORMAL
stored L FLOW relation:       p.*/FLOW -> x.f.*/FLOW      NORMAL
actual loop result:           x.f.[any-taint]/T           NORMAL
stored relation growth:       FL 0 -> FL 1; invoke the gate
saved AL field read:          x.f.*/FLOW -> ret.*/FLOW
hypothetical AL result:       ret.[any-taint]/T           NORMAL
current enclosing C5:         rejects DATA; expects the Target/ZERO path
actual normal-exit sink:      not reached; run-3 ROOT targets are empty
```

The run-2 source-hit assertion and the run-3 source-permission assertion both
pass. Thus this failure does not depend on the backward entry-source gap.
Removing only the feedback edge preserves the same write, read, source and
physical exit sink; that control reports in **run-1**. The suite has two tests:
one failing loop finding and one passing no-feedback finding. No corrected
implementation or green loop result is claimed.

The saved AL body result is before the original exit rule, so it cannot by
itself stand for the full enclosing result. This confirms the boundary-complete
summary requirement at the other end of the method as well. XML and trace
hashes are in the embedded data under `symmetricExitControl`.

## 4. Selected investigation direction

The selected ownership rule is now explicit: publish Target and run-1 static
results at the nearest block boundary. Use ordinary parent summary propagation
to reach the method level. Each entered block must therefore retain its own
eligible rows and guidance before the next handoff. A direct root publication
cannot replace those local rows. This also applies to nested before and after
regions.

Use the previous iteration's saved summary that includes the original entry
rule. Do not add another boundary-rule evaluator to the observer. Do not use a
conservative keep-raw fallback as the selected correction.

The selected publication rule is to emit reached Targets and run-1 static
results at the nearest block boundary. Existing complete local-summary
application then propagates them through each ancestor to the method. This
must create the genuine scoped AL Target in run-1, so its reverse demand is
available to the next run. Retain internal static-to-static rows for this
propagation; apply public S-S erasure only at the method boundary. No new
actor, hypothetical evaluator or guidance closure is selected.

The required scoped interface is:

```text
forward prefix input:  before the original method-entry rule
forward prefix output: the real BL exit towards L
saved relation:        entry rule ; BL body
backward use:          reverse and apply this saved relation by standard replay
```

For the reproduced source, the saved prefix relation must contain the genuine
ZERO-origin source image at the loop input. Standard opposite-direction native
replay can then map the matched marked input back to ZERO. The existing local
record application converts that result to DemandTarget. The existing complete
paired method C5 can accept the Target. The observer only reads and composes
these saved relations. It does not run a rule or create a source-hit record.
Actual execution keeps the normal source-hit handling.

| Part | Current code | Required investigation direction |
|---|---|---|
| Original method-entry rule | The root executes it. | Keep this execution and ownership. |
| Root prefix completion | It composes the root original with the completed BL output. | Use this genuine completed relation to define a boundary-inclusive prefix interface. |
| Scoped frozen export | It exports child block summary rows; child BL initials are after the entry rule. | Export the complete relation from the boundary-inclusive input to its real output port. |
| Observer | It replays an after-rule BL row and applies enclosing C5 to DATA. | Replay the complete saved relation and apply the same enclosing C5 to its result. |
| AP and Target rules | Standard native reversal and ZERO-to-Target conversion already exist. | Reuse them unchanged. |

Do not relabel an after-rule child row as a before-rule row. Such a label does
not add the missing transfer. A whole-method public summary is also not a
replacement for a prefix relation over the local values offered at the loop.
The new interface must have a real derivation through the original boundary
handler and BL body. It must retain the complete original, actual input and
output ports, layer, mark and protection annotation.

The existing stores can hold the relation. `Record` keeps the method, native
direction, initial, result, and paired scope/exit ports. `scopeIn` and `exitIn`
swap the two ports for an opposite-direction read. Scoped `byEntry` and `byExit`
select candidates; the normal AP matcher still decides applicability. A native
record must be a legal admitted NORMAL singleton summary. DEMAND relations use
the demand handoff, not native persistence. C2 reads only the entry view for the
selected scope; C5 still checks one complete entry/exit demand pair at the
actual output port. The correction must not merge independent entry and exit
permissions or make every physical port equal to a logical boundary.

The forward exit control also requires a saved interface that includes its
original exit-rule stage. An AL body row before that stage is not a full method
result. The exact export and composition hooks still need a design and proof review.
No storage, routing, AP or rule implementation is changed by this report.

The Lean projection theorem assumes a complete observer. The native failure
shows that the current production adapter does not meet that premise. It does
not refute the theorem about the complete reference observer.

## 5. Campaign state

The second campaign was stopped before native investigation tests ran, to avoid
mixing measurement with test workload. OWASP is **run-5 / run-5 / run-5** for
reached / completed / accepted. Conductor reached **run-4**, completed **run-3**
and accepted **run-3** before the stop. Thingsboard and Stirling-PDF had not
started in that attempt. No OOM was observed.

Logs, manifests, quality differences and derived CPU/memory summaries remain in
`../loop-blocks-restriction-fixed-20261102`. A third directory is prepared with
the same configurations and saved baselines, but it has not launched. The final
campaign, full quality comparison, performance report and next-iteration
proposal remain incomplete.

## 6. Correction and native validation

The corrected code starts the first local span before the real method-entry
rules and ends the last span after the real exit rules. Each rule still executes
at its original instruction. Targets and run-1 statics first publish at the
nearest boundary and then use ordinary matched parent-summary application.
Internal static-to-static rows remain available until public root erasure.
Method metadata runs with the restored original premise and does not repeat
the rules.

Normal loop leaves use one shared normal interface. Their actual acyclic tails
remain in the loop span until the real join. The user accepts the cross-branch
ND false positive at that join. Exceptions, returns and feedback retain their
roles. An inner normal leave to an outer loop header retains the outer gate.

The formerly failing named-field and array controls now pass. The symmetric
exit-sink control passes. A full three-method static Driver control completes
**run-3** with the expected NORMAL caller finding. It also asserts the genuine
ordinary AL source row, exact reversed C5 pair, run-2 source hit and run-3
source permission. The fixture uses the same MarkInput/KEEP lowering as the
production method form; a private static operation row alone is not guidance
for the ordinary AL span.

The clean complete suites pass **2,369 common tests and 453 JVM tests**, with
no failure or skipped test. See the [validation record](bidirectional-loop-blocks-implementation-validation-20261102.md)
and its source hashes. This establishes the native controls, not recovery of
all 51 project identities. That recovery must be measured on the committed
correction in `../loop-blocks-restriction-verified-20261102`.

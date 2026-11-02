# Native controls for the growing feedback case

Date: 2 November 2026. Analyzer revision:
`8213756108af9cd278668db871fc77428caec64a`.
No analyzer runtime file was changed. FULL mode, field limits `1,1,2,…`.

These are finite driver/AP fixture tests. The source call is expressed by
its ordinary source micro-edge stages, and the sink by an ordinary sink
rule. The test does not inject a predefined method-summary model. It does
not compile and extract a JVM program with a new outlining pass.

The [test source](controls/LoopGrowingDemandControlTest.kt) preserves the
control used for this investigation. It was compiled from an external
source directory through a Gradle init script. Both tests passed, with
zero failures and errors. The whole-loop test reached and completed
**run-3**, with one report and no outgoing refinement demand.

## Whole-loop code and trace

```java
// No DATA method-exit demand. B is void.
void B(Node p) {
    Node x = p;
    while (again()) {
        sourceFF(x); // Assign T exactly at x.f.f.$; preserve other marks.
        x = x.f;
        sinkRootT(x); // Check T exactly at x.$.
    }
}
```

The CFG is `entry -> move -> test -> source -> read -> sink -> test`,
with another edge from test to the void exit. The native trace is:

```text
run-1, limit 1, forward:
  source: cut x.f.[any]/T, DEMAND
  read:   x.[any]/T, DEMAND
  sink:   outgoing ZERO -> DemandTarget

run-2, limit 1, backward:
  sink:             x.$/T, NORMAL
  inverse read:     x.f.$/T, NORMAL
  source survives:  x.f.$/T, NORMAL
  feedback:         x.f.$/T reaches the earlier inverse read
  inverse read:     x.f.[any]/T, DEMAND
  source discharge: sourceFF is permitted for run-3
  outgoing:         ZERO -> DemandTarget

run-3, limit 2, forward:
  source:      x.f.f.$/T, NORMAL
  first read:  x.f.$/T, NORMAL
  feedback:    preserve exact x.f/T across sourceFF at x.f.f
  second read: x.$/T, NORMAL
  sink:        ZERO -> NormalTarget(0)
  outgoing:    empty
```

Key control output, with object addresses omitted:

```text
CONTROL_END status=COMPLETE run=3 direction=FORWARD
            reason=NO_DEMAND_EDGE run1MarkMode=FULL reports=1
run-1 outgoing: ZERO -> DemandTarget
run-2 outgoing: ZERO -> DemandTarget
run-3 raw:      ZERO -> NormalTarget(0)
run-3 outgoing: []
B_RUN2_DATA_ROWS []
B_RUN2_ZERO_C2   [ZERO, NORMAL]
B_RUN2_TARGET_C5 true
B_C5_FEEDBACK accepts=0
```

The last assertion intersects B's actual run-2 demand with original ZERO
and output `local x.f.$/T`. This has no DATA result. It does not assert
that B has no Target guidance; the Target check is independently true.

## Body C2/C5 control

A separate test constructs this legal preceding body guidance:

```text
Previous forward row: arg.*/FLOW -> arg.[any]/FLOW, DEMAND
Run-2 demand.entry:   arg.[any]/FLOW
Run-2 demand.exit:    arg.*/FLOW
Submitted:           arg.$/T, NORMAL
C2 initial:          arg.$/FLOW, NORMAL
Reverse-read raw:    arg.f.$/FLOW, NORMAL
Production C5:       arg.f.*/FLOW, NORMAL
Stored FLOW shape:   arg.*/FLOW -> arg.f.*/FLOW
```

C2 and C5 are production `DemandStore` operations. This is a growing body
relation after existing FLOW normalization. It shows that body C5 does
not reject every growing relation. The preceding pair is supplied to
this isolated AP test; it is not a recorded complete synthetic-body
handoff from the whole-loop control above.

## What follows, and what does not

The native controls show a real multi-iteration internal consumer and
that legal growing body results exist. The Lean `Feedback` model proves
the exact-path two-iteration observation and the failure of an empty
AL/B-end gate for that model. Together they expose the missing next-body consumer in the rejected
two-test rule. The selected design also checks L demand. The Lean model
proves preservation of this exact-path observation when that check admits
the intermediate value.

No outlined runtime exists yet. There is no executed end-to-end failure
of that future implementation, no proof that its complete handoff equals
this isolated body pair, and no project performance result here. Keep
these distinctions when selecting the repair.

To repeat the finite controls from the repository root:

```sh
./core/gradlew -p core :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.LoopGrowingDemandControlTest \
  -I "$PWD/spec/lean/proposals/loop-fragments-and-demand-collapse-20261102/controls/control.init.gradle" \
  -DloopControlDir="$PWD/spec/lean/proposals/loop-fragments-and-demand-collapse-20261102/controls"
```

The archived init script takes the source directory as a JVM system
property, so included Gradle builds see the same value. The
original execution used the same source-set hook with the external
absolute directory. Project performance measurements were not repeated.

## Existing backward discovery with no loop leave

Date: 2 November 2026. Runtime is still
`8213756108af9cd278668db871fc77428caec64a`; documentation baseline is
`7b59054efa6c010780fa79c3e9357a4b1b54679e`.

The current JVM `JIRMethodEntry` already builds backward graphs using
`JIRExitWiredGraph(...).reversed`. That wrapper wires a node unable to
reach an original exit to the exceptional exit before reversal. Backward
ZERO starts at normal and exceptional exits. The forward graph remains
raw. This is interpreter I11(e)/AP S11, not a new loop policy.

```java
void B(Node p) {
    Node x = p;
    while (true) {
        sourceFF(x); // Assign T at x.f.f.$ only.
        x = x.f;
        sinkRootT(x); // CM(x.$, T).
    }
}
```

The [FULL control source](controls/LoopNoLeaveDiscoveryControlTest.kt)
uses CFG `0 -> 1 -> 2 -> 3 -> 4 -> 5 -> 2`, normal exit 6 and exceptional
exit 7. Neither exit has a forward predecessor. Its fixture explicitly
selects the existing JVM-style backward-discovery contract. Backward
wiring adds `7 -> 0,1,2,3,4,5`. It adds no forward edge.

Four native checks passed:

| Check | Result |
|---|---|
| Existing BackwardDiscoveryGraphTest: selected exceptional wiring | PASS; exact independent edge reference |
| Existing BackwardDiscoveryGraphTest: no fallback to normal exit | PASS |
| Existing CurrentSequenceTest: nonreturning worker with a real caller | PASS; GROUP completes run-3 |
| New LoopNoLeaveDiscoveryControlTest | PASS; FULL completes run-3 with one report |

The FULL trace has:

```text
run-1, limit 1, forward:  ZERO -> DemandTarget
run-2, limit 1, backward:
    ZERO reaches points 3,4,5 through exceptional discovery
    the second inverse read reaches the source requirement
    sourceFF is permitted for run-3
    ZERO -> DemandTarget
run-3, limit 2, forward:
    x.f.f.$/T -> x.f.$/T -> x.$/T through two iterations
    ZERO -> NormalTarget(0)
    outgoing refinement: empty
    status: COMPLETE, reason: NO_DEMAND_EDGE

forward visits to normal exit 6:      0
forward visits to exceptional exit 7: 0
reports:                             1
```

This verifies reuse of the current discovery mechanism. It is not a
block-decomposition runtime test. The method-owned block view must retain
the same backward-only edges and the actual destination instruction,
with its local control C2 and complete paired gates.

Repeat these four checks from the repository root:

```sh
./core/gradlew -p core :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests 'org.opentaint.dataflow.bidi.BackwardDiscoveryGraphTest' \
  --tests 'org.opentaint.dataflow.bidi.CurrentSequenceTest.a nonreturning worker loop reports its sink without waiting for a normal summary' \
  --tests 'org.opentaint.dataflow.bidi.LoopNoLeaveDiscoveryControlTest' \
  -I "$PWD/spec/lean/proposals/loop-fragments-and-demand-collapse-20261102/controls/control.init.gradle" \
  -DloopControlDir="$PWD/spec/lean/proposals/loop-fragments-and-demand-collapse-20261102/controls"
```

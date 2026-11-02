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
./gradlew :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.LoopGrowingDemandControlTest \
  -I spec/lean/proposals/loop-fragments-and-demand-collapse-20261102/controls/control.init.gradle \
  -PloopControlDir="$PWD/spec/lean/proposals/loop-fragments-and-demand-collapse-20261102/controls"
```

The archived init script takes the source directory as a property. The
original execution used the same source-set hook with the external
absolute directory. Project performance measurements were not repeated.

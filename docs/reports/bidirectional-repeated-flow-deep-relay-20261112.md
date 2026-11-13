# Repeated FLOW demand can remain necessary

The native baseline reaches **run-9**, ends with `NO_DEMAND_EDGE`, and reports
one sink. Removing one repeated FLOW demand row after **run-5** makes the same
fixture end at **run-7** with no finding. Neither control has an iteration cap.
This is a counterexample to repetition alone as a deletion predicate. It does
not classify the current OWASP corpus row `1025a197…` as necessary.

## Program and native model

```java
void main() {
    Object p = sourceT();                 // Assign T at p.$ only.
    Object ret = relay(p);
    sinkT(ret);                           // Check T at ret.$ only.
}

Object relay(Object p) {
    Chain tmp = freshInitializedChain();
    tmp.f1.f2.f3.f4.f5.f6.f7.f8 = p;
    return tmp.f1.f2.f3.f4.f5.f6.f7.f8;
}
```

The native fixture configures these two NORMAL micro-edges directly:

```text
p.* / FLOW                        → tmp.f1.f2.f3.f4.f5.f6.f7.f8.* / FLOW
                                     tmp.f1.f2.f3.f4.f5.f6.f7.f8.* / FLOW → ret.* / FLOW
```

The first statement also preserves `p`. Call bindings, the source, the sink,
C2, C5, field limits, summary storage, persistence, handoff and stopping use
the native core. There are two methods and no loops, statics, ND rules or
mark checks inside `relay`. There is exactly one configured source and sink.

This is an explicit native IR/pass-model program, not a JVM lowering test.
The Java code gives its intended fresh-chain store/read interpretation.
The fixture adds no alias or overwrite micro-edges. Its result does not prove
that arbitrary JVM field assignments have no aliases or strong-write effects.

Notation: `N` is NORMAL; `D` is DEMAND; `$` is EXACT; `[any]` is MAY.
`p` is native `arg(0)`; `tmp` is local 2; `ret` is the return base. All field
and mark exclusions are empty. `T` is the sole ordinary concrete mark.

A handoff row is written `(entry ; exit)`, with the coordinates used by the
**next** run. This differs from the produced summary's `premise → conclusion`
notation. The selected whole row is:

```text
X = relay: (ret.[any]/FLOW ; p.*/FLOW)
```

## Native traces around the removal point

The submitted facts and initials below are actual fixture observations.
In particular, the restricted initial is EXACT/FLOW. Its stored summary
premise is STAR after the existing summary normalization.

```java
// Run-3 FORWARD, field limit 2.
// Incoming demand H2: (p.[any]/FLOW ; ret.*/FLOW).
// Submitted:          p.$/T, N.
// Emitted initial:    p.$/FLOW → p.$/FLOW, N.
Object relay(Object p) {
    Chain tmp = freshInitializedChain();
    tmp.f1.f2.f3.f4.f5.f6.f7.f8 = p;  // The 8-field temporary does not fit.
    return tmp.f1.f2.f3.f4.f5.f6.f7.f8;
}
// Produced NORMAL summaries: none.
// Produced DEMAND summary: p.*/FLOW → ret.[any]/FLOW.
// H3 contains exactly X and main: (Target ; Zero).
```

```java
// Run-4 BACKWARD, field limit 3.
// Incoming demand H3: (ret.[any]/FLOW ; p.*/FLOW).
// Submitted:          ret.$/T, N.
// Emitted initial:    ret.$/FLOW → ret.$/FLOW, N.
Object relay(Object p) {
    Chain tmp = freshInitializedChain();
    tmp.f1.f2.f3.f4.f5.f6.f7.f8 = p;
    return tmp.f1.f2.f3.f4.f5.f6.f7.f8; // The reversed read exposes the deep temporary.
}
// Produced NORMAL summaries: none.
// Produced DEMAND summary: ret.*/FLOW → p.[any]/FLOW.
// H4: relay: (p.[any]/FLOW ; ret.*/FLOW),
//     main: (Target ; Zero), main: (Zero ; Zero).
```

```java
// Run-5 FORWARD, field limit 4.
// Incoming demand H4: (p.[any]/FLOW ; ret.*/FLOW).
// Submitted:          p.$/T, N.
// Emitted initial:    p.$/FLOW → p.$/FLOW, N.
Object relay(Object p) {
    Chain tmp = freshInitializedChain();
    tmp.f1.f2.f3.f4.f5.f6.f7.f8 = p; // Still cannot represent all 8 fields.
    return tmp.f1.f2.f3.f4.f5.f6.f7.f8;
}
// Produced NORMAL summaries: none.
// Produced DEMAND summary: p.*/FLOW → ret.[any]/FLOW.
// H5 contains exactly X and main: (Target ; Zero).
// Deletion control removes X here, after H5, before run-6.
```

These are the complete newly produced `relay` summaries for each of runs
3–5. `main` produces `Zero → Zero,N` in all three and additionally
`Zero → Zero,D` in run-4. There is no hidden concrete-T demand in those
frontiers. Run-1 additionally saves `p.*/FLOW → p.*/FLOW,N` and
`Zero → Zero,N` for `relay`; neither transfers `p` to `ret`.

## All iteration frontiers

Define the exact row sets:

```text
O = { relay: (ret.[any]/FLOW ; p.*/FLOW), main: (Target ; Zero) }
E = { relay: (p.[any]/FLOW ; ret.*/FLOW),
      main: (Target ; Zero), main: (Zero ; Zero) }
Z = { main: (Zero ; Zero) }
```

| Completed run | Direction | Field limit | Baseline outgoing rows | Deletion outgoing rows |
|---|---|---:|---|---|
| run-1 | Forward | 1 | O (2) | O (2) |
| run-2 | Backward | 1 | E (3) | E (3) |
| run-3 | Forward | 2 | O (2) | O (2) |
| run-4 | Backward | 3 | E (3) | E (3) |
| run-5 | Forward | 4 | O (2) | O before cut; `{main: (Target ; Zero)}` after cut (1) |
| run-6 | Backward | 5 | E (3) | Z (1) |
| run-7 | Forward | 6 | O (2) | Empty; natural end, 0 findings |
| run-8 | Backward | 7 | E (3) | Not run |
| run-9 | Forward | 8 | Empty; natural end, 1 finding | Not run |

Baseline run-9 admits the same `p.$/T,N` and starts the same
`p.$/FLOW → p.$/FLOW,N` initial. The full temporary now fits. It publishes
`p.*/FLOW → ret.*/FLOW,N`. Application to the concrete caller yields
`ret.$/T,N`; the sole sink is reported at `main:2`, rule `deep relay sink`,
with `provisional=false`.

The deletion control changes only H5's demand store. It removes the whole X
row, not one origin or one output selector. It retains the other H5 row
`main: (Target ; Zero)`. The test asserts the precise set difference and
preserves the same record-store view, source-seed index and NormalTarget
view by reference; roots and every other configuration field stay equal.
The initial H3 and H5 full row sets agree across the controls. After the
cut, `relay` has no analysis or new summaries in runs 6–7. No saved NORMAL
relation transfers `p` to `ret`, so retaining those records cannot recover
the finding.

## Consequence for deletion predicates

```text
X ∈ H3 ∩ H5
same admitted inputs and same normalized relay summary shape at runs 3 and 5
  ⇏ no new required summary at a later field limit
```

The lost information is inside the temporary path. Entry and exit demand
coordinates do not expose its depth. Repetition alone, even with unchanged
STAR entry processing and existing NORMAL input identities, does not
certify future closure. A stronger predicate must prove that no new
required transfer can arise, or prove a retained delivery route.

The constructive [Lean concept model](../../spec/lean/proposals/redundant-demand-deep-relay-20261112/BoundedRoundTrip.lean)
checks repetition at limits 2/4 and change at limit 8. It is a finite
field-limit model, not a formal proof of the whole engine or a correspondence
theorem for arbitrary programs. The native sole-row deletion supplies the
separate observed sink-loss control.

## Reproduction and evidence

The [native JUnit fixture](../../scripts/demand_campaign/native-fixtures/DeepRelayDemandTest.kt)
uses `IncreasingLimits` directly: limits `1,1,2,3,…`. It never calls
`configuredIncreasingLimits` and does not use `HardRunLimitPolicy`.
Both controls assert `COMPLETE/NO_DEMAND_EDGE` and runs 9/7, respectively.
The 20-second per-control resource budget is a failure guard, not a proof
of termination. The successful test takes 0.271 seconds; termination is
observed from the native end reason.

Production source is pinned to `14d7b63369d94f49d4c551be8405ed7719f267cc`.
Its 68 fixture helpers are extracted from the same revision. The JUnit
fixture is compiled from source by Gradle, offline, with external test
sources/classes/reports and the existing source-built main overlay. No
analyzer artifact is downloaded, and no production source is changed.
The frozen source-build package does not claim whole-jar historical byte
identity.

External evidence, including all literal native rows, source/compiler
inputs, runtime classpath hashes, XML and the receipt:

```text
/drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/
  redundant-demand-rows-20261112/cases/deep-relay-repeated-flow-v4/
```

From `core/`, using the absolute external directory as `CASE` and its sibling
`pinned-runtime-source-build-v3` as `RUNTIME`:

```sh
./gradlew :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.campaign.deeprelay.DeepRelayDemandTest \
  --offline --console=plain \
  -I "$RUNTIME/pinned-source.init.gradle" -I "$CASE/test.init.gradle"
```

Use a fresh external case directory and replace the case path in the test
init before rerunning; it refuses to overwrite the captured result.
`check_deep_relay.py CASE` verifies the sealed v4 package without running
Gradle or an analyzer.

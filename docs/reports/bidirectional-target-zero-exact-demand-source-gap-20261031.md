# Exact FULL sources use native replay

Date: 31 October 2026. Status: corrected implementation control.
Latest reached and complete iteration: **run-3** in the two-field control;
**run-1** in the one-field control. This is a correctness report. It is
not a project performance result.

The narrative below records the native-replay correction and its earlier
conditional-source counterexample. The later concrete exact-DEMAND
amendment is now implemented. The final complete validation passes 2,207
core and 452 JVM tests. An explicit concrete exact demand now admits MAY
as exact DEMAND; an empty demand still does not start current analysis.
Weak multi-origin source arms stay DEMAND. The conditional-source control
reports the good call only at run-3. See the
[current validation](bidirectional-target-zero-implementation-validation-20261031.md)
and [amendment trace](bidirectional-target-zero-nonzero-source-admission-gap-20261031.md#8-latest-implemented-correction-concrete-exact-demand-and-origin-support).
Earlier failure claims and source hashes below are historical evidence.

The earlier version of this report attributed a missed FULL source to
EXACT/MAY admission. That diagnosis was incomplete. The run-1 engine
changed an exact, ordinary FULL `ZERO -> ret.$/U` result from NORMAL to
DEMAND. It then did not save that result as a native record. This removed
the native replay route that must run before current demand admission.

The first correction preserved NORMAL only for a FULL ZERO original.
The user then clarified the complete rule: FULL uses ordinary computed
layers, as in the other iterations. The blanket taint demotion applies
only to GROUP mode:

```text
run-1, FULL, ordinary nonstatic relation:
    keep the result's computed NORMAL or DEMAND layer

run-1, GROUP taint; static result; static original:
    keep the independent DEMAND policy

concrete STAR start; uncertain guard; field-limit cut; lost exclusion:
    keep the DEMAND layer required by the ordinary AP rules
```

This correction does not change C2, C5, field transfer, source permissions,
ND origin selection, or the call policy. It changes the layer of ordinary
FULL nonzero results that the previous blanket demotion had changed to
DEMAND. A NORMAL weakened origin arm is now observable and can be saved.
The conditional-source negative control below identifies the resulting
caller-binding problem; this report does not claim that problem is fixed. A second explicit rule converts
an accepted backward source-summary result from ZERO to DemandTarget.
This rule applies to current summaries and native reads, including the
opposite-direction read view. A balanced ZERO-to-ZERO control row remains
an ordinary AP result. It does not promote a DEMAND
result to NORMAL. It does not add a source hit during native replay.

The selected [C2 rule](../design/bidirectional-constant-filter-target-zero-implementation-v2-20261031.md#41-exact-demand-correction)
still rejects a submitted `[any]` for an exact `$` demand. The selected
[unanswered-demand rule](../design/bidirectional-constant-filter-target-zero-implementation-v2-20261031.md#43-starts-and-no-op-behavior)
still adds no other work. The
[static terminal completion](bidirectional-target-zero-static-c5-gap-20261031.md)
is separate: all run-1 static results remain DEMAND.

The executable control is
[ExactDemandMaySourcePermissionTest](../../core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/ExactDemandMaySourcePermissionTest.kt).
It uses the actual method engines, record store, caller replay and driver.
It has no static field, cleaner or predefined summary. It uses FULL marks
and field limits `1,1,2`. Each write transfers one field.

The source rule assigns U exactly at the result of `sourceU()`. The sink
rule checks `ContainsMark(p.$, U)` at `sinkU(p)`. All exclusions in the
trace are empty. `N` means NORMAL; `D` means DEMAND; `DT` means
`DemandTarget`. `(Dc,Dp)` is a paired demand row.

## Run-1: save the exact source; refine only the cut caller

```java
// Incoming demand: none. Submitted: ZERO.
Object factory() {
    return sourceU();
    // ZERO -> ret.$/U, N.
}
// Summary: ZERO -> ret.$/U, N.
// Save this native forward record.
// No DEMAND row is produced for this exact source.

// Incoming demand: none. Submitted: ZERO.
void main(Box out) {
    Object x = factory();
    // ZERO -> x.$/U, N.

    Box tmp = new Box();
    tmp.b = x;
    // ZERO -> tmp.b.$/U, N. This write fits limit 1.

    out.a = tmp;
    // Limit 1 cuts the second field:
    // ZERO -> out.a.[any]/U, D.

    sinkU(out.a.b);
    // The cut witness produces ZERO -> DT, D.
}
// Relevant demand: ZERO -> out.a.[any]/U and ZERO -> DT.
// The factory's exact source remains a saved NORMAL relation.
```

The one-field control uses `out.a = x; sinkU(out.a)`. It has no field
cut. Its NORMAL witness produces `ZERO -> NormalTarget(id)` and the
analysis completes at **run-1** with the sink report.

## Run-2: use the saved reverse source before the demand gate

```java
// Current factory demand: none.
// Offered by the caller: ret.[any]/U, D.
// Saved native read view: ret.$/U -> ZERO, N.
Object factory() {
    return sourceU(); // no current factory actor is needed
}
// Native replay applies the saved reverse view to the MAY offer.
// Its accepted nonzero-to-ZERO source result becomes DemandTarget.
// The caller keeps its original ZERO: ZERO -> DT, D.
// No return/cleanup/CFG suffix executes for this source discharge.
// No actual reverse GEN executes. No Source seed is recorded.

// Incoming demand includes (Target, ZERO).
// Submitted: ZERO, admitted by this explicit local control demand.
void main(Box out) {
    Object x = factory();
    // Backward arrival: ZERO -> x.[any]/U, D.
    // Result binding offers ret.[any]/U to the factory.
    // Step 1: apply the saved native reverse source.
    // Step 2: current demand lookup is empty.
    // Stop current admission: no subscription or factory initial.

    Box tmp = new Box();
    tmp.b = x;
    // Reverse transfer: tmp.[any]/U -> x.[any]/U, D.

    out.a = tmp;
    // Reverse transfer: out.a.[any]/U -> tmp.[any]/U, D.

    sinkU(out.a.b);
    // Seed before the cut: out.a.b.$/U, N.
    // Seed after the limit-1 cut: out.a.[any]/U, D.
}
// The caller's outgoing ZERO -> DT gives explicit Target guidance.
// There is no factory Source permission for run-3.
```

A native record read uses the existing record matcher. It does not emit
an exact current initial from the MAY input. If a temporary exact demand
`(ret.$/U,ZERO)` is supplied to C2 directly, this same MAY input still
produces no initial. Native replay and current admission are separate
operations.

## Run-3: use the saved forward source without a Source seed

```java
// Current factory demand: none. Source permission: absent.
// Saved forward record: ZERO -> ret.$/U, N.
Object factory() {
    return sourceU(); // no current factory actor is needed
}

// Limit 2. Submitted root control: ZERO.
void main(Box out) {
    Object x = factory();
    // Apply the saved forward record before the current demand gate.
    // ZERO -> x.$/U, N. Native replay does not require a Source seed.

    Box tmp = new Box();
    tmp.b = x;
    // ZERO -> tmp.b.$/U, N.

    out.a = tmp;
    // ZERO -> out.a.b.$/U, N. Both fields now fit.

    sinkU(out.a.b);
    // ZERO -> NormalTarget(id), N.
}
// Final report: sink U.
```

The test checks the native record in the run-2 snapshot, actual MAY input
at the backward call, the reverse view, its ZERO-origin DemandTarget,
record crossings in both later runs, no current factory actor or subscription, no reverse factory source
hit, no next factory Source permission, and the final sink report.

## Source-summary discharge in each read lane

[BackwardSourceSummaryTargetTest](../../core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/BackwardSourceSummaryTargetTest.kt)
checks the same terminal dispatch through all three existing lanes:

| Lane | Existing AP relation or read view | Accepted backward effect |
| --- | --- | --- |
| Current backward summary | `ret.$/U -> ZERO` | caller `P -> DT` |
| Saved backward record | `ret.$/U -> ZERO`, NORMAL native record | caller `P -> DT` |
| Opposite-direction read | saved forward `ZERO -> ret.$/U`, read as `ret.$/U -> ZERO` | caller `P -> DT` |

The tests keep the complete caller original: ZERO, one marked original,
or a complete union at the adapter boundary. They cover exact and MAY
actuals through the existing matchers. Unmatched marks produce nothing.
No lane adds a source hit, source seed, return effect or CFG work. Saved
terminal-only effects still count as native record crossings. A balanced
backward `ZERO -> ZERO` stays an AP control result. A saved forward
`ZERO -> ret.$/U` still supplies its marked AP result without a Source
seed. No Target is stored as a native AP record.

## Genuine DEMAND control

A second program supplies an uncertain guard to the factory. A source
rule assigns T at `box.[any]`. A conditional source checks T at its
argument and assigns U exactly at its return:

```java
// The source rule produces box.[any]/T, D.
void main(Box out) {
    Box box = sourceMayT();
    Object x = conditionalFactory(box);
    Box tmp = new Box();
    tmp.b = x;
    out.a = tmp;
    sinkU(out.a.b);
}

// Guard input is uncertain, so the exact action result stays DEMAND.
Object conditionalFactory(Box p) {
    return assignUIfContainsT(p);
}
// Run-1 relation: p.*/T -> ret.$/U, D.
// This relation is not a NORMAL native record.
// Run-2 demand: ret.$/U. Caller offer: ret.[any]/U, D.
// C2 emits no initial. No current factory actor or subscription is made.
```

This control preserves the strict C2/no-op contract. The exact result
position does not remove the uncertainty in the guard. There is no
NORMAL producer that could supply a native replay result. No retry,
extra demand, fabricated source permission or terminal bypass is added.
The provisional result does not produce a settled NORMAL report.

GROUP mode still demotes its group-taint results. A group-valued source
therefore does not acquire the FULL native route described above. This
report does not claim complete GROUP refinement or whole-program coverage.
The separate static completion has its own positive checks.

## Reproduction

From `core`:

```sh
./gradlew :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.ExactDemandMaySourcePermissionTest --console=plain
```

The earlier native-dispatch check passed 11 tests. It included the two
source controls above, five actual call-source-hit tests, and four
backward source-summary dispatch tests. Receipt:
`/tmp/bidi-target-source-replay-recheck.log`.

After the broader FULL layer correction, the latest combined check ran
nine tests. The two source controls in this report and all six layer
policy controls passed. The separate two-input conditional-source test
failed only its negative caller check: both the valid finding and the
`missing second input` finding were reported at **run-3**. Exact FULL
request initials and the resulting atomic source summaries were NORMAL.
The helper had saved `arg0/T1 -> ret/U` and `arg1/T2 -> ret/U` as separate
NORMAL relations after the complete `CM(arg0,T1) AND CM(arg1,T2)` condition
was met. A later call with only `arg0/T1` reused one arm. Its positive
finding is restored, but its negative caller is not preserved. The
negative assertion remains in
[FullConditionalSourceDemandTest](../../core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/FullConditionalSourceDemandTest.kt).
No C2 relaxation or NORMAL-report bypass was added. Receipt:
`/tmp/bidi-target-full-ordinary-layer-tests.log`.
Worktree base: `79775235e99583878c17f4fd88d2f7e09ea3c3ac`.
Test SHA-256:
`c4216397ee335466ae7a32a5aade4adc921605bc0a58ce76937d4e523852997f`.
The semantic evidence is checked by the repository tests and stated in
this report. No project timing or whole-program no-FN claim follows from
these controls.

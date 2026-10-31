# Static Target completion restores ZERO guidance

Date: 31 October 2026. Status: the selected static completion passes the
focused checks. The final complete validation also passes.
Latest reached and complete iteration: **run-3**. Run-3 now creates the
required actors and reports the sink. This is a correctness trace, not a
project performance result.

Static Target completion restores the source-to-sink path below. It keeps
the paired C5 rule in
[the implementation proposal](../design/bidirectional-constant-filter-target-zero-implementation-v2-20261031.md#62-paired-restriction).
The first sections record the failure before the fix. The last sections
give the selected rule, the successful trace, and the focused checks.
This report records correctness. The
[current validation](bidirectional-target-zero-implementation-validation-20261031.md)
tracks complete checks; project measurements are recorded separately.

The test is
[StaticTargetRefinementTraceTest](../../core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/StaticTargetRefinementTraceTest.kt).
It uses the method engine and the driver. It has no predefined summary
and no witness-to-report adapter. It uses FULL marks, enabled statics,
and field limits `1,1,2`.

```java
// srcT assigns T at C.f.$. sinkT checks T at C.f.$.
void root() { set(); consume(); }
void set() { C.f = srcT(); }
void consume() { sinkT(C.f); }
```

All field exclusions are empty. `DT` means `DemandTarget`. A pair
`(Dc,Dp)` has a next-run entry endpoint and exit endpoint.

## Before the fix: run-1 reaches the write and sink

```text
set:
  ZERO -> C.f.$/T                 DEMAND AP summary

consume:
  C.f.*/T -> DT                   raw and published terminal

root:
  ZERO -> C.f.$/T                 DEMAND AP summary
  C.f.*/T -> DT                   raw and published terminal
```

The static summary machinery keeps the selected static original when
it delivers the terminal to root. This is the specified run-1 behavior.

## Before the fix: run-2 rejects the completed root terminal

The complete incoming pairs are:

```text
root:     (C.f.$/T, ZERO), (Target, C.f.*/T)
set:      (C.f.$/T, ZERO)
consume:  (Target, C.f.*/T)
```

The Target entry admits ZERO at root and consume. The AP entry admits
the exact static requirement at set. The sink seed and the normal
backward call procedure reach the actual source in set.

```text
set:
  source hit: srcT at the static write
  C.f.$/T -> DT                   raw and published terminal

root:
  ZERO -> DT                     raw terminal
  published terminal set: empty
```

C5 tests one complete pair:

| Root pair | Entry test for ZERO | Exit test for DT | Result |
|---|---|---|---|
| `(C.f.$/T, ZERO)` | Reject | Accept | Reject |
| `(Target, C.f.*/T)` | Accept | Reject | Reject |

The source hit and its source seed exist. The lost item is root's
outgoing terminal, which must give root ZERO permission in run-3.

## Before the fix: run-3 cannot start root

The remaining pairs are:

```text
root:     (C.f.$/T, ZERO)
set:      (Target, C.f.$/T)
consume:  (C.f.$/T, ZERO)
```

Root has no Zero or Target entry. Its ZERO lookup returns the empty
set. The driver creates no actor and stops with `NO_DEMAND_EDGE`.
The final report is empty.

This trace has no field overflow, Constant base, ND relation, cleaner,
or ambiguous MAY-to-EXACT admission. The source is found in run-2.
The missing report follows from the terminal restriction and handoff.

## Pre-fix check after source-summary conversion

The latest source-summary correction is present in this receipt. In a
backward call, an accepted nonzero-to-ZERO source result now produces
DemandTarget under the caller's original premise. The conversion applies
to current summaries, saved backward records and opposite-direction read
views. It executes no return, cleanup or CFG suffix. A balanced
ZERO-to-ZERO control summary keeps its AP behavior.

The static failure is unchanged after this correction. The run-2 source
in `set` already publishes a selected `C.f.$/T -> DT`. Both that terminal
and any accepted source-summary discharge give root the same raw
`ZERO -> DT`. The owned set merges the duplicate. Paired C5 still rejects
that root row through both pairs in the table above. Run-3 still has no
root actor and no report.

The separate FULL layer correction also does not change this case.
At this pre-fix check, the correction preserved NORMAL only for ordinary
nonstatic FULL ZERO-origin results. The user later extended it to all
ordinary FULL computed layers. Static results and static originals keep
their independent DEMAND rule, so this static writer still has no saved
NORMAL source record that could supply a different route. The
[nonstatic native-source controls](bidirectional-target-zero-exact-demand-source-gap-20261031.md)
pass with no relaxation of C2 or C5.

Fresh command, from `core`:

```sh
./gradlew :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.StaticTargetRefinementTraceTest --console=plain
```

In that pre-fix receipt, the positive report assertion fails. Latest
reached/complete run in the receipt: **run-3**. The exact run-2 rows, rejected root terminal and run-3 ZERO
lookup are the rows shown above. Receipt:
`/tmp/bidi-target-static-after-source-dispatch.log`. This was a correctness
failure, not an accepted report reduction or a performance measurement.

## Selected static completion

The user selected static composition at the run-1 to run-2 boundary. Keep
paired C5. Extend the existing frozen static completion with an anonymous
typed terminal endpoint:

```text
ZERO -> C.f.$/T       +       C.f.*/T -> DemandTarget
                     =>      ZERO -> DemandTarget

Virtual run-2 pair: (Target, ZERO)
```

The composition must use compatible static geometry and marks. It may
follow the existing visible static-to-static bridges. The writer and
terminal attachments keep their complete method owner. A typed Target
is not an AP fact or an internal graph vertex. NormalTarget is excluded.

The demand lookup must use the composed pair for ZERO admission and
terminal restriction. It must not combine an entry from one pair with
an exit from another pair. A nonzero writer `p/T -> C.f/T` can instead
produce `(Target, p/T)`; that pair permits a data result at `p/T` and
still rejects `ZERO -> DemandTarget`.

The implementation extends the existing lazy completion and demand
lookup. It adds no eager Cartesian closure, new static service, or C5
bypass. Only the run-1 to run-2 snapshot has this completion. Later
handoffs use explicit local demand rows.

NormalTarget's normal-only composition, backward exclusion, and report
rules stay unchanged. The directed C2 correction stays unchanged.

## After the fix: run-2 retains the complete source path

Run-1 produces the same AP and terminal rows as before. The frozen input
also keeps the typed terminal reader at root. The explicit run-2 pairs
remain the same. A query at root now sees this additional virtual pair:

```text
root, explicit:
  (C.f.$/T, ZERO)
  (Target, C.f.*/T)

root, lazy composition:
  (Target, ZERO)
```

This pair is not inserted as an AP row or an ordinary summary publication.
The fallback handoff test has two explicit rows before and after lookup.
The completed pair is used by the normal demand API:

```text
initials(root, ZERO)                   = { ZERO }
acceptsTarget(root, original=ZERO)      = true

set, run-2:
  actual source hit: srcT at the static write
  C.f.$/T -> DemandTarget              raw and selected

root, run-2:
  ZERO -> DemandTarget                raw and selected
```

C5 accepts the last row through one complete `(Target, ZERO)` pair. The
implementation does not join the entry of one explicit pair with the
exit of another pair.

## After the fix: run-3 starts and reports

The selected run-2 terminal gives root an explicit `(Target, ZERO)` pair
for run-3. The run-3 snapshot has no frozen static completion. The source
seed comes from the actual run-2 source hit.

```java
// Run-3, limit 2.
// root demand: (ZERO, ZERO), (C.f.$/T, ZERO), (Target, ZERO)
// submitted: ZERO
void root() {
    set();
    // NORMAL ZERO -> C.f.$/T
    consume();
    // NORMAL ZERO -> NormalTarget(static sink)
}
// Root terminal: ZERO -> NormalTarget(static sink), NORMAL.

// set demand: (Target, C.f.$/T)
// submitted: ZERO; source permission: actual srcT hit from run-2
void set() {
    C.f = srcT();
    // NORMAL ZERO -> C.f.$/T
}
// Summary: ZERO -> C.f.$/T, NORMAL.

// consume demand: (C.f.$/T, ZERO)
// submitted: C.f.$/T, NORMAL
void consume() {
    sinkT(C.f);
    // NORMAL C.f.$/T -> NormalTarget(static sink)
}
// Terminal: C.f.$/T -> NormalTarget(static sink), NORMAL.
```

The final report contains the configured sink at `consume:1`. The driver
stops with `NO_DEMAND_EDGE` after **run-3**. This test has one sink, one
report, empty field exclusions, no ND edge, and no cleaner. It uses FULL
marks and enabled statics. It does not establish GROUP-mode refinement
or whole-program performance.

## Focused verification

The command below passed **60 tests in eight suites**, with no failures
or errors. Gradle took 9 seconds. This is test time, not analyzer engine
time. Worktree base: `79775235e99583878c17f4fd88d2f7e09ea3c3ac`.

```sh
# From core
./gradlew :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.StaticTargetClosureTest \
  --tests org.opentaint.dataflow.bidi.StaticTargetRefinementTraceTest \
  --tests org.opentaint.dataflow.bidi.ControlDemandTest \
  --tests org.opentaint.dataflow.bidi.FrozenStaticCompletionTest \
  --tests org.opentaint.dataflow.bidi.DemandStorageDifferentialTest \
  --tests org.opentaint.dataflow.bidi.HandOffTest \
  --tests org.opentaint.dataflow.bidi.C5StaticPruningTest \
  --tests org.opentaint.dataflow.bidi.Run1StaticGroupProtocolRemovalTest \
  --console=plain
```

| Suite | Tests | Result |
|---|---:|---|
| StaticTargetClosureTest | 9 | Pass |
| StaticTargetRefinementTraceTest | 1 | Pass; latest complete run-3 |
| ControlDemandTest | 7 | Pass |
| FrozenStaticCompletionTest | 11 | Pass |
| DemandStorageDifferentialTest | 6 | Pass |
| HandOffTest | 12 | Pass |
| C5StaticPruningTest | 6 | Pass |
| Run1StaticGroupProtocolRemovalTest | 8 | Pass |

The nine new closure checks cover these cases:

- A direct ZERO writer and terminal reader yield a lazy `(Target, ZERO)`.
  The original explicit row count stays two, and no NORMAL record is
  created by completion.
- FLOW bridges and exact `T -> U` bridges retain the correct label.
  Wrong marks and different static fields do not yield ZERO permission.
- A nonzero writer yields `(Target, p/T)`. It admits the matching data
  result and rejects a ZERO terminal.
- A reachable callee's static bridge is visible. An unrelated method's
  bridge is not visible. Writer and terminal bindings keep their complete
  owner context.
- Completion is valid only for run-2. Later local snapshots create no
  virtual permission.
- A joined snapshot remains usable after mutable run-1 catalogs are
  released. The query needs no actor or mutable catalog.
- A colored static cycle terminates. A frozen snapshot does not change
  when its builder receives another terminal reader.
- NormalTarget creates no backward demand and is ignored by backward
  actors.

The existing static Target checks also pass. They use the existing static
call delivery and exact-field continuation machinery. There is no second
Target-specific static service. Receipt:
`/tmp/bidi-target-static-closure-tests.log`. The full trace is embedded
above; the log is not needed to understand the result.

## Additional check: a virtual AP ZERO exit also accepts Target

A later focused check found one missing demand adapter. The existing AP
completion could select a ZERO result, but terminal selection did not
check the same virtual pair. The failure occurred with two wrappers and
a static write that an exit rule removed from the outgoing static result:

```java
// Source: srcT assigns T to C.f at the write.
// Exit rule for get: drop static output facts; keep returned facts.
// Sink: sinkT checks T at its argument.
void main() { sinkT(wrap0()); }
Object wrap0() { return wrap1(); }
Object wrap1() { return get(); }
Object get() {
    C.f = srcT();
    Object result = C.f;
    return result;
}
```

The getter keeps the executed write as a killed-write candidate. Its
FLOW read gives the ordinary frozen AP completion:

```text
ZERO -> C.f.$/T                 killed-write candidate
C.f.*/FLOW -> ret.*/FLOW       DEMAND read summary

Completed AP relation: ZERO -> ret.$/T
Virtual run-2 pair:     (ret.$/T, ZERO)
```

Before the adapter fix, a query with original `ret.$/T` gave these
results at the getter and both wrappers:

```text
intersect(original, ZERO)       nonempty
acceptsTarget(original)         false
```

The actual source hit existed in run-2. The getter and the inner wrapper
had raw `ret.$/T -> DemandTarget` rows, but those rows were not selected.
The outer wrapper received no terminal. Run-3 could not re-enter the
wrapper chain. This was a missing use of an existing complete pair. It
was not a source-admission failure.

The correction uses the existing ZERO-exit restriction as a read-only
query. `Dp=ZERO` already accepts both ZERO and Target. The query creates
no stored or enqueued ZERO edge. After this correction, the same pair
accepts the terminal. The source route reports at **run-3** with zero or
two wrappers, in both FULL and GROUP mode.

[VirtualZeroExitTargetTest](../../core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/VirtualZeroExitTargetTest.kt)
is the small store control. It uses no terminal-reader seed. It checks
agreement of the AP ZERO result and Target result for the virtual
`(ret/T, ZERO)` pair. A different mark, a ZERO original, and ZERO initial
admission remain rejected. Thus the correction does not introduce an
entry-only terminal permission.

## Additional check: separate roots cannot complete a NORMAL terminal

The static NNF test also had an old report expectation. Its crossed case
has two separate roots:

```java
// Source actions: C.f gets T; C.g gets U.
void root0() { sourceT(C.f); check(); }
void root1() { sourceU(C.g); check(); }
Box check() {
    Box result = new Box();
    // Exit source rule: CM(C.f,T) AND CM(C.g,U) assigns V to @return.a.b.
    // Exit sink rule: CM(@return.a.b,V).
    return result;
}
```

Run-1 uses the accepted static approximation and can combine the global
supplies. In FULL run-3, the shared callee derives a NORMAL terminal
with the complete premise `{C.f.$/T, C.g.$/U}`. Each root supplies only
one member. Neither root has one complete normal caller binding, so
neither root can derive `ZERO -> NormalTarget`. The final report is
empty in this crossed case. This follows the selected report rule; it
is not a C2 failure or a missing demand edge.

The test now requires that complete two-member callee terminal and
rejects a root ZERO terminal in the crossed case. Its uncrossed case
still requires the positive report when one root supplies both marks.
Source-hit identities, action identities, and forward source seeds
remain checked in both cases. No runtime behavior changed for this test
expectation.

## Latest additional verification

The command below passed **42 tests in seven suites**, with no failures
or errors, after the ZERO-exit adapter correction. Gradle took 8 seconds.
The correctness traces above reached and completed **run-3**.

```sh
# From core
./gradlew :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.VirtualZeroExitTargetTest \
  --tests org.opentaint.dataflow.bidi.Run1StaticExitRoutingTest \
  --tests org.opentaint.dataflow.bidi.StaticCatalogIterationTest \
  --tests org.opentaint.dataflow.bidi.StaticTargetClosureTest \
  --tests org.opentaint.dataflow.bidi.StaticTargetRefinementTraceTest \
  --tests org.opentaint.dataflow.bidi.ControlDemandTest \
  --tests org.opentaint.dataflow.bidi.TargetCallTest \
  --console=plain
```

| Suite | Tests | Result |
|---|---:|---|
| VirtualZeroExitTargetTest | 1 | Pass |
| Run1StaticExitRoutingTest | 17 | Pass; includes separate FULL and GROUP wrapper checks |
| StaticCatalogIterationTest | 1 | Pass; uncrossed positive and crossed negative |
| StaticTargetClosureTest | 9 | Pass |
| StaticTargetRefinementTraceTest | 1 | Pass; latest complete run-3 |
| ControlDemandTest | 7 | Pass |
| TargetCallTest | 6 | Pass |

Receipt: `/tmp/bidi-target-static-zero-exit-probe-tests.log`. The FULL
conditional-source case and the other known GROUP refinement cases are
separate. After the broader FULL layer correction, its valid finding is
restored but its missing-second-input negative caller is reported too.
That NORMAL origin-arm issue remains open. This static result does not
close it or establish project performance.

# Same-mark disjoint return: an uncapped demand cycle

Historical counterexample to whole/per-mark return completion. The
[reply-scoped NORMAL service repair](../design/bidirectional-reply-scoped-point-service-20261116.md)
now stops this unchanged example naturally at run-5, with its NORMAL
observation and an uncapped quiet-suffix proof. The run-11/run-12 recurrence
below is the checked before-change result. Production is unchanged; the
finite native diagnostic still reaches run-31/POLICY.

16 November 2026. Synthetic data-flow reachability. FULL marks.
Follow [proof-guide.md](../../spec/proof-guide.md).
Production is unchanged.

**Before the reply-scoped repair, whole/per-mark completion had this uncapped counterexample.**
It uses three acyclic calls, six positive unary marking rules, and ordinary
field reads. It has no loop, recursion, cleaner, configured pass rule,
unresolved transfer or predefined summary.

The handoff demand sets repeat from **run-9**. The complete reference
state, including result ordering, repeats **run-11/run-12 forever**:
**70/82 demand rows**, ten persisted NORMAL rows, and no completed point
or mark-scoped point. Both completion mechanisms remain enabled. A NORMAL
observation is retained from **run-5**, but a separate DemandTarget still
renews the analysis. No hard iteration limit enters the proof.

Latest finite native diagnostic: **run-31, POLICY**. Its NORMAL report count
is zero; the proposal reference has a NORMAL observation from run-5.
This difference is an explicit validation limit, explained below.

## 1. Code and rules

```java
class Box { Box f; Box g; Box h; Box k; }

// Entry marking: assign T only at a.f.g.$.
void root(Box a) {
    Box x = make(a).h;
    Box y = make(x).h;
    Box z = make(y).h;
    // Observation: CM(z.M,U).
}

Box make(Box p) {
    Box r = new Box();
    // Six ordinary positive unary rules at this point:
    // CM(p.f.g.g.M,T) => assign U to r.h.MUST.
    // CM(p.M,T)       => assign U to r.h.h.MUST.
    // CM(p.M,T)       => assign U to r.k.MUST.
    // CM(p.f.g.g.M,U) => assign T to r.h.MUST.
    // CM(p.M,U)       => assign T to r.h.h.MUST.
    // CM(p.M,U)       => assign T to r.k.MUST.
    return r;
}
```

`$` = EXACT; `*` = correlated STAR; M = MAY; NE = nonempty MAY;
MUST = uniform mark. N/D are NORMAL/DEMAND. E and mark exclusions are
empty. Every H membership is plain. Both full marks are assigned and used
in CM, so executable-rule mark reduction cannot remove either mark.

Each `.h` is an ordinary read after the call. The native fixture builds it
with `MicroEdgeBuilder.read`. It is not a configured pass rule. The only
call-graph edge is `root -> make`; repeated call sites are not recursion.

The complete per-block cold trace is in
[the companion trace](bidirectional-unadmitted-field-trace-20261116.md).
It lists every paired demand, submitted fact, emitted initial, current
NORMAL/DEMAND summary, and root packet through run-12. Forward inputs
appear above each body and summaries below it. Backward placement reverses
this order. Each later pair repeats the checked run-11/run-12 state.

## 2. Why the latest repair does not close this case

At the first call, the precise offered input is `p.f.g.$/T,N` from run-3.
The deep `p.f.g.g.M/T` guard rejects this exact point. The other two T
conditions succeed:

```text
complete raw NORMAL returns of the fine query:
    p.f.g.$/T -> ret.h.h.MUST/U, N
    p.f.g.$/T -> ret.k.MUST/U,   N
```

The caller reads `.h`, so its backward demand selects `ret.h...`.
C5 admits the first result and rejects the disjoint second result:

```text
ret.h.h.MUST/U intersects ret.h.*/U = ret.h.h.MUST/U
ret.k.MUST/U   intersects ret.h.*/U = empty
```

Both outputs have **the same full mark U**. The previous counterexample
had an unused V output; full-mark completion correctly ignored V when
certifying U. Here, complete U service must also cover `ret.k.MUST/U`.
It does not. The exact query therefore obtains neither the whole certificate
nor the U certificate. The homogeneous-output theorem proves that mark
projection adds no partial certificate for any query/store in this body.
This is a genuine failed coverage check, not a disabled completion feature.

The other, coarse initial is still present:

```text
p.f.*/T, D
    deep guard may match
    -> ret.h.M/U, D
    ordinary caller read .h
    -> x.M/U, D
```

The fine service takes a different route:

```text
p.f.g.$/T, N -> ret.h.h.MUST/U, N
    ordinary caller read .h
    -> x.h.MUST/U, N
```

`x.h.MUST/U,N` cannot cover the whole `x.M/U,D` region. The actual-packet
coverage rule therefore keeps both. The later two calls renew root MAY
with alternating U/T/U. All calls share the same `make` owner, which
receives both fine inputs and root-MAY inputs. Its next C2 family continues
to contain broad STAR starts as well as its bounded field children.

No NORMAL FLOW relation can produce the mark change T -> U or U -> T on
the freshly allocated return object. The absence of a correlated FLOW
provider here is a consequence of the ordinary code and literal actions.

## 3. The repeating demand

For each `m` in `{T,U}`, let `flip(T)=U` and `flip(U)=T`.
The forward summary set contains:

```text
p.f.*/m -> ret.h.M/flip(m), D
```

Thus its next backward paired demand contains:

```text
[entry = ret.h.M/flip(m) | output = p.f.*/m]
```

The backward run also publishes a broad-input arm:

```text
ret.h.*/flip(m) -> p.M/m, D
```

Its next forward paired demand contains:

```text
[entry = p.M/m | output = ret.h.*/flip(m)]
```

This latter demand admits the coarse first-field start again. Backward
ordinary `.h` reads prepend the known h field before reverse call
application. The broad CM arm has no concrete input field, so it still
produces root MAY. NE progress on the separate deep arm does not eliminate
this broad arm.

These displayed rows are witnesses inside the complete paired frontier;
the proof does not replace that frontier with these rows. The full
frontier has 70 forward-handoff and 82 backward-handoff rows.

## 4. Uncapped proof

The reference uses schedule `1,1,2,3,...`. It applies C2, bounded
first-field children, ordinary field cuts to NE, paired C5, persisted
NORMAL replay, native-style reply matching, actual-packet coverage,
whole and mark-scoped completion, and accumulating ZERO/Target permissions.
Every summary output still passes C5 before publication. No unbounded
NORMAL candidate archive or loss-evidence composition is introduced.

The key constructive result is:

```text
forall n >= 0:
    history(11 + 2*n) = stableForward
    history(12 + 2*n) = stableBackward

stableForward.rows.size  = 70
stableBackward.rows.size = 82
stableForward.TargetDemand = true
stableBackward.entryMarkingPermission = true
```

`FieldCold` checks the complete cold prefix through run-10 and a
within-run fixed point at each run. `FieldRounds` checks every delivery
and publication stage at an arbitrary budget `8+n`. `FieldSteady` checks
saturation at every such budget and later run parity. `FieldRecurrence`
connects the cold prefix to run-11 and proves the displayed identities by
induction. It proves membership of the repeating rows and failure of the
stop test at every later forward run. No earlier odd run satisfies that
stop test either. Finite counts are not the induction hypothesis.

The within-run states are fixed points, so the result does not depend on
the reference's eight-round evaluation bound or on a worklist starvation
policy. The root Target flag includes every emitted DemandTarget during
the run; it is not canceled by later NORMAL service. NormalTarget is
retained and ignored backward as selected.

All E/mx remain empty and H stays plain. The input-family proof retains
both the global cap and Dc+1. Paired output publication retains the
original Dp+1 cap. The unchanged NORMAL-MUST/nonempty-E exception is
ineligible here. This counterexample needs **no new cap exception** and
continues after the global cap can represent every code path.

## 5. Checks and scope

Proofs and the runnable checker are in
[unadmitted-field-cycle-20261116](../../spec/lean/proposals/unadmitted-field-cycle-20261116/README.md).
The checker source-compares the selected admission, C5/reply adapters,
whole/scoped completion, persistence and Target functions with the latest
`ScopedBody` baseline. Only the synthetic leaf program and the caller's
ordinary h reads change. Production policy does not change.

```bash
ELAN_TOOLCHAIN=leanprover/lean4:v4.35.0 \
python3 spec/lean/proposals/unadmitted-field-cycle-20261116/check.py \
  --out /tmp/unadmitted-field-proofs

./core/gradlew -p core :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.UnadmittedFieldCycleTest \
  --tests org.opentaint.dataflow.bidi.CompletePointServiceNativeTest \
  --tests org.opentaint.dataflow.bidi.ScopedPointServiceNativeTest --offline
```

The proof audit passes **177 new constructive claims; 5,766 cumulative claims
in 293 source-hash-checked modules**. No classical choice, custom axiom or
native evaluator is used.

The 15 native tests pass: three new tests and twelve retained completion
controls. The new native checks establish the same-mark disjoint C5
rejection, the ordinary h-read results, and run-31/POLICY with an outgoing
DemandTarget. They do not install the proposed NE/completion mechanism.
The unchanged native diagnostic has zero NORMAL reports, while the
proposal reference retains one from run-5. No whole-engine equivalence,
JVM/alias refinement theorem or project-performance result is claimed.

The uncapped counterexample is to the preceding executable proposal model,
before reply-scoped completion, with all its then-selected repairs enabled. Its proof is independent of the finite native
run limit. No repair for this new case is selected in this report.

Raw captures, test XML and compiled proofs are outside the repository under
`/drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/unadmitted-field-cycle-20261116/`.
All fact samples needed to understand the counterexample are embedded in
the report and companion trace.

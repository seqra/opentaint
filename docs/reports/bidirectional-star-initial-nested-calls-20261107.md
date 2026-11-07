# STAR initials: a nested-call coverage gap

Date: 7 November 2026. Language: ASD-STE100 Simplified Technical English.
Runtime source: `7069fe2d7`; source HEAD at capture: `0a2846c44`.
The user selected FULL conversion. Production source was unchanged at capture.

**Replacing emitted MAY with STAR and updating its image is insufficient.**
The current policy reports all four programs below. The FULL policy copy
loses the finding when an ordinary getter is wrapped in another method.
Both policies stop naturally at run-3. This is a correctness gap, not a
timeout or an insufficient field limit.

## 1. Program and result

All referenced objects and the Element slot are initialized finite-IR
preconditions. There is one exact T source and one exact T sink. The fixture
uses ordinary field-write/read and resolved-call operations. It supplies no
demand, initial, saved summary or source permission.

```java
void main() {
    Object s = sourceExactT();
    temp.g = s;
    next.f = temp;
    Object x = getF(next);
    Object y = wrapG(x);    // The direct control calls getG here.
    out.Element.h = y;
    sinkExactT(out.Element.h);
}

Object getF(Object p) {
    return p.f;
}

Object wrapG(Object p) {
    Object tmp = getG(p);
    return tmp;
}

Object getG(Object p) {
    return p.g;
}
```

The source assigns `s.$/T`, NORMAL. The sink checks `out.Element.h.$/T`.
On concrete execution, `next.f.g` is s, so the wrapper preserves the same
real flow as the direct control. Limits are `1,1,2,3,...`; limit 2 represents
both two-field chains. All variants use FULL marks, one CPU and a 1 GiB test
worker. These are native diagnostics, not project performance runs.

| Case | Current policy | FULL conversion | Latest reached/complete run, both |
| --- | --- | --- | --- |
| Direct getF and getG | One NORMAL finding in run-3 | One NORMAL finding in run-3 | run-3 / run-3 |
| One wrapper around getG | One NORMAL finding in run-3 | No finding | run-3 / run-3 |
| Two wrappers around getG | One NORMAL finding in run-3 | No finding | run-3 / run-3 |
| One wrapper around each getter | One NORMAL finding in run-3 | No finding | run-3 / run-3 |

Every case ends COMPLETE / NO_DEMAND_EDGE. Current JUnit is 4/4 green.
The FULL suite has one pass and three failed expected-one-report assertions.
No assertion was weakened. The exact same source program runs under both
classpaths; the FULL copy overlays only RestrictedInitialPolicy.

## 2. First missing admission in the one-wrapper case

`F` means FLOW. `N` means NORMAL; `D` means DEMAND. All displayed exclusions
are empty, and all displayed facts are unprotected.

Both run-1 traces are equal as multisets for every case. For getG they
contain the exit tuple:

```text
P = arg(0).*/F
C = ret.[any]/F, D
```

The ordinary run-1 publication and handoff rules give the backward pair
`Dc = ret.[any]/F`, `Dp = arg(0).*/F`. This pair is source-derived from the
captured exit tuple and HandOff; it is not a directly dumped demand-store row.

The following trace uses the same one-wrapper program. Produced relations
are shown after each declaration. The facts at wrapper's inner call are
directly observed; binding to the callee and C2 rejection are derived from
the pinned ordinary call plan and native policy.

```java
// Run-2 entry, current:
//   initial/start ret.[any]/F, D
// Run-2 entry, FULL copy:
//   initial/start ret.*/F, N
Object wrapG(Object p) {
    Object tmp = getG(p);
    // Backward arrival BEFORE this call:
    //   current: tmp.[any]/F, D
    //   FULL:    tmp.*/F, N
    // Reverse bind maps tmp to callee ret and preserves tail/layer.
    return tmp;
}
// Current backward exit tuple: ret.[any]/F -> arg(0).g.[any]/F, D.
// FULL: no corresponding DATA exit tuple.

// Run-2 demand: Dc=ret.[any]/F, Dp=arg(0).*/F.
// Current submitted: ret.[any]/F, D; emits ret.[any]/F, D.
// FULL submitted:    ret.*/F, N; emits NOTHING under the unchanged STAR cell.
Object getG(Object p) {
    return p.g;
}
// Current backward exit tuple: ret.[any]/F -> arg(0).g.[any]/F, D.
// FULL: complete run-2 processed trace has no getG rows.
```

The decisive current branch is:

```kotlin
if (submitted.path == demand.path && demand.tail == ANY) {
    when (submitted.tail) {
        STAR -> null
        // The selected conversion only maps existing ANY outputs.
        // It cannot change this already absent output.
    }
}
```

The candidate's image predicate accepts the new STAR output shape. That
does not make the emitter accept a submitted STAR. Output-image membership
and actual-input admission are different checks.

## 3. Consequence and evidence boundary

Current run-2 enters getG, reaches `arg(0).g.[any]/F` and continues through
the wrapper. In current run-3, the trace contains the root T source and
getG's exact/FLOW return, and the finding is reported.

The FULL run-2 trace has no getG processing. Its run-3 root has only seven
ZERO events, no T source event, and no getG event. It stops with no outgoing
demand and no finding. Thus the failure also removes required later source
guidance; it is not merely a different number of callbacks.

These are complete frozen fixture process-event traces, each below 2,000
events. The callback runs immediately before processing its EdgeDelta. They
are not post-statement-storage snapshots. The callee-bound ret fact and
the exact handoff pair above are source-derived. No raw rejected-C2 callback
was captured. The complete program result establishes the regression even
with those observation limits.

The previous original four-method loop test still passes under FULL
conversion, first reporting at run-3 and completing at run-5. It has no such
extra wrapper. That positive result does not cover this new negative case.
No LicenseKeyChecker or other real-project cause is inferred from this test.

## 4. Concrete-mark wrapper control

A second independent native fixture has a guarded source conversion and no
FLOW input-to-return route:

```java
Object convert(Object p) {
    return newInitializedContainer();
}
// Converter source rule: CM(p.[any], T) assigns U at ret.f.g.$.

Object wrap(Object p) {
    return convert(p);
}

void main() {
    Object t = sourceExactT();
    Object result = wrap(t); // Direct control calls convert(t).
    sinkExactU(result.f.g);
}
```

The converter's native statement has one source edge with its real source
action: `arg.[any]/T -> ret.f.g.$/U`. It is a rule transfer, not a supplied
method summary. With run-1 limit 1 its two-field target is cut to MAY.

| Concrete case | Current | Plain FULL conversion | Latest reached/complete run |
| --- | --- | --- | --- |
| Direct converter | One NORMAL finding | One NORMAL finding | run-3 / run-3 |
| One wrapper | One NORMAL finding | No finding | run-3 / run-3 |

Current JUnit is 2/2 green; the plain-FULL suite fails its wrapped finding
assertion. Both stop COMPLETE / NO_DEMAND_EDGE. At the run-2 inner call the
observed wrapper fact is `tmp.f.[any]/U, D` under current policy, versus
`tmp.f.*/U, D` under the copy. Current enters convert and reaches `arg.[any]/T`;
the copy has no convert rows. The ordinary bind maps tmp to callee ret.
Thus this gap also concerns concrete STAR/DEMAND, not only FLOW's layer change.

## 5. Selected resolution

FULL conversion remains selected. A direct ordinary-STAR extension considered
during the investigation was:

```text
demand:    x.p.[any]/M
submitted: x.p.*/M
emit:      x.p.*/M

FLOW output starts NORMAL; concrete output stays DEMAND.
Keep base/mark/budget/shape guards and empty-exclusion requirements explicit.
```

Admitting only NORMAL STAR/FLOW addresses the displayed local cell but
leaves concrete-STAR forwarding as a separate obligation. Admitting both
mark forms closes that self-composition cell, but needs a refinement/progress
proof because the submitted STAR adds no new field to the MAY demand.
Neither choice was silently included in the implemented source.

The user instead selected a new intra-procedural **STAR_OR_ANY** tail. It
uses STAR data behavior and special initial admission, and normalizes to STAR
before summary/demand storage. Ordinary STAR rejection remains unchanged.
The [new spec](../../spec/intra-procedural-star-or-any.md) and
[implementation proposal](../design/bidirectional-star-or-any-initials-implementation-20261107.md)
define that resolution. The new model/native gates must pass before a core
patch lands. These measurements are of the failed plain-STAR copy, not an
execution of the new marker design.

## 6. Portable evidence

The [embedded evidence](data/bidirectional-star-initial-nested-calls-20261107.json)
contains both complete process-event traces and test logs, JUnit XML, exact
source programs/candidate diffs, frozen ordered classpaths, loaded-source
checks, source pins, the first-loss decoder and its line references. The
root comparison verifies all four equal run-1 trace multisets and preserves
the three failed expected-report checks. The concrete two-case appendix has
its own frozen inputs/results and preserves its failed wrapper assertion.
No historical project was rerun.

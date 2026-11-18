# Prefix return: saved summary exists, but demand service is lost

17 November 2026. Synthetic data-flow reachability. FULL marks.
Latest reached iteration: **run-5**, natural `NO_DEMAND_EDGE`.
Follow [proof-guide.md](../../spec/proof-guide.md).
[Consolidated proposal](../design/bidirectional-demand-termination-approach-20261115.md).
Production is unchanged.

**Historical confirmed soundness gap; proposal repair validated.**
The [additional possible DIRECT replay](../design/bidirectional-saved-direct-possible-replay-20261117.md)
now retains the NORMAL observation and empties demand at **run-5** in the
reference. Native components check the repaired run-4/run-5 path. The
unchanged production driver and this pre-repair trace still expose the loss.

**Before repair:** A helper has the needed NORMAL summary
from run-2. In run-4, its caller submits a STAR fact above the summary's
premise. Saved replay is in the same direction, so STAR-inside matching is
not allowed. The helper has no current demand and starts no query. The
caller loses its remaining guide, then finishes at run-5 without a real
observation.

The gap appears in the current native engine and in the updated proposal
reference with NE, current C2, raw owned-query permission, paired C5 and
both field caps. R31, R32, F72, protection and mark-group behavior do not
repair it. The repair above is a separate explicit matching change; the
original trace below is retained unchanged.

## 1. Minimal ordinary code

```java
void main() {
    Node x = new Node();
    markBelowG(x);                  // Assign T at x.g and all descendants.
    Node r = wrap(x);
    observeBelow(r);                // CM(r.MAY, T).
}
Node wrap(Node x) {
    Node a = x.g.g;
    Node b = keepF(a);
    Node c = new Node(); c.g = b;
    Node y = new Node(); y.g = c;
    return y;
}
Node keepF(Node x) {
    Node y = new Node(); y.f = x.f;
    return y;
}
```

There is one call to wrap. Each method is straight-line code. There is no
loop, recursion, cleaner, ND condition, configured pass rule, static,
unresolved body, alias target or overwrite of an existing field region.
Writes construct fresh objects. Fields f and g are distinct.

A concrete NORMAL path exists:

```text
x.g.MUST/T
    -- read x.g.g --> a.MUST/T
    -- keepF ------> b.f.MUST/T
    -- c.g=b ------> c.g.f.MUST/T
    -- y.g=c ------> y.g.g.f.MUST/T
```

Thus the point `r.g.g.f.$/T` satisfies the broad observation. There is no
claim that an uncertain MAY fact is a NORMAL witness. The witness above is
a definite uniform region with a concrete marked point.

## 2. Rules that interact

```text
saved NORMAL replay first
then current demand admission; no relevant demand => no current query

incoming STAR inside a deeper saved premise:
    SAVED_OPPOSITE: possible result, DEMAND
    SAVED_DIRECT:  no match

NE demand at its own head:
    emit STAR; no exact-at-head initial

real field cut:
    keep the bounded prefix; emit NE, DEMAND
```

All these mechanisms can be locally correct. Their composition needs an
alternative service route. This example lacks that route. The needed field
f is in keepF's saved guard; it is not in wrap's own demand or NORMAL return
snapshot, so wrap's prepared next-field set is empty.

Notation: F=FLOW, N=NORMAL, D=DEMAND. `ret` denotes the declared method's
return position. A backward demand is shown as `(Dc; Dp)`. All E and mx are
Empty, and all protection memberships are plain. No field ban is present.

The tables below list return-service rows. ZERO identities and unchanged
argument identities are retained. An argument-only identity cannot match
the return offer at keepF or produce main's fresh result variable r.

## 3. Run-1: forward, field limit 1

```java
// Demand: unrestricted. Submitted/initial control: ZERO,N.
void main() {
    Node x = new Node();
    markBelowG(x);                  // x.g.MUST/T,N, within limit 1.
    Node r = wrap(x);               // r.g.NE/T,D.
    observeBelow(r);                // DEMAND witness.
}
// Published: ZERO -> DemandTarget,D; ZERO -> ZERO,N.

// Submitted: x.g.MUST/T,N. Initial: x.*/F,N.
Node wrap(Node x) {
    Node a = x.g.g;                 // a.MAY/F,D.
    Node b = keepF(a);              // b.f.MAY/F,D.
    Node c = new Node(); c.g = b;    // A real cut is needed.
    Node y = new Node(); y.g = c;
    return y;
}
// Published return: x.*/F -> ret.g.NE/F,D.
// Also retain the NORMAL unchanged-argument and ZERO identities.

// Submitted: x.MAY/F,D. Initial: x.*/F,N.
Node keepF(Node x) {
    Node y = new Node(); y.f = x.f;  // y.f.MAY/F,D; f fits limit 1.
    return y;
}
// Published return: x.*/F -> ret.f.MAY/F,D.
// Also retain the NORMAL unchanged-argument and ZERO identities.
```

The helper's MAY is an unknown-read result, not a cut at f. The wrapper's
NE is a real field cut. This distinction stays active in the new model.

## 4. Run-2: backward, field limit 1

```java
// main: the backward route reaches the marking action and permits run-3.
void main() {
    Node x = new Node();
    markBelowG(x);
    Node r = wrap(x);
    observeBelow(r);                // Seed r.MAY/T,D.
}
// Demand: Target -> ZERO. Control initial: ZERO.
// The successful reverse-source route permits the marking action in run-3.

// Published return service: ret.g.*/F -> x.g.NE/F,D.
Node wrap(Node x) {
    Node a = x.g.g;
    Node b = keepF(a);              // Backward offer to keepF: ret.MAY/F,D.
    Node c = new Node(); c.g = b;
    Node y = new Node(); y.g = c;
    return y;
}
// Demand (Dc; Dp): (ret.g.NE/F; x.*/F).
// Submitted: ret.MAY/T,D. Initial: ret.g.*/F,N.

// Published NORMAL return service: ret.f.*/F -> x.f.*/F,N.
Node keepF(Node x) {
    Node y = new Node(); y.f = x.f;
    return y;
}
// Demand (Dc; Dp): (ret.f.MAY/F; x.*/F).
// Submitted: ret.MAY/F,D.
// Initials: ret.f.$/F,N and ret.f.*/F,N.
// Both valid raw starts normalize to the same admitted NORMAL FLOW record.
```

Removing the first known g at wrap leaves STAR. Removing the second,
unknown g produces MAY. MAY can reach keepF's known f guard. The NORMAL
helper record is fully computed and persisted at this point.

## 5. Run-3: forward, field limit 2

```java
// Demand/source permission: retained by run-2. Control initial: ZERO.
void main() {
    Node x = new Node();
    markBelowG(x);                  // x.g.MUST/T,N.
    Node r = wrap(x);               // r.g.g.NE/T,D.
    observeBelow(r);                // DEMAND witness remains.
}
// Published: ZERO -> DemandTarget,D; ZERO -> ZERO,N.

// Demand (Dc; Dp): (x.g.NE/F; ret.g.*/F).
// Submitted: x.g.MUST/T,N. Initial: x.g.MUST/F,N.
Node wrap(Node x) {
    Node a = x.g.g;                 // a.MUST/F,N.
    Node b = keepF(a);              // Saved opposite NORMAL: b.f.MUST/F,N.
    Node c = new Node(); c.g = b;
    Node y = new Node(); y.g = c;    // Raw y.g.g.f.MUST/F,N has FL=3.
    return y;
}
// Published return: x.g.MUST/F -> ret.g.g.NE/F,D.
// No NORMAL return summary for wrap is available.

// Demand: empty. Submitted: x.MUST/F,N.
// Current initial: none; saved NORMAL replay runs first.
Node keepF(Node x) {
    Node y = new Node(); y.f = x.f;
    return y;
}
// Current return summaries: none required.
// Saved backward record, read in the opposite direction:
//     x.f.*/F -> ret.f.*/F,N.
```

The cut is correct and mandatory:

```text
raw return FL = 3
budget = min(globalLimit=2, FL(own paired Dp ret.g.*)+1=2)
ret.g.g.f.MUST/F,N -> ret.g.g.NE/F,D
```

The same-lane NORMAL-MUST replacement does not apply: wrap has no retained
uncut NORMAL return provider. The child-flow service and concrete completion
rules add no such record. This is not a case for exceeding either cap.

The actual next demand is:

```text
(Dc=ret.g.g.NE/F; Dp=x.g.MAY/F)
```

The existing handoff projects the forward MUST premise to its backward MAY
guidance. Neither demand endpoint has a MUST initial or nonempty mx.

## 6. Run-4: backward, field limit 3 — first lost service

```java
// main: no reverse marking hit; no new source permission is produced.
// ZERO identities may remain, but they cannot create the marked DATA route.
void main() {
    Node x = new Node();
    markBelowG(x);                  // The marked requirement never reaches here.
    Node r = wrap(x);
    observeBelow(r);                // Seed r.MAY/T,D as before.
}
// Demand: Target -> ZERO. Submitted/initial control: ZERO.

// Published return DATA: none.
Node wrap(Node x) {
    Node a = x.g.g;
    Node b = keepF(a);              // Backward offer: ret.*/F,N.
    Node c = new Node(); c.g = b;
    Node y = new Node(); y.g = c;
    return y;
}
// Demand (Dc; Dp): (ret.g.g.NE/F; x.g.MAY/F).
// Submitted: ret.MAY/T,D. Initial: ret.g.g.*/F,N.
// No ret.g.g.f child is observed in wrap's own frozen snapshot.

// Published current return DATA: none.
Node keepF(Node x) {
    Node y = new Node(); y.f = x.f;
    return y;
}
// Demand: empty. Submitted: ret.*/F,N. Initials: none.
// Saved record: ret.f.*/F -> x.f.*/F,N, learned in backward run-2.
// Read role: SAVED_DIRECT (backward record in a backward run).
// ret.* cannot use the deeper ret.f.* guard in this role.
```

Here both g fields are known. Reverse packing removes them without an
unknown read, so the helper receives STAR instead of run-2's MAY.

```text
run-2: ret.g.*   --remove g,g--> ret.MAY -> helper saved/current f case
run-4: ret.g.g.* --remove g,g--> ret.*   -> same-direction saved f case rejects
```

The helper's current demand is empty because its return was already served
by a NORMAL record. Saved-first replay is attempted. Its match fails.
The ordinary call policy then skips current analysis. No current-summary
publication or subscription can recover the missing field f.

A deeper wrapper initial at `ret.g.g.f` would fit both run-4 input caps,
but no selected mechanism derives that child from the callee's f guard.
A blanket statement that a child exists is not a complete child-service
proof. The existing prepared plan only uses the owner's qualified rows and
retained NORMAL guards.

## 7. Run-5: forward, field limit 4 — natural loss

```java
// No successful run-4 marking permission; control can still reach main.
void main() {
    Node x = new Node();
    markBelowG(x);
    Node r = wrap(x);
    observeBelow(r);
}
// No NormalTarget or DemandTarget. Natural NO_DEMAND_EDGE at run-5.

// Demand: empty. Saved NORMAL return service: empty.
// Actual DATA offer: none in the permission-gated native execution.
// Even an optimistic x.g.MUST/T,N offer yields no reply.
// Current initials: none.
Node wrap(Node x) {
    Node a = x.g.g;
    Node b = keepF(a);
    Node c = new Node(); c.g = b;
    Node y = new Node(); y.g = c;
    return y;
}
// No current DATA summary. Argument identities cannot return r.

// No call reaches this helper for DATA. Demand: empty; initials: none.
Node keepF(Node x) {
    Node y = new Node(); y.f = x.f;
    return y;
}
// Its NORMAL f-to-f record is still stored, but has no active caller route.
```

The reference grants the original source again even after run-4. It still
gets no reply. The lack of service therefore does not depend on blaming
source-permission handling. With no outer demand and no saved outer return
record, C2 starts no body at any larger limit. Local lemmas quantify this
absence over every run/limit. No run-11 cutoff is used.

## 8. Controls, proof scope and next design obligation

Changing the observation to `CM(r.g.g.f.$,T)` keeps the same real path and
produces one NORMAL finding at run-5. The named field f enters the backward
question and matches the saved helper guard. The broad observation is a
semantic superset; it must not lose this finding.

| Native execution, no iteration-count cutoff | NORMAL findings | Latest natural run |
|---|---:|---|
| Minimal one-call code, broad observation | **0, no provisional finding** | run-5 |
| Minimal one-call code, named g.g.f observation | 1 | run-5 |
| Full old case 165, broad observation | **0, no provisional finding** | run-5 |
| Full old case 165, named observation | 1 | run-5 |
| Full old case 884, broad observation | 1 | run-5 |
| Full old case 884, named observation | 1 | run-5 |

The native matcher control separately verifies that the same root STAR
matches the deeper guard only under SAVED_OPPOSITE; MAY can match it under
SAVED_DIRECT. These are existing behaviors, not enabled repair switches.

[Lean package](../../spec/lean/proposals/ordinary-alignment-audit-20261117/README.md):
25 new constructive claims; **7,212 cumulative claims in 417 hash-checked
modules**. The model imports the latest C2, keeps the prepared children,
raw-own-query C5, normal precoverage, NE cuts, real E operators and saved
record directions. Every cold run reaches its full within-run fixed point.
It computes the stored NORMAL helper record, the mandatory cut, the empty
run-4 service, final loss and all-limit absence of outer replay. The updated
884 control retains its NORMAL point at run-5.

The formal state is the unary return cone, not the entire JVM/Target driver.
It deliberately grants backward observation and forward source inputs,
which strengthens service compared with the failed native run. The native
cold tests validate typed Targets, source permission, actual binding and
natural stopping separately. Unchanged argument-only summaries are present
natively; they cannot supply this return route. No whole-analyzer proof is
claimed.

[Native regression/components](../../core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/OrdinaryAlignmentSoundnessTest.kt)
add seven tests; the combined targeted suite passes **77 tests**. Two tests
assert the known broken broad-observation behavior as diagnostics. They must
require the finding after a repair. Passing this suite does not certify the
current proposal sound.

The earlier 1,536-case search remains valid in its conditional-marking
helper scope. It did not include a caller that removes and then restores a
known field prefix around a separate callee. It therefore did not exercise
this change from a MAY call offer in run-2 to a same-direction STAR offer
in run-4. No earlier local theorem is promoted to a general service proof.

The open obligation is service across this boundary: a bounded unknown
caller question must retain a route through a deeper NORMAL callee guard,
even when the callee has no current demand. A repair must construct that
route or prove a complete substitute. Merely retaining the callee record,
replaying it first, or raising the global field limit is insufficient.
Do not bypass FL+1, add full suffix evidence, or relax saved STAR matching
without a separate correctness and workload argument. R34 now supplies
that explicit possible-replay repair, with constructive local coverage,
unchanged caps, the repaired cold run-5 result and measured extra work in
two older reference cases. The general whole-engine obligation stays open.

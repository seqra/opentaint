# Soundness follow-up after the run-2 STAR repair

17 November 2026. Synthetic data-flow reachability. FULL marks.
[Consolidated proposal](../design/bidirectional-demand-termination-approach-20261115.md).
Follow [proof-guide.md](../../spec/proof-guide.md). Production is unchanged.

## 1. Finding: a missing handoff step in a candidate model

The run-2 STAR repair remains selected. The next candidate involved a
wrapper, a field read and an unrelated selected-mark cleaner. A model that
retains a FLOW summary's mark exclusions in the next demand loses a valid
U observation at run-3. The native controls **rule out this counterexample**:
the existing AP F72 handoff clears those exclusions from demand endpoints.
The actual nested example retains one NORMAL U observation and completes
naturally at **run-3**.

The consolidated document now states this reused boundary rule explicitly.
This is a specification/model clarification, with **no new transfer or C2
semantics**. A local C2 rejection for an excluded-mark demand does not prove
that the native handoff can produce that demand.

```text
projectDemandEndpoint(a):
    return a with mx={} if a.mark == FLOW else a

handoff(DEMAND P -> C):
    Dc = projectDemandEndpoint(C)
    Dp = projectDemandEndpoint(P)
    apply the existing tail/field/port projection
    retain that paired row

runtime actuals:                 keep mx
admitted summaries and records:  keep mx
next-run FLOW demand endpoints:  mx={}
```

This is [AP §3.4](../../spec/ap.md), including the F72 note on MarkSlot and
§9.2 handoff. Native `DemandStore.Builder` checks that demand marks are
normalized. It does not accept a FLOW endpoint with nonempty mx.

## 2. Principal example and trace

```java
void main() {
    Box a = new Box();
    markUField(a);       // Rule: assign U exactly at a.f; U != T.
    Box r = wrap(a);
    observeU(r);         // Rule: CM(r.$, U).
}
Box wrap(Box p) {
    return get(p);
}
Box get(Box p) {
    Box r = p.f;
    clearTRoot(r);       // Rule: remove T exactly at r.$.
    return r;
}
```

There is no loop, recursion, alias, ND, unresolved transfer or real field
cut. The synthetic cleaner has an exact keep form around its rule action;
it does not rely on an unresolved library model. The source at a.f becomes
r.$/U and survives the unrelated T cleaner.

F is FLOW; N/D are layers. `mx={T}` is a mark exclusion, not a field hole.
Argument and ZERO identities are included where they matter.

```java
// RUN-1, forward, limit 1.
// Demand: unrestricted; submitted/initial: ZERO,N.
void main() {
    Box a = new Box();
    markUField(a);               // a.f.$/U,N.
    Box r = wrap(a);             // r.MAY/U,D.
    observeU(r);                // DEMAND witness.
}
// Published: ZERO -> DemandTarget,D; ZERO -> ZERO,N.

// Submitted: p.f.$/U,N. Initial: p.*/F,N.
Box wrap(Box p) {
    return get(p);              // Submit p.*/F,N.
}
// Published:
//   p.*/F -> ret.MAY/F,mx={T},D
//   p.*/F -> p.*/F,N
//   ZERO -> ZERO,N

// Submitted: p.*/F,N. Initial: p.*/F,N.
Box get(Box p) {
    Box r = p.f;                // r.MAY/F,D: unknown suffix read.
    clearTRoot(r);              // r.MAY/F,mx={T},D.
    return r;
}
// Published:
//   p.*/F -> ret.MAY/F,mx={T},D
//   p.*/F -> p.*/F,N
//   ZERO -> ZERO,N
```

The cleaner may request T. Any T-only rows do not handle U and do not
supply the structural unmasked FLOW probe. They are not disabled in the
native test. The retained NORMAL argument identity has no return premise;
main does not read a after the call, so it is not the marked return route.

```java
// RUN-2, backward, limit 1. Summaries ABOVE the methods.
// main: the existing reverse-source/Target route permits markUField.
void main() {
    Box a = new Box();
    markUField(a);
    Box r = wrap(a);
    observeU(r);                // Seeds r.$/U,N.
}
// Demand: Target -> ZERO. Submitted/initial control: ZERO.

// Published: ret.*/F -> p.f.*/F,mx={T},N.
Box wrap(Box p) {
    return get(p);              // Submit ret.$/F,N to get.
}
// Demand pair (Dc;Dp): (ret.MAY/F,mx={}; p.*/F,mx={}).
// Submitted: ret.$/U,N. Initial: ret.$/F,N.

// Published: ret.*/F -> p.f.*/F,mx={T},N.
Box get(Box p) {
    Box r = p.f;                // Backward: r.$/F -> p.f.$/F.
    clearTRoot(r);              // Backward first: r.$/F gains mx={T}.
    return r;
}
// Demand pair (Dc;Dp): (ret.MAY/F,mx={}; p.*/F,mx={}).
// Submitted: ret.$/F,N. Initial: ret.$/F,N.
// Raw C5 accepts the EXACT initial; normalization stores the FLOW STAR pair.
```

The invalid candidate omitted F72 and used `ret.MAY/F,mx={T}` as Dc. It then
rejected the wrapper's `ret.$/F,mx={}` because `{T}` is not a subset of `{}`.
The real Dc has Empty mx; it accepts this probe. R32's STAR-to-STAR cell is
inactive. R31's disjoint-cleaner branch is also inactive at the cleaned root.

```java
// RUN-3, forward, limit 2.
// Demand: source/control route; submitted/initial: ZERO.
void main() {
    Box a = new Box();
    markUField(a);               // a.f.$/U,N.
    Box r = wrap(a);             // Saved NORMAL replay returns r.$/U,N.
    observeU(r);                // NORMAL witness.
}
// Published: ZERO -> NormalTarget(id),N.
// No outgoing refinement demand; natural completion at run-3.

// No current DATA initial needed. Submitted: p.f.$/U,N.
Box wrap(Box p) {
    return get(p);
}
// Use the reversed saved NORMAL relation. Its input excludes T.
// U is allowed. Return ret.$/U,N. No new DATA summary is required.

// No new get invocation is needed; wrap has its own saved summary.
Box get(Box p) {
    Box r = p.f;
    clearTRoot(r);
    return r;
}
// Saved record retains mx={T}; the handoff projection did not change it.
```

Replacing U by an exact T mark at a.f leaves no finding after run-3. Empty
mx on guidance does not remove the cleaner's real transfer or the saved
record's mask. This control is about an exact point; it does not undo the
accepted same-head MUST cleaner approximation.

## 3. Checked scope

[Constructive proof package](../../spec/lean/proposals/handoff-mask-audit-20261117/README.md)
adds **27 claims**, bringing the audited chain to **7,187 claims in 413
hash-checked modules**. Sixteen claims describe the deliberately invalid
unprojected countermodel and its local cells. Eleven establish the real
projection and corrected trace. The wrapper induction is over arbitrary
finite depth. These are not 27 claims of whole-engine soundness.

[Native tests](../../core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/MaskedFlowRelaySoundnessTest.kt)
use the unmodified driver, transfers, C2, C5 and record application. They
check actual run-2 demand admission, not only a printed summary.

| Control | NORMAL findings | Latest natural iteration |
|---|---:|---|
| Nested read and unrelated T cleaner | 1 | run-3 |
| Direct call | 1 | run-3 |
| Nested call, no cleaner | 1 | run-3 |
| Depth 1..6 × EXACT/MUST U at p.f: 12 executions | 1 each | run-3 |
| Exact T at p.f, cleaned at returned root | 0 | run-3 |

Five tests make 16 cold executions. The existing repair/control suite is
retained. Large XML, logs and compiled models remain outside Git under
`report-data-archive/.../data/post-run2-soundness-20261117/`.

The general cross-iteration relevance, native service closure, FLOW lifting
and loop-handoff obligations G1–G4 remain open. This investigation does not
establish universal soundness or termination. It selects no additional
semantic repair and makes no project performance claim.

## 4. Fresh bounded search with the latest C2

A deterministic **1,536-configuration** sweep uses `Run2Relay.emit` in the
complete prepared plans of the conditional-marking helper reference. The
adapter otherwise keeps the existing model byte-for-byte, apart from its
import and namespace. Publication uses the own prepared row and both field
caps. Native-bound service, protected results, current/saved delivery and
source permissions remain active.

Each helper has two unary marking actions: one checks a selected field
region; one checks the whole input region. The caller reads one named field
from the return between calls. The sample varies source/condition paths
through five fields, exact/uniform marking, two literal output paths, mark
changes and one to five calls. Input field exclusions are Empty and source
protection is plain; same-mark assignments can produce protected outputs.
No cleaner, overwrite, alias, ND or static protocol is added to this family.
The separate native controls cover the masked-cleaner boundary. The earlier
65-test suite retains its own overwrite and other repair controls.

| Result | Count |
|---|---:|
| Concrete observation present | 1,303 |
| Concrete observation absent | 233 |
| Observation mismatches | **0** |
| Failed within-run fixed-point checks | **0** |
| Unclosed at diagnostic run-25 | **0** |

| Natural completion | Configurations |
|---|---:|
| run-3 | 295 |
| run-5 | 229 |
| run-7 | 306 |
| run-9 | 312 |
| run-11 | 257 |
| run-13 | 137 |

The latest natural completion is **run-13**. The script checks through
**run-25**; this is a diagnostic horizon, not a hard-limit redundancy proof.
Every observation equals the untruncated concrete reference. For each run,
one additional full round produces exactly the same work state. The sample
is deterministic, not an exhaustive enumeration of all parameter products.
These results do not establish universal termination or G1–G4.

[Search and exact adapter definition](../../scripts/demand_experiments/post-run2-soundness-20261117/README.md).
The full result rows and source hashes are external. The combined targeted
native suite has **70 passing tests**, zero failures and zero skipped tests.

No new soundness counterexample is confirmed in this checked scope. The
older reference-alignment diagnostics 165 and 884 remain listed in the
[counterexample catalogue](bidirectional-demand-termination-counterexamples-20261115.md#known-model-alignment-gaps-not-termination-proofs);
this sweep does not resolve or reclassify them. Wider loop, ND, alias,
static and boundary-rule service still needs its own proof and integration
checks. The handoff clarification is the only contract update from this
follow-up; production is unchanged.

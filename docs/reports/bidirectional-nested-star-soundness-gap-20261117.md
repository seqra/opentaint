# Nested overwrite: same-head STAR admission gap

17 November 2026. Synthetic data-flow reachability. FULL marks.
Latest reached iteration: **run-3**, natural `NO_DEMAND_EDGE`.
[Consolidated contract](../design/bidirectional-demand-termination-approach-20261115.md).
Follow [proof-guide.md](../../spec/proof-guide.md).

**Historical soundness gap, now repaired in the proposal.**
The [run-2 STAR relay](../design/bidirectional-run2-star-relay-20261117.md)
retains the NORMAL observation and stops naturally at **run-3**. The trace
below records the pre-repair rejection. Production is unchanged.

**Cause of the historical gap:** Run-2 rejects a same-head
STAR/FLOW offer for a precise STAR/FLOW demand. A wrapper can produce
exactly that offer. The rejected query is needed to learn a NORMAL summary
that preserves an untouched sibling field.

This is separate from the repaired cleaner case. It has no cleaner, loop,
recursion, configured pass rule, static, ND join, unresolved transfer or real
field cut. All involved paths fit limit 1. The disjoint-cleaner repair and
NE are inactive.

The unchanged native engine admits this input and retains the observation.
A controlled native adapter that applies the proposal's one rejection loses
the observation and stops at run-3. This is a proposal regression, not a
claim that the current production driver has this failure.

## 1. Code and exact result

```java
void main() {
    Box a = new Box();
    markG(a);                 // Rule: assign T exactly at a.g.$.
    Box r = wrap(a);
    observeG(r);              // Rule: CM(r.g.$, T).
}
Box wrap(Box p) {
    Box r = overwrite(p);
    return r;
}
Box overwrite(Box p) {
    p.f = new Box();           // f != g.
    return p;
}
```

The marked point a.g survives the write to f and reaches r.g. The direct
concrete AP execution preserves it on NORMAL. All field names can be
ordinary fields of the same Box class; no type-policy exception is used.

Notation: `N/D` are layers; `*` is correlated STAR; `$` is EXACT;
`ret` is the method's return position; `{f}` is a real field exclusion.
ZERO identities are kept separately from marked DATA.

## 2. Run-1, forward, limit 1

```java
// Previous demand: unrestricted run-1. Submitted/initial: ZERO,N.
void main() {
    Box a = new Box();
    markG(a);                 // a.g.$/T,N; no field cut.
    Box r = wrap(a);           // r.g.$/T,D from the wrapper's FLOW summary.
    observeG(r);              // DEMAND witness.
}
// Published: ZERO -> DemandTarget,D; ZERO -> ZERO,N.
// No local a or r DATA summary escapes main.

// Submitted: p.g.$/T,N from main.
// Initial: p.*/FLOW -> p.*/FLOW,N (no mark check in wrap requests T).
Box wrap(Box p) {
    Box r = overwrite(p);     // The owned query submits p.*/FLOW,N.
    return r;                 // Owned result: ret.*/FLOW,D.
}
// Published:
//   p.*/FLOW -> ret.*/FLOW,D
//   p.*/FLOW -> p.*/FLOW,D
//   ZERO -> ZERO,N

// Submitted: p.*/FLOW,N from wrap's owned query.
// Initial: p.*/FLOW -> p.*/FLOW,N.
Box overwrite(Box p) {
    p.f = new Box();
    // Updating the field exclusion moves this edge to D in run-1.
    // Run-1 E remains empty: p.*/FLOW,D.
    return p;
}
// Published:
//   p.*/FLOW -> ret.*/FLOW,D
//   p.*/FLOW -> p.*/FLOW,D
//   ZERO -> ZERO,N
```

There is no NORMAL DATA record for either method. The argument-result row
is included; its backward entry base is p, while the next actual arrives
on ret. Since main's a is dead after the call, no argument-output requirement
supplies a second route.

## 3. Run-2, backward, limit 1

Backward summaries are above each declaration; demand, submitted facts and
initials are below it.

```java
// main: no marked source route or backward DATA result is produced.
// Ordinary ZERO identity can remain; it is not a source hit or Target.
void main() {
    Box a = new Box();
    markG(a);                 // Requires an actual a.g/T backward fact.
    Box r = wrap(a);
    observeG(r);              // Seeds r.g.$/T,N as the exact requirement.
}
// Previous control demand: Target -> ZERO.
// Initial control: ZERO. Call offer to wrap: ret.g.$/T,N.

// wrap: no backward DATA summary; its marked return query gets no answer.
Box wrap(Box p) {
    Box r = overwrite(p);     // Backward call offer: overwrite's ret.*/FLOW,N.
    return r;
}
// Previous (entry Dc; paired exit Dp):
//   (ret.*/FLOW; p.*/FLOW)
//   (p.*/FLOW; p.*/FLOW)
// Submitted: ret.g.$/T,N.
// Initial: ret.*/FLOW,N.
// Reason: the existing run-2 deeper-actual STAR exception admits g.

// overwrite: no backward DATA summary.
Box overwrite(Box p) {
    p.f = new Box();
    return p;
}
// Previous (entry Dc; paired exit Dp):
//   (ret.*/FLOW; p.*/FLOW)
//   (p.*/FLOW; p.*/FLOW)
// Submitted: ret.*/FLOW,N -- same head and STAR tail.
// Initials: EMPTY under the consolidated same-head table.
// Saved NORMAL DATA replay: EMPTY.
```

The exact failure cell is:

```text
HeadPolicy.emit(run=2, limit=1, backward=true,
                demand=ret.*/FLOW,
                actual=ret.*/FLOW,N) = []
```

The argument row rejects by base. The return row rejects by tail. The raw
C5 image could admit a STAR query: the legal hypothetical ret.g.$/T offer
is its existing run-2 witness. But C5 cannot start a query which C2 did not
emit for the actual STAR offer.

All refinement entries here are precise STAR. There is no MAY/NE row to
prepare a child, and no retained NORMAL DATA guard to supply saved replay.
Completion selectors require an owned strong query and actual NORMAL
service; neither exists here. No other selected mechanism fills the gap.

## 4. Run-3, forward, limit 2

```java
// No new marked route to the observation was retained by run-2.
// Even optimistically allowing the original source does not help:
// wrap has neither relevant demand nor a saved NORMAL DATA record.
void main() {
    Box a = new Box();
    markG(a);
    Box r = wrap(a);
    observeG(r);
}
// No NormalTarget or DemandTarget. Natural stop: run-3; zero findings.

// Previous DATA demand: empty. Actual run: no DATA offer/initial.
// Counterfactual p.g.$/T,N would also get no current query or saved result.
Box wrap(Box p) {
    Box r = overwrite(p);
    return r;
}
// Published current DATA summaries: none.

// Previous DATA demand: empty. DATA offers/initials: none.
Box overwrite(Box p) {
    p.f = new Box();
    return p;
}
// Published current DATA summaries: none.
```

A larger field limit cannot change the same-head rejection, which the
proof quantifies over every limit. There is no hidden longer path to expose.
Once demand and NORMAL DATA service are empty, uncapped extra rounds cannot
invent the missing method relation. A hard cutoff is not used.

## 5. The missing NORMAL relation and controls

If the inner query can run, it computes:

```text
run-2 raw inner initial: ret.*/FLOW,N
reversed return:         p.*/FLOW,N
restricted field write:  p.*/FLOW {f},N
ordinary paired C5:      ret.*/FLOW -> p.*/FLOW {f},N

run-3 saved reverse:     p.*/FLOW {f} -> ret.*/FLOW,N
actual p.g.$/T,N:        ret.g.$/T,N
actual p.f.$/T,N:        rejected by {f}
```

This is the ordinary computed summary, not a predefined edge. Its field
length is zero and it satisfies both caps. The exclusion is essential for
correct f behavior. The wrapper then publishes the same normal preservation
relation through ordinary summary application.

[Native test](../../core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/NestedOverwriteStarAdmissionTest.kt):

| Case | NORMAL findings | Latest run / reason |
|---|---:|---|
| Unchanged native policy, nested overwrite | 1 | run-3 / NO_DEMAND_EDGE |
| Historical proposal rejection, nested overwrite | **0, no provisional finding either** | run-3 / NO_DEMAND_EDGE |
| Same rejection, direct call to overwrite | 1 | run-3 / NO_DEMAND_EDGE |
| Same rejection, nested helper with no overwrite | 1 | run-1 / NO_DEMAND_EDGE |
| Repaired run-2 STAR relay, nested overwrite | 1 | run-3 / NO_DEMAND_EDGE |
| Repaired relay, source and observation at overwritten f | 0 | run-3 / NO_DEMAND_EDGE |

The adapter leaves native transfers, C5, saved replay, ZERO, subscriptions,
publication and the driver enabled. It drops one nonzero inner start in
run-2, after checking that the old emitter supplied exactly its root EXACT
FLOW probe. It independently captures the actual inner offer and checks
that it is root STAR/FLOW. That maps precisely to the rejected proposal
cell. It retains subscriptions, which can add work but cannot supply absent
DATA in this example. The production policy itself is unchanged.

The test retains the old rejection as a historical diagnostic. Separate
repair tests require the NORMAL finding at run-3 and reject the overwritten
f point at run-3. They change only the run-2 FLOW start through a test
adapter; production is unchanged. This is not whole-proposal integration.

## 6. Historical proof scope and selected repair

[Constructive proof package](../../spec/lean/proposals/nested-star-admission-gap-20261117/README.md)
imports the selected complete `HeadPolicy` and C5. It computes both run-1
argument/return rows, the outer initial, the rejected inner initial family,
empty backward service, the direct NORMAL C5 control and exact g survival.
It checks that the NORMAL control excludes f and transports g. Its final
quiet-suffix lemma models the empty-demand/no-saved-DATA call policy; it is
not an independent whole-JVM driver theorem. The cold native adapter is
separate evidence for that execution bridge.

The selected [run-2 STAR relay](../design/bidirectional-run2-star-relay-20261117.md)
accepts same-head STAR under precise STAR demand in run-2 only. It applies
the existing base/mark/budget gates and updates C5's complete raw image.
FLOW is a NORMAL conditional identity. Concrete T remains DEMAND with its
FLOW companion. Exact demand and later-run rejection stay unchanged.

The [repair proof package](../../spec/lean/proposals/run2-star-relay-20261117/README.md)
adds C2/C5 preservation and cap checks, a complete positive trace, the f
negative control and an induction over arbitrary finite wrapper depth.
The repaired native adapter retains one NORMAL observation and stops at
run-3. Its overwritten-f control has no NORMAL observation and also stops
at run-3. No cap exception, new field, exclusion policy or tail is added.
The old counterexample proof is retained as evidence for the old table;
it is not a counterexample to the repaired contract.

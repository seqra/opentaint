# Exact FLOW replay: facts inside the code

Status: historical regression **before** the selected
[FLOW summary normalization and write-exclusion update](bidirectional-flow-summary-normalization-20261029.md).
The stored EXACT rows below describe the rejected path. With normalization,
run-2 stores STAR summaries and run-3 preserves h. Point-query EXACT facts
remain part of the selected design.

Date: 29 October 2026. Source reviewed: `036b4569a`.
Latest modeled iteration: **run-3**. Field limits: `1,1,2`. FULL marks.
This is the proposed abstract EXACT domain with the current exact-target
application left unchanged. Production code is unchanged.

Each run has one listing. Above a method: previous demand, submitted facts,
and emitted initials. After its closing brace: new summaries, split by layer.
A reused record is listed separately from a new summary. Run-2 executes the
shown code backward: read its instruction comments from bottom to top.

Notation:

```text
FLOW               abstract mark
T                  concrete mark
N / D              NORMAL / DEMAND layer of an analyzed edge or fact
* / $              STAR / EXACT field tail
[any]              MAY field tail
[any-taint]        MUST field tail
ret                return coordinate of the current method
(entry X; exit Y)  paired demand for the current analysis direction
```

Instruction value-transfer micro-edges are NORMAL STAR-to-STAR. Inline D
labels describe their applied results. Common NORMAL `ZERO -> ZERO` rows
are omitted below helper, box, and wrapper. Other displayed summaries retain
their real premises. All displayed fact exclusions are empty; ordinary
field-write preservation micro-edges still carry their field exclusions.

The types and configured call-site rules are shared by all listings:

```java
static final class Root { Inner f; }
static final class Inner { Leaf h; }
static final class Leaf { }
static final class Box { Root value; }
static final class Pair { Inner a; Box b; }
```

```text
source(Root):     true -> AssignMark(T, arg0.f.h.[any])
sinkExact(Object): ContainsMark(arg0.$, T);     no end actions
sinkAny(Object):   ContainsMark(arg0.[any], T); no end actions
```

The rule-hook methods have empty bodies. Their configured effects occur at
the call sites annotated in main. The source's terminal `[any]` gives
`q.f.h.[any-taint]/T`. It does not mark q.f itself. There are no predefined
summaries, pass rules, cleaners, conditional sources, or ND rules. Box and
Pair are fresh objects. Their writes do not overwrite q or each other.

## Run-1: forward, field limit 1

```java
// Previous demand: none; this is the unrestricted first run.
// Submitted: ZERO from the driver.
// Initial: ZERO.
public static void main(String[] ignored) {
    Root q = new Root();
    q.f = new Inner();
    q.f.h = new Leaf();

    source(q);
    // GEN before limit: ZERO -> q.f.h.[any-taint]/T [D].
    // After limit 1:    ZERO -> q.f.[any]/T [D].

    sinkAny(q.f.h);
    // Its field reads receive the concrete T fact; this sink is reached.

    Pair r = wrapper(q);
    // Submitted to wrapper: q.f.[any]/T [D].
    // Instantiate wrapper's FLOW summaries with that actual T input:
    //   ZERO -> r.a.[any]/T [D]
    //   ZERO -> r.b.[any]/T [D].

    sinkExact(r.a); // Reached through the MAY/DEMAND A result.
    sinkAny(r.b);   // Reached through the MAY/DEMAND B result.
}
// Produced NORMAL: ZERO -> ZERO.
// Produced DEMAND: no nonzero boundary summary in this finite trace.
// The q/r facts above are local facts, not method-return summaries.


// Previous demand: none.
// Submitted: q.f.[any]/T [D], from main.
// Emitted initial: q.*/FLOW; start q.*/FLOW -> itself [N].
static Pair wrapper(Root q) {
    Pair r = new Pair(); // No marked r fact.

    Inner a = helper(q);
    // Submit p.*/FLOW [N] to helper.
    // Apply its inferred summary: q.*/FLOW -> a.[any]/FLOW [D].

    r.a = a;
    // q.*/FLOW -> r.a.[any]/FLOW [D].

    Box b = box(q);
    // Submit p.*/FLOW [N] to box.
    // Apply its inferred summary: q.*/FLOW -> b.value.*/FLOW [N].

    r.b = b;
    // Before limit: q.*/FLOW -> r.b.value.*/FLOW [N].
    // After limit:  q.*/FLOW -> r.b.[any]/FLOW [D].
    // Two fields exceed limit 1. The r.a fact survives this disjoint write.

    return r;
    // Exit fact A: ret.a.[any]/FLOW [D].
    // Exit fact B: ret.b.[any]/FLOW [D].
}
// Produced NORMAL:
//   q.*/FLOW -> q.*/FLOW.
// Produced DEMAND:
//   q.*/FLOW -> ret.a.[any]/FLOW.
//   q.*/FLOW -> ret.b.[any]/FLOW.
// Run-2 demand:
//   (entry ret.a.[any]/FLOW; exit q.*/FLOW)
//   (entry ret.b.[any]/FLOW; exit q.*/FLOW).


// Previous demand: none.
// Submitted: p.*/FLOW [N], from wrapper's FLOW analysis.
// Emitted initial: p.*/FLOW; start p.*/FLOW -> itself [N].
static Inner helper(Root p) {
    return p.f;
    // NORMAL read micro-edge: p.f.*/FLOW -> ret.*/FLOW.
    // Applied to p.*/FLOW: p.*/FLOW -> ret.[any]/FLOW [D].
    // Reading below the supplied root loses suffix correlation.
}
// Produced NORMAL:
//   p.*/FLOW -> p.*/FLOW.
// Produced DEMAND:
//   p.*/FLOW -> ret.[any]/FLOW.
// Run-2 demand:
//   (entry ret.[any]/FLOW; exit p.*/FLOW).


// Previous demand: none.
// Submitted: p.*/FLOW [N], from wrapper's FLOW analysis.
// Emitted initial: p.*/FLOW; start p.*/FLOW -> itself [N].
static Box box(Root p) {
    Box z = new Box(); // No marked z fact.

    z.value = p;
    // p.*/FLOW -> z.value.*/FLOW [N]. One field fits limit 1.

    return z;
    // p.*/FLOW -> ret.value.*/FLOW [N].
}
// Produced NORMAL:
//   p.*/FLOW -> p.*/FLOW.
//   p.*/FLOW -> ret.value.*/FLOW.
// Produced DEMAND: none.
// Persist these NORMAL records. No Box demand is needed in run-2.
```

## Run-2: backward, field limit 1

The A and B comments below are two separate analyses of wrapper, with
different initials. Each summary uses its own initial. A NORMAL conditional
summary does not turn its caller's DEMAND input into a NORMAL fact.

```java
// Previous demand: no nonzero main boundary pair in this finite trace.
// Previous guidance: the three sink occurrences reached in run-1.
// Submitted: ZERO from the driver; concrete sink seeds appear below.
public static void main(String[] ignored) {
    Root q = new Root();
    q.f = new Inner();
    q.f.h = new Leaf();

    source(q);
    // Backward direct-sink route arrives as q.f.[any]/T [D].
    // It reaches the reversed source at f.h and records a source hit.
    // That source hit keeps this source enabled for run-3.

    sinkAny(q.f.h);
    // Seed T below q.f.h; reversing its reads and limit gives q.f.[any]/T [D].

    Pair r = wrapper(q);
    // A submitted return requirement: ret.a.$/T [D].
    // B submitted return requirement: ret.b.[any]/T [D].
    // Instantiate wrapper's answers back into main:
    //   A -> q.f.$/T [D]; B -> q.[any]/T [D].

    sinkExact(r.a); // A seed: r.a.$/T [D].
    sinkAny(r.b);   // B seed: r.b.[any]/T [D].
}
// Produced NORMAL: ZERO -> ZERO.
// Produced DEMAND: no nonzero boundary summary in this finite trace.
// Additional result: source hit, used at the next forward run.


// Previous demand from run-1:
//   (entry ret.a.[any]/FLOW; exit q.*/FLOW)
//   (entry ret.b.[any]/FLOW; exit q.*/FLOW).
// Submitted A: ret.a.$/T [D].
// Submitted B: ret.b.[any]/T [D].
// Emitted A initial: ret.a.$/FLOW; start NORMAL.
// Emitted B initial: ret.b.[any]/FLOW; start DEMAND.
static Pair wrapper(Root q) {
    Pair r = new Pair();
    // Backward: the q facts pass this fresh-r allocation unchanged.

    Inner a = helper(q);
    // A: submit ret.$/FLOW [N] to helper.
    // A: its live NORMAL summary returns p.f.$/FLOW [N].
    // A: bind p back to q, giving q.f.$/FLOW [N].
    // B: q.[any]/FLOW [D] passes via helper's old argument identity.

    r.a = a;
    // Backward A: r.a.$/FLOW -> a.$/FLOW [N].
    // Backward B: q.[any]/FLOW [D] is unaffected.

    Box b = box(q);
    // B: submit ret.[any]/FLOW [D] in Box coordinates.
    // B: reuse NORMAL record view ret.value.*/FLOW -> p.*/FLOW.
    // B: the actual ret.[any] is above the record's ret.value.* premise.
    // B: ancestor application gives p.[any]/FLOW [D], then q.[any]/FLOW [D].
    // A: the unrelated r.a.$/FLOW fact is preserved.

    r.b = b;
    // Backward B: r.b.[any]/FLOW -> b.[any]/FLOW [D].
    // Backward A: r.a.$/FLOW is preserved because a and b differ.

    return r;
    // Backward A: ret.a.$/FLOW -> r.a.$/FLOW [N].
    // Backward B: ret.b.[any]/FLOW -> r.b.[any]/FLOW [D].
}
// Produced NORMAL:
//   ret.a.$/FLOW -> q.f.$/FLOW.
// Produced DEMAND:
//   ret.b.[any]/FLOW -> q.[any]/FLOW.
// C5 retains both rows. Persist the NORMAL A row.
// Run-3 demand:
//   (entry q.[any]/FLOW; exit ret.b.[any]/FLOW).


// Previous demand from run-1:
//   (entry ret.[any]/FLOW; exit p.*/FLOW).
// Submitted A: ret.$/FLOW [N], from wrapper's A analysis.
// Submitted B: p.[any]/FLOW [D], for argument preservation only.
// Emitted A initial: ret.$/FLOW; start NORMAL.
// B emits no initial: the old argument identity answers it at the caller.
static Inner helper(Root p) {
    return p.f;
    // Backward A, NORMAL reversed read: ret.*/FLOW -> p.f.*/FLOW.
    // Applied to ret.$/FLOW: ret.$/FLOW -> p.f.$/FLOW [N].
}
// Produced NORMAL:
//   ret.$/FLOW -> p.f.$/FLOW.
// Produced DEMAND: none.
// C5 retains this row; persist it as a backward record.
// Its forward read view is p.f.$/FLOW -> ret.$/FLOW [N].
// Run-3 demand: none.


// Previous demand from run-1: none.
// Submitted: ret.[any]/FLOW [D], from wrapper's B analysis.
// Emitted nonzero initials: none. The caller uses the old record.
static Box box(Root p) {
    // This body is not re-analyzed for a new nonzero initial in run-2.
    Box z = new Box();
    z.value = p;
    return z;
}
// Produced new NORMAL: none.
// Produced new DEMAND: none.
// Reused NORMAL record, backward view:
//   ret.value.*/FLOW -> p.*/FLOW.
// Apply it to ret.[any]/FLOW [D] -> p.[any]/FLOW [D].
// This instantiated result is not a new Box summary.
```

## Run-3: forward, field limit 2

The NORMAL A summary below is the disputed raw row. It is stored before
C5, but C5 does not publish it to main in this run. The trace checks the
current exact-target replay cell under the proposed EXACT domain.

```java
// Previous demand: no nonzero main boundary pair in this finite trace.
// Previous guidance: the source hit in run-2 keeps source(q) enabled.
// Submitted: ZERO from the driver.
public static void main(String[] ignored) {
    Root q = new Root();
    q.f = new Inner();
    q.f.h = new Leaf();

    source(q);
    // ZERO -> q.f.h.[any-taint]/T [N]. Two fields fit limit 2.

    sinkAny(q.f.h);
    // The source supplies the marked leaf at this point.

    Pair r = wrapper(q);
    // Submitted to wrapper: q.f.h.[any-taint]/T [N].
    // Its old exact A record cannot match this deeper concrete input.
    // New C5 publication is B only. Instantiate it:
    //   ZERO -> r.b.value.[any]/T [D].
    // The disputed raw NORMAL A row is NOT delivered here in run-3.

    sinkExact(r.a); // No false A-root T is supplied by that unpublished row.
    sinkAny(r.b);   // Reads the B result with a possible marked descendant.
}
// Produced NORMAL: ZERO -> ZERO.
// Produced DEMAND: no nonzero boundary summary in this finite trace.
// These local observations are not main return summaries.


// Previous demand from run-2:
//   (entry q.[any]/FLOW; exit ret.b.[any]/FLOW).
// Submitted: q.f.h.[any-taint]/T [N].
// Emitted initial: q.f.*/FLOW; start q.f.*/FLOW -> itself [N].
// The first new field f refines ANY. Do not consume h as well.
static Pair wrapper(Root q) {
    Pair r = new Pair();

    Inner a = helper(q);
    // Bound input: p.f.*/FLOW [N]; no new helper initial is needed.
    // Reuse p.f.$/FLOW -> ret.$/FLOW [N] from run-2.
    // Current inside matching accepts this same-prefix STAR input.
    // Current exact-target cell gives a.$/FLOW [N]: the disputed result.

    r.a = a;
    // q.f.*/FLOW -> r.a.$/FLOW [N].

    Box b = box(q);
    // Bound input: p.f.*/FLOW [N]; reuse the NORMAL run-1 Box record.
    // q.f.*/FLOW -> b.value.f.*/FLOW [N]. Two fields still fit.

    r.b = b;
    // Before limit: q.f.*/FLOW -> r.b.value.f.*/FLOW [N].
    // After limit:  q.f.*/FLOW -> r.b.value.[any]/FLOW [D].
    // Three fields exceed limit 2. The separate r.a.$ fact survives.

    return r;
    // Exit fact A: ret.a.$/FLOW [N].
    // Exit fact B: ret.b.value.[any]/FLOW [D].
}
// Produced raw NORMAL:
//   q.f.*/FLOW -> q.f.*/FLOW.
//   q.f.*/FLOW -> ret.a.$/FLOW.                 <-- disputed row
// Produced raw DEMAND:
//   q.f.*/FLOW -> ret.b.value.[any]/FLOW.
// C5 publishes only the DEMAND B row; the two NORMAL rows miss its exit.
// Raw NORMAL persistence still stores the disputed A row at the barrier.


// Previous demand from run-2: none.
// Bound/submitted input: p.f.*/FLOW [N], from wrapper.
// Emitted nonzero initials: none. The caller replays a stored record.
static Inner helper(Root p) {
    // This body is not re-analyzed for a new nonzero initial in run-3.
    return p.f;
}
// Produced new NORMAL: none.
// Produced new DEMAND: none.
// Reused NORMAL record, forward view:
//   p.f.$/FLOW -> ret.$/FLOW.
// Current replay on p.f.*/FLOW [N] returns ret.$/FLOW [N].
// No stored NORMAL p.f.*/FLOW -> ret.*/FLOW covers this record.


// Previous demand from run-2: none.
// Bound/submitted input: p.f.*/FLOW [N], from wrapper.
// Emitted nonzero initials: none. The caller replays a stored record.
static Box box(Root p) {
    // This body is not re-analyzed for a new nonzero initial in run-3.
    Box z = new Box();
    z.value = p;
    return z;
}
// Produced new NORMAL: none.
// Produced new DEMAND: none.
// Reused native NORMAL forward record:
//   p.*/FLOW -> ret.value.*/FLOW.
// Apply it to p.f.*/FLOW [N] -> ret.value.f.*/FLOW [N].
// This instantiated result is not a new Box summary.
```

The disputed raw row maps `q.f.h/T` to the root `ret.a/T`. The Java code
maps it to `ret.a.h/T`. The helper read and Pair write must preserve h.
No retained NORMAL STAR return summary supplies a cover, and C5 rejection
does not remove the raw row before normal-record persistence.

## Validation

This is the same finite code-only trace, with a new layout. Analysis behavior,
source/sink rules, emitted initials, record views and layers are unchanged.
The active Lean certificate is
[`RestrictedInitialPolicy.CodeOnlyExactReplay`](../../spec/lean/proposals/initial-emission/RestrictedInitialPolicy.lean).
Its 11 theorems and executable check pass. The complete facts, summaries,
source hashes and receipts are in
[the embedded trace](../reports/data/bidirectional-closed-exact-replay-20261029.json).

The original Java example compiles. Each annotated per-run listing is also
checked with the same types and empty source/sink hook bodies. These are
syntax/type checks, not a JVM execution of the proposed domain. The finite
model does not prove the complete driver or alias implementation. No replay
repair, DEMAND demotion, or new matching guard is selected here.

# Termination counterexample after the MUST-preserving cleaner revision

14 November 2026. Follow [proof-guide.md](../../spec/proof-guide.md).
The [selected MUST cleaner revision](../../spec/non-empty-may.md),
[bounded refinement](../design/bidirectional-bounded-demand-refinement-20261114.md)
and [NORMAL uniform FLOW coverage](../design/bidirectional-normal-uniform-ne-coverage-20261114.md)
are all in force. No production change is made.

**Result:** a root-only selected cleaner inside the ordinary two-call
read/write example leaves a concrete protected field-cut cycle. The same
root `ZERO -> DemandTarget, DEMAND` recurs after run-3, run-5 and every
later forward run. A NORMAL finding can already exist in run-3.

This has no loop, recursion, pass rule, static, alias, ND condition or
predefined method summary. Unlike the withdrawn root-only example,
it does not demote a MUST merely because the root cleaner is partial.

## 1. Code and ordinary rules

```java
static void main(boolean b1, boolean b2) {
    Node x = sourceTreeT();
    Node y = choose(x, b1);
    Node z = choose(y, b2);
    sinkTreeT(z);
}

static Node choose(Node x, boolean b) {
    removeTAtRoot(x);
    if (b) return x.f.f;
    Node t = new Node();
    t.f = x;
    Node y = new Node();
    y.f = t;
    return y;
}
```

Use the same method/context policy as the previous two-call reference.
The rule APIs have no analyzed bodies:

| API | Rule |
| --- | --- |
| `sourceTreeT()` | Unconditional source: mark the return and descendants with T, `MUST/T,N` |
| `removeTAtRoot(x)` | Selected `RemoveMark(T)` at `x.$`, EXACT reach |
| `sinkTreeT(z)` | Unary `ContainsMark(z.[any],T)` sink |

The helper has two ordinary branches: consume two f fields, or add two
f fields. There is no configured data-transfer/pass action. Only main
and choose are analyzable blocks. The CFGs are acyclic.

## 2. Why the new cleaner rule does not close this case

All recurring queries below enter choose with a **known nonempty path**:

```text
x.f^(L-1).MUST/T,N   or   x.f^L.STAR/T,D
```

The cleaner targets x itself. These facts describe descendants, so the
cleaner is disjoint and retains their shape and layer. Its existing
selected-survivor rule adds protection H. No new cleaner demotion occurs:

```text
removeTAtRoot(x):
    x.f.MUST/T,N -> x.f.MUST/T,N,H
    x.f.f.*/T,D  -> x.f.f.*/T,D,H
```

For an additional same-head `x.MUST/T,N` query, the **new rule is used**:
it also stays NORMAL. The proof imports that rule; it does not use the
old counterexample's `x.MUST,N -> x.MUST,D` row.

Now compare these legal run-3 results with exactly the same complete
original and protection class:

```text
NORMAL: x.f.MUST/T -> ret.f.MUST/T, N,H
DEMAND: x.f.MUST/T -> ret.f.f.NE/T, D,H
```

The NORMAL result is a useful uniform cover. However, the currently
proposed new rule accepts only **unprotected FLOW** originals/results.
Both rows above are concrete T relations, and the cut is protected.
Ordinary same-layer MUST canonicalization also cannot delete this D/NE
row using the N/MUST row. Extending that rule is not assumed here.

## 3. Trace notation and scope

```text
U = MUST / [any-taint]; M = MAY / [any]; NE = non-empty MAY
N = NORMAL; D = DEMAND; H = protected; F = FLOW
Z = ZERO; DT = DemandTarget; NT(id) = NormalTarget(id)
[Dc ; Dp] = one complete paired demand row
x.f^k = x followed by k copies of the field f; x.f^0 is x
```

The annotations below show a closed recurring witness through **both real
calls**, plus the relevant NORMAL route. They are not a claim that other
queries or summaries are absent. Each listed C2 cell includes its FLOW
companion. The proof accepts an arbitrary additional NORMAL basis: no
provider in the selected uniform-coverage rule can remove a protected
cut. Section 9 covers the other compaction and delivery rules.

For every forward limit L >= 2 used below, a useful incoming local row is

```text
RF(L) = [x.f^(L-1).NE/T ; ret.f^(L-1).*/T]
```

The proof also permits MAY in place of NE at the same head, independently
in every run. Coalescing a same-head NE into MAY does not break the witness.
Deeper heads remain in the bounded refinement view even if executable
MAY coverage hides them from caller delivery.

## 4. Run-1: bootstrap, forward limit 1

```java
// Demand: unrestricted. Submitted: Z,N. Initial: Z -> Z,N.
static void main(boolean b1, boolean b2) {
    Node x = sourceTreeT();      // x.U/T,N.
    Node y = choose(x, b1);      // Receives y.M/T,D,H from the reader arm.
    Node z = choose(y, b2);      // Receives z.M/T,D,H from that arm again.
    sinkTreeT(z);                // Z -> DT,D. Capture this sink seed.
}
// NORMAL control: Z -> Z. DEMAND terminal: Z -> DT.

// Demand: unrestricted. Submitted: x.U/T,N; also x.M/T,D at call 2.
// FLOW initial: x.* / F,N.
// The selected cleaner requests T on that FLOW original.
// The actual T supply answers with initial x.*/T,D (not MUST).
static Node choose(Node x, boolean b) {
    removeTAtRoot(x);            // x.*/T,D -> x.M/T,D,H.
    if (b) return x.f.f;         // Unknown reads: ret.M/T,D,H.
    Node t = new Node();
    t.f = x;                    // t.f.M/T,D,H.
    Node y = new Node();
    y.f = t;                    // y.f.f.M/T; real cut at 1 -> y.f.NE/T,D,H.
    return y;
}
// Concrete DEMAND rows, before executable MAY coverage:
//   x.*/T -> ret.M/T,D,H
//   x.*/T -> ret.f.NE/T,D,H
// FLOW rows exclude T after the selected cleaner; they cannot replace T.
// Local handoff retains the field head. It includes
//   [ret.f.NE/T ; x.*/T] for run-2, as well as the MAY row.
```

Nonexact concrete run-1 answers are STAR on DEMAND, as in
[Run1RequestMatching](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/engine/Run1RequestMatching.kt).
The bootstrap does not invent a run-1 MUST initial or a NORMAL concrete
STAR start. The FLOW request has a real whole-object T supply.

## 5. Run-2: backward limit 1

```java
// Published: Z -> DT,D; normal completion Z -> Z.
// Source hit: sourceTreeT, so permit it in run-3.
static void main(boolean b1, boolean b2) {
    Node x = sourceTreeT();      // The backward x.M/T,D route reaches the source.
    Node y = choose(x, b1);      // Reverse call 1: ret.M/T,D -> x.M/T,D.
    Node z = choose(y, b2);      // Reverse call 2 supplies that ret.M requirement.
    sinkTreeT(z);                // Seed z.M/T,D at the actual sink.
}
// Demand: [Target ; Z]. Submitted: Z,N at normal exit.
// Initial: Z -> Z,N. No DATA/MAY owned initial is used in main.

// Published concrete DEMAND witnesses:
//   ret.f.*/T -> x.f.NE/T,D,H
//   ret.f.*/T -> x.M/T,D,H
static Node choose(Node x, boolean b) {
    removeTAtRoot(x);            // Reached x.f.NE is disjoint; keep D,H.
                                // Reached x.M retains its partial D,H survivor.
    if (b) return x.f.f;         // Reverse two reads: add f twice.
                                // Each is bounded; final x.f.NE/T,D,H.
    Node t = new Node();
    t.f = x;                    // Reverse two writes from ret.f.* produces x.M.
    Node y = new Node();
    y.f = t;
    return y;
}
// Demand witness: [ret.f.NE/T ; x.*/T].
// Submitted at reverse call 2: ret.M/T,D.
// C2 initials for this cell: ret.f.*/T,D and ret.f.*/F,N.
// The MAY row/other branch supplies ret.M/T,D to reverse call 1.
// Handoff witness for run-3: RF(2) = [x.f.NE/T ; ret.f.*/T].
```

The entire concrete C2 family from the two run-1 local heads also includes
ret.$/T,D, ret.*/T,D and the matching FLOW starts. Those extra commands are
not suppressed. The displayed ret.f command alone constructs RF(2), and
the independently computed MAY result reaches the real source.

## 6. Run-3: forward limit 2

```java
// Demand: [Target ; Z]. Submitted/initial: Z,N.
// Source permission was obtained in run-2.
static void main(boolean b1, boolean b2) {
    Node x = sourceTreeT();      // x.U/T,N.
    Node y = choose(x, b1);      // One actual reply is y.f.f.NE/T,D,H.
    Node z = choose(y, b2);      // That actual replies with z.f.f.NE/T,D,H.
    sinkTreeT(z);                // Z -> DT,D, even if a NORMAL witness also hits.
}
// DEMAND terminal: Z -> DT.
// A NORMAL route also exists: both calls can return a NORMAL uniform f region.
// Its NT(id) is retained, but it does not erase the anonymous DT.

// Demand witness: [x.f.NE/T ; ret.f.*/T].
// Call 1 submitted: x.U/T,N. Its C2 initial: x.f.U/T,N.
// Call 2 submitted: x.f.f.NE/T,D from call 1.
// Its C2 initials: x.f.f.*/T,D plus x.f.f.*/F,N.
static Node choose(Node x, boolean b) {
    removeTAtRoot(x);            // Both known nonempty prefixes are disjoint.
                                // Keep their layers, add survivor protection.
    if (b) return x.f.f;         // From x.f.U: ret.U/T,N,H.
                                // Own C5 selects ret.f.U/T,N,H.
    Node t = new Node();
    t.f = x;                    // Call-1 query: t.f.f.U/T,N,H, still within 2.
    Node y = new Node();
    y.f = t;                    // y.f.f.f.U -> real cut: y.f.f.NE/T,D,H.
    return y;                   // Call-2 query also cuts to this head.
}
// NORMAL witness: x.f.U/T -> ret.f.U/T,N,H.
// DEMAND witnesses:
//   x.f.U/T   -> ret.f.f.NE/T,D,H
//   x.f.f.*/T -> ret.f.f.NE/T,D,H
// Next backward row: [ret.f.f.NE/T ; x.f.f.*/T].
```

These witnesses share neither a new tail nor discarded suffix evidence.
The cuts occur during ordinary body propagation before NORMAL precoverage
can skip a duplicate relative C5 result.

## 7. Run-4 and run-5

```java
// Run-4, backward limit 3. Published: Z -> DT,D. Source hit renewed.
static void main(boolean b1, boolean b2) {
    Node x = sourceTreeT();      // x.f.f.f.NE/T,D reaches the whole-object source.
    Node y = choose(x, b1);      // Reverse call 1 receives the f.f.f.NE actual.
    Node z = choose(y, b2);      // Reverse call 2 receives sink MAY.
    sinkTreeT(z);
}
// Demand: [Target ; Z]. Submitted/initial at exit: Z,N.

// Run-4 published DEMAND:
//   ret.f.f.*/T   -> x.f.f.f.NE/T,D,H
//   ret.f.f.f.*/T -> x.f.f.f.NE/T,D,H
static Node choose(Node x, boolean b) {
    removeTAtRoot(x);            // Backward facts have known nonempty paths.
    if (b) return x.f.f;         // Reverse prefix growth, with a real cut at 3.
    Node t = new Node();
    t.f = x;
    Node y = new Node();
    y.f = t;
    return y;
}
// Demand: [ret.f.f.NE/T ; x.f.f.*/T].
// Reverse call 2: submitted ret.M/T,D;
//   initials ret.f.f.*/T,D plus its FLOW companion.
// Reverse call 1: submitted ret.f.f.f.NE/T,D from reverse call 2;
//   initials ret.f.f.f.*/T,D plus its FLOW companion.
// Handoff for run-5: RF(4) = [x.f.f.f.NE/T ; ret.f.f.f.*/T].
```

```java
// Run-5, forward limit 4. Demand: [Target ; Z]. Submitted/initial: Z,N.
static void main(boolean b1, boolean b2) {
    Node x = sourceTreeT();
    Node y = choose(x, b1);      // y.f.f.f.f.NE/T,D.
    Node z = choose(y, b2);      // z.f.f.f.f.NE/T,D.
    sinkTreeT(z);                // The same Z -> DT,D as after run-3.
}
// Published DEMAND: Z -> DT. It is not discharged by an old NT(id).

// Demand: [x.f.f.f.NE/T ; ret.f.f.f.*/T].
// Call 1: submitted x.U/T,N; initial x.f.f.f.U/T,N.
// Call 2: submitted x.f.f.f.f.NE/T,D;
//   initials x.f.f.f.f.*/T,D and its FLOW companion.
static Node choose(Node x, boolean b) {
    removeTAtRoot(x);            // Disjoint on the known prefixes; add H.
    if (b) return x.f.f;
    Node t = new Node();
    t.f = x;
    Node y = new Node();
    y.f = t;                    // Real global cut at 4, not a new cleaner loss.
    return y;
}
// Published DEMAND witnesses:
//   x.f.f.f.U/T   -> ret.f.f.f.f.NE/T,D,H
//   x.f.f.f.f.*/T -> ret.f.f.f.f.NE/T,D,H
// Next backward row: [ret.f.f.f.f.NE/T ; x.f.f.f.f.*/T].
```

## 8. General uncapped recurrence

For even L >= 2, the forward run with limit L has this closed witness:

```text
incoming RF(L) = [x.f^(L-1).NE/T ; ret.f^(L-1).*/T]

call 1 actual x.U/T,N:
    C2 x.f^(L-1).U/T,N
    cleaner: same fact, N,H
    two writes, cut after each:
    A_L: x.f^(L-1).U/T -> ret.f^L.NE/T,D,H
    application supplies call 2's actual x.f^L.NE/T,D

call 2 C2:
    x.f^L.*/T,D plus FLOW companion
    B_L: x.f^L.*/T -> ret.f^L.NE/T,D,H
    application reaches the sink on D

handoff RB(L) = [ret.f^L.NE/T ; x.f^L.*/T]
```

The next backward run has limit L+1:

```text
reverse call 2 actual ret.M/T,D:
    C2 ret.f^L.*/T,D plus FLOW companion
    reverse two reads, cut after each, then the disjoint cleaner:
    C_L: ret.f^L.*/T -> x.f^(L+1).NE/T,D,H
    supplies reverse call 1 actual ret.f^(L+1).NE/T,D

reverse call 1:
    C2 ret.f^(L+1).*/T,D plus FLOW companion
    D_L: ret.f^(L+1).*/T -> x.f^(L+1).NE/T,D,H
    this reaches the real uniform T source and renews its permission

handoff RF(L+2) = [x.f^(L+1).NE/T ; ret.f^(L+1).*/T]
```

Every A/B/C/D row passes its own raw C2 authority and paired C5; each
conclusion fits its own `min(global, FL(Dp)+1)` bound. The field limit and
query head advance together. Each forward pair creates a new cut, rather
than exhausting the uncertainty.

The executable proof constructs RF(2) from run-1/run-2 and computes both
actual call bindings in both directions. Induction gives, for every k:

```text
run-(2k+3) produces ZERO -> DemandTarget,D
run-(2k+4) reaches the actual source and enables the next forward run
```

The same statement is proved for arbitrary per-run choices of MAY versus
NE at the surviving head. The literal repeated edge is the **root Target**;
the helper's concrete DATA heads move deeper. No hard iteration limit,
JVM type fact or saved unbounded field suffix is used.

## 9. Why other work does not remove the witness

| Existing mechanism | Why it does not retire these rows |
| --- | --- |
| New uniform FLOW-to-NE coverage | Every cut is protected and its original is concrete T; both are exclusion guards of that rule |
| Unprotected FLOW backing | It cannot absorb a protected membership. Cleaner FLOW also excludes T |
| NORMAL correlated specialization | It preserves STAR suffix correlation; independent NE cuts are not a correlated STAR specialization |
| MUST canonicalization | The useful provider is N/MUST; the candidate is D/NE. Current same-layer rules do not compare those memberships |
| Executable MAY coverage | Can hide the output from delivery, but the bounded refinement view keeps the deeper admitted head |
| Same-head MAY/NE compaction | Allowed; both selectors admit the recurring commands, as the generic Boolean-selector proofs check |
| Local child routing | The growing branch transports a known prefix; it is not a delegated unknown STAR read. The cleaner forwards the recurring nonempty inputs unchanged |
| NORMAL precoverage | A real global cut occurs first. It cannot be reclassified NORMAL as a covered raw candidate |
| NormalTarget persistence | Does not suppress a DemandTarget. Backward analysis follows the D sink seed |
| Future added queries or NORMAL providers | The new coverage predicate rejects these protected cuts for every possible provider; no particular fixed NORMAL cache is assumed |

The scalar proof checks coverage survival in an arbitrary final provider
list, and checks the same complete initial, mark, protection and own-row
C5 coordinates. The written argument above binds that witness to the
remaining unchanged compaction rules. This is an AP/protocol counterexample,
not a full Lean formalization of the JVM interpreter and native scheduler.

## 10. Evidence and limits

The [Lean package](../../spec/lean/proposals/protected-cleaner-growth-cycle-20261114/README.md)
first rechecks every earlier reference and the new MUST-preserving cleaner
policy. It then checks **38 new constructive claims**, **359 including
dependencies**, across **21 modules**. No proof hole, classical/custom
axiom or infinite-run assumption is accepted.

A finite replay of the formal witness reaches **run-31**, retaining one
repeated root Target in every checked forward round under both NE and
MAY selectors. The generic induction, not this finite replay, proves
non-termination.

[ProtectedCleanerGrowthComponentsTest](../../core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/ProtectedCleanerGrowthComponentsTest.kt)
checks native components:

- The root cleaner preserves a nonempty MUST on NORMAL and a nonempty STAR
  on DEMAND, with existing survivor protection.
- A real run-3 helper body/C2/C5 has NORMAL `x.f.MUST/T -> ret.f.MUST/T`
  and protected DEMAND `x.f.MUST/T -> ret.f.f.[any]/T` simultaneously.
- NORMAL and DEMAND Targets coexist in either arrival order.

The current core's cut tail is MAY. The proof uses the selected NE cut.
The native test therefore checks the shared path, layer, protection and
pipeline, not a whole-engine implementation of NE or the new cleaner
policy. Its recurring nonempty cleaner inputs are outside the changed
same-head case, so the current component behavior is the selected one.
The existing nonexact run-1 answer test also checks the STAR/DEMAND bootstrap.
These **4 native tests pass**. Native latest component: **run-3**; there
is no claimed whole-program native run-31.

Fresh external receipt:
`protected-cleaner-growth-cycle-20261114/proofs-v2/receipt.json`.
No project scan was run. Historical reached/completed/accepted-forward
positions remain OWASP **run-11/11/11**, Conductor **run-8/7/7**,
Stirling-PDF **run-11/10/9**. Production and selected semantics are unchanged.

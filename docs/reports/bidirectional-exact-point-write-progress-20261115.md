# EXACT point write progress: validation

17 November follow-up: [the ordinary-prefix audit](bidirectional-prefix-return-soundness-gap-20261117.md)
confirms case 165's broad-observation loss at natural run-5 and reduces it
to one straight-line call. Case 884 now passes the updated reference and
both native observation controls at run-5. The original receipts below
remain historical; their alignment-only status is superseded.


15 November 2026. Synthetic data-flow reachability, FULL marks.
[Approach](../design/bidirectional-exact-point-write-progress-20261115.md).
[Proof guide](../../spec/proof-guide.md).
Production is unchanged; no project or Java-front-end run is claimed.

**Remove only the EXACT/FLOW exception which lets a point enter a strictly
deeper excluded identity keep.** The new negative example stops at **run-3**.
All twelve earlier reference traces remain exactly the same. All positive
new reference cases retain their observations and naturally stop.

Latest required reference: **run-15**, the unchanged Double case. The new
nested-write cases finish at **run-3, run-5 or run-11**. The wider 1,000-case
diagnostic finishes by **run-13**; its comparison horizon is run-41.

## 1. What changes

The ordinary nested core form `x.f.g = new Node()` has parallel keeps:

```text
K0: x.*   -> x.*   {f}
K1: x.f.* -> x.f.* {g}
```

From an EXACT/FLOW point at x:

```text
                         before                         after
K0                  x.$/FLOW {f},N                x.$/FLOW {f},N
K1                  x.f.MAY/FLOW,D                no result
later y=x.f         y.MAY/FLOW,D                  no y from that point
```

K1's guard does not contain the point x. The old exception creates an
uncertain descendant. This can renew a MAY demand without increasing its
head. A plain field read already rejects this descent from EXACT.

This correction does not add an exclusion, field ban, query, origin or
evidence store. It does not suppress a whole field write. A value transfer
`y.* -> x.f.g.*` still prepends f.g. STAR and all other non-EXACT operands
keep their old behavior. The existing child routing still needs a complete
cover before it can omit a supported STAR contribution.

The normal root keep still records `{f}` before `$` becomes `*` at summary
publication. Dropping that exclusion would be a different and incorrect
change. No normalization or intersection rule is changed here.

## 2. New principal example, complete cold trace

This is the same ordinary synthetic core-form input as the
[non-termination counterexample](bidirectional-nested-write-nontermination-20261115.md).
Its nested assignment is an atomic `write(base,[f,g],strong)`. The JVM
adapter's usual lowering to temporary registers is not reproduced here.

```java
Node choose(Node x, boolean down) {
    x.f.g = new Node();
    Node y;
    if (down) y = x.f;
    else { y = new Node(); y.f = x; }
    y.f.g = new Node();
    return y;
}
void entry(boolean down) {
    Node x = produce(); // Configured T at x.g and descendants, NORMAL.
    Node y = choose(x, down);
    observe(y);         // CM(y.MAY,T).
}
```

The finite allocation body of `produce` is in the counterexample report.
There is no loop, recursion, cleaner, pass rule, unresolved transfer or
intrinsic MAY producer. No actual marked g path reaches the return.

Notation: `M=MAY`, `NE=non-empty MAY`, `MUST=uniform taint`; `N/D` are
NORMAL/DEMAND. A demand is `(Dc | paired Dp)` in the current run direction.
`I(q)` is raw `q/FLOW -> q/FLOW,N`. All unshown E/mx and protection are empty.
The raw initials stay EXACT/STAR until the usual complete FLOW normalization.

### Run-1: forward, limit 1

Unchanged: this execution has no eligible EXACT/FLOW descendant keep.

```java
// Demand: discovery, none.
// Submitted: x.g.MUST/T,N.
// Raw initial: I(x.*).
Node choose(Node x, boolean down) {
    x.f.g = new Node();
    Node y;
    if (down) y = x.f;
    else { y = new Node(); y.f = x; }
    y.f.g = new Node();
    return y;
}
// Published FLOW summaries:
//   x.* -> ret.M,    D
//   x.* -> ret.f.*,  D
//   x.* -> ret.f.NE, D
// NORMAL DATA: none.

// Demand: discovery, none.
// Submitted: ZERO,N. Initial: ZERO -> ZERO,N.
void entry(boolean down) {
    Node x = produce(); // x.g.MUST/T,N
    Node y = choose(x, down); // y.M/T,D
    observe(y);
    return;
}
// Published: ZERO -> DemandTarget,D.
```

The rule hosts and constructor have stable ordinary NORMAL control completion;
the configured marking/observation actions occur at the calls in entry.
Their bodies add no refining DATA demand in this return-cone reference.

### Run-2: backward, limit 1

Backward publications are above the declaration; demand/submission/initials
are below it.

```java
// Published FLOW summaries:
//   ret.*   -> x.f.* {f,g}, N
//   ret.f.* -> x.*   {f,g}, N
//   ret.f.* -> x.f.M,        D
//   ret.f.* -> x.f.NE,       D
Node choose(Node x, boolean down) {
    x.f.g = new Node();
    Node y;
    if (down) y = x.f;
    else { y = new Node(); y.f = x; }
    y.f.g = new Node();
    return y;
}
// Demand from run-1:
//   (ret.M | x.*), (ret.f.* | x.*), (ret.f.NE | x.*)
// Submitted at return: ret.M/T,D.
// Raw initials: I(ret.$), I(ret.*), I(ret.f.$), I(ret.f.*).
// Actual backward result: x.M/T,D.

// Published: ZERO -> DemandTarget,D.
void entry(boolean down) {
    Node x = produce(); // Backward x.M/T,D reaches the known x.g marking.
    Node y = choose(x, down);
    observe(y);         // Supplies ret.M/T,D backward.
    return;
}
// Demand: (Target | ZERO).
// Submitted: ZERO,N. Initial: ZERO -> ZERO,N.
```

The two NORMAL relations are the same code-derived records as before.
Reversal saves these forward views:

```text
Wfg: x.*   -> ret.f.* {f,g},N
Rfg: x.f.* -> ret.*   {f,g},N
```

What is absent is the old EXACT-origin pair:

```text
ret.* -> x.M,    D
ret.* -> x.f.NE, D
```

The remaining `ret.f.*` demand is genuine child-query work; the correction
does not delete it by a repetition heuristic. The forward handoff is:

```text
(x.f.M  | ret.f.*)
(x.f.NE | ret.f.*)
```

### Run-3: forward, limit 2

```java
// Demand:
//   (x.f.M | ret.f.*), (x.f.NE | ret.f.*)
// Submitted: x.g.MUST/T,N.
// Raw initials: none; f and g differ.
Node choose(Node x, boolean down) {
    x.f.g = new Node();
    Node y;
    if (down) y = x.f;
    else { y = new Node(); y.f = x; }
    y.f.g = new Node();
    return y;
}
// New DATA publications: none.
// Saved Wfg and Rfg remain; neither returns T for this g input.
// Outgoing DATA demand: empty.

// Demand: (Target | ZERO).
// Submitted: ZERO,N. Initial: ZERO -> ZERO,N.
void entry(boolean down) {
    Node x = produce(); // x.g.MUST/T,N
    Node y = choose(x, down); // No marked return.
    observe(y);              // No observation witness.
    return;
}
// DemandTarget: none. NORMAL observation: none.
// DATA plus Target continuation is empty: stop naturally after run-3.
```

This does not depend on run-11 or any other limit. The proof checks the empty
final frontier and the absence of pending method work.

## 3. Real descendant examples

Use the same choose body; change only the producer's known location.

**T exactly at x.f.** Run-3 demand admits `I(x.f.$)`. The initial matches K1
at its own head and keeps `{g}`. After the read and the post-write:

```text
I(x.f.$)
    x.f.g=new: x.f.$ {g},N
    y=x.f:     y.$ {g},N
    y.f.g=new: y.$ {f,g},N
```

The returned-root T is real and remains NORMAL. The writer branch also
returns the exact point at ret.f.f. Saved/current application returns both
NORMAL outputs. The complete execution stops at run-3 with its observation.

**T uniformly at x.f.** The existing dedicated MUST query remains. It
preserves the marked returned root and surviving descendants, with genuine
exclusions. This also stops at run-3 with a NORMAL observation.

**T uniformly at x.f.f or x.f.f.f.** Real write growth still causes NE cuts;
they are not filtered by the point rule. These examples continue through
run-4 and stop at run-5 with their NORMAL observations. For x.f.f, the run-3
remaining qualified row is:

```text
x.f.f.* -> ret.f.f.NE/FLOW,D
```

It is a real relative cut, not an EXACT-to-descendant artifact. Run-4 can
reuse saved relations without creating another DATA demand. Its actual
backward MAY packet still enables Target/producer guidance, so the analysis
does not stop prematurely. Saved NORMAL delivery in run-5 gives the final
NORMAL result and clears Target continuation.

**An uncertain actual x.MAY.** C2 still emits its EXACT and STAR branches.
Only the impossible descendant contribution from EXACT is rejected. STAR
still yields ordinary MAY where necessary, or uses the previously proved
prepared children. The correction does not require knowing the next field
in advance, and does not turn MAY into a definite point.

## 4. All supplied reference executions

The old column is the previous exclusion-aware approach. Equality covers
every cold domain, current packet, saved basis, handoff and actual outer
packet. Python also compares every emitted query set.

| Reference | Old latest/natural stop | New latest/natural stop | Result |
|---|---:|---:|---|
| Nested saved replay | run-9 | run-9 | All states equal; NORMAL observation retained |
| Prefix | run-9 | run-9 | All states equal; no observation |
| PrefixPostfix | run-11 | run-11 | All states equal |
| Postfix | run-13 | run-13 | All states equal |
| RoundTrip | run-9 | run-9 | All states equal |
| Double | run-15 | run-15 | All states equal |
| Original method example | run-5 | run-5 | All states equal |
| Original generated-BB example | run-5 | run-5 | All states equal |
| LongReader | run-5 | run-5 | All states equal |
| OrdinaryTwo | run-3 | run-3 | All states equal |
| Growth regression | run-11 | run-11 | All states equal |
| Ordinary overwrite example | run-9 | run-9 | All states equal |
| New nested negative | run-61, unresolved | **run-3** | No concrete observation; empty demand |
| New nested positive MUST at f | run-61, unresolved | **run-3** | NORMAL observation retained |
| New nested positive EXACT at f | run-61, unresolved | **run-3** | NORMAL observation retained |
| New nested survivor at f.f | run-61, unresolved | **run-5** | NORMAL observation retained |
| New nested deeper input | run-61, unresolved | **run-5** | NORMAL observation retained |
| New larger f.f reader/writer, three calls | run-61, unresolved | **run-11** | NORMAL observation retained |

Run-61 is a diagnostic horizon for the old variants. It does not prove that
each such variant diverges. The original nested negative's separate uncapped
non-termination proof remains in the counterexample dossier. New natural
stopping follows from the checked empty DATA/Target frontier, not a horizon.

## 5. Work and negative consequences

Compare the same run prefix, ending at the new natural stop. These are
reference membership counts, not project timing measurements.

| New case | Queries before -> after | Executable publications before -> after | Actual outer packet memberships before -> after |
|---|---:|---:|---:|
| Negative | 7 -> 5 | 6 -> 4 | 3 -> 2 |
| MUST at f | 8 -> 6 | 10 -> 6 | 5 -> 4 |
| EXACT at f | 7 -> 6 | 8 -> 5 | 5 -> 4 |
| Survivor at f.f | 20 -> 8 | 15 -> 7 | 7 -> 6 |
| Deeper input | 21 -> 8 | 15 -> 7 | 6 -> 6 |
| Larger | 83 -> 42 | 40 -> 19 | 54 -> 48 |

The twelve old cases have identical work. No additional query, child,
subscription or origin is introduced by the correction. For a fixed native
contribution list and downstream processing, the Lean bound is non-increase.

Possible consequences are narrower: fewer DEMAND candidates, earlier natural
stopping and different confirmation timing on new programs. Removing broad
MAY may expose smaller facts in an antichain, so no whole-run cardinality
bound is claimed. All real field cuts remain. Ordinary STAR descendants,
MUST facts, concrete marks, protection and genuine exclusions must not be
removed to obtain an artificial improvement.

Five candidate native tests check real NORMAL E, the supplied first-field
point, unchanged STAR uncertainty, unchanged value writes, and every exact
point up to depth three over f/g outside the overwritten subtree. Four old
native controls also pass. These tests wrap the existing scalar operators
with the proposed filter. They do not patch the production packed traversal.
A later implementation must validate mixed packed trees at that traversal
boundary; the proposed branch change retains matching-node and descendant
processing.

## 6. Wider diagnostic and one unchanged alignment issue

A 1,000-case screen varies acyclic helper graphs, ordinary prefix reads and
writes, nested strong replacement, exact/uniform supplied marks and one to
three outer calls. An independent region interpreter uses exact points or
uniform regions with arbitrary subtree exclusions. It is a diagnostic oracle,
not a proposed runtime evidence store.

```text
tested:                         1,000
new incomplete at run-41:            0
old incomplete at run-41:            7
new loss of an old NORMAL result:    0
latest new completed run:       run-13
new/independent mismatches:          1
```

Case 884 is a reference-alignment issue in both modes. Its **complete old/new
reference states are equal**, both naturally ending at run-4 without the
independently reachable observation. Its ordinary core shape is:

```java
Node wrap(Node x) {
    if (branch) {
        x.f.f.g = new Node();
        Node a = x.f;
        Node b = new Node(); b.f = a;
        Node c = new Node(); c.g = b;
        return choose(c);
    }
    x.g.f.f = new Node();
    Node a = x.g.f;
    Node b = new Node(); b.g = a;
    return choose(b);
}
Node choose(Node x) {
    if (branch) {
        Node a = x.g.f.g;
        Node b = new Node(); b.g = a;
        Node c = new Node(); c.f = b;
        return c;
    }
    x.f.g.g = new Node();
    Node a = x.g.f.g;
    Node b = new Node(); b.g = a;
    Node c = new Node(); c.f = b;
    c.f.g.f = new Node();
    return c;
}
// T exactly at x.f.g.g; call wrap twice; observe the result or below.
```

The first branch of each helper gives the exact point sequence:

```text
f.g.g --read f--> g.g --prepend f then g--> g.f.g.g
      --read g.f.g--> g --prepend g then f--> f.g.g
```

The point is unchanged by the second wrap call. Neither written subtree kills
that route. This case is not repaired here. It prevents claiming universal
native completeness from the diagnostic. The eighteen supplied acceptance
references, their natural stops and the new point-domain correction are
checked separately.

## 7. Proof audit and reproduction

[Constructive dossier](../../spec/lean/proposals/point-write-progress-20261115/README.md):
**596 new theorems, 2,083 audited declarations, 105 modules**. The checker
verifies the previous build's source hashes, rebuilds all new modules, rejects
placeholders/custom assumptions/classical choice, and permits only `propext`
and `Quot.sound`. Every reference run has an independent quiescence proof.
Final observations and empty DATA plus Target continuation are checked.

```bash
python3 scripts/demand_experiments/point-write-progress/acceptance.py \
  --out /tmp/point-write-data
python3 scripts/demand_experiments/point-write-progress/capture.py \
  --out /tmp/point-write-data --lean-dir /tmp/point-write-cold
python3 spec/lean/proposals/point-write-progress-20261115/check.py \
  --out /tmp/point-write-proofs
python3 scripts/demand_experiments/point-write-progress/screen.py \
  --out /tmp/point-write-screen.json
cd core
./gradlew :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.PointWriteProgressNativeTest \
  --tests org.opentaint.dataflow.bidi.NestedWriteCycleComponentsTest
```

Bulk JSON, build receipts and logs stay outside the repo under
`/drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/point-write-progress-20261115/`.
The approach is a proposal; production behavior has not changed.

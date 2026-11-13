# Equal demand history can hide a later NORMAL transfer

Four uncapped native controls have equal typed history through handoff H5.
Deleting the same repeated FLOW row preserves A's final finding set, but
loses B's U finding. Both kept controls finish naturally at **run-13**;
both cut controls finish naturally at **run-11**. No iteration limit is used.

This tests the proof contract for history-based deletion. It does not
classify the actual OWASP target `1025a197…`, which remains OPEN.

## Native program

`PASS` below means one configured NORMAL FLOW micro-edge. All five common
PASS operations, and B's extra PASS, belong to **one** native instruction.
A and B have the same instructions, bases, call bindings, sources, sinks,
field declarations and marks. B has one extra micro-edge in that instruction.

```java
void main() {
    // Two exact caller temporaries delay both sides of the U query.
    sourceU(before.d1.d2.d3.d4.d5.d6.d7.d8.bytes.g); // U at this exact point.
    Object p = before.d1.d2.d3.d4.d5.d6.d7.d8;
    sourceAllT(p);                               // NORMAL root MUST T.
    Object ret = helper(p);
    sinkT(ret);                                 // Checks ret.$/T.
    after.d1.d2.d3.d4.d5.d6.d7.d8 = ret;          // Also preserve ret.
    sinkU(after.d1.d2.d3.d4.d5.d6.d7.d8.f);       // Checks exact U.
}

Object helper(Object p) {
    PASS(p.*,          ret.*);
    PASS(p.bytes.*,    ret.*);
    PASS(p.*,          ret.bytes.*);
    PASS(p.bytes.[].*, ret.*);
    PASS(p.*,          ret.bytes.[].*);
    // Only in B:
    PASS(p.bytes.g.*,  ret.f.*);
    return ret;
}
```

This is a native IR/PASS test, not a JVM lowering or alias analysis test.
The two temporary transfers are explicit NORMAL pass models. They add no
strong writes, kills or alias edges. The fixture has two methods and no
loops, statics, ND rules or rule conditions inside `helper`. Both marks
remain eligible because both corresponding sinks exist in both worlds.
The array accessor `[]` is the real native `ElementAccessor`.

Notation: `N` = NORMAL, `D` = DEMAND, `$` = EXACT, `[any]` = MAY,
`[any-taint]` = MUST. All exclusions and protection flags in the relevant
relations are empty/false. `p` is native `arg(0)`. A handoff row is
`(entry ; exit)` in the next run's coordinates.

## What is equal at H5

The complete frontier at H3 and H5 is exactly:

```text
X = helper: (ret.[any]/FLOW ; p.*/FLOW)
            main: (Target ; Zero)
```

The removal point is after H5, before run-6. This is repetition from
run-3 to run-5, not a run-1 argument.

The full retained NORMAL scalar basis after H5 is also equal:

| Native direction | Owner | Relation |
|---|---|---|
| Forward | helper | `p.*/FLOW → ret.*/FLOW` |
| Forward | helper | `p.*/FLOW → ret.bytes.*/FLOW` |
| Forward | helper | `p.[any-taint]/FLOW → ret.[any-taint]/FLOW` |
| Forward | helper | `Zero → Zero` |
| Backward | helper | `ret.*/FLOW → p.*/FLOW` |
| Backward | helper | `ret.*/FLOW → p.bytes.*/FLOW` |
| Forward | main | `Zero → Zero` |

The NORMAL root copy is present from run-1. The H5 state additionally has
the same root `Zero → NormalTarget(T)` report and the same two sink seeds.
The cut preserves the **same objects** for records, seeds and NormalTargets,
plus equal roots and all other configuration fields. It removes only X's
whole native row, retaining main's `(Target ; Zero)` row.

The equality check includes all observations from each run 1–5:

- Every accepted summary publication, including transient rows that a later
  publication covers, and every Target publication.
- All caller facts before the fixed helper binding, admitted subscriptions,
  run-1 links, initial packets and actually processed entry initials.
- Every final summary, raw/outgoing Target row, incoming/outgoing demand
  row, retained NORMAL record, NormalTarget and seed.

There are **203 observations**: `38, 41, 41, 42, 41` by run. The fixture
compares the full ordered stream after sorting only read-only set snapshots.
Runtime publication/input order and multiplicity remain unchanged. All four
streams agree. A-keep and B-keep in fact agree through run-10; their first
semantic difference occurs in run-11.

## Principal trace

These are the actual run-5 inputs and initials in both worlds:

```text
Incoming demand: (p.[any]/FLOW ; ret.*/FLOW)

Submitted p.[any-taint]/T, NORMAL:
    initial p.[any-taint]/FLOW → p.[any-taint]/FLOW, NORMAL

Submitted p.[any]/U, DEMAND:
    initial p.*/FLOW → p.*/FLOW, NORMAL
```

The extra B micro-edge does not create a new visible relation at this
point. The ordinary coarse input produces root MAY output through the
common readers. Its root MAY image covers B's child MAY image.
The root MUST input produces root MUST output, which covers B's child
MUST image. Neither route reveals the `g → f` rename as a distinct
publication. The full publication history, not only the final store,
checks this claim.

Both worlds produce these complete helper summaries in run-5:

```text
p.*/FLOW           → ret.*/FLOW,           NORMAL
p.*/FLOW           → ret.bytes.*/FLOW,     NORMAL
p.[any-taint]/FLOW → ret.[any-taint]/FLOW,  NORMAL
p.*/FLOW           → ret.[any]/FLOW,       DEMAND
```

Run-10 has field limit 9. Its delayed backward U input finally becomes
`ret.f.$/U,NORMAL`. Its initial is `ret.f.*/FLOW,NORMAL`, with the ordinary
exact FLOW companion. C5 still gives the same retained observations in A
and B at this run.

Run-11 has field limit 10. The full source path now fits, and both worlds
submit `p.bytes.g.$/U,NORMAL`. Both admit
`p.bytes.g.*/FLOW,NORMAL`, with the ordinary exact FLOW companion.
B alone publishes:

```text
p.bytes.g.*/FLOW → ret.f.*/FLOW, NORMAL
```

Applied to the concrete input, this gives `ret.f.$/U,NORMAL`. The explicit
store gives `after.d1.d2.d3.d4.d5.d6.d7.d8.f.$/U,NORMAL`, and the U sink
produces a root NormalTarget. A's common relations have no such rename.
The root NORMAL copy gives `ret.bytes.g.$/U`, which cannot satisfy `ret.f.$/U`.
The other common relations also preserve or add their named prefixes.

After the H5 cut, saved NORMAL replay remains enabled in both worlds.
It preserves the T finding. It does not infer B's previously unseen rename,
and neither cut control reaches the U finding.

## All native frontiers and results

Each cell below is `outgoing demand rows / Target demand / total findings`.
A and B differ only in the kept U report from run-11 onward.

| Run | Field limit | A-keep | B-keep | A-cut | B-cut |
|---|---:|---|---|---|---|
| run-1 | 1 | 2 / 1 / 1 | 2 / 1 / 1 | 2 / 1 / 1 | 2 / 1 / 1 |
| run-2 | 1 | 3 / 1 / 1 | 3 / 1 / 1 | 3 / 1 / 1 | 3 / 1 / 1 |
| run-3 | 2 | 2 / 1 / 1 | 2 / 1 / 1 | 2 / 1 / 1 | 2 / 1 / 1 |
| run-4 | 3 | 3 / 1 / 1 | 3 / 1 / 1 | 3 / 1 / 1 | 3 / 1 / 1 |
| run-5 | 4 | 2 / 1 / 1 | 2 / 1 / 1 | 2 / 1 / 1 | 2 / 1 / 1 |
| run-6 | 5 | 3 / 1 / 1 | 3 / 1 / 1 | 2 / 1 / 1 | 2 / 1 / 1 |
| run-7 | 6 | 2 / 1 / 1 | 2 / 1 / 1 | 1 / 1 / 1 | 1 / 1 / 1 |
| run-8 | 7 | 3 / 1 / 1 | 3 / 1 / 1 | 2 / 1 / 1 | 2 / 1 / 1 |
| run-9 | 8 | 2 / 1 / 1 | 2 / 1 / 1 | 1 / 1 / 1 | 1 / 1 / 1 |
| run-10 | 9 | 4 / 1 / 1 | 4 / 1 / 1 | 2 / 1 / 1 | 2 / 1 / 1 |
| run-11 | 10 | 2 / 0 / 1 | 2 / 0 / 2 | 0 / 0 / 1, end | 0 / 0 / 1, end |
| run-12 | 11 | 0 / 0 / 1 | 0 / 0 / 2 | — | — |
| run-13 | 12 | 0 / 0 / 1, end | 0 / 0 / 2, end | — | — |

The run-5 frontier is measured before the cut; each cut changes its two-row
store to the single main Target/Zero row. All four terminal reasons are
`COMPLETE/NO_DEMAND_EDGE`; all reported findings are non-provisional.
The final finding sets are:

```text
A-keep = A-cut = B-cut = {common T sink at main:4}
B-keep                 = {common T sink at main:4, delayed U sink at main:6}
```

## Proof-contract consequence

Let `H5(program)` contain the permitted finite edge/input history. The
native controls establish:

```text
H5(A) = H5(B)
findings(A, keep X) = findings(A, cut X)
findings(B, keep X) ≠ findings(B, cut X)
```

Any predicate that reads only this history returns the same decision in
both worlds. If it permits this deletion, B loses a refined finding. A
sound history-only predicate must reject this particular history unless
its assumptions exclude B. This does not invalidate other sound
redundancy predicates, or prove that all repeated rows must stay.

The [Lean concept and policy lemmas](../../spec/lean/proposals/redundant-demand-same-prefix-20261112/FiniteHistory.lean)
are constructive and have no axioms. They prove finite observational
equality, later distinction and decision extensionality. The native test
provides the AP execution and sink outcomes; the Lean file is not a
full-engine correspondence proof.

## Validation and scope

[Native JUnit source](../../scripts/demand_campaign/native-fixtures/SamePrefixHiddenRenameTest.kt)
uses the production handlers, stores and `IncreasingLimits` driver.
Its test-only wrapper delegates all native events and records publications
at the existing publication sink. All observers are read only. Set snapshots
are serialized in canonical order after runners join. No source transfer,
demand restriction or summary matcher is patched.

The source Gradle task passed offline: one JUnit test, four native controls,
0 failures. It uses source revision
`14d7b63369d94f49d4c551be8405ed7719f267cc` and all 68 helper sources from that
revision. `IncreasingLimits` is passed directly, without a run-11 wrapper.
The 10-second resource budget per control is a failure guard; it is not
a termination or redundancy argument. Actual natural completion is checked.

External package:

```text
/drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/
  redundant-demand-rows-20261112/cases/same-prefix-hidden-rename-v4/
```

It contains the four literal traces, ordered-prefix checks, complete
frontiers, source/compiler inputs, runtime file pins, XML, Lean output and
receipt. `scripts/demand_campaign/check_same_prefix.py CASE` verifies the
sealed evidence without an analyzer run. The exact offline Gradle command
is in `command.json`; reproduction uses a fresh external case directory.

The source-built runtime does not claim historical whole-jar byte identity.
The generic program has not been mapped to all retained providers and
guidance of corpus target `1025a197…`; no corpus verdict, queue, ledger or
production implementation changed.

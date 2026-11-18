# A nested ordinary write renews MAY demand

15 November 2026. Synthetic data-flow reachability; FULL mark T.
Counterexample to [the latest exclusion-aware child routing](../design/bidirectional-exclusion-aware-child-replay-20261115.md)
combined with [non-empty MAY](../../spec/non-empty-may.md) and the selected
bounded child refinement. Follow [proof-guide.md](../../spec/proof-guide.md).

**An EXACT/FLOW prefix probe can create MAY during a nested ordinary write.
The current routing covers STAR contributions, so this EXACT contribution
can renew the same root MAY demand indefinitely.**

Latest finite reference: **run-61**. Complete cold reference certificates:
**run-1 through run-11**. The arbitrary later recurrence is proved separately;
no iteration limit is a proof premise. Native component checks: **4 passed**.
Production is unchanged.

## 1. Scope and code

This is a **synthetic core-form counterexample**. Its ordinary nested assignment
uses the supported form `write(x,[f,g],weak=false)` and its parallel
`strongKeep` edges. The native tests execute these existing core operators.
It is not an end-to-end Java-front-end reproduction: the JVM adapter normally
lowers a local field write to one accessor and temporary registers. The proof
does not establish that this adapter produces the atomic nested form.

The complete checked reference covers the unary FLOW return cone, the original
marked caller packets, C2, paired C5, current and saved summaries, and the
ZERO/Target continuation. Other bases and mark-changing rules are not added
to this reference. This is not a whole-production simulation theorem.

[Code notation](../../spec/lean/proposals/nested-write-cycle-20261115/NestedWriteCycle.java):

```java
final class Node { Node f; Node g; }

Node produce() {
    Node x = new Node();
    x.f = new Node();
    x.f.f = new Node();
    x.g = new Node();
    return x;
}

Node choose(Node x, boolean down) {
    x.f.g = new Node();
    Node y;
    if (down) {
        y = x.f;
    } else {
        y = new Node();
        y.f = x;
    }
    y.f.g = new Node();
    return y;
}

void observe(Node y) { }

void entry(boolean down) {
    Node x = produce(); // Call-site marking rule: T at x.g and descendants.
    Node y = choose(x, down);
    observe(y);         // Call-site observation: CM(y.[any],T).
}
```

There is no loop, recursion, cleaner, pass rule, unresolved transfer, static
field, or intrinsic MAY marking rule. Allocation adds no T. The only marking
rule gives the NORMAL fact `x.g.MUST/T`; the only observation reads `y.MAY/T`.
The fresh receiver objects required by both branches exist.

For every concrete marked point `x.g.s`:

```text
read branch:   x.g.s --read f--> no result
write branch:  x.g.s --y.f=x--> y.f.g.s --overwrite y.f.g--> no result
```

Thus no actual T reaches the returned object. Lean proves this for arbitrary
suffix s, not just the allocated paths. The recurring Target is anonymous
DEMAND; this example has no confirmed NORMAL observation.

## 2. Notation and the decisive native transfer

```text
$ = EXACT       * = correlated STAR
M = MAY         NE = non-empty MAY       MUST = uniform taint
N = NORMAL      D = DEMAND
{f,g} = real field exclusion, at the displayed suffix scope
(Dc | Dp) = current-direction demand entry and its paired exit selector
```

All query initials below have FLOW, NORMAL support and false protection.
`I(q)` means the raw identity `q/FLOW -> q/FLOW,N`. It is not a public
STAR premise until normalization. Original caller packets carry concrete T.
Unshown exclusions and mark exclusions are empty. The returned base is `ret`.

A nested strong write has two parallel keep micro-edges:

```text
x.*   -> x.*   {f}
x.f.* -> x.f.* {g}
```

Each consumes the original input. They must not be applied sequentially.
For `I(x.$)` after run-1, native execution gives:

```text
x.$/FLOW,N + first keep   = x.$/FLOW {f},N
x.$/FLOW,N + second keep  = x.f.M/FLOW,D
```

The second result is the existing excluded-identity-write exception for
EXACT/FLOW. A plain `y=x.f` cannot produce a y fact from `x.$/FLOW`.
However, once the write has produced `x.f.M`, that read gives `y.M,D`.
This is an intrinsic transfer promotion, not a field-limit cut.

The complete forward EXACT-probe trace is:

```text
I(x.$)
  x.f.g=new:
    x.$ {f},N                 x.f.M,D
  read branch y=x.f:
    no y from x.$ {f}         y.M,D
  y.f.g=new:
    y.M,D                     // root MAY remains
  return:
    raw x.$/FLOW -> ret.M/FLOW,D
  C5 and FLOW normalization:
    public x.*/FLOW -> ret.M/FLOW,D
```

The write branch also gives:

```text
I(x.$)
  x.f.g=new:                  x.$ {f},N + x.f.M,D
  y.f=x:                      y.f.$ {f},N + y.f.f.M,D
  y.f.g=new:                  y.f.$ {f,g},N + y.f.f.M,D
  C5, paired exit ret.*:
    y.f.f.M --budget 1--> ret.f.NE,D
```

The global field limit can grow without changing that paired budget:
`min(globalLimit, FL(ret.*)+1) = 1`.

## 3. Cold trace: run-1

Every run is drained before handoff. Rows below are qualified C5 demand rows;
executable MAY packet coverage can merge their delivered results.

```java
// Run-1 FORWARD, field limit 1.
// Demand: none (discovery).
// Submitted: x.g.MUST/T,N.
// Raw initials: I(x.*).
Node choose(Node x, boolean down) {
    x.f.g = new Node();
    Node y;
    if (down) y = x.f;
    else { y = new Node(); y.f = x; }
    y.f.g = new Node();
    return y;
}
// Newly published FLOW summaries:
//   x.* -> ret.M,    D
//   x.* -> ret.f.*,  D
//   x.* -> ret.f.NE, D
// Newly saved NORMAL DATA: none.

// Demand: none (discovery).
// Submitted: ZERO,N.
// Raw initial: ZERO -> ZERO,N.
void entry(boolean down) {
    Node x = produce(); // x.g.MUST/T,N
    Node y = choose(x, down);
    // Actual returned packet: y.M/T,D.
    observe(y);
    return;
}
// Published: ZERO -> DemandTarget,D.
```

The source-code hosts `produce` and `observe` have only ordinary, stable NORMAL
control completion in this return-cone reference. Their call-site rules execute
in `entry`; they introduce no additional refining DATA demand. The constructor
also has ordinary NORMAL control completion. This convention applies in every
following annotated run.

Run-1 handoff at `choose` selects:

```text
(ret.M | x.*), (ret.f.* | x.*), (ret.f.NE | x.*)
```

The root control demand becomes `(Target | ZERO)`.

## 4. Cold trace: run-2

Backward annotations appear below the method; publications appear above it.

```java
// Run-2 BACKWARD, field limit 1.
// Newly published FLOW summaries:
//   ret.*   -> x.M,           D
//   ret.*   -> x.f.NE,        D
//   ret.*   -> x.f.* {f,g},   N
//   ret.f.* -> x.*   {f,g},   N
//   ret.f.* -> x.f.M,         D
//   ret.f.* -> x.f.NE,        D
Node choose(Node x, boolean down) {
    x.f.g = new Node();
    Node y;
    if (down) y = x.f;
    else { y = new Node(); y.f = x; }
    y.f.g = new Node();
    return y;
}
// Demand:
//   (ret.M | x.*), (ret.f.* | x.*), (ret.f.NE | x.*)
// Submitted at return: ret.M/T,D.
// Raw initials: I(ret.$), I(ret.*), I(ret.f.$), I(ret.f.*).
// Actual backward output to entry: x.M/T,D.

// Published: ZERO -> DemandTarget,D.
void entry(boolean down) {
    Node x = produce(); // Backward x.M/T,D accepts the known x.g producer.
    Node y = choose(x, down);
    observe(y);         // Backward observation submits ret.M/T,D to choose.
    return;
}
// Demand: (Target | ZERO).
// Submitted: ZERO,N.
// Raw initial: ZERO -> ZERO,N.
```

The two NORMAL backward publications have real code producers. Reversal saves
these forward views, both tagged as BACKWARD-produced:

```text
Wfg: x.*   -> ret.f.* {f,g},N
Rfg: x.f.* -> ret.*   {f,g},N
```

They are not predefined records. Later NORMAL precoverage suppresses their
republication. Both remain stored.

Run-2 handoff gives the forward demand set:

```text
DF = {
    (x.M    | ret.*),
    (x.f.NE | ret.*),
    (x.f.M  | ret.f.*),
    (x.f.NE | ret.f.*)
}
```

## 5. Every forward run-3, run-5, run-7, ...

This is one template for all `r=3+2k`, with field limit `r-1`.
The cold certificate checks its first instances; the uncapped proof checks
arbitrary k.

```java
// Demand: DF (the four rows listed above).
// Submitted: x.g.MUST/T,N.
// Raw initials:
//   I(x.g.*)                  // first-field refinement of x.M
//   I(x.$)                    // retained conditional FLOW prefix probe
// Other DF entries start no query: their first field f differs from g.
Node choose(Node x, boolean down) {
    x.f.g = new Node();
    Node y;
    if (down) y = x.f;
    else { y = new Node(); y.f = x; }
    y.f.g = new Node();
    return y;
}
// Newly published FLOW summaries:
//   x.* -> ret.M,    D
//   x.* -> ret.f.NE, D
// Newly saved NORMAL DATA: none. Wfg and Rfg remain persisted.

// Demand: (Target | ZERO).
// Submitted: ZERO,N.
// Raw initial: ZERO -> ZERO,N.
void entry(boolean down) {
    Node x = produce(); // x.g.MUST/T,N
    Node y = choose(x, down);
    // Saved Wfg rejects g: g is excluded.
    // Saved Rfg rejects g: required first field is f.
    // Current coarse summary supplies y.M/T,D.
    observe(y);
    return;
}
// Published: ZERO -> DemandTarget,D.
// No NORMAL observation.
```

`I(x.g.*)` produces no return fact in either branch: the read requires f;
the write branch produces `y.f.g.*`, which the post-write kills.
`I(x.$)` produces the two D summaries in section 2. Thus the prefix probe,
not the concrete g refinement, renews the coarse obligation.

The next backward demand is always:

```text
DB = {(ret.M | x.*), (ret.f.NE | x.*)}
```

## 6. Every backward run-4, run-6, run-8, ...

This template covers all `r=4+2k`, with field limit `r-1`.

```java
// Newly published FLOW summaries:
//   ret.*   -> x.M,    D
//   ret.*   -> x.f.NE, D
//   ret.f.* -> x.f.M,  D
//   ret.f.* -> x.f.NE, D
// No new NORMAL DATA. Wfg and Rfg stay persisted.
Node choose(Node x, boolean down) {
    x.f.g = new Node();
    Node y;
    if (down) y = x.f;
    else { y = new Node(); y.f = x; }
    y.f.g = new Node();
    return y;
}
// Demand: DB.
// Submitted at return: ret.M/T,D.
// Raw initials: I(ret.$), I(ret.*), I(ret.f.$), I(ret.f.*).
// Existing child mask for I(ret.*): {f}.
// No child mask routes the EXACT-origin write promotion.
// Actual backward output: x.M/T,D.

// Published: ZERO -> DemandTarget,D.
void entry(boolean down) {
    Node x = produce(); // x.M/T,D reaches the marking rule at x.g.
    Node y = choose(x, down);
    observe(y);
    return;
}
// Demand: (Target | ZERO).
// Submitted: ZERO,N.
// Raw initial: ZERO -> ZERO,N.
```

Backward reversal of the write branch reads f between the two strong keeps.
The EXACT return probe therefore renews `ret.* -> x.M,D` by the same native
promotion/read sequence. The STAR parent's prepared f children remove the
supported STAR contribution; they do not remove this EXACT contribution.
C5 reconstructs DF for the next forward run.

## 7. Uncapped proof

The [Lean dossier](../../spec/lean/proposals/nested-write-cycle-20261115/README.md)
checks these distinct obligations:

1. **Cold reachability.** Starting with empty demand and no saved records,
   native-form transfer, C2, C5, original caller delivery and handoff give the
   frozen states through run-11. Each state is independently quiescent.
2. **Record provenance.** Run-2 derives Wfg and Rfg from the body. The saved
   record set is constant after run-2. Nothing is borrowed from a future run.
3. **Complete reference packet stability.** For arbitrary k, every C2 plan,
   raw body result, paired intersection and relative cut equals its mature
   forward/backward base computation. Every plan member is included.
4. **Two-step recurrence.** With `step` equal to the checked C2/transfer/C5
   pipeline, not a table-defined cycle:

   ```text
   stepForward(DF, limit=2k+4) = DB
   stepBackward(DB, limit=2k+5) = DF
   ```

   Induction proves this for every k. Both sets contain a nonempty root MAY
   obligation. The stable phase is reached in the cold trace after run-3/4.
5. **Actual delivery and control.** Each later forward call returns only
   `y.M/T,D`; each backward call returns only `x.M/T,D`. The latter permits
   the actual producer at x.g. Both directions produce fresh anonymous Target
   guidance. Paired C5 accepts it, its handoff admits ZERO, and the continuation
   predicate remains true. There is no manufactured NORMAL observation.
6. **Concrete negative reachability.** Every exact path in the supplied g
   region is rejected or overwritten before return, for arbitrary suffix.

Two additional checks isolate why the previous repair cannot remove this
witness: the EXACT-probe read-branch result is still MAY for **any child mask**;
and a DEMAND root MAY result passes C5 regardless of the saved NORMAL packet.
Neither statement assumes an empty exclusion on a saved reader.

The reference counts qualified rows. Even if an executable MAY view absorbs a
narrower NE result, the root MAY result remains. Existing MUST coverage cannot
cover a STAR-initial FLOW MAY relation. Wfg and Rfg cannot replace its original
caller service: both reject the actual g input. Increasing the field limit does
not change the intrinsic MAY promotion or the root paired output budget.

This is a counterexample to termination of the specified synthetic core-form
pipeline. A native whole-analyzer or JVM-front-end counterexample requires a
separate reproduction; neither is claimed by the component tests.

## 8. Validation and artifacts

- Native test: `NestedWriteCycleComponentsTest`, 4 passing checks of the actual
  field-write/read/normalization operators and concrete g input.
- Lean: **90 new theorems**, **1,487 audited declarations**, **85 modules**.
  All dependency modules were rebuilt, and their hashes were checked again
  before this package's final audit. Only `propext` and `Quot.sound` are permitted.
  No unproved assumptions, classical choice, placeholders or external decision
  oracle. Cold finite states and the uncapped recurrence are separate claims.
- Code notation compiles with `javac`; this checks syntax, not adapter lowering.
- Broad preliminary searches: 10,000 three-owner DAG cases and 10,000 wider
  three-field cases reached no survivor at the run-61 horizon. These are
  diagnostics, not termination proofs.

Reproduce the minimal cold witness and proof audit from the repository root:

```bash
python3 scripts/demand_experiments/exclusion-counterexample/capture.py \
  --out /tmp/nested-write-data --lean-dir /tmp/nested-write-cold
python3 spec/lean/proposals/nested-write-cycle-20261115/check.py \
  --out /tmp/nested-write-proofs
cd core
./gradlew :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.NestedWriteCycleComponentsTest
```

Large JSON and proof build output stay outside the repository at
`/drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/nested-write-cycle-20261115/`.
The decisive code, trace, recurrence and limitations are embedded in this report.

Subsequent proposal: [EXACT point write progress](../design/bidirectional-exact-point-write-progress-20261115.md)
removes the EXACT/FLOW descendant-keep exception. Under that proposed rule,
this reference naturally stops at run-3. This does not change the historical
uncapped counterexample proof for the earlier rule.

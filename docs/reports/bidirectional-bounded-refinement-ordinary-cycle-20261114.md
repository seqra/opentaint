# Ordinary-code non-termination after bounded refinement

14 November 2026. Counterexample under
[non-empty MAY](../../spec/non-empty-may.md) and
[bounded demand refinement](../design/bidirectional-bounded-demand-refinement-20261114.md),
including local routing without artificial exclusions. Follow
[proof-guide.md](../../spec/proof-guide.md). Production remains unchanged.

**No pass rules, loops, recursion, aliases, statics, cleaners, ND rules or
predefined summaries are used.** The helper either reads two fields or
writes two fields. Its caller calls it twice. The source and sink are
ordinary whole-object rules.

The repeated edge is the root's `ZERO -> DemandTarget, DEMAND`. The helper's
DATA demands move deeper rather than repeating at identical coordinates.
They keep producing that same root edge for arbitrarily many completed
runs. This distinction is part of the counterexample.

## 1. Code and rules

```java
class Node {
    Node f;
}

static void main(boolean b1, boolean b2) {
    Node x = sourceTree();
    Node y = choose(x, b1);
    Node z = choose(y, b2);
    sinkTree(z);
}

static Node choose(Node x, boolean b) {
    if (b) return x.f.f;
    Node t = new Node();
    t.f = x;
    Node y = new Node();
    y.f = t;
    return y;
}
```

`sourceTree` and `sinkTree` have no analyzable body. Configure only:

```text
sourceTree: AssignMarkOnAnyAccessor(T, Result)
            // The result and its descendants have T: MUST, NORMAL.

sinkTree:   ContainsMarkOnAnyField(Argument(0), T)
            // Ordinary whole-object sink; backward seed is MAY, not MUST.
```

The source returns a Node of unknown shape. This is the usual whole-object
source contract, not an existential MAY pass target. Neither rule models
any write. Every field read/write comes from the shown code. Use FULL mode
and disable aliases for this reference.

There are two analyzable blocks: `main` and `choose`. There is no loop
decomposition. `choose` contains ordinary conditional basic blocks inside
its method graph. Constructors contribute no marked return in this example.

## 2. Notation and the decisive difference

```text
F = FLOW; U = MUST; M = MAY; NE = non-empty MAY
N = NORMAL; D = DEMAND; Z = ZERO; DT = DemandTarget
ret = choose's method-result base
f^k = k repeated f accessors after a named base, never a base itself

X = Z -> DT,D                       // main's repeated demand
[Dc ; Dp]                           // complete incoming paired demand row
all E/mx are empty; H=false
```

The earlier terminating reference wrote **one** field. This example writes
**two**. At forward field limit L, an admitted query at depth L-1 grows to
depth L+1. The ordinary transfer cuts it **before** the proposed NORMAL
precoverage test at the summary boundary:

```text
initial:       x.f^(L-1).U/F -> itself,N
double write:  x.f^(L-1).U/F -> ret.f^(L+1).U/F,N
global cut:    x.f^(L-1).U/F -> ret.f^L.NE/F,D
```

The proposal cannot precover this boundary result: it is already D/NE.
The proposed precoverage explicitly excludes DEMAND results. A saved
NORMAL `x.* -> ret.f.f.*` still runs first on the original actual. It does
not cancel this new, successful demand admission.

## 3. Per-iteration trace

The annotations give a **closed witness trace**. Each method is shown for
every run. They list the rows, offers, initials and summaries needed by the
recurrence, not a claim that no additional NORMAL records or paired rows
exist. Section 5 checks survival in the presence of those records. In
particular, no incomplete NORMAL store is frozen to manufacture repetition.

All displayed DATA initials start as identities. Trivial unchanged argument
and ZERO identities may also be retained. They do not produce a return
value or cover the displayed return demands.

### Run-1: forward, limit 1

```java
// Demand: none. Submitted: Z,N. Initial: Z -> Z,N.
static void main(boolean b1, boolean b2) {
    Node x = sourceTree();       // Z -> x.U/T,N
    Node y = choose(x, b1);      // Actual x.U/T,N -> y.M/T,D
    Node z = choose(y, b2);      // Actual y.M/T,D -> z.M/T,D
    sinkTree(z);                // D witness: Z -> DT,D
}
// Published DEMAND: X = Z -> DT,D.

// Demand: none.
// Submitted: x.U/T,N at call 1; x.M/T,D at call 2.
// Run-1 abstract initial: x.*/F -> x.*/F,N.
static Node choose(Node x, boolean b) {
    if (b) return x.f.f;         // x.* -> ret.M/F,D
    Node t = new Node();
    t.f = x;                    // x.* -> t.f.*/F,N
    Node y = new Node();
    y.f = t;                    // Would be y.f.f.*; cut to y.f.NE/F,D
    return y;
}
// NORMAL return provider: none from this root FLOW query.
// Local DEMAND: x.*/F -> ret.M/F,D; x.*/F -> ret.f.NE/F,D.
// Caller-visible union can keep only the MAY row.
// The local refinement store retains ret.f.NE for run-2 admission.
```

### Run-2: backward, limit 1

Published summaries are above backward declarations; incoming demand,
submitted facts and emitted initials are below them.

```java
// Published DEMAND: X = Z -> DT,D. Source permission renewed.
static void main(boolean b1, boolean b2) {
    Node x = sourceTree();       // Reverse x.M/T,D matches whole-object source.
    Node y = choose(x, b1);      // Receives y.M/T,D; returns x.M/T,D backward.
    Node z = choose(y, b2);      // Receives z.M/T,D; returns y.M/T,D backward.
    sinkTree(z);                // Backward seed: z.M/T,D.
}
// Demand: [Target ; Z]. Submitted: Z,N. Initial: Z -> Z,N.

// Local DEMAND includes:
//   ret.*/F   -> x.f.NE/F,D
//   ret.f.*/F -> x.f.NE/F,D      // bootstrap row retained locally
//   ret.f.*/F -> x.M/F,D         // caller-visible MAY answer
static Node choose(Node x, boolean b) {
    if (b) return x.f.f;         // Reverse prepends f.f. Global cut -> x.f.NE.
    Node t = new Node();
    t.f = x;                    // Reverse remaining unknown f -> x.M/F,D.
    Node y = new Node();
    y.f = t;                    // ret.f.* reads its known f -> t.*.
    return y;
}
// Incoming rows: [ret.M/F ; x.*/F], [ret.f.NE/F ; x.*/F].
// Submitted at both reverse calls: ret.M/T,D.
// Initials from original C2 and the one-field plan:
//   ret.$/F,N; ret.*/F,N; ret.f.$/F,N; ret.f.*/F,N.
// The original-root STAR delegates its unknown-f case locally.
// ret.f.* is already at the limit; no ret.f.f child can be admitted.
// Next forward row includes [x.f.NE/F ; ret.f.*/F].
```

The NE row is used as **local guidance**. The trace does not apply it to
callers after MAY has hidden it. The visible MAY row supplies the real
source hit and the next source permission.

### Run-3: forward, limit 2

```java
// Demand: [Target ; Z]. Submitted: Z,N. Initial: Z -> Z,N.
// sourceTree is permitted by the real run-2 hit.
static void main(boolean b1, boolean b2) {
    Node x = sourceTree();       // x.U/T,N
    Node y = choose(x, b1);      // A2 below supplies y.f.f.NE/T,D.
    Node z = choose(y, b2);      // B2 below supplies z.f.f.NE/T,D.
    sinkTree(z);                // Republishes X on D.
}
// Published DEMAND: X = Z -> DT,D.
// Saved/current NORMAL replay can also yield a NORMAL sink witness.

// Witness demand: [x.f.NE/F ; ret.f.*/F].
// Call 1 submitted: x.U/T,N.
// Emitted initial: x.f.U/F -> x.f.U/F,N.
// Call 2 submitted from A2: x.f.f.NE/T,D.
// Emitted initial: x.f.f.*/F -> x.f.f.*/F,N.
static Node choose(Node x, boolean b) {
    if (b) return x.f.f;         // Uniform or known-prefix read; no unknown MAY.
    Node t = new Node();
    t.f = x;
    Node y = new Node();
    y.f = t;                    // q=x.f.U: result ret.f.f.f.U -> cut at 2.
                                // q=x.f.f.*: result ret.f^4.* -> cut at 2.
    return y;
}
// Published witness DEMAND:
//   A2: x.f.U/F   -> ret.f.f.NE/F,D
//   B2: x.f.f.*/F -> ret.f.f.NE/F,D
// Each uses its own original paired exit ret.f.*: budget 1+1=2.
// NORMAL providers from other queries remain available, including
// the eventual double-read and double-write STAR relations.
// Next backward row from B2: [ret.f.f.NE/F ; x.f.f.*/F].
```

### Run-4: backward, limit 3

```java
// Published DEMAND: X = Z -> DT,D. Source permission renewed.
static void main(boolean b1, boolean b2) {
    Node x = sourceTree();       // x.f.f.f.NE/T,D overlaps its uniform target.
    Node y = choose(x, b1);      // Receives ret.f.f.f.NE/T,D at reverse call 1.
    Node z = choose(y, b2);      // Root MAY offer -> y.f.f.f.NE/T,D via C2.
    sinkTree(z);                // Seed z.M/T,D.
}
// Demand: [Target ; Z]. Submitted: Z,N. Initial: Z -> Z,N.

// Published witness DEMAND:
//   C2: ret.f.f.*/F   -> x.f.f.f.NE/F,D
//   D2: ret.f.f.f.*/F -> x.f.f.f.NE/F,D
static Node choose(Node x, boolean b) {
    if (b) return x.f.f;         // Reverse adds f.f: depths 4 or 5, cut at 3.
    Node t = new Node();
    t.f = x;
    Node y = new Node();
    y.f = t;
    return y;
}
// Witness demand: [ret.f.f.NE/F ; x.f.f.*/F].
// Reverse call 2 submitted: ret.M/T,D.
// Initial: ret.f.f.*/F -> itself,N.
// Reverse call 1 submitted from C2: ret.f.f.f.NE/T,D.
// Initial: ret.f.f.f.*/F -> itself,N.
// Paired output budget: FL(x.f.f.*)+1=3. No additional cut.
// Next forward row from D2: [x.f.f.f.NE/F ; ret.f.f.f.*/F].
```

### Run-5: forward, limit 4

```java
// Demand: [Target ; Z]. Submitted: Z,N. Initial: Z -> Z,N.
// sourceTree permitted by run-4.
static void main(boolean b1, boolean b2) {
    Node x = sourceTree();       // x.U/T,N: constant, already precise.
    Node y = choose(x, b1);      // A4 supplies y.f^4.NE/T,D.
    Node z = choose(y, b2);      // B4 supplies z.f^4.NE/T,D.
    sinkTree(z);                // Same X, regardless of a NORMAL witness.
}
// Published DEMAND: X = Z -> DT,D.

// Witness demand: [x.f.f.f.NE/F ; ret.f.f.f.*/F].
// Call 1 submitted: x.U/T,N. Initial: x.f.f.f.U/F -> itself,N.
// Call 2 submitted: x.f^4.NE/T,D. Initial: x.f^4.*/F -> itself,N.
static Node choose(Node x, boolean b) {
    if (b) return x.f.f;
    Node t = new Node();
    t.f = x;
    Node y = new Node();
    y.f = t;                    // Raw depths 5 or 6 -> global cut at 4.
    return y;
}
// Published witness DEMAND:
//   A4: x.f.f.f.U/F -> ret.f^4.NE/F,D
//   B4: x.f^4.*/F   -> ret.f^4.NE/F,D
// Paired budget: 3+1=4.
// Next backward row: [ret.f^4.NE/F ; x.f^4.*/F].
```

### Run-6: backward, limit 5

```java
// Published DEMAND: X = Z -> DT,D. Source permission renewed.
static void main(boolean b1, boolean b2) {
    Node x = sourceTree();       // x.f^5.NE/T,D -> real source hit.
    Node y = choose(x, b1);      // Reverse call 1 receives ret.f^5.NE/T,D.
    Node z = choose(y, b2);      // Reverse call 2 receives ret.M/T,D.
    sinkTree(z);                // Seed z.M/T,D.
}
// Demand: [Target ; Z]. Submitted: Z,N. Initial: Z -> Z,N.

// Published witness DEMAND:
//   C4: ret.f^4.*/F -> x.f^5.NE/F,D
//   D4: ret.f^5.*/F -> x.f^5.NE/F,D
static Node choose(Node x, boolean b) {
    if (b) return x.f.f;         // Reverse raw depths 6 or 7 -> cut at 5.
    Node t = new Node();
    t.f = x;
    Node y = new Node();
    y.f = t;
    return y;
}
// Witness demand: [ret.f^4.NE/F ; x.f^4.*/F].
// Submitted: ret.M/T,D at call 2; ret.f^5.NE/T,D at call 1.
// Initials: ret.f^4.*/F,N; ret.f^5.*/F,N, both identities.
// Paired budget: 4+1=5.
// Next forward row: [x.f^5.NE/F ; ret.f^5.*/F].
```

### Every later forward run: run-(2k+1), limit L=2k, k>=3

```java
// Demand [Target ; Z]. Submitted Z,N. Initial Z -> Z,N.
// Source permission renewed by run-(2k).
static void main(boolean b1, boolean b2) {
    Node x = sourceTree();       // x.U/T,N
    Node y = choose(x, b1);      // AL -> y.f^L.NE/T,D
    Node z = choose(y, b2);      // BL -> z.f^L.NE/T,D
    sinkTree(z);                // Z -> DT,D
}
// Published DEMAND: X = Z -> DT,D.

// Demand: [x.f^(L-1).NE/F ; ret.f^(L-1).*/F].
// Call 1 submitted x.U/T,N; initial x.f^(L-1).U/F,N.
// Call 2 submitted x.f^L.NE/T,D; initial x.f^L.*/F,N.
// Both initials are identities.
static Node choose(Node x, boolean b) {
    if (b) return x.f.f;
    Node t = new Node();
    t.f = x;
    Node y = new Node();
    y.f = t;                    // Depth L+1 or L+2 -> global NE cut at L.
    return y;
}
// Published DEMAND:
//   AL: x.f^(L-1).U/F -> ret.f^L.NE/F,D
//   BL: x.f^L.*/F     -> ret.f^L.NE/F,D
// Paired budget FL(ret.f^(L-1).*)+1=L; C5 keeps both cuts.
// Next backward row: [ret.f^L.NE/F ; x.f^L.*/F].
```

### Every later backward run: run-(2k+2), limit L+1

```java
// Published DEMAND: X = Z -> DT,D. Real source permission renewed.
static void main(boolean b1, boolean b2) {
    Node x = sourceTree();       // x.f^(L+1).NE/T,D overlaps source's MUST.
    Node y = choose(x, b1);      // Reverse call 1: ret.f^(L+1).NE/T,D.
    Node z = choose(y, b2);      // Reverse call 2: ret.M/T,D.
    sinkTree(z);                // Seed z.M/T,D.
}
// Demand [Target ; Z]. Submitted Z,N. Initial Z -> Z,N.

// Published DEMAND:
//   CL: ret.f^L.*/F     -> x.f^(L+1).NE/F,D
//   DL: ret.f^(L+1).*/F -> x.f^(L+1).NE/F,D
static Node choose(Node x, boolean b) {
    if (b) return x.f.f;         // Reverse depth L+2/L+3 -> cut at L+1.
    Node t = new Node();
    t.f = x;
    Node y = new Node();
    y.f = t;
    return y;
}
// Demand: [ret.f^L.NE/F ; x.f^L.*/F].
// Submitted ret.M/T,D at call 2; ret.f^(L+1).NE/T,D at call 1.
// Initials ret.f^L.*/F,N; ret.f^(L+1).*/F,N, both identities.
// Paired budget L+1. No backward MUST initial.
// Next forward row: [x.f^(L+1).NE/F ; ret.f^(L+1).*/F].
```

## 4. Induction without an iteration limit

For every even L>=2 define the complete incoming forward row:

```text
RF(L) = [x.f^(L-1).NE/F ; ret.f^(L-1).*/F].
```

**Base.** The real run-1 double write is cut to `ret.f.NE`. Run-2 starts
the legal `ret.f.*` query under that local row. Reversing the two reads
prepends two fields, cuts to `x.f.NE`, and publishes
`ret.f.* -> x.f.NE,D`. Its handoff is RF(2). The visible MAY return through
the reverse write renews the real source permission.

**Forward step at L.** RF(L) and the actual whole-object source admit
`x.f^(L-1).U/F`, using the existing rebased MUST lane. The double write
gives L+1 fields; the global cut gives AL. The actual source covers the
entire uniform premise of AL, so its ordinary application submits
`x.f^L.NE/T,D` at call 2. C2's first-new-field rule admits `x.f^L.*/F`.
Its double write is cut to BL. Applying BL reaches the sink on D and
publishes X. BL supplies the backward row `[ret.f^L.NE ; x.f^L.*]`.

**Backward step at L+1.** The ordinary root MAY sink seed admits
`ret.f^L.*/F`. Reversing the read branch prepends two fields; the global
cut gives CL. Applying CL supplies `ret.f^(L+1).NE/T,D` to the first
reverse call. C2 emits `ret.f^(L+1).*/F`. Its reverse read produces DL
after the global cut. DL's actual reaches the source's uniformly marked
region, renewing permission. Its handoff is RF(L+2).

All paired relative budgets are exactly the current global limit for these
witnesses. No row borrows another row's exit permission. All offers used
to admit the second query are computed by the first query's actual result.

By induction, RF(2), RF(4), RF(6), ... are produced in arbitrarily late
forward runs. Every forward run produces the **same** X; every intervening
backward run renews source permission and root Target guidance. Thus:

```text
for every k>=1:
    X belongs to H_(2k+1)
    X belongs to H_(2k+2)
```

H_r is the final post-compaction handoff. In particular X repeats after
run-i and run-(i+2) at every selected removal point i>=3. No finite hard
iteration limit is used.

Each run is finite. At fixed limit it has a finite field/base/tail/mark
domain, a finite acyclic method graph and two calls. Ordinary membership
deduplication reaches its within-run fixed point. The non-termination is
the infinite sequence of completed runs.

## 5. Why existing mechanisms do not discharge the witness

**Local routing.** Every growing operation in the recurrence is a known
prefix write: the real forward writes or the reversed field reads. It is
not an unknown-suffix read producing MAY. The no-artificial-E plan does
not delegate these operations, for any G. Child plans can add queries;
they cannot remove the at-limit branch without retaining its complete
service. If a prepared finer child replaces a coarse backward family,
its at-limit STAR query is already the DL case.

**NORMAL precoverage.** The normal double-read/write relations are not
assumed absent. Retain and apply both, including uniform specializations.
The recurrence cuts *inside the block*, before the boundary check; the
boundary receives NE/D. The proposal expressly retains a real global cut
and excludes DEMAND results from its NORMAL precoverage case. The Lean
publication lemmas permit any NORMAL-coverage answer, including `true`.

**Executable and handoff subsumption.** The retained NORMAL STAR relation
does not cover an independent NE relation by the selected rules. See
[non-empty MAY, section 7](../../spec/non-empty-may.md). No STAR-to-NE
replacement or MUST-to-NE deletion is selected. For the large queries,
the other direct branch has a known/uniform read and produces STAR/MUST
on N, not a same-P MAY/D row which could absorb this cut. Even a covered
caller-visible child cannot erase its required local refinement head and
paired budget. A shorter-premise row cannot be used to silently reduce
that budget.

**Actual fact canonicalization.** A NORMAL MUST actual may coexist with
these NE/DEMAND actuals. The selected MUST canonicalization preserves
mark/layer/H classes and adds no MUST-to-NE deletion. Consequently the
normal actual does not cancel the successful second-call NE offer.

**Targets.** Ordinary paired Target/ZERO gates accept the root X. A NORMAL
sink report, when present, does not erase anonymous DemandTarget from an
unresolved witness. No new control bypass or Target subsumption is used.

**No stationary DATA claim.** These DATA heads do increase, but they chase
fresh cuts of conditional queries. The original whole-object source and
the finite code do not become less uncertain. The same root terminal
question never disappears. The increasing-depth DATA recurrence and the
fixed Target repetition together refute termination.

## 6. Evidence and proof scope

The [constructive Lean package](../../spec/lean/proposals/bounded-refinement-ordinary-cycle-20261114/README.md)
imports the actual selected C2/C5 functions and the revised local routing
reference. It checks:

- run-1/run-2 bootstrap and caller-visible MAY handling;
- raw initial families, both unchanged limits and both directions;
- ordinary prefix writes under arbitrary local delegation masks;
- global NE cuts before publication, with any NORMAL provider answer;
- own-row C5 and applications to original actuals;
- computed cross-call offers and real whole-object source overlap;
- handoff reversal, paired root controls and induction over unbounded runs.

Result: **PASS, 13 modules, 241 audited declarations**, including 42 new
theorems. No proof uses a hard iteration limit, an unproved custom axiom,
`sorryAx` or `Classical.choice`. The receipt and exact source hashes are
linked in the proof package README.

The proof is a closed witness projection, not a full Kotlin/JVM engine
simulation. It establishes the ordinary prefix/control component; the
embedding and survival argument above explicitly retains saved NORMAL
records and the current compaction contract. It does not infer infinite
behavior from a finite timing experiment or reset a NORMAL store each run.

An exploratory model searched 504 small read/write/source configurations.
The selected family still has demand after **run-31**. That bounded
experiment is supplementary; the uncapped induction is the non-termination
proof. Exploratory rows are not production dumps or performance timings.

Reproduce the formal check:

```sh
python3 spec/lean/proposals/bounded-refinement-ordinary-cycle-20261114/check.py \
  --out /tmp/bounded-refinement-ordinary-cycle-proof
```

No project scan was run. Historical reached/completed/accepted-forward
positions remain OWASP **run-11/11/11**, Conductor **run-8/7/7**, and
Stirling-PDF **run-11/10/9**. The new reference reaches **run-31** in the
exploratory execution and has no finite last iteration in the proof.

This replaces the special-pass example for the user's narrowed request.
It identifies an ordinary-code limitation of the current proposal; it
does not authorize a transfer, subsumption, stopping or truncation change.

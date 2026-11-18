# Branching field paths: termination investigation

17 November 2026. Synthetic reachability. Production baseline:
`966a40c3647268cc006e5776591d6b68849379d0`. Production is unchanged.
[Selected R39 proposal](../design/bidirectional-regular-field-goal-service-20261117.md).
[Consolidated approach](../design/bidirectional-demand-termination-approach-20261115.md).

## 1. Findings

A recursive writer and reader can renew the same `ZERO -> DemandTarget`
without a valid exact mark-to-observer path. The writer has a required final
field f. The reader has a different required final field g. A cut removes f
from the writer's known prefix. The reader can then choose g from the unknown
suffix and return MAY on DEMAND. Backward MAY includes the real root marking
point, so its permission and the next forward root seed remain present.
R38 has no NORMAL observation with which to serve this false goal.

This is a cross-run recurrence. Every measured within-run worklist reaches
its fixed point. It is not an infinitely draining local queue.
The field limits increase; the root Target has no field chain to refine.
The paired FL(Dp)+1 cap can still recreate an unknown suffix at each larger
limit. Shorter NORMAL relations do not cover the independent MAY output.

R39 proves that the complete writer/read word languages do not intersect.
It can serve this origin/goal pair as NoRoute, without confirming a finding
or propagating unbounded field evidence. It keeps the current root Target
closure, then omits only the certified root guidance at a later handoff.

| Check | Result and latest run |
| --- | --- |
| Selected-policy cold reference, before R39 | Fixed within every run; root DT at every measured pair through run-7; uncapped operational cycle proved separately |
| Native branching recursion diagnostic | Zero NORMAL findings; root DT through **run-9/POLICY** |
| Unfused native code: one instruction per field/read/copy | Same diagnostic **run-9/POLICY**; R39 adapter natural **run-5** |
| Repaired negative cold reference/native adapter | No finding; natural **run-5** |
| Positive recursive control | NORMAL relation retained; natural **run-7** |
| Two ordinary loops | Already natural **run-5** before R39; preserved at run-5 |
| Mutual recursion control | Already natural **run-3**; preserved at run-3, including its positive finding |
| Same-terminal-chunk/parity negative native controls | Already natural run-3/run-5; preserved. They are proof generalization controls, not new native cycles |
| Existing source-specific nested-loop controls | Earlier natural **run-17** preserved in the combined suite |

## 2. Ordinary code and exact relation

The inputs describe independent finite lists of branch choices. No unresolved
`choose()` method is needed. Node/Choice constructors are empty ordinary code.
Only x receives T, exactly at its root. The observer checks z exactly.

```java
class Node { Node f; Node g; Node h; }
class Choice { Choice next; boolean useH; }
void main(Choice wc, Choice rc) {
    Node x = new Node(); // Marking rule: assign full T at x.$ only.
    Node y = write(x, wc);
    Node z = read(y, rc);
    // Observation rule: CM(z.$, T).
}
Node write(Node p, Choice c) {
    Node b = new Node();
    if (c == null) { b.f = p; return b; }
    Node q = write(p, c.next);
    if (c.useH) b.h = q; else b.g = q;
    return b;
}
Node read(Node p, Choice c) {
    if (c == null) return p.g;
    Node q = c.useH ? p.h : p.g;
    return read(q, c.next);
}
```

Writer words are `{g,h}*·f`. Reader words are `{g,h}*·g`. An exact root
observation requires equality of the two words. They always differ at the
last field. Reading a shorter prefix can return an exact marked descendant;
it cannot make the root marked. No valid NORMAL root witness exists.

The next trace uses the smaller program with only the g recursive branch.
Its stopping depth is still nondeterministic. The full g/h program is checked
by the generic automaton proof and both native instruction variants. Extra
h branches cannot repair the final f/g mismatch.

## 3. Cold trace, selected NE policy

`F=FLOW`, `N/D=NORMAL/DEMAND`, `$=EXACT`, `M=MAY`, `NE=non-empty MAY`.
`ret` means that method's return base. All E/mx are Empty; H is plain.
`[Dc | Dp]` is the entry selector and its original paired exit selector.
A set such as `p.{g.*,gg.*}/F,N` means two facts with base p.
FLOW initials below are conditional method hypotheses, not NORMAL observed
source routes. The listed domains include offers that C2 rejects and offers
from recursive calls. Initials list the complete accepted raw FLOW shapes
in this scalar return-cone reference. No MAY/NE premise is emitted.

ZERO transport uses the existing saved control summaries. The DATA lists
omit unchanged saved ZERO identities. Root ZERO/Target routing is explicit.
Native production still uses MAY at cuts. These are NE reference traces;
the native diagnostic separately validates the root recurrence.

### Run-1: forward, limit 1

```java
// Demand: unrestricted. Submitted Z,N. Initial Z -> Z,N.
void main(Choice wc, Choice rc) {
    Node x = new Node(); // Z -> x.$/T,N.
    Node y = write(x,wc);// y.f.$/T,N; y.g.NE/T,D.
    Node z = read(y,rc); // z.M/T,D.
    // CM(z.$,T): DEMAND witness only.
}
// NORMAL control completion. DEMAND: Z -> DT. No local DATA method result.

// Demand: unrestricted.
// Submitted: p.$/T,N; p.*/F,N from recursive calls.
// Initial: p.*/F -> p.*/F,N.
Node write(Node p, Choice c) {
    Node b = new Node();
    if(c==null){b.f=p;return b;}
    Node q=write(p,c.next); b.g=q; return b;
}
// NORMAL: p.*/F -> ret.f.*/F.
// DEMAND: p.*/F -> ret.g.NE/F.

// Demand: unrestricted.
// Submitted: p.M/F,D; p.f.$/T,N; p.g.NE/T,D.
// Initial: p.*/F -> p.*/F,N.
Node read(Node p, Choice c) {
    if(c==null)return p.g;
    Node q=p.g; return read(q,c.next);
}
// NORMAL: none. DEMAND: p.*/F -> ret.M/F.
```

Handoff: write uses `[ret.g.NE/F | p.*/F]` in backward orientation;
read uses `[ret.M/F | p.*/F]`. Main uses `[Target | Z]`.

### Run-2: backward, limit 1

```java
// Published DEMAND: Z -> DT; source permission for x.$/T is retained.
void main(Choice wc, Choice rc) {
    Node x=new Node();   // Reverse x.M/T,D includes this exact marking point.
    Node y=write(x,wc);  // Reverse: y.g.NE/T,D -> x.M/T,D.
    Node z=read(y,rc);   // Reverse: z.$/T,D -> y.g.$/T,D and y.g.NE/T,D.
    // Reversed observer emits z.$/T,D on reached Z.
}
// Demand [Target|Z]. Submitted Z,N. Initial Z -> Z,N.

// Published NORMAL: none.
// Published DEMAND: ret.g.*/F -> p.M/F.
Node write(Node p, Choice c) {
    Node b=new Node();
    if(c==null){b.f=p;return b;}
    Node q=write(p,c.next); b.g=q; return b;
}
// Demand [ret.g.NE/F | p.*/F].
// Submitted: ret.*/F,N; ret.g.$/T,D; ret.g.NE/T,D.
// Initial: ret.g.*/F -> ret.g.*/F,N.
// The same-head g.$ offer alone cannot satisfy g.NE.

// Published NORMAL: ret.*/F -> p.g.*/F.
// Published DEMAND: ret.*/F -> p.g.NE/F.
Node read(Node p, Choice c) {
    if(c==null)return p.g;
    Node q=p.g; return read(q,c.next);
}
// Demand [ret.M/F | p.*/F].
// Submitted ret.$/F,N and ret.$/T,D. Initial ret.$/F -> ret.$/F,N.
```

The backward NORMAL g relation is a transfer hypothesis. Applied to the
DEMAND caller it stays DEMAND. The forward Root has no NORMAL observation.

### Run-3: forward, limit 2

```java
// Demand root Target/Z. Submitted Z,N. Initial Z -> Z,N.
void main(Choice wc, Choice rc) {
    Node x=new Node();   // Mark permission from run-2: x.$/T,N.
    Node y=write(x,wc);  // y.f.$/T,N; y.g.f.$/T,N; y.g.g.NE/T,D.
    Node z=read(y,rc);   // z.f.$/T,N, and z.M/T,D.
    // Only z.M/T,D can satisfy the exact-root observer; it is DEMAND.
}
// DEMAND: Z -> DT. NORMAL marked descendant is not a root finding.

// Demand [p.M/F | ret.g.*/F].
// Submitted p.$/F,N and p.$/T,N. Initial p.$/F -> p.$/F,N.
Node write(Node p, Choice c) {
    Node b=new Node();
    if(c==null){b.f=p;return b;}
    Node q=write(p,c.next); b.g=q; return b;
}
// New NORMAL: p.*/F -> ret.g.f.*/F. Saved NORMAL ret.f.* remains.
// DEMAND: p.*/F -> ret.g.g.NE/F.

// Demand [p.g.NE/F | ret.*/F].
// Submitted p.{*,f.$,g.*}/F,N; p.{f.$,g.f.$}/T,N; p.g.g.NE/T,D.
// Initials p.{g.*,g.f.$,g.g.*}/F,N (each starts as an identity).
Node read(Node p, Choice c) {
    if(c==null)return p.g;
    Node q=p.g; return read(q,c.next);
}
// New NORMAL: p.g.g.*/F -> ret.*/F. Saved NORMAL p.g.* -> ret.* remains.
// DEMAND: p.g.*/F -> ret.M/F; p.g.g.*/F -> ret.M/F.
```

Saved NORMAL replay also returns z.f.$/T from the precise y.g.f.$/T offer.
That does not cover the independent root-MAY DEMAND result from a coarse
relation. A precise offer can match an already published coarse DEMAND
summary's premise; its independent MAY output does not recover suffix
correlation. New precise summaries therefore do not by themselves erase DT.

### Run-4: backward, limit 3

```java
// Published DEMAND: Z -> DT. The marking permission still exists.
void main(Choice wc, Choice rc) {
    Node x=new Node();
    Node y=write(x,wc); // Reverse g.g.NE or g.g.g.NE -> x.M/T,D.
    Node z=read(y,rc);  // Reverse exact z gives g, gg, ggg exact/NE offers.
    // z.$/T,D is generated from the reversed observer.
}
// Demand [Target|Z]. Submitted Z,N. Initial Z -> Z,N.

// NORMAL: none newly published.
// DEMAND: ret.g.g.*/F -> p.M/F; ret.g.g.g.*/F -> p.M/F.
Node write(Node p, Choice c) {
    Node b=new Node();
    if(c==null){b.f=p;return b;}
    Node q=write(p,c.next); b.g=q; return b;
}
// Demand [ret.gg.NE/F | p.*/F].
// Submitted ret.{g.*,gg.$,gg.*}/F,N;
// ret.{g.$,gg.$,gg.NE,ggg.$,ggg.NE}/T,D.
// Initials ret.{gg.*,ggg.$,ggg.*}/F,N.

// New NORMAL: ret.*/F -> p.g.g.g.*/F; shorter saved NORMALs remain.
// DEMAND: ret.*/F -> p.g.g.NE/F; ret.*/F -> p.g.g.g.NE/F.
Node read(Node p, Choice c) {
    if(c==null)return p.g;
    Node q=p.g; return read(q,c.next);
}
// Demands [ret.M/F | p.g.*/F] and [ret.M/F | p.gg.*/F].
// Submitted ret.$/F,N; ret.$/T,D. Initial ret.$/F -> ret.$/F,N.
```

### Run-5: forward, limit 4; before R39

```java
// Demand root Target/Z. Submitted Z,N. Initial Z -> Z,N.
void main(Choice wc, Choice rc) {
    Node x=new Node();
    Node y=write(x,wc); // N: f, gf, ggf, gggf exact; D: ggg.NE, gggg.NE.
    Node z=read(y,rc);  // N: f, gf, ggf exact; D: root MAY.
    // Exact-root observer still has no NORMAL witness.
}
// DEMAND Z -> DT, as at run-1 and run-3.

// Demands [p.M/F | ret.gg.*/F] and [p.M/F | ret.ggg.*/F].
// Submitted p.$/F,N and p.$/T,N. Initial p.$/F -> p.$/F,N.
Node write(Node p, Choice c) {
    Node b=new Node();
    if(c==null){b.f=p;return b;}
    Node q=write(p,c.next); b.g=q; return b;
}
// New NORMAL: p.* -> ret.ggf.*, p.* -> ret.gggf.* (all F).
// DEMAND: p.* -> ret.ggg.NE and p.* -> ret.gggg.NE (all F).

// Demands [p.gg.NE/F | ret.*/F], [p.ggg.NE/F | ret.*/F].
// Submitted p.{g.*,gf.$,gg.$,gg.*,ggf.$,ggg.*}/F,N;
// p.{f.$,gf.$,ggf.$,gggf.$}/T,N; p.{ggg.NE,gggg.NE}/T,D.
// Initials p.{gg.*,ggg.$,ggg.*,ggf.$,gggf.$,gggg.*}/F,N.
Node read(Node p, Choice c) {
    if(c==null)return p.g;
    Node q=p.g; return read(q,c.next);
}
// New NORMAL p.gggg.*/F -> ret.*/F.
// DEMAND p.{gg.*,ggg.*,gggf.*,gggg.*}/F -> ret.M/F.
```

The `ggg.NE` writer result is a real paired cap at FL 3, although the global
limit is 4. Its raw `gggf` result could fit globally. All summary candidates
still pass ordinary paired intersection. No unrestricted archive is used.

## 4. Uncapped recurrence and repair

Use g^a for a concrete field word, always after a real fact base.
The operational induction keeps these cells at each completed pair:

```text
Forward W entry: [p.M/F | ret.g^a.*/F]
Forward R entry: [p.g^a.NE/F | ret.*/F]
W has a raw EXACT/FLOW probe at p.
Its finite recursive unroll produces g^(a+1).f; the cut gives g^(a+1).NE/D.
At the smallest cold cell the global cut gives that same result; later
the unroll fits globally and the paired C5 cut still removes f.
R has a STAR query at g^a (also reached by its recursive calls).
Its ordinary read and saved opposite NORMAL relation produce root MAY/D.
R publishes p.g^a.* -> ret.M, D; caller application recreates root DT.

Backward R's finite prefix unroll yields g^(a+1).NE/D at its paired cap.
W's STAR query uses the saved NORMAL g^a.f relation in reverse.
The permitted inside match yields p.M/D; the real root marking point matches.
Backward source permission and Z -> DT are renewed.
Projection supplies the next W/R entry rows at a+1.
```

`OperationalCycle.lean` calculates the C5 summaries, applications, reverse
publication and next selectors with the actual scalar operators. The cold
run-1/run-2 fixed points initialize the induction. The normal providers come
from finite pure field unrolls that fit the current caps, or their retained
saved equivalents. Extra branches/qualified rows do not remove their service.
The repeated exact edge is the root ZERO/DT, even when DATA heads advance.
This is a scoped return-cone/least-fixed-point proof; G1–G4 remain native
integration obligations. The run-9 native cutoff is supporting evidence,
not the uncapped proof.

For R39, the complete writer automaton has a base f arc and g/h repeat arcs.
The reader has a base g arc and g/h repeat arcs. Its accepting product pair
is unreachable. The checked finite closed set proves disjointness at every
depth. Clause validation and exact-point word semantics prove that pruning
cannot remove a valid mark-to-observer relation in this supported scope.

The certificate is established at run-1's seal. Run-3 still computes its
full DATA fixed point, but its frozen service set can omit the root DT at
handoff. DATA handoff is preserved. Without that root guide, backward run-4
has no root offer or source permission. Forward run-5 has no new DATA/Target
frontier. The quiet-suffix theorem covers every later pair without a limit.
No NORMAL finding is created by NoRoute service.

## 5. Generalization and negative controls

A last-field rule is insufficient:

```text
writer: {g,h}* · f.h     reader: {g,h}* · g.h  // same last field h
writer: (g.g)* · f       reader: (g.g)* · g.f  // even/odd depth; same long suffixes
```

The finite word product proves both empty. Native versions of these
particular controls already stop naturally (run-3/run-5); do not call them
additional native nontermination counterexamples. The product proof covers
all their word lengths. A matching word, even a long one, prevents NoRoute.
An empty word is a real match. An omitted branch fails clause validation.
An incomplete route slice returns Unknown. A source alias cycle cannot be
represented by a singleton source word; its alias language must be covered
or the query remains Unknown. A true unserved second origin
keeps the whole anonymous Target. Writer instruction order is checked.

Two actual loops use the same word relation, with reversed write order.
The native loop restriction already finishes the negative at run-5. R39
keeps that result and its positive finding, without changing block liveness,
ports or growth gating. The adapter preserves method and scoped DATA
origins through the existing handoff compactor.

## 6. Fresh search and a separate native limitation

The fresh reference checks **9,604** unary regular grammar pairs and **100**
branching pairs. No empty/nonempty mismatch occurs; the largest visited
product has **20 pairs**. Unary comparisons use independent finite word
witnesses up to a product bound. No alphabet-power path enumeration is used.
A second search runs the current cold C2/body/C5/saved-summary model on
**32 paired recursive programs**, with all within-run fixed points checked.
They keep the expected observations and finish naturally through **run-7**.
The longer shared-word reference finishes at **run-13** with its NORMAL
observation. The generic NoRoute safety proof covers all words, separately
from these finite search bounds.

The long native control has a pre-existing discrepancy:

```text
W = (g.g)* · f;  R base = g.g.g.g.g.g.f
The word g.g.g.g.g.g.f is shared (three writer recursive frames).
```

The unfused native baseline and the R39 adapter both naturally stop at
**run-5 with zero NORMAL findings**. NoRoute is false and the adapter performs
**zero handoff rewrites**. The selected-policy reference reaches that NORMAL
relation at run-13. Thus the native loss is not introduced by R39 and does
not meet phase 3's baseline-success condition. It is a separate baseline/
proposal-integration limitation, not a passing positive reachability test.
It remains recorded for implementation validation; this campaign does not
silently change admission or compaction to fix it.

The combined native suite passes **170 tests in 26 classes**, including
expected-broken diagnostics and that explicit unchanged limitation. Older
cleaner, source-specific and loop controls remain included; the older nested
loop control still reaches natural run-17. There is no new project scan.

The constructive proof audit passes **65 new claims**, with **7,468 claims
in 445 source-hash-checked modules** in the cumulative receipt. The transitive
axiom audit permits only `propext` and `Quot.sound`. It accepts no classical
choice, proof hole or external decision shortcut.

No further termination or comparative soundness counterexample is found in
these explicit families after R39. This does not establish universal
convergence, arbitrary code-to-grammar extraction, or whole-native soundness.
Unsupported mixed/two-sided/nonlinear field SCCs, aliases, ND, statics, GROUP,
unknown generators and general cleaner combinations keep their old guidance.

[Lean dossier and reproducible checks](../../spec/lean/proposals/branching-field-cycle-20261117/README.md).
Compiled objects, complete scalar/native captures and hashes stay outside Git
under `branching-field-cycle-20261117/` in the
[external data root](EXTERNAL_DATA.md). Essential data and traces are above.

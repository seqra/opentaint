# Uniform NE coverage: old and new reference traces

14 November 2026. Checked references for the
[proposed approach](../design/bidirectional-normal-uniform-ne-coverage-20261114.md).
Production is unchanged. These are scalar AP models, not project scans.
All cases use FULL marks and empty E/mx in the relevant neutral FLOW lane.

```text
F=FLOW; U=MUST; NE=non-empty MAY; M=MAY; N=NORMAL; D=DEMAND
Z=ZERO; NT=NormalTarget(sinkId); DT=DemandTarget
[Dc ; Dp] is a complete paired incoming row.
Every initial below starts as an identity.
```

## 1. Run-1 and backward run-2 are unchanged

The old method-only and BB traces retain their
[original bootstrap](bidirectional-non-empty-may-acyclic-nontermination-20261113.md).
The bounded local plan keeps the finer field-NE row and supplies:

```text
old choose, incoming forward run-3:
    [p.f.NE/F ; ret.*/F]
    [p.f.NE/F ; ret.f.*/F]
source permission: the real source marks p.f and its descendants.
```

The new ordinary-code case retains its
[run-1/run-2 annotations](bidirectional-bounded-refinement-ordinary-cycle-20261114.md).
The complete run-2 local return packet is:

```text
ret.*/F   -> x.f.NE/F,D
ret.f.*/F -> x.f.NE/F,D
ret.f.*/F -> x.M/F,D
```

For backward run-2, published rows are above `choose`; its boundary facts
are below it:

```java
// Published D: the three rows above. The finer NE stays local even
// when the caller-visible MAY row covers its output region.
static Node choose(Node x, boolean b) {
    if (b) return x.f.f;
    Node t = new Node();
    t.f = x;
    Node y = new Node();
    y.f = t;
    return y;
}
// Demand: [ret.M/F ; x.*/F], [ret.f.NE/F ; x.*/F].
// Submitted at both reverse calls: ret.M/T,D.
// Initials: ret.$/F,N; ret.*/F,N; ret.f.$/F,N; ret.f.*/F,N.
// Source permission comes from the visible MAY result reaching sourceTree.
```

Thus the new method's complete incoming rows for run-3 are:

```text
[x.f.NE/F ; ret.*/F]
[x.f.NE/F ; ret.f.*/F]
[x.M/F    ; ret.f.*/F]
```

Main has `[Target ; Z]` and its ordinary ZERO identity initial in both
cases. No new ZERO seed, backward MUST initial or source permission is added.

## 2. Old method-only case: complete run-3 closure

```java
// Demand [Target ; Z]. Submitted Z,N. Initial Z -> Z,N.
// sourceAtF is permitted by run-2.
void main(boolean b1, boolean b2) {
    Box x = sourceAtF();       // x.f.U/T,N
    Box y = choose(x, b1);     // Normal replies include y.U and y.f.f.U.
                              // Existing N MUST canonicalization keeps y.U.
    Box z = choose(y, b2);     // Original offer y.U/T,N -> z.U/T,N.
    sinkAnywhere(z);          // Z -> NT,N.
}
// Published N terminal: Z -> NT,N. Published D: none.

// Demand: [p.f.NE/F ; ret.*/F], [p.f.NE/F ; ret.f.*/F].
// Call 1 submitted p.f.U/T,N; call 2 submitted p.U/T,N.
// Both admit only p.f.U/F,N. No new raw initial appears at call 2.
Box choose(Box p, boolean b) {
    if (b) return p.f.g;      // p.f.U/F -> ret.U/F,N.
    Box q = new Box();
    q.f = p;                 // p.f.U/F -> ret.f.f.U/F,N.
    return q;                // Retained NORMAL writer covers this duplicate
                              // before the old relative C5 cut.
}
// Accepted N candidates from the reader:
//   p.f.U/F -> ret.U/F,N
//   p.f.U/F -> ret.f.U/F,N
// Existing MUST/MUST canonicalization can keep the broader first row.
// Published D: none. Next demand for choose and main: empty.
```

The second offer produces the same candidate packet and the same final
basis. Replaying the normal basis gives the same actual uniform root.
This is the complete two-call fixed point, not a missing cycle witness.
The finding is NORMAL. The reference finishes **run-3**.

## 3. Old BB case: all inner owners

Main's demand, actuals, initial and normal terminal are exactly as above.
Write the two branch bodies as explicit functions to show their ownership:

```java
// Parent demand and submitted facts: same as method-only choose above.
// Initial: p.f.U/F,N.
Box choose(Box p, boolean b) {
    if (b) return readBB(p);  // readBB supplies ret.U/F,N.
    return writeBB(p);       // Saved NORMAL writer supplies ret.f.f.U/F,N.
}
// Parent N packet: the same two reader candidates as above.
// Parent D: none; existing writer precoverage suppresses its duplicate.

// Demand: [p.f.NE/F ; ret.*/F]. Submitted: p.f.U/F,N.
// Initial: p.f.U/F,N.
Box readBB(Box p) {
    return p.f.g;
}
// Published N: p.f.U/F -> ret.U/F,N. Published D: none.

// Current demand: none. Submitted from parent: p.f.U/F,N.
// Current initial: none; saved NORMAL replay executes first.
Box writeBB(Box p) {
    Box q = new Box();
    q.f = p;
    return q;
}
// Saved N: p.*/F -> ret.f.*/F,N.
// Applied actual: ret.f.f.U/F,N. New D: none.
```

Read block, write block, parent and root have no outgoing DEMAND. The
reference finishes **run-3** with its normal finding. If another analysis
path forces a later backward run, the existing weak reverse-MUST view
remains DEMAND; the new rule is disabled backward.

## 4. New ordinary case: complete run-3 closure

```java
// Demand [Target ; Z]. Submitted Z,N. Initial Z -> Z,N.
// sourceTree is permitted by the actual run-2 source hit.
static void main(boolean b1, boolean b2) {
    Node x = sourceTree();       // x.U/T,N
    Node y = choose(x, b1);      // y.U/T,N; covered N children are canonicalized.
    Node z = choose(y, b2);      // Same original U offer; z.U/T,N.
    sinkTree(z);                // Z -> NT,N. No D actual reaches this sink.
}
// Published N terminal: Z -> NT,N. Published D: none.

// Demand: all three rows from section 1.
// Submitted at both calls: x.U/T,N.
// C2 initials: x.f.U/F,N (first two rows), x.U/F,N (third row).
// No other raw initial is produced by the second offer.
static Node choose(Node x, boolean b) {
    if (b) return x.f.f;         // Both U initials give ret.U/F,N before C5.
    Node t = new Node();
    t.f = x;
    Node y = new Node();
    y.f = t;                    // x.f.U query really cuts ret.f.f.f.U at 2.
    return y;
}
// C5's accepted candidates, BEFORE new coverage:
//   N: x.f.U/F -> ret.U/F,N
//   N: x.f.U/F -> ret.f.U/F,N
//   N: x.U/F   -> ret.f.U/F,N
//   N: x.U/F   -> ret.f.f.U/F,N
//   D: x.f.U/F -> ret.f.NE/F,D
//   D: x.f.U/F -> ret.f.f.NE/F,D
// New coverage removes both D rows using x.f.U/F -> ret.U/F,N.
// Existing N MUST canonicalization may compact the four N candidates further.
// Published D: none. Local refinement demand: none.
```

The global cut still exists in the computed packet. The proof checks that
it is removed by a valid uniform provider, not skipped or relabeled NORMAL.
The first actual reply has a NORMAL uniform root; same-layer actual
canonicalization leaves that root alone. The second C2 offer is therefore
identical to the first. It adds no query or summary. Replaying once more
changes nothing. Choose and main have empty outgoing demand and a NORMAL
finding: natural completion at **run-3**, with no hard limit.

## 5. Warm records, cleaner and wrapper controls

With retained normal double-read and double-write STAR records, old
precoverage can omit the explicit normal U candidates. The warm check
therefore reconstructs only legal U views through their original C5 rows.
Its current published packet is empty, and original actual replay still
returns a NORMAL uniform root through both calls. No raw candidate is
archived and no global cut is used as a NORMAL view.

The cleaner regression has concrete original marks and a protected repair:

```text
backward run-2:
    ret.*/T -> p.M/T,D,protected
    -> matches the actual source at p.f.$/T

forward run-3:
    demand p.M/T; submitted p.f.$/T,N
    C2: p.f.$/T,N plus the existing p.$/FLOW,N prefix probe
    root-only T cleaner preserves p.f.$/T
    published: p.f.$/T -> ret.f.$/T,N
    concrete outgoing demand: empty
```

The FLOW complement excludes T; it does not replace the repair. The new
rule covers neither this concrete original nor its protected membership.

The wrapper regression retains its normal child route:

```text
backward child EXACT -> full NORMAL ret.f.* -> p.h.* reader
forward source p.h.MUST/T,N -> choose ret.f.MUST/T,N
wrap's ordinary k write    -> ret.k.f.MUST/T,N
```

Its run-3 pair `[p.h.MAY/FLOW ; ret.k.STAR/FLOW]` admits the actual uniform
h query and the complete k.f result within limit 2. The normal summary and
its concrete application are checked. No artificial field exclusion is
exported to the caller.

## 6. Validation and limits

Fresh constructive check: **17 modules, 292 audited declarations, 51 new**,
all passing. The source-hashed external receipt is
`normal-uniform-ne-coverage-20261114/proofs-v4/receipt.json`.

The [Lean package](../../spec/lean/proposals/normal-uniform-ne-coverage-20261114/README.md)
checks both complete call closures, every involved BB, arbitrary longer
read suffixes, warm native views, cleaner repair and the wrapper's normal
finding route. The new covered-NE rule is a scoped proposal; native service
correspondence remains required before implementation.

Eleven current native tests passed: 3 FlowSpatialCanonicalizationTest,
5 TaintCanonicalClassesTest and 3 ConductorUniformLateIterationsTest.
These validate the reused mechanisms, including Conductor's **run-4/run-5**
components. They do not implement or test the new NE tail in Kotlin.

No project scan was made. Historical reached/completed/accepted-forward:
OWASP **run-11/11/11**, Conductor **run-8/7/7**, Stirling-PDF **run-11/10/9**.
The new formal and exploratory references naturally finish at **run-3**.

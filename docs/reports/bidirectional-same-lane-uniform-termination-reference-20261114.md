# Same-lane uniform termination: complete reference frontier

14 November 2026. Latest completed reference iteration: **run-3**.
Native component body: **run-3**, not an integrated NE scan. No project rerun.
[Approach](../design/bidirectional-same-lane-uniform-termination-20261114.md)
and [constructive proof package](../../spec/lean/proposals/same-lane-uniform-termination-20261114/README.md).

The old examples remain in the acceptance set. Their complete
[method/BB/ordinary-code traces](bidirectional-uniform-ne-coverage-reference-20261114.md)
are unchanged by the extended predicate; `Acceptance.lean` rechecks their
frontiers and finding routes. This report adds the new protected example
and includes all its return summaries, rather than only the old recurrence
witnesses.

## Notation and analyzed code

`F` = FLOW; `F-T` = FLOW with mark exclusion `{T}`; `U` = MUST (`[any-taint]`);
`M` = MAY; `NE` = non-empty-MAY; `$` = EXACT; `*` = STAR.
`N/D` are layers. `H` means literal non-subsumable protection.
All real field exclusions are empty. Each helper has one physical return
boundary; the `if` branches are not additional analyzable owners.
The two configured APIs have ordinary source/sink rules and no analyzed
bodies. There is no pass rule, static, alias, ND, loop or recursion.

```java
void main(boolean b1, boolean b2) {
    Node x = sourceTreeT();       // Assign T uniformly at x and descendants.
    Node y = choose(x, b1);
    Node z = choose(y, b2);
    sinkTreeT(z);                 // ContainsMark(z.[any], T).
}

Node choose(Node x, boolean b) {
    removeTAtRoot(x);             // Selected T, EXACT reach at x.
    if (b) return x.f.f;
    Node t = new Node(); t.f = x;
    Node y = new Node(); y.f = t;
    return y;
}
```

Use the user-selected cleaner contract: same-head MUST retains its shape
and layer, with the existing H survivor flag. Nonempty known heads are
disjoint from the root cleaner. Root EXACT/T is killed; partial root
STAR/T has the existing protected MAY/DEMAND survivor. Its separate
exact-root false-positive consequence is already documented in the
[cleaner decision](bidirectional-uniform-root-cleaner-nontermination-20261114.md#10-selected-must-preserving-revision).
No further cleaner behavior changes here.

## Run-1, forward, limit 1

```java
// Demand: none (unrestricted first run).
// Submitted: ZERO,N. Initial: ZERO,N.
void main(boolean b1, boolean b2) {
    Node x = sourceTreeT();       // Actual x.U/T,N; saved source stays NORMAL.
    Node y = choose(x, b1);       // Return y.M/T,D,H and y.f.NE/T,D,H.
    Node z = choose(y, b2);       // Same helper initial keys; returns DEMAND.
    sinkTreeT(z);                 // DEMAND witness.
}
// Published terminal: ZERO -> DemandTarget,D.
// No NORMAL sink Target. No escaping DATA result from this void root.

// Demand: none.
// Call 1 submitted x.U/T,N. Call 2 has the DEMAND returned views above.
// Owned initials: x.*/F,N and request answer x.*/T,D.
// Nonexact run-1 request answers remain DEMAND even for an actual MUST.
Node choose(Node x, boolean b) {
    removeTAtRoot(x);             // x.*/F-T,N; x.M/T,D,H.
    if (b) return x.f.f;          // ret.M in both surviving lanes.
    Node t = new Node(); t.f = x;
    Node y = new Node(); y.f = t;  // Two writes; global cut at length 1.
    return y;
}
// Published, complete interface set:
// x.*/F -> ret.M/F-T,D
// x.*/F -> ret.f.NE/F-T,D
// x.*/F -> x.*/F-T,N
// x.*/T -> ret.M/T,D,H
// x.*/T -> ret.f.NE/T,D,H
// x.*/T -> x.M/T,D,H
```

The argument-side `x` rows model the cleaner's input effect. Main does not
use x after call 1 or y after call 2. They are not additional return facts.
Run-2's actual `ret` offer cannot admit those argument-side entry selectors.
No new coverage rule applies at run-1: these originals are STAR, not MUST.

## Run-2, backward, limit 1

Backward annotations follow the requested reverse layout: published
summaries above the function, and submitted facts, initials and demand
below it.

```java
// Published terminal/source permission: ZERO -> DemandTarget,D.
// Reverse source discharge remains DEMAND and gives run-3 permission.
void main(boolean b1, boolean b2) {
    Node x = sourceTreeT();       // Reverse source discharge at this rule.
    Node y = choose(x, b1);       // Receives the backward helper result.
    Node z = choose(y, b2);       // First reverse call: ret.M/T,D.
    sinkTreeT(z);                 // Seeds z.M/T,D.
}
// Submitted: CFG-reached ZERO at exit; initial ZERO through Target guidance.
// Previous forward demand: ZERO -> DemandTarget,D.

// Published, complete active helper set:
// ret.*/F -> x.f.NE/F-T,D
// ret.f.*/F -> x.f.NE/F-T,D
// ret.f.*/F -> x.M/F-T,D
// ret.$/T -> x.f.NE/T,D,H
// ret.*/T -> x.f.NE/T,D,H
// ret.*/T -> x.M/T,D,H
// ret.f.*/T -> x.f.NE/T,D,H
// ret.f.*/T -> x.M/T,D,H
Node choose(Node x, boolean b) {
    removeTAtRoot(x);
    if (b) return x.f.f;          // Reversed read prefixes f twice, with cuts.
    Node t = new Node(); t.f = x;
    Node y = new Node(); y.f = t;  // Reversed writes remove the known f heads.
    return y;
}
// Submitted at the first reverse call: ret.M/T,D.
// The resulting x.M/T,D and x.f.NE/T,D also serve the other reverse call;
// their queries add no additional active key or published row.
// Initials (distinct):
// ret.$/F,N; ret.*/F,N; ret.f.$/F,N; ret.f.*/F,N;
// ret.$/T,D; ret.*/T,D; ret.f.*/T,D.
// Demand pairs (entry ; paired output), reversed from run-1:
// (ret.M/F ; x.*/F), (ret.f.NE/F ; x.*/F),
// (ret.M/T ; x.*/T), (ret.f.NE/T ; x.*/T).
// Argument-side entry demands do not match the ret offers.
```

The proof enumerates all own-row keys, not just `ret.f.*/T`.
`MUST` is not introduced as a backward owned initial.

## Run-3, forward, limit 2

Reverse the eight run-2 summaries to get these eight current demand pairs:

```text
entry          paired output
x.f.NE/F       ret.*/F
x.f.NE/F       ret.f.*/F
x.M/F          ret.f.*/F
x.f.NE/T       ret.$/T
x.f.NE/T       ret.*/T
x.M/T          ret.*/T
x.f.NE/T       ret.f.*/T
x.M/T          ret.f.*/T
```

Only demand guidance clears mx; retained NORMAL providers keep their real
mx. Both concrete and FLOW lanes are evaluated.

```java
// Demand: run-2 Target/ZERO guidance; no invented source permission.
// Submitted and initial: ZERO,N.
void main(boolean b1, boolean b2) {
    Node x = sourceTreeT();       // Actual x.U/T,N.
    Node y = choose(x, b1);       // Complete canonical reply: y.$/T,N,H;
                                 //                           y.U/T,N,H.
    Node z = choose(y, b2);       // Same canonical z.$ and z.U, both NORMAL.
    sinkTreeT(z);                 // NORMAL witness; NormalTarget(id).
}
// Published: ZERO -> NormalTarget(id),N.
// Complete outgoing refinement demand: empty.

// Demand: all eight pairs above.
// Call 1 submitted: x.U/T,N.
// Distinct initials from all its own-row C2 plans:
// x.f.U/F,N; x.U/F,N; x.f.U/T,N; x.U/T,N.
// Call 2 also receives x.$/T,N,H and x.U/T,N,H after argument binding.
// The exact offer additionally admits x.$/F,N and x.$/T,N.
Node choose(Node x, boolean b) {
    removeTAtRoot(x);             // Uniform T starts preserve NORMAL + H.
                                 // Exact root T start is killed.
                                 // FLOW starts exclude T.
    if (b) return x.f.f;          // NORMAL uniform reader.
    Node t = new Node(); t.f = x;
    Node y = new Node(); y.f = t;  // The original global/relative cuts remain.
    return y;
}
// Published, complete final NORMAL interface basis (11 rows):
// x.f.U/F -> ret.U/F-T,N
// x.f.U/F -> ret.f.U/F-T,N
// x.U/F   -> ret.f.U/F-T,N
// x.U/F   -> ret.f.f.U/F-T,N
// x.f.U/T -> ret.$/T,N,H
// x.f.U/T -> ret.U/T,N,H
// x.U/T   -> ret.U/T,N,H
// x.f.U/T -> ret.f.U/T,N,H
// x.U/T   -> ret.f.U/T,N,H
// x.U/T   -> ret.f.f.U/T,N,H
// x.*/F   -> ret.f.f.*/F-T,N      // From the extra exact FLOW start.
// Complete outgoing refinement demand: empty.
```

The cold call-1 packet also computes these five DEMAND rows before
coverage. Each has a NORMAL provider in the same packet:

```text
cut row                                  retained NORMAL provider
x.f.U/F -> ret.f.NE/F-T,D                 x.f.U/F -> ret.U/F-T,N
x.f.U/F -> ret.f.f.NE/F-T,D               x.f.U/F -> ret.f.U/F-T,N
x.f.U/T -> ret.f.NE/T,D,H                 x.f.U/T -> ret.U/T,N,H
x.U/T   -> ret.f.NE/T,D,H                 x.U/T   -> ret.U/T,N,H
x.f.U/T -> ret.f.f.NE/T,D,H               x.f.U/T -> ret.f.U/T,N,H
```

They are computed through their own global cuts and paired C5 before they
are retired. All ten other cold rows are NORMAL. One of them is the root
EXACT/T row; it remains present and its extra second-call probe is included.
Thus the final total is eleven NORMAL rows, not an assumed ten-row basis.

## Delivery and the fixed point

The old queue-empty publication barrier contains the ready NORMAL provider
and its cut candidates. Filter before sending DEMAND callbacks. For one
complete call reply packet, fold returned MUST facts before queueing the
next call. Root MUST retains the NORMAL finding and absorbs its NORMAL
MUST descendants with equal mark/layer/H. Root EXACT remains separate.

This is essential. The model also executes the failure prefix: publishing
`ret.f.f.U/T,N,H` alone makes C2 create an additional STAR/DEMAND query at
the next call. Same-original MUST coverage cannot remove that query's
STAR-original cuts. Waiting until handoff to remove the original cut is
therefore insufficient.

With the proposed packet rule:

```text
cold helper:                  15 candidates -> 10 NORMAL rows
first call canonical actuals: {ret.$/T,N,H; ret.U/T,N,H}
second-call C2/body/C5:        adds one NORMAL FLOW row
complete helper basis:        11 NORMAL rows, 0 DEMAND rows
second call canonical actuals: {ret.$/T,N,H; ret.U/T,N,H}
another complete closure:     same 11-row basis and same actuals
```

`no_later_closure_round_can_recreate_the_cycle(n)` proves the last equality
for every later closure round by constructive induction. The engine has
no next iteration: both helper and root handoffs are empty at run-3. The
proof does not inspect the run-11 cap or erase DemandTarget merely because
a NormalTarget exists. No DemandTarget witness is generated in this closed
run-3 packet.

## Evidence and limits

Fresh checker: **PASS**, **401 constructive declarations in 25 modules**,
**42 new claims**. All earlier example packages are rebuilt, including
long-reader bootstrap, BB composition, exact-cleaner survivor, wrapper
child demand, saved NORMAL views and the historical infinite recurrences.
Source hashes and logs are external:
`same-lane-uniform-termination-20261114/proofs-v3/receipt.json` under the
report-data archive.

Native components: **15 tests passed** (3 new provider-service tests,
3 protected-growth component tests, 9 existing local-relation tests).
They cover native current/saved definite MUST service with H, excluded
mark suppression, DEMAND support, weak reverse behavior and Target
coexistence. They do not install the new NE law or prove full-native
termination. Latest native body component is **run-3**.

No project scans were made. Historical reached/completed/accepted-forward:
OWASP **run-11/11/11**, Conductor **run-8/7/7**, Stirling-PDF
**run-11/10/9**. The earlier failing reference was replayed through
**run-31**; the new reference stops naturally at **run-3**.

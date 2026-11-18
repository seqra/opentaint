# Source-specific Target service: soundness repair

17 November 2026. Synthetic data-flow reachability. Production is unchanged.
Baseline: `966a40c3647268cc006e5776591d6b68849379d0`.
The selected repair is **R38 [REC] [LOOP]**. It strengthens R37's certificate;
it does not change DATA transfer. See the
[consolidated proposal](../design/bidirectional-demand-termination-approach-20261115.md).

## 1. Result and semantic change

R37 used a confirmed observer/report ID as evidence of completed service.
That is insufficient for `term-task.md`'s marking-point/full-mark/observer
contract. Different marking points can have the same full T and report ID.
One can be NORMAL while another still needs refinement.

| Case | Pinned native baseline | R37 handoff adapter | R38 adapter |
| --- | --- | --- | --- |
| Flat branch example below | Deep route NORMAL; natural **run-5** | Deep route absent; natural **run-3** | Same deep route; natural **run-5** |
| Same example, NORMAL root generation followed by four writes | Deep route NORMAL; natural **run-5** | Deep route absent; natural **run-3** | Same deep route; natural **run-5** |
| Actual hierarchical loop control | Deep route NORMAL; natural **run-13** | Deep route absent; natural **run-5** | Same deep route; natural **run-13** |
| Two nested hierarchical loops | Deep route NORMAL; natural **run-17** | Deep route absent; natural **run-5** | Same deep route; natural **run-17** |
| Two marking points in the recursive wrapper | Diagnostic **run-15/POLICY** | Not used as a valid repair | Both routes served; natural **run-9** |
| Earlier single-origin recursive wrapper | Diagnostic **run-15/POLICY** | Natural run-7 | Unique-origin certificate keeps natural **run-7** |

Each positive flat/loop row has **one NORMAL report ID** on both sides.
The missing relation cannot be detected by report count. Native loop ports, including the nested control,
need more steps than the flat/reference component. Do not replace run-13
with the reference component's smaller bound.

**Major proposal change:** retire a root Target only after every possible
marking origin for each relayed observer has a valid retained NORMAL route.
Report identity alone no longer permits retirement. A NORMAL generation
at a marking point alone is insufficient too. All C2, C5, layers, field
limits, aliases, cleaners, saved replay and stopping rules stay unchanged.
The one terminal bit and its late OR upgrades stay as in R37.

## 2. Small ordinary-code counterexample

`M = MAY`, `NE = non-empty MAY`, `N/D = NORMAL/DEMAND`, `Z = ZERO`.
All facts have Empty E/mx and plain H. There is one full T. Marking point A
assigns T exactly at `r.g`; point B assigns T exactly at `x.f.f.f.f`.
The single observer checks `CM(r.M,T)`. Its ID is `o` in both branches.
The three field reads are ordinary code. There are no helper methods,
loops, cleaners, special pass rules or predefined summaries in this case.
Only `main` is an analyzable block. Locals produce no DATA method summaries.

The following traces use the selected NE cuts. The pinned production core
still uses MAY at these cut sites. Its native control reaches the same
NORMAL endpoints and handoff outcomes. This model/production difference is
explicit; it is not counted as a new analyzer fault.

### Run-1: forward, limit 1

```java
// Demand: unrestricted run-1.
// Submitted control: Z, N. Initial: Z -> Z, N.
void main(boolean chooseA) {
    Node r;
    if (chooseA) {
        r = new Node();      // A: assign T only at r.g.$.
        // Z -> r.g.$/T, N.
    } else {
        Node x = new Node();// B: assign T only at x.f.f.f.f.$.
        // Cut: Z -> x.f.NE/T, D.
        Node a = x.f;       // Z -> a.M/T, D.
        Node b = a.f;       // Z -> b.M/T, D.
        r = b.f;            // Z -> r.M/T, D.
    }
    // Observer CM(r.M,T): A gives N; B gives D.
}
// Published NORMAL: Z -> NT(o), Z -> Z (control completion).
// Published DEMAND: Z -> DT. DATA method summaries: none.
// Handoff keeps Z -> DT. Confirmed IDs now contain o.
```

### Run-2: backward, limit 1

```java
// Published NORMAL control completion may replay; it does not mark B.
// Published DEMAND: Z -> DT. This supplies the next root permission.
// Source permissions include A and B; no new DATA initial is fabricated.
void main(boolean chooseA) {
    Node r;
    if (chooseA) {
        r = new Node();      // r.M/T matches A's r.g.$/T.
    } else {
        Node x = new Node();// x.f.NE/T includes B's f.f.f suffix.
        Node a = x.f;       // Reverse: a.f.NE/T after cut.
        Node b = a.f;       // Reverse: b.f.M/T.
        r = b.f;            // Reverse: r.M/T -> b.f.M/T.
    }
    // Reversed observer on reached Z emits r.M/T, D.
}
// Demand from run-1: [entry Target | paired output Z].
// Submitted: backward Z. Initial: Z -> Z, N.
// The marking rules convert matching reverse facts to Z/DT guidance.
```

Native production uses `x.f.M`, rather than `x.f.NE`, at this real cut.
Both contain the required B position. The Lean proof checks NE membership.
Z control and reverse marking permission are separate from DATA queries.
There is no MAY premise initial in this example.

### Run-3: forward, limit 2

```java
// Demand: root Z/Target route from run-2; no DATA entry selectors.
// Submitted Z, N. Initial Z -> Z, N. A and B have marking permission.
void main(boolean chooseA) {
    Node r;
    if (chooseA) {
        r = new Node();      // Z -> r.g.$/T, N.
    } else {
        Node x = new Node();// Z -> x.f.f.NE/T, D.
        Node a = x.f;       // Z -> a.f.NE/T, D.
        Node b = a.f;       // Z -> b.NE/T, D.
        r = b.f;            // Z -> r.M/T, D.
    }
    // Same NT(o) from A. DT from B. B has no NORMAL observed r.f.$/T.
}
// NORMAL: existing Z -> NT(o), plus control completion.
// DEMAND: Z -> DT. No DATA method summary can replace this permission.
// Baseline: keep DT.
// R37: o was already confirmed, so false needs-bit; omit root DT.
// R38: A is served, B is not; true needs-bit; keep root DT.
```

R37 now has no outgoing guidance. It **naturally completes at run-3**.
If a hypothetical later run is forced, it has no root offer or B marking
permission. Saved NORMAL DATA records have no actual offer to which they
can apply. The Lean history theorem proves absence for every later pair,
not only until an iteration cutoff.

### Run-4: backward, limit 3; baseline and repair only

```java
// DEMAND publication: Z -> DT, preserving both marking permissions.
// NORMAL control completion stays separate.
void main(boolean chooseA) {
    Node r;
    if (chooseA) {
        r = new Node();      // Reverse r.M/T matches A.
    } else {
        Node x = new Node();// Reverse x.f.f.f.M/T matches B's last f.
        Node a = x.f;       // Reverse a.f.f.M/T.
        Node b = a.f;       // Reverse b.f.M/T.
        r = b.f;            // Reverse r.M/T -> b.f.M/T.
    }
    // Reached Z activates reversed observer: r.M/T, D.
}
// Demand: [Target | Z]. Submitted Z. Initial Z -> Z, N.
```

### Run-5: forward, limit 4; baseline and repair only

```java
// Demand: root Target/Z route; marking permissions A and B.
// Submitted Z, N. Initial Z -> Z, N.
void main(boolean chooseA) {
    Node r;
    if (chooseA) {
        r = new Node();      // Z -> r.g.$/T, N.
    } else {
        Node x = new Node();// Z -> x.f.f.f.f.$/T, N. No cut.
        Node a = x.f;       // Z -> a.f.f.f.$/T, N.
        Node b = a.f;       // Z -> b.f.f.$/T, N.
        r = b.f;            // Z -> r.f.$/T, N. This is B's distinct witness.
    }
    // Both marking points now have a real NORMAL route to this observer.
}
// NORMAL: Z -> NT(o), control completion. DEMAND: none.
// Natural completion at run-5. One report ID, two required origin relations.
```

For the NORMAL-generation variant, replace B with:

```java
Node x = new Node(); // B assigns T at x.$, already NORMAL at run-1.
Node x1 = new Node(); x1.f = x;
Node x2 = new Node(); x2.f = x1;
Node x3 = new Node(); x3.f = x2;
Node x4 = new Node(); x4.f = x3;
Node a = x4.f; Node b = a.f; r = b.f;
```

Each write is ordinary and each real cut still obeys the global cap.
The observed result is D/M at limits 1/2 and N/`r.f.$` at limit 4.
`OriginGrowth.lean` proves these cells. Therefore checking that B has
executed normally is not a substitute for a complete NORMAL route.

## 3. R38 [REC] [LOOP]: source-specific service certificate

A goal is the existing observer ID plus its fixed full-mark/position
predicate. A marking point is its existing method, instruction, action and
position with the full mark. Equal marks do not merge marking points.
Do not add these labels to DATA facts, summaries or equality/hash keys.

For a goal g, construct two **read-only finite query views**:

```text
U: conservative possible-origin graph, including future refinements
N: witnessed NORMAL graph, grounded in actual root offers
Sources: complete marking-point catalogue for the goal's full mark

closedGoal(g) = accountingComplete(U, Sources)
            && every s in Sources with path_U(s,g) has path_N(s,g)
```

`U` cannot be a graph of only this run's bounded processed facts. A cut
must not remove a possible source from U. Use the existing complete resolved
micro-edge/call graph with fields forgotten for a safe base-level upper
view. Ignore kills/conditions if needed. Include every possible mark
assignment/entry generator. Include all resolved call targets and block
ports. Alias, mark-changing, rule or provider cases without a proved upper
map are **Unknown**, not absent. No JVM type reasoning is added.
A point outside a **proved complete** observer cone need not block service.
An unexecuted marking action is not automatically outside that cone.

`N` has actual NORMAL generator activation edges and proved NORMAL transfers
from the same marking point to this observer. A local conditional `p -> NT`
is not a root witness. A prior N fact at the same coordinate, an unrelated
report, a NORMAL source before a later cut, or an ND arm alone is not such
an edge. Cuts/D paths add no N arc. Pure NORMAL FLOW summaries can carry an
already grounded actual source fact through calls/blocks. Apply them with
the native matcher, real E/mx/H, bindings and caps. Use no uncertain inside
result as NORMAL. Mark-changing/conditional GEN, ND, alias or cleaner
results need their own valid witness adapter; otherwise return Unknown.
In particular do not use an accepted coarse cleaner survivor as proof of a
baseline-valid precise route. No new `GroundingSupport` is added to storage.

Both maps are proof obligations: every possible required concrete route
must map to U; every N path must provide a retained valid NORMAL route.
The generic Lean theorem is conditional on these explicit adapter maps.
The flat, root-generator and pure-wrapper controls instantiate them. It is
not a proof that arbitrary native graphs already implement these maps.

```text
atExistingJoinedSeal(goal):                 // before its witness rows are released
    if goal is not supported: return Unknown
    U = borrowCompletePossibleOriginView(goal)
    N = borrowProvedNormalWitnessView(goal) // current/saved bounded states only
    if either view is incomplete: return Unknown
    upper = reverseBFS(U, goal)             // one visited bit per existing node
    normal = reverseBFS(N, goal)
    answer = all source nodes s: s not in upper or s in normal
    discard both visited sets
    return answer ? ClosedGoal : OpenGoal

onForwardStart():
    K = freezePreviouslyProvedClosedGoals() // never current report IDs alone

onLocalDemandTarget(goal):
    offerTargetAsInR37(needs = goal not in K)

atHandoff():
    use R37's original closed-OR-bit test for configured root ZERO/DT only
```

A complete singleton origin catalogue plus a valid root NORMAL witness is
an O(1) fast path: that witness must have the sole origin. This applies to
the earlier recursive example. It is **not** the only supported case.
Two NORMAL origin paths also close the goal. The two-source recursive
native control checks this; merely disabling R37 for multiple sources would
restore its recurring root demand.

The query borrows/recomputes edges from existing bounded state and summary
views; it does not store a second persistent derivation graph. At an owner
seal, child pure FLOW summaries can replace released child bodies. Missing
proof after release means Unknown; do not retain all in-method stores to
force a proof. Keep only the resulting per-goal Closed bit/certificate.
The adapter catalogue must cover future reachable placements under the
frozen prescan/rule set. An incomplete/dynamic catalogue cannot close a goal.
There is no per-source set on a DATA fact, subscription, packet or Target.
There is no new mark token or full suffix archive across calls.

## 4. Why retirement is safe; costs and limits

For each retired root row, R37's OR closure proves that every finite
terminal derivation originates at a goal in K, including recursive/loop
relays. R38 strengthens K: every possible marking point for that goal has
a retained valid NORMAL route for the same full mark and observer. Thus
no missing origin relation depends solely on the omitted root permission.
A mixed unserved/unknown goal sets true and retains the whole anonymous row.
Normal reports remain retained; no new report is confirmed by this rule.
The no-limit proof of the original loss and the fixed history are separate.

Reverse BFS uses one node visit and one incoming-edge visit. With adjacency
views its time is O(V+E+S), temporary space O(V+S), for one goal. The list
reference uses repeated scans; its sound/closed-set theorem proves the
same membership as a validated queue implementation. Many goals can cost
O(G(V+E+S)); cache only proved Closed goals, use the singleton fast path,
and share identical views. This is **extra proof work**, not a measured
performance improvement. Unknown keeps the original frontier. The six
native certificate controls check cycles, unknowns, separate source nodes
and the one-visit bound. Do not eagerly bind all rules for the catalogue.

There are no new DATA starts, summaries, caller subscriptions, path words,
mark sets or field-cap exceptions. Mandatory global, FL(Dc)+1 and FL(Dp)+1
caps stay unchanged. The terminal bit still upgrades at most once per key.
The normal graph cannot consist of arbitrary unbounded compositions or
paths not already justified by bounded native operators. A conservative
upper view or Unknown result can retain a Target indefinitely; this repair
is not a universal termination theorem. One source rule can have many
marking points. A singleton rule count is not a singleton origin catalogue.

## 5. Fresh search, proofs and validation scope

The fresh Lean reference has **7,686** configurations, no mismatch, no
unfinished in-run closure and no unfinished refinement within its stated
bounds:

| Family | Cases | Scope |
| --- | ---: | --- |
| Flat two-point programs | 6,615 | Source words length 0..5; ordinary read word 0..3, write word 0..2; alphabet f/g; same full T/observer; compare each source's exact reachability |
| Loop repeat components | 735 | Source words 0..3, read/write words 0..2; finite closure with a broad AL observer; validate fixed point, keep internal DATA frontier; no claim to reproduce native hierarchical ports |
| Shared direct/mutual recursive wrappers | 336 | One or two wrapper functions; two actual marking offers; pure NORMAL FLOW source-witness queries against shared settled summaries |

Latest natural reference completion is **run-9**. Earlier 11,340 recursive,
2,551,500 cleaner and previous ordinary proof packages remain hash-pinned
and checked. No finite search establishes universal termination. The
additional native loop controls use actual decomposition, C2/C5 and ports
and finish naturally at **run-13** and **run-17** (nested). They are separate
from the 735 reference components. The unchanged recursive diagnostic still reaches run-15/POLICY.

Whole-analyzer adapter/progress obligations G1–G4 remain open. This package
does not add a complete upper/lower adapter for GROUP, ND, arbitrary
mark-changing GEN, aliases, statics or all cleaner/loop/recursion mixtures.
Unknown certificates retain guidance in these cases. No known open case
remains **in the explicitly checked families** after the repair. Do not
turn that statement into a universal no-counterexample claim.

**143 targeted native tests pass.** The checker validates 43 new claims,
7,403 cumulative in 436 hash-pinned modules.

[Proof sources and reproducible checks](../../spec/lean/proposals/mark-origin-soundness-20261117/README.md).
Compiled proofs, searches, native XML and source hashes are outside Git in
`mark-origin-soundness-20261117/` under the
[external data root](EXTERNAL_DATA.md).

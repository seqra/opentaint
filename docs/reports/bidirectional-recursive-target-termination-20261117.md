# Recursive wrappers: recurring Target and confirmed-goal service

**Later correction:** R37's report-ID-only K is insufficient for the
marking-point/full-mark/observer contract. The
[R38 source-specific repair](bidirectional-mark-origin-service-soundness-20261117.md) supersedes that predicate. Its generic
terminal OR proof and this single-origin recursive trace stay valid.
Do not apply this document's original ID-only retirement rule to multiple
unserved marking points. The repaired two-origin native wrapper completes
naturally at run-9; the single-origin case retains natural run-7.


17 November 2026. Synthetic data-flow reachability, FULL marks.
Baseline `966a40c36472`; selected proposal through R36.
Follow [proof-guide.md](../../spec/proof-guide.md).
Production is unchanged. The new rule is **R37 [REC]** in the
[consolidated proposal](../design/bidirectional-demand-termination-approach-20261115.md).

**Result:** a recursive wrapper renews the same root Target demand at every
field limit. Every individual run reaches a finite summary fixed point.
The native diagnostic reaches **run-15/POLICY**, with a NORMAL observation
already retained from **run-3**. The R37 reference and native handoff adapter
finish naturally at **run-7**, retaining that observation. A fresh search of
11,340 direct/mutual-recursion configurations has no further counterexample
in its stated scope; latest natural completion is **run-13**.

The cutoff is not a termination proof. The constructive proof derives the
recurring cut and backward MAY, then proves nonempty root demand for every
uncapped pair. General whole-analyzer proof obligations G1–G4 remain open.

## 1. Code and rules

```java
class Node { Node f; Node g; }

void main(int depth) {
    Node x = new Node(); // Marking rule: assign T only at x.f.g.$.
    Node r = wrap(x, depth);
    // Observation rule: CM(r.[any], T).
}

Node wrap(Node p, int depth) {
    if (depth <= 0) return p;
    Node tmp = wrap(p, depth - 1);
    Node y = new Node();
    y.f = tmp;
    return y;
}
```

There is no CFG loop, cleaner, special pass, unresolved library model or
predefined summary. The only cycle is an ordinary recursive call. The
counterexample does not rely on nonreturning execution: every nonnegative
finite depth has a finite execution and puts the marked point at r.f^depth.f.g.
The integer argument has no T flow. The fixture omits its value calculations
and retains the same branching CFG and field transfers.

Notation: F=FLOW, $=EXACT, *=correlated STAR, M=MAY, NE=non-empty MAY,
N/D=NORMAL/DEMAND, Z=ZERO, DT=anonymous DemandTarget. E and H are empty/plain.
`f^k` means k occurrences of f after a named base; it is never a base.
`[Dc | Dp]` is one paired next-run demand. Every owned initial is an identity.

We show the return cone and all root Target rows. ZERO completion and
unmodified argument-preservation NORMAL identities are also retained;
they cannot consume the recursive return cut. Only eligible NORMAL
records persist across runs. The native engine currently uses MAY for
real cuts; the selected formal contract uses NE. Both admit the broad
observation in this example. They are not claimed to be identical engines.

## 2. Per-run trace before R37

### Run-1, forward, field limit 1

```java
// Demand: none. Submitted: Z,N. Initial: Z -> Z,N.
void main(int depth) {
    Node x = new Node(); // x.f.g.$/T,N is cut to x.f.NE/T,D.
    Node r = wrap(x, depth); // r.f.NE/T,D after bounded call application.
    // CM(r.M,T): Z -> DT,D.
}
// Published: Z -> Z,N; Z -> DT,D. No NormalTarget.
// Handoff includes [Target | Z].

// Demand: none. Submitted: p.f.NE/T,D and control Z.
// Initials: p.*/F -> p.*/F,N; Z -> Z,N.
Node wrap(Node p, int depth) {
    if (depth <= 0) return p; // p.*/F -> ret.*/F,N
    Node tmp = wrap(p, depth - 1);
    Node y = new Node();
    y.f = tmp;             // Each completed recursive frame adds f.
    return y;
}
// Published return relations:
// N0: p.*/F -> ret.*/F,N
// N1: p.*/F -> ret.f.*/F,N
// D1: p.*/F -> ret.f.NE/F,D  (one more frame cuts a real f)
// Handoff for D1: [ret.f.NE/F | p.*/F].
```

Applying D1 to the actual marked input returns a concrete DEMAND result.
The NORMAL identities do not cover it: their correlated suffix is the
input suffix; the cut represents more recursive wrappers.

### Run-2, backward, field limit 1

```java
// Published: Z -> Z,N; Z -> DT,D. Marking permission is retained.
void main(int depth) {
    Node x = new Node(); // Backward x.M/T,D includes the real x.f.g.$/T point.
    Node r = wrap(x, depth);
    // Admitted Target route emits r.M/T,D.
}
// Demand: [Target | Z]. Submitted: reached backward control Z.
// Initial: the existing Target/ZERO control route; no owned MAY initial.

// Published new return-cone relation:
// ret.f.*/F -> p.M/F,D. (Saved N0/N1 supply the NORMAL cases.)
Node wrap(Node p, int depth) {
    if (depth <= 0) return p;
    Node tmp = wrap(p, depth - 1); // saved opposite N1 recreates root MAY
    Node y = new Node();
    y.f = tmp;                  // backward read consumes one known f
    return y;
}
// Demand: [ret.f.NE/F | p.*/F]. Submitted: ret.M/T,D.
// C2 raw initial: ret.f.*/F -> ret.f.*/F,N, with the actual D on its binding.
// Handoff: [p.M/F | ret.f.*/F].
```

In the recursive branch, the known f read changes the initial ret.f.* to
the inner call's ret.* offer. Opposite-direction replay may match that
STAR against saved N1's ret.f.* guard. The result is p.M/F,D. This is the
existing opposite-direction inside rule. R37 does not change it.

### Run-3, forward, field limit 2

```java
// Demand: [Target | Z]. Submitted: Z and real marking permission.
// Initial: Z -> Z,N.
void main(int depth) {
    Node x = new Node(); // x.f.g.$/T,N now fits.
    Node r = wrap(x, depth);
    // N0 gives r.f.g.$/T,N: Z -> NormalTarget(id),N.
    // Recursive cut replies also give Z -> DT,D.
}
// Published: Z -> Z,N; Z -> NormalTarget(id),N; Z -> DT,D.
// Handoff still includes [Target | Z].

// Demand: [p.M/F | ret.f.*/F]. Submitted: p.f.g.$/T,N.
// C2 initials: p.f.*/F -> p.f.*/F,N and p.$/F -> p.$/F,N.
// The second is the existing conditional FLOW prefix probe.
Node wrap(Node p, int depth) {
    if (depth <= 0) return p;
    Node tmp = wrap(p, depth - 1);
    Node y = new Node();
    y.f = tmp;
    return y;
}
// New NORMAL: N2 = p.*/F -> ret.f.f.*/F,N.
// New DEMAND return relations:
// p.*/F   -> ret.f.f.NE/F,D
// p.f.*/F -> ret.f.f.NE/F,D
// Saved N0,N1 remain applicable. No unbounded raw summary is stored.
```

The NORMAL observation is permanent. It does not remove the anonymous DT.
NormalTarget's existing normal-only composition and backward exclusion stay
in force. The next backward run therefore still has a root control seed.

### Run-4, backward, field limit 3

```java
// Published: Z -> Z,N; Z -> DT,D; real marking permission.
void main(int depth) {
    Node x = new Node(); // x.M/T,D still reaches the marking action.
    Node r = wrap(x, depth);
    // The DT route emits r.M/T,D; the saved NormalTarget is ignored backward.
}
// Demand: [Target | Z]. Submitted: backward Z; initial: Target/ZERO route.

// Published DEMAND:
// ret.f.f.*/F -> p.M/F,D
// ret.f.f.*/F -> p.f.M/F,D
Node wrap(Node p, int depth) {
    if (depth <= 0) return p;
    Node tmp = wrap(p, depth - 1);
    Node y = new Node();
    y.f = tmp;
    return y;
}
// Demand pairs: [ret.f.f.NE/F | p.*/F], [ret.f.f.NE/F | p.f.*/F].
// Submitted: ret.M/T,D. Raw initial: ret.f.f.*/F,N (identity).
// The whole actual binding is DEMAND. Existing NORMAL reverse cases are reused.
```

### Run-5, forward, field limit 4

```java
// Demand: [Target | Z]. Submitted: Z plus marking permission.
// Initial: Z -> Z,N. NormalTarget(id) is already retained from run-3.
void main(int depth) {
    Node x = new Node(); // x.f.g.$/T,N
    Node r = wrap(x, depth);
    // The same anonymous Z -> DT,D is emitted again.
}
// Published current Target: Z -> DT,D. Retained report: NormalTarget(id).

// Demands: [p.M/F | ret.f.f.*/F], [p.f.M/F | ret.f.f.*/F].
// Submitted: p.f.g.$/T,N.
// Raw identity initials: p.$/F,N; p.f.*/F,N; p.f.$/F,N; p.f.g.$/F,N.
Node wrap(Node p, int depth) {
    if (depth <= 0) return p;
    Node tmp = wrap(p, depth - 1);
    Node y = new Node();
    y.f = tmp;
    return y;
}
// New NORMAL: N3 = p.*/F -> ret.f.f.f.*/F,N.
// New DEMAND: P -> ret.f.f.f.NE/F,D,
// for P in {p.*/F, p.f.*/F, p.f.g.*/F}.
// C5 cuts the fourth wrapper at FL(Dp)+1=3, although the global limit is 4.
```

The displayed return-cone reference has these exact rows. Native scalar
packing can expose extra typed memberships and argument-preservation rows;
the native diagnostic separately checks the same root DT recurrence.
No proof uses equality of diagnostic batch counts.

## 3. Uncapped proof and the cause

Write `Nk = p.*/F -> ret.f^k.*/F,N`. The base case constructs N0. A completed
recursive frame constructs Nk+1 from Nk. For any cap k, the finite value
fixed point contains N0..Nk and:

```text
Xk = p.*/F -> ret.f^k.NE/F,D.
cut(k, wrap(Xk)) = Xk.
```

Every Nk with k within the cap is reached by a finite number of frames;
one further frame reaches Xk. Thus each individual run terminates.
In restricted forward runs, the admitted point/FLOW probe can reuse these
relations. Paired C5 constructs the next Nk and Xk at its ordinary cap.
An earlier global cut gives the same frontier. There is no cap exception.

The backward witness for every k uses the saved NORMAL Nk+1. The known
field read leaves ret.f^k.* at the inner call. Opposite Nk+1 maps that
ancestor STAR to p.M/F,D. Paired output intersection retains it. Root
binding supplies T, and that MAY includes x.f.g, so real marking permission
and the root DT are regenerated. The longest saved guard has no next ready
child, and the forward structural point probe cannot use STAR delegation.
The owner frontier is FLOW, so the concrete-return completion selector does
not remove it. There is no MUST provider or cleaner in this example.

Let forward run-(2n+1) have cap n+1, with the cold run-1 cap 1. For every n:

```text
forward root demand = backward root demand = {[Target | Z]}.
```

The DATA frontier advances; the **literal root Target does not**. Growing
the NORMAL summary archive by one more wrapper does not finish the goal.
This is not an infinite CFG worklist and not a repeated source permission
invented by the model. The proof derives the cut, saved backward result,
source match and actual marked return; it keeps the current C2/C5 rules.
It is a constructive return-cone/control witness, not a complete formal
implementation of all native scheduling or packed storage.

## 4. R37 [REC]: serve confirmed root goals

At forward-run start freeze K, the IDs of **previously confirmed root
ZERO-to-NormalTarget reports**. A conditional local `P -> NormalTarget(id)`
does not put id in K. A new confirmation in this run is used only in the
next forward run. Reuse the existing report identity; do not create another ID.

DemandTarget stays anonymous. Add one `needsUnconfirmed` bit at its existing
method/block/port/premise key, owned by terminal storage. It is not H, not
an AP fact field, and not part of equality or hashing.

```text
onForwardObservationDemand(row, id):
    offerTarget(row, needs = (id not in K))

onUnknownTargetProducer(row):
    offerTarget(row, needs = true) // backward and old/opaque paths keep fallback

onRelayedTarget(parentRow, childNeeds):
    offerTarget(parentRow, needs = childNeeds)

offerTarget(row, incoming):
    if row is new:
        store row and incoming
        publish the ordinary row with its bit
    else if incoming and storedBit(row) == false:
        storedBit(row) = true
        notify existing Target subscribers of the bit upgrade only
    // Ordinary DATA, rule evaluation and fact queues do not replay.

atCompletedForwardHandoff(rootRow):
    if owner is a configured method root
       and premise == ZERO and conclusion == DemandTarget
       and origin accounting is complete and storedBit(rootRow) == false:
        omit only this redundant root Target guidance row
    else:
        use the existing handoff
```

OR-merge the bit across every real Target derivation and binding. A late
unconfirmed origin must upgrade a row already published as covered. Its
upgrade must cross the same Target subscriptions even though the ordinary
row was deduplicated. Every unrecognized producer is needed/unknown; no
certificate means no removal. Do not retain origin sets, field suffixes or
call histories. The full origin set is only a proof model.
Only accepted Target bindings relay the bit. A metadata upgrade does not
bypass C5, create another admission or revive a rejected Target. Existing
binding lookup may run again; DATA propagation does not.

Do not change current-run Target closure, ND binding, ZERO admission,
NormalTarget composition, source permissions, C2/C5, DATA handoff or the
stopping rule. Do not remove nonroot, nonzero or backward Target rows. Do
not classify an entire method or report as covered from one conditional
NORMAL premise. The same anonymous row can serve another unconfirmed ID;
then its bit is true and the whole row stays.

This is a **semantic handoff change**: it removes continuation for goals
that already have a retained NORMAL report. It does not prove a new report,
accept an unresolved goal, or replace a cut with a NORMAL fact.

### Proof, including recursion and mixed origins

Each actual terminal has a finite derivation from a local observation or
an unknown producer. A recursive dependency graph does not make a finite
published witness an infinite proof. If some reachable origin is not in K,
its local bit is true. Induction over its finite relay path gives a true
bit at the root. Therefore:

```text
root bit false => every represented observation origin is already in K.
origin not in K => root bit true => its Target guidance is kept.
```

Unknown producers behave as an unconfirmed origin. OR is a homomorphism of
origin-set union, so a bit replaces the conceptual set for this predicate
without losing a mixed unconfirmed member. The model includes a finite
executable checker for local seeds and relay closure; production need not
store a second graph. Completed owner queues must establish that invariant,
or use the conservative unknown fallback.

As with the existing Target handoff, whole-program preservation also needs
the AP invariant that every still-needed later observation has retained
current guidance. R37 retains every current unconfirmed Target lineage and
all DATA guidance; it does not establish that broader invariant for the
whole implementation. G1–G4 stay open. The concrete wrapper has one explicit
observation and no latent rule action; its complete required route is traced
and checked. No additional observation can be lost in that example.

### Work and storage

Each Target key is first published once and can upgrade false-to-true once.
Each existing Target subscription receives at most two bit states. Cost is
O(V+E) for V existing terminal keys and E existing Target deliveries, plus
existing report-set lookups. Extra space is one bit per terminal key and
the normal queue entry for an upgrade. No DATA row or source/mark query is
added. No origin-ID product or new suffix evidence crosses a call.
Store the bit in the existing terminal entry or in a bitset by row index.
In the wrapper's covered run all origins have the same known ID, so no
false-to-true upgrade is needed; it adds no extra Target notification.

A frozen snapshot is necessary for this bound. Updating K during the run
would require downward bit changes and invalidation; that is not selected.
Unknown/mixed rows can prevent the optimization, but cannot remove a goal.

## 5. Repaired trace

Run-1 through run-4 stay as above. In run-5, K contains id from run-3. All
DT derivations in this example have that same origin, so the final root bit
is false. The current DT is still processed; only its handoff row is omitted.

```java
// run-5 forward: [Target | Z]; submitted Z and real marking permission;
// initial Z -> Z,N. Frozen K contains id.
void main(int depth) {
    Node x = new Node();
    Node r = wrap(x, depth);
    // The raw Z -> DT,D has needsUnconfirmed=false.
}
// Current Target exists. Root Target handoff: empty. Retained NormalTarget(id).

// run-5 wrap demands/initials are exactly as section 2.
Node wrap(Node p, int depth) {
    if (depth <= 0) return p;
    Node tmp = wrap(p, depth - 1);
    Node y = new Node(); y.f = tmp;
    return y;
}
// N3 and every DATA demand row from section 2 stay in the handoff.
```

Run-6 has no root Target entry guidance. The ordinary ZERO admission emits
no root initial. The void root has no independent DATA entry demand. No
call offer reaches wrap. Existing saved-first replay is unchanged and has
no actual offer to process. Run-6 produces no new demand or marking permission.

```java
// run-6 backward: published root/wrap summaries: none.
void main(int depth) { Node x = new Node(); Node r = wrap(x, depth); }
// Target demand: none. Reached admitted initial: none. Submitted DATA: none.
Node wrap(Node p, int depth) {
    if (depth <= 0) return p;
    Node tmp = wrap(p, depth - 1);
    Node y = new Node(); y.f = tmp; return y;
}
// Stored method DATA demand exists but has no call offer. Initials: none.
```

Run-7 has no root admission or new summaries. The unchanged forward stopping
test sees an empty frontier. NormalTarget(id) remains retained. The
constructive quiet-suffix proof holds for every later index without a limit.
The native adapter changes only the root Target rows in one handoff; it
keeps all native DATA guidance, records and seeds. It uses the known single
origin of this fixture, not a production implementation of bit propagation.

## 6. Fresh search and native controls

| Check | Result | Latest reached run |
|---|---|---|
| Current single recursive wrapper | Repeated root DT; retained NORMAL observation from run-3 | run-15/POLICY |
| R37 root/control reference and native single-origin handoff adapter | Same NORMAL report, no hard limit | natural run-7 |
| Native mutual wrappers, with/without adapter | Earlier natural completion is preserved; adapter is not needed | natural run-5 |
| Native unreachable sibling observation | No report and no coverage certificate | natural run-3 |
| Fresh direct/mutual return-cone reference | 11,340 configurations; no missing/extra observation and no failed per-run fixed point | natural run-13 |
| Combined native suite | 123 tests, zero failures/errors | Older cleaner diagnostic through run-15; earlier cold controls through run-9 |

The fresh family has 36 call graphs: four direct wrapper words and 32
two-owner variants, including with/without the second base case. Words are
f, g, ff and fg; source EXACT paths have length 0..2; observations have
length 0..3 and tails EXACT/MAY/NE. It uses current prepared C2, paired C5,
saved-first replay, R32/R34 and ordinary cuts. Target continuation and
backward marking permission are modeled, not a DATA-only stop test.
Of these cases, 7,560 use configured-shape EXACT/MAY observations; 3,780
use NE region-query components. The NE components test the internal region
contract and do not add a new serialized rule-condition shape.

For these linear wrapper graphs, concrete outputs have prefix C^n, with
one optional base prefix in the mutual case. C is nonempty. EXACT queries
need at most their path length worth of cycles. A broad prefix query either
matches by n<=length(query)+1 or is incompatible with the periodic prefix.
The independent oracle enumerates that finite witness bound; it does not
impose an analyzer iteration limit. The analyzer search treats failure to
stop within its observation window as a failure, not a successful cutoff.

The first search harness incorrectly treated same-head NE as disjoint from
MAY. That dropped a real coarse observation and disabled its backward root
permission. The harness now uses region overlap: NE matches same-head
MAY/NE, but not EXACT. A constructive regression pins that cell. The early
harness losses are not analyzer counterexamples and are not counted as
successful checks. All final sources are hash-pinned before evaluation.

Scope limits: the new recursive search has unary neutral return cones and
one explicit observation per program. It does not integrate arbitrary ND,
aliases, statics, GROUP, recursive cleaners or conditional mark generation.
The generic origin proof covers cyclic Target relays and mixed/unknown
origins; native components check those separately. Earlier cleaner/acyclic
proof scopes remain in the dependency closure. No universal termination or
whole-proposal production result is claimed. No further counterexample is
known in the combined explicitly checked scopes.

**Evidence:** 52 new constructive claims; **7,360 cumulative claims in 431
source-hash-checked modules**. Allowed transitive axioms are only `propext`
and `Quot.sound`. The **123 native tests** include historical expected-broken
controls and proposal adapters. Production code and the hard limit setting
are unchanged.

[Proof package and reproduction](../../spec/lean/proposals/recursive-target-service-20261117/README.md).
[Wrapper fixture and handoff adapter](../../core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/RecursiveWrapperTerminationTest.kt).
[Origin-bit cyclic/mixed/epoch controls](data/bidirectional-experiment-sources-20261118/core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/RecursiveTargetSupportTest.kt).
Compiled proofs, axiom logs, search output and native XML/logs are outside
Git under `recursive-target-service-20261117/` at the
[external data root](EXTERNAL_DATA.md). No new project performance run is claimed.

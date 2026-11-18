# Different-path uniform replies: an acyclic termination counterexample

**Current status:** resolved in the proposed definite native MUST replay
policy. The revised complete cold reference naturally stops at **run-5**,
with its findings and NORMAL records retained. Production is unchanged;
the native capture below still reaches **run-31**. The trace and uncapped
proof below describe the named historical policy before this matching
change. [Current rules, proof and validation](bidirectional-definite-must-replay-20261116.md).


16 November 2026. Synthetic data-flow reachability. FULL marks.
Latest native completed iteration: **run-31**, policy cutoff. Support-only
formal result: **uncapped recurrence from run-6**. Both observations are
NORMAL by **run-5**. Production is unchanged.

This is a counterexample to the support-only revision of the
[consolidated approach](../design/bidirectional-demand-termination-approach-20261115.md),
including its latest identical EXACT/MUST reply support law. Follow
[proof-guide.md](../../spec/proof-guide.md).

## 1. Code and decisive pattern

```java
class Box { Box f; Box g; }

Box make(Box p) {
    Box r = new Box();
    // Rule 0: CM(p.g.MAY, T) => assign U to r.MUST.
    // Rule 1: CM(p.MAY,   T) => assign U to r.f.MUST.
    return r;
}

void root() {
    Box a = new Box(); // Entry marking: a.f.MUST/T, NORMAL.
    Box b = new Box(); // Entry marking: b.MUST/T, NORMAL.
    Box x = make(b);
    Box y = make(a);
    // Observation 0: CM(x.MAY, U).
    // Observation 1: CM(y.MAY, U).
}
```

The comments specify ordinary unary marking and observation rules. They are
not unresolved calls. T and U are distinct full marks. `r.MUST/U` means U
at r and its descendants. `r.f.MUST/U` starts at r.f. The two rules generate
U; neither copies a field suffix from T. They can belong to one top-level
rule family. The entry rules are unconditional generators. Rule 0 and rule 1
have separate unary occurrences, so no ND approximation is involved.

There are two method owners, `root` and `make`. Both CFGs and the call graph
are acyclic. There is no loop, recursion, cleaner, special pass rule, static,
alias operation or external body. Fields f and g differ. All relevant paths
have length at most one.

The retained native records include:

```text
B: p.MUST/T   -> ret.MUST/U,   NORMAL
F: p.f.MUST/T -> ret.f.MUST/U, NORMAL

actual at make(a): p.f.MUST/T, NORMAL
apply saved B:    ret.MUST/U,   DEMAND   // provisional MUST match
apply saved F:    ret.f.MUST/U, NORMAL   // definite match
```

The new support law compares identical concrete values. These outputs have
different paths. The NORMAL child cannot cover the whole DEMAND root, even
if region inclusion were considered. It proves no U at the root or at g.
The NORMAL root reply at the other call, `make(b)`, belongs to a different
call-site/return continuation and cannot supply this call's support.

Both observations already have a NORMAL witness: the second one needs only
U somewhere under y, and y.f supplies it. The additional root DEMAND reply
still emits an anonymous DemandTarget. The selected policy does not cancel
that Target because another witness is NORMAL.

## 2. Notation and trace scope

```text
$ = EXACT; * = STAR; M = MAY; MUST = uniform taint; F = FLOW
N = NORMAL; D = DEMAND; Z = ZERO
DT = DemandTarget; NT(0), NT(1) = the two NormalTarget identities
[Dc | Dp] = next-run entry selector with its original paired output selector
ret = the return position of make; every path starts at a named base
```

All E/mx are empty and all memberships are plain. Limits are `1,1,2,3,...`.
No field is cut, so neither NE nor FL+1 truncation is needed for this cycle.
Raw starts are identities. Concrete STAR starts are D; FLOW companions are
N. A MUST demand selector is projected to MAY by the existing handoff rule.

The annotations below give the entire relevant T-to-U cone. Ordinary ZERO
and unchanged parameter identities carry no new U and are independent of
this cone. They are preserved. Only control summaries can escape the void
root. A persisted NormalTarget is not republished. Its report stays retained.
Saved NORMAL records are applied before the current demand lookup, including
when the current helper demand is empty.

For backward runs, published summaries are above the declaration. Demand,
submitted facts and raw starts are below it. For forward runs, they are above
the declaration and published summaries are below it. No generated inner
block exists in this sample.

## 3. Cold prefix under the latest policy

### Run-1 — forward, limit 1

```java
// Demand: unrestricted run-1.
// Submitted: b.MUST/T,N and a.f.MUST/T,N, projected to p at the calls.
// Emitted relevant initials: p.*/F,N; requested p.*/T,D.
Box make(Box p) {
    Box r = new Box();
    // p.*/T -> r.M/U,D      (unknown read of g for rule 0).
    // p.*/T -> r.f.MUST/U,D (rule 1).
    return r;
}
// Published qualified D rows:
//   p.*/T -> ret.M/U,D
//   p.*/T -> ret.f.MUST/U,D
// The executable root MAY can cover the child. The qualified refinement
// view keeps both heads. No NORMAL U record exists yet.

// Demand: unrestricted run-1. Submitted: Z. Initial: Z -> Z,N.
void root() {
    Box a = new Box(); // Z -> a.f.MUST/T,N
    Box b = new Box(); // Z -> b.MUST/T,N
    Box x = make(b);   // Z -> x.M/U,D
    Box y = make(a);   // Z -> y.M/U,D
    // Both observations have D witnesses.
}
// Published: Z -> DT,D. Reports: none. Backward observation seeds: {0,1}.
```

### Run-2 — backward, limit 1

```java
// Published D summaries (all qualified rows are retained):
//   ret.$/U   -> p.g.M/T,D
//   ret.*/U   -> p.g.M/T,D
//   ret.*/U   -> p.M/T,D
//   ret.f.$/U -> p.g.M/T,D
//   ret.f.$/U -> p.M/T,D
//   ret.f.*/U -> p.g.M/T,D
//   ret.f.*/U -> p.M/T,D
Box make(Box p) {
    Box r = new Box();
    // Reverse rule 0 requires p.g.M/T.
    // Reverse rule 1 requires p.M/T.
    // A root EXACT/U cannot come from r.f; no ret.$ -> p.M row is made.
    return r;
}
// Demand: [ret.M/U | p.*/T], [ret.f.M/U | p.*/T].
// Submitted from the observations: ret.M/U,D at both calls.
// Initials: ret.$/U,D; ret.*/U,D; ret.f.$/U,D; ret.f.*/U,D.
// FLOW companions: ret.*/F,N; ret.f.*/F,N.
// The f-child is prepared from the qualified deeper head, within limit 1.

// Published: Z -> DT,D.
void root() {
    Box a = new Box(); // a.M/T and/or a.f.M/T can reach its marking rule.
    Box b = new Box(); // b.M/T and b.g.M/T can reach its marking rule.
    Box x = make(b);
    Box y = make(a);
    // Reverse observations emit x.M/U,D and y.M/U,D.
}
// Demand: [Target | Z]. Submitted and initial: Z.
// Existing observation seeds: {0,1}.
// Call offers are ret.M/U,D. Source-discharge permissions: {a,b}.
```

### Run-3 — forward, limit 2

```java
// Demand: the reverse of all seven run-2 rows:
//   [p.g.M/T | ret.$/U],   [p.g.M/T | ret.*/U], [p.M/T | ret.*/U],
//   [p.g.M/T | ret.f.$/U], [p.M/T | ret.f.$/U],
//   [p.g.M/T | ret.f.*/U], [p.M/T | ret.f.*/U].
// Submitted: p.MUST/T,N from b; p.f.MUST/T,N from a.
// Initials from b: p.MUST/T,N and p.g.MUST/T,N.
// Initial from a: p.f.*/T,D.
// Its companions: p.f.*/F,N and conditional p.$/F,N.
// No p.g query is admitted from the incomparable p.f actual.
Box make(Box p) {
    Box r = new Box();
    // Uniform p proves rule 0 and rule 1.
    // Uniform p.g also proves both.
    // p.f.* proves only rule 1, with D support.
    return r;
}
// Published NORMAL basis after same-initial MUST canonicalization:
//   p.g.MUST/T -> ret.$/U,N
//   p.g.MUST/T -> ret.MUST/U,N
//   p.MUST/T   -> ret.MUST/U,N
//   p.g.MUST/T -> ret.f.$/U,N
//   p.MUST/T   -> ret.f.$/U,N
// Published D:
//   p.f.*/T -> ret.f.MUST/U,D
//   p.f.*/T -> ret.f.$/U,D
// A same-initial NORMAL root MUST covers its NORMAL child MUST;
// exact members remain. Qualified D output heads remain for run-4.

// Demand: [Target | Z]. Submitted and initial: Z.
// Marking permissions from run-2: {a,b}.
void root() {
    Box a = new Box(); // Z -> a.f.MUST/T,N
    Box b = new Box(); // Z -> b.MUST/T,N
    Box x = make(b);   // x.MUST/U,N; x.f.$/U,N; also x.f.MUST/U,D.
    Box y = make(a);   // y.f.MUST/U,D and y.f.$/U,D.
    // Observation 0 has N and D witnesses; observation 1 still has D.
}
// Published: Z -> NT(0),N; Z -> DT,D.
// Retained reports: {0}. Backward seeds: {0,1}.
```

### Run-4 — backward, limit 3

```java
// Published D:
//   ret.f.$/U -> p.f.M/T,D
//   ret.f.*/U -> p.f.M/T,D
Box make(Box p) {
    Box r = new Box();
    // Rule 0's p.g result is rejected by paired p.f output permission.
    // Rule 1's p.M is selected at p.f, giving p.f.M/T,D.
    return r;
}
// Demand: [ret.f.M/U | p.f.*/T], [ret.f.$/U | p.f.*/T].
// Submitted: ret.M/U,D.
// Initials: ret.f.$/U,D; ret.f.*/U,D; companion ret.f.*/F,N.

// Published: Z -> DT,D. Persisted Z -> NT(0),N is ignored backwards.
void root() {
    Box a = new Box(); // Saved broad and current f requirements renew a.
    Box b = new Box(); // The still-active observation 0 renews b.
    Box x = make(b);
    Box y = make(a);
}
// Demand: [Target | Z]. Submitted and initial: Z.
// Observation seeds: {0,1}; call offers ret.M/U,D.
// Saved NORMAL records are replayed before current demand admission.
// Marking permissions for run-5: {a,b}.
```

### Run-5 — forward, limit 4

```java
// Demand: [p.f.M/T | ret.f.$/U], [p.f.M/T | ret.f.*/U].
// Submitted: p.MUST/T,N and p.f.MUST/T,N.
// Initial: p.f.MUST/T,N; both callers support this same uniform query.
Box make(Box p) {
    Box r = new Box();
    // p.f is incomparable with p.g. Only rule 1 applies.
    return r;
}
// New NORMAL:
//   p.f.MUST/T -> ret.f.$/U,N
//   p.f.MUST/T -> ret.f.MUST/U,N
// New D: none. The five run-3 NORMAL records remain. Total: seven.

// Demand: [Target | Z]. Submitted and initial: Z. Marking permissions: {a,b}.
void root() {
    Box a = new Box(); // Z -> a.f.MUST/T,N
    Box b = new Box(); // Z -> b.MUST/T,N
    Box x = make(b);   // NORMAL x.MUST/U and x.f.$/U.
    Box y = make(a);   // Saved broad: y.MUST/U,D.
                      // Precise: y.f.$/U,N and y.f.MUST/U,N.
    // Both observations now have NORMAL witnesses.
    // The different-path root D member at y still triggers DT.
}
// New summaries: Z -> NT(1),N; Z -> DT,D.
// Retained reports: {0,1}. Only backward seed 1 remains.
```

## 4. Repeating suffix: run-6 onward

### Every backward run 2k, k >= 3

```java
// Published current summaries: none. No make analyzer is required.
Box make(Box p) {
    Box r = new Box();
    return r; // Both marking rules remain configured; no current query runs.
}
// Current make demand: empty. Current initials: none.
// At make(a), saved summaries still see the reverse actual ret.M/U,D.
// The broad native record reverses to p.M/T,D.
// The f record reverses to p.f.M/T,D. Extra g records give p.g.M/T,D.
// After binding back: a.M/T and a.f.M/T reach the marking at a.f.
// a.g.M/T cannot reach that marking and adds no permission.

// Published: Z -> DT,D.
void root() {
    Box a = new Box(); // Its reverse marking discharges the T requirement.
    Box b = new Box(); // No observation-0 seed; no renewed b permission.
    Box x = make(b);
    Box y = make(a);   // Offer ret.M/U,D to saved NORMAL records.
}
// Demand: [Target | Z]. Submitted and initial: Z.
// Observation seed: {1}; reverse observation emits y.M/U,D.
// Accepted reversed generator reaches ZERO; existing ZERO->Target conversion
// emits the root demand summary. Next forward marking permission: {a}.
// Both NORMAL report ids remain retained and are ignored backwards.
```

### Every forward run 2k+1, k >= 3

```java
// Current make demand: empty.
// Original submitted call fact: p.f.MUST/T,N from a.
// Current emitted initials: none. Saved-first replay still runs.
Box make(Box p) {
    Box r = new Box();
    return r; // No current body analysis and no new method summaries.
}
// Retained records: the same seven NORMAL members from run-3 and run-5.
// Actual reply packet at make(a), after latest canonicalization:
//   ret.MUST/U,D; ret.f.$/U,N; ret.f.MUST/U,N.

// Demand: [Target | Z]. Submitted and initial: Z. Marking permission: {a}.
void root() {
    Box a = new Box(); // Z -> a.f.MUST/T,N
    Box b = new Box(); // No fresh T from this rule in the restricted run.
    Box x = make(b);   // No fresh marked offer. NT(0) remains persisted.
    Box y = make(a);   // y.MUST/U,D; y.f.$/U,N; y.f.MUST/U,N.
    // Observation 1 again has a D witness, as well as its retained N witness.
}
// New published summary: Z -> DT,D.
// Both NT summaries are already persisted and are not emitted again.
// Retained reports: {0,1}. Next backward observation seed: {1}.
```

This suffix is not a manually seeded state. The executable cold transition
functions derive it from run-1. Enlarging the field limit changes no path or
matching decision in it.

## 5. Uncapped proof

The [Lean package](../../spec/lean/proposals/different-uniform-reply-cycle-20261116/README.md)
imports the actual latest `DefiniteReplySupport.foldValues` function and the
NE C2/C5 kernels. Its preparation includes qualified heads, retained normal
guards and the dedicated MUST exception. All extra exact and g-guard records
in the trace are retained. Nothing is fixed by silently omitting them.

Let S be the complete relevant state after run-6:

```text
current make demand = empty
NORMAL records       = the seven listed above
root Target demand   = { ZERO -> DemandTarget }
next source permission = {a}
retained reports       = {0,1}
backward observation seeds = {1}
```

The constructive theorems establish:

```text
history(6) = S
forward(r,k,S) = S   for every r != 1 and every field limit k
backward(r,k,S) = S  for every r and every field limit k

therefore, for every n >= 0:
    history(n+6) = S
    outgoing Target demand is nonempty
```

`no_early_stop` also proves that runs 1–5 have nonempty outgoing Target
demand. Thus the ordinary stop condition cannot stop before or within the
recurrence. No iteration limit or timeout appears in this argument.

`actual_packet_is_different_not_identical_support` computes the surviving
packet. `no_normal_root_reply_can_absorb_the_witness` checks the absence of
an actual NORMAL root output. `added_g_guards_cannot_supply_the_f_actual`
checks the additional precise providers. `prepared_children_are_enabled_in_the_cold_run`
checks that bounded f and g preparation was not disabled. Native tests check
the corresponding matcher, reversal and support-filter cells.

The proof has **31 new constructive claims**. The source-hash-checked build
contains **2,331 audited claims in 116 modules**. The only permitted
foundational axioms are `propext` and `Quot.sound`. There are no custom
assumptions, proof holes, classical choice or external decision oracles.
This is a scoped two-owner model with native cell validation, not a formal
bisimulation of the full Kotlin engine.

## 6. Why existing progress rules do not close this case

| Mechanism | Why the repeated witness remains |
|---|---|
| NE and real cuts | No real field is cut; every relevant path fits limit 1 |
| Qualified deeper demand and bounded children | f and g queries are included; they produce the extra records shown above |
| Coarse child routing | The rule is restricted to eligible correlated FLOW reads; this is a concrete mark-changing MUST replay |
| NORMAL FLOW precoverage | The relation generates U from T; there is no corresponding FLOW relation to the fresh result |
| NORMAL MUST covering NE | The surviving output is MUST, not NE; its premise/output marks also differ |
| Same-layer MUST canonicalization | The root output is D and the child output is N, so they are different partitions |
| Identical EXACT/MUST reply support | Root and f outputs have different literal paths; exact f is not uniform root support |
| Extra precise g guards | The actual is p.f.MUST; g and f are incomparable |
| Native NORMAL record retention | No cross-premise mark-changing MUST compactor is selected; the extra g provider does not delete B |
| Empty current helper demand | Saved NORMAL replay runs before demand lookup and still produces the provisional reply |
| Increasing field limit | There is no growing path to refine |
| Existing NORMAL report | The policy preserves independently reached anonymous DemandTarget guidance |

The recurring dependency is:

```text
a.f.MUST/T,N
  -> provisional saved broad MUST premise
  -> y.MUST/U,D
  -> ZERO -> DemandTarget
  -> backward y.M/U,D
  -> saved reversed broad premise becomes a.M/T,D
  -> marking at a.f is eligible again
```

The actual input does not prove rule 0's p.g condition. The provisional
saved read nevertheless creates the broad D output. Its reverse MAY
requirement can be met at f, so the cycle never requires proof of g. The
precise f relation is already known and both observations are already NORMAL.
This is a replay/support cycle, not a field-path enumeration cycle.

No new repair is selected in this report. In particular, the report does not
weaken matching, merge different caller contexts, cancel Targets, remove a
NORMAL native record or introduce a new admission rule.

## 7. Native evidence and reproduction

Revision: `966a40c3647268cc006e5776591d6b68849379d0`, with only an added native
test class for this case. Three tests pass:

1. The actual native matcher plus a test-only adapter for latest support
   absorption retains root MUST/D and f EXACT/MUST/N, in both record orders.
   All seven latest-policy records are supplied. Precise g records reject f.
   Removing only B from this test packet leaves no D reply, which isolates
   the renewing record. The production store still retains B as specified.
2. Native reversed records return MAY/T at their actual root/f input heads.
3. The unchanged production driver completes **run-31**, then stops at the
   finite policy limit. It has two non-provisional findings, a root D Target
   after every run, no helper analyzer from run-6, and only source a renewed
   from run-6. All processed paths have length at most one.

The unchanged driver does not contain the proposed NE/split-C2 policy. Its
retained native U basis has two uniform records. The latest-policy Lean
reference includes all seven extra scalar records from split C2, qualified
heads and bounded preparation. Both show the same stable root demand. The
native finite capture alone is not claimed as a proof for the latest policy.

```bash
python3 spec/lean/proposals/different-uniform-reply-cycle-20261116/check.py \
  --out /tmp/different-uniform-reply-proofs
cd core
./gradlew :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.DifferentUniformReplyCycleTest
```

Bulk receipts, compiler output and native logs are outside the repository at
`/drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/mismatched-reply-search-20261116/`.
All decisive states and classifications are included in this report. No
project benchmark is added. No production semantic change is made.

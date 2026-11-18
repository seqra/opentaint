# Direct MUST replay renews a settled observation

**Current status:** resolved in the proposed definite native MUST replay
policy. The revised complete cold reference naturally stops at **run-5**,
with its findings and NORMAL records retained. Production is unchanged;
the native capture below still reaches **run-31**. The trace and uncapped
proof below describe the named historical policy before this matching
change. [Current rules, proof and validation](bidirectional-definite-must-replay-20261116.md).


15 November 2026. Synthetic data-flow reachability. FULL marks.
Counterexample to the [consolidated approach](../design/bidirectional-demand-termination-approach-20261115.md).
Follow [proof-guide.md](../../spec/proof-guide.md). Production is unchanged.
Native source revision: `966a40c3647268cc006e5776591d6b68849379d0`.

**Latest native run: run-31. It stops at the diagnostic policy ceiling.**
The constructive proof has no ceiling. After run-5, both findings are NORMAL,
the helper has no fresh DATA demand, and the root still emits
`ZERO -> DemandTarget, DEMAND` on every iteration.

**Later proposed resolution:** the consolidated proposal now includes
[exact FULL reply support absorption](../design/bidirectional-demand-termination-approach-20261115.md#definite-full-reply-support).
The checked revised reference naturally stops at **run-7**, retaining both
findings and both NORMAL records. This report and its uncapped proof describe
the previous rule, which remains unchanged in production. The repair is
validated separately; its proof does not replace this regression.

The cause is **direct saved concrete MUST replay on a partial uniform input**.
This is not a field-cut cycle. It needs no loop, recursion, cleaner, special
pass rule, alias, static field or unresolved method body. The producer assigns
an exact full mark. It does not assign an intrinsic MAY value.

## 1. Code and rules

The annotations below are configured marking/observation rules at the shown
code positions. They are not extra AP transfer summaries. All ordinary code
is analyzed. An implementation can attach the rules to empty rule-host calls;
those calls add only ordinary NORMAL ZERO completion.

```java
class Box { Box f; }

Box make(Box p) {
    Box r = new Box();
    // Producer: CM(p.[any], T) => AssignMark(r.$, U).
    return r;
}

void root() {
    Box a = new Box(); a.f = new Box();
    // Producer: AssignMark(a.f.[any-taint], T), NORMAL.
    Box b = new Box();
    // Producer: AssignMark(b.[any-taint], T), NORMAL.

    Box x = make(b);
    Box y = make(a);
    // Observation 0: CM(x.$, U).
    // Observation 1: CM(y.$, U).
}
```

The conditional producer tests T and creates U at a **fixed exact position**.
It copies neither T nor its field suffix. It is an ordinary unary source
predicate with an `AssignMark` action, not a pass rule. Both observations are
valid under the selected rule semantics: a mark exists under each argument.

```text
$ = EXACT; * = correlated STAR; M = MAY; MUST = [any-taint]
N/D = NORMAL/DEMAND; Z = ZERO; DT = anonymous DemandTarget
NT(0), NT(1) = stable NormalTarget report IDs
[Dc | Dp] = current entry selector and its paired output selector
```

All E/mx are empty. All protection memberships are plain. T and U are
different full marks. The largest field chain is f, of length 1. The normal
field-limit schedule is `1,1,2,3,...`; increasing that limit changes no
transfer in the final cycle.
If full keys include a top-level rule coordinate, use one join-rule group
for T and U; their full mark components still differ.

## 2. The two NORMAL records

The two calls eventually establish these native records:

```text
M0: p.MUST/T   -> ret.$/U, N       // learned in run-3
Mf: p.f.MUST/T -> ret.$/U, N       // learned in run-5
```

For the field input, ordinary definite CURRENT application rejects M0:
`p.f.MUST/T` does not establish uniform T over all of p. Direct saved replay
has an additional provisional lane. It accepts the overlapping uniform child,
applies M0 and commits pending demotion after the return actions.

```text
provided: p.f.MUST/T, N

saved M0: provisional match -> ret.$/U, D
saved Mf: definite match    -> ret.$/U, N

complete reply packet: {ret.$/U,N; ret.$/U,D}
```

The output remains EXACT. Pending demotion changes its support; it does not
turn that point into NE or MAY. Packet canonicalization retains the different
layers. The exact observation therefore has both a NORMAL witness and a
DEMAND witness. NormalTarget does not cancel the anonymous DemandTarget.

The native boundaries are
[nativeRecordLanes](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/engine/LocalRelationApplication.kt),
[same-direction replay and pending demotion](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/engine/RunMethodCallServices.kt),
and [reverseRecordLeaf](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/ap/Reference.kt).
The native component test checks the definite/provisional split separately
from the multi-run test.

## 3. Complete annotated phase trace

The following trace lists the producer-to-observation cone. Untouched argument
identity and NORMAL `Z -> Z` completion add no U and do not change any row
below. They use the common call machinery. There are two analyzed owners:
root and make. The rule annotations introduce no extra owner or opaque body.

Each NORMAL record is persisted after its run. A displayed saved effect is
not a fresh summary publication. After run-5, saved NormalTarget IDs are also
retained; duplicate NORMAL terminal summaries are not published again.

### Run-1: forward, field limit 1

```java
// Demand: discovery.
// Submitted: p.MUST/T,N from b; p.f.MUST/T,N from a; Z,N control.
// Initials: Z->Z,N; p.*/FLOW->p.*/FLOW,N;
//           requested p.*/T->p.*/T,D.
Box make(Box p) {
    Box r = new Box();
    // CM(p.M,T) => assign U at r.$.
    return r;
}
// Published DATA: p.*/T -> ret.$/U,D.
// Published NORMAL U relations: none.

// Demand: discovery. Submitted: Z,N. Initial: Z->Z,N.
void root() {
    Box a = new Box(); a.f = new Box(); // a.f.MUST/T,N
    Box b = new Box();                 // b.MUST/T,N
    Box x = make(b);                   // x.$/U,D
    Box y = make(a);                   // y.$/U,D
    // CM(x.$,U); CM(y.$,U).
}
// Published: Z -> DT,D. No NORMAL report.
```

Concrete STAR queries start on DEMAND, including FULL run-1. The source
action generates an exact U result with that support. No field is cut.

### Run-2: backward, field limit 1

```java
// Published: ret.$/U -> p.M/T,D.
Box make(Box p) {
    Box r = new Box();
    // Reverse producer: required r.$/U requires p.M/T.
    return r;
}
// Demand: [ret.$/U | p.*/T].
// Submitted: ret.$/U,N from the reversed exact observations.
// Initial: ret.$/U -> ret.$/U,N.

// Published: Z -> DT,D. Both T producers have backward permission.
void root() {
    Box a = new Box(); a.f = new Box(); // a.M/T,D reaches a.f marking
    Box b = new Box();                 // b.M/T,D reaches b marking
    Box x = make(b);                   // backward x.$/U,N -> b.M/T,D
    Box y = make(a);                   // backward y.$/U,N -> a.M/T,D
    // Exact U observations supply the backward marked facts.
}
// Demand: [Target | Z]. Submitted: Z,N. Initial: Z->Z,N.
```

The source condition is MAY. Its reversed result is MAY/DEMAND even though
the supplied U point is exact and NORMAL. Source hits use the existing
backward ZERO-to-Target conversion. No new control rule is needed.

### Run-3: forward, field limit 2

```java
// Demand: [p.M/T | ret.$/U].
// Submitted: p.MUST/T,N from b; p.f.MUST/T,N from a.
// Initials for b: p.MUST/T -> p.MUST/T,N.
// Initials for a: p.f.*/T -> p.f.*/T,D;
//                p.f.*/FLOW -> p.f.*/FLOW,N;
//                conditional prefix p.$/FLOW -> p.$/FLOW,N.
Box make(Box p) {
    Box r = new Box();
    // CM(p.M,T) => assign U at r.$.
    return r;
}
// Published NORMAL: M0 = p.MUST/T -> ret.$/U,N.
// Published DEMAND: p.f.*/T -> ret.$/U,D.
// FLOW companions create no U.

// Demand: [Target | Z]. Submitted: Z,N. Initial: Z->Z,N.
void root() {
    Box a = new Box(); a.f = new Box(); // a.f.MUST/T,N
    Box b = new Box();                 // b.MUST/T,N
    Box x = make(b);                   // x.$/U,N; a D candidate can coexist
    Box y = make(a);                   // y.$/U,D
    // CM(x.$,U); CM(y.$,U).
}
// New NORMAL publication: Z -> NT(0),N.
// DEMAND publication: Z -> DT,D.
// Persist M0.
```

The first-field policy deliberately emits STAR for the deeper MUST offer.
The NORMAL whole-object record is a real inferred conditional relation.
It is not supplied as a predefined summary.

### Run-4: backward, field limit 3

```java
// Saved read of M0: ret.$/U -> p.M/T,D.
// Fresh published DATA: ret.$/U -> p.f.M/T,D.
Box make(Box p) {
    Box r = new Box();
    // Reverse producer: required r.$/U requires p.M/T.
    return r;
}
// Demand: [ret.$/U | p.f.*/T].
// Submitted: ret.$/U,N. Initial: ret.$/U -> ret.$/U,N.
// C5 selects p.M/T against paired p.f.*/T: p.f.M/T,D.

// Published: Z -> DT,D. Both T producers retain permission.
void root() {
    Box a = new Box(); a.f = new Box(); // backward a.M/T,D
    Box b = new Box();                 // backward b.M/T,D
    Box x = make(b);                   // exact U backward
    Box y = make(a);                   // exact U backward
    // Target guidance admits ZERO; both checks still have seed permission.
}
// Demand: [Target | Z]. Submitted: Z,N. Initial: Z->Z,N.
```

Saved reads run before current demand lookup. The fresh summary uses its own
paired C5 row and advances the field requirement, as specified. This is why
the one-input control terminates; that control alone is not a counterexample.

### Run-5: forward, field limit 4

```java
// Demand: [p.f.M/T | ret.$/U].
// Submitted: p.MUST/T,N from b; p.f.MUST/T,N from a.
// Initial: p.f.MUST/T -> p.f.MUST/T,N for both admitted offers.
// Saved-first M0 reply to a: ret.$/U,D (provisional lane).
Box make(Box p) {
    Box r = new Box();
    // CM(p.M,T) => assign U at r.$.
    return r;
}
// Published NORMAL: Mf = p.f.MUST/T -> ret.$/U,N.
// Fresh published DEMAND DATA: none.
// Persist Mf and retain M0.

// Demand: [Target | Z]. Submitted: Z,N. Initial: Z->Z,N.
void root() {
    Box a = new Box(); a.f = new Box(); // a.f.MUST/T,N
    Box b = new Box();                 // b.MUST/T,N
    Box x = make(b);                   // x.$/U,N
    Box y = make(a);                   // y.$/U,N AND y.$/U,D
    // CM(x.$,U); CM(y.$,U).
}
// New NORMAL publication: Z -> NT(1),N; NT(0) is already retained.
// DEMAND publication: Z -> DT,D.
// Required reports are now {0,1}, both NORMAL.
```

The provisional reply is not withdrawn when Mf supplies a better reply.
The two supports stay separate. There is no fresh helper demand to refine.

### Run-6: backward, field limit 5

```java
// Saved M0 read: ret.$/U -> p.M/T,D.
// Saved Mf read: ret.$/U -> p.f.M/T,D.
// Fresh published summaries: none.
Box make(Box p) {
    Box r = new Box();
    // CM(p.M,T) => assign U at r.$.
    return r;
}
// Current demand: empty.
// Offers at the call: ret.$/U,N.
// Initials: none. The helper body is not analyzed.
// Saved replay still delivers its results before the empty-demand gate.

// Published: Z -> DT,D. The a.f/T producer permission is renewed.
void root() {
    Box a = new Box(); a.f = new Box(); // a.M/T,D reaches the a.f producer
    Box b = new Box();                 // no fresh backward T requirement
    Box x = make(b);                   // settled check 0 has no U seed
    Box y = make(a);                   // saved reverse records only
    // Only check 1 still has a DEMAND witness and seeds exact U.
}
// Demand: [Target | Z]. Submitted: Z,N. Initial: Z->Z,N.
// Saved NormalTarget IDs are ignored backward. They do not remove DT.
```

The existing sink-seed index selects check 1 after run-5. This permission is
separate from the anonymous Target payload. The b producer has no new
backward hit from run-6 onward. Its earlier NORMAL report and M0 remain
retained. Only a.f/T must be produced again; the native test checks this
smaller permission set.

### Every later forward run: run-7, run-9, ...

```java
// Current demand: empty.
// Marked offer: p.f.MUST/T,N from a. The b call has no new marked offer.
// Initials: none. No current summary publication or subscription.
// Saved replies for b: ordinary ZERO completion; no new U.
// Saved replies for a: {ret.$/U,N; ret.$/U,D}.
Box make(Box p) {
    Box r = new Box();
    // CM(p.M,T) => assign U at r.$.
    return r;
}
// Fresh published summaries: none. Saved basis remains {M0,Mf}.

// Demand: [Target | Z]. Submitted: Z,N. Initial: Z->Z,N.
void root() {
    Box a = new Box(); a.f = new Box(); // a.f.MUST/T,N
    Box b = new Box();                 // no new T emission is needed
    Box x = make(b);                   // no new U; NT(0) is already retained
    Box y = make(a);                   // y.$/U,N AND y.$/U,D
    // CM(x.$,U); CM(y.$,U).
}
// Published: Z -> DT,D.
// Retained reports: NT(0), NT(1). Duplicate NORMAL publications are skipped.
```

### Every later backward run: run-8, run-10, ...

```java
// Saved M0 read: ret.$/U -> p.M/T,D.
// Saved Mf read: ret.$/U -> p.f.M/T,D.
// Fresh summaries: none.
Box make(Box p) {
    Box r = new Box();
    // CM(p.M,T) => assign U at r.$.
    return r;
}
// Current demand: empty. Offers: ret.$/U,N.
// Initials: none. The body is not analyzed.

// Published: Z -> DT,D; the a.f/T producer permission stays valid.
void root() {
    Box a = new Box(); a.f = new Box(); // a.M/T,D reaches a.f marking
    Box b = new Box();                 // no fresh T requirement
    Box x = make(b);                   // no backward U seed for check 0
    Box y = make(a);                   // saved reverse reads
    // Check 1's exact U seed is enabled by the existing seed index.
}
// Demand: [Target | Z]. Submitted: Z,N. Initial: Z->Z,N.
// NormalTarget IDs are ignored backward.
```

## 4. Uncapped recurrence proof

The checked steady state after run-6 has:

```text
saved producer/observation-cone records = {M0,Mf}
fresh make DATA demand = empty
root demand = { Z -> DT,D }
fresh producer permissions = { a.f/T }
backward observation seeds = { check 1 }
NORMAL report IDs = {0,1}
```

For any later forward run:

1. Source permission supplies the same NORMAL field-uniform a input.
2. Saved-first M0 replay accepts its provisional lane and emits `y.$/U,D`.
   Empty helper demand cannot prevent this earlier replay.
3. Mf also emits `y.$/U,N`. The complete packet keeps both support layers.
4. The D witness emits `Z -> DT,D`. Its current root pair is `[Target | Z]`,
   so typed C5 admits it. A NORMAL report does not remove it.

For any later backward run:

1. The root Target admits ZERO. The existing seed index enables check 1's
   exact U seed; settled check 0 needs no new seed.
2. The saved reverse-MUST reads produce MAY/T requirements without analyzing
   make. The root MAY requirement reaches the a.f marking position.
3. The accepted reversed producer renews that source permission and emits the
   same root D Target through the existing ZERO conversion.

No step increases a field chain or changes a paired budget. No body query
can remove the saved root record: there is no current helper demand. Existing
handoff compaction does not add a NORMAL-record compactor.

The formal model computes the cold prefix, including C2, companions, raw C5,
output intersection, normalization, cuts, record insertion, both call inputs,
saved-first replies, observations and producer permissions. It then proves:

```text
forall n >= 0:
    history(n+6) = stateAfterRun6
    rootDemand(history(n+6)) = true
    makeDemand(history(n+6)) = empty
    reports(history(n+6)) = {0,1}
```

This is induction over arbitrarily many completed steps, not inference from
the run-31 capture. The root demand edge is the fixed non-progress witness.
It is already present in run-5; run-6 also removes the no-longer-needed b
producer permission.
The model also proves that adding another saved reply cannot retract the
M0 provisional reply. Native tests separately check that both support layers
survive packet storage.

## 5. Why every retained fix leaves this case active

| Mechanism | Why it does not remove the witness |
|---|---|
| NE field cuts | There is no real cut, even at limit 1. The recurring output is EXACT/D. |
| Empty/nonempty MAY admission | Fresh make offers are exact U backward or genuine MUST/T forward. There is no MAY/MAY input renewal in the final state. |
| Bounded children and qualified refinement | They help learn Mf. The final provisional reply occurs before lookup, when make demand is already empty. |
| Prepared-child saved routing | Its supported service is owned correlated FLOW/STAR replay of opposite NORMAL STAR records. This is direct concrete MUST replay on the original offer. |
| E-aware routing | All E are empty. It does not enable the unsupported MUST service. |
| NORMAL precoverage and FLOW-backed T | T->U is mark-changing. There is no pure FLOW relation that generates U at fresh r. |
| NORMAL uniform covers NE | The reply is EXACT, not NE; the record is also mark-changing. |
| Complete reply packet canonicalization | Exact U/N and exact U/D have different support. Same-layer MUST folding does not equate them. |
| Protection handling | All edges are plain. No protected member is needed. |
| EXACT/FLOW keep correction | The raw producer and return have no descendant-keep match. The saved result is a concrete U point. |
| Handoff compaction | It compacts outgoing guidance; it does not remove M0 from the NORMAL native basis. The sole root D Target still needs a retained representative. |
| Persisted NormalTarget suppression | It skips repeated NORMAL reports, while the anonymous D Target remains. |
| Persisted summaries before demand | This is the route that recreates the D witness. The selected order explicitly retains it. |

The older reference model used for the unary FLOW return-cone screens did
not exercise this direct **concrete, mark-changing MUST provisional lane**.
Its successful screens do not prove this lane terminates. The new example
uses the original native rule and record machinery rather than adding a
special MAY operation to that model.

## 6. Validation and limits

- Native latest reached iteration: **run-31**, `POLICY` termination of the
  finite capture. Every completed run retains root D Target guidance.
- Both required findings are NORMAL by **run-5**.
- From **run-6** onward, make has no analyzer: saved replay alone sustains
  the cycle. The test checks that only a.f/T needs a new backward source hit,
  and that no new b/T fact is processed in run-7 or run-9.
- Native tests: the multi-run case, direct provisional/definite comparison,
  reverse-MUST view, and three rejected-candidate controls.
- [Constructive proof package](../../spec/lean/proposals/provisional-must-cycle-20261115/README.md)
  checks **30 theorems** for the finite prefix and arbitrary later recurrence.

The scope is the fully analyzed synthetic unary producer/observation cone.
The native fixture lowers the configured rule into `SourceRuleOccurrence`
and uses ordinary allocation, return, call, request, summary and Target
services. It is not a Java-front-end or project measurement. No production
transfer or rule is patched. No universal whole-analyzer simulation is claimed.
The native core does not yet install the whole consolidated NE proposal.
The formal trace uses its selected C2/C5 policy; the table above checks why
the other proposed fixes cannot alter the direct replay witness.

```bash
python3 spec/lean/proposals/provisional-must-cycle-20261115/check.py \
  --out /tmp/provisional-must-cycle-proofs
cd core
./gradlew :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.ProvisionalMustReplayCycleTest \
  --tests org.opentaint.dataflow.bidi.ConditionalMarkMayCycleTest
```

Bulk search data, native logs and compiled proofs stay outside the repository
under `/drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/termination-search-20261115/`.
The report contains the decisive data and trace directly.

# Uniform saved replay repeats after exact reply absorption

**Current status:** resolved in the proposed definite native MUST replay
policy. The revised complete cold reference naturally stops at **run-5**,
with its findings and NORMAL records retained. Production is unchanged;
the native capture below still reaches **run-31**. The trace and uncapped
proof below describe the named historical policy before this matching
change. [Current rules, proof and validation](bidirectional-definite-must-replay-20261116.md).


16 November 2026. Synthetic data-flow reachability. FULL mode.
Counterexample to the former consolidated policy with exact-only FULL
reply support absorption. [Current consolidated approach](../design/bidirectional-demand-termination-approach-20261115.md).
Follow [proof-guide.md](../../spec/proof-guide.md). Production is unchanged.
Native source revision: `966a40c3647268cc006e5776591d6b68849379d0`.

**Latest native capture: run-31, policy ceiling.** The new constructive
proof has no ceiling. From run-6 onward, the complete relevant state repeats:
both findings are NORMAL, the helper has no DATA demand or body query, and
the root publishes `ZERO -> DemandTarget, DEMAND` on every iteration.

The exact-reply repair is enabled in the formal execution. It removes the
DEMAND exact result as intended. A **DEMAND MUST result** remains and renews
the same observation. No real field cut occurs; every known field path has
length at most 1. This is a saved-replay support cycle, not field growth.

**Later proposed resolution:** [definite FULL reply support](../design/bidirectional-demand-termination-approach-20261115.md#definite-full-reply-support)
extends the same actual-reply law to an identical MUST region, with its real
E. The revised cold reference stops at **run-7**, retaining both findings and
all NORMAL members. The [new proof and validation](bidirectional-definite-reply-support-20261116.md)
are separate. This report and its uncapped proof remain the regression for
the earlier exact-only policy; production remains unchanged.

## 1. Code and ordinary rules

```java
class Box { Box f; }

Box make(Box p) {
    Box r = new Box();
    // Producer: CM(p.[any], T) => AssignMark(r.[any-taint], U).
    return r;
}

void root() {
    Box a = new Box(); a.f = new Box();
    // Producer: AssignMark(a.f.[any-taint], T), NORMAL.
    Box b = new Box();
    // Producer: AssignMark(b.[any-taint], T), NORMAL.

    Box x = make(b);
    Box y = make(a);
    // Observation 0: CM(x.[any], U).
    // Observation 1: CM(y.[any], U).
}
```

The comments are ordinary configured marking/observation rules at those
positions. All allocations, calls, bindings and returns are analyzed. There
is no pass action: the conditional producer tests T and generates a distinct
U at a fixed fresh local, including that local's represented descendants.
It copies no input field suffix. It does not assign intrinsic MAY.
Uniform assignment is an ordinary source action: the existing JVM rule-form
[sourceFact constructor](../../core/opentaint-dataflow-core/opentaint-jvm-dataflow/src/main/kotlin/org/opentaint/dataflow/jvm/bidi/interp/JIRRuleForms.kt)
maps an all-fields target to `Tail.ANY_TAINT`. No new rule shape is assumed.

The program has two method owners and an acyclic call graph. Its CFGs are
straight lines. There is no loop, recursive call, cleaner, alias, static
field, unresolved method model or predefined transfer summary. T and U are
distinct full marks; if keys have a top-level group coordinate, use the same
join-rule group for both. All E/mx are empty and every H is plain.

```text
$ = EXACT       * = correlated STAR       M = MAY
MUST = [any-taint], uniform mark           NE = non-empty MAY
N/D = NORMAL/DEMAND     Z = ZERO     DT = anonymous DemandTarget
NT(0), NT(1) = stable NormalTarget report IDs
[Dc | Dp] = current entry demand and its own paired output selector
```

Untouched argument identities and NORMAL `Z -> Z` completion add no U.
The traces below show the complete producer-to-observation cone; the Lean
model includes its controls and source permissions. No loop-generated owner
is needed. A displayed saved replay is not a fresh summary publication.

## 2. The surviving reply

The latest cold policy infers four **scalar NORMAL members**:

```text
E0: p.MUST/T   -> ret.$/U,N        // run-3
U0: p.MUST/T   -> ret.MUST/U,N     // run-3
Ef: p.f.MUST/T -> ret.$/U,N        // run-5
Uf: p.f.MUST/T -> ret.MUST/U,N     // run-5
```

Packed storage can combine members. Four logical members do not require
four physical records. The exact members arise from the exact branch of
the new C2 policy and paired output restriction. They are included here;
the counterexample does not rely on omitting them.

For the original NORMAL field input, native saved replay yields:

```text
provided: p.f.MUST/T,N

E0 provisional: ret.$/U,D
U0 provisional: ret.MUST/U,D
Ef definite:    ret.$/U,N
Uf definite:    ret.MUST/U,N

after same-layer packet canonicalization and exact FULL absorption:
    ret.$/U,N
    ret.MUST/U,N
    ret.MUST/U,D       // still present
```

Exact absorption deletes the first DEMAND point. Its guard rejects MUST,
so it cannot delete the last line. Same-layer MUST canonicalization keeps
NORMAL and DEMAND separate. The existing NORMAL-uniform/NE rule also cannot
delete it: the result is MUST, not NE, and the relation changes T to U.

Ordinary definite CURRENT application of U0 rejects p.f.MUST/T: this input
does not establish uniform T over all of p. The saved native matcher admits
the overlapping uniform child in its provisional lane. Its pending demotion
commits to DEMAND without changing the output tail from MUST.

The observation sees a NORMAL witness and a DEMAND witness. Target handling
preserves both effects; NormalTarget does not cancel anonymous DemandTarget.
Folding even more exact NORMAL results into the same batch cannot remove
the MUST member. The proof checks that statement for arbitrary extra values.

## 3. Per-iteration annotated code

Field limits are `1,1,2,3,...`. No iteration uses the extra field room.
Raw initials below are identity edges. Backward annotations put published
summaries above each declaration and demand/submitted/initial facts below it.

### Run-1: forward, limit 1

```java
// Demand: discovery.
// Submitted: p.MUST/T,N from b; p.f.MUST/T,N from a; Z,N control.
// Initials: Z->Z,N; p.*/FLOW->p.*/FLOW,N;
//           requested p.*/T->p.*/T,D.
Box make(Box p) {
    Box r = new Box();
    // CM(p.M,T) => assign U uniformly at r.
    return r;
}
// Published DATA: p.*/T -> ret.MUST/U,D.
// No NORMAL U relation.

// Demand: discovery. Submitted: Z,N. Initial: Z->Z,N.
void root() {
    Box a = new Box(); a.f = new Box(); // a.f.MUST/T,N
    Box b = new Box();                 // b.MUST/T,N
    Box x = make(b);                   // x.MUST/U,D
    Box y = make(a);                   // y.MUST/U,D
    // CM(x.M,U); CM(y.M,U).
}
// Published: Z -> DT,D. No NORMAL report.
```

Run-1's concrete STAR query is DEMAND. The conditional producer carries that
support to its uniform U result. Handoff uses the existing uniform-to-MAY
guidance projection: `[ret.M/U | p.*/T]`.

### Run-2: backward, limit 1

```java
// Published:
//   ret.$/U -> p.M/T,D
//   ret.*/U -> p.M/T,D
Box make(Box p) {
    Box r = new Box();
    // Reverse uniform U assignment: require CM(p.M,T).
    return r;
}
// Demand: [ret.M/U | p.*/T].
// Submitted: ret.M/U,D from the reversed nonexact observations.
// Initials: ret.$/U->ret.$/U,D; ret.*/U->ret.*/U,D;
//           ret.*/FLOW->ret.*/FLOW,N companion.
// The FLOW companion generates no T-to-U relation.

// Published: Z -> DT,D. Both T producer permissions are renewed.
void root() {
    Box a = new Box(); a.f = new Box(); // a.M/T,D reaches a.f producer
    Box b = new Box();                 // b.M/T,D reaches b producer
    Box x = make(b);                   // backward x.M/U,D -> b.M/T,D
    Box y = make(a);                   // backward y.M/U,D -> a.M/T,D
    // Reversed observations supply the U requirements.
}
// Demand: [Target | Z]. Submitted: Z,N. Initial: Z->Z,N.
```

Both raw marked initials are legal under the selected MAY split. The reverse
producer emits MAY/T, so both summaries stay DEMAND. Source hits use the
existing backward ZERO-to-Target conversion.

### Run-3: forward, limit 2

```java
// Demand: [p.M/T | ret.$/U] and [p.M/T | ret.*/U].
// Submitted: p.MUST/T,N from b; p.f.MUST/T,N from a.
// Initial for b: p.MUST/T->p.MUST/T,N.
// Initials for a: p.f.*/T->p.f.*/T,D;
//                p.f.*/FLOW->p.f.*/FLOW,N;
//                conditional prefix p.$/FLOW->p.$/FLOW,N.
Box make(Box p) {
    Box r = new Box();
    // CM(p.M,T) => assign U uniformly at r.
    return r;
}
// Published NORMAL: E0 and U0.
// Published DEMAND:
//   p.f.*/T -> ret.$/U,D
//   p.f.*/T -> ret.MUST/U,D
// FLOW companions generate no U. Persist E0 and U0.

// Demand: [Target | Z]. Submitted: Z,N. Initial: Z->Z,N.
void root() {
    Box a = new Box(); a.f = new Box(); // a.f.MUST/T,N
    Box b = new Box();                 // b.MUST/T,N
    Box x = make(b);                   // x.$/U,N; x.MUST/U,N; D may coexist
    Box y = make(a);                   // y.$/U,D; y.MUST/U,D
    // CM(x.M,U); CM(y.M,U).
}
// Published NORMAL: Z -> NT(0),N.
// Published DEMAND: Z -> DT,D.
```

The producer's raw uniform result is intersected separately with each row's
own exit selector: ret.$ selects an exact result, while ret.* retains MUST.
No normalized key or other row's output permission is borrowed.

### Run-4: backward, limit 3

```java
// Saved E0/U0 reads provide p.M/T,D.
// Fresh published summaries:
//   ret.$/U -> p.f.M/T,D
//   ret.*/U -> p.f.M/T,D
Box make(Box p) {
    Box r = new Box();
    // Reverse producer requires p.M/T.
    return r;
}
// Demand: [ret.$/U | p.f.*/T] and [ret.M/U | p.f.*/T].
// Submitted: ret.M/U,D.
// Initials: ret.$/U->ret.$/U,D; ret.*/U->ret.*/U,D;
//           ret.*/FLOW->ret.*/FLOW,N companion.
// C5 selects p.M/T against paired p.f.*/T: p.f.M/T,D.

// Published: Z -> DT,D. Both T producer permissions remain valid.
void root() {
    Box a = new Box(); a.f = new Box(); // backward a.M/T,D
    Box b = new Box();                 // backward b.M/T,D
    Box x = make(b);                   // backward x.M/U,D
    Box y = make(a);                   // backward y.M/U,D
    // Both observations still have backward seed permission.
}
// Demand: [Target | Z]. Submitted: Z,N. Initial: Z->Z,N.
```

Saved U0 uses its native reverse view `ret.*/U -> p.M/T,D`. E0 uses
`ret.$/U -> p.M/T,D`. Neither is a backward MUST initial.

### Run-5: forward, limit 4

```java
// Demand: [p.f.M/T | ret.$/U] and [p.f.M/T | ret.*/U].
// Submitted: p.MUST/T,N from b; p.f.MUST/T,N from a.
// Initial: p.f.MUST/T->p.f.MUST/T,N for both admitted offers.
// Saved U0 replay on a already provides ret.MUST/U,D.
Box make(Box p) {
    Box r = new Box();
    // CM(p.M,T) => assign U uniformly at r.
    return r;
}
// Published NORMAL: Ef and Uf. Retain E0 and U0.
// Fresh DEMAND DATA: none.

// Demand: [Target | Z]. Submitted: Z,N. Initial: Z->Z,N.
void root() {
    Box a = new Box(); a.f = new Box(); // a.f.MUST/T,N
    Box b = new Box();                 // b.MUST/T,N
    Box x = make(b);                   // NORMAL U replies
    Box y = make(a);                   // y.MUST/U,N AND y.MUST/U,D
    // CM(x.M,U); CM(y.M,U).
}
// New NORMAL publication: Z -> NT(1),N. NT(0) remains retained.
// DEMAND publication: Z -> DT,D. Both findings are now NORMAL.
```

Even a complete batch containing both new NORMAL results cannot remove the
DEMAND uniform reply. This counterexample does not depend on a late-reply
race or record enumeration order.

### Run-6: backward, limit 5

```java
// Saved E0/U0 reads: ret U requirement -> p.M/T,D.
// Saved Ef/Uf reads: ret U requirement -> p.f.M/T,D.
// Fresh summaries: none.
Box make(Box p) {
    Box r = new Box();
    // CM(p.M,T) => assign U uniformly at r.
    return r;
}
// Current demand: empty. Submitted at call: ret.M/U,D.
// Emitted initials: none. No make body actor.
// Saved-first replay still applies before the empty-demand gate.

// Published: Z -> DT,D. Only the a.f/T producer permission is renewed.
void root() {
    Box a = new Box(); a.f = new Box(); // backward a.M/T,D reaches producer
    Box b = new Box();                 // no new T requirement
    Box x = make(b);                   // settled observation 0 has no U seed
    Box y = make(a);                   // saved reverse records provide T need
    // Observation 1 still has a DEMAND witness and backward seed permission.
}
// Demand: [Target | Z]. Submitted: Z,N. Initial: Z->Z,N.
```

The seed permission is the existing sink-seed index. No ID is added to the
anonymous DemandTarget. NormalTarget IDs are ignored backward. The normal
whole-object producer record and NT(0) remain cached after b's fresh source
permission ends.

### Every later forward run: run-7, run-9, ...

```java
// Current demand: empty.
// Marked submitted input: p.f.MUST/T,N from a.
// b supplies no new marked input. Initials: none. No body analysis.
// Complete saved batch after exact absorption:
//   ret.$/U,N; ret.MUST/U,N; ret.MUST/U,D.
Box make(Box p) {
    Box r = new Box();
    // CM(p.M,T) => assign U uniformly at r.
    return r;
}
// Fresh summaries: none. Saved E0/U0/Ef/Uf remain unchanged.

// Demand: [Target | Z]. Submitted: Z,N. Initial: Z->Z,N.
void root() {
    Box a = new Box(); a.f = new Box(); // a.f.MUST/T,N
    Box b = new Box();                 // no fresh T
    Box x = make(b);                   // NT(0) already retained
    Box y = make(a);                   // y.MUST/U,N AND y.MUST/U,D
    // CM(x.M,U); CM(y.M,U).
}
// Published: Z -> DT,D.
// Retained NORMAL reports: NT(0), NT(1). Duplicate N publications are skipped.
```

### Every later backward run: run-8, run-10, ...

```java
// Saved reverse reads: p.M/T,D and p.f.M/T,D. No fresh summary.
Box make(Box p) {
    Box r = new Box();
    // CM(p.M,T) => assign U uniformly at r.
    return r;
}
// Demand: empty. Submitted at call: ret.M/U,D.
// Initials: none. The body is not analyzed.

// Published: Z -> DT,D. The a.f/T producer permission remains valid.
void root() {
    Box a = new Box(); a.f = new Box(); // backward a.M/T,D reaches producer
    Box b = new Box();                 // no new T permission
    Box x = make(b);                   // no U seed for observation 0
    Box y = make(a);                   // backward y.M/U,D from observation 1
    // Existing seed index retains observation 1, not observation 0.
}
// Demand: [Target | Z]. Submitted: Z,N. Initial: Z->Z,N.
```

## 4. Uncapped recurrence

Let S be the complete relevant state after run-6:

```text
make current DATA demand = empty
saved scalar NORMAL members = {E0,U0,Ef,Uf}
root outgoing demand = { Z -> DT,D }
fresh producer permission = { a.f/T }
backward observation seed = { observation 1 }
retained NORMAL reports = {0,1}
```

For any later forward run:

1. The valid source permission produces the same NORMAL a.f.MUST/T input.
2. Saved U0 replay supplies U/MUST on DEMAND before demand lookup.
3. Uf also supplies NORMAL U/MUST. The exact filter can remove E0's weak
   exact image using Ef, but it rejects U0's MUST image as ineligible.
4. Observation 1 therefore emits the same anonymous D Target. Its own root
   pair `[Target | Z]` admits it. Reports and saved records are unchanged.

For any later backward run:

1. The root Target admits ZERO and the existing seed index enables the same
   observation 1 requirement.
2. Saved reverse U0/E0/Uf/Ef supply the same MAY/T needs without a body query.
3. The a.f producer accepts that requirement and renews its permission.
   Existing backward ZERO-to-Target conversion emits the same root DT.

Thus the formal model proves, by induction:

```text
for every n >= 0:
    history(n+6) = S
    rootDemand(history(n+6)) = true
    makeDemand(history(n+6)) = empty
    NORMALreports(history(n+6)) = {0,1}
```

It also checks every completed run before S has nonempty continuation.
The stopping rule therefore never observes an empty refinement frontier.
There is no field growth, demand refinement, new summary or changing source
permission after run-6. Increasing the limit cannot change this state.
This proves non-termination without using the run-31 diagnostic ceiling.

## 5. Latest-mechanism audit

| Selected mechanism | Why the counterexample survives |
|---|---|
| NE and FL+1 cuts | No real field cut; ret has path length 0, input paths at most 1 |
| Empty/nonempty MAY split | Included: backward EXACT and STAR initials infer the extra E0/Ef records |
| FLOW companions | Included in C2; they do not generate the distinct U mark |
| Qualified field children | Advance the field query to Uf; no current helper demand remains afterward |
| Saved child routing | Limited to supported correlated FLOW/STAR reads; this is direct concrete MUST replay |
| EXACT/FLOW keep correction | No overwritten descendant or such keep contributes U |
| NORMAL FLOW specialization/backing | T changes to U; no FLOW relation generates this U |
| NORMAL uniform/NE retirement | Surviving result is MUST, not NE; relation is mark-changing |
| Complete same-layer MUST packet fold | Different support layers remain separate |
| Exact FULL reply support absorption | Enabled and removes weak EXACT; explicitly does not cover MUST |
| H/protection handling | Every membership is plain; no cleaner or protection mismatch is needed |
| Handoff compaction | No new NORMAL-record compactor; the sole root D Target retains a representative |
| NORMAL report persistence | Preserves both reports but does not cancel anonymous D Target |
| Saved summaries before current demand | Recreates the D uniform result even when the helper lookup is empty |

## 6. Native correspondence and evidence

The unchanged native core has the earlier MAY-to-STAR admission policy. Its
capture has U0 and Uf but not the selected policy's extra E0/Ef members.
The formal trace includes those exact members and enables exact absorption.
They strengthen the NORMAL basis without removing the D uniform witness.

The native tests independently check:

- Native saved U0 accepts the field input provisionally; Uf accepts it
  definitely. CURRENT U0 rejects that same input.
- Complete native packet canonicalization preserves both U/MUST layers.
  The exact filter is inert on that pair. Adding the extra exact members
  removes only the weak exact point, in either enumeration order.
- The backward native uniform record view is `ret.*/U -> p.M/T,D`.
- The real actor/driver reaches **run-31**, every completed run has root
  D Target, make has no actor from run-6 onward, both final findings are
  NORMAL, and only a.f/T has new backward producer hits from run-6.

The [Lean package](../../spec/lean/proposals/provisional-uniform-cycle-20261116/README.md)
checks **30 new constructive claims**. Its receipt covers **2,210 declarations
in 110 modules**, including source-hash-checked existing dependencies. The
native suite has three new checks plus eleven exact/conditional controls.
The controls retain the previous counterexample and its separate repair.

```bash
python3 spec/lean/proposals/provisional-uniform-cycle-20261116/check.py \
  --out /tmp/provisional-uniform-proofs
cd core
./gradlew :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.ProvisionalUniformReplayCycleTest \
  --tests org.opentaint.dataflow.bidi.ExactSupportAbsorptionNativeTest \
  --tests org.opentaint.dataflow.bidi.ProvisionalMustReplayCycleTest \
  --tests org.opentaint.dataflow.bidi.ConditionalMarkMayCycleTest
```

No production rule, matcher, batching operator or stop policy is changed.
No whole-engine/Java-front-end equivalence or new project result is claimed.
The recurrence is checked for the synthetic producer/observation cone under
the latest selected policy. Native matching and seed cells have separate
tests. Generated logs, JSON and compiled proofs stay outside the repository
under `/drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/termination-search-20261116/`.

**Current status:** historical regression for the exact-only policy. The
consolidated proposal now resolves it through definite actual reply support;
its reference stops at **run-7**. The original run-31 native capture and
uncapped counterexample proof remain unchanged. Production is not patched.

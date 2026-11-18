# A real field hole prevents termination after uniform coverage

16 November 2026. Synthetic data-flow reachability. FULL marks. No loops,
recursion, cleaner, pass rule, unresolved body or intrinsic-MAY assignment.
Production is unchanged. Follow [proof-guide.md](../../spec/proof-guide.md).

**Historical policy:** this report and its proof package retain the
preceding Empty-E admission policy. The [current repair](bidirectional-concrete-query-exclusions-20261116.md)
carries actual E onto same-head concrete STAR starts and their existing
FLOW companions, with the same raw C5 image. The repaired reference naturally
stops at **run-5**, with its NORMAL observation at **run-3**. All old cases
retain their stops, latest **run-15**. Production remains unchanged; the
native diagnostic below still completes **run-31**.

**Historical result:** the preceding [consolidated approach](../design/bidirectional-demand-termination-approach-20261115.md)
had another uncapped counterexample. The checked marked-return/control
reference reaches a two-state cycle at **run-7/run-8**. Every later forward
run retains 52 qualified demand rows; every later backward run retains 58.
The root DemandTarget remains live, even after its NORMAL observation is
retained. The finite native diagnostic completes **run-31** at its policy
limit. That finite result is supporting evidence, not the termination proof.

## 1. Code and rules

```java
class Box { Box f; Box g; Box h; }

// Entry marking rule: assign T to a.f.MUST.
void root(Box a) {
    a.f.g = new Box();
    Box x = make(a);
    Box y = make(x);
    Box z = make(y);
    // Observation rule: CM(z.M,U).
}

Box make(Box p) {
    Box r = new Box();
    // The four marking rules occur here:
    // CM(p.f.g.M,T) => assign U to r.MUST.
    // CM(p.M,T)     => assign U to r.h.MUST.
    // CM(p.f.g.M,U) => assign T to r.MUST.
    // CM(p.M,U)     => assign T to r.h.MUST.
    return r;
}
```

All calls use the same analyzed `make` owner. All marking actions assign a
literal full mark to a fresh result. They do not copy an unknown suffix.
Their configured targets are MUST, never MAY. The allocation and field
replacement have ordinary transfers. The sample uses no special pass rule.
The nested replacement is expressed with the native parallel strong keeps.

Compared with the preceding alternating example, there are two changes in
the **sample**, not the analyzer: the root replaces `a.f.g`, and the child
assignments write `r.h` instead of `r.f`. These are permitted ordinary code
and rule configurations. No new semantic repair is selected here.

## 2. Decisive facts

Notation:

```text
$ = EXACT; * = correlated STAR; M = MAY; NE = non-empty MAY
MUST = uniform taint; N = NORMAL; D = DEMAND
[Dc | Dp] = current entry selector and its original paired output selector
m ranges over T,U; flip(T)=U; flip(U)=T
E is a real field exclusion at the fact's head. H is plain throughout.
```

Run-1 field replacement moves the retained mark to DEMAND and keeps Empty E.
Later forward replacements produce the precise NORMAL fact:

```text
before replacement: a.f.MUST/T,N
replace a.f.g:       a.f.MUST/T {g},N
```

Consider the repeated row `[p.M/T | ret.*/U]` and this submitted input:

```text
submitted:              p.f.MUST/T {g},N
coarse first-field C2:  p.f.*/T,D             // Empty E, as specified.
fine same-head C2:     p.f.MUST/T {g},N       // The real E is retained.
```

The coarse query can meet `CM(p.f.g.M,T)` through its unknown STAR suffix.
It emits `p.f.*/T -> ret.M/U,D`. The precise query cannot meet that condition:
g is excluded. It emits only the other action's NORMAL child result.
After real call application, the caller can therefore have:

```text
ZERO -> x.M/U,D
ZERO -> x.h.MUST/U,N
ZERO -> x.h.$/U,N
```

The child does not cover the whole root-MAY region. NORMAL uniform actual
coverage correctly keeps `x.M/U,D`. In particular, it must not use spatial
overlap as whole-region coverage. A NORMAL mark at x itself is not proved.

The next two calls repeat the coarse route with alternating marks:

```text
a.f.MUST/T {g},N -> x.M/U,D -> y.M/T,D -> z.M/U,D
```

Their independent NORMAL replies stay under h. A mark under h cannot meet
the f.g guard and cannot supply a NORMAL whole-root result. The NORMAL child
observations are real within this data-flow model. They do not cancel the
anonymous DemandTarget produced by the still-present root-MAY fact.

Backward STAR queries intersect the `r.h.MUST` assignments and request the
broad `CM(p.M,m)` operands. They recreate the same root-MAY input rows.
At root, backward MAY survives `a.f.g = new Box()` and reaches the entry
marking rule. Source permission is renewed.

## 3. Exact uncapped recurrence

Let F be the complete frozen reference state after run-7 and B the state
after run-8. These include the qualified demand view, all retained NORMAL
records, actual submissions, admitted current results and control state.
The proof constructs the cold prefix from run-1. It then proves:

```text
forall n >= 0:
    State(2*n+7) = F
    State(2*n+8) = B

F.rows has 52 members; B.rows has 58 members.
F.saved = B.saved; there are 12 retained NORMAL return records.
F.observationActive = true; B.sourceAllowed = true; F.report = true.
```

The two essential row families are:

```text
After every later forward run:
    [ret.M/flip(m) | p.*/m]     // From p.*/m -> ret.M/flip(m),D.

After every later backward run:
    [p.M/m | ret.*/flip(m)]     // From ret.*/flip(m) -> p.M/m,D.
```

For both m values, each family is a member of its complete state at every
corresponding later run. Hence the same nonempty demand repeats at i and
at i+2 for every forward i >= 7. No hard iteration limit is used.

The run number is not hidden behind a finite capture. `Phase.lean` proves
that, after the special first two runs, only direction and field budget
matter. `ParametricRounds.lean` proves the delivery/publication steps for
**every budget n+4**. `Steady.lean` connects those steps to the unbounded
`1,1,2,3,...` schedule. `Recurrence.lean` proves the displayed equalities by
induction over n and proves that no later forward run passes the stop test.

Eight worklist sweeps are not an analysis timeout: each cold result is
checked to be a fixed point of one more complete sweep. The same property
is proved for the parametric steady states. Targets accumulate through all
within-run deliveries; no already-emitted Target is erased by later DATA
normalization.

| Completed run | Direction / field limit | Qualified demand rows | Retained NORMAL return records | Fresh forward DemandTarget | NORMAL observation retained |
|---|---|---:|---:|---|---|
| run-1 | F / 1 | 4 | 0 | yes | no |
| run-2 | B / 1 | 14 | 0 | source permission renewed | no |
| run-3 | F / 2 | 26 | 6 | yes | yes |
| run-4 | B / 3 | 44 | 6 | source permission renewed | yes |
| run-5 | F / 4 | 52 | 12 | yes | yes |
| run-6 | B / 5 | 58 | 12 | source permission renewed | yes |
| run-7 | F / 6 | 52 | 12 | yes | yes |
| run-8 | B / 7 | 58 | 12 | source permission renewed | yes |
| run-(7+2n) | F / (6+2n) | 52 | 12 | yes | yes |
| run-(8+2n) | B / (7+2n) | 58 | 12 | source permission renewed | yes |

Counts refer to this marked-return/control reference, not all engine facts.

## 4. Why the selected repairs do not remove the cycle

- Every real field cut still uses NE. The decisive forward/backward root
  MAY results have FL=0. They are created by a coarse conditional read or
  a reverse marking rule, not a real field cut. A larger limit cannot
  refine their empty concrete path.
- The qualified refinement view retains the fine f.g questions and the
  bounded plan prepares their first fields. They coexist with the base
  STAR starts; they do not cancel them. Fine source queries respect `{g}`.
- Bounded child routing is for the selected correlated FLOW transfer
  class. These fresh T-to-U and U-to-T assignments are outside that class.
- Definite native MUST replay remains enabled. The repeating records have
  STAR premises and are current DEMAND results, not an unsupported saved
  MUST lane. The legitimate NORMAL h replies are kept.
- Both actual uniform coverage and identical EXACT/MUST support remain
  enabled. A NORMAL h result cannot cover root MAY. All flags and full
  marks are compared literally; no protected/plain collapse is used.
- A FLOW provider cannot cover the cross-mark generated relation. The
  input mark and output mark differ. Return r is not an identity on p.
- Reporting the NORMAL h witness does not remove an independent Target.
  The selected stop rule still sees nonempty refinement demand.

The lost progress is thus specific: coarse STAR admission forgets a real
hole while a separate fine query preserves it. The coarse cross-mark MAY
result survives, and reverse broad conditions keep admitting it again.
This report identifies the gap. It does not select a field ban, new input
history, Target cancellation or new repair.

## 5. Per-run annotated trace

Each restricted `make` annotation lists its full current demand rows, all
submitted facts in this reference and all emitted initials, including FLOW
companions. Rows with the same entry are grouped by paired output. The
DEMAND lists are the qualified post-C5 refinement view **before executable
MAY union**, as section 4 of the consolidated proposal requires. Execution
may compact covered child results without deleting their refinement heads.

The root snippets show its relevant control and marked-return cone. Its
unchanged argument/ZERO identities are outside this fragment. They cannot
supply a missing cross-mark root return. On backward runs the root begins
with reached ZERO; its observation rule creates the displayed z.M/U input.
Source permission follows the real replacement and entry marking handler.
NORMAL summaries listed below are newly persisted records, not re-emission
of an already known root NormalTarget. No backwards NORMAL report is emitted.

### Run-1 forward, field limit 1

```java
// Demand: unrestricted
// Submitted: ZERO. Initial: ZERO.
void root(Box a) { // Entry producer assigns T to a.f.MUST.
    a.f.g = new Box();
    // a.f.MUST/T,D, E={}
    Box x = make(a); // x.M/U,D
    Box y = make(x); // y.M/T,D
    Box z = make(y); // z.M/U,D
    // Observe CM(z.M,U): DemandTarget
}
// Summary: ZERO -> DemandTarget,D.
// NORMAL report: none.
```

```java
// Demand rows [entry | paired output]:
//   unrestricted run-1
// Submitted to this shared method:
//   D: p.f.MUST/T, p.M/T
//   D: p.M/U
// Emitted initials:
//   D: p.*/T
//   D: p.*/U
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.M,T) => assign U to r.MUST.
    // CM(p.M,T)     => assign U to r.h.MUST.
    // CM(p.f.g.M,U) => assign T to r.MUST.
    // CM(p.M,U)     => assign T to r.h.MUST.
    return r;
}
// New NORMAL summaries: none
// DEMAND summaries in the qualified refinement view:
//   p.*/T -> D: ret.M/U, ret.h.MUST/U
//   p.*/U -> D: ret.M/T, ret.h.MUST/T
```

### Run-2 backward, field limit 1

```java
// New NORMAL summaries: none
// DEMAND summaries in the qualified refinement view:
//   ret.$/U -> D: p.f.NE/T
//   ret.*/U -> D: p.f.NE/T, p.M/T
//   ret.h.$/U -> D: p.f.NE/T, p.M/T
//   ret.h.*/U -> D: p.f.NE/T, p.M/T
//   ret.$/T -> D: p.f.NE/U
//   ret.*/T -> D: p.f.NE/U, p.M/U
//   ret.h.$/T -> D: p.f.NE/U, p.M/U
//   ret.h.*/T -> D: p.f.NE/U, p.M/U
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.M,T) => assign U to r.MUST.
    // CM(p.M,T)     => assign U to r.h.MUST.
    // CM(p.f.g.M,U) => assign T to r.MUST.
    // CM(p.M,U)     => assign T to r.h.MUST.
    return r;
}
// Demand rows [entry | paired output]:
//   [ret.M/U | p.*/T]
//   [ret.h.M/U | p.*/T]
//   [ret.M/T | p.*/U]
//   [ret.h.M/T | p.*/U]
// Submitted to this shared method:
//   D: ret.M/U
//   D: ret.M/T
// Emitted initials:
//   D: ret.$/U, ret.*/U, ret.h.$/U, ret.h.*/U
//   N: ret.*/FLOW, ret.h.*/FLOW
//   D: ret.$/T, ret.*/T, ret.h.$/T, ret.h.*/T
```

```java
// Published summary: ZERO -> DemandTarget,D.
void root(Box a) {
    // Backward source check accepts a.M/T,D and renews permission.
    a.f.g = new Box(); // Backward root MAY survives the replacement.
    Box x = make(a);   // a.M/T,D <- x.M/U,D
    Box y = make(x);   // x.M/U,D <- y.M/T,D
    Box z = make(y);   // y.M/T,D <- z.M/U,D
    // Backward observation emits z.M/U,D from reached ZERO.
}
// Submitted: ZERO at the normal exit. Initial: ZERO.
// Demand control: [Target | ZERO].
```

### Run-3 forward, field limit 2

```java
// Demand: [Target | ZERO]
// Submitted: ZERO. Initial: ZERO.
void root(Box a) { // Entry producer assigns T to a.f.MUST.
    a.f.g = new Box();
    // a.f.MUST/T,N, E={g}
    Box x = make(a); // x.M/U,D; x.h.MUST/U,N and x.h.$/U,N
    Box y = make(x); // y.M/T,D; y.h.MUST/T,N and y.h.$/T,N
    Box z = make(y); // z.M/U,D; z.h.MUST/U,N and z.h.$/U,N
    // Observe CM(z.M,U): DemandTarget and retained NormalTarget(id)
}
// Summary: ZERO -> DemandTarget,D.
// Retain ZERO -> NormalTarget(id),N; emit it once.
```

```java
// Demand rows [entry | paired output]:
//   [p.f.NE/T | ret.$/U, ret.*/U, ret.h.$/U, ret.h.*/U]
//   [p.M/T | ret.*/U, ret.h.$/U, ret.h.*/U]
//   [p.f.NE/U | ret.$/T, ret.*/T, ret.h.$/T, ret.h.*/T]
//   [p.M/U | ret.*/T, ret.h.$/T, ret.h.*/T]
// Submitted to this shared method:
//   N: p.f.MUST/T {g}, p.h.MUST/T, p.h.$/T
//   N: p.h.MUST/U, p.h.$/U
//   D: p.M/U
//   D: p.M/T
// Emitted initials:
//   N: p.f.MUST/T {g}, p.h.$/T
//   D: p.f.*/T, p.$/T, p.*/T, p.f.$/T, p.h.*/T
//   N: p.f.*/FLOW, p.$/FLOW, p.h.*/FLOW, p.*/FLOW
//   D: p.h.*/U, p.f.*/U, p.$/U, p.*/U, p.f.$/U
//   N: p.h.$/U
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.M,T) => assign U to r.MUST.
    // CM(p.M,T)     => assign U to r.h.MUST.
    // CM(p.f.g.M,U) => assign T to r.MUST.
    // CM(p.M,U)     => assign T to r.h.MUST.
    return r;
}
// New NORMAL summaries:
//   p.f.MUST/T {g} -> N: ret.h.MUST/U, ret.h.$/U
//   p.h.$/U -> N: ret.h.MUST/T, ret.h.$/T
//   p.h.$/T -> N: ret.h.MUST/U, ret.h.$/U
// DEMAND summaries in the qualified refinement view:
//   p.f.*/T -> D: ret.M/U, ret.h.MUST/U, ret.h.$/U, ret.h.M/U, ret.$/U
//   p.h.*/U -> D: ret.h.MUST/T, ret.h.$/T
//   p.f.*/U -> D: ret.$/T, ret.M/T, ret.h.MUST/T, ret.h.$/T, ret.h.M/T
//   p.$/U -> D: ret.h.MUST/T, ret.h.$/T
//   p.*/U -> D: ret.M/T, ret.h.MUST/T, ret.h.$/T, ret.h.M/T
//   p.f.$/U -> D: ret.h.MUST/T, ret.h.$/T
//   p.$/T -> D: ret.h.MUST/U, ret.h.$/U
//   p.*/T -> D: ret.M/U, ret.h.MUST/U, ret.h.$/U, ret.h.M/U
//   p.f.$/T -> D: ret.h.MUST/U, ret.h.$/U
//   p.h.*/T -> D: ret.h.MUST/U, ret.h.$/U
```

### Run-4 backward, field limit 3

```java
// New NORMAL summaries: none
// DEMAND summaries in the qualified refinement view:
//   ret.$/U -> D: p.f.g.M/T, p.f.NE/T
//   ret.*/U -> D: p.f.g.M/T, p.f.M/T, p.f.NE/T, p.M/T
//   ret.h.$/U -> D: p.f.g.M/T, p.f.M/T, p.$/T, p.f.NE/T, p.M/T, p.f.$/T, p.h.M/T
//   ret.h.*/U -> D: p.f.g.M/T, p.f.M/T, p.$/T, p.f.NE/T, p.M/T, p.f.$/T, p.h.M/T
//   ret.f.$/T -> D: p.f.g.M/U, p.f.NE/U
//   ret.f.*/T -> D: p.f.g.M/U, p.f.NE/U
//   ret.h.$/T -> D: p.h.M/U, p.f.g.M/U, p.f.M/U, p.$/U, p.f.NE/U, p.M/U, p.f.$/U
//   ret.h.*/T -> D: p.h.M/U, p.f.g.M/U, p.f.M/U, p.$/U, p.f.NE/U, p.M/U, p.f.$/U
//   ret.$/T -> D: p.f.g.M/U, p.f.NE/U
//   ret.*/T -> D: p.f.g.M/U, p.f.M/U, p.f.NE/U, p.M/U
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.M,T) => assign U to r.MUST.
    // CM(p.M,T)     => assign U to r.h.MUST.
    // CM(p.f.g.M,U) => assign T to r.MUST.
    // CM(p.M,U)     => assign T to r.h.MUST.
    return r;
}
// Demand rows [entry | paired output]:
//   [ret.M/U | p.f.*/T, p.*/T]
//   [ret.h.M/U | p.f.*/T, p.$/T, p.*/T, p.f.$/T, p.h.*/T]
//   [ret.h.$/U | p.f.*/T, p.$/T, p.*/T, p.f.$/T, p.h.*/T]
//   [ret.h.M/T | p.h.*/U, p.f.*/U, p.$/U, p.*/U, p.f.$/U]
//   [ret.h.$/T | p.h.*/U, p.f.*/U, p.$/U, p.*/U, p.f.$/U]
//   [ret.$/T | p.f.*/U]
//   [ret.M/T | p.f.*/U, p.*/U]
//   [ret.$/U | p.f.*/T]
// Submitted to this shared method:
//   D: ret.M/U, ret.h.$/U
//   D: ret.f.M/T, ret.h.$/T, ret.M/T
// Emitted initials:
//   D: ret.$/U, ret.*/U, ret.h.$/U, ret.h.*/U
//   N: ret.*/FLOW, ret.h.*/FLOW, ret.f.*/FLOW, ret.$/FLOW
//   D: ret.f.$/T, ret.f.*/T, ret.h.$/T, ret.h.*/T, ret.$/T, ret.*/T
```

```java
// Published summary: ZERO -> DemandTarget,D.
void root(Box a) {
    // Backward source check accepts a.M/T,D and renews permission.
    a.f.g = new Box(); // Backward root MAY survives the replacement.
    Box x = make(a);   // a.M/T,D <- x.M/U,D
    Box y = make(x);   // x.M/U,D <- y.M/T,D
    Box z = make(y);   // y.M/T,D <- z.M/U,D
    // Backward observation emits z.M/U,D from reached ZERO.
}
// Submitted: ZERO at the normal exit. Initial: ZERO.
// Demand control: [Target | ZERO].
```

### Run-5 forward, field limit 4

```java
// Demand: [Target | ZERO]
// Submitted: ZERO. Initial: ZERO.
void root(Box a) { // Entry producer assigns T to a.f.MUST.
    a.f.g = new Box();
    // a.f.MUST/T,N, E={g}
    Box x = make(a); // x.M/U,D; x.h.MUST/U,N and x.h.$/U,N
    Box y = make(x); // y.M/T,D; y.h.MUST/T,N and y.h.$/T,N
    Box z = make(y); // z.M/U,D; z.h.MUST/U,N and z.h.$/U,N
    // Observe CM(z.M,U): DemandTarget and retained NormalTarget(id)
}
// Summary: ZERO -> DemandTarget,D.
// Retain ZERO -> NormalTarget(id),N; emit it once.
```

```java
// Demand rows [entry | paired output]:
//   [p.f.g.M/T | ret.$/U, ret.*/U, ret.h.$/U, ret.h.*/U]
//   [p.f.M/T | ret.*/U, ret.h.$/U, ret.h.*/U]
//   [p.$/T | ret.h.$/U, ret.h.*/U]
//   [p.f.NE/T | ret.$/U, ret.*/U, ret.h.$/U, ret.h.*/U]
//   [p.M/T | ret.*/U, ret.h.$/U, ret.h.*/U]
//   [p.f.$/T | ret.h.$/U, ret.h.*/U]
//   [p.h.M/T | ret.h.$/U, ret.h.*/U]
//   [p.f.g.M/U | ret.f.$/T, ret.f.*/T, ret.h.$/T, ret.$/T, ret.*/T, ret.h.*/T]
//   [p.f.NE/U | ret.f.$/T, ret.f.*/T, ret.h.$/T, ret.$/T, ret.*/T, ret.h.*/T]
//   [p.h.M/U | ret.h.$/T, ret.h.*/T]
//   [p.f.M/U | ret.h.$/T, ret.*/T, ret.h.*/T]
//   [p.$/U | ret.h.$/T, ret.h.*/T]
//   [p.M/U | ret.h.$/T, ret.*/T, ret.h.*/T]
//   [p.f.$/U | ret.h.$/T, ret.h.*/T]
// Submitted to this shared method:
//   N: p.f.MUST/T {g}, p.h.MUST/T, p.h.$/T
//   N: p.h.MUST/U, p.h.$/U
//   D: p.M/U
//   D: p.M/T
// Emitted initials:
//   N: p.f.MUST/T {g}, p.f.$/T, p.h.MUST/T, p.h.$/T
//   D: p.f.*/T, p.h.*/T, p.f.g.$/T, p.f.g.*/T, p.f.$/T, p.$/T, p.*/T, p.h.$/T
//   N: p.f.*/FLOW, p.$/FLOW, p.h.*/FLOW, p.f.g.*/FLOW, p.*/FLOW
//   N: p.h.MUST/U, p.h.$/U
//   D: p.h.*/U, p.f.g.$/U, p.f.g.*/U, p.f.*/U, p.h.$/U, p.f.$/U, p.$/U, p.*/U
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.M,T) => assign U to r.MUST.
    // CM(p.M,T)     => assign U to r.h.MUST.
    // CM(p.f.g.M,U) => assign T to r.MUST.
    // CM(p.M,U)     => assign T to r.h.MUST.
    return r;
}
// New NORMAL summaries:
//   p.f.$/T -> N: ret.h.$/U, ret.h.MUST/U
//   p.h.MUST/U -> N: ret.h.$/T, ret.h.MUST/T
//   p.h.MUST/T -> N: ret.h.MUST/U, ret.h.$/U
// DEMAND summaries in the qualified refinement view:
//   p.f.*/T -> D: ret.M/U, ret.h.MUST/U, ret.h.$/U, ret.h.M/U, ret.$/U
//   p.h.*/U -> D: ret.h.$/T, ret.h.MUST/T
//   p.h.*/T -> D: ret.h.MUST/U, ret.h.$/U
//   p.f.g.$/U -> D: ret.f.$/T, ret.f.MUST/T, ret.h.$/T, ret.$/T, ret.MUST/T, ret.h.MUST/T
//   p.f.g.*/U -> D: ret.f.$/T, ret.f.MUST/T, ret.h.$/T, ret.$/T, ret.MUST/T, ret.h.MUST/T
//   p.f.*/U -> D: ret.f.$/T, ret.f.M/T, ret.h.$/T, ret.M/T, ret.h.MUST/T, ret.h.M/T, ret.$/T
//   p.h.$/U -> D: ret.h.$/T, ret.h.MUST/T
//   p.f.$/U -> D: ret.h.$/T, ret.h.MUST/T
//   p.$/U -> D: ret.h.$/T, ret.h.MUST/T
//   p.*/U -> D: ret.h.$/T, ret.M/T, ret.h.MUST/T, ret.h.M/T
//   p.f.g.$/T -> D: ret.$/U, ret.MUST/U, ret.h.MUST/U, ret.h.$/U
//   p.f.g.*/T -> D: ret.$/U, ret.MUST/U, ret.h.MUST/U, ret.h.$/U
//   p.f.$/T -> D: ret.h.MUST/U, ret.h.$/U
//   p.$/T -> D: ret.h.$/U, ret.h.MUST/U
//   p.*/T -> D: ret.M/U, ret.h.MUST/U, ret.h.$/U, ret.h.M/U
//   p.h.$/T -> D: ret.h.MUST/U, ret.h.$/U
```

### Run-6 backward, field limit 5

```java
// New NORMAL summaries: none
// DEMAND summaries in the qualified refinement view:
//   ret.$/U -> D: p.f.g.M/T, p.f.g.$/T, p.f.NE/T
//   ret.*/U -> D: p.f.g.M/T, p.f.M/T, p.f.g.$/T, p.f.NE/T, p.M/T
//   ret.h.$/U -> D: p.f.g.M/T, p.f.M/T, p.h.M/T, p.f.g.$/T, p.f.$/T, p.$/T, p.f.NE/T, p.M/T, p.h.$/T
//   ret.h.*/U -> D: p.f.g.M/T, p.f.M/T, p.h.M/T, p.f.g.$/T, p.f.$/T, p.$/T, p.f.NE/T, p.M/T, p.h.$/T
//   ret.f.$/T -> D: p.f.g.$/U, p.f.g.M/U, p.f.NE/U
//   ret.f.*/T -> D: p.f.g.$/U, p.f.g.M/U, p.f.NE/U
//   ret.h.$/T -> D: p.h.M/U, p.h.$/U, p.f.g.$/U, p.f.g.M/U, p.f.$/U, p.f.M/U, p.$/U, p.f.NE/U, p.M/U
//   ret.h.*/T -> D: p.h.M/U, p.h.$/U, p.f.g.$/U, p.f.g.M/U, p.f.$/U, p.f.M/U, p.$/U, p.f.NE/U, p.M/U
//   ret.$/T -> D: p.f.g.$/U, p.f.g.M/U, p.f.NE/U
//   ret.*/T -> D: p.f.g.$/U, p.f.g.M/U, p.f.M/U, p.f.NE/U, p.M/U
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.M,T) => assign U to r.MUST.
    // CM(p.M,T)     => assign U to r.h.MUST.
    // CM(p.f.g.M,U) => assign T to r.MUST.
    // CM(p.M,U)     => assign T to r.h.MUST.
    return r;
}
// Demand rows [entry | paired output]:
//   [ret.M/U | p.f.*/T, p.f.g.$/T, p.f.g.*/T, p.*/T]
//   [ret.h.M/U | p.f.*/T, p.h.*/T, p.f.g.$/T, p.f.g.*/T, p.f.$/T, p.$/T, p.*/T, p.h.$/T]
//   [ret.h.$/U | p.f.*/T, p.h.*/T, p.f.g.$/T, p.f.g.*/T, p.f.$/T, p.$/T, p.*/T, p.h.$/T]
//   [ret.h.$/T | p.h.*/U, p.h.$/U, p.f.g.$/U, p.f.g.*/U, p.f.$/U, p.f.*/U, p.$/U, p.*/U]
//   [ret.h.M/T | p.h.*/U, p.h.$/U, p.f.g.$/U, p.f.g.*/U, p.f.$/U, p.f.*/U, p.$/U, p.*/U]
//   [ret.f.$/T | p.f.g.$/U, p.f.g.*/U, p.f.*/U]
//   [ret.f.M/T | p.f.g.$/U, p.f.g.*/U, p.f.*/U]
//   [ret.$/T | p.f.g.$/U, p.f.g.*/U, p.f.*/U]
//   [ret.M/T | p.f.g.$/U, p.f.g.*/U, p.f.*/U, p.*/U]
//   [ret.$/U | p.f.g.$/T, p.f.g.*/T, p.f.*/T]
// Submitted to this shared method:
//   D: ret.M/U, ret.h.M/U
//   D: ret.f.M/T, ret.h.M/T, ret.M/T
// Emitted initials:
//   D: ret.$/U, ret.*/U, ret.h.$/U, ret.h.*/U
//   N: ret.*/FLOW, ret.h.*/FLOW, ret.f.*/FLOW, ret.$/FLOW
//   D: ret.f.$/T, ret.f.*/T, ret.h.$/T, ret.h.*/T, ret.$/T, ret.*/T
```

```java
// Published summary: ZERO -> DemandTarget,D.
void root(Box a) {
    // Backward source check accepts a.M/T,D and renews permission.
    a.f.g = new Box(); // Backward root MAY survives the replacement.
    Box x = make(a);   // a.M/T,D <- x.M/U,D
    Box y = make(x);   // x.M/U,D <- y.M/T,D
    Box z = make(y);   // y.M/T,D <- z.M/U,D
    // Backward observation emits z.M/U,D from reached ZERO.
}
// Submitted: ZERO at the normal exit. Initial: ZERO.
// Demand control: [Target | ZERO].
```

### Run-7 forward, field limit 6

```java
// Demand: [Target | ZERO]
// Submitted: ZERO. Initial: ZERO.
void root(Box a) { // Entry producer assigns T to a.f.MUST.
    a.f.g = new Box();
    // a.f.MUST/T,N, E={g}
    Box x = make(a); // x.M/U,D; x.h.MUST/U,N and x.h.$/U,N
    Box y = make(x); // y.M/T,D; y.h.MUST/T,N and y.h.$/T,N
    Box z = make(y); // z.M/U,D; z.h.MUST/U,N and z.h.$/U,N
    // Observe CM(z.M,U): DemandTarget and retained NormalTarget(id)
}
// Summary: ZERO -> DemandTarget,D.
// Retain ZERO -> NormalTarget(id),N; emit it once.
```

```java
// Demand rows [entry | paired output]:
//   [p.f.g.M/T | ret.$/U, ret.*/U, ret.h.$/U, ret.h.*/U]
//   [p.f.M/T | ret.*/U, ret.h.$/U, ret.h.*/U]
//   [p.h.M/T | ret.h.$/U, ret.h.*/U]
//   [p.f.g.$/T | ret.$/U, ret.*/U, ret.h.$/U, ret.h.*/U]
//   [p.f.$/T | ret.h.$/U, ret.h.*/U]
//   [p.$/T | ret.h.$/U, ret.h.*/U]
//   [p.f.NE/T | ret.$/U, ret.*/U, ret.h.$/U, ret.h.*/U]
//   [p.M/T | ret.*/U, ret.h.$/U, ret.h.*/U]
//   [p.h.$/T | ret.h.$/U, ret.h.*/U]
//   [p.f.g.$/U | ret.f.$/T, ret.f.*/T, ret.h.$/T, ret.h.*/T, ret.$/T, ret.*/T]
//   [p.f.g.M/U | ret.f.$/T, ret.f.*/T, ret.h.$/T, ret.h.*/T, ret.$/T, ret.*/T]
//   [p.f.NE/U | ret.f.$/T, ret.f.*/T, ret.h.$/T, ret.h.*/T, ret.$/T, ret.*/T]
//   [p.h.M/U | ret.h.$/T, ret.h.*/T]
//   [p.h.$/U | ret.h.$/T, ret.h.*/T]
//   [p.f.$/U | ret.h.$/T, ret.h.*/T]
//   [p.f.M/U | ret.h.$/T, ret.h.*/T, ret.*/T]
//   [p.$/U | ret.h.$/T, ret.h.*/T]
//   [p.M/U | ret.h.$/T, ret.h.*/T, ret.*/T]
// Submitted to this shared method:
//   N: p.f.MUST/T {g}, p.h.$/T, p.h.MUST/T
//   N: p.h.$/U, p.h.MUST/U
//   D: p.M/U
//   D: p.M/T
// Emitted initials:
//   N: p.f.MUST/T {g}, p.f.$/T, p.h.$/T, p.h.MUST/T
//   D: p.f.*/T, p.h.*/T, p.f.g.$/T, p.f.g.*/T, p.f.$/T, p.h.$/T, p.$/T, p.*/T
//   N: p.f.*/FLOW, p.$/FLOW, p.h.*/FLOW, p.f.g.*/FLOW, p.*/FLOW
//   N: p.h.$/U, p.h.MUST/U
//   D: p.h.*/U, p.f.g.$/U, p.f.g.*/U, p.f.*/U, p.h.$/U, p.f.$/U, p.$/U, p.*/U
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.M,T) => assign U to r.MUST.
    // CM(p.M,T)     => assign U to r.h.MUST.
    // CM(p.f.g.M,U) => assign T to r.MUST.
    // CM(p.M,U)     => assign T to r.h.MUST.
    return r;
}
// New NORMAL summaries: none
// DEMAND summaries in the qualified refinement view:
//   p.f.*/T -> D: ret.M/U, ret.h.MUST/U, ret.h.$/U, ret.h.M/U, ret.$/U
//   p.h.*/U -> D: ret.h.$/T, ret.h.MUST/T
//   p.h.*/T -> D: ret.h.MUST/U, ret.h.$/U
//   p.f.g.$/U -> D: ret.f.$/T, ret.f.MUST/T, ret.h.$/T, ret.h.MUST/T, ret.$/T, ret.MUST/T
//   p.f.g.*/U -> D: ret.f.$/T, ret.f.MUST/T, ret.h.$/T, ret.h.MUST/T, ret.$/T, ret.MUST/T
//   p.f.*/U -> D: ret.f.$/T, ret.f.M/T, ret.h.$/T, ret.h.M/T, ret.h.MUST/T, ret.M/T, ret.$/T
//   p.h.$/U -> D: ret.h.$/T, ret.h.MUST/T
//   p.f.$/U -> D: ret.h.$/T, ret.h.MUST/T
//   p.$/U -> D: ret.h.$/T, ret.h.MUST/T
//   p.*/U -> D: ret.h.$/T, ret.h.M/T, ret.h.MUST/T, ret.M/T
//   p.f.g.$/T -> D: ret.$/U, ret.MUST/U, ret.h.MUST/U, ret.h.$/U
//   p.f.g.*/T -> D: ret.$/U, ret.MUST/U, ret.h.MUST/U, ret.h.$/U
//   p.f.$/T -> D: ret.h.MUST/U, ret.h.$/U
//   p.h.$/T -> D: ret.h.$/U, ret.h.MUST/U
//   p.$/T -> D: ret.h.$/U, ret.h.MUST/U
//   p.*/T -> D: ret.M/U, ret.h.MUST/U, ret.h.$/U, ret.h.M/U
```

### Run-8 backward, field limit 7

```java
// New NORMAL summaries: none
// DEMAND summaries in the qualified refinement view:
//   ret.$/U -> D: p.f.g.M/T, p.f.g.$/T, p.f.NE/T
//   ret.*/U -> D: p.f.g.M/T, p.f.M/T, p.f.g.$/T, p.f.NE/T, p.M/T
//   ret.h.$/U -> D: p.f.g.M/T, p.f.M/T, p.h.M/T, p.f.g.$/T, p.f.$/T, p.h.$/T, p.$/T, p.f.NE/T, p.M/T
//   ret.h.*/U -> D: p.f.g.M/T, p.f.M/T, p.h.M/T, p.f.g.$/T, p.f.$/T, p.h.$/T, p.$/T, p.f.NE/T, p.M/T
//   ret.f.$/T -> D: p.f.g.$/U, p.f.g.M/U, p.f.NE/U
//   ret.f.*/T -> D: p.f.g.$/U, p.f.g.M/U, p.f.NE/U
//   ret.h.$/T -> D: p.h.M/U, p.h.$/U, p.f.g.$/U, p.f.g.M/U, p.f.$/U, p.f.M/U, p.$/U, p.f.NE/U, p.M/U
//   ret.h.*/T -> D: p.h.M/U, p.h.$/U, p.f.g.$/U, p.f.g.M/U, p.f.$/U, p.f.M/U, p.$/U, p.f.NE/U, p.M/U
//   ret.$/T -> D: p.f.g.$/U, p.f.g.M/U, p.f.NE/U
//   ret.*/T -> D: p.f.g.$/U, p.f.g.M/U, p.f.M/U, p.f.NE/U, p.M/U
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.M,T) => assign U to r.MUST.
    // CM(p.M,T)     => assign U to r.h.MUST.
    // CM(p.f.g.M,U) => assign T to r.MUST.
    // CM(p.M,U)     => assign T to r.h.MUST.
    return r;
}
// Demand rows [entry | paired output]:
//   [ret.M/U | p.f.*/T, p.f.g.$/T, p.f.g.*/T, p.*/T]
//   [ret.h.M/U | p.f.*/T, p.h.*/T, p.f.g.$/T, p.f.g.*/T, p.f.$/T, p.h.$/T, p.$/T, p.*/T]
//   [ret.h.$/U | p.f.*/T, p.h.*/T, p.f.g.$/T, p.f.g.*/T, p.f.$/T, p.h.$/T, p.$/T, p.*/T]
//   [ret.h.$/T | p.h.*/U, p.h.$/U, p.f.g.$/U, p.f.g.*/U, p.f.$/U, p.f.*/U, p.$/U, p.*/U]
//   [ret.h.M/T | p.h.*/U, p.h.$/U, p.f.g.$/U, p.f.g.*/U, p.f.$/U, p.f.*/U, p.$/U, p.*/U]
//   [ret.f.$/T | p.f.g.$/U, p.f.g.*/U, p.f.*/U]
//   [ret.f.M/T | p.f.g.$/U, p.f.g.*/U, p.f.*/U]
//   [ret.$/T | p.f.g.$/U, p.f.g.*/U, p.f.*/U]
//   [ret.M/T | p.f.g.$/U, p.f.g.*/U, p.f.*/U, p.*/U]
//   [ret.$/U | p.f.g.$/T, p.f.g.*/T, p.f.*/T]
// Submitted to this shared method:
//   D: ret.M/U, ret.h.M/U
//   D: ret.f.M/T, ret.h.M/T, ret.M/T
// Emitted initials:
//   D: ret.$/U, ret.*/U, ret.h.$/U, ret.h.*/U
//   N: ret.*/FLOW, ret.h.*/FLOW, ret.f.*/FLOW, ret.$/FLOW
//   D: ret.f.$/T, ret.f.*/T, ret.h.$/T, ret.h.*/T, ret.$/T, ret.*/T
```

```java
// Published summary: ZERO -> DemandTarget,D.
void root(Box a) {
    // Backward source check accepts a.M/T,D and renews permission.
    a.f.g = new Box(); // Backward root MAY survives the replacement.
    Box x = make(a);   // a.M/T,D <- x.M/U,D
    Box y = make(x);   // x.M/U,D <- y.M/T,D
    Box z = make(y);   // y.M/T,D <- z.M/U,D
    // Backward observation emits z.M/U,D from reached ZERO.
}
// Submitted: ZERO at the normal exit. Initial: ZERO.
// Demand control: [Target | ZERO].
```

## 6. Checks and scope

[Constructive proof package](../../spec/lean/proposals/excluded-guard-cycle-20261116/README.md).
The cold-prefix, budget-parametric fixed-point and exact uncapped recurrence
proofs are kernel checked. The axiom audit permits only `propext` and
`Quot.sound`; it accepts no custom axiom, hole, classical choice or external
decision oracle. A small proof-runner tactic closes parameters around the
ordinary `of_decide_eq_true rfl` certificate and asks Lean's kernel to check
it directly. It is not an analyzer mechanism or a native-evaluation oracle.

Two native tests pass. One runs the unchanged engine to run-31 and checks
its persistent root demand. The other checks the ordinary write's real E,
the coarse C2 initial, rejection by the fine guard, the coarse generated
MAY result, and absence of whole-region coverage by the h child. This
native diagnostic does not integrate the proposed NE policy or its new
coverage implementation. The uncapped result is proved independently in
the selected reference; no whole-engine bisimulation is claimed.

```bash
python3 spec/lean/proposals/excluded-guard-cycle-20261116/check.py \
  --out /tmp/excluded-guard-proofs
cd core
./gradlew :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.ExcludedGuardCycleTest
```

Frozen proof witnesses stay in the proof package. Bulk captures, rejected
candidate diagnostics, compiler output and receipts stay outside the repo,
under `excluded-guard-cycle-20261116/` in the existing external report-data
archive. `scripts/demand_experiments/excluded-guard-cycle-20261116/` contains
the diagnostic exporters and the trace renderer. They are not proof oracles.

# Root-cleaner / getter admission gap

17 November 2026. Synthetic marked-data reachability. FULL marks.
Latest reached native iteration: **run-3**, natural `NO_DEMAND_EDGE`, no
observation. There is no timeout, memory failure or iteration-cutoff argument.

**Status update:** [the proposal repair](../design/bidirectional-disjoint-cleaner-flow-20261117.md)
preserves FLOW outside the cleaner's whole suffix region. The repaired
reference now retains its NORMAL observation and stops at **run-3**. Native
components confirm its C5/replay pipeline. The unchanged production driver
still has the loss described below. The following trace is the historical
contract before that repair; it is kept as a regression witness.

The pre-repair [consolidated proposal](../design/bidirectional-demand-termination-approach-20261115.md)
retained an admission gap. This report does **not** establish that the latest
reply-service optimization introduced it. The unchanged native engine also
reproduces it. The proposal's additional EXACT start does not repair it.

## 1. Program and concrete result

```java
void main() {
    Box a = new Box();
    markGH(a);                 // Rule: assign T at a.g.h and its descendants.
    Box r = helper(a);
    observeTBelow(r);           // Rule: CM(r.[any], T).
}

Box helper(Box p) {
    clearRootT(p);             // Selected RemoveMark(T), EXACT reach at p.
    return p.g;
}
```

`a` is a local, not a parameter of `main`. It is dead after the call. The
cleaner removes only a mark at `p` itself. The concrete point `p.g.h/T`
survives and returns as `r.h/T`; the observation is reachable. No loop,
recursion, pass rule, alias expansion or unresolved MAY-producing model is
needed. The configured cleaner has its explicitly stated transfer.

Notation: `M` = MAY, `NE` = nonempty MAY, `*` = correlated STAR, `$` = EXACT,
`MUST` = uniform mark. `N/D` are layers. `mx={T}` excludes T from FLOW.
Selected-cleaner survivors have the existing protected membership `H=1`.
Omitted ZERO identity records do not carry T or supply a DATA query.

## 2. Run-1: forward, limit 1

```java
// main:
// Previous demand: unrestricted run-1.
// Entry: ZERO, NORMAL.
void main() {
    Box a = new Box();
    markGH(a);
    // Exact source region: a.g.h.MUST/T,N.
    // Real field cut:     a.g.NE/T,D.
    Box r = helper(a);
    // Concrete helper result: r.M/T,D.
    observeTBelow(r);
}
// Published control: ZERO -> DemandTarget,D.
// No local a DATA summary escapes main.

// helper:
// Previous demand: unrestricted run-1.
// Submitted marked offer: p.g.NE/T,D.
// Initials requested by the root cleaner/read:
//   p.*/FLOW -> p.*/FLOW,N
//   p.*/T    -> p.*/T,D
Box helper(Box p) {
    clearRootT(p);
    // FLOW: p.*/FLOW(mx={T}),N.
    // T:    p.M/T,D,H=1. The selected STAR partial survivor loses correlation.
    return p.g;
    // Returned FLOW: ret.M/FLOW(mx={T}),D.
    // Returned T:    ret.M/T,D,H=1.
}
// Published summaries:
//   p.*/FLOW -> p.*/FLOW(mx={T}),N
//   p.*/FLOW -> ret.M/FLOW(mx={T}),D
//   p.*/T    -> p.M/T,D,H=1
//   p.*/T    -> ret.M/T,D,H=1
```

For the proposal, all real cuts use NE. The current native engine uses MAY
for that cut. Both yield the same marked return `ret.M/T,D` in this case.
The run-1 abstraction still uses the empty-path nonstatic initial.

## 3. Run-2: backward, limit 1

Backward summaries are above the body; entry-side demand, submitted facts
and initials are below the body. The annotations name facts in the helper
namespace, not caller locals.

```java
// helper published backward DATA:
//   ret.$/T -> p.g.$/T,D,H=1       // Additional EXACT arm in the proposal.
//   ret.*/T -> p.g.*/T,D,H=1
// Native also retains a structural NORMAL companion:
//   ret.*/FLOW -> p.g.*/FLOW(mx={T}),N
Box helper(Box p) {
    clearRootT(p);
    // Backward p.g.$/T and p.g.*/T are disjoint from cleaning p itself.
    // They retain their precise g head. Neither undergoes a real field cut.
    return p.g;
    // Reverse read: ret.$ -> p.g.$; ret.* -> p.g.*.
}
// Relevant previous rows, written as (entry Dc; paired exit Dp):
//   (ret.M/T; p.*/T)
//   (p.M/T; p.*/T)                 // No matching p offer arrives here.
//   (ret.M/FLOW(mx={T}); p.*/FLOW)  // Rejects an actual T mark.
// Submitted: ret.M/T,D.
// Selected complete C2 family:
//   ret.$/T,D; ret.*/T,D; ret.*/FLOW,N.
// No p/T output offer is submitted by main: local a has no later consumer.

// main published backward control: ZERO -> DemandTarget,D.
void main() {
    Box a = new Box();
    markGH(a);
    // Reversed correlated helper reply reaches a.g.M/T,D.
    // It overlaps the marked g.h source region and renews its permission.
    Box r = helper(a);
    observeTBelow(r);
}
// Previous demand: Target -> ZERO.
// Backward observation supplies r.M/T,D, hence helper's ret.M/T,D.
```

The proposal's strict scalar C5 mark gate can reject the FLOW companion
under concrete `Dp`. The native path retains it as a structural companion.
The proof conservatively retains that NORMAL record too: it still excludes
T and cannot fix the gap. No argument relies on deleting it.

No observed-field preparation adds `h` here. The relevant retained NORMAL
input guards have only `p.*` or `p.g.*`, not `p.g.h.*`. Preparation applies
to MAY/NE rows; after this handoff the marked entries are precise `$/*`.

## 4. Run-3: forward, limit 2

```java
// main:
// Previous control permits entry/source processing.
void main() {
    Box a = new Box();
    markGH(a);
    // Now uncut: a.g.h.MUST/T,N.
    Box r = helper(a);
    // No T result. No NormalTarget or DemandTarget reaches the observation.
    observeTBelow(r);
}
// No outgoing demand. Native stop: run-3, NO_DEMAND_EDGE, findings=0.

// helper:
// Previous marked demand rows:
//   p.g.$/T -> ret.$/T
//   p.g.*/T -> ret.*/T
// Submitted: p.g.h.MUST/T,N.
// Saved NORMAL replay: all potential T transfers exclude T via mx={T}.
// C2: both precise rows reject the deeper h path after run-2.
// Emitted initials: none.
Box helper(Box p) {
    clearRootT(p);
    return p.g;
}
// Published current T summaries: none.
```

The missing output is not a failed source permission: the formal model
optimistically supplies the precise NORMAL marked actual and still gets no
query. More global field room cannot repair this precise-STAR rejection.
The same-head MUST cleaner revision cannot help because no helper query is
admitted. Completion selectors only remove current deliveries; none can
create a missing query.

## 5. Proof and validation

[AuditCleanerGetter.lean](../../spec/lean/proposals/termination-soundness-audit-20261117/AuditCleanerGetter.lean)
checks the selected complete C2 families, marked own-row C5 results, real
NE cut, retained argument outputs, root cleaner, ordinary read, correlated
call binding, renewed source region and rejection of the precise run-3
offer. It also checks that both retained NORMAL structural routes exclude
T. The rejection theorem quantifies over every global limit. A concrete
transfer theorem constructs the surviving NORMAL `ret.h.MUST/T` witness.

This is a focused executable policy model. It is not a formal model of the
entire JVM/driver. Its small `cold` result records the computed quiet suffix;
it is not an independent driver-verification theorem. In particular, the
reference/native structural-companion distinction above is explicit.

[CleanerGetterAdmissionSoundnessTest.kt](../../core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/CleanerGetterAdmissionSoundnessTest.kt)
independently runs the unchanged driver from cold entry. The cap is 15;
all three cases stop naturally at **run-3**:

| Case | NORMAL observations | Latest run / reason |
|---|---:|---|
| Root cleaner, source at g.h | **0: missed observation** | run-3 / NO_DEMAND_EDGE |
| Remove the cleaner | 1 | run-3 / NO_DEMAND_EDGE |
| Keep cleaner; source at g only | 1 | run-3 / NO_DEMAND_EDGE |

The first test deliberately asserts the current missing result. It documents
an unfixed defect; it must be changed to require the observation when a repair
is selected. It is not evidence of correct analyzer behavior.

## 6. What this disproves

The following implication is false without an additional relevance invariant:

```text
Demand precise STAR rejects deeper inputs
AND a preceding MAY analysis produced that precise STAR demand
    => the rejected deeper input has another retained NORMAL service.
```

Here the only structural alternatives exclude T. The source becomes fully
representable at run-3, but the precise demand blocks its analysis. Therefore
point coverage, a finite termination campaign and local C5 no-loss proofs
cannot establish the requested whole-proposal no-missed-observation claim.

At discovery, the audit selected no repair. Changing STAR admission, cleaner FLOW masks,
query completion or demand emission is a semantic decision. A repair must
preserve the intended field budget and the previous termination examples.

The selected repair changes only the disjoint nonstatic FULL FLOW cleaner
branch. It retains STAR admission and all budgets. Its generic whole-region
proof and repaired per-run trace are in the linked repair document.

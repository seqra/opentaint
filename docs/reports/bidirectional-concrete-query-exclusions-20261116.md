# Retain real exclusions on same-head concrete queries

16 November 2026. Synthetic data-flow reachability. FULL marks. Follow
[proof-guide.md](../../spec/proof-guide.md). This is a proposal and a checked
reference model. Production is unchanged.

The [real-exclusion counterexample](bidirectional-excluded-guard-nontermination-20261116.md)
now stops naturally at **run-5**. Its valid NORMAL observation is reached at
**run-3**. The previous 18 ordinary examples retain their complete states,
findings and stops, latest **run-15**. The alternating-generator and three
strict concrete-replay examples retain their **run-5** stops. The protected
closure and selected cleaner retain their separate **run-3/run-1** results.
There is no hard-limit argument and no universal termination theorem.

## 1. Cause and selected semantic change

The previous C2 family could forget a real field exclusion when it changed
an actual MUST into a first-field STAR query. The query could then test a
field which the actual explicitly excluded. Fine queries respected the hole,
but they could not cancel the independently generated coarse question.

```text
entry selector: p.M/T             paired output: ret.*/U
submitted:     p.f.MUST/T {g}, NORMAL

previous concrete start: p.f.*/T {}, DEMAND
new concrete start:      p.f.*/T {g}, DEMAND

previous FLOW companion: p.f.*/FLOW {}, NORMAL
new FLOW companion:      p.f.*/FLOW {g}, NORMAL
```

This changes **C2 semantics and C5's constructive raw entry image**. It does
not change instruction transfer, rule evaluation, native matching, output
intersection or the stop test. Concrete STAR stays DEMAND. The FLOW query
remains a conditional hypothesis; it does not prove that T exists.

Use the following map on the **complete existing C2 family**, including its
existing FLOW companions. An independent FLOW-only demand is unchanged.

```text
emit(run, mode, demand, actual):
    family = previousCompleteC2Family(run, demand, actual)
    if run == 1 or mode != FULL or demand.mark is not concrete:
        return family
    if actual.E is empty:
        return family

    return map family as q:
        if q.tail == STAR
           and q.base == actual.base and q.path == actual.path
           and q.E is empty
           and actual.tail in {STAR, MUST}:
            return q with E = actual.E
        return q

restrictOne(previousDemand, rawInitial, rawConclusion, legalOffers):
    image = union of emit(run, FULL, previousDemand.Dc, a)
            for a in legalOffers
    if rawInitial is not a member of image: return empty
    // Use the existing paired C5, not a new output policy.
    (P, C) = existingFLOWNormalization(rawInitial, rawConclusion)
    C = existingOutputIntersection(C, previousDemand.Dp)
    if C is empty: return empty
    C = existingCut(C, min(globalLimit, FL(previousDemand.Dp) + 1))
    return existingFLOWNormalization(P, C)
```

C5 tests the actual raw initial with its E before FLOW normalization. It
must use this new family; accepting only the old Empty-E key would reject
the new legitimate summaries. It must not borrow an old Empty-E admission
to accept an unrelated query. Real E remains part of the existing initial
key, equality, hashing and persistence.

`legalOffers` is the explicit reference model's admissible offer domain.
In production the existing structural C5 image test must recognize this
constructive image over the legal grammar. It must not retain a new history
of submitted actuals or use a sampled input dump as the complete domain.

The map also applies in backward restricted runs when its conditions hold.
It adds no backward MUST start. A same-head MUST query already retains E
and is unchanged. The conditional prefix `p.$/FLOW` probe is unchanged.
No new member, field, mark, layer, mx or protection flag is added.

## 2. Exclusion scope is essential

E is relative to its fact's head. Copy it only when that head is unchanged.

```text
actual:        p.f.g.MUST/T {g}, NORMAL
first start:   p.f.*/T {}, DEMAND
```

The actual excludes `p.f.g.g`, not `p.f.g`. Copying `{g}` to p.f would remove
the actual's own root. This case therefore keeps the old coarse start.
An existing nonempty query E is also left unchanged. Do not union exclusions
from different arrivals or invent a ban from the failed guard.

For an eligible same-head query q and actual a, the proof establishes:

```text
pointRegion(q with E=a.E) = pointRegion(a)
```

This is geometric equality. STAR still has weaker mark knowledge than MUST;
the proof does not equate correlated FLOW with uniform taint. Every actual
represented point remains available. Native operations already check E at
that head, so the excluded descendant cannot satisfy a guard and the allowed
root/other descendants still can. Conditional summaries carry their real E
and cannot apply to an actual confined to the excluded subtree.

## 3. New example and the decisive run-3 trace

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
    // CM(p.f.g.M,T) => assign U to r.MUST.
    // CM(p.M,T)     => assign U to r.h.MUST.
    // CM(p.f.g.M,U) => assign T to r.MUST.
    // CM(p.M,U)     => assign T to r.h.MUST.
    return r;
}
```

Notation: `$` is EXACT, `*` is correlated STAR, M is MAY, NE is nonempty
MAY, and N/D is NORMAL/DEMAND. All H memberships in this example are plain.
All three calls share one make owner. There is no loop, recursion, cleaner,
pass rule, unresolved method or intrinsic-MAY action.

The run-2 backward frontier includes both the root-MAY and qualified f.NE
input questions. At run-3 the replacement emits `a.f.MUST/T {g},N`.
The principal make queries and their admitted summaries are:

```java
// run-3, forward, field limit 2
// Demand entries include p.M/T and p.f.NE/T.
// Paired outputs include ret.*/U and ret.h.$/U.
// At make(a), submitted: p.f.MUST/T {g},N.
// Initials include:
//   p.f.*/T {g},D; p.f.*/FLOW {g},N; p.$/FLOW {},N;
//   p.f.MUST/T {g},N from the qualified row.
// At make(x), submitted: p.h.MUST/U,N and p.h.$/U,N.
// Initials include p.h.*/U,D; p.h.$/U,N, and existing FLOW probes.
// At make(y), submitted: p.h.MUST/T,N and p.h.$/T,N.
// Initials include p.h.*/T,D; p.h.$/T,N, and existing FLOW probes.
Box make(Box p) {
    Box r = new Box();
    // The f.g checks produce no root result for any of these actuals:
    // - p.f starts exclude g;
    // - p.h starts cannot reach p.f.g.
    // The broad p.M checks still assign the other mark to r.h.MUST.
    return r;
}
// Published NORMAL return records, exactly six:
//   p.f.MUST/T {g} -> ret.h.MUST/U,N
//   p.f.MUST/T {g} -> ret.h.$/U,N
//   p.h.$/U       -> ret.h.MUST/T,N
//   p.h.$/U       -> ret.h.$/T,N
//   p.h.$/T       -> ret.h.MUST/U,N
//   p.h.$/T       -> ret.h.$/U,N
// Six qualified DEMAND rows also remain, two per conditional STAR input:
//   p.f.*/T {g} -> ret.h.M/U,D or ret.h.$/U,D
//   p.h.*/U     -> ret.h.M/T,D or ret.h.$/T,D
//   p.h.*/T     -> ret.h.M/U,D or ret.h.$/U,D
```

These are summaries, not all raw rule outputs. Existing paired C5 produces
the listed MAY/point images from the raw uniform assignments.

```java
// run-3 root control: the previous backward run permits the entry mark.
void root(Box a) {
    a.f.g = new Box(); // a.f.MUST/T {g},N
    Box x = make(a);  // x.h.MUST/U,N and x.h.$/U,N
    Box y = make(x);  // y.h.MUST/T,N and y.h.$/T,N
    Box z = make(y);  // z.h.MUST/U,N and z.h.$/U,N
    // CM(z.M,U) has a NORMAL witness. No root-MAY/D witness arrives.
}
// Root observation: NORMAL retained; no fresh DemandTarget.
```

Keep the NORMAL exact h summaries alongside MUST summaries. The exact actual
can start a NORMAL exact query at the next call. The resulting ready uniform
reply covers the whole corresponding child DEMAND image, through the
already selected actual-DATA coverage rule. No hypothetical callee summary
is used as a NORMAL actual. No emitted Target is canceled.

## 4. Complete run sequence and uncapped stop

Counts are the marked-return/control reference's qualified method rows and
retained NORMAL return records, not project-wide engine measurements.

| Completed run | Direction / field limit | Qualified rows | NORMAL records | Fresh root DemandTarget | NORMAL observation retained |
|---|---|---:|---:|---|---|
| run-1 | F / 1 | 4 | 0 | yes | no |
| run-2 | B / 1 | 14 | 0 | backward source permission renewed | no |
| run-3 | F / 2 | 6 | 6 | no | yes |
| run-4 | B / 3 | 0 | 6 | no backward root start | yes |
| run-5 | F / 4 | 0 | 6 | no; natural stop | yes |
| Every forced later run | existing increasing schedule | 0 | 6 | no | yes |

Run-1/run-2 are identical to the previous reference. In run-1 E is empty;
run-2's assembled offers also have empty E. The repair first changes run-3.
Its six remaining make rows do not imply a root continuation: no root
DemandTarget was emitted. Existing ZERO/Target admission therefore does not
start the backward root at run-4. The driver stops at the next forward empty
frontier, run-5. Nothing is deleted based on an earlier hard cutoff or a
prediction that the report is sufficient.

Lean constructs each cold state from run-1 and checks within-run quiescence.
It then proves an absorbing quiet state for arbitrary later run numbers:

```text
State(4) = quiet(retainedReport=true, savedSixRecords)
forall n >= 0, State(n+6) = State(6)
stop(State(5)) = true
```

Thus the termination argument is not a finite run-31 observation. The old
uncapped run-7/run-8 counterexample remains valid for the historical policy
which cleared E; its proof sources remain unchanged.

## 5. Old examples and limits of the result

The 18 ordinary references have FLOW-only demand rows at every checked
prefix. A generic pipeline-equivalence proof shows that the new map leaves
their admission, raw C5, publication, delivery and whole cold states exactly
unchanged. This includes the earlier overwrite/exclusion case; it is not
assumed to have empty actual E.

| Reference | Natural stop, before and after |
|---|---|
| Double | run-15 |
| Growth | run-7 |
| LongReader | run-5 |
| Nested | run-9 |
| NestedDeep | run-5 |
| NestedExact | run-3 |
| NestedLarger | run-11 |
| NestedNegative | run-3 |
| NestedPositive | run-3 |
| NestedSurvivor | run-5 |
| OldBB | run-5 |
| OldMethod | run-5 |
| OrdinaryTwo | run-3 |
| Overwrite | run-9 |
| Postfix | run-13 |
| Prefix | run-7 |
| PrefixPostfix | run-11 |
| RoundTrip | run-9 |

The alternating conditional-generator model is rerun with the new emitter
and accumulating Targets. It retains its exact cold states and run-5 stop.
The strict exact, uniform and different-path saved-replay references have
empty E on all assembled actual offers; generic full-history equivalence
therefore preserves their run-5 stops and both observations. Each has an
uncapped no-revival theorem. Selected cleaner and protected-closure controls
retain their previous rules and results.

This proves the supplied references. It does not prove universal termination
of every acyclic program, whole-production equivalence or coverage for GROUP.
The existing independent-model/front-end scope limits still apply. The new
rule deliberately leaves changed-head abstraction coarse, so a different
example may still require another progress law.

## 6. Work and storage

Per offer, family size is unchanged before ordinary deduplication. The map
adds one constant number of head/tail checks per existing member and reuses
the actual immutable E. With uncached scalar paths the head check costs
O(path length). It stores no suffix, origin product, truncation history or
new subscription, and generates no combinations of exclusions.

There is one cost to retain: different actual E sets can now create distinct
conditional initial keys where the old Empty-E keys merged. No global bound
of “no more work than before” is claimed. The new keys use only already
arrived real E, with existing interning and freshness. A native test pins
two distinct E sets and verifies that no union/powerset keys are produced.

The benefit in the new example is algorithmic: excluded g never generates
the repeated root-MAY path. Increasing the field limit or making a matcher
faster could not remove that path under the old policy.

## 7. Validation

[Constructive proof package](../../spec/lean/proposals/concrete-query-exclusions-20261116/README.md):
**458 new claims; 4,342 audited claims across 210 modules**. Dependencies are
source-hash checked. The axiom audit allows only `propext` and `Quot.sound`;
there are no custom axioms, holes, classical choice or external decision
oracles. Full states are retained as Lean witnesses, not generated snapshots
accepted on trust.

The native component/control suite passes **31 tests**: nine new admission,
E-scope, C5-key, interning, rule-transfer and current-summary checks, plus
22 previous controls. The candidate is a test adapter. The native production
counterexample control still completes **run-31**; this is not a claim of an
integrated native run-5 result or a project performance measurement.

```bash
python3 spec/lean/proposals/concrete-query-exclusions-20261116/check.py \
  --out /tmp/concrete-query-exclusions-proofs

cd core
./gradlew :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.ConcreteQueryExclusionsTest \
  --tests org.opentaint.dataflow.bidi.ExcludedGuardCycleTest \
  --tests org.opentaint.dataflow.bidi.AlternatingConditionalCycleTest \
  --tests org.opentaint.dataflow.bidi.NormalUniformActualCoverageTest \
  --tests org.opentaint.dataflow.bidi.DefiniteMustReplayNativeTest --console=plain
```

Compiled proofs, receipts and logs are outside the repository. The package
README gives the exact current validation location and the optional cached
dependency command. Production changes require a later implementation task.

# Complete NORMAL service for one current return reply

Later investigation found a
[protected-return case](../reports/bidirectional-protected-return-nontermination-20261116.md):
the earlier full-raw plain-support checks reject a protected NORMAL return
outside this reply's region. Its complete reference states repeated
run-11/run-12 uncapped. The selected
[layer-aware repair](bidirectional-layer-aware-point-service-20261116.md)
now stops this case at **run-5**, with its NORMAL observation retained.
It keeps H in full NORMAL-layer closure, and requires plain service for
every overlapping terminal return. The geometric theorem remains sound;
the earlier h-read case below retains its identical semantic cold history
and run-5 stop. The two new layer/service checks supersede only the
corresponding globally plain eligibility checks described below.

16 November 2026. Synthetic data-flow reachability. FULL marks.
Follow [proof-guide.md](../../spec/proof-guide.md). Production is unchanged.
[Consolidated approach](bidirectional-demand-termination-approach-20261115.md).

The [same-mark disjoint-return case](../reports/bidirectional-unadmitted-field-nontermination-20261116.md)
now stops naturally at **run-5**, with its NORMAL observation retained.
Its earlier complete states repeated run-11/run-12 without a limit.
The old exact-input and V-return cases still stop at run-5, with unchanged
semantic cold histories. All earlier guard-ineligible references remain
unchanged; the largest retained reference stops at run-15.
Latest unchanged native diagnostic: **run-31/POLICY**.

## 1. Change and limits

This is a **major change to current DEMAND return delivery**.

| Part | Before | After |
|---|---|---|
| Completion scope | Whole return service, or all returns of one full mark | Also permit complete service for the region of this current reply |
| Same-mark disjoint return | An unadmitted k/U return blocks h/U completion | It does not block an h-region reply; it still blocks a root or k reply |
| No real return in that region | Mark-scoped completion requires a positive NORMAL group | A completed full NORMAL analysis can reject this reply on demand; store no negative certificate |
| Query metadata | Shared internal closure and whole/mark flags | Expose its current-owner NORMAL-closed status for existing queries; add no region cache |
| C2, C5, transfers, layers, marks, H, caps, saved replay, Targets | Selected consolidated rules | Unchanged |

Do not change a DEMAND fact into NORMAL. Do not infer that a child NORMAL
fact covers a parent MAY region. Do not remove the coarse query, stored
summary, subscription, non-return effect or an already emitted Target.
Only omit the selected current return DATA delivery to one supported actual.

This is a general boundary-selection rule. It does not depend on field
names, action ordinals, a particular marking pair or a particular helper.
It adds no initial, summary, field path, cap exception, cross-call suffix
evidence or unrelated propagated work.

The existing strong-closure adapter remains conservative. The executable
adapter in this package handles already analyzed leaf bodies with ordinary
allocation/return and positive unary marking actions. No new closure adapter
for ND, negative conditions, cleaners, statics, aliases, opaque operations or
cyclic dependencies is selected. Unsupported cases keep ordinary delivery.
This is not a universal termination claim.

## 2. The rule

Keep whole and per-full-mark completion as fast paths.
For the additional path, let:

```text
I = an already owned NORMAL concrete EXACT initial, Empty E/mx, plain H
C = its existing complete NORMAL internal states
R = the full, uncut, mode-stable transfer relation
r = this scalar CURRENT DEMAND return reply, after C5 and native binding
A = the same-context NORMAL return service which actually applied

Closed(I,C) := seed(I) in C and forall s in C: R(s) subset C
Relevant(c,r) := possibleRegion(c) overlaps possibleRegion(r)

CompleteForReply(I,r,A) :=
    Closed(I,C)
    and forall real return c in C:
        Relevant(c,r) implies
            an admitted NORMAL service row covers the WHOLE c
            and that row's NORMAL image actually applied in A
```

The scope includes owner, semantic revision, direction, physical entry/return
ports, complete caller original, continuation, mark and literal H. Compare
regions at the same physical return boundary, before caller register renaming.
Use the already bound reply's owner-side geometry. The leaf adapter's native
application changes only the base, so its stored and bound reply geometries
are identical. Do not assume this equality for an unsupported binding or
alias effect; keep ordinary delivery there.

**R and C stay complete and unprojected.** Process the k return and every
other-mark internal state. Queue empty alone is not closure. A cut, pending
operation, unclosed child, unstable dependency, unsupported effect or missing
state prevents this check. Do not rerun precise transfer or add states to
make closure succeed. Do not infer closure from successful C5 publications.
A child reply-specific certificate is not a complete child relation; it
cannot justify the enclosing query's full internal closure.

Every overlapping real return needs **whole** NORMAL service. If a root
MUST overlaps h but only its h portion was admitted, the extra path fails.
No new partial-return coverage or projection proof is assumed. This is a
conservative restriction, not permission to lose the unrepresented portion.

If no real return overlaps r, the terminal obligation is empty. The query
must still have completed its full NORMAL analysis. Evaluate this case for
this reply, then discard the verdict. Add no negative-result cache.

## 3. Overlap

Use the ordinary point-region interpretation of fields and tails, including
real exclusions and full-mark compatibility. STAR has its possible suffix
region for this test; its native correlation and admission rules do not change.
A conservative overlap test may retain extra replies, but must never reject
a common concrete location:

```text
possibleOverlap(a,b):
    reject different bases or disjoint full-mark possibilities
    consume equal concrete head fields
    if the remaining heads are both empty:
        return (both tails permit the empty suffix)
               or (both tails can contain a nonempty suffix)
    if only a's head is empty:
        return a.tail admits the path towards b, with E at a's head
    if only b's head is empty:
        return b.tail admits the path towards a, with E at b's head
    return false  // different next concrete fields
```

The same-head nonempty test is conservative when exclusions differ. It must
not turn incomparable exclusions into a disjointness claim. The constructive
geometry proof shows that any common admitted location passes this test.
Unknown FLOW that may contain the selected full mark is not silently excluded.

| Raw true return c | Reply region | Relevant? |
|---|---|---|
| ret.h.h.MUST/U | ret.h.M/U | yes |
| ret.k.MUST/U | ret.h.M/U | no |
| ret.k.MUST/U | ret.M/U | yes |
| ret.MUST/U | ret.h.M/U | yes |
| ret.$/U | ret.h.M/U | no |
| ret.h.$/U | ret.h.NE/U | no |
| ret.MUST/U {h} | ret.h.M/U | no |
| ret.h.MUST/U {h} | ret.h.M/U | yes: the h root is not excluded |

## 4. Delivery pipeline and ownership

Use the existing saved-first call/block pipeline, scalar memberships and
local publication boundary. The complete native packet and its existing
NORMAL service must be ready before this selection. No caller waits for a
new global barrier. A late check can help later deliveries/runs.

```text
onCurrentReturnReply(context, actual, currentRow, boundReply, normalPacket):
    // Saved NORMAL replay and current NORMAL application already ran as usual.
    if existing whole/mark certificate and its application receipt suffice:
        use the existing selection
    else if not (restricted forward FULL, run >= 3,
                 actual is supported NORMAL concrete EXACT, Empty E/mx, plain H,
                 currentRow.initial is a strict shorter-prefix STAR,
                 boundReply is plain CURRENT DEMAND concrete return DATA):
        deliver(boundReply)
    else if not owner.hasCurrentFullNORMALClosure(actual.rawInitial, context):
        deliver(boundReply)
    else:
        region = ownerSideRegion(boundReply)
        for c in owner.existingProcessedReturns(actual.rawInitial):
            if possibleOverlap(c, region):
                n = existingAdmittedWholeNORMALCover(c, actual.rawInitial, context)
                if n is absent or its whole NORMAL image did not apply here:
                    deliver(boundReply)
                    return
        omit this scalar reply membership
```

The new check adds no caller history or per-region status. The owner/coordinator
may expose one current-epoch NORMAL-closed bit on an **existing** exact query.
Discard this new status with the query/iteration. Whole and mark certificates
keep their previous lifetime rules. Invalidate readiness when dependencies or
semantic revisions change. An owner which lacks the required processed boundary
states must fall back; it must not create an unrestricted summary archive.

A full NORMAL closure is not GroundingSupport. It is an eligibility certificate
on the query coordinator. It does not change fact equality, MethodEdgeStore,
field transfer, premise matching or a mark's layer. No label propagates with
facts or through callers.

Keep every NORMAL/protected result and all FLOW, ZERO, Target, static-pool,
request and subscription channels. Keep AND binding and original identity.
Do not borrow an h verdict for a k reply, another mark or another caller.
Saved NORMAL replay stays unchanged. Preserve original field/exclusion/layer
handling, all selected observation behavior and the stopping test.

## 5. New example and trace

```java
// Entry marking: T only at a.f.g.$.
void root(Box a) {
    Box x = make(a).h;
    Box y = make(x).h;
    Box z = make(y).h;
    // Observe CM(z.M,U).
}
Box make(Box p) {
    Box r = new Box();
    // For (m,n) = (T,U), (U,T), use these three unary rules:
    // CM(p.f.g.g.M,m) => assign n to r.h.MUST.
    // CM(p.M,m)       => assign n to r.h.h.MUST.
    // CM(p.M,m)       => assign n to r.k.MUST.
    return r;
}
```

For the first fine query at run-3:

```text
actual / initial: p.f.g.$/T,N
full raw NORMAL returns: ret.h.h.MUST/U and ret.k.MUST/U
admitted NORMAL service: ret.h.h.MUST/U
coarse CURRENT reply:    ret.h.M/U,D

before: k/U blocks full-mark completion -> deliver h.M -> caller x.M/U,D
new:    k/U is disjoint from this h reply;
        h.h/U has actual whole NORMAL service -> omit this coarse delivery
        caller keeps x.h.MUST/U,N
```

Do not discard k from the internal closure or publish k as a new summary.
A root or k reply still requires k service. Later calls complete under the
ordinary demand mechanism; no new MAY-owned initial or deeper query is added.

| Run | Previous demand | Updated demand | Updated NORMAL records | New current-owner closed keys | Observation/control |
|---|---:|---:|---:|---:|---|
| run-1 | 6 | 6 | 0 | 0 | DemandTarget |
| run-2 | 6 | 6 | 0 | 0 | entry-marking permission |
| run-3 | 15 | 4 | 1 | 1 | previously emitted DemandTarget retained |
| run-4 | 40 | 11 | 1 | 0 | entry-marking permission |
| run-5 | 42 | 0 | 10 | 3 | NORMAL observation; natural stop |

The old frontier later repeated 70/82 rows forever. The updated reference
has a constructive uncapped quiet suffix after run-5. It also checks a
within-run fixed point at every cold run; its fuel bound is not the stop.
[Complete updated per-block trace](../reports/bidirectional-reply-scoped-point-service-trace-20261116.md).

Two controls explain the rule's boundary:

```text
raw c: ret.k.MUST/U,N; candidate ret.h.M/U,D; no h NORMAL row:
    complete full NORMAL analysis proves no h return -> omit on demand
    without completed closure -> keep

raw c: ret.MUST/U,N; candidate ret.h.M/U,D; only h NORMAL service:
    root overlaps h -> require whole root service -> keep
```

## 6. Work and field limits

The change **only selects among existing replies**. It creates no query,
propagated edge, summary, subscription, mark group or concrete field path.
It does not enumerate full suffixes or compose evidence across calls.
There is no persistent query-by-region table. Current closure status is
bounded by already owned queries. Temporary work uses this current reply
and references to existing NORMAL boundary states/service.

For B eligible reply leaves and R already owned return leaves, a conservative
implementation scans at most B*R pairs, with existing path and native-cover
lookup costs. Whole/mark completion remains the fast path. Reuse identical
checks within the current publication packet; discard temporary decisions
at its end. Existing boundary indexes may skip proved disjoint subtrees,
but must include overlapping ancestors such as root MUST. No new precise
analysis or dense mark/region product is allowed to build that index.
This is a bounded local cost, not a claim of constant time or guaranteed
project-level speedup. Measure scan counts and removed deliveries.

All initial and output limits remain unchanged:

```text
ordinary initial: FL(I) <= min(globalLimit, FL(own Dc)+1)
summary output:   FL(C) <= min(globalLimit, FL(own Dp)+1)
real field cut:   NE/DEMAND, with the existing mark/H behavior
```

The only retained input exception is the previously enumerated NORMAL-MUST
actual with a deeper real hole. This change adds **zero exceptions**, uses
none in the new example and cannot weaken its output cap. The new selection
requires a NORMAL EXACT actual, so it cannot itself activate the MUST exception.
If an owned query needs a cut to complete its body, it is ineligible for the
new full-NORMAL-closure check. Do not raise its limit to obtain a certificate.

## 7. Proofs and regression scope

[Constructive proof package](../../spec/lean/proposals/reply-scoped-point-service-20261116/README.md):

- A common concrete location always passes the overlap test, including tails,
  full marks and real exclusions. Conservative overlap can only keep extra work.
- CompleteClosure still covers the full internal relation. Terminal projection
  gives a whole NORMAL service witness for every reachable relevant return.
  Actual native application preserves any corresponding continuation observation.
- Missing relevant service, ancestor uniform effects, unfinished/DEMAND work,
  wrong support and missing receipts block selection. Disjoint terminal effects
  do not need service for this one reply. An empty region still needs full closure.
- Complete cold states and within-run fixed points prove the new natural run-5
  stop, NORMAL observation and an inductive uncapped quiet suffix.
- The old exact and V-return references are rerun with the new coordinator.
  Erasing only new coordinator metadata gives **identical semantic states** to
  their selected old cold histories. Both keep the run-5 stop and observations.
- A universal old-guard-to-new-guard bridge lifts the existing exhaustive
  guard-ineligibility checks for the 18 ordinary references and the older
  real-hole/alternating cases. FLOW, MUST and DEMAND actuals remain ineligible.
  The older strict-replay, protected and selected-cleaner gates remain intact.
  The largest retained supplied stop is run-15.
- The new status references only existing C2 queries; selection is a filter;
  no query/path/cap change or k-summary archive is introduced. Target accumulation
  is unchanged, including the live run-3 Target before the new run-5 stop.

No claim is made that every future ordinary program terminates or that every
possible partial-return service is recognized. Incomplete closure and whole
cover deliberately keep the ordinary path. The established scope is the
listed examples and the generic local observation-preservation theorem under
its native/closure hypotheses. No whole-engine/JVM/alias equivalence is claimed.

## 8. Validation

```bash
ELAN_TOOLCHAIN=leanprover/lean4:v4.35.0 \
python3 spec/lean/proposals/reply-scoped-point-service-20261116/check.py \
  --out /tmp/reply-scoped-proofs

./core/gradlew -p core :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.ReplyScopedPointServiceNativeTest \
  --tests org.opentaint.dataflow.bidi.UnadmittedFieldCycleTest \
  --tests org.opentaint.dataflow.bidi.ScopedPointServiceNativeTest \
  --tests org.opentaint.dataflow.bidi.UnadmittedReturnCycleTest \
  --tests org.opentaint.dataflow.bidi.CompletePointServiceNativeTest \
  --tests org.opentaint.dataflow.bidi.ConcreteQueryExclusionsTest \
  --tests org.opentaint.dataflow.bidi.ExcludedHeadAdmissionTest --offline
```

The proof audit passes **152 new constructive claims; 5,918 cumulative claims
in 303 source-hash-checked modules**. Only `propext` and `Quot.sound` occur
in the new proof dependencies; no classical choice or custom axiom is used.

All **46 native component/control tests pass**, including eight new reply-scope
controls. The full-program diagnostic remains unchanged at run-31/POLICY,
with zero NORMAL reports; the new proposal reference retains its NORMAL
observation at run-5. These tests do not install NE/completion in production
or prove full-engine equivalence. Compiled proofs, full captures and test XML
are outside the repository under
`/drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/reply-scoped-point-service-20261116/`.

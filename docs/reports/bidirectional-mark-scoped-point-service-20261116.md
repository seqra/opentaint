# Complete NORMAL return service per full mark

16 November 2026. Synthetic data-flow reachability. FULL mode.
[Consolidated approach](../design/bidirectional-demand-termination-approach-20261115.md).
Follow [proof-guide.md](../../spec/proof-guide.md). Production is unchanged.

The [unadmitted V-return example](bidirectional-unadmitted-return-nontermination-20261116.md)
now stops naturally at **run-5**, with its NORMAL observation retained from
**run-3**. If the new completion flag becomes usable only after handoff,
it stops at **run-7**. Both results have constructive uncapped quiet-suffix
proofs. The older examples retain their results, latest **run-15**.
The unchanged native full-program diagnostic still reaches **run-31**.

## 1. Selected change

| Part | Previous approach | New approach |
|---|---|---|
| Internal NORMAL closure | Must cover every relevant instruction, rule, CFG and child effect | Unchanged; do not remove other marks from this closure |
| Whole return completion | Every raw return needs admitted NORMAL service | Keep this certificate and its existing use |
| Additional return completion | An unadmitted V return blocks all completion | A U certificate needs every real U return covered; V needs its own certificate |
| Current reply delivery | A complete whole-point service can omit a shorter-STAR DEMAND return | Also allow the matching full-output-mark certificate, after its NORMAL service applies |
| Metadata | Whole-query completion state | Add sparse completion flags for existing admitted NORMAL return-mark groups |
| C2, C5, field transfer, marks, caps, H, Target | Existing selected rules | Unchanged |

This is a **major change to current DEMAND return delivery**. It can remove
intermediate candidates. It does not infer that h/U geometrically covers
root MAY/U. It proves that h/U is the complete real U return service for
the supplied exact point. It adds no initial, summary, propagated field,
cap exception, mark assignment or source permission.

## 2. Certificate

Use the previous exact-point eligibility: restricted forward FULL, NORMAL
concrete EXACT actual, Empty E/mx and plain H. The initial must already
exist under C2. The owner, form/rule revision, direction and physical
entry/return ports remain part of its scope.

Let R be the **full**, uncut, mode-stable internal transfer relation. Let
C be the already computed NORMAL states for initial I. Let c be a raw
return, and N be existing admitted NORMAL summary service.

```text
Closed(I,C) :=
    seed(I) in C
    and forall s in C: R(s) subset C

Complete(I, returnPort, base, fullMark U, H=false) :=
    Closed(I,C)
    and a real U return exists
    and forall return c in C with this port/base/full mark/H:
          exists n in N: NativeWholeReturnCover(n,c,I)
```

Keep the previous adapter's conservative unsupported-operation and plain
support checks. An unfinished instruction, internal/global cut, unclosed
child dependency or unsupported operation prevents closure. Queue empty
alone is insufficient. This proposal adds no new transfer-completeness
adapter for ND, negative conditions, cleaners, aliases or opaque effects.

The first concrete adapter remains the fully analyzed leaf body with
ordinary allocation/return and positive unary mark conditions. In that
body, the reference enumerates its finite raw returns to check closure
and service. This is not permission to rerun unbounded transfer in production.

Only the **terminal coverage obligation** is projected. Internal V states
must still be processed. For example:

```text
I -> internal V state -> returned U
```

The V state belongs to C. Dropping it makes closure fail. Missing NORMAL
service for the resulting U also makes the U certificate fail. The Lean
controls check both failures.

A whole-point certificate remains stronger and can be used as before.
The new sparse flags are needed only when whole completion is unavailable.
The new path requires a positive NORMAL return group; it adds no new
negative-result cache. The previous whole no-return certificate is retained.

## 3. Delivery and calls

```text
handleCurrentReturnReply(context, actual, reply):
    // Keep the selected call policy and all native matching.
    replaySavedNORMALFirst(actual, context)
    applyCurrentNORMALAsUsual(actual, context)

    wholeReady = valid whole certificate
                 and its whole NORMAL service actually applied here
    markReady = reply has one concrete full mark U
                and valid certificate(I=actual.rawExactKey, port, base, U, H=false)
                and every NORMAL U service row actually applied here

    if oldExactActualAndStrictShorterSTARGuardsHold(actual, reply)
       and reply is plain CURRENT DEMAND return DATA
       and (wholeReady or markReady):
        omit only this reply membership
    else:
        deliver as usual
```

The new certificate cannot be borrowed for V, FLOW, another initial,
caller original, owner, physical continuation, port, revision or H class.
A stored flag is not a native-application receipt. It cannot bypass current
C2 permission. Packed replies must select the applicable scalar mark
memberships before suppression; other memberships remain unchanged.

Keep every NORMAL and protected output, every non-return effect, all
ZERO/Targets, requests, subscriptions and the coarse query's own work.
Saved NORMAL replay remains unchanged. No caller waits for completion.
Already emitted DemandTargets remain emitted; a late certificate can help
the next forward run.

**At calls:** a U-only child certificate is not a complete child transfer
relation. A caller cannot discard V effects when proving its own internal
closure: the caller may convert V into U. Keep the previous full-child
closure requirement, or an independently proved complete native transfer
relation. This proposal adds no cross-call relevance index, suffix evidence
or partial-child closure inference. If that proof is unavailable, retain
ordinary delivery. This conservative fallback can leave other programs
uncertified; no universal termination claim is made.

## 4. Storage and bounded construction

Completion belongs to the existing **query owner/coordinator**, never to
fact equality or MethodEdgeStore. Keep the previous shared closure and
whole-completion state. For a fixed raw I and physical return port/base/H,
add a sparse set of complete full output marks, using existing mark keys:

```text
query I:
    shared NORMAL closure status
    whole completion status
    completeReturnMarks: existing full-mark set representation
```

There is no dense input-mark by output-mark table. A new persisted mark
flag must have an existing admitted NORMAL return group. Invalidate it if
that exact-initial group loses its NORMAL support or its semantic revision
changes. Drop flags dominated by a whole certificate. No NORMAL summary
is retained merely to support a flag.

Use one bounded pass over the already owned NORMAL boundary states after
the query, its required dependencies and its NORMAL provider basis are
quiescent. Reuse the previous whole-completion coverage pass:

```text
at owner/dependency/NORMAL-basis quiescence:
    present = {}; bad = {}
    sharedClosure = existing complete-body check
    for each already owned raw NORMAL return state c in C:
        present += class(c)                 // full mark, port, base, H
        if no cover exists in the final admitted NORMAL basis:
            bad += class(c)
    if sharedClosure is valid:
        complete = existingNORMALReturnClasses intersect present minus bad
        retain only classes not dominated by whole completion
    else:
        complete = {}
    discard temporary present/bad sets
```

Every raw return must be checked, including one that produced no summary.
Do not certify from only successful publication callbacks. Use the final
NORMAL basis: a transient early cover miss can be covered by a later NORMAL
provider. A sticky early-failure bit is conservative but is not equivalent
to the checked final-pass algorithm. The sets contain output-class identifiers,
**not raw edges or field suffixes**.
They are local to an already owned query and do not propagate to callers.
Their transient size is bounded by distinct output classes already observed
for that query. Persisted additional flags are bounded by existing NORMAL
return-group memberships. These bounds can grow with real analysis state;
they are not constant-space claims.

The reference predicate scans raw returns per selected mark. The checked
grouped predicate uses `present` and `bad` membership and is equivalent.
For R return leaves and K existing classes, grouping removes the K repeated
scans: O(R + K) class operations after native cover results are known, with
normal set/index lookup costs. Cover/path hashing still has its existing
cost. Use the current summary indexes and mark-set representation; no mark
census, rule specialization or global MarkTable enumeration is introduced.

The finite proof model stores explicit lists for checking. Production must
reuse existing processed boundary states and NORMAL cover indexes; it must
not build an unrestricted summary archive or run a second precise analyzer.
If the required raw boundary state or complete transfer adapter is unavailable,
do not certify. This is the same ownership/closure obligation as before.

## 5. New example: current versus new

The code and six rules are unchanged:

```java
class Box { Box f; Box g; Box h; Box k; Box s; }
// Entry marking: T only at a.f.g.$.
void root(Box a) {
    Box x = make(a);
    Box y = make(x);
    Box z = make(y);
    // Observe CM(z.M,U).
}
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.MUST.
    // CM(p.M,T)       => assign U to r.h.MUST.
    // CM(p.f.g.g.M,U) => assign T to r.MUST.
    // CM(p.M,U)       => assign T to r.h.MUST.
    // CM(p.M,T)       => assign V to r.k.MUST.
    // CM(p.s.M,V)     => assign U to r.h.MUST.
    return r;
}
```

At run-3 the already owned p.f.g.$/T,N query has these raw NORMAL returns:

```text
p.f.g.$/T -> ret.h.MUST/U,N    // admitted
p.f.g.$/T -> ret.k.MUST/V,N    // rejected by paired C5 as before
```

The full NORMAL closure contains both returns. Its complete U projection
has only h/U, with admitted NORMAL support. No V certificate is granted.
The old whole certificate remains false.

```text
Before: missing V service -> no completion -> coarse ret.M/U,D delivered
New:    complete U service applied -> coarse ret.M/U,D omitted for this exact actual
        V delivery, C5 and all other effects unchanged
```

The NORMAL h/U -> h/T -> h/U route still reaches the observation. The
fictitious root-MAY chain no longer reaches it. The V return is still absent
from current and persisted summary storage. The helper does not preserve
an unrestricted V edge to obtain this result.

| Run | Before: demand rows | New: rows | NORMAL records | Whole flags / additional mark flags | Root state |
|---|---:|---:|---:|---:|---|
| run-1 | 6 | 6 | 0 | 0 / 0 | DemandTarget |
| run-2 | 16 | 16 | 0 | 0 / 0 | source permission |
| run-3 | 26 | 7 | 6 | 1 / 2 | NORMAL observation, no fresh DemandTarget |
| run-4 | 42 | 0 | 6 | 1 / 2 | inactive |
| run-5 | 44 | 0 | 6 | 1 / 2 | natural stop |

The additional flags are `(p.f.g.$/T, U)` and `(p.h.$/T, U)`. They reference
existing exact queries and NORMAL U groups. The old whole flag for p.h.$/U
remains. No query or field limit is extended.

With mark-scoped readiness delayed until handoff, run-3 retains its early
DemandTarget and 26 rows; run-4 has 42 rows; run-5 has seven rows and no
fresh DemandTarget; run-6 is inactive and run-7 naturally stops. The NORMAL
observation remains. This is a separate checked cold history, not Target
cancellation or a dependency on favorable callback order.

[Complete per-block traces](bidirectional-mark-scoped-point-service-trace-20261116.md).

## 6. Proofs, old cases and limits

[Constructive Lean package](../../spec/lean/proposals/mark-scoped-point-service-20261116/README.md):

1. The full NORMAL closure remains unprojected. Projecting only the return
   predicate gives an existing NORMAL witness for every real selected-mark
   return. Native application of these witnesses preserves any corresponding
   continuation observation. Other-mark replies are not selected for removal.
2. The leaf adapter instantiates this theorem with the unchanged six-rule
   body. An unadmitted V result does not block U, while missing U, partial
   uniform coverage, wrong-initial or DEMAND support does block it.
3. A receipt requires every selected NORMAL service to have actually applied.
   NORMAL, protected and FLOW replies retain their previous behavior.
4. Complete cold states, within-run fixed points and inductive uncapped quiet
   suffixes establish the run-5 stop and the delayed run-7 stop.
5. Grouped failure-set membership equals the reference per-mark scan.
   New flags reference already owned queries and existing NORMAL groups.
6. In every older single-output-mark generator family, a successful projected
   check already proves the previous whole certificate. Thus this extension
   adds **no flags**, for any query and admitted store. This covers the old
   exact, real-exclusion, deeper-hole and alternating-generator references.
   Old FLOW-only queries are ineligible, and strict MUST actuals keep their
   previous guards. The earlier field-flow, replay, protected and cleaner
   proofs remain applicable; their largest selected natural stop is run-15.

All field admission, transfer and C5 definitions stay unchanged. Every
ordinary initial keeps both global and FL(own Dc)+1 bounds; every published
result keeps min(global,FL(own Dp)+1). The older sole NORMAL-MUST/real-E
entry-cap exception remains separately enumerated in the consolidated
proposal. This repair adds **zero** exceptions and uses none in this case.

These are scoped reference results, not a proof of universal termination,
project performance, complete JVM/alias modeling or whole-engine equivalence.
The strong-closure and native whole-cover adapters remain eligibility
requirements. Other-mark internal dependencies cannot be skipped to make
a certificate succeed.

Validation: **114 new constructive claims; 5,589 cumulative audited claims
in 284 source-hash-checked modules; 35 native component/control tests pass**.
Only `propext` and `Quot.sound` occur in the new proof dependencies.

## 7. Reproduction and native controls

```bash
ELAN_TOOLCHAIN=leanprover/lean4:v4.35.0 \
python3 spec/lean/proposals/mark-scoped-point-service-20261116/check.py \
  --out /tmp/mark-scoped-point-proofs

./core/gradlew -p core :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.ScopedPointServiceNativeTest \
  --tests org.opentaint.dataflow.bidi.UnadmittedReturnCycleTest \
  --tests org.opentaint.dataflow.bidi.CompletePointServiceNativeTest \
  --tests org.opentaint.dataflow.bidi.ConcreteQueryExclusionsTest \
  --tests org.opentaint.dataflow.bidi.ExcludedHeadAdmissionTest --console=plain
```

The six new adapter tests use native rule transfer, C5 and reply application.
They check positive U completion despite discarded V, missing same-mark and
uniform service, unfinished/DEMAND work, receipts, unrelated output marks,
FLOW, H, original support, owner, ports, revision and mode. The previous
native controls remain unchanged.

The unchanged full-program native diagnostic still reaches **run-31/POLICY**,
with zero NORMAL reports. The scalar reference has its NORMAL observation
at run-3. This inherited alignment gap remains explicit; these component
tests do not claim integration of the entire NE/completion proposal.
All compiled artifacts and full captures remain outside the repository.

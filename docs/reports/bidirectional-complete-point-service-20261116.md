# Complete NORMAL return service for an existing exact query

16 November 2026. Synthetic data-flow reachability. FULL mode.
[Consolidated proposal](../design/bidirectional-demand-termination-approach-20261115.md).
Production is unchanged. Follow [proof-guide.md](../../spec/proof-guide.md).

The new exact-input example now stops naturally at **run-5** in the checked
reference. It keeps its NORMAL observation from **run-3**. With completion
made available only at the next handoff, it stops at **run-7** instead.
Both results have constructive uncapped quiet-suffix proofs. The former
policy repeats run-9/run-10 forever; the unchanged native diagnostic still
reaches **run-31**. These are different executables and must not be confused. The unchanged
native fixture still records **zero NORMAL reports at run-31/POLICY**,
whereas the scalar reference has a NORMAL observation at run-3. That
previously documented report-count alignment gap is not fixed by this
proposal or the component tests.

## Change

An exact query can already know every return effect of one exact marked
point. A shorter STAR query can still emit an additional DEMAND reply for
that same actual. The existing coverage rule cannot remove that reply if
its root MAY is larger than the exact query's NORMAL child result.

**New delivery rule:** omit a shorter-STAR CURRENT DEMAND return reply only
when a complete NORMAL service for this exact actual is certified and all
of that service has already passed ordinary native application at this
continuation. Do not shape-subsume the two summaries.

This is a **major semantic change to current return delivery**. It can
remove intermediate candidates and demand. It preserves every reachable
return observation within the certified transfer scope. It adds no C2
start, field path, companion, input-cap exception or source permission.
It does not change the instruction transfer, C5, summary normalization,
saved replay, H, real E, static handling, or Target rules.

## 1. Executable completeness certificate

Let I be an **already owned** NORMAL concrete EXACT initial with Empty E/mx
and plain H. Let R be the method/block's mode-stable strong transfer
relation for I. R includes every relevant CFG, rule and boundary operation
and every normal/exceptional port that can reach the selected return.
Let C be its existing NORMAL states. No extra analysis is run to construct C.
Let N be existing admitted NORMAL return services for I.

```text
Complete(I,C,N) :=
    seed(I) in C
    and forall s in C: R(s) subset C
    and forall return c in C:
          exists n in N: NativeWholeReturnCover(n,c,I)
```

Coverage must include the complete mark/path/port/literal-H result. One
NORMAL child is insufficient. A lost C5 return invalidates completion.
An empty return set needs this explicit certificate too; no rows alone
prove nothing. No information from the next iteration is used.

A practical sufficient check is deliberately conservative:

```text
on an already owned point query I:
    dirty = false
    process the existing work as usual
    dirty |= unsupported transfer or unclosed CFG/rule dependency
    dirty |= a real cut or an uncovered DEMAND transfer result
    dirty |= an unfinished child, opaque effect, or incomplete boundary service
    dirty |= a raw return with no admitted NORMAL native whole-result cover

at owner/dependency quiescence:
    if not dirty and NORMAL closure is certified:
        mark existing I as complete
```

Queue empty by itself is insufficient. The first supported instantiation
is the supplied leaf body with unary positive mark conditions and ordinary
allocation/return. ND interaction, negative conditions, cleaners, statics,
alias-dependent effects and unresolved bodies have **no new completeness
adapter** here. Such a dependency leaves the query uncertified. Existing
analysis continues. This is a sufficient optimization, not a requirement
that the owner perform a second precise analysis.

The closure proof also permits ordinary calls: use a completed child NORMAL
service in R, then certify the caller from its already computed states.
There is no cyclic self-certification. A child service must already have a
closed proof. The generic composition theorem is checked; a production
call/alias/IR completeness adapter remains future implementation work.

## 2. Publication, persistence and application

Completion belongs to the **query owner/coordinator**, keyed by the existing
raw initial, form/rule revision, direction and physical entry/return ports.
It is not a fact annotation. MethodEdgeStore and ordinary fact equality
stay unchanged. No GroundingSupport is introduced.

Keep only a completion bit/state and references to existing NORMAL service
rows. Do not copy the intra-procedural states or retain discarded raw
candidates. The reference model explicitly enumerates its finite support
for checking; an implementation can track a dirty bit and outstanding
work, then use existing NORMAL service handles.

A completed service remains valid at larger field limits because its
certificate closes the **uncut, mode-stable** transfer relation, rather
than just the current restricted worklist. Invalidate it when the method,
rules, ports or supported transfer semantics change. When NORMAL storage
compacts supporting rows, revalidate against the proven covering basis;
otherwise invalidate completion. Never keep otherwise redundant rows
merely to make this optimization succeed.

```text
handleCallOrBlockReply(context, originalActual, currentReply):
    replaySavedNORMALAsUsual(originalActual, context)
    deliverCurrentNORMALAsUsual(originalActual, context)

    cert = owner.completedReturnService(originalActual.rawExactKey)
    ready = cert is valid
            and every cert service row actually passed native application
                for originalActual at this same physical continuation

    if forward FULL and run >= 3
       and originalActual is NORMAL concrete EXACT, Empty E/mx, plain H
       and currentReply is plain DEMAND return DATA
       and currentReply.initial.tail == STAR
       and currentReply.initial.path is a strict prefix of originalActual.path
       and ready:
        omit only this CURRENT DEMAND return reply
    else:
        apply currentReply as usual
```

The delivery receipt is temporary for this reply/continuation. It cannot
be borrowed from another original, caller stage or physical port. A stored
certificate without this receipt does not bypass C2 permission for current
NORMAL application. Saved NORMAL replay stays first and unchanged.

Keep every NORMAL result, every protected result, static/other DATA effects,
ZERO/Targets, requests, subscriptions, and the coarse query's own work.
Do not delete its summary from the method store. A MAY/NE/STAR/MUST actual,
a DEMAND actual, backward delivery, GROUP and run-1 use ordinary handling.
No extra exact query is generated when an existing one is unavailable.

Already emitted DemandTargets remain emitted. If completion is too late
in this run, retain the candidate and use completion on a later forward
run. No global barrier or waiting caller queue is needed.

## 3. The new example

```java
class Box { Box f; Box g; Box h; }
// Entry rule: mark T only at a.f.g.$.
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
    // Symmetric U -> T rules.
    return r;
}
```

At run-3, the qualified demand already admits p.f.g.$/T,N under both
ordinary caps. Its complete unbounded return service is:

```text
p.f.g.$/T -> ret.h.MUST/U,N
```

The deeper guard cannot match an exact mark at p.f.g. No return effect was
cut or discarded by C5. The coarse p.f.*/T,D query still emits ret.M/U,D.
It is stored, but its reply to this exact actual is omitted after the
complete NORMAL h service is applied. The latter is the **entire** answer
for that point, not a geometrical cover of root MAY.

The next call receives x.h.MUST/U,N. Its native uniform query and the
retained uniform-coverage law handle the h service normally. The final
z.h.MUST/U,N produces the valid NORMAL observation. No fictitious root-MAY
chain reaches it. There is no new source or rule transfer.

| Run | Earlier policy: qualified rows | Ready service: rows / NORMAL records / completed keys | DemandTarget / NORMAL observation |
|---|---:|---:|---|
| run-1 | 4 | 4 / 0 / 0 | yes / no |
| run-2 | 14 | 14 / 0 / 0 | backward / no |
| run-3 | 26 | 7 / 6 / 3 | no / yes |
| run-4 | 42 | 0 / 6 / 3 | inactive / retained |
| run-5 | 44 | 0 / 6 / 3 | natural stop / retained |

The three completion keys are the existing exact points p.f.g.$/T,
p.h.$/U and p.h.$/T. No field exceeds its cap. Seven unconsumed method
DEMAND rows at run-3 are not evidence of a reachable root Target.
The ordinary controller makes no backward observation seed and reaches
its quiet state. No demand row is declared redundant from repetition alone.

[Full per-block run trace](bidirectional-complete-point-service-trace-20261116.md).

If completion is usable only from the previous handoff:

| Run | Rows | NORMAL records | Completed keys | Root DemandTarget |
|---|---:|---:|---:|---|
| run-3 | 26 | 6 | 3 | retained |
| run-4 | 42 | 6 | 3 | backward permission |
| run-5 | 7 | 10 | 3 | none |
| run-6 | 0 | 10 | 3 | inactive |
| run-7 | 0 | 10 | 3 | natural stop |

This separate cold proof includes within-run Target accumulation. It does
not erase run-3's Target when completion becomes available.

## 4. Proofs and scope

[Constructive Lean package](../../spec/lean/proposals/complete-point-service-20261116/README.md):

1. Reachability induction through a checked finite NORMAL closure covers
   every reachable return. The witness is an existing admitted NORMAL row.
2. Applying that witness preserves any continuation observation covered by
   native whole-return service. This justifies removal of the coarse return
   approximation for this actual. It does not claim root MAY is covered by h.
3. The leaf body instantiates the closure with every literal unary rule
   transfer. Missing, demanded or wrong-initial service rows reject.
4. The current-delivery receipt requires every NORMAL service result to
   have actually applied. NORMAL/protected replies cannot be pruned.
5. Complete cold states, each within-run fixed point and an uncapped quiet
   suffix prove the new run-5 and delayed run-7 stops. No hard limit is used.
6. The 18 older multi-owner field-flow histories prepare only abstract
   initial keys, so none can create the new concrete-point completion.
   This checks prepared work, including unreturned or later compacted keys.
   The three earlier conditional histories admit no eligible deletion even
   with maximal readiness; a subset lemma covers their earlier delivery
   events. Existing stop/observation proofs remain applicable. The three
   strict replay cases use MUST actuals and are ineligible; H and the
   selected cleaner policy retain their earlier controls.

The earlier largest natural stop remains **run-15**. This does not prove
termination for every program, full-engine equivalence, or project speed.
The fully closed transfer adapter is part of the eligibility contract.
Extending it to another operation requires its native completeness proof.

## 5. Field/work bounds

```text
New queries, propagated field paths, summary rows created by the rule: 0
New input-cap exceptions:                                         0
New output-cap exceptions:                                        0
Completion keys <= distinct eligible exact-query keys already owned over this scan
Reply selection output subset native current replies
```

The older **sole** input-cap exception remains restricted forward FULL
concrete MAY/NE, NORMAL MUST actual, nonempty real E, already admitted
shorter Empty-E STAR at the same base. It replaces that start and its
existing FLOW companion with the submitted head/E. It remains global-cap
bounded. It is not extended to EXACT, Empty E, STAR or DEMAND actuals.
All output summaries still obey min(global,FL(own Dp)+1).

The executable list checker costs O(states + native transitions + return
service checks), with list membership overhead in the proof reference.
An implementation should reuse processed-state membership, dirty flags
and existing NORMAL cover indexes. It must not rerun strong transfer or
enumerate concrete suffixes at call sites to obtain a certificate.

Per delivery, reuse the NORMAL application already required by the call
policy and record its service receipt. Certificate lookup can be a query-key
lookup. Work for applying its rows is the existing NORMAL application cost;
pruning adds a key/shape test per candidate. Do not scan every method query
for every caller. No original-by-mark-by-path table or new retained offered
fact set is required. These metadata keys can grow with the distinct owned queries across runs;
there is no constant-space or universal query-count claim. The proposal does
not bound total later work for methods which remain ineligible.

## 6. Reproduction

```bash
ELAN_TOOLCHAIN=leanprover/lean4:v4.35.0 \
python3 spec/lean/proposals/complete-point-service-20261116/check.py \
  --out /tmp/complete-point-proofs

./core/gradlew -p core :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.CompletePointServiceNativeTest \
  --tests org.opentaint.dataflow.bidi.ExactInputGuardCycleTest \
  --tests org.opentaint.dataflow.bidi.ExcludedHeadAdmissionTest \
  --tests org.opentaint.dataflow.bidi.ConcreteQueryExclusionsTest --console=plain
```

**Validation: 144 new constructive claims; 5,304 cumulative audited claims in
267 modules. All 28 selected native component/control tests pass.**

The new native adapter checks exact guard rejection, complete raw-return
coverage, lost/unfinished/wrong C5 support, native NORMAL reply application,
mode/layer/port/revision guards, H, and existing bounded C2 admission.
The complete proposal, including NE, is not installed in production. The
native full-program run-31 diagnostic is intentionally unchanged.

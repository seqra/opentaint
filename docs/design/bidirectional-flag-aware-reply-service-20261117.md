# Complete NORMAL service within each protection flag

17 November 2026. Synthetic data-flow reachability. FULL marks.
Follow [proof-guide.md](../../spec/proof-guide.md). Production is unchanged.
[Consolidated approach](bidirectional-demand-termination-approach-20261115.md).

The later [native-bound service](bidirectional-native-bound-reply-service-20261117.md)
adds a separate path for protected caller inputs and exact/same-head
premises. This document retains the guards and validation of the earlier
same-H path. Those guards do not restrict the later path.

The [protected relevant-return example](../reports/bidirectional-relevant-protected-return-nontermination-20261117.md)
now naturally stops at **run-5**, retaining its NORMAL observation. Its
previous complete run-9/run-10 cycle is closed. Earlier exact, mark, h-read
and unrelated protected-return histories remain unchanged in the checked
cold prefix. Older references retain their results, latest **run-15**.

## 1. Selected semantic change

This is a **major change to current DEMAND return delivery**. A protected
coarse return may now be omitted for one actual input after a complete
NORMAL answer has been applied in that context. It is not storage subsumption.

| Part | Before | After |
|---|---|---|
| Protected current DEMAND reply | Always delivered | May be selected by complete same-flag NORMAL service |
| Terminal coverage | Every overlapping return must be plain | Select overlapping returns of this reply's literal H class |
| Full internal closure | All states must be NORMAL; retain both H classes | Unchanged; do not project internal states or transitions |
| Wrong-H service | Cannot cover a return | Unchanged; never borrow another flag's provider or receipt |
| Stored protected/plain copies; NORMAL outputs | Kept separately | Unchanged; neither copy is removed or relabeled |
| C2/C5, transfers, caps, saved replay, Targets | Selected current rules | Unchanged |

The new check applies to either flag. Existing whole/mark/plain-reply checks
remain fast paths. A protected original remains a conservative fallback.
No other activation boundary is widened.

## 2. Certificate

Use the existing forward FULL run >= 3 guard: an already owned concrete
EXACT query I, a NORMAL actual with Empty E/mx, and a plain original. The
current DEMAND concrete return must have a strict shorter-prefix STAR premise.

```text
C = all existing processed states for I, including both literal H classes
R = the full uncut, mode-stable strong transfer relation
N = admitted NORMAL service for I and the same physical return boundary

ClosedNORMAL(I,C) :=
    seed(I) in C
    and forall s in C: s.layer == NORMAL and R(s) subset C

Selected(c,reply) :=
    c.H == reply.H and possibleRegion(c) overlaps possibleRegion(reply)

CompleteReply(I,reply) :=
    ClosedNORMAL(I,C)
    and forall real return c in C where Selected(c,reply):
        a row in N covers the WHOLE c, including its exact H
        and that whole NORMAL image actually applied to this original
            at this continuation, revision and physical ports
```

Other-H terminal returns do not establish or refute service for this flag.
They remain in C. Any internal/global cut, DEMAND state, unfinished child,
unclosed dependency or unsupported effect still blocks full closure.
Internal transitions can change H; therefore internal flag projection is invalid.
An empty selected region is checked on demand, without a negative cache.

Retain the conservative supported leaf adapter. Do not infer complete child
transfer from a reply-specific certificate. Existing ND/negative/cleaner/
static/alias/opaque fallback boundaries remain. No new adapter for these
operations is claimed here.

```text
onCurrentReply(actual, original, row, reply):
    apply saved NORMAL service first
    apply admitted current NORMAL service
    if an existing fast path selects reply: omit this delivery; return
    if not existingExactActualAndStrictPrefixGuards(actual, row, reply): deliver; return
    if original.H != 0: deliver; return
    if not owner.currentClosedNORMAL(actual.rawExactKey): deliver; return
    for c in owner.processedReturns(actual.rawExactKey):
        if c.H == reply.H and possibleOverlap(c, ownerSideRegion(reply)):
            require whole admitted NORMAL service with c's exact H
            require its actual native NORMAL image in this same context
            otherwise: deliver; return
    omit only this current DEMAND reply membership
```

The formal model reuses the old Boolean shape guard by testing a temporary
copy with H=false. This copy is never applied, stored or published. An
implementation can extract a common shape predicate instead. The real
reply and every provider retain their literal H.

## 3. Example and effect

```java
// Entry marking: T only at a.f.g.$.
void root(Box a) {
    Box x=make(a).h;
    Box y=make(x).h;
    Box z=make(y).h;
    // Observe CM(z.M,T).
}
Box make(Box p) {
    Box r=new Box();
    // CM(p.f.g.g.M,T) => assign T to r.h.MUST.   // H=1
    // CM(p.M,T)       => assign T to r.h.h.MUST. // H=1
    return r;
}
```

For actual p.f.g.$/T,N, the complete body returns ret.h.h.MUST/T,N,H=1.
Its deep check is false. That whole protected NORMAL answer is admitted
and applied. The coarse p.f.*/T query also publishes ret.h.M/T,D,H=1.
Before, its protection blocked selection. Now its same-flag complete
service proves that the actual has only the h.h result. Omit the coarse
current delivery, retain the stored row and the NORMAL result. The caller
keeps x.h.MUST/T,N,H=1; no root-MAY approximation is renewed by that delivery.

| Run | Prior helper demand rows | Updated rows | NORMAL records | Current closure keys |
|---|---:|---:|---:|---:|
| run-1 | 2 | 2 | 0 | 0 |
| run-2 | 3 | 3 | 0 | 0 |
| run-3 | 8 | 3 | 1 | 1 |
| run-4 | 22 | 11 | 1 | 0 |
| run-5 | 23 | 0 | 6 | 2 |

The run-3 DemandTarget stays emitted. Run-5 produces no new DemandTarget
and retains the NORMAL observation. An inductive quiet suffix starts at
run-6. [Complete per-block trace](../reports/bidirectional-flag-aware-reply-service-trace-20261117.md).

## 4. Work, storage and field limits

Add no query, summary, input cache, region cache, suffix evidence or raw
summary archive. Read the existing original H at delivery; do not add H to
query equality or MethodEdgeStore. The only current status remains the
existing owner-local full-closure status. Use scalar flag memberships or
the equivalent existing packed masks; a nonempty packet protection mask
must not classify every leaf as protected.

For B eligible replies and R existing return memberships, the conservative
scan is O(B*R) overlap/service checks plus native lookup costs. Adding H
comparison is constant work per selected leaf. Reuse ephemeral packet
results; retain no query-by-region table. This selects existing replies;
it does not launch transfer to prove completion. Unsupported or unavailable
owned state uses the ordinary path.

Keep every global, FL(Dc)+1 entry and FL(Dp)+1 output cap. No exception is
added. The selected deeper NORMAL-MUST/real-hole exception remains exactly
as before; this example has Empty E and uses no exception. Future frontier
changes can alter total work; no whole-run speed theorem is claimed.

## 5. Proofs and validation

[Constructive Lean dossier](../../spec/lean/proposals/flag-aware-reply-service-20261117/README.md)
checks **136 new claims; 6,591 cumulative claims in 347 modules**. New proof
dependencies use only the allowed `propext` and `Quot.sound` axioms.

The generic proof keeps full internal closure and constructs a whole NORMAL
witness and actual native receipt for every reachable selected return.
The witness retains H. Wrong-flag providers/receipts, missing service,
DEMAND/unfinished states and protected originals do not pass. NORMAL outputs
are retained. Store membership and path limits are unchanged.

The new complete cold reference stops at run-5, retains its observation and
has an uncapped quiet suffix. Four previous exact/mark/h-read/unrelated
protected references retain identical checked cold states and run-5 stops.
The older ordinary inventories retain their plain replies and old shape
guards; the new check cannot change their results, latest run-15. Existing
unsupported protected/cleaner adapters are not widened by this repair.

All **19 selected native fixture/component tests pass**. These include new
same-flag, mixed-flag, wrong-provider, receipt, scope and direction controls.
The unchanged full-program diagnostic remains **run-31/POLICY** with zero
NORMAL reports; the proposal reference retains its run-5 NORMAL observation.
This inherited model/native difference prevents a whole-engine equivalence
claim. Production is unchanged. These are scoped results, not a universal
termination proof. Continue the counterexample search under term-task.md.

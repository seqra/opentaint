# Proposal: relational loss evidence and focused refinement

**WITHDRAWN — 13 November 2026.** The user rejected full relational
evidence composition across calls. It bypasses the field abstraction in a
second analysis. Sharing expression nodes does not establish a bound on
the distinct composed paths or on coverage work. The call/reference,
evidence-compilation and focused-row pipeline below is historical material,
not an implementation plan.

For example, a helper that wraps its input under either f or g has two
prefix relations. A chain of n calls has up to 2^n distinct composed field
paths. A shared expression may encode that family compactly, but compiling
it into relations recreates the path enumeration. The Lean results below
prove relation identities in a declared model; they do not prove an
acceptable abstraction, memory bound or cost for this analyzer.

Any replacement must respect the native summary boundary. A DEMAND call
cannot export or reconstruct its complete untruncated derivations in the
caller. Missing bounded evidence means that a redundancy check cannot
certify removal; it is not evidence of no flow.

The bounded next candidate is to check an already available raw NORMAL
summary against retained NORMAL subsumers **before C5 can turn it into
a truncated DEMAND**. This uses the current bounded AP candidate and the
existing NORMAL basis, with no cross-call evidence arena. Its native
guidance-preservation proof is still required. It addresses redundant
re-cutting only; the intrinsic STAR-to-MAY repetition remains unresolved.
No replacement whole-core progress or termination theorem is claimed.

13 November 2026. Proposed algorithm under
[proof-guide.md](../../spec/proof-guide.md). No production change.
Field bans are not part of this design.

## 1. Proposed change

Currently a loss leaves a coarse AP edge and discards its input/output
field correlation. The next run repeats the query for that coarse edge.

Retain the lost relation as evidence. At handoff, compare that evidence
with retained NORMAL summaries. Remove covered demand contributions.
For uncovered contributions, request analysis of their precise entry and
exit paths instead of repeating only the broad query.

Start with neutral nonstatic FLOW and empty E/mx, then its unprotected
diagonal FULL T transfers. Unmodelled rules, ND, protected effects and
statics remain OPEN. The first version handles finite acyclic evidence.

This changes demand generation and retirement. Ordinary AP transfer,
layers, fact equality, protection, C2/C5 tables, source/sink rules and
saved-summary-first replay remain unchanged. C2/C5 receive additional,
more specific guidance rows. No new initial tail or fabricated NORMAL
summary is introduced. The whole-core convergence guarantee remains open
until unsupported classes have their own refinement/closure rules.

## 2. Stored state and evidence construction

An evidence alternative is a conditional prefix relation:

```text
(P,Q): for every suffix s, input P.s can produce output Q.s

read f:   (x.f, y)
write f:  (y, x.f)
```

Keep the full owner/context, ports, direction, bases, mark relation and
protection class as well. The analyzer's refinement planner owns an arena:

```text
Atom(supported AP prefix transfer)
Union(alternatives)
Compose(first, second)
Cut(child)                // retains the relation BEFORE the cut
Open(reason)              // an unsupported or incomplete contribution
```

Start at a precision loss. A preceding NORMAL STAR/STAR FLOW edge gives
its existing correlated prefix relation. Compose the lossy operation and
later supported transfers with it. For a NORMAL candidate about to be cut,
retain its uncut relation. A NORMAL MUST candidate needs a uniform-image
certificate: retained NORMAL replay on its MUST premise must produce a
covering NORMAL uniform result. Do not silently reinterpret MUST as STAR.

The arena does not change MethodEdgeStore keys, membership or layers.
It records positional transformations, not whether an actual input grounds
a rule. This does not restore grounding support.

Merge every contribution by Union, even if ordinary fact deduplication
rejects its duplicate. When compaction absorbs an edge, join its evidence
to the coverer's evidence. One Open origin prevents aggregate retirement.
Use shared equation nodes referencing their input nodes; evidence updates
do not re-enqueue AP facts. Freeze the arena at a completed handoff.
Unsupported or unclosed cyclic equations become Open.

This is new proof data beyond the old edge-history campaign. Producer and
merge hooks must establish completeness. Do not reconstruct completeness
from final summary shapes. Hash-cons nodes, retain evidence reachable from
outstanding losses, and measure the cost; no memory benefit is claimed.

## 3. Explicit operations

For `R=(P,Q)` followed by `T=(A,B)`:

```text
if Q = A.v: compose(R,T) = (P,   B.v)
if A = Q.v: compose(R,T) = (P.v, B)
otherwise:  there is no point flow through this composition
```

Thus reading f then g computes `(p.f.g,ret)`, even when the public edge
is `p.* -> ret.MAY`.

For retained NORMAL `S=(A,B)` and required evidence `R=(P,Q)`:

```text
normalCovers(X,S,R):
    require compatible supported class, owner, ports, bases and mark
    v = stripPrefix(A, P)
    require v exists AND Q == B.v
    if S.premise is strictly below X.publicPremise:
        require S has an opposite-direction native view for this run
    return true
```

Check against the final retained NORMAL basis, in the correct native
direction view. Retired demands are not providers. Every finite evidence
alternative must pass. This is a prefix comparison, not a future-run oracle.

The direction check preserves the existing STAR-inside policy. An opposite
view can still carry a broad STAR offer through the known guarded relation.
A same-direction guarded record alone cannot justify removing that route.
For the example, the forward reader is supplied by its backward NORMAL
record; the backward writer is supplied by its forward NORMAL record.

### 3.1 Method calls

Keep callee evidence method-relative: its endpoints use the callee's
formal arguments, receiver and exits. Do not send caller evidence into
the callee as an additional input fact or instantiate callee evidence per
caller. Existing C2 admission and initial emission stay unchanged.

Across the complete call, build evidence with the same entry and exit
bindings as ordinary propagation:

```text
E_after = Compose(E_before, BindInput, E_summary, BindOutput)

E_summary = Atom(native summary relation)    for a supported NORMAL row
          = SummaryRef(calleeEvidenceHandle) for a supported DEMAND row
          = Open                            for an unsupported row
```

Use the actual call-plan stages for the bindings, rather than inventing
another projection. Formal arguments bind to actual arguments, the
receiver to the actual receiver, and the return to the result location.
A summary conclusion on a mutable argument binds back to that argument;
it is not forced through the return variable. Preserve normal/exceptional
ports and the existing summary direction view.

```text
onCallStageResult(stage, inputEdge, row, resultEdge):
    effect = supported binding stage
        ? Atom(stage.binding)
        : callee stage with supported NORMAL row
          ? Atom(row.nativeView)
          : callee stage with supported DEMAND row
            ? SummaryRef(row.evidenceHandle)
            : supportedStageEvidenceOrOpen(stage, row)
    evidence[resultEdge] |= Compose(evidenceOf(inputEdge), effect)
```

The full formula starts before input binding and ends after output binding.
At an internal Callees-stage hook, the earlier binding is already part of
`evidenceOf(inputEdge)`; do not apply it a second time. Each ordinary call
stage contributes exactly once. A supported predefined NORMAL prefix row
can be an atom too; it does not require a callee analyzer or subscription.

`evidenceOf` can start from an existing NORMAL correlated prefix edge if
this call is the first loss. Otherwise use the edge's existing evidence;
an unexplained DEMAND edge becomes Open. Do not start from the observed
coarse output packet, or from a C2 seed substituted for the original offer.
Compose through supported surrounding call stages too. A rule, cleaner,
ND or other unmodelled stage contributes Open; it is not silently bypassed.

For example:

```java
Node get(Node p) {
    return p.f.g;
}
// Method-relative evidence: p.f.g.suffix -> ret.suffix.

Node wrap(Node a) {
    Node x = a.h;              // Evidence: a.h.suffix -> x.suffix.
    Node y = get(x);           // Bind p -> x, ret -> y.
                               // Callee relation: x.f.g.suffix -> y.suffix.
                               // Compose: a.h.f.g.suffix -> y.suffix.
    return y;
}
// Caller evidence: a.h.f.g.suffix -> ret.suffix.
```

This preserves the h/f/g correlation even when the public facts are MAY.
A NORMAL callee row does not erase an earlier caller loss. Nor does it
automatically count as a same-owner NORMAL provider for wrap: retirement
still checks wrap's complete composed relation and the native adapter.

`SummaryRef` is a shared, versioned arena handle, not a copied callee
graph. Each call site has its own binding node; all sites can reference
the same formal callee evidence. Callers cannot mutate that evidence.
If several targets, paths or summaries produce the same result, Union
all their contributions before declaring coverage. Joining more callee
origins updates the referenced node, even if the public summary key did
not change. Evidence-only updates do not replay AP facts. Resolve the
final references at the completed-run barrier.

For a not-yet-published summary, retain the ordinary subscription and wait;
absence is not an identity or a redundancy proof. Existing publication
delivery creates actual result edges as usual. A handle must remain valid
when summary compaction removes its old public key; preserve the referenced
origin or a validated redirect. Freeze referenced evidence reachable from
handed-over demands before clearing run-local arenas. A NORMAL record can
be an atom without retaining its complete derivation history.

Backward handling is the same composition in the existing backward call
plan: caller result to callee return, callee backward summary, then formal
arguments back to actual arguments. Do not independently reverse rule or
Target semantics. Recursive reference SCCs are Open in the initial finite
scope. Calls and loop-block boundaries use the same evidence-composition
mechanism with their own existing bindings and ports.

[Calls.lean](../../spec/lean/proposals/demand-progress-20261113/Calls.lean)
checks field-preserving base binding, caller/callee composition, both
return alternatives, separate call-site bases, backward binding order,
Open propagation, Union updates and explicit DEMAND-call resolution.
Run the checker with `--calls` to include these 15 checks:
**180 audited declarations, nine modules**.
Receipt: `demand-progress-20261113/demand-call-proofs-v1/receipt.json` under the
[external archive](../reports/EXTERNAL_DATA.md). These checks cover the
neutral-prefix model, not the native call scheduler or rule stages.

### 3.2 When the callee summary is DEMAND

Preserve two separate results: the ordinary AP output and its evidence.
A supported DEMAND summary keeps the caller output on DEMAND. Resolving
its evidence does not promote that output to NORMAL or change its premise.

```text
caller before call:
    runtime edge: a.h.* -> x.*, NORMAL
    evidence:     a.h.suffix -> x.suffix

callee summary:
    runtime row:  p.* -> ret.MAY, DEMAND
    evidence:     p.f.g.suffix -> ret.suffix

caller after y = get(x):
    runtime edge: a.h.* -> y.MAY, DEMAND
    evidence:     a.h.f.g.suffix -> y.suffix
```

Keep `Compose(E_before, Bind(SummaryRef(S)))`. Do not replace the caller
evidence by the callee evidence, compose only with the coarse MAY head,
or turn the composed evidence into a live NORMAL edge. The guard added
by the callee refines the caller's original input, not its runtime premise.

A cut works the same way:

```text
callee public row: p.* -> ret.f.NE, DEMAND
callee evidence:   p.suffix -> ret.f.g.suffix
caller evidence:   a.h.suffix -> y.f.g.suffix
caller AP output: a.h.* -> y.f.NE, DEMAND
```

If either operand has an unknown contribution, the complete result is
not yet certifiable. Keep the known operands and unresolved reference in
the arena. Do not destructively replace the stored expression with Open.
The same node can resolve when the callee finishes; it need not recreate
or reprocess the AP fact. Known alternatives remain useful for refinement,
but one unknown alternative still prevents aggregate retirement.

At handoff, compare the resolved caller relation against independent
NORMAL providers in the caller scope. A DEMAND summary is not a NORMAL
provider for itself, and complete evidence alone is not a NORMAL witness.
Only successful coverage plus the native adapter can remove the caller's
refinement obligation. Otherwise keep it and generate its focused request.

The opposite case is distinct: a NORMAL callee summary applied to an
already-DEMAND caller input also yields a DEMAND-supported result, but
its callee operand can be an Atom. The existing caller evidence still
participates. Neither case erases an upstream loss.

## 4. Handoff algorithm and refinement requests

For an uncovered `(P,Q)`, create focused analysis requests:

```text
forward:  entry P.MAY, exit Q.STAR
backward: entry Q.MAY, exit P.STAR
```

They retain the real mark relation, scope and ports. They are guidance,
not current-run FLOW effects. The precise entry can address the missing
prefix, and the precise exit avoids the permanently small old root budget.
Existing C2 still checks the actual offer. An ancestor STAR does not gain
permission to satisfy a deeper demand.

```text
handoff(completedRun):
    N = freezeFinalRetainedNormals()
    kept = {}
    focused = {}

    for X in outgoingDemandContributions:
        E = compileFiniteEvidence(frozenEvidence[X])
        if E is Open:
            kept += X
            registerOpenQuestion(X)
            continue

        missing = []
        for R in E:
            if no S in N satisfies normalCovers(X,S,R):
                missing += R

        if missing is empty:
            retire X's contribution
        else:
            kept += X
            for (P,Q) in missing:
                focused += forward/backwardFocus(P,Q,X.scope,X.mark)

    merge ordinary demand from kept with focused requests
    activate newly answerable focused questions
    keep blocked questions subscribed to their upstream losses
```

Retirement is enabled only for a class with a proved native adapter: its
complete evidence covers every possible precise contribution and saved
replay preserves delivery, source permissions and Target routing. The
prefix checker below proves the relation step; it does not establish that
adapter for arbitrary AP operations. Until the adapter is proved, the
algorithm emits candidate certificates without modifying the analyzer.

Focus questions are fair and deduplicated by their full descriptor. A
larger run number alone is not a new question. A blocked focus keeps the
broad relay; it does not justify a negative flow conclusion or an empty
iteration. Refine its upstream loss when the necessary input is still
abstract. All effects still pass through ordinary C2/C5.

## 5. Decisions on the examples

Eventually `choose` retains these NORMAL providers:

```text
R: (p.f.g,ret)
W: (p,ret.f)
```

| Demand contribution | Evidence | Result |
| --- | --- | --- |
| reader `p.* -> ret.MAY` | `(p.f.g,ret)` | R covers it with empty shift |
| writer specialization cut to `ret.f.NE` | `(p.f,ret.f.f)` | W covers it with shift f |
| backward writer `ret.* -> p.MAY` | `(ret.f,p)` | W's backward view covers it |

Process all contributing variants, including partial and uniform queries;
removing only the root row can leave the cycle alive through another origin.

Before R exists, `(p.f.g,ret)` remains uncovered. Request:

```text
forward focus:  (p.f.g.MAY ; ret.STAR)
backward focus: (ret.MAY   ; p.f.g.STAR)
```

Once representable and admitted, the backward focus can retain the full
NORMAL reader instead of cutting it under the old root-p output budget.
When R arrives, the explicit coverage test retires the coarse contribution.

In the wrapper case the missing reader is `(p.h,ret.f)`:

```text
provider W       = (p,ret.f)
premise shift    = h
expected output  = ret.f.h
evidence output  = ret.f
decision         = NOT covered
```

Keep it and request `(p.h.MAY ; ret.f.STAR)`. The direct writer cannot
suppress the reader. Once NORMAL `(p.h,ret.f)` arrives, coverage succeeds.
There is no field ban.

## 6. Cyclic evidence

For write-only producer and read-only consumer cycles, compile the whole
path families to NFAs and test their synchronized product:

```text
producer: f*.g       consumer: f*.h
start: (producer.loop,consumer.loop)
f:     stays at the same pair
g/h:   cannot reach a joint accepting state
result: empty intersection; retire the false-flow obligation
```

This closes the entire family instead of increasing a cut depth forever.
The graph must cover all contributing routes and preserve marks and
boundaries. Mixed read/write cycles and rule-dependent effects need more
invariants. Leaving them Open is conservative but does not prove global
termination or asymptotic precision. Do not present this first scope as
the completed whole-core solution.

## 7. Proof and rollout

[Handoff.lean](../../spec/lean/proposals/demand-progress-20261113/Handoff.lean)
implements prefix composition, coverage, finite evidence retirement,
uncovered-focus selection and Open/Union handling. Its native evidence
producer and focus integration are separate proof obligations.

The constructive kernel passes **165 audited declarations in eight
modules**, including 19 new composition, compilation and coverage checks.
It proves preservation of every precise unary prefix observation for an
accepted complete prefix model. Reproduce with
`python3 spec/lean/proposals/demand-progress-20261113/check.py --handoff --out <fresh external directory>`.
The receipt is `demand-progress-20261113/handoff-proofs-v5/receipt.json`
under the [external archive](../reports/EXTERNAL_DATA.md).

Finite compilation can expand a branching expression into many relations.
Use the shared graph and the existing prefix index to check providers
lazily; a naive prototype costs O(E*N*L) for E evidence alternatives,
N providers and maximum path length L. Measure this cost before choosing
an always-on representation. No improvement is inferred from row counts.

Proposed order: prove the native finite-prefix adapter and evidence merge
hooks; prototype retirement; add focused demand rows; then support the
regular read-only/write-only cycle product. Validate the original and BB
examples, the wrapper, delayed findings and both arrival orders uncapped.

No project run or production change is included. Historical reached/
completed/accepted-forward positions remain OWASP **run-11/11/11**,
Conductor **run-8/7/7**, Stirling-PDF **run-11/10/9**.

# Share the analysis owner for pure forwarding methods

**Withdrawn as the solution to the active goal.** The user rejected the
wrapper-shape precondition. This remains a historical reference experiment.
The replacement is [progressive input partitions](bidirectional-progressive-input-partition-20261115.md),
which retains separate owners and handles ordinary operations around calls.

15 November 2026. Proposal under [proof-guide.md](../../spec/proof-guide.md).
Production is unchanged. Keep the selected
[same-lane coverage and complete reply packets](bidirectional-same-lane-uniform-termination-20261114.md).
Add the owner projection below for the
[new nested-call example](../reports/bidirectional-nested-saved-replay-nontermination-20261115.md).

**Reference result:** the new example naturally finishes at **run-9** with
its NORMAL observation retained. The old required examples retain their
run-1/run-3 completions and their existing observation routes. This is a
solution for the selected acceptance set, not a universal termination claim.
The earlier special-pass intrinsic-MAY example remains outside that set.

## 1. Proposed change

A method whose whole behavior is a call and an unchanged return does not
need a second DATA abstraction:

```java
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
```

Make `wrapper` a view of the original inner call's analysis owner. Retain
its logical method/call frame for the caller protocol and trace output.
Do not rewrite the IR, call graph or configured rules.

```text
BEFORE
    original input U
        -> wrapper C2: q
        -> choose saved/current application on q
        -> wrapper C5
        -> caller

AFTER, for a certified forwarding method
    original input U
        -> choose saved replay on U
        -> choose demand lookup and C2, when needed
        -> choose C5
        -> original caller binding

    wrapper has no independent DATA store, query or refinement frontier.
```

**Major analysis-semantic change:** remove the extra C2/C5 boundary for
certified forwarding owners. Intermediate demand, layers and confirmation
timing can differ. This is not merely a compact representation of the old
work. The concrete transfer/observation relation of an eligible wrapper
is unchanged; the operational proof in section 6 establishes that fact.

This does not assume that saved NORMAL summaries form a complete method
model. The canonical callee is analyzed from empty stores, under the usual
demand policy. The wrapper shares its current, incomplete stores too.

| Part | Before | Proposed |
| --- | --- | --- |
| Eligible forwarding method | Own analyzer, C2, C5, stores | One descriptor pointing to the original inner call's canonical owner |
| Original actual | Coarsened at wrapper before the inner call | Given directly to the canonical owner's existing call service |
| Demand lookup | Wrapper rows, then callee rows | Canonical callee rows once; pass its plan to that owner |
| Summary delivery | Apply inner summary to wrapper hypothesis, then summarize again | Expose canonical rows through the identity boundary view |
| Ineligible method/block | Existing analysis | Exactly the same analysis |
| Program observations | Existing rule sites and ids | Same sites and ids; retain the logical wrapper frame |

Keep unchanged: FULL marks, the `1,1,2,3,...` schedule, every real NE cut,
C2's legal raw tails and layers, paired C5, FLOW normalization, opposite-only
STAR inside matching, selected cleaner behavior, literal protection, mark
exclusions, source permissions, ZERO/Target rules and the empty-frontier
stop rule. No new mark or tail, grounding support, path evidence, field
ban, request store or cross-call suffix product is introduced.

This uses a structural method-form certificate. It is separate from the
paused edge-only demand-elimination campaign; it is not a new predicate
over repeated edge histories.

## 2. Eligibility certificate

The first implementation should accept only a strict template. Start with
static ordinary methods whose arguments stay in their original positions.
The shape is checked on the method form and complete analyzed call plan.
Unknown or unsupported cases use ordinary analysis.

```text
eligible(methodContext):
    methodContext is not a configured root
    wrapper and target have ordinary analyzable bodies, not predefined models
    exactly one fixed resolved inner target, including its analysis context
    every call operand is the corresponding unchanged wrapper parameter
    all normal paths return exactly that call's result
    all exceptional paths pass through exactly that call's exception
    no loop, branch around the call, catch, finally, field operation or extra call
    no wrapper entry/exit rule and no instruction rule in its body
    no rule or extra effect in the inner call's entry/return stages
    all remaining instructions/stages are identity copies or control
    proxy chain is acyclic
    native context adapters have a preservation proof
```

Check the whole template, not only the last `return`. A constant argument,
duplicate parameter, reordered parameter, selected cleaner, generated
assignment, observation, predefined model or exception handler rejects this
initial template. The new example satisfies it. So do chains of such methods.

The call-plan check includes implicit modeled effects, such as class
initialization, cleanup and unresolved handling. A source-level one-line
method is insufficient evidence. Keep an opaque case on the ordinary path.
Filter by structure before inspecting the already resolved rule/call data;
do not add an eager bound-rule census over all methods.

The current formal activation scope is the positive unary AP context of
the supplied examples, with no alias expansion or special static effects.
Native activation in another context needs the corresponding adapter proof;
it must otherwise fall back. This proposal changes no alias/static policy.

Build the certificate once for the fixed scan configuration, before run-1.
It must remain valid for all runs. It is not inferred from empty demand,
stable counts, submitted facts or a supposedly complete NORMAL basis.
If configuration or IR changes, rebuild it before a new scan.

Use the **original inner call's resolved MethodKey/context**, not a new
hypothetical call from the outer caller to the target. Caller-sensitive
resolution and rule metadata must not change. Preserve the original outer
call facade. In particular, rules on that outer call still use its original
logical target and statement.

## 3. Owners and stores

```text
OwnerDirectory:
    Ordinary(logicalMethodKey, its current existing owner)
    Forwarding(logicalMethodKey,
               canonicalMethodKey,
               originalInnerCall,
               normalPortMap,
               exceptionalPortMap,
               traceFrame)
```

Resolve forwarding chains once. Store a path-compressed canonical pointer.
Reject a cycle; do not use a cycle as a new termination shortcut. The
finite graph traversal bound applies only to directory construction,
not to the number of analysis iterations.

There is one MethodEdgeStore, summary store, demand store and query plan
for the canonical owner. A forwarding descriptor has none of those stores.
It does not archive inputs or copy summary rows. Its identity-parameter
view shares immutable AP facts. Fields, tails, E, mx, marks and H are
unchanged; only the qualified owner/physical-port view is adapted.

Map normal and exceptional ports separately. Do not merge ZERO ports.
Keep native record producer direction/read role; do not rebuild an
opposite-direction record as a current or direct record under a new name.

At handoff, persist NORMAL rows and form demand once per canonical owner.
The wrapper's next demand view is the same owner's view. Count each
physical frontier once for stopping. A logical-method diagnostic may list
the wrapper view separately, but that must not materialize another store.

The prescan call graph stays logical. Other mechanisms do not lose the
wrapper's graph node. Rule selection and mark specialization must still use
that logical graph, not shrink their scope to the canonical-owner set. Trace resolution can reinsert its certified identity
entry/call/return or exception frame. Observation ids still name the
original actual rule site; the wrapper has no additional observation.

## 4. Call pipeline

Use the existing persisted-first call policy. The only new step is owner
resolution before selecting the store and plan. Keep the original actual;
never substitute a wrapper-owned STAR hypothesis.

```text
onCall(call, callerOriginal, actual):
    facade = existingLogicalCallFacade(call)
    runExistingOuterCallEntryStages(facade, callerOriginal, actual)

    view = OwnerDirectory.resolve(facade.methodKey)
    if view is Ordinary:
        existingCallPolicy(facade, callerOriginal, actual)
        return

    canonical = view.canonicalOwner
    input = view.toCanonicalBoundary(actual)       // identity AP slots here
    resume = existingCallerResume(facade, callerOriginal, view.fromCanonical)

    canonical.savedNormals.apply(input, resume)    // original offer, as before
    plan = canonical.demand.lookup(input)
    if plan.empty:
        runExistingOuterCallReturnStages(facade)
        return

    canonical.startExistingC2(plan)                // entry dedup stays there
    canonical.current.applyAndSubscribe(plan, input, resume)
    runExistingOuterCallReturnStages(facade)

onCanonicalRawSummary(P, C):
    useExistingPairedC5AndPublication(P, C)         // including all old guards
    // Forwarding views observe the existing publication.
    // No wrapper re-emission, reclassification, cut or second C5.

onHandoff():
    for canonical in distinctOrdinaryOwners:
        existingPersistAndDemandHandoff(canonical)
    useExistingCompleteOutgoingDemandStop()        // includes DemandTarget
```

The resume context still carries the outer caller's original premise,
actual support layer, statement and stages. A NORMAL callee relation cannot
upgrade a DEMAND actual. Current summaries still need a canonical demand
plan; saved NORMAL replay still happens when that plan is empty.

This is not saved-replay pruning. No MAY result is discarded because a
child query is presumed to cover it. The redundant wrapper query that
created that result is never constructed. A nontransparent caller keeps
all its current replay results and its own C2/C5 boundary.

## 5. The new example

Use exactly the marking/observation rules and program from the
[counterexample report](../reports/bidirectional-nested-saved-replay-nontermination-20261115.md).
Only the analysis-owner policy changes.

Once the two NORMAL `choose` records have been derived:

```text
R: x.f.f.* -> ret.*
W: x.*     -> ret.f.f.*

original offer: x.f.g.MUST/T,N
    R does not match: g != f
    W gives ret.f.f.f.g.MUST/T,N
```

There is no intermediate wrapper `x.f.*` query that could use R's inside
match. The next real call still sees the known g and the uniform tail.
For three calls, the mature packets are:

```text
U0 = x.f.g.MUST/T,N
U1 = x.f.f.f.g.MUST/T,N
U2 = x.f.f.f.f.f.g.MUST/T,N
U3 = x.f.f.f.f.f.f.f.g.MUST/T,N

{U0} -> {U1} -> {U0,U2} -> {U1,U3}
```

Do not assume that basis at run-1. The complete cold reference derives W
at run-3 and the backward-produced R view at run-4. It keeps every actual
field cut. In particular, run-7 still has an NE/DEMAND result because the
eight-field U3 does not fit limit 6. The existing backward replay reaches
the real producer and keeps the permission for run-9. At limit 8 all final
facts are NORMAL; no further Target demand is emitted.

| Run | Canonical choose outgoing DATA demand | Final call packet size | DEMAND members in that packet |
| --- | ---: | ---: | ---: |
| run-1 | 2 | 1 | 1 |
| run-2 | 3 | 1 | 1 |
| run-3 | 6 | 1 | 1 |
| run-4 | 4 | 1 | 1 |
| run-5 | 2 | 6 | 5 |
| run-6 | 0 | 1 | 1 |
| run-7 | 0 | 2 | 1 |
| run-8 | 0 | 1 | 1 |
| run-9 | 0 | 2 | 0 |

The proxy has no independent frontier in any row of the table. Canonical
DATA demand becoming empty at run-6 is insufficient to stop: entry's
DemandTarget still matters. At run-9 the **complete** frontier, including
entry's Target, is empty and the existing NORMAL observation id is retained.
This is natural completion, not a run-11 cutoff or a count-based heuristic.

## 6. Proofs and old acceptance set

[Constructive Lean package](../../spec/lean/proposals/transparent-forwarder-termination-20261115/README.md)
checks three distinct obligations:

1. **Program behavior.** The relay's operational steps are entry/copy,
   the original callee invocation, and unchanged return/throw. An execution
   exists iff that callee execution exists, with the same output bindings,
   exit port and complete observation sequence. The proof constructs the
   intermediate states in both directions. It holds for arbitrarily many
   certified forwarding frames; no NORMAL-basis completeness is assumed.
2. **Abstraction mechanics.** The descriptor preserves AP fields, marks,
   E/mx, tail, layer and protection. Identity boundary frames add no field.
   Field cuts and FLOW normalization commute with the boundary projection.
   C2 and paired C5 execute only at the unchanged canonical owner. Unsupported
   shapes select the old analyzer for every possible stored state/frontier.
3. **Actual convergence.** From empty stores, every complete run-1 through
   run-9 state, one further quiescent queue round and both handoff stores
   are kernel-checked. Final DATA demand is empty, no anonymous Target
   survives, and the same NORMAL observation id is collected. This proves
   a natural finite stop without any iteration cap. It does not merely
   remove the former cycle's selected witnesses.

The unchanged old acceptance set is checked in the same package:

| Required old case | Why projection cannot remove its semantics | Reference result |
| --- | --- | --- |
| Read f.g / write one f, two calls | Field operations/branch reject relay recognition | run-3, NORMAL observation retained |
| Same method with inner read/write blocks | Branching parent and nonidentity blocks stay ordinary owners | run-3, all inner frontiers empty |
| Arbitrarily longer reader | Nonidentity reads reject; old complete packet theorem holds for every suffix | Existing run-3 packet and observation |
| Read ff / write ff, two calls | Nonidentity helper stays ordinary; retain uniform coverage | run-3 |
| Selected root cleaner plus that helper | Rule/field guards reject; retain same-H concrete/FLOW-mx law and reply folding | run-3, protected observation retained |
| Standalone uniform input/root cleaner | Rule guard rejects; retain selected MUST behavior | run-1 |
| Wrapper/child-demand regression with h read/k write | Those field transforms reject the relay template | Existing NORMAL route retained |
| Exact-root selected-cleaner survivor | Cleaner is not transparent | Existing nonempty repair and NORMAL route retained |

The old programs do not become rule-free because a NORMAL row happened
to be cached. Recognition uses their operations and rule effects. Literal
H classes remain separate and the selected MUST cleaner's documented
NORMAL exact-root approximation is unchanged. No new cleaner behavior is
hidden in this owner optimization.

## 7. Complexity, validation and limits

Recognition scans a candidate's normalized method/call form once. Chain
resolution with memoization costs O(methods + forwarding edges). Store one
small descriptor per forwarding method. After resolution, dispatch adds one
canonical-owner lookup; it does not walk a field path or a wrapper chain.

For n forwarding frames around one callee, use one DATA owner and one set
of stores, not n extra DATA owners. A call uses one C2/C5 boundary. Inputs
are not copied into a per-wrapper history. The old global/relative field
bounds remain the controls on the actual callee analysis. This does not
promise that arbitrary nontransparent methods have a small bounded AP set.

The checker passes **55 new theorems**, **597 audited declarations in
36 modules** including the complete old packages and counterexample proofs.
All proofs are constructive, with no holes, custom/classical axioms or
`native_decide`. Native validation passes **12 component tests**, including
three new tests for complete precise three-call replay, support-layer
preservation and the real backward producer route. They do not implement
owner routing or NE in production.

Latest reached positions: old required references finish at **run-1/run-3**;
the new full reference finishes at **run-9**. Its old-policy control reaches
**run-31** and has a separate uncapped nontermination proof. Native operators
use forward limit 8 (run-9 geometry), backward limit 7 (run-8 geometry), and
include an existing run-3 body check. No project scan was run.

This solution is deliberately gated. A method with extra field work,
rules, handlers, ambiguous targets or an uncertified context keeps its
existing owner and may need another progress mechanism. In particular,
this is not a proof that arbitrary saved-summary inside matches can be
pruned or that every program now terminates.

Before production activation, implement and test the real method-form
certificate, the context/port-preserving directory view, logical trace
expansion and canonical demand-plan plumbing. The current proof models
that certificate interface; it is not a JIR classifier/binary correspondence
proof. Keep the fallbacks until those adapter obligations are discharged.

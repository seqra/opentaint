# Terminate the old and protected uniform-growth examples

14 November 2026. Investigation proposal. Follow
[proof-guide.md](../../spec/proof-guide.md). Production is unchanged.
This extends [bounded refinement](bidirectional-bounded-demand-refinement-20261114.md)
and [neutral uniform coverage](bidirectional-normal-uniform-ne-coverage-20261114.md).
The [acceptance list](bidirectional-may-may-progress-task-20261113.md) retains
all old examples and the new selected-cleaner example.

## 1. Approach

Keep field truncation. Remove a truncated result when a retained NORMAL
uniform result already supplies its whole region under the **same complete
initial**. Extend the earlier FLOW-only rule to the concrete mark and
protection lane that occur in the new example. Canonicalize a complete call
reply packet before admitting its facts at the next call.

```text
P = one forward MUST initial

N: P -> a.u.MUST / m, NORMAL, H=h
X: P -> a.u.v.NE / m, DEMAND, H=h

N covers X.  v can be empty.
```

`MUST` is `[any-taint]`. `NE` is non-empty-MAY. `m` is either the unchanged
full mark T, or FLOW with exactly the same output mark exclusions in N and
X. The full original P is identical, including its mark and exclusions.
This is a summary relation comparison, not a comparison between unrelated
caller facts.

The NORMAL result is derived by the ordinary analysis. It is not inferred
from the cut. It proves uniform coverage even when the other branch creates
an ever longer path. That branch can then add no uncovered tainted location.
No discarded suffix needs to cross a call.

## 2. Selected behavior and proposed differences

| Part | Before this extension | Proposed behavior |
| --- | --- | --- |
| Neutral coverage | Empty-mx, unprotected FLOW/MUST can cover FLOW/NE | Keep this case |
| Concrete coverage | Full-T and protected rows bypass that rule | Same-T NORMAL MUST can cover NE; require identical literal H |
| FLOW mark exclusions | Nonempty mx bypasses that rule | Equal output mx is permitted; excluded T stays excluded |
| Publication | Owner already waits for its fact queue to empty | Recheck pending D against the final admitted NORMAL basis before publishing |
| Call replies | Scalar outputs can be enqueued separately | Fold one complete publication/replay packet by the existing same-layer MUST/MUST law before enqueueing its surviving facts |
| Backward analysis | Existing C2, C5 and saved-record reversal | Unchanged |
| Cleaner | Selected same-head MUST-preserving policy | Unchanged, including its already documented exact-root NORMAL false positive |
| Field cuts | Global and relative `FL(Dp)+1` cuts emit NE/DEMAND | Unchanged; no raw candidate becomes NORMAL |

**Major proposed semantic change:** retire some protected concrete and
FLOW/mx refinement guidance. The new law permits protected-to-protected
replacement with the same full mark and complete initial. It never permits
plain/protected replacement or erases protection. This extends the previous
rule that kept these protected NE rows. It needs selection before production
implementation.

**Execution change:** complete reply packets use canonical facts before
further C2 admission. This is necessary for the reference termination result;
it is not safe to assume that already queued scalar descendants disappear
when a later root arrives. No in-flight query is cancelled or relabelled.

Keep unchanged: source permissions, rule evaluation, real field exclusions,
mark-changing rules, actual support layers, NORMAL-only Target composition,
backward weak/provisional MUST behavior and literal protection membership.
No new grounding state, field ban, tail kind, source scan or global barrier
is introduced.

## 3. Activation guards

The initial proposal is for the qualified forward, positive field-transfer
scope of the supplied programs. They have no alias operations, statics, ND,
loops, recursion or special pass rules. Compare only within the same method
or inner block, context, physical ports and complete singleton initial.

```text
eligible(N, X) :=
    sameQualifiedFrame(N, X)
    and N.P == X.P and N.P.tail == MUST
    and N.P.E == N.C.E == X.C.E == empty
    and N.layer == NORMAL and X.layer == DEMAND
    and N.C.tail == MUST and X.C.tail == NE
    and N.C.base == X.C.base
    and N.C.mark == X.C.mark and N.C.mx == X.C.mx
    and N.H == X.H
    and diagonal(N)
    and prefix(N.C.path, X.C.path)

diagonal(N) :=
    (N.P.mark == FLOW and N.C.mark == FLOW)
    or (N.P.mark == N.C.mark == full T
        and N.P.mx == N.C.mx == empty)
```

Do not extend this predicate to STAR originals, independent MAY outputs,
ZERO/GEN, mark-changing relations, ND or backward views. Keep unsupported
memberships. Protection is part of the comparison key, not an eligibility
bit that is cleared for matching.

A retained NORMAL record may supply a transient provider when an existing
precoverage optimization omitted its duplicate. Apply that record to the
whole P with the native **definite** matcher; run its image through the
candidate's own C5 row. Require an uncut NORMAL result satisfying the same
predicate. A weak or globally cut image is not a provider. The earlier
[warm-record proof](../../spec/lean/proposals/normal-uniform-ne-coverage-20261114/VirtualProviders.lean)
is retained; this extension does not add a new provisional lane.

## 4. Pipeline and storage

Reuse the existing method/block queue-empty publication boundary. No method
waits for unknown future input, another actor or all project work. In the
supplied acyclic helpers, one input's complete C2 family is installed before
body processing, so that boundary contains all its branch results.

```text
onAddedInput(owner, actual):
    keys = existingC2Plan(actual)          // all own-row keys in one batch
    owner.startInitials(keys)

onOwnerFactQueueEmpty(owner):
    batch = detachExistingPendingPublications()
    normals = retainedNormalProviders + batch.NORMAL
    survivors = batch.NORMAL
    for X in batch.DEMAND:
        N = findEligibleProvider(normals, X)
        if N is absent:
            N = legalDefiniteSavedViewThroughOwnC5(X)
        if N is absent or not eligible(N, X):
            survivors.add(X)
    publishOnePacket(survivors)           // no covered D callback escapes

onCallReplyPacket(callContext, publications):
    packet = emptyTemporaryFactCollection()
    for publication in publications:
        for value in existingNativeApplication(publication,
                                                callContext.originalActual):
            packet.add(value)
    packet = existingSameLayerMustMustCanonicalization(packet)
    // Partition by caller original, statement/stage, base, mark/mx,
    // layer and literal H. Keep root EXACT alongside root MUST.
    enqueueSurvivorsThroughExistingPostStatementStorage(packet)

onHandoff(owner):
    recheckPendingGuidanceAgainstFinalRetainedProviders()
    useExistingHandoffAndEmptyDemandStop()
```

Apply the same reply folding to a saved-summary replay packet. Retained
NORMAL records are still replayed on the original actual, before current
admission. Do not replace that actual with a guessed MUST or upgrade its
layer. Late input can create a later batch; no batch closure claims that
future input is absent. The termination proof below is for the supplied
finite call graphs and actual families, not arbitrary asynchronous input.

Storage is the existing pending-publication list and NORMAL index, plus
one transient reply collection per processed call packet. Index providers
by complete original, lane, output base and H; use a prefix lookup on the
bounded output chain. A scalar scan costs O(k × L) for k matching providers
and field limit L. A prefix trie costs O(L) after the qualified-key lookup.
Reply folding reuses the current MUST/MUST operation. It has no persistent
suffix history, origin product or cross-call evidence product.

## 5. Why batching is part of this approach

In the new example, run-3 NORMAL replies include all of:

```text
ret.MUST/T, H=1
ret.f.MUST/T, H=1
ret.f.f.MUST/T, H=1
ret.$/T, H=1
```

If `ret.f.f.MUST/T` is submitted to the second call first, its first-field
C2 plan creates a STAR/DEMAND query. Removing NE from the original MUST
query does not cancel that new STAR query. The formal model reproduces it.

The complete reply packet instead keeps root MUST and root EXACT. Root
MUST covers the two descendant MUST memberships in their same layer/H
class. It does **not** delete root EXACT. That EXACT offer produces another
FLOW probe, so the proof also evaluates that probe rather than hiding it.
It contributes one NORMAL FLOW summary with mx excluding T, and no demand.

Enumeration order within a complete packet does not change surviving
semantic membership. Delaying publication without canonicalizing its
application results is insufficient: stale descendant work can still be
queued in the caller.

## 6. Soundness and termination claims

For every removed NE point `a.u.v.w`, the retained MUST provider contains
that same point: its suffix is the executable concatenation `v ++ w`.
The mark gate, output mx and protection are identical. Under the identical
whole original P, the provider is available whenever X's complete premise
is available. It remains in the final basis. In the declared positive
field-transfer scope, subsequent reads/writes and source/sink observations
lose no marked location by using that provider. Actual DEMAND support
remains DEMAND under a NORMAL provider.

This is not a proof that a plain FLOW identity can erase a protected T
assignment, or that one can reverse MUST by swapping endpoints. Neither
operation is proposed. Native alias effects and arbitrary rule/record
correspondence need their own proof before widening the scope.

The [complete traces](../reports/bidirectional-same-lane-uniform-termination-reference-20261114.md)
and [Lean package](../../spec/lean/proposals/same-lane-uniform-termination-20261114/README.md)
check the full acceptance set:

| Example | Reference natural completion |
| --- | --- |
| Old read `x.f.g`, write one f, two calls | run-3; NORMAL finding retained |
| Same example with read/write BBs | run-3 in method and inner blocks |
| Longer reader/bootstrap | Same NORMAL reader, for an arbitrary remaining read suffix |
| Ordinary read `x.f.f`, write two f fields | run-3; root and helper demand empty |
| Same helper with root-only selected T cleaner | run-3; full T and FLOW/mx packets close; NORMAL finding retained |
| Standalone uniform source/root cleaner | run-1 under the selected MUST-preserving policy |
| Wrapper/child demand and exact-root cleaner survivor | Legal NORMAL finding routes retained |

For the protected helper, the cold run-3 packet has 15 distinct rows:
10 NORMAL and 5 DEMAND. The 5 cuts have same-lane providers. Full return
processing adds one more NORMAL FLOW row. All 11 final helper rows are
NORMAL; both calls return the same canonical NORMAL root EXACT/MUST pair.
Another complete C2/body/C5/delivery round leaves that basis unchanged.
Induction proves that every further closure round is identical. Main emits
only a NORMAL sink Target; its complete outgoing refinement demand is empty.
Thus the engine naturally stops at run-3, without a hard limit.

The [old counterexample](../reports/bidirectional-protected-cleaner-growth-nontermination-20261114.md)
remains a regression against omitting the new rule. The delivery-prefix
counterexample remains a regression against omitting reply folding.

## 7. Validation and limits

Constructive checker: **401 audited declarations in 25 modules**, including
42 new claims. It rechecks the old models, both nontermination proofs, the
selected cleaner policy, complete new packets, all paired rows and the
within-run fixed point. It rejects proof holes, warnings and custom or
classical axioms; only Lean's `propext` and `Quot.sound` are allowed.

Production still has the old tail set. All **15 native component tests passed**, including three new provider-service
tests. They validate retained-provider matching, protection and mark-exclusion gates; they do
not claim an integrated native NE run-3 completion. The current historical
cleaner tests are not relabelled as tests of the selected proposal.

No project scan was run. Latest reached positions: the counterexample
reference was replayed through **run-31**; the new closed references finish
at **run-3** (standalone cleaner **run-1**); native body components reach
**run-3**. Historical project reached/completed/accepted-forward positions
remain OWASP **run-11/11/11**, Conductor **run-8/7/7**, Stirling-PDF
**run-11/10/9**.

This is an approach for every provided in-scope example, with explicit
reference/native boundaries. It is not a universal termination proof for
all programs. Special pass-target intrinsic-MAY rules remain outside the
user-selected acceptance set.

# Route saved replay through the existing prepared child cases

15 November 2026. Proposal under [proof-guide.md](../../spec/proof-guide.md).
Production is unchanged. This replaces the whole-body
[persistent partition proposal](bidirectional-progressive-input-partition-20261115.md).

**Reuse the child queries that C2 already prepares. Do not add a refinement
trie, new initial facts or a deeper input budget.** Apply their existing
routing rule to supported saved NORMAL reader contributions inside an owned
query, as well as to primitive field reads.

The positive reference examples naturally finish at **run-3 through run-15**.
The growth regression finishes at **run-11** with the complete old state
preserved at every run. See the [report](../reports/bidirectional-prepared-child-saved-replay-20261115.md).

## 1. Selected change

Current bounded refinement already creates a complete local family for a
selected next field f, within the same original demand row:

```text
parent: P.*
child:  P.f.$ and P.f.*
```

It routes a supported unknown-f primitive read through those child queries.
Saved NORMAL reader replay does not use that routing. The parent can therefore
regenerate a coarse MAY/DEMAND result which duplicates the child case.

Change only that per-record contribution. Keep the existing entry work,
original call offer, current-summary admission, C5 and output field limits.

```text
owned query and correlated fact:   P.* -> v.*, NORMAL FLOW
opposite saved NORMAL reader:      v.f.f.* -> r.*
already prepared child pair:       P.f.$ and P.f.*

old parent contribution:           P.* -> r.MAY, DEMAND
new parent contribution:           omitted for this reader only
child P.f.$:                      no result: the next f is absent
child P.f.*:                      P.f.* -> r.MAY, DEMAND
```

The child can remain uncertain. It does not need a complete NORMAL answer
for the entire f.f guard. The first child covers every concrete input on
which this particular reader could succeed. Further iterations refine the
remaining uncertainty through the ordinary demand mechanism.

**Semantic scope:** this removes duplicate coarse refinement guidance and
its intermediate observations. Per-run demand and confirmation timing can
change. It is not a new global edge-subsumption law. C2, C5, field processing,
raw initial shapes, marks, real exclusions, protection, source permissions,
ZERO/Target rules and the `1,1,2,3,...` schedule stay unchanged.

No new body is analyzed under P.f merely for this proposal: its two queries
were already prepared by the existing plan. No prefix path, evidence set or
new caller input is manufactured.

## 2. Why this makes progress

Consider a forward pair before the handoff:

```text
coarse parent: P.*   -> ret.MAY,D
child:        P.f.* -> ret.MAY,D
```

If the parent survives, the next backward row retains paired output P.*.
Its relative output bound is one field. An inverse read-two relation can be
cut back to P.f.NE again.

After removing this reader's duplicate parent contribution, the child's
row has paired output P.f.*. Its bound is two fields. The next backward
analysis can retain the two-field relation instead of renewing the same
one-field cut. This uses the existing `FL(Dp)+1` rule; no input/output bound
is enlarged by the proposal.

Other branches still have their own contributions. Do not delete a MAY
result merely because another derivation with the same output was routed.
Normal writer precoverage, selected MUST/NE coverage and complete reply
folding remain necessary for the old examples. Real global cuts still create
DEMAND and keep the root Target frontier alive until they are refined.

This is a progress explanation for the supported duplicate-reader pattern.
It is not a rule that all repeated demands are redundant or that every
program terminates.

## 3. Admission and stable child readiness

Use the existing qualified prepared plan of the **current owner**. It can
be a method or an inner block. Each child keeps exactly the parent's original
paired Dp, mark lane, protection membership, physical ports and context.

Before processing a deduplicated raw initial q, establish a safe routing
mask from the immutable prior demand/record snapshot. It must remain valid
for every potential row which can issue q, including later offers.

A conservative test is:

```text
ready(q, f) :=
    every row that can emit raw q provides the complete f child pair
    and each pair uses that row's original Dp and existing C2 budget
    and those child commands are installed before the parent is processed
```

Use the C2 inverse for the implemented table. Do not approximate it by
normalized summary-key matching. In the reference table, if q can also be
a first-field start of a shallower MAY row, that consumer does not have the
extra child budget and disables routing. A precise STAR/EXACT consumer does
not acquire child admission.

Do not infer readiness only from the inputs seen so far. Do not enlarge or
shrink a mask after deduplication. If readiness is not established, keep the
old parent contribution. The reference uses a conservative prior-row test,
intersected with the existing common mask; no new persistent state is added.
The native adapter must prove its own C2 inverse/child-availability condition.

A child over the global limit is not ready. A NORMAL record selecting f is
not, by itself, a proof of readiness. The complete existing child query must
cover the required continuation.

## 4. Supported contribution and pipeline

The first proof scope is positive unary prefix transport with empty real
field/mark exclusions. Route only an owned NORMAL FLOW STAR query whose
current operand is still a correlated NORMAL FLOW STAR fact. Require a saved
opposite-direction, unprotected NORMAL FLOW STAR-to-STAR reader. It must use
an unknown field inside the current operand, and its first unknown field
must be ready.

Concrete, protected, MUST, mark-changing, ND and unsupported alias/port
services retain their old work. No rule check or cleaner is skipped. A trie
field is not a field exclusion and cannot make a condition false. Use the
same complete child-service proof required by existing primitive routing;
otherwise keep the contribution.

```text
processCallInsideOwnedQuery(q, originalOperand, preparedPlan):
    // Same original operand and native call stages as before.
    enrollOriginalCalleeInputAndItsObservations(originalOperand)
    mask = preparedPlan.frozenChildCover(q)

    for savedRecord in nativeSavedNormalLookup(originalOperand):
        match = nativeMatch(savedRecord, originalOperand)
        if match.empty: continue
        if supportedOwnedNormalPrefixReader(q, originalOperand, savedRecord)
           and match.isInside
           and mask.coversFirstUnknownField(match):
            continue                    // omit this contribution only
        deliverNativeResult(match)      // no result, mark or layer rewrite

    applyAndSubscribeCurrentUsingExistingDemandPlan(originalOperand)
    // Do not replay all records on child inputs or submit new callee offers.
```

The real outer call service remains the old one: saved NORMAL records apply
to the original actual before current demand lookup, even with no demand.
The routing above belongs only to an owned conditional query. Keep actual
marked facts and their normal/DEMAND layers.

Primitive instructions use exactly their old transfer/routing. C5 receives
the same raw initial from the same C2 plan and intersects against the same
original Dp. Output normalization, NORMAL precoverage, local refinement
capture and publication batching are unchanged.

## 5. Workload property and remaining risks

For a fixed input, prepared query plan and saved-record list:

```text
new raw entry keys                 = old raw entry keys
new original callee offers         = old original callee offers
new saved contributions            = filter(old saved contributions)
new per-contribution postprocessing <= old per-contribution postprocessing
```

The last inequality applies to the same fixed native postprocessing function,
including paired C5. A kept result is exactly the native result. The filter
adds no premise geometry and restarts no method body. This removes the cause
of the earlier 2-to-18 growth regression.

Precompute the readiness mask once per raw query from the prepared plan.
Reuse native matching's first-unknown-field result. Do not scan every demand
row again for every delivered summary, or materialize a result just to drop
it. The extra hot-path operation is a qualified mask membership check.

**This is not a whole-run cardinality theorem.** Removing a broad MAY can
expose several narrower facts which it previously covered. Later demand,
initials and caller work can differ. In the 600 post-read reference screen,
the largest total summary-membership increase was about 3.6%; the separate
600-case screen had no increase. These are finite diagnostic results, not
native performance bounds.

Other limits remain: conservative readiness can miss an optimization;
unsupported records can still repeat; legitimate field combinations can
still be large; a retained NORMAL observation must not erase an unresolved
DemandTarget. No project performance or universal native termination claim
follows from the checked examples.

## 6. Proof and validation

The [constructive package](../../spec/lean/proposals/prepared-child-saved-replay-20261115/README.md)
models unchanged C2/C5, concrete prefix-reader child coverage, the filter-only
cost property and complete cold reference states. It checks the full growth
case against both enabled and old modes at every run, not only summary counts.
Older uniform/cleaner/protection packages are rebuilt as dependencies.

Native integration must bind the qualified child-service predicate to actual
alias, rule and port handling. If that proof is absent, keep ordinary replay.
Production is unchanged; the discarded dynamic-origin and full-guard
composition experiments are not selected parts of this proposal.

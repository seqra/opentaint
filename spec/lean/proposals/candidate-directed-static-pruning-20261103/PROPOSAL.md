# Exact candidate-directed static pruning — unselected proposal

Date: 3 November 2026. Reference runtime:
`050b83cfb7b2e75856ea113c44d0a2d6b707250d`.
Status: **UNSELECTED**. This package changes no Kotlin or native tests and does
not authorize implementation. Optimization ranking remains provisional while
heap dominance analysis is pending.

## Contract and scope

Selected major semantic changes: **none**. A future implementation must preserve
the old `KilledStaticWriteStore.freeze` result exactly. This model proposes only
a different way to answer its final exact membership queries. No ZERO admission,
source permission, primitive policy, field transfer, demand/C2/C5, mark ownership,
report identity, summary-store coverage or observation rule changes are proposed.
Data-class equality/hashing and the raw interner key remain unchanged.

Currently `freeze` consumes all eligible scalar rows of `common.all()` and
private B, normalizes them into a survivor `HashSet`, and then classifies each
observed raw candidate ID. This occurs even when the candidate list C is empty.
The proposal supplies an exact membership oracle and queries it only for C's
normalized keys. For empty C, return the same frozen empty arrays/peak without
iterating common/private B or invoking the row lookup/oracle. The finite access
trace proves that no enumeration request is made; it is not a model of arbitrary
side effects or cancellation timing of Kotlin `Sequence` implementations.

Let S be exactly the normalized keys emitted by the old eligible common and
private-B enumerations. The necessary prerequisite is, for every raw ID i in C,

`oracle(normalize(row(i))) = (normalize(row(i)) in S)`.

**This prerequisite is not proved for any Kotlin membership API.** It is not a
license to use an input borrow that silently ignores DEMAND, protection, a packed
store branch or a normalized-key collision. The executable finite reference
oracle establishes consistency by enumerating S, so it does not itself improve
complexity. A future exact index/query requires an adapter proof and meaningful
native tests before implementation selection.

## Equality and normalization

The finite row snapshot is supplied after existing runtime-domain/packet filters.
Only valid FLOW/FLOW or concrete/concrete endpoint pairs represent production
rows; `outsideScope` is a total finite encoding for mixed invalid pairs, not a
new Kotlin acceptance rule. Abstract base IDs/field IDs represent opaque unchanged
coordinates, with base0 denoting real ZERO. The model does not prove AP algebra.

The key function reproduces the existing normalization order:

1. For a complete FLOW pair, EXACT endpoints become STAR. Other pair tails stay.
2. Each MUST/ANY_TAINT endpoint becomes ANY and loses its field exclusions.
3. FLOW mark exclusions are discarded by the guidance-pattern STAR mark.
4. A FLOW STAR endpoint loses field exclusions; other ordinary exclusions remain.
5. Concrete mark IDs remain exact. The mark relation is FLOW or mapped; real ZERO
   endpoints use absent mapped mark labels as in `StaticGuidanceEdge.of`.

Layer and protection are not fields of the guidance key. The old freeze loops do
not filter out DEMAND or protected survivors, so the oracle must include both
layers and ignore protection exactly as the old key equality does. This does not
change those policies elsewhere in the analyzer.

Candidate identities stay raw and ordered. Two different raw IDs may normalize
to the same key; both observed IDs and their order remain in the frozen inventory.
Both remain lost if that key is absent. A normalized-key set must never replace
C or merge its raw interner rows. Peak metadata is copied unchanged.

The colored omission witness is deliberate: if the old `all()` survivor view
contains only a FLOW row and omits a colored diagonal row, the colored candidate
remains lost. Logical FLOW coverage, a previous observation, stored protection or
a historical colored row is not a substitute for current emitted membership.
No claim is made that existing Kotlin `borrow`/coverage queries already satisfy
this condition.

## Proved finite laws and cost model

Under the explicit oracle prerequisite, the ordered lost list is exactly the old
filter of C, and the entire frozen result (observed, lost, peak) is equal. No
assumption about answers outside C is required. The model also proves empty-C
non-evaluation, raw collision retention, layer/protection behavior and executable
normalization examples. These are finite functional/interface laws, not a proof
of actor queues, live stores, heap retention or whole-analyzer convergence.

The old caller plan materializes n common plus m private-B scalar rows before
checking C. The candidate caller plan makes one row lookup and one oracle query
per raw ID, with zero full-view enumeration requests. `oldUnrelatedRows` counts
materialized survivor rows whose normalized keys are not among C's keys. The
candidate caller contributes zero such materializations; strict empty and
nonempty witnesses are proved. Oracle-internal work is a separate explicit cost.
A zero total requires a separate zero-unrelated-oracle-work law, which is not
proved for Kotlin. No project speedup, allocation reduction or retained-byte
saving follows merely from these caller counts.

## Validation required before a runtime proposal

First prove the real oracle equivalent to the exact old union of all eligible
emitted common/private-B rows, including both layers, all storage branches,
normalization and omitted colored rows. Then verify the empty-C fast path and
candidate query retain raw order, owner/interner identity, peak metadata and
freeze idempotence. The finite model covers one freeze result; it does not model
mutable observe/freeze lifecycle, iterator exceptions or cancellation effects.
Native tests and actual project measurements remain separate work. No such
Kotlin adapter, implementation or analyzer experiment is included here.

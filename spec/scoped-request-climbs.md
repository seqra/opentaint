# Preserve the block scope of a physical mark request

Date: 3 November 2026. Status: **selected correctness correction;
implemented and native checks pass**. The four-project rerun is pending.

This addendum restores the selected method-owned block contract. A physical
call subscriber has a caller method and a block scope. Its request must
return to that same owner. This correction does not select a new ZERO,
field, mark, source-permission, sink or Target policy.

## Current defect

`CallerRef` contains `scope`. `SubscriptionManager.joinRequests` selects a
matching FLOW input and its original `Run1Slot`, but its `ClimbTarget` keeps
only `(method, slot)`. It reads the root method request storage and emits
`MarkRequestsIn(method, rows)`. The receiver applies those rows to the root
analyzer. It loses the caller block scope.

For example, a helper needs mark T on a FLOW input submitted from a local
in the AL block at entry port 47. The sender can emit the correct mark and local-variable slot, but
the root actor has only a ZERO initial. The local AL47 state never receives
the request and cannot refine its FLOW input. A root request for the same
slot can also suppress a request that belongs to another block.

```text
Same method M, same slot v27, same full marks {T,U}:
A = scope(block3, entry47)
B = scope(block3, entry7)

Before: (M,A,v27) and (M,B,v27) both become (M,ROOT,v27).
After:  (M,A,v27) and (M,B,v27) remain two distinct request destinations.
```

## Required behavior

The climb key is `(method, scope, slot)`. A batch destination is
`(method, scope)`. Each batch merges all marks for each slot. It must not
merge, replace or suppress rows from another scope. The event carries the
same destination scope. The owning method actor dispatches the event to
that existing block state. ROOT remains the default for existing callers
that have no local scope.

The sender can keep its existing ROOT request-storage prefilter for a
ROOT destination. It must not use ROOT rows as evidence that a non-root
owner has the same request. For a non-root destination, send the complete
matched marks and let the destination perform its existing local request
and initial deduplication. Do not read mutable peer block state to perform
a new sender prefilter.

The existing FLOW eligibility, `normalRun1Slot`, field matching and mark
selection occur before the climb. Copy the selected slot and every full
mark unchanged. Do not add an empty-exclusion test, remove field chains,
replace full marks with groups, create an initial, or grant a source
permission as part of transport. Static-origin requests and direct TAINT
answers retain their existing paths.

The receiver must use the exact live block owner named by the event. It
must not fall back to ROOT or create a new scope when a local destination
is absent. Request insertion, concrete-answer emission and Work scheduling
remain the existing owner-local operations. Event unit routing can still
use the method key; the scope selects the local owner inside that method.

## Invariants and proof scope

The [constructive model](lean/proposals/scoped-request-climbs-20261103/README.md)
models finite request marks, exact method/scope/slot coordinates, owner
batching, ROOT-only prefiltering and receiver-local deduplication. It proves
that batching delivers exactly the offered scoped cells. Thus it neither
loses a full mark nor invents a request. It proves that equal slots in two
scopes remain distinct and that request or initial history at another
owner cannot suppress a local cell. Repeated local insertion is idempotent.
The model has an executable witness for the old scope loss.

A slot is an immutable base, field sequence and tail. The matching function
is supplied unchanged. The model does not prove production AP matching,
exclusion handling, packed mark storage, actor scheduling or source rules.
It does not assert project quality, performance or whole-driver convergence.
Native checks must establish the model-to-runtime correspondence.

The `ClimbTarget` and event equality keys now include scope. This is an
intentional change to request deduplication: equal method/slot/mark values
at different block entries are different requests. Fact, mark and rule
equality stay unchanged. ROOT-only batches keep their existing identity.

## Required native checks

- Two physical subscribers with the same caller method and slot but different
  scopes receive two correctly addressed event batches with every mark.
- A root R row must not suppress a non-root request with the same slot and
  mark. A repeated request at the exact same local owner remains deduplicated.
- Same-owner rows merge their marks. Direct TAINT answers and static-origin
  request handling retain their current destinations.
- The handler commits a request to the named existing local R, not ROOT,
  and resumes that owner's local abstraction. It reserves counted Work
  whenever the resulting local work requires it.
- The real helper/AL regression recovers the finding. Its trace must show
  the scope at subscription, event, local commit and concrete answer.
- Root-only controls retain their previous behavior. No C2/C5, field, layer,
  ZERO, source-permission or Target rule is changed.

The [native receipt](../docs/reports/data/bidirectional-scoped-mark-requests-validation-20261103.json)
records 2,399 common tests and 453 JVM tests with no failure. The
[actual-JIR gap report](../docs/reports/bidirectional-loop-block-scoped-request-gap-20261103.md)
shows RED and GREEN complete **run-3** results: zero findings before the
scope correction, and the expected `BenchmarkTest01875` finding after it.
These native results do not replace the full project campaign.

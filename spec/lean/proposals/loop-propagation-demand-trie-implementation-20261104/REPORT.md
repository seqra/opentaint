# Implementation-proposal proof delta report

Status: **IMPLEMENTATION PROPOSAL MODEL ONLY — no Kotlin implementation**.

No major semantic change is selected. The models preserve exact ordered
outputs relative to their explicit native-adapter capabilities. They do not
change AP field transfer, source authority, labels, marks, protection, aliases,
ZERO/Target handling, complete ND execution, routing or first-cut selection.

## Eligible output-program deduplication

An ordinary output payload is an opaque exact identity. A separate finite
Boolean function represents every protection-mask coordinate. The ordered
accumulator updates the first matching payload in place, ORing masks. The
model proves coverage monotone under later outputs, repeated identical streams
idempotent, and skipping already executed programs exact. This holds for the
entire accumulator list, including payload order and all protection bits; it
is not merely equality of a shape, count or unannotated set.

Rows first undergo their existing complete eligibility predicate. Only then
are repeated **identical output programs** removed in first-occurrence order.
The accepted program count is at most the eligible row count. The finite
controls retain payload order `[5,7]`, preserve two independent protection
upgrades to payload 5, and reduce `[0,1,0]` to two program evaluations. A
counterexample retains an eligible second row after an ineligible first row
with the same program; deduplication before eligibility would lose it.

The native adapter must establish program identity in the fixed complete
query context. `EntryRestrictionTicket.restrict` uses `pair.exit` after its
entry ticket has been accepted; it then performs the unchanged protection
transport and exact packing. `offerDataPair` derives its budget from that same
exit. A native output-program key must retain the exact exit Pattern, effective
budget, frozen scope/physical exit/policy/catalog and all remaining operation
parameters. Raw annotated actuals and whole-original normalization cannot be
silently shared across different query contexts. Ordinary `Facts.equals`
omits protection and is not an annotated-program equality proof.

The model assumes identical program IDs have the same pure emitted stream;
it does not assume two different native operations equivalent. The Kotlin
mapping to those IDs and to the ordered union remains unproved. DATA-only
output deduplication must not suppress source, request or Target effects.

## Prepared route token and effect-preserving delivery

A relation's forward destination is its conclusion; its reverse destination
is its premise. Only LocalVar endpoints use a liveness mask. ZERO, STATIC,
arguments, receiver, return and exception endpoints retain their ordinary
path. Full opaque DATA payloads and their protection functions are returned
unchanged.

The primary `DataAt` capability constrains only the endpoint of DATA callbacks
from one exact application. Target, mark request and static callbacks remain
allowed. `prepare_route_before_application_keep_effects` proves that computing
the oriented route token before calling native application and using that
constant token in its DATA sink yields the same ordered outputs as applying
the existing liveness filter afterward. Application still runs when the token
is dead. `all_effects_preserved_for_every_token` proves every non-DATA effect
and its order survives, independently of DATA capability.

The separate stronger `DataOnlyAt` capability permits full application
omission, but applies only to the already certified pure observer/empty-output
path. It is not the mutable-delivery rule. Explicit counterexamples retain
requests and reject using the conclusion endpoint for reverse application.
Feedback and leaving routes use separate masks: the example keeps a live
feedback local and drops it on the dead leaving route.

The producer-union theorem covers a logical interface followed by its actual
route. If the actual route belongs to that interface's genuine route list,
union filtering followed by the actual route filter equals the actual filter
alone. The adapter must use exactly the certified directed route list for that
interface, including its represented repeat/leave routes; do not add unrelated
feedback routes or omit represented ones. Dynamic intersection with the actual
`ActualStarts` remains a native adapter obligation and is not proved here.
Synthetic/unknown routes use native fallback. The model does not prove native layout construction, liveness
metadata correctness, route discovery, AP orientation, or a universal native
DATA destination property. In particular, base-preserving means the **oriented
destination**, not equality to the caller's input base.

## Conservative inverse candidate selection

`CandidateJoin` permits false-positive candidates and omits a pair only when
the native matcher returns `None`. It proves the ordered per-row input match
list and complete ordered nested row/input join unchanged. A finite witness
rejects omitting a live pair. Actual mutable inputs, versioning, snapshots,
duplicate keys, full ND AND combinations and queued delivery effects need
separate source/TDD evidence; this model does not replace them by metadata
queries or a cross-version cache.

The package compiles only its new Lean modules with one CPU and a 900 MiB Lean
memory limit. It does not import or regenerate the earlier proof packages.
There are no runtime edits, Kotlin/build/analyzer/profile runs, project
coverage or speedup claims, resource-limit proofs or commits in this delta.

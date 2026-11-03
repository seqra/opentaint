# Scoped physical request climbs

Status: **selected transport correction; constructive finite model**.
Read the [spec addendum](../../../scoped-request-climbs.md) and
[proof guide](../../../proof-guide.md).

```sh
python3 spec/lean/proposals/scoped-request-climbs-20261103/check.py
```

The executable model uses immutable owners `(method, scope)` and exact
slots `(base, fields, tail)`. Request cells include the full mark ID.
Batch rows union marks only at the same owner and slot. A generic proof
shows that the decoded batch contains a request if and only if the input
contains that exact request. The model constructs the old ROOT projection
that collapses two distinct local scopes and proves that the corrected
transport retains both owners and all marks.

ROOT can use its existing R prefilter. Non-root requests do not read peer
rows and remain available for destination-local R/P deduplication. The
finite history model proves idempotence, arrival-order membership equality,
no cross-owner suppression and no new mark. Matching is a supplied function;
its selected slot and marks are copied without a field or exclusion rewrite.

The checker uses Lean4.33.1, one worker and an axiom audit of every explicit
public definition and theorem. It rejects unproved declarations, choice and
native-evaluation proofs. Immutable Git blobs identify the pre-correction
production interfaces. They are not a kernel verification of Kotlin.

The [receipt](checks.json) and [portable audit](audit.txt) state the exact
checked scope. Native AP, actor ownership, event dispatch, queue accounting,
quality and performance remain separate validation requirements. This
package changes no ZERO admission, C2/C5, source permission or Target rule.

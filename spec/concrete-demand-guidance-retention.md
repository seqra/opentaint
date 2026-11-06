# Concrete demand positions and protected storage

Date: 6 November 2026. Status: selected storage laws implemented and locally
checked. Project acceptance and the end-to-end finding gate remain open.

The [post-landing project report](../docs/reports/bidirectional-protected-guidance-storage-performance-20261106.md)
measures committed runtime `7069fe2d7`. Latest reached / fully completed /
accepted forward runs are OWASP **run-5 / run-5 / run-5**, Conductor
**run-4 / run-3 / run-3**, Thingsboard **run-1 / none / none**, and
Stirling-PDF **run-5 / run-4 / run-3**. Conductor recovers the two missing
control identities. Thingsboard has no accepted report; Stirling's remaining
strict identity gap is unresolved. Do not treat those timeouts as quality passes.

This specification records three user decisions: keep STAR and repair demand
guidance; do not subsume protected memberships; do not let pass rules introduce
protection. It changes the storage clauses of the
[canonical-facts proposal](../docs/design/bidirectional-canonical-facts-normal-relations-directional-inside-implementation-20261105.md).
The [implementation draft](../docs/design/bidirectional-concrete-demand-guidance-implementation-20261106.md)
describes the source changes. The
[native report](../docs/reports/bidirectional-concrete-guidance-repair-reproducer-20261106.md)
records latest reached/completed/accepted **run-5 / run-5 / run-5** for the
small example, with zero NORMAL reports. Do not treat a local storage proof
as proof of that required finding.

## 1. Scope and semantic changes

| Part | Before | Selected behavior |
| --- | --- | --- |
| TAINT/DEMAND/ANY position | A containing MAY can remove a child position | Keep each supplied MAY position for later refinement |
| Protected membership | Coverage, E joins or fills can remove or move its flag | Keep the exact typed protected coordinate |
| Exact duplicate | Ordinary payload can already exist | Merge; protection wins and a new flag is fresh |
| Pass action | A broad action-ID test can classify it as an assignment | Transport existing protection; introduce none |

These changes affect initial-selection guidance and protection storage. They
are not only representation changes. They do not change C2 initial emission,
C5 summary restriction, fields, layers, mark identity, requests, aliases,
source/sink conditions, Target handling, ports, scheduling or stopping.
NORMAL relation coverage, opposite-record STAR matching and unprotected
EXACT/MUST/STAR DATA behavior keep their existing contracts. No raw-input
archive, new support label or history store is added.

## 2. Complete cell and effective coordinates

Fix owner, method/context, direction, block scope, physical entry and exit,
complete original premise, base and layer. Never combine different cells.
For one concrete full-mark bit, a coordinate is:

```text
K = (complete cell, field path, full mark, effective tail, effective E)

leaf.exact: effective tail = EXACT, effective E = Empty
            ignore the packet's mixed tail/E wrapper
leaf.any:   effective tail = packet tail, effective E = packet E
ANY:        effective E = Empty, as required by the existing grammar

May(X) = supplied TAINT/DEMAND/ANY leaf.any coordinates in X
H(X)   = supplied protected effective coordinates in X
```

H applies to NORMAL and DEMAND, with EXACT, ANY, STAR or MUST tails. It is
not limited to MAY guidance. Runtime GROUP atoms retain their existing
storage treatment; this change adds no FULL/GROUP eligibility filter.

For residual rows admitted by the existing relation-coverage law, each
fact-group update must satisfy:

```text
May(after) = May(before) union May(offer)
H(after)   = H(before) union H(offer)
H(after) is included at the same effective coordinates in payload(after)
```

Coalesce duplicate H only at the same effective coordinate. Different H
coordinates can share a packet, but both remain. Prefix coverage, E containment,
E intersection and complete-child filling cannot delete or relocate H.
A protected ancestor cannot remove a protected child. A protected MAY cannot
remove protected EXACT at the same point. EXACT flags deduplicate across
mixed wrappers; span flags retain their supplied tail/E.

This is a storage invariant. A real field operation or cleaner can still
kill a membership under its existing transfer rules. The invariant does not
keep facts beyond their owner or run lifetime.

## 3. Preserve incremental DATA admission

Do not re-admit the complete current state from empty. Existing STAR/T4
admission and packet normalization do not define one global normal form.
Use the same restored current DATA state and admit only the new offer:

```text
erase(X) = complete current payload packets without protection annotations
A(S,t)   = existing no-H DATA admission, with selected MAY-position retention

(dataAfter, legacyDelta) = A(restoreCurrent(erase(before)), erase(offer))
after = embedRawProtection(dataAfter, H(before) union H(offer))
```

Keep old DATA E-join carriers plain. For example, two protected MUST headers
at p with E={f} and E={g} can produce plain MUST E={}. Keep both original
protected headers too. Do not flag the derived E={} carrier.

For EXACT H, reuse an existing DATA exact coordinate once. If DATA removed
it, use an existing original cohort where possible, then an exact-only
carrier. For span H, restore the original typed header. Add the payload
carrier before attaching the mask, so factory clipping cannot remove H.

No DATA confluence or global fold-idempotence law is assumed. H union is
order independent; that fact alone does not prove all DATA effects equal.

## 4. Freshness, deltas and backends

Check ordinary DATA freshness, selected MAY-coordinate freshness and exact
H freshness. Reject only if none is fresh. A new flag is work even when its
ordinary payload already exists.

Keep legacy whole-content STAR/T4 deltas, including their exact siblings.
Filter those deltas against the new current state. Attach only current H at
the same typed coordinates. Add the remaining new H carriers. Coalesce equal
headers by raw payload/mask union; do not prefix-normalize those deltas.

The scalar and packed stores must implement this same law. Decode an affected
packed mark's current headers, restore them without re-admission, apply the
list-returning scalar update, then replace only that mark atomically. Keep
other marks unchanged. A packed FLOW-shaped geometry remains concrete TAINT
when decoded; it does not acquire the real FLOW coverage policy.

Cold packets, parent-before-child, child-before-parent, one root+child packet,
partial masks and exact duplicates all follow the same effective-coordinate
law. Publication can deliver only current memberships. It cannot revive a
legally removed plain relation. Existing FLOW replacement still applies to
unprotected rows; it cannot remove H.

## 5. Pass protection

A pass applies the ordinary AP transfer to input protection. An unprotected
input produces no new protection from that pass. This applies to CopyMark
and CopyAllMarks, in either direction and for exact or MAY targets.

PASS_THROUGH in either the action role or rule kind prevents assignment
classification. Native pass micro-edges keep their existing null action IDs.
No metadata is added to fact or micro-edge equality/hashing. Keep the existing
assignment, cleaner-survivor and generic summary-cycle protection rules.

## 6. Proof and validation boundaries

Follow [proof-guide.md](proof-guide.md). The local checked models are separate:

- `ConcreteGuidance.lean`: 58 historical MAY-only laws and unchanged C2 cells.
- `AllProtectionRetention.lean`: 35 incremental H/MAY laws with DATA admission
  as a parameter. This is not a proof of the native embedding algorithm.
- `EmbedRawProtectionOrdered.lean`: 50 ordered-bag placement, H-retention and
  EXACT allocation laws. Native DAG and mutable-loop refinement remain open.
- `PassProtectionPolicy.lean`: 24 pass-classification and transport laws.
- `NormalStarFlowAdmissionGap.lean`: 12 current-policy countermodel laws.
  These do not select a new admission policy or prove termination.

The models and receipts are in
[the proof directory](lean/proposals/concrete-demand-guidance-retention-20261106/README.md).
Native checks cover both storage backends, typed masks, E/header cases,
complete original/ports, handoff and pass forms. Native DATA/embedding/delta
bridges and required downstream effects need their own evidence.

The [historical control and DATA bridge report](../docs/reports/bidirectional-guidance-historical-control-and-data-bridge-20261106.md)
records five restored-state DATA bridge checks and the latest default gate:
3,040 clean results, including 462 reused JVM results. It also reproduces the
same zero-report run-5 on the complete pre-canonical 52f runtime. This establishes
that the small-program miss predates the current optimization; it does not
identify its first cause or remove the required finding gate.

The small native program now retains the previously lost child guide.
It still stops at run-5 without a NORMAL report. A getter has ANY/FLOW demand
and receives NORMAL STAR/FLOW at the same nonempty path; unchanged C2 rejects
it. This specification does not change that rule to make the gate pass.
Admitting it needs a separate semantic decision and progress check. A local
suffix-transport proof is insufficient. Project quality and post-landing
performance remain required by task.md.

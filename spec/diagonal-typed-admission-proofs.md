# Typed diagonal admission: conformance correction

Date: 26 October 2026. This correction follows sections 5.3 and 7 of the
[implementation proposal](../docs/design/bidirectional-correlated-concrete-implementation-20261026.md).
It adds no analyzer semantic policy. It changes admission of already covered
TAINT work in the current complete scope. It does not change FLOW replacement,
field processing, requests, rule handling, or handoff.

The latest measured unmodified candidate is **Thingsboard run-2 OOM;
run-1 COMPLETE** at revision `85dc2bbf8`. This document contains no project
measurement of this correction and no explanation of that OOM or its cause.

## 1. Confirmed gap

Revision `85dc2bbf8` separates diagonal rows by complete output tail and E.
That separation preserves the suffix binder. However, its scalar and packet
admission inspect only the equal header. They do not apply the selected
same-premise TAINT coverage law across those headers.

For one complete original `I = p.*/T`, one output base, and DEMAND layer:

```text
Offer 1: I -> ret.f.[any]/T, plain
Offer 2: I -> ret.f.*/T, plain

TaintGroup delta:          [ANY, empty]
Diagonal scalar delta:    [ANY, STAR]
Diagonal packet delta:    [ANY, STAR]
```

The second relation is contained in the first. The old implementation keeps
and propagates redundant work. It does not lose a relation or protected guide.
Repeating each exact typed offer then returns no delta. This witness is not
an infinite processing proof.

Protection has its own admission test:

| Existing ANY | Offered STAR | Selected later delta |
| --- | --- | --- |
| plain | plain | empty |
| protected | plain | empty |
| protected | protected | empty |
| plain | protected | protected STAR |

A proper ANY output prefix can cover the offered STAR output path. A STAR
prefix cannot do this: STAR coverage requires equal output paths and a stored
E that admits every offered suffix. The group and atom must remain equal.

The reverse order remains intentionally non-minimal:

```text
Offer STAR; then offer ANY -> keep both current rows, as TaintGroup does.
```

There is no new retroactive STAR-to-ANY compaction. Equal-root STAR/E merging
uses the existing exclusion-intersection law. No other field policy changes.

## 2. Current storage and exact scalar adapter

The primary current store is:

```kotlin
headers: LinkedHashMap<Scope, Rows>
Scope(initialShape, outputBase, outputLayer)
Rows(tail, exclusion) : LinkedHashMap<FlowNode, Masks> {
    var next: Rows? // Other current typed headers in this exact scope.
}
Masks(marks, protectedMarks)
```

The usual single-header cell has one primary map entry and one geometry map,
as before. There is no second scope index, per-scope set, scalar archive, or
answered-row history. The transient `Header` value is not a retained map key.
All atom masks remain exact and each atom retains its own concrete original.

Admission performs these steps:

```kotlin
if (!otherTypedHeaderContainsAnOfferedAtom(scope, tail, E, marks)) {
    return existingSameHeaderAdmission()
}

// Packet: no mutation. The caller decodes at the existing scalar boundary.
return null
```

The scalar boundary uses one temporary adapter:

```kotlin
current = decodeCurrentAtomInExactScope(atom) // Exclude all other atoms.
temporary.restoreCurrent(current)           // Restore, do not re-admit.
delta = temporary.add(offered)              // The existing TaintGroup law.

if (currentStateChanged) {
    replacement = encodeCurrentStateAndKeepOtherAtomMasks()
    // All cancelable work is complete. Commit one prepared scope head.
    headers[scope] = replacement
}
return delta
```

`restoreCurrent` receives one complete current tree per typed header. It
must not re-admit the snapshot: doing so could remove a previously stored
STAR merely because a later ANY is already present. The adapter retains no
scalar current state after this call. Ordinary soft interner caches keep
their existing cache policy.

Replacement prepares independent mutable masks before commit. Immutable
mark sets and geometry can be shared. A T-only update must not mutate a
still-published shared T/U mask. Cancellation during preparation leaves the
published scope unchanged. Other complete initials, bases, layers, and atoms
are outside the adapter. Empty rows and removed sibling links are not retained.

FLOW compaction looks up only the complete initial, output base, and the
already eligible layers. Its same-tail/E/mark/protection tests are unchanged.
Borrow filters original scopes before it constructs transient typed views.
Neither path scans unrelated geometry to find sibling headers.

## 3. Constructive proofs and limits

[DiagonalTypedAdmission.lean](lean/ApSpec/DiagonalTypedAdmission.lean) uses the
existing AP pair denotation. Its laws have no run or FULL/GROUP gate.

| Law | Result |
| --- | --- |
| `any_covers_star_prefix` | A retained ANY prefix contains every offered STAR pair for the same complete original and atom |
| `star_covers_star` | Equal-path STAR coverage respects exclusion inclusion |
| `covered_later_star_union` | Suppressing the later covered relation keeps the represented pair union |
| `equal_root_exclusion_merge` | The existing E intersection represents exactly the union; reuses `Subsume.merge_inter` |
| `covered_plain_no_delta`, `covered_protected_no_delta` | An already covered ordinary or protected membership adds no work |
| `late_protection_is_work` | Plain coverage cannot suppress new protection |
| `unchanged_repeat_no_delta` | Repeating an unchanged complete membership adds no work |
| `protected_obligation_retained` | The update retains each supplied protected obligation |
| `handoff_any_prefix` | The retained ANY handoff pattern covers each removed descendant pattern, with the opposite endpoint and atom fixed |

These proofs use no new axiom, `sorry`, or classical witness selection.
They supplement the existing packet decode and per-membership progress laws.
The old per-cell residual proof does not itself prove cross-header Kotlin
normalization. Scalar-to-packet tests that compare two `DiagonalRelations`
instances can also miss a shared admission defect. The new tests use
`TaintGroup` as the independent admission oracle.

No theorem here proves a minimal final representation across all arrival
orders, whole-engine termination, or a fixed project memory/time saving.
No FLOW-vs-TAINT cross-tail coverage is introduced. A FLOW ANY summary still
cannot replace a TAINT STAR summary under the selected replacement law.

## 4. Validation controls

`DiagonalTypedAdmissionTest` contains ten controls. They check both arrival
orders, ordinary/protected deltas, prefix paths, late flags, STAR exclusions,
partial flags, scalar and packet paths, mixed mark masks, complete scope
separation, shared T/U rows, and FLOW compaction followed by readmission.

The final source was checked with the new controls and the existing
`DiagonalRelationsTest`, `DiagonalDeltaTest`, and `GeneralFlowCoverageTest`.
The external validation receipt records exact source hashes, compiled input
copies, commands, and results. Compiler memory is bounded; test JVM heap
settings are unchanged. The active project campaign and its source were not
modified. Broad integration checks remain the integrating change's gate.

On the unmodified revision, eight of the ten new controls fail on the stated
admission expectations. The STAR-before-ANY and scope-separation controls
already pass. The earlier standalone audit also checks twelve sequences and
45 admissions: scalar/packet current pair unions and protected obligations
agree, but the old deltas contain the redundant memberships.

## 5. Cost and remaining representation limit

The adapter runs only if a different tail/E header in the exact scope
contains an offered atom. It decodes only that atom. It can transiently copy
current geometry-map metadata for the scope to prepare an atomic replacement;
it does not decode the other atoms or enumerate mark products. This cost
must be measured if conflicting scopes dominate.

On the checked Java 17 HotSpot layout with compressed references and 8-byte
alignment, shallow field-layout estimates are:

```text
Old retained Header + geometry LinkedHashMap: 32 + 56 = 88 bytes
New retained Scope + geometry Rows:          24 + 72 = 96 bytes
```

Thus a single-header scope adds approximately 8 shallow bytes, with no new
per-scope object count, map, set, or entry. Additional typed siblings share
the primary scope entry. These are shallow layout estimates, not a measured
retained heap or a project memory prediction.

The old ANY-diagonal versus EXACT/must/cross-atom scalar-fallback separation
is outside this correction. It already exists at reference `583a58063`:
the diagonal owner accepts ANY only, unsupported rows use a separate
`ConclusionGroup`, and normalization compares FLOW rather than diagonal
TAINT. The selected proposal explicitly keeps these unsupported residuals.
They can be non-minimal without losing the semantic union. This correction
does not add cross-bucket normalization for them.

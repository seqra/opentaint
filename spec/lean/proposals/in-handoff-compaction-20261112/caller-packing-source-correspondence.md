# FULL caller-input packing: source correspondence

12 November 2026. Specification audit; production is unchanged. Inspected
HEAD: `5971701619350e51e277dd0e27c23c0e4aef9bd2`. The
[receipt](caller-packing-receipt.json) pins the cited runtime sources.
The selected contract is exact native logical-input storage, not eventual
coarsening. See [the combined specification, §15](../../../in-handoff-edge-compaction.md#15-pack-full-caller-inputs-with-exact-mark-relations).

## 1. Owners and native group identity

Runtime paths are relative to
`core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/`.

| Source | Required correspondence |
| --- | --- |
| `engine/SubscriptionManager.kt` | One runner owns a directory keyed by exact callee MethodKey. Keep the packed table inside that same owner, with the same subscriber registration. |
| `engine/CalleeSubscriptions.kt` | Preserve logical input groups, handles/order, candidate postings, separate ZERO handling, immutable fresh subscriptions and current-snapshot readers. |
| `store/AddedFacts.kt` | Native keys are complete CallerRef plus the original offered GroupKey. A private family may erase the singleton full mark; the decoded public key cannot. |
| `ap/Conclusions.kt` | GroupKey keeps kind, layer, current base, E, mx, tail and protection class. Preserve every coordinate. |
| `ap/FlowBackedProtection.kt` | Retained TAINT packets have one protection class. Keep the existing validation/splitting boundary; add no new OR-upgrade or acceptance policy. |

Only singleton nonzero FULL originals and legal FULL TAINT output
memberships are eligible. ND, FLOW, ZERO and GROUP remain scalar. Mixed
full output marks are factored by exact literal coordinates, not a single
mask applied to all positions. This change selects function caller-input
storage only. LocalInputDirectory, summary stores and enabled diagnostic
archives keep their existing representations. AddedFactAccumulator remains
available with its old contract for other owners.

## 2. Geometry and mark-map binding

`ap/Facts.kt` defines immutable MarkSet as sorted distinct IDs with content
equality and snapshot arrays. It is not GROUP abstraction or an assumed
bitmap. Retain existing full atom IDs and their RuleMarkCatalog meaning.

At one fixed complete family/header, a literal coordinate is:

```text
(current path, exact/any leaf slot, original full mark, output full mark)
```

The relation at each exact/any slot has a diagonal MarkSet and
changingByTarget[target] source MarkSet. In Lean, `changing` is a finite list
of pairs. `target_bucket_membership` proves correspondence with these
buckets. Map-key uniqueness and native set deduplication refine membership
without adding pairs. Geometry/header codes must be full injective keys,
not unchecked hashes or predicates on JVM types.

Keep exact and any slots separate, with the family's original any-tail/E.
Factoring an exact-only delta does not replace the admitted GroupKey with
the delta's simplified header. The model's factor/restore laws preserve
literal coordinates, isolate different source marks and distribute over
packet union. Native reconstruction must restore the canonical full root
and header before replay. The model does not implement that tree constructor.

`ap/ApManager.kt` and `ap/Premise.kt` restore the real original InitialAp
with its full mark and geometry. A mark-erased descriptor is never interned
as FLOW or submitted as a new initial/summary/demand.

## 3. Growth and scalar consumers

`ap/TrieOps.kt` implements mergeAddDelta as literal root/mark union inside
one GroupKey. TAINT merge carries the same class of protection to its
merged root and exact fresh delta. Hence stored cells grow by exactly the
fresh cells. The reference adapter calls this native merge on a transient
decoded old snapshot until direct cell admission has a native equivalence
proof. No second full standing archive is retained.

The relation model proves union, exact fresh difference, idempotence and
arrival-order membership equality. It does not assert that reversing
offers preserves insertion order. Keep native logical ordinals/handles.

`ap/Trie.kt` compares nodes by their literal leaf/child contents, paths and
derived shape fields, rather than requiring the same node address.
Restoring the same root and native header therefore preserves Facts value
equality/hash. InitialAp identity remains canonical through ApManager.
The source-cell posting laws prove exact coordinate selection and growth;
native implementation must maintain those derived postings consistently.

Preserve the distinction between:

- an immutable admission-time fresh delta for queued replay;
- the current standing union, which can grow before a later read;
- complete candidate snapshots copied before callbacks can mutate the owner;
- request-batch deduplication by logical input handle, not by shared family.

A target bucket can select original source marks. It cannot replace a
selected original's complete current snapshot by one selected cell. Joins
and request/source handling can inspect other marks and positions too.

The scalar-reply theorem proves exact pairs can be passed to the same pair
consumer. It does not equate native whole-packet application with independent
per-cell application. The spec requires full reconstruction before all
existing consumers. For a P/T -> Q/U relation composed with U -> T, the
existing protection logic must still see original T.

`engine/NeutralRelationBatch.kt` has narrower execution guards: STAR
original, empty E, nonstatic current base, uniform geometry and separately
certified operations. The new storage changes none of those guards. Decode
at unsupported boundaries; no mark-changing bulk composer is selected.

## 4. Lifetime and equality

`engine/JoinedCallerInputs.kt` moves the per-callee directory after workers
join and clears it on close. Joined writer binding must visit the same
logical snapshots. Never expose mutable maps to publishers/queued callbacks
or retain a decoded standing mirror in the joined phase.

Public CallerRef/Subscription/Facts equality and hashing stay unchanged.
Private keys compare full content. Logical input counts/order remain
distinct from physical template/cell counts. Counters must name their unit.

## 5. Checks and remaining native gates

`CallerMarkRelations.lean` passes 26 constructive claims, with only
`propext` and `Quot.sound` in successful audits. The first failed idempotence
proof and its hash/log are retained separately; the corrected source passes.
The later reserved-binder parser failure is also preserved separately.

`CallerPackingMarkSetControl.java` checks the target-bucket prototype with
native immutable MarkSet: every one of 512 relations over three opaque IDs,
sparse non-Cartesian pairs and immutable snapshots. **8,325 assertions
pass.** It performs no MarkTable ownership lookup and is not a production
directory, replay, request or concurrency test.

No production class was modified and no analyzer engine/project was run.
Before landing implementation, bind full native snapshot/delta equality,
candidate completeness, queued-fresh/current semantics, callback ordering,
fallback and joined release in differential tests. Known finding failures
are not waived. No whole Kotlin protocol formalization is claimed.

# Work reduction and handoff compaction proof package

This package accompanies [the specification](../../../in-handoff-edge-compaction.md).
It changes no analyzer code and starts no project scan. The campaign remains
stopped. The selected contract permits different intermediate runs but must
preserve eventual refined findings without an iteration limit.
That weaker contract applies to residual MAY coarsening across storage lanes.
Same-premise scalar MAY coverage and NORMAL record compaction already exist;
the spec proposes no replacement for them. The added C2,
loop-probe, disabled-diagnostic and FULL caller-storage changes preserve exact semantic results
on common completed runs.

## Checked model

`HandoffCompaction.lean` has 17 constructive claims. Run:

```sh
lean spec/lean/proposals/in-handoff-compaction-20261112/HandoffCompaction.lean
```

The model distinguishes two contracts:

| Component | What is proved | What is not proved |
| --- | --- | --- |
| `checkNeed` | A finite same/point/prefix certificate implies inclusion of semantic precise-request languages. | That native C2 emits identical initials for those requests. |
| `checkEdge` | Every source ND arm has an actual final-retained provider for every permitted point. | Changing a live ND AND into OR. |
| `checkPlan` | The complete semantic request union is equal before and after a checked joint cut. Kept providers belong to the original input. | Generalized MAY eventual findings in the Kotlin engine. |
| `retained_service_cover` | For any service reply relation, actual retained reply coverage gives service-union equality. | A new native entry adapter; existing C2/C5 laws must establish its premise. |
| `eventual_from_per_step_equality` | Per-step equality implies equality of finite eventual observations, without a cutoff. | Progress when MAY changes the steps or their timing. |

The executable fixtures check two ND arms with exact/STAR point requests,
reject a missing arm, reject empty mutual support and reject a different
header. A reordered input passes with the same retained providers. A mixed
MAY fixture passes **semantic** request coverage; the native activation gate
for that case remains open. Ancestor STAR coverage of a deeper exact point
is constructively refuted.

All quantifiers over points are unbounded. The Boolean checker checks a
finite suffix witness, not a finite enumeration of possible fields. No
Classical choice, `sorry`, `native_decide` or extra axiom is used. Successful
axiom reports contain only `propext` and `Quot.sound`.

## Native binding

`header` is an opaque code for the complete projected owner/ports,
direction, full conclusion mark and protection class. `arms` are opaque
codes for complete canonical paired-output selectors. They are not runtime
ND alternatives. Bind codes injectively to decoded native keys; do not use
an unchecked hash or JVM hierarchy as the binding.

An `Edge` is a modeled projected origin shape. A native certificate must
also name the literal original origin identity and prove that every modeled
arm and leaf is in its **complete** native projection. A final provider must
remain retained. This model does not allow a fabricated broader edge or a
provider which another cut has removed.

The zero/control constructor has exact opaque identity. It cannot be
covered by a DATA prefix. Nonempty exclusions, marks, physical ports and
protection are not erased by this model: either bind them in the full keys
under an existing exact-key theorem or reject the adapter. The new MAY
adapter is restricted to empty E in the specification.

Existing native laws are reused from:

- [Retained demand service basis](../../../retained-demand-service-basis.md):
  complete C2/C5 answer and support profiles, canonical keys, first-counted
  point-to-MAY **C5** adapter and arbitrary unchanged continuation state.
- [Individual retained-query service cover](../../../individual-retained-query-service-cover.md):
  separate individual and final-joint witness contexts.
- [Existing AP subsumption](../../../edge-subsumption-initial-emission-demand-intersection.md#3-relation-subsumption):
  NORMAL common-suffix relation cover, exclusion overlap, mark and H guards.
- [The earlier bounded review](../handoff-subsumption-review-20261112/README.md):
  13 relation/query claims, 12 request-order claims and actual isolated
  C2/C5/scalar controls. Those tests explicitly expose the different MAY
  initial families; they prove no whole-engine Y-only MAY deletion.

## Remaining proof gate

The native eventual-refinement simulation for the new cross-lane MAY
removals is not supplied by this package. Request-set inclusion is insufficient:
the first-field C2 emission and C5 image can differ. A native proof must
construct the required later precise derivation, preserve source and ND
permissions and typed control guidance, and account for early stopping.
Neither the temporary run-11 limit nor a passing finite fixture closes this
gate. Exact-service cuts remain available without that additional theorem.

`CurrentCompactionInventory.java` checks the current summary stores in both
arrival orders: scalar same-premise MAY removes its exact child, but a
packed diagonal MAY and scalar exact child can coexist. Same-head DEMAND
STAR/EXACT also coexist. All 8 controls pass on the pinned runtime JAR;
see [the inventory receipt](compaction-inventory-receipt.json). The IDs are
opaque, with no declaration-ownership lookup, analyzer run or project scan.
The old unrelated-C2-provider example is an exact-service certificate,
not a condition of the proposed MAY rule. NORMAL specialization/persistence
and projection remain existing machinery, as the spec's delta table states.

## Receipts

The first compile attempt failed on Lean Boolean theorem names and an
unexpanded STAR/EXACT match. Its source hash, diagnostics and failed audit
are preserved as `lean-attempt1.*`; those are not successful claims.
`lean-attempt2.*` records the successful corrected check. The final
`lean-receipt.json` pins the checked source and successful 17-claim audit.

## Added work-reduction model

`WorkReduction.lean` has 23 checked constructive claims. It proves empty
strict-descendant emission and ordered stream filtering; descriptor
materialization membership under a decoding round trip; a constructive
first-extra witness; equality of trial decisions and the first accepted
budget; and diagnostic noninterference with unchanged enabled processing.
Its finite controls reject a late extra companion, a different scope and a
missing-only observation which has no extra member. The successful audit
uses only `propext` and `Quot.sound`.

```sh
lean spec/lean/proposals/in-handoff-compaction-20261112/WorkReduction.lean
```

The [source correspondence](work-reduction-source-correspondence.md) supplies
the native assumptions and current source pins. The new proof does not
formalize the whole Kotlin trie, observer or driver. It does not change or
close the MAY eventual-progress gate above. The first two work-reduction
Lean attempts failed on reserved binder names; their logs and source hashes
are preserved. The corrected source passes; see
[work-reduction-receipt.json](work-reduction-receipt.json).

`NativeWorkReduction.java` passes 182 native operator assertions against the
previously pinned JAR, including actual `InitialAp.toPattern` round trips.
See [the native receipt](work-reduction-native-receipt.json). Its first
failed Java compile is preserved separately. These are empty-E operator
controls, not a modified-trie test, loop-adapter parity suite or project run.

## Exact diagonal and changing FULL caller relations

`CallerMarkRelations.lean` adds 26 constructive claims for the newly selected
storage extension. It models diagonal mark IDs plus exact changing pairs
at each complete geometry/header key. Its target-bucket theorem binds the
pair list to `changingByTarget[target] = source MarkSet`.

The laws cover exact decode/encode, add/union, fresh differences, duplicate
idempotence, arrival-order membership equality, source/target selection,
literal packet factoring/reconstruction and separation of different keys.
They also give exact source-to-cell postings and their growth law.
Fixtures reject Cartesian products and retain one-to-many/many-to-one pairs.
The successful axiom audit uses only `propext` and `Quot.sound`.

```sh
lean spec/lean/proposals/in-handoff-compaction-20261112/CallerMarkRelations.lean
```

See [the packing receipt](caller-packing-receipt.json) and
[native source correspondence](caller-packing-source-correspondence.md).
The first compile failed on an incomplete idempotence proof; its diagnostics
remain in `caller-packing-attempt1.*`. The corrected final source passes.
The later parser failure during the posting extension is preserved in
`caller-packing-attempt3.*`; it is not a successful claim.
The model does not implement native root reconstruction or the whole caller
protocol. Existing scalar consumers must still receive the complete native
snapshot, not an independent callback per cell.

`CallerPackingMarkSetControl.java` is a proof-side target-bucket prototype
using the actual immutable native MarkSet. All 512 relations on three opaque
mark IDs and sparse/snapshot controls pass: **8,325 assertions**. The
[native receipt](caller-packing-native-receipt.json) pins its JAR and source.
It runs no production directory, analyzer or project. Implementation must
still pass the spec's native snapshot/delta, replay, request, order, index,
fallback and release tests. This feature does not use the MAY progress gate.

## Implementation algorithms

The [implementation proposal](../../../../docs/design/bidirectional-work-reduction-implementation-20261112.md)
adds `ImplementationAlgorithms.lean`, with 13 constructive claims:

```sh
lean spec/lean/proposals/in-handoff-compaction-20261112/ImplementationAlgorithms.lean
```

Its certificate model proves that removing one provider leaves unaffected
certificates valid. Repairing the affected certificates and the new removal
against the final retained set preserves the provider-membership invariant.
Native service correctness still comes from the complete keys and the
existing retained-service proof; a provider ID alone does not prove coverage.

Its storage model proves ordered source projection, exact source partition,
preservation of other sources during fallback, complete native-join input,
stable handle and removal of the migrated source from packed authority.
The native join remains an opaque supplied operation; its equality/delta law
is an existing native obligation, not inferred from this migration model.

The successful [receipt](implementation-algorithms-receipt.json) pins the
source and Lean output. Its axiom audit uses only `propext`/`Quot.sound`, or
no axioms. Three failed proof attempts remain in their own logs/receipts.
Neither these models nor the proposal change runtime code or close R3's
native MAY progress gate. No analyzer or project scan ran for this addition.

The [proposal validation receipt](implementation-proposal-validation.json)
records all four model checks (79 claims), local link checks and unchanged
production scope. Its run labels refer to existing measurements, not new
engine executions.

## Runtime binding

The [runtime binding](runtime-binding.md) maps the checked local laws to the
implemented owners and native differential controls. It preserves the R3
proof gate and states the storage fallback and release boundaries.

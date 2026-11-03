# Cross-feature integration audit and composition dossier

Status: **SELECTED DESIGN COMPOSITION; NOT IMPLEMENTED**.
Reference runtime: `050b83cfb7b2e75856ea113c44d0a2d6b707250d`.

## 1. Audit result

The three component designs are compatible under the explicit port
contracts below. No new ZERO, Target, source-permission, field, mark,
layer, ND, static-visibility, or IR policy is required. The archived
internal-ZERO-control draft is not part of this composition.

The audit inspected the three detailed design documents and the reference
runtime. It did not run native tests, a Kotlin implementation, or a new
project experiment. The component receipts and their input hashes are
pinned separately from the composition model.

### Common ownership and phase contract

```text
LIVE owner quantum:
  P2 scratch active only inside MethodBlockRuntime.work; native fallback
  outside that interval; clear scratch in finally, including cancellation.

Successful complete physical join:
  Assert counted work/queues/callbacks idle.
  Capture exact driver exports, diagnostics and NORMAL contributors.
  Move local and physical actual-input directories to JoinedBindingLease.
  Detach native admitted/Target/raw-write/private-seed source inventories.
  Release execution and current-delivery owners.

Run-1 completion:
  Apply unchanged pruning to both-layer admitted stores plus private B.
  Ingest the exact old normalized/ordered attachment stream into P3.
  Bind through the same moved inputs; append the same bound extras.
  Freeze detached compact completion; close lease/temporary source readers.

Result and driver:
  Return frozen method exports plus compact completion.
  Use the existing persistence/report/handoff/contributor commit sequence.
```

`JoinedBindingLease` is the single actual-input ownership API. P3 consumes
its exact local/physical visits; it does not create a second input archive.
P3's final `FrozenCompletion` contains no lease, actor, context, subscriber,
or callback to a live owner. P2 caches contain only fixed snapshot/row/packet
references for one owner quantum. They cannot cross the join or become a
standing catalog. Existing observer closures end with the method runtime.

Native admitted stores remain reachable from frozen method exports until
the driver consumes them. Closing temporary reader wrappers must not clear
these shared native stores. The raw NORMAL Target inventory remains for
reporting; only outgoing anonymous DEMAND Target rows feed static terminal
attachment. A compact static catalog is not the report's raw Target store.

### API and typing requirements

| Boundary | Required exact contract |
| --- | --- |
| P1 local inputs -> binder | All existing runtime entries, including saved-only entries; full method/scope/point/original/layer/group and annotations |
| P1 physical inputs -> binder | Same complete callee and caller scopes, call/stage, current merged Facts and existing candidate order |
| P1 detached source -> P3 ingestion | Actual state/source order; original root/scoped branch; exact producer exits and empty entered ports; no pre-release survivor enumeration |
| Prune -> catalog | Prune still reads both layers/private B. Catalog attachments still read `demandEdges(FORWARD)` and outgoing DEMAND terminals only |
| Raw binding -> normalized catalog | Raw ID/field and FLOW-exclusion data remain raw until unchanged AP application. Normalize only at the existing ingestion sites |
| P3 -> P2 native static fallback | Same complete ordered public query streams, callback arguments/early stop, owner visibility, typed ZERO/Target and port adapters |
| P2 checked C5 -> native AP | Actual normalized complete original, exact view/scope/exit/policy, unchanged `canStoreInitial`, output matching and per-row FL+1 budget |
| P2 memo -> work lifecycle | Synchronous hits/misses and fallback; no queued cache work, no extra completion rule, finally cleanup and entry checkpoints |
| All keys and retained values | Existing equality/hash unchanged; packet keys add the full protection mask in private wrappers only |

No code adapter can replace an unknown/oversize/unsupported P2 plan with an
empty answer. Run-2/static-carry/completion/control/Target cells keep native
fallback. P3 must preserve that native oracle, even where P2 does no work.

### Integration clarifications confirmed by the audit

The final P3 pipeline now agrees with P1: close temporary binding inputs
after catalog freeze and before `RunResult` return. Keep this single phase
order in the canonical proposal. It does not authorize a new driver
transaction or a different lifetime for frozen native summary exports.

Do not use one untyped `targets` field for all inventories. The common API
must name raw NORMAL/DEMAND Target inventory separately from outgoing
DEMAND-only static attachment input. Do not infer either from a released
Target delivery index.

These are interface/lifetime clarifications. The audit found no selected
behavior that requires a new analyzer semantic decision.

## 2. Constructive composition

The module uses only functions and the component types. It adds no new
analyzer data model. `ingest` is the unchanged deterministic adapter that
maps the retained source/input footprint to the exact old ordered static
row stream, including bound extras. P1 preserves that footprint. P3
preserves the complete query oracle built from that row stream.

The observer port has two adapters:

```text
enclosingNative(unchangedStaticOracle, completeQueryKey)
enclosingPrepared(unchangedStaticOracle, completeQueryKey)
```

The explicit `preparedPort` prerequisite states their complete ordered
results are equal. P2's component model supplies its finite factoring,
fallback, normalization, protection, DATA-only omission and exact ticket
laws. Kotlin must still implement their native adapter conditions. This
package does not assume that a Boolean entry match is complete observation
equality, or infer Target permission from a DATA-only plan.

The composed results are:

| Theorem | Result |
| --- | --- |
| `release_preserves_complete_source_stream` | Same ordered normalized source and bound-extra stream after release |
| `release_and_packing_preserve_complete_oracle` | Same complete static query function |
| `combined_complete_observer_port_equal` | Same adjacent/repeat/labelled admissions and complete enclosing results |
| `combined_finite_restriction_program_equal` | Same result for every finite adaptive query/restriction program, with quantum-local memo |
| `combined_handoff_and_report_projection_equal` | Same deterministic handoff/report projection from complete exports and equal program result |
| `combined_static_callback_trace_equal` | Same callback accumulator and consumed prefix through an early false |
| `NORMAL_and_DEMAND_Target_export_ids_equal` | Same raw Target values/IDs and outgoing Target inventory, independently of catalog encoding |
| `packed_oracle_preserves_finite_recursive_compositions` | Same finite sequence of query-dependent static composition states |

The result is conditional on equal component port values, not on a measured
hit rate or work count. Exact ordinals and callback order are covered;
different speed, allocation and diagnostic native-check counts are allowed
where the component designs say so.

## 3. Limits and future native gate

The checker imports and rechecks exact pinned models. It does not verify
Kotlin source, store aliases, class fields, native AP transfer, callback
purity, concurrent quiescence, cancellation timing, memory safety, JVM key
identity, garbage collection, resource-limit outcomes, or whole-driver
convergence. Handoff/report equivalence here is a deterministic function
projection of equal inputs, not an unconditional project-quality proof.

Before implementation acceptance, use the existing observer/builder/binder
as differential oracles, then test the composed lifecycle: P2 scratch is
empty at joined seal; detached readers cannot reach an actor; static native
fallback sees the same P3 stream; complete exports survive input closure;
late events cannot cross the barrier; failure publishes neither partial
guidance nor contributor/report state. The selected project experiment
matrix remains unchanged. No new performance claim follows from this package.

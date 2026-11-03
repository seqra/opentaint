# Selected-design proof dossier: joined state release

Status: **SELECTED DESIGN; NOT IMPLEMENTED**.
Runtime reference: `050b83cfb7b2e75856ea113c44d0a2d6b707250d`.

The [design](../../../../docs/design/bidirectional-joined-state-release-design-20261103.md)
keeps analyzer semantics unchanged. It releases execution and current
delivery owners after successful join, before static pruning/binding.
It retains actual input directories, native admitted relations, raw and
outgoing Target inventories, raw writes, private seeds, required exports,
and contributor/diagnostic snapshots.

## Model and proof map

| Requirement | Model construction or theorem |
| --- | --- |
| Existing conditional output equivalence | `PostJoinRelease.release_then_binding_same_final_state`, including success and failure |
| Join only after physical owner stop and finite pending work drain | `idle`, `join`, `join_requires_idle`, `join_requires_stopped` |
| No post-join execution, publication or delivery | Original `admitLive` laws; selected `mayLive` joined/captured/released laws |
| Capture before release, with a sealed input lease | `capture_complete_exports`, `release_requires_capture`, `release_requires_lease` |
| Exact method/block/entry routing | `localAt`, `exact_local_owner`, `no_cross_scope_local_read` |
| Exact complete callee routing | `callersAt`, `exact_callee_owner` |
| Same finite candidate enumeration | `concrete_local_binding_sequence_preserved`, `concrete_physical_binding_sequence_preserved` |
| No AP key/value rewrite | `release_preserves_retained`, `capture_does_not_rebind_inputs`; all immutable Payload fields remain equal |
| Preserve summaries, NORMAL IDs, DEMAND Targets, seeds, contributor rows and diagnostics | `all_driver_exports_preserved` plus explicit inventory laws |
| Keep raw killed-write evidence | `all_raw_writes_preserved` |
| No second standing input archive | `detach_moves_exact_values`, `detach_does_not_keep_two_standing_directories` |
| Preserve order/multiplicity, close once | `detach_preserves_order_and_multiplicity`, detach/release/dispose idempotence |
| Drop the moved owner reference after binding | `moved_then_closed_has_no_directory_root`, `close_joined_idempotent`; retained aliases remain a separate obligation |
| Failed binding/driver validation cannot publish new accepted reports | Failure laws; `abort_preserves_prior_reports` |
| Failed run cleanup | `failed_join_cannot_capture`, `failed_join_cannot_bind`, disposal laws |
| Removing a root is not sufficient for reclamation | Executable finite `actor_callback_alias_keeps_execution` witness |
| Removing actual inputs would lose data | Executable finite `removing_input_reader_would_lose_input` witness |

`StaticRow`, `Payload`, `TargetRow`, and input descriptors are finite value
certificates. Their fields carry exact owner/port/raw IDs, full premises,
fields, marks, exclusions, layers, protection and Target IDs. The model
retains their values without rebuilding them. These descriptors do not
define AP transfer, mark composition, or new matching rules.

## Explicit prerequisites

1. The real counted-Work protocol reaches a successful COMPLETE and all
   runner jobs join. No queued callback can later mutate a detached input.
2. Kotlin capture covers every read in the design's audit. In particular,
   inputs include saved-only runtime entries with no instantiated state.
3. The actual local/physical matcher and traversal order are unchanged.
   Both binding paths use the exact same immutable retained footprint.
4. Hash keys and canonical AP values remain immutable. Ownership transfer
   moves the original directory; it does not clear a shared backing key.
5. The released roots have no remaining alias through a reader closure,
   callback, inner class, port, handler, or runner.
6. Current record persistence, source permission, report preparation and
   contributor publication remain external driver contracts. The design
   does not add rollback to `PersistentRecordStore` or change its order.
7. Cleanup runs only after a successful physical join. If join fails,
   runner-owned values are neither read nor cleared while mutation remains
   possible.

These prerequisites are obligations for the implementation and native
controls. Pinning inspected Kotlin source does not prove them. In
particular, the model cannot prove a JVM reference has the same identity,
that a captured Kotlin lambda has no outer reference, or that the GC
reclaims a measured number of bytes.

## Counterexample-guided limits

The original `execution_read_breaks_equivalence_witness` demonstrates that
release is invalid if the binder still reads execution state. The selected
finite object graph demonstrates that a reader closing over an actor can
retain the supposedly released instruction store. The detached reader
witness keeps the actual input while excluding that execution path.

These are executable finite witnesses, not general JVM reachability
theorems. The 4,268,877,960-byte MAT union is a removal simulation from one
captured process. Neither that number nor the model proves a patch saving,
binding completion, run-2 convergence, report equality on projects, or a
speedup. No Kotlin/native/analyzer experiment was run for this design.

The generated [checks.json](checks.json) and [audit.txt](audit.txt) contain
the exact checked declarations and input hashes. A PASS validates only
the constructive model and its stated scope.

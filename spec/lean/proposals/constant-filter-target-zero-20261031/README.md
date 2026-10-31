# Constant filtering and Target-guided ZERO: proposal proofs

This package supports the
[implementation proposal](../../../../docs/design/bidirectional-constant-filter-target-zero-implementation-20261031.md).
No analyzer implementation is changed. The user selected the exact-demand
C2 correction: MAY `[any]` cannot answer `$`. The earlier example which
used that old cell is withdrawn as a reason for backward NormalTarget
lookup. Proposal section 10.3 specifies no special action for an unanswered
demand.
An unsatisfied offer creates no initial, and an all-unsatisfied iteration
requires no retry, copied demand, synthetic Target, or forced continuation.

Admission has a direction: demand `p.[any]/T` plus submitted `p.$/T`
emits `p.$/T`; reversing demand and submitted tails emits nothing.
Existing base, mark, geometry and field-budget checks still apply.

The caller layer model is conditional on a permitted complete match. Its
layer theorem cannot grant initial admission or silently narrow ordinary
saved-record matching. NORMAL report IDs still require NORMAL complete
support all the way to a configured root.

```sh
python3 spec/lean/proposals/constant-filter-target-zero-20261031/check.py
```

The checker uses pinned Lean `leanprover/lean4:v4.33.1`. Each command uses one
worker, one CPU, a 768 MiB compiler limit, and a 90-second bound. Build and
audit logs stay in ignored `spec/lean/.lake/verification/`. The maintained
JSON receipt binds the proposal, models and checker. Rerun after edits.

The checker audits all explicit public theorem and definition declarations.
It rejects proof holes, added axioms, noncomputable definitions, compiler
warnings, and axiom dependencies other than `propext` and `Quot.sound`.
There is no `Classical.choice`. Executable witnesses include finite caller
closure, complete contributor search, and an append-only report registry.

## Selected contract

```text
NORMAL sink binding -> NormalTarget(reportId)
DEMAND sink binding -> anonymous DemandTarget
accepted reverse actual GEN -> anonymous DemandTarget
NORMAL Target + NORMAL caller input -> same NormalTarget(id)
NORMAL Target + any DEMAND support -> no terminal result
DemandTarget + permitted complete support -> anonymous DemandTarget
backward NormalTarget processing -> no effect
persisted ZERO -> NormalTarget replay -> no effect; keep settled report ID
persisted exact owned P -> NormalTarget -> no new insertion/publication
final report <- configured-root ZERO -> NormalTarget(id)
future Target guidance <- DemandTarget only
```

`D_c=Target` accepts actual ZERO only. `D_p=ZERO` accepts ZERO and either
Target constructor, preserving the exact constructor and ID. Ordinary
`D_p` rejects Target. Handoff is paired, including ZERO premises. These
are DEMAND publication rules; there is no blanket DEMAND Target C5 bypass.
Complete raw NORMAL terminal relations have a separate retention and
reporting role before future-run selection. That retention is not new AP
admission permission.

Actual GEN means a forward edge from ZERO to nonzero AP. Conditional
predicate-source transfers and opposite-record reads do not create a new
terminal GEN event. Existing action seed identities remain separate.

Constant filtering rejects the entire executable packet if its conclusion
or any premise member has a Constant base. It does not change IR literals,
AP payloads, rule conditions, or the older analyzer.

## Theorem map

| Module | Checked claims |
|---|---|
| `ConstantBoundary` | Whole-packet acceptance is unchanged; no Constant conclusion/member survives; no ND weakening; no callback for a rejected packet; constant-free store closure; preservation of every explicitly all-intermediate-safe route |
| `TargetZeroKernel` | Actual-ZERO-only entry; paired C5; Target label preservation; paired ZERO handoff; selected Target layers; caller layer/ID composition; strict actual-GEN scope; exact root report test; finite supported caller routes |
| `TargetZeroRegistry` | Lookup points to its key; distinct keys have distinct IDs; append preserves old IDs; fresh append gets a fresh ID; executable registration witness |
| `TargetZeroND` | Arbitrary finite layer aggregation is NORMAL iff all contributors are NORMAL; complete binary same-call join; exact origin union; duplicate seed membership independence; executable complete pair witness |
| `TargetZeroSourcePermission` | Explicit AP-adapter countermodel for lost GEN permission; absent permission emits no data; an abstract marked requirement restores the finite route; raw NORMAL publication is separate from paired DEMAND C5 |
| `InitialEmissionExact` | MAY is rejected for an exact demand at every prefix; EXACT/MUST use unchanged geometry, mark and full-budget checks; empty emission creates no helper initial, witness or ZERO fallback |
| `UnansweredDemand` | Rejected admission is a no-op; all-unsatisfied finite batches have no completion action; duplicate rejected offers do not create work or Targets |
| `SelectedTargetApplication` | Complete all-NORMAL support retains a NormalTarget ID; any DEMAND contributor or required demotion rejects it; existing DemandTarget stays DEMAND |
| `NormalTargetPersistence` | Exact owned-key dedup, forward-only reads, settled ZERO replay suppression, retained root-ID membership and nonzero saved application to a fresh caller key |

Important names:

```text
ConstantBoundary.admitted_iff
ConstantBoundary.nd_with_constant_rejected
ConstantBoundary.nd_not_weakened
ConstantBoundary.rejected_has_no_callback
ConstantBoundary.save_preserves_constant_free
ConstantBoundary.safe_route_preserved
ConstantBoundary.Controls.lost_route_is_intentional

TargetZeroKernel.target_entry_zero_only
TargetZeroKernel.c5_accept_target_iff
TargetZeroKernel.c5_target_label_preserved
TargetZeroKernel.handoff_zero_premise_paired
TargetZeroKernel.normal_target_overrides_ordinary_selection
TargetZeroKernel.accepted_gen_target_precedes_downstream_filter
TargetZeroKernel.conditional_transfer_cannot_create_gen_target
TargetZeroKernel.final_report_iff
TargetZeroKernel.demand_target_never_reports

TargetZeroRegistry.append_preserves_existing_id
TargetZeroRegistry.registeredIdWitness
TargetZeroND.join_normal_iff_all_normal
TargetZeroND.output_iff_complete_pair
TargetZeroND.outputPairWitness
TargetZeroND.duplicate_seed_independent

TargetZeroSourcePermission.demandPublicationPairWitness
TargetZeroSourcePermission.Controls.raw_root_report_survives_future_selector

InitialEmissionExact.any_actual_rejected_at_every_path
InitialEmissionExact.exact_actual_uses_existing_emitter
InitialEmissionExact.must_actual_uses_existing_emitter
InitialEmissionExact.any_actual_has_no_callee_witness
InitialEmissionExact.zero_not_a_nonzero_fallback
InitialEmissionExact.Controls.exact_refines_any_but_any_does_not_satisfy_exact

UnansweredDemand.rejected_offer_leaves_state_unchanged
UnansweredDemand.all_unsatisfied_batch_unchanged
UnansweredDemand.all_unsatisfied_no_initial_no_auto_target
UnansweredDemand.duplicate_unsatisfied_no_effect

SelectedTargetApplication.normal_keeps_id
SelectedTargetApplication.demand_contributor_rejects_normal
SelectedTargetApplication.demand_native_classification_rejects_normal
SelectedTargetApplication.failed_application_creates_no_target

NormalTargetPersistence.contains_means_no_owned_insertion_or_publication
NormalTargetPersistence.all_backward_normal_reads_none
NormalTargetPersistence.settled_zero_replay_none
NormalTargetPersistence.skipped_zero_adds_no_final_report_id
NormalTargetPersistence.saved_nonzero_new_normal_caller_can_apply
SelectedTargetApplication.backward_current_normal_application_none
```

The finite controls include nonreturning methods, mixed caller layers,
premature future-run filtering, unrelated methods, same/different sink
keys, distinct conditional premises, partial ND, cross-call contributors,
mixed ZERO/nonzero origins, and coexisting NORMAL/DEMAND Targets.

## Limits and remaining implementation proofs

- Constant endpoint freedom alone is insufficient for old-route equivalence.
  The module constructs an old nonconstant-to-Constant-to-nonconstant route
  and proves that the selected filter removes it. It does not prove no FN
  for all old programs.
- Ordinary AP emission and restriction are parameters. Their Kotlin
  implementation, marks, tails, fields, exclusions, protection, type filters,
  complete NNF bindings, and call mappings remain adapter obligations.
- Supported finite caller closure assumes the explicit C5 support at each
  hop. It does not prove that production creates every such support.
  Unsatisfied demand requires no special continuation under the selected
  contract. The admission no-op is modeled after saved-summary replay;
  it does not undo valid effects already produced by that replay.
- The old source-permission fixture is in `HistoricalPreCorrection`. Its
  MAY-to-EXACT helper step is invalid under the new C2 rule. It is not a
  selected regression or an argument for a new backward NormalTarget
  channel. The separate raw-NORMAL and paired-DEMAND publication laws are
  still current. Old NORMAL-to-DEMAND promotion algebra is reference only.
  `SelectedTargetApplication` is the selected terminal application rule.
- The executable origin join has two slots; the layer theorem is general.
  Arbitrary production ND geometry and same-invocation matching need adapter
  tests. Never infer complete ND evidence from a last-arriving contributor.
- Same-key IDs are stable within the modeled append-only catalog. Production
  rule identity, cache rebuilding, synchronization, and catalog lifetime
  must implement those laws.
- NORMAL Target retention, current/saved replay, root report persistence,
  source seed permissions, and removal of every unguided ZERO path require
  implementation tests. The model does not validate Kotlin coroutines,
  required-send routing, cancellation, or incomplete barriers.
- Persisted ZERO replay suppression uses a settled-effect certificate;
  report membership must already hold for every committed ZERO row.
  The model does not infer root reporting from a ZERO premise alone.
  Production fixed-point completion and barrier ordering must establish
  that invariant. Owned-row publication dedup does not suppress applying
  a saved nonzero relation at a new eligible NORMAL caller.
- A proof that duplicate seed insertion preserves a finite join does not
  permit dropping a different sink's metadata when anonymous Target dedup
  returns no delta.

No whole-runtime equivalence, whole-project no-FN, convergence, complexity,
or measured speedup claim follows from the proof receipt. Its PASS means
the listed proposal kernels and axiom audits pass. Implementation and
project tests remain separate gates; no pending admission workaround is
part of the selected proposal.

## Current AP controls

The optional controls exercise existing compiled AP classes. They do not
run the analyzer, Gradle, or a Target implementation.

```sh
python3 spec/lean/proposals/constant-filter-target-zero-20261031/controls/check_ap.py \
  --compiler-options core/opentaint-dataflow-core/opentaint-dataflow/build/20261029_8894186253707317018.compiler.options
```

Use the actual existing compiler-options file for the local build. The
checker does not trigger a build or guess a different classpath. It binds
source and bytecode hashes separately; it does not prove the bytecode was
built from those exact source bytes. Its retained receipt is
[`controls/checks.json`](controls/checks.json).

- `TerminalBoundaryApControl.java`: records the pre-correction runtime
  behavior. Its MAY actual creates a NORMAL exact initial under the old
  emitter; the selected C2 correction must reject this step. The control
  remains evidence of the behavior being removed, not an expected selected
  result. Its independent field-cut, GEN and record checks are unchanged.
- `NormalTargetCurrentGateControl.java`: 35 concrete demand patterns,
  35 actual facts, 314 NORMAL initial instances, and 2,967 matching
  consumer cases under the old emitter. No matching case in that old
  bounded search has empty emission. Revisit its expected cells after the
  C2 correction; the old count is not a proof about the corrected emitter.

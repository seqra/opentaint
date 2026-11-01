# Demand-relative restriction: implementation proof dossier

Date: 1 November 2026. Status: constructive design evidence. No runtime
implementation or project measurement is part of this dossier.

- [Specification](demand-relative-summary-restriction.md)
- [Specification proofs and scope](demand-relative-summary-restriction-proofs.md)
- [Implementation proposal](../docs/design/bidirectional-demand-relative-summary-restriction-implementation-20261101.md)
- [Adapter proof package](lean/proposals/demand-relative-summary-restriction-implementation-20261101/README.md)

Follow [proof-guide.md](proof-guide.md). All existence witnesses in these
models use executable finite operations. The checker rejects classical
choice and unproved declarations. It binds the specification, proposal,
models, dossier, and reviewed runtime sources by hash.

## 1. Semantic reference and technical adapters

The specification's 162 theorems remain the selected local theory. The
existing C5 selects a complete row; its own Dp determines the extra cut.
The actor admits only that final result. NORMAL persistence has no raw
fallback. These are the selected semantic changes, not optimizations that
preserve the old unrestricted NORMAL output set.

The implementation adds technical adapters to that reference:

```text
packed leaf/delta delivery -> same finite reference result set
admitted store views      -> same final-header handoff selection
Reach early completion    -> same exhaustive result set
measurement collection    -> distinct populations and attributed stages
```

The adapters do not change C2, instruction transfer, initial layers,
field/mark exclusions, cleaners, aliases, source permissions, ND binding,
Target rules, or the global body limit. They introduce no new semantic
fields or equality/hash behavior.

## 2. Fixed-gate leaf union and fresh deltas

[AdapterPipeline.lean](lean/proposals/demand-relative-summary-restriction-implementation-20261101/AdapterPipeline.lean)
imports the actual executable scalar C5/cut gate from the specification
package. Its finite packed reference is `flatMap gate leaves`.

It proves:

```text
RelativeImplementation.gate_distributes_over_leaf_append
RelativeImplementation.gate_leaf_membership
RelativeImplementation.post_statement_delta_is_sufficient
RelativeImplementation.same_leaf_set_has_same_gate_set
RelativeImplementation.packed_result_has_pair_witness
```

If old leaves plus fresh semantic deltas represent the whole current
post-statement value, applying the fixed gate to those deltas gives the
same accumulated result membership as applying it to the whole value.
Every result retains one actual input leaf and one complete row witness.

This supports keeping the existing post-exit MethodEdgeStore fresh-delta
gate before summary admission. It does not permit destructive raw FLOW
replacement there. It also does not justify ignoring layer/protection
changes: those changes must appear in the semantic delta law.

The finite reference treats a protected upgrade as a semantic annotation
event. Real Facts equality omits protection. The Kotlin union, packed
mask and transport adapters must satisfy the existing monotone protection
contract and differential tests. The model does not prove those Kotlin
implementations by importing their source hashes.

## 3. Reach saturation, including Target admission

For fixed `raw = Reach(layer)`, the typed exact operation can return only
that same Reach, or no result. DATA exit selectors do not admit Reach;
ZERO exit selectors need the complete entry permission.

```text
RelativeImplementation.Reach.pair_result_is_original_reach
RelativeImplementation.Reach.any_result_is_original_reach
RelativeImplementation.Reach.first_reach_saturates_result_set
RelativeImplementation.Reach.pair_reach_iff_complete_permission
RelativeImplementation.Reach.target_probe_iff_nonempty_reach_result
```

The saturation theorem permits stopping after the first admitted Reach.
Any remaining accepted row adds the same element. The proof compares
semantic sets, not callback counts. Its witness is a complete row, not
independent entry and exit hits.

This preserves the existing short-circuit opportunity for `acceptsTarget`
without a new terminal lookup service. All existing local, control, and
virtual static routes remain available. AP-form ZERO endpoints from the
static walker must dispatch to this typed control behavior before budget
calculation. Their representation is not permission to give ZERO depth 0.

For DATA, the specification's two-budget counterexample still applies.
This implementation does not use the Reach theorem to stop DATA result
enumeration, even when the raw DATA fact appears fully covered.

## 4. One admitted relation and filtered views

The existing Admission and Integration models prove that stored rows,
pending publication, eligible native records, and NORMAL providers have
gate provenance. A newly cut NORMAL candidate enters the final-DEMAND
view and has no new NORMAL native record.

AdapterPipeline adds:

```text
RelativeImplementation.Views.frontier_is_final_admitted_view
RelativeImplementation.Views.header_selection_matches_existing_rule
RelativeImplementation.Views.ordinary_normal_singleton_is_not_guidance
RelativeImplementation.Views.all_final_demand_rows_are_guidance
RelativeImplementation.Views.diagonal_header_selection_is_key_independent
```

The extracted header predicate is equal to the existing AP selector,
including NORMAL ND and NORMAL backward-ZERO. The predicate operates on
final admitted rows. No separate mutable demand relation is required.

Diagonal scopes contain nonzero singleton originals. Their selection
depends on the final layer, not the decoded concrete key/mark. Thus the
filtered census can select a packed header before counting its mark
mask. Exact numeric census weights remain the existing runtime adapter.

The implementation must pass direction from stable run inputs. The proof
does not model actor resource release. A Kotlin test must build HandOff
after actor.freeze and show that the filtered view does not access the
released actor context.

NORMAL-provider provenance is not a ban on admitted DEMAND-FLOW replacing
unprotected DEMAND concrete results. The existing permitted coverage cells
remain. Neither proof package strengthens that coverage relation.

## 5. Measurement laws and diagnostic controls

[WorkloadAccounting.lean](lean/proposals/demand-relative-summary-restriction-implementation-20261101/WorkloadAccounting.lean)
is a measurement model, not an analyzer-performance proof.

```text
RestrictionMeasurements.outcomes_partition_attempts
RestrictionMeasurements.identical_cut_counts_do_not_identify_the_cause
RestrictionMeasurements.summary_attempts_are_not_fresh_memberships
RestrictionMeasurements.bounded_summary_can_produce_a_deeper_caller_fact
RestrictionMeasurements.two_producer_paths_and_two_actual_suffixes_have_four_candidates
```

For sampled per-row leaf attempts, rejection, selected-uncut, and
selected-cut form a disjoint partition. Attempts are not unique admitted
memberships. The same C5 compression counts can follow local generation
or current-summary delivery. A shallow summary prefix can also acquire
a deeper caller suffix during application, before caller C5.

These executable counterexamples justify the experiment's separate body,
delivery, saved replay, call-stage, and C5 measurements. C5 counts alone
cannot establish that an observed slowdown is intra-procedural. They also
cannot establish that it is inter-procedural.

## 6. Proof and implementation acceptance

Run:

```sh
python3 spec/lean/proposals/demand-relative-summary-restriction-implementation-20261101/check.py
```

The checker rebuilds the eight specification modules and two adapter
modules with Lean 4.33.1, then audits all explicit public theorems,
definitions, and abbreviations. Only `propext` and `Quot.sound` may occur
in axiom dependencies. A warning fails the check. The
[receipt](lean/proposals/demand-relative-summary-restriction-implementation-20261101/checks.json)
records the exact inventory and input hashes.
The current check passes 182 theorems, including 20 new adapter theorems,
and audits 303 declarations.

The checked scope remains local and constructive. Packed Kotlin AP
refinement, full FLOW/MUST/native/ND composition, runtime scheduling,
arbitrary source-permission recovery, general convergence, whole-project
finding equivalence, and speedup are not established by these kernels.
They are not assumptions that authorize hidden semantic changes.

The proposal requires production packed/scalar differential tests,
actor/store/persistence/handoff tests, existing regressions, and the full
selected project experiment. The post-implementation report must test
competing blow-up hypotheses and reproduce representative captured hot
patterns. No raw NORMAL cache or new local widening is part of that work.

Runtime remains at the reviewed c4 implementation. Latest measured
reached/completed/accepted iterations remain Stirling-PDF **run-8/7/7**,
conductor **run-4/3/3**, thingsboard **run-2/1/1**, OWASP **run-5/5/5**.

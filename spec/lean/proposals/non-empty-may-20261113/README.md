# Non-empty MAY proof dossier

The [complete specification](../../../non-empty-may.md) is the behavioral
contract. No production analyzer implementation is changed by this package.
It follows [the proof guide](../../../proof-guide.md).

## Reproduce

Use a fresh output directory outside the repository:

```sh
python3 spec/lean/proposals/non-empty-may-20261113/check.py \
  --out /tmp/non-empty-may-proof-check
```

The checker copies and compiles four modules with Lean 4.35.0, records
source/object hashes, and audits all printed theorem dependencies. It rejects
custom axioms, `sorryAx` and classical choice. Standard `propext` and
`Quot.sound` are the only permitted dependencies. Existential witnesses
are explicit paths, submitted facts, commands or retained memberships.
The current package audits 79 declarations. The frozen complete receipt is
`non-empty-may-20261113/complete-proofs-v1/receipt.json` under the external
data root linked below.

## Contract and checked results

| Contract | Result |
| --- | --- |
| MAY is EXACT union NE; branches are disjoint | `NonEmptyMay.may_partition`, `rooted_may_partition`, `branches_disjoint` |
| Nonempty means some first field, not a named first field | `nonempty_has_first_field`; `nonempty_admission_does_not_force_a_known_field` |
| Selected EXACT/STAR raw starts and first read | `may_offer_under_may_demand_starts_both`, `split_first_read_keeps_only_the_nonempty_branch` |
| Complete spatial C2 reference with FULL marks | `Policy` defines same/descendant/ancestor cases, seed layers, companions, MUST and run-2 exception |
| Initial depth and legal kinds, generic in paths/run/budget | `emitted_legal`, `emitted_no_may_or_ne_initial` |
| NE has no same-head raw EXACT initial | `no_same_head_empty_initial_under_ne`, `ne_raw_image_excludes_same_head_exact_for_every_domain` |
| Every NE query is an identical query of the MAY family | `every_ne_query_is_a_may_query`, for arbitrary paths, offers, marks, E and field budget in this model |
| Concrete dual starts retain D; FLOW companion is conditional N | `selected_two_concrete_starts_and_existing_flow_companion` |
| MUST query, prefix probe, strict STAR ancestor and run-2 exception | Four executable `Policy` theorems; no new MUST probing policy |
| C5 raw-image witness is executable | `raw_image_has_constructive_offer`, `every_admitted_summary_has_the_actual_raw_witness` |
| Normalized STAR is not a substitute raw witness | `normalization_erases_the_branch_distinction`, `normalized_alternative_is_not_a_raw_entry_witness`, `raw_exact_cannot_borrow_the_normalized_star_witness` |
| NE read can exhaust its suffix | `read_nonempty_to_may`, `read_can_produce_exact_root`, `nonempty_descent_resets_the_residual_to_may` |
| Write preserves the known child root | `write_may_retains_empty_at_child`, `nonempty_at_child_loses_written_root`, `write_child_may_includes_every_input_binding` |
| A real cut covers every removed binding by NE | `real_cut_is_nonempty`, generic in kept/lost field paths and old suffix |
| Cut support/mark/H and depth bounds | `real_cut_has_ne_demand_and_keeps_mark_protection`, `cut_respects_depth`, `cut_never_upgrades_demand` |
| Final C5 result uses its own Dp-relative bound | `final_summary_keeps_its_own_row_bound`; two-row executable example |
| Normalization preserves paths, marks, support and H, and keeps NE | `normalize_preserves_paths_marks_layers_protection`, `normalize_does_not_erase_ne` |
| MAY/NE same-premise output coverage | `selected_may_covers_nonempty`, `dropping_covered_nonempty_preserves_union`; generic operational query inclusion in `Policy` |
| Arrival order, idempotence and flag separation | `both_arrival_orders_keep_only_may`, `repeated_offer_is_idempotent`, `no_cross_protection_compaction` |
| Coverage/service transitivity | `coverage_is_transitive`, `service_cover_is_transitive` |
| STAR does not cover independent MAY/NE by matching heads | Two executable witnesses in `Coverage` |
| Legacy handoff keys versus the new tail | `star_exact_point_entry_table_is_still_equivalent`, `old_empty_exclusion_output_keys_agree_for_new_ne_too` |
| ND projection retains real members | `nd_projection_has_a_real_member`; executable AND application is not weakened |

The MAY→NE deletion proof has two parts. The removed output region is a
subset of the retained output region. At the same selector coordinate the
entire NE C2 command family, including seed layers and companions, is a
subset of the MAY family. The paired output selector/budget is unchanged
because the complete original premise is the same. Thus no removed row is
the sole authority for its positive query. Further store replacement still
requires the existing valid retained-provider laws.

## Model boundary and proof arguments for retained mechanisms

The model uses scalar Nat field strings. It implements FULL mark identity
and FLOW mx, finite field-E guards, seed support, literal H on conclusions,
C2 tables and C5. It does not claim to implement the IR, rule provider,
aliases, JVM types, array/class accessor weights, real ports or the driver.
These are checked by native adaptation and the acceptance programs below.

The raw-image reference accepts an explicit finite domain of legal offers.
Its witness theorem holds for every supplied domain. A sampled input dump
is not a complete domain. Production must implement the structural existence
predicate over the full legal grammar, not over previously observed offers.
The image witness is the actual raw initial; another normalized preimage is
not sufficient. Native base/shape/E/mx/static guards must remain in force.

Cut soundness is independent of the alphabet's field weights: the native
adapter must show that overflow removed at least one known field and kept
the indivisible static anchor. The constructed witness then has a nonempty
first field for every old-tail binding. Uncut MAY is a counterexample to an
unconditional MAY→NE relabel. Missing certificates remain broad.

Output intersection deliberately retains correlated STAR whole. It is not
ordinary unary meet. The model preserves this existing rule, the mark gate,
and the candidate's layer/H. A new same-head NE cannot become EXACT; a
deeper exit can consume the nonempty suffix and therefore get EXACT or MAY.
The table and scalar examples check these distinctions explicitly.

Complete FLOW normalization reuses the existing exclusion-aware contract.
No new NE-to-STAR normalization is selected. For legacy correlated FLOW
subsumption the original witness remains `r ++ suffix`; this proposal does
not change STAR transfer, exclusions or opposite-direction matching. New NE
members cannot enter that proof's STAR-only case. Existing same-tail FLOW
backing gains a literal NE case, with the same marks/support/flag guards.
Raw-entry and typed MUST integration must still be tested before landing.

Legacy late STAR/EXACT point-entry equivalence is unchanged by the new actual
tail: same-head NE rejects both, MAY supplies the same EXACT, and the other
path cases use the same point policy outside run-2. For the old Empty-E
MUST/STAR outgoing keys, NE remains NE at the same output head and becomes
MAY after an admitted unknown descent in either case. The full native
adapter must preserve these header and per-row-budget hypotheses.

ND coverage is about outgoing projection, not execution. For each original
member keep a retained witness with the right ports and complete paired
selector. The generic projection theorem constructs that actual member.
It is not permission to split a later-run executable ND summary into arms.

## Native evidence and required acceptance

[CurrentMayWriteTraceTest.kt](../../../../scripts/demand_experiments/non-empty-may/CurrentMayWriteTraceTest.kt)
passes against current C2/AP/C5 and checks the baseline write trace, FLOW
companion and exact root binding. Frozen receipt:
`non-empty-may-20261113/current-write-v1/` under the
[external data root](../../../../docs/reports/EXTERNAL_DATA.md).
The earlier `ProjectedMayCoverTest` checks the unchanged correlated/loss
branch operators. Neither test installs the new tail in the analyzer.

Before implementation acceptance, differentially test the scalar reference
and optimized C2/image/C5 for canonical and mixed packed inputs; all marks,
mx, E, H, static anchors, arrays, MUST and both directions; real loop ports
and Target/source routing; current/saved/opposite matching; source/cleaner
and alias transfers; and all arrival orders. Exercise every real cut site
in run-1 and later runs. Audit serializers, tail headers, indexes and old
`isAny` callers: NE admits no empty suffix and cannot use every MAY branch.
Keep legacy rejected rule shapes and ordinary run-1 static ownership.

Run the wrapper, successive-loop, no-leave and two historical Conductor
finding regressions without an iteration limit, then project validation.
This package proves neither global convergence nor full-program no-FN.
It contains no universal-workload bound or measured new-policy speedup.
No new project run is claimed; latest historical positions are in the spec.

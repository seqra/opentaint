# EXACT/MAY emission and local evidence: proof dossier

This package supports the [specification](../../../exact-may-emission-and-truncation-evidence.md).
It does not implement the analyzer policy. The remaining MAY-replacement
decision is explicit in specification section 8.

## Check

Use a new external output directory. No `.olean` or large data enters Git:

```sh
python3 spec/lean/proposals/exact-may-evidence-policy-20261113/check.py \
  --out /tmp/exact-may-evidence-proof-check
```

The checker compiles seven modules with Lean 4.35.0, including two reused
models. It audits 66 declarations and rejects classical choice, `sorryAx`
and custom axioms. Some declarations use standard `propext` and `Quot.sound`.
Every existential witness is a constructed seed, path or raw emission.

## Proof map

| Contract | Checked result |
| --- | --- |
| Complete scalar spatial selector | `Emission.lean` defines same/ancestor/descendant C2, first-field stopping, the requested run-2 replacement, marks, empty-binding gate and complete initial families. Typed base/E/budget/port guards are factored out explicitly. |
| No raw STAR seed | `family_has_no_star` and `emitted_initial_has_no_star` quantify over every output of that selector, including the extra prefix probe. |
| MAY cannot confirm | `may_family_is_demand`; reused `DualStarts.normal_provider_preserves_may_uncertainty` checks application of a NORMAL provider to a MAY input. |
| Constructive C5 image | `stored_image_has_executable_raw_witness` gives the emitted raw seed for every normalized key. It does not prove the Kotlin image decision procedure. |
| First new field | `explicit_first_field_example` and `both_first_field_starts_are_present` compute exactly the user-selected pair at f, plus the existing root prefix probe. |
| Admitted MAY views | `dropPrefix_sound`, `first_field_may_view_covers_all_original_bindings` and `deeper_demand_may_view_stays_inside_original_may` construct the retained suffix bindings. This geometric coverage does not turn D support into N or prove safe deletion of a MAY summary. |
| Wrapper | `ancestor_may_preserves_wrapper_query` computes both starts at a deeper demand head from a broad MAY offer, even under nonempty-only evidence. |
| Full-mark guards and exact complete field | `mismatched_mark_is_rejected`, `exact_complete_first_field_is_not_widened`, and the native concrete-layer test keep full-mark behavior separate from FLOW normalization. |
| Exact-empty rejection | Reused `Evidence.reject_exact_empty` proves rejection under complete binding evidence. `Capture.member_language_retained` proves that every recorded contributing language survives union; `excluded_empty_not_in_any_contributor` checks that union's negative certificate. |
| Evidence representation | Reused `mayEmpty_exact`, `merge_empty` and `merge_denotes` prove the one-bit query equivalent to suffix-language union. `rebased_empty_bit` handles an unknown child rebased below an ancestor. |
| Evidence update order | `first_real_cut_is_nonempty`, `unknown_duplicate_widens`, `known_duplicate_cannot_clear_empty` and `contributor_order_independent` check initialization and OR merge. Unknown is not an empty witness set. |
| MAY still has a route | `a_live_known_may_query_has_a_binding` and `a_live_unknown_may_query_has_a_binding` construct bindings; absence of epsilon does not justify rejecting MAY. |
| EXACT-first local queue | `Priority.may_dispatch_has_exact_quiescence` requires no ready/in-flight local exact work; dispatch removes exactly one queued job. |
| Late work and owner scope | `late_exact_preempts`, `dropping_reservation_too_early_is_observable` and `another_owner_need_not_wait` distinguish local priority from a global barrier. |
| Subsumption gap | `ViewCover` models both ordinary return branches, constructs the projected precise-input counterexample and the user's longer MAY binding. A matching NORMAL shape is not a complete method model. |
| Latest STAR-start alternative | `StarAdmissionComparison` isolates its descendant C2 change. Its genuine MAY-loss row is retained by the selected conclusion-tail guard, so it is not a counterexample to that guard. The empty-binding gate retains broad STAR offers, leaving STAR-driven repetition unresolved. See the [comparison](../../../../docs/design/bidirectional-star-may-admission-comparison-20261113.md); it does not prove the complete alternative policy. |

## Assumptions and limits

The selector model uses finite Nat field paths and FULL marks. The new
selector has no assumed global completeness theorem. Base identity,
class/field anchors, field weights, E/mx, literal H, control facts, ND and
physical ports remain native adapter obligations. MUST has a separate
forward-only legality guard; the spatial model does not make it legal backward.

Evidence is complete for the explicitly gathered contributors in its model.
Runtime soundness additionally requires capturing every **actual paired-C5
contribution**, including duplicate and compacted memberships, and rebasing
it at the right frozen demand row. The proof does not turn samples into
complete certificates or assume that observed history covers future code.

The normalized image theorem describes the reference operation. Before
implementation acceptance, the optimized image, demand trie, prepared C5,
loop probe, caller ticket and handoff compactor must equal that reference.
Its simplified `storedSeed` models normalization of a complete FLOW-to-FLOW
pair. Production normalization must inspect both endpoints; it must not
normalize an EXACT premise merely because its own mark is FLOW when the
conclusion changes marks.
Old emission-dependent proofs cannot be imported without checking their
changed hypotheses.

The scheduling model is one owner. It does not establish a global phase,
remote quiescence, termination of every run or freedom from MAY-to-MAY
cycles. Fair delivery and a finite local closure are conditions of the
usual fixed-point scheduling argument. No work is deleted by this priority.
The production adapter must classify mixed packets and high publications
correctly; the old full-queue publication barrier must not hide them.

## Native evidence

- [Six dual-start AP tests](../../../../scripts/demand_experiments/dual-starts/DualStartsTest.kt)
  pass for normalization, getter/copy operators, same-head MAY application,
  the descendant-result difference and concrete layer retention.
- [Projected-view counterexample](../../../../scripts/demand_experiments/dual-starts/ProjectedMayCoverTest.kt)
  passes: the ordinary second branch returns a real root T which the
  retained copy-shaped NORMAL provider alone does not return on the precise
  offer. It is a local AP test, not a complete driver finding-loss proof.

Both are source-Gradle offline tests. Their frozen evidence is outside Git:
`dual-exact-may-starts-20261113/native-v2/` and
`exact-may-evidence-policy-20261113/projected-cover-v2/` under the
[external data root](../../../../docs/reports/EXTERNAL_DATA.md).
The extended native STAR-start check passes in
`exact-may-evidence-policy-20261113/star-start-cover-v1/`.

No complete new-policy driver or project run was executed. Historical
wrapper controls finish at run-7 and run-5; project positions are recorded
in specification section 9. Full C2/C5/Target/static/ND/loop integration
and the uncapped principal regressions are required before claiming
whole-analyzer finding preservation. The pending replacement decision
must be resolved before this specification is advertised as finalized.

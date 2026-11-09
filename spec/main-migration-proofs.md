# Main migration: proofs and acceptance obligations

9 November 2026. Companion to [main-migration.md](main-migration.md).
Follow [proof-guide.md](proof-guide.md).

This dossier proves the selected adapter rules in a constructive component
model. It does not assert that a rebase was done or that the Kotlin analyzer
implements the new contract. Latest reached project iteration: not applicable.

## 1. Domain and proof boundaries

The model is [MainMigration.lean](lean/proposals/main-migration-20261109/MainMigration.lean).
Its domain has:

- A base and a finite path of already typed/interned accessor IDs.
- Serialized concrete/AnyField modifiers and canonical rule descriptors.
- Finite marked locations and Boolean rule conditions with AND, OR and NOT.
- Existing EXACT, STAR, MAY and MUST target tags.
- Original rule/action stamps and payload support headers.
- The selected shape restrictions, cleaner/reset reach and fallback policy.
- Bidirectional configuration projection and the controller exit gate.

`region(p,x)` requires equal bases and a prefix path. It includes p itself,
as the existing MAY/MUST rule-region interpretation requires. An exact check
requires the same position. The model evaluates conditions before the core's
existing negative-literal approximation; it does not strengthen that policy.

The source geometry model starts with an already enabled rule. It does not
make a hypothetical conditional source unconditional. Layers for actual
source execution, run-1 statics, GROUP, source permission and selected-cleaner
survivors remain in their existing engine components. `routePass` models
support-header framing around an existing geometry operation; it is not a
new AP concat definition.

The new ActionPosition wrappers are adapter types. The model does not add a
tail, analysis support label, mark atom or storage dimension. All existence
witnesses are computed by `split`, `bind`, `lower`, `bindSource`, the selector
or the explicitly defined policy functions. It uses no classical choice or
custom axioms. Boolean examples are kernel-checked with `decide`.

## 2. Proof map

| Obligation | Constructive proof in MainMigration | Scope and implementation check |
| --- | --- | --- |
| P01: preserve the concrete prefix before AnyField | `split_concrete`, `first_any_discards_only_the_suffix` | All finite modifier lists. Native binding must call main's helper and retain owner/type information. |
| P02: descriptor normalization is stable | `canonical_position_roundtrip`, `concrete_prefix_is_not_changed`, `trailing_any_is_not_a_concrete_field` | Every descriptor, with executable re-encoding. Native validation must not parse another AnyField accessor into the concrete AP. |
| P03: translate exact/any conditions without changing Boolean meaning | `condition_lowering_preserves_truth` | Structural induction over every modeled condition and arbitrary finite facts. Native predicate lowering must remove automatic array alternatives. |
| P04: star reach does not change conjunction | `complete_and_guard_is_retained`, `explicit_star_uses_or` | Exact translation of complete AND/OR structure. Existing ND execution and run-1 contribution policy remain separate obligations. |
| P05: star-aware Boolean simplification | `plain_check_implies_star`, `plain_and_star_is_plain`, `plain_and_not_star_is_false` | Prefix-based region model. A finite field-only witness shows why `X* AND NOT X` cannot be folded to false. Main's compiler tests check actual parser/unifier behavior. |
| P06: distinguish source and pass targets | `ordinary_source_is_exact`, `any_source_is_uniform`, `source_and_pass_any_targets_are_distinct` | Existing exact/uniform source versus MAY pass geometry. Backward AP semantics are reused, not reproved by equality of tags. |
| P07: source covers its declared region | `source_target_covers_exactly_its_declared_region` | All modeled positions, descriptors, marks and offered locations. Type validity and native source execution remain required. |
| P08: preserve original action identity and vector order | `source_identity_is_preserved`, `source_vector_keeps_order_and_duplicates` | An arbitrary ordered vector, including duplicates. Native specialization/expansion metadata must use original ordinals. |
| P09: pass does not change support headers | `pass_preserves_all_support_headers`, `pass_cannot_create_protection` | Arbitrary geometry function and payload. Preserve actual E/mx/layer/H and original premise in the real core operation. |
| P10: do not collapse plain/protected memberships | `opposite_protection_classes_are_distinct` | Logical payload identity. Scalar/packed storage, freshness and publication remain covered by existing core regressions. |
| P11: keep rejected rule shapes rejected | `any_pass_premise_stays_rejected`, `below_only_removeAll_stays_rejected` | Selected shape tests. Existing class/static/read-source/type validators still apply; the model does not replace them. |
| P12: preserve the distinction between clean and definition reset | `any_selected_clean_keeps_below_scope`, `any_source_definition_reset_keeps_whole_scope`, `cleaner_definition_reset_preserves_selected_reach` | Existing primitive-reach selection. Native generated-reset tests must show that the prefix is not accidentally retained. |
| P13: fallback depends on rule presence, not output | `fallback_when_no_explicit_rule`, `no_fallback_after_present_rule`, `rejected_outputs_do_not_enable_fallback` | An arbitrary prepared rule vector. Native plan building must remove statically false rows before this decision and must not redecide per fact. |
| P14: focus cannot add an unrelated matched-position clean | `nonfocus_binding_is_not_added`, `selected_binding_is_added`, `focus_free_keeps_all_matched_positions` | Original Result/by-side-effect defaults remain explicit parameters. A nonfocused receiver is excluded only when it is also absent from those defaults. |
| P15: exact clean has no hidden child effect | `exact_clean_has_no_implicit_child_effect` | Exact concrete locations. General STAR/MUST cleaner splitting and protection reuse the selected baseline laws. |
| P16: ignore legacy cap without changing bidi field depth | `legacy_cap_never_changes_bidi_schedule`, `explicit_cap_produces_one_diagnostic`, `absent_cap_is_silent` | Every schedule and optional natural cap, including zero. The runner must emit the diagnostic at configuration time. |
| P17: keep controller F2F exit applicability | `controller_exit_does_not_require_ZERO`, `generated_exit_rules_stay_hidden` | The provider gate only. Actual annotation matching, exit-rule joins and report production need native tests. |
| P18: predefined models do not add body analysis | `complete_predefined_does_not_add_body_analysis` | Existing Boolean dispatch choice. Completeness and actual cleanup summary contents are existing contracts, not newly inferred facts. |

The checker audits all **51 explicitly declared theorems**, including 11
finite example proofs. Generated equality/constructor helper theorems are
not counted as additional user-declared laws. Allowed standard dependencies
are `propext` and `Quot.sound`; custom axioms, classical choice and proof holes
are rejected. This is the repository's constructive-proof convention.

## 3. Counterexamples that constrain the design

The component examples are checked for arbitrary-size inputs where the
corresponding theorem above is general. The following finite witnesses make
the semantic boundaries visible. See the specification for code examples.

| Tempting shortcut | Counterexample and required result |
| --- | --- |
| Keep implicit array alternatives | Only `a.[*]/T` is marked. Plain `CM(a,T)` must fail; explicit any-field check can succeed. `E01_plain_array_check_has_no_implicit_element`. |
| Treat starred/plain metavariables as identical in exclusions | Only `x.f/T` is present. `X*` can hold while X does not. `E02_starred_field_only_exclusion_is_satisfiable`. |
| Use star alternatives to weaken a whole AND guard | `p.f/T` is present but `q/U` is absent. Complete conjunction stays false. `E03_distinct_AND_inputs_are_not_OR`. |
| Preserve an accessor after AnyField as concrete path data | `x.f.AnyField.g` must bind to prefix `x.f`, with any reach. `E04_main_normalization_retains_the_prefix`. This is an explicit change from the old rejection. |
| Clean all metavariables in a focused accessor sanitizer | With focus ret, x is only a receiver constraint. It is not added to defaults `[ret]`. `E05_accessor_focus_does_not_clean_receiver`. |
| Clean only Result for an argument-focused sanitizer | Its entering argument x still needs a clean. `E06_pass_sanitizer_keeps_its_focused_argument`. |
| Narrow a focus-free sanitizer by guessing a focus | Main keeps the receiver/matched-position policy. `E07_no_focus_keeps_the_receiver_policy`. |
| Merge new virtual fields into the old generic carrier | Named `x.f` and `x.g` do not match. `E08_named_model_fields_are_not_interchangeable`. |
| Apply `iteration-limit 0` to the new-core schedule | Run-1 remains limit 1, with one diagnostic. `E09_explicit_cap_zero_keeps_run1_limit_one`. |
| Lower both AnyAfter source and pass as MAY or both as MUST | Their target tags must differ. `E10_ANY_source_and_pass_do_not_share_the_tail`. |
| Keep the hidden exact-String byte clean | Cleaning x leaves the independent child fact. `E11_exact_clean_does_not_clean_string_bytes`. |
| Encode a source-definition reset through an ordinary AnyAfter cleaner | BELOW does not cover the source's prefix; AT_AND_BELOW does. P12 retains the old reset primitive rather than changing ordinary selected-clean semantics. |
| Enable fallback because an explicit rule produced no output | An explicit row rejected by an output filter still blocks fallback. P13 checks this independently of the output filter. |

These are design counterexamples and executable model witnesses. They are
not claims that Java native integration tests have already run.

## 4. Reused proofs and required native correspondence

This migration must not alter the implementations of C2/C5, summary
subsumption or loop growth to make a new compiler input pass. Use the
[selected gap proof dossier](selected-gap-resolutions-proof-dossier-20261108.md)
and the [existing combined specification](edge-subsumption-initial-emission-demand-intersection.md)
at their stated scopes. In particular:

- A rule descriptor's ANY reach can produce a rule literal/MAY output; it
  cannot introduce an ANY owned initial or premise.
- Exact FLOW summary normalization and companion emission remain unchanged.
- Original entry/exit ports and nearest-boundary ownership remain unchanged.
- Generated source targets keep existing layers, guard support and static
  writer requests; no grounding mechanism is added.
- Existing selected partial-cleaner survivor and own-ZERO loop behavior stay
  in force for the same core primitive inputs.

The adapter-input equality argument is local: if two encodings select the
same existing primitive with the same logical headers, the existing proof
for that primitive still applies. Main's changed rules/models can select
different primitives/field keys. That is a declared semantic input change;
no theorem here equates the complete old/new finding sets.

The implementation must supply evidence for the following bridges:

1. Main parser/compiler output and serialized round trips match the declared
   descriptors, focus actions and signed condition identities.
2. Actual Kotlin wrapper lowering selects the primitives in section 5 of
   the spec, at every source/sink/boundary/metadata stage.
3. Real equal/hash/freshness/cache keys preserve semantic reach and original
   labels while excluding transient identity. Plain and protected memberships
   both survive packing, replay and rebuild.
4. Default-get suppression uses the prepared explicit list and the named slot
   in forward, backward and report paths.
5. Static and loop principal cases still use the existing core pipeline;
   the migration adds no legacy filter or hard cap.
6. Main model modules/loader expose the intended body CFG and callback targets
   before the method-form catalog is frozen.
7. Controller exit, predefined cleanup and actual runner selection tests pass.

Those bridges require native tests. They cannot be discharged by a theorem
about a small Boolean policy or by a successful Kotlin compile. Full project
acceptance and convergence remain outside the proved component claims.

## 5. Reproduce and inspect

Use the [proof package](lean/proposals/main-migration-20261109/README.md).
The manifest pins the model, checker, axiom audit, this proof map, the spec
and the proof guide. From the repository root:

```bash
python3 spec/lean/proposals/main-migration-20261109/check.py \
  --output-directory /tmp/main-migration-proof-review
```

Use a fresh output directory. The checker compiles the model under Lean
4.33.1, compiles an imported-module axiom audit, lists each theorem and
writes a receipt. It rejects changed source pins and forbidden constructs.
No Gradle task, downloaded analyzer artifact or project scan is needed to
check this source specification.

The saved [receipt](lean/proposals/main-migration-20261109/receipt.json) and
[axiom audit](lean/proposals/main-migration-20261109/axiom-audit.txt) record
the checked component status. Native analyzer proved: **false**. Whole-program
convergence proved: **false**. No unresolved behavior decision remains from
the two questions raised for this specification. Implementation/test gates
remain pending.

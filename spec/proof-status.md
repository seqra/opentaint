# Current proof status

The normative rules are [ap.md](ap.md), [interpreter.md](interpreter.md), and
[analyzer-core.md](analyzer-core.md): F72 demand sharing, F74 field-cleaner lowering,
F75 base-dependent cleaner splitting, and F76 must-summary read views. This file
states proof scope and evidence.
It adds no analysis rule. [proof-history.md](proof-history.md) retains earlier
theorem catalogs; F70/F71 concrete-run results do not prove current restricted runs.

The current general closure model has three tails: exact, star with field exclusion,
and may-any. It is single-premise and alias-free. It does not combine the full
must-tail/X, static, conjunction, end-fact, interpreter, and pipeline extensions.
`CurrentDefs.lean` defines run 1 `RC`, restricted forward `FC`, and backward `BC`.
All use `BaseCleaner.cleanRes`; only `RC` has request rules. `FW` and `BW` select
the current `emitW`, `satW`, and mark-aware `restrictI` operations.
These generalized closures do not implement every W6 layer refinement. The
tail/mark shape proofs alone do not prove the typed FLOW any-demand/star-normal
flags of the full spec. These closures use the generic record reader and the original no-any crossing
classifier. F76's
concrete-star views are checked separately below; they are not native initial
kinds or an integrated current closure/iteration theorem.

| Current result | Evidence | Conditions and limits |
|---|---|---|
| F75 cleaner coverage with computed output-or-request witness; normal-result exactness | [BaseCleaner.lean](lean/ApSpec/BaseCleaner.lean): `cleanRes_sound_witness`, `cleanRes_exact` | Local operation, not full run coverage. Same-base abstract selected-mark facts always request in run 1, including an already excluded mark. Concrete/all-mark spatial behavior is unchanged. |
| C2/L6 emission produces an actual premise covering the pair, satisfying the added fact, and wholly inside the demand | [CurrentDemand.lean](lean/ApSpec/CurrentDemand.lean): `emitCertificate`; [AbsDefs.lean](lean/ApSpec/AbsDefs.lean): `emitW_contract` | Abstract pattern tail must be exact, any, or empty-exclusion star. A concrete pattern requires a concrete added mark. Demand and added fact cover the same marked location. Nonempty-star counterexample: `Abs.emitW_needs_patTail`. |
| C5 reduction computes a publication retaining the demanded pair, input mark and layer; no new pair | `CurrentDemand.restrictCertificate`, `reduceEmission` | Whole premise inside `D-c` in locations **and marks**; actual input denotation pair; `D-p` present and covers the exit **with its mark**. Premise overlap and location-only exit tests are insufficient. Exact demand intersection has AP §6.4's three representability limits. |
| Normalization computes the actual hand-off pattern and preserves location sets and covered marks | `CurrentDemand.normalizeCertificate` | Changes mark exclusions only. Star field exclusions stay. Must-tail forgetting is a separate X operation, outside this base certificate. |
| Current prefix index gives exactly the same reduction results as a full demand scan | `CurrentDemand.restrict_index_equiv`, `insidePrefixWitness` | Key is `base::path`. Lookup returns ancestors of the premise key; run full `restrictI` on each candidate. Equivalence is result membership, not order or duplicate multiplicity. |
| Per-leaf tree reduction and rebuilt tree have exactly the same whole facts, layers, and mark exclusions | [CurrentTreeReduction.lean](lean/ApSpec/CurrentTreeReduction.lean): `tree_reference_equiv`, `tree_reference_key`, `tree_reference_wf` | Executable reference rebuild. Generic model trees permit cells that canonical typed FLOW values exclude. No optimized structural-walk or full X-tree theorem is claimed. |
| Actual restricted closure initial facts and publications have computed demand certificates | [CurrentDemandClosure.lean](lean/ApSpec/CurrentDemandClosure.lean): `forwardEmission`, `backwardEmission`, `publishedReduction` | Uses the explicit entry-shape guard. These certify local constructors, not coverage of every real witness. Concrete seeds are needed for canonical hand-off/representation results below. |
| Current run-1 and restricted-forward normal edges/records are exact | [CurrentExact.lean](lean/ApSpec/CurrentExact.lean): `RC_edge_exact`, `FW_edge_exact`, `FW_records_exact`; valid variants | S7 mark well-formedness; upward-closed filter acceptance (`FiltUp`), or S13 filter/validity conditions. Restricted runs require exact input records. The proof inducts directly on F75 closures, not old-cleaner embeddings. |
| Current backward nonzero normal edges/records are exact | `Current.BW_edge_exact`, `BW_records_exact`; valid variants | Same mark/filter/record conditions on the backward program; no binding into callee zero. Zero-premise seeds are excluded. |
| Actual reversed backward normal record pairs are forward flows | `Current.BW_rev_record_exact`; [CurrentHandoff.lean](lean/ApSpec/CurrentHandoff.lean): `BW_rev_record_exact_shape` | Mark well-formedness, upward-closed forward filter acceptance (`FiltUp`), exact backward input records, no forward zero back-binding, mark-reversible/exact-shape statements and calls. Premise is nonzero and has empty exclusion for star; the hand-off shape derives the latter. Dropping real backward filters does not establish this theorem. |
| Normalized hand-offs preserve the C2 entry-tail guard across an explicit alternating base sequence | `Current.shapeSeq_entry_shape`, `shapeSeq_PatTail` | Concrete non-star sink seeds. The sequence uses F75 base closures and their generic raw crossing tests before publication; it excludes F76's new must-selection branch. Arbitrary record sets suffice for this weaker shape result; their exactness is separate. |
| Canonical paired demand guards prevent abstract exact FLOW entries and narrowed conclusions | [CurrentKinds.lean](lean/ApSpec/CurrentKinds.lean): `shapeSeq_tree_shape`, `emitW_tree_init`, `restrictI_tree_flow` | S7/S8 on both programs, concrete non-star seeds, and `RecordKinds` for both native stores. Abstract entry patterns are any; exact exit demand implies concrete entry mark. `EntryShape` alone is too weak. `RecordKinds` constrains tails/marks, not all FLOW layers. Full W6/typed-tree packing preservation remains open. |
| Native record-kind conditions survive raw insertion, generic base reversal, and retained unions | `Current.native_record_kinds`, `revRec_kinds`, `reversed_record_kinds`, `record_kinds_union` | Derive native kinds from reached closure edges, not reduced publications. Reversed reads require their crossable reversed premise and concrete-premise preservation. This is generic/base `revRec`, with field exclusion on the conclusion, not F76's concrete-star read views. |
| Exact-premise forward must summary has a computed backward view with exactly its annotated converse pairs | [CurrentMustReverse.lean](lean/ApSpec/CurrentMustReverse.lean): `readView`, `exactCertificate_converse`, `transferCertificate`, `exact_transfer_rejects` | Native normal singleton forward record, concrete premise/target marks, exact premise with empty annotation. Preserve conclusion E on the star read premise; discard the incoming suffix at the exact target. Relation equality is local; S14 native-record exactness is required to infer real program flows. View is transient, never started or persisted. |
| Computed must-premise views cover every annotated converse pair and every application stays demand-layer | `CurrentMustReverse.mustAnyCertificate_covers`, `mustExactCertificate_covers`, `must_read_demand`, `must_application_demand` | Normal singleton native must record, concrete marks, must or exact conclusion. Keep conclusion E on the star input; forget old must-premise E in the may-any output. These are pair-inclusion and layer results, not pair-exactness or program-flow coverage. |
| Generic-Cross diagnostic and must-to-may copying preserve published pairs while forgetting must exclusions | [CurrentMustHandoff.lean](lean/ApSpec/CurrentMustHandoff.lean): `normal_any_selection`, `selectAny_equiv`, `copyCertificate`, `handoff_retains_pair`, `x_any_restricted_demand` | The selection equivalence uses the original generic `Handoff.Cross`, not F76's broadened forward classifier. The copying certificate still applies to selected must demand pieces. Select RAW leaves before restriction; copy each published piece, even if narrowed to exact. Must-to-may forgetting can add excluded locations. Local publication/conversion result, not full annotated hand-off coverage. |
| F76's computed raw exact-to-must selector returns a normal read-view certificate and omits its backward demand | `CurrentMustReverse.omit_eq_guardsB`, `omit_eq_normal_read`, `normalMustWitness`, `publicationPlan` | Raw native singleton forward record; normal must target and concrete marks; exact premise with empty annotation, not a must-premise. Conclusion E is arbitrary and retained. Other shapes keep generic classification; must-premises remain demand. `publicationPlan` preserves the new branch's raw selection bit, not the full generic selector. This adds a local branch to generic Cross; it is not a full current hand-off/closure theorem. |
| F76's star/E view matches each canonical concrete exact or may-any requirement covering an admitted marked location | `CurrentMustReverse.concrete_read_matches`, `selected_view_transfer` | Arbitrary E. Matching is `inside || applicable`; exact transfer returns the old premise without the suffix. Abstract marks are outside this contract. |
| Omitted exact-to-must record returns a distinct upstream mark and reaches zero through an actual reversed source edge | `CurrentMustReverse.Certificate.upstreamSourceWitness`, `restricted_publication_keeps_selection` | Executable local chain with U ≠ T and nonempty E; the annotated restriction publishes an exact piece while keeping the raw omission bit. The witness does not model the source-hit store or full iteration. |
| Restricted runs have no request objects | `Current.FC_no_req`, `BC_no_req` | By closure definition, not by concreteness. Abstract facts can occur. |

An existence result is not obtained by selecting data from a proposition. The
certificates above compute the relevant AP function first and carry its proof.
Runtime checks evaluate those data through Lean's compiler.

The checked optimization is the maintained candidate index. On the distinct
33-demand workload, `CurrentDemand.reductionWorkWitness` computes 33 full restriction
calls for a scan and 1 for indexed lookup. This counts full restriction calls;
it excludes index construction. Lookup also walks at most the key length plus
one path-map nodes. Both queries return the same result set. Cleaner batching
has a separate 33-to-1 base-guard check witness in `BaseCleaner.workWitness`;
it still maps the residual over all leaves. Neither result claims constant total
runtime or an optimized sharing theorem for the whole analyzer.

The regression modules preserve their design versions:

| Module | What its executable witness establishes |
|---|---|
| `CleanerLowering`, `FieldCleanerX`, `ReviewFieldCleaner` | F74 read/clean/write lowering, reach policies, outside-field X fact, and reached 1/2/3 program source hit and finding |
| `ReviewRootCleaner` | Root-EXACT loss under the old spatial rule; historical counterexample, superseded by F75 |
| `ReviewBackwardCleaner` | Backward abstract pass-through can produce a reached stored record and false normal finding; the rejected experiment |
| `ReviewBaseCleaner.Repaired` | F75 produces the concrete request/hand-off, source hit, record, and normal finding for the root-EXACT example |
| `ReviewBaseCleaner.Blocked` | F75's actual stored record reverses with mark exclusion and rejects `T`, blocking that bad-record application |

The last check rejects the witnessed record. It does not enumerate every possible
finding. A reached local regression is not a global iteration proof.

The remaining current obligations are:

1. L1–L4 mode coverage: abstract forward/backward coverage, run-1 mode selection,
   and contract B through F74 lowered actions and F75 cleaners.
2. Full current no-loss iteration with F76 selection, source-seeded confirmation, method exclusion,
   and round-to-round narrowing. Mark normalization and AP §6.4 exceptions limit
   exact narrowing claims.
3. Combined must-tail/X and F76 read-view integration, statics, restricted conjunction support, aliases,
   end facts, and actual interpreter forms; their stronger hand-off guards.
4. Current pipeline/driver encoding and dominance under store subsumption.
   `Pipeline`'s generic reliable-join/quiescence theorem requires a correct encoding;
   historical concrete AP/driver instances do not supply the current instance.
5. Tree shortcuts beyond the proved per-leaf rebuild and candidate index. The
   old `restrictS/U` tree theorem does not prove the current mark-aware tail meet.

These obligations are explicit limits, not established invariants of every
implementation run. The proposals use the checked demand reference and enforce
its representation conditions; they do not claim these wider proofs.

Build and audit from the repository root:

```bash
cd spec/lean
lake build
lake env lean audit.lean
```

[audit.lean](lean/audit.lean) examines every declaration from every imported
`ApSpec` module, including private and generated declarations. It rejects transitive
axioms other than `propext` and `Quot.sound`; thus `sorryAx`, classical choice, and
native proof oracles fail the audit. It also executes the cleaner, lowering,
regression, emission, reduction, normalization, index-cost, tree, must-hand-off,
and must-summary read-view witnesses.
The exact declaration count is reported by the audit and changes with the model.

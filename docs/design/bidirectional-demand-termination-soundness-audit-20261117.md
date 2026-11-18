# Soundness audit of the consolidated progress proposal

17 November 2026. Synthetic data-flow reachability. FULL mode.
[Proposal under review](bidirectional-demand-termination-approach-20261115.md).
Follow [proof-guide.md](../../spec/proof-guide.md).

**Prefix-return G1/G2 case repaired in the proposal:** the
[prefix-return example](../reports/bidirectional-prefix-return-soundness-gap-20261117.md)
historically lost its NORMAL observation at natural **run-5**. The selected
[additional possible DIRECT replay](bidirectional-saved-direct-possible-replay-20261117.md)
keeps the missing run-4 guide and the NORMAL run-5 result in the reference.
Six native components check E/mx/H, paired C5 and the final NORMAL route.
Production still has the old run-5 loss. The added matching lane is a major
semantic change; caps, C2/C5 and definite application remain unchanged.
General G1–G4 are not discharged by this concrete repair.

**Further investigation:** the
[post-DIRECT audit](../reports/bidirectional-post-direct-soundness-audit-20261117.md)
finds no additional concrete gap in 13,604 finite reference configurations.
Exact observations, branch alternatives, three owners and strong writes
reach within-run fixed points and natural completion through **run-11**.
Nine new unmodified native controls retain NORMAL observations through
**run-9**; the combined targeted suite passes **92 tests**. Eight new
constructive claims give 7,245 cumulative claims in 422 checked modules.
This adds evidence and corrects the search harness, not analyzer semantics.
It does not discharge G1–G4 or source-permission/Target integration.

**Result: the whole proposal cannot yet be certified sound.** The audit found
a [root-cleaner / getter missed-observation case](../reports/bidirectional-cleaner-getter-soundness-gap-20261117.md).
The unchanged native driver stops at **run-3** without the reachable
observation. The selected proposal's complete C2 family also rejects its
precise input. This is a retained admission gap, not evidence that the latest
reply-service change introduced it.

**Repair update:** [disjoint selected FLOW cleanup](bidirectional-disjoint-cleaner-flow-20261117.md)
closes this case in the proposal. The reference retains the NORMAL observation
and stops at **run-3**; native components confirm the C5/replay route. The
unchanged production driver still has the original loss. R31, R32 and R34 below are the
selected semantic deltas; the old counterexample proofs remain historical controls.

The local algebra and guarded replacement laws have constructive proofs.
Four obligations remain between those laws and whole-analyzer execution;
the first had the concrete case now repaired by R31; R32 and R34 repair two further concrete cases. The general obligation
remains open. Earlier termination results and
the theorem count do not discharge them.

Production is unchanged. The original audit proof sources keep the original
rules; separate R31, R32 and R34 packages prove the selected repairs. The structural ownership
model below makes existing guards explicit; it adds no runtime query key,
record label, input history or field-limit exception.

**Follow-up and R32 repair:** the
[nested overwrite counterexample](../reports/bidirectional-nested-star-soundness-gap-20261117.md)
found another G1 admission failure after R31. The selected
[run-2 STAR relay](bidirectional-run2-star-relay-20261117.md) repairs it.
Same-head STAR queries can relay in run-2; raw C5 uses the same policy.
The reference and cold native adapter retain the NORMAL observation and
stop naturally at **run-3**. Exact demands, limits and run-3 onward admission
are unchanged. The old rejecting adapter remains a historical diagnostic;
no whole-analyzer certificate follows from this repair.

**Next audit result:** the masked-FLOW relay candidate is ruled out by the
existing AP F72 handoff. FLOW demand endpoints have Empty mx; actual facts
and NORMAL records keep their masks. This missing step is now explicit in
the consolidated specification and the new model. Native controls keep U
through 1..6 wrappers and reject the exact cleaned T, all at **run-3**.
[Candidate, corrected trace and scope](../reports/bidirectional-post-run2-soundness-audit-20261117.md).
This is a specification/model alignment correction, not a new analyzer fix.

## 1. What must be preserved

The reference is the selected AP behavior, including its accepted cleaner
revision, run-1 approximation and ND join scope. Soundness here means that
an optimization must not remove a valid reachable observation. It does not
mean equal callback counts or identical intermediate runs.

Use three separate proof goals:

```text
DATA:
    each concrete marked point needed before replacement remains supported

SERVICE:
    each needed continuation, query/lookup, rule effect and future guide
    has a retained execution route or a complete alternative proof

NORMAL:
    uncertain support is not silently turned into a NORMAL assertion;
    a conditional NORMAL relation is used only under its complete premise
```

Before claiming a gap, construct the actual normalized handoff. In
particular, F72 removes mx from FLOW Dc and Dp; a copied masked summary
endpoint is not a legal demand. Runtime/record masks remain real effects.

A data cover is not automatically a service cover. A local matching theorem
is not automatically a cross-iteration relevance theorem. A proof of natural
termination on a program establishes neither theorem for all programs.

The selected exact cleaner on same-head MUST deliberately keeps more marks
than the old concrete cleaner. Its previously accepted NORMAL exact-root
false positive remains. No proof here claims old cleaner precision or
concrete path precision for the existing ND joins.

## 2. Rule inventory and proof map

`Local` means the listed theorem proves the stated local property for all
inputs in its mathematical scope. `Guarded` means the complete-service guard
is essential. `G1`–`G4` below name the remaining obligations. These labels
must not be combined into an unconditional whole-engine claim.

Proof names are grouped by package. The new package is
[termination-soundness-audit](../../spec/lean/proposals/termination-soundness-audit-20261117/README.md).
The proposal's proof table links the retained packages.

| ID | Rule / retained invariant | Soundness argument and proof | Limit |
|---|---|---|---|
| R01 | MAY = empty or nonempty suffix; NE is a distinct tail | Case analysis constructs either `[]` or `f::rest`. NE has no root witness. `AuditGeometry.MAY_is_empty_or_nonempty_without_a_named_first_field`; `NonEmptyMay.may_partition`. | Local; STAR remains correlated, not another name for NE. |
| R02 | A real field cut emits NE/D and forgets E | Every old point has a retained prefix and a nonempty removed suffix. `AuditIntersection.cut_covers_every_original_point`; `Restriction.real_cut_has_ne_demand_and_keeps_mark_protection`. | Local; a native cut must remove a real counted accessor and retain static anchors. G2. |
| R03 | NE read/write rules | An unknown read can consume the only unknown field; its residual may be empty. A write preserves its named child root. `AuditGeometry.unknown_read_of_NE_must_allow_an_empty_residual`, `a_written_MAY_retains_every_possible_written_location`. | Local; do not relabel an uncut MAY as NE. |
| R04 | MAY/NE C2 split; no MAY/NE owned premise | Empty and nonempty cases cover the admissible suffixes; `Policy.every_ne_query_is_a_may_query`, `HeadSafety.never_owned_MAY_or_NE`. NE removes only its own empty-head starts. | Legal shape proved. R31 repairs the cleaner case; R32 repairs run-2 same-head STAR relay. General G1 remains open. |
| R05 | Bounded possible STAR descent | Keep the actual binding and its possible flag. `Binding.possible_admission_cannot_confirm_a_target`. A possible match remains D even if its structural FLOW hypothesis is N. | Local; current-record authority remains tied to its own qualified query. |
| R06 | Retained FLOW companions and prefix probes | These are conditional structural hypotheses. They do not establish a concrete mark. Normalization requires the suffix proof in R22. | Retained behavior; G3 for the complete native transfer set. |
| R07 | Copy real E at an unchanged actual head | The represented point region equals the actual region, with tail/mark/layer unchanged. `CarrySafety.eligible_copy_preserves_the_entire_actual_point_region`; `AuditGeometry.unchanged_head_real_E_copy_loses_no_actual_point`. | Local; do not move E to a shorter head. Cross-offer reuse: G1. |
| R08 | Retain a NORMAL MUST actual's deeper head and real E | The new query region equals the actual region. It is a map of an old member, not a field product. `HeadSafety.retains_the_actual_point_region`, `every_relative_cap_exception_has_the_enumerated_certificate`. | Local; the exhaustive entry exception remains global-bounded. Future conditional-service reuse: G1. |
| R09 | Observed first-field child plan | Every successful unknown-prefix read begins with that field. Empty and nonempty child cases cover its suffix. `ChildCover.the_child_covers_the_whole_normal_reader_contribution`; `Frontier` query-bound theorems. | Positive unary prefix fragment. No recursive unfolding; no new cap exception. |
| R10 | Separate executable union from qualified refinement rows | Retain each paired head/budget before union. `Subsumption.a_parent_plan_cannot_admit_the_deeper_initial` proves why spatial union alone cannot replace the child service. | Guarded: delete a refinement row only with its service witness. |
| R11 | Delegate a coarse primitive read to ready children | The concrete input/output relation is unchanged on the delegated field. `ExclusionCover.complete_child_cover_with_arbitrary_real_exclusions`; `LocalRouting.normal_results_are_forwarded_unchanged`. | Guarded full child service, including observations. G2 outside the proved prefix fragment. |
| R12 | Delegate supported opposite NORMAL saved reads | The same suffix witness gives the child route, with the same paired output selector and real E. `ChildCover.cover_survives_any_fixed_paired_output_selector`; `ExclusionCover.coverage_preserves_any_fixed_qualified_output_service`. | Not general current-inside pruning. Unsupported aliases/ND/effects remain enabled. G2. |
| R13 | Reject a strict-descendant keep below EXACT/FLOW | There is no matching exact point. `PointWriteProperties.removed_guard_has_no_exact_point_witness`; `AuditNormalization.EXACT_before_normalization_cannot_execute_a_deeper_read`. | Local; normal root keep retains the needed write exclusion. |
| R14 | Saved NORMAL replay first; demand gates current analysis | Preserve the original offer and saved effects. This is the retained call policy, not a new pruning theorem. | An empty current lookup must not skip saved replay. Baseline service invariant required. |
| R15 | Saved MUST uses only definite lanes | A child uniform region does not establish a parent uniform premise. `DefiniteMustReplay.definite_geometry_covers_every_required_location`, `every_old_normal_data_output_is_preserved`. | Local matching proof is closed. Removing provisional future guidance needs G1. |
| R16 | Identical definite N/D actual support | The same full key, point/uniform region, continuation and H retain a stronger actual witness. `DefiniteReplySupport` retained-NORMAL and concrete-support theorems. | Resolve alias/identity routes before comparison; complete ND original must agree. G2. |
| R17 | NORMAL MUST actual covers a whole D region | Every candidate point has a NORMAL provider. The new `AuditGeometry.uniform_actual_cover_preserves_the_entire_positive_program` handles arbitrary finite positive rules and complete AND premises. | This proves positive ground continuation coverage, not equal C2 images. G1 remains. |
| R18 | NORMAL FLOW precoverage before relative C5 | A retained provider supplies the same complete native correlated result; a genuine global cut is not removed. `VirtualProviders.exactPriorImage` and its warm replay proofs. | The executable precoverage model uses saved records. A current-provider extension needs delivery service, not geometric inclusion alone. G2/G3. |
| R19 | Whole / mark / plain-region / same-H / native-bound completion | Full owned closure contains every reachable return. Each selected true bound return has a same-context NORMAL witness. `CompleteClosure.every_reachable_return_is_covered`; `AuditReplySafety.complete_query_service_preserves_positive_continuations_without_an_external_monotonicity_axiom`. | Guarded. Current unary concrete return DATA only for the added path. Whole native closure/effects: G2; future engine guidance: G1. |
| R20 | C5 tests the raw C2 image before normalization | `AuditServices.every_actual_C2_start_is_a_full_raw_C5_witness` constructs the witness. Normalized aliases of another raw initial are not witnesses. | The full image is over legal offers, not a sample/history. Native structural lookup correspondence: G2. |
| R21 | Own-row scalar output selection and FL(Dp)+1 cut | The new `AuditIntersection.every_scalar_C5_exit_keeps_every_point_in_its_paired_intersection` covers arbitrary paths/tails/E; a subsequent real cut still covers every point. `scalar_exit_preserves_mark_layer_and_literal_protection` proves the header invariant. | Spatial proof is closed. STAR is retained whole to preserve correlation. Whole restriction relevance: G1/G4. |
| R22 | Complete FLOW EXACT-to-STAR normalization | A successful finite NORMAL prefix path transports the same suffix. `AuditNormalization.every_finite_NORMAL_prefix_path_preserves_correlation`; the guarded version retains write E. | An exact probe alone is insufficient. Native E/mx guard extraction and all normal path forms: G3. |
| R23 | Same-premise MAY/NE executable coverage | MAY contains NE. Same-head NE C2 service is included in MAY service; deeper refinement heads remain separately captured. `Coverage.dropping_covered_nonempty_preserves_union`; `Policy.every_ne_query_is_a_may_query`. | No blanket deeper-demand deletion. The paired premise and budget must be identical. |
| R24 | Same-lane NORMAL MUST summary covers NE | The same complete MUST original gives a concrete uniform witness for every NE point, with identical marks/mx/H. `UniformService.every_covered_point_has_a_constructive_uniform_witness`. | Forward singleton, diagonal, nonstatic, empty real E only; caller service G2. |
| R25 | Transitive and arrival-independent replacement | Every removed membership must have a final retained witness. `AuditKernel.final_basis_replacement_preserves_all_positive_observations`; existing coverage transitivity laws. | Use service witnesses where service matters. Do not jointly delete all individually redundant providers. |
| R26 | Selected exact cleaner cannot clean same-head MUST | Its old survivor points are retained, with its input layer; D is not upgraded. `RootCleanerPolicy.no_new_layer_change_for_any_matched_must`. | Accepted semantic coarsening. Does not preserve the old exact-root cleaner precision. |
| R27 | EXACT/high-priority work and complete ready reply batches | At quiescence, sound positive stores closed under the same rules have the same least result. `AuditKernel.quiescent_sound_stores_are_order_independent`. | Requires fair complete processing. Callback counts may differ; no late Target cancellation. |
| R28 | Typed Target persistence and empty-frontier stopping | Preserve accumulated effects independently of DATA compaction. `AuditKernel.cumulative_effects_cannot_be_retracted_by_later_data_compaction`; selected cold Target-kernel proofs. | Retained behavior. Empty frontier is safe globally only under the relevance invariant G4. No hard cutoff is a proof. |
| R29 | Complete context, literal H, mark/E/mx and distinct keys | The new `AuditScopedService` constructs the exact same-frame witness. Existing key laws keep plain/protected memberships separate; no hash-only equality. | Local. Native adapters must supply the actual frame, binding and stage. G2. |
| R30 | Complete ND conditions; run-1 origin approximation only | `AuditKernel.a_substitution_never_needs_a_weaker_ND_condition` preserves full AND. Later executable ND is not split. Run-1 retains the already selected approximation and all-ZERO rule. | The run-1 baseline is unchanged; do not interpret projected handoff arms as executable AND replacements. |
| R31 | Preserve nonstatic selected FULL FLOW outside the cleaned suffix region | `DisjointCleaner.safe_cone_has_no_cleaned_point` and `guarded_FLOW_identity_is_valid_for_every_full_mark_and_suffix` prove the complete region, including normalized EXACT. `CleanerRepairTrace` computes the new C5 NORMAL record and run-3 saved observation. | The named gap is repaired with unchanged C2 and limits. This does not discharge all G1–G4. |
| R32 | Run-2 same-head STAR relay after run-1 writes | `Run2Relay.no_old_C2_membership_is_removed`, `every_old_paired_C5_result_is_unchanged`, executable raw witnesses and both field bounds; `RelayTrace.any_finite_wrapper_depth_retains_the_same_NORMAL_reply` and precise g/f controls. | A semantic admission change only in run-2. Concrete STAR stays D; FLOW is conditional. Native cold adapter retains the NORMAL observation at run-3. General G1–G4 stay open. |
| R33 | Existing AP F72 demand mark projection, now explicit | `MaskHandoff.every_FLOW_demand_endpoint_has_empty_mx`, idempotence, unchanged concrete/path/tail/E; corrected own-row C5 and arbitrary wrapper depth retain the masked NORMAL service. | A reused boundary invariant. The unprojected masked-demand countermodel is invalid. Actuals/records keep mx; G1–G4 remain open. |
| R34 | Possible DIRECT replay of a blocked unary NORMAL FLOW STAR relation | `DirectPossibleProofs` preserves old successful reads, proves new replies D-only, constructive concrete suffix coverage, fixed qualified child cover and the cold run-4/run-5 repair. | Concrete G1/G2 case repaired in reference. Native components preserve E/mx/H and paired C5; unchanged driver still loses it at run-5. No whole-engine G1–G4 certificate. |

## 3. The common no-loss proof

A positive concrete rule has a complete premise list. It may represent an
ordinary transfer, a source condition, a call relation or an observation.
Scope/ports/originals are fixed in this instance or included in the atoms.

```text
derive(S,a):
    a is in S
    OR there exists rule (P -> a) with every p in P derivable

SeedCover(old,new):
    for every old seed a, construct derive(new,a)

SeedCover(old,new) AND derive(old,observation)
    => derive(new,observation)                 // induction on the old proof
```

The induction keeps the **whole** premise of an ND rule. It supplies every
required input to the same retained rule; it does not turn AND into OR.
It works for any finite derivation, even if the rule graph has cycles.
This is not a convergence theorem for the graph.

For whole NORMAL uniform coverage, point containment constructs each new
seed witness. This proves the positive continuation claim without an
unproved `observe`-monotonicity parameter. The packet theorem also retains
unrelated marks/effects unchanged while replacing only the selected output
region. Other terminal marks do not disappear from the full internal graph.

Current JVM source/observation predicates are positive NNF. Their existing
negative-mark approximation precedes predicate compilation; dynamic
mark-dependent cleaners are not executed unless their rewritten condition
is true. A native adapter must still establish that its modeled transfer
and effect set matches this behavior. The theorem does not authorize a new
negative-condition or cleaner semantics.

## 4. C5 and normalization proof boundaries

The scalar C5 proof is generic, not an enumeration of the earlier examples:

```text
word in candidate AND word in own selected Dp
AND base/mark gate succeeds AND Dp is legal
    => exists selected result containing word
    => its own FL(Dp)+1 cut still contains word
```

Two prefixes of the same word are comparable. This gives exactly the
same-head, deeper-candidate and deeper-selector proof cases. Real E remains
at its own head; same-head MUST uses the union of candidate and selector
holes. NE cannot meet an exact root, but can meet an exact descendant after
its nonempty suffix is consumed. Retaining a whole STAR result is a safe
cover here, not ordinary set intersection.

FLOW normalization needs a different property:

```text
run(prefixMoves,a)=b
    => run(prefixMoves,a+suffix)=b+suffix
```

The new proof derives this property for any finite path of known-prefix
moves. Its guarded form applies only to suffixes admitted by the actual
collected E/mx conditions. A field write excludes the overwritten suffix.
A function that works only for the empty suffix is a countermodel to the
argument that an exact probe alone proves a STAR relation. It is not
claimed as a permitted native NORMAL path. The missing native lifting
proof is G3, not permission to normalize arbitrary functions.

## 5. Why the remaining obligations are necessary

### G1. Data coverage must be connected to future demanded execution

The following legal interface state is checked constructively:

```text
demand:       x.M/T
actuals:      x.MUST/T,N,H=0
              x.f.M/T,D,H=0

uniform cover removes the second actual.

C2 from x.f.M/T,D:
    x.f.$/T,D; x.f.*/T,D; x.f.*/FLOW,N; x.$/FLOW,N
C2 from x.MUST/T,N:
    x.MUST/T,N
```

Every old possible marked point is supported by the retained uniform value.
The old raw initials are nevertheless different. This is **not** evidence
of a missed finding: the uniform query may supply all needed results by a
different derivation. It refutes a proof that relies on equal raw images.
The required theorem is about needed observations and guides, not retaining
every old query, including redundant queries.

Likewise, a retained NORMAL record
`p.MUST/T -> ret.MUST/U` does not apply to the legal actual
`p.f.MUST/T,N`. If local demand is empty, saved replay plus current admission
returns no service from that interface state. This is not asserted to be a
reachable cold handoff of the selected whole analyzer. Proving that it
cannot be the sole route for a valid later flow requires a history invariant.
Preserving every old NORMAL output on the old inputs does not prove it.

The remaining statement is:

```text
for every needed concrete derivation after handoff i:
    either a retained, applicable NORMAL route supplies its next step
    or a surviving paired demand admits an adequate next-run derivation
```

It must cover new actuals, stronger/finer inputs, source permissions,
NORMAL ND contributors, narrower head/E queries, and the current/saved
call policy. It cannot use the run-11 cutoff. R07/R08/R15/R17/R19 cannot gain
this global conclusion merely from their local region proofs.

The original audit produced this concrete failure before R31:

```text
helper(p) { clearRootT(p); return p.g; }
source in main: T at local a.g.h.MUST; observe T anywhere below helper(a).

run-1: p.*/T -> ret.M/T,D
run-2: ret.*/T -> p.g.*/T,D       // plus the proposal's exact arm
run-3: submit p.g.h.MUST/T,N
       precise p.g.* and p.g.$ demands both reject it
       retained NORMAL FLOW alternatives exclude T
       no result, empty frontier, missed observation
```

The [complete trace and controls](../reports/bidirectional-cleaner-getter-soundness-gap-20261117.md)
include retained parameter outputs and the NORMAL structural companion.
`AuditCleanerGetter` computes the selected C2/C5 trace and constructs the
real surviving concrete mark. The native cold test independently reaches
run-3 with zero observations. Without the cleaner, or with the source at
g rather than g.h, the native test reaches one NORMAL observation at run-3.
This was a retained policy gap. The old no-cleaner termination family does
not cover it. R31 now retains the missing NORMAL structural provider, without
creating a query or relaxing STAR. See the repaired run-2/run-3 trace. No
completion-selector extension is used.

The follow-up found this second, independent historical failure:

```text
overwrite(p) { p.f = new Box(); return p; }
wrap(p) { return overwrite(p); }
main marks a.g.$/T and checks wrap(a).g.$/T; f != g.

run-1: both methods have p.*/FLOW -> ret.*/FLOW,D, with Empty E.
run-2: wrap starts ret.*/FLOW from the caller's ret.g.$/T requirement.
       its inner call offers ret.*/FLOW to overwrite's ret.*/FLOW demand.
       same-head STAR rejection emits no inner initial.
       neither method learns a NORMAL DATA relation.
run-3: demand and saved DATA service are empty; the valid g flow is lost.
```

The historical [full annotated trace](../reports/bidirectional-nested-star-soundness-gap-20261117.md)
includes mutable-argument summaries, ZERO identities, the direct C5 control
and actual native offers. The source and summaries fit limit 1. No cleaner,
NE cut, loop, special pass or ND is involved. The current native policy's
EXACT FLOW probe learns the NORMAL `{f}`-guarded relation and retains the
finding at run-3. Rejecting just the specified offer in the native protocol
loses it at natural run-3. R31 is inactive and does not resolve this case.
R32 now enables the run-2 same-head relay and updates the raw C5 image.
Its reference and native adapter retain the NORMAL observation at run-3;
the f control remains rejected. This closes this concrete G1 case, not the
general relevance obligation.

The next audit confirms a third concrete failure:

```text
wrap(x): read x.g.g; call keepF; prepend g.g; return
keepF(x): fresh y; y.f=x.f; return y
mark x.g uniformly; observe any returned T

run-2: keepF stores NORMAL ret.f.* -> x.f.*
run-3: wrap's NORMAL raw ret.g.g.f.MUST is correctly cut to ret.g.g.NE/D
run-4: wrap starts ret.g.g.*; reverse packing supplies keepF with ret.*
       keepF's saved record is SAVED_DIRECT; STAR inside f is forbidden
       keepF has no current demand; no query or reply is produced
run-5: wrap has no demand or saved NORMAL return service; finding is lost
```

This is not the rejected masked-demand countermodel. All mx are Empty, R32
is inactive at the decisive boundary, and all field caps remain active.
The source is granted optimistically in the formal reference. Native typed
Targets/source permission give the same natural run-5 loss. The named
observation and updated 884 controls retain NORMAL findings at run-5.
This case invalidates a blanket claim that retaining the NORMAL callee
record is enough to preserve future caller service. R34 now adds the missing
possible replay without restarting that callee or bypassing a cap. The
reference retains its NORMAL observation at run-5. General G1 still needs
the whole native history/service proof; this local repair does not supply it.

### G2. Complete service means the real native pipeline

A callback value with the right AP shape, mark and H but a different owner
or revision is not a witness. The new frame proof rejects it. It also keeps
actual D, saved-replay selection, backward, GROUP and run-1 outside the new
native-bound selector. The frame is a proof view of existing ownership,
not a new MethodEdgeStore key.

The native bridge must include real physical ports, whole ND originals,
rule occurrences, source/static callbacks, normal/exceptional boundaries,
actual limits and resolved alias/identity routes. Complete query closure
must include every true transfer, not just the transfers retained by a
pruning policy being justified. A projected return list alone is not proof
of full closure. Existing unsupported-case fallbacks remain required.

For R18 the executable model uses persisted provider records. Saved-first
replay supplies their native route. A broader interpretation allowing a
current record to delete a more specific candidate must prove delivery to
every affected admitted subscriber; a broader premise alone does not prove
current admission. This audit does not silently select that extension.

### G3. NORMAL FLOW path lifting must cover all allowed native path forms

The suffix proof is closed for the stated prefix fragment. It must be
connected to the actual exclusion collector, mark masks, types, aliases,
call bindings and packed/scalar operation decomposition. Exact root keeps
must record field-write exclusions before normalization. Partial cleaners
and unknown reads cannot be treated as precise prefix moves. Existing
rejected rule shapes remain rejected.

A type/field/path-specific NORMAL witness cannot be generalized by testing
only its empty suffix. Unsupported operations must remain outside the
normalization proof, or have a separate valid lifting lemma.

### G4. Handoff and loop gates must preserve the needed-witness invariant

The scalar C5 theorem preserves points within a **given** paired row. It
does not prove that every needed row is present at the next handoff.
Nor does positive semantic coverage show which method/block query a loop
will analyze. A changed initial path can change the loop's growth test.
The full proof must connect qualified rows, both loop exits, saved replay,
block boundary rules and the empty-frontier stopping condition to G1.

Already emitted Targets stay in the cumulative effect set. A NORMAL finding
at one location does not cancel an unresolved target at another location.
NormalTarget composition stays normal-only. The proof must use the current
selected typed ZERO/Target rules and source permissions, rather than the
older final-DATA-only diagnostic controller.

These are explicit proof obligations. R31 repairs the cleaner case and
R32 repairs the nested overwrite case. The new prefix-return gap remains
open. A whole-analyzer relevance theorem
remains open. No additional tail, query or field-cap exception is implied
by these open obligations. The selected semantic deltas are listed above.

## 6. Validation and acceptance

The proof package reuses the source-hash-checked 7,009-claim dependency chain
and adds **72 claims: 7,081 cumulative across 407 checked modules**. These
include the counterexample, not 7,081 claims of whole-analyzer soundness.
Axiom auditing permits only `propext`
and `Quot.sound`; no classical choice, custom axiom, hole or external
proof oracle is accepted. See the package receipt for the final count.

**53 native tests pass**: 50 existing component checks across reply service,
strict MUST replay, definite reply support, uniform actual coverage, exact
point writes, E-aware child replay and initial E preservation, plus three
cleaner/getter diagnostics. The failing-behavior diagnostic asserts the
current missed observation, not correct behavior. The tests do not install
NE or establish the missing whole-analyzer theorem.

Inherited reference measurements remain: new cases settle at run-7/run-9;
the finite search's latest diagnostic is run-25; the historical unchanged
native driver diagnostic is run-31/POLICY. No new project scan is claimed.

Acceptance of a general soundness claim requires G1–G4 to be discharged
for the activated native scope. R31 resolves the demonstrated admission gap
in the proposal, with separate local and example proofs. Until then, retain the stated fragments
and conservative unsupported-case fallbacks. The consolidated proposal's
termination milestone remains valid in its tested scope; this audit does
not enlarge that scope.

Current repair validation adds 27 constructive claims (7,108 cumulative,
409 modules) and seven native components (60 tests in the combined suite).
The repaired reference stops at run-3; native validation is a component
pipeline, not a patched cold driver. The original 72-claim audit and its
historical countermodel remain source-hash checked.

Follow-up validation adds 16 constructive claims (7,124 cumulative across
410 modules) and three native diagnostics (63 tests combined). The new
selected-policy counterexample stops at run-3 with zero findings. Its
current-policy and direct controls retain the finding at run-3; no-write
control stops with the finding at run-1. The separate 784-configuration
GEN-helper sweep has no mismatch, with natural stops through run-13 and
diagnostics through run-25; it does not cover this overwrite mechanism.


The next handoff-mask audit adds 27 constructive claims: 7,187 cumulative
in 413 checked modules. The native controls reach natural run-3 completion.
The report distinguishes the invalid unprojected candidate model from the
actual F72 trace. No additional analyzer semantic change is selected.

The combined targeted suite now passes 70 native tests. A fresh 1,536-case
conditional-marking reference sweep with Run2Relay C2 has zero observation
mismatches and fixed points within every checked run. All cases finish
naturally by run-13; the diagnostic scan reaches run-25. This finite sample
does not resolve G1–G4. Current concrete statuses are in the later
prefix-return repair and post-DIRECT investigation above.


The ordinary-prefix audit adds 25 constructive claims (7,212 cumulative,
417 modules) and seven native tests. The combined targeted suite passes
77 tests, including diagnostics that deliberately assert the missing broad
finding at natural run-5. The exact controls and both 884 controls retain
their NORMAL findings at run-5. No production fix is installed.

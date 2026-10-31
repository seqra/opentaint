# Constant filtering and Target-guided ZERO: implementation proofs

Date: 31 October 2026. This package checks retained protocol kernels and
labeled historical admission controls. It does not verify the complete
current implementation proposal or change the Kotlin runtime.

The [concrete exact-DEMAND amendment](../../../demand-layer-exact-initials.md)
supersedes this package's concrete MAY-rejection and weakened-ND
classification assumptions. Its current laws are checked in the
[new proof package](../demand-layer-exact-initials-20261031/README.md).
The original Lean kernels here are retained without rewriting history.

- [Specification](../../../../docs/design/bidirectional-constant-filter-target-zero-implementation-20261031.md)
- [Implementation proposal](../../../../docs/design/bidirectional-constant-filter-target-zero-implementation-v2-20261031.md)
- [Proof guide](../../../proof-guide.md)

The specification SHA-256 is
`43fce6a3ff0adaac7361124dbe531ce2933e19437b743b22faf6d6c9b24a8a50`.
The reviewed runtime is based on
`e090118e5f9603f1973c0578a3e04998035f4508`.

## Reproduce the check

From the repository root, run:

```sh
python3 spec/lean/proposals/constant-filter-target-zero-implementation-v2-20261031/check.py
```

Use Lean `leanprover/lean4:v4.33.1`. The checker selects this toolchain
through `ELAN_TOOLCHAIN`. It compiles one module at a time with one worker,
one CPU, a 768 MiB Lean memory limit, and a 90-second command timeout.
It needs no project build or project analysis.

The package has 16 modules, 293 theorems, 248 public executable
definitions, and 2 public abbreviations. The checker audits all 543
explicit public declarations. Only `propext` and `Quot.sound` are permitted. No classical
choice, `sorryAx`, custom axiom, `noncomputable`, `unsafe`, or `partial`
declaration is permitted. A compiler warning fails the check.

The generated [checks.json](checks.json) records the result, every audited
declaration, the toolchain, input hashes, and log locations. The checker
binds the specification, implementation proposal, this README, its own
code, the models, and the reviewed runtime source files. Generated logs
and `.olean` files go to the ignored
`spec/lean/.lake/verification/constant-filter-target-zero-implementation-v2-20261031/`
directory. They are not maintained proof inputs.

## Retained protocol and historical admission rules

```text
Constant in runtime data or any premise member -> reject the whole packet
all current offers fail admission             -> no extra action

NORMAL sink binding with retained full dependencies -> NormalTarget(id)
complete DEMAND sink binding -> DemandTarget
accepted actual reverse GEN  -> DemandTarget

NormalTarget + complete all-NORMAL support -> same NormalTarget(id)
NormalTarget + DEMAND or native demotion    -> no result
NormalTarget in backward                   -> ignored
DemandTarget + permitted complete support  -> anonymous DemandTarget

persisted full owned NORMAL key -> no new owned emission/publication
persisted ZERO -> NormalTarget  -> skip replay; keep the settled report

final report <- configured-root ZERO -> NormalTarget(id)
next-run Target guidance <- DemandTarget only
```

Historical concrete admission only:

```text
EXACT demand + submitted ANY -> no initial
```

That equation describes the superseded C2 policy, not the current
concrete exact-DEMAND proposal. Do not reinterpret its scalar mark model
as a proof of the unchanged FLOW policy. Truly rejected offers still
have no extra action; a matching concrete MAY offer is no longer one of
those rejected offers under the amendment.

Target is a terminal conclusion outside AP facts. C2 control admission
uses an actual ZERO. C5 tests the actual premise against `D_c` and the
actual conclusion against `D_p`, using one demand row. A ZERO `D_p`
accepts ZERO and either exact Target label. AP `D_p` rejects Target.
Handoff keeps complete `(Target, original member)` pairs, including a
ZERO original. Ordinary NORMAL ND and backward-ZERO **AP** selection
remain. NormalTarget never becomes guidance through those exceptions.

The package has no withdrawn NORMAL-to-DEMAND report promotion policy
and no withdrawn NormalTarget source-permission workaround. The explicit
31 October amendments preserve the computed layer for ordinary FULL
ZERO and nonzero origins, keep GROUP/static overrides, and convert accepted
backward source-summary ZERO results to anonymous DemandTarget. They are
semantic changes, not an extension of current exact-data C2 permission.
The subsequent static Target correction adds anonymous terminal reader
endpoints to the same run-1 frozen closure. It retains paired C5 and
produces a witnessed `(Target,ZERO)` row for a `ZERO -> C.f/T ->
DemandTarget` route. GROUP mode stays available; known GROUP coverage
issues are recorded, and acceptance currently focuses on FULL mode.

## Proof map

| Module | Main checked obligation |
|---|---|
| [SelectedCore](SelectedCore.lean) | Typed control C2/C5, raw NORMAL publication, paired handoff, source scope, continuation, and root report extraction |
| [ConstantBoundary](ConstantBoundary.lean) | Whole-packet rejection, no ND weakening, no rejected callback, constant-free store closure, and preservation of routes whose intermediate packets are in the selected domain |
| [TargetZeroRegistry](TargetZeroRegistry.lean) | Stable exact sink-key interning, distinct keys, and executable ID witnesses |
| [InitialEmissionExact](InitialEmissionExact.lean) | Historical concrete MAY/EXACT rejection and its controls; superseded by the exact-DEMAND amendment |
| [UnansweredDemand](UnansweredDemand.lean) | Generic actually-empty emission remains a no-op; specializations through the old exact emitter are historical |
| [TargetZeroND](TargetZeroND.lean) | Finite all-NORMAL support, complete binary origin union, and independent seed memberships |
| [SelectedTargetApplication](SelectedTargetApplication.lean) | Complete admitted NORMAL-only forward application, exact ID preservation, native-demotion rejection, anonymous DEMAND, and backward ignore |
| [TargetJoin](TargetJoin.lean) | Arbitrary-arity complete bucket products, exact call/slot keys, full origins, selected result generation, and executable complete-tuple witnesses |
| [OwnedDelta](OwnedDelta.lean) | Full owned-key retained/seen suppression equals logical set extension; pending work and independent seeds remain |
| [TerminalProtocol](TerminalProtocol.lean) | Register, replay, start, publication and receipt invariants; failed sends keep required work; successful flush publishes every seen row |
| [ZeroSettlement](ZeroSettlement.lean) | Constructive finite settlement of every exposed ZERO row and atomic completed record/report snapshots |
| [ProducerDomain](ProducerDomain.lean) | Held REACH/TAINT plus K6 excludes FLOW premise members; actual reverse GEN has the same law; run-1 static layer and original descriptors remain |
| [FullZeroSourceReplay](FullZeroSourceReplay.lean) | Historical ZERO-only override; retained exact NORMAL ZERO-native replay and bounded cleanup kernels; nonzero demotion theorems are superseded, not selected runtime laws |
| [FullComputedLayer](FullComputedLayer.lean) | Current ordinary FULL computed-layer preservation for every origin, no DEMAND promotion, exact/STAR initial layers, static/GROUP overrides, ZERO-native compatibility, NORMAL weakened-ND-arm counterexample |
| [StaticTargetClosure](StaticTargetClosure.lean) | Existing eager/factored static closure with typed ZERO/Target endpoints; source and target seed witnesses; direct and inherited W/B/R examples; paired Target/ZERO C2/C5 and read-only ZERO-exit probe equality; precise FLOW and full/group label reference |
| [SourceSummaryCompletion](SourceSummaryCompletion.lean) | An accepted backward concrete nonzero-to-ZERO summary emits DemandTarget under the whole caller original; balanced ZERO and forward/nonzero results stay AP; native/current routes share dispatch; no fake source hit or C5 bypass |

Important general results include:

```text
OwnedDelta.full_relation_membership_after_offer
OwnedDelta.batch_preserves_relation
OwnedDelta.pending_never_erased_by_offer
TerminalProtocol.successful_flush_publishes_every_seen
TerminalProtocol.missing_receipt_prevents_completion
TargetJoin.product_member_iff_complete
TargetJoin.full_origin_zero_iff_every_origin_zero
TargetJoin.every_complete_permitted_match_is_emitted
ZeroSettlement.committed_zero_invariant
FullComputedLayer.ordinary_full_keeps_computed_layer
FullComputedLayer.computed_demand_is_never_promoted
FullComputedLayer.full_star_initial_stays_demand
FullComputedLayer.full_exact_initial_keeps_normal
FullComputedLayer.NDArmRisk.normal_origin_projection_can_report_without_other_input
FullZeroSourceReplay.full_exact_source_has_native_route
FullZeroSourceReplay.ExactCleanup.serial_bulk_same_leaves_and_protection
SourceSummaryCompletion.native_may_replay_emits_target_before_empty_gate
SourceSummaryCompletion.completion_does_not_bypass_c5
SourceSummaryCompletion.Controls.source_completion_does_not_close_static_pair_gap
SourceSummaryCompletion.Controls.computed_demand_producer_has_no_native_admission_fallback
StaticTargetClosure.eager_iff_factored
StaticTargetClosure.sourceWitness
StaticTargetClosure.targetWitness
StaticTargetClosure.terminalGuide
StaticTargetClosure.target_pair_admits_zero
StaticTargetClosure.zero_target_pair_is_accepted
StaticTargetClosure.c5_target_equals_zero_probe
StaticTargetClosure.any_target_equals_any_zero_probe
StaticTargetClosure.Controls.inheritedLazy
```

`TargetJoin` proves the product/join boundary for arbitrary finite arity.
An executable witness contains the complete tuple, its arity, every
call/slot key, and the selected result. The three-slot control keeps the
nonzero middle origin even when the last origin is ZERO. Empty slots,
cross-call bindings, and wrong arity cannot produce a terminal. The
existing `arityAllowed` policy controls zero-arity behavior.

`ZeroSettlement` does not assume that a new nonroot ZERO row is already
reported. `processReceipts` executes exact owned-key admission. Completed
receipts and required publication establish parent-row closure. `settle`
then follows a finite `FirstAdmissionRoute` to a configured root or an
old settled row. It returns the actual stop witness and report membership.
`committed_zero_invariant` covers all exposed ZERO rows. The concrete
`0 -> 1 -> root 2` control evaluates a `configuredRoot 2` witness.

`TerminalProtocol` does not equate seen keys with delivered work. Its
invariant keeps each required delivery pending or received. A failed
send retains the obligation. Missing receipts prevent completion.
Only a complete barrier exposes a new record/report snapshot.

`FullComputedLayer` starts after unchanged AP transfer computes payload
and layer. It preserves ordinary FULL results under ZERO and nonzero
origins, never promotes computed DEMAND, and retains GROUP/static
DEMAND overrides. The independent initial table records exact NORMAL
and concrete STAR/MAY DEMAND. An all-NORMAL cube can produce NORMAL
weakened unary arms under unchanged run-1 ND handling; the conditional
counterexample shows that one arm can report without its other input.
The current amendment supplies cause-specific DEMAND for weakened source
and sink arms. That repair is checked by the new package, not by this
ordinary-layer kernel. The old NORMAL weak-arm control remains a
pre-repair counterexample.

`FullZeroSourceReplay.force` is the historical first ZERO-only policy.
Its nonzero blanket-demotion theorems are no longer current runtime
requirements. `zero_native_kernel_unchanged` establishes compatibility
of its exact ZERO-source/native kernel with the new override. Native
matching retains method/base/path/full-mark identity. Its backward MAY
read and forward ZERO read precede the current-demand gate. The exact
current-admission function in this old module still rejects every MAY
actual; that slice and all empty-gate conclusions based on it are
historical. Replaying a saved effect before C2 remains the selected order,
but a matching current MAY offer can now start a separate D lane.
The model
does not prove general AP matching or field transfer. The all-EXACT ZERO
cleanup kernel keeps ordered membership/protection; NORMAL nonzero and
MUST/STAR headers retain scalar fallback. Spatial predicates remain
runtime adapters.

`SourceSummaryCompletion` retains the post-match terminal boundary. It
still composes its call controls with the old `admitExact` function. Its
MAY-empty-current-gate and no-native/no-current-start controls are
historical admission comparisons. They do not describe the new D
admission. The source-summary dispatch itself does not admit an initial
or relax native matching. Current and saved accepted source
summaries use the same terminal dispatch. A backward nonzero concrete
summary premise and ZERO result produce anonymous DemandTarget under the
complete original; ZERO-to-ZERO stays AP control. The resulting terminal
still needs the selected same-pair C5 permission. Summary replay creates no actual source/action hit and does not fabricate
a fresh source seed. The explicit static control proves that rows
`(APa,ZERO)` and `(Target,APa)` both reject a caller `ZERO -> DemandTarget`.
It preserves the pre-completion counterexample instead of selecting a
bypass. `StaticTargetClosure` supplies the newly selected complete row.

`StaticTargetClosure` extends the previous static closure's exact
factorization construction with typed ZERO and DemandTarget vertices.
All joins still have a static middle. Only static/static relations inherit
through call-graph paths; ordinary W/R boundaries retain their exact
owner. A local reader ending in Target uses the same path construction.
`factor` and `expand` are executable translations between eager closure
and factored paths. `sourceWitness` and `targetWitness` return actual seed
endpoints, so closure cannot invent a ZERO origin. The direct and
inherited examples end at Target and project to `(Target,ZERO)`, which
ordinary control C2 and paired C5 accept. The old two rows still reject
that result; their separate endpoints never become a bypass.

The finite full-mark reference checks FLOW identity and FULL/GROUP
selector expansion. NormalTarget produces no terminal seed. AP path
compatibility, exact MethodKey/context ownership, existing B owner
visibility, query termination/early coverage, and Kotlin indexes remain
runtime adapters. The model does not claim that a local negative answer
permits skipping inherited search or that terminal seeds are copied to
all callers. The Target adapter must use the full existing C5 row search, including
ordinary AP virtual rows with a ZERO exit. The probe lemmas show that
Target and ZERO have equal acceptance under the same complete pair,
owner and original, for every exit kind and arbitrary row lists. Thus a
read-only `intersect(original, Reach.DEMAND)` query can test Target
permission without encoding or delivering Target as Reach. This also
retains getter/wrapper `(ret/T,ZERO)` composition. It does not change C5
or prove complete FULL conditional-source/caller-context correctness.

## Runtime adapter obligations and scope

1. Map full method/premise keys, original caller support, AP geometry,
   fields, marks, exclusions, type/protection masks, and native MUST
   classification to the model inputs. The package does not verify
   Kotlin AP matching geometry.
2. Apply the corrected full C2 query before current starts. Protocol
   subscriptions cover admitted/prepared calls. No new subscription is
   promised for an offer that has no current demand. Saved replay stays
   before this admission gate.
3. Map Kotlin locks, immutable messages, required sends, and actor
   completion to the protocol transitions. Cancellation or a failed send
   must not erase pending work. An incomplete run cannot commit a new
   snapshot.
4. Obtain each ZERO admission route from a configured root or an earlier
   actual NORMAL-ZERO caller with a prepared subscription and complete
   NORMAL support. Detached/imported rows have no such witness. No
   runtime grounding label or field-transfer change is proposed.
5. Process every relevant received terminal and flush every owned
   publication before completion. Lean evaluation does not prove JVM
   scheduling fairness or production fixed-point detection.
6. Place constant-domain checks before all callbacks, packed paths and
   storage. Keep literal IR effects and STATIC fields. Preserve actual
   source-action permissions and producer kind checks.
7. Preserve configured sink/rule identity, catalog lifetime, and atomic
   retained-record/report snapshots. Keep source/sink seed occurrence
   membership separate from anonymous Target deduplication.
8. Populate general join buckets from complete existing same-call,
   same-slot matches with full original support. The model does not
   verify Kotlin `KaryJoin` internals or permit removing a missing slot.
9. Map canonical selected mark representations to the layer model. FULL
   packets carry full marks; GROUP packets carry group tokens. Preserve
   computed AP layers, tails, E and protection before the scoped override.
   The exact source/native model uses a ZERO original and ordinary result;
   it does not certify native eligibility or complete ND support for every
   nonzero FULL result. Static-dependent results keep DEMAND.
10. Keep the selected run-1 static known-input/pool-interest route. Carry
   its selected STATIC original into terminal matching. Do not replace
   it with ZERO or introduce an abstract FLOW Target branch. Use the
   existing static call continuation, waiting set, PointReady dispatch,
   and staticSupply callback with a typed result payload. No separate
   terminal waiting directory is required.

Use the existing PublicationIndex premise postings, KaryJoin products,
publication flush/failure procedure, and Seed values. The protocol model
does not require separate runtime receipt, retry, or settlement services.
Sharing these implementations changes no selected transfer law. The explicit
31 October semantic amendments are explicit and have separate model and
runtime adapter obligations.

This is a constructive protocol and boundary proof package. It does not
prove whole-Kotlin refinement, unchanged findings for constant-bearing
derivations, whole-project no-FN, convergence, complexity, or measured
speedup. Runtime adapter tests and the selected project campaign remain
implementation obligations.

Implementation tests exposed composed-coverage issues beyond the original
boundary proofs. The
[exact-source trace](../../../../docs/reports/bidirectional-target-zero-exact-demand-source-gap-20261031.md)
motivates the FULL layer correction and native-source result dispatch.
The ZERO-native route is modeled. The later broad FULL override also
preserves computed NORMAL nonzero results. It does not certify their
native eligibility or complete guard support. The
[conditional FULL-source trace](../../../../docs/reports/bidirectional-target-zero-nonzero-source-admission-gap-20261031.md)
records the old narrow-policy run-3 loss. The new focused control
completes run-3 with both the real two-input report and the invalid
one-input report. The positive is restored, but the negative exposes a
NORMAL weakened-arm caller-context false positive in the pre-amendment
runtime. A source-and-sink ND repair is now selected in the concrete
amendment; it is not implemented or proved by these old controls. Do not retain the old
claim that every nonzero FULL producer is DEMAND or that the layer proof
closes this issue. A saved backward identity does not replace a missing
forward producer or its guard dependencies.

The constructive `computed_demand_producer_has_no_native_admission_fallback`
control retains a historical admission boundary: a source whose ordinary
transfer computed DEMAND has no NORMAL producer candidate, and the old
exact emitter rejects its MAY offer. The DEMAND/native-candidate fact
remains reusable, while the resulting empty-initial/no-current-start
claim is superseded by provisional exact admission. It assumes no other matching saved
producer or demand row. It does not force every nonzero FULL source to
DEMAND, relax C2, or add no-op behavior.

The [static source trace](../../../../docs/reports/bidirectional-target-zero-static-c5-gap-20261031.md)
motivates the selected typed static Target completion. The new closure
constructs the full `(Target,ZERO)` pair before run-2 without changing C5.
Its runtime adapter regression must retain the positive finding. Neither
kernel asserts that all emitted terminals pass caller C5 or that every
program route is guided. Complete FULL conditional-source/caller-context behavior and known GROUP
admission issues remain separate obligations.

The receipt marks `kernelScope=RETAINED_PROTOCOL_PLUS_HISTORICAL_ADMISSION`
and `currentProposalConformance=NOT_VERIFIED_BY_THIS_PACKAGE`. It distinguishes
`kernelSelectedLaws` from
`composedRuntimeCoverage`. Kernel PASS is not proposal readiness or a
whole-project no-FN claim. Runtime hashes include the relevant Target,
layer, source-summary, cleanup, native-record and demand implementations;
the receipt also binds the named regression test sources. The
`FullConditionalSourceDemandTest` source is bound as a composed-coverage
obligation, including its negative caller control. The checker does not
run or certify that test.

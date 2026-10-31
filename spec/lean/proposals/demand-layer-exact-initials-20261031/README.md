# Exact DEMAND initials: constructive design proofs

Date: 31 October 2026. Status: design proof package. This package changes
only proof artifacts and does not verify Kotlin implementation.

- [Specification](../../../demand-layer-exact-initials.md)
- [Proof dossier](../../../demand-layer-exact-initials-proofs.md)
- [Implementation proposal](../../../../docs/design/bidirectional-constant-filter-target-zero-implementation-v2-20261031.md)
- [Proof guide](../../../proof-guide.md)

## Reproduce

From the repository root:

```sh
python3 spec/lean/proposals/demand-layer-exact-initials-20261031/check.py
```

Use Lean `leanprover/lean4:v4.33.1`. The checker builds the 11 local modules
in a fresh directory, one worker and one CPU at a time, with a 768 MiB
per-command limit. It audits every explicit public theorem, executable
definition and abbreviation. The current inventory is 159 theorems and
121 executable definitions: 280 declarations. Only `propext` and
`Quot.sound` are permitted. No choice, `sorryAx`, custom axiom, unsafe,
noncomputable or partial declaration is permitted. A warning fails the
check.

The specification SHA-256 is `a37aeee246f5373f933269f3babd20a18e71d33a0b950021f612c0545e0c58d7`.
The generated [checks.json](checks.json) binds the models, specification,
proof dossier, current implementation proposal, README, checker and
reviewed reference source bytes. The proposal binding records source
alignment; it is not a proof of the full implementation or runtime. Those runtime bytes
are evidence of the current implementation reviewed by the design, not a
verification or implementation of the proposed policy. Build outputs and
logs go under ignored `spec/lean/.lake/verification/`.

## Selected core and limits

The core covers exact demands for FULL concrete marks on constant-free
ordinary data APs. Every path element in this model is a counted field.
Base IDs and full-mark IDs are immutable. JVM static anchor indivisibility,
array/accessor counting, rule specialization and actual compiled method
contexts remain runtime adapters. The existing static approximation and
GROUP policy are unchanged. The user selected concrete marks only. FLOW
keeps its existing behavior, as specified in section 14. A false core scope
predicate for FLOW is not a decision to reject it in the runtime.

The changed cell admits a matching same-prefix or ancestor MAY actual as
an exact DEMAND hypothesis. It also preserves DEMAND on exact actuals.
The prior demand row's layer is guidance, not a lower bound: a later exact
NORMAL actual can emit the same key in NORMAL. Exact keys retain empty
field exclusion. Concrete exact demands with nonempty E are rejected;
actual STAR/MUST exclusion still blocks descent. Both input and demand
budgets, full marks, bases and directed paths are checked. Limit zero is
rejected. Other geometric admission cells are not redefined here.

Starting-layer canonicalization happens before seen bits and coverage.
The initial key has no layer field. NORMAL and DEMAND are separate seen
memberships for the same valid exact key. Concrete STAR has intrinsic
DEMAND, so a supplied NORMAL tag is canonicalized into DEMAND and cannot
create a second copy of the same start lane. Existing static/GROUP mode
policies must also be applied before final-layer classification by the
production adapter.

ZERO uses the existing explicit permission and existing starting-layer
policy. Data coercion does not manufacture ZERO or Target. No new ZERO
DEMAND policy is selected. Dependent chains preserve the nonzero origin;
accepted backward source completion keeps that original. Independent
ZERO GEN and already admitted root/control paths retain their own rules.

## Proof map

| Module | Checked obligation |
|---|---|
| [Domain](Domain.lean) | Layer join, immutable key/seed separation, directed base/path/mark/exclusion and budget geometry |
| [ExactAdmission](ExactAdmission.lean) | Provisional MAY-to-EXACT DEMAND, actual DEMAND preservation, nonsticky prior guidance, all unchanged guards, intrinsic/start canonicalization and no data-to-ZERO |
| [C2C5Image](C2C5Image.lean) | Structural exact entry image iff C2-emittable, executable canonical actual witness, unchanged paired exit adapter and result-layer preservation |
| [AdmissionStore](AdmissionStore.lean) | Independent N/D memberships, both arrival orders, duplicate suppression, no erased pending work, canonical STAR collapse |
| [AdmissionBounds](AdmissionBounds.lean) | Reachable-store uniqueness and an injective fresh-seed bound of at most `2 * keys.length`, with constructive list removal |
| [NDProjection](NDProjection.lean) | Complete binding before projection, source/sink arm layer includes dropped support, same-origin/ZERO precise cases, full physical sink seed and no unary FULL blanket demotion |
| [FactoredOrigins](FactoredOrigins.lean) | Executable column choice, complete supported binding iff factored membership, equivalence to eager Cartesian search, separate all-ZERO witness, no invented origin, binary cost bounds, and incremental nonzero/Zero membership classification |
| [ResultLanes](ResultLanes.lean) | Rule-owned result admission preserves separate N/D lanes and monotone protection upgrades |
| [TargetLayers](TargetLayers.lean) | NormalTarget requires normal support, N cannot cover the D execution, DEMAND has no normal report/native record, arbitrary dependent chain preservation and no fabricated source action |
| [Pipeline](Pipeline.lean) | Actual reverse requirements and action IDs recover sourceA/sourceB; normal good finding by F3, bad and crossed callers absent, no global F3-stop claim |
| [IntrinsicMayCycle](IntrinsicMayCycle.lean) | Repeated finite F/B frontier through intrinsic MAY and existing saved source replay, no source guide or fake source hit, no general cross-run termination claim |

Important constructive results:

```text
ExactDemand.emitted_has_all_guards
ExactDemand.emitted_has_matching_base_mark_and_budgets
ExactDemand.guidance_layer_is_not_starting_layer
ExactDemand.c5ImageWitness
ExactDemand.c5_image_iff_c2_emittable
ExactDemand.canonical_seed_is_idempotent
ExactDemand.AdmissionBounds.reachable_admissions_are_bounded_by_two_times_keys
ExactDemand.NDProjection.normal_projected_arm_has_complete_dependency_support
ExactDemand.FactoredOrigins.choose
ExactDemand.FactoredOrigins.eager_iff_factored
ExactDemand.FactoredOrigins.normal_arm_iff_existing_origin_and_complete_supported_binding
ExactDemand.FactoredOrigins.binary_product_cardinality
ExactDemand.FactoredOrigins.binary_scan_budget
ExactDemand.FactoredOrigins.nonzero_growth_preserves_other_existing_normal_arm
ExactDemand.FactoredOrigins.omitted_existing_origin_is_unchanged_after_incremental_growth
ExactDemand.demand_is_preserved_through_any_dependent_chain
ExactDemand.legal_may_cannot_apply_cached_normal_target
ExactDemand.Pipeline.only_new_good_route_recovers_source_b_permission
ExactDemand.Pipeline.good_report_is_normal_by_run3_and_bad_is_absent
ExactDemand.IntrinsicMayCycle.frontier_never_changes
```

## What the finite pipeline proves

The principal program has configured local root source actions A and B,
a two-input producer in `make`, two one-field writes, and a good and bad
sink. The root source actions generate local facts; they do not gain a
separate persisted root-local producer record.

```java
// A: assign T1; B: assign T2.
// make: CM(p,T1) AND CM(q,T2) -> assign U at ret.$.
// sink: CM(value,U).
a = sourceA(); b = sourceB();
r = make(a,b); tmp.g = r; out.f = tmp;
bad = make(a,clean);
sinkU(out.f.g); sinkU(bad);
```

F1 waits for the producer's complete NORMAL witness, then marks both
weakened unary arms DEMAND. Its bad-call over-approximation is provisional,
and produces no normal report. The physical backward sink seed is an
independent existing NORMAL requirement: the good two-field path is cut
to MAY/DEMAND, while the bad uncut return seed is exact/NORMAL. They admit
the same helper key in D and N, which must both be processed.

The actual reverse producer action 31 emits both argument requirements.
Good-call mapping reaches source actions 41 (A) and 42 (B). Bad-call
mapping reaches 41 and a clean object, so it does not grant 42. The old
MAY rejection loses the good path and retains only permissions 31 and 41.
The new D admission obtains 31, 41 and 42. Admission alone grants none.

F3 source facts require their real source permissions. Exact NORMAL
actuals discharge old guidance DEMAND. The later complete ND summary
binds both inputs at the same call. The good call reports; the bad call
and two crossed partial callers do not. The direct ND sink uses the full
physical predicate seed and the same complete later binding.

This is a finite executable model of the stated marks, bindings and
transfers. It is not a proof of JVM lowering, every NNF predicate, every
AP normalization, native matching, scheduling fairness, completed-barrier
reporting, or arbitrary project findings. Existing NORMAL ND guidance may
remain after the good F3 report. The model does not claim a driver stop
at F3.

## Factored support and work

The factoring model assumes one already canonical, compatible proof/header
partition with accepted NORMAL origin domains. It must not mix columns
from different rules, header partitions, call contexts or predicate proofs.
For a known origin P, every column must contain P or ZERO. `choose` returns
an actual binding using `List.find?`; no existence proof uses choice.
The origin must already occur in the union. An all-ZERO binding is checked
separately and cannot invent a nonzero arm.

The eager reference constructs the Cartesian product. The factored test
has the same supported-binding answer. With k binary columns, product
cardinality is `2^k`; the per-origin column-scan budget is `2*k`, and each
column's scan is bounded by its length. The origin union is already owned
by the rule store. These are practical reference-operation bounds, not a
whole-analyzer complexity or measured speedup claim. A conservative
implementation can demote more arms; it cannot create NORMAL from missing
support.

Incremental classification keeps the same canonical compatible columns.
A fresh nonzero Q membership cannot change the P-or-ZERO test for another
existing P, and cannot change the all-ZERO test. Thus nonzero growth only
needs to retest the added origin. Adding ZERO can unlock multiple old
origins and the all-ZERO binding, so it must revisit the full union. The
proof uses per-column membership growth, not only a globally new origin;
an existing P can become complete when it first arrives in a missing
column. `omitted_existing_origin_is_unchanged_after_incremental_growth`
proves that the selected candidate set misses no changed support test.

These incremental laws concern support classification. They do not waive
existing full invalidation after a version gap or protection growth.
Rule-owned protection/cycle upgrades and separate result lanes retain
their own obligations; Q-only support candidates are not a proof that
all other emission annotations stay unchanged.

## Caller and termination boundaries

The caller keeps actual Facts and applies saved summaries before current
C2. Cached application does not require a new admission descriptor.
Legal production MAY facts carry DEMAND: their AP application stays D and
a cached NormalTarget is rejected. The synthetic MAY/N test proves only
that local coercion still chooses D; it does not certify invalid inputs
for existing cached application.

The intrinsic-MAY counterexample uses an already persisted NORMAL source
producer. Its backward native replay occurs before C2 and needs no invented
source demand. It creates no actual source callback. Root ZERO permission
was already explicit, and Target projection retains the complete
`(Target,ZERO)` pair. The check helper's exact D guide is refreshed by its
existing reverse sink need. Each fixed round is finite and provisional,
but every positive field budget can reproduce the same frontier. Global
termination and a progress policy are not proved or selected.

Runtime implementation and validation are separate work. The checker
records kernel results separately from implementation status and adapter
coverage; reference source hashes do not establish runtime correctness.

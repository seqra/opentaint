# Branching field recurrence and regular goal service

R39 **[REC] [LOOP]**, 17 November 2026. Production is unchanged.
[Proposal](../../../../docs/design/bidirectional-regular-field-goal-service-20261117.md).
[Counterexample, per-run traces, native results and limitations](../../../../docs/reports/bidirectional-branching-field-termination-20261117.md).

A writer can produce `{g,h}* f` while a reader accepts `{g,h}* g`.
Truncation hides the final mismatch. The same root ZERO/DT recurs at every
pair in the scoped return-cone model. Every measured inner worklist is fixed.
The new certificate proves the complete word languages disjoint. It adds
no AP tail, field-cap exception or full-path evidence on a call.

## Constructive proof inventory

| Module | Claims | Scope |
| --- | ---: | --- |
| `PairedReference` | 0 | Executable cold C2/body/C5/saved-summary model; two distinct outer callees; recursive owner fixed points; complete principal offers and raw initials |
| `FrontierCycle` | 12 | Exact word mismatch; cut removes final field; arbitrary-depth MAY/DEMAND candidate; paired C5 cut and source-root membership |
| `CycleRules` | 11 | Real C2 image witnesses, permitted inside application, current C5 result, forward/reverse application and cold run-1/run-2 fixed points |
| `OperationalCycle` | 11 | Calculated writer/reader results and root candidate for every pair; calculated reverse publication and next selectors; cold global-cut equivalence; later true FL(Dp)+1 cuts |
| `RegularCertificate` | 19 | Word-run/product synchronization; closed-set emptiness; executable clause coverage; all grammar derivations; arbitrary word lengths; equal terminal chunks and parity controls |
| `RegionSemantics` | 5 | Actual source/observer word append; valid exact-point relation cannot be pruned; loop write order; incomplete-slice fallback |
| `RegularRepair` | 7 | Frozen-goal run-1/3/5 transition and uncapped quiet suffix; all-origin service; no loss of a valid relation |
| `RegularSearch` | 0 | 9,604 unary and 100 branching grammar comparisons |
| `PairedSearch` | 0 | 32 full cold paired models plus the long shared-word control |

**65 new claims; 7,468 cumulative in 445 source-hash-checked modules.**
Lean **4.35.0** permits only `propext` and `Quot.sound` in the transitive axiom
sets. There are no custom axioms, proof holes, classical choice or external
decision shortcuts. The generic admission proofs use constructive Nat BEq
instances; the audit rejects the classical generic-order fallback.

`CycleRules.Cell` is only control/index bookkeeping. It is not the proof
that a candidate exists. `OperationalCycle` calculates that candidate from
actual C5 and AP application results, including the next reverse selector.
The recurrence uses the inherited fair least-fixed-point/retained-provider
contract. It is a scoped scalar return-cone proof, not a proof of every
native scheduler, alias adapter or compaction implementation. G1–G4 remain
open. Finite native run-9 evidence is not an uncapped proof.

NoRoute safety is more general than this counterexample: equal accepted
words must reach an accepting product pair. A validated closed product set
with no such pair cannot remove a valid exact-point relation at any depth.
The compiler checks all supplied clauses. Code-to-complete-clause coverage,
all source aliases, caller bindings, rule effects and observer ports remain
explicit eligibility/proof obligations. A missing one returns Unknown.

## Reproduce

Use a fresh output directory outside Git and the preceding 7,403-claim
receipt under the external data root:

```sh
python3 spec/lean/proposals/branching-field-cycle-20261117/check.py \
  --dependencies /absolute/external-data/mark-origin-soundness-20261117/checked-proofs \
  --out /absolute/external-data/branching-field-cycle-20261117/checked-proofs
```

The checker verifies all 436 parent source hashes, compiles all nine new
modules in dependency order, and audits every new theorem's transitive
axioms. It then executes these fresh checks:

```text
REGULAR_SEARCH unary=9604 branching=100 failed=0 largestVisitedProduct=20
PAIRED_SEARCH total=32 failed=0 latestNaturalRun=7
LONG_SHARED result=(13, (true, true))
REGULAR_REPAIR branch=false positive=false result=(5, (false, true))
REGULAR_REPAIR branch=false positive=true result=(7, (true, true))
REGULAR_REPAIR branch=true positive=false result=(5, (false, true))
REGULAR_REPAIR branch=true positive=true result=(7, (true, true))
```

Unary grammars use nonempty repeat words of length 1..3 and terminal words
of length 0..2 over two fields. Independent repeat-count word witnesses
check empty/nonempty classification up to a product bound. Branching tests
use several prefix sets and distinct/equal terminal symbols. The 32 cold
checks include one/two recursive branch words and equal/distinct one/two-field
terminals; every in-run fixed point is checked. The long positive model
needs natural run-13. These finite checks do not prove universal convergence.

## Native checks

Baseline: `966a40c3647268cc006e5776591d6b68849379d0`.
The new classes are `BranchingWriteReadTerminationTest`,
`RegularFieldPathCertificateTest`, `LoopWriteReadTerminationTest` and
`WordChunkWriteReadTerminationTest`. `RegularTargetHandoffAdapter` is test-only.
It preserves method/scoped DATA, ports and native handoff compaction and
omits only the selected root ZERO/DT. Records and seeds are unchanged.
The query grammar and the unfused CFG come from the same finite branch
specifications; every field operation in that CFG is a separate instruction.

```sh
./core/gradlew -p core :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.BranchingWriteReadTerminationTest \
  --tests org.opentaint.dataflow.bidi.RegularFieldPathCertificateTest \
  --tests org.opentaint.dataflow.bidi.LoopWriteReadTerminationTest \
  --tests org.opentaint.dataflow.bidi.WordChunkWriteReadTerminationTest --offline
```

The combined earlier 143-test suite plus **27 new tests** passes **170 tests
in 26 classes**. This includes expected-broken baseline controls. Recursive
negative diagnostics reach **run-9/POLICY**, separately from the uncapped
proof. Repaired negative cases finish naturally at **run-5**. Short positive
and different-observer-coordinate controls retain their NORMAL finding.
Older source-specific nested-loop validation still reaches natural run-17.

The two-loop and mutual-recursion controls already terminate in the baseline
(run-5/run-3). The same-final-field and parity native controls do too; these
are valid proof generalizations, not additional native cycle claims.

The long word `g.g.g.g.g.g.f` is shared. The regular certificate correctly
declines pruning. Native baseline and adapter both naturally stop at run-5
without the expected NORMAL observation, with **zero adapter rewrites**.
The selected-policy reference retains it at run-13. This explicit existing
baseline/proposal-integration limitation is not a passing reachability test
and is not caused by R39. It does not satisfy phase 3's baseline-success
condition. It stays recorded for future implementation validation.

Unsupported mixed/two-sided or nonlinear field effects, unknown aliases or
initial bindings, internal GEN, ND, statics, GROUP, unproved cross-owner
epsilon recursion, and general cleaner combinations do not get a certificate.
No claim is made for arbitrary production extraction or full-program
termination/soundness. All earlier proofs and native controls remain checked.

All compiled files, hashes, XML and full captures are outside Git under
`branching-field-cycle-20261117/` in the
[external data root](../../../../docs/reports/EXTERNAL_DATA.md).

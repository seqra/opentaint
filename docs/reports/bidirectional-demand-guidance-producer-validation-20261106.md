# Demand-guide producer validation — 2026-11-06

The selected producer repair passes **3,009 native tests** and restores the run-3 report checkpoint in both small prefix fixtures. Their natural traces finish run 5 with one normal report. The separate shared-loop fixture remains unresolved: it naturally completes run 5 with zero reports and fails its expected-one-report assertion. This report seals the native validation before the project campaign. The fresh `4182adae6` project commands have now ended; their quality and performance review is separate.

The [portable evidence bundle](data/bidirectional-demand-guidance-producer-validation-20261106.json) records the tested working-tree hashes, commands, XML counts and hashes, both new test classes and their complete final XML, the finite-model sources and checks, and complete program/shared-loop logs. Tests ran on the uncommitted correction over `f07e82139`; the commit that contains this report includes those tested source bytes. Report collection started no Gradle, JVM or Lean process and changed no production source or existing log.

The repair follows the [selected demand-guidance design](../design/bidirectional-demand-guidance-retention-implementation-20261106.md). It changes three production files:

- `SpatialCanonical.kt` retains explicit positions for real `FlowTree` values with `layer=DEMAND` and `tail=ANY`, through cold packets and warm canonical state. DATA normalization remains available separately.
- `Groups.kt` stops ancestor subtraction from rejecting those guide positions. Equal-coordinate duplicates and existing same-head mx intersection remain active; a weaker mx can require fresh support without adding a new head.
- `DiagonalRelations.kt` explicitly uses DATA normalization for packed TAINT's temporary FLOW geometry. That geometry does not acquire guide-retention behavior.

Scalar C2, admission layers, field transfer and NormalTarget rules are unchanged. This is a repair for the selected FLOW-demand producer domain, not a general NORMAL-to-GUIDE design or a first-field MUST emitter.

Root's final native command, from `core/`, was:

```text
./gradlew :opentaint-dataflow-core:opentaint-dataflow:test :opentaint-dataflow-core:opentaint-jvm-dataflow:test --console=plain --max-workers=1 --no-build-cache
```

Session 8123 ended with code 0 and `BUILD SUCCESSFUL in 2m 42s`. The totals below were read from the actual XML, not inferred from the console summary.

| Module | XML files | Tests | Failures / errors / skipped |
| --- | ---: | ---: | ---: |
| Dataflow | 389 | 2,548 | 0 / 0 / 0 |
| JVM dataflow | 45 | 461 | 0 / 0 / 0 |
| **Total** | **434** | **3,009** | **0 / 0 / 0** |

All 434 XML files were copied without changing their originals to the [external archive receipt](/drive-testcomp/opentaint-go-rules/canonical-relations-directional-inside-20261105/preparation/flow-demand-guidance-producer-validation-20261106/full-native-xml-20261106T124836060239Z/receipt.json). The receipt SHA256 is `08f16eeaeac14f0cbe8f2cc31781b053d8353d71d9993c02616e920d4093159b`. The portable bundle also contains each XML count and hash. Its two new classes contribute 12 producer tests and four mx follow-up tests; those 16 tests are already included in 3,009. Root's separate `:classes` build, session 1153, also ended with code 0.

The real RED-to-GREEN evidence has specific setup qualifications:

1. Session 19947 failed all 12 cases during fixture construction: the original FLOW premise illegally excluded marks. These were setup failures, not guide-regression evidence. Root changed the premise to legal `MarkSlot.STAR`.
2. With that legal fixture, session 69027 produced **eight assertion failures and four passing controls**. The failures cover cold AP packets, cold and both-order FlowGroup admission, point/SUMMARY/publication owners, and frozen paired handoff. In particular, root-first rejected the fresh child and child-first removed the retained child. This is the native producer RED evidence.
3. After repair, session 98077 passed all 29 targeted tests: 12 producer tests and 17 spatial tests. The final suite also passes all four mx cases, including the detached publication batch's final child-mx replacement and unchanged packed TAINT canonicalization.
4. A wrong JVM project task path and the prohibited `vararg TaintMark` test helper caused separate setup/compile failures. Neither is behavioral RED evidence. The current repository mx helper uses a nullable single-mark parameter.

The first full dataflow pass after the repair had six failures in old guide-contract expectations. The reference updates are intentional semantic changes, retained in the bundle's diff and failure list:

- `SubsumptionTest` and `MethodEdgeStoreTest` distinguish unchanged region coverage from guide-coordinate admission and freshness.
- `NormalStarRelationStoreTest` retains detached FLOW/DEMAND/ANY guide rows while continuing to compact MUST data. `SpatialCanonicalTest`, updated earlier, makes the same guide/data distinction.
- `LoopCanonicalBoundaryTest` observes both explicit guide heads before restriction. An observer-certified cut remains permitted; a distinct child observation prevents that cut.
- `CurrentModeActionsTest` expects the additional raw `return.f.EXACT/FLOW` initial produced by existing same-head C2. It still asserts that the named cleaner removes `f/T` and the final reports contain only the `g` and `k` cases. Both action-fixture tests pass in the final XML.

These updates do not redefine concrete TAINT coverage or scalar C2 to obtain a pass. They change the storage reference contract for retained FLOW-demand positions and its existing downstream images.

The [finite-model receipt](../../spec/lean/proposals/demand-guidance-retention-20261106/checks.json) records **39 passing lemmas**: 16 in `GuidanceFrontier.lean` and 23 in `ProducerGuidance.lean`. The current source hashes match that receipt. Its axiom audit allows only `propext` and `Quot.sound`. The model covers finite FULL scalar rows, coordinate freshness, exact paired-label handoff and same-head mx request union with unchanged scalar emission. It starts from supplied rows; it does not prove native producer retention, production C5, budgets, aliases, statics, role adapters or whole-engine effects. No proof was rerun for this report.

Root ran the canonical-prefix and uniform-prefix check and trace tasks together in session 26823; the command and complete log are embedded in the bundle. All four tasks passed in FULL mode with a 1 GiB heap and one active CPU:

| Fixture / task | First normal target / report | Latest completed run | End reason | Normal reports |
| --- | --- | ---: | --- | ---: |
| Canonical prefix / check | 3 / 3 | 3 | POLICY checkpoint | 1 |
| Canonical prefix / trace | 3 / 3 | 5 | NO_DEMAND_EDGE | 1 |
| Uniform prefix / check | 3 / 3 | 3 | POLICY checkpoint | 1 |
| Uniform prefix / trace | 3 / 3 | 5 | NO_DEMAND_EDGE | 1 |

The check tasks stop at an explicit run-3 checkpoint. Only the trace tasks establish natural run-5 completion for these two fixtures. These four executions are not four independent vulnerability findings.

The shared-loop run, session 32528, returned code 1 after:

```text
RESULT firstReport=null normalReports=0 terminal=AnalysisEnd(status=COMPLETE, run=5, direction=FORWARD, reason=NO_DEMAND_EDGE, run1MarkMode=FULL)
```

The analysis completed; its program assertion failed. The guide repair therefore does not resolve this reproducer. The full native pass must not be reported as all program or project quality passing.

The later committed-runtime campaign covers OWASP, Conductor, ThingsBoard and Stirling-PDF. Its baseline-relative quality, latest reached/completed/accepted iterations, OOM/timeouts, profiles and performance require a separate report. No baseline was rerun here. There is no final Conductor-recovery, broad convergence or performance-improvement claim in this native validation.

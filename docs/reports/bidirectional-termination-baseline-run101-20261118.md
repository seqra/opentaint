# Pre-refinement termination baseline through run-101

The analyzer is restored to `0438facd2a09e44a386b829cb2f1f4fe3d3954a8`.
Its production sources and benchmark launcher match that revision.
The tests use FULL and limits `1,1,2,…,100`, with the final forward
barrier at run-101. The production policy still ends at run-11.
The previous [termination catalogue](bidirectional-demand-termination-counterexamples-20261115.md)
and its constructive recurrence proofs supply the sample definitions.

## Native and reference outcomes

`RUN_LIMIT` means the run and barrier completed with demand remaining.
A timeout gives the latest reached run and the last completed barrier.
The run-101 diagnostics establish a reproducible lower bound on the
duration of a cycle. The selected Gradle suite passed 114 tests. The
corresponding uncapped models establish
recurrence within their stated scopes.

| Fixtures | Latest reached / completed | Result |
| --- | --- | --- |
| Exact/protected original, alternating uniform-input control, protected relevant and unrelated returns, unadmitted same-mark and other-mark returns | run-101 / run-101 | `RUN_LIMIT`. Each retains the repeated root Target. |
| Exact input, deeper real exclusion, carried exclusion, alternating conditional rules | run-101 / run-101 | `RUN_LIMIT`, repeated root Target. |
| Direct concrete MUST replay, uniform replay and different-path uniform replay | run-101 / run-101 | `RUN_LIMIT`, repeated root Target. |
| Exact root/descendant cleaner, nested ALL/BELOW, and nested RemoveAll | run-101 / run-101 | `RUN_LIMIT`, repeated root Target. |
| Root MAY, global field cut, protected global cut, nested replay, overwrite replay, exact-origin nested write | run-101 / run-101 | `RUN_LIMIT`. Six cold fixtures using native transfer, C2, C5 and handoff. |
| Intrinsic MAY pass | run-101 / run-101 | `RUN_LIMIT`, with one provisional observation. Excluded from the ordinary-code design scope. |
| [REC] Self-recursive wrappers with one or two marking origins | run-101 / run-101 | `RUN_LIMIT`, confirmed observation and repeated root Target. The mutual baseline control naturally stops at run-5. |
| [REC] Disjoint branching write/read | run-22 / run-21 | Timeout with a Target still present at the last completed barrier. |
| [REC] Unfused ordinary write/read control | run-21 / run-20 | Timeout with a Target still present at the last completed barrier. |
| [REC] Nested reader negative and positive baseline | run-101 / run-101 | `RUN_LIMIT`. The positive control preserves the confirmed observation. |
| [LOOP] Ordinary disjoint two-loop control | run-5 / run-5 | Natural `NO_DEMAND_EDGE`. |
| Enclosing method with independent BB owners | run-101 reference | The historical BB model still has demand. The native analyzer uses its existing method/block owners. General BB decomposition remains a reference-only case. |

The finite acyclic fixture builds ordinary read, write and return forms
with the same branch and binding structure as the catalogue. The
exact-origin case uses the documented atomic nested write form.

| Acyclic fixture at run-101 | All handoff pairs | Target demand | Confirmed / provisional |
| --- | ---: | ---: | ---: |
| Root MAY | 4 | 1 | 1 / 0 |
| Global cut | 6 | 1 | 1 / 0 |
| Protected global cut | 7 | 1 | 0 / 1 |
| Nested replay | 5 | 1 | 1 / 0 |
| Overwrite replay | 5 | 1 | 1 / 0 |
| Exact-origin nested write | 2 | 1 | 0 / 1 |

## OWASP `doSomething`

Run the actual compiled `BenchmarkTest01000#doPost` entry and its
`Test#doSomething` helper, with the saved benchmark input and rule set.
The selected-entry scan completed run-101 by `RUN_LIMIT` with two
confirmed observations and zero provisional observations. The exact
benchmarked helper keys match across every same-direction handoff
from run-7 forward and run-8 backward. The integration test reran and
checked the same results.

| Barriers | Global field limit | Helper DATA pairs | Caller control pairs | All handoff pairs |
| --- | ---: | ---: | ---: | ---: |
| run-7, run-9, …, run-101 | 6, 8, …, 100 | 6 | 11 | 17 |
| run-8, run-10, …, run-100 | 7, 9, …, 99 | 8 | 22 | 30 |

With b for either modeled byte field, one forward raw relation
`p.b.[].*/FLOW→ret.b.[].*/FLOW,N` is restricted against the shallow
`ret.*/FLOW` selector. The relative cap stays 1 and publishes
`p.b.[].*/FLOW→ret.b.[any]/FLOW,D`. In the opposite direction the
shallow `p.b.*/FLOW` selector caps at 2, renewing the paired guide at
the element. The other cause is a native inside read that already
produces intrinsic MAY before C5. Increasing the global limit leaves
both producers active. NE addresses the empty-suffix ambiguity of a
field cut. Retiring the recurring pair needs the separate saved
replay proof.

The rollback audit checked all **664 helper pair instances** and
**2,374 clipped origin instances** from H7 through H101 against the
saved NORMAL basis in both native record roles. Each barrier contained
21 eligible NORMAL records and every clipped origin had a provider.
This reuses the archived 12-row copy relation. The audit verifies
geometry and native record roles. Current compiled-form completeness,
caller continuation and source-permission closure are separate native
acceptance checks for R41.
[Helper analysis](bidirectional-demand-refinement-performance-20261118.md#why-the-termination-rules-keep-the-helper-active)

### Isolated helper handoff ablation

A diagnostic removed the six helper FLOW pairs from the run-7 handoff
using the fixed method key and checked the shape of every removed pair.
It applied the same filter at later handoffs and removed no further rows.
The selected entry completed naturally at **run-11** with an empty
handoff. Exact SARIF rule/location identities matched both confirmed
observations from the run-101 baseline. There were zero provisional
observations in both scans.

| Run | Baseline handoff rows | Ablation handoff rows | Ablation Target gauge |
| --- | ---: | ---: | ---: |
| run-7 | 17 | 11 | 11 |
| run-8 | 30 | 22 | 1 |
| run-9 | 17 | 4 | 4 |
| run-10 | 30 | 15 | 1 |
| run-11 | 17 | 0 | 0 |

The diagnostic uses an allowlist. It tests the effect of omission
and the ordinary caller continuation on this entry. R41 still requires
the general predicate and its scope proof before native activation.
No Target, loop, or recursion rule took part in the ablation.

## Specification changes

| Evidence | Change |
| --- | --- |
| R32 shared static carry dominated Conductor run-2. The carry-only ablation restored completion at 183.584 s. The pre-rule run-2 took 41.308 s. | Keep native static C2/C5 and lazy lookup. Apply the R32 relay in validated nonstatic scopes. |
| Conductor retained 448,592 qualified memberships beside 449,452 ordinary memberships. Disabling the path changed the frontier. | Share admitted payloads and apply each authorized effective binding once. Keep distinct permissions. |
| Static C2 traversed 4.53 million and C5 9.45 million states before Conductor's guard. Stirling-PDF run-3 rose from 4.224 s to 418.955 s. | Preserve native static coverage and native loop plans. Share exact entry tests and paired output tests for revised C5. |
| Broad helper and terminal root obligations still recur. | Add certificate-gated R41 for copy service and acyclic R37/R38 for terminal service. Use same-lane R42 for the neutral and protected uniform-cut cases. Keep LOOP/REC deferred. |

The spec requires a strict improvement in a matched comparison and no
per-project regression in verified completion, reachability or resource
use. The initial rollback and extended tests establish the baseline.
The revised rules are a specification.
[Revised spec](../../spec/demand-refinement-and-termination.md) ·
[Performance attribution](bidirectional-demand-refinement-performance-20261118.md)

## Reproduction

```sh
./core/gradlew -p core :opentaint-dataflow-core:opentaint-dataflow:test --offline \
  --tests '*CycleTest' --tests '*AcyclicTerminationBaselineTest' \
  --tests '*CleanerTerminationTest' --tests '*RecursiveWrapperTerminationTest' \
  --tests '*WriteReadTerminationTest' --tests '*CycleComponentsTest' \
  --tests '*ProtectedCleanerGrowthComponentsTest' --tests '*HardRunLimitPolicyTest'

python3 scripts/demand_experiments/run101/owasp.py NEW_OUTPUT_DIR \
  --project PATH_TO_SAVED_OWASP_PROJECT_YAML --capture-agent PATH_TO_CAPTURE_JAR
```

The capture JAR comes from the performance archive at
`demand-refinement-performance-20261118.DS91bH/cutoff/OWASP-helper-H10-H11/agent/build/capture.jar`.
The run-101 archive is `termination-baseline-run101.NbDdcB`. It contains
the native log and outcome table, both OWASP baseline captures, the helper
ablation, the checked BB
reference and the rerun of the 24-case historical reference catalogue.
The new Lean checks prove grouped C5 membership equivalence, effective
reply sharing and the frozen origin test. The inherited report documents
the separate scope of the reference catalogue.
[Lean checks](../../spec/lean/proposals/termination-rollback-20261118/Handoff.lean) ·
[Reference verification](bidirectional-termination-fix-validation-20261117.md)

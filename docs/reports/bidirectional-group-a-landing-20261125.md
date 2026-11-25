# Group A landing: implementation and performance

Date: 25 November 2026. Build: `saloed/bidirectional` at `5804e44dd`
(`27264ff95` adds spec text only). Implementation proposal:
[acyclic-group-a-implementation.md](../../spec/acyclic-group-a-implementation.md).
Baseline: the legacy analyzer at `54ad708fe`, saved runs (not run again).
Next iteration: [bidirectional-next-iteration-20261125.md](../design/bidirectional-next-iteration-20261125.md).

## 0. Summary

- Group A is implemented as plain semantics, with no switch and no counter:
  R1, the G6 drop form with the path-filter change (`4fed782fa`), and R2,
  an EXACT cleaner keeps a MUST leaf (`5804e44dd`). All suites pass. The
  rule suite has 786 OK, 0 FP, 0 FN and 0 skipped cases.
- **Group A changes no result.** The confirmed and provisional results are
  the same as in the parent core on OWASP, Conductor and Stirling-PDF.
  The Conductor and complete Stirling-PDF SARIF files are byte-identical.
- **False negatives against the baseline:**
  - OWASP and Conductor: none.
  - Stirling-PDF: none. The 8 "missing" findings are the same confirmed
    findings, shown at another `return` of the same method.
  - ThingsBoard: all 15 are missing. Run-1 ends with a memory-guard OOM,
    so the analyzer accepts no forward report. This cause was there
    before group A (§8).
- **Performance:**
  - OWASP: the engine is 20% faster than the same core without group A,
    and runs 3-11 are 65% faster. Wall time is still 26% more than the
    baseline.
  - Conductor: no change. Run 8 times out, as before.
  - ThingsBoard: OOM in run-1, as before.
  - Stirling-PDF: 2 of 3 launches stall in a loop block and time out, as
    in the parent core. One launch completed run 11 in 160 s of engine
    time. The stall depends on the work order (§9).
- **Hot spots:**
  - Loop-block replay and loop output restriction (Conductor runs 4-8,
    Stirling-PDF stall).
  - FLOW subsumption maintenance in `FlowGroup.addAll`.
  - Run-1 repeats prescan work: alias analysis and rule resolution.
  - The call plans are built again in each run.
- **Memory (ThingsBoard):** run-1 keeps all its state to the barrier.
  Most of that state is DEMAND TAINT facts, stored once per FULL mark
  (14.7-17.4 marks per geometry).

## 1. Implementation

| Commit | Content | Production files |
| --- | --- | --- |
| `4fed782fa` | R1: G6 drop form for the type-filter mark policy; no class-static accessor below a true primitive | `ap/Primitives.kt`, `ap/Filter.kt`, `interp/FormsReference.kt`, jvm `bidi/interp/JIRTypeFilters.kt`, jvm `ap/ifds/JIRFactTypeChecker.kt` |
| `5804e44dd` | R2: an EXACT cleaner does not apply to a MUST leaf (both directions, every run) | `ap/Clean.kt` (`cut`, PART), `ap/Reference.kt` (`concPart`) |
| `27264ff95` | Spec: `ap.md` §4.7, §4.8, §2.2; `interpreter.md` §5.1 and G6; ApSpec module `AnyTaintExR2.lean` (7 theorems, `propext` only) | none |

The code follows the proposal snippets (§3.3, §4.3). The landed code has no
`G6Drops`, no `MustIgnoresExactCleaner`, no counters and no log lines.

**Tests.**

| Test | Change |
| --- | --- |
| `PrimitiveValuesTest` | A level-policy test |
| `JIRTypeFiltersTest` | `int / cls.f` and `int[] / [].cls` are rejected. The facts below `Integer` lose ordinary marks |
| `JIRG6DropPrefixTest` (new) | P1-P6 on 29 JIR types and 12 accessors, with the class-static accessor (1,885 paths). Multi-leaf cases per boxed type (assumption A1). 0 violations |
| `JIRStringChainFiltersTest` (new) | The decision rows. No type breaks a cut prefix (11,342 exact facts kept) |
| `G6DropFormFixtureTest` (new, 10 tests) | M4, D5 (6), D6 (16), all 202 String-chain variants. The results agree with `g6-drop-xsub-20261120` |
| R2 rows | `CleanerTest` (3 rows, plus a new runtime-vs-reference table over reach × any tail × layer × run), `ReferenceOperationsTest`, `FieldCleanStepTest`, `OneRunAcceptanceTest` (index 3), `JIRLoweredCleanerEffectTest` |
| Signed-off fixtures (proposal §4.6) | The two `UniformRootCleanerTerminationTest` cases and the `DescendantCleanerTerminationTest` case confirm in run 1. `protectedGlobalCutGrowth` is 101 / `RUN_LIMIT` and confirmed. Three tests were renamed because the old names stated the old behavior |
| `DemandLinkTest` | The DEMAND maker is now an AT_AND_BELOW cleaner at `h.g`, two accessors below the MUST root (R2 does not touch it). The test still has 7 runs, and all DLINK assertions are kept. Two other makers did not work: a MAY source has demand left at run 7, and a STAR source with a concrete mark ends ABNORMAL in run 1 |

**Gates (combined tree `5804e44dd`).**

| Check | Result |
| --- | --- |
| Module suite | 2,774 tests, 0 failed (R1 alone: 2,773; R2 alone: 2,763) |
| Jvm suite | 474 tests, 0 failed (it covers the IFDS use of `JIRFactTypeChecker`) |
| Lean `acyclic-group-a-20261124/check.sh` | 17 + 12 claims, only `propext` / `Quot.sound` |
| Rule suite, bidirectional (`docs/rule-testing.md`, fresh portable project) | OK 786, Skip 0, FP 0, FN 0, Disabled 22. 585 Java analyses entered the engine and completed |
| Rule suite, default engine | OK 786, Skip 0, FP 0, FN 0, Disabled 22 |

Latest completed run of the 585 Java rule analyses:

| End | 18 Nov (before) | Now |
| --- | ---: | ---: |
| run-1 `NO_DEMAND_EDGE` | 468 | 468 |
| run-3 | 109 | 110 |
| run-5 | 4 | 3 |
| run-7 | 2 | 2 |
| run-9 | 1 | 1 |
| run-11 `RUN_LIMIT` | 1 | 1 |

## 2. Configuration

- Harness: `scripts/benchmark_bidi_projects.py`, which runs the Gradle
  `runProjectAnalyzer` task directly.
  - Options: `--sides bidi --heap-snapshots --profile-runs 2 4 6 8 9 11`.
  - Production analyzer configuration, with no statistics switches.
  - Continuous JFR (profile settings).
  - async-profiler 30 s windows: 60 s into run-1 (`normal`), 60 s into
    runs 2, 4, 6, 8, 9 and 11, and at the timeout minus 60 s.
  - A heap snapshot when the MemoryManager guard reports OOM.
- Project parameters, as in the configuration:

| Project | Model | Heap | Analysis timeout |
| --- | --- | --- | --- |
| OWASP | `owasp-ci-investigation/project/project.yaml` (as `ci-analyzer-owasp.yaml`) | 8 GiB | 1,000 s |
| Conductor | `opentaint-test-conductor/opentaint-project` + conductor rules, passthrough, approximations | 8 GiB | 1,080 s |
| ThingsBoard | `opentaint-test-thingsboard/opentaint-project` (`max-memory: 12G`) | 12 GiB | 1,080 s |
| Stirling-PDF | `e2e-root/model-Stirling-PDF` | 8 GiB | 1,080 s |

- Launches: one per project. Stirling-PDF got two more launches, because
  the first one ran at load average 15-28 on 20 CPUs and the others ran at
  2-6 (design-guide rule 6).
- Captures from earlier campaigns were deleted before the runs: 727 files,
  502.6 GB of hprof, MAT index, JFR and collapsed profiles. The list is in
  the campaign directory, `previous-capture-cleanup.tsv`.
- Same-core references: the parent core without R1/R2, on the prototype
  branches with all flags off. Their harness had no JFR and had the
  residual diagnostic:
  - `termination-next-20261119/dt-owner-route/projects/{OWASP,conductor}-native-1`;
  - `acyclic-only/projects/{OWASP,conductor}-native-1`;
  - `acyclic-only/projects/Stirling-PDF-native-{1,2,long-1}`.
- Campaign data: `/drive-testcomp/opentaint-go-rules/group-a-landing-20261125/`
  (`projects/`, `projects-rerun*/`, `compare*/`, `analysis/`, `unit-tests/`,
  `rule-suite/`, `scripts/`).

## 3. Reported vulnerabilities against the baseline

The key is rule ID, sink fingerprint, full method signature and occurrence
count (`scripts/compare_bidi_projects.py`).

| Project | Baseline | New | Shared | Missing | Extra | Missing: cause |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| OWASP | 2,633 | 2,633 | 2,633 | 0 | 0 | — |
| Conductor | 7 (baseline OOM) | 7 | 7 | 0 | 0 | — |
| ThingsBoard | 15 (baseline OOM) | 0 | 0 | 15 | 0 | run-1 OOM, no accepted forward report |
| Stirling-PDF, launch 1 | 24 | 34 (32 confirmed + 2 provisional) | 16 | 8 | 18 | 8 location twins |
| Stirling-PDF, launches 2 and 3 | 24 | 32 (timeout: only confirmed) | 16 | 8 | 16 | 8 location twins |

### 3.1 Group A changed no result

| Project | Same-core native | New | Comparison |
| --- | --- | --- | --- |
| OWASP | 2,633 / 0 (complete run 11) | 2,633 / 0 | the same results; only their order differs |
| Conductor | 7 / 0 (timeout run 8) | 7 / 0 | byte-identical SARIF |
| Stirling-PDF | 32 / 2 (`native-long-1`, complete) | 32 / 2 (launch 1) | byte-identical SARIF |

The numbers are confirmed / provisional results.

### 3.2 Stirling-PDF: the 8 missing findings are location twins

All 8 findings have the same features:

- They are the `java.security.xss#sink#1` exit sink.
- The new build confirms each of them; the identity is in the
  `confirmedIds` of `native-long-1`.
- The bidirectional engine reports at the joined synthetic normal exit
  and gives no trace.
- `TraceMessageBuilder.tryResolveExitLocation` (`TraceMessageBuilder.kt:1162-1167`)
  then shows the last `return` of the method. The baseline shows the
  `return` on its trace.
- The fingerprint hashes the location, so one finding counts as
  "missing + extra".

| Method | Baseline `return` | New `return` |
| --- | --- | --- |
| `ConvertEmlToPDF#convertEmlToPdf` | L133 | L148 |
| `PipelineController#handleData` | L90 | L130 |
| `JobController#getFileMetadata` | L278 | L291 |
| `AdminSettingsController#getSettingValue` | L381 | L388 |
| `InviteLinkController#acceptInvite` | L477 | L482 |
| `InviteLinkController#generateInviteLink` | L242 | L246 |
| `InviteLinkController#validateInviteToken` | L387 | L391 |
| `UserController#inviteUsers` | L518 | L521 |

The extra findings:

- 8 are these twins.
- 10 are new `xss#sink#1` method pairs. `native-long-1` has them too:
  - `WebResponseUtils#bytesToWebResponse` and `#multiPartFileToWebResponse`;
  - `AuthController#login`;
  - `UserController#register`, `#getApiKey` and `#updateApiKey` (the
    last two are provisional);
  - `FilterController#fileSize`, `#pageCount`, `#pageRotation` and
    `#pageSize`.
- No finding failed trace generation (`generationFailed=0` on all
  projects). The bidirectional results are "simple" results without a
  code flow, so `codeFlows` and the trace hashes differ from the baseline
  on every shared finding.

### 3.3 ThingsBoard: 15 missing

The SARIF has 0 results:

```text
BIDI_RUN_END run=1 status=OOM engineTime=3m 48.245036898s
BIDI_REPORT_STATISTICS run=1 reason=ABNORMAL confirmed=0 provisional=0
```

The missing findings by rule:

| Rule | Missing |
| --- | ---: |
| unrestricted-request-mapping | 4 |
| java-jwt-decode-without-verify | 3 |
| stacktrace-printing-in-error-message | 2 |
| unvalidated-redirect#sink#0 | 2 |
| cookie-issecure-false | 1 |
| hardcoded-password | 1 |
| unsafe-reflection | 1 |
| xss#sink#1 | 1 |

The previous bidirectional cores ended the same way (§8).

## 4. Performance overview

The engine time is from `BIDI_ANALYSIS_END elapsed`. The baseline column
shows the IFDS phase in parentheses.

| Project | Build | Status | Wall s | Engine s | Peak RSS GiB | Max heap after GC MB | Run reached / completed / accepted |
| --- | --- | --- | ---: | ---: | ---: | ---: | --- |
| OWASP | baseline | OK | 156.4 | (109.3) | 8.58 | 4,987 | — |
| OWASP | native (same core) | OK | 227-231 | 150.2-153.2 | 9.23-9.31 | 6,976-7,254 | 11 / 11 / 11 |
| OWASP | **new** | OK | 197.1 | 121.0 | 9.52 | 7,097 | 11 / 11 / 11 |
| Conductor | baseline | OOM | 187.4 | (144.5) | 9.36 | 7,805 | — |
| Conductor | native | TIMEOUT | 1,126.8-1,126.9 | 1,053.7-1,053.8 | 9.49-9.63 | 8,111-8,112 | 8 / 7 / 7 |
| Conductor | **new** | TIMEOUT | 1,124.5 | 1,053.8 | 10.26 | 8,112 | 8 / 7 / 7 |
| ThingsBoard | baseline | OOM | 439.7 | (402.4) | 13.48 | 11,718 | — |
| ThingsBoard | previous bidi core (18 Nov, with statistics) | OOM | 333.8 | 179.7 | 13.79 | 11,444 | 1 / – / – |
| ThingsBoard | **new** | OOM | 384.0 | 228.2 (37.7 s heap dump) | 14.04 | 11,526 | 1 / – / – |
| Stirling-PDF | baseline | OK | 52.1 | (23.5) | 7.58 | 3,849 | — |
| Stirling-PDF | native-long (7,200 s) | OK | 2,756.0 | 2,704.2 | 9.42 | 7,314 | 11 / 11 / 11 |
| Stirling-PDF | native-1, -2 (3,000 s) | TIMEOUT | 3,034 | 2,978.7 | 9.46-9.70 | 7,337-7,347 | 11 / 10 / 9 |
| Stirling-PDF | **new**, launch 1 (load 22) | OK | 254.3 | 160.4 | 9.49 | 6,933 | 11 / 11 / 11 |
| Stirling-PDF | **new**, launch 2 | TIMEOUT | 1,123.1 | 1,058 | 10.11 | — | 9 / 8 / 7 |
| Stirling-PDF | **new**, launch 3 | TIMEOUT | 1,112.8 | 1,061 | 9.87 | — | 11 / 10 / 9 |

Verdict per project:

- **OWASP:** an improvement against the parent core. The engine takes 121.0 s
  against 150-153 s. About 17.5 s of that difference is the residual
  diagnostic in the native run-1 barrier. Runs 3-11 take 12.3 s against
  34-36 s. Against the baseline, the wall time is 40.7 s (26%) more and
  the peak RSS is 0.94 GiB more.
- **Conductor:** no change. All runs are within ±6% of native, except
  run 5 (10.1 s against 7.6 s). The H7 barrier comes at 667 s (native
  645-666 s). The baseline OOM at 187 s, but this build has no OOM: it
  times out.
- **ThingsBoard:** both builds stop with OOM in run-1. The guard fires
  190 s into run-1, after 4.69 M events. The previous core reached the
  guard after 149 s and 3.28 M events, but that run carried about 515 MB
  of statistics.
- **Stirling-PDF:** not fixed. Two of three launches stall in run 9 or
  run 11 and time out, as native does. The launch that completed ran
  under heavy external load (§9). Against the baseline (52 s), every
  launch is much slower.

## 5. Iterations

The "Demand rows out" column is the frontier demand edges after a run,
that is, the hand-off into the next run.

**OWASP** (new build; the native column is `dt-owner-route native-1`):

| Run | Dir | Limit | Engine s | Barrier s | Demand rows out | Method keys | Native engine s |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | FWD | 1 | 76.2 | 2.48 | 67,943 | 4,888 | 69.9 |
| 2 | BWD | 1 | 23.8 | 0.87 | 19,938 | 4,296 | 20.7 |
| 3 | FWD | 2 | 8.5 | 0.69 | 462 | 208 | 9.0 |
| 4 | BWD | 3 | 1.2 | 0.49 | 757 | 204 | 3.4 |
| 5 | FWD | 4 | 1.3 | 0.59 | 160 | 28 | 3.6 |
| 6-11 | | 5-10 | 0.1-0.3 each | ~0.5 each | 214 / 269 alternating | 20 | 3.2-3.6 each |

From run 7 on, the state repeats every two runs: forward runs hand off
214 rows and backward runs 269 rows, in 20 method keys. The analysis
ends at the run limit, so requirement AC is not met. Proposal §0
expected this for group A alone.

**Conductor:**

| Run | Dir | Limit | Engine s | Barrier s | Demand rows out | Method keys | Native engine s |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | FWD | 1 | 18.6 | 1.82 | 127,286 | 6,804 | 18.1 |
| 2 | BWD | 1 | 38.7 | 5.02 | 477,906 | 9,409 | 37.5 |
| 3 | FWD | 2 | 7.8 | 0.95 | 17,511 | 329 | 7.4 |
| 4 | BWD | 3 | 106.6 | 0.76 | 29,922 | 196 | 100.8 |
| 5 | FWD | 4 | 10.1 | 0.84 | 25,180 | 174 | 7.6 |
| 6 | BWD | 5 | 374.6 | 3.08 | 149,622 | 171 | 364.9 |
| 7 | FWD | 6 | 96.1 | 0.93 | 85,066 | 170 | 92.1 |
| 8 | BWD | 7 | 386.7, timeout | — | — | — | 409.2, timeout |

Two methods hold most of the late demand:
`ParametersUtils#replace(Map, DocumentContext, String)` (two contexts) and
`ParametersUtils#replaceList`. They are mutually recursive, so this is
cyclic code.

- They hold 86% of the rows that leave run 6 and 88% of the rows that
  enter run 8.
- Their rows grow with the field limit: 14.4 k in run 4 (limit 3) and
  128.6 k in run 6 (limit 5).

**Stirling-PDF** (engine seconds per run):

| Run | Dir | Launch 1 | Launch 2 | Launch 3 | Native-long | Native-1 |
| ---: | --- | ---: | ---: | ---: | ---: | ---: |
| 1 | FWD | 28.3 | 21.1 | 21.4 | 21.0 | 20.3 |
| 2 | BWD | 18.5 | 12.9 | 13.0 | 13.1 | 13.0 |
| 3 | FWD | 4.3 | 4.2 | 3.8 | 4.0 | 4.0 |
| 4 | BWD | 4.8 | 3.9 | 4.0 | 4.0 | 3.8 |
| 5 | FWD | 2.2 | 1.1 | 1.4 | 1.3 | 1.3 |
| 6 | BWD | 9.7 | 6.9 | 8.5 | 7.8 | 7.9 |
| 7 | FWD | 2.7 | 88.6 | 25.9 | 10.2 | 20.3 |
| 8 | BWD | 28.6 | 18.1 | 17.0 | 16.7 | 17.1 |
| 9 | FWD | 5.1 | 893.8, timeout | 399.4 | 156.3 | 371.1 |
| 10 | BWD | 34.7 | — | 17.1 | 16.9 | 17.1 |
| 11 | FWD | 5.8 | — | 540.3, timeout | 2,440.9 | 2,491.3, timeout |

**ThingsBoard:** run-1 (FWD, limit 1) took 228.2 s and ended with OOM. The
guard fired 190.4 s into run-1, and the heap dump took 37.7 s.

## 6. Run-1 and the transition to run-2

Run-1 work, as disjoint JFR subsystem shares:

| | OWASP | Conductor | Stirling-PDF | ThingsBoard |
| --- | ---: | ---: | ---: | ---: |
| Run-1 engine s | 76.2 | 18.6 | 28.3 | 228.2 (OOM) |
| Process cores (average) | 2.9 | 11.8 | 7.9 | 9.7 |
| Alias analysis | 22.2% | 20.3% | 38.0% | 8.0% |
| Rule resolution | 7.9% | 29.9% | 31.5% | 17.0% (61.3% in the first 15 s) |
| Call-plan forms | 16.0% | 8.3% | 8.6% | 7.5% |
| Summary store | 7.0% | 6.2% | 2.5% | 16.8% |
| FLOW subsumption | 7.7% | 4.6% | 2.8% | 3.3% |
| Inclusive `FormsCache.payload` | 47.6% | 60.7% | 78.8% | 33.2% |
| Workers blocked on the rule-cache lock | 0 s | 8.7 s | 73.1 s | 197.7 s |

- **Run-1 mostly prepares methods.** Building the call plans, which
  includes rule resolution and alias analysis, is 33-79% of the samples.
- **Run-1 repeats prescan work.**
  - The prescan already ran alias analysis and rule resolution.
  - Run-1 does both again (`JIRCallPlanBuilder.aliases`; a new resolver
    epoch for the bidirectional rule selection).
  - One method (`CompressController#createLineArtImages`) logs its 10 s
    alias overrun in both phases.
- **OWASP runs 1-2 use 1-2 of 10 workers.** `PackageUnitResolver` puts
  almost all OWASP methods in one unit, and one `UnitRunner` processes a
  unit sequentially. The bidirectional workers were parked for a total
  of 573 s in run-1.

The transition from run-1 to run-2:

| | OWASP | Conductor | Stirling-PDF (launch 1) |
| --- | ---: | ---: | ---: |
| Barrier after run-1, s | 2.48 | 1.82 | 1.41 |
| H1 rows (method keys) | 67,943 (4,888) | 127,286 (6,804) | 66,170 (1,987) |
| H1 target demand | 6,867 | 7,921 | 6,105 |
| Run-2 engine s | 23.8 | 38.7 | 18.5 |
| Heap after GC, MB: run-1 end → barrier → run-2 max | 6,380 → 6,253 → 7,097 | 6,002 → 6,292 → 7,632 | 4,795 → 4,867 → 6,102 |
| Run-2 barrier s (H2 compaction s) | 0.87 (0.16) | 5.02 (3.42) | 2.67 (1.65) |
| H2 rows | 19,938 | 477,906 | 265,845 |

- The heap does not jump at the barrier. Run-2 adds 0.8-1.3 GB at its peak.
- Conductor has the one guard event of the transition. It came at
  7.73 GB in run-2, and one full GC (1.36 s) recovered the heap.
- Run-2 work:
  - OWASP spends 52% of run-2 building call plans again. Run-1 built the
    `RUN1_GROUP` view, and run-2 needs `FULL`.
  - Each run ends with `MemoryManager.runWithMemoryManager`, whose
    `cleanup()` also empties the form cache. So runs 3 and later build
    the plans again: OWASP run-3 43.8%, Stirling-PDF runs 3-11 13-33%.
  - Conductor run-2 runs on 11 cores. It spends 27% in C5 restricted-initial
    admission and 20% in callee subscription.

## 7. Hot spots and unexpected workload patterns

### 7.1 FLOW subsumption maintenance in `FlowGroup.addAll`

`addAll` inserts the new rows. Then, after every insert, also an insert
that changes nothing, it runs `compactPacket` and `subtractSubsumed(row,
every other row)` over all `k` rows. It does this twice, and then runs a
promotion scan.

| Window | FLOW subsumption share |
| --- | ---: |
| Conductor run-7 tail | 93% |
| Conductor run-6 | 40% |
| Conductor run-8 | 36% |
| Stirling-PDF runs 8 and 10 (launch 1) | 48-56% |

- In Conductor run 8, 94.5% of the `addAll` time is in the two full
  passes, and 1.6% is in the insert.
- `compactPacket` walks each leaf path again from the root
  (`TrieNode.child` 22%, `ApManager.path` 12%).
- `SubtractKey` objects are 4.7-8.2% of the allocated bytes.

### 7.2 Loop-block replay and loop output restriction

The call chain of this work:

```text
MethodBlockRuntime.offerChild → replaySaved → applySaved/applySummary → limitFacts → onApplied
  → LoopConsumerObservation.observe / LoopOutputRestriction.restrictScalar → LoopRestrictionSession.trial
  → DemandStore.scanLocalInitials → RestrictedInitialPolicy.emitAdmissions / fitsBudget
  → MethodBlockRuntime.Entry.addCompletion → ScopedEdgeStore.addAll → FlowGroup.addAll
```

- **Conductor tails:** C5 restricted-initial admission plus loop
  restriction take 54% of run 4, 35% of run 6 and 54% of run 8.
- **Stirling-PDF stalled run 9 (launch 2):** `replaySaved` is 61%,
  `LoopOutputRestriction.restrict` 43% and `TaintGroup.addAll` 15% of the
  samples.
- **One worker runs for minutes.** In each long tail, one worker runs the
  local fixpoint of one owner and completes no event. The other workers
  are parked:

| Run | Completed events in the tail |
| --- | --- |
| Conductor run 6 | +537 events in 364 s |
| Conductor run 8 | +0 events in 367 s |
| Stirling-PDF run 8 (launch 1) | +0 events in 18.6 s |

- The query scratch of the loop blocks lives one work quantum, holds at
  most 32 entries and skips answers of more than 128 rows. The demand
  trie is frozen for the whole run.

### 7.3 Other patterns

| Pattern | Evidence | Cost |
| --- | --- | --- |
| Run-1 does the prescan work again | §6 | 5-20 s of run-1 per project |
| A lock around a rule-cache miss (`ResolverView.cached`, `@Synchronized resolveItems`) | Workers blocked: 8.7-198 s in run-1, 137-414 s in the prescans | Lower run-1 parallelism |
| The form cache is emptied at the end of each run | §6 | ~5-6 s per project in runs 3 and later |
| One package unit holds OWASP | §6 | Most of the 100 s of OWASP runs 1-2 |
| GC beside every busy thread | G1 marks continuously at 1.8-2.7 GiB/s of allocation. Conductor's old generation stays at 4.3-5.0 GB | About one core; not on the critical path |
| OWASP period-2 repetition | §5 | ~3.6 s; this is a termination question |

## 8. ThingsBoard OOM: the source of memory consumption

The guard snapshot (`projects/thingsboard/bidi/guard-live.hprof`, 18.6 GB)
holds 11.38 GB reachable in 302.8 M objects. Two earlier ThingsBoard
run-1 guards held 11.38 and 11.39 GB.

| Owner | Retained |
| --- | ---: |
| `UnitRunner` (72,108 method actors) | 3.61 GB |
| IR / project database | 3.08 GB |
| `SubscriptionManager.inputDirectory` (caller inputs, 86,283 callees) | 1.84 GB |
| Loop actors' `MethodBlockRuntime` (1,276 methods) | 1.58 GB |
| `CallerInputValues` (3.17 M slots) | 1.52 GB |
| Rule resolution cache | 0.80 GB |
| `RunManager` (72,962 callee summary storages) | 0.80 GB |
| `JIRMethodEntries` (alias state) | 0.77 GB |
| `RunMethodAnalyzer.edgeStore` | 0.76 GB |
| `PublicationIndex.targets` (1.59 M Target premises) | 0.39 GB |

The rows overlap. The run-1 engine state is 6.28 GB (55% of the heap),
and the fixed base is 5.1 GB.

- **Shape.** There are 17.07 M point memberships:
  - 91% are on the DEMAND layer, and 85% are TAINT DEMAND;
  - 66% of these have the MAY tail and 17.5% the STAR tail;
  - 0.5% are NORMAL TAINT.

  Of the 3.17 M caller-input slots, 83% are TAINT DEMAND.
- **Per-mark repetition.** The same geometry repeats once per FULL mark:
  - a caller family carries 14.7 marks, and 99.6% of caller mark pairs
    keep the same mark;
  - a diagonal point row carries 17.4 marks;
  - all 1.59 M DemandTarget premises are concrete.
- **Growth.** The live heap grows by about 1.1 KB per event: 6.5 GB at
  0.38 M events, 11.06 GB at 4.69 M events. Older 16 GB runs finished
  ThingsBoard run-1 after 7.9-9.9 M events, so this run stopped at about
  half of run-1.
- **Mechanism.**
  - Field limit 1 and `limitFacts` cut every path past one field to a
    DEMAND tree, and `run1CoverFacts` moves a fact with a field exclusion
    to DEMAND.
  - `SubscriptionManager.joinRequests` → `forEachConcreteAnswer` makes one
    callee premise per concrete mark, and `CallerInputValues.add` stores
    a slot per caller premise.
  - Each DEMAND sink hit adds a DemandTarget per concrete premise.
  - The run-1 barrier (`RunManager.prepareJoined`) reads every actor,
    local input and caller input, so all of them stay live until the
    barrier.
- **Group A did not cause it.** R1 only removes marks. The R2 signature
  (protected NORMAL TAINT) is 86 memberships. The same sources without
  R1/R2 (`472288cf3`) reach the run-1 guard with the same composition per
  event: 3.64 point memberships per event now and 3.65 before.
- **Guard cost.** At the end of run-1 the guard forces 19 full GCs
  (39.4 s), and GC pauses take 66% of the last 50 s.

## 9. Stirling-PDF: an order-dependent stall

- **The same owner as native.** The stalled run is forward, at limit 8 or
  10. The owner is `EmlProcessingUtils#decodeMimeHeader`, a method with a
  `while` loop. It holds the most demand rows: 238-240 into run 9, and
  334-336 into run 11.
- **Almost the same hand-offs.** The three launches hand off almost the
  same rows: 1,086, 1,088 and 1,088 into run 9. The difference is 1-2
  rows, all in `decodeMimeHeader`.
- **Very different costs.** Run 9 took 5.1 s (launch 1), more than 893 s
  (launch 2) and 399 s (launch 3). The native runs took 156 s and 371 s.
- **The profile of the stall.** It is the loop-block replay of §7.2:
  `replaySaved` 61%, `LoopOutputRestriction.restrict` 43%, and
  `ScopedEdgeStore`/`TaintGroup.addAll` 15%.
- **Conclusion.** The cost of the loop-block local fixpoint depends on the
  order in which offered values and saved records arrive. Group A does
  not change it. Launch 1 ran under load average 22 and took the fast
  order. The two quiet launches took the slow order, as all native
  launches did.
- **Results are stable.** The confirmed results are the same in all
  launches (32). The 2 provisional findings are published only when the
  analysis ends normally.

## 10. Optimization points

The ranked proposals, with the current and new behavior, are in
[bidirectional-next-iteration-20261125.md](../design/bidirectional-next-iteration-20261125.md):

| # | Proposal | Kind |
| ---: | --- | --- |
| P1 | One geometry with an exact mark set in run-1 (ThingsBoard OOM) | algorithmic |
| P2 | Semi-naive, order-independent loop-block replay (Stirling-PDF stall, Conductor tails) | algorithmic |
| P3 | Incremental canonicalization in `FlowGroup.addAll` | algorithmic |
| P4 | Do not repeat prescan work in run-1 | algorithmic |
| P5 | Keep the method forms across runs | algorithmic |
| P6 | Joined-exit report location (8 Stirling-PDF twins) | fix |
| P7 | Smaller work units for a single-package project (OWASP) | technical |
| P8 | No lock around a rule-cache miss | technical |

## 11. Blind spots

- **Launch counts.** OWASP, Conductor and ThingsBoard had one launch each.
  The Stirling-PDF stall is order-dependent, so one launch is not enough
  there. Three launches show two outcomes; the true frequency is not known.
- **Harness differences.** The native references used another harness
  (no JFR, with the residual diagnostic, nice 5). The new runs had JFR
  and profiler windows; these add some overhead and native memory, and
  peak RSS is 0.2-0.8 GiB higher than native.
- **No same-core ThingsBoard run.** The ThingsBoard comparison is with the
  previous core, whose run carried statistics that retained about 515 MB.
- **Owner attribution.** The bidirectional runs log no per-method
  progress lines. The owners of the Conductor and Stirling-PDF tails come
  from the frontier demand maps, not from stacks.
- **Upper bounds only.** The P2/P3 effects are share × time bounds. No
  counter measured the repeated (value, record) replays.
- **ThingsBoard event estimate.** The figure of 7.9-9.9 M events to finish
  run-1 comes from older runtimes with a 16 GB heap.
- **R2 protection.** No test isolates the protection consequence of R2
  (proposal §2). The R2 signature in the heap is small (86 memberships).
- **One unexplained heap shift.** Protected DEMAND memberships roughly
  doubled (+0.48 M, under 3% of the stored data). The pattern is not R2.

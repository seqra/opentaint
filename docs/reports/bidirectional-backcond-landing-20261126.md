# Backward condition progress landing: implementation and performance

Date: 26 November 2026. Build: `saloed/bidirectional` at `ba69bbb72`
(R1 `4af723e80` and R2 `ba69bbb72`).
Implementation proposal:
[backward-condition-progress-implementation.md](../../spec/backward-condition-progress-implementation.md).
Spec: [backward-condition-progress.md](../../spec/backward-condition-progress.md).
Parent: P3 landed (`c89881544`), measured in
[bidirectional-p3-p2m-landing-20261125.md](bidirectional-p3-p2m-landing-20261125.md).
Baseline: the legacy analyzer at `54ad708fe`, saved runs (not run again).
Next iteration: [bidirectional-next-iteration-backcond-20261126.md](../design/bidirectional-next-iteration-backcond-20261126.md).

## 0. Summary

- **Implementation.** R1 (seed layer) and R2 (capture tree) are landed as
  plain semantics, with no switch, census or counter. The module suite
  (2,807 tests), the jvm suite (474 tests) and the rule suite (786 OK,
  0 FP, 0 FN, 22 disabled) pass.
- **No result changed.** On all four projects the confirmed and
  provisional results are those of the parent. The Conductor and
  Stirling-PDF SARIF files are byte-identical to the parent. OWASP has
  the same 2,633 results and code flows.
- **False negatives against the baseline:**
  - OWASP, Conductor and Stirling-PDF: none. The 8 Stirling-PDF "missing"
    findings are the same 8 location twins as in the parent.
  - ThingsBoard: all 15 are missing. Run 1 stops with a memory-guard OOM
    at 4.33 M events, as in the parent (4.34 M). This is pre-existing (§9).
- **Performance against the parent: no change that the data can show.**

  | Project | Result | Main point |
  | --- | --- | --- |
  | OWASP | complete, run 11 | Paired control (§4.2): engine 149.9 s (new) against 149.0 s (parent), mean of 2 + 2 launches; same heap and GC |
  | Conductor | timeout in run 8, as before | Paired control (§4.2): 1,047.2 s against 1,046.3 s, same CPU per run (3,135 s), same events at the timeout |
  | ThingsBoard | OOM in run 1, as before | Same memory wall (§9) |
  | Stirling-PDF | 2 of 3 launches time out in run 9; 1 of 3 completes (parent: 0 of 3) | The stall signature holds in 21 of 21 launches; R1 and R2 do not change the hand-off rows (§10) |

  The first launches ran 15-25% slower than the parent. The cause is the
  machine: other users kept the 1-minute load at 8-22 (parent 2-8). Code
  that R1 and R2 do not touch (the setup before run 1) was 13-16% slower
  in the same launches. A paired control of the two builds on the same
  machine state removes the difference (§4.2). The only difference in
  the control: OWASP run 1 uses 30-50 s more process CPU in the C2 JIT
  threads, with the same wall time. This is inside the spread of the
  parent build (58 s).
- **Cost of R2.** At most 0.66% of the execution samples of any run
  (OWASP run 2); 0.14% or less in each Conductor run; 0 samples in the
  Stirling-PDF stall windows. Most of it is the `CaptureKey` lookup at
  each backward seed (§6).
- **Effect of R2: not shown.** R2 changes the backward seeds, but no
  result in this campaign. On the spec example PG, R1 alone also confirms
  the finding, in the same number of runs: the forward start follows the
  field-limit schedule, so the cut that the spec calls "the anchor"
  (§I.2) does not bind in this program. On the real trace of the spec,
  Stirling-PDF `AuthController#login`, the run frontiers are the same as
  without R2 in each of the 11 runs, and `login` stays in each (§6.2).
- **Hot spots** are those of the parent: the loop-output restriction and
  `replaySaved` in the long backward runs, `FlowBackedSummaries.recompact`
  in Conductor run 7, form building in run 1 and run 2 (§8).
- **Next iteration:**
  [bidirectional-next-iteration-backcond-20261126.md](../design/bidirectional-next-iteration-backcond-20261126.md).

## 1. Implementation

| Commit | Rule | Production files |
| --- | --- | --- |
| `4af723e80` | R1: a backward sink seed is NORMAL only if its literal is unary and has the `$` tail; otherwise DEMAND (spec §II.2) | `engine/RunMethodLocalServices.kt` |
| `ba69bbb72` | R2: the forward run stores a capture tree per (method, statement, rule, `[any]` literal); the next backward run seeds the tree, not the literal (spec §I.3, §II.4) | `ap/CaptureTree.kt` (new), `store/CaptureTreeStore.kt` (new), `engine/RunMethodLocalServices.kt`, `engine/BlockRunState.kt`, `engine/BlockRuntimeBinding.kt`, `engine/MethodBlockRuntime.kt`, `store/Run1OriginPredicateStore.kt`, `driver/Seeds.kt`, `driver/HandOff.kt` |

Paths are relative to
`core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/`.

R1:

- `seedFact` gets the unary flag. A predicate sink reads
  `RulePredicate.isUnary`. A legacy sink reads the sink alternatives of
  the same rule at the site, in the backward forms.
- A trigger seed (K7) uses the same flag.
- Changed test expectations: `EndFactTriggerTest` (the exact literal of
  an ND rule now seeds DEMAND, K3). Four tests (`FieldLimitScheduleAdmissionTest`,
  `MethodLocalServicesTest`, `ScheduleFuzzerTest`, `NaiveClosureTest`)
  had a legacy seed with no sink in the forms; they now register the
  sink, so the seed stays NORMAL (K1). The reference closure
  `NaiveClosure` uses the R1 layer.

R2:

- Capture at each completed combination: the sink predicate callback,
  the legacy non-conjunctive and conjunctive sinks, the unary `[any]`
  source transfer (one `checkMark` per call after a fired edge), the
  restricted multi-source `Combination` and the run-1 `ReadyCube`.
- The store keeps only `TaintTree` inputs of captured literals (`[any]`
  tail, empty exclusion, concrete non-group mark).
- The hand-off merges the stores of all analyzers. A sink tree crosses
  only with a seed of the same key. All source trees cross.
- The backward run replaces an `[any]` literal by its tree seed: sink
  seeds (K2, K4) and reversed source literals (S3, S5, with the A3
  guard). With no tree, the seed is the CURRENT literal.

Tests:

| Suite | Result | Data |
| --- | --- | --- |
| Module suite (`opentaint-dataflow`) | 2,807 tests, 0 failures | `unit/r2-dataflow/` |
| jvm suite (`opentaint-jvm-dataflow`) | 474 tests, 0 failures | `unit/r2-jvm/` |
| Rule suite, bidirectional (`docs/rule-testing.md`, fresh project) | OK 786, Skip 0, FP 0, FN 0, Disabled 22 | `rule-suite/bidi/` |
| New: `CaptureTreeTest` | 11 tests: spec vectors m1-m4, t1-t4, `star_start`, `spine_excl`, `mark_other`, `flow_none`, and a property test of the trie against the Lean `insertLeaf` copy (2,000 random cases) | |
| New: `RefinedSeedIterationTest` | 8 tests: PG at depths 1-3, t5, a seed with and without a tree, A7, the run-1 cube, the restricted combination, S3/S5 with the A3 guard | |
| New: `BackwardSeedLayerTest` | 9 tests: K1, K3, K5, S-H4, an OR, legacy unary and ND, K7 | |
| Extended: `HandOffTest` | pruning of unseeded sink trees, source trees, merge of equal keys | |

The Lean model was not changed, so it was not built again.

## 2. Configuration

- Harness: `scripts/benchmark_bidi_projects.py`. It runs the Gradle
  `runProjectAnalyzer` task directly, with the options of the parent
  campaign: `--sides bidi --heap-snapshots --profile-runs 2 4 6 8 9 11`.
  - Continuous JFR (profile settings).
  - async-profiler 30 s CPU windows: 60 s into run 1 (`normal`), 60 s into
    runs 2, 4, 6, 8, 9 and 11, and at the timeout minus 60 s
    (`near-limit`).
  - A heap snapshot when the MemoryManager guard reports OOM.
- Project parameters, as in the configuration (OWASP as in
  `.github/workflows/ci-analyzer-owasp.yaml`: 8 GiB, 1,000 s,
  `rules/ruleset`):

| Project | Heap | Analysis timeout |
| --- | --- | --- |
| OWASP | 8 GiB | 1,000 s |
| Conductor | 8 GiB | 1,080 s |
| ThingsBoard | 12 GiB | 1,080 s |
| Stirling-PDF | 8 GiB | 1,080 s |

- Launches, one at a time under the shared projects lock:

| Launch | Build | Load median (max) | Note |
| --- | --- | --- | --- |
| OWASP | `ba69bbb72` | 11.0 (13.7) | |
| Conductor | `ba69bbb72` | 8.4 (19.5) | class histograms planned in runs 1 and 3; both runs ended before +40 s |
| ThingsBoard | `ba69bbb72` | 22.3 (39.4) | |
| Stirling-PDF 1, 2, 3 | `ba69bbb72` | 14.2 (26.4), 10.4 (19.1), 12.4 (14.1) | |
| Control: OWASP ×2, Conductor ×1 | `5c5627703` (core = parent `c89881544`) | OWASP 11.7, 7.4; Conductor 8.0 | interleaved with the new build (§4.2) |
| Control: OWASP ×2, Conductor ×1 | `ba69bbb72` | OWASP 7.7, 8.0; Conductor 8.6 | OWASP new-2 has a class histogram 10 s into run 2 |

  The parent launches ran at a load median of 2.4-3.7 (ThingsBoard 8.1).
  The load includes the threads of the analyzer itself. The machine has
  20 CPUs. In this campaign other users kept the 1-minute load at 10-14
  for hours (a qemu emulator on about 4 CPUs and Java jobs on up to
  8 CPUs). A wait for a load below 5 of up to 30 minutes did not give a
  quiet machine, so the later launches waited only 5 minutes. Load per
  launch: `load.log`, `load-control.log`, `scripts/launch_load.py`.
- Heap after GC is the heap after a Young or Full pause.
- Captures of earlier campaigns were deleted before the runs: 99 files,
  46.6 GB (hprof, MAT indexes, JFR). The analysis summaries were kept.
- Campaign data: `/drive-testcomp/opentaint-go-rules/backcond-landing-20261126/`.

| Directory | Content |
| --- | --- |
| `projects/`, `projects-stirling-{2,3}/` | launches of `ba69bbb72` |
| `control/` | paired control launches (§4.2) |
| `compare*/` | comparisons with the baseline (`compare_bidi_projects.py`) |
| `analysis/perf/hotspots-transition.md` | hot spots, R2 cost, run-1 transition, contention indicators |
| `analysis/stirling/stirling.md` | Stirling-PDF stall signature, per-run times, hot spots |
| `analysis/heap/heap-thingsboard.md` | ThingsBoard heap census at the guard |
| `analysis/sarif-vs-parent.jsonl` | SARIF comparisons with the parent |
| `probe/PgProbeTest.kt` | the PG probe of §6.2 |
| `unit/`, `rule-suite/`, `scripts/` | suites and scripts |

## 3. Reported vulnerabilities

### 3.1 Against the baseline

The key is rule ID, sink fingerprint, full method signature and
occurrence count (`scripts/compare_bidi_projects.py`).

| Project | Baseline | New | Shared | Missing | Extra | Missing: cause |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| OWASP | 2,633 | 2,633 | 2,633 | 0 | 0 | — |
| Conductor | 7 | 7 | 7 | 0 | 0 | — |
| ThingsBoard | 15 | 0 | 0 | 15 | 0 | run-1 OOM (§9), pre-existing |
| Stirling-PDF, complete launch | 24 | 34 (32 confirmed + 2 provisional) | 16 | 8 | 18 | 8 location twins |
| Stirling-PDF, timeout launches | 24 | 32 (confirmed only) | 16 | 8 | 16 | 8 location twins |

The 6 missing keys (8 occurrences) and the extra keys are the same sets
as in the parent comparison (`compare/*-removed.json`,
`compare/*-added.json` against `p3p2m-landing-20261125/compare-p3/`). The
parent report §3.1-3.2 gives their cause: the same confirmed findings at
another `return` of the same method, and the `xss#sink#1` method pairs.

**False negatives:** OWASP, Conductor and Stirling-PDF have none.
ThingsBoard has 15, all from the run-1 OOM.

### 3.2 R1 and R2 changed no result

| Project | New against parent | Data |
| --- | --- | --- |
| OWASP | same 2,633 results, same code flows; the order differs | `analysis/sarif-vs-parent.jsonl` |
| Conductor | byte-identical SARIF (7 confirmed) | same |
| ThingsBoard | no report in either build (run-1 OOM) | |
| Stirling-PDF, timeout launches | byte-identical to all three parent launches (32 confirmed) | same |
| Stirling-PDF, complete launch | byte-identical to the complete group-A launch (32 confirmed + 2 provisional) | |

The 2 provisional Stirling-PDF findings are `java.security.xss#sink#1`
in `UserController` (lines 753 and 768). They are provisional in the
parent too. R2 did not make them confirmed. Their cause is not known
(next iteration, item B2).

## 4. Performance overview

### 4.1 Launches of the new build

| Project | Result | Latest run | Latest complete run | Engine s | Peak RSS GiB | Max heap after GC MB |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| OWASP | complete | 11 | 11 | 144.5 | 9.65 | 6,716 |
| Conductor | timeout | 8 | 7 | 1,046.2 | 10.19 | 8,157 |
| ThingsBoard | OOM | 1 | — | 354.0 | 13.85 | 11,225 |
| Stirling-PDF 1 | timeout | 9 | 8 | 1,058.7 | 10.09 | 6,778 |
| Stirling-PDF 2 | timeout | 9 | 8 | 1,053.6 | 9.98 | 6,686 |
| Stirling-PDF 3 | complete | 11 | 11 | 116.2 | 9.77 | 6,825 |

Parent (P3 landed, load median 2.4-3.7, ThingsBoard 8.1): OWASP complete in 125.0 s;
Conductor timeout in run 8; ThingsBoard OOM in run 1; Stirling-PDF 3 of 3
timeouts (runs 9, 9, 11).

The latest run and the latest complete run are those of the parent for
each project with the same outcome. OOM and timeout events: ThingsBoard
1 OOM (run 1); Conductor 1 timeout (run 8); Stirling-PDF 2 timeouts
(run 9).

### 4.2 Paired control: new against parent on the same machine state

The parent build in the control is `5c5627703`: the commit before R1.
Its analyzer core is the same as the parent `c89881544`. The launches
ran one after the other, in this order: OWASP parent-1, new-1, parent-2,
new-2, then Conductor parent and new (`scripts/control.sh`). OWASP new-2
took a class histogram 10 s into run 2 (§6.1), so its run-2 time is not
used. Load median per launch: OWASP 11.7, 7.7, 7.4, 8.0; Conductor 8.0
and 8.6.

OWASP (engine seconds; heap after GC from Young and Full pauses):

| Measure | Parent-1 | Parent-2 | New-1 | New-2 |
| --- | ---: | ---: | ---: | ---: |
| Engine s (complete, run 11) | 153.6 | 144.4 | 150.6 | 149.2 |
| Run 1 s | 97.3 | 88.5 | 94.6 | 95.3 |
| Run 2 s | 28.6 | 29.6 | 29.3 | (27.0, histogram) |
| Run 3 s | 11.1 | 10.2 | 10.8 | 10.3 |
| Runs 4-11 s | 5.6 | 5.4 | 4.2 | 6.4 |
| Max heap after GC in run 1, MB | 6,410 | 6,794 | 6,124 | 6,254 |
| GC pauses, count / s | 365 / 6.76 | 369 / 7.05 | 356 / 6.79 | 378 / 6.80 |
| Peak RSS GiB | 9.49 | 9.70 | 9.66 | 9.68 |
| Process CPU s before run 1 | 180.1 | 184.5 | 188.0 | 180.9 |
| Process CPU s in run 1 | 231.7 | 203.9 | 263.6 | 257.2 |
| of it, Java analyzer and other threads | 114 | 100 | 109 | 109 |
| of it, C2 JIT threads | 86 | 144 | 142 | 191 |
| Results | 2,633 | 2,633 | 2,633 | 2,633 |

- The engine time is the same: mean 149.9 s (new) against 149.0 s
  (parent). The spread inside one build is 9.2 s.
- Run 1 uses 30-50 s more process CPU in the new build, in both pairs.
  The analyzer threads use the same CPU (100-114 s). The difference is in
  the C2 JIT compiler threads, and their CPU changes by 58 s between two
  launches of the parent build. The split comes from the JFR
  `jdk.ThreadCPULoad` events (one 10 s period per event); it does not
  include the GC threads. A possible cause is that R2 adds code to hot
  methods (larger compile units). It does not change the wall time.
- All four launches give the same 2,633 results and code flows.

Conductor (engine seconds; process CPU seconds):

| Run | Parent s | New s | Parent CPU | New CPU | Hand-off rows after the run, parent / new |
| ---: | ---: | ---: | ---: | ---: | --- |
| 1 | 24.2 | 23.4 | 256.0 | 258.8 | 478,128 / 478,177 |
| 2 | 50.6 | 47.8 | 511.3 | 488.9 | 17,507 / 17,454 |
| 3 | 9.8 | 9.4 | 63.8 | 59.5 | 29,960 / 29,937 |
| 4 | 121.8 | 119.2 | 290.6 | 281.8 | 25,155 / 25,123 |
| 5 | 10.5 | 11.1 | 48.9 | 47.8 | 149,903 / 149,517 |
| 6 | 396.4 | 398.1 | 996.8 | 1,014.9 | 86,781 / 85,215 |
| 7 | 71.8 | 72.2 | 185.8 | 185.1 | — |
| 8 | 343.8 T | 347.7 T | 781.6 | 799.1 | — |
| Total | 1,046.3 | 1,047.2 | 3,135.4 | 3,135.1 | |

- Both launches time out in run 8, at 15,634 (parent) and 15,677 (new)
  events. The first new launch (load 8.4) reached 15,265.
- GC: 2,013 pauses, 22.32 s, max heap after GC 8,173 MB (parent) against
  2,063 pauses, 22.44 s, 8,115 MB (new). Peak RSS 10.01 and 10.09 GiB.
- The hand-off rows differ by 0.0-1.8%. Two launches of the parent build
  differ by the same amount (run 2: 477,786 in the P3 landing against
  478,128 here).
- Both SARIF files are byte-identical to the P3-landed parent.

**Result.** On the same machine state, R1 and R2 change neither the time
nor the memory of OWASP and Conductor. The only measured difference is
more C2 JIT CPU in OWASP run 1, inside the spread of the parent build.

### 4.3 Contention, not work

Data: `analysis/perf/hotspots-transition.md` §4.

- Before run 1, both builds run the same code. In OWASP and Conductor this
  phase took 13-16% more CPU and 17-18% more wall than in the parent
  launches. The load was 12.3 against 3.0-5.4.
- In Conductor run 1 the CPU is the same (257 s against 262 s), but on
  9.8 cores against 12.1. The wall grew 21%.
- In Conductor runs 4-7 (one analyzer thread) the GC pause count, the
  heap and the profile shares match the parent. The CPU is 24-29% higher.
- The hand-off compaction handles the same rows (0-3% difference) but
  takes 4-46% longer per row.
- ThingsBoard run 1 used 16% more CPU, but its setup phase used 1% more.
  Most of the wall difference (84 s of 105 s) is the GC-bound end phase
  after 4.0 M events (GC pauses in run 1: 78.4 s against 59.5 s). In the
  new launch the Java threads used 1,360 s of the 2,597 s of run-1 CPU;
  the rest is GC and VM threads. The parent recording was deleted in the
  cleanup, so the split cannot be compared. No R2 frame explains the
  difference (0.003% of samples). ThingsBoard has no paired control: one
  launch takes 25 minutes and ends in the same OOM.
- In the paired control (§4.2) these differences go away for OWASP and
  Conductor.

## 5. Iterations

Engine seconds per run, new launch / parent launch (P3 landed).

| Run | Dir | OWASP | Conductor | Stirling-PDF 1 | Stirling-PDF 2 | Stirling-PDF 3 (complete) |
| ---: | --- | --- | --- | --- | --- | --- |
| 1 | F | 90.8 / 80.8 | 24.2 / 20.0 | 26.2 / 21.4 | 24.3 / 21.4 | 25.2 / 28.3 (group A) |
| 2 | B | 29.0 / 23.7 | 48.0 / 39.7 | 17.1 / 13.2 | 16.9 / 13.8 | 16.4 / 18.5 |
| 3 | F | 9.8 / 8.6 | 9.4 / 7.6 | 5.1 / 4.0 | 5.1 / 4.3 | 5.9 / 4.3 |
| 4 | B | 1.3 / 1.2 | 122.5 / 102.8 | 4.7 / 3.4 | 4.1 / 3.3 | 4.2 / 4.8 |
| 5 | F | 1.1 / 1.0 | 10.5 / 9.3 | 1.6 / 1.1 | 1.7 / 1.4 | 1.7 / 2.2 |
| 6 | B | 0.2 / 0.1 | 408.4 / 338.2 | 6.8 / 5.9 | 8.0 / 6.8 | 10.1 / 9.7 |
| 7 | F | 0.4 / 0.2 | 75.0 / 61.2 | 99.0 / 82.6 | 125.9 / 107.6 | 2.3 / 2.7 |
| 8 | B | 0.2 / 0.1 | 330.3 T / 459.7 T | 20.2 / 13.5 | 20.5 / 15.4 | 15.8 / 28.6 |
| 9 | F | 0.2 / 0.3 | — | 867.0 T / 909.2 T | 836.9 T / 879.0 T | 3.0 / 5.1 |
| 10 | B | 0.1 / 0.0 | — | — | — | 15.3 / 34.7 |
| 11 | F | 0.3 / 0.2 | — | — | — | 3.4 / 5.8 |

T = timeout. The Stirling-PDF 3 parent column is the complete group-A
launch (`group-a-landing-20261125/projects/Stirling-PDF`), because no
P3-landed launch completed. These are single launches under different
loads; §4.2 gives the paired comparison.

## 6. R2: cost and effect

### 6.1 Cost

Data: `analysis/perf/hotspots-transition.md` §2 (JFR execution samples of
`continuous.jfr`); `analysis/stirling/stirling.md` §4.

| Project | Run | R2 share of analyzer samples | Frames |
| --- | --- | ---: | --- |
| OWASP | 1 (F) | 0.03% | `checkMark` in the source transfer |
| OWASP | 2 (B) | 0.66% (4 of 603) | `SeedIndex.sinkTree` → `CaptureKey` hash, `refinedSeed` |
| OWASP | 3 (F) | 0.30% (1 of 333) | `CaptureTreeStore` |
| Conductor | 1-8 | 0.00-0.14% | mostly `SeedIndex.sinkTree` |
| ThingsBoard | 1 (F) | 0.003% | |
| Stirling-PDF | stall windows | 0 samples | |
| Stirling-PDF | whole launch | 0.1-0.4% | mostly run 2 |

- The forward capture (`captureInput`, `insertCaptureLeaf`) has about one
  sample per project. The hand-off merge has 0-2 samples per barrier.
- The heap of the capture stores at the ThingsBoard guard: 8.9 MB, 0.08%
  of the heap (§9).
- OWASP control new-2, class histogram 10 s into run 2: 10,630
  `CaptureKey` objects (0.34 MB shallow) and 2 `SeedIndex` objects. The
  trees use the shared `TaintTree` and trie classes, so their size is not
  separate in a histogram. The heap after GC in run 2 is the same as in
  the parent (§4.2).

### 6.2 Effect

R2 changes the seeds of `[any]` literals. In this campaign it changes no
result (§3.2) and no hand-off row set after run 2 in Stirling-PDF
(`analysis/stirling/stirling.md` §2).

The spec example PG (§I.2) was checked end to end
(`RefinedSeedIterationTest`, `probe/PgProbeTest.kt`). `main` taints
`v.f1…fd`, `use(x)` has the unary sink `x.[any](T)`.

| Build | Backward seeds at `sink(x)` | Finding | Last run |
| --- | --- | --- | --- |
| R1 + R2 | run 2k seeds `x.f1…f(k-1).[any](T)`: one field deeper per round | confirmed | 2d+1 |
| R1 alone | `x.[any](T)` in each round | confirmed | 2d+1 |

- Run 1 starts `use` with the abstract `x.*` (depth 0). So the run-1
  capture tree has only the root leaf, and the first refined seed comes
  in run 4, not in run 2 as the spec table shows.
- In both builds the forward start in `use` follows the field-limit
  schedule: run 3 starts at `x.f.*`, run 5 at `x.f.g.*`. The forward
  facts at the sink are the same in both builds.
- So the cut that the spec calls the anchor ("C2 cut at depth 1" under the
  demand `x.[any]`, §I.2) does not bind in PG. R1 alone already
  converges. The spec row "CURRENT: provisional in each round" does not
  hold for this program.

This does not show that R2 has no effect anywhere. It shows that the
example of the spec does not need R2.

The real trace of the spec (§II.1) is Stirling-PDF
`AuthController#login`. The gate expected its demand rows to reach zero.
They do not:

| Run | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Frontier methods, new (complete launch) | 4,219 | 8,381 | 4,135 | 532 | 217 | 185 | 157 | 125 | 124 | 120 | 108 |
| `login` premises in the frontier, new | 2 | 2 | 2 | 2 | 2 | 1 | 2 | 1 | 2 | 1 | 2 |
| Frontier methods, group A (complete launch) | 4,219 | 8,381 | 4,135 | 532 | 217 | 185 | 157 | 125 | 124 | 120 | 108 |
| `login` premises in the frontier, group A | 2 | 2 | 2 | 2 | 2 | 1 | 2 | 1 | 2 | 1 | 2 |

Source: the "Run n frontier: analysed" lines of `analyzer.log`. Both
complete launches stop at the run limit (11), and `login` is analysed in
each run. The frontier is the same in each run. So R2 does not change the
work of the case that it was designed for. The next iteration finds the
cause (item B1).

## 7. Run 1 and the transition to run 2

Data: `analysis/perf/hotspots-transition.md` §3.

| Measure | OWASP new / parent | Conductor new / parent | ThingsBoard new / parent |
| --- | ---: | ---: | ---: |
| Run-1 engine s | 90.8 / 80.8 | 24.2 / 20.0 | 354.0 / 248.7 (OOM) |
| Run-1 process CPU s | 229.5 / 226.2 | 257.2 / 262.0 | 2,596.9 / 2,239.5 |
| Barrier 1 s | 3.46 / 2.34 | 2.48 / 1.81 | — |
| Hand-off compaction after run 1: s / rows | 0.20 / 18,971 vs 0.20 / 19,938 | 4.10 / 478,014 vs 3.36 / 477,786 | — |
| Run-2 engine s | 29.0 / 23.7 | 48.0 / 39.7 | — |
| Heap after GC at the end of run 1, MB | 6,172 / 6,072 | 6,022 / 6,064 | 11,062 / 11,063 |
| Heap after GC, last in run 2, MB | 4,025 / 4,015 | 7,280 / 7,275 | — |
| GC pauses run 1: count / s | 137 / 3.0 vs 142 / 2.7 | 48 / 1.7 vs 49 / 1.5 | 1,067 / 78.4 vs 941 / 59.5 |
| GC pauses run 2: count / s | 22 / 0.9 vs 25 / 1.0 | 291 / 7.2 vs 301 / 5.8 | — |
| Peak RSS GiB | 9.65 / 9.53 | 10.19 / 9.95 | 13.85 / 13.80 |

- The heap at the transition is that of the parent within 100 MB.
- Conductor backward run 2 is the memory peak of the launch: the max heap
  after GC is 8,157 MB of the 8,192 MB heap, with 317 GC pauses in 48 s.
  The parent control has the same peak (8,173 MB in run 2). No heap census
  of run 2 exists (next iteration, M1).
- The barrier and the compaction take more time on the same rows; §4.3
  explains it by the machine.
- Run 1 is the largest share of OWASP (63% of the engine time) and of
  ThingsBoard (the only run). Form building (`FormsCache.payload` →
  `JIRCallPlanBuilder.build`) takes 44-49% of run 1 and 57% of OWASP
  run 2 (§8).

## 8. Hot spots

Data: `analysis/perf/hotspots-transition.md` §1 and §5;
`analysis/stirling/stirling.md` §4. Shares are inclusive, of the analyzer
samples.

| Where | Frame | Share | Change against the parent |
| --- | --- | ---: | --- |
| Conductor runs 6, 8, near the limit | `MethodBlockRuntime.replaySaved` | 89-99% | none (< 5 points) |
| same | `LoopOutputRestriction.restrict` | 61-85% | none |
| same | `LoopRestrictionSession.trial` | 30-48% | none |
| Conductor run 7 | `FlowBackedSummaries.recompact` → `FlowGroup.addAll` | 47% / 58% | none |
| Every backward run | `RestrictedInitialPolicy.fitsBudget` (own time) | 5-6% | none; the top own-time frame |
| Stirling-PDF run 9 (stall) | `replaySaved` / `restrict` / `TaintGroup.addAll` | 99-100% / 54-74% / 21-41% | restriction and TAINT trade 5-12 points; their sum stays at 94-95% |
| OWASP runs 1-2, ThingsBoard run 1 | `FormsCache.payload` → `JIRCallPlanBuilder.build` | 44-57% | window phases differ; no parent value for the whole run |
| ThingsBoard run 1 | `TaintRulesStorage.configForMethod` | 24% | linear scan with `AnnotationConstraint.equals` |
| OWASP and ThingsBoard run 1 | `ConclusionsKt.run1CoverFacts` | 15-16% | |

No frame is new, except three small frames in Conductor run 4
(0.6-1.1%, for example `DemandStore.prepareLocalDataPlan`). None of them
is an R2 frame.

Forms: `FormsCache` keeps each payload behind a soft reference in the
per-method interpreter entry. The MemoryManager clears soft references
near the guard ("Cleaned soft refs: 343" in ThingsBoard), so forms can be
built again. Run 2 also builds the reversed forms. The share of rebuilds
is not measured.

## 9. ThingsBoard OOM: the source of memory consumption

Data: `analysis/heap/heap-thingsboard.md` (MAT on `guard-live.hprof`,
the dump at the memory guard; the method and the census queries of the
parent, plus one query for the capture stores).

**Same wall at the same events.** The dump came at 4.329 M events with
11,062 MiB live after GC (parent 4.333 M, 11,063 MiB). From 3.8 M events
to the dump, the live heap of the two builds at the same event count
differs by 70 MiB or less. Growth: 1,267 B per event (parent 1,279 B).

| Owner (retained, disjoint) | New GB | Parent GB |
| --- | ---: | ---: |
| Reachable heap | 11.37 | 11.39 |
| Engine state | 6.270 | 6.288 |
| — actors | 3.642 | 3.546 |
| — caller subscriptions | 1.798 | 1.829 |
| — callee storages | 0.807 | 0.836 |
| IR | 3.08 | 3.08 |
| Rules cache | 0.81 | 0.81 |
| Interpreter entries (`JIRMethodEntries`) | 0.77 | 0.77 |

- No structure differs by more than 2% of the engine state (125 MB).
  The actors gain 96 MB because two loop runtimes (47.7 MB) fall under
  their actors in the dominator tree of this dump; this is attribution,
  not more data.
- Stored data: 16.53 M point and completion memberships (parent 16.79 M),
  at 379 B of engine state each (parent 374 B).

**R2.** 72,126 `CaptureTreeStore` objects, one per forward analyzer;
286 hold keys. They hold 1,385 keys (1,380 sources, 5 sinks) and retain
8.9 MB: 0.08% of the heap. 97% of it is the empty store and its two empty
maps (120 B per analyzer). The keys and trees are 0.25 MB; most entries
point to one shared `[any]` leaf, and the stores own only 62 trie nodes.
All captured literals are `[any]` on the base, with the xss mark (988
entries) or the path-traversal mark (397). Sources: `ResponseEntity`
constructors (594) and `toString` calls (786). Sinks: `Files.readAllBytes`
and `FileUtils.deleteDirectory`.

**Source of the memory consumption.** The cause of the parent holds: run 1
keeps the working state of finished work until the barrier, and the
barrier drops it without reading it.

| Category at the guard | New GB | Parent GB | Share of engine state | Proposal |
| --- | ---: | ---: | ---: | --- |
| Working state: point edges 0.99, point resumes 0.24, local services 0.25, worklists and queues 0.23 | 1.70 | 1.64 | 27.1% | N1 |
| Caller inputs | 1.80 | 1.83 | 28.7% | N1 |
| Publication indexes (dropped unread at the barrier) | 0.73 | 0.76 | 11.6% | N1 |
| Exports that the barrier reads: summaries, Target rows, capture trees | 0.58 | 0.58 | 9.2% | keep |
| Loop runtimes (1,276 loop actors: 1.8% of the actors, 43.5% of the actor bytes) | 1.59 | 1.59 | 25.3% | N5 |
| All engine-owned collection structures | 3.94 | 3.99 | 62.9% | N6 |

The categories overlap (a loop runtime holds working state too). The
capture trees are a new export that the hand-off reads, so N1 must keep
them with the summaries.

**Time.** The dump came 279 s into run 1 (parent 220 s). The mean
1-minute load in run 1 was 27 (parent 17), and the process used 14% more
CPU. Capture code is 0.003% of the CPU samples and 0.004% of the
allocation samples. The extra time is contention, not R2.

## 10. Stirling-PDF stall

Data: `analysis/stirling/stirling.md`.

- **Signature.** The stall owner `EmlProcessingUtils#decodeMimeHeader`
  gets extra hand-off rows after run 6 in each slow launch and none in
  each fast launch. New launches: +3, +3 and 0. Tally: 21 of 21 launches
  (6 fast, 15 slow). Each +3 launch times out in run 9 (7 of 7); each +1
  launch times out in run 11 (8 of 8).
- **R1 and R2 do not change the hand-off.** From run 3 on, slow launch 1
  has the same rows per method key as parent launch 1, and slow launch 2
  as parent launch 2. Only run 2 differs a little; two parent launches
  differ in the same way.
- **The stall.** It starts in run 7 (99.0 s and 125.9 s, against 2.3 s in
  the fast launch). In run 9 the event count stays flat for 820-850 s
  with 11-12 events in flight. One thread does the work.
- **Not explained.** Backward run 8 takes 20.2-20.5 s against 13.5-15.3 s,
  with 28-33% more CPU, the same events and GC, and no R2 sample.
- **The fast launch** (116.2 s against 160.4 s for the complete group-A
  launch): runs 8 and 10 give 32.2 s of the 44.2 s difference. P3 made
  these runs faster before this build. n = 1; no speedup is claimed.

## 11. Optimization points per project

| Project | Run-1 time | Run 1 → run 2 | Code hot spots | Memory |
| --- | --- | --- | --- | --- |
| OWASP | 63% of the engine time; form building 49% of run 1 | form building 57% of run 2 | `run1CoverFacts` 16%, `IntDisjointSets.allElements` 7% (own time) | heap 6.2 GB of 8 GB at the end of run 1 |
| Conductor | 24 s; not the limit | compaction 4.1 s for 478 k rows | `replaySaved` + restriction in runs 4, 6, 8; `recompact` in run 7 | max heap after GC 8,157 MB of 8,192 MB, in backward run 2 |
| ThingsBoard | the only run; OOM at 4.33 M events | — | form building 44%, `configForMethod` 24% | engine state 6.27 GB of 11.37 GB; working state of finished work 1.70 GB and caller inputs 1.80 GB, dropped unread at the barrier; loop runtimes 1.59 GB |
| Stirling-PDF | 21-26 s | — | stall: restriction + TAINT canonicalization on one thread | — |

The proposals are in
[bidirectional-next-iteration-backcond-20261126.md](../design/bidirectional-next-iteration-backcond-20261126.md).

## 12. Blind spots

- The new launches ran on a shared machine at 2-4 times the parent load.
  Single launches of the two builds are not comparable in time. Only the
  paired control (§4.2) compares time, and only for OWASP and Conductor.
  ThingsBoard and Stirling-PDF have no paired control.
- One heap dump per build for ThingsBoard: a difference below about 7%
  can come from the launch. The run-2 copy of the capture trees is not in
  the dump (run 2 did not start).
- No capture-tree census: the landed code has no counter, so the number
  of refined seeds per run is not measured. The class histogram of §6.1
  gives only a size at one moment.
- The PG result (§6.2) is for one program shape. A program where the
  anchor binds is not known yet.
- Stirling-PDF has n = 3. The outcome depends on the order of work (§10).

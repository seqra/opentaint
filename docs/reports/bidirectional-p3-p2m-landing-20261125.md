# P3 and P2' landing: implementation and performance

Date: 25-26 November 2026. Build: `saloed/bidirectional` at `c89881544`:
P3 is landed; P2' was landed and then reverted.
Implementation proposal:
[next-iteration-p3-p2m-implementation.md](../../spec/next-iteration-p3-p2m-implementation.md).
Parent: the group A build (`4bedb350b`; its core is `5804e44dd`), measured in
[bidirectional-group-a-landing-20261125.md](bidirectional-group-a-landing-20261125.md).
Baseline: the legacy analyzer at `54ad708fe`, saved runs (not run again).
Next iteration: [bidirectional-next-iteration-20261126.md](../design/bidirectional-next-iteration-20261126.md).

Two builds were measured:

| Name | Commit | Content |
| --- | --- | --- |
| P3 + P2' | `ad7b06320` | P3 (`0919c7500`) and P2' |
| P3 alone (landed) | `c89881544` | P2' reverted; the core is identical to `0919c7500` |

## 0. Summary

- **Implementation.** P3 (`0919c7500`) and P2' (`ad7b06320`) were
  implemented as plain semantics, with no switch, census or counter. All
  suites passed for both commits; the rule suite has 786 OK, 0 FP, 0 FN
  and 0 skipped cases.
- **P2' was reverted** (`c89881544`) by the memory clause of the proposal
  gate (§6). It kept all results and saved 84 s of Conductor runs 1-7
  (run 4 -49%), but its memo held about 0.9 KB of live heap per entry:
  +0.8-1.4 GB of heap after GC in Conductor runs 6-8 and in the
  Stirling-PDF stall runs, and Conductor GC pauses of 34.5 s against
  20.3 s. The landed state is P3 alone.
- **No result changed.** Both builds give the confirmed and provisional
  results of the parent on all four projects. The Conductor, ThingsBoard
  and Stirling-PDF SARIF files are byte-identical; OWASP has the same
  results and code flows in another order.
- **False negatives against the baseline:**
  - OWASP, Conductor and Stirling-PDF: none. The 8 Stirling-PDF "missing"
    findings are the same findings at another `return` of the same method.
  - ThingsBoard: all 15 are missing, because run 1 ends with a
    memory-guard OOM (pre-existing, §9).
- **Performance of the landed state (P3 alone) against the parent:**

  | Project | Result | Main change |
  | --- | --- | --- |
  | OWASP | complete, 125.0 s engine (parent 121.0 s) | none: runs 2-11 35.4 s against 36.1 s; run 1 +4.5 s is launch noise |
  | Conductor | timeout in run 8, as before | runs 1-7 -11% (578.7 s against 652.4 s): run 6 -10%, run 7 -36%. GC and heap unchanged |
  | ThingsBoard | OOM in run 1, as before | none; P3 does not change the run-1 heap |
  | Stirling-PDF | 3 of 3 launches time out (parent: 2 of 3) | backward runs 8 and 10 -10% to -28%; GC and heap unchanged |

- **Stirling-PDF stall.** The order of work decides each launch. The
  stall owner `EmlProcessingUtils#decodeMimeHeader` gets 1-3 extra
  hand-off rows after run 6 in each slow launch and none in each fast
  launch (18 of 18 launches). With P3 active, 1 of 9 launches was fast;
  without it, 4 of 9 (not significant, p = 0.15). P3 gives the native rows
  for each call sequence, so only the timing can make this difference
  (§10.1).
- **Hot spots:**
  - Conductor runs 4-8: the loop-output restriction (59-84% of the analyzer
    samples), its trials and the demand-view scan. P3 cut
    `FlowGroup.addAll` in run 8 from 22% to 8%.
  - Conductor run 7: `FlowBackedSummaries.recompact` adds every row
    again, and each row is canonicalized from the root (§8.2).
  - Stirling-PDF stall: the restriction and the TAINT canonicalization
    (`TaintGroup.addAll` 21-52%), on one thread.
  - Run 1 of every project: alias analysis and rule resolution, which the
    prescan already did.
- **Memory (ThingsBoard).** Run 1 keeps the working state of all finished
  work until the run-1 barrier, but the barrier does not read most of it:
  point edges, resumes, local services and publication indexes (2.2 GB)
  and most caller inputs (1.83 GB). Collection structures are 63% of the
  6.29 GB engine state (§9).
- **Next iteration:**
  [bidirectional-next-iteration-20261126.md](../design/bidirectional-next-iteration-20261126.md).
  N1 releases the working state of complete subgoals in run 1, N2 makes
  TAINT canonicalization incremental, N3 makes the stored rows independent
  of the arrival order, and N4 brings the restriction memo back with a
  bounded footprint.

## 1. Implementation

| Commit | Rule | Production files |
| --- | --- | --- |
| `0919c7500` | P3: incremental canonicalization in `FlowGroup.addAll`. An insert that keeps the same row objects returns at once. A clean row is subtracted only by the changed rows. The final pass is deleted. A call that throws restores its list | `ap/Groups.kt` |
| `ad7b06320` | P2': per-run memo of the loop-output restriction. Key = (parent scope, loop, exit, original, value). Only calls that do not bypass use it. Soft through `ap.softRefs`; at most 1,000,000 entries per method runtime, clear-all when full; `freezeChildren` clears it | `engine/LoopRestrictionMemo.kt` (new), `engine/MethodBlockRuntime.kt`, `engine/LoopOutputRestriction.kt` (`bypasses`) |
| `c89881544` | Revert of `ad7b06320` (§6) | the same files |

The code follows the proposal snippets (§3.3, §4.3). It has no switch, no
census and no counter. The proof modules were committed with the proposal
(`ccc3ae812`): `FlowGroupIncrementalImpl.lean` and `RestrictionMemoImpl.lean`.
They stay in the tree: the P2' proofs are valid for the next memo (N4 of
the next proposal).

**Tests.**

| Test | Content |
| --- | --- |
| `NativeFlowGroupReference` (new, test tree only) | The native `FlowGroup` of `29c78d5c3`, with `isFixpoint` and test-only counts of MUST merges and promotions |
| `FlowGroupIncrementalTest` (new, 4 tests) | 3,000 random insertion sequences: delta and rows equal to the reference after each call, invariant F after each call, coverage (more than 10,000 calls, 1,000 empty and 1,000 non-empty deltas, at least one MUST merge and one promotion). Directed MUST-merge and promotion sequences. A cancelled call keeps the stored row objects |
| `LoopRestrictionMemoTest` (5 tests; reverted with P2') | Hit; a change of each key part; the cap; the memory guard; `clear` |
| `LoopOutputRestrictionTest` (1 test; reverted with P2') | `bypasses` agrees with the bypass statistic of `restrict` |

A mutation check: when a clean row is not subtracted by the changed rows,
two `FlowGroupIncrementalTest` tests fail (the random sequences and the
directed promotion).

**Gates.**

| Check | Result |
| --- | --- |
| Module suite | 2,778 tests after P3, 2,784 after P2'; 0 failed. The revert gives the P3 tree again (`git diff 0919c7500 c89881544 -- core` is empty) |
| Jvm suite | 474 tests after each commit; 0 failed |
| Lean (`lake build && lake env lean audit.lean`) | 46,038 ApSpec declarations, 0 unexpected axioms |
| Rule suite, bidirectional (`docs/rule-testing.md`, fresh portable project) | P3 + P2' and P3 alone: OK 786, Skip 0, FP 0, FN 0, Disabled 22 |

The default-engine rule suite was not run: P3 and P2' change only the
`bidi` package.

The last completed run of the 585 Java rule analyses is the same in both
builds and in the parent: run 1 `NO_DEMAND_EDGE` 468, run 3 110, run 5 3,
run 7 2, run 9 1, run 11 `RUN_LIMIT` 1.

## 2. Configuration

- Harness: `scripts/benchmark_bidi_projects.py`. It runs the Gradle
  `runProjectAnalyzer` task directly, with the same options as the parent
  campaign: `--sides bidi --heap-snapshots --profile-runs 2 4 6 8 9 11`.
  - Continuous JFR (profile settings).
  - async-profiler 30 s CPU windows: 60 s into run 1 (`normal`), 60 s into
    runs 2, 4, 6, 8, 9 and 11, and at the timeout minus 60 s.
  - A heap snapshot when the MemoryManager guard reports OOM.
  - P3 + P2', Conductor only: `jcmd GC.class_histogram -all` (no forced
    GC) 40 s into run 4 and 150 s into runs 6 and 8, for the memo heap
    (proposal §6.2).
- Project parameters, as in the configuration:

| Project | Model | Heap | Analysis timeout |
| --- | --- | --- | --- |
| OWASP | `owasp-ci-investigation/project/project.yaml` (as `ci-analyzer-owasp.yaml`) | 8 GiB | 1,000 s |
| Conductor | `opentaint-test-conductor/opentaint-project` | 8 GiB | 1,080 s |
| ThingsBoard | `opentaint-test-thingsboard/opentaint-project` | 12 GiB | 1,080 s |
| Stirling-PDF | `e2e-root/model-Stirling-PDF` | 8 GiB | 1,080 s |

- Launches, one at a time under the shared projects lock:

| Build | OWASP | Conductor | ThingsBoard | Stirling-PDF |
| --- | --- | --- | --- | --- |
| P3 + P2' | 2 (launch 1 under load, median 9.1; rerun at 3.9) | 2 (launch 1 under load, median 7.6; rerun at 4.8, with histograms) | 1 (load median 18.3) | 3 (load medians 5.3 / 8.4 / 3.4) |
| P3 alone | 1 (load median 3.2) | 1 (load median 3.7) | not launched: it ends in run 1, where P2' never acts, so its run is the P3 + P2' launch | 3 (load medians 3.0 / 2.9 / 2.4) |

  The tables use the quiet launches. Each P3-alone launch waited for a
  1-minute load below 5 on 20 CPUs. Load per launch: `load*.log`,
  `scripts/launch_load.py`.
- **Heap after GC** in this report is the heap after a Young or Full
  pause. G1 Remark and Cleanup pauses free no memory: their "after"
  value includes the allocation since the last young pause. The first
  draft of the P2' analysis and the revert commit message counted them,
  which gave a higher launch maximum for Stirling-PDF (7,272-7,305 MB).
  The conclusion of §6 does not change with the correct measure.
- Captures from earlier campaigns were deleted before the runs: 750 files,
  29.8 GB (hprof, JFR, collapsed profiles, MAT indexes). The list is in
  `previous-capture-cleanup.tsv`. The profile shares of the parent windows
  were saved first (`analysis/parent-profile-shares.tsv`).
- Campaign data: `/drive-testcomp/opentaint-go-rules/p3p2m-landing-20261125/`.

| Directory | Content |
| --- | --- |
| `projects/`, `projects-rerun/`, `projects-stirling-{2,3}/` | P3 + P2' launches |
| `projects-p3/`, `projects-p3-stirling-{2,3}/` | P3-alone launches |
| `compare*/` | comparisons with the baseline (`compare_bidi_projects.py`) |
| `analysis/performance.md` | P3 + P2' performance analysis (per run, GC, profiles, memo heap) |
| `analysis/stall.md` | Stirling-PDF stall and Conductor tail analysis |
| `analysis/heap-thingsboard.md` | ThingsBoard heap census at the guard |
| `analysis/sarif-vs-parent.jsonl`, `analysis/sarif-p3-vs-parent.jsonl` | SARIF comparisons with the parent |
| `unit/`, `rule-suite/`, `rule-suite-p3/`, `scripts/` | suites and scripts |

## 3. Reported vulnerabilities

### 3.1 Against the baseline

The key is rule ID, sink fingerprint, full method signature and occurrence
count (`scripts/compare_bidi_projects.py`). Both builds give the same
numbers.

| Project | Baseline | New | Shared | Missing | Extra | Missing: cause |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| OWASP | 2,633 | 2,633 | 2,633 | 0 | 0 | — |
| Conductor | 7 (baseline OOM) | 7 | 7 | 0 | 0 | — |
| ThingsBoard | 15 (baseline OOM) | 0 | 0 | 15 | 0 | run-1 OOM, no accepted forward report (§9) |
| Stirling-PDF, complete launch | 24 | 34 (32 confirmed + 2 provisional) | 16 | 8 | 18 | 8 location twins |
| Stirling-PDF, timeout launches | 24 | 32 (only confirmed) | 16 | 8 | 16 | 8 location twins |

The 8 Stirling-PDF "missing" findings are the same confirmed findings,
shown at another `return` of the same method (joined synthetic exit,
parent report §3.2). The 10 other extra findings are the `xss#sink#1`
method pairs of the parent report §3.2.

**False negatives:** OWASP, Conductor and Stirling-PDF have none.
ThingsBoard has 15, all from the run-1 OOM, which is pre-existing (§9).

### 3.2 P3 and P2' changed no result

| Project | Parent (same end) | P3 + P2' | P3 alone | Comparison |
| --- | --- | --- | --- | --- |
| OWASP | 2,633 / 0 (complete run 11) | 2,633 / 0, both launches | 2,633 / 0 | the same results and code flows; only their order differs |
| Conductor | 7 / 0 (timeout run 8) | 7 / 0, both launches | 7 / 0 | byte-identical SARIF (both builds) |
| ThingsBoard | 0 (OOM run 1) | 0 | (not launched) | byte-identical SARIF |
| Stirling-PDF, complete | 32 / 2 (parent launch 1) | 32 / 2 (launch 2) | no launch completed | byte-identical SARIF |
| Stirling-PDF, timeout | 32 / 0 (parent launch 2) | 32 / 0 (launches 1 and 3) | 32 / 0 (3 launches) | byte-identical SARIF |

The numbers are confirmed / provisional results. Comparison data:
`analysis/sarif-vs-parent.jsonl`, `analysis/sarif-p3-vs-parent.jsonl`
(`scripts/compare_sarif.py`).

### 3.3 Internal counts that change from launch to launch

Two internal counts differ from the parent although the results are the
same. Neither is caused by P3 or P2': both take each of their values in
launches of one build.

| Count | Parent | P3 + P2' | Other launches |
| --- | --- | --- | --- |
| OWASP hand-off rows after runs 5 / 6 / 7 / 8 | 160 / 270 / 214 / 269 | 62 / 120 / 78 / 105, both launches | after run 5 in prototype launches: 62 (P1-P3 counters), 189 (P3 alone), 189 and 91 (two launches of P2' alone); P3 alone (landed): 62 / 120 / 78 / 105 |
| Stirling-PDF run-3 raw / outgoing targets | 654 / 461 in 3 of 3 | 681 / 488 in 3 of 3 | prototype launches: 681 in 2 of 7 (P1-P3 counters, P3 alone launch 3), 654 in 5 of 7; P3 alone (landed): 654, 681 and 654 |

The kept hand-off rows and the reports of Stirling-PDF run 3 are equal
in all launches (1,324 kept, 1,571 rows, 28 reports). The order of work
decides these counts (§10).

## 4. Performance overview

The engine time is from `BIDI_ANALYSIS_END elapsed`. The baseline column
shows the IFDS phase in parentheses. Heap after GC: Young and Full pauses
only (§2). GC pauses: all pauses of the process.

| Project | Build | Status | Wall s | Engine s | Peak RSS GiB | Max heap after GC MB | GC pauses s | Run reached / completed / accepted |
| --- | --- | --- | ---: | ---: | ---: | ---: | ---: | --- |
| OWASP | baseline | OK | 156.4 | (109.3) | 8.58 | 4,987 | — | — |
| OWASP | parent | OK | 197.1 | 121.0 | 9.52 | 6,326 | 5.56 | 11 / 11 / 11 |
| OWASP | P3 + P2' (rerun) | OK | 197.9 | 120.5 | 9.50 | 6,370 | 5.73 | 11 / 11 / 11 |
| OWASP | **P3 alone** | OK | 201.1 | 125.0 | 9.53 | 6,394 | 5.90 | 11 / 11 / 11 |
| Conductor | baseline | OOM | 187.4 | (144.5) | 9.36 | 7,478 | — | — |
| Conductor | parent | TIMEOUT | 1,124.5 | 1,053.8 | 10.26 | 8,112 | 20.27 | 8 / 7 / 7 |
| Conductor | P3 + P2' (rerun) | TIMEOUT | 1,122.6 | 1,050.4 | 9.70 | 8,113 | 34.53 | 8 / 7 / 7 |
| Conductor | **P3 alone** | TIMEOUT | 1,124.7 | 1,052.2 | 9.95 | 8,111 | 20.47 | 8 / 7 / 7 |
| ThingsBoard | baseline | OOM | 439.7 | (402.4) | 13.48 | 11,364 | — | — |
| ThingsBoard | parent | OOM | 384.0 | 228.2 | 14.04 | 11,096 | 65.10 | 1 / – / – |
| ThingsBoard | P3 + P2' (= P3 alone in run 1) | OOM | 430.2 | 248.7 | 13.80 | 11,069 | 66.55 | 1 / – / – |
| Stirling-PDF | baseline | OK | 52.1 | (23.5) | 7.58 | 3,849 | — | — |
| Stirling-PDF | parent, 3 launches | 1 OK, 2 TIMEOUT | 254.3; 1,123.1; 1,112.8 | 160.4; 1,058.1; 1,061.5 | 9.49-10.11 | 5,218-5,708 | 9.2; 11.3; 11.2 | 11/11/11; 9/8/7; 11/10/9 |
| Stirling-PDF | P3 + P2', 3 launches | 1 OK, 2 TIMEOUT | 148.5; 1,111.8; 1,122.0 | 91.9; 1,061.1; 1,056.6 | 9.69-10.10 | 5,105-5,495 | 6.1; 16.9; 16.0 | 11/11/11; 11/10/9; 9/8/7 |
| Stirling-PDF | **P3 alone**, 3 launches | 3 TIMEOUT | 1,109.6; 1,109.4; 1,108.2 | 1,061.9; 1,060.8; 1,062.1 | 9.70-9.84 | 5,007-5,666 | 10.8; 10.7; 11.3 | 9/8/7; 9/8/7; 11/10/9 |

Verdict per project (P3 alone, the landed state, against the parent):

- **OWASP:** no change. Runs 2-11 take 35.4 s (parent 36.1 s). Run 1 is
  80.8 s against 76.2 s; the P3 + P2' rerun has the same run-1 code and
  took 76.3 s, so this is launch noise. Against the baseline, the wall
  time is still 45 s (29%) more.
- **Conductor:** runs 1-7 are 11% faster (578.7 s against 652.4 s), so
  run 8 starts 75 s earlier. The gain is in run 6 (-10%) and run 7
  (-36%). Run 8 still times out: in the last 440 s it handles 21 events.
  GC and heap are the same as the parent. The 7 results are
  byte-identical.
- **ThingsBoard:** OOM in run 1, as before (§9). P3 does not change the
  run-1 heap.
- **Stirling-PDF:** all three P3-alone launches time out (in run 9, run 9 and
  run 11); the parent and P3 + P2' each completed 1 of 3. The results are
  byte-identical to the parent timeout launch. The backward runs are
  faster: run 8 13.1-15.4 s against 17.0-18.1 s, run 10 13.5 s against
  17.1 s. GC and heap are the same as the parent. The stall rate is
  discussed in §10.1.

## 5. Iterations

**Conductor** (engine seconds; the "rows out" column is the hand-off into
the next run, P3 alone / parent):

| Run | Dir | Limit | Parent | P3 + P2' (rerun) | **P3 alone** | P3 alone vs parent | Rows out |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | --- |
| 1 | FWD | 1 | 18.58 | 20.00 | 19.99 | +7.6% | 127,017 / 127,259 |
| 2 | BWD | 1 | 38.65 | 43.41 | 39.66 | +2.6% | 477,786 / 477,906 |
| 3 | FWD | 2 | 7.78 | 7.74 | 7.56 | -2.8% | 17,471 / 17,511 |
| 4 | BWD | 3 | 106.60 | 52.50 | 102.76 | -3.6% | 29,921 / 29,922 |
| 5 | FWD | 4 | 10.12 | 8.97 | 9.34 | -7.7% | 25,045 / 25,180 |
| 6 | BWD | 5 | 374.55 | 304.39 | 338.20 | **-9.7%** | 149,499 / 149,622 |
| 7 | FWD | 6 | 96.14 | 57.77 | 61.17 | **-36.4%** | 84,937 / 85,066 |
| 8 | BWD | 7 | 386.70 T | 540.36 T | 459.65 T | starts 75 s earlier | — |
| Runs 1-7 | | | 652.4 | 494.8 | 578.7 | **-11.3%** | |

- The rows differ by less than 0.1% between builds; the order of work
  makes such differences in every launch (§10.2).
- Run 1 is 20.0 s in both landed launches, against 18.6-19.0 s in five
  earlier launches of the parent core (the P3 prototype: 19.0 s). The
  FLOW subsumption share of run 1 is lower than in the parent (3.7%
  against 4.6%), so the extra 1.0-1.4 s is not in `FlowGroup.addAll`.
  The cause is not found. It is +5-7% of a 20 s run; the next landing
  measurement must check it again.
- Run 2 is +2.6% with P3 alone and +12% with P3 + P2'. The P2' prototype
  had no run-2 slowdown (38.4 s), so it came with the landed form of the
  memo (§6.1).
- Run 8 (T = timeout): 15,614 events 20 s into the run, then +21 events
  in the last 440 s (parent: +0 in 360 s). The owners
  `ParametersUtils#replace` and `replaceList` hold the run (§10.2).

**OWASP** (engine seconds):

| Run | Dir | Parent | P3 + P2' (rerun) | **P3 alone** | Rows out (all builds) |
| ---: | --- | ---: | ---: | ---: | --- |
| 1 | FWD | 76.24 | 76.26 | 80.76 | 67,943 |
| 2 | BWD | 23.77 | 22.47 | 23.67 | 19,938-19,942 |
| 3 | FWD | 8.46 | 9.78 | 8.63 | 462 |
| 4 | BWD | 1.24 | 1.30 | 1.18 | 757 |
| 5 | FWD | 1.29 | 1.06 | 1.03 | 62 (parent 160) |
| 6-11 | | 0.10-0.32 | 0.04-0.25 | 0.04-0.26 | 78-120 (parent 214-270) |
| Runs 2-11 | | 36.1 | 35.3 | 35.4 | |

From run 6 on, the state repeats every two runs, and the analysis ends at
the run limit (requirement AC is not met, as for the parent).

**Stirling-PDF** (engine seconds per run; T = timeout; italic = the
forward stall):

| Run | Dir | Parent 1 (load 22) | Parent 2 | Parent 3 | P3 + P2' 1 | P3 + P2' 2 | P3 + P2' 3 | P3 alone 1 | P3 alone 2 | P3 alone 3 |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | FWD | 28.29 | 21.08 | 21.40 | 21.80 | 21.54 | 22.47 | 21.41 | 21.39 | 20.65 |
| 2 | BWD | 18.52 | 12.94 | 13.04 | 14.48 | 14.25 | 13.54 | 13.23 | 13.81 | 13.18 |
| 3 | FWD | 4.26 | 4.21 | 3.83 | 4.93 | 4.43 | 4.28 | 3.96 | 4.27 | 3.97 |
| 4 | BWD | 4.78 | 3.86 | 3.98 | 3.70 | 3.31 | 3.17 | 3.41 | 3.34 | 3.19 |
| 5 | FWD | 2.17 | 1.14 | 1.44 | 1.07 | 1.28 | 1.24 | 1.09 | 1.37 | 0.98 |
| 6 | BWD | 9.73 | 6.95 | 8.48 | 5.52 | 5.82 | 6.02 | 5.93 | 6.78 | 5.90 |
| 7 | FWD | 2.71 | *88.55* | *25.95* | *5.48* | 1.55 | *46.06* | *82.57* | *107.61* | *10.37* |
| 8 | BWD | 28.59 | 18.08 | 17.01 | 12.72 | 12.39 | 16.00 | 13.52 | 15.35 | 13.07 |
| 9 | FWD | 5.06 | *893.80 T* | *399.44* | *109.61* | 1.82 | *935.72 T* | *909.22 T* | *879.05 T* | *177.95* |
| 10 | BWD | 34.67 | — | 17.13 | 12.87 | 12.94 | — | — | — | 13.53 |
| 11 | FWD | 5.75 | — | *540.34 T* | *858.78 T* | 2.24 | — | — | — | *790.38 T* |
| End | | OK | T run 9 | T run 11 | T run 11 | OK | T run 9 | T run 9 | T run 9 | T run 11 |
| Owner rows at f6 (excess) | | 238 (0) | 237 (+3) | 239 (+1) | 235 (+1) | 238 (0) | 241 (+3) | 237 (+3) | 241 (+3) | 235 (+1) |

- The last row is the hand-off rows of the stall owner after run 6, and
  their excess over the minimal value for the same run-5 output (§10.1).
  Each launch with an excess times out; each launch without one
  completes.
- Backward runs 6, 8 and 10 are faster in both P3 builds than in parents 2
  and 3 (run 8: 12.4-16.0 s against 17.0-18.1 s).
- Load medians of the P3-alone launches: 3.0, 2.9 and 2.4.

**ThingsBoard:** run 1 (FWD, limit 1) took 248.7 s and ended with OOM. The
guard fired 220.3 s into run 1 (parent 190.4 s). The difference is a
40 s CPU shortage on the host after the first guard event (§8.4).

## 6. P2': the time gain, the memory cost and the revert

### 6.1 Time

P2' acts in runs 2 and later, on calls that do not bypass. Its effect is
the difference between the P3 + P2' rerun and the P3-alone launch:

| Measure | Parent | P3 alone | P3 + P2' (rerun) | P2' effect |
| --- | ---: | ---: | ---: | ---: |
| Conductor run 2, s | 38.65 | 39.66 | 43.41 | +9.5% |
| Conductor run 4, s | 106.60 | 102.76 | 52.50 | -48.9% |
| Conductor run 6, s | 374.55 | 338.20 | 304.39 | -10.0% |
| Conductor run 7, s | 96.14 | 61.17 | 57.77 | -5.6% |
| Conductor runs 1-7, s | 652.4 | 578.7 | 494.8 | -14.5% |
| Conductor run-8 start, s into the analysis | 665.8 | 590.8 | 508.4 | 82 s earlier |
| Conductor run-8 tail | +0 events in 360 s | +21 in 440 s | +20 in 520 s | none |
| Stirling-PDF run 6, s (3 launches) | 6.95-9.73 | 5.90-6.78 | 5.52-6.02 | about -7% (means) |
| Stirling-PDF run 8, s | 17.01-28.59 | 13.07-15.35 | 12.39-16.00 | none |
| OWASP runs 2-11, s | 36.1 | 35.4 | 35.3 | none |

- P2' made Conductor run 4 twice as fast and saved 84 s of runs 1-7. No
  build finishes the run-8 tail.
- Conductor run 2 is 9.5% slower with P2'. The P2' prototype (a plain
  `SoftReference`, all calls kept) had no run-2 slowdown (38.4 s), so the
  cause is in the landed form (calls C2 or C3 of the proposal). It is not
  found: the loop restriction, memo included, is 0.5% of the run-2
  samples.

### 6.2 Memory and GC

Conductor, per run (G1; heap after Young and Full pauses):

| Run | Pauses (s), parent | P3 + P2' | P3 alone | Max heap after GC MB, parent | P3 + P2' | P3 alone |
| ---: | --- | --- | --- | ---: | ---: | ---: |
| 1 | 1.41 | 1.56 | 1.57 | 6,292 | 6,261 | 6,279 |
| 2 | 7.37 | 7.83 | 7.28 | 8,112 | 8,113 | 8,111 |
| 3 | 0.43 | 0.32 | 0.41 | 6,364 | 6,333 | 6,349 |
| 4 | 0.88 | 0.97 | 0.86 | 5,867 | 5,847 | 5,862 |
| 5 | 0.21 | 0.26 | 0.23 | 4,950 | 5,298 | 4,998 |
| 6 | 3.06 | **4.92** | 2.75 | 6,055 | **6,828** | 6,196 |
| 7 | 0.72 | 0.70 | 0.60 | 5,366 | **6,770** | 5,357 |
| 8 | 2.56 (in 387 s) | **14.20 (in 540 s)** | 3.05 (in 460 s) | 5,203 | **6,590** | 5,195 |

A run window goes from the start of the run to the start of the next
run, so it includes the barrier. `scripts/gc_per_run.py`.

- Whole process: GC pauses 34.5 s with P2' against 20.3 s in the parent
  and 20.5 s with P3 alone. Concurrent mark: 509.8 s against
  348.9 s (parent).
- The memo heap (class histograms, `-all`, dead objects included):

  | Class | Run 4 +40 s | Run 6 +150 s | Run 8 +150 s |
  | --- | ---: | ---: | ---: |
  | `LoopRestrictionMemo$Key` | 706,285 / 22.6 MB | 1,024,096 / 32.8 MB | 1,308,127 / 41.9 MB |
  | `HashMap$TreeNode` (all maps) | 56,105 / 3.1 MB | 55,996 / 3.1 MB | 400,678 / 22.4 MB |
  | `TrieNode` | 3,471,611 / 194.4 MB | 6,810,581 / 381.4 MB | 8,447,267 / 473.0 MB |
  | `FlowTree` | 1,277,497 / 51.1 MB | 2,912,827 / 116.5 MB | 3,082,485 / 123.3 MB |

- The live size per entry comes from the old-generation drops. In run 8
  the old generation drops by 0.9 GB at the moments when a memo of
  1,000,000 entries is full and cleared. At the run-6 end, where
  `freezeChildren` clears the memos, it drops by 1.6 GB (parent: 0.3 GB).
  So one entry holds about 0.9 KB: the bounded value of the key and the
  result values, which no other store holds.
- Stirling-PDF: the heap after GC of the stall runs is 4,599-4,839 MB
  with P2', against 3,443-3,480 MB in the same runs of the parent and
  3,431-3,698 MB with P3 alone (+1.1-1.4 GB). The GC pauses of the
  timeout launches are 16.0-16.9 s with P2', against 11.2-11.3 s (parent)
  and 10.7-11.3 s (P3 alone).
- The launch maximum of the heap after GC does not change (Conductor
  8,113 MB against 8,112 MB; Stirling-PDF 5,105-5,495 MB against
  5,218-5,708 MB), because run 2 (Conductor) and the prescan and runs 1-3
  (Stirling-PDF) set it. Peak RSS does not change: the heap is committed
  early in all launches.
- The memo lookups were slow. Keys of trie values with the same low 32
  hash bits fall into one bucket. A bucket of more than 8 entries becomes
  a tree, and `Key` is not `Comparable`, so each lookup walks the tree and
  calls the deep `Key.equals`. In the Stirling-PDF stall of launch 1,
  this was 14.0% of the analyzer samples. The cause is the trie hash: it
  is a sum over the children, and each level shifts the child hash by 5
  bits (`ap/Trie.kt:60`); `hashCode` keeps the low 32 bits (`:76`). So
  two tries that differ only at depth 7 or more have the same `hashCode`.

### 6.3 Decision

Proposal §6.3 reverts a commit when "the time or the memory of a project
is worse beyond the spread of the parent launches". For P2':

| Item | Spread of the parent | P3 + P2' | Verdict |
| --- | --- | --- | --- |
| Results | — | identical | pass |
| Heap after GC of the long loop runs | Conductor: one launch; Stirling-PDF stall runs 3,443-3,480 MB | Conductor runs 6-8 +0.8-1.4 GB; Stirling-PDF stall runs +1.1-1.4 GB | **worse** |
| GC pause time | Conductor 20.3 s (one launch); Stirling-PDF timeout launches 11.2-11.3 s | Conductor 34.5 s (launch 1: 37.2 s); Stirling-PDF 16.0-16.9 s | **worse** |
| Launch maximum of the heap after GC, peak RSS | — | not higher | pass |
| Time of the long runs | — | Conductor runs 4 and 6 faster (§6.1) | pass |
| Conductor run 2 | parent 38.7 s; P3 alone 39.7 s | 43.4 s (+9.5% against P3 alone) | worse; cause not found |

So P2' was reverted (`c89881544`). P3 stays. The memo is exact and it
saves time; its footprint is the problem. In an 8 GiB heap, a project
with several hot loop owners in one run could hold several GB in memos,
because the cap is per method runtime. The next proposal (N4) bounds the
footprint in trie nodes, keeps the entries that recur, and gives the memo
key its own strong digest.

## 7. Run 1 and the transition to run 2

P2' does not act in run 1, so run 1 is the same code in both builds. The
run-1 shares below are from the P3 + P2' launches (JFR, disjoint
subsystems; OWASP and Conductor reruns, Stirling-PDF launch 2):

| Subsystem | OWASP new / parent | Conductor new / parent | Stirling-PDF new / parent | ThingsBoard new / parent |
| --- | --- | --- | --- | --- |
| Alias analysis | 22.8% / 22.2% | 21.6% / 20.3% | 39.0% / 38.0% | 8.6% / 8.0% |
| Rule resolution | 7.9% / 7.9% | 29.7% / 29.9% | 31.3% / 31.5% | 18.7% / 17.0% |
| Call-plan forms | 16.6% / 16.0% | 7.9% / 8.3% | 8.2% / 8.6% | 7.4% / 7.5% |
| Summary store | 6.4% / 7.0% | 5.3% / 6.2% | 2.0% / 2.5% | 15.8% / 16.8% |
| AP algebra | 9.9% / 10.5% | 5.4% / 5.3% | 2.2% / 2.0% | 13.7% / 13.9% |
| FLOW subsumption (P3) | 7.3% / 7.7% | 3.7% / 4.6% | 2.9% / 2.8% | 2.1% / 3.3% |
| Allocation, GiB | 119.5 / 120.8 | 54.8 / 56.0 | 61.5 / 54.8 | 805.3 / 867.6 |

Run-1 engine seconds:

| Project | Parent | P3 + P2' | P3 alone |
| --- | ---: | ---: | ---: |
| OWASP | 76.24 | 76.26 | 80.76 |
| Conductor | 18.58 | 20.00 | 19.99 |
| Stirling-PDF (3 launches) | 21.08-28.29 | 21.54-22.47 | 20.65-21.41 |
| ThingsBoard | 228.2 (OOM) | 248.7 (OOM) | not launched |

- No subsystem moves by more than 2 points. Run 1 is not faster: P3 cuts
  the FLOW subsumption allocation (ThingsBoard `compactPacket` 4.25 GB →
  0.90 GB sampled), but FLOW subsumption is only 2-8% of run 1.
- Run 1 is still dominated by work that the prescan already did: alias
  analysis (8.6-39.0%) and rule resolution (7.9-31.3%). This is P4 of
  the carried-over proposals.
- **Transition.** The run-1 barrier and the hand-off are unchanged:

  | Item | OWASP | Conductor | Stirling-PDF |
  | --- | --- | --- | --- |
  | Barrier 1, s (new / parent) | 2.37 / 2.48 | 2.08 / 1.82 | 0.85 / 0.78 |
  | Demand rows out of run 1 (new / parent) | 67,943 / 67,943 | 127,259 / 127,259 (P3 alone 127,017) | 66,169 / 66,169 |
  | Max heap after GC, run 1 → run 2, MB (new / parent) | 6,244 → 6,370 / 6,253 → 6,326 | 6,261 → 8,113 / 6,292 → 8,112 | 3,522 → 4,769 / 3,747 → 5,367 |
  | RSS before → after, GiB | 9.40 → 9.38 / 9.40 → 9.41 | 9.30 → 9.30 / 9.41 → 9.41 | 9.49 → 9.49 / 8.63 → 8.63 |

  No heap jump at the barrier and flat RSS. The barrier is 1-10% of the
  run-1 time. On Conductor, run 2 sets the heap maximum of the launch
  (8.1 GB of 8 GiB) in every build.
- **Run 2.** Conductor run 2 is 39.7 s with P3 alone (parent 38.7 s,
  P3 + P2' 43.4 s): the +12% of P3 + P2' is a P2' effect (§6.1).
  Stirling-PDF run 2 is 13.2-13.8 s with P3 alone (parent 12.9-13.0 s;
  nine prototype launches of this core: 13.0-16.0 s), so within the
  spread.

## 8. Hot spots and unexpected workload patterns

### 8.1 P3: the diagnosing quantity fell

`FlowGroup.addAll` in the Conductor tails, P3 + P2' against the parent:

| Window | Measure | P3 + P2' | Parent |
| --- | --- | ---: | ---: |
| Run 6, async-profiler | % of analyzer samples | 8.0% | about 10.3% |
| Run 6 tail, JFR | Java samples (share) | 1,208 (19.8%) | 3,608 (33.3%) |
| Run 8, async-profiler | % of analyzer samples | 7.7% | 22.0% |
| Run 8 tail, JFR | samples per second (share) | 3.1 (10.4%) | 15.0 (35.1%) |
| Run 7 tail, JFR | Java samples (share) | 2,115 (82.3%) | 5,284 (90.3%) |

The P3-alone Conductor windows (async-profiler; shares of analyzer
samples, GC as a share of all samples):

| Window | Cores | GC | `FlowGroup.addAll` | `restrict` | `TaintGroup.addAll` | `replaySaved` | trials |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| P3 alone, run 4 | 2.23 | 55.2% | 1.0% | 81.6% | 5.7% | 1.4% | 50.2% |
| P3 alone, run 6 | 2.04 | 51.2% | 2.4% | 59.1% | 17.3% | 84.9% | 31.8% |
| Parent, run 6 | 1.9 | 47.1% | about 10.3% | 57.3% | — | 83.9% | — |
| P3 alone, run 8 | 2.02 | 50.8% | 7.9% | 83.6% | 0.0% | 99.2% | 47.6% |
| Parent, run 8 | 2.1 | 52.2% | 22.0% | 70.6% | — | 99.5% | 40.6% |
| P3 alone, near the limit | 2.08 | 52.0% | 6.8% | 83.6% | 0.1% | 98.9% | 48.4% |
| Parent, near the limit | 2.2 | 53.8% | 27.1% | 66.5% | — | 99.4% | — |

With P3 alone the GC share is the parent's (51-55%), and
`FlowGroup.addAll` falls from 22-27% to 7-8% of the analyzer samples in
run 8. The loop restriction takes its place (84% against 67-71%).

In run 8, about 76% of the remaining `addAll` time is
`canonicalize → subtractSubsumed → TrieOps.subtract`: the subtraction of
the dirty rows themselves.

### 8.2 Conductor run 7: `recompact` re-adds every row

- Run 7 is still 82% `FlowGroup.addAll` (JFR, P3 + P2'; parent 90%).
- 74% of these calls come from `FlowBackedSummaries.recompact →
  ConclusionGroup.addAll` (`store/FlowBackedSummaries.kt:42-76`). 91% of
  their time is `canonicalize → compactPacket → forEachLeafPosition`.
- `recompact` builds a new group and adds every current row to it again.
  Each row is new to the empty group, so P3 treats it as dirty, and
  `compactPacket` walks all its leaves from the root. P3 cannot help this
  path (next proposal N7).

### 8.3 Stirling-PDF: TAINT canonicalization in the stall

- With P3 + P2', `TaintGroup.addAll` is 64-83% of the Java samples of
  each stall window (JFR). Inside it, `TaintGroup.canonicalize →
  TrieOps.subtract → SubtractKey.equals` is the top path. With P3 alone
  the restriction is again the largest part (41.8-74.8% of the analyzer
  samples) and `TaintGroup.addAll` the second (20.8-52.4%).
- `TaintGroup.addAll` runs a full canonicalization of the lane after each
  insert, as `FlowGroup.addAll` did before P3 (next proposal N2).
- Allocation in the stall: `TrieOps.subtract` 17.2%, `mapChildren`
  15.5%, `MarkSet.minus` 13.3%; `SubtractKey` objects are 14.9% of the
  bytes.

### 8.4 Other patterns

- **Single-thread tails.** In the Conductor and Stirling-PDF tails one
  analyzer thread works (JFR: 1.00-1.14 analyzer threads per 5 s in both
  builds). The other workers park; 4,664 worker-seconds are parked in the
  Conductor run-8 tail.
- **Rule-cache lock.** Waits in `ResolverView.cached`: ThingsBoard
  prescan 536 s and run 1 231 s, Conductor prescan 166 s, Stirling-PDF
  prescan 97 s (P3 + P2'; parent: 414 s, 198 s, 137 s, 138 s). The code
  is the same; the waits vary with timing (P8).
- **Call plans built in each run.** OWASP `FormsCache.payload` is 56.8%
  of the run-2 and 47.0% of the run-3 Java samples (parent 59.8% and
  43.8%) (P5).
- **Memo lookups in tree bins** (P3 + P2' only, §6.2).
- **ThingsBoard P3 + P2' launch:** 40 s at 3.8-4.9 process cores while
  the host load was 19-26. Other processes took the CPU. After it, the
  event rate equals the parent.

## 9. ThingsBoard OOM: the source of memory consumption

Data: `analysis/heap-thingsboard.md` (Eclipse MAT census of the P3 + P2'
heap dump at the guard, compared with the parent dump). Run 1 is the same
code in both builds (P2' bypasses run 1), so the P3-alone build has this
heap too.

- **The same wall.** The guard stopped run 1 with 11.39 GB reachable in
  302.5 M objects (parent 11.38 GB, 302.8 M). The live heap after the
  last full GC is 11,063 MiB in both. The guard came at 4.33 M events
  (parent 4.69 M; five other launches of this run 1: 4.28-4.42 M). The
  engine bytes per stored point membership are the same: 374 B (parent
  368 B).
- **P3 and P2' do not change run-1 memory.** FLOW groups at points hold
  297.6 MB (parent 300.5 MB). P3 cut the sampled allocation in
  `FlowGroup.compactPacket` from at least 4.25 GB to 0.90 GB; this is CPU
  and GC work, not live heap. `LoopRestrictionMemo` exists as 1,276 empty
  objects (30,624 B in total).
- **Owners** (disjoint, retained):

  | Owner | Bytes | Share |
  | --- | ---: | ---: |
  | Actors (562 units, 72,065 actors) | 3.55 GB | 31.1% |
  | Caller subscriptions (`SubscriptionManager`) | 1.83 GB | 16.1% |
  | Callee storages and static service | 0.84 GB | 7.3% |
  | **Engine state** | **6.29 GB** | **55.2%** |
  | IR database | 3.08 GB | 27.1% |
  | Rules cache | 0.80 GB | 7.0% |
  | Interpreter entries (`JIRMethodEntries`) | 0.77 GB | 6.7% |

- **What fills the engine.** About 3.99 GB (63% of the engine state) are
  collection structures, and most sets hold 1-2 elements: 2.61 M
  per-source cell sets of caller families (0.57 GB), 1.13 M `PathTrie`
  posting sets (0.47 GB), 1.74 M one-element Target sets (0.39 GB),
  unused replacement indexes (0.30 GB), empty mark-relation maps
  (0.19 GB). Duplicate small keys hold 0.43 GB (4.27 M `GroupKey` objects
  with 2,856 values), and duplicate trie nodes, headers and mark sets
  0.32 GB.
- **Loop actors.** 1,276 loop actors (1.8% of the actors) hold 1.59 GB
  (45% of the actor bytes), in 11,602 block entries.
- **Root cause.** Run 1 keeps the working state of every actor until the
  run-1 barrier, but the barrier does not read most of it
  (`RunManager.prepareJoined`, `engine/RunManager.kt:211-268`):

  | State | Bytes | Read at the barrier |
  | --- | ---: | --- |
  | Point edges (`ScopedEdgeStore`) | 0.98 GB | no: `freeze` drops them |
  | Point resumes (`Run1PointResume`) | 0.23 GB | no: `freeze` clears them |
  | Local services | 0.24 GB | no: `freeze` clears them |
  | Publication indexes | 0.76 GB | no: `detachJoinedSubscribers` drops them |
  | Caller inputs (`CallerInputValues`) | 1.83 GB | only by the static-writer binding (568 writer rows) |
  | Summaries and Target rows (exports) | 0.57 GB | yes |

  The engine bytes per stored membership are constant over the run, so
  the heap follows all past work, not the open work. The parent report
  said that the barrier reads all actors; the code reads only the exports
  and the inputs on static-writer chains.
- **Candidates** (all exact; next proposal N1, N5, N6):
  1. Release the working state of a complete subgoal (actor and premise,
     completed with its strongly connected group, as in tabled
     resolution) before the barrier: up to 3.4 GB. The complete share at
     the guard is not measured.
  2. One store set per loop method, not per loop block: 1.0-1.3 GB.
  3. Representation and sharing (caller families, Target rows, lazy
     indexes, interned keys, shared tries, `PathTrie` sets): together
     2.1-2.4 GB. This alone moves the guard to about 6.5-7.0 M events.
     Earlier 16 GB launches needed 7.9-9.9 M events to finish run 1, so
     items 1 and 2 are necessary.
  4. A bound on the rules cache and the interpreter entries: up to
     0.7 GB, at the cost of recomputation.

## 10. Stirling-PDF stall and the Conductor tail

Data: `analysis/stall.md` (logs, JFR, async-profiler windows and the
frontier lines of 15 Stirling-PDF launches of this core: parent, P3 + P2',
and the P1-P3 prototype launches), and the 3 P3-alone launches of this
report.

### 10.1 Stirling-PDF: the hand-off split decides the stall

- **The owner** is `EmlProcessingUtils#decodeMimeHeader(String) [{}]`, as
  before. It is the only method key whose hand-off rows differ between
  launches.
- **The rule (stall analysis, 15 launches).** At frontier 6 the owner gets 234 or 238
  rows in each of the 5 fast launches. All 5 complete; runs 9 and 11 take
  1.6-5.8 s. It gets 1 or 3 rows more in each of the 10 slow launches. All
  10 time out. So the outcome is fixed after runs 1-6, about 57-58 s into
  the analysis.
- **The split starts in run 5** (forward, limit 4, 1.0-1.7 s). Its input
  has equal per-key row counts in all 18 launches. Its output on the
  owner is 181 or 166 rows, and the owner gets 2,467 or 1,006 offers.
- **Probable mechanism (from the code; not measured).** The FLOW and TAINT
  groups keep a covered coordinate in the row that arrived first, and the
  merges act on the first match in list order (`ap/Groups.kt`). So the same
  facts can be stored as a different set of rows, and the hand-off
  (`driver/HandOff.kt:49-72`) projects a different number of rows. A
  census of the stored rows and of the union of their facts at the run-6
  barrier must confirm this (next proposal N3).
- **Inside a stall (P3 + P2' launches).** One thread works (172 of 172 and 187 of 188
  five-second buckets). The handled-event count stays flat with 11-12
  events in flight. Shares of analyzer samples: `TaintGroup.canonicalize`
  38.8-77.2%, restriction misses 7.2-39.4%, memo `HashMap` 3.1-14.0%;
  the top self frame is `SubtractKey.equals` (18.2-34.7%).
- **Inside the stall, P3 changes nothing, and P2' only moved the
  cost.** `FlowGroup.addAll` is 0.0% of the stall samples in every build.
  With P2' the restriction fell from 26.5-48.6% to 3.4-23.3% of all
  samples, and `TaintGroup.canonicalize` became the top frame. With P3
  alone the shares are those of the parent: restriction 41.8-74.8% and
  `TaintGroup.addAll` 20.8-52.4% of the analyzer samples.
- **The f6 rule holds in 18 of 18 launches**: the 15 launches of the
  stall analysis and the 3 P3-alone launches (f6 excess +3, +3 and +1;
  all time out).
- **The stall rate.** The parent and P3 + P2' time out in 2 of 3
  launches, P3 alone in 3 of 3. Over all launches of this core:

  | Launches | Fast | Slow |
  | --- | ---: | ---: |
  | P3 active (P3 prototype, P3 + P2', P3 alone; 3 each) | 1 | 8 |
  | P3 not active (parent, P2' prototype, P2 census and counters; 3 each) | 4 | 5 |

  The difference is not significant at this size (Fisher exact test,
  one-sided p = 0.15). P3 gives the native rows and delta for each call
  sequence (§1 tests), so it can change the outcome only through the
  timing of the work in runs 5-6, which decides the split. This is a
  signal, not a proof. N3 of the next proposal removes the dependency on
  the order; until then, a Stirling-PDF gate with 3 launches cannot see
  a change of the stall rate.

### 10.2 Conductor: the tail grows with the field limit

- **The owners** are `ParametersUtils#replace` (two contexts) and
  `ParametersUtils#replaceList`, which are mutually recursive. They hold
  92.8% of the rows into run 7 and 88.0% into run 8.
- **All launches stall in run 8**, and their row counts differ by 2.4% at
  most. So the Conductor tail does not depend on the order.
- **Cost per offer grows with the limit.** Replay cost per offer of
  `replace [HashMap]`: 0.150 ms (limit 3), 0.589 ms (limit 5), 2.085 ms
  (limit 7). Distinct restriction keys per run: 0.83 M, 2.43 M, 2.83 M.
  Inside one run, 73-90% of the restriction calls repeat a key.
- **Run-8 frames** (analyzer samples): `replaySaved` 99.2%, restriction
  77.2-81.0%, trials 43.8-47.1%, the demand-view scan
  (`scanLocalInitials`) 28.2-31.0%. One thread works in 106 of 109
  five-second buckets.
- **Why the run order does not stop the growth.** This is cyclic code:
  the rows of the owners grow with K (14.4 k at limit 3, 128.6 k at
  limit 5, parent report §5). Requirement AC does not cover it.

## 11. Optimization points per project

| Project | Run-1 time | Run-1 → run-2 transition | Hot spots | Memory (OOM) source |
| --- | --- | --- | --- | --- |
| OWASP | 76-81 s: alias analysis 22.8%, call-plan forms 16.6%, rule resolution 7.9% (P4); one analyzer core (P7) | Barrier 2.3-2.5 s, 67,943 demand rows out of run 1, no heap jump. Run 2 is 47-52% call-plan building (`FormsCache.payload`): P5 | Runs 1-2 use about one analyzer core: P7 | no OOM; the launch maximum of the heap after GC (6.3-6.4 GB) is in runs 1-2 |
| Conductor | 20.0 s: rule resolution 29.7%, alias analysis 21.6% (P4); +1.0-1.4 s against earlier launches, cause not found (§5) | Barrier 1.8-2.1 s, 127 k demand rows out of run 1. Run 2 makes 478 k rows; their compaction takes 3.4-3.7 s, and barrier 2 has one Full GC (1.5-1.7 s) | Runs 4-8: loop replay and restriction (N4, N8), TAINT canonicalization (N2), `recompact` (N7); one thread in the tail (N9) | no OOM; the heap after GC reaches 8.1 GB in run 2 |
| ThingsBoard | Run 1 does not finish: OOM at the guard (§9) | not reached | Rule-cache lock in the prescan (536 s of waits) and in run 1 (231 s): P8 | Working state of finished work (N1), loop block stores (N5), collection overhead (N6) |
| Stirling-PDF | 20.7-21.4 s: alias analysis 39.0%, rule resolution 31.3% (P4) | Barrier 0.8 s, 66,169 demand rows out of run 1 | Order-dependent stall in run 7/9/11: TAINT canonicalization (N2), the hand-off split (N3) | no OOM; prescan and runs 1-3 set the heap maximum |

## 12. Blind spots

- **Conductor run 1 is +1.0-1.4 s in both landed launches** (§5). The
  cause is not found.
- **The Stirling-PDF stall rate with P3** (1 fast of 9 launches against 4
  of 9) is a signal without significance (§10.1).
- **One launch per build for OWASP and Conductor.** The parent has one
  launch of each. Run-1 time of one build varies by up to 6% between quiet
  launches (OWASP P3 + P2' 76.3 s, P3 alone 80.8 s, with the same run-1
  code). Gains below about 10% on these projects are not proven.
- **Order noise.** Stirling-PDF stalls in 2 of 3 launches in each build;
  over 15 launches, 10 stalled. Three launches cannot show a change of
  the stall rate.
- **The Stirling-PDF stall owner is inferred.** The landed logs do not
  name it. The mechanism (H1) is from the code.
- **The memo hit rate and the memo retained size are not measured.** The
  landed code has no counter. The size per entry is an inference from
  old-generation drops.
- **ThingsBoard was not launched with P3 alone.** Its run 1 does not use
  P2', and the census shows an empty memo.
- **The P3 + P2' ThingsBoard launch lost about 40 s** to other processes
  on the host (load 19-26 while the process used 3.8-4.9 cores).
- **Parent profiles.** The parent Stirling-PDF reruns have no JFR and no
  raw collapsed files; only the shares in
  `analysis/parent-profile-shares.tsv` remain.
- **JFR covers Java code only**, and an async-profiler window is 30 s of
  one run.

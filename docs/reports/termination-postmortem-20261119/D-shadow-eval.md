# D — Shadow evaluation of QUIET-Q2 / QUIET-Q1' / REPEAT on existing logs

Read-only log analysis; nothing was built or run. Scripts and raw output are in this directory:
`shadow.py` (parser + the three tests), `list.tsv`/`list2.tsv` (label + log path), `shadow.json` (2,083 analyses,
every run of every analysis), `summ.py`, `detail.py`, `native-projects.md` (full per-run tables for the native
project launches), `rules-late.md` (native rule cases ending at run >= 5), `refine-late.md`.

## 1. What the log fields mean (Frontier.kt 69-78, Report.kt, IterationDriver.kt 214-233)

- `reports N` in the `Run N (DIR) frontier:` line and `reports=` in `BIDI_TARGET_STATISTICS` are both
  `terminals.entries.size` = **confirmed** root reports only (NormalTarget rows with a ZERO premise at a configured root).
  The map is carried forward and only `putIfAbsent`-ed, and `prepare` returns the old state unchanged on backward runs.
  So within one analysis the confirmed set is **monotone**: an equal count between two barriers means an identical
  identity set. Counts-vs-identities is therefore not an issue for confirmed reports inside one launch.
- **Provisional** reports (`latestReached`, the last forward run's `reachedSinkReportIds`) are NOT in the frontier line.
  They are replaced at every forward barrier and are added to the final report only when the end reason is `RUN_LIMIT`
  (`ReportBuilder.build`). The only place they are logged is the final `BIDI_REPORT_STATISTICS … confirmed= provisional=`.
- `demand edges X in Y method keys` = handoff demand rows / owner keys; `target demand` = outgoing targets;
  `BIDI_HANDOFF_COMPACTION rows=` equals the frontier demand rows in every log read.
- Engine time per run = `BIDI_RUN_END engineTime`; barrier cost = `BIDI_BARRIER_END iterationTime - engineTime`.
- REPEAT was evaluated in two forms: *strict* (all ten frontier numbers equal) and *loose*
  (demand rows, keys, target demand, reports, seeds — ignoring `record crossings`, `analysed`, `left`, zero-only).

## 2. Corpus

| Label | Runtime | Logs | Analyses | Reached run >= 5 |
|---|---|---|---|---|
| NATIVE-758ad99ff | current native HEAD (worktrees `baseline`, `baseline-stirling-repeat`, `cost-control` in `…rule-prototypes-20261118.n00xyl`) | 8 | 8 (OWASP x2, conductor x2, Stirling x3, OWASP selected entry to run-101) | 8 |
| NATIVE-run101 | `termination-baseline-run101.NbDdcB` (OWASP selected entry, cutoff 101, 2 launches) + omit-helper ablation (diagnostic) | 3 | 3 | 3 |
| NATIVE-Nov12-472288cf | `/drive-testcomp/opentaint-go-rules/work-reduction-20261112` — the run that produced 449/128/3/2/1/2 | 4 | 585 rule cases + OWASP, conductor, Stirling | 11 |
| OLDER (Nov 8-10 native + diagnostics) | main-migration, post-merge-validation, rules-bidirectional-runner, investigations, redundant-demand | 37 | 747 (incl. a second 585-case rule suite, `main-migration-20261109/rules-run11`) | 41 |
| REFINEMENT-1197f72f7 (NOT native) | `demand-refinement-performance-20261118.DS91bH` (468/109/4/2/1/1 rule suite, projects, ablations) | 13 | 597 | 12 |
| PROTOTYPE (NOT native) | every `R*`, `useful-*`, `SINGLETON`, `C5-SHARE` tree in n00xyl | 140 | 140 | 139 |

The native rule-suite log with per-run lines is NOT in the archive tree; it is at
`/drive-testcomp/opentaint-go-rules/work-reduction-20261112/rules/analyzer.log` (revision 472288cf, Nov 12).
There is no rule-suite log from the current native HEAD 758ad99ff.
thingsboard never completes run-1 (OOM) in any native log, so it contributes nothing.

## 3. Native project launches (per-run tables in `native-projects.md`)

| case | end | fwd confirmed counts | final conf/prov | last gain | Q2 | Q1' | REPEAT strict / loose | engine total s |
|---|---|---|---|---|---|---|---|---|
| n00xyl/baseline/projects/conductor | run-8 ABNORMAL/TIMEOUT | 1:2 3:5 5:7 7:7 | 7/0 | run-5 | never | run-7, loss 0, saves 192.5s | never / never | 1034 |
| n00xyl/baseline/projects/OWASP | run-11 RUN_LIMIT/COMPLETE | 1:2120 3:2633 5:2633 7:2633 9:2633 11:2633 | 2633/0 | run-3 | run-7, loss 0, saves 17.0s | run-5, loss 0, saves 26.3s | never / run-11 (=cutoff, saves 0) | 150 |
| n00xyl/baseline/projects/Stirling-PDF | run-11 ABNORMAL/TIMEOUT | 1:7 3:28 5:32 7:32 9:32 | 32/0 | run-5 | run-9, loss 0, saves 89.3s | run-7, loss 0, saves 847.2s | never / never | 1009 |
| n00xyl/baseline-stirling-repeat/…/Stirling-PDF | run-11 ABNORMAL/TIMEOUT | 1:7 3:28 5:32 7:32 9:32 | 32/0 | run-5 | run-9, loss 0, saves 568.5s | run-7, loss 0, saves 976.4s | never / never | 1047 |
| n00xyl/cost-control/projects/Stirling-PDF | run-11 ABNORMAL/TIMEOUT | 1:7 3:28 5:32 7:32 9:32 | 32/0 | run-5 | run-9, loss 0, saves 548.7s | run-7, loss 0, saves 969.9s | never / never | 1051 |
| n00xyl/cost-control/projects/conductor | run-8 ABNORMAL/TIMEOUT | 1:2 3:5 5:7 7:7 | 7/0 | run-5 | never | run-7, loss 0, saves 228.0s | never / never | 1031 |
| n00xyl/cost-control/projects/OWASP | run-11 RUN_LIMIT/COMPLETE | 1:2120 3:2633 5:… | 2633/0 | run-3 | run-7, loss 0, saves 14.0s | run-5, loss 0, saves 21.7s | never / run-11 (=cutoff) | 145 |
| n00xyl/baseline/owasp-entry (cutoff 101) | run-101 RUN_LIMIT | 1:1 3:2 5:2 … 101:2 | 2/0 | run-3 | run-7, loss 0 | run-5, loss 0 | run-13 / run-11 | 6 |
| run101.NbDdcB (2 launches, cutoff 101) | run-101 RUN_LIMIT | 1:1 3:2 5:2 … 101:2 | 2/0 | run-3 | run-7, loss 0 | run-5, loss 0 | run-13 / run-11 | 4 |
| run101.NbDdcB/owasp-omit-helper (diagnostic) | run-11 NO_DEMAND_EDGE | 1:1 3:2 … 11:2 | 2/0 | run-3 | run-7, loss 0 | run-5, loss 0 | never / never | 1 |
| work-reduction-20261112/projects/conductor | run-8 ABNORMAL/TIMEOUT | 1:2 3:5 5:7 7:7 | 7/0 | run-5 | never | run-7, loss 0, saves 372.3s | never / never | 1039 |
| work-reduction-20261112/projects/OWASP | run-11 RUN_LIMIT | 1:2120 3:2633 … | 2633/0 | run-3 | run-7, loss 0, saves 13.6s | run-5, loss 0, saves 23.1s | never / run-11 (=cutoff) | 142 |
| work-reduction-20261112/projects/Stirling-PDF | run-11 ABNORMAL/TIMEOUT | 1:7 3:28 5:32 7:32 9:32 | 32/0 | run-5 | run-9, loss 0, saves 812.7s | run-7, loss 0, saves 989.6s | never / never | 1050 |

"saves" = engine time of all later runs, including the partial run cut by the timeout, so on TIMEOUT cases it is
"time until the wall-clock budget", not the cost of a completed analysis.

Representative per-run rows (native HEAD, `baseline/projects`):

```
conductor   run: 1F    2B     3F    4B     5F    6B      7F     8B
  reports      2     2      5     5      7     7       7      (timeout)
  demand rows 127047 477983 17468 29951  25114 149630  85402
  engine s    21.0   45.7   9.0   134.8  9.4   499.2   122.7  192.5+
Stirling    run: 1F    2B     3F   4B   5F   6B   7F   8B   9F     10B  11F
  reports      7     7      28   28   32   32   32   32   32     32   (timeout)
  demand rows 66172 265833 1594 4844 1232 1327 980  1132 892    1127
  engine s    41.2  39.5   15.9 9.9  3.6  18.3 33.1 32.6 725.2  19.3 70.1+
OWASP       run: 1F    2B    3F   4B   5F   6B   7F   8B   9F   10B  11F
  reports      2120  2120  2633 2633 2633 2633 2633 2633 2633 2633 2633
  demand rows 68053 20032 1064 2173 1045 2130 1111 2223 1111 2223 1111
  engine s    79.1  25.5  11.5 3.9  3.8  6.0  3.3  3.6  3.3  6.7  3.5
```

Observations:
- Every project gains its last confirmed report at run-3 (OWASP) or run-5 (conductor, Stirling), in all 11 native
  project launches (3 revisions, counts identical across launches).
- **Q2** fires at run-7 (OWASP) and run-9 (Stirling) and **never on conductor**: conductor's last gain is run-5, so
  Q2 needs run-9, and run-8 already times out. Q2 does not rescue conductor.
- **Q1'** fires at run-5 (OWASP) and run-7 (conductor, Stirling). On Stirling it avoids the pathological run-9
  (725 s / 391 s / 403 s / 160 s) which Q2 must still execute.
- **REPEAT** (strict) never fires on any project inside the run-11 cutoff. OWASP is period-2 from run-7 in demand
  rows/keys/targets/seeds, but `record crossings` keeps drifting (5454, 5845, 5853), so strict equality fails; the
  loose form first matches at run-11, i.e. at the cutoff, saving nothing. On the OWASP selected entry strict REPEAT
  fires at run-13 and loose at run-11 — only visible with the cutoff raised to 101. Conductor (growing) and
  Stirling (slowly decaying) never repeat.

## 4. Native rule suite (585 Java cases, Nov-12, 472288cf)

End distribution reproduced from the log: 449 run-1, 128 run-3, 3 run-5, 2 run-7, 1 run-9, 2 RUN_LIMIT at run-11.
Final: 265 cases with 0 confirmed, 303 with 1, 12 with 2, 2 with 3, 1 with 5; provisional = 0 in all 585.
(end run, last-gain run) census: (1,-)238 (1,1)211 (3,-)27 (3,1)76 (3,3)25 (5,3)2 (5,5)1 (7,5)2 (9,1)1 (11,1)1 (11,3)1.
No confirmed report is ever gained at run >= 7.

Cases ending at run >= 5 (forward confirmed counts):

| case | natural end | run1 | run3 | run5 | run7 | run9 | run11 | Q2 | Q1' | REPEAT strict/loose |
|---|---|---|---|---|---|---|---|---|---|---|
| PassthroughValueFlowSamples#facesSelectItemGroupUnsafe | run-5 | 0 | 0 | **1** | | | | — | — | — |
| PassthroughContainerSamples#listIterateUnsafe | run-5 | 0 | 1 | 1 | | | | — | run-5 (= natural end) | — |
| PathTraversalServletSamples$UnsafeCookieDownloadServlet#doGet | run-5 | 0 | 3 | 3 | | | | — | run-5 (= natural end) | — |
| PassthroughContainerSamples#mapEntryUnsafe | run-7 | 0 | 0 | **1** | 1 | | | — | run-7 (= natural end) | — |
| BeanInjectionSamples#doPost | run-7 | 0 | 0 | **1** | 1 | | | — | run-7 (= natural end) | — |
| PassthroughValueFlowSamples#stringBuilderAppendUnsafe | run-9 | 1 | 1 | 1 | 1 | 1 | | run-5 | run-5 | — / run-5 |
| PathTraversalServletSamples$UnsafeFileUploadServlet#doPost | cutoff | 0 | 1 | 1 | 1 | 1 | 1 | run-7 | run-5 | run-9 / run-9 |
| PassthroughFileModelSamples#fileToStringUnsafe | cutoff | 1 | 1 | 1 | 1 | 1 | 1 | run-5 | run-5 | run-5 / run-5 |

LOSS = 0 for all three tests over all 585 cases. Before-natural-end firings: Q2 3 cases, Q1' 3 cases, REPEAT 2
(strict) / 3 (loose). Engine time saved is negligible (whole suite = 6.2 s of engine time; savings < 0.25 s).
The same table holds, count for count, in the Nov-9 native suite (`main-migration-20261109/rules-run11`) (see section 5 for
the refinement suite, which is not native).

## 5. Counterexample hunt: "quiet then gain"

Definition used: a forward run i >= 3 with count_i == count_{i-2}, and a later forward run with a larger count.

Found in 2,083 analyses: **only one pattern, in three rule cases, and only "quiet at run-3, gain at run-5"**:

| case | run1 | run3 | run5 | run7 | seen in |
|---|---|---|---|---|---|
| PassthroughValueFlowSamples#facesSelectItemGroupUnsafe (os-command-injection) | 0 | 0 | 1 | | native Nov-12, native Nov-9, refinement |
| PassthroughContainerSamples#mapEntryUnsafe (os-command-injection) | 0 | 0 | 1 | 1 | native Nov-12, native Nov-9 |
| BeanInjectionSamples#doPost (bean-injection) | 0 | 0 | 1 | 1 | native Nov-12, native Nov-9, refinement |

Consequences:
- "No growth at one forward run" is NOT a sound indicator of finality: these three true-positive samples would be
  lost by a Q1'-style test evaluated at run-3. They survive only because of the `i >= 5` floor: at run-5 the count
  grows, so neither Q1' nor Q2 fires there. Q1' has a margin of exactly zero runs on them.
- No case anywhere has a quiet forward run at i >= 5 followed by a gain; the longest quiet streak ever followed by a
  gain is 1 forward run; no confirmed report is first seen at run >= 7 in any log of any runtime
  (native, refinement, 140 prototype launches). Q2 (two quiet forward runs) has LOSS = 0 on every analysis.
- Corollary for the cases with a natural stop at 5/7/9: reports are confirmed at run-1 (1 case), run-3 (2) or
  run-5 (3); the run-7/run-9 tails add demand only.
- Extra long-horizon evidence (older, Nov-9 uncapped rule log `main-migration-20261109/rules/analyzer.log`, filtered
  copy `mm-rules-filtered.log`): `fileToStringUnsafe` ran 1,275,423 runs to a timeout (the per-analysis split of the rest was not
  parsed); 1,800,104 of the 1,800,333 frontier lines in that log say `reports 1`, with two
  exactly period-2 frontier shapes. Together with the three OWASP-entry run-101 launches (2 confirmed from run-3 to
  run-101) these are the only trajectories longer than 11 runs, and none gains a report late.

## 6. Totals per stop test

| test | native HEAD projects (8) | native Nov-12 projects (3) | native rule suite (585) | all 2,083 analyses (incl. non-native) |
|---|---|---|---|---|
| Q2 | fires 6/8 (not conductor), LOSS 0, saves 1,242 s of 5,473 s engine | fires 2/3, LOSS 0, saves 826 s of 2,231 s | 3 early firings, LOSS 0, ~0.1 s | LOSS 0 |
| Q1' | fires 8/8, LOSS 0, saves 3,267 s of 5,473 s | fires 3/3, LOSS 0, saves 1,385 s | 3 early firings (+4 at the natural end), LOSS 0, ~0.2 s | LOSS 0 |
| REPEAT strict | fires 1/8 (OWASP entry, run-13 > cutoff) | never | 2 (file-upload run-9, fileToString run-5), LOSS 0 | LOSS 0 |
| REPEAT loose | OWASP at run-11 (= cutoff), entry run-11 | OWASP at run-11 | 3, LOSS 0 | LOSS 0 |

## 7. Loss that the counts do NOT show: provisional reports

A quiet stop ends with a reason other than `RUN_LIMIT`, and `ReportBuilder.build` attaches the provisional
(`latestReached`) entries only for `RUN_LIMIT`. Three places where that changes the final report:

1. **Run-101 synthetic fixtures** (`termination-baseline-run101.NbDdcB/native-outcomes.tsv`, end state only):
   `exact-origin nested write` and `protected global cut` end with **confirmed=0 provisional=1**. Confirmed is
   monotone, so it was 0 at every barrier: Q2 and Q1' both fire at run-5 with zero reports, and the one finding the
   fixture reports today exists only as a provisional entry. Unless the quiet stop publishes `latestReached` the way
   `RUN_LIMIT` does, these two fixtures go from 1 finding to 0. This is the only concrete counterexample to a
   "confirmed-count-only" quiet stop, and it is by deduction from the end state (per-run lines were not logged).
   The report also lists "Intrinsic MAY pass: RUN_LIMIT with one provisional observation".
2. **Stirling-PDF**: no native launch completes run-11 (all three time out inside it; final 32/0). Four prototype
   launches that do complete it (R36, R36-cost, R13-loop-prefix-c5, R41-cost; NOT native) end `RUN_LIMIT` with
   confirmed=32 **provisional=2**. A Q2 stop at run-9 or Q1' stop at run-7 would report 32, not 34, unless it also
   publishes provisional entries; whether the same two IDs are already reached at run-7/9 is not logged.
3. All other analyses read have provisional=0 at the end (OWASP, OWASP entry, both capped rule cases).

## 8. What is missing, and what to log to finish the evaluation

- **Per-run provisional data.** Log at every forward barrier the size (and ideally an order-independent hash) of
  `latestReached`, and of `latestReached - entries`. Needed to say what a quiet stop would publish.
- **NORMAL-record novelty**, the second half of the real Q1. Nothing in the logs gives it. Log per forward barrier:
  number of NORMAL DATA rows and NORMAL Target rows in `NormalTargetStore`, the number added at this barrier, and a
  set hash. (The perf report states "151 NORMAL DATA / 25 NORMAL Target rows stable from run-5" for file-upload only.)
- **State identity for REPEAT.** The frontier numbers are a weak proxy: `record crossings` drifts while the demand
  is period-2, and equal counts do not prove equal demand sets. Log a hash of the handoff demand rows, the seeds and
  the Target pairs per barrier.
- **Synthetic fixtures / run-101 unit tests**: only end-state lines exist (`TERMINATION_BASELINE … confirmed= provisional=`,
  `AnalysisEnd(...) findings=`). No per-run confirmed counts for the ~60 fixture outcomes, including the ones with a
  natural stop at run-5/7/9 (`RecursiveWrapper` 5/5/7/9, `BranchingWriteRead` 7/5/7, `WordChunk` 5/7, `LoopWriteRead` 5).
  Needed: `Frontier.log()` at INFO in those tests, or dump `driver.frontiers.map { it.run to it.reportedSinks }`.
- **Rule suite on the current native HEAD** (758ad99ff): not on disk. Nov-12 472288cf is the latest native suite log.
- **Report identities across launches**: within a launch the count is exact; across launches (e.g. Stirling 32 in six
  launches) only counts were compared here; SARIF identity comparison was not done.
- **Completed tails for conductor and Stirling**: every native launch times out (run-8 / run-11), so "final" there is
  "final at timeout". Whether a report would appear after run-7 (conductor) or run-11 (Stirling) with more budget is
  unknown; conductor has only one quiet forward run (run-7) in evidence.
- **thingsboard**: OOM in run-1, no data.

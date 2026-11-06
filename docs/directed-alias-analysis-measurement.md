# Directed local alias analysis — measurement against the DSU

This document gives the measurement of the directed alias analysis (`docs/directed-alias-analysis-impl.md`, "IMPL") against the current alias analysis of main (the DSU). It follows the plan of `docs/directed-alias-analysis-design.md` §11.2 and §11.3 ("design"). It gives facts only. It makes no proposal.

Modes (IMPL §8): `DSU` gives the answers of main. `SHADOW` runs both backends, gives the DSU answers to the taint analysis and compares the two answers of each query. `DIRECTED` gives the directed answers to the taint analysis. K is the symbolic depth, D is the maximum number of accessors of an answer path.

## 1. Setup and reproduction

### 1.1 Setup

| Item | Value |
|---|---|
| Date | 2026-11-06 |
| Measurement jar | branch `saloed/directed-alias-impl` at `8ebf62f53` (after the fix wave of the final review), `opentaint-project-analyzer.jar` sha256 `b13e8cacf974c273...` |
| Pre-fix jar | the same branch at `3fa7a880c` (before the fix wave). Its runs are kept as "pre-fix" data (section 1.3). |
| Baseline jar | branch base `e7a0fe803` (the analyzer of main, no mode option), sha256 `dd363802deb650e9...` |
| Defaults | K = 7, D = 6, inter-procedural alias depth 1, alias time limit 10 s |
| JVM | Temurin 21.0.11 (`~/.opentaint/install/jre`) for the projects; OpenJDK 21 for dataflowbench |
| Machine | 20 cores, 62 GB RAM. Other sessions used the machine at the same time (Gradle test runs of another worktree). The 1-minute load average was 3-6 during the tms timing rounds and 7-21 during the thingsboard and Conductor runs. Each `result.txt` records the load. |
| Projects | tms (`opentaint-test-tms`, repo `9510b7cc`), thingsboard (`opentaint-test-thingsboard`, `b31176433e`), Conductor (`opentaint-test-conductor`, `c466eaf70`) |

Analyzer flags of every project run (the flags of the Go CLI, copied from its command builder `cli/cmd/command_builder.go`):

```
java -Xmx<heap> -Dorg.opentaint.ir.impl.storage.defaultBatchSize=2000 -Djdk.util.jar.enableMultiRelease=false \
  -jar <jar> --project <proj>/project.yaml --output-dir <out> --logs-file <out>/analyzer.log --sarif-file-name out.sarif \
  --sarif-tool-version custom --sarif-tool-semantic-version dev --sarif-uri-base <proj>/sources/ --sarif-semgrep-style-id \
  --sarif-generate-fingerprint --verbosity=debug --semgrep-rule-severity=warning --semgrep-rule-severity=error \
  --ifds-analysis-timeout=<800 for tms, 1080 for thingsboard and Conductor> \
  --semgrep-rule-set rules/ruleset [project flags] [--experimental-alias-analysis-mode=dsu|shadow|directed] \
  [--experimental-alias-stats] [--experimental-alias-symbolic-depth=K --experimental-alias-max-accessors=D]
```

- Conductor project flags (the CI `scan-flags` of `opentaint-test/projects/repos.yaml`): `--semgrep-rule-set opentaint-test-conductor/rules --passthrough-approximations opentaint-test-conductor/passthrough --java-dataflow-approximations opentaint-test-conductor/dataflow-compiled`.
- thingsboard has no `scan-flags` in `repos.yaml` and no rule directory. Its runs use the bundled ruleset only.
- The bundled ruleset is `rules/ruleset` of the branch (the CI builds the analyzer and the rules from one checkout).
- In `DSU` mode the statistics are off by default since the fix wave (no cost on the default path). The DSU timing runs do not use `--experimental-alias-stats`. One extra DSU run of each project uses it and gives the DSU volume baseline.

### 1.2 How to reproduce each number

The scripts are in the scratch directory `<scratch>/meas/bin/`. `<scratch>` is the session scratch directory of the measurement (`/tmp/claude-1002/-drive-testcomp-opentaint-go-rules-opentaint-w4/8ce2436d-4e75-4cd3-be3a-d8d5973c2b63/scratchpad`). The raw data is not committed.

1. Build the jar in a separate worktree: `git worktree add <scratch>/meas/final2 8ebf62f53`, then `cd <that>/core && ./gradlew :projectAnalyzerJar --offline -x :opentaint-ir:go:buildGoServer`.
2. Project run: `run.sh <name> <tms|tb|cond> <jar> <dsu|shadow|directed|none> <heap> <limit-s> [extra flags]`. The script writes `runs/<name>/{cmd.txt, stdout.log, out.sarif, rss.txt, result.txt}`. It polls `VmHWM` of the analyzer process each second (peak RSS), records the wall time (resolution about 1 s), and sends `SIGTERM` 45 s after the first `OutOfMemoryError` line or at the time limit, then `SIGKILL` 90 s later. `SIGTERM` lets the shutdown hook print the `ALIAS-STATS` block. With `HISTO=1` it takes a heap histogram (`jcmd GC.class_histogram`) at the first memory guard line.
3. Statistics: `extract.py runs/<name>` reads the log and writes `stats.json`: IFDS time (from `Start IFDS analysis` to `Finish IFDS analysis`, or to the last log line), the last `Progress: N/M` value of each IFDS phase, memory guard lines (`Running low on memory`), `OutOfMemoryError` lines, `exceed` lines (alias time-outs), and the `ALIAS-STATS` blocks (a run that the memory guard stops prints one block at the end and one more block from the shutdown hook; the script adds them). `table.py <names>` prints the rows of section 2.
4. Findings: `sarifdiff.py A.sarif B.sarif` compares on `(ruleId, message, locations, codeFlows)`, then on `(ruleId, path, startLine, startColumn)`, and counts the findings with a changed code-flow count.
5. Diff lines: `diffparse.py runs/<name>/stdout.log` parses the `ALIAS-SHADOW-DIFF` lines and tags each line by the shape of the extra answer items. `diffshow.py <log>.diff.json <tag> <n>` prints lines in a short form.
6. dataflowbench: `run-dfb.sh <java|kotlin> <dsu|directed|shadow>`. The harness and its toolchain are in `<scratch>/meas/dfb` (recipe `dfb/RECIPE.md`, harness `36d93cc32`, pinned release `analyzer/2026.09.04.c51dc3e`). The wrapper `dfb/log-wrapper.sh` is the `--java` of the harness. It runs the measurement jar in place of the pinned jar, adds the mode flag, `--verbosity=info` and a log file for each case. The harness still witnesses the pinned jar digest, so the `tool_build_identity` of these reports does not name the jar that ran. `dfbcmp.py <lang>` compares the per-case outcomes.
7. Test suites: `run-tests.sh <jvm|ql> SHADOW` runs the Gradle suite in the measurement worktree with `-PaliasAnalysisMode=SHADOW`. `teststats.py runs/tests-<suite>-SHADOW` adds the `ALIAS-STATS` blocks and collects the diff lines from the Gradle log and the result XML files.

### 1.3 Pre-fix runs

The first runs used the jar at `3fa7a880c`. The final review then changed three items that affect the measurement: the per-query statistics on the default DSU path, the size of the diff lines, and the cost of the `nullOnly` statistic in the directed query. It also changed one directed answer rule (a resolved call with an override that has no body now applies the unresolved-call rule too). All numbers in this document come from the jar at `8ebf62f53`, except where the text says "pre-fix". The pre-fix DSU runs (tms 3 rounds, thingsboard, Conductor) give the same findings as the final DSU runs on both keys.

## 2. Summary

Heap limit: tms DSU 8 GB, all other project runs 16 GB. "Events" are the IFDS events of the first IFDS phase before the stop (the last `Progress: N/M` value). The DSU volume comes from the run with `--experimental-alias-stats`. The SHADOW volume is for the queries before the stop only.

| Input | Mode | Completes | Wall / IFDS time | Peak RSS | Events (phase 1) | Findings | Stop point |
|---|---|---|---|---|---|---|---|
| tms | baseline (main) | yes | 37.1 s / 17.3 s (median of 3) | 4.6-5.1 GB | 17 502-17 619 | 153 | — |
| tms | DSU | yes | 38.1 s / 17.5 s (median of 3) | 4.6-4.9 GB | 17 567-17 616 | 153, equal to main | — |
| tms | SHADOW | no | 66.6 s / 46.2 s | 16.8 GB | 779 | 0 (partial) | guard at IFDS +9.4 s, `OutOfMemoryError` at +45.7 s, guard stop (exit 253) |
| tms | DIRECTED | no | 78.4 s / 59.7 s | 16.8 GB | 839 | none (no SARIF) | guard at +8.4 s, `OutOfMemoryError` at +15.3 s, analyzer hangs, `SIGTERM` |
| tms | SHADOW, K = 0, D = 0 | yes | 74.3 s / 53.7 s | 16.8 GB | 17 462 | 153, equal to DSU | — |
| thingsboard | baseline (main) | yes | 264.1 s / 214.6 s (load 15) | 17.0 GB | 8 630 024 | 14 | — |
| thingsboard | DSU | yes | 187.8 s / 151.8 s | 16.7 GB | 7 204 687 | 14, equal to main | — |
| thingsboard | SHADOW | no | 148.5 s / 103.3 s | 17.1 GB | 3 288 | 1 (partial) | guard at IFDS +36.1 s, guard stop (exit 253) |
| thingsboard | DIRECTED | no | 159.9 s / 119.2 s | 17.0 GB | 3 407 | none | guard at +36.0 s, `OutOfMemoryError` at +73.7 s, `SIGTERM` |
| Conductor | baseline (main) | yes | 101.6 s / 52.9 s (load 12) | 11.4 GB | 83 960 | 6 | — |
| Conductor | DSU | yes | 78.3 s / 37.4 s | 12.3 GB | 84 066 | 6, equal to main | — |
| Conductor | SHADOW | no | 205.4 s / 156.4 s | 17.1 GB | 32 215 | 0 (partial) | guard at IFDS +54.4 s, guard stop (exit 253) |
| Conductor | DIRECTED | no | 251.3 s / 200.8 s | 17.1 GB | 35 179 | none | guard at +55.5 s, `OutOfMemoryError` at +155.9 s, `SIGTERM` |
| dataflowbench Java (70) | DSU / SHADOW / DIRECTED | yes | 741 / 425 / 502 s for the kernel | — | — | 61/70 in each mode, equal per case to the pinned release | — |
| dataflowbench Kotlin (70) | DSU / SHADOW / DIRECTED | yes | 587 / 533 / 522 s for the kernel | — | — | 60/70 in each mode, equal per case to the pinned release | — |

The baseline and DSU rows of thingsboard and Conductor are single runs at a different machine load. Their times are not an A/B comparison. Only tms has the 3 alternating rounds of design §11.3 step 6.

Alias statistics (all queries of the run; "paths" = `AliasApInfo` items; "max" = the largest answer of one query; "longest" = the most accessors of one path):

| Input | Mode | Methods | Queries | DSU paths | Directed paths | DSU / directed max | DSU / directed longest | notSubset | precisionGain | equal | Directed time-outs / cancelled | Alias time DSU / directed | Node count max | Table content max (ints) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| tms | DSU (stats run) | 1 448 | 24 499 | 110 274 | — | 126 / — | 12 / — | — | — | — | — | 6.3 s / — | — | — |
| tms | SHADOW | 87 | 658 | 1 376 | 78 756 | 29 / 17 692 | 6 / 7 | 132 | 62 | 479 | 0 / 2 | 5.6 s / 32.1 s | 345 557 | 486 133 544 |
| tms | DIRECTED | 96 | 552 | — | 1 797 445 | — / 542 349 | — / 7 | — | — | — | 0 / 0 (3 failures) | — / 101.3 s | 345 557 | 486 133 544 |
| tms | SHADOW K0 D0 | 1 448 | 24 152 | 110 274 | 36 641 (no accessors) | 126 / 37 | 12 / 0 | 8 127 | 12 623 | 8 942 | 1 / 0 | 8.3 s / 29.4 s | 67 153 | 14 903 792 |
| thingsboard | DSU (stats run) | 21 897 | 136 662 | 229 416 | — | 864 / — | 13 / — | — | — | — | — | 48.5 s / — | — | — |
| thingsboard | SHADOW | 507 | 3 470 | 5 252 | 13 116 061 | 39 / 1 225 974 | 7 / 6 | 787 | 207 | 2 291 | 1 / 1 | 5.5 s / 115.7 s | 8 199 | 2 149 097 |
| thingsboard | DIRECTED | 509 | 3 511 | — | 18 678 160 | — / 6 788 581 | — / 6 | — | — | — | 1 / 0 (1 failure) | — / 86.1 s | 8 199 | 2 149 097 |
| Conductor | DSU (stats run) | 6 425 | 43 870 | 81 050 | — | 98 / — | 12 / — | — | — | — | — | 15.7 s / — | — | — |
| Conductor | SHADOW | 3 706 | 23 401 | 39 477 | 18 717 379 | 73 / 1 671 732 | 12 / 7 | 4 295 | 2 448 | 15 165 | 5 / 1 | 22.2 s / 82.1 s | 159 592 | 527 455 996 |
| Conductor | DIRECTED | 3 884 | 24 880 | — | 24 763 077 | — / 2 732 379 | — / 7 | — | — | — | 5 / 3 | — / 99.5 s | 159 592 | 527 455 996 |

Other directed counters of the failed runs: `callFallbacks` 0 (tms, thingsboard) and 7 (Conductor); `headIterationsMax` 22 (tms SHADOW), 34 (thingsboard), 173 (Conductor); `retainedEntriesMax` 249 788 (tms), 79 662 (thingsboard), 1 423 648 (Conductor); call closure size max 6 507 / 3 278 / 15 263. The largest directed alias time of one method is 96.4 s (thingsboard SHADOW, a cancelled method) and 45.9 s (tms DIRECTED).

## 3. Volume and precision

### 3.1 V1 (SHADOW)

The SHADOW runs with the default K = 7 and D = 6 stop on all three projects before the end of the first IFDS phase. So V1 has only the queries before the stop. All of them are `BEFORE` queries, except 7 `AFTER` queries on Conductor.

| Project | Queries (DSU / directed) | Paths DSU → directed | Accessors DSU → directed | Answer size p50 / p99 / max, DSU | Same, directed | Mean answer size DSU → directed | `nullOnlyPaths` (share of directed paths) |
|---|---|---|---|---|---|---|---|
| tms | 667 / 658 | 1 376 → 78 756 (57x) | 3 905 → 410 738 | 1 / 22 / 29 | 1 / 2 816 / 17 692 | 2.5 → 120 | 179 (0.2 %) |
| thingsboard | 3 496 / 3 470 | 5 252 → 13 116 061 (2 497x) | 9 723 → 76 370 489 | 1 / 20 / 39 | 1 / 960 / 1 225 974 | 1.7 → 3 780 | 29 (0.0002 %) |
| Conductor | 23 567 / 23 394 | 39 473 → 18 717 375 (474x) | 90 158 → 108 204 678 | 1 / 21 / 73 | 1 / 2 816 / 1 671 732 | 1.9 → 800 | 101 839 (0.5 %) |

Per method (answers of all queries of one method, p50 / p99 / max): tms DSU 4 / 384 / 404, directed 4 / 45 056 / 45 221; thingsboard DSU 4 / 104 / 265, directed 4 / 294 912 / 3 895 806; Conductor DSU 2 / 144 / 1 170, directed 2 / 32 768 / 3 343 471.

The median query has the same size in both backends. A small set of queries has very large directed answers. The `<rule-storage>` cells of the pass-through models make them (section 3.4).

Per-query comparison (sets; `null` = empty set): on tms 479 of 658 queries are equal, 132 are `notSubset` (the directed answer has an item that the DSU answer does not have), 62 are `precisionGain` (the DSU answer has an item that the directed answer does not have). thingsboard: 2 291 / 787 / 207 of 3 470. Conductor: 15 165 / 4 295 / 2 448 of 23 401. A query can count in both `notSubset` and `precisionGain`.

V1 at K = 0, D = 0 (tms, the only SHADOW run that completes): the directed answers have no accessors (D = 0), so they cannot be compared with the DSU paths for volume. 24 152 queries: 8 942 equal, 8 127 `notSubset`, 12 623 `precisionGain`. `deepOrigins` = 36 614 in 1 383 of 1 447 methods: at K = 0 each field read gives the deep summary of its base, so two reads from one base alias each other. One directed alias time-out (10 s, `FileController#upload`). Findings: 153, equal to the DSU on both keys.

Findings in SHADOW (design §11.2 V1 row "Findings in SHADOW"): only the K = 0 tms run completes, and its findings equal the DSU findings. The default SHADOW runs stop, so their SARIF files are partial (tms 0, thingsboard 1, Conductor 0 findings).

### 3.2 V2 (DIRECTED)

DIRECTED stops with `OutOfMemoryError` on all three projects at 16 GB. The IFDS events before the stop are 839 on tms (DSU: 17 572 in phase 1 and 213 065 in phase 2), 3 407 on thingsboard (DSU: 7.2M and 2.45M) and 35 179 on Conductor (DSU: 84 066 and 534 519). The memory guard fires 8-56 s after the IFDS start. No DIRECTED run writes a SARIF file. Alias time-outs (the 10 s limit): tms 0, thingsboard 1, Conductor 5. The DSU has no alias time-out on any project.

### 3.3 Where the memory goes

| Run | Evidence | Main memory user |
|---|---|---|
| tms SHADOW / DIRECTED | `contentSizeMax` 486M ints (1.9 GB) for one method; `contentSize` sum 1.3G ints (5.3 GB) over 84 finished methods; D1 heap histograms (`int[]` 7.5 GB at 8 GB) | node tables of the string-building methods (`toString`, javac concatenation) |
| thingsboard SHADOW | heap histogram at the memory guard (`runs/tb-shadow-histo/histo-guard.txt`, live objects): `int[]` 10.4 GB in 0.8M arrays; 59.1M `AliasAccessor$Field` (1.4 GB), 10.1M `AliasApInfo` (0.24 GB), 11.8M `ArrayList` (0.28 GB), `Object[]` 0.5 GB; IFDS `LongMapEntry` and 23-tree nodes about 1 GB | `int[]` (probably the node tables of the methods in flight: the finished methods hold only 11M ints = 45 MB), and the cached answer lists (about 2.4 GB for 13M paths) |
| Conductor SHADOW / DIRECTED | `contentSizeMax` 527M ints (2.1 GB) for one method; 18.7M (SHADOW) and 24.8M (DIRECTED) answer paths | node tables and answer lists |

In DIRECTED mode the IFDS gets the large answers. In SHADOW mode it does not, but the facade keeps the directed answers in its answer cache, and the directed query runs in the IFDS worker thread.

### 3.4 The K/D table of the D1 investigation and the root cause

The D1 investigation (pre-fix jar with the K/D options, tms, SHADOW) gave this table. The fix wave does not change the representation or the model rules, so the causes stay. Source: the D1 report of the implementation (`.superpowers/sdd/directed-alias-impl/D1-report.md`, not committed).

| K | D | Heap | Result | Directed methods done | Directed answers |
|---|---|---|---|---|---|
| 7 | 6 | 8 GB | OOM at about 26 s | 82 | 30 258 |
| 7 | 6 | 16 GB | OOM at about 34 s | 111 | 42 979 |
| 7 | 4 | 8 GB | OOM | 75 | 15 835 |
| 7 | 2 | 8 GB | OOM | 64 | 3 104 |
| 5 | 4 | 8 GB | OOM | 95 | 152 788 |
| 5 | 2 | 8 GB | guard + OOM | 75 | 50 767 |
| 3 | 2 | 8 GB | guard stop | 144 | 257 153 |
| 2 | 1 | 8 GB | guard stop | 403 | 81 258 |
| 1 | 1 | 8 GB | guard stop (`long[]` 5.6 GB) | 473 | 139 034 |
| 0 | 0 | 8 GB | guard stop (`long[]` 6.0 GB) | 1 361 | 28 362 |
| 0 | 0 | 16 GB | completes (this measurement) | 1 448 | 47 175 |

Root cause (D1, no engine defect): the rules make this growth, and the IMPL data structures keep it.

1. Pass-through models with many read cells. `toString()` has 32 models; 24-30 of them read `this.<C>.<rule-storage>` for one class C each. `StringBuilder#append` reads 2 cells. A model read of an unwritten cell gives each receiver origin a new default child. The append chain feeds the set back into the receiver, so a base gets up to Σ_{d≤K} |cells|^d origins.
2. The load fold of IMPL §4.2 interns each intermediate union: Θ(m²) node content for a base of m origins.
3. The weak model stores make m different heap nodes, and the query reverse indexes are cached for each queried state.

The answer volume has a second source: the default parents of the deep summary of each depth-K origin (the Task 5 universe ruling). So `var.c1...cD` aliases it for each cell sequence over the model cells. At K ≥ 3 the node tables fill the heap; at K ≤ 1 the reverse indexes do. A small K moves the deep summary inside D and makes the answers larger. A large K makes the tables larger.

## 4. Findings-level differences

### 4.1 Projects

DSU against main (baseline jar): equal on both keys on tms (3 rounds, 153 findings, 75 code flows), thingsboard (14 findings, 5 code flows) and Conductor (6 findings, 17 code flows). The DSU runs with `--experimental-alias-stats` give the same findings. The pre-fix DSU runs give the same findings. No code-flow count changes.

DIRECTED: no comparison is possible. No DIRECTED run on a project writes a SARIF file. SHADOW at K = 0, D = 0 on tms: 153 findings, equal to the DSU.

### 4.2 dataflowbench

| Kernel | Pinned release `c51dc3e` | Measurement jar, DSU | SHADOW | DIRECTED | Changed cases |
|---|---|---|---|---|---|
| Java | 61/70 | 61/70 | 61/70 | 61/70 | none |
| Kotlin | 60/70 | 60/70 | 60/70 | 60/70 | none |

Each case outcome (`reached` / `not-reached`) is equal in all modes and equal to the pinned release. No case has a `runner-error`. So no changed case needs a classification of its alias query. The design gate "Java ≥ 49/58, Kotlin ≥ 50/58" (§11.2) names the old kernel size; the kernels now have 70 cases each.

Alias statistics of the Java kernel (70 analyzer runs, 95 methods with a query): SHADOW 299 queries, 126 equal, 130 both empty, 31 `notSubset`, 24 `precisionGain`; DSU 344 paths (max 23, longest 6), directed 251 paths (max 32, longest 3). The directed answers are smaller on this kernel. Kotlin kernel (70 analyzer runs, 135 methods): SHADOW 447 queries, 230 equal, 91 both empty, 67 `notSubset`, 18 `precisionGain`; DSU 309 paths (max 21, longest 6), directed 267 paths (max 17, longest 3). Of the 65 printed Kotlin lines, 49 add only a string constant base (a local that holds the literal `"tainted"` gets the constant item: interned constant, design §7.5), 6 have model cells, 2 add an allocation item, and 8 have other paths (the 3 sampled lines have the `Iterable.Element` / `Iterator.Element` shape below).

Classes of the Java `notSubset` lines (25 of 31 lines printed):

| Shape | Lines | Example | Class |
|---|---|---|---|
| Model cells with `<rule-storage>` (`Bindings.<rule-storage>` next to `MapValue`, `Map$Entry.<rule-storage>`) | 14 | `DispatchTable*#run`, `MapIteration*#run` | directed pass-through models (PL6) that read several model cells; not in the design list; the small form of the D1 shape |
| A second synthetic cell for one container (`Iterable.Element` next to `Iterator.Element`) | 8 | `CallbackRegistration*$Registry#fire`, `MapIteration*#run` | the same (model cells) |
| An extra allocation item of an equal constant | 3 | `ComputedPropertyNegative#run`, allocation items 4 and 8 | constant shared by value (IMPL §1.5 "Box and class constants", design §7.5) |

### 4.3 Classification of the project diff lines

The process prints at most 300 diff lines; a line has at most 20 items of each list and 8 000 characters. A tag uses the printed items only. "Model cells" means that an extra path has a `<rule-storage>` cell of a pass-through model.

| Tag of the extra items (first match in this order) | tms (132 lines) | thingsboard (300) | Conductor (300) |
|---|---|---|---|
| model cells | 109 | 65 | 122 |
| string constant base (`const<String>(...)`) | 0 | 202 | 127 |
| allocation items | 0 | 5 | 0 |
| DSU answer empty | 5 | 16 | 13 |
| extra not printed (line cut) | 3 | 5 | 21 |
| other paths | 15 | 7 | 17 |

Hand-checked sample:

| Project, method, query | DSU | Directed extra | Class |
|---|---|---|---|
| tms `ChannelServiceImpl#createAsSuper`, `user` after `channelRepository.saveAndFlush(channel)` (4 lines) | `this.userRepository.__repo__` | `channel2.owner`, `this.channelRepository.__repo__.owner` | U2: the DSU drops `channel.owner` at the unresolved call |
| tms `CustomApplicationRunner#initProjectAndLanguage` (6 lines) | `language` and `project` without the repository paths | `languageRepository.__repo__.creator`, `project.language` | U2 (repository `save` calls) |
| tms `DataInitConfig#init`, `mailSettings` (4 lines) | empty | `SettingRepository.__repo__.content` | U2: the call `mailSettings.get(...)` drops the alias |
| tms `GroupMember#toString` and 3 other `toString` methods, inst 14 | the builder chain over `CharSequence.<rule-storage>` | `this.<field>.<C>.<rule-storage>` for each field and model cell | model cells (D1 shape) |
| tms `ChatMsgImpl#put` (8 lines) | `var.MapValue^k` | `MapValue`, `Bindings.<rule-storage>`, `LRUMap.<rule-storage>`, `headerValue`, `headerValues` paths | model cells (D1 shape) |
| tms `CustomMailSender#sendTextTo` | `formatText.content^k` | `vals[*].content^k` (inlined `StringUtil.replace`, `String.valueOf(vals[i])`) | U2: in the loop of the inlined `StringUtil.replace`, JIR copies `vals` to a local (`%2 = vals`). So the unresolved call `String.valueOf(%2[i - 1])` removes the heap alias `vals[*]` before the model merges it (shape of probe row 24). A scratch sample gives the same difference with the loop at depth 0, and no difference without the loop. The directed answer is correct. |
| thingsboard `CirclePerimeterDefinition#toString` | `this.latitude` | `const<String>(CirclePerimeterDefinition(latitude=)` | interned constant (design §7.5) |
| thingsboard `MqttSslClient#main` | allocation item 22 | allocation item 28 | class constant `MqttSslClient.class` at two statements (IMPL §1.5) |
| thingsboard `JacksonUtil#addKvEntry` | `var[*]^k` | `kvEntry.value` | probably U2 (`isPresent()` on the inlined optional); not checked in the bytecode |
| tms K = 0 run, `ChatMsgImpl#put`, two locals | `arg0.id`, `arg0.openEdit` | `var(9)` for both | probably the K-limit: at K = 0 a field read gives the deep summary of its base, so the reads share an origin; not checked in the bytecode |

No sampled line shows a wrong answer. Each sampled line has a class. No line of the sample is U1 or U4. The tags "model cells" and "string constant" cover 83 % (tms, Conductor) and 89 % (thingsboard) of the lines.

## 5. Behaviour changes in the test suites

### 5.1 DIRECTED mode (from the Task 10 run at `3fa7a880c`)

G-JVM has 33 failures in DIRECTED mode, G-QL 2, G-ROOT 0 outside the 52 Go baseline failures. Each G-JVM failure is a test that asserts the DSU answer (a `today` probe or a DSU sample test). The `directed` twin of each test passes, and the engine answer equals the naive concept on each probe. Grouped by the rows of IMPL §1.1:

| IMPL row | Tests | Probe rows |
|---|---|---|
| Join (non-transitive answers) | 7 | 1, 2, 3, 4, 8, 10, 37 |
| Unresolved call (no alias drop, D2) | 6 | 21, 22, 24, 25, 27, `test external call invalidates heap aliases` |
| Strong update (rule of §S 5.3, U1 fixed) | 4 | 13, 14, 15, 16 |
| Recency | 4 | 17, 18, 19, 20 |
| Strong update on entry roots (D1 decision) | 2 | 30, `test swap fields` |
| Field read (value read rule, U4 fixed) | 2 | 35, 36 |
| Answers: backward search, complete to depth D | 3 | 9 (heap query form, spec §5.7), 41 and 42 (deep summary element paths, Task 8 F1) |
| Pass-through models are directed (PL6) | 1 | 11 |
| Loop at the first instruction | 1 | T0 `loopAtFirstInstruction` |
| `null` against empty list (IMPL §1.5) | 1 | 12 |
| Array element query (I4, IMPL §6.3) | 2 | T0 vararg string and boxed constants |

G-QL (2): `StrConcatTest` `test rule with ellipsis concat` and `test rule with multiple metavar concat` stop at the IFDS time limit of the test. Their `findAlias` answers have up to 2 114 360 paths. This is the D1 shape (model cells), not a wrong answer.

### 5.2 SHADOW mode (this measurement, jar `8ebf62f53`)

| Suite | Tests | Skipped | Failed | Time |
|---|---|---|---|---|
| jvm-dataflow | 785 | 29 | 0 | 108 s |
| querylang | 207 | 23 | 1 (`StrConcatTest` `test rule with multiple metavar concat`, 189 s, the IFDS time limit) | 293 s |

Before the fix wave both `StrConcatTest` tests failed in SHADOW mode. Now `test rule with ellipsis concat` passes in 20.9 s, because the `nullOnly` statistic no longer re-reads each answer path.

querylang SHADOW statistics (one summary from the shutdown hook of the test JVM): 1 112 queries; DSU 2 078 paths (max 28, longest 6); directed 9 466 508 paths (max 1 552 720, longest 6); 517 equal, 122 `notSubset`, 51 `precisionGain`, 465 one side empty; no directed failure or time-out; DSU alias time 1.2 s, directed 4.0 s; `contentSizeMax` 500 634 768 ints; 4 call fallbacks. Of the 122 diff lines, 25 are in the test output: 13 have model cells, 10 have a string constant base and no model cell, 2 have other paths. All 25 are in the string-concatenation samples or `custom.sampleWithAlias`.

jvm-dataflow SHADOW statistics: the test runtime of this module has no SLF4J provider (the log says "No SLF4J providers were found"), so the summary of the shutdown hook and the diff lines are not printed. The only numbers are the ones that `AliasShadowModeTest` prints for its three sample classes (depth 0 and 1, every local of every call): 816 queries, 293 equal, 318 `notSubset`, 163 `precisionGain`; DSU 2 161 answers, directed 3 122. Of the `notSubset` queries, 222 are `ARRAY_ELEMENT` queries (I4: the directed element query gives the element items; 266 of the 272 element queries have an empty answer on one side).

## 6. Conclusions

Gates of design §11.2 (the user sets the thresholds; this table gives the measured state):

| Gate | State | Fact |
|---|---|---|
| V1 can be measured on the three projects | not met | SHADOW at K = 7, D = 6 stops on tms, thingsboard and Conductor at 16 GB (guard or `OutOfMemoryError`). V1 has only the first 658 / 3 470 / 23 401 queries. |
| V1 volume | measured, partial | directed paths 57x (tms), 2 497x (thingsboard), 474x (Conductor) of the DSU paths for the same queries; max answer 17 692 / 1 225 974 / 1 671 732 against 29 / 39 / 73 |
| V1 unexplained `notSubset` queries = 0 | not measurable | each sampled line has a class (`CustomMailSender#sendTextTo` is U2: the loop copies `vals` to a local, so the call `String.valueOf(vals[i - 1])` removes the alias `vals[*]`); only 300 lines of each run are printed, and only a sample is checked by hand |
| V1 precision (mean and p99 of the answer size) better than the DSU | not met | mean 2.5 → 120, 1.7 → 3 780, 1.9 → 800; p99 22 → 2 816, 20 → 960, 21 → 2 816. On the dataflowbench kernels the directed answers are smaller (Java 344 → 251, Kotlin 309 → 267 paths). |
| V1 findings in SHADOW equal to DSU | met only at K = 0, D = 0 on tms | the default SHADOW runs do not complete |
| V2 (IFDS events, peak heap, guard, OOM in DIRECTED) | not met | DIRECTED gets 839 / 3 407 / 35 179 events before `OutOfMemoryError`, against 230 k / 9.7M / 619 k for the DSU |
| Alias time-outs | not met | DIRECTED: tms 0, thingsboard 1, Conductor 5; DSU 0 |
| tms wall time, DIRECTED against DSU | not measurable | DIRECTED does not complete. DSU against main: 38.1 s against 37.1 s wall, 17.5 s against 17.3 s IFDS (median of 3; the wall time has 1 s resolution) |
| Table content below `maxTableContent` | no cap in IMPL | `contentSizeMax` 486M (tms), 2.1M (thingsboard), 527M ints (Conductor) |
| dataflowbench at or above the baseline | met | Java 61/70 and Kotlin 60/70 in DSU, SHADOW and DIRECTED mode; no case changes against the pinned release |
| No unexplained lost finding | not measurable | no DIRECTED SARIF on a project |
| DSU mode gives the answers of main | met | equal findings on tms, thingsboard and Conductor |

What blocks DIRECTED (facts only):

1. The answer volume (decision D11). The large answers come from the pass-through models with many `<rule-storage>` cells and from the default parents of the deep summary of each depth-K origin. On thingsboard one query has 6.8M paths in DIRECTED mode. At the memory guard of the thingsboard SHADOW run, the answer lists hold about 2.4 GB and the `int[]` arrays hold 10.4 GB (probably the node tables of the methods in flight; the histogram does not name the owner); the finished methods hold only 45 MB of node content.
2. The representation (D1): the load fold of IMPL §4.2 (Θ(m²) intermediate nodes), the heap content of the weak model stores (one node for each origin), and the cached query reverse indexes. They fill the heap on tms and Conductor (up to 2.1 GB of node content for one method).
3. No checkpoint in loads, weak stores, models and queries (IMPL §5.2 has none). One directed method runs 96 s before its cancellation; the 10 s alias limit does not stop the growth in time.
4. In SHADOW mode the directed query runs in the IFDS worker thread and its answers stay in the answer cache. So SHADOW also fails where DIRECTED fails, and the V1 statistics stop at the same point.

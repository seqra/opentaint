# Loop-block campaign status: interim quality failure

Date: 2 November 2026. **INTERIM — QUALITY FAILED — NOT FINAL PERFORMANCE.**
Measured revision: `6052e2ea2d400a7f1f47c0f5fe4497bae23e2ace`.

This campaign does not pass the finding gate. OWASP completes and accepts **run-5**, but loses 18 saved baseline identities. Conductor fails in **run-2**, after complete and accepted **run-1**. Thingsboard is stopped before run-1. Stirling-PDF does not start. This is not a complete four-project measurement or a final result for the iteration.

The [compact evidence](data/bidirectional-loop-block-campaign-status-20261102.json) contains all 18 identities, exact timing markers, selected CPU/allocation/GC data, source and capture hashes, cleanup records, and native failure/control receipts. No analyzer, test, or profile capture was started to write this report.

## 1. Fixed inputs and current status

The finding baseline remains `f945f92c5ae554ff4f5fc7696ee5a269210478bb`. Its saved reports were reused. It was not run again. The immediate control is `86ad3b70b5b834d60bc0fe96a91091174265c827`. The test-input revision is `bbdbcc5fd35d976d93348760ea60561e4670f68c`.

The selected configuration is FULL, a 16 GiB heap, field limits **1,1,2,3,...**, statics enabled, and aliases enabled. The IFDS budgets are 1,000 seconds for OWASP and 1,080 seconds for each real project. Each outer command budget is 1,200 seconds. The commands use `runProjectAnalyzer` directly. No alternate configuration is included here.

| Project | Command or phase result | Latest reached / complete / accepted | Saved f945 / current identities |
|---|---|---|---:|
| OWASP | Command OK; engine COMPLETE; finding gate failed | run-5 / run-5 / run-5 | 4,112 / 4,094 |
| Conductor | Exception; run-2 FAILED | run-2 / run-1 / run-1 | 7 / 2 |
| Thingsboard | Stopped during setup/prescan; no engine start | None / None / None | 14 / unavailable |
| Stirling-PDF | Not started | None / None / None | 17 / unavailable |

Conductor's two exported identities are its accepted run-1 report. The five absent final-baseline identities are an incomplete-analysis observation. This report does not attribute them to a separate semantic defect. The immediate control has all seven identities at accepted run-5. No empty result is inferred for the two projects with no completed command.

The campaign stop was requested at 20:39:52 UTC after the OWASP comparison. Thingsboard had begun rule loading, but its log has no run-1 marker or completed prescan marker. The command wall times are 200.288 seconds for OWASP and 86.524 seconds for Conductor. These values include work outside the engine.

Four selected JVM call/export source files are byte-identical between 86ad and the measured 6052 revision: `JIRCallPlanBuilder`, `JIRBidiAnalysis`, `JirSarifGenerator`, and `TraceMessageBuilder`. The JSON records both source hashes and equality flags. This is not a claim that the whole analyzer or its runtime inputs are unchanged.

## 2. Official iteration times

All values below are seconds. A successful `engineTime` excludes joined static completion. The marker window from `BIDI_RUN_START` to `BIDI_RUN_END` includes it. Barrier time and full iteration time are separate logged values; small driver overhead also remains. Do not add the same phase twice.

| Project | Run | Status | Logged engine | Joined static | Barrier | Full iteration |
|---|---|---|---:|---:|---:|---:|
| OWASP | run-1 | COMPLETE | 76.195 | 0.489 | 2.112 | 78.893 |
| OWASP | run-2 | COMPLETE | 25.574 | — | 0.196 | 25.808 |
| OWASP | run-3 | COMPLETE | 20.516 | — | 0.195 | 20.727 |
| OWASP | run-4 | COMPLETE | 0.659 | — | 0.001 | 0.664 |
| OWASP | run-5 | COMPLETE | 0.659 | — | 0.024 | 0.687 |
| Conductor | run-1 | COMPLETE | 14.336 | 0.581 | 1.552 | 16.571 |
| Conductor | run-2 | FAILED | 6.314 until failure | — | Unavailable | Unavailable |

The failed Conductor value is elapsed time to an exception. It is not a completed backward-run time and cannot support a speedup ratio. OWASP's measured run-1 exceeds the 60-second engine target. Its later short runs also stop with lost findings, so they do not establish an accepted performance improvement.

OWASP's forward report totals are 3,227 after run-1 and 4,094 after run-3 and run-5. Only final SARIF was saved. These totals do not show which individual identities were present in run-1.

## 3. The 18 OWASP losses

The exact final comparison is the same against f945 and 86ad: **18 missing, no additions**. All 18 are in the earlier failed attempt's set of 51. The current code recovers 33 of that set and loses no additional identity outside it. This is progress in the diagnosis, but it does not pass the fixed finding gate.

All remaining identities use `java/security/insecure-design.yaml:trust-boundary-violation`. Their input families are 14 cookie paths, two header-name paths, and two parameter-name paths. OWASP labels 13 cases as true and five as false. The labels do not remove any of the 18 strict baseline losses.

Each row below names the complete `BenchmarkTestNNNNN#doPost(HttpServletRequest,HttpServletResponse)` sink owner. The JSON also stores its rule ID, full method signature, sink fingerprint, IR index, source path and region.

| Benchmark case | Sink line | Input family | OWASP label |
|---|---:|---|---|
| BenchmarkTest00004 | 68 | Cookies | True |
| BenchmarkTest00097 | 74 | Cookies | False |
| BenchmarkTest00098 | 69 | Cookies | True |
| BenchmarkTest00099 | 79 | Cookies | False |
| BenchmarkTest00991 | 69 | Cookies | True |
| BenchmarkTest00992 | 69 | Cookies | False |
| BenchmarkTest00993 | 69 | Cookies | False |
| BenchmarkTest00994 | 69 | Cookies | True |
| BenchmarkTest00995 | 69 | Cookies | True |
| BenchmarkTest01143 | 64 | Header names | True |
| BenchmarkTest01458 | 63 | Parameter names | True |
| BenchmarkTest01872 | 69 | Cookies | True |
| BenchmarkTest01873 | 69 | Cookies | False |
| BenchmarkTest01874 | 69 | Cookies | True |
| BenchmarkTest01875 | 69 | Cookies | True |
| BenchmarkTest01876 | 69 | Cookies | True |
| BenchmarkTest02016 | 64 | Header names | True |
| BenchmarkTest02352 | 63 | Parameter names | True |

The serialized rule audit and a native counterexample identify the missing mechanism. The source automaton marks the request. Array specialization gives `getCookies` two exact DATA targets, at the result root and at its element. The separate sink-pattern automaton gives `getSession` an unconditional, type-qualified exact SESSION marker. The final sink needs both that receiver marker and a DATA argument. This principal specialization needs no static or global mark.

The [ZERO-control gap report](bidirectional-loop-block-zero-control-gap-20261102.md) contains the code and complete per-run trace. In its native control:

1. Run-1 stores the normal source prefix and the after block's normal `ZERO -> session/SESSION` relation. Its joined sink has a DEMAND data witness and publishes only the nonzero DATA origin as demand.
2. Run-2 visits the real session producer and records its source action. Run-3 has permission for that source. The after block retains `ZERO -> param/DATA`, but its raw source-discharge Target fails the paired DATA exit restriction.
3. Run-3's after-block lookup returns **no ZERO initial** and a **NORMAL DATA initial**. The block reaches the sink with DATA but never executes its independent ZERO producer. A cached whole-block source output cannot insert the session marker before that internal sink.
4. The native run ends at **run-3**, COMPLETE with `NO_DEMAND_EDGE`, and no finding. Identical code with feedback removed reports the finding. Both uniform-source/conditional-session controls also pass.

The four-test native suite has one failure. This proves the block-local coverage gap. It is not an event-by-event proof of the first loss for every project path. The common rule shape supports the project diagnosis. The forward block ZERO policy requires a decision and proof before implementation. No ZERO policy change is implemented by this status report.

## 4. Conductor's separate backward crash

Conductor fails at `MethodBlockRuntime.routeInside` during run-2. A real reverse normal join has two physical predecessors. Both can reach an empty prefix before a second loop. The first arrival uses the empty block's identity adapter. A later arrival for an already admitted ZERO was sent through physical-instruction routing instead. The ownership check correctly rejects a physical predecessor that is not inside that empty block. The later “runner is closed” exception follows cancellation; it is not the first failure.

`LoopBlockEmptyReverseJoinTest` reproduces that stack with two successive loops and both real reverse predecessors. It fails before the correction and passes after the correction. The correction uses the existing empty-block identity adapter for the late arrival too. It does not create a physical instruction, new AP permission, or additional exit target.

The JSON embeds the RED XML, the GREEN test line, and their hashes. The GREEN batch has five tests: the Conductor control passes, while the separate exact-array ZERO-producer control still fails. That batch is not described as a fully green suite. The corrected Conductor path has not been measured again on the project.

## 5. Existing profile and memory evidence

The following values come from the already-derived **continuous JFR** rows for the stopped 6052 attempt. No new recording or heap scan was made for this report. Each end snapshot is a cumulative view of a recording. Those snapshots were kept as separate audits and were **not added** to the continuous rows.

| Project/run | Java samples | Weighted allocation, decimal GB | GC pause overlap, seconds | Largest first-match Java scope |
|---|---:|---:|---:|---|
| OWASP run-1, COMPLETE | 3,620 | 143.346 | 2.702 | Physical calls, 69.0% |
| OWASP run-2, COMPLETE | 906 | 47.224 | 1.075 | Physical calls, 84.5% |
| OWASP run-3, COMPLETE | 912 | 47.751 | 0.469 | Saved block replay, 57.3% |
| OWASP run-4, COMPLETE | 2 | 0.409 | 0 | Too few samples |
| OWASP run-5, COMPLETE | 0 | 0.406 | 0 | No Java samples |
| Conductor run-1, COMPLETE | 3,876 | 42.327 | 1.039 | Physical calls, 67.0% |
| Conductor run-2, FAILED window | 1,572 | 26.200 | 0.712 | Physical calls, 41.5% |

These are diagnostic samples from a rejected campaign. First-match scope tables use an explicit precedence order. Inclusive stack percentages overlap. Neither table is a partition of wall time. Allocation weights estimate churn, not retained objects or exact allocated bytes. GC pauses are wall intervals, not GC CPU.

OWASP's 30-second async profile starts after 60 seconds of run-1 but ends in run-2. It has no per-event timestamps, so it cannot be split into exact per-run shares. In that mixed capture, sampled native GC stacks are 31.9% and sampled compiler stacks are 25.0%. Do not report these as run-1 wall-time percentages. Process CPU includes native GC/JIT work and uses interpolation between roughly one-second resource samples.

Peak command RSS is **17.531 GiB** for OWASP and **17.679 GiB** for Conductor. RSS includes more than the configured heap. No OOM stop, JVM OOM, or new heap snapshot is observed. Thus this attempt provides no retained-heap ownership measurement. It cannot decide whether a later completed thingsboard run would have a memory blow-up.

After derivation and hash verification, 11 raw capture files were removed, freeing 230,497,034 bytes. Logs, SARIF, manifests, resource samples, derived summaries, and raw capture hashes remain. The JSON includes the cleanup receipt and provenance hashes.

## 6. Work still required

The next step is the explicit forward block ZERO decision and its correctness proof. After the correction and native checks, the implementation must be committed and all four fixed project commands must run on that commit. A final report must compare exact findings, completed iteration times, demand frontiers, workload, and any OOM heap evidence. Only then can the measured optimization candidates be ranked for the next iteration.

This interim report does not close `task.md` or replace that final campaign.


## 7. Full native check of the current worktree

The later clean native check covers the uncommitted Conductor empty-block correction and the new ZERO counterexample. It does not change the measured 6052 project results above.

| Source state | Common tests | JVM tests | Result |
|---|---:|---:|---|
| Committed 6052 before the project campaign | 2,372 pass | 453 pass | Previous accepted native PASS receipt |
| Current worktree, with the Conductor correction and new controls | 2,377: 2,376 pass, one fail | 453 pass | Known open ZERO design failure |

The full current-worktree command completes with exit code 1. Every previously accepted common and JVM test passes, with the same class test counts. There are no errors or skipped tests. The new Conductor control passes. Three of the four trust-boundary controls pass. The only failure is the exact-array, independent ZERO-producer loop case. It still reaches, completes, and accepts **run-3**, then stops with `NO_DEMAND_EDGE` and no finding.

The [new known-failure receipt](data/bidirectional-loop-block-known-zero-gap-native-20261102.json) stores the exact command, source hashes, per-class results, failure trace, and log hash. It is a separate receipt. The prior 6052 PASS receipt and its pinned inputs remain unchanged. This check confirms that the Conductor correction does not break the old native controls; it does not pass the ZERO counterexample, approve a ZERO policy, complete the project campaign, or close `task.md`.

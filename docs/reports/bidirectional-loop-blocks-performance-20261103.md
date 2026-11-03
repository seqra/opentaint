# Loop-block campaign: quality failed; performance review is interim

3 November 2026. Measured commit: `1e6c43963868dde6f652a4b9fa0284c95c818b2c`. All four selected commands ended. OWASP completed and accepted **run-5**. Conductor completed and accepted **run-7**. Thingsboard reached **run-2**, but its last complete and accepted run is **run-1**. Stirling-PDF reached **run-8**, but its last complete and accepted run is **run-7**.

**Status: QUALITY_FAILED / PERF_INTERIM.** The campaign still misses one OWASP identity and three Conductor identities after convergence. Thingsboard and Stirling-PDF timed out. Their reports are provisional. Do not accept the shorter Conductor work as a correct speedup until the missing findings are resolved.

## 1. Selection and evidence

The selection uses FULL marks, a 16 GiB heap, aliases and statics enabled, and field limits `1,1,2,3,...`. OWASP uses a 1,000 s analysis timeout. The other projects use 1,080 s. The outer command limit is 1,200 s. The commands use `runProjectAnalyzer` directly. No baseline was run again.

The fixed finding baseline is `f945f92c5ae554ff4f5fc7696ee5a269210478bb`. The immediate control is `86ad3b70b5b834d60bc0fe96a91091174265c827`. Model and saved SARIF hashes match the preparation plan. The measured runtime source hashes matched the launch snapshot. The subsequent scope-routing fix described below is a post-measurement change. Native checks before this campaign passed 2,395 common tests, 453 JVM tests, and 60 Python controls. Formal model checks do not verify the Kotlin runtime.

All parsed controls, iteration timings, demand frontiers, workload counters, resource windows, GC observations, identity sets, full changed occurrence rows, and provenance hashes are embedded in [the report data](data/bidirectional-loop-blocks-performance-20261103.json). The report does not depend on a temporary shape-probe directory.

## 2. Command and quality results

“Reached/complete/accepted” gives the three separate latest run labels. “Accepted” means that the forward report barrier committed; it does not mean that the quality gate passed.

| Project | Engine outcome | Reached/complete/accepted | Command s | Peak RSS GiB | Current / f945 / 86ad | Missing vs f945 | Added vs f945 | Missing vs 86ad |
| --- | --- | --- | ---: | ---: | --- | ---: | ---: | ---: |
| OWASP | COMPLETE | run-5/run-5/run-5 | 209.359 | 17.66 | 4111 / 4112 / 4112 | 1 | 0 | 1 |
| conductor | COMPLETE | run-7/run-7/run-7 | 115.984 | 17.82 | 4 / 7 / 7 | 3 | 0 | 3 |
| thingsboard | TIMEOUT | run-2/run-1/run-1 | 1,121.425 | 18.28 | 13 / 14 / 13 | 1 | 0 | 0 |
| Stirling-PDF | TIMEOUT | run-8/run-7/run-7 | 1,109.480 | 14.73 | 21 / 17 / 22 | 4 | 8 | 1 |

The fixed quality comparison has nine absent identities: four are preexisting and five are new relative to the immediate control. The explicit rows below are authoritative. Eight Stirling additions are already present in 86ad; this campaign adds no new identity relative to that control. A preexisting loss is not an accepted false negative.

All identity comparisons have no extractor warning. The generic comparison tool marks some bundles as incomplete or input-incompatible because the legacy baseline configuration and the timeout snapshots are not complete performance controls. Exact fingerprint-set differences remain valid observations; the tool verdict is not a successful quality gate.

## 3. Missing identities

Each row includes the code instruction. The data file also keeps its full fingerprint, method signature, location, rule, and the complete changed SARIF result with its available baseline trace. Benchmark labels are included where a labelled test set is available.

| Project | New vs 86ad? | Rule | Method | Location | Instruction |
| --- | --- | --- | --- | --- | --- |
| OWASP | yes | java/security/insecure-design.yaml:trust-boundary-violation | org.owasp.benchmark.testcode.BenchmarkTest01875#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) | src/main/java/org/owasp/benchmark/testcode/BenchmarkTest01875.java:69 | `%30.setAttribute(bar, "10340")` |
| conductor | yes | java.security.graaljs-polyglot-code-injection | com.netflix.conductor.core.execution.evaluators.PythonEvaluator#evaluate(java.lang.String, java.lang.Object) | core/src/main/java/com/netflix/conductor/core/execution/evaluators/PythonEvaluator.java:63 | `%54 = context.eval("python", %53)` |
| conductor | yes | java.security.graaljs-polyglot-code-injection | com.netflix.conductor.core.events.ScriptEvaluator#getSource(java.lang.String) | core/src/main/java/com/netflix/conductor/core/events/ScriptEvaluator.java:253 | `%8 = org.graalvm.polyglot.Source.newBuilder("js", script, "inline")` |
| conductor | yes | java.security.ssrf | com.netflix.conductor.tasks.http.HttpTask#httpCall(com.netflix.conductor.tasks.http.HttpTask$Input) | http-task/src/main/java/com/netflix/conductor/tasks/http/HttpTask.java:173 | `responseEntity = restTemplate.exchange(%21, %23, request, %24, %25)` |
| thingsboard | no | java.security.unsafe-reflection | org.thingsboard.server.common.data.util.ReflectionUtils#getAnnotationProperty(java.lang.String, java.lang.String, java.lang.String) | common/data/src/main/java/org/thingsboard/server/common/data/util/ReflectionUtils.java:27 | `%2 = java.lang.Class.forName(targetType)` |
| Stirling-PDF | yes | java.security.ssrf | stirling.software.SPDF.controller.api.pipeline.PipelineProcessor#sendWebRequest(java.lang.String, org.springframework.util.MultiValueMap) | app/core/src/main/java/stirling/software/SPDF/controller/api/pipeline/PipelineProcessor.java:274 | `%12 = restTemplate.exchange(url, %9, entity, %10, %11)` |
| Stirling-PDF | no | java.security.os-command-injection | stirling.software.common.util.ProcessExecutor#runCommandWithOutputHandling(java.util.List, java.io.File) | stirling/software/common/util/ProcessExecutor:183 | `processBuilder.<init>(command)` |
| Stirling-PDF | no | java.security.xss#sink#1 | stirling.software.SPDF.controller.api.pipeline.PipelineController#handleData(stirling.software.SPDF.model.api.HandleDataRequest) | app/core/src/main/java/stirling/software/SPDF/controller/api/pipeline/PipelineController.java:90 | `return %104` |
| Stirling-PDF | no | java.security.xss#sink#1 | stirling.software.SPDF.controller.api.converters.ConvertEmlToPDF#convertEmlToPdf(stirling.software.common.model.api.converters.EmlToPdfRequest) | app/core/src/main/java/stirling/software/SPDF/controller/api/converters/ConvertEmlToPDF.java:133 | `return %54` |

OWASP recovered 17 of the 18 identities missing in the prior 6052 campaign. The remaining case is labelled `trustbound,true,501` in the pinned `expectedresults-1.2.csv`, so it is an expected vulnerable benchmark case. The remaining `BenchmarkTest01875#doPost` case has a conditional source in `doSomething`: `ESAPI.encoder()` creates an independent receiver marker, then `encodeForHTML(param)` requires this marker and DATA and assigns DATA again. The source metadata also contains a redundant OR of these two positive leaves. This helper is the principal difference from the existing cookie-loop/session native control. The six finite controls did not identify the first lost edge; a later actual-JIR routing diagnostic is recorded in the post-measurement note below. Three additional native fidelity variants were checked after the campaign: six tests pass, including their loop and no-feedback controls. They do **not** reproduce the real miss. A successful 21 s standalone audit of actual JIR and all selected rules confirms the conditional same-mark source shape. That lowering audit does not execute the project engine or identify the first lost edge. The first ordinary JVM test attempt was blocked by preexisting stale `ReportState` test compilation; this is not an analyzer runtime error. Sources, result summaries, and log hashes are embedded in the data file. The later actual single-method engine diagnostic is recorded in the post-measurement note below.

Conductor stops at run-7 with no outgoing demand while three baseline sinks are absent. These are completed-analysis quality regressions that need a trace. The shared ND-source hypothesis is not a proved cause for all three.

The Thingsboard reflection loss and three Stirling losses were already absent from 86ad. Earlier trace review found a dynamic reflection path, a command path, and two return-location changes. These observations do not prove that a later iteration will recover the paths. A different return fingerprint is not an automatic replacement. The newly absent Stirling SSRF sink is also absent from the last accepted run-7 snapshot; the engine timed out in run-8, so final convergence was not measured.

## 4. Added identities

All eight additions are Stirling XSS return identities and all eight are retained from 86ad. This report does not classify them as valid findings or false positives without a witness review.

| Project | Rule | Method | Location | Instruction |
| --- | --- | --- | --- | --- |
| Stirling-PDF | java.security.xss#sink#1 | stirling.software.SPDF.controller.api.converters.ConvertEmlToPDF#convertEmlToPdf(stirling.software.common.model.api.converters.EmlToPdfRequest) | app/core/src/main/java/stirling/software/SPDF/controller/api/converters/ConvertEmlToPDF.java:148 | `return %89` |
| Stirling-PDF | java.security.xss#sink#1 | stirling.software.SPDF.controller.api.filters.FilterController#pageRotation(stirling.software.SPDF.model.api.filter.PageRotationRequest) | app/core/src/main/java/stirling/software/SPDF/controller/api/filters/FilterController.java:210 | `return null` |
| Stirling-PDF | java.security.xss#sink#1 | stirling.software.SPDF.controller.api.filters.FilterController#pageSize(stirling.software.SPDF.model.api.filter.PageSizeRequest) | app/core/src/main/java/stirling/software/SPDF/controller/api/filters/FilterController.java:146 | `return null` |
| Stirling-PDF | java.security.xss#sink#1 | stirling.software.common.util.WebResponseUtils#multiPartFileToWebResponse(org.springframework.web.multipart.MultipartFile) | stirling/software/common/util/WebResponseUtils:42 | `return %8` |
| Stirling-PDF | java.security.xss#sink#1 | stirling.software.SPDF.controller.api.pipeline.PipelineController#handleData(stirling.software.SPDF.model.api.HandleDataRequest) | app/core/src/main/java/stirling/software/SPDF/controller/api/pipeline/PipelineController.java:130 | `return null` |
| Stirling-PDF | java.security.xss#sink#1 | stirling.software.SPDF.controller.api.filters.FilterController#fileSize(stirling.software.SPDF.model.api.filter.FileSizeRequest) | app/core/src/main/java/stirling/software/SPDF/controller/api/filters/FilterController.java:175 | `return null` |
| Stirling-PDF | java.security.xss#sink#1 | stirling.software.common.util.WebResponseUtils#bytesToWebResponse(byte[], java.lang.String, org.springframework.http.MediaType) | stirling/software/common/util/WebResponseUtils:58 | `return %11` |
| Stirling-PDF | java.security.xss#sink#1 | stirling.software.SPDF.controller.api.filters.FilterController#pageCount(stirling.software.SPDF.model.api.PDFComparisonAndCount) | app/core/src/main/java/stirling/software/SPDF/controller/api/filters/FilterController.java:107 | `return null` |

## 5. Iteration times and demand frontiers

Times below are the official log values in seconds. “Static join” is separate from engine time. “Iteration” includes the joined-static phase and the barrier. A timeout row has no completed barrier or outgoing frontier. Demand, Target demand, and method keys are the counters printed at the completed handoff; they are not counts of concrete facts in memory.

### OWASP — run-5/run-5/run-5

| Run | Direction / limit | Status | Engine s | Static join s | Barrier s | Iteration s | Demand | Target demand | Method keys | Reports |
| --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| run-1 | FORWARD / 1 | COMPLETE | 79.532 | 0.483 | 2.284 | 82.405 | 200,431 | 14,085 | 4,447 | 3,227 |
| run-2 | BACKWARD / 1 | COMPLETE | 25.312 | — | 0.180 | 25.531 | 27,425 | 2,462 | 4,352 | 3,227 |
| run-3 | FORWARD / 2 | COMPLETE | 23.786 | — | 0.236 | 24.035 | 176 | 80 | 78 | 4,111 |
| run-4 | BACKWARD / 3 | COMPLETE | 0.691 | — | 0.001 | 0.697 | 135 | 42 | 44 | 4,111 |
| run-5 | FORWARD / 4 | COMPLETE | 0.925 | — | 0.442 | 1.372 | 0 | 0 | 0 | 4,111 |

### conductor — run-7/run-7/run-7

| Run | Direction / limit | Status | Engine s | Static join s | Barrier s | Iteration s | Demand | Target demand | Method keys | Reports |
| --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| run-1 | FORWARD / 1 | COMPLETE | 14.746 | 0.623 | 2.112 | 17.599 | 145,347 | 3,028 | 6,456 | 2 |
| run-2 | BACKWARD / 1 | COMPLETE | 15.504 | — | 0.802 | 16.366 | 179,425 | 116 | 9,356 | 2 |
| run-3 | FORWARD / 2 | COMPLETE | 9.942 | — | 0.492 | 10.454 | 29,666 | 145 | 528 | 4 |
| run-4 | BACKWARD / 3 | COMPLETE | 0.131 | — | 0.002 | 0.137 | 241 | 13 | 100 | 4 |
| run-5 | FORWARD / 4 | COMPLETE | 0.188 | — | 0.008 | 0.199 | 149 | 143 | 91 | 4 |
| run-6 | BACKWARD / 5 | COMPLETE | 0.121 | — | 0.002 | 0.127 | 193 | 13 | 89 | 4 |
| run-7 | FORWARD / 6 | COMPLETE | 0.172 | — | 0.007 | 0.183 | 0 | 0 | 0 | 4 |

### thingsboard — run-2/run-1/run-1

| Run | Direction / limit | Status | Engine s | Static join s | Barrier s | Iteration s | Demand | Target demand | Method keys | Reports |
| --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| run-1 | FORWARD / 1 | COMPLETE | 273.733 | 128.145 | 17.954 | 420.049 | 3,568,476 | 2,934,269 | 29,843 | 13 |
| run-2 | BACKWARD / 1 | TIMEOUT | 515.657 | — | — | — | — | — | — | — |

### Stirling-PDF — run-8/run-7/run-7

| Run | Direction / limit | Status | Engine s | Static join s | Barrier s | Iteration s | Demand | Target demand | Method keys | Reports |
| --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| run-1 | FORWARD / 1 | COMPLETE | 17.131 | 0.385 | 0.705 | 18.288 | 83,562 | 5,297 | 2,024 | 7 |
| run-2 | BACKWARD / 1 | COMPLETE | 14.196 | — | 0.812 | 15.042 | 274,574 | 455 | 4,197 | 7 |
| run-3 | FORWARD / 2 | COMPLETE | 4.832 | — | 0.427 | 5.276 | 1,432 | 137 | 146 | 20 |
| run-4 | BACKWARD / 3 | COMPLETE | 4.852 | — | 0.011 | 4.870 | 3,675 | 102 | 112 | 20 |
| run-5 | FORWARD / 4 | COMPLETE | 13.945 | — | 0.011 | 13.961 | 1,894 | 106 | 84 | 21 |
| run-6 | BACKWARD / 5 | COMPLETE | 100.347 | — | 0.016 | 100.367 | 8,241 | 79 | 57 | 21 |
| run-7 | FORWARD / 6 | COMPLETE | 855.159 | — | 0.041 | 855.209 | 3,748 | 104 | 54 | 21 |
| run-8 | BACKWARD / 7 | TIMEOUT | 51.763 | — | — | — | — | — | — | — |

## 6. Work removed and work still present

Against 86ad, Thingsboard run-1 engine time falls from 393.147 s to 273.733 s, while processed packets fall from 14,892,455 to 10,344,822. Its joined-static completion still takes 128.145 s and its barrier takes 17.954 s. The full first iteration takes 420.049 s. The next backward run times out after 515.657 s of engine work. There is no completed run-2 census; a frozen-result counter of zero does not mean zero work.

Conductor run-4 drops from 76.862 s to 0.131 s and from 8,185,369 to 8,628 processed packets. This is a large observed reduction. The three missing sink identities prevent acceptance of this reduction as a correct optimization result.

OWASP run-1 removes 29.2% of processed packets but takes 79.532 s instead of 64.342 s. Run-3 takes 23.786 s instead of 8.781 s with only 5.4% fewer processed packets. Packet-count reduction alone does not explain wall time.

Stirling run-6 improves from 312.734 s to 100.347 s. Its cyclic processed packets are 2,147,793 of 2,172,437, so cycles still dominate that count. The major regression moves to **forward run-7**: 855.159 s instead of 2.733 s, although current processed packets fall from 588,012 to 115,571. Run-7 offers 347,443 candidates and hands off only 3,748 demand rows. GC pauses in that forward run total 1.642 s. The report must not describe all slow runs as backward runs.

The current counter set does not count all saved-summary replay, local delivery, and demand-query work as processed statement packets. The CPU and allocation profiles now identify the dominant paths. These findings locate the performance cost; they do not close the missing-finding investigation.

Public plus block run-1 Thingsboard concrete output memberships are 242,265, of which 144,967 are protected; scalar concrete rows are 17,719. The earlier values were much larger. Early loop restriction can change those sets. A lower protected count does not establish that a protection flag was lost.

### 6.1. Stirling: the loop-consumer observer dominates forward run-7

Latest reached/complete/accepted: **run-8/run-7/run-7**. The complete forward run-7 lasts 855.159 s. Its continuous JFR contains 44,842 sampled Java stacks; 43,103, or **96.12%**, are in `MethodBlockRuntime.observe` / `LoopConsumerObservation`. The allocation sampler estimates 2.373 TB of allocation churn; **95.76%** of its weight is in the same observer scope. These are sampled execution and allocation shares, not wall-time shares or retained bytes.

The exact run-7 async-profiler window corroborates this result: 94.04% of all CPU-stack samples are in the observer, while 1.03% name native GC stacks. The full run has 1.642 s of logged GC pauses. The observer is the measured cost; a GC-pause explanation is not supported.

The observer replays saved suffix summaries for a growing loop result, then checks local initial admission and enclosing summary demand. The sampled chain is:

```text
LoopOutputRestriction.restrict
  -> MethodBlockRuntime.observe
    -> LoopConsumerObservation.observe
      -> saved suffix record application/enumeration
      -> C2 initial admission
      -> enclosing C5 demand intersection
```

Within the 43,103 observer Java samples, the deepest semantic-operation classification is:

| Observer component | Samples | Share of observer samples |
| --- | ---: | ---: |
| Enclosing C5 restriction | 23,600 | 54.75% |
| C2 initial admission | 8,750 | 20.30% |
| Saved record application | 4,986 | 11.57% |
| Saved record enumeration | 1,939 | 4.50% |
| Observer control / other | 1,806 | 4.19% |
| AP normalization / exit metadata | 1,210 | 2.81% |
| Observation-result union | 772 | 1.79% |
| NormalTarget lookup | 40 | 0.09% |

These components partition observer samples only. They must not be added to the top-level 96.12% share. C5 accounts for 60.16% of allocation weight *within* the observer. Arrays, boxed integers, leaf frames, maps, and iterators are leading allocation classes. This explains why a low count of processed instructions can coexist with high CPU time and allocation churn: the expensive work is the repeated consumer query around loop outputs.

The checked whole-run JFR and run-6/run-7 collapsed samples contain no NORMAL-contributor-cache or ND-join frame in the measured slow windows. This does not prove zero cache work. It does rule out a claim that these profiles show the new NORMAL support cache as the dominant run-7 cost.

### 6.2. Thingsboard: C5 static Target-origin lookup dominates backward run-2

Latest reached/complete/accepted: **run-2/run-1/run-1**. The backward run-2 times out after 515.657 s. Its continuous JFR contains 236,698 sampled Java stacks. **95.02%** are classified as C5 restriction. Inclusive stacks contain `DemandStore.visitControlPairs` in 93.09% and `StaticPairLookup.walkTargetOrigins` in 91.23%. These inclusive percentages overlap.

The allocation sampler estimates 3.723 TB of churn; **92.04%** of its weight is in C5. The largest sampled class is `FrozenStaticCompletion.View.rows` coroutine state, followed by mark/path records, sequence iterators, and related selector records. Thus the main cost is repeated control-pair and static-origin query work, not propagation of a large number of retained intra-procedural facts alone.

The exact run-2 async-profiler window has C5 at 71.73% and native GC at 24.84% of all CPU-stack samples. Near the timeout, the corresponding shares are 63.47% and 28.36%. Native GC CPU is therefore material even though stop-the-world pauses total only 11.799 s. Java-only JFR samples exclude this native work; the two denominators must remain separate.

The same bottleneck exists in the saved 86ad run-2 profile: C5 has 96.51% of Java samples. That aborted window lasts 317.713 s, while the current aborted window lasts 515.656 s. A larger current allocation total is not proof of a new per-query regression. The comparable observation is that both versions spend almost all sampled Java execution in the same demand path.

### 6.3. What the measurements establish

The new Stirling cost is per-result loop-consumer observation, dominated by C5 and C2 plus saved-summary work. The Thingsboard run-2 cost is the existing static/control demand lookup path. These are concrete targets for reducing work. This report does not prescribe an unreviewed runtime change, nor claim that the quality losses have the same cause.

`+0 events` does not prove an infinite call. The handler count increases when a whole `Work` reservation completes. It can remain unchanged while the method executes and requeues several work quanta. The stack samples show active lookup and observation work. Neither the counter nor these finite captures prove global termination.

The source-pinned direct JFR reader matches 6,188 exact controls from the independent Stirling JSON reader, with no differences. The data file embeds this receipt, all four project CPU/workload comparisons, the two critical full-phase profiles, decompositions, capture hashes, and reader hashes. Do not sum overlapping windows or cumulative end recordings. Thingsboard run-1 selected-event coverage starts about 2.3 s after the phase begins; do not describe that sampled phase as fully covered.

## 7. Memory observations

No run reports an exact OOM stop or a JVM `OutOfMemoryError`. No heap snapshot exists. Thingsboard emits three high-memory warnings during run-1, then completes that run. The timeout is in run-2. These warnings are not an OOM result.

RSS includes committed heap and native memory; a 16 GiB heap can therefore have RSS above 16 GiB. After-GC occupancy is an observation, not a retained-owner layout. No dominator or object ownership claim can be made without a heap.

| Project / run | GC pause s | Last after-GC GiB | Peak after-GC GiB | Cumulative reclaimed GiB |
| --- | ---: | ---: | ---: | ---: |
| OWASP / run-1 | 2.723 | 6.69 | 6.91 | 131.5 |
| OWASP / run-2 | 1.155 | 9.18 | 9.18 | 45.5 |
| OWASP / run-3 | 0.575 | 3.83 | 10.04 | 47.2 |
| conductor / run-1 | 1.271 | 12.78 | 12.78 | 36.8 |
| conductor / run-2 | 1.431 | 6.53 | 12.87 | 65.6 |
| conductor / run-3 | 0.615 | 6.54 | 10.60 | 29.3 |
| thingsboard / run-1 | 20.908 | 12.67 | 14.70 | 1,215.6 |
| thingsboard / run-2 | 11.799 | 11.91 | 14.32 | 3,483.2 |
| Stirling-PDF / run-1 | 0.958 | 3.62 | 6.04 | 48.6 |
| Stirling-PDF / run-2 | 0.934 | 5.20 | 5.20 | 60.5 |
| Stirling-PDF / run-3 | 0.490 | 6.21 | 6.21 | 23.9 |
| Stirling-PDF / run-4 | 0.176 | 6.40 | 6.40 | 13.5 |
| Stirling-PDF / run-5 | 0.346 | 6.38 | 6.38 | 37.5 |
| Stirling-PDF / run-6 | 0.566 | 6.52 | 6.53 | 260.9 |
| Stirling-PDF / run-7 | 1.642 | 6.83 | 6.83 | 2,212.4 |
| Stirling-PDF / run-8 | 0.105 | 6.87 | 6.87 | 125.2 |

Stirling run-7 reclaims about 2,212 GiB cumulatively while its last after-GC observation is 6.84 GiB. This shows allocation churn; it does not show a 2 TiB retained heap. Thingsboard run-2 similarly reclaims about 3,483 GiB and ends near 11.91 GiB after its last observed pause. These runs need allocation and CPU attribution. GC pause totals alone do not explain their engine time.

All GC and resource rows are embedded in the data file. Their windows use logger clocks and interpolation. Short runs can have no resource sample or no GC event. Do not treat a missing observation as zero memory.

## 8. Limits and remaining work

All four commands finished, but the optimization task is not complete. Resolve the completed OWASP and Conductor quality gaps. Trace the newly absent Stirling SSRF path and preserve the provisional status of timeout results. The CPU/allocation findings above identify the performance targets. Keep the correctness investigation separate from the next optimization proposal.

The saved f945 and 86ad reports are reused. The source-equivalence flags in the data file cover four named call-lowering/exporter files only. They do not establish whole-analyzer semantic equality. Every sampled hot-owner `normalExitGaps` count is zero; the logs do not cover every owner, so this is not a complete layout proof.

No new analyzer configuration, baseline run, heap request, or runtime modification was used to produce this report. No raw capture was deleted during this post-processing.

## 9. Post-measurement scope-routing correction

The actual `BenchmarkTest01875` JIR reproduces a physical mark-request routing loss. The caller subscription has a block scope, but the old climb target drops it. The event is then sent to the method root. A root request can also suppress the same slot in a waiting non-root block. The correction preserves the caller scope through batching and event dispatch; it does not change ZERO admission or the AP rules.

Four focused protocol controls now pass after two intended failures before the correction. The actual single-root JIR engine changes from zero trust-boundary reports at complete/accepted **run-3** to the expected sink report at complete/accepted **run-3**. The logs, hashes and finite-model receipt are embedded in the data file. The earlier six encoder fidelity controls passed before this correction; they were not reproducers.

The full native gate passes 2,399 common tests and 453 JVM tests, with no failures or skips. The [validation receipt](data/bidirectional-scoped-mark-requests-validation-20261103.json) pins all 936 main/test Kotlin source files in both tested modules; its SHA-256 is recorded in the report data. The committed correction revision is pending. A fresh four-project directory is prepared, but has not been launched. This is native verification of the scoped route, not a new project measurement. Every timing, frontier, profile, identity count and quality status above still describes measured commit `1e6c43963868dde6f652a4b9fa0284c95c818b2c`. The measured campaign remains **QUALITY_FAILED / PERF_INTERIM** until the project rerun is reviewed.

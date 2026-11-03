# Scoped physical-request campaign: measured outcomes

3 November 2026. Selected commit: `050b83cfb7b2e75856ea113c44d0a2d6b707250d`. The runtime correction is `11c1ca265f25cef91a3ca38175c4ca9ecb050d30`; the closing commit expands validation provenance.

**Status: MEASUREMENTS_COMPLETE / QUALITY_NOT_PASSED / CPU_AND_HEAP_ROOTCAUSED.** All four commands end by **10:26:58 UTC**. OWASP converges through reached/completed/accepted **run-5/run-5/run-5** with all 4,112 baseline identities. Conductor times out at **run-6/run-5/run-5** with all seven identities. Thingsboard ends in OOM at **run-1 / none / none**. Stirling times out at **run-8/run-7/run-7**, with 22 identities equal to 86ad and three preexisting exact f945 gaps. No four-project quality pass or convergence claim is made.

The four projects, order, FULL mark mode, 16 GiB heap, field limits `1,1,2,3,...`, aliases/statics, models and saved f945/86ad baselines match the prior campaign. OWASP uses 1,000 s; the other analysis timeouts are 1,080 s; outer limits are 1,200 s. No baseline is run again. The scope correction passes 2,399 common and 453 JVM tests. All 936 source pins match; main 564 and scoped 32 finite-model theorems pass. Model proofs do not verify Kotlin.

The [embedded data](data/bidirectional-loop-blocks-scoped-requests-performance-20261103.json) pins the launch, configuration, baselines, native/formal receipts and prior capture cleanup. Root owns the analyzer commands and live status. All commands have now ended. CPU and allocation profiles are now embedded and interpreted in section 6. The retained-heap evidence is embedded and interpreted in section 7.

The historical [1e6 campaign report](bidirectional-loop-blocks-performance-20261103.md) remains QUALITY_FAILED / PERF_INTERIM. Its timings and quality counts are not replaced by the native scope-control result.

| Project | Command outcome | Reached / complete / accepted | Command s | Peak RSS GiB | Accepted identity snapshot |
| --- | --- | --- | ---: | ---: | --- |
| OWASP | OK | run-5 / run-5 / run-5 | 204.978 | 17.32 | 4112 |
| conductor | TIMEOUT | run-6 / run-5 / run-5 | 1122.392 | 18.33 | 7 |
| thingsboard | OOM | run-1 / none / none | 927.266 | 18.23 | no accepted report; empty export is censored |
| Stirling-PDF | TIMEOUT | run-8 / run-7 / run-7 | 1111.216 | 13.19 | 22 |

The fixed f945 identity baseline used 8 GiB, while this campaign and the saved 86ad control use 16 GiB. The fixed comparison therefore does not establish equal-memory performance. Exact identity set comparisons remain explicit below. No baseline is rerun.

## 1. OWASP completed result — run-5/run-5/run-5

The engine completes with `NO_DEMAND_EDGE`. Its command takes 204.978 s and peak sampled RSS is 17.32 GiB. The final report has **4,112 exact sink identities**. The identity set equals both saved f945 and 86ad: zero missing and zero added identities against either baseline.

Against the prior 1e6 report, all 4,111 identities remain and exactly one is recovered: `BenchmarkTest01875#doPost`, trust-boundary violation at `%30.setAttribute(bar, "10340")`, line 69, fingerprint `BIG74iyPOXJ2cdCFdDFqOq3ZD5rg0rIlMy0wd1+HWp8=`. The exact identity and complete current SARIF result are embedded in the data file. This confirms recovery by identity, not by an equal total count.

Times are official engine, static-completion and barrier values. All command summaries are now verified. Current CPU findings are in section 6.

| Run | Direction / limit | Engine s | Static join s | Barrier s | Iteration s | Demand | Target demand | Reports |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| run-1 | FORWARD / 1 | 78.200 | 0.512 | 2.423 | 81.223 | 201,752 | 14,087 | 3227 |
| run-2 | BACKWARD / 1 | 30.914 | — | 0.176 | 31.124 | 27,425 | 2,463 | 3227 |
| run-3 | FORWARD / 2 | 17.223 | — | 0.252 | 17.486 | 175 | 80 | 4112 |
| run-4 | BACKWARD / 3 | 0.217 | — | 0.001 | 0.223 | 135 | 42 | 4112 |
| run-5 | FORWARD / 4 | 0.178 | — | 0.028 | 0.213 | 0 | 0 | 4112 |

## 2. Conductor timeout snapshot — run-6/run-5/run-5

The command ends with `TIMEOUT` after 1122.392 s. Peak sampled RSS is 18.33 GiB. Run-6 times out; no completed run-6 frontier is available. The final exported report is the accepted forward run-5 snapshot, so it is provisional rather than a converged result.

The snapshot has **seven exact sink identities**, equal to both f945 and 86ad with zero missing or added identities. Its SARIF is byte-identical to the 86ad report (`f1bda968bbfaef7ed65382cb6efc78e7c58337742f5b3fd28300351df47eb2d7`). Against prior 1e6, all four identities remain and exactly these three are recovered:

| Rule | Method | Location | Instruction |
| --- | --- | --- | --- |
| java.security.graaljs-polyglot-code-injection | com.netflix.conductor.core.execution.evaluators.PythonEvaluator#evaluate(java.lang.String, java.lang.Object) | core/src/main/java/com/netflix/conductor/core/execution/evaluators/PythonEvaluator.java:63 | `%54 = context.eval("python", %53)` |
| java.security.graaljs-polyglot-code-injection | com.netflix.conductor.core.events.ScriptEvaluator#getSource(java.lang.String) | core/src/main/java/com/netflix/conductor/core/events/ScriptEvaluator.java:253 | `%8 = org.graalvm.polyglot.Source.newBuilder("js", script, "inline")` |
| java.security.ssrf | com.netflix.conductor.tasks.http.HttpTask#httpCall(com.netflix.conductor.tasks.http.HttpTask$Input) | http-task/src/main/java/com/netflix/conductor/tasks/http/HttpTask.java:173 | `responseEntity = restTemplate.exchange(%21, %23, request, %24, %25)` |

All fingerprints and complete recovered current SARIF results are embedded in the data file. The separate [independent recovery audit](data/bidirectional-conductor-scoped-request-recovery-20261103.json), also embedded in the data, checks all seven identities and preserves the selected old traces. It does not trace Conductor’s first lost edge. No project convergence claim follows from this set equality.

| Run | Direction / limit | Status | Engine s | Static join s | Barrier s | Iteration s | Demand | Target demand | Reports |
| --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| run-1 | FORWARD / 1 | COMPLETE | 15.166 | 1.025 | 1.860 | 18.153 | 158,675 | 7,896 | 2 |
| run-2 | BACKWARD / 1 | COMPLETE | 24.221 | — | 0.906 | 25.173 | 238,753 | 404 | 2 |
| run-3 | FORWARD / 2 | COMPLETE | 43.961 | — | 0.608 | 44.586 | 44,515 | 3,894 | 5 |
| run-4 | BACKWARD / 3 | COMPLETE | 249.455 | — | 0.554 | 250.021 | 123,257 | 39 | 5 |
| run-5 | FORWARD / 4 | COMPLETE | 463.785 | — | 1.908 | 465.707 | 232,988 | 10,125 | 7 |
| run-6 | BACKWARD / 5 | TIMEOUT | 252.540 | — | — | — | — | — | — |

### Workload counters

Backward run-4 takes 249.455 s versus 76.862 s in 86ad: about 3.25 times longer. Yet processed statement packets fall from 8,185,369 to 842,344, a reduction of 89.7%. Physical call offers fall from 2,562,751 to 245,408. These counters show less physical statement/call work, not less total work.

The new completed run-4 has 594,514 candidate offers: 132,979 at method boundaries and 461,535 at block boundaries. The prior 86ad candidate count is 129,761 without this block/observer split. For 24 logged hot owners out of 49 loop methods, the counters record 19,629,812 observations and 11,188,282 prefix trials. This is a bounded hot-owner sample, not an all-owner total. A query observation, scalar trial, candidate offer and processed statement packet are different units.

The runtime performs loop restriction observation before the parent child-result admission/deduplication gate. This ordering and the large observer counts identify work to investigate. The measured CPU distribution is given in section 6. The earlier 1e6 run-4 was fast while omitting three real baseline paths, so its tiny work count is not an equivalent-quality performance control.

Forward run-5 takes 463.785 s, processes 2,342,668 packets and offers 2,893,739 candidates, including 2,237,280 block candidates. Its outgoing demand is 232,988 rows with 10,125 Target demand. The following backward run-6 consumes 252.540 s and times out. Its aborted frozen counters must not be read as zero performed work.


## 3. Thingsboard first-run OOM — run-1 / none / none

Thingsboard ends with analyzer exit **253 / OOM** after 927.266 s of command time. The latest reached iteration is **run-1**; no iteration completes and no forward report is accepted. Official engine time is 699.248 s. Joined static binding then records 53.411 s with `OOM` and `no-completed-binding`; there is no barrier, demand frontier or completed summary-shape census.

The exported SARIF has zero results. All **14** f945 identities and all **13** 86ad identities are absent from this unaccepted export. These absences are **censored by the first-run OOM**, not fourteen proved false negatives, and not a completed quality comparison. The data file embeds every baseline identity and full baseline result with this qualification.

The [reflection baseline audit](data/bidirectional-thingsboard-reflection-baseline-audit-20261103.json) is also embedded in full. It verifies the old `Class.forName(targetType)` trace, including its 21- and 27-point flows. The 86ad and 1e6 runs accepted run-1 and timed out in run-2. The helper was analyzed and had one demand edge, but its first lost marked transfer was not captured. This evidence does not establish a converged false negative, an acceptable loss, or field truncation as the cause.

### Memory signals

Peak sampled RSS is **18.23 GiB**. The memory guard starts its live heap capture at **10:07:26.062 UTC**, with 15,565,038,232 used heap bytes above its 15,461,882,265-byte threshold. It completes at **10:08:04.622 UTC**, before cancellation, and writes **25,285,137,741 bytes** to `guard-live.hprof`. Watcher timestamps are later observations of these markers and are retained separately in the data. The dump file size is not the retained heap size.

Post-full-GC occupancy rises from **9,484 MiB** at 09:57:22 to **14,765 MiB** immediately before capture. Heap-dump GC leaves **14,832 MiB**. This is evidence of rising live heap pressure. It does not identify which storage owns it. The whole JVM log records 3,481 GC pauses totaling 61.004 s, including prescan and capture; these are not run-1-only totals. This section is based on lightweight GC and marker evidence. The retained-owner result is in section 7.

### Work observed before cancellation

The aborted joined-packet census records **19,261,206 processed steps** and **15,663,424 candidate offers**, across 73,668 actors. The post-abort completed-snapshot counters show zero actors and must not be read as zero work. A completed subsumption/protection census is unavailable.

Abstraction counters record 10,745,073 input arrivals, 24,595,529 initial candidates and 1,180,063 new initials. Request handling records 10,411,729 climbs, 10,008,000 outgoing memberships and 33,589,315 member scans. The static snapshot has 147,835 point subscriptions, 1,063 writer rows, 384 FLOW writer rows and 2,472,972 pending memberships. These are different units and must not be added together as a fact total.

The logged hot-owner sample contains short, often STATIC/ANY concrete-mark edges, including protected memberships. It is not a retained-heap census. Twelve logged loop owners show 1,408,287 loop restriction bypasses and zero observations/trials, as expected for the run-1 bypass policy; this is a sample rather than a global total.

For context, 86ad completed run-1 with 14,892,455 processed packets and 6,462,597 candidate offers; 1e6 completed it with 10,344,822 packets and 6,538,707 offers. Current aborted counts already exceed those candidate totals. Different completion states and the corrected request reachability prevent an equal-work speed comparison. Section7 identifies the retained owners from the live heap. The counters alone do not establish which restored path produces each object.


## 4. Stirling timeout snapshot — run-8/run-7/run-7

The command ends with `TIMEOUT` after **1,111.216 s**, with peak sampled RSS **13.19 GiB**. Backward run-8 times out after 51.108 s. Forward run-7 is the latest completed and accepted report, so the exported finding set is provisional rather than converged.

The snapshot contains **22 exact identities**, equal to all 22 in 86ad with zero removed or added identities. Against f945, 14 of 17 remain, three exact identities are absent, and eight identities are added. All eight additions and all three gaps were already present in 86ad. Against 1e6, 21 identities remain and one is recovered; no identity is removed. The recovered row is:

- `java.security.ssrf` in `stirling.software.SPDF.controller.api.pipeline.PipelineProcessor#sendWebRequest(java.lang.String, org.springframework.util.MultiValueMap)` at `app/core/src/main/java/stirling/software/SPDF/controller/api/pipeline/PipelineProcessor.java:274`: `%12 = restTemplate.exchange(url, %9, entity, %10, %11)`.

The data file embeds every changed identity and full relevant SARIF result. Added findings are not labeled false positives without review.

| Run | Direction / limit | Status | Engine s | Static join s | Barrier s | Iteration s | Demand | Target demand | Reports |
| --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| run-1 | FORWARD / 1 | COMPLETE | 18.914 | 0.410 | 0.742 | 20.139 | 86,411 | 5,400 | 7 |
| run-2 | BACKWARD / 1 | COMPLETE | 14.405 | — | 0.859 | 15.297 | 275,022 | 469 | 7 |
| run-3 | FORWARD / 2 | COMPLETE | 4.958 | — | 0.458 | 5.433 | 1,382 | 137 | 21 |
| run-4 | BACKWARD / 3 | COMPLETE | 4.839 | — | 0.009 | 4.856 | 3,720 | 96 | 21 |
| run-5 | FORWARD / 4 | COMPLETE | 16.244 | — | 0.012 | 16.260 | 1,849 | 107 | 22 |
| run-6 | BACKWARD / 5 | COMPLETE | 91.925 | — | 0.017 | 91.946 | 8,475 | 79 | 22 |
| run-7 | FORWARD / 6 | COMPLETE | 860.464 | — | 0.045 | 860.517 | 4,017 | 103 | 22 |
| run-8 | BACKWARD / 7 | TIMEOUT | 51.108 | — | — | — | — | — | — |

Forward run-7 takes **860.464 s** despite entering from 8,475 demand edges after run-6. Its outgoing frontier has 4,017 demand edges and 103 Target demand rows. This remains a slow completed forward iteration; the campaign does not support a backward-only performance explanation. Section6 locates the dominant CPU work in loop consumer observation.

The [independent Stirling recovery audit](data/bidirectional-stirling-scoped-request-recovery-20261103.json) is embedded in full and checks the exact current identity set and recovered SSRF result. The [preexisting Stirling audit](data/bidirectional-stirling-preexisting-baseline-audit-20261103.json) is embedded in full. Two exact missing identities are XSS controller returns in `PipelineController#handleData` and `ConvertEmlToPDF#convertEmlToPdf`. Same-rule, same-method findings remain at other returns. The pinned lowering/export path explains representative final-return selection, but that does not prove equal per-return coverage or replace the missing fingerprint. The third gap is the `ProcessExecutor#runCommandWithOutputHandling` command-injection identity. Its saved 11-point path reaches `ProcessBuilder` through argument-list additions; the first lost current edge is unknown. The strict f945 identity gate remains unpassed.

## 5. GC, resources, and remaining analysis

| Project | Actual OOM markers | Heap capture | Whole-process GC pauses | Whole-process pause s |
| --- | --- | --- | ---: | ---: |
| OWASP | no | none; no OOM capture expected | 311 | 5.961 |
| conductor | no | none; no OOM capture expected | 871 | 11.779 |
| thingsboard | yes | one native live dump | 3,481 | 61.004 |
| Stirling-PDF | no | none; no OOM capture expected | 824 | 6.819 |

These pause totals cover the JVM lifetime, including initialization, prescan and teardown; they are not concurrent-GC CPU shares. The data also embeds process resource windows for each run, including sampled RSS and interpolated process CPU, and per-phase GC end-event attribution. RSS, allocation and retained object ownership are different quantities.

Thingsboard is the only command with exact OOM markers and a heap. The completed capture receipt records SHA-256 `cbe8f38fbb2268a06d1a0e8616dd6d0e8f136265b2fcc86f81aeff1221958756`. Other commands have no actual OOM evidence. The receipt is embedded; the report reader does not reread the 25 GB heap.

All run frontiers, method-key counts, record crossings, source/Target counters, sampled hot owners, exact error/guard signals, and input hashes are in the data. Logged `normalExitGaps` are zero for the sampled owners. The diagnostics cover bounded hot-owner samples, so this is not proof that every layout has no gap.

The four command metrics and exact report comparisons are complete. CPU/allocation findings follow in section 6. Thingsboard retained-owner findings follow in section 7. A timeout snapshot matching a baseline is not a project convergence result. The Thingsboard empty export is not an accepted zero-finding result, and the remaining Stirling identity gaps are not waived.


## 6. CPU findings: repeated loop observations dominate restricted runs

The new scoped blocks remove physical propagation work, but the loop consumer observer performs expensive demand queries before the parent result deduplication gate. This explains the measured Conductor and Stirling slowdown: repeated admission/intersection and saved-relation observation has become the main Java workload. The measurements show this in both directions. They do not prove nontermination.

The complete current/86ad/1e6 profile matrix, source/input hashes and **537-check PASS receipt** are embedded in the data file. The comparison SHA-256 is `3ea79ff1cdf8ae7d9ed740c9614f07caf6ee1290d16dd88c2cf18b987897a158`. The checks cover derived arithmetic, stable inputs and window classification. The earlier 6,188-control reader comparison is explicitly historical implementation evidence, not a new validator run on these recordings.

### Conductor and Stirling

The following shares use sampled **Java-thread stacks**, which exclude native GC and compiler CPU. Allocation is sampled weighted churn, not retained heap. Observer components use an observer-only denominator and must not be added to the whole-Java shares.

| Project / run | Engine outcome | Observer share of Java samples | Weighted allocation TB | Observer share of allocation |
| --- | --- | ---: | ---: | ---: |
| conductor / run-4 | COMPLETE | 61.70% | 0.774 | 46.79% |
| conductor / run-5 | COMPLETE | 76.86% | 1.340 | 63.33% |
| conductor / run-6 | TIMEOUT | 93.63% | 1.697 | 92.29% |
| Stirling-PDF / run-6 | COMPLETE | 78.43% | 0.242 | 68.86% |
| Stirling-PDF / run-7 | COMPLETE | 95.74% | 2.225 | 95.61% |
| Stirling-PDF / run-8 | TIMEOUT | 96.43% | 0.128 | 94.06% |

In **Conductor backward run-4**, the observer accounts for **61.70%** of Java samples. Within that observer work, **66.12%** is C2 initial admission and **18.07%** is enclosing C5 restriction. Physical packets are 89.7% lower than 86ad, yet the completed run takes 3.25 times longer. The 86ad run-4 profile instead spends 46.61% of Java samples in direct calls, 23.82% in saved replay and 22.42% in current delivery. The new query work is substantial despite fewer statement visits.

In **Conductor forward run-5**, the observer share rises to **76.86%**, with enclosing C5 responsible for 72.00% of observer Java samples. In the timed-out **backward run-6**, it reaches **93.63%**, with C5 responsible for 76.25% of observer samples. These three runs complete/abort at different workloads; their allocation totals are not interchangeable regression controls.

The exact all-thread CPU captures confirm significant native GC work that Java-only profiles omit. In the run-4 normal window, **35.17%** of all async CPU samples are native GC stacks and **30.52%** are observer stacks. In the run-6 near-limit window, they are **24.80% GC** and **72.56% observer**. These percentages have a different denominator and window from the whole-run Java table; they must not be converted directly into wall-time shares.

In **Stirling forward run-7**, the observer occupies **95.74%** of Java samples. Within the matching observer component census, **51.92%** is enclosing C5 restriction, **21.37%** is C2 initial admission, **12.92%** is saved-record application, and **4.71%** is saved-record enumeration. Its exact run-7 CPU window has **94.72% observer** and **1.32% native GC** among all samples. The slow forward iteration is primarily query/observation work, rather than GC or physical statement execution.

Stirling’s near-limit CPU capture crosses run-7, the barrier and run-8. Its aggregate is preserved as a mixed window; it is not assigned to either run or split in proportion to wall overlap. The run-6 normal capture also crosses a run boundary. The JFR event timestamps provide the separate whole-phase run-8 observer share of **96.43%**.

Current Stirling run-7 takes 860.464 s versus 855.159 s in 1e6, with the same observer bottleneck. Both scoped versions are much slower here than the 86ad run-7 window of 2.733 s. Conductor and Stirling now recover the complete86ad report identity sets, while 1e6 omits real identities; this makes its tiny Conductor run-4/run-5 workload an invalid equal-quality speed reference. Matching final identities does not prove identical work at each intermediate iteration.

### Thingsboard run-1 and interrupted static completion

Thingsboard has no run-1 loop observer work under the selected bypass policy. Among **70,531** sampled Java stacks, **32.35%** are classified as direct-call work, **13.79%** as current delivery, **9.87%** as block routing and **8.81%** as block current delivery. `transportProtection` occurs inclusively in **33.91%** of Java samples. That inclusive share overlaps the top-level scopes and cannot be added to them. The retained 256 MiB recording does not certify full run-1 coverage, so these shares describe the retained sampled evidence.

The sampled weighted allocation estimate is **3.206 TB**, dominated by AP/trie operations and common arrays/collections. It establishes churn, not which owner retains memory. The residual `other` source classifier also contains nested `MethodBlockRuntime$Binding` work because those class names do not match its literal routing anchor. It must not be read as idle time or proof that rule guards dominate.

The separately reported **53.411 s static-completion window** contains only **235 Java samples**. Inclusive stacks place 232 samples in `completeJoinedStaticGuidance` and 93 samples (**39.57%**) in `KilledStaticWriteStore.freeze`. This confirms work in guidance collection/freezing; the run ends without a completed binding. It does not establish an unbounded join matrix or completed writer binding as the OOM cause.

That static-completion window overlaps **38.560 s** of the native heap-capture interval. The heap-dump GC itself is a separate 2.214 s pause. Much of the enclosing wall interval is therefore capture/guard interruption rather than evidence of continuous summary-join computation. No CPU share or allocation estimate proves retained ownership. Section7 supplies the live heap’s dominators and strong paths to roots.

The practical performance target is now clear for restricted Conductor/Stirling runs: avoid repeating loop consumer demand observation when an equivalent result is already known. Section7 identifies the Thingsboard retained owners and the staged lifetime overlap. The campaign remains quality-unaccepted because Thingsboard has no accepted report and the three strict Stirling baseline identity gaps remain.


## 7. Thingsboard retained heap: closed execution state overlaps static handoff construction

The live run-1 snapshot is now analyzed with Eclipse MAT 1.17/Java 21. MAT parses **426,076,912 reachable objects**, totaling **15,309,242,544 bytes: 15.309 GB or 14.258 GiB**. It removes only 41,012 unreachable objects totaling 1,732,088 bytes. This population is mostly MAT-reachable objects, rather than unreachable garbage. Strong GC-root paths are verified for the selected closed-state owners; MAT reachability alone does not classify every cache referent as strong.

The complete **510,983-byte** retention summary, all five successful MAT command receipts, selected object/field tables, strong GC-root paths, exact removal query and input/tool hashes are embedded in the data. Summary SHA-256: `244139fe369c65689e72d923bb48ed0f77dbfffcc44ce5eece851baa1739dd08`. The actual heap and MAT indexes remain intact. The report adds no new MAT execution.

Here and below, **GB/MB use decimal units**. GiB/MiB use powers of 1,024. Serialized hprof bytes, parsed shallow heap, retained subtrees and sampled allocation are different measurements.

### Where memory is retained

| Dominator owner group | Retained GB |
| --- | ---: |
| Method actors | 5.704 |
| Subscription managers | 1.622 |
| IR RAM storage | 1.619 |
| Threads | 1.452 |
| RunManager | 1.289 |
| Rules provider | 0.855 |
| Method-entry cache | 0.805 |

These are ownership views, not an instruction to sum nested tables. The IR and method/rule caches remain outside the analyzer-core optimization scope.

The main thread’s **1.452 GB** subtree is chiefly an unfinished `FrozenStaticCompletion.Builder` (**1,372,508,384 bytes**) and `OwnedJoinedStaticWriterBinding` (**76,720,608 bytes**). The builder already holds a duplicate handoff inventory while the original actors, indexes and raw static stores remain reachable.

The thread stack locates the pause in static candidate freezing. Its current killed-write inventory has **1,353 candidate IDs**, retaining only **24,720 bytes**. That inventory is distinct from the local survivor set. The main-thread dominators identify the accumulated builder as the large owner; they do not establish a gigabyte current prune-survivor set. The binder has 3,238,251 offered writers; its `processed`, `candidateInputs` and `boundOutputs` counters are all **zero**. Recursive writer propagation has not begun in this snapshot. This rules out attributing this captured OOM to completed writer-input joins.

The `StaticWriteKeyInterner` has **4,135 geometries**, **60,143 rows**, and **4,943,880 retained bytes**. Only **83 NORMAL contributor rows/keys** exist. These observations do not support a mark-exclusion-subset explosion or a NORMAL ND certificate-payload explosion as the captured retained root cause.

### Quantified closed-state release opportunity

MAT evaluates one explicit field-root removal set and computes its retained union. The set covers selected closed execution fields, block current-delivery indexes/completions, and public publication indexes. Its exact union is:

- **104,324,750 objects**;
- **4,268,877,960 bytes: 4.269 GB or 3.976 GiB**;
- **27.884%** of the parsed live heap.

This union accounts for cross-field sharing and nesting. It is a **snapshot root-removal simulation**, not implemented cleanup, an observed JVM reclamation result, or proof that later static binding/run-2 will fit 16 GiB. The exact OQL query and resulting histogram are embedded. Individual field-retained sizes must not be added on top of this union.

The deletion set deliberately preserves the actual local input maps, admitted summaries, raw Target rows, raw static inventories and diagnostics. In particular, local link inputs retain **772,618,488 bytes** and are needed for later binding/replies. Native summary/Target/candidate inventories must remain available. The selected removable local `targets` field is a closed current-delivery index, not the retained raw Target summary inventory. A release implementation must establish the no-future-callback/lifetime boundary before it changes these owners.

Diagnostic `BodyWork.samples` alone retains **491,530,680 bytes**. It is outside the stated 4.269 GB union. This separate cost is measured, but the current report does not authorize removing required diagnostics or add it to the simulated saving.

The evidence therefore gives two concrete memory targets: end the lifetime of closed execution/current-delivery state before handoff construction, and avoid simultaneously building another full static completion inventory. The first has a measured 4.269 GB root-removal opportunity; the duplicate builder is 1.373 GB in this captured stage. These quantities cannot be blindly summed as a promised saving or applied by clearing required input/summary state.

## 8. Outcome and next work

The scope correction restores all exact OWASP identities and all previously missing Conductor/Stirling identities from 1e6. Conductor’s accepted run-5 and Stirling’s accepted run-7 sets match 86ad; their following backward runs still time out. OWASP converges at run-5. Thingsboard reaches only run-1 and fails with OOM before any report is accepted. Its baseline absences remain censored. Stirling’s three strict preexisting f945 identity gaps remain open.

The next analyzer-core work has two separate measured causes. For Thingsboard memory, prioritize closed-state lifetime release and duplicate handoff-builder storage. For Conductor/Stirling CPU, avoid repeated loop consumer demand observation that now dominates restricted-run execution. Each needs a design that preserves existing demand, summary, source, Target and callback semantics. No runtime optimization is implemented by this report, and no four-project quality or performance acceptance is claimed.

The [next-iteration proposal](../design/bidirectional-joined-state-and-loop-consumers-next-iteration-20261103.md)
ranks these changes and states the required proofs, native controls and
same-configuration experiments. Candidate-directed static pruning stays a
secondary proposal; the heap does not identify a large current survivor set
as the main owner.

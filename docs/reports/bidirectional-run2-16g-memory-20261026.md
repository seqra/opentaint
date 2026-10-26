# Run-2 at a 16 GiB heap — 2026-10-26

**A 16 GiB heap does not let Thingsboard, Conductor, or Stirling-PDF complete run-2.** All three still reach the memory guard. OWASP completes run-2 and reaches run-11.

The extra memory lets the failing projects create more method-local queries, call-input groups, and stored relations before they stop. Repeated summary publication also grows. The evidence supports a state/work amplification problem, rather than a few missing megabytes or only a large reclaimable cache. It does not establish the final heap needed to reach a fixed point.

## Experiment and run outcomes

Only the analyzer JVM maximum heap changes: `-Xmx16g`. Thingsboard’s previous limit was **12 GiB**; the other three projects used **8 GiB**. The memory guard remains at 90%, so its new threshold is **14.4 GiB** (15,461,882,265 bytes).

Inputs, timeouts, FULL marks, statics, alias settings, rule selection, and Java 17 remain unchanged. The source revision is `30b50b20029394eee9c34acb5afce934b08591b9`. Its core tree is `e3ede1a36d3b04d79a23cc93285f385ecd968dbf`, identical to the previous measured implementation. There are no analyzer changes.

The four timed runs are serial. Automatic OOM heap dumps remain enabled in both configurations. OWASP has a separate diagnostic capture during run-2, because its timed run completes without a run-2 OOM. That diagnostic is stopped after capture and is excluded from the timing comparison.

| Project | Previous heap | Previous run-2 result / s | 16 GiB result / s | Latest reached / completed / accepted forward |
| --- | --- | --- | --- | --- |
| Thingsboard | 12 GiB | OOM / 149.784 | OOM / 214.498 | run-2 / run-1 / run-1 |
| Conductor | 8 GiB | OOM / 67.265 | OOM / 306.041 | run-2 / run-1 / run-1 |
| Stirling-PDF | 8 GiB | OOM / 107.438 | OOM / 479.109 | run-2 / run-1 / run-1 |
| OWASP | 8 GiB | COMPLETE / 40.263 | COMPLETE / 41.877 | run-11 / run-11 / run-11 |

| Project | Previous run-2 excluding dump bounds (s) | 16 GiB excluding dump bounds (s) | Ratio |
| --- | --- | --- | --- |
| Thingsboard | 120.277 | 175.034 | 1.46× |
| Conductor | 49.801 | 267.598 | 5.37× |
| Stirling-PDF | 88.567 | 438.687 | 4.95× |
| OWASP | 40.263 | 41.876 | 1.04× |

The first table uses engine-end markers and includes any heap-dump pause. The second excludes the logged dump interval. Neither is a completion-time improvement for a project that still ends with OOM. A longer interval before OOM can mean more completed partial work and more retained state.

The successful OWASP diagnostic reaches run-2, completes run-1, and retains the run-1 forward report. The timed OWASP run above reaches, completes, and accepts run-11. These are separate progress records.

| Project | Heap used after GC near run-2 start | Near active midpoint | Last sample before dump / run-2 end |
| --- | --- | --- | --- |
| Thingsboard | 0.9 s / 9.121 GiB | 87.4 s / 11.498 GiB | 175.0 s / 14.406 GiB |
| Conductor | 0.5 s / 12.719 GiB | 133.8 s / 13.016 GiB | 267.6 s / 14.406 GiB |
| Stirling-PDF | 0.7 s / 3.689 GiB | 219.4 s / 14.123 GiB | 438.7 s / 14.404 GiB |
| OWASP | 0.5 s / 5.343 GiB | 19.7 s / 3.929 GiB | 41.7 s / 5.152 GiB |

Each cell gives elapsed run-2 time and heap used after a recorded GC. These are nearest samples within the active interval. They include remaining caches and differ from the exact retained-owner census below. Cache reclamation and object creation interleave, so these traces need not increase at every sample.

## 1. The larger heap retains more state

| Project | Run-2 activity | Previous | 16 GiB | Ratio |
| --- | --- | --- | --- | --- |
| Thingsboard | New method-local initials | 1,609,008 | 2,957,159 | 1.84× |
| Thingsboard | New call-input groups | 2,067,458 | 4,288,079 | 2.07× |
| Conductor | New method-local initials | 770,455 | 2,437,415 | 3.16× |
| Conductor | New call-input groups | 1,392,371 | 5,051,513 | 3.63× |
| Stirling-PDF | New method-local initials | 769,456 | 1,954,171 | 2.54× |
| Stirling-PDF | New call-input groups | 1,329,510 | 3,616,180 | 2.72× |
| OWASP | New method-local initials | 32,504 | 32,504 | 1.00× |
| OWASP | New call-input groups | 10,076 | 10,059 | 1.00× |

These are END minus START counter totals from each timed run-2. Initial counts include ZERO control initials. They are not counts of globally distinct AP objects. Call-input groups preserve their caller/premise/call-stage coordinates.

OWASP starts exactly **32,504** method-local initials in both configurations. In contrast, the failing projects create substantially more state with 16 GiB and still do not finish. Those are different partial progress points; this is not evidence that increasing the heap changes the intended fixed point.

| Project | Previous stored method output memberships | 16 GiB memberships | Ratio | Previous / new processed delta headers |
| --- | --- | --- | --- | --- |
| Thingsboard | 8,936,562 | 14,333,425 | 1.60× | 28,964,422 / 42,336,430 |
| Conductor | 4,127,680 | 13,621,583 | 3.30× | 12,931,366 / 39,911,367 |
| Stirling-PDF | 9,871,214 | 21,979,846 | 2.23× | 29,397,777 / 64,080,522 |
| OWASP | 792,986 | 876,495 | 1.11× | 6,238,819 / 6,994,497 |

A membership is one stored output path/mark under an owning method, initial premise, statement, and layer. Trees can contain several memberships. A processed delta header can also carry several marks or paths. Neither number is a count of unique program taints.

The OOM snapshots occur at the memory guard. OWASP’s snapshots are active marked-phase samples from separate diagnostic runs. Their membership counts are not whole-run totals or peak-memory measurements.

| Project | Incoming run-2 demand pairs, previous → 16 GiB | 16 GiB method keys |
| --- | --- | --- |
| Thingsboard | 2,379,523 → 2,380,368 | 73,599 |
| Conductor | 72,881 → 72,857 | 17,417 |
| Stirling-PDF | 36,772 → 36,774 | 7,258 |
| OWASP | 133,966 → 133,966 | 12,083 |

Incoming demand is guidance from run-1. The small count differences between repeated runs are shown explicitly; the inputs and implementation are fixed. The current actual-input query set is stored separately. These two counts do not have the same meaning.

## 2. Run-2 memory layout

| Retained owner / union (GiB), previous → 16 GiB | Thingsboard | Conductor | Stirling-PDF | OWASP |
| --- | --- | --- | --- | --- |
| Whole live heap | 10.605 → 14.136 | 7.094 → 14.159 | 7.101 → 14.186 | 4.288 → 4.289 |
| IR RAM relationship store | 2.094 → 1.510 | 2.091 → 2.109 | 0.913 → 0.915 | 0.503 → 0.502 |
| Method execution | 2.034 → 3.774 | 1.500 → 4.869 | 3.542 → 8.106 | 0.093 → 0.094 |
| Raw and selected summaries | 0.653 → 0.962 | 0.426 → 1.470 | 0.444 → 1.167 | 0.031 → 0.031 |
| Publication / subscription stores | 1.141 → 1.932 | 0.793 → 2.599 | 0.725 → 1.891 | 0.041 → 0.042 |
| Call-input accumulators | 0.317 → 0.633 | 0.234 → 0.839 | 0.225 → 0.606 | 0.005 → 0.005 |
| Incoming demand | 0.785 → 0.779 | 0.033 → 0.033 | 0.015 → 0.015 | 0.043 → 0.043 |
| Current query sets | 0.075 → 0.136 | 0.035 → 0.111 | 0.034 → 0.086 | 0.002 → 0.002 |
| Persistent NORMAL records | 0.132 → 0.132 | 0.032 → 0.032 | 0.009 → 0.009 | 0.018 → 0.018 |
| Method-form directories | 0.863 → 0.936 | 0.199 → 0.199 | 0.208 → 0.208 | 0.378 → 0.378 |
| Rule providers / resolver views | 0.792 → 0.792 | 0.057 → 0.001 | 0.127 → 0.127 | 0.077 → 0.077 |
| Reports / vulnerability witnesses | 0.154 → 0.154 | 0.000 → 0.000 | 0.001 → 0.001 | 0.044 → 0.044 |

| Additive 16 GiB snapshot partition (GiB), by dominator-root class | Thingsboard | Conductor | Stirling-PDF | OWASP |
| --- | --- | --- | --- | --- |
| Per-unit runners | 5.696 | 6.463 | 9.440 | 0.147 |
| Subscription managers | 1.061 | 1.272 | 0.863 | 0.011 |
| IR RAM store | 1.510 | 2.109 | 0.915 | 0.502 |
| Method-form directory | 0.936 | 0.199 | 0.208 | 0.378 |
| Run configuration | 0.786 | 0.033 | 0.016 | 0.044 |
| Soft-reference roots | 0.000 | 0.000 | 0.000 | 2.496 |
| Other roots and shared objects | 4.147 | 4.083 | 2.744 | 0.712 |
| Whole live heap | 14.136 | 14.159 | 14.186 | 4.289 |

Each object belongs to one root in this partition. A per-unit runner can retain several analyzer stores. Objects shared across those roots are separate roots or belong to another category. The partition is physical ownership, not a sum of all logical stores.

Owner unions are **not additive**. The call-input row is part of publication/subscription storage. Shared AP data can require removal of several owners before it becomes unreachable. The IR row is a physical dominator.

The main growing owners are the active method graph and interprocedural stores. Statement arrays alone remain a small part of them; most of the cost is the occupied relation coordinates, group/maps/lists, TAINT payloads, and call joins. The demand and NORMAL-record handoff is largely fixed for each input.

Run-1’s compact diagonal storage and FLOW-first batching are not enabled in run-2. Current queries are started from actual marked inputs by `StrongQueries`; concrete guides can refine them. Thus the incoming explicit demand count does not bound the executable query set.

| Project | Previous / new form-cache bytes under soft-reference roots (GiB) |
| --- | --- |
| Thingsboard | 0.000 / 0.000 |
| Conductor | 0.000 / 0.000 |
| Stirling-PDF | 0.000 / 0.000 |
| OWASP | 2.496 / 2.496 |

All three 16 GiB OOM heaps have already gone through the memory manager’s cache-cleanup path. Their soft-reference-root cache census must be read separately from strongly held form directories and currently pinned forms. OWASP can retain rebuildable forward/reverse form payloads without running out of memory.

The cache census partitions dominator roots and checks that their retained-byte sum equals the whole live heap. Dump-file sizes are not heap sizes; HPROF stores object IDs and metadata in a different format.

## 3. Statics remain dominant on Conductor and Stirling-PDF

| Project | Previous static output share | 16 GiB share | 16 GiB static outputs | Nonstatic outputs | S → S memberships |
| --- | --- | --- | --- | --- | --- |
| Thingsboard | 14.6% | 18.2% | 2,609,366 | 11,724,059 | 2,272,627 |
| Conductor | 84.7% | 87.7% | 11,941,973 | 1,679,610 | 11,522,120 |
| Stirling-PDF | 95.7% | 96.2% | 21,150,465 | 829,381 | 20,246,921 |
| OWASP | 5.0% | 4.5% | 39,340 | 837,155 | 8,770 |

`S` is the static base, `NS` is a nonstatic base, and `Z` is ZERO. Arrows describe the stored **backward** relation, from premise to conclusion. `S → S` can connect the same field or different fields; it is not an identity count.

The shares are exact stored method-output membership partitions at the snapshots. They are not exact CPU shares or counts of all historical processed static facts. No per-fact history instrumentation was added.

| Backward premise → conclusion | Thingsboard | Conductor | Stirling-PDF | OWASP |
| --- | --- | --- | --- | --- |
| Z->NS | 4,615,270 | 41,349 | 47,689 | 756,822 |
| Z->S | 260,262 | 170,390 | 808,736 | 30,570 |
| NS->NS | 7,102,882 | 1,561,955 | 669,213 | 80,333 |
| NS->S | 76,477 | 249,463 | 94,808 | 0 |
| S->NS | 5,907 | 76,306 | 112,479 | 0 |
| S->S | 2,272,627 | 11,522,120 | 20,246,921 | 8,770 |

| Project | Current query memberships | Static query memberships | Static query share |
| --- | --- | --- | --- |
| Thingsboard | 2,897,382 | 859,057 | 29.6% |
| Conductor | 2,419,929 | 2,194,967 | 90.7% |
| Stirling-PDF | 1,946,915 | 1,871,243 | 96.1% |
| OWASP | 18,425 | 2,510 | 13.6% |

The dominant static shape is a named field with a full mark, retained under many method/call coordinates. Common forms are `S → S / EXACT / NORMAL` and `S → S / ANY / DEMAND`. A named-field ANY query can also require its EXACT counterpart. Those forms are semantically distinct; this report does not propose to remove one as a duplicate.

Thingsboard still has a large nonstatic component: sink-seeded `Z → NS` and marked-premise `NS → NS` relations. A ZERO premise on a marked backward fact can represent a sink seed; it must not be confused with ZERO control or an unconditional forward source. The one-field limit still permits a large product of methods, premise colors, field names, program points, and full marks.

| Project | Hot static position in DEMAND method state | Memberships |
| --- | --- | --- |
| Thingsboard | `org.thingsboard.server.common.data.page.SortOrder$Direction/org.thingsboard.server.common.data.page.SortOrder$Direction.ASC` | 86,866 |
| Thingsboard | `org.thingsboard.server.common.data.EntityType/org.thingsboard.server.common.data.EntityType.DEVICE` | 85,046 |
| Thingsboard | `org.thingsboard.server.common.data.id.TenantId/org.thingsboard.server.common.data.id.TenantId.SYS_TENANT_ID` | 76,068 |
| Conductor | `__spring_registry__/__spring_registry__.com.netflix.conductor.redis.jedis.JedisCommands` | 377,589 |
| Conductor | `__spring_registry__/__spring_registry__.com.netflix.conductor.dao.ExecutionDAO` | 358,566 |
| Conductor | `__spring_registry__/__spring_registry__.com.netflix.conductor.common.utils.ExternalPayloadStorage` | 337,479 |
| Stirling-PDF | `__spring_registry__/__spring_registry__.stirling.software.common.model.ApplicationProperties` | 1,634,527 |
| Stirling-PDF | `__spring_registry__/__spring_registry__.org.springframework.context.ApplicationContext` | 1,601,797 |
| Stirling-PDF | `__spring_registry__/__spring_registry__.stirling.software.SPDF.config.ExternalAppDepConfig` | 1,524,934 |
| OWASP | `org.owasp.benchmark.helpers.Utils/org.owasp.benchmark.helpers.Utils.TESTFILES_DIR` | 7,648 |

| Project | Largest stored output families (base / tail / layer / accessor depth) | Memberships |
| --- | --- | --- |
| Thingsboard | `S->S\|TAINT\|ClassStatic\|EXACT\|NORMAL\|depth=2` | 1,274,433 |
| Thingsboard | `NS->NS\|TAINT\|LocalVar\|ANY\|DEMAND\|depth=1` | 1,258,478 |
| Thingsboard | `NS->NS\|TAINT\|LocalVar\|EXACT\|NORMAL\|depth=1` | 1,141,812 |
| Conductor | `S->S\|TAINT\|ClassStatic\|ANY\|DEMAND\|depth=2` | 5,359,937 |
| Conductor | `S->S\|TAINT\|ClassStatic\|EXACT\|NORMAL\|depth=2` | 5,190,902 |
| Conductor | `S->S\|TAINT\|ClassStatic\|EXACT\|DEMAND\|depth=2` | 900,464 |
| Stirling-PDF | `S->S\|TAINT\|ClassStatic\|EXACT\|NORMAL\|depth=2` | 9,761,508 |
| Stirling-PDF | `S->S\|TAINT\|ClassStatic\|ANY\|DEMAND\|depth=2` | 9,405,050 |
| Stirling-PDF | `S->S\|TAINT\|ClassStatic\|EXACT\|DEMAND\|depth=2` | 782,241 |
| OWASP | `Z->NS\|TAINT\|LocalVar\|EXACT\|NORMAL\|depth=1` | 400,174 |
| OWASP | `Z->NS\|TAINT\|LocalVar\|ANY\|DEMAND\|depth=1` | 96,991 |
| OWASP | `Z->NS\|TAINT\|LocalVar\|ANY\|DEMAND\|depth=0` | 83,720 |

Generated Spring registry fields and application constants recur. Special EXACT class markers are separate from named-field positions in the detailed census. An enum constant appearing here is not proof that the Java field is writable.

## 4. Repeated publication work grows too

| Project | Previous pending offers | 16 GiB offers | 16 GiB exact duplicates, lower bound | Duplicate share | Retained pending GiB |
| --- | --- | --- | --- | --- | --- |
| Thingsboard | 10,371,275 | 23,878,689 | 23,551,069 | 98.6% | 0.658 |
| Conductor | 471,537 | 743,359 | 695,430 | 93.6% | 0.021 |
| Stirling-PDF | 2,195,367 | 5,141,284 | 5,094,684 | 99.1% | 0.140 |
| OWASP | 34,583 | 39,058 | 0 | 0.0% | 0.004 |

A definite duplicate has the same method owner, canonical premise object, and immutable conclusion object. Equal values in different objects are not counted, so this is a lower bound.

When `StrongQueries.admit` returns any new initial, `RunMethodAnalyzer.addLink` scans all existing raw summaries and queues every already permitted row. It can offer old rows for unrelated, already authorized premises again. The shared publication index deduplicates later. The pending lists, row scans, and repeated insertion tests have already incurred their cost.

These bytes do not explain the whole OOM heap. The duplicate offers do identify avoidable work before publication admission. The intended fix needs to preserve newly authorized premises and annotation changes; it is not implemented in this experiment.

| Project | Method with pending publication offers | Offers | Distinct identity pairs |
| --- | --- | --- | --- |
| Thingsboard | `org.thingsboard.server.common.data.page.BasePageDataIterable#next()Ljava/lang/Object;` | 4,501,967 | 2,403 |
| Thingsboard | `org.thingsboard.server.common.data.page.BasePageDataIterable#hasNext()Z` | 1,957,300 | 1,477 |
| Conductor | `com.netflix.conductor.core.execution.tasks.SubWorkflow#start(Lcom/netflix/conductor/model/WorkflowModel;Lcom/netflix/conductor/model/TaskModel;Lcom/netflix/conductor/core/execution/WorkflowExecutor;)V` | 140,544 | 1,098 |
| Conductor | `com.netflix.conductor.core.execution.WorkflowExecutorOps#scheduleTask(Lcom/netflix/conductor/model/WorkflowModel;Ljava/util/List;)Z` | 89,500 | 1,263 |
| Stirling-PDF | `stirling.software.common.model.ApplicationProperties$TempFileManagement#getBaseTmpDir()Ljava/lang/String;` | 625,201 | 2,160 |
| Stirling-PDF | `stirling.software.SPDF.service.CertificateValidationService#loadJavaSystemTrustStore()V` | 395,590 | 1,658 |
| OWASP | `org.owasp.benchmark.testcode.BenchmarkTest02160#doPost(Ljavax/servlet/http/HttpServletRequest;Ljavax/servlet/http/HttpServletResponse;)V` | 101 | 101 |
| OWASP | `org.owasp.benchmark.testcode.BenchmarkTest00660#doPost(Ljavax/servlet/http/HttpServletRequest;Ljavax/servlet/http/HttpServletResponse;)V` | 100 | 100 |

| Project | Estimated allocated GiB | PublicationIndex.addAll on-stack CPU share | Raw-summary scan on-stack share |
| --- | --- | --- | --- |
| Thingsboard | 789.3 → 1263.1 | 17.6% → 20.6% | 6.8% → 8.1% |
| Conductor | 242.5 → 2074.8 | 21.1% → 35.9% | 6.6% → 10.9% |
| Stirling-PDF | 595.0 → 3073.7 | 25.4% → 39.1% | 8.1% → 12.1% |
| OWASP | 65.5 → 64.2 | 1.1% → 0.3% | 0.2% → 0.1% |

These are sampled JFR observations from run-2, with heap-dump bounds excluded. Allocation weight is estimated allocation volume, not retained memory. Inclusive scopes overlap and must not be added. The recording event spans cover all eight requested active windows. This checks span coverage; JFR still samples CPU and allocation events. Recording hashes and exact windows are pinned in the machine-readable evidence.

Conductor and Stirling-PDF allocate several times more before stopping at 16 GiB. Publication insertion and full-summary scans take larger sampled shares. This supports work avoidance at query/publication admission, alongside the retained static relation problem. It does not measure the speedup of a proposed fix.

## Interpretation

- **16 GiB is not sufficient for the three failing run-2 analyses.** The larger heap extends partial execution, but all three still reach the guard.
- **The failure is not explained only by reclaimable caches.** The OOM path has cleared managed caches, while query, method, summary, subscription, and pending-publication state remains.
- **The workload has two important patterns.** Static marked relations dominate Conductor and Stirling-PDF. Thingsboard remains mainly nonstatic and has a large duplicate-publication queue.
- **Two heap limits do not prove unbounded growth or an infinite loop.** These runs stop at different points before reaching a fixed point. They do not establish the exact final live-set bound, nor rule out completion at some larger limit. They do show that a small heap adjustment to 16 GiB does not solve the observed failures.

The next changes should target the replicated relation/work products and repeated whole-summary replay. An OOM later in a longer partial run is not evidence that the underlying workload has been reduced.

## Evidence and checks

The [machine-readable report](bidirectional-run2-16g-memory-20261026.json) preserves the exact census data, comparison inputs, phase markers, hashes, counters, and profile windows. The baseline is [the prior run-2 investigation](bidirectional-run2-memory-and-workload-20261025.md). Raw evidence is under `/drive-testcomp/opentaint-go-rules/run2-16g-20261026`.

All three guard heaps are bound to run-2 before cancellation. The OWASP live dump is from a separate run-2 diagnostic, not a later iteration or the initial ZERO-only phase. The timed outcomes above remain the authority for completion and latest iteration.

The decoder checks complete map/collection contents, shared-DAG path multiplicity, exact actor/query/store counts, and whole-heap root-byte partitions. Its existing controls pass. Per-store pattern counts are complete. For later heaps, physical fact class counts replace the additional whole-heap physical-pattern pass; the reported method/call/summary partitions use the same decoder logic. Offline MAT memory budgets do not change the analyzer’s 16 GiB limit. The first Conductor parse was stopped after repeated full GCs in the offline tool. The failed attempt is preserved; the successful retry uses a larger old generation. Its offline HPROF page cache also needed a temporary memory-pressure cleanup. The remaining reads use a stricter soft-cache policy. These changes affect the reader process only. All reported census outputs come from complete queries.

The rules, models, Conductor extension, and compiled approximations match the frozen baseline at both start and end. Large shared IR/dependency trees are not fully hashed. Inputs, core source, and analysis flags are unchanged. Old raw evidence is retained; only rebuildable MAT indexes are removed for disk space. No analyzer implementation or semantics are changed.

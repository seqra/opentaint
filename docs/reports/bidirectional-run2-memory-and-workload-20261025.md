# Run-2 memory and workload — 2026-10-25

The four selected projects complete run-1. On the three OOM projects, run-2 has two major costs: replicated concrete relations and repeated summary publication. The successful OWASP sample instead keeps much of its memory in rebuildable form caches. Thingsboard also starts run-2 with a large retained program, rule, and guidance footprint. Static relations dominate Conductor and Stirling-PDF. Nonstatic relations dominate Thingsboard.

This report changes no analyzer behavior. All measurements use FULL marks in run-1, statics enabled, and the existing alias-analysis configuration.

## Progress and evidence scope

| Project | Run-1 engine | Run-2 result / engine time | Latest reached | Latest completed | Latest accepted forward report |
| --- | --- | --- | --- | --- | --- |
| Thingsboard | 392.439 s | OOM / 149.784 s | run-2 | run-1 | run-1 |
| Conductor | 13.673 s | OOM / 67.265 s | run-2 | run-1 | run-1 |
| Stirling-PDF | 25.288 s | OOM / 107.438 s | run-2 | run-1 | run-1 |
| OWASP | 93.900 s | COMPLETE / 40.263 s | run-11 | run-11 | run-11 |

These are the unchanged full-campaign results from [the previous performance report](bidirectional-flow-backed-concrete-performance-20261024.md). The three OOM snapshots are live heaps captured by the memory guard during run-2. “OOM” is the analyzer result; this report does not replace it with a claim about a JVM allocation failure.

The measured implementation is `5ec1b30be614a0cfdc31ec3102bfa2f9301ee21e`. Extra diagnostic captures use documentation HEAD `0a941b541b5242c5eca9c5229ecbd92776359965`. Both have core tree `e3ede1a36d3b04d79a23cc93285f385ecd968dbf`.

Extra Thingsboard and OWASP runs were stopped on purpose after live heap capture. Their latest reached iteration is **run-2**, their latest completed iteration is **run-1**, and their accepted forward report is **run-1**. They do not replace the full-campaign outcomes above. External heap capture forces GC and adds pauses; its timings are not benchmark results.

A header is one `Facts` object. A membership is one stored output path/mark or FLOW path under a method, premise, statement, and layer. A tree can contain many memberships. The same immutable header can be shared by several stores. Neither count is a count of distinct program taints.

`Z` means ZERO. `S` means the static base. `NS` means any nonstatic base, including arguments, receiver, locals, and return. Arrows in the run-2 tables follow the **stored backward relation**, from premise to conclusion. They do not show forward program flow.

## 1. Thingsboard memory after run-1

The live early-run-2 snapshot contains **5.871 GiB** and 189,136,648 objects. Capture was requested 64 ms after the run-2 start marker. At the snapshot, initialized run-2 actors had processed 18,396 deltas, and had admitted **zero nonzero current queries**. Two additional actors were under construction with zero work counters. This is a close post-run-1 sample, not an exact stop at the handoff barrier.

| Retained owner / union | Bytes | GiB |
| --- | --- | --- |
| IR RAM relationship storage | 2,236,728,608 | 2.083 |
| Method forms and form caches | 907,247,592 | 0.845 |
| Incoming demand guidance | 845,962,376 | 0.788 |
| Rule provider and resolver views | 842,946,440 | 0.785 |
| Reports plus vulnerability witnesses | 165,306,088 | 0.154 |
| Persistent NORMAL summary records | 141,321,560 | 0.132 |
| New run-2 method execution | 2,097,352 | 0.002 |
| New raw/selected summaries | 1,341,104 | 0.001 |
| Publication/subscription state | 6,396,840 | 0.006 |

Retained unions are **not additive**. Shared objects can be retained only by a joint removal of owners. The IR row is one physical dominator. The other rows use the exact retained set of the named owner families.

The high starting footprint is mainly program data, compiled method forms, resolved rules, and the handoff index. It is not an unreleased run-1 static service or a retained run-1 method-edge graph. The live sample has zero `Run1StaticService`, zero `FlowBackedSummaries`, and zero `RunResult` objects.

There are **4,239,145 `TaintMethodExitSink` objects** already live at this boundary. Their shallow object storage uses **203,478,960 bytes**. Their conditions, positions, specialization data, and lists cost more. These are actual exit-sink rules, not the ignored `trackFactsReachAnalysisEnd` list. The provider/form owner measurements show that rule materialization remains a major part of Thingsboard’s retained footprint; they do not prove which cache entries can safely be removed.

The handoff also retains **154,239 NORMAL records** and **256,220 sink witnesses**. The reports and vulnerability store share witnesses, so they were measured together. The early sample has 161,294 FLOW headers and 256,962 TAINT headers. At the original run-2 OOM snapshot, the FLOW count is still 161,294, while the TAINT count has grown to 9,521,644.

The repeat diagnostic produces 2,380,574 explicit handoff pairs, versus 2,379,523 in the original campaign: 1,051 more pairs (0.044%). Both have 73,599 method keys, 102,187 DEMAND report entries, and 154,881 seeds. Thus the two snapshots are separate executions of the same fixed workload; subtracting their bytes is not an exact allocation trajectory.

## 2. Memory during run-2

| Owner / retained union (GiB) | Thingsboard | Conductor | Stirling-PDF | OWASP |
| --- | --- | --- | --- | --- |
| Whole live heap | 10.605 | 7.094 | 7.101 | 4.288 |
| IR RAM relationship storage | 2.094 | 2.091 | 0.913 | 0.503 |
| Method execution | 2.034 | 1.500 | 3.542 | 0.093 |
| Raw and selected summaries | 0.653 | 0.426 | 0.444 | 0.031 |
| Publication and subscription stores | 1.141 | 0.793 | 0.725 | 0.041 |
| Call-input accumulators | 0.317 | 0.234 | 0.225 | 0.005 |
| Incoming demand | 0.785 | 0.033 | 0.015 | 0.043 |
| Current queries | 0.075 | 0.035 | 0.034 | 0.002 |
| Persistent NORMAL records | 0.132 | 0.032 | 0.009 | 0.018 |
| Method forms | 0.863 | 0.199 | 0.208 | 0.378 |
| Rule provider / resolver views | 0.792 | 0.057 | 0.127 | 0.077 |
| Reports / vulnerability witnesses | 0.154 | 0.000 | 0.001 | 0.044 |

| Soft-reference-root form cache payloads | Thingsboard | Conductor | Stirling-PDF | OWASP |
| --- | --- | --- | --- | --- |
| GiB | 0.000 | 0.000 | 0.000 | 2.496 |

The form-directory union above does not own every cached payload: both the cache slot and the managed reference queue hold the reference. A disjoint dominator-root census finds **2.496 GiB (58.2% of the live OWASP sample)** beneath soft references to `FormsCache.ForwardReversePayload`. These payloads hold forward forms and cached backward reversals. They are rebuildable caches, not millions of active backward relations.

Thingsboard's early post-run-1 sample retains another **0.102 GiB** beneath such form-cache references. The three original OOM heaps have **zero bytes under SoftReference dominator roots**. Their logs show managed cache cleanup before capture. Thus reclaimable form-cache retention explains much of OWASP's memory, but it does not explain away the OOM projects' active relation storage. This zero is about the measured root partition; it does not assert that no strongly pinned form exists.

The cache census groups the disjoint dominator roots by class and by referent class. Its root-byte sum equals the whole live heap in every sample. This check also prevents the owner-union table from hiding the large OWASP cache component.

Call-input accumulators are included in the publication/subscription family. Do not add those rows. All other retained-union rows are also nonadditive.

`MethodEdgeStore` keeps a conclusion group at each occupied premise/statement coordinate. Run-2 uses the scalar representation. Its raw summaries, selected summaries, publication index, call-input directories, and query sets are separate owners. They share some immutable AP data, but keep separate indexes, maps, lists, and relation coordinates.

The run-1 compact diagonal stores, FLOW-backed summary replacement, and FLOW-first batching are selected only for run-1 FULL mode. They are not active in run-2. Run-2 has no retained run-1 static pool. It uses ordinary backward call propagation.

| Project | Method/premise arrays | Occupied cells | Stored output memberships | Array shallow MiB |
| --- | --- | --- | --- | --- |
| Thingsboard | 1,570,752 | 4,251,218 | 8,936,562 | 98.4 |
| Conductor | 754,372 | 3,479,808 | 4,127,680 | 54.5 |
| Stirling-PDF | 762,649 | 8,613,786 | 9,871,214 | 102.8 |
| OWASP | 21,429 | 128,698 | 792,986 | 1.8 |

The statement arrays alone are a small part of execution memory. The larger multiplication is the number of occupied relation coordinates and their group/map/list/TAINT payloads. Output marks already merge within a fixed coordinate. Different initial premises and caller references remain separate.

### Pending summary publications

| Project | Pending offers | Unique identity pairs per method | Exact duplicate offers (lower bound) | Duplicate share | Pending-list retained GiB |
| --- | --- | --- | --- | --- | --- |
| Thingsboard | 10,371,275 | 172,031 | 10,199,244 | 98.3% | 0.287 |
| Conductor | 471,537 | 19,931 | 451,606 | 95.8% | 0.013 |
| Stirling-PDF | 2,195,367 | 55,929 | 2,139,438 | 97.5% | 0.059 |
| OWASP | 34,583 | 34,583 | 0 | 0.0% | 0.003 |

The duplicate test uses the same method owner, the same canonical premise object, and the same immutable conclusion object. It counts definite repeat offers. Equal conclusions held in different objects are not counted as duplicates. Thus the duplicate count is a lower bound. The Thingsboard pending-list union retains about 0.287 GiB. This is a clear source of avoidable work, but it does not account for its whole 10.605 GiB heap.

This state is in `RunMethodAnalyzer.pending`, before the shared publication index removes duplicates. Delivery batches are a different queue and can share publication objects across recipients.

| Project | Queued delivery events | Delivery list memberships |
| --- | --- | --- |
| Thingsboard | 8,548 | 166,700 |
| Conductor | 22 | 96 |
| Stirling-PDF | 27 | 300 |
| OWASP | 0 | 0 |

The source contains this repeat path:

```kotlin
val starts = currentQueries.admit(added, guides)
if (starts.isNotEmpty()) {
    for ((premise, facts) in summaries.all()) {
        if (currentQueries.permits(premise)) {
            queuePublications(premise, facts) // appends a new Publication
        }
    }
    starts.forEach(::addInitial)
}
```

A new query makes the actor scan **all** old raw summaries. Previously authorized summaries are offered again, including summaries for other premises. A busy actor can collect these offers before its work event flushes `pending`. Later deduplication prevents a repeated semantic publication, but it does not prevent these allocations, retained queue entries, or repeated insertion tests.

In Thingsboard, `BasePageDataIterable.next()` alone holds **2,085,407 pending offers** after only 13,018 processed deltas. `hasNext()` holds another **721,893**. This is direct evidence of large auxiliary work, separate from new fact derivation. The heap confirms definite repeat offers; the source identifies a mechanism that creates them. This report does not assign every duplicate to one call site without a runtime provenance counter.

## 3. Demand guidance for run-2

| Project | Explicit incoming demand pairs | Method keys | Sink seeds |
| --- | --- | --- | --- |
| Thingsboard | 2,379,523 | 73,599 | 154,881 |
| Conductor | 72,881 | 17,417 | 60 |
| Stirling-PDF | 36,772 | 7,258 | 1,012 |
| OWASP | 133,966 | 12,083 | 11,077 |

These are the exact normalized `(MethodKey, DemandPattern)` pairs from the original run-1 handoff. Each OOM heap census matches its frontier count. OWASP’s later diagnostic matches its original 133,966 pairs as well.

These counts exclude the implicit ZERO query and the symbolic static-group guidance family. The run-1 handoff enables `staticGroupsEnabled` and `COMPLETE_RUN1_STATIC_FIELDS`. The family is represented by a policy, not a materialized method-by-field product. Do not interpret the explicit pair count as the total executable query space.

OWASP’s **outgoing run-2** handoff has 122,428 pairs in 6,172 method keys and 30,557 source seeds. That is guidance for run-3; it is not the incoming run-2 count.

The actor counter named `demandLayerEdges` is also not this count. It counts queued DEMAND deltas and an input-presence marker. Neither it nor a count of selected run-2 summaries is a completed run-2 handoff for the three OOM projects.

| Project | Run-2 input arrivals | Demand-guide intersections | New method-local initials | New call-input groups |
| --- | --- | --- | --- | --- |
| Thingsboard | 3,794,889 | 34,132,382 | 1,609,008 | 2,067,458 |
| Conductor | 1,690,740 | 1,785,400 | 770,455 | 1,392,371 |
| Stirling-PDF | 1,630,966 | 1,689,129 | 769,456 | 1,329,510 |
| OWASP | 29,855 | 42,920 | 32,504 | 10,076 |

The counters above subtract run-2 START totals from END totals. They are cumulative activity over the original run-2, including work after the heap sample. They are not counts of currently live objects.

The current implementation uses `StrongQueries` on restricted runs. `admit` starts canonical queries from **actual current marked inputs**, independently of whether an explicit old guide exists; concrete guides can add refined intersections. A named static ANY input can also start its corresponding EXACT query. `permits` then authorizes the current premise’s raw summaries.

Consequently, the incoming explicit demand count does not cap the number of method-local queries or stored relations. This is an existing runtime mechanism, not a change made for this investigation.

## 4. Static and nonstatic facts

| Project / snapshot | Current queries | Static queries | Nonstatic queries | Static share |
| --- | --- | --- | --- | --- |
| Thingsboard | 1,552,230 | 460,648 | 1,091,582 | 29.7% |
| Conductor | 752,989 | 668,987 | 84,002 | 88.8% |
| Stirling-PDF | 762,200 | 720,518 | 41,682 | 94.5% |
| OWASP | 17,161 | 2,510 | 14,651 | 14.6% |

Query counts are method-scoped memberships. The same interned AP in 1,000 methods counts 1,000 times. ZERO initials are not included in this query table.

The next table classifies stored **method output memberships** by conclusion base. All these measured method outputs are TAINT. Control REACH rows are counted separately in the machine-readable artifact. The physical heaps also contain FLOW objects retained from run-1 records and reporting state; their presence is not evidence of FLOW-first execution in run-2.

| Project | Static outputs | Nonstatic outputs | Static share | S → S outputs | S → S share of all outputs |
| --- | --- | --- | --- | --- | --- |
| Thingsboard | 1,305,432 | 7,631,130 | 14.6% | 1,065,179 | 11.9% |
| Conductor | 3,494,315 | 633,365 | 84.7% | 3,344,118 | 81.0% |
| Stirling-PDF | 9,444,494 | 426,720 | 95.7% | 8,688,516 | 88.0% |
| OWASP | 39,357 | 753,629 | 5.0% | 8,770 | 1.1% |

| Backward premise → conclusion | Thingsboard | Conductor | Stirling-PDF | OWASP |
| --- | --- | --- | --- | --- |
| Z->NS | 3,807,557 | 28,220 | 47,277 | 675,123 |
| Z->S | 182,147 | 96,536 | 714,023 | 30,587 |
| NS->NS | 3,821,920 | 588,490 | 331,175 | 78,506 |
| NS->S | 58,106 | 53,661 | 41,955 | 0 |
| S->NS | 1,653 | 16,655 | 48,268 | 0 |
| S->S | 1,065,179 | 3,344,118 | 8,688,516 | 8,770 |

`S → S` includes both same-field and different-field relations. This census does not label every such edge as an identity. Named fields and special EXACT class markers are separate in the static-position census. The field limit is one counted field in run-2; a static class accessor plus its field uses two encoded accessors.

### Thingsboard: nonstatic marked relations and publication growth

Nonstatic outputs dominate. Two large families are sink-seeded `Z → NS` relations and `NS → NS` relations under marked method premises. Sink seeds start backward facts with a ZERO premise; such rows must not be mistaken for ZERO control or for unconditional forward sources.

The largest stored shape buckets include `Z → LocalVar / EXACT / NORMAL`, with 912,826 memberships in trees of maximum accessor depth one; `NS → This / EXACT / NORMAL`, with 740,602; and `Z → Argument / EXACT / NORMAL`, with 640,320. A maximum-depth bucket can include shorter paths in the same tree.

`pruneNode(ObjectNode, Set, String, ObjectMapper)` processes **858,049 deltas** and retains **208,492 output memberships**. `processPattern(String, TbMsg)` processes **268,282**. These are high-work methods, while the highest pending-publication owners are the small iterable and identifier accessors described above.

Statics are still material. Hot static positions include `SortOrder.Direction.ASC` (55,640 NORMAL and 60,740 DEMAND memberships), `HousekeeperTaskType.DELETE_LATEST_TS` (56,486 NORMAL), and `EntityType.DEVICE` (25,117 DEMAND). These are measured positions, not a claim that enum constants are mutable. Static handling alone cannot explain Thingsboard’s total run-2 workload.

### Conductor: static fields across method and call coordinates

The main method-store shapes are `S → S / ANY / DEMAND` at encoded depth two (**1,553,621 memberships**) and `S → S / EXACT / NORMAL` at depth two (**1,531,293**). The ANY and EXACT query counts are both about 330,000. They are distinct semantic query forms, not duplicates that this report proposes to discard.

Generated `__spring_registry__` fields dominate the static position census. Examples include `ExecutionDAO` (168,943 NORMAL / 212,925 DEMAND), `ExternalPayloadStorage` (170,032 / 210,397), and `IndexDAO` (162,536 / 196,453). Constants and enum fields also recur.

`ParametersUtils.replaceVariables` processes **347,373 deltas**, `ParametersUtils.replace` **207,058**, and `ExecutionService.poll` **132,978**. The run-2 call-input directory holds 1,487,753 output memberships, including 1,242,625 `S → S` memberships. This is ordinary static call traffic, not retained run-1 read subscriptions.

### Stirling-PDF: static registry propagation is the main stored workload

The two largest shapes are `S → S / EXACT / NORMAL` at depth two (**4,201,875 memberships**) and `S → S / ANY / DEMAND` (**4,046,032**). The call-input directory has 1,428,152 memberships, of which 1,274,728 are `S → S`.

The `__spring_registry__.ApplicationProperties` field alone accounts for **1,177,909 DEMAND memberships** in method stores. `PipelineProcessor` and `PdfJsonConversionService` registry fields add 507,643 and 503,183 respectively.

`GetInfoOnPDF.getPdfInfo` processes **2,900,803 deltas**, with 131,741 changed delta enqueues and 129,880 stored output memberships. `PipelineProcessor.runPipelineAgainstFiles` processes **430,758 deltas**. The gap between processed deltas and changed enqueues includes unchanged propagation; it is not by itself proof of duplicate facts or an infinite loop.

### OWASP: successful run-2; use an active marked-phase sample

The selected OWASP heap has 12,083 initialized backward actors, 6,238,819 processed deltas, and 17,161 current query memberships. It is a diagnostic sample, not a peak-memory measurement or a completed run-2 relation set. The original run-2 completes and starts only 32,504 new method-local initials and 10,076 call-input groups over its whole execution. This is much less interprocedural expansion than on the other projects.

The earlier OWASP sample at about 20 seconds had 299,047 processed deltas but **no nonzero admitted queries**. It measured the ZERO-control phase and cannot establish a zero static workload for run-2. It is retained as evidence and excluded from the main static/nonstatic comparison.

## 5. CPU and allocation evidence

| Project | Stacked CPU samples | Estimated allocated GiB | Elapsed excluding dump bounds (s) | Contained GC pauses (s) | TAINT subsumption on-stack CPU share |
| --- | --- | --- | --- | --- | --- |
| Thingsboard | 32,049 | 789.3 | 120.277 | 47.469 | 21.9% |
| Conductor | 11,457 | 242.5 | 49.801 | 24.051 | 29.7% |
| Stirling-PDF | 23,656 | 595.0 | 88.567 | 34.173 | 34.7% |
| OWASP | 1,524 | 65.5 | 40.263 | 1.636 | <5% |

These are the original continuous JFR recordings, restricted to run-2 and with logged heap-capture intervals excluded. Allocation weight is a sampled estimate of allocation volume, not retained bytes. GC pause time is from fully contained events; boundary-crossing events are not added.

The three OOM projects spend about 39–48% of the remaining wall interval in contained GC pauses. `TaintGroup.add` and `subtractSubsumed` repeatedly appear in sampled stacks. Call processing, summary insertion, and subscription handling are also frequent. This agrees with the large relation stores and repeated pending offers.

Inclusive scopes overlap. In particular, `FormsCache.withForm` and `transportProtection` call the operation inside their scope. Their inclusive percentages do not measure cache rebuilding or protection overhead alone. The run-2 heaps have no active compact diagonal owners. Thingsboard and Conductor have no protected TAINT headers; Stirling-PDF has 81, all referenced by retained `SinkEdge` objects. Protection annotations do not explain the millions of run-2 relations.

There is no evidence here that an infinite loop is needed to explain the OOMs. The measured finite query, relation, queue, and allocation counts are already large. These snapshots and profiles do not constitute a termination proof.

## Conclusions and next investigation targets

1. **After run-1, Thingsboard retains a large baseline.** The largest owners are IR storage, method forms, rule resolution, and the 2.38-million-pair demand index. The run-1 execution/static services have been released.
2. **Run-2 reintroduces a large concrete relation space.** It uses scalar, premise-colored method and call stores. Small field depth does not bound the product of methods, origins, statements, callers, layers, paths, and full marks.
3. **OWASP retains rebuildable form caches:** 2.496 GiB in its marked-phase sample. The OOM heaps have already cleared soft-reference-root caches.
4. **Static propagation is the leading stored pattern on Conductor and Stirling-PDF.** Generated Spring registry fields are a major part of it. Thingsboard needs a broader explanation: its stored facts are mostly nonstatic, with a large sink-seeded ZERO-premise component.
5. **Publication management contains definite avoidable repetition.** New current queries rescan and offer previously authorized raw summaries; millions of offers wait before publication-index deduplication. A follow-up design should address admission and merging at this earlier boundary, while preserving newly authorized summaries and annotation changes.

The next design should separate those causes. A static-only fix will not remove Thingsboard’s nonstatic workload. A smaller AP container alone will not prevent repeated full-summary replay. This investigation does not change query authorization, static precision, field processing, mark semantics, or persistence.

## Evidence, controls, and limits

The [machine-readable report](bidirectional-run2-memory-and-workload-20261025.json) contains exact counts, per-shape partitions, top methods, source/heap hashes, and retained-owner values. Raw evidence is under `/drive-testcomp/opentaint-go-rules/run2-memory-investigation-20261025`. Original OOM heaps, logs, and timings remain under `/drive-testcomp/opentaint-go-rules/run1-flow-backed-20261024`.

The heap census uses a private Eclipse MAT query extension. It reads the full maps and tries; no table export cap is used for fact membership counts. Controls cover shared-DAG path multiplicity, colliding hash keys, identity maps, unmodifiable collections, set deduplication, fastutil values including key zero, and rejection of missing fields. A separate pending-publication fixture verifies duplicates within one method and preservation across different method owners. The small metadata CSV exports reconcile with heap actor counts and stay below their export cap.

The first new Thingsboard capture attempt failed in the benchmark helper because `JAVA_HOME` was unset after a completed run-1. It is preserved as `capture-attempt1.json`; it is not counted as an analyzer failure. The corrected attempt sets the same Java 17 toolchain explicitly. An initial decoder attempt rejected an unsupported fastutil map; the decoder was extended and controlled before accepting counts. The early Thingsboard all-in-one census rejected an actor interrupted during construction. Its memory owners were rerun successfully as a separate complete query; a second complete actor query records the two zero-counter constructor objects explicitly. Failed attempts remain in the evidence directory.

The extra OWASP captures deliberately stop during run-2. The full campaign still reaches and accepts **run-11** on OWASP, and reaches **run-2** with completed/accepted **run-1** on the other projects.

A heap gives stored and pending state at one instant. Actor counters give cumulative processed delta counts, but do not record each processed fact’s static/nonstatic type. Thus the report gives **exact snapshot partitions**, plus historical method counters and sampled CPU evidence. It does not claim exact historical static/nonstatic processing counts or equivalent progress across unequal snapshots.

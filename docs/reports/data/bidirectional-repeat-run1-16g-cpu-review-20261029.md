# CPU and GC evidence for the16g REPEAT_RUN1 experiment

Runtime: `c2bc5e78dfdb13f95bda970c5f4e0c247acbac29`. Run-1 mark mode is FULL. Field limits are1,1,2,3,... . All four primary analyses closed before the reader work. No primary analysis had OOM. No new HPROF exists. No MAT process, heap control or manual dump ran. These data do not give a new retained-owner layout.

The larger heap avoids the old conductor run-4 guard OOM in this test. It does not complete that run. Conductor still reaches run-4, completes run-3 and accepts run-3. Stirling still reaches run-6, completes run-5 and accepts run-5. The remaining cost is repeated analysis work with GC CPU cost. A finite timeout does not prove an unbounded memory growth or an infinite loop.

| Window | Seconds | Java samples | GC pause union, s | GC collection union, s | Concurrent GC phase union, s |
|---|---:|---:|---:|---:|---:|
| conductor run4-whole | 956.363 | 25,431 | 6.694 | 278.096 | 272.155 |
| conductor run4-mid30 | 30.000 | 177 | 0.055 | 6.372 | not collected separately |
| conductor run4-late30 | 30.000 | 634 | 0.190 | 8.616 | not collected separately |
| Stirling-PDF run5-whole | 682.927 | 56,752 | 4.413 | 110.338 | 106.822 |
| Stirling-PDF run5-middle30 | 30.000 | 2,252 | 0.046 | 5.457 | not collected separately |
| Stirling-PDF run5-final30 | 30.000 | 2,143 | 0.056 | 2.775 | not collected separately |
| Stirling-PDF run6-whole | 317.764 | 48,987 | 5.581 | 128.486 | 123.940 |

GC collection intervals include full cycles. The separate concurrent-phase union uses `jdk.GCPhaseConcurrent`. GC pause union uses `jdk.GCPhasePause`. Do not add these overlapping interval families. The native profiles use CPU sample weights, not wall intervals or Java-only samples.

Conductor run-4 takes956.363s and stops on timeout. The saved8g run stops on OOM after282.283s, which includes15.796s of heap capture. Current GC pause and collection unions are6.694s and278.096s. The saved unions are18.205s and231.052s. The phase is the same backward run at limit3, but the old run stops much earlier. This is not a matched amount-of-work speed comparison.

The current conductor handled-event counter stays at2,649,089 from09:09:44.550 to09:16:24.575, a400.025s observed span. This counter counts completed reservations. `UnitRunner` does not count each fact operation or each incomplete Work quantum. It can also process a whole delivery before it counts that event. In the requested middle30s,176of177 Java samples contain `SubscriptionManager.onDelivery`. That code loops over publications, premise members and current caller-input candidates. It therefore shows work inside delivery, although it does not identify one exact event for the whole400s. Later completion counts rise again. The middle30s has only0.055s of GC pause union; a full30s stop-the-world pause does not explain the plateau. No native CPU window covers this middle span, so its total CPU use is not measured by Java samples alone.

Conductor late30s has74.92% inclusive Java call-pipeline samples. `DiagonalRelations.borrow` is the leaf in28.23% of634 samples. The observed call path is subscribe → replay → SummaryStorage candidates → PublicationIndex publications → DiagonalRelations borrow. The source iterates all header scopes and then tests the exact initial. This is a direct repeated-search candidate. The profile does not count unrelated scopes or prove a fixed speedup. Late native GC accounts for47.53% of5,712 CPU sample weight.

Stirling forward run-5 completes in682.927s. The saved8g run takes796.302s, including15.489s of manual dump time. Collection union falls from601.054s to110.338s; current concurrent phases occupy106.822s. The run remains long after GC pressure falls. In both current middle and final30s, the completion counter rises by about1,000 per10s. This is not a scalar fact-operation rate.

Stirling run-5 Java leaves include `CallExprVisitor.defaultVisitJIRInst`10.33% and `JIRLanguageManager.getCallExpr`8.87%. Exact stacks show process → RunMethodContext.callAt → getCallExpr → assignment instruction visitor. The whole run has `emitUnchanged` in34.98% of Java samples. It already avoids persistent point-store writes, but still schedules work and classifies instructions. `FormsCache.withForm` is inclusive in58.76%; it includes the callback. This does not prove form rebuilding, cache misses or cache thrashing. The IR API/storage family also includes instruction visitors and is not a retained-memory estimate.

Stirling backward run-6 stops on timeout after317.764s. Call pipeline is84.23% inclusive and protection is54.52% inclusive of48,987 Java samples. `NodePair.equals` is the leaf in22.75%; `intersectTaintMask` is the leaf in7.91%. Exact paths enter through emitCovered → MethodEdgeStore.add → TaintGroup.add → withRoot/withProtection → intersectTaintMask → memo HashMap lookup. NodePair equality compares two node identities. It is not recursive structural equality. High cost here indicates many protection/memo operations or collision work; the data do not separate those two causes. Near-limit native GC has44.70% of10,786 CPU sample weight; protection has26.24% of that native denominator.

Current phase counters also show repeated initial admission attempts. Conductor run-4 has5,395,498 candidates and201,266 fresh initials;5,194,232 attempts repeat an initial already held by the method store. Stirling run-5 has1,800,094 candidates and466,826 fresh initials. Run-6 has907,635 and146,795. These are START-to-END differences of cumulative counters. They are not duplicated retained initials. They do not justify skipping input storage, subscriptions or geometry effects at the outer call boundary.

The next investigation should test which joins, header scans, unchanged instruction visits and protection re-intersections can be omitted without a semantic change. The reader results do not authorize an implementation change or prove a twofold workload reduction. No current static/nonstatic retained-header census is available.

## Evidence and reader checks

All seven windows lie within observed recording spans. Every Java sample has a stack and zero stacks are truncated. The five original controls pass on a fresh source compilation. A separate exact-leaf/concurrent-phase control passes. Extension whole-window sample counts and selected leaf totals match the original reader output. Source, class, input profile and output hashes are saved. The primary continuous recordings retain the same final hashes. The isolated OWASP diagnostic is outside these paths and windows.

One post-reader Python wrapper failed on9digit timestamp parsing and then fractional-padding equality. Its logs remain. The completed first result was validated and reused; its successful reader did not run again. Raw nanosecond timestamps remain in the JSON. See `preparation/cpu-wrapper-reconciliation.json`.

Files: `summary.json`, `read-receipts.json`, `path-read-receipts.json`, `runtime-source-binding.json`, `phase-counter-deltas.json`, both scheduler extracts, both native receipts, and `analysis-tools/family-jfr-reader/*controls*.json`. Family shares overlap. They cannot be added or used as wall-time shares. JFR heap-used observations are not retained-owner measurements.

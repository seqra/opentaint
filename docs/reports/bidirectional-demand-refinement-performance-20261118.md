# Bidirectional demand refinement performance

The project scans used commit `1197f72f7cf773aeb4a77e42dd923fe8f6f0003b`
and enabled revised demand refinement for the FULL diagnostic policy. The
production policy uses native demand refinement while the comparative
activation proof is open. [Implementation and activation requirements](../design/bidirectional-demand-refinement-implementation-20261118.md)

The Conductor isolation runs identify **R32 on shared static carry**
as a cause of the run-2 memory regression. Restoring the previous
EXACT start only for the carry route enabled run-2 to complete in
183.584 s, with R32 for explicit and virtual rows and qualified
delivery still active. The qualified reply channel independently
amplifies work and memory. Disabling it also completed run-2, with
a much smaller H2. The [Conductor comparison](#conductor-rule-isolation)
records remaining costs and coverage limits.

The finding reference is the saved build at
`54ad708fe1c4f551956d3d572866de1534415fa1`. The comparison uses rule ID,
sink fingerprint, full method signature and occurrence count. The physical
and logical locations also agree for every shared occurrence. The legacy
reference has no bidirectional run numbers.

## Project results

| Project | Heap / analysis timeout | Reference status / wall s | Diagnostic status / wall s | Latest reached / completed / accepted forward | Exact findings reference / diagnostic | Missing / extra |
| --- | --- | --- | --- | --- | --- | --- |
| OWASP | 8 GiB / 1,000 s | Complete / 156.357 | Run limit / 233.102 | run-11 / run-11 / run-11 | 2,633 / 2,633 | 0 / 0 |
| Conductor | 8 GiB / 1,080 s | OOM / 187.389 | OOM / 311.024 | run-2 / run-1 / run-1 | 7 / 2 | 5 / 0 |
| ThingsBoard | 12 GiB / 1,080 s | OOM / 439.652 | OOM / 333.842 | run-1 / none / none | 15 / 0 | 15 / 0 |
| Stirling-PDF | 8 GiB / 1,080 s | Complete / 52.109 | Timeout / 1,118.766 | run-4 / run-3 / run-3 | 24 / 28 | 10 / 14 |

OWASP has all reference occurrences and no extra occurrence. Its 2,633
occurrences were confirmed and the final report had no provisional
occurrence. Conductor published two confirmed occurrences before the
memory guard stopped run-2. Both are reference occurrences. The five
absences compare a run-1 accepted result with a partial legacy result.
The diagnostic analysis did not reach the refinement runs needed to
assess those five paths. ThingsBoard stopped before the first
accepted forward result. Its 15 missing occurrences have the same
incomplete-result limitation.

Stirling-PDF kept 28 confirmed occurrences at the run-4 timeout.
Fourteen match exactly. Seven of the ten missing exact locations
have a report at a different return of the same method and rule.
The analyzer joins exit rules at a synthetic normal exit. Its simple
report can render another return when the descriptor has no witness
location. These seven differences remain strict location mismatches.
Three baseline methods have no same-rule report in the diagnostic
output: `ProcessExecutor#runCommandWithOutputHandling`,
`LicenseKeyChecker#getLicenseKeyContent` and
`InviteLinkController#validateInviteToken`. The timeout prevented
another forward barrier. The accepted output cannot show whether
further refinement would recover these methods. The 14 extra locations
include the seven different returns and seven additional method and
rule pairs. The location comparison does not establish that those
seven findings are false positives. [Exit location rendering](../../core/src/main/kotlin/org/opentaint/jvm/sast/sarif/TraceMessageBuilder.kt#L1167)

Wall time includes project preparation and report output. Incomplete
iterations have no accepted barrier from that iteration. Benchmark
numbers compare the two measured configurations, which use different
engines. They cannot isolate the impact of revised C2 or C5.

OWASP used 49.1% more wall time than the reference. Conductor used
66.0% more wall time and reached the guard with fewer findings.
ThingsBoard used 24.1% less wall time and still ran out of memory
before its first accepted result. Its shorter time measures an earlier
stop. Stirling-PDF stopped after 21.47 times the complete reference
wall time.

| Project | Reference peak RSS (GiB) | Diagnostic peak RSS (GiB) |
| --- | ---: | ---: |
| OWASP | 8.58 | 9.75 |
| Conductor | 9.36 | 9.68 |
| ThingsBoard | 13.48 | 13.79 |
| Stirling-PDF | 7.58 | 9.96 |

## Comparison with the previous bidirectional core

The saved bidirectional runs at `472288cf34ddf75290e3fab4d6f5cbc0a366646c`
use the same `core` and `rules` Git trees as the implementation's
parent, `0438facd2a09e44a386b829cb2f1f4fe3d3954a8`. The model
hashes, test revision, heap, timeout, FULL mode, field schedule and
profile options agree. The reference in the first table is the separate
legacy engine. [Previous bidirectional campaign](bidirectional-work-reduction-performance-20261112.md)

| Project | Previous reached / completed / accepted forward | Revised reached / completed / accepted forward | Previous → revised run-1 engine s | Previous → revised run-2 engine s |
| --- | --- | --- | ---: | ---: |
| OWASP | run-11 / run-11 / run-11 | run-11 / run-11 / run-11 | 79.917 → 80.748 | 22.580 → 27.049 |
| Conductor | run-8 / run-7 / run-7 | run-2 / run-1 / run-1 | 19.556 → 21.490 | 41.308 → 219.120, OOM |
| ThingsBoard | run-1 / none / none | run-1 / none / none | 183.641 → 179.704, both OOM | — |
| Stirling-PDF | run-11 / run-10 / run-9 | run-4 / run-3 / run-3 | 21.127 → 24.516 | 13.783 → 41.852 |

Stirling-PDF's run-3 engine grew from 4.224 s to 418.955 s.
OWASP's complete engine time including barriers fell from 151.761 s to
147.720 s, while its run-11 engine grew from 3.169 s to 6.086 s.
ThingsBoard hit the same incomplete run-1 outcome in both measurements.
The largest loss in completed iterations is Conductor.

## Configuration and evidence

The project harness used the source Gradle `:runProjectAnalyzer` task with
the configured project models, aliases and statics enabled, the field
schedule `1,1,2,…` and the run-11 cutoff. It used the 1,200-second
outer limit for each scan. It kept continuous JFR, GC logs, named
30-second CPU windows and an automatic snapshot on memory-guard OOM.
The measured checkout had a test-source modification from earlier work.
The analyzer production sources match the committed revision.

| Project | Model SHA-256 |
| --- | --- |
| OWASP | `e8fd467e410051c3b0b36d461d953780e5819345fd3b7fddc68a3f8769e09873` |
| Conductor | `3457cf5a1b3c63e0710dfa50a9fbca1c4229f2726ea3276cc409e019515ee35d` |
| ThingsBoard | `1246cb43621245e0ef971a51052b54a56abd60725860f44824f00f34d57b58f3` |
| Stirling-PDF | `b62263d3134af8b0c93426dedcd15a976808e4c8e838950c1a4959022d5d3ef4` |

The campaign files are in
`demand-refinement-performance-20261118.DS91bH` in the external
archive. They include per-project launch manifests, analyzer logs,
SARIF comparisons and `measurements.json`. Previous project captures
were cleaned after preservation of their derived reports and manifests.
`previous-capture-cleanup.json` lists 33 obsolete files and
20,409,101,312 bytes removed. [External data layout](EXTERNAL_DATA.md)

## Engine and handoff time

**OWASP reached and completed run-11.** Engine time excludes the
separately measured run-1 static bind. Handoff rows are retained paired
rows after insertion. Target origins are outgoing method and block
records before handoff compaction.

| Run | Engine s | Barrier s | Handoff rows | Target origins |
| --- | ---: | ---: | ---: | ---: |
| run-1 | 80.748 | 2.717 | 84,835 | 6,867 |
| run-2 | 27.049 | 1.051 | 29,215 | 1,918 |
| run-3 | 9.616 | 0.825 | 531 | 735 |
| run-4 | 1.308 | 0.572 | 1,469 | 144 |
| run-5 | 2.340 | 0.669 | 688 | 2,379 |
| run-6 | 0.936 | 0.534 | 1,022 | 63 |
| run-7 | 2.552 | 0.731 | 650 | 4,739 |
| run-8 | 0.759 | 0.598 | 1,035 | 46 |
| run-9 | 4.356 | 1.041 | 756 | 8,797 |
| run-10 | 0.698 | 0.589 | 1,055 | 46 |
| run-11 | 6.086 | 1.268 | 776 | 10,513 |

Run-1 took 84.045 s through its barrier, including 0.482 s of
static binding. The normal 30-second CPU window started 60 seconds
into run-1 and crossed into run-2. JVM worker threads for garbage
collection account for 53.86% of its weighted samples. Frames for
method forms appear in 18.36%. This window describes both phases.
The near-limit profile was unnecessary because the scan finished
before that time window.

Phase-aligned JFR records 3,517 Java execution samples during
run-1. Its bidirectional form payload frame appears in 1,751 of
them. The largest sampled bidirectional allocation sites are call
plan construction and source/sink rule normalization. The run-11
slice has 100 Java execution samples, 61 with
`DemandStore.visitControlPairs` and 60 with
`RestrictedInitialPolicy.rawWitness`. Treat this small slice as
evidence for the terminal lookup hot path. Samples of execution or
allocation are separate from the amount of retained heap.

**Conductor reached run-2 and completed run-1.**

| Run | Engine s | Barrier s | Handoff rows | Target origins |
| --- | ---: | ---: | ---: | ---: |
| run-1 | 21.490 | 2.294 | 173,371 | 7,922 |
| run-2, guard OOM | 219.120 | — | — | — |

Run-1 took 25.152 s through its barrier, including 1.209 s of
static binding. Run-2 elapsed time includes 16.885 s for the guard
snapshot. The heap used 7,737,032,704 bytes when the guard requested
the snapshot. The resulting HPROF file is 11,626,267,020 bytes.
The run-2 CPU window contains 19,965 weighted samples. GC worker
frames occur in 63.89% of samples. Inclusive stacks contain
`ApOps.limit` in 17.28%, `BlockSummaryLinks.deliver` in 12.95%,
`DemandStore.intersectAdmitted` in 11.51%, and
`RestrictedInitialPolicy.rawWitness` in 7.64%. The categories
overlap. Only four of the 3,449 `ApOps.limit` samples include the
field-cut implementation. Of those 3,449 samples, 1,977 include
loop output restriction. The limit frame includes the callback
that consumes the limit result. These samples describe execution
and allocation pressure.

Run-2 stopped after 4,783,762 actor steps and 1,060,969 candidate
offers. The static view logged 4,525,716 C2 states and 9,454,590 C5
states. Among the logged loop owners,
`WorkflowExecutorOps#decide` alone accounted for 1,147,748 boundary
limit offers, zero cuts, 1,058,775 native C5 queries and 1,073,416 local
DATA callbacks. This workload occurs with a one-field limit.

### Conductor run-2 workload growth

| Metric | Previous complete run-2 | Revised run-2 before OOM |
| --- | ---: | ---: |
| Paired rows entering run-2 | 127,044 | 173,371 |
| Owners with incoming rows | 6,804 | 6,804 |
| Direct C2 queries | 1,715,775 | 3,830,439 |
| Static C2 visited states | 99,701 | 4,525,716 |
| Static C5 visited states | 2,895,127 | 9,454,590 |
| Initial keys offered through selected calls | 1,764,796 | 2,730,060 |
| `decide` live local input groups | 3,240 | 5,972 |
| `decide` local DATA publications | 5,907 | 133,031 |
| `decide` local DATA callbacks | 74,594 | 1,073,416 |
| `decide` local C5 queries | 33,909 | 1,058,775 |
| `decide` scalar loop observations | 11,180 | 454,463 |
| `decide` selected saved records | 31,422 | 1,133,107 |
| `decide` local C2 requests / cache hits | 27,970 / 13,764 | 1,061,221 / 0 |
| `decide` loop-boundary cuts / prefix trials | 0 / 0 | 0 / 0 |

There are 36.5% more entering demand pairs and 22.5 times as many
local DATA publications in the hot owner. A local publication can
be a public result or a result for a qualified possible input.
These counters count both. The extra publications and callbacks
show real propagation growth. They do not show how much of the
published set has distinct public edge identities.

The static search also repeated work: the previous path reported
935,842 C2 coverage exits. The revised path reports zero such exits
in its older coverage counter and visits 45.4 times as many states.
Inspection shows that the revised path collects explicit and carry
answers separately from its virtual-lookup coverage. This increases
work per offer. A separate publication or retained-state mechanism
must explain the memory increase.

The H1 change comes from run-1 transfer or projection. The
exact-only handoff compactor (R25) starts after run-2. The new
STAR admission and child bindings (R06/R09–R12 and R32), and
their raw C5 publication path (R18/R20–R22), can increase the
number of local results. R21 also widens the static FLOW search
to concrete selector labels. This run records zero R08 overruns.

The R32 same-head change is a direct route to the largest heap
shape. For a run-2 demand `C.f.*/T` and offer `C.f.*/T,DEMAND`,
the prior C2 starts `C.f.$/T,DEMAND`. R32 starts
`C.f.*/T,DEMAND` plus `C.f.*/FLOW,NORMAL`. Both starts fit
the one-field limit. The concrete start can retain a suffix
through a read and the FLOW companion can open other C5 routes.
The existing run-2 shared static carry creates a same-slot
demand for each static offer through
`staticCarry(leaf)`. It preserves the STAR tail. This supplies
the R32 selector for every such STAR offer, including offers
with an empty method-local demand. [Shared carry lookup](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/store/DemandStore.kt#L235)

The counterfactual test restores the prior same-head start
and keeps the deep relay and other revised rules. This example
describes the tested rule cell. It does not label heap objects by
their originating C2 command.

Revised loop observation bypasses the existing quantum C2 cache
when it needs qualified bindings. This adds repeated lookup, in
addition to the larger number of queries. The native prepared C5
plan already excluded run-2, and both executions made zero prefix
trials in `decide`. The bypass of those optimizations cannot
account for the Conductor regression. The heap census and
focused comparisons will distinguish retained rows from repeated
lookup and replay.

The guard snapshot contains 7,630,618,152 reachable bytes across
209,928,735 objects. The largest analyzer-owned groups are the
active method actors and the subscription input directory. Retained
sizes overlap. Each row describes the retention below that field.

| Retaining field | Retained bytes |
| --- | ---: |
| `UnitRunner.actors` | 1,339,868,232 |
| `SubscriptionManager.inputDirectory` | 1,272,443,856 |
| `CalleeSubscriptions.values` | 1,134,125,536 |
| `MethodBlockRuntime.entries` | 549,891,968 |
| `RunMethodAnalyzer.edgeStore` | 389,228,768 |
| `PublicationIndex.qualified` | 213,640,960 |
| `CalleeSubscriptions.bound` | 5,378,744 |
| Local block delivery queues | 2,895,632 |

`decide` is the single largest method actor at 35,854,360 bytes.
The largest global subscription cost is its standing underlying
caller values. The new qualifier side stores hold 226,936 DATA
groups with 448,592 logical FLOW/TAINT memberships. The ordinary
summary stores hold 449,452 FLOW/TAINT memberships. The qualified
groups repeat enough payload to matter. Their direct memory is
smaller than the standing caller-value store. Their effect on
further calls and propagation needs an isolated run.

The point stores hold 5,063,995 logical memberships, of which
3,901,576 (77.0%) conclude at a static base. Statics also account
for 346,446 of the 449,971 ordinary summary memberships. The
largest point shape is `STAR/TAINT, DEMAND`. Static conclusions
make up 2,166,855 of its 2,212,025 memberships (98.0%).
By comparison, NE accounts for 668,506 point memberships across
all bases and marks. The snapshot locates the workload in
restricted static propagation and standing callers. It does not
attribute every static fact to a virtual search or to its first
C2 admission.

### Conductor rule isolation

The D diagnostic changes one live C2 cell in the revised build.
For a backward run-2 STAR demand and STAR offer at the same
head, it restores the prior EXACT start. It keeps deeper STAR
relay, raw C5 eligibility, the full run-1 policy and the same
model, FULL marks, aliases, statics, heap and timeout. The changed
cell loses the concrete STAR start and its FLOW companion when
the selector is concrete. The diagnostic tests the R32 start
family without testing those effects separately.

The isolation launches have the same outgoing H1 count at each
of the 6,804 owner keys as the original revised scan. The
comparison checks counts rather than a full key dump.

| Metric | Revised | R32 diagnostic D |
| --- | ---: | ---: |
| Incoming run-2 pairs / owners | 173,371 / 6,804 | 173,371 / 6,804 |
| Run-2 result | OOM | Complete |
| Run-2 engine s | 219.120, includes heap dump | 181.458 |
| Run-2 barrier s | — | 5.080 |
| H2 paired rows | — | 466,674 |
| Initial keys offered by selected calls | 2,730,060 | 1,168,206 |
| Run-2 accepted caller deltas | 1,484,751 | 827,063 |
| Run-2 caller groups created | 1,370,523 | 732,533 |
| Static C2 states | 4,525,716 | 4,912,588 |
| Static C5 states | 9,454,590 | 9,159,845 |
| `decide` local DATA publications | 133,031 | 143,218 |
| `decide` local DATA callbacks | 1,073,416 | 1,176,934 |

The failing run's work counters are partial. The completed
diagnostic offered 57.2% fewer initial keys and created 46.5%
fewer caller groups than the failing run had created at abort.
Its counters record 49,107 offers in the changed cell. Among
them, 39,412 are concrete static offers, 7,349 are static FLOW,
and 2,346 are nonstatic FLOW. Each selected the EXACT command.
The diagnostic's own offer count can change because a start can
enable offers later in the same fixed point.

This isolates a trigger of the OOM in the revised configuration.
The same-head family widened run-2 fact and caller-state
propagation. High static search volume and local replay remain
after the OOM disappears. The isolated `decide` counts include
the later work it completed. They do not show that reverting
the start family lowers that owner's local work.

The test reached run-3 after it committed H2. The diagnostic
stopped there by an external signal. Run-1 remained its latest
accepted forward report. The diagnostic changes admission and
can remove required service. A production rollback needs a
coverage proof.

The C diagnostic kept R32 and restored the previous FLOW
label filter for virtual, composed C5 searches. It used the same
173,371 incoming pairs and hit the guard in run-2 after
188.312 s, including 16.633 s to write its snapshot. It logged
8,367,887 static C5 states and 2,811,706 offered initial keys
at abort. The narrowed search lowers the observed static C5
volume. The run-2 caller expansion and memory failure persist.

The narrower D2 diagnostic replaces only the concrete static
STAR start with EXACT. It keeps that start's NORMAL FLOW
companion and the independent abstract FLOW relay. It hits the
guard in run-2 after 112.556 engine seconds, with the same
incoming count. It records 162,944 such EXACT and FLOW companion
commands and zero concrete STAR commands in the selected cell.
That concrete STAR replacement alone is insufficient. The larger
R32 admission family remains the demonstrated intervention.

The complementary D3 diagnostic removes only the FLOW
companion from that same concrete static R32 cell. It retains
the concrete STAR start and the independent abstract FLOW
relay. The guard stops it in run-2 after 213.524 s. The live C2
counters record 1,076,995 same-head STAR row offers. Of these,
1,074,625 (99.78%) come from shared static carry, 2,362 from
explicit pairs, and eight from virtual completion. Among the
886,457 concrete static offers, 886,456 use carry. These are
offer attempts before initial deduplication. This locates the
main route that invokes R32. Changing only one output of the
concrete start family leaves the memory failure.

The D4 diagnostic restores the previous EXACT start only for
the R32 same-head shared carry route. It retains explicit and
virtual R32, deeper relay, qualified delivery and the revised
raw C5. It also keeps the same H1 counts for all owners.

| Metric | Revised before OOM | Carry-only diagnostic D4 |
| --- | ---: | ---: |
| Run-2 result | OOM | Complete |
| Run-2 engine s | 219.120, includes heap dump | 183.584 |
| Run-2 barrier s | — | 5.116 |
| H2 paired rows | — | 467,877 |
| Initial keys offered by selected calls | 2,730,060 | 1,168,385 |
| Run-2 accepted caller deltas | 1,484,751 | 826,861 |
| Run-2 caller groups created | 1,370,523 | 732,869 |

D4 records 46,761 carry EXACT offers and retains 2,402 explicit
STAR commands. Its caller workload and timing are close to the
broader D diagnostic. This isolates shared carry as the R32
route that crosses the memory guard in the measured configuration.
The ordinary R32 proof example concerns a nonstatic wrapper.
A carry-specific correction needs a separate proof for static
suffixes, saved replay and later guidance.

D4 reached run-3 and stopped by the barrier monitor. It completed
run-2 and accepted run-1. The test changes which starts execute
and keeps the broad raw C5 image for isolation. It supplies a
causal workload comparison and leaves finding parity open.

The B diagnostic keeps R32, the revised C2 start rules, ordinary
publication and raw C5. It suppresses the auxiliary qualified
reply channel for possible starts in run-2. It completes that run
in 98.344 engine seconds plus 5.129 s for its barrier, then reaches
run-3 and stops by the barrier monitor. Run-1 is its latest
accepted forward report. It starts with the same 173,371 pairs
over 6,804 keys.

| Run-2 metric | Revised before OOM | Diagnostic B, complete |
| --- | ---: | ---: |
| `decide` local DATA publications | 133,031 | 19,758 |
| `decide` local DATA callbacks | 1,073,416 | 526,774 |
| Static C2 states | 4,525,716 | 1,681,752 |
| Static C5 states | 9,454,590 | 5,289,958 |
| Initial keys offered by selected calls | 2,730,060 | 2,307,936 |
| Run-2 caller groups created | 1,370,523 | 1,177,162 |
| H2 paired rows | — | 252,373 |

Most caller-group growth remains with R32 in B. The auxiliary
channel creates a large independent publication and delivery
workload. Removing its effects lowers the available H2 guidance
from D's 466,674 rows to 252,373 and the next source seeds from
1,427 to 1,226. The diagnostics change different transfer results.
They identify two contributors to the resource failure and give
no full-coverage basis for either rollback. The variants and
receipts are in `conductor-ablations/` in the campaign archive.

**ThingsBoard reached run-1.** The memory guard stopped its engine at
179.704 s, including 30.127 s to write the snapshot. It reached
70,672 actors, 6,619,454 steps and 3,546,945 candidate offers. Peak
process RSS was 13.79 GiB. There is no measured transition into run-2.
The heap used 11,617,123,480 bytes at the guard. The HPROF file is
18,425,788,922 bytes.

The normal CPU window stayed within run-1 and contains 42,790 weighted
samples. Inclusive frames include GC worker threads (41.22%), forms
(34.43%), subscription management (18.90%) and field-limit operations
(11.96%). These counts overlap. Static service frames appear in 1.18%
of samples. This does not measure the amount of downstream work that
static offers trigger. The run-1 abort counters record 1,561,984
pending static request memberships over 4,919 outstanding region
and mark requests. They also record 2,240,216 created caller
groups, 2,492,978 packed diagonal memberships released at shutdown
and 17,204,520 decodes of packed caller input. The request batch
visited 14,011,874 caller members for 271,466 geometry tests.
These were different units measured at different lifecycle points.
The live heap has 11,389,017,328 reachable bytes, within 0.1% of
the previous run-1 guard's reachable heap. The owner census found
the following retaining fields. Nested rows overlap.

| Retaining field | Retained bytes |
| --- | ---: |
| `UnitRunner.actors` | 3,224,254,528 |
| `MethodBlockRuntime.entries` | 1,590,461,904 |
| `SubscriptionManager.inputDirectory` | 1,316,497,128 |
| `RunMethodAnalyzer.edgeStore` | 1,065,404,320 |
| `CalleeSubscriptions.values` | 1,063,918,832 |
| `RunMethodAnalyzer.bodyWork` profiling counters and samples | 515,003,296 |
| `Run1PointResume.points` | 118,017,480 |
| `Run1StaticService.fields` | 26,339,896 |

The global static field directory contains 46 retained fields.
Its FLOW writer directory retained 616,904 bytes. The ordinary
method and block state dominates this snapshot. The benchmark's
workload observer also costs 515 MB across method actors, including
414 MB of sampled observations. The previous bidirectional run used
the same observer. It retained 538 MB in that field.

The point stores hold 11,603,354 memberships. Of these, 9,336,150
are concrete DEMAND memberships and 2,528,831 have an NE tail.
Static premises account for 3,914,404 point memberships (33.7%).
Static conclusions account for 187,376 (1.61%). The summary
stores hold 1,046,270 memberships with 63,543 static conclusions.
Compare the rule and propagation effects of static premises with
the cost of the static protocol's own stores. In this snapshot that
protocol owns a small part of the heap, while its premises
participate in a substantial fraction of the point facts.

**Stirling-PDF reached run-4 and completed run-3.** Run-1 took
26.600 s through its barrier, including 0.617 s of static binding.

| Run | Engine s | Barrier s | Handoff rows | Target origins |
| --- | ---: | ---: | ---: | ---: |
| run-1 | 24.516 | 1.345 | 74,200 | 6,106 |
| run-2 | 41.852 | 2.821 | 204,847 | 534 |
| run-3 | 418.955 | 1.393 | 18,683 | 828 |
| run-4, timeout | 566.277 | — | — | — |

A focused run-3 capture at engine seconds 131–162 contains 4,715
samples. Loop restriction appears in
53.68%, local relation application in 57.22%, revised C5 in
30.10%, raw witness search in 24.71% and revised C2 in 22.08%.
The samples overlap. The revised loop path requests a complete
observation for each attempted prefix, so saved replay and C5 run
even when an admission difference could reject that prefix.

Run-3 records 2,714,092 direct C2 calls and 18,882,188 C5 row
attempts in the revised counters. The largest two logged owners,
`EmlProcessingUtils#decodeMimeHeader` with untyped and StringBuilder
argument contexts, account for 1,455,858 complete observations,
524,384 prefix trials and 2,331,037 native C5 queries. Those two
owners executed 99.8% of the observations in the logged top-24
sample. The failed-prefix cost is concentrated in a single loop
body and two contexts. The current counters cannot determine how
many full observations a sound early probe could avoid.

The run-4 profile at about 60 engine seconds contains 4,571
weighted samples. Loop restriction appears in 64.19%, local
relation application in 64.56%, revised C5 in 33.54% and raw
witness search in 26.93%. The field-cut implementation appears
in 0.50%. The same loop boundary evaluation dominates the
forward run-3 and backward run-4 samples.

The 30-second near-limit window stayed within run-4 and contains
4,968 weighted samples. Loop restriction appears in 59.32%, revised
C5 in 42.33%, raw witness search in 34.58%, and GC worker frames in
39.65%. The engine ended with 22 work items still in flight after the
logged event count stayed at 84,531 for close to three minutes. The
abort counters for the two `decodeMimeHeader` contexts record
355,581 observations, 202,949 trials, 1,455,814 C5 queries and only
33 local row publications. This supports repeated expensive boundary
evaluation as the cause of the timeout. A stalled event count does
not establish an uncapped demand cycle.

## Cutoff evidence

OWASP reached the hard limit with a nonempty frontier. A passive
replay matched the measured H7–H11 counts, terminal reason and
2,633 confirmed reports. It captured 107,608 records with no observer
errors. Every explicit retained pair matched at least one outgoing
summary or Target origin. The observer compares physical owner and
ports, both selectors, mark labels and masks.

| Replayed handoffs | Shared exact pairs | Earlier only | Later only |
| --- | ---: | ---: | ---: |
| H7 and H9 | 650 | 0 | 106 |
| H8 and H10 | 1,035 | 0 | 20 |
| H9 and H11 | 756 | 0 | 20 |

The 20 H11 additions are method-level `Target → DATA` demand
pairs in two nested-loop owners. `BenchmarkTest02326#doPost`
adds 16 and `BenchmarkTest01474#doPost` adds four. Each has the
same depth-five exact path and mark as one of the 20 new H10
`DATA → ZERO` pairs. The latter come from NORMAL backward
`ZERO → DATA` summaries. In the first owner, one new point
extends the previous depth-four
`arg(0).<get-default>.elements.bytes.[]` guide by `.chars`.
Run-8 already has a global limit that fits five fields. The
new depth-four H9 selector makes the fifth field available
under the paired cap. This is progress in those obligations.
The separate FLOW pairs still recur.

The 16 new `BenchmarkTest02326` points match 1,824 outgoing
origin memberships. One origin is unary for each point, 912
memberships are from binary ND origins, and 896 are from
ternary ND origins. Projecting one exact point from many
origins does not show that those complete origins had identical
runtime effects.

Twelve `doSomething` helper owners account for all 72 repeated
forward FLOW pairs. Each has the same six endpoint patterns.
`BenchmarkTest01000$Test#doSomething` also repeats eight backward
FLOW pairs at H8 and H10. One forward summary has the shape
`arg(1).bytes.[].* → ret.bytes.NE, DEMAND`. One backward
summary has `ret.bytes.* → arg(1).bytes.[].NE, DEMAND`.
The physical parent for both is the method boundary. The
nonempty tail improves the local cut geometry. The corresponding
forward and backward demand keys still recur.

The focused replay captured 139 C2/C5 queries and 698 summary
applications without drops. It reproduced every forward handoff
key and every exact finding from the passive replay. Its two
backward handoffs each contained 26 extra rows in other owners.
The selected helper's exact keys agree in both captures.

For the following trace, `p` is `arg(1)`, `b` is the exact
`String#<string-bytes>` accessor, and all summaries use FLOW.
The run-10 offer uses one concrete full mark T.

| Step | Actual or raw relation | Selected demand and result |
| --- | --- | --- |
| run-10 C2, query 11 | `ret.MAY/T, DEMAND` | `ret.MAY → p.b.*` authorizes possible `ret.b.*/FLOW, NORMAL`. |
| run-10 C5, query 21 | `ret.b.* → p.b.[].b.*, NORMAL` | The same shallow pair has cap 2 and publishes `ret.b.* → p.b.[].NE, DEMAND`. `ret.b.NE → p.b.[].*` has cap 3 and retains the full NORMAL relation. |
| run-11 C2, query 73 | `p.b.*/FLOW, NORMAL` | The `p.b.MAY → ret.*` and deeper NE pairs authorize possible `p.b.[].*/FLOW, NORMAL`. |
| run-11 C5, query 80 | `p.b.[].* → ret.b.[].*, NORMAL` | The shallow pair has cap 1 and republishes `p.b.[].* → ret.b.NE, DEMAND`. The deeper pair has cap 2 and keeps the NORMAL relation. |

The corresponding raw EXACT inputs (queries 29 and 84) normalize
to the same public STAR shape and produce the same cuts.
A current call application resumes the NE result. A separate
saved reverse MUST view resumes MAY. The cut is already present
in the current summary before either delivery.

The two root MAY rows enter C5 on DEMAND in run-11 queries
101–102. Run-10 query 71 already offers the raw DEMAND relation
`ret.* → p.MAY`. Its output selection retains
`ret.* → p.b.MAY, DEMAND`. The paired cut trace explains the
four NE rows. The root MAY rows have a second source of renewal
that also needs coverage.

### Why the termination rules keep the helper active

- **R05 and R09–R12 find the refined starts.** The run-11
  offer `p.b.*` starts the prepared child `p.b.[].*`.
  For the shallow pair, the field comes from a saved NORMAL
  guard. The deeper NE pair has a different exit selector
  and cannot supply a child to the shallow pair by the
  same-exit rule. The prepared child still keeps the shallow
  exit selector and its cap.
  [Prepared-child rules](../../spec/demand-refinement-and-termination.md#31-prepare-one-level-of-children)
- **R18 and R20–R23 retain the cut beside the precise result.**
  R18 runs C5 even when a saved NORMAL relation covers the raw
  transfer. The shallow backward pair has cap 2 and the shallow
  forward pair has cap 1. Increasing the global limit beyond
  those caps leaves the cuts unchanged. The deeper pairs admit
  the NORMAL relations separately. A constructive Lean check
  derives the same two projected NE keys for all global caps
  that fit the raw inputs, assuming the observed raw offers and
  shallow rows remain available.
  [Paired C5 contract](../../spec/demand-refinement-and-termination.md#33-raw-entry-witness-and-paired-output)
- **R25 cannot merge the shallow and deep pairs.** The
  revised handoff deduplicates exact pairs. The observed pairs
  also have different C2/C5 service. For example, shallow
  C5 accepts the raw point in query 29. The deeper NE selector
  rejects that same-head point before FLOW normalization.
  Query 84 shows the same distinction in the forward direction.
  NORMAL subsumption applies to executable NORMAL relations.
  It leaves the separate DEMAND refinement service available.
  [Service keys](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/driver/HandoffServiceKeys.kt)
- **The driver sees nonempty DATA demand.** R37–R40 address
  Target service. The helper's repeated pairs are FLOW DATA
  and its method has no loop. The current `NO_DEMAND_EDGE`
  check therefore still sees these pairs.
  [Stop test](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/driver/IterationDriver.kt#L224)

The capture shows the active rules producing their specified
results. The missing behavior is retirement of a FLOW demand
whose complete transfer can already use saved NORMAL replay.
The [earlier retirement proposal](../../spec/normal-backed-flow-demand-retirement.md)
defines that proof for this helper. It was a design experiment.
The active spec explicitly keeps ordinary C5 in the historical
precoverage case. Unconditionally skipping a cut when one
NORMAL result covers it can remove another service of the
same demand pair.

The saved replay check reused the 12 paired copy origins from
the earlier compiled-form audit. It checked each origin
assigned to each of the 34 retained helper row instances in
H7–H11 against the 21 revised, saved NORMAL STAR relations
at each barrier. All 124 clipped origin instances had an
aligned witness in both directions. The check uses the whole
MAY region as a conservative cover of NE. Each witness uses
the provider's real direct or opposite replay role. This
confirms the retained-basis part of the older proof against
the revised capture. It uses the prior form closure and leaves
current form completeness and retirement through caller C2
and C5 to check before activation.

The focused native test command passed all 22 tests in
`RevisedDemandPolicyTest`, `HandoffCompactorTest` and
`OwaspDemandCycleTest`. The C5 test expects both a NORMAL
result and a shallow NE result. The revised OWASP-shaped
test requires its observation and completed runs. It has no
natural-stop assertion for the actual helper. Evidence for
this review is in `cutoff/OWASP-helper-H10-H11/coverage-review/`
in the campaign archive.
[Prior helper trace](bidirectional-owasp-helper-cycle-20261110.md)

The replay accounted for all 776 H11 pairs. Twenty are new
exact points. Seventy-two repeated FLOW pairs have the helper
shape family above. The other 684 repeated pairs retain their
exact keys and matching producers in the archive. Their
complete dynamic guards remain open.

The forward loop-owner diagnostics show 245,899, 387,770 and
433,878 local Target callbacks in run-7, run-9 and run-11. At run-11,
`BenchmarkTest02326#doPost` accounts for 345,970 of the logged
callbacks and 3,292 published local Target rows. Its logged DATA
callbacks and boundary cuts are both zero. H11 compaction processed
10,587 origins and 25,694 projected obligations to produce 776
retained rows. High callback counts and a repeated final obligation
require separate explanations.

## Test gates

The worktree core and JVM bidirectional sweep passed 3,059 tests
(2,708 core and 351 JVM). The core sweep includes 295 tests from
untracked research fixtures and three tests in a pre-existing
modified loop-boundary fixture. The revised OWASP-shaped and
Conductor uniform fixtures passed. Lean checked the
qualified-admission claims.

The source Gradle rule suite passed `checkRuleTestResults`. It
recorded 786 successes, 22 disabled cases, and zero skips, false
positives or false negatives. The first analyzer launch failed
before execution because a diagnostic init script selected a
task in an included Gradle build. The retry selected the core
root build and reused the newly built portable model.

All 585 collected, enabled Java cases entered the FULL revised
bidirectional engine and completed. The most advanced case reached
run-11. The 201 enabled Go cases passed with the existing Go
engine. Two Java interface declarations were outside the runner's
collection, as in the previous validation. This leaves 607 of 609
Java declarations collected, including disabled cases.

| Latest completed Java run | Cases |
| --- | ---: |
| run-1 | 468 |
| run-3 | 109 |
| run-5 | 4 |
| run-7 | 2 |
| run-9 | 1 |
| run-11 | 1 |

`PathTraversalServletSamples#streamFile` was the sole Java case
to reach the run-11 cutoff. It kept one confirmed result and no
provisional result. The other 584 stopped with no outgoing demand.
The selected test entry is
`PathTraversalServletSamples$UnsafeFileUploadServlet#doPost`.
[Rule-test procedure](../rule-testing.md)

The isolated Gradle replay passed the same rule gate. It
reproduced all handoff counts and captured 7,950 complete C2/C5
queries and 1,818 Target calls with no errors or drops.
H5, H7, H9 and H11 contain the same 30 Target-entry pairs.
H6, H8 and H10 contain the same 44 control pairs. The forward
turns keep one confirmed report ID and three predicate seeds
at its physical observer. The late backward turns add no
source seed. The 151 saved NORMAL DATA rows and 25 saved
NORMAL Target rows are stable from run-5.

```text
run-10 C5, limit 9, selected pair cap 1:
  raw    ZERO → file.uri.value.$/T, NORMAL
  keep   ZERO → file.uri.value.$/T, NORMAL
  guide  ZERO → file.uri.NE/T, DEMAND

run-11 C2, limit 10:
  offer  file.uri.value.$/T, NORMAL
  starts file.uri.value.$/T, NORMAL
         file.uri.*/T, DEMAND
         companion FLOW

run-11 Target:
  keep one saved confirmed ID
  attempt the same outer ZERO → DemandTarget row 13 times
  retain that Target pair once
```

This is the known LOOP Target renewal. The raw cut feeds a
provisional route beside the confirmed route. Deferred R37/R38
address that terminal service. The observed prefix does not
establish the complete retirement certificate or an uncapped
proof for the revised rule set. The existing small test remains
the regression control. The complete query IDs and guard checks
are in `cutoff/rule-file-upload/cutoff-analysis.md` in the campaign
archive. [Deferred terminal specification](../../spec/demand-target-retirement.md)

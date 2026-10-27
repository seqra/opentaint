# Correlated concrete initials: fixed-project performance report

Measured runtime date: 26 October 2026. Report completed: 27 October 2026.
The fresh baseline diagnostic cohort spans both UTC dates.

All four projects complete run-1. Engine time improves on Thingsboard,
Conductor and Stirling-PDF, but regresses 29.69% on OWASP. The three real
projects still stop during run-2. The largest demonstrated redundant state
is Thingsboard's 8.19 million exact duplicate pending publications. Conductor
and PDF instead have predominantly static scalar method state, concentrated
on generated Spring registry fields. No current backward FLOW rows exist
to support ordinary FLOW compaction in these snapshots. These findings
motivate different changes from another static-only run-1 refactor.

The final Conductor/PDF/OWASP exports match the fresh pre-iteration branch
exports. Nine strict native-main PDF locations remain missing; source and
catalog/export evidence explain the cases. The timed Thingsboard export is
unavailable; a separate run-1 diagnostic retains all thirteen native-main
locations. Performance and correctness gates are reported separately below.

The measured runtime is `fcfe2e90558665d813bd74207832d4ae3fc83aec`, core tree
`57ca8d4940e8fb52e7eed6151928d4025c7d7ad9`. The pre-iteration runtime is
`583a58063ab67ad18b8664d45badee065e68fd85`. Native main is
`c86a5fbd60f7bcef212c5ecde0bddecc8cb56ada`. All project results in the final
comparison must come from the final runtime, not the superseded `85dc2bbf8`
measurement. The earlier candidate's raw captures have been removed. Its
sealed intermediate notes explain the admission defect; they do not prove
final performance.

The change preserves a concrete STAR suffix relation at initial emission and
through matching copies. It permits FLOW replacement at every summary owner
in every run. It retains protected marked dependencies, supports legal
NORMAL FLOW records with nonempty exclusions, and removes the alias-effect
exception under the selected input-alias-closure contract. The final correction
makes packed TAINT admission obey the scalar ANY/STAR law across typed headers.
It does not add a new FLOW coverage cell or remove an older STAR merely
because ANY arrives later. No new optimization, field policy, request
protocol, IR storage change or cache-manager rewrite is included.

## Configuration and evidence

Each project uses the direct Gradle `runProjectAnalyzer` task, Java 17,
run-1 FULL mode, statics enabled and default aliases. Configured budgets are:

| Project | Analyzer heap | Timeout | Outer harness cutoff |
| --- | ---: | ---: | ---: |
| Thingsboard | 12 GiB | 1,080 s | 1,200 s |
| Conductor | 8 GiB | 1,080 s | 1,200 s |
| Stirling-PDF | 8 GiB | 1,080 s | 1,200 s |
| OWASP | 8 GiB | 1,000 s | 1,200 s |

The native-main correctness baseline uses main's own pinned rule catalog.
The pre-iteration/current performance comparison uses the same branch
catalog. These are distinct comparisons. The old shared-catalog main control
is supplemental and cannot replace the native baseline.

The host is shared. The harness records available memory, swap, load,
process CPU and RSS throughout each run. Other analyzer JVMs were observed
outside this campaign. Own-process liveness guards do not prove host
isolation. Timing differences need this limit; workload counters and
source-bound relation counts do not become host CPU measurements.

Timed runs and joined run-1 diagnostic runs are separate executions. The
latter capture edge shapes, exact whole-protection classes, physical work
credits and repeated conclusion templates. Selected method points/forms and
witnesses are streamed after all runners join and before their state is
released. Raw/selected summaries and counters are captured at the driver
barrier after that release. Seven controls check this lifecycle, unchanged
store state, scalar/packet counts, coverage reasons and exact template keys.
No observer hook or per-edge processing history is added.

## Implementation validation

The full final-source suites executed afresh. Their source guard remained
unchanged throughout. Every pre-existing test status and failed assertion
matches the preceding candidate. The ten new admission controls pass.

| Suite | Tests | Failures | Skips |
| --- | ---: | ---: | ---: |
| Common dataflow | 1,929 | 0 | 0 |
| JVM dataflow | 440 | 0 | 0 |
| Go dataflow | 1,323 | 0 | 0 |
| Configuration equality | 5 | 0 | 0 |
| Application | 1,039 | 11 | 13 |

The application gate is not green. The eleven failures and thirteen skips
also occur in the baseline; the exact assertion comparison passes. This
report does not turn those failures into successful tests. The admission
correction also passes 31 focused controls; eight of its ten new controls
fail on the intermediate implementation. The constructive Lean audit
checks 356 declarations and 26 executable controls, with no unexpected
axioms. These are local correspondence results, not a whole-engine or
real-project no-FN proof.

## Native-main Conductor OOM: completed baseline diagnosis

This is the legacy engine. A bidirectional run iteration is **not applicable**.
Its analyzer used the configured 8 GiB heap. Offline MAT used 12 GiB; this
is a parser budget and does not change the analyzer experiment.

The dump has 7,665,119,816 reachable bytes in 199,622,454 objects. The complete
root partition agrees with the full class histogram. Runner and unit-storage
root families retain 2,828,594,336 disjoint bytes, 36.90% of the live heap.
RAMEntityRelationshipStorage retains 2,251,534,032 bytes; this is IR accounting,
not an IR optimization proposal. Top-level shared byte-array roots retain
1,041,800,248 bytes and are a separate root partition; do not assign them to
an owner without a path proof.

The source-bound field unions show:

| Legacy field | Retained bytes, rounded MB | Interpretation |
| --- | ---: | --- |
| MethodAnalyzerEdges.taintedToFactEdges | 835.74 | Retained ordinary nonzero relations |
| NormalMethodAnalyzer.delayedSequentialEdges | 390.91 | Deferred sequential relations |
| NormalMethodAnalyzer.pendingSideEffectSummaries | 368.72 | Pending side effects |
| NormalMethodAnalyzer.unprocessedEdges | 2.94 | Immediate work queue |

These field unions overlap. Do not add them. The heap contains 5,632,963
FactSideEffectSummary and 6,682,493 TaintMarkFieldUnfoldRequest instances.
Their instance counts do not prove duplicate counts, static shares or
logical relation counts. Source appends pending side effects before
queue-empty publication. Its final persistent store merges kinds and
exclusions after that barrier. The lazy side-effect storage delegates are
not in the per-field census, so the 1.052 GB summary-owner union has a
stated attribution gap. It cannot be explained by subtraction from the
listed ordinary-summary and request fields.

The source evidence identifies retained relation/side-effect state, rather
than the immediate work queue, as a substantial native-baseline cost.
This is not a claim about the final bidirectional run-2 heap. Those dumps
have separate source-bound decoders and owner counts below.

## Final timed project results

Thingsboard completed run-1 in **592.190834914 s**, compared with
632.911642548 s in the fresh pre-iteration run: **6.43% less engine time**.
The 60-second engine target is not met. Its latest reached iteration is
**run-2**; its latest completed and accepted forward iteration is **run-1**.

Run-2 selected 232.540319863 s of remaining budget. The memory guard started
its snapshot at 21:05:20.494 UTC, with 11,632,802,736 used bytes above its
11,596,411,699-byte threshold. It completed the 18,253,330,215-byte file at
21:06:02.255 UTC. The dump pause was 41.761 s. The engine ended TIMEOUT at
259.034898968 s, and the outer command ended HARD_TIMEOUT without a SARIF
export. The status is not relabeled OOM. The completed guard snapshot still
provides valid run-2 memory evidence; the offline decoder must check the
actual marker/path/size binding rather than infer eligibility from the final
status alone. The primary timed finding counts are unavailable, not zero.

The timed run-1 marker census has 1,800,397 retained concrete output
memberships, 1,737,136 protected (96.49%), 31,445 diagonal geometry rows,
181,253 diagonal mark rows, 18,239 scalar headers and 224,337 FLOW annotations.
Raw and selected counts agree; they are not added. Physical rows are not
logical output memberships. The separate joined diagnostic has its own
physical-row counts; do not combine those counts with the timed census.

| Project | Previous run-1, s | Final run-1, s | Change | Final status | Latest reached / completed / accepted |
| --- | ---: | ---: | ---: | --- | --- |
| thingsboard | 632.912 | 592.191 | -6.43% | HARD_TIMEOUT | run-2 / run-1 / run-1 |
| conductor | 23.583 | 20.501 | -13.07% | OOM | run-2 / run-1 / run-1 |
| Stirling-PDF | 42.851 | 33.255 | -22.39% | OOM | run-2 / run-1 / run-1 |
| OWASP | 174.991 | 226.948 | +29.69% | TIMEOUT | run-9 / run-8 / run-7 |

The engine-only 60-second target is met by Conductor and Stirling-PDF. It is not met by Thingsboard or OWASP. The OWASP run-1 regression is +29.69%; its previous run reached run-10 and accepted run-9, while the final run reaches run-9 and accepts run-7. OOM/timeout prefixes are not completion measurements. Shorter failed run-2 time alone is not an improvement.

The fresh timed completion counters show these raw summary changes. The
selected counts are equal except for one extra old protected annotation on
Thingsboard. Each column belongs to its own timed invocation.

| Project | Before concrete memberships | Final concrete memberships | Before protected annotations | Final protected annotations |
| --- | ---: | ---: | ---: | ---: |
| Thingsboard | 2,081,257 | 1,800,397 | 943,571 | 1,737,136 |
| Conductor | 20,186 | 16,767 | 20 | 22 |
| Stirling-PDF | 24,773 | 24,479 | 2,249 | 2,273 |
| OWASP | 111,133 | 111,025 | 413 | 460 |

Thingsboard retains 13.49% fewer concrete memberships. Its protected share
increases from 45.34% to 96.49%. This is not evidence that protection alone
causes all retained work. The new checker tests STAR coverage as well as
ANY coverage and removes the alias-effect exception. The earlier published
16 GiB census uses the older predicates and a different heap budget. It
provides the investigation method; its rejection categories are not silently
treated as a fresh fixed-budget before/after classification.

| Project | Iteration | Direction | Limit | Status | Engine, s | Barrier, s |
| --- | --- | --- | ---: | --- | ---: | ---: |
| thingsboard | run-1 | FORWARD | 1 | COMPLETE | 592.191 | 14.863 |
| thingsboard | run-2 | BACKWARD | 1 | TIMEOUT | 259.035 | — |
| conductor | run-1 | FORWARD | 1 | COMPLETE | 20.501 | 0.842 |
| conductor | run-2 | BACKWARD | 1 | OOM | 110.591 | — |
| Stirling-PDF | run-1 | FORWARD | 1 | COMPLETE | 33.255 | 0.477 |
| Stirling-PDF | run-2 | BACKWARD | 1 | OOM | 191.752 | — |
| OWASP | run-1 | FORWARD | 1 | COMPLETE | 226.948 | 7.430 |
| OWASP | run-2 | BACKWARD | 1 | COMPLETE | 97.961 | 0.337 |
| OWASP | run-3 | FORWARD | 2 | COMPLETE | 50.604 | 1.689 |
| OWASP | run-4 | BACKWARD | 3 | COMPLETE | 76.867 | 0.375 |
| OWASP | run-5 | FORWARD | 4 | COMPLETE | 55.538 | 2.444 |
| OWASP | run-6 | BACKWARD | 5 | COMPLETE | 89.158 | 0.335 |
| OWASP | run-7 | FORWARD | 6 | COMPLETE | 47.104 | 1.799 |
| OWASP | run-8 | BACKWARD | 7 | COMPLETE | 212.440 | 3.203 |
| OWASP | run-9 | FORWARD | 8 | TIMEOUT | 54.557 | — |

An absent SARIF export is unavailable, not zero findings. Native-main
timeouts/OOM supply only a prefix baseline. Raw occurrence counts differ
from unique locations and full result-body identities.

Conductor completed run-1 in **20.500967091 s**, then ended OOM in
run-2. Its latest reached/completed/accepted sequence is **run-2 / run-1 /
run-1**. The final export retains all seven native-main unique and strict
locations. Its 41 branch identities and 42 occurrences exactly match the
fresh pre-iteration branch export. This preserves the exported baseline
prefix; it does not establish completion of either failed analysis.

The PDF investigation also has a same-core catalog control. Native main
with its native catalog completes with 24 findings, including nine XSS
findings. The preserved supplemental main run, with the same core/model/
heap/timeout but the branch catalog, completes with eight findings and no
XSS. All nine missing native XSS identities are absent in that control.
The source catalog changes starred UNTRUSTED access to plain root access
and removes the Object.toString propagator. The parser lowers plain access
to root CM and starred access to root OR AnyField CM, with corresponding
assignment positions. Thus catalog policy is a demonstrated cause at the
input-set level, without any bidirectional core change.

The final diagnostic explains the six Map-response cases: UNTRUSTED reaches
`Map#MapValue` at the response factory, or reaches the return under
`HttpEntity#Body`. All nine applicable response-transition variants check
the root or an exact array element; none checks MapValue or an arbitrary
descendant. Thus they do not generate the distinct exit-sink marker. The
exit rule checks that generated marker on any result field, not the source
UNTRUSTED atom. The missing source-to-marker step is observable before the
exit. `getSettingValue` has the same problem for `DTO#key`; a later finding
on another return in that method is not an equivalent path. Two other
cases, ConvertEmlToPDF return 103 and PipelineController return 50, do have
the generated marker at the native return and remain consistent with the
exporter's last-return fallback. All nine strict misses remain explicit.

| Project | Native-main unique locations | Final primary unique locations | Final occurrences | Missing native primary / strict locations |
| --- | ---: | ---: | ---: | --- |
| Thingsboard, timed run | 13 | Unavailable | Unavailable | Unavailable |
| Thingsboard, separate run-1 diagnostic | 13 | 5,089 | 92,016 | 0 / 0 |
| Conductor | 7 | 41 | 42 | 0 / 0 |
| Stirling-PDF | 24 | 148 | 973 | 9 / 9 |
| OWASP | 2,633 | 4,112 | 9,179 | 0 / 0 |

Thingsboard's separate diagnostic has 5,112 strict coordinates. Primary
fingerprints can merge coordinates; the two uniqueness definitions are not
interchangeable. It reaches, completes and accepts **run-1**. The timed run
still ends at **run-2 / run-1 / run-1** with no exported file. Neither a native
failed prefix nor a run-1-only diagnostic proves whole-project completion.

Conductor, PDF and OWASP have exactly the same exported primary/strict
identities and occurrence counts as their fresh pre-iteration branch runs.
Thus the selected optimization introduces no observed exported finding
loss in those comparisons. The nine PDF native-main misses remain a known
baseline/catalog difference. The much larger branch finding populations
are not described as only a few false positives without manual validation.

The branch OWASP workflow checks 4,112 raw traces. Both fresh pre-iteration
and final exports have 9,179, so that raw-count CI check fails. These results
have 4,112 unique primary/strict identities and 4,112 distinct complete JSON
result bodies, with 5,067 duplicate occurrences. Native main has 2,633 and
passes its own pinned workflow's 2,633-trace check. Deduplicating findings
for review does not make the branch's raw-count gate pass.

The final joined OWASP target gives a concrete cause for a nine-fold
duplicate. At `BenchmarkTest02299.doPost`, statement 87, nine different
stored rule configurations share the identical method and statement object.
Five have no remaining receiver type condition but retain different
serialized sink IDs; four retain different LDAP receiver type conditions.
`TaintMethodSink` equality includes condition and serialized ID. Simple
export emits their common rule ID and location, so the nine internal keys
become nine identical SARIF result bodies. Twenty witness rows map to
these nine keys. This is a pre-existing rule-occurrence/export identity
mismatch, not nine distinct sink statements or a finding identity introduced
by the correlated-STAR change.

## Final CPU and allocation profiles

Ten official JFR event-count controls pass: run-1 and continuous captures
for each final project, plus the two fresh pre-iteration OWASP captures.
The source/window gates are closed. Allocation values below are sampled
allocation traffic estimates in GiB, not retained heap. GC pauses include
only events fully inside the window.

| Project, run-1 | CPU samples | Allocation weight, GiB | GC pauses, s | Largest nearest CPU owner |
| --- | ---: | ---: | ---: | --- |
| Thingsboard | 58,221 | 1,392.72 | 37.079 | IR graph/lookup, 22.04% |
| Conductor | 4,583 | 41.70 | 1.123 | IR graph/lookup, 30.00% |
| Stirling-PDF | 6,028 | 66.20 | 1.315 | IR graph/lookup, 38.21% |
| OWASP | 11,227 | 137.97 | 6.428 | Call-plan construction, 28.40% |

Nearest-owner categories partition samples. Inclusive protection and
subscription scopes overlap and must not be added. IR is accounted for
here but stays outside the selected optimization scope.

Thingsboard's run-1 allocation estimate falls from 1,705.95 to 1,392.72 GiB.
Nearest-owner AP input matching falls from 385.63 to 173.05 GB; summary
normalization/admission rises from 170.02 to 246.17 GB; protection-mask
operations rise from 58.28 to 116.84 GB. Inclusive protection is present on
18.64% of CPU samples and 43.42% of allocation weight. That inclusive scope
is larger than the disjoint protection owner because it also encloses
matching and other work.

The selected cross-header admission adapter has only 0.246% of run-1 CPU
and 0.501% of allocation weight. `TaintGroup.add` has 0.797% CPU/1.474%
allocation; diagonal normalization has 1.163%/1.576%; FLOW removal has
1.039%/1.409%. A blanket adapter rewrite does not target the measured main
cost. The corrected targeted replay passes positive and near-miss controls;
an earlier zero result from an invalid frame matcher is retained as failed
evidence and is not used.

Thingsboard's failed run-2 prefix, excluding its 41.761-second dump interval,
lasts 217.274 seconds. It has 23,220 CPU samples, 776.10 GiB allocation weight
and 79.541 seconds of fully contained GC pauses. Summary normalization/
admission owns 21.64% CPU and 30.14% allocation (251.16 GB). Inclusive
`TaintGroup.add` has 16.697% CPU/20.404% allocation. The cross-header adapter
has no sampled stack in this window. This is substantial scalar admission
work during a failed backward prefix, not evidence of run-2 completion.

### OWASP regression: measured bounds

Run-1 engine wall time rises by 51.96 seconds. New initials remain 36,592 and
fresh request memberships remain 82,957. Accepted call-input deltas rise
155,929 to 155,996 (0.043%); concrete summaries fall 111,133 to 111,025.
Cleanup kernel inputs fall 2,222,211 to 2,221,778. These counters do not show
a large new request/fact workload.

Sampled allocation rises only 137.02 to 137.97 GiB. Call-plan construction
allocation falls 53.247 to 52.833 GB, while its CPU samples rise 1,960 to
3,189. These frames are actual `JIRCallPlanBuilder` construction reached from
the forms-cache supplier, not ordinary dispatch through an existing plan.
The call-plan category accounts for 39.5% of the additional CPU samples.
Sample count growth is not an operation-count measurement.

The whole-JVM sampled CPU envelope rises from 384.85--397.02 CPU-seconds to
422.86--431.20 CPU-seconds. It includes JIT and GC. Average process CPU per
wall second falls from about 2.20--2.27 to 1.86--1.90. Recorded compiler
time does not rise, recorded soft-reference processing counts stay zero,
and the manager logs no run-1 cache cleanup. GC CPU rises by about 7.64
CPU-seconds; pauses rise by 2.70 wall seconds. Neither GC nor these cache/JIT
observations explains the full wall-time increase. The exact causal split
between additional CPU cost, effective parallelism and uncounted inner
operations remains unresolved. The regression is retained as a failed
performance result, not dismissed as host noise.

## Final run-2 retained memory

All three actual offline heap censuses are complete. These are the captured
live heaps, not the larger file sizes. Parser heaps are separate from
analyzer budgets. All three reached **run-2** and completed/accepted
**run-1**. The native legacy heap above is a distinct baseline.

| Captured live state | Thingsboard | Conductor | Stirling-PDF |
| --- | ---: | ---: | ---: |
| Reachable bytes | 11,403,249,848 | 7,613,302,200 | 7,610,134,648 |
| Reachable objects | 339,784,117 | 220,404,288 | 229,542,775 |
| Backward actors | 56,652 | 17,465 | 7,258 |
| Explicit incoming run-1 demand pairs | 2,077,650 | 69,677 | 36,468 |
| Current concrete query memberships | 1,501,686 | 744,646 | 758,063 |
| Static query share | 28.77% | 88.17% | 95.72% |
| Method-point TAINT memberships | 8,627,744 | 4,081,927 | 10,164,396 |
| Method-point static-output share | 14.18% | 83.59% | 96.54% |
| Raw summary TAINT memberships | 1,740,593 | 735,247 | 785,763 |
| Selected summary TAINT memberships | 1,089,469 | 421,395 | 414,499 |
| Published-index TAINT memberships | 1,658,011 | 732,444 | 781,734 |

Every current non-control method, raw, selected and publication scope has
TAINT only, with no FLOW rows. Thus the new all-run FLOW replacement code
has no current FLOW witness in these backward stores. Thingsboard retains
77,944 forward NORMAL FLOW memberships in a separate persistent-record
owner; applying those records to an actual marked input does not create a
current backward FLOW original. Extending the storage mechanism to every
run alone does not change that query policy.

### Repeated old-summary replay creates large pending lists

| Pending publication state | Thingsboard | Conductor | Stirling-PDF |
| --- | ---: | ---: | ---: |
| Entries | 11,428,775 | 748,046 | 1,399,814 |
| Distinct per-actor premise/conclusion object pairs | 3,242,057 | 467,257 | 811,719 |
| Exact duplicate entries, lower bound | 8,186,718 | 280,789 | 588,095 |
| Exact duplicate share | 71.63% | 37.54% | 42.01% |
| Retained-list union, bytes; nonadditive | 807,352,840 | 105,887,208 | 179,798,096 |

The source explains an avoidable pattern. For each addLink admission batch
which contains fresh initials,
`RunMethodAnalyzer.addLink` walks every raw summary and queues every row
permitted by the cumulative query set. An unrelated new query therefore
requeues older permitted answers. `queuePublications` allocates a wrapper
before asking the selected store to merge selected pieces, and ignores that
store's novelty result. Pending lists flush only when the method worklist
is empty. The publication index eventually removes duplicates, after their
allocation, retention and index-admission work. Deduplication occurs before
subscriber notification; duplicate caller applications are not established.

Thingsboard's `BasePageDataIterable.next` has 2,009,360 pending offers for
836,430 identity pairs; `hasNext` has 707,139 for 184,069. A further actor
has 167,699 offers for 664 pairs. This is a concrete repeated-state
pattern. The census does not prove that every duplicate came from this
one path or quantify its complete CPU cost.

There are 11,594,073 physical Publication objects on Thingsboard, with
278,257,752 shallow bytes. Entry count is not an exact object-identity
partition, and the pending-list union shares facts with other stores.
Therefore 71.63% duplicate entries does not imply that 71.63% of the heap,
or all 807 MB, can be removed. Replaying only newly authorized rows can
remove many offers without changing current query admission. It is separate
from the major proposal to restore demand-guided FLOW body computation.

### Scalar body state and different static workloads

Run-2 method points use scalar storage. Thingsboard has 1,519,783 per-premise
arrays and 17,808,437 slots, with 4,105,255 occupied cells; their array
shallow size is 99,662,544 bytes. The method-execution retained union is
2,136,730,680 bytes. The full arrays are not the whole owner cost. Conductor
has 746,029 scalar arrays and 3,404,236 occupied cells. Both have zero
packed statement owners: that method-point mechanism is enabled only for
run-1 FULL. Summary/publication diagonal storage is active in all runs.

Thingsboard's two largest current output families are nonstatic to nonstatic
(3,712,304 memberships) and ZERO to nonstatic (3,690,602, 42.78% of
method-point TAINT). Static outputs are
only 14.18%, even though backward input demand is static-heavy. Current
method-point tails are 5,475,749 EXACT and 3,151,995 ANY; layers are
5,290,190 NORMAL and 3,337,554 DEMAND. There are only 227 flagged method-point
memberships and 74 flagged raw/selected memberships. The high run-1 flag
share is not the explanation for this run-2 heap.

Conductor has 3,247,604 static-to-static method memberships. Generated Spring
registry fields dominate its static results: ExecutionDAO has 219,321 DEMAND
and 171,544 NORMAL memberships; ExternalPayloadStorage has 202,774/162,076;
IndexDAO has 194,623/159,014. There are only 106 DEMAND static positions and
104 NORMAL positions. Its queries include 323,335 named-field ANY and
323,796 named-field EXACT entries, reflecting the same-field completion
policy. These are repeated field/mark/original/point combinations, not
106 facts. Static-to-static does not itself prove identity geometry.

Stirling-PDF is more static-heavy: 9,109,407 static-to-static memberships
and 9,812,706 static outputs, 96.54% of its method-point marked total. Its
758,514 scalar arrays have 24,180,662 slots and 8,973,101 occupied cells.
The method-execution retained union alone is 4,048,017,736 bytes. Only 108
static positions occur. Generated ApplicationProperties has 678,127 DEMAND
and 615,794 NORMAL memberships; ApplicationContext has 635,720/589,642;
ExternalAppDepConfig has 632,987/590,934. The largest two bins are
static-to-static EXACT/NORMAL (4,408,633) and ANY/DEMAND (4,258,568).
The paired ANY/EXACT query policy and repeated scalar traversal of registry
facts are a specific target; these counts alone do not prove which rows
can be skipped.

### Physical roots and logical owners

Thingsboard's additive physical dominator-root partition is:

| Root family | Retained bytes |
| --- | ---: |
| UnitRunner | 3,641,977,720 |
| IR RAM relationship storage | 1,620,719,920 |
| JIRMethodEntries | 1,006,487,248 |
| Rule resolver epoch | 805,545,016 |
| RunConfig | 765,893,712 |
| Shared byte-array roots | 691,197,608 |
| SubscriptionManager | 553,206,920 |
| RunManager | 523,403,960 |
| Other physical root families | 1,794,817,744 |
| Total | 11,403,249,848 |

These buckets sum exactly. They are not exclusive logical subsystem names:
UnitRunner owns multiple actor stores, and RunConfig includes demand. The
nonadditive retained unions answer a different question: method execution
2.137 GB; publication/subscriptions 1.070 GB; forms 1.006 GB; incoming demand
plus queries 0.836 GB; pending lists 0.807 GB; raw/selected summaries 0.501
GB; caller inputs 0.329 GB. Do not sum those unions or add them to the root
partition. IR is accounted for but remains out of optimization scope.

The rule epoch strongly caches storage/method-query/bound-rule lists. It
can also be rooted by an in-flight captured local. The provider/view union
of only 24.3 MB therefore does not describe all rule-cache memory. The
physical epoch root is 805.5 MB. There are 4,238,893 TaintMethodExitSink
objects, 203,466,864 shallow bytes. The census does not assign an exact
epoch fraction to that class. Conductor has only 105,533 such objects;
the two projects do not have the same rule-binding footprint.

Conductor's main physical roots include IR 2.255 GB, UnitRunner 2.123 GB,
shared byte-array roots 1.042 GB, SubscriptionManager 411.7 MB and RunManager
398.8 MB. Its complete source-bound partition sums to 7,613,302,200 bytes.
Soft-reference top-root retention is zero on both projects. This does not
mean every soft reference is empty or every cached form has no strong owner.

PDF's UnitRunner roots retain 4,501,191,288 bytes, versus IR 977,715,776,
SubscriptionManager 347,261,584, shared byte-array roots 345,012,920 and
RunManager 303,196,240. Its complete partition sums to 7,610,134,648 bytes.
Its forms union is 222,648,736 bytes; soft-reference top-root retention is
also zero. Most current retained memory is analyzer state. This snapshot
alone cannot predict the heap needed for completion.

## Fresh before/after run-1 classification

A second fixed-budget baseline cohort now supplies the missing old-policy
classification. Both versions reach, complete and accept **run-1**. The
baseline uses its own ANY-only normalizer and alias-effect guard; the final
version uses STAR/ANY coverage and no alias exception. These are separate
diagnostics, not timed engine measurements or matched per-edge histories.
All 564 comparison checks pass. The baseline Thingsboard command ends
HARD_TIMEOUT after its valid capture and accepted report; no SARIF export
or successful outer completion is inferred. The original all-OK queue
assertion failure is preserved separately from the four valid captures.

| Project | Before raw TAINT | After raw TAINT | Before protection-only | After protection-only | Before other reasons | After other reasons |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Thingsboard | 2,081,189 | 1,800,397 | 130,921 | 901,285 | 1,950,268 | 899,112 |
| Conductor | 20,236 | 16,750 | 0 | 1 | 20,236 | 16,749 |
| Stirling-PDF | 24,774 | 24,479 | 15 | 26 | 24,759 | 24,453 |
| OWASP | 111,133 | 111,025 | 0 | 8 | 111,133 | 111,017 |

Every owner has zero removable-now memberships. Source/version-bound full
histograms, rejection reasons, both owners and actual removal events are in
the companion run-1 shape report. Its numbers are not substituted into the
earlier timed completion counters.

Thingsboard's population shift is substantial: static outputs rise from
902,474 to 1,660,499; nonstatic outputs fall from 1,178,715 to 139,898.
Static outputs already have 98.57% protection before, versus 99.32% after.
Their share of all retained concrete outputs rises from 43.36% to 92.23%.
Thus the overall protected share mixes a changed population with changes
inside each category. It is not a count of extra protection operations.
The old alias-effect primary reason accounts for 702,038 memberships;
nonstatic-to-nonstatic outputs fall from 780,032 to 13,893. These are own-policy
populations, not proof that the same old edges moved between categories.

| Project | Before physical dispatches | After physical dispatches | Change |
| --- | ---: | ---: | ---: |
| Thingsboard | 177,847,174 | 143,907,111 | -19.08% |
| Conductor | 6,677,025 | 6,652,192 | -0.37% |
| Stirling-PDF | 5,343,031 | 5,569,881 | +4.25% |
| OWASP | 63,017,085 | 62,973,426 | -0.07% |

Both sides use frozen actor arithmetic: steps minus packed mark credits plus
packed invocations. Actor counts match per project. The current-only hot
diagnostic additionally classifies pure unchanged visits. Instrumentation
and scheduling differ, so this is not a controlled timing decomposition.
OWASP has no aggregate outer-operation explosion in these captures; its
time regression still needs an inner-work/runtime explanation.

The timed explicit handoff totals are also lower:

| Project | Before run-2 demand patterns | After run-2 demand patterns |
| --- | ---: | ---: |
| Thingsboard | 2,380,152 | 2,077,650 |
| Conductor | 72,850 | 69,677 |
| Stirling-PDF | 36,773 | 36,468 |
| OWASP | 133,966 | 133,858 |

These count deduplicated normalized explicit patterns, not marked-only
publication callbacks. Implicit static completion is a symbolic policy,
not an added method-by-field matrix. The separate diagnostic executions have
their own handoff totals in the companion report. A marked summary count
is not automatically an identical normalized demand count.

## Joined run-1 edge shapes

All four separate diagnostics reach, complete and accept **run-1**. Each
table row below is a raw-owner partition from that invocation. Its selected
owner has the same logical counts; the two owners are not added.

| Project | Retained TAINT | Removable now | Protection-only | Other reasons | Flag annotations |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Thingsboard | 1,800,397 | 0 | 901,285 | 899,112 | 1,737,136 |
| Conductor | 16,750 | 0 | 1 | 16,749 | 22 |
| Stirling-PDF | 24,479 | 0 | 26 | 24,453 | 2,273 |
| OWASP | 111,025 | 0 | 8 | 111,017 | 460 |

Conductor's diagnostic total differs slightly from its timed completion
counter. Both executions keep their own source/configuration and count
binding. Use the diagnostic's total for its partition, not the timed total.

| Project | STAR to STAR | STAR to ANY | EXACT to EXACT | EXACT to ANY | EXACT to must | STAR to EXACT |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Thingsboard | 30 | 1,722,623 | 14,977 | 50,468 | 10,839 | 1,460 |
| Conductor | 8 | 6 | 5,398 | 9,422 | 1,279 | 637 |
| Stirling-PDF | 72 | 1,213 | 18,816 | 1,235 | 3,017 | 126 |
| OWASP | 99 | 77 | 109,041 | 1,534 | 107 | 167 |

These are retained concrete outputs, not initial seed counts or counts of
already removed relations. All are DEMAND. MUST is the current
`ANY_TAINT` nonexact tail. A tree may also contain exact siblings; the
per-membership table uses each leaf's actual tail.

Thingsboard's retained outputs are mostly nonstatic-premise to static-result
relations: 1,640,454. It also has 102,961 static-premise to nonstatic-result,
23,044 ZERO to nonstatic, 20,045 ZERO to static and 13,893 nonstatic to
nonstatic memberships. No static-to-static summary remains. Static here
describes the conclusion or premise explicitly; it does not mean an
intra-procedural static fact traversed all statements. The process counters
in the next section show that ordinary method-edge work is nonstatic.

### Thingsboard coverage and representation

The separate diagnostic reaches, completes and accepts **run-1**. It has
the same final runtime plus a tested read-only census. Its engine time is
not the timed performance result. Each raw/selected owner has this disjoint
partition:

| Retained concrete membership category | Count |
| --- | ---: |
| Removable with protection honored | 0 |
| Blocked only by protection | 901,285 |
| Not covered for another reason | 899,112 |
| Total | 1,800,397 |

The 1,737,136 flag annotations are a separate measurement. A flag can occur
on a cross-mark result with no eligible FLOW counterpart. It does not mean
that the flag is the only blocker.

| Primary reason among the 899,112 other memberships | Count |
| --- | ---: |
| Cross-atom relation | 817,618 |
| ZERO initial | 43,089 |
| Unsupported initial | 33,195 |
| FLOW excludes the selected atom | 3,934 |
| Unsupported output | 1,096 |
| Output base differs | 108 |
| No FLOW counterpart | 54 |
| Output tail differs | 18 |

One tail-mismatch example is `CassandraToSqlColumn.getColumnValue(Row)`:
`arg0.*/T3 -> ret.*/T3` is retained, while the matching FLOW result is
`ret.[any]` at DEMAND and excludes T1/T2, not T3. The selected replacement
law requires equal tails. The helper `replaceNullChars` supplies a
source/model derivation of ANY: Pattern.matcher copies its argument to
`Matcher.group.String.content`; the limit of one cuts that two-field image
to `Matcher.group.[any]`, then the applicable Matcher.replaceAll model
reads `group` into the root return. Four external tests execute the actual
final AP/store primitives and confirm this cut and return kind.

They also reproduce a valid admission sequence: a FLOW ANY arrives first
and suppresses a later same-layer FLOW STAR; a marked ANY offer is covered
and rejected, but the marked STAR remains. Reversing arrival order or
changing layer keeps the appropriate STAR coverage. This explains how the
sampled table can occur. It does not establish the historical first producer
or winning branch. Driver `DefaultRow.data` bytecode is not used as a
claimed producer: ordinary library bodies are excluded under this model's
unit policy, and external getter fallback models are STAR-to-STAR.

Raw admission rejected 7,327,506 covered offers. It compacted 102 stored
memberships. These are event counts, can include repeated offers, and are
not a history of distinct removed edges. Selected admission has zero offer
rejections and the same 102 compaction events. Do not add the owners.

The source-derived logical backend split is 905,399 diagonal memberships
(905,219 protected), and 894,998 scalar fallback memberships (831,917
protected). This split uses the admitted same-atom STAR/ANY invariant and
decoded per-membership shape counts. It does not subtract physical mark
rows from logical path counts. The joined diagnostic separately has 25,820
diagonal geometry rows, 176,807 diagonal mark rows and 18,239 scalar rows.

Full protection is common in decoded stored trees, but identity sharing is
rare: 182,426 trees with 1,720,875 memberships have structurally equal payload
and mask roots; 61 trees/memberships share the identical root object. There
are 360 partial trees with 32,166 memberships, and 12,199 unprotected trees
with 47,295 memberships. These tree classes and membership totals reconcile.
They do not measure the joint guard needed to reuse both subtraction passes
at every admission.

Within each method and owner, exact complete TAINT templates under unary
nonzero premises have 1,757,308 memberships across 193,732 origin/template
pairs. The 115,108 distinct templates carry 1,032,432 memberships. Repeated
templates under another origin account for 724,876 memberships. Maximum
origin width is six. This is a potential sharing population, not permission
to union origins or remove a required premise. It is not a measured byte
saving and does not cover ZERO or ND origins.

## What Thingsboard actually processes in run-1

The separate joined diagnostics measure these work counts. Each reaches,
completes and accepts **run-1**; none of these diagnostic times replaces
the timed engine comparison.

| Project | Physical method-edge invocations | Scalar TAINT headers | Pure unchanged scalar callbacks | Pure share of physical invocations |
| --- | ---: | ---: | ---: | ---: |
| Thingsboard | 143,907,111 | 128,093,674 | 71,897,409 | 49.96% |
| Conductor | 6,652,192 | 3,291,538 | 2,915,724 | 43.83% |
| Stirling-PDF | 5,569,881 | 3,101,198 | 2,804,145 | 50.34% |
| OWASP | 62,973,426 | 58,213,674 | 28,618,850 | 45.45% |

These counts expose a much larger workload than call-input delta counts
alone. They show potentially avoidable ordinary statement visits. They
do not by themselves explain the OWASP before/after time regression.

The joined diagnostic records 140,288,224 scalar process calls and 3,618,887
packed process calls: **143,907,111 physical method-edge invocations**.
Actor credits reconcile to 147,077,789 = 140,288,224 scalar calls + 6,789,565
packed mark credits. A further 1,011,222 point resumes are counted separately.
Stored summary memberships and actor credits are not the same unit.

There are 128,093,674 scalar TAINT calls. Of all scalar calls, 86,690,000
invoke the unchanged callback. Of these, 71,897,409 visit a non-call,
non-exit point with no source, conjunction or static operation. These pure
unchanged callbacks account for 49.96% of all physical method-edge
invocations. The current unchanged path already avoids fact-store admission,
but still enqueues the successor and processes the same fact at the next
statement. It therefore avoids a storage operation without avoiding this
repeated per-statement work.

The pure count is an opportunity bound, not a proved count of nodes that
can all be removed. Bypass needs a source/rule/static/exit/resume and cycle
proof. It does not imply a 2x whole-engine speedup. Processing
`EdgeGrpcSession.processUplinkMsg` alone accounts for 14,676,377 physical
invocations, about 10.2% of the total. The final next-iteration proposal
must target this work as well as retained summary representation.

## Remaining gates and next work

The final source/form/point/summary dossiers cover all nine missing PDF
native locations. Seven have a descendant source-to-marker guard loss and
two have positive marker evidence at the native return with a different
export location. A same-method finding alone is not an equivalent flow.
The catalog control reproduces the loss with the same native core. These
cases remain failed strict-location checks, rather than newly introduced
losses from the selected concrete-STAR optimization. No ZERO-only exit
change or unrelated catalog/export fix is included.

The next proposal distinguishes avoided statement visits, demand-guided
callee computation, direct known-static projection and equal mask images.
Restoring demand-guided FLOW abstraction is a major admission/publication
change from StrongQueries; a covering persistent record alone does not
prove that a method's complete answer set is available. Static completion,
later forward ND restriction, field transfer and source/sink behavior need
explicit scope and proofs before such a change is implemented.

## Reproduce and inspect the evidence

The companion [run-1 shape report](bidirectional-correlated-concrete-run1-shapes-20261026.md) and [work comparison](bidirectional-correlated-concrete-run1-work-20261026.md) contain full before/after tables. The [machine-readable report](bidirectional-correlated-concrete-performance-20261026.json) embeds all seventeen representative concrete edges and complete matching FLOW candidate lists, code snippets, per-project commands, profiles, heap analyses, finding cases and hashed source bindings. Counts with different units or invocation identities remain separate.

The selected runtime is already committed. The [local validation report](bidirectional-correlated-concrete-validation-20261026.md), [implementation proposal](../design/bidirectional-correlated-concrete-implementation-20261026.md) and [next-iteration proposal](../design/bidirectional-correlated-concrete-next-iteration-20261026.md) state the tested behavior and remaining work. No next-iteration runtime change is included.

The following are the exact Gradle commands from the four final manifests.
Run from a checkout at the measured runtime with the retained init scripts;
the scripts contain each model, budget, JVM arguments and output path.
These commands start new expensive project analyses. They were not rerun
while writing this report.

```sh
# thingsboard
./gradlew :runProjectAnalyzer --console=plain -I /drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/candidate-final-results/thingsboard/bidi/benchmark.init.gradle -x :opentaint-ir:go:buildGoServer
# conductor
./gradlew :runProjectAnalyzer --console=plain -I /drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/candidate-final-results/conductor/bidi/benchmark.init.gradle -x :opentaint-ir:go:buildGoServer
# Stirling-PDF
./gradlew :runProjectAnalyzer --console=plain -I /drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/candidate-final-results/Stirling-PDF/bidi/benchmark.init.gradle -x :opentaint-ir:go:buildGoServer
# OWASP
./gradlew :runProjectAnalyzer --console=plain -I /drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/candidate-final-results/OWASP/bidi/benchmark.init.gradle -x :opentaint-ir:go:buildGoServer
```

To repeat the census, use separate checkouts at the pinned source revisions.
Apply each lane's read-only diagnostic patch and run its existing
`runProjectAnalyzer` manifest command. The [final diagnostic controls](../../../correlated-concrete-20261026/validation/shape-probe/terminal.json) and [baseline preparation](../../../correlated-concrete-20261026/validation/baseline-shape-probe/prepared.json) bind the patch, commands and tests. Use the old normalizer for the old lane;
do not transplant the new predicate into the baseline. Keep all diagnostic
times out of the timed performance comparison. The [baseline capture-quality companion](../../../correlated-concrete-20261026/validation/baseline-shape-probe/capture-quality-companion.json) preserves the failed outer all-OK queue assertion while validating the four completed run-1 captures.

The following command regenerates the combined JSON from the retained
receipts. It starts no analyzer, JVM, heap parser or project:

```sh
python3 /drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/tools/build_final_report_data.py
```

Additional direct evidence:

- [Final fixed-input/source guards](../../../correlated-concrete-20261026/preparation/candidate-final-campaign.json).
- [Actual three-heap comparison](../../../correlated-concrete-20261026/final-heap-analysis/comparison.md) and [native Conductor heap](../../../correlated-concrete-20261026/main-heap-analysis/conductor).
- [Official profile event-count controls](../../../correlated-concrete-20261026/validation/final-profile-event-count-controls.json) and [profile summary](../../../correlated-concrete-20261026/validation/final-profiles-summary.md).
- [All seventeen current edge examples](../../../correlated-concrete-20261026/validation/final-run1-shapes/report.md) and [code under analysis](../../../correlated-concrete-20261026/validation/final-run1-shapes/code-under-analysis.md).
- [Actual AP/model ANY-origin replay](../../../correlated-concrete-20261026/validation/cassandra-regex-ap-replay/report.md).
- [Nine PDF source/guard/export cases](../../../correlated-concrete-20261026/validation/finding-comparison/source-review/final-diagnostic/report.md) and [same-core catalog control](../../../correlated-concrete-20261026/validation/finding-comparison/source-review/catalog-control/report.md).
- [Final-source test outcome comparison](../../../correlated-concrete-20261026/validation/final-tests-comparison.json) and [final Lean command receipt](../../../correlated-concrete-20261026/validation/cross-header-admission/lean-final-receipt.json).

Raw profiles and heaps stay outside Git. Earlier superseded captures were cleaned; the retained final/reference/native evidence is identified by the receipts. Relative raw-evidence links require the adjacent campaign directory. The combined JSON carries the count tables and representative facts in this repository.

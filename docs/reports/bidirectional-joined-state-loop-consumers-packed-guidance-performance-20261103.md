# Joined state, loop queries and packed static guidance: performance report

3 November 2026. All four project commands have ended.

Measured analyzer: `e558b496acf82de6ff136325d58f3d90ee5b8559`.
The [selected implementation proposal](../design/bidirectional-joined-state-loop-consumers-packed-guidance-implementation-20261103.md)
is implemented in three commits:

- `250c199bd`: capture exports, move input directories and release closed execution state before static binding.
- `9efe7ee15`: store frozen static W/R rows and terminal inputs with shared geometry and primitive memberships.
- `e558b496a`: reuse loop C2/C5 queries within one work quantum and drop dead local conclusions at block boundaries.

The source tree was fixed during the campaign. No new analyzer policy or extra
project configuration is part of these measurements.

## 1. Validation and measurement contract

All **2,431 common tests** and **461 JVM tests** pass. The analyzer runner builds.
The full suite includes lifecycle failures, exact moved-input identity, saved-only
block entries, ordered static query comparisons, full protection annotations,
native C5 comparisons and the `tmp = x` loop case. Closed stores reject live
operations. Tests use a new owner for a new lifecycle.

The [portable implementation receipt](data/bidirectional-joined-state-implementation-validation-20261103.json)
contains the source hashes, suite counts, model audits and raw-capture cleanup
receipt. The five unchanged finite Lean models pass: **256 theorems and 412
audited declarations**. Their permitted axioms are `propext` and `Quot.sound`.
The stock 768 MiB checker budget failed. A direct kernel check and declaration
audit passed with a 4,096 MiB budget. This checks the models; it does not verify
Kotlin, coroutine execution or JVM memory release.

Use the same four configurations as the previous campaign: FULL marks, 16 GiB,
statics and aliases enabled, and field limits `1,1,2,3,...`. Each command uses
the Gradle `runProjectAnalyzer` task. Analysis timeouts are 1,000 s for OWASP
and 1,080 s for the other projects. The outer timeout is 1,200 s. The saved
`f945f92c5` baseline is reused. The `86ad3b70b` and `050b83cfb` results provide
additional controls. No baseline is rerun.

Previous raw captures were hashed and removed: 46 files, 57,634,631,136 bytes.
Their derived tables, logs and SARIF files remain. The prior Thingsboard heap
simulation of 3.976 GiB is not an observed saving from this patch.

### Timing and profile limits

Keep the existing formula:

```text
engineTime = elapsed RunManager call - joinedStaticBindingTime
```

Static binding time includes prune, writer binding and catalog freeze.
The new `sealReleaseTime` is a separate subset of elapsed time. It adds the
pre-bind capture/release work and the post-bind input-lease close. It is not
one contiguous interval. Do not subtract it from engine time again.

The static-binding log is written after lease close. A window obtained by
subtracting its duration from that log clock is approximate. Exact run markers,
reported durations and sampled stacks must remain separate observations.

JFR and CPU profiles are samples. Allocation weights show churn, not retained
ownership. GC pause time is not GC CPU time. RSS is not live Java heap.
Rolling or overlapping JFR recordings must not be added together. Heavy profile
analysis started after all four project commands ended.

## 2. Current outcomes

The labels below mean **latest reached / completed / accepted forward report**.

| Project | Latest run labels | Command result | Exact finding comparison |
| --- | --- | --- | --- |
| OWASP | run-5 / run-5 / run-5 | Complete; 199.338 s | All 4,112 identities match f945, 86ad and 050b |
| Conductor | run-6 / run-5 / run-5 | Timeout; 1,121.682 s | All 7 identities match f945, 86ad and 050b; provisional report |
| Thingsboard | run-1 / none / none | Timeout; 1,122.121 s | No accepted report; coverage is censored |
| Stirling-PDF | run-8 / run-7 / run-7 | Timeout; 1,110.179 s | Same 22 identities as 86ad and 050b; 3 missing and 8 added against f945 |

The [quality audit](data/bidirectional-joined-state-quality-20261103.json)
contains exact identity sets, occurrence data, changed SARIF results and input
hashes. Equal identity sets do not mean byte-identical SARIF or equal traces.
A timeout can retain an accepted earlier snapshot; it is not a convergence result. A missing
report from an unfinished run is not a proved false negative.

## 3. OWASP: complete through run-5

OWASP completes with all 4,112 exact baseline identities and no added identity.
The accepted forward run is run-5. Its outgoing demand is empty.

| Run | Direction / limit | Engine s | Outgoing demand | Target demand | Reports |
| --- | --- | ---: | ---: | ---: | ---: |
| run-1 | FORWARD / 1 | 77.437 | 162,366 | 14,087 | 3,227 |
| run-2 | BACKWARD / 1 | 26.994 | 27,419 | 2,463 | 3,227 |
| run-3 | FORWARD / 2 | 16.603 | 176 | 80 | 4,112 |
| run-4 | BACKWARD / 3 | 0.289 | 135 | 42 | 4,112 |
| run-5 | FORWARD / 4 | 0.574 | 0 | 0 | 4,112 |

Run-1 static binding takes 0.477 s. Its seal/release duration is 0.183 s.
The run-1 engine remains above the 60 s target. The complete command takes
199.338 s versus 204.978 s in 050b. Command time includes setup and reporting.

## 4. Conductor: mixed completed-run results

Conductor reaches backward run-6 and times out. Forward run-5 is the last
completed and accepted report. It retains all seven exact baseline identities.

| Run | Direction / limit | Status | Engine s |
| --- | --- | --- | ---: |
| run-1 | FORWARD / 1 | Complete | 14.834 |
| run-2 | BACKWARD / 1 | Complete | 22.188 |
| run-3 | FORWARD / 2 | Complete | 33.947 |
| run-4 | BACKWARD / 3 | Complete | 281.981 |
| run-5 | FORWARD / 4 | Complete | 232.558 |
| run-6 | BACKWARD / 5 | Timeout | 463.287 |

| Completed run | Outgoing demand | Method keys with demand | Target demand | Reports |
| --- | ---: | ---: | ---: | ---: |
| run-1 | 120,070 | 6,763 | 7,896 | 2 |
| run-2 | 239,191 | 9,366 | 404 | 2 |
| run-3 | 47,462 | 661 | 4,214 | 5 |
| run-4 | 127,564 | 443 | 39 | 5 |
| run-5 | 260,822 | 414 | 9,526 | 7 |

There is no completed run-6 frontier. Its timeout diagnostics are not a
substitute for an outgoing demand snapshot.

Run-4 takes 281.981 s versus 249.455 s in 050b. Run-5 takes 232.558 s versus
463.785 s. Run-6 receives more time because earlier runs use less of the fixed
budget. Its longer aborted duration is not a completed-run slowdown ratio.

### More work in run-4

The current run-4 has 1,087,616 processed physical packets versus 842,344 in
050b, an increase of 29.1%. Candidate offers increase by 40.6%. Offered initial
keys increase from 113,338 to 169,049. These are event counts, not unique facts.

The same 24 MethodKeys appear in both hot loop-owner samples. Their observer
calls increase from 19.630 million to 30.613 million. Raw scalar queries increase
from 8.442 million to 13.285 million. Trials per scalar decrease slightly,
from 1.325 to 1.304. This points to more offered work, rather than more trial
depth per scalar. Incoming demand after run-3 increases by 6.62%, from 44,515
to 47,462 rows. The completed runs therefore have different workloads.

No protected output membership is present in either version's run-3 public or
block census. The retained samples do not establish protected rows as the cause
of this frontier growth. They also do not record a complete transient history.

### Query counters need separate denominators

Current run-4 hot owners make 61.232 million logical C2 calls. The cache answers
43.3%; 34.736 million still execute the native lookup. Their C5 memo hit rate is
97.3%, with 192,148 preparations and 2,518,214 entry checks. No factory fallback
is recorded in this sample. CPU attribution is given in section 7.

In run-5, the sample records 949,699 C5 factory attempts, 49,699,051 entry checks,
21.053 million memo hits and 8.932 million skipped empty DATA replays. The sample
contains 243,046 dead-local guard drops. A packet can reach more than one guard;
this is not a unique-fact count.

These are bounded owner samples. C5 memo hits include cached negative plans.
A cached negative plan still uses native C5. Factory-fallback counts exclude
later native executions through that cached result. Cache counts do not prove
the number of distinct contexts or the cost of capacity and quantum resets.

### Lightweight memory result: run-6

The [interim memory audit](data/bidirectional-joined-state-memory-conductor-interim-20261103.json)
uses only GC logs, resource samples and run markers. Run-6 has post-pause heap
min/max/last values of 4.992/14.194/7.435 GiB. Successive 60 s minima range from
about 4.99 to 5.23 GiB. The logs show heavy churn with a fairly stable low-water
level. They do not demonstrate unbounded retained growth.

The sum of heap decreases across pauses is 3,665.740 GiB. This is not an exact
allocation measurement. Pause wall time is 3.149 s; concurrent GC CPU is a
separate measure. No Full GC, OOM or heap dump is recorded. Peak whole-command
RSS is 18.286 GiB during SARIF reporting, after run-6 ends. Run-6 peak RSS is
18.057 GiB. RSS above Xmx does not identify exact native-memory ownership.

## 5. Thingsboard: engine work ends, static completion times out

Thingsboard reaches run-1. No complete iteration or forward report is accepted.
Engine time is 686.278 s. Static completion then takes 240.471 s and times out.
Seal/release time is 0.739 s. The final command takes 1,122.121 s.

The exported report has zero identities. All 14 f945 and 13 86ad identities are
absent from this unaccepted export. These are censored observations, not 14 or
13 demonstrated false negatives. The 050b control also has no accepted report.

The [lightweight memory audit](data/bidirectional-joined-state-memory-thingsboard-interim-20261103.json)
records two early high-memory warnings. Full GCs recover heap occupancy to
about 9.273 GiB. No OOM or heap capture follows. Around the reconstructed
binding boundary, post-pause minima fall from 13.880 GiB in the preceding
minute to 9.330 GiB in the first binding minute and 9.005 GiB in the final
minute. RSS remains near 18.295 GiB while Java heap remains committed at 16 GiB.
These measurements show lower later occupancy. They do not identify exact
retained owners or attribute a byte saving to the released fields.

The static log prints `no-completed-binding`. Its zero candidate and phase
counters are unavailable partial-result placeholders. They do not prove that
no candidates, pruning or writer binding were processed.

The continuous JFR recording contains 16,759 Java execution samples in the
reconstructed static-completion window. Of these, 16,471 (98.28%) contain
`OwnedJoinedStaticWriterBinding.complete`. Caller-input visits account for
85.98%; `ApOps.satisfying` accounts for 46.02%; summary application accounts for
23.72%. These are overlapping inclusive shares. This identifies writer/input
binding as the main sampled stage, rather than survivor pruning or catalog
freeze. The near-limit CPU capture also contains substantial native GC:
60.68% of its 7,577 all-thread samples. Its Java stacks are almost all inside
the same writer-binding operation. Neither percentage is wall time.

During engine work, the retained JFR samples show another repeated join:
subscription replay and call-result handling. The last 30 engine seconds have
669 Java samples; 598 contain `SubscriptionManager.subscribe` and 583 contain
its replay. The rolling recording omits the first part of engine work, so its
whole-engine shares describe retained events, not a complete execution census.

## 6. Stirling-PDF: faster completed loops, run-8 still times out

Stirling-PDF completes run-7 and reaches backward run-8. Run-7 is the accepted
forward report. The final SARIF has 22 identities and is byte-identical to
86ad and 050b. Thus, the selected changes introduce no observed finding change
against those controls. They do not close the three strict f945 baseline gaps.

| Run | Direction / limit | Status | Engine s, 050b | Engine s, current | Outgoing demand | Target demand | Reports |
| --- | --- | --- | ---: | ---: | ---: | ---: | ---: |
| run-1 | FORWARD / 1 | Complete | 18.914 | 18.150 | 74,452 | 5,400 | 7 |
| run-2 | BACKWARD / 1 | Complete | 14.405 | 13.677 | 274,723 | 469 | 7 |
| run-3 | FORWARD / 2 | Complete | 4.958 | 4.590 | 1,454 | 137 | 21 |
| run-4 | BACKWARD / 3 | Complete | 4.839 | 4.431 | 3,769 | 102 | 21 |
| run-5 | FORWARD / 4 | Complete | 16.244 | 13.002 | 1,739 | 105 | 22 |
| run-6 | BACKWARD / 5 | Complete | 91.925 | 58.166 | 6,897 | 79 | 22 |
| run-7 | FORWARD / 6 | Complete | 860.464 | 507.119 | 3,806 | 103 | 22 |
| run-8 | BACKWARD / 7 | Timeout | 51.108, partial | 444.341, partial | Unavailable | Unavailable | Last accepted: 22 |

Completed run-6 is 36.7% faster and run-7 is 41.1% faster. Run-8 receives more
of the fixed budget; the two partial durations are not a slowdown ratio.
Run-7 process CPU is about 521 s over 507 s elapsed, or 1.03 cores on average.
This points to owner-local work rather than high parallel utilization.

The same ten loop owners complete in both versions. Run-7 observer calls fall
from 11.228 million to 9.735 million. Raw scalar queries fall from 4.915 million
to 4.108 million. Physical processed packets increase by 17.2%, while public
method candidate offers fall by 51.9%. Different counters measure different
work; this is not an equal-work speed comparison.

The run-7 C5 memo hit rate is 99.972%. Native C2-direct calls fall from 45.375
million to 12.179 million. However, **502.471 million C5 rows are still
attempted**, versus 488.917 million before. The cache removes repeated entry
checks; it does not remove repeated exit-row selection and intersection.
There are 33,366 empty-DATA replay skips, confined to `PdfAttachmentHandler`.
The dominant `decodeMimeHeader` owner has no such skip.

## 7. CPU and allocation: remaining work

The [portable profile data](data/bidirectional-joined-state-profiles-20261103.json)
contains recording hashes, selected event windows, stack/class rankings,
sample counts, allocation weights, reader versions and all CPU captures.
The [campaign data](data/bidirectional-joined-state-campaign-20261103.json)
contains all run markers, frontiers, counters and exact OOM/timeout signals.
The [query audit](data/bidirectional-joined-state-query-workload-20261103.json)
contains the detailed old/current query comparison.

| Project / run | Java samples | Loop observer share | C5 share within observer | Saved AP application share within observer |
| --- | ---: | ---: | ---: | ---: |
| Conductor run-4 | 5,905 | 46.35% | 23.57% | 3.62% |
| Conductor run-6, partial | 79,421 | 94.28% | 75.12% | 6.38% |
| Stirling-PDF run-7 | 21,365 | 93.16% | 41.59% | 22.05% |
| Stirling-PDF run-8, partial | 18,562 | 73.48% | 66.87% | 6.43% |

The denominators differ between the last two columns and the observer column.
They must not be added. An async-profiler capture after 60 s gives independent
all-thread evidence: observer shares are 56.45% in Conductor run-6, 94.12% in
Stirling run-7 and 90.47% in Stirling run-8. Native GC is 30.32% of Conductor's
same run-6 capture. Java-only JFR samples omit that native GC work.

Fine stack classification separates the C5 region from outer callback frames.
The [fine CPU audit](data/bidirectional-joined-state-query-fine-cpu-20261103.json)
embeds the classifier, selected windows, source hashes and 42 aggregate checks.
In Conductor run-6, output-path index selection is 31.15% of all Java samples,
output restriction is 21.87%, row selection is 13.47%, entry preparation and
lookup are 2.88%, and the actual C5 field cut is 1.27%. In Stirling run-8,
output-path selection is 28.76%, output restriction 10.90%, and row selection
6.21%. This supports output-side work removal as the first next target.

Do not interpret an outer `transportProtection` or `limit` frame as the cost
of that primitive alone. Its callback can enclose the entire observer. The
fine classifier cuts the stack at the C5 region before it assigns the stage.

Conductor run-6 has about 3.93 TB of sampled allocation weight. The lambda
which inserts output demand IDs into a new C5 `HashSet` accounts for 36.31%
of that weight. The same site accounts for 23.98% in Stirling run-8 and 6.58%
in run-7. These weights estimate churn. They are not retained memory or exact
allocated bytes. The source creates this temporary output-ID set for each
prepared-plan intersection, even though the entry plan is already cached.

The main remaining cost is not simply the number of retained demand edges.
Many observer offers repeatedly join a small result with the same demand
geometry and then apply saved AL summaries to test enclosing demand. The new
cache handles entry eligibility, but that repeated output-side work remains.
This explains why a small frontier can still require hundreds of seconds.

OWASP has no loop-observer cost in run-1. Direct call handling accounts for
75.03% of its 3,452 Java samples. Call-plan construction and normalized rule
forms account for 9.88% and 7.54% of sampled allocation weight. These are
secondary design targets. They do not explain the slow later loop runs.

## 8. Finding gaps and limits

OWASP and Conductor retain all fixed baseline identities. Stirling has the
same three missing and eight added identities as the controls before this
patch. Added identities are report differences; they are not all verified
false positives. Thingsboard has no accepted report, so its coverage remains
unresolved under the configured budget.

Two Stirling gaps concern controller return locations. The current report
uses a representative final JIR return when there is no concrete return
witness. The fixed baseline uses a branch return. This explains the different
location selection, but does not prove that every old branch witness survives.
The exact identity gate remains failed; these rows are not waived.

The third gap is the command sink at `ProcessExecutor:183`. A focused native
test shows that an unresolved `add(URL)` can create an `ARGS` mark on the list
receiver, then `add("--pdf-forms")` clears that receiver mark. The marked-add
control reports; inserting the unmarked literal add loses the report. The
actual Stirling lowering contains these two unresolved calls and the matching
receiver reset actions. The reset is unconditional even when the source
condition is not satisfied. This is a verified transfer discontinuity. The
campaign does not contain a complete first-loss trace of incoming marks at
these two actual call sites, so the attribution has that explicit limit.
No unselected source-rule fix is included in this optimization patch.
The [focused receiver-reset report](bidirectional-stirling-command-receiver-reset-20261103.md)
contains the code, facts, exact rule actions and native witness.

### Memory and joined ownership

The [final memory audit](data/bidirectional-joined-state-memory-20261103.json)
embeds all per-run GC/resource tables, capture receipts, source ownership
checks and input hashes. No current heap dump exists because no OOM occurs.
No MAT result or exact retained-byte saving is claimed.

| Project | Latest reached / completed / accepted | Peak command RSS, GiB | Full GC count | OOM / heap captures |
| --- | --- | ---: | ---: | --- |
| OWASP | run-5 / run-5 / run-5 | 17.086 | 0 | 0 / 0 |
| Conductor | run-6 / run-5 / run-5 | 18.286 | 0 | 0 / 0 |
| Thingsboard | run-1 / none / none | 18.295 | 2 | 0 / 0 |
| Stirling-PDF | run-8 / run-7 / run-7 | 14.466 | 0 | 0 / 0 |

Thingsboard changes from OOM in 050b to timeout in this campaign. That is a
resource-outcome improvement under the same memory limit. It is not a
completed-run or quality success. Its post-join occupancy decrease is
consistent with earlier release, but does not measure the released owners.

Stirling run-7 has 60 s post-pause minima of about 5.985 to 6.175 GiB. Run-8
has post-pause min/max/last values of 6.199/7.041/7.032 GiB. Together with the
allocation samples, this supports a repeated-work/churn diagnosis for these
windows. It does not prove a global bound for later iterations.

Source and native lifecycle tests establish the ownership sequence: capture
admitted/native exports and exact local/caller inputs; seal and clear closed
instruction queues, current delivery indexes and runtime links; bind static
writers through the moved inputs; then close those input leases. Admitted
summaries, outgoing Targets, raw write identities and private static B records
remain available through binding. Source/sink seed and contributor data remain
available for the handoff. The generic actor fallback stays supported.
Without a fresh heap, this is a source/test audit, not a null-field census.

The successful packed static catalogs have these physical/logical counts:

| Project / run | W/R label memberships | Shared W/R geometries |
| --- | ---: | ---: |
| OWASP run-1 | 11,153 | 259 |
| Conductor run-1 | 63,012 | 7,867 |
| Stirling-PDF run-1 | 35,347 | 1,640 |

The membership count includes distinct ordered mark labels. It is not a count
of separately retained relation objects after packing. Thingsboard has no
completed catalog, so its counts are unavailable. These ratios establish
geometry sharing, not a measured byte saving.

## 9. Impact and next iteration

The patch improves the expensive completed Stirling runs and Conductor run-5.
It also permits much more work in the final backward run within the same
timeout. It does not make Thingsboard finish run-1, make the later projects
converge, or close the pre-existing strict baseline gaps.

Conductor run-4 regresses by 13.0%. It receives more demand and performs more
physical work. Neither the samples nor the counters identify one exact
upstream first difference responsible for that increase. A complete transient
per-scope inventory was not captured. Native oracle tests pass, but this does
not prove identical real-project intermediate inventories. Do not attribute
the whole difference to cache overhead or protected edges.

The [next-iteration proposal](../design/bidirectional-demand-output-selection-writer-binding-next-iteration-20261103.md)
prioritizes repeated C5 output selection, shared complete-premise writer
selection, and saved observer replay that cannot produce an accepted result.
It states current/new behavior, examples, exact equivalence obligations and
the measurements needed before each change is accepted. It also records the
source reset as a separate correctness issue. No further analyzer change is
part of this report.

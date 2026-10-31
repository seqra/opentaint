# Target-guided ZERO: project results and workload

Date: 31 October 2026. Runtime commit:
`c4a71246519ee5432879ce82518823f1703f3aa4`.
Selected mode: FULL, 16 GiB Java heap, field limits `1,1,2,3,…`.

OWASP completes **run-5** and retains all 4,112 baseline finding identities.
Conductor times out in **run-4**, thingsboard in **run-2**, and Stirling-PDF
in **run-8**. Their accepted forward reports are from run-3, run-1, and
run-7, respectively. No project has an OOM.

The large costs have different causes. Thingsboard spends its late run-2
on repeated static terminal-demand traversal. Conductor spends its late
run-4 on current-summary delivery and application. Stirling spends its slow
backward runs on call-stage application and edge storage, with substantial
allocation and GC work. One static optimization will not fix all three.

## 1. Scope and reproducibility

The implementation follows the
[current proposal](../design/bidirectional-constant-filter-target-zero-implementation-v2-20261031.md)
and [concrete exact-DEMAND amendment](../../spec/demand-layer-exact-initials.md).
The [validation report](bidirectional-target-zero-implementation-validation-20261031.md)
records 2,207 common-core tests, 452 JVM tests, and 39 script tests, all
passing. Both constructive proof packages pass their source-bound checks.

The selected changes reject constant-base runtime facts, use Targets to
guide ZERO, and preserve the layer of concrete initial admission. A complete
run-1 rule witness still produces singleton origin arms. An arm that loses
required support is DEMAND. It cannot create a NORMAL report. The actual
caller input stays separate from an admitted exact DEMAND hypothesis.
FLOW admission and normalization retain their selected rules. There is no
new grounding label or IR storage change.

The campaign used the committed runtime. The only tracked worktree change
at launch was the unrelated user edit in `issues.md`. It does not affect
the analyzer. New report files do not change this measured runtime.

The direct Gradle command for each project was:

```text
./gradlew :runProjectAnalyzer --console=plain \
  -I <project>/bidi/benchmark.init.gradle \
  -x :opentaint-ir:go:buildGoServer
```

The benchmark script supplied the configured project model and extensions.
It did not invoke the CLI. The saved command, JVM arguments, model hashes,
test revision, report hashes, and iteration markers are embedded in
[campaign data](data/bidirectional-target-zero-campaign-20261031.json).
The test input revision is `bbdbcc5fd35d976d93348760ea60561e4670f68c`.
Static handling and aliases are enabled. Optimization statistics and JFR
are enabled. Form statistics are disabled.

The IFDS budget is 1,000 seconds for OWASP and 1,080 seconds for each real
project. The outer command budget is 1,200 seconds. The campaign root is
`../constant-filter-target-zero-20261031`. It contains the raw logs,
continuous JFR, closed CPU captures, GC logs, resource samples, and SARIF.
The JSON files linked here retain the small results and source evidence
inside the repository. All principal measurements are also in this text.

The fixed baseline is `f945f92c5ae554ff4f5fc7696ee5a269210478bb`.
Its saved receipts come from
`../run1-full-work-batching-20261023/main-reference`. The baseline was not
run again. It uses the legacy analyzer, so bidi iteration labels do not
apply to it. The input model hashes and test revision match. Its heap is
8 GiB for OWASP, conductor, and Stirling, and 12 GiB for thingsboard.
Baseline optimization statistics are disabled. Thus the command times
below are observed outcomes, not a controlled speedup estimate for this
patch. The strict comparison tool reports these input qualifications.

## 2. Final outcomes

| Project | Status | Latest reached | Latest complete | Accepted report | Command wall, s | Peak process RSS, GiB |
|---|---|---|---|---|---:|---:|
| OWASP | OK | run-5 | run-5 | run-5 | 177.501 | 13.06 |
| conductor | TIMEOUT | run-4 | run-3 | run-3 | 1,123.050 | 17.98 |
| thingsboard | TIMEOUT | run-2 | run-1 | run-1 | 1,121.075 | 18.36 |
| Stirling-PDF | TIMEOUT | run-8 | run-7 | run-7 | 1,108.698 | 17.92 |

RSS includes native memory and can exceed the 16 GiB Java heap. Command
wall includes startup, prescan, analysis, and reporting. It is not engine
time. A timed-out backward run does not replace the accepted forward
report. No completed frontier is claimed for an incomplete run.

| Project | Saved baseline status | Baseline command wall, s | Current command wall, s | Baseline / current heap, GiB |
|---|---|---:|---:|---:|
| OWASP | OK | 539.774 | 177.501 | 8 / 16 |
| conductor | OK | 292.347 | 1,123.050 | 8 / 16 |
| thingsboard | TIMEOUT | 520.090 | 1,121.075 | 12 / 16 |
| Stirling-PDF | OK | 145.624 | 1,108.698 | 8 / 16 |

OWASP finishes earlier in this saved comparison. Conductor and Stirling
fail to finish where the baseline finished. Thingsboard does not finish
in either receipt. No OOM was observed with the 16 GiB heap. Excessive
work remains; this campaign does not isolate the effect of heap size.

## 3. Engine times and completed demand frontiers

`F` is forward. `B` is backward. `Demand` is the logged explicit normalized
handoff-row count. It includes typed control rows; it is not an AP-only
count. `Target` is the separate outgoing Target diagnostic and must not be
added to `Demand` as a disjoint population. Virtual static compositions
are not all materialized in these counts. `Keys` counts full method keys.
`Crossings` counts persisted-record applications, not distinct facts.

### OWASP: run-5 complete, run-5 accepted

| Run | Direction / limit | Engine, s | Demand | Keys | Target | Crossings | Reports |
|---|---|---:|---:|---:|---:|---:|---:|
| run-1 | F / 1 | 66.811 | 9,507 | 4,012 | 6,310 | 0 | 3,885 |
| run-2 | B / 1 | 23.397 | 10,073 | 4,048 | 1,600 | 10,609 | 3,885 |
| run-3 | F / 2 | 8.810 | 145 | 58 | 64 | 23,656 | 4,112 |
| run-4 | B / 3 | 0.216 | 110 | 38 | 36 | 578 | 4,112 |
| run-5 | F / 4 | 0.151 | 0 | 0 | 0 | 472 | 4,112 |

The driver stops with `NO_DEMAND_EDGE` after run-5. Bidi analysis takes
101.108 seconds. Run-1 joined static binding takes 0.089 seconds. Its first
report barrier takes 1.247 seconds. Run-1 engine time is still above the
60-second target.

### Conductor: run-4 timeout, run-3 accepted

| Run | Direction / limit | Engine, s | Demand | Keys | Target | Crossings | Reports |
|---|---|---:|---:|---:|---:|---:|---:|
| run-1 | F / 1 | 13.688 | 36,364 | 6,615 | 5,663 | 0 | 2 |
| run-2 | B / 1 | 15.141 | 153,939 | 9,366 | 360 | 167,677 | 2 |
| run-3 | F / 2 | 14.714 | 21,757 | 637 | 1,483 | 645,179 | 5 |
| run-4 | B / 3 | 1,009.021, timeout | — | — | — | — | — |

Run-1 joined binding takes 0.455 seconds. Its first barrier takes 1.216
seconds. Almost all later analysis time is in run-4. The small run-3
frontier does not bound the number of saved-record or current-summary
applications in run-4.

### Thingsboard: run-2 timeout, run-1 accepted

| Run | Direction / limit | Engine, s | Demand | Keys | Target | Crossings | Reports |
|---|---|---:|---:|---:|---:|---:|---:|
| run-1 | F / 1 | 437.728 | 4,621,432 | 30,211 | 2,714,707 | 0 | 13 |
| run-2 | B / 1 | 254.776, timeout | — | — | — | — | — |

The run-1 engine timer excludes joined static binding. The complete
run-1 interval is much longer:

| Phase | Time, s | Evidence |
|---|---:|---|
| Prescan interval | about 140.238 | Before run-1 starts |
| Run-1 logged engine | 437.728 | Worker analysis, plus small setup/teardown |
| Joined static binding | 225.956 | After worker JOIN; main thread |
| First report barrier | 18.191 | After joined binding |
| Complete run-1 iteration | 681.958 | Start to barrier end |
| Remaining run-2 engine | 254.776 | Until timeout |

The joined phase is not an intra-procedural static relay. It binds retained
writer relations to the completed caller input directory to build the
run-2 guidance. Avoiding run-1 static relays does not remove this phase.

### Stirling-PDF: run-8 timeout, run-7 accepted

| Run | Direction / limit | Engine, s | Demand | Keys | Target | Crossings | Reports |
|---|---|---:|---:|---:|---:|---:|---:|
| run-1 | F / 1 | 12.308 | 23,973 | 1,904 | 2,887 | 0 | 7 |
| run-2 | B / 1 | 6.504 | 115,158 | 4,205 | 344 | 12,901 | 7 |
| run-3 | F / 2 | 3.900 | 48,028 | 3,691 | 96 | 42,701 | 21 |
| run-4 | B / 3 | 4.354 | 26,134 | 3,672 | 80 | 148,461 | 21 |
| run-5 | F / 4 | 3.496 | 9,848 | 3,582 | 66 | 247,924 | 22 |
| run-6 | B / 5 | 312.047 | 9,286 | 3,582 | 55 | 2,846,169 | 22 |
| run-7 | F / 6 | 3.528 | 12,895 | 3,582 | 73 | 438,848 | 22 |
| run-8 | B / 7 | 716.925, timeout | — | — | — | — | — |

The fast forward runs and slow backward runs are distinct. There is no
static completion graph in run-6 or run-8: only run-2 can use that graph.
The observed demand sequence is not constant. This campaign does not
prove an infinite refinement cycle.

## 4. Finding comparison

Identity uses the rule, sink fingerprint, and full method signature.
The comparator also checks spans and multiplicity. It does not match
findings by total count alone.

| Project | Baseline | Current | Unchanged | Removed identities | Added identities |
|---|---:|---:|---:|---:|---:|
| OWASP | 4,112 | 4,112 | 4,112 | 0 | 0 |
| conductor | 7 | 5 | 5 | 2 | 0 |
| thingsboard | 14 | 13 | 13 | 1 | 0 |
| Stirling-PDF | 17 | 22 | 14 | 3 | 8 |

OWASP has equal counts for all 22 rules and no span or multiplicity
change. This meets the no-FN check against the saved baseline identities.

The three incomplete projects do not meet the no-missing-baseline check.
Timeout explains why refinement did not finish. It does not prove eventual
recovery or rule out a semantic defect. The following omissions remain
open; none was dismissed as a constant-only flow.

| Project | Missing baseline sink | Source and remaining guidance |
|---|---|---|
| conductor | `ScriptEvaluator.java:253`, `getSource(script)`, `Source.newBuilder` | Dynamic REST request data reaches the script parameter. Method has 2 outgoing guide rows after run-3. |
| conductor | `PythonEvaluator.java:63`, `Context.eval(python, wrappedExpression)` | Dynamic expression and input-map paths. Method has 3 guide rows after run-3. Blank-text checks do not establish sanitization. |
| thingsboard | `ReflectionUtils.java:27`, `Class.forName(targetType)` | Dynamic request-derived type name, before validating the loaded configuration. Sink method has 1 guide row after run-1; validator and caller have 37 and 21. |
| Stirling-PDF | `ProcessExecutor:183`, `ProcessBuilder(command)` | Baseline traces request URL into the command list. Method has 4 guide rows after run-7; run-8 is incomplete. |

These counts are method-level guidance, not proof that a particular sink
will be recovered. The ProcessBuilder rule covers tainted command-list
arguments. A separate URL argument and URL checks do not justify deleting
its configured finding, although the trace alone does not prove an exploit.

Stirling has two additional identity changes at method exits:

```text
ConvertEmlToPDF.convertEmlToPdf, same XSS rule: line 133 -> line 148
PipelineController.handleData, same XSS rule: line 90 -> line 130
```

The new Target export uses a Simple trace. When it has no preceding return
witness, `JirSarifGenerator.unwrapBoundary` selects the method's last
return. This explains the physical location change. It does not prove
equality with the old source-to-sink flow. The raw comparison retains both
removed and added identities.

All eight added Stirling rows have zero codeFlows:

| Added location | Kind |
|---|---|
| `ConvertEmlToPDF.java:148` | Same-rule/method exit replacement |
| `PipelineController.java:130` | Same-rule/method exit replacement, at final `return null` |
| `FilterController.java:107`, `:146`, `:175`, `:210` | Four additional method-exit reports, at final `return null` |
| `WebResponseUtils:42`, `:58` | Two additional response-helper reports |

The FilterController methods can return uploaded-file bytes before the
final null. The helper takes a dynamic content type. Thus a null report
anchor is not evidence of taint on the null constant. The current artifact
does not identify the contributing branch or prove the HTML context.
These additions are unverified findings, not automatically valid findings
or false positives. Target report location/trace preservation needs a
separate correctness follow-up.

The full per-location evidence is in
[OWASP](data/bidirectional-target-zero-owasp-20261031.json),
[conductor](data/bidirectional-target-zero-conductor-20261031.json),
[thingsboard](data/bidirectional-target-zero-thingsboard-20261031.json), and
[Stirling](data/bidirectional-target-zero-stirling-20261031.json).

## 5. Thingsboard: two large static costs

### Joined writer binding, after run-1 worker JOIN

| Counter | Value |
|---|---:|
| Observed candidate writer memberships | 2,699,759 |
| Lost candidate memberships retained for guidance | 467,941 |
| Writer offers | 26,409,078 |
| Admitted and processed writer rows | 2,351,008 |
| Candidate input visits | 222,626,595 |
| Matched input visits | 28,046,748 |
| Bound output offers | 27,946,039 |
| Exact `InputKey` duplicates | 0 |

Pruning takes 2.377 seconds, writer processing 218.285 seconds, and closure
freeze 1.552 seconds. The total joined phase takes 225.956 seconds.

The source stores a scalar writer `(owner, initial, static result)`.
Each writer repeats candidate selection against the same frozen callee
input directory. Its visited key includes the full call reference and
stage. The result uses the caller method, caller initial, and static
Pattern; it does not execute the caller suffix or aliases in this phase.

The zero duplicate counter says only that full call/stage/group keys do
not repeat inside one scalar writer. It does not establish that all
222.6 million selections or all output offers are semantically distinct.
The directory already selects unique member handles. A more useful unit
is the complete owner/premise input-selection problem, shared across its
different static results. A separate guide-only caller quotient may also
remove distinctions that cannot change its exported DEMAND Pattern.

The complete joined JFR window has 16,388 Java samples. The joined-input
visitor scope appears in 97.2%, including its matching and transfer
callbacks. Input matching appears in 39.2% and summary transfer in 35.2%.
Inclusive shares overlap. Estimated cumulative allocation is 552.842 GiB.
In the late joined CPU capture, native GC is 69.3% of all-thread samples.
All bidi workers are parked; the main thread runs joined binding.

### Run-2 terminal demand intersection

| Counter | Value |
|---|---:|
| C5 compositions attempted / accepted | 1,174,034,530 / 1,174,034,530 |
| C5 duplicate-state admissions | 1,147,998,193 |
| C5 admitted states / popped states | 108,665,651 / 108,648,447 |
| Static owner bit queries | 2,120,832,791 |

These are aggregate C5 counters. They include ordinary and typed-terminal
paths. The stack data identifies the leading path: `DemandStore.intersect`
appears in 94.9% of run-2 Java samples; `walkTargetOrigins` appears in
92.8%. The latter accounts for 84.5% of estimated allocation. Current
summary delivery is small in this run.

The cause is visible in the source:

```text
queuePublications -> published -> DemandStore.intersect
  visitControlPairs(includeDerived = original.isZero)
    walkTargetOrigins(method)
      start from every target input
      follow compatible static predecessors
      only then test the origin against the provided raw output
```

Every qualifying raw summary can start another terminal-origin search.
The ordinary AP query has endpoint-selection guards. This terminal query
does not receive the raw-output selector. Its local seen set prevents one
search from looping forever, but it is discarded at the next query. It
also detects duplicate states only after each predecessor has been
selected and composed. This creates much work without new demand rows.

The next design should select relevant origins before the walk and reuse
immutable reachability work. It must retain complete paired C5. A reader
mark filter alone is unsafe: a bridge can map writer mark U to reader
mark T. ZERO and nonstatic origins require a writer route; static origins
can also use a bridge-only route.

Statistics have a visible observer cost. In the near-limit CPU capture,
27.7% of all-thread leaf samples are in atomic counter increments from
the graph walk. The billion-step work is real, but this measurement does
not equal a production run with statistics disabled. No new unselected
configuration was run to estimate that difference.

See [thingsboard profile data](data/bidirectional-target-zero-thingsboard-profiles-20261031.json).

## 6. Conductor: long current-summary delivery

Run-4 has 14,278 Java execution samples. `onDelivery` appears in 72.3%
and accounts for 86.7% of estimated allocation. In the last 60 seconds
these shares reach 93.7% and 98.5%. The initial/intersection demand-query
family is only about 2.0% of run-4 Java samples. Call-plan construction
is about 0.1%. The thingsboard C5 fix will not address this hotspot.

| Run-4 counter increment | Value |
|---|---:|
| Selected call offers / saved replay invocations | 4,373,189 / 4,373,189 |
| Empty current-demand lookups | 3,330,099, or 76.1% of offers |
| Saved replay candidates / matches | 27,019,728 / 7,978,859 |
| Initial candidates / new initial keys | 2,056,696 / 12,493 |
| Accepted subscription deltas / new groups | 798,070 / 51,427 |

The 0.607% new-initial ratio does not imply that 99.393% of work is
redundant. An old initial can still get a new conclusion. Empty current
demand does not permit skipping saved NORMAL summaries: selected call
handling replays them before demand gating, on each offer.

The current delivery loop scans inputs separately for each fresh
publication, then matches, applies, and resumes the caller. Pure matching
is only 3.3% of the whole run-4 Java samples. A cache of match results
alone cannot explain a factor-of-two improvement. The larger opportunity
is to reduce publication/input products or share a larger pure transfer
before the required per-origin continuation.

The existing detached publication batch can contain several compatible
fresh deltas with the same complete premise and header. Storage deduplicates
their contents, but the notification list can still contain one row per
delta. Packing these deltas before notification can remove repeated
candidate scans and transfer calls. Batch width and distinct-header counts
were not recorded, so the achievable reduction is not yet known.

Two thread snapshots about 150 seconds apart show one active bidi worker
inside delivery and application. Saved per-thread CPU counters show about 1.05 bidi
worker cores plus 0.42 GC cores over that interval. For all of run-4,
process CPU is about 1.50 cores on average. Outer event counts grow from
67,949 to 73,395; 84 of 100 heartbeat intervals show no completed-event
growth. Large handlers do finish. This supports long nested work and low
parallelism; it does not prove an infinite loop.

See [conductor closed profile data](data/bidirectional-target-zero-conductor-profiles-20261031.json)
and its [saved thread evidence](data/bidirectional-target-zero-conductor-live-profile-20261031.json).

## 7. Stirling: saved-record and call-stage work

| Metric | run-6, complete | run-8, timeout |
|---|---:|---:|
| Call offers | 2,734,000, approximately | 6,456,000, approximately |
| Saved matches | 2,846,000, approximately | 6,564,000, approximately |
| Offers eligible for current demand | 30,126 | 33,361 |
| Empty current-demand offers | 98.90% | 99.48% |
| `MethodEdgeStore.add`, Java sample share | 34.1% | 33.8% |
| `cleanChain`, Java sample share | 14.4% | 16.5% |
| Estimated cumulative allocation, GiB | 950.702 | 2,160.443 |

One worker supplies 97.3% of run-6 Java samples and 91.3% of run-8 samples.
Current-summary `onDelivery` is below 0.1%. The near-limit CPU capture
has 69.6% native GC samples. A static C5 search or current-notification
batching fix alone does not explain this workload.

`cleanChain` includes all action stages. These stacks do not identify
return cleanup alone. The bulk FULL return-cleanup helper is currently
run-1-forward only. Backward stages do not use the forward MemoryEffect
guard. Skipping a backward alias or cleaner stage requires its own proof.

The source also shows a possible repeated AP traversal:

```text
transportProtection(input with non-subsumable marks):
  operation(protected part, collect output mask)
  operation(full input, attach output mask)
```

For an input with all taint memberships protected, these operations have
the same ordinary data. A one-pass implementation may be possible after proof. For a
partly protected input, the mask distinction is required. The broad
inclusive `transportProtection` stack contains callbacks and is not the
cost of flag bookkeeping. Direct `intersectTaintMask` allocation is about
12% in these runs. No full-mask/partial-mask count was collected. This is
a candidate for measurement, not an established factor-of-two fix.

The immediate follow-up is to measure native application output: complete
input and record identities, action-stage kinds, protection shape, and
new-versus-old post-statement memberships. The current profiles do not
show the values needed to prove that the millions of offers are repeated
semantic work. Saved replay must keep its selected order and frequency
unless a separate equivalent algorithm is proved.

See [Stirling profile data](data/bidirectional-target-zero-stirling-profiles-20261031.json).

## 8. OWASP: initial construction cost

`JIRCallPlanBuilder.build` appears in 50.4% of run-1 Java samples and
53.6% of run-2 samples. It accounts for 49.6% and 61.5% of estimated
allocation. Alias-plan construction appears in 26.2% of run-1 samples.
Demand lookup and publication delivery are small in the principal OWASP
runs. This is a fourth workload shape.

These stacks establish construction cost. They do not establish repeated
cache misses: form statistics were disabled. A lazy plan or cache proposal
must first distinguish necessary first construction from repeated builds.
It has lower priority than the billion-step thingsboard traversal and
the timed-out backward workloads.

The normal 30-second CPU capture starts late in run-1 and ends in run-2.
It is not a pure run-1 profile. The JFR analysis uses the exact run marker
windows. See [OWASP profile data](data/bidirectional-target-zero-owasp-profiles-20261031.json).

## 9. Memory evidence and capture limits

| Project / phase | Estimated allocation, GiB |
|---|---:|
| conductor run-1 / run-2 / run-3 / run-4 | 33.985 / 61.349 / 35.446 / 2,663.741 |
| thingsboard run-1 workers / joined binding / first barrier / run-2 | 1,838.928 / 552.842 / 8.347 / 1,599.189 |
| Stirling run-6 / run-8 | 950.702 / 2,160.443 |

These are JFR allocation-sample weights. They estimate cumulative
allocation, not retained memory. Inclusive frame shares overlap and must
not be added. CPU sample shares are not wall-time shares.

Late conductor run-4 young-GC observations return to about 5.01 GiB used
heap. Thingsboard returns to about 10.99 GiB near the worker end,
11.57–12.16 GiB near the joined end, and 11.76 GiB late in run-2.
Stirling run-6 ends with about 6.53 GiB observed post-GC heap. Run-8 has a
minimum observed post-GC heap of about 6.89 GiB and
late observations of about 11.15–11.18 GiB. Its occupancy still grows in
the final window; there is no observed memory convergence there.
Young-GC occupancy is not an exact retained-object count. Short
stop-the-world pauses also do not measure concurrent GC CPU. The CPU
captures show substantial native GC work.

There were no MemoryManager OOM events and no JVM OOM events. No new
HPROF was produced. Therefore this campaign has no new retained-container
layout. The reader was prepared but was not run against an old heap as a
substitute. The available evidence supports high allocation churn and
repeated work. It does not prove either bounded eventual memory or an
unbounded memory leak.

All analyzer processes, campaign commands, profiler attachments, and JFR
reader jobs have ended. Closed previous campaign captures were cleaned
before this campaign; the cleanup receipt records about 293 MB removed.
User `run-debug` material was preserved. The extra OWASP post-run capture
failed because another capture was active; it is excluded. Its successful
normal capture and JFR remain valid. Run-1 JFR snapshots overlap the
continuous recording and are not added as independent samples.

## 10. Next work

The [ranked next-iteration proposal](../design/bidirectional-target-zero-work-reduction-next-iteration-20261031.md)
targets endpoint-directed terminal demand queries, packed current-summary
delivery, and joined-writer input sharing. It includes a separate Stirling
native-output investigation. No candidate is implemented by this report.

The acceptance gaps stay explicit: two conductor baseline findings, one
thingsboard finding, and the Stirling ProcessBuilder finding remain absent
under timeout. Stirling exit locations and untraced additions need a
reporting check. A completed semantic comparison and a measured large
work reduction are required before these results can be called a complete
performance or no-FN success.

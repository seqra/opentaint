# Selected call policy: performance and memory

Date: 30–31 October 2026. Runtime: `e090118e5f9603f1973c0578a3e04998035f4508`.
All four analyzer commands and all profile/heap readers are closed.
The fresh histogram and retained-owner queries are complete. Two detailed
classifier limits are stated below.

The caller demand gate removes much input-store work. Stirling now completes
run-6 and reaches run-7. Conductor still times out in run-4. Thingsboard still
reaches OOM in run-2 at 16 GB. The next work must reduce summary delivery,
joined writer selection and output subtraction.

All exported finding identities and occurrence counts equal the previous
runtime. The fixed legacy baseline still has three missing Stirling identities
and many additional thingsboard candidates. The no-FN/few-FP target is not
established by this campaign.

## Implementation and validation

The [implementation contract](../design/bidirectional-selected-call-policy-implementation-20261030.md)
has two selected policy changes. Replay persisted NORMAL summaries on every
original offer. Admit current summaries and subscriptions only when complete
initial emission is nonempty. The caller sends immutable final initial keys;
the callee starts each key once without another demand lookup.

The initial-start gate, AP tables, field and mark transfer, exclusions,
protection, record transfer, aliases and stopping remain unchanged. Run-1 and
explicit backward ZERO handling retain their routes. No replay input history,
negative cache, IR storage change or reference-manager change was added.

Validation: 2,126 core tests and 452 JVM tests pass, with no failures, errors
or skips. The constructive Lean check passes 58 named theorems and 112 public
declarations. The [source adapter receipt](../../spec/lean/proposals/selected-call-policy-20261030/implementation-checks.json)
passes 20 checks. The finite model and source checks do not prove whole-project
finding completeness.

The persisted replay uses the core actor, so configured call-service wrappers
retain their existing route. Initial-key equality and the original AP and
receiver pipelines stay unchanged. Later proposal controls add seven tests:
the full supplemental run passes 2,133 core tests and 452 JVM tests, with no
failures, errors or skips. No next-candidate production change is included.

## Controls and current iteration status

Use Gradle `runProjectAnalyzer`, FULL marks, statics and aliases enabled,
16 GB, and limits `1,1,2,3,...`. OWASP uses its CI model and a 1,000-second
IFDS budget. The real projects use 1,080 seconds. The outer limit is 1,200
seconds from analyzer JVM launch. No baseline was rerun. No other project
configuration is part of this campaign.

The fixed finding baseline is the saved `f945f92c5ae554ff4f5fc7696ee5a269210478bb`
report. The immediately previous measured runtime is
`edb2e06cdb17eecafbe03415236bf56c57910239`, under the same current controls.
The legacy baseline has different heap ceilings; it is a finding comparison,
not a matched performance control.

| Project | Status | Reached | Complete | Accepted forward | Command s | Peak RSS GiB |
|---|---|---|---|---|---:|---:|
| OWASP | OK | run-5 | run-5 | run-5 | 276.657 | 17.660 |
| conductor | TIMEOUT | run-4 | run-3 | run-3 | 1,121.987 | 18.057 |
| thingsboard | OOM | run-2 | run-1 | run-1 | 1,077.986 | 18.403 |
| Stirling-PDF | TIMEOUT | run-7 | run-6 | run-5 | 1,111.913 | 17.791 |

A complete engine and an accepted forward report are different states. An
incomplete backward run does not replace the prior forward report. Outgoing
demand is unavailable for an incomplete engine; it must not be called zero.

Command time includes startup, prescan, reporting and capture work. RSS includes
native memory; it is not Java live heap. Prelaunch and postrun input audits
pass for 25 datasets and four models. Cleanup removed 27 prior closed capture
and index files, totaling 57,444,499,095 bytes. Hashes and parsed prior evidence
were retained. User debug directories were not changed.

## Closed OWASP and conductor results

OWASP retains all 4,112 baseline finding identities. It has the same 9,179
occurrences as the previous runtime. It stops after run-5 with no outgoing
demand. Command time changes from 278.577 to 276.657 seconds. This small
single-run difference is not evidence of a substantial speedup.

Conductor retains all seven baseline identities and all seven previous
occurrences. It still times out in run-4, as before. This incomplete run does
not prove whole-project absence of missing findings. The gate reduces input
stores, but remaining current-summary delivery dominates the time limit.

| Project | Run | Engine s | Previous engine s |
|---|---|---:|---:|
| OWASP | run-1 | 63.867 | 61.064 |
| OWASP | run-2 | 33.805 | 37.506 |
| OWASP | run-3 | 31.573 | 28.375 |
| OWASP | run-4 | 35.670 | 38.749 |
| OWASP | run-5 | 26.638 | 31.867 |
| conductor | run-1 | 13.469 | 12.780 |
| conductor | run-2 | 23.579 | 21.168 |
| conductor | run-3 | 14.377 | 17.876 |
| conductor | run-4, timeout | 1,001.477 | 1,000.877 |

Run-1 call routing is unchanged. Conductor's observed run-1 frontier is
33,148 memberships, versus 33,178 before. Its run-3 frontier is 20,661,
versus 23,896. Do not infer equal raw frontiers from unchanged run-1 source,
or infer a new field-transfer policy from these counts. Report comparisons
are separate evidence.

## The gate works; the heavy join remains

| Conductor run-4 count | New | Previous incomplete run-4 |
|---|---:|---:|
| Original restricted offers | 4,454,134 | not separately measured |
| Empty demand admission | 3,662,193 (82.22%) | no caller gate |
| Eligible offers / initial packets | 791,941 | not separately measured |
| Offered canonical initial keys | 2,052,959 | not separately measured |
| Fresh live deltas | 609,805 | 2,439,370 |
| Created input groups | 57,834 | 195,704 |
| Created index postings | 629,454 | 3,391,063 |
| Persisted replay candidates | 32,615,708 | not separately measured |
| Persisted replay matches | 7,807,279 | not separately measured |

These are unequal incomplete executions. They establish a large reduction in
retained-input admission work, not equal completed work or a per-finding cost.
Initial packets, offered keys and newly started keys are different counters.
The caller queries once; the new key packet causes no callee demand query.

Conductor run-4 has 14,138 recorded Java samples and about 2.928 TB of sampled
allocation weight. Current delivery accounts for 69.96% of Java samples and
87.83% of allocation. Persisted replay accounts for 9.29% and 2.75%; caller
demand lookup accounts for 1.84% and 0.36%; live input accumulation accounts
for 0.59% and 0.07%. These are inclusive stack families. Their shares overlap.

A closed long-task window at 22:56:10.923–22:56:40.965 UTC lies wholly in
run-4, with run-3 complete and accepted. Its JFR has 255 Java samples and
86.201 GB of sampled allocation weight. Current delivery accounts for
95.69% of Java samples. Persisted replay accounts for 0.78%.

| Operation in that window | Java share | Allocation share |
|---|---:|---:|
| Candidate snapshot | 19.22% | 1.23% |
| Full matching | 5.10% | 9.35% |
| Summary geometry application | 19.61% | 32.79% |
| Return resumption | 48.63% | 47.37% |
| Post-statement admission, nested in returns | 22.35% | 23.85% |
| Cleaner chain | 1.18% | 1.76% |

This is not a cleaner-chain explosion diagnosis. The largest sampled
`ArrayList.grow` path is summary graft construction; other paths include
call-expression reconstruction and stage output collection. The existing
base index already selects micro edges by input base.

The same native window has 5,262 weighted CPU samples. GC workers account
for 43.10% and current delivery for 55.82%. JFR reports only 0.086 seconds of
GC pause in this window. Native GC CPU and stop-the-world pause time are
different measurements. Logged heap occupancy cycles down as well as up;
this window shows heavy allocation churn, not a proved unbounded live heap.

Scheduler progress can be flat for minutes inside one callback. It later
advances again. Thread and profile evidence supports long synchronous
summary-delivery tasks. It does not prove an infinite loop or global
termination.

## Thingsboard run-1 and transition

Thingsboard reached run-2; run-1 is complete and accepted. Its run-1 engine
uses 390.372 seconds, versus 388.450 before. Joined binding uses 236.104
seconds, versus 232.465. The report barrier uses 8.227 seconds and the full
iteration uses 634.769 seconds. These times show no material improvement in
the unchanged run-1 route.

Joined binding processes 2,351,008 writers. It visits 222,615,530 candidate
inputs, accepts 28,045,257 matches and produces 27,942,954 bound outputs.
The writer portion uses 226.920 seconds. The new caller gate does not remove
this joined operation.

A separate closed 30-second profile is confirmed to be in joined binding by
a thread dump. It contains 2,196 Java samples and 81.578 GB of sampled
allocation weight. Summary matching accounts for 38.43% of Java samples and
60.24% of allocation. Trie work overlaps these families. The top Java leaf
is `MarkExclusions.excludes`, with 15.57%. Native GC workers account for
62.84% of CPU samples.

The query matches a writer's original nonstatic input, such as `p.*/FLOW`,
against frozen caller inputs. Different destinations with the same complete
original premise can repeat this selection. Query sharing can remove those
repeats. This does not relay static facts through run-1 method bodies.

A direct universal-premise result is a separate opportunity: every such visit
must match, so its count is at most 28,045,257, or 12.60% of all visits. This
case alone cannot explain the 87.40% rejected visits. The actual complete-query
multiplicity and premise-kind distribution remain unmeasured.


## All iteration times and demand frontiers

These are current-runtime outgoing relation memberships. They are not an
instruction-work count. Command-level iteration labels are in the status table.

| Project | Run | Direction | Limit | Engine status | Engine s | Outgoing demand | Method keys |
|---|---|---|---:|---|---:|---:|---:|
| OWASP | run-1 | forward | 1 | COMPLETE | 63.867 | 111,374 | 6,468 |
| OWASP | run-2 | backward | 1 | COMPLETE | 33.805 | 112,081 | 5,222 |
| OWASP | run-3 | forward | 2 | COMPLETE | 31.573 | 85 | 22 |
| OWASP | run-4 | backward | 3 | COMPLETE | 35.670 | 198,829 | 3,791 |
| OWASP | run-5 | forward | 4 | COMPLETE | 26.638 | 0 | 0 |
| conductor | run-1 | forward | 1 | COMPLETE | 13.469 | 33,148 | 6,289 |
| conductor | run-2 | backward | 1 | COMPLETE | 23.579 | 339,729 | 9,263 |
| conductor | run-3 | forward | 2 | COMPLETE | 14.377 | 20,661 | 552 |
| conductor | run-4 | backward | 3 | TIMEOUT | 1001.477 | unavailable | unavailable |
| thingsboard | run-1 | forward | 1 | COMPLETE | 390.372 | 1,927,719 | 20,870 |
| thingsboard | run-2 | backward | 1 | OOM | 226.862 | unavailable | unavailable |
| Stirling-PDF | run-1 | forward | 1 | COMPLETE | 11.868 | 26,494 | 1,803 |
| Stirling-PDF | run-2 | backward | 1 | COMPLETE | 23.359 | 455,311 | 4,208 |
| Stirling-PDF | run-3 | forward | 2 | COMPLETE | 4.425 | 44,679 | 3,690 |
| Stirling-PDF | run-4 | backward | 3 | COMPLETE | 10.022 | 10,583 | 351 |
| Stirling-PDF | run-5 | forward | 4 | COMPLETE | 73.466 | 888 | 74 |
| Stirling-PDF | run-6 | backward | 5 | COMPLETE | 357.562 | 185,950 | 306 |
| Stirling-PDF | run-7 | forward | 6 | TIMEOUT | 581.009 | unavailable | unavailable |

OWASP stops after run-5 with `NO_DEMAND_EDGE`. Stirling's 888 incoming run-6
memberships still permit millions of offers and large post-statement joins.
A small frontier does not bound the number of intermediate derivations.

| Project | Run-1 engine s | Joined binding s | Writer application s | Report barrier s | Full iteration s |
|---|---:|---:|---:|---:|---:|
| OWASP | 63.867 | 0.114 | 0.011 | 2.189 | 66.197 |
| conductor | 13.469 | 0.545 | 0.316 | 0.458 | 14.518 |
| thingsboard | 390.372 | 236.104 | 226.920 | 8.227 | 634.769 |
| Stirling-PDF | 11.868 | 0.217 | 0.077 | 0.244 | 12.343 |

Thingsboard binding also spends 5.079 seconds pruning and 1.126 seconds freezing
its closure. Those are nested parts of binding. The previous thingsboard
command also reaches run-2 OOM. Neither OOM time is completed-run performance.

Stirling previously timed out in run-6 after 935.324 engine seconds. It now
completes run-6 in 357.562 seconds and reaches run-7. Its incoming run-6 frontier
also changes from 1,284 to 888. This is further progress, not an equal-work
speedup factor. Its command remains limited by timeout.

The older saved `c98d12582a138d5898e94908ee6690dda73998ca` measurement
completed conductor run-4 in 309.370 seconds
and run-5 in 139.016 seconds, then timed out in run-6. The current optimization
does not restore that progress. Its incoming run-4 frontier also differs:
24,131 / 555 method keys then, 23,896 / 556 in the previous runtime, and
20,661 / 552 now. The embedded historical comparison keeps every iteration
and its original source line. No old analyzer was rerun.

## Finding locations and accuracy limits

An identity is the comparator's strict rule and sink-location key. Occurrences
retain multiplicity. Exact keys and counts are embedded in the companion data.

| Project | Current identities / occurrences | Legacy retained / total | Missing legacy | Added identities | Change from previous runtime |
|---|---:|---:|---:|---:|---|
| OWASP | 4,112 / 9,179 | 4,112 / 4,112 | 0 | 0 | equal identities and occurrences |
| conductor | 7 / 7 | 7 / 7 | 0 | 0 | equal identities and occurrences |
| thingsboard | 5,089 / 92,016 | 14 / 14 | 0 | 5,075 | equal identities and occurrences |
| Stirling-PDF | 30 / 77 | 14 / 17 | 3 | 16 | equal identities and occurrences |

OWASP uses the CI model and analyzer route. Its 4,112 unique locations match
the legacy set, but its 9,179 occurrences do not equal the CI constant
`EXPECTED_TRACES=4112`. The literal CI trace-count check is not reported as PASS.

An added identity is not by itself a proved false positive. Incomplete commands
and different legacy heap limits prevent an end-to-end completeness claim.
The three Stirling misses predate this implementation. They remain open:

1. `ConvertEmlToPDF`: the old location is an earlier return, IR 103, lines
   133–134. The current Simple exporter selects the last return, IR 126,
   lines 148–149. Two related output locations expose this mismatch.
2. `PipelineController.handleData`: the old location is IR 50, lines 90–91.
   The current Simple location is the last return, IR 109, line 130,
   `return null`. Source and tests prove that this exporter selects the last
   return without a return-path witness. They do not prove that the earlier
   branch's real taint dependency survives analysis.
3. `ProcessExecutor.runCommandWithOutputHandling(List, File)`: the old sink at
   IR 8 is absent in that overload. A source-defined differential control shows
   that a conditional `CM(arg0,U) -> Assign(This,A)` rule can install an
   ordinary-return reset on `This`, even when its guard is false. An unresolved
   pass-through can then lose `A` on a later safe `add`. The old caller-local
   fallback can bypass that reset. The real bytecode has this command-building
   pattern. The first dynamic loss in the project has not been proved.

The rebound source audit and four deterministic JVM controls are included in
the data. Relevant production paths are unchanged from the previous campaign.
These controls identify concrete risks; they do not close all three project
accuracy gaps. No unrelated accuracy patch was added to this optimization.

## Gate selectivity in the other projects

All gate counters are per-engine END minus START. Aggregate N2 counters also
include unchanged run-1/ZERO routes. Offered packets and keys do not count new
callee starts.

| Run | Original offers | Empty admission | Empty share | Eligible offers | Initial keys offered |
|---|---:|---:|---:|---:|---:|
| OWASP run-2 | 25,028 | 17,491 | 69.89% | 7,537 | 8,771 |
| conductor run-4, incomplete | 4,454,134 | 3,662,193 | 82.22% | 791,941 | 2,052,959 |
| thingsboard run-2, incomplete | 18,224,485 | 5,745,947 | 31.53% | 12,478,537 | 16,001,750 |
| Stirling-PDF run-5 | 223,380 | 202,087 | 90.47% | 21,293 | 23,808 |
| Stirling-PDF run-6 | 4,158,533 | 4,149,399 | 99.78% | 9,134 | 14,439 |

The cancelled thingsboard engine has one unfinished admission query and three
eligible results without an offered packet. It offers 12,478,534 packets.
Do not force completed-engine accounting on this partial execution.

Thingsboard's gate is less selective. Incomplete run-2 still accepts 12,119,319
live deltas, creates 9,030,432 input groups and 9,578,559 postings. These are
cumulative counts. The fresh heap census distinguishes live rows and queued work.

## Thingsboard run-2 profile

The memory guard starts capture after **189.235 seconds**. The 226.862-second
engine time includes the 37.566-second snapshot. The previous precapture
interval is 177.091 seconds. Neither interval is a completed-run speed comparison.

The current precapture window has 52,045 Java samples and 1.303 TB of sampled
allocation weight. GC pause union is 56.813 seconds.

| Inclusive family | Java share | Allocation share |
|---|---:|---:|
| Demand lookup | 20.18% | 16.46% |
| Current-summary replay | 12.03% | 24.77% |
| Current delivery | 10.08% | 17.10% |
| C5 summary restriction | 13.89% | 8.49% |
| Live-input accumulation | 2.85% | 1.42% |

Several run-2 owners remain material. These inclusive families overlap. The
profile alone does not justify blaming one request store. There are no Java
samples during snapshot capture; that is not evidence of zero CPU usage.

## Stirling: output admission after the gate

Completed run-6 has 38,347 Java samples and 2.366 TB of allocation weight.
Caller accumulation is only **0.008% Java / 0.002% allocation**. Point admission
is 42.47% / 45.08%; generic mask merging is 40.18% / 45.31%; cleaners are
9.83% / 10.89%; persisted replay is 8.66% / 5.92%.

A closed run-6 window, 23:33:23–23:33:53 UTC, has 2,970 Java samples and
171.154 GB of allocation weight. Post-statement admission is 42.86% Java and
43.67% allocation. `subtractSubsumed` alone is **22.80% / 26.96%**;
`mergeProtection` is 2.63% / 2.09%. Native GC is 46.88%. The measured target
is ordinary subtraction, not a presumed dominant protection operation.

Incomplete run-7 has 19,809 Java samples and 1.812 TB of allocation weight.
Point admission is 45.64% / 50.31%; generic merging is 40.64% / 50.26%; rule
evaluation is 19.14% / 30.88%; persisted replay is 7.52% / 5.20%.
The near-limit worker is in this path:

```text
endAt -> RuleWorklist.drain -> MethodEdgeStore.add -> TaintGroup.mergeAddDelta
```

Run-7 starts with 185,950 memberships, versus run-6's 888. This is a different
domain; the times are not a matched regression.

## Thingsboard run-2 heap

The fresh snapshot is from reached **run-2**, complete **run-1**, accepted
**run-1**. It has **15,196,053,768 live bytes in 452,067,347 objects**. The raw
HPROF is 24,436,846,134 bytes; it is not a live-heap-size measurement. Its SHA-256
is `2427eb2b1d7c34cccccdc85d373cca6b283dac970c8d143cf28eae5790b6f8f9`.
The memory guard reports 15,488,847,112 used bytes before live capture.

The fresh class histogram contains:

| Physical class | Live objects | Shallow bytes |
|---|---:|---:|
| AddedFactAccumulator.Entry | 9,030,427 | 216,730,248 |
| AddedFactAccumulator.Key | 9,030,427 | 216,730,248 |
| CallerRef | 4,511,244 | 144,359,808 |
| CalleeSubscriptions | 83,695 | 4,017,360 |
| AddedFactAccumulator | 83,695 | 2,678,240 |
| InitialsIn packet | 293,357 | 7,040,568 |
| InitialAp canonical key | 41,775 | 2,005,200 |
| TaintTree | 10,479,818 | 419,192,720 |
| TrieNode | 13,057,704 | 731,231,424 |

Thus the heap contains millions of retained caller-input rows, even though the
canonical initial-key domain is much smaller. A final initial key does not
identify a complete actual fact and CallerRef used to apply future summaries.
The selected gate keeps those data for eligible offers. The physical class
counts alone do not identify static rows, exact collection memberships or queued
key counts. An InitialsIn object can also be held outside a queue.

Completed retained-owner queries give these unions. **Do not add the rows**:
shared and nested owners overlap. The union includes exclusively retained
objects, not all objects reachable from each owner.

| Owner roots | Retained bytes | Root count |
|---|---:|---:|
| SubscriptionManager + CalleeSubscriptions + AddedFactAccumulator | 2,699,416,432 | combined families |
| SubscriptionManager | 2,697,368,752 | 562 |
| CalleeSubscriptions | 2,693,363,944 | 83,695 |
| AddedFactAccumulator | 1,874,324,936 | 83,695 |
| DemandStore | 2,422,238,600 | 1 |
| FrozenStaticCompletion | 1,512,257,560 | 1 |
| MethodEdgeStore | 1,618,962,616 | 67,252 |
| ScalarPremiseRows | 1,501,145,552 | 3,263,825 |
| Method forms and form caches | 1,085,785,352 | mixed classes |
| Rule provider views | 840,910,088 | mixed classes |
| DeltaWorklist | 210,596,984 | 67,252 |
| InitialFactStore | 186,913,608 | 67,252 |
| PersistentRecordStore | 138,586,408 | 1 |
| FrozenOwnerVisibility | 99,855,928 | 1 |
| CfgDeliveryCache | 67,719,816 | 67,252 |
| InitialsIn packets | 28,186,416 | 293,357 |

The exact union of DemandStore and FrozenStaticCompletion is 2,422,238,600
bytes, equal to DemandStore alone. This confirms the overlap. The part beyond
the frozen-completion retained set is 909,981,040 bytes; these are not two
independent 2.42 GB and 1.51 GB costs.

The combined subscription-root union is slightly larger than SubscriptionManager
alone; not every other live root is wholly nested there. Accumulator retention
contains all 9,030,427 Entry/Key objects, plus 4,283,015 TaintTree and 95,292
FlowTree objects. These are retained-payload class counts, not a per-row static
or mark classification.

Subscriptions, caller inputs, demand and point stores are the main measured
analyzer owners. Forms and rule views also take material space. These results
explain why the caller gate alone does not remove run-2 OOM. They do not prove
that every retained row is necessary, nor that every row is static. The detailed
row classifier did not complete, so a static-by-mark family ratio is unavailable.

The largest individual IR storage dominator retains 1,622,296,400 bytes.
The companion data includes the full class histogram and top dominators.
Container-class shallow sizes are parts of these owners; they are not extra
bytes to add to the owner table. IR storage changes remain outside this iteration.

The detailed N2 row classifier hit its 2,400-second offline reader bound while
extracting a large ArrayList through MAT address-to-ID lookup. It produced no
complete eligibility result. The completed histogram and owner results remain
valid. The HPROF hash is unchanged. The follow-up reuses the fresh indexes;
it does not repeat the classifier or run an analyzer. Offline reader latency
is not analyzer work.

The follow-up completes all seven stock retained queries and closes after
138.236 seconds. Its optional packet-key/queue decoder rejects a runtime-class
assumption: MethodKey is an alias whose runtime object is MethodEntryPoint.
Detailed packet-key multiplicities and queue occupancy are unavailable, not
zero. Physical packet counts and their 28,186,416-byte retained union remain
valid. No additional scan was started. The snapshot hash is unchanged.

No current static-family ratio or logical exact/span distribution is inferred
from the old heap. In particular, a raw TaintTree `ANY_TAINT` header does not
by itself mean a logical uniform-taint fact. A single near-OOM snapshot also
does not prove an unbounded growth rate or the heap size required to converge.

## Next iteration

The [next proposal](../design/bidirectional-summary-work-next-iteration-20261030.md)
contains code, fact traces and constructive kernels. It ranks operation removal:

1. Share joined writer input selection by complete pending query, then apply
   every destination. This targets thingsboard's 236.104-second transition.
2. Merge exactly equal current-summary images within one delivery batch before
   return processing. This targets conductor's measured return work.
3. Stop subtraction below a subtree already covered by inherited marks. This
   targets Stirling's point-store work. Use a warm cached fold in the first scope.

The models pass 47 named theorems and 99 audited declarations. Seven controls
pass on current production AP code. Query multiplicity, equal-image rate and
safe subtree-prune rate remain unmeasured. A two-to-one example is not a twofold
project speedup. Kotlin callback/ND/alias adapters and those measurements remain
implementation gates. No next-candidate runtime change is in the measured commit.

These three proposals target measured time and allocation work. None is proved
to remove the thingsboard run-2 OOM. A memory compaction proposal needs a complete
current row-family census before its eligible count or byte saving can be ranked.

## Embedded evidence and measurement limits

The [embedded data](data/bidirectional-selected-call-policy-20261030.json)
contains closed commands, source hashes, input
audits, exact finding identities and multiplicities, all iteration frontiers,
counter deltas, parsed profiles, thread samples, fresh heap results, controls
and model receipts. It also contains all 54 iteration/frontier rows across
the three recent runtimes and validates all 18 current run-counter sets.
Raw recordings, the 24 GB heap and MAT indexes stay outside
Git. Absolute paths identify original artifacts; parsed results must remain
directly available in the repository.

The [validation receipt](data/bidirectional-selected-call-policy-20261030-validation.json)
binds the embedded data hash, report hash, model receipt, passing tests and
unchanged production source. It checks artifact consistency; it is not another
project run or a proof of finding completeness.

JFR allocation is sampled allocation weight, not live heap. Inclusive stack
families overlap. Native CPU includes GC and has a different denominator from
Java samples. All parsed engine windows lie inside Java-sample envelopes; this
is not proof of continuous coverage. OWASP's normal native capture crosses
run-1 into run-2. An extra OWASP observer was rejected because the original
profiler was active; the original capture succeeds. No analyzer was restarted.

All analyzer, capture and heap-reader handles are closed. The final heap status
records the two classifier limits and the completed retained queries. Finite-run
evidence does not prove whole-project termination, no false negatives or a
stable performance distribution.

# Demand stopping, static label selection and CFG delivery: measurements

Date: 30 October 2026. Analyzer commit: `c98d12582a138d5898e94908ee6690dda73998ca`.
The four project commands are closed. No extra configuration was run.

The change fixes the OWASP stopping problem and greatly reduces Stirling's
run-5 time. It does not solve the thingsboard problem. Thingsboard reaches
**run-2**, completes and accepts **run-1**, then stops with **OOM at 16 GB**.
The previous matched command stopped with timeout in run-2.

## 1. Implementation and controls

The selected implementation does three things:

1. After a complete restricted forward run, stop when the normalized selected
   outgoing refinement demand is empty. Persist results and accept the report
   before this stop. Run-1, backward runs and cancelled runs keep their rules.
2. Select relevant static-demand labels before the existing exact predicates
   and owner checks. Keep each original row's owner family and full relation.
3. Cache first relevant CFG destinations by instruction and fact base. Use a
   finite BFS on a miss, and cache an empty result too. Store a completed
   result under its **producing statement S**. Do not store an initial or
   resumed input as if S had processed it.

The stopping rule is an intentional semantic change. The other two changes
alter selection, scheduling and storage. They retain the transfer contract.
There is no new field, mark, cleaner, alias, source/sink, static-pool or
backward-ZERO policy. Identity results now use the durable post-S output gate;
this adds a memory cost which the heap section examines.

Validation at the measured commit:

| Validation | Result |
|---|---:|
| Core tests | 2,075 passed; 0 failed, errors or skips |
| JVM tests | 452 passed; 0 failed, errors or skips |
| Selected Lean package | 67 named theorems; 127 audited public declarations |

The Lean count includes 56 new theorems and 11 dependency theorems. The models
cover finite kernels. They do not prove the whole analyzer or certify its
runtime adapters. The production tests include finite CFGs, identity cycles,
late protection changes, static exit delivery, actual JVM relevance, and
static label/owner scope. See the implementation and proof receipts in the
[embedded measurement data](data/bidirectional-demand-stop-static-labels-cfg-delivery-20261030.json).

All commands use Gradle `runProjectAnalyzer`, FULL marks, statics enabled,
aliases enabled, a 16 GB heap, and field limits `1,1,2,3,...`. OWASP uses its CI
model and a 1,000-second IFDS budget. Each real project uses a 1,080-second IFDS
budget. The 1,200-second outer budget starts at analyzer JVM launch; earlier
Gradle startup is outside this budget.

The fixed finding baseline is the saved
`f945f92c5ae554ff4f5fc7696ee5a269210478bb` report. It was **not rerun**. Its heap
limits were 8 GB, except thingsboard at 12 GB. The matched previous analyzer is
`bb74cef6cf483db167c161020a8a4cca576ca005`, with the current controls. Use that
comparison to assess this iteration's performance. The legacy comparison is
for reported locations, with its configuration limits stated.

Full-content audits before and after the campaign pass for **25 datasets and
four model files**. The post-run audit found no active analyzer JVM. Old closed
campaign captures were removed before this campaign: 17 files, 1,154,794,195
bytes. Their hashes and parsed evidence remain in the cleanup receipt.

## 2. Final status and latest iterations

“Complete” means the last complete engine. “Accepted” means the last forward
report accepted by the driver. A partial backward run does not replace it.

| Project | Status | Latest reached | Latest complete | Accepted forward | Command seconds | Peak RSS GiB |
|---|---|---|---|---|---:|---:|
| OWASP | OK; no outgoing demand | run-5 | run-5 | run-5 | 287.656 | 17.562 |
| conductor | TIMEOUT | run-6 | run-5 | run-5 | 1,132.852 | 18.431 |
| thingsboard | OOM | run-2 | run-1 | run-1 | 1,074.086 | 18.416 |
| Stirling-PDF | TIMEOUT | run-6 | run-5 | run-5 | 1,113.705 | 17.601 |

RSS includes memory outside the Java heap. Command time includes startup,
prescan, barriers, report work and captures. It is not engine time.

### 2.1 Iteration times and outgoing demand frontiers

Demand is the selected outgoing membership count. It is not the number of
all observed demand objects, stored point rows, or processed instructions.
`—` means unavailable for a partial engine, not zero.

| Project | Run | Direction / field limit | Engine seconds | Outgoing demand | Demand method keys |
|---|---|---|---:|---:|---:|
| OWASP | run-1 | forward / 1 | 64.177 | 111,374 | 6,468 |
| OWASP | run-2 | backward / 1 | 41.121 | 112,175 | 5,222 |
| OWASP | run-3 | forward / 2 | 27.837 | 85 | 22 |
| OWASP | run-4 | backward / 3 | 38.426 | 198,817 | 3,791 |
| OWASP | run-5 | forward / 4 | 27.191 | 0 | 0 |
| conductor | run-1 | forward / 1 | 12.908 | 33,154 | 6,289 |
| conductor | run-2 | backward / 1 | 29.944 | 340,173 | 9,263 |
| conductor | run-3 | forward / 2 | 18.549 | 24,131 | 555 |
| conductor | run-4 | backward / 3 | 309.370 | 62,685 | 606 |
| conductor | run-5 | forward / 4 | 139.016 | 194,046 | 336 |
| conductor | run-6 | backward / 5; partial | 542.028 | — | — |
| thingsboard | run-1 | forward / 1 | 373.717 | 1,927,771 | 20,871 |
| thingsboard | run-2 | backward / 1; OOM | 238.628 | — | — |
| Stirling-PDF | run-1 | forward / 1 | 12.456 | 26,494 | 1,803 |
| Stirling-PDF | run-2 | backward / 1 | 22.888 | 455,211 | 4,208 |
| Stirling-PDF | run-3 | forward / 2 | 4.059 | 52,186 | 3,690 |
| Stirling-PDF | run-4 | backward / 3 | 10.646 | 15,938 | 496 |
| Stirling-PDF | run-5 | forward / 4 | 72.640 | 1,676 | 166 |
| Stirling-PDF | run-6 | backward / 5; partial | 940.048 | — | — |

The thingsboard run-2 interval includes a 37.879-second heap capture. Its
pre-capture workload window is 200.698 seconds. Do not count the capture as
ordinary analysis or call its whole duration a GC pause.

### 2.2 Run-1 binding and transition

The joined static-writer binding follows the run-1 engine. It must be measured
separately. The run-1 iteration time includes this work and the report barrier.

| Project | Engine s | Joined binding s | Report barrier s | Full run-1 iteration s |
|---|---:|---:|---:|---:|
| OWASP | 64.177 | 0.103 | 2.326 | 66.618 |
| conductor | 12.908 | 0.429 | 0.356 | 13.720 |
| thingsboard | 373.717 | 228.449 | 7.645 | 609.863 |
| Stirling-PDF | 12.456 | 0.215 | 0.233 | 12.913 |

Thingsboard binding considers **222,437,787 inputs**, matches **28,024,746**,
and produces **27,923,003 bound outputs**. It admits 2,351,008 writers from
26,403,962 offers. Matching uses the current base/path candidate index. The
rejected-input breakdown is not measured. It is not valid to call all rejected
inputs wrong-mark inputs.

### 2.3 What improved, and what did not

- OWASP stops at run-5. At this barrier, outgoing demand methods are **0**,
  but observed demand objects are **31,477**. The old test continued from
  those observations. The new test does not start run-6. The matched previous
  command timed out after 1,042.744 seconds, with run-12 reached and run-11
  complete. The current accepted report has the same finding identities and
  occurrences. The current report still contains demand findings; the stop
  result alone is not proof that all reports are precise.
- OWASP run-1 falls from 100.367 to 64.177 seconds, about **1.56 times faster**.
  Its outgoing demand remains 111,374.
- Stirling run-5 falls from 612.328 to 72.640 seconds, about **8.43 times
  faster**. The incoming frontier is different: 13,901 before, 15,938 now.
  Its outgoing frontier changes from 1,304 to 1,676. Thus this is an observed
  complete-engine improvement, not a claim of equal instruction work.
- Conductor run-4 falls from 635.366 to 309.370 seconds, about **2.05 times
  faster**. Its outgoing frontier grows from 47,475 to 62,685. Run-5 rises
  from 108.790 to 139.016 seconds, with a 32% larger incoming frontier.
- Thingsboard run-1 rises from 349.927 to 373.717 seconds. Binding changes
  from 230.023 to 228.449 seconds. Run-2 stops with OOM instead of timeout.
  There is no overall thingsboard improvement in this campaign.

Conductor and Stirling now have more time left for their partial run-6. The
old partial run-6 times were 241.444 and 393.611 seconds. Current times are
542.028 and 940.048 seconds. These are **budget endpoints**, not comparable
times to finish the same work. Both still time out.

Demand counts can change with the selected scheduling. The embedded audit
shows OWASP forward maps equal at run-1, run-3 and run-5; backward run-2 differs
by -42 and run-4 by -1,984 memberships. Conductor run-4 grows by 15,210 and
run-5 by 39,193. Most run-4 growth is in recursive ParametersUtils map/list
handling. The saved diagnostics contain counts, not full AP payloads. They
cannot establish that all differences are redundant. Tests and equal final
finding reports do not replace a complete relation-equivalence proof.

## 3. Reported locations

The comparison uses strict rule/location identities. It also compares report
occurrences. It does not classify the added identities as proven false
positives or the missing identities as proven vulnerabilities.

| Project | Legacy unique | Retained | Missing | Added | Current unique |
|---|---:|---:|---:|---:|---:|
| OWASP | 4,112 | 4,112 | 0 | 0 | 4,112 |
| conductor | 7 | 7 | 0 | 0 | 7 |
| thingsboard | 14 | 14 | 0 | 5,075 | 5,089 |
| Stirling-PDF | 17 | 14 | 3 | 16 | 30 |

Against the matched previous analyzer, **all four projects have exactly the
same unique identities and occurrences**: OWASP 4,112 / 9,179; conductor
7 / 7; thingsboard 5,089 / 92,016; Stirling 30 / 77. Thus this iteration adds
no observed location loss and no new reported-location growth.

The strict comparator retains `INCOMPLETE_OR_INVALID_INPUT_COMPARISON`:
legacy heap limits differ, and one or both matched commands can be incomplete.
The full input audits pass, but they do not make a partial analysis complete.
Thingsboard attempts to export 95,058 results and exports 92,016. The SARIF
generator rejects 3,042 locations. The comparison above covers exported
locations. The embedded data preserve this discrepancy and examples; an
equal exported report does not prove that every internal result was exported.
The goal of no missing legacy locations and few added locations is **not met**:
Stirling still has three strict misses, and thingsboard still has many additions.

### 3.1 The three Stirling misses

These are unchanged from the previous analyzer. The embedded source audit
contains all three strict identities, rule data, source hashes and traces.

Two have exit-location differences in ConvertEmlToPDF and PipelineController.
The old exit report can use the last-return fallback; the current report uses
the actual return origin. Related return candidates exist at different strict
locations. The saved evidence does not prove that each candidate retains the
same baseline branch. Do not close these two misses as harmless, or relax
the comparator silently.

The remaining command-source case has a source-position reset before its
ContainsMark condition. A reset can remove the incoming ARGS mark before the
guard fails. The unresolved-call route matters: the legacy route can preserve
the caller local before binding, while the current bound `this.$/ARGS` can
cross the return reset. The old provider also installed resets. Therefore,
“the reset exists” alone does not explain the revision difference. The saved
traces do not prove which resolution route the real call selected. The audit
establishes the local mechanism and the conditional differential route; exact
call-resolution attribution remains unproved. No unselected rule fix was made.

## 4. CFG delivery workload

The cache stores base/destination metadata, not facts or premises. Statistics
are per run and are copied before actors release their caches. They are not
cumulative values to subtract across runs.

| Project / run | Cache hits | Searches | Nodes visited on misses | Destination indices | Maximum width |
|---|---:|---:|---:|---:|---:|
| OWASP / run-1 | 2,316,445 | 226,508 | 3,875,656 | 314,857 | 8 |
| conductor / run-1 | 301,497 | 180,019 | 1,875,584 | 211,826 | 33 |
| thingsboard / run-1 | 11,881,374 | 625,155 | 5,573,903 | 738,282 | 37 |
| Stirling / run-1 | 89,478 | 35,613 | 911,544 | 45,738 | 13 |
| conductor / run-4 | 7,920,278 | 14,700 | 62,185 | 16,012 | 8 |
| Stirling / run-5 | 5,226,895 | 10,772 | 319,294 | 14,204 | 84 |

Stirling run-5 now searches the CFG for only 10,772 instruction/base pairs.
This replaces the old repeated neutral traversal. A hit still delivers and
processes relevant input; it is not an operation-free fact. Distinct producers
can deliver equal input to one relevant instruction. The durable output gate
rejects repeated output after that instruction runs. No standing destination
input-history cache was added.

## 5. CPU, allocation and GC

The [profile data](data/bidirectional-demand-stop-static-labels-cfg-delivery-profiles-20261030.json)
include window timestamps, sample counts, family definitions, source/reader
hashes and coverage limits. Inclusive stack families overlap. Do not add their
percentages. Java sample shares are not wall-time shares. Allocation weights
are sampled estimates, not retained bytes or exact allocation counts.

Use actual capture timestamps to assign phases. OWASP's native normal capture
crosses from late run-1 into run-2; the pure run-1 figures below use a filtered
JFR window. Stirling run-1 lasts only 12.456 seconds, so a 30-second capture
one minute into that engine is impossible. Its observer dumps the closed
run-1 recording 5.57 seconds after engine end; the reader selects the engine
timestamps. Near-limit windows describe the then-active run, not run-1 by
default. Missing recording coverage remains explicit in the data.

### 5.1 Thingsboard: run-1 and joined binding

The run-1 engine window has 46,334 Java samples. The call pipeline has 64.90%,
subscription handling 32.58%, and post-statement storage about 17.6%. Plan
construction has 14.46% over this whole startup-inclusive window.

The dedicated normal-workload native profile has 42,001 samples. Call-stage
application has 38.18%, pending-call processing 44.32%, and collector workers
about 38%. Plan construction has only 1.01%, alias construction 0.63%, and
FormsCache payload access 2.05%. Thus an eager-plan fix is not the main
explanation for thingsboard's normal run-1 workload.

The engine's allocation-sampled weight is 1.646 TB; GC pause union is 17.743
seconds. The 228.449-second binding window has 16,612 Java samples, with 98.28%
in joined-writer binding, 40.80% in matching and 34.72% in summary application.
Its allocation weight is 600.66 GB; GC pause union is 3.803 seconds. Candidate
selection and repeated AP joins remain substantial work after CFG skipping.

### 5.2 Thingsboard: run-2

The pre-snapshot window has 68,496 Java samples:

| Family | Java sample share | Sampled allocation weight |
|---|---:|---:|
| C2 initial admission | 55.06% | 676.64 GB |
| Static owner eligibility | 55.43% | 658.67 GB |
| Detached call-graph reachability | 54.88% | 630.23 GB |
| C5 summary restriction | 15.02% | 171.39 GB |

The whole window has 1.408 TB allocation weight and 54.362 seconds of GC
pauses. Owner reachability is the clearest current avoidable algorithmic work.
Label filtering removed many irrelevant owner questions, but each fresh view
can still recompute the same graph reachability.

```text
Frozen call graph:           51,953 methods; 117,581 edges
Existing owner families:     16,414
Owner evaluations:           52,148,176
Views which allocate memo:    1,850,835
Memo byte capacity allocated: 30,379,605,690 (cumulative, not retained)

B: 760 geometries; 14,449 labels
Local writer attachments: 2,175,161
Local reader attachments:   140,668
C5 duplicate states rejected: 17,406,979
```

The old partial endpoint had 603,417,178 owner evaluations. The current count
is much lower, but the endpoints differ. It does not give a fixed-work speedup.
Only four owner views remain live in the heap snapshot. The 30.38 GB capacity
counter is allocation pressure, **not a 30 GB retained owner cache**.

### 5.3 Conductor: latest run-6 / complete run-5

A 30-second native capture entirely inside run-4 has 4,514 samples: summary
delivery 66.02%, applyMatch 61.85%, summary application 49.42%, and caller
resume 34.40%. Collector workers have about one third of all samples.
No C2/C5 frame occurs in that capture.

The continuous recording no longer contains run-1 to run-3. Those CPU windows
are **unavailable**, not zero work. Run-4 is partly covered. Run-5 and run-6
are within the retained sample envelope. Run-6 has 87,935 Java samples:
subscription handling 40.27%, native-record replay 28.03%, post-statement
storage 18.61%, C2 2.18%, and C5 10.63%. Its allocation weight is 3.866 TB and
GC pause union is 36.108 seconds. Actual after-GC heap rises from about 6.66
to 14.53 GB. Summary application/replay remains a target; a wrapper's sample
share does not show how much delivery is duplicate.

### 5.4 OWASP: latest run-5 complete

The closed run-1 engine recording has 2,672 Java samples. Plan construction
has 54.98%; alias construction has 29.94%. Allocation weight is 113.53 GB,
with 57.01 GB under plan construction. GC pause union is 2.259 seconds.
Form statistics were disabled. These samples do not measure cache rebuild
frequency or distinguish first builds from repeated builds.

### 5.5 A rejected hotspot interpretation

`transportProtection` is hot, but it wraps ordinary AP operations too. A
source-line audit distinguishes its three branches. In conductor run-4 to
run-6, there are **no observed protected-image branch samples**. The hot branch
calls the ordinary operation once with no protection mask.

In the closed early thingsboard run-1 prefix, the extra protected-image branch
has only 0.642% of Java samples and 0.847% of allocation weight. It is not a
credible main explanation for the current slowdown. A whole-protected-image
shortcut is deferred. Treating the whole wrapper as duplicate work would rank
the wrong proposal.

### 5.6 Stirling: latest run-6 / complete run-5

The closed run-6 recording has 103,030 Java samples. Here the protection
helper itself is expensive: `intersectTaintMask` has **80,076 samples,
77.72%**, and **2.468 TB of 3.906 TB** allocation weight. MethodEdgeStore.add
has 77.25%; TaintGroup.add has 77.91%. These families overlap. GC pause union
is 7.679 seconds, and after-GC heap grows from about 4.74 to 6.96 GB. C2 has
0.06%; C5 is near zero. This is not the thingsboard owner-search problem.

The source and exact parent stacks identify redundant normalization in
TaintGroup.add. It changes an ordinary root with `withRoot`, which intersects
the old protection mask. It then replaces that intermediate mask with
`withProtection`, which intersects again. For a merged root, the union of two
valid masks is already contained in the union of their ordinary roots. Both
walks are unnecessary in this proved case. Other operations which remove
members still need to trim protection.

`NodePair.equals` alone has 38.82% leaf samples. It already compares node
identities. This is not a recursive equality bug. The opportunity is to avoid
unnecessary mask traversals and their memo work, with the same protection
result. It is distinct from the deferred whole-protected-image shortcut.

## 6. Thingsboard run-2 live heap

The guard-triggered snapshot is 24,600,048,230 bytes on disk. Its SHA-256 is
`f9ada43cef71a1ede35f098033f3753c6df49ccda0a2d282bb917b5942323365`.
The HPROF file size is not the live heap size. MAT reads the complete snapshot
without discarded objects. Its live histogram contains **462,698,899 objects
and 15,209,201,048 shallow bytes**.

The OOM status comes from the analyzer memory guard. At capture it reports
15,489,713,088 bytes against a 15,461,882,265-byte threshold, about 90% of
the 16 GiB maximum. This is not proof of a JVM allocation failure at the full
heap limit, or of unbounded memory growth.

Use MAT and actual GC heap summaries for retained-memory conclusions. The
RunManager memory log uses `maxMemory - freeMemory`; it can include uncommitted
heap capacity. It is not an independent retained-heap measurement. The OOM
guard also has actual after-GC checks, so this logging issue alone does not
explain the observed OOM.

The following retained unions are separate queries. They can overlap through
ownership and shared objects; do not add them to calculate total heap.

| Owner/query | Retained bytes | Meaning |
|---|---:|---|
| All completed MethodEdgeStore point stores | 3,431,625,208 | Current method post-statement results and their exclusive payload |
| FrozenStaticCompletion | 1,408,463,216 | Frozen static guidance, attachments and indexes |
| JIRMethodEntries | 1,068,056,392 | JVM entries and their owned analysis data |
| DemandStore | 909,617,128 | Current demand and indexes |
| JIRTaintRulesProvider | 828,559,584 | Provider-owned rule data |
| All StaticOutputOrdinals indexes | 297,760,144 | Subset of frozen static storage |
| All CFG delivery caches | 54,054,040 | Current instruction/base routing metadata |

Physical dominator grouping attributes 4,522,414,680 bytes to UnitRunner roots
and 1,638,646,192 bytes to SubscriptionManager roots. These rows are another
view of ownership, not extra independent allocations. IR RAM storage retains
1,619,911,472 bytes. IR representation changes remain outside the selected
analyzer-core work.

The point-store union alone contains 7,514,636 ConclusionGroup objects,
7,610,287 TaintGroup objects, 7,925,067 TaintTree objects and 1,820,609
per-premise statement arrays. Its 15,029,272 HashMap objects use 721,405,056
shallow bytes. Its ArrayList objects use another 378,969,984 bytes. Small
per-cell containers are a material part of this owner, not just taint payload.

The new delivery cache is small relative to these owners. Its run-1 data were
released before run-2; this census is of live run-2 caches. The snapshot does
not support blaming the OOM on retained run-1 delivery frontiers.

### 6.1 The repeated static identity pattern is confirmed

The focused census checks the **whole** conclusion against its initial:
same base, single complete path, tail, field exclusion and mark image. FLOW
must have empty mark exclusion. A mixed tree which merely contains an
identity path is not classified as a literal identity. Layer and protection
still have to be preserved by any storage change.
Tail means the canonical initial image: an exact concrete leaf is EXACT even
though its TaintTree.anyTail header is ANY_TAINT.

| Point-store cell class | Occupied cells | Identity-only cells | Identity-only share |
|---|---:|---:|---:|
| Nonstatic FLOW premise | 166,480 | 47,600 | 28.59% |
| Nonstatic TAINT premise | 1,736,125 | 551,158 | 31.75% |
| Static FLOW premise | 88,065 | 87,849 | 99.75% |
| Static TAINT premise | 5,359,538 | 5,237,365 | 97.72% |
| ZERO premise | 164,428 | 0 | 0% |
| **All** | **7,514,636** | **5,923,972** | **78.83%** |

Static identity-only cells total **5,325,214: 70.86% of all occupied cells**.
Static premises account for 5,447,603 cells in total, or 72.49% of all cells.
This is a cell count, not a leaf-membership or CPU-work count. All literal
TAINT identity headers in this snapshot have no protection mask. A future
compact store must still support late protection upgrades.
For one `TbKafkaProducerTemplate.addAnalyticHeaders(List)` context, the heap
has 617 static premises and 28 identity positions: capacity 17,276. It has
17,104 static identity-only cells and 17,282 total occupied cells.

```java
// Schematic CFG example. The census counts statement indices;
// it does not prove that all 28 measured positions are calls.
void addAnalyticHeaders(List headers) {
    firstCall();   // Post-S stores I -> I for each applicable static I.
    secondCall();  // Another point container for the same I -> I.
    // More relevant call positions.
}
// One observed context: 617 static premises × 28 identity positions.
```

This confirms the static premise-by-statement product. All relevant completed
outputs still need a post-S admission record under the selected design. They
do not need a separate full container tree when the value is reconstructible
from the initial and a few state bits.

The whole per-premise statement-array payload is only 129,494,896 bytes. An
array-layout change alone cannot remove the 3.43 GB point-store owner. The
larger opportunity is to avoid full containers for identity-only cells. The
5,325,214 static cells alone have a lower-bound **809,432,528 bytes** of
ConclusionGroup, BooleanArray and two HashMap object headers, before maps'
tables, lists, taint groups, fact headers or trie roots. This is an object
accounting bound, not a measured net saving for a future representation.

### 6.2 What the new routing metadata retains

The live run-2 caches have 303,188 instruction/base entries and 341,680
destination indices. Of these frontiers, 287,202 are singletons; maximum width
is 43. The focused census finds no empty cached frontier at this snapshot.
These are retained entries, not the released run-1 counters.

There are 73,668 contextual JIRMethodForms for 51,952 physical JVM entries.
The new forward/backward relevance maps have 808,391 cached instruction
copies but only 424,197 distinct physical-method/direction/instruction keys.
This confirms some context duplication. The counted map and set object
headers are about 22.36 MB, excluding backing arrays and retained bases.
Do not attribute the whole 1.068 GB JIRMethodEntries owner to these footprints.
Sharing them is a smaller follow-up than the identity point-store change.

The live ordinal indexes have 3,047,219 FULL postings and the same number of
`fullInGroup` postings. The latter arrays and map object headers use about
34.62 MB before map entries/tables. All GROUP maps are null in this FULL
campaign. This is a smaller target than millions of full point containers.

Work queues contain 373,980 pending scalar inputs. The census finds 2,872
repeated object triples `(premise,node,facts)`. This is only a lower bound:
different but equal Facts objects are not compared. It does not support a
claim that most current retained memory is a duplicate queue backlog.

### 6.3 What this explains about the OOM

Run-2 combines a large point store, summary subscriptions, frozen static
guidance, demand, rules and JVM/IR state. The new producer gate retains a full
identity cell at each relevant statement. Static facts are relevant at calls,
so this creates the measured repeated identity product. The cache itself is
not the large retained owner. Owner-graph search adds high allocation/GC
pressure, but its per-view memo is not a large retained archive.

The snapshot explains the current retained sources and confirms the capacity
added by the new output policy. There is no matched previous heap at the same
work point. Thus it does not measure the exact net byte increase caused by
this commit, or prove that one owner alone caused the earlier OOM endpoint.
The proposed fixes must measure retained bytes and completed run-2 behavior;
they must not claim an OOM fix from CPU samples alone.

## 7. Measurement limits and remaining work

The code tests pass, all four configured measurements are closed, and current
reported locations match the previous analyzer. The broader real-project
acceptance goal remains unmet: thingsboard has OOM, conductor and Stirling
have timeout, three strict legacy Stirling identities are missing, and
thingsboard reports many added identities.

The report does not infer an infinite local loop from long runtime. It shows
large finite stores, allocation and repeated queries. Summary replay can have
an overlapping replay/delivery schedule, but its real-project duplicate rate
is not measured. A production pair-deduplication policy needs that evidence
and an annotation-aware proof before implementation.

Use the [next-iteration proposal](../design/bidirectional-demand-stop-static-labels-cfg-delivery-next-iteration-20261030.md)
for the ranked changes. These changes are proposed, not included in the
measured analyzer.

## 8. Embedded evidence

The report's counts and principal findings are in this file. Repository data
also include the detailed iteration counters, strict finding comparison,
input/test/proof receipts, profiles, source audits and heap census. Large raw
JFR/HPROF files remain outside Git. Each embedded artifact records its source
path and SHA-256 so it can be checked without depending on an untracked
`shape-probe-results` directory.

- [Campaign, comparison and validation data](data/bidirectional-demand-stop-static-labels-cfg-delivery-20261030.json)
- [CPU, allocation, GC and branch evidence](data/bidirectional-demand-stop-static-labels-cfg-delivery-profiles-20261030.json)
- [Heap owners and focused census](data/bidirectional-demand-stop-static-labels-cfg-delivery-heap-20261030.json)

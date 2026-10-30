# Identity storage, owner visibility and protection admission: measurements

Date: 30 October 2026. Analyzer commit:
`edb2e06cdb17eecafbe03415236bf56c57910239`.
All four project commands, profile readers and heap readers are closed.

The selected changes remove most static-owner search work and replace millions
of identity containers with bits. They do not solve the overall workload.
Thingsboard still stops with **OOM in run-2 at 16 GB**. Conductor regresses to
**run-4**, with run-3 complete; the previous implementation reached run-6 and
completed run-5. OWASP finishes at run-5. Stirling still times out in run-6.

All four exported reports have the same unique identities and occurrences as
the matched previous implementation. The old accuracy limits remain: three
strict Stirling misses and many added thingsboard candidates versus the legacy
baseline. This iteration does not establish the no-FN/few-FP target.

## 1. Implementation and validation

The implementation contains three changes:

1. Store a complete literal identity in point bits. Keep each producing statement,
   layer and protection state. Restore the exact current image before promotion
   to a full group. Keep packed run-1 storage and REACH unchanged.
2. Compute static owner visibility once on the frozen call graph. Use iterative
   SCC construction, an explicit quotient DAG order and immutable family bits.
   Keep outside owners, each original label family and local MethodKey scope.
3. Skip protection-mask intersection only in proved TaintGroup construction
   paths. Keep general mask trimming, transfer and protection rules unchanged.

The implementation commits are `0ad56d290`, `b1d217233` and `579e1f5ff`.
Commit `edb2e06cd` binds the checked models to the source adapters.
There is no selected analyzer semantic change. Field transfer, marks, layers,
cleaners, aliases, callbacks, C2/C5 demand handling, output ownership and the
stop rule keep the base contract. Object addresses and internal scheduling
can differ. The result tables below expose the observed frontier differences.

| Validation | Result |
|---|---:|
| Complete core tests | 2,106 passed; no failures, errors or skips |
| Complete JVM tests | 452 passed; no failures, errors or skips |
| Constructive Lean models | 58 named theorems; 124 audited public declarations |
| Benchmark/comparison/profile Python tests | 45 passed |

The models prove finite storage, visibility and mask kernels. They do not
verify Kotlin or the whole analyzer. Differential tests compare state and every
emitted annotated delta. Independent BFS tests check SCCs, owner queries, packed
word boundaries and deep graphs. The [embedded data](data/bidirectional-identity-owner-protection-20261030.json)
contain source hashes, comparisons, parsed counters and profile evidence.
Raw current captures remain outside Git.

## 2. Controls and final iterations

All four commands use Gradle `runProjectAnalyzer`, FULL marks, enabled statics
and aliases, 16 GB, and limits `1,1,2,3,...`. OWASP uses its CI model and a
1,000-second IFDS budget. Each real project uses 1,080 seconds. The outer
1,200-second limit starts at analyzer JVM launch. No baseline was rerun and no
extra project configuration was tested.

The fixed finding baseline is the saved
`f945f92c5ae554ff4f5fc7696ee5a269210478bb` report. Its heap limits differ: 8 GB,
except 12 GB for thingsboard. The matched previous implementation is
`c98d12582a138d5898e94908ee6690dda73998ca`, with the current controls.
Current full-content input audits pass before and after the campaign for
25 datasets and four models. No analyzer remained active after the audit.

Closed prior raw captures and MAT indexes were removed: 26 files,
58,382,507,070 bytes. Their reports, hashes and parsed evidence remain.
JFR, GC logs, process resources and native CPU samples were captured for the
current commands. Additional closed native windows cover conductor run-4
and Stirling run-6. Bounded streaming readers avoid expanded JFR JSON.
OWASP's normal native window crosses run-1 into run-2; it is not a pure run-1
profile. Thingsboard's normal window is in run-1. Its near-limit native window
was not reached before OOM. A separate run-1 JFR keeps early samples which
the rolling recording no longer contains. Window bounds and missing captures
are explicit in the embedded evidence.

“Complete” means a complete engine. “Accepted” is the latest forward report
accepted by the driver. An incomplete backward engine does not replace it.

| Project | Status | Reached | Complete | Accepted | Command s | Peak RSS GiB |
|---|---|---|---|---|---:|---:|
| OWASP | OK | run-5 | run-5 | run-5 | 278.577 | 17.672 |
| conductor | TIMEOUT | run-4 | run-3 | run-3 | 1122.814 | 18.021 |
| thingsboard | OOM | run-2 | run-1 | run-1 | 1080.936 | 18.469 |
| Stirling-PDF | TIMEOUT | run-6 | run-5 | run-5 | 1110.932 | 17.880 |

RSS includes memory outside the Java heap. Command time includes startup,
prescan, barriers, report export and captures. It is not engine time.

### 2.1 Iteration times and outgoing demand

| Project | Run | Direction / limit | Engine s | Outgoing demand | Method keys |
|---|---|---|---:|---:|---:|
| OWASP | run-1 | forward / 1 | 61.064 | 111,374 | 6,468 |
| OWASP | run-2 | backward / 1 | 37.506 | 112,176 | 5,222 |
| OWASP | run-3 | forward / 2 | 28.375 | 85 | 22 |
| OWASP | run-4 | backward / 3 | 38.749 | 198,829 | 3,791 |
| OWASP | run-5 | forward / 4 | 31.867 | 0 | 0 |
| conductor | run-1 | forward / 1 | 12.780 | 33,178 | 6,289 |
| conductor | run-2 | backward / 1 | 21.168 | 340,267 | 9,263 |
| conductor | run-3 | forward / 2 | 17.876 | 23,896 | 556 |
| conductor | run-4 | backward / 3; timeout | 1000.877 | — | — |
| thingsboard | run-1 | forward / 1 | 388.450 | 1,927,695 | 20,870 |
| thingsboard | run-2 | backward / 1; oom | 215.315 | — | — |
| Stirling-PDF | run-1 | forward / 1 | 12.188 | 26,494 | 1,803 |
| Stirling-PDF | run-2 | backward / 1 | 22.557 | 455,222 | 4,208 |
| Stirling-PDF | run-3 | forward / 2 | 4.247 | 52,170 | 3,690 |
| Stirling-PDF | run-4 | backward / 3 | 11.112 | 16,382 | 496 |
| Stirling-PDF | run-5 | forward / 4 | 76.705 | 1,284 | 151 |
| Stirling-PDF | run-6 | backward / 5; timeout | 935.324 | — | — |

Demand is the selected outgoing membership count, not the number of point
rows, observed demand objects or pending tasks. A dash means unavailable for
an incomplete engine. It does not mean zero.

### 2.2 Run-1 engine and transition

| Project | Run-1 engine s | Joined binding s | Report barrier s | Full iteration s |
|---|---:|---:|---:|---:|
| OWASP | 61.064 | 0.101 | 2.089 | 63.282 |
| conductor | 12.780 | 0.546 | 0.380 | 13.751 |
| thingsboard | 388.450 | 232.465 | 8.006 | 629.011 |
| Stirling-PDF | 12.188 | 0.276 | 0.310 | 12.795 |

Full iteration time also includes short handoff and scheduling work. It need
not equal the sum of the three measured subphases.

Thingsboard binding considers 222,569,600 writer/input candidates, matches
28,037,170 and creates 27,935,427 bound outputs. It processes 2,351,008 writers.
Writer work takes 223.083 seconds, 95.96% of binding. The rejected-input cause
breakdown is not measured. Do not call every rejection a wrong-mark input.

### 2.3 Performance assessment

- OWASP ends at run-5 in 278.577 command seconds, versus 287.656 before.
  The small difference in one pair of commands is not a stable speedup claim.
- Conductor run-2 falls from 29.944 to 21.168 seconds. However, run-4 does not
  complete within 1,000.877 seconds; before it completed in 309.370 seconds.
  The overall command regresses from run-6 reached/run-5 complete to
  run-4 reached/run-3 complete.
- Thingsboard run-1 rises from 373.717 to 388.450 seconds. Binding rises from
  228.449 to 232.465 seconds. Run-2 still stops with OOM. Its logged 215.315
  seconds include a 38.164-second heap capture. Its exact pre-capture window
  is 177.091 seconds, versus 200.698 before. Earlier OOM is not a speedup.
- Stirling run-5 uses 76.705 seconds, versus 72.640 before. Run-6 again uses
  the remaining budget and times out. It does not converge in this command.

These are not equal-work comparisons. For example, conductor enters run-4
with 23,896 demand memberships in 556 keys, versus 24,131 in 555 keys before.
Stirling enters run-6 with 1,284, versus 1,676 before. The differences must not
be hidden by a statement that the number of final findings is equal.

## 3. Reported locations and accuracy limits

| Project | Legacy unique | Retained | Missing | Added | Current unique / occurrences |
|---|---:|---:|---:|---:|---:|
| OWASP | 4,112 | 4,112 | 0 | 0 | 4,112 / 9,179 |
| conductor | 7 | 7 | 0 | 0 | 7 / 7 |
| thingsboard | 14 | 14 | 0 | 5,075 | 5,089 / 92,016 |
| Stirling-PDF | 17 | 14 | 3 | 16 | 30 / 77 |

Every current unique identity and occurrence matches the previous c98 report.
Legacy OWASP has 4,112 occurrences; the current and previous reports both have
9,179. Keep unique locations and occurrences separate. Added identities are
not automatically proved false positives; missing identities are not a proof
that an exploitable flow was lost.

The strict comparator keeps `INCOMPLETE_OR_INVALID_INPUT_COMPARISON`: legacy
heap limits differ and most commands are incomplete. Input audits pass, but
an audit cannot make an incomplete engine complete. Thingsboard attempts
95,058 SARIF traces and logs 3,042 invalid locations; 92,016 occurrences are
exported. Equal exported reports do not prove that rejected candidates are
correct. Export diagnostics and exact case evidence are in the embedded data.

The three Stirling gaps predate this iteration. The current source audit
binds the new report and unchanged JVM adapter code:

| Missing legacy site | Established cause | Remaining limit |
|---|---|---|
| ConvertEmlToPDF.convertEmlToPdf, IR103, lines 133–134 | Simple exit output has no return witness. The exporter selects the last return, IR126, and hashes that instruction. The old strict site is not representable by this current boundary candidate. | Survival of the original branch flow is not proved. |
| PipelineController.handleData, IR50, lines 90–91 | The same exporter path selects the last return, IR109 (`return null`). | That location is not proof of tainted null, nor proof that the original returned-byte branch survives. |
| ProcessExecutor.runCommandWithOutputHandling(List,File), IR8 | A conditional List.add source installs a receiver-mark reset. Current bound unresolved identities cross that reset before bind-back. The legacy default unresolved route uses the caller-local base and can bypass the This reset. Classfile and resolver source establish this differential route. | The real first runtime loss and incoming ARGS at the literal add are not recorded in the saved report. The local mechanism is identified; exact dynamic attribution remains unproved. |

Do not relax the comparator or close these gaps as harmless. No unselected
rule, exporter or alias fix was made.

## 4. Compact storage and owner visibility

Conductor run-2 has 3,999,166 unique compact scalar cells and 189,692 full
cells. Thus 95.47% of these cells use bits. The layer count is 3,999,176:
ten cells have both layers. There are 32,291 promotions. Bit payload is
5,835,656 bytes, excluding headers and premise maps. These are complete current
counts, not a retained-byte comparison with a previous snapshot.

The owner index is shared and immutable. It replaces per-view owner searches;
it does not change exact local ownership or attach another context's W/R rows.

| Project / transition | Families | Components | DAG edges | Word payload bytes | Build ms |
|---|---:|---:|---:|---:|---:|
| conductor run-1 → run-2 | 334 | 13,521 | 19,014 | 649,008 | 19.554 |
| thingsboard run-1 → run-2 | 16,414 | 48,000 | 92,064 | 98,688,000 | 93.901 |

Thingsboard's old pre-capture profile spent 54.88% of Java samples and
630.233 GB of sampled allocation weight in static call-graph work. The current
owner eligibility region is 1.403%; the frozen bit query is 0.060%. Remaining
call-graph samples are small ID/look-up operations. Per-view BFS is removed.
The old 30.38 GB memo counter was cumulative allocation, not retained memory.
It cannot be subtracted from the new index payload as a memory saving.

Cancelled engines can return no actors. Their logged zero frozen-store gauges
do not measure active stores; `unavailableActors=0` only describes the returned
actor list. Use complete gauges or the heap census, not those zeros.

## 5. OOM snapshot and retained memory

Thingsboard reaches run-2, with run-1 complete and accepted. The memory guard
fires at 15,483,713,744 reported heap bytes against a 15,461,882,265-byte
threshold. It captures 24,519,290,190 HPROF bytes from 11:42:22.255 to
11:43:00.419 UTC. A complete capture is not proof of a JVM allocation failure
at the full 16 GB ceiling.

The exact last pre-capture young-GC log reports 15,466,496,000 bytes after
collection. Use GC and retained-object data: the general progress logger's
`maxMemory-freeMemory` can include uncommitted capacity. Sampled allocation
weight is not live heap.

The closed snapshot SHA-256 is
`2821df85dda58a6e81de26d2666b576e9ba9450f75c5df7b31f056134ebf1299`.
MAT reports **15,194,880,608 live bytes in 450,039,953 objects**. Its complete
class histogram sums to these totals. The first parser built the indexes but
its custom queries failed registration. Its receipt remains failed. An explicit
MAT installation and registry control fixed the reader. The second reader
reopened those indexes and completed all ten queries. No second HPROF parse
or analyzer run was needed. All readers kept the original HPROF unchanged.
Default reachability filtering excluded 32,343 unreachable objects from the
indexes; no sampling or discard option was enabled.

### 5.1 Retained owners

The following table groups direct dominator-tree root children by class.
These rows are disjoint parts of the heap; they are not the complete partition.

| Root-child class | Retained bytes | Share of live heap |
|---|---:|---:|
| SubscriptionManager | 3,071,378,720 | 20.21% |
| UnitRunner | 2,915,339,720 | 19.19% |
| IR RAM relationship storage | 1,626,704,624 | 10.71% |
| FrozenStaticCompletion | 1,511,299,560 | 9.95% |
| JIRMethodEntries | 1,079,784,912 | 7.11% |
| DemandStore | 909,924,272 | 5.99% |
| RunManager | 841,128,328 | 5.54% |
| JIRTaintRulesProvider | 828,612,896 | 5.45% |

Exact retained sets rooted at all instances give 3,072,595,992 bytes for
SubscriptionManager, 3,067,474,448 for CalleeSubscriptions, and 2,061,995,216
for AddedFactAccumulator. Publication indexes retain 815,088,496 bytes;
summary stores retain 838,917,464. **These sets overlap. Do not add them.**
Their role is to identify the input directory inside the large subscription
owner, not to assign another independent 2.06 GB to the heap.

Other exact owner unions include point stores, 1,556,857,864 bytes; frozen
owner visibility, 99,855,928; initial stores, 178,188,984; CFG delivery,
62,610,672; and method worklists, 144,519,144. Channels plus EventQueue retain
113,969,440 bytes. Queues are large by event count but are not the main retained
owner. TrieInterner objects retain 31,305,536 bytes; no live interner Table
instances occur in the complete histogram. These figures do not support a
large retained interner-table explanation at this snapshot. IR storage remains
outside the selected optimization scope.

### 5.2 The input directory repeats one static route for many exact marks

The heap contains **10,818,019 AddedFactAccumulator keys and the same number
of entries**, each class using 259,632,456 shallow bytes. There are 11,013,074
GroupKeys and 32,252,029 LinkedHashMap entries. These are actual live objects,
not cumulative admission counters.

A separate source-bound query checked every input entry, not just point-store
identities. It kept the owning callee directory, full caller key, call, stage,
layers, complete initial geometry and exclusions. Only the full mark value
was removed from the potential family key. The actual input had to be the
canonical unprotected literal image of that same concrete initial.

| Restricted static input census | Count |
|---|---:|
| All stored input entries | 10,818,019 |
| Eligible exact static identities | 7,990,412 (73.86%) |
| Exact-scope families for those entries | 465,029 |
| Mean exact marks per eligible family | 17.18 |
| Families with 18 marks | 388,620 |
| Largest family | 20 marks |
| Unchanged fallback entries | 2,827,607 |
| Potential total physical rows | 3,292,636 |

This is **3.286 times fewer rows** with unchanged fallback, not a measured
3.286-fold byte or engine improvement. Exact mark membership still needs
storage. Most families contain different marks, not duplicate equal marks;
the query found no duplicate eligible mark memberships. Its conservative
physical caller/call IDs must not become a new runtime identity-equality rule.

The disjoint fallback counts are nonstatic premise 2,162,131; ZERO 201,713;
static root/class 169,600; static FLOW 166,903; other tail 101,694; and other
base 25,566. A full-mark family can remove per-mark key/entry wrappers and
geometric postings. It can also select a concrete publication's mark before
trying every member. It must retain every caller route and exact full mark.
This is the strongest measured next memory target.

### 5.3 Point cells and queued work

There are 10,621,242 unique compact point cells and 2,128,430 full cells:
12,749,672 occupied cells. The previous snapshot had 7,514,636 occupied cells.
The current point-store union is smaller than its previous 3,431,625,208 bytes
despite more explored cells. The snapshots have different work endpoints;
this is not an isolated fixed-work saving estimate.

Compact cells include 9,748,319 static TAINT and 210,999 static FLOW cells.
They have 3,963,167 NORMAL and 6,658,219 DEMAND memberships, with 144 cells in
both layers. One compact DEMAND membership is protected. The full representation
has 341,530 literal-identity-only cells; permanent promotion can leave such a
cell full. The snapshot cannot recover each original promotion cause.

There are 1,156,366 live LinkIn objects and 40,521 potential lanes by exact
callee, layer, complete header and physical mask: 28.54 times input-count
potential. There are 9,445 additional occurrences with the same callee, link
layer, typed header, physical root ID and mask ID. This is not a global
duplicate-object count. Filtering those repeats cannot realize the lane
potential. Packing different
literal coordinates needs a separate emitter and scheduling proof; semantic
AP coverage can lose a refinable child below ANY. This is an operation-count
study, not the main retained-memory fix. Global live LinkIn counts are not
decoded channel occupancy.

The same snapshot gives negative evidence for simple return batching:
61,727 delivery publication occurrences have only 38 eligible repeated-lane
surplus, about 0.062% of raw input. Actor pending lists have 1,412 surplus out
of 81,919, about 1.72%. This does not support a twofold thingsboard improvement
from within-delivery coalescing. Historical conductor batches are not measured
by this thingsboard snapshot.

## 6. Remaining measured work

### 6.1 Conductor run-4: repeated delivery

Current run-4 has 17,509 Java samples and 2.830 TB of sampled allocation weight.
Summary delivery accounts for 71.29% of Java samples and 87.39% of allocation
weight. Native near-limit sampling has 53.19% collector-worker samples. Java
shares omit native GC; inclusive scopes overlap.

| Run-4 work | Previous complete engine | Current partial engine |
|---|---:|---:|
| Accepted subscription deltas | 1,565,622 | 2,439,370 |
| Actual input arrivals | 3,056,912 | 4,856,738 |
| Created subscription groups | 197,505 | 195,704 |
| Created index postings | 3,361,210 | 3,391,063 |
| New method initials | 30,221 | 28,965 |

The command processes more updates with fewer initials and a similar group
count. This supports reducing repeated delivery and return continuation work.
It does not prove every extra update is redundant or identify the first cause
of the larger update volume. Flat outer event counts are not proof of an
infinite loop: profiles show work inside long delivery tasks.

Compact identities also skip old `internIfRequired` calls. Those tiny-tree
calls decremented an interning cadence counter. A finite source model proves
that the next moderate root can now stay raw where it was interned before.
This can change sharing. It is not a proved cause of the whole regression:
old admission also returned raw deltas, and the interned stored root is not
automatically every later composition input. Keep this as a separate measured
investigation target; do not silently change cache policy in this iteration.

### 6.2 Thingsboard run-2: demand and subscription work

The pre-capture window has 49,593 Java samples, 1.189 TB sampled allocation
weight and 51.328 seconds of GC pause interval union. C2 initial admission is
17.44% of Java samples; C5 summary restriction is 18.47%; summary subscription
is 21.63%. Aliases are 0.76% and cleaners 1.50%. These inclusive regions overlap.

Before its guard, the current engine performs 37,704,647 successful C5
compositions and reaches 2,683,688 fresh states. The previous snapshot endpoint
has 18,348,725 compositions and 1,381,519 states. The current engine also has
36,188,215 duplicate admissions. That counter includes duplicate seeds; it
is not an exact count of wasted composition calls. One must distinguish
repeated endpoint results from repeated identical operand pairs.

The current engine reaches substantially more demand work before OOM. This
is consistent with more throughput after owner search is removed. It does not
isolate the cause of every extra operation. The heap locates large retained
state in the caller input directories, method points and frozen static demand.

### 6.3 Stirling run-6: generic input merge dominates

Run-6 has 100,992 Java samples and 3.688 TB of sampled allocation weight.
The selected TaintGroup construction path falls from 77.91% of Java samples
to 10.22%. Mask intersection remains at 75.47%, now mainly below the generic
caller-input accumulator:

```text
SubscriptionManager.subscribe
  CalleeSubscriptions.admit
    AddedFactAccumulator.add
      ApManager.mergeAddDelta
        ApManager.taintTree
          intersectTaintMask
```

AddedFactAccumulator.add rises from 9.51% to 75.00%; generic merge is 78.66%.
These inclusive shares overlap. The focused leaf check finds this complete
generic path in 8,060 of 8,351 exact mask-leaf samples. Thus the remaining
hotspot is measured, not inferred from a wrapper's name. Mask work accounts
for 56.41% of sampled allocation weight. Native mid-run samples have 45.50%
collector-worker samples; Java-only shares do not include that cost.

Generic input merge constructs and normalizes a stored tree even when both
ordinary and protection deltas are empty; the accumulator then discards it.
That construction is avoidable. For fresh input, exact coordinate differences
can also avoid full merged-mask intersections. A proposal-only Lean kernel
proves the mask equations; the Kotlin adapter is still a future proof gate.

Current run-6 receives 2,334,947 inputs but admits 1,029,061 fresh subscriptions,
including controls. Since each normal link follows subscription admission,
at least 1,305,886 received offers were nonfresh. Equivalent lower bounds are
2,417,368 in conductor run-4 and 174,138 in thingsboard run-2. These are offers,
not individual AP coordinates. Linking only fresh restricted input needs
literal-union distributivity of limit plus initial emission; it must not
discard protected-only updates or refinable children.

### 6.4 Run-1 work remains

Thingsboard run-1 call-pipeline code accounts for 65.22% of Java samples;
summary subscription is 32.41%, post-result admission 16.99% and aliases
11.58%. These are overlapping scopes. A callback wrapper such as `withForm`
or `limitFacts` includes its callback; its whole share is not form rebuilding
or pure limiter cost. IR storage remains outside this optimization scope.

The 232.465-second joined writer phase is also large. Grouping writer
conclusions with one complete premise can share matching. Its multiplicity
must be measured before a project speedup is claimed. Even deleting all
223.083 writer seconds cannot halve the 620.915 engine-plus-binding seconds.

## 7. Run-1 protected and ordinary summary shapes

These are stored output memberships, not concrete locations denoted by ANY.
They do not by themselves classify geometric FLOW coverage.

| Project / run-1 raw store | Concrete memberships | Protected memberships | Raw FLOW annotations | Selected FLOW annotations |
|---|---:|---:|---:|---:|
| OWASP | 110,251 | 443 | 11,229 | 1,123 |
| conductor | 16,854 | 22 | 36,496 | 16,409 |
| thingsboard | 1,800,217 | 1,737,136 | 216,520 | 138,567 |
| Stirling-PDF | 24,486 | 2,273 | 4,870 | 2,055 |

OWASP's full run-1 census matches c98 exactly. Thingsboard has many protected
memberships, which cannot be called removable merely because the ordinary
shape overlaps FLOW. Raw and selected stores have different compaction scopes;
subtracting their counts is not a subsumption-reason census.

The heap's full point headers often fail literal-identity recognition because
the base differs (1,614,841 nonstatic TAINT header occurrences) or the tail
differs (178,460 static TAINT occurrences). Those are compact point-storage
fallbacks, **not reasons that FLOW cannot subsume a concrete summary**. This
campaign does not have a fresh geometric FLOW-coverage reason census. Keep
that limit explicit rather than reusing a previous runtime's shape counts.

## 8. Next iteration and remaining limits

The [ranked next proposal](../design/bidirectional-input-admission-delivery-next-iteration-20261030.md)
has four targets: exact full-mark static subscription families, no-op/exact-mask
generic admission, fresh restricted links, and shared writer matching. The
first target has an exhaustive current heap census. The writer target has
measured total work but not shared-premise multiplicity. No proposed change
is implemented by this report.

The current optimization and campaign are complete. The report does not claim
that thingsboard now fits 16 GB, that conductor's regression has a proved
single cause, or that the old strict accuracy gaps are fixed. One command per
configuration, different partial frontiers and sampled profiles limit causal
comparisons. The embedded data include all four comparison results, per-run
profiles, complete heap phase outputs, source bindings and validation receipts.

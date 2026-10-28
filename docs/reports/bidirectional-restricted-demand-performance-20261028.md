# Restricted demand and static closure: performance report

Date: 28 October 2026. Runtime: `53991b7483b062b0287152130cbbbfc87623093b`.
Status: campaign and analysis complete. The baseline acceptance gate fails.

The change is implemented and committed. All four configured analyses stopped
with OOM or timeout. The strict baseline gate is not passed: Stirling-PDF has
three missing sink identities, and Thingsboard retains many run-1 candidates.
The main new costs are writer binding at the run-1 boundary and virtual demand
lookup in run-2. Later iterations have a separate memory and fact-growth problem.

## Fixed inputs and scope

The baseline is `f945f92c5ae554ff4f5fc7696ee5a269210478bb`. Its saved reports
were reused. The baseline was not run again. The current source was committed
before measurement. All four runs used the Gradle `:runProjectAnalyzer` task,
FULL marks, enabled statics and default aliases. No other project configuration
was run. Before and after the campaign, all 25 content datasets and four project
models matched the saved baseline inputs.

The [data file](data/bidirectional-restricted-demand-performance-20261028.json)
contains commands, JVM flags, model hashes, report hashes, all iteration times,
input checks, counters and source-log references. Raw captures are under
`/drive-testcomp/opentaint-go-rules/restricted-demand-20261028`. Prior raw captures
were removed before this campaign; the preserved cleanup receipt records
257 files and 148,519,354,024 logical bytes. Current captures remain available.

| Project | Heap | IFDS limit s | Outer limit s |
|---|---:|---:|---:|
| OWASP | 8g | 1000 | 1200 |
| conductor | 8g | 1080 | 1200 |
| thingsboard | 12g | 1080 | 1200 |
| Stirling-PDF | 8g | 1080 | 1200 |

## Outcome and iteration reached

A completed backward run does not update the forward report. The last column
below is the latest accepted forward report. All baseline runs completed.

| Project | Current outcome | Latest reached | Latest completed | Accepted forward |
|---|---|---|---|---|
| OWASP | TIMEOUT | run-12 | run-11 | run-11 |
| conductor | OOM | run-4 | run-3 | run-3 |
| thingsboard | TIMEOUT | run-2 | run-1 | run-1 |
| Stirling-PDF | OOM | run-5 | run-4 | run-3 |

| Project | Baseline wall s | Current wall s | Current peak RSS GiB |
|---|---:|---:|---:|
| OWASP | 123.217 | 1047.756 | 9.583 |
| conductor | 92.193 | 505.105 | 9.704 |
| thingsboard | 220.437 | 1168.191 | 14.013 |
| Stirling-PDF | 55.108 | 230.484 | 9.849 |

Wall time includes the Gradle command, scan, report export and diagnostics.
RSS includes JVM memory outside the configured heap. These are different terminal
outcomes, not equal completed work. The data shows degradation against the saved
legacy baseline; it does not isolate the causal effect of this patch from all
earlier new-core changes.

## Run-1 and transition

| Project | Run-1 engine s | Joined completion s | Report barrier s | 60 s engine target |
|---|---:|---:|---:|---|
| OWASP | 91.130 | 0.106 | 2.177 | Miss |
| conductor | 15.399 | 0.495 | 0.325 | Pass |
| thingsboard | 378.990 | 251.337 | 7.987 | Miss |
| Stirling-PDF | 25.207 | 0.155 | 0.181 | Pass |

Engine time excludes joined static completion. The report barrier follows both.
Thingsboard spends 251.337 s in completion; 244.196 s is actual writer binding,
1.761 s is candidate pruning, and 0.450 s is graph freeze. Thus, a fast graph
freeze does not imply a cheap transition.

| Project | Observed candidates | Lost candidates | Processed writer keys | Input candidates | Matched inputs | Bound outputs |
|---|---:|---:|---:|---:|---:|---:|
| OWASP | 1,994 | 664 | 2,458 | 1,344 | 1,344 | 1,864 |
| conductor | 12,657 | 4,369 | 10,306 | 169,876 | 60,899 | 63,073 |
| thingsboard | 2,706,439 | 467,941 | 2,351,008 | 222,531,429 | 28,035,102 | 27,933,247 |
| Stirling-PDF | 18,044 | 76 | 15,123 | 15,145 | 14,942 | 15,141 |

Thingsboard matches only 12.60% of 222.5 million candidate inputs. It offers
26,395,364 writer keys and admits 2,351,008. These are operation and admission
counts, not distinct facts. The current phase replays observed and surviving
writers as well as lost writers. The proposal must prove which raw publications
have already completed their caller work before it can omit that replay.

## Every measured iteration

Times below are seconds. A dash means the phase did not run. OOM engine time
includes the automatic capture: 15.718 s in conductor run-4 and 16.863 s in
Stirling run-5. Pre-capture hotspot windows exclude these intervals;
whole-engine windows retain them.

| Project | Run | Direction | Field limit | Status | Engine s | Joined s | Barrier s |
|---|---|---|---:|---|---:|---:|---:|
| OWASP | run-1 | FORWARD | 1 | COMPLETE | 91.130 | 0.106 | 2.177 |
| OWASP | run-2 | BACKWARD | 1 | COMPLETE | 38.059 | — | 0.154 |
| OWASP | run-3 | FORWARD | 2 | COMPLETE | 31.209 | — | 1.460 |
| OWASP | run-4 | BACKWARD | 3 | COMPLETE | 40.361 | — | 0.147 |
| OWASP | run-5 | FORWARD | 4 | COMPLETE | 33.497 | — | 1.442 |
| OWASP | run-6 | BACKWARD | 5 | COMPLETE | 50.139 | — | 0.176 |
| OWASP | run-7 | FORWARD | 6 | COMPLETE | 41.843 | — | 1.649 |
| OWASP | run-8 | BACKWARD | 7 | COMPLETE | 104.092 | — | 0.578 |
| OWASP | run-9 | FORWARD | 8 | COMPLETE | 41.825 | — | 1.400 |
| OWASP | run-10 | BACKWARD | 9 | COMPLETE | 335.734 | — | 2.120 |
| OWASP | run-11 | FORWARD | 10 | COMPLETE | 35.085 | — | 1.396 |
| OWASP | run-12 | BACKWARD | 11 | TIMEOUT | 110.662 | — | — |
| conductor | run-1 | FORWARD | 1 | COMPLETE | 15.399 | 0.495 | 0.325 |
| conductor | run-2 | BACKWARD | 1 | COMPLETE | 85.791 | — | 1.518 |
| conductor | run-3 | FORWARD | 2 | COMPLETE | 47.814 | — | 0.617 |
| conductor | run-4 | BACKWARD | 3 | OOM | 284.680 | — | — |
| thingsboard | run-1 | FORWARD | 1 | COMPLETE | 378.990 | 251.337 | 7.987 |
| thingsboard | run-2 | BACKWARD | 1 | TIMEOUT | 298.941 | — | — |
| Stirling-PDF | run-1 | FORWARD | 1 | COMPLETE | 25.207 | 0.155 | 0.181 |
| Stirling-PDF | run-2 | BACKWARD | 1 | COMPLETE | 40.064 | — | 1.057 |
| Stirling-PDF | run-3 | FORWARD | 2 | COMPLETE | 7.730 | — | 0.232 |
| Stirling-PDF | run-4 | BACKWARD | 3 | COMPLETE | 22.065 | — | 0.657 |
| Stirling-PDF | run-5 | FORWARD | 4 | OOM | 87.234 | — | — |

## Finding locations

| Project | Baseline unique | Current unique | Retained | Missing | Added | Current occurrences |
|---|---:|---:|---:|---:|---:|---:|
| OWASP | 4,112 | 4,112 | 4,112 | 0 | 0 | 9,179 |
| conductor | 7 | 10 | 7 | 0 | 3 | 10 |
| thingsboard | 14 | 5,089 | 14 | 0 | 5,075 | 92,016 |
| Stirling-PDF | 17 | 39 | 14 | 3 | 25 | 95 |

The comparison keeps full rule, method signature, sink fingerprint and location.
It does not merge overloads or treat repeated occurrences as new sink identities.
All four outputs are partial. No added candidate is automatically a false positive.
The [comparison index](data/bidirectional-restricted-demand-findings-20261028.json)
records the exact status and iteration labels for each result.

OWASP retains every baseline identity. Its 5,067 extra occurrences are repeats,
not extra unique sinks. Conductor retains every baseline identity and adds two
GraalJS evaluation sites in `ScriptEvaluator` and a reflection invocation in
`AnnotatedWorkflowSystemTask`. The JS sites consume the same cached script
source; the reflection target comes from startup worker-task scanning. These
are additional candidates, not proved new vulnerabilities or proved false positives.

Thingsboard has only its run-1 report. Of its 5,075 added identities, 5,060 use
`java.security.xss#sink#1`. They account for 91,981 occurrences. The remaining
15 identities are path traversal (6), SQL injection (3), SSRF (2), reflection
(2), script evaluation (1) and object mapping (1). The
[breakdown](data/bidirectional-restricted-demand-thingsboard-added-20261028.json)
includes representative locations for each rule.

Some XSS candidates occur at DAO method exits. This alone does not prove a
controller-annotation failure: the automaton converter creates an `anyFunction()`
method-end sink, and the Spring provider delegates that sink for noncontrollers.
The [rule evidence](data/bidirectional-restricted-demand-thingsboard-exit-rules-20261028.json)
contains two resolved conditions that test the generated result-state mark.
The first over-approximate mark derivation is not traced here. The number of
unrefined candidates fails the intended small-extra-result target.

### Stirling-PDF: three strict differences

| Baseline sink | Baseline location | Current observation | Explanation |
|---|---|---|---|
| `ProcessExecutor.runCommandWithOutputHandling(List, File)` | IR 8, `new ProcessBuilder(command)`, line 183 | No same-method replacement | Existing D23 source-output reset can delete the accumulated command-list mark |
| `ConvertEmlToPDF.convertEmlToPdf(...)` | Return IR 103, lines 133–134 | Return IR 126, lines 148–149 | Simple exit export selects a different, constant-error return |
| `PipelineController.handleData(...)` | Return IR 50, lines 90–91 | Return IR 109, line 130 | Simple exit export selects catch-branch `return null` |

The two return rows remain missing in the strict comparison. A result in the
same method at another return is not proof that the baseline taint path survived.
The simple bidi export has no trace that selects the actual return.
`TraceMessageBuilder.tryResolveExitLocation` therefore selects the last return.
The baseline traces select the earlier returns. Exact old traces, current
locations and source hashes are in the
[missing-location evidence](data/bidirectional-restricted-demand-stirling-missing-20261028.json).

The command trace contains this sequence:

```java
command.add(request.getUrlInput());  // assigns the generated receiver ARGS mark
command.add("--pdf-forms");
command.add(tempOutputFile.toString());
executor.runCommandWithOutputHandling(command);
```

The current rewriter installs an unconditional reset for the receiver output
when a source condition is not statically false. A later constant append can
remove `ARGS` without a matching replacement; the reverse reset can cut the
requirement before the earlier URL append. This is an identified local loss
mechanism on the baseline trace. The campaign has no per-edge ledger that proves
it is the exclusive first loss in every context.

This reset is selected D23 behavior in
[interpreter.md](../../spec/interpreter.md) and
[implementation-background.md](../../spec/implementation-background.md).
It predates this optimization. Weakening it is a new semantic choice, not a
cache or representation fix. The return exporter is a separate correctness
issue. Both require explicit follow-up; neither was silently changed to pass
the baseline comparison.

## CPU, allocation and operation counts

Thirty bounded JFR windows passed with a freshly compiled reader and three
reader controls. Closed recordings, reader classes, commands, time windows and
outputs have hash bindings. The
[CPU data](data/bidirectional-restricted-demand-cpu-20261028.json) preserves all
window results. Java execution samples and native CPU samples have different
denominators. Inclusive shares overlap. Sampled allocation weight is not retained
heap size or an exact allocation total.

| Workload | Java samples | Main observation |
|---|---:|---|
| Thingsboard run-1 engine | 59,920 | Call flow 33.70%; summary application 20.21%; synchronous initial admission 9.52% |
| Thingsboard joined completion | 17,930 | Writer binding 98.83%; `satisfying` 39.62%; summary application 33.66% |
| Thingsboard run-2 | 20,135 | `DemandStore.near` 64.34%; `covering` 14.77%; virtual lookup total 78.82% |
| Conductor run-2 | 27,406 | Virtual lookup 74.55%; static call-graph reachability 65.56% |
| OWASP run-10 | 8,672 | Protection-mask intersection 31.45%; the run still completed |
| Stirling run-5, last 30 s before capture | 1,285 | GC pause union 26.869 s of 30 s |

Thingsboard's joined phase has only 3.740 s of GC pauses in 251.337 s.
Its main cost is the number of binding and matching operations. Its run-2
allocation sample attributes 69.54% of weight to `near` and 85.44% to virtual
lookup. Optimizing one list or mark-table helper would leave this workload.
C2 asks for entry patterns but currently constructs full paired closure rows.

Thingsboard run-1 offers 17,948,441 initial candidates and admits 809,960 new
initials. It attempts 7,103,774 concrete request answers, creates 3,954,631 fresh
request memberships, and makes 8,058,545 request climbs. These counters prove
repeated admission work. They do not split new initials into FLOW/ZERO/concrete,
or prove how much concrete prefix propagation a new algorithm could omit.

The native normal window was requested 60 s after run-1 start for 30 s; the
near-limit window was requested 60 s before the IFDS limit. Short run-1 engines
and early OOM stops do not provide both native windows. Continuous JFR supplies
the completed/reached phase windows. Heap-capture intervals are kept separate.

### Later backward growth on OWASP

| Backward run | Field limit | Engine s | Explicit demand pairs | Edge deltas in zero-only methods |
|---|---:|---:|---:|---:|
| run-2 | 1 | 38.059 | 112,743 | 1,084,000 approximately |
| run-4 | 3 | 40.361 | 203,976 | 1,775,000 approximately |
| run-6 | 5 | 50.139 | 330,933 | 2,713,000 approximately |
| run-8 | 7 | 104.092 | 772,667 | 5,906,000 approximately |
| run-10 | 9 | 335.734 | 2,544,211 | 18,724,000 approximately |

From run-6 to run-10, new initials remain 12,213 and caller admissions are roughly
stable. Work inside methods grows sharply. "Zero-only methods" means methods
without a nonzero initial; their edge counts can include marked seed facts.
It does not mean that all these edges are ZERO-to-ZERO. Run-10 completed, so its
delay is not evidence of an infinite loop. Stable finding counts alone would
not justify stopping before a larger field limit.

## OOM memory layout

Only conductor and Stirling report memory-manager OOM in this campaign.
Their paired automatic captures contain the active run-4 and run-5 heaps,
respectively. OWASP and Thingsboard stop on time, so they have no OOM heap.
The analyzer heap remains 8 GiB in both OOM cases. The diagnostic readers use
separate 16/24 GiB limits; these are not new analyzer configurations.

| Heap | Live bytes | Reachable objects | HPROF file bytes | Latest reached / completed / accepted forward |
|---|---:|---:|---:|---|
| conductor | 7,649,110,680 | 217,636,610 | 11,380,099,520 | run-4 / run-3 / run-3 |
| Stirling-PDF | 7,618,536,744 | 225,357,902 | 11,647,763,216 | run-5 / run-4 / run-3 |

The serialized HPROF size is not live heap size. Full class histograms and
class-grouped dominator-root partitions agree on both live-byte totals.
No heap-discard option was used. The two tables below partition physical
dominator roots; their listed rows can be added. Unlisted roots account for
the remaining bytes.

| Conductor root family | Retained bytes | Share of live heap |
|---|---:|---:|
| IR RAM storage | 2,254,830,664 | 29.48% |
| `UnitRunner` | 1,769,314,680 | 23.13% |
| Root `byte[]` family, owner not assigned | 1,041,841,952 | 13.62% |
| `SubscriptionManager` | 683,013,800 | 8.93% |
| `RunMethodAnalyzer` | 269,945,592 | 3.53% |
| `PersistentRecordStore` | 213,984,848 | 2.80% |

| Stirling root family | Retained bytes | Share of live heap |
|---|---:|---:|
| `UnitRunner` | 3,818,202,120 | 50.12% |
| IR RAM storage | 979,572,912 | 12.86% |
| `RunManager` | 482,422,936 | 6.33% |
| `SubscriptionManager` | 403,379,024 | 5.29% |
| `PersistentRecordStore` | 276,169,040 | 3.63% |
| `JIRMethodEntries` | 218,249,048 | 2.86% |

Separate retained owner unions can overlap and must not be added to those
partitions. In conductor, IR owners retain 3,533,964,400 bytes, active method
edges/initials/work queues retain 1,555,338,808, and N2 caller/publication owners
retain 848,519,120. Native records plus incoming demand retain 348,226,576.
Thus, the OOM is not only a record-store problem. IR is measured here but
remains outside this core optimization scope.

The new run-1 state does not explain conductor's run-4 heap. There are no live
`KilledStaticWriteStore`, `FrozenStaticWrites`, `FrozenStaticCompletion` or
query `Walk` instances. The cleared raw key directory retains only 21,520
bytes. Empty private-B stores and their directory retain about 9.09 MB.
N1 stores have zero rows and marks. A general claim that run-1 state leaked
into every later OOM is not supported.

### Facts, statics and ND premises

These are physical wrapper counts. They are not logical paths, scalar mark
memberships or propagation-operation counts. A shared wrapper can appear at
many points; one wrapper can contain many paths or marks.

| Physical class or shape | conductor, run-4 | Stirling-PDF, run-5 |
|---|---:|---:|
| `TrieNode` | 12,544,939 | 14,512,940 |
| `FlowTree` | 357,646 | 94,428 |
| `TaintTree` | 3,563,593 | 9,804,358 |
| Static `FlowTree` | 193,054 (53.98%) | 78,773 (83.42%) |
| Static `TaintTree` | 1,329,911 (37.32%) | 9,716,512 (99.10%) |
| `TaintTree` with protection data | 6 | 2,734 |

Protection is rare in these physical wrappers. It is not the main measured
population. Conductor has 17,465 method actors, 198,756 stored initial
memberships, 181,593 scalar premise arrays and 764,932 current caller groups.
Its incoming demand has 6,901 method owners and 268,995 physical
`DemandPattern` objects; 268,994 are explicit and one is implicit ZERO.
Its 178,425 physical `Record`
objects are indexed chunks, not one record per concrete fact.

Stirling has 7,447,662 `ConclusionGroup`, 7,442,402 `TaintGroup`, 15,094,393
`HashMap` and 17,113,188 `ArrayList` objects. The map/list shallow sizes alone
are about 724.5 MB and 410.7 MB, before their backing arrays. This is a large
active program-point representation, not proof of a large ND product:

```text
all physical premise sets:             17
current atomic program-point rows:      6,558,256
current ND program-point rows:          30
current distinct active ND keys:        13, all arity 2
ZERO atomic point rows:                 7,793
nonzero atomic point rows:              6,550,463
```

The globally shared 1,553 `InitialAp` objects do not bound method-local
replication. `GetInfoOnPDF.getPdfInfo(PDFFile)` alone has 49,983 occupied point
rows, of which 49,518 have nonzero atomic originals. Many generated Spring
dispatcher methods each have about 35,000 such rows. The current census does
not prove that every conclusion group is a singleton. Similar group and
wrapper totals cannot establish that property.

There is a concrete source pattern worth checking before container tuning.
`SpringWebProject.ndMethodDispatch` saves **every** component-registry static
to a local, calls the all-static cleanup, then restores every saved static.
It emits this block in each per-controller dispatcher too. This creates real
repeated static instructions and local copies. The present heap classifier
does not count field names, so it does not yet attribute the large named-field
population to this registry. A bulk transfer would need to preserve cleaners,
rules, aliases and immediate write effects; the block cannot simply be dropped.

### What the Stirling static headers contain

The fresh geometry classifier inspects the first two accessor levels and the
cached bounded depth. It does not enumerate all paths. It classifies every
physical static TAINT header:

| Shape | Headers | Share of static TAINT headers |
|---|---:|---:|
| Named static fields only | 9,611,483 | 98.92% |
| EXACT class markers only | 105,029 | 1.08% |
| Mixed fields/markers or invalid broad root/class forms | 0 | 0% |

Of the 9,716,512 static headers, 5,088,941 have an ANY node and 4,627,571 do
not. ANY presence does not give a scalar tail histogram. Synthetic global
markers are a small part of this heap. They cannot explain the named-field
population. Nor does this snapshot prove which transfer first created it,
or that these fields can be made globally flow-insensitive in later runs.

The [conductor heap data](data/bidirectional-restricted-demand-conductor-heap-20261028.json)
and [Stirling heap data](data/bidirectional-restricted-demand-stirling-heap-20261028.json)
contain counts, roots, current store fields and source-bound reader receipts.
The [Stirling shape data](data/bidirectional-restricted-demand-stirling-shapes-20261028.json)
also contains the largest point owners and decoded class-marker examples.
An old reader schema was not reused. The first 16 GiB Stirling owner pass
was stopped after reader GC thrashing; a separate bounded 24 GiB reader
completed the current-schema census. Its result does not change the analyzer
heap or justify another analyzer configuration.

## Interpretation and next iteration

The evidence identifies several different costs:

1. Thingsboard run-1 still repeats initial-admission, call and request work.
   Its operation counters do not yet prove how much prefix propagation can be
   omitted. It misses the 60 s engine target.
2. Thingsboard's transition repeats a large writer/input join. This is CPU
   work, with little GC pause time. Avoid certified completed raw bindings.
3. Run-2 on Thingsboard and conductor repeatedly expands virtual demand
   closure. C2 needs only entries; C5 needs full pairs. Separate those views.
4. Later active point state causes memory pressure. Stirling's problem is
   largely named-field TAINT wrappers and their containers. Conductor has a
   broader mix of method state, subscriptions and IR owners.
5. OWASP's later backward demand grows at higher field limits. A completed
   run-10 disproves an infinite run at that point, but does not resolve the growth.

The [ranked next proposal](../design/bidirectional-restricted-demand-next-20261028.md)
gives current/new examples, the storage pipeline, risks, measurements and
39 constructive local proof audits. It makes no measured speedup claim and
does not change the runtime. It keeps IR storage outside the selected scope.

The implementation is committed, but acceptance fails: all projects stop
early, Thingsboard has too many unrefined candidates, and three strict
Stirling sink identities are missing. The local suite also retains eight
known exact-precision cleaner failures; expected finding IDs remain in those
tests. See the [local validation snapshot](bidirectional-restricted-demand-followup-validation-20261028.md)
for the complete test results and their limits. The D23 reset policy and exit
location export require explicit correctness follow-up. They were not changed
as unselected performance fixes.

The [artifact index](data/bidirectional-restricted-demand-artifacts-20261028.json)
binds this report, the proposal, embedded evidence and proof receipts to their
SHA-256 hashes. The runtime and rule source remain unchanged after the measured
implementation commit.

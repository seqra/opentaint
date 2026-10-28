# Demand storage and predefined summaries: project results

Date: 28 October 2026. Analyzer: `2273c824510ed9366ccd2aa65935f8d3561c38d1`.
Saved baseline: `f945f92c5ae554ff4f5fc7696ee5a269210478bb`.

The implementation is committed. The four fixed project tests are complete.
All four current analyses stop before convergence. Conductor stops on OOM;
the other three stop on timeout. The intended no-missing-results target is
not met: the accepted Stirling report misses three exact baseline locations.
Thingsboard also has far more added candidates than the intended small set.

The main costs differ by phase. Thingsboard spends 239.536 s on joined static
writer binding after its run-1 engine. Demand queries dominate its run-2.
Conductor's run-4 OOM contains active method trees and subscriptions, with no
run-2 static completion left. Stirling's run-5 contains a large replication
of named static facts across methods and points. Two marks account for almost
all its concrete initial memberships. Large mark cardinality does not explain
that snapshot.

## 1. Source, inputs and measurement scope

The selected [implementation proposal](../design/bidirectional-demand-storage-predefined-summaries-implementation-20261028.md)
has two parts: distinct-entry demand admission with correlated summary
restriction, and complete predefined summaries for generated Spring cleanup.
See the [local validation record](bidirectional-demand-storage-predefined-validation-20261028.md)
for tests, proofs, removals and the selected boundary-rule change.

The project campaign uses the committed runtime and rules. Later work changes
only report files and external measurement readers. The content hashes of the
44 changed Kotlin source and test files match the validation receipt and the
commit. This set contains 23 production files and 21 test files.

The command uses `runProjectAnalyzer` through `benchmark_bidi_projects.py`.
It does not use the CLI. Static propagation and alias analysis are enabled;
run-1 mark mode is FULL. The unrelated Go server build is excluded because
the installed protoc cannot rebuild it. The existing server artifact is not
used by these JVM projects. No analyzer heap or timeout is changed.

| Project | Heap | Analyzer timeout, s | Outer timeout, s |
|---|---:|---:|---:|
| OWASP | 8g | 1,000 | 1,200 |
| conductor | 8g | 1,080 | 1,200 |
| thingsboard | 12g | 1,080 | 1,200 |
| Stirling-PDF | 8g | 1,080 | 1,200 |

The saved baseline is reused, with no new baseline run. Prelaunch and final
input audits pass: 25 content datasets and four project models. All four
comparison input-difference lists are empty. The baseline uses the legacy
engine, so a bidi run number does not apply to it. These are single runs;
they do not isolate the time effect of this commit from all earlier bidi
changes or from profiling overhead.

Previous campaign captures were removed before this campaign: 67 raw capture,
index and profile files, with 53,667,747,443 logical bytes. Compact earlier
evidence and unrelated user files were kept. Current captures remain available.

Artifact root, called `ROOT` below:

```text
/drive-testcomp/opentaint-go-rules/demand-storage-predefined-20261028
```

The [embedded measurement data](data/bidirectional-demand-storage-predefined-performance-20261028.json)
contains phase rows, query counters, exact initial and point counts, CPU
families, baseline summaries and artifact hashes. The
[missing-location evidence](data/bidirectional-demand-storage-predefined-missing-20261028.json)
contains the complete saved baseline traces and fresh same-method results.
Raw heaps and full profiles stay outside Git.

## 2. Outcomes and comparison with the saved baseline

Reached means that the engine started that run. Complete means that its
engine finished. Accepted means that the report accepted a forward frontier.
An accepted report can still contain DEMAND candidates.

| Project | Current outcome | Latest reached | Latest complete | Accepted forward | Current wall, s | Saved baseline wall, s |
|---|---|---|---|---|---:|---:|
| OWASP | TIMEOUT | run-12 | run-11 | run-11 | 1,040.751 | 123.217 |
| conductor | OOM | run-4 | run-3 | run-3 | 466.007 | 92.193 |
| thingsboard | TIMEOUT | run-2 | run-1 | run-1 | 1,171.230 | 220.437 |
| Stirling-PDF | TIMEOUT | run-6 | run-5 | run-5 | 1,107.876 | 55.108 |

All saved baseline runs finished successfully. Current total completion and
wall time are worse on each project. This comparison does not establish that
the two selected optimizations caused the difference: the baseline is a
different engine, and there is no new matched pre-commit bidi campaign.

| Project | Baseline full engine, s | Current prescan, s | Current run-1 engine, s | Joined binding, s | First barrier, s | Peak process RSS, GiB |
|---|---:|---:|---:|---:|---:|---:|
| OWASP | 35.513 | 33.795 | 94.144 | 0.091 | 2.386 | 9.494 |
| conductor | 23.048 | 24.375 | 14.387 | 0.363 | 0.310 | 9.787 |
| thingsboard | 26.779 | 147.407 | 354.334 | 239.536 | 7.330 | 13.893 |
| Stirling-PDF | 4.869 | 14.141 | 13.319 | 0.155 | 0.229 | 9.550 |

Baseline full engine time comes from the second `Analysis done in` log row;
the first row is prescan. It is not the same amount of analysis as one bidi
iteration. RSS includes nonheap process memory and can exceed `-Xmx`.

`engineTime` excludes joined binding. The run-1 start-to-end interval includes
both phases. Thus thingsboard needs about 594 s before its first barrier,
including 354.334 s of engine work and 239.536 s of binding. The 60 s run-1
engine target is met on conductor and Stirling, but not OWASP or thingsboard.

## 3. Iteration times and demand frontiers

Times below are engine seconds. `D` is the outgoing demand membership count
at the completed frontier. It is not a count of scalar taint facts. `—` means
that no completed frontier exists.

| Run | OWASP: seconds / D | conductor: seconds / D | thingsboard: seconds / D | Stirling-PDF: seconds / D |
|---|---:|---:|---:|---:|
| run-1 | 94.144 / 111,374 | 14.387 / 33,089 | 354.334 / 1,928,079 | 13.319 / 26,469 |
| run-2 | 36.433 / 112,741 | 56.167 / 641,505 | 328.264 TIMEOUT / — | 28.187 / 492,667 |
| run-3 | 32.298 / 392 | 42.982 / 261,363 | — | 6.760 / 72,648 |
| run-4 | 40.904 / 204,035 | 282.283 OOM / — | — | 18.079 / 224,886 |
| run-5 | 31.092 / 162 | — | — | 796.302 / 197,579 |
| run-6 | 51.229 / 330,891 | — | — | 198.846 TIMEOUT / — |
| run-7 | 31.839 / 162 | — | — | — |
| run-8 | 90.398 / 772,739 | — | — | — |
| run-9 | 35.473 / 162 | — | — | — |
| run-10 | 316.428 / 2,543,689 | — | — | — |
| run-11 | 35.377 / 162 | — | — | — |
| run-12 | 155.504 TIMEOUT / — | — | — | — |

Run-1 and run-2 use field limit 1. Later runs increase the limit, as specified.
The Conductor run-4 time includes a 15.796 s automatic heap capture. Stirling
run-5 includes a 15.489 s manual capture. These pauses are part of observed
times; they must not be called analyzer transfer work.

Stirling run-5 finished. Its long duration is not evidence of an infinite
loop. Near the capture it processes roughly 85–90 scheduler events per second
with one in-flight event. Thingsboard run-2 ends with 3,139,672 processed
events and 707,460 in-flight events. These observations show large work and
state; they do not prove nontermination.

## 4. Exact vulnerability locations

The strict identity includes the rule, full method overload and instruction
location. Another return in the same method does not replace a missing one.
Each current count is from the accepted forward report in section 2.

| Project | Baseline unique | Current unique | Kept | Missing | Added |
|---|---:|---:|---:|---:|---:|
| OWASP | 4,112 | 4,112 | 4,112 | 0 | 0 |
| conductor | 7 | 10 | 7 | 0 | 3 |
| thingsboard | 14 | 5,089 | 14 | 0 | 5,075 |
| Stirling-PDF | 17 | 31 | 14 | 3 | 17 |

OWASP exports 9,179 occurrences: 5,067 repeat an existing strict identity.
This is distinct from added unique findings. All four current analyses stop
on resource limits. Preservation of these baseline locations is not a proof
of complete-analysis equivalence. Final campaign diagnostics show zero
CONFIRMED results; the exported rows are DEMAND candidates. Matching locations
is a location-preservation check, not a proof of equal taint paths or no false
negatives. Added candidates lack detailed code flows; do not classify them
as proved false positives or new vulnerabilities.

### 4.1 Three missing Stirling locations, accepted run-5

| Rule / method | Saved location | Current evidence |
|---|---|---|
| OS command injection / `ProcessExecutor.runCommandWithOutputHandling(List, File)` | IR 8, `ProcessBuilder(command)`, line 183 | No same-rule result in this full overload |
| XSS / `ConvertEmlToPDF.convertEmlToPdf(EmlToPdfRequest)` | IR 103, return, lines 133–134 | Different return: IR 126, lines 148–149, literal `File processing error` |
| XSS / `PipelineController.handleData(HandleDataRequest)` | IR 50, return, lines 90–91 | Different return: IR 109, line 130, `return null` |

The command trace passes through an accumulated receiver mark:

```java
command.add(request.getUrlInput()); // UNTRUSTED argument gives receiver ARGS
command.add("--pdf-forms");
command.add(tempOutputFile.toString());
executor.runCommandWithOutputHandling(command);
```

The current D23 call rewrite installs a returned-target reset when a source
condition is not statically false. A later constant append can fail the
source branch, but its ordinary result still crosses that exact receiver
reset. It can remove the accumulated `command.$ / ARGS` without a replacement.
The reversed reset can also stop its demand. All involved methods occur in
completed runs 1–5. This identifies a concrete local loss mechanism on the
baseline path. There is no current per-edge first-loss ledger, so the evidence
does not prove that D23 is the sole first loss in this campaign.

The two return differences have a separate export mechanism. Synthetic exit
results use Simple output. Without a detailed return witness,
`TraceMessageBuilder.tryResolveExitLocation` selects the last return. The
baseline EML return contains a request filename; the displayed fresh return
contains a constant error. The baseline Pipeline return contains processed
request bytes; the displayed fresh return is the catch-branch null. This
explains the displayed location selection. It does not prove survival of
the earlier taint path. Both strict losses remain in the table.

These mechanisms predate this commit. The call `rewriterSteps` body is equal
to the previous runtime body. None of these controllers has a predefined
model. The selected cleanup boundary-rule exclusion does not explain them.
A D23 correction needs a separate semantic decision and validation.

### 4.2 Added candidates

Conductor, accepted run-3: two GraalJS candidates occur in
`ScriptEvaluator.lambda$eval$0` at line 302 and `lambda$eval$1` at line 339.
The third is reflection at `AnnotatedWorkflowSystemTask.execute`, line 91.
They are actual eval/invoke locations, with no detailed new path witness.

Thingsboard, accepted run-1: 5,060 of 5,075 added identities are XSS method-end
candidates. The other 15 are six path traversal, three SQL injection, two
SSRF, two reflection, one script engine and one object mapper. 4,440 added
identities display a return. Examples are ordinary
`ActorSystemContext.getNotificationCenter` and `getStatsActor` getters.

The automaton converter creates `anyFunction()` method-end sinks.
`SpringRuleProvider.sinkRulesForMethodExit` delegates noncontroller rules;
only its controller branch performs annotation-aware object unfolding.
Fresh diagnostics show generated-state `CM(Result, state)` checks on protobuf
getters and builders. Export rejects 3,042 XSS locations. It attempts 95,058
candidates and exports 92,016 occurrences. This explains the broad sink family
and the large unrefined output. It does not establish every first mark
derivation. Run-2 times out, so no later forward report refines the candidates.

Stirling, accepted run-5: 16 added identities are XSS returns. They include
the changed returns above. One added path candidate is
`AdminLicenseController.uploadLicenseFile`, `Files.createDirectories`, line
337. A changed return does not compensate for a missing baseline return.

## 5. Thingsboard run-1 handoff

Latest reached: run-2; latest complete and accepted forward: run-1.

| Measure | Value | Unit |
|---|---:|---|
| Observed candidates | 2,702,544 | Candidate memberships |
| Lost candidates | 467,941 | Candidate memberships selected for preservation |
| Writer offers | 26,395,161 | Offer calls |
| Admitted / processed writers | 2,351,008 | Exact owner/write-key memberships |
| Candidate inputs | 222,365,480 | Candidate visits |
| Matched inputs | 28,015,232 | Successful match operations |
| Bound outputs | 27,913,713 | Output callbacks |
| Final W attachments | 2,175,161 | Frozen writer memberships |
| Final R attachments | 141,006 | Frozen reader memberships |
| B labels / geometries / owner memberships | 14,449 / 760 / 294,535 | Separate index counts |

The phase takes 239.536 s: writer work 233.184 s, candidate pruning 2.139 s,
and freeze 1.175 s. Other phase overhead accounts for the balance. Joined
binding appears in 98.49% of its Java samples. Matching appears in 39.91%,
summary application in 33.50%, and trie work in 31.65%. These inclusive shares
overlap.

`JoinedStaticWriterBinding` processes one scalar output key at a time. For
each key it borrows candidate inputs and matches the same original again.
`matches` depends on the original and actual input, not the static output.
Thus several outputs with one complete owner/original can repeat input
selection and matching. The current candidate index already uses prefixes
and extensions; this is not an unindexed full scan.

Only 12.60% of candidate visits match. This is not itself proof that the
other visits are redundant. Sharing exact owner/original matching across a
batch of outputs is a concrete way to avoid repeats. The current counters
do not give the batch widths, so they do not prove a fixed speedup.
Do not subtract output callbacks from frozen rows to claim an exact duplicate
count: those units differ.

## 6. Demand query work

`C2` returns initial facts from an actual input. `C5` restricts a provided
summary with correlated entry/exit demand. Static transitive completion is
enabled only for incoming run-2. All later rows below are local-only.

| Run / project | Local entries / pairs | C2 direct | C2 graph states | C5 restrictions | C5 graph states |
|---|---:|---:|---:|---:|---:|
| run-2 / thingsboard | 665,838 / 1,928,079 | 2,809,524 | 1,675,872 | 4,789,881 | 4,603,109 |
| run-2 / conductor | 27,384 / 33,089 | 1,999,445 | 90,625 | 2,346,699 | 1,596,655 |
| run-4 / conductor | 159,920 / 261,363 | 6,517,662 | 0 | 4,576,760 | 0 |
| run-5 / Stirling | 221,274 / 224,886 | 1,993,361 | 0 | 1,053,375 | 0 |

These are work counters, not retained object counts. `c2Joins` excludes the
root point probes inside `hasMarkedOutput`; it is not all geometry tests.

Thingsboard run-2 spends 75.45% of Java samples in demand work: C5 48.96% and
C2 26.49%. Its near-limit native profile assigns 62.01% of total CPU sample
weight to C5 and 6.48% to C2. C5 is the first query target for this project.

The C5 prefix search keeps its right endpoint geometry. Once mapped, it also
keeps that endpoint's output mark. It currently extends states even when that
fixed endpoint cannot admit the current original member. Those subtrees
cannot pass the first test in `Reference.restrict`. Pruning them is the next
query proposal. Keep FLOW states that a marked prefix can still refine.

Conductor run-4 has 3,007,186 initial candidate attempts but only 199,295 new
initial memberships: 2,807,891 attempts, or 93.37%, repeat existing initials.
The initial store deduplicates them. These are redundant admission attempts,
not duplicate stored initials. Candidate generation must still preserve call
subscriptions, actual input storage and new geometry. This count alone does
not justify a base/mark-only admission shortcut.

## 7. CPU and GC evidence

All 64 phase JFR windows and five native windows pass the fresh reader and
capture provenance checks. JFR stacks are not truncated. The early native
window is absent where run-1 finished before the one-minute trigger; continuous
JFR still covers those engines. Late native windows record their actual run.
No missing native window is represented as a zero-cost result.

| Window | Java samples | Window, s | GC pause union, s | GC collection union, s | Principal inclusive Java shares |
|---|---:|---:|---:|---:|---|
| thingsboard run-1 engine | 55,340 | 354.218 | 23.332 | 247.784 | Calls 63.54%; IR API/storage 17.15%; trie 16.16%; Spring 13.87%; aliases 10.26% |
| thingsboard joined binding | 17,076 | 239.536 | 1.751 | 166.169 | Writer binding 98.49%; matching 39.91%; application 33.50% |
| thingsboard run-2 | 42,568 | 328.264 | 14.981 | 242.199 | Demand 75.45%; C5 48.96%; C2 26.49% |
| conductor run-2 | 16,489 | 56.167 | 8.758 | 49.228 | Demand 60.62%; graph 54.70%; C5 36.18% |
| conductor run-4 late 30 s before capture | 422 | 30.000 | 6.686 | 24.139 | Calls 83.65%; trie 19.67%; demand 3.79% |
| Stirling run-5 | 58,692 | 796.302 | 9.589 | 601.054 | Calls 25.71%; IR API/storage 25.62%; demand 0.90% |
| Stirling run-6 | 33,226 | 198.846 | 8.649 | 171.359 | Calls 83.18%; protection 45.65%; trie 25.93% |
| OWASP run-10 | 9,052 | 316.428 | 11.240 | 200.343 | Calls 45.48%; protection 29.61%; trie 23.87% |

Inclusive families overlap and must not be added. Sample shares are not wall
time shares. Sampled allocation weight is not retained memory. The raw reader
label `IR-storage` includes IR API visitors as well as storage.

Stirling run-5's pre-capture 30 s window has 1,965 Java samples. Leaf samples
include `CallExprVisitor.defaultVisitJIRInst` 13.13% and
`JIRLanguageManager.getCallExpr` 10.53%. `runStatement` is 54.76% inclusive,
`FormsCache.withForm` 53.13%, and `emitUnchanged` 36.54%. `withForm` includes
its callback; this is not evidence of 53% form rebuilding or cache thrashing.
The unchanged path already avoids `MethodEdgeStore.add`, but still schedules
each successor and redoes instruction classification.

Short stop-the-world pauses do not make GC irrelevant. Concurrent collection
is active for 601.054 s of Stirling run-5. At the later run-6 native capture,
GC has 58.01% of CPU sample weight. Thingsboard's late run-2 GC share is
29.79%; OWASP's late run-12 share is 76.06%. These denominators differ from
the Java-only table. Reduce avoidable state and work before inferring a
single expensive operation or changing cache policy.

## 8. Heap layout and fact shapes

Conductor has the automatic MemoryManager OOM capture. Stirling has one
manual diagnostic capture near the guard, with the fixed analyzer limits.
`GC.heap_dump -all` does not request full GC and includes unreachable objects.
The MAT analysis removes unreachable objects. Serialized HPROF bytes are not
live heap bytes. The manual pause is included in the time table.

| Capture | Capture reached / complete / accepted | Final reached / complete / accepted | Reachable objects | Reachable bytes |
|---|---|---|---:|---:|
| conductor, automatic | run-4 / run-3 / run-3 | run-4 / run-3 / run-3 | 216,998,193 | 7,645,928,344 |
| Stirling, manual | run-5 / run-4 / run-3 | run-6 / run-5 / run-5 | 219,086,040 | 7,395,248,192 |

Conductor removes 32,096 unreachable objects / 1,516,320 shallow bytes.
Stirling removes 2,021,104 / 60,116,448. OWASP and thingsboard stop on timeout;
they have no OOM heap in this campaign. Do not infer their live layout from
the other two heaps.

### 8.1 Physical dominator partition

Each row is a union of disjoint physical dominator-root subtrees with the
same root class. Full partition rows and class histograms sum to the same
live byte total. The selected rows below are additive within each column.

| Root class | conductor retained bytes | Stirling retained bytes |
|---|---:|---:|
| `UnitRunner` | 1,551,747,840 | 2,728,740,408 |
| RAM IR storage | 2,245,106,248 | 977,820,640 |
| `SubscriptionManager` | 683,655,896 | 480,432,104 |
| `RunMethodAnalyzer` | 466,090,568 | See full partition in data |
| `RunManager` | 166,398,176 | 507,355,064 |
| `RunConfig` | 205,749,584 | 231,172,680 |
| `PersistentRecordStore` | 188,541,792 | 253,221,424 |
| `SoftReference` | See full partition in data | 683,466,480 |

A separate selected-owner retained-union view can overlap. It must not be
added to this partition or summed across families:

| Owner family | conductor bytes | Stirling bytes |
|---|---:|---:|
| Active method work | 1,528,939,512 | 2,308,977,520 |
| N2 subscriptions | 849,362,744 | 987,566,112 |
| Incoming demand | 205,718,624 | 230,907,408 |
| Native records | 188,541,792 | 253,221,424 |
| IR owners | 3,408,043,992 | 1,363,474,072 |

Incoming demand is only 2.69% and 3.12% of these live heaps. Neither heap
retains `FrozenStaticCompletion`. Thus retained run-2 closure is not the cause
of this run-4 OOM or this run-5 near-limit state. IR storage remains outside
the selected analyzer-core optimization scope.

### 8.2 Initial memberships, point groups and physical headers

The new initial reader first passes a fresh synthetic MAT control: two stores,
five initial memberships, four unique keys and six separate REACH bits. It
then reads the two existing indexed heaps. No analyzer rerun is used.

| Measure | conductor, run-4 | Stirling, run-5 |
|---|---:|---:|
| Active initial stores | 17,464 | 7,257 |
| Initial memberships across methods | 199,295 | 452,182 |
| Unique keys across active initial stores | 11,613 | 515 |
| STATIC initial memberships | 146,211 | 444,441 |
| Concrete initial memberships | 180,434 | 444,647 |
| Concrete geometries ignoring mark, counted per store | 71,791 | 326,384 |
| Non-REACH premise+point groups | 1,314,702 | 4,022,715 atomic + 30 ND |
| Per-method atomic keys used by point maps | 182,133 | 445,082 |
| Separate REACH layer+point bits | 66,560 | 7,263 |
| Physical TAINT headers / STATIC part | 3,490,178 / 1,264,482 | 7,205,523 / 7,114,109 |
| Physical FLOW headers / STATIC part | 305,504 / 144,134 | 37,043 / 19,396 |

An initial membership is one key retained by one method's initial store.
A point group is one premise at one instruction, with packed conclusions.
A physical header can contain many field paths or marks. None of these is
the scalar propagation count. REACH uses separate bitsets and can overlap
the node/original scope of other groups; do not add the bit count as scalar
facts.

In conductor, only five atom IDs account for all 180,434 concrete memberships.
The two largest initial owners show field-shape growth: `ParametersUtils.replace`
has 3,448 initials / 3,433 geometries without marks; `replaceVariables` has
2,222 / 2,215. The top point owners are `replaceVariables` with 103,001 rows,
`verifyAndUpload` with 82,140, and `terminateWorkflow` with 51,881.

In Stirling, atom 89 has 326,167 memberships and atom 77 has 118,283. Together
they form 99.956% of concrete memberships. STATIC is 99.922% of concrete
initials and 98.73% of physical TAINT headers. Most static headers are named
fields: 7,009,170, versus 104,939 EXACT class markers. Conductor also has a
named-field majority: 1,053,229 named-only static TAINT headers, 203,246
class-only, and 8,007 mixed. No invalid broad concrete root/class shape is
found. Class markers alone are not the main pattern.

A fresh controlled key lookup identifies atom 77 as the path-traversal Spring
source `UNTRUSTED` mark, and atom 89 as the XSS source `UNTRUSTED` mark. They
belong to two different top-level rule groups. GROUP mode would keep that
dominant distinction; it would not merge those two values into one group.

Stirling `getPdfInfo` has 121 atomic point-map keys and 50,625 occupied rows;
`runPipelineAgainstFiles` has 271 keys and 30,634 rows. The snapshot shows a
small canonical initial set repeated across many method/point slots. The
geometry-without-mark factors are 2.51 for conductor and 1.36 for Stirling.
These ratios describe shape; they are not proof that the rows are redundant.

Retained ND point state is small in these captures: zero current ND rows in
conductor, 30 in Stirling. This census does not measure all prior ND work.
Conductor has only 857 `MarkSet` and 490 `TaintLeaves` objects,
against 12,494,105 trie nodes. The evidence does not support a large canonical
mark-leaf history as the OOM cause.

### 8.3 What the heap establishes

Conductor's core memory problem is active point-tree state and cumulative
subscriptions, in addition to material IR owners. It is not incoming static
completion or a high number of marks. Most physical TAINT headers there are
nonstatic, so a statics-only fix cannot be assumed to remove the OOM.

Stirling shows a stronger static replication pattern. It also has observed
instruction classification and unchanged scheduling work in run-5. This
supports testing a conservative route through static-identity CFG regions.
It does not yet prove how many visits are eligible. The current unchanged
route already skips persistent point-store writes, so such a change must
not claim to remove all the counted point rows.

## 9. Evidence integrity and limits

The heap readers run after the campaign, one at a time, on existing captures.
Their larger tool heaps do not change the analyzer configuration. Each custom
query has fresh control results and source/JAR/runtime bindings.

MAT truncates report suffixes. The first Stirling overview wrapper looked for
the wrong archive name after MAT exited successfully. A later query reused
that truncated name. The original overview ZIP is unavailable; its extracted
CSV/HTML files remain and are hash-bound. The completed demand archive was
copied and preserved. Later ND, geometry and owner stages use distinct safe
suffixes. The active-initial wrapper has a reconciled successful output path.
No analyzer or successful query was rerun to hide these wrapper errors.
The overview also logs a nonfatal XML parameter-order warning; all queries
execute, and histogram/partition totals agree. Receipts retain the warnings,
failed wrapper expectations and reconciled artifact paths.

Primary external evidence:

| Evidence | Path below ROOT |
|---|---|
| Fixed command and terminal state | `campaign-handle.json`, `campaign-terminal.json` |
| Baseline bindings and capture cleanup | `preparation/saved-baseline-bindings.json`, `previous-capture-cleanup.json` in the same directory |
| Final content audit | `input-audit-post/summary.json` |
| All iteration times, barriers and counters | `phase-evidence.json` |
| Full fresh finding review and identities | `findings/fresh-review.md`, `fresh-review-summary.json`, `fresh-added-identity-tables.json` |
| Full CPU windows and capture audit | `cpu-profile-metrics.json`, `cpu-profile-provenance-audit.json` |
| Automatic conductor heap analysis | `heap-analysis/conductor/` |
| Manual Stirling heap analysis | `heap-analysis/Stirling-PDF/manual-*` |
| Controlled initial reader | `analysis-tools/active-initials/validation-receipt.json` |

## 10. Next decision

The [ranked next proposal](../design/bidirectional-demand-storage-predefined-next-20261028.md)
targets repeated writer matching, impossible C5 prefix subtrees, certified
static-identity CFG stretches, and irrelevant restricted FULL cleanup blocks.
These remove work rather than change fact representation. They are proposals;
none is in the measured runtime.

The current campaign does not pass the no-FN or small-extra-result goals.
Keep the three strict Stirling losses and the thingsboard candidate expansion
as correctness and precision gates. Keep performance claims separate from
those gates and from the unresolved first-loss evidence.

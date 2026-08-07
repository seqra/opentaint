# Fingerprint stability report

**Subject:** the fingerprint `vulnerabilitySourceSinkHash/v1` changes between two runs of the same code.
**Test project:** Stirling-PDF v2.14.2. **Analyzer:** 2026.08.01.a8995a6. **Rules:** v0.3.0.
**Style:** this document uses ASD-STE100 Simplified Technical English.

---

## Status: corrected in analyzer 908e924b3

**Do not use sections 1 to 7 as a statement about the analyzer of today.** They
describe the analyzer of 2026.08.01. The commit `908e924b3` ("Small fixes",
PR #336) corrects the cause. Read this section first, then read the rest as the
record of the defect.

What the commit changes: the event order in the IFDS scheduler. An analyzer that
holds unprocessed zero-to-zero edges now goes first. This order comes from the
content, not from the time at which a thread puts an event into the queue.

Measurement after the change, on the reproduction project
(`projects/local/taint-nondeterminism` in the regression harness), with 10 runs
and 5 different thread counts:

| Measurement | Before | After |
|---|---|---|
| `vulnerabilitySourceSinkHash/v1` set | changes between runs | the same in all 10 runs |
| Complete SARIF results, all fields | change between runs | the same in all runs |
| Delayed-analyzer set in each round | changes between runs | the same in all runs |

The same commit also adds the key `vulnerabilitySinkHash/v1`, and `06c8d25e9`
puts the rule id into it. The key is now "rule and sink only" — Change 1 of
section 8, as written. The CLI accepts it as `--fingerprint-key sink`.

Change 1 of section 8 is fully done. The sink hash is also the default key of
the CLI. The measurement of section 8 gives the reason: the sink hash is unique
for each finding (36 of 36), because the analyzer makes one finding for each rule
and each sink. The coarser key thus loses no finding. It only stops a finding
from changing its identity.

A coarser key hides less than it looks. If the source moves, the finding stays
the same finding, and the CLI writes `Updated, source changed`. If only the path
moves, the CLI writes `Updated, path changed`. Use `--fingerprint-key
source-sink` when a new source must be a new finding.

Change 2 (make the flow selection stable) is **not** done. The commit removes the
effect on the report. It does not sort the graph.

---

## 1. Read this first

Five facts. Read only this section if you have no time.

1. The analyzer gives a fingerprint to each finding. The CLI compares reports with the fingerprint.
2. The fingerprint is **not stable**. It changes between two runs of the same code.
3. In nine runs of one project, only **28 of 36** fingerprints stayed the same.
4. The cause is the list of flows. The analyzer puts each flow into the fingerprint. The list of flows changes in each run.
5. A fingerprint that contains only the rule and the sink is stable. **All 36 stayed the same in all nine runs.**

**The one-line cause:** the fingerprint contains data that the analyzer selects, not data that the code contains.

---

## 2. Why this is a problem

Four effects. Each effect is a test result, not an opinion.

| Effect | Test result |
|---|---|
| A build with no code change fails the gate | 4 new findings, exit code 2 |
| The report shows fixes that did not happen | 4 findings became "Fixed" |
| A triage decision goes away | 1 of 2 decisions did not move to the next run |
| The state `updated` has little value | only 8 of 36 trace fingerprints are stable |

---

## 3. Words in this document

Each word has one meaning. This document always uses the same word for the same thing.

| Word | Meaning |
|---|---|
| finding | a security problem that the analyzer reports |
| sink | the statement where the problem occurs |
| source | the statement where the untrusted data starts |
| flow | one path from a source to a sink |
| fingerprint | a value that identifies a finding across reports |
| baseline | an older report. The CLI compares a new report with the baseline |
| graph | the internal data structure with the nodes and the edges of the flows |
| run | one start of the analyzer |
| CLI | the `opentaint` command-line program |
| SARIF | the report file format |

---

## 4. The measurements

**Summary: the findings are stable. The flows are not stable.**

Nine runs. The same worktree. No code change between the runs.

| Quantity | Result |
|---|---|
| Sinks that the analysis phase finds | 46 in each run |
| Findings in the report | 36 in each run |
| Rule and sink of each finding | the same in each run |
| Fingerprint `vulnerabilitySourceSinkHash/v1` | 28 of 36 stable |
| Fingerprint `vulnerabilityWithTraceHash/v1` | 8 of 36 stable |
| A fingerprint of the rule and the sink only | **36 of 36 stable** |

### Example of the change

One sink. Three runs. Three different lists of sources.

```
LocalStorageProvider.java:62
  run 1: FormFillController:265, FormFillController:332, SigningSessionController:97
  run 2: ServerCertificateController:52,                 SigningSessionController:97
  run 3: DatabaseController:43, ServerCertificateController:52, SigningSessionController:97
```

The three lists are not the same. Only one source is in all three lists.

---

## 5. The cause: five steps

Read the steps in order. Step 1 is the origin. Step 5 is the effect that you see.

### Step 1 — The graph is different in each run

The analyzer builds a graph of the flows in the phase "Trace resolution".
This graph is **not the same in each run**.

Measurement, two runs, 29 sinks with more than one flow:

| Part of the graph | Number of sinks with a difference |
|---|---|
| Set of nodes | 8 of 29 |
| Count of nodes | 2 of 29 |
| Set of edges | 3 of 29 |
| Set of start nodes | 6 of 29 |

Example: `DeletingRandomAccessFile#close()` has 2421 nodes in run A and 2406 nodes in run B.
The same sink has 3860 edges in run A and 3845 edges in run B.

**Code:** `TraceResolver.kt`, `ParallelProcessingContext.kt`.
The analyzer runs this phase in parallel. The analyzer also stops the work in time slices of 100 ms
(`TraceResolver.kt:161-162`).

### Step 2 — The graph gives a number to each method

The analyzer gives a number to each node and to each method. The analyzer gives the numbers in the
order that it finds the nodes. A different graph gives different numbers.

**Code:** `Source2SinkTraceGraph.getOrCreateNodeIdx`, `Source2SinkMethodTraceGraph.getOrCreateMethodIdx`.

### Step 3 — The selection reads the methods in number order

The analyzer keeps the methods in an `IntOpenHashSet`. This set reads the numbers in the order of the
numbers. Different numbers give a different order.

Measurement: for **8 of 29** sinks, the set of methods was the same, but the order was different.
The set had the same 66 methods in both runs.

### Step 4 — The first flow in the order wins

The analyzer does not report all flows. The analyzer keeps a flow only if the flow shows a method that
no other kept flow shows. Therefore the first flow in the order wins. A different order gives a
different list of flows.

**Code:** `MethodTraceSearch.kt:193-284`.

```kotlin
if (addsNewNode(trace)) {                 // keep the flow only if it shows a new method
    val res = collect(trace)
    if (res != null) { result.add(res); markCovered(trace) }
}
```

Measurement: the list of flows was different for the same **8 of 29** sinks.

### Step 5 — The fingerprint contains the flows

The analyzer puts the source of each flow into the fingerprint. A different list of flows gives a
different fingerprint.

**Code:** `SarifGenerator.kt:118-136`.

```kotlin
digest.update(ruleId.toByteArray())
digest.addLocationFingerprint(vulnerabilityLocation)          // the sink
traces?.map { computeTraceFingerprint(it, kind) }
      ?.sortedWith(Arrays::compare)?.forEach(digest::update)  // each flow
```

The analyzer sorts the flows, but the analyzer does not remove the duplicates. One more flow or one
less flow changes the fingerprint.

---

## 6. What the tests exclude

**Summary: two usual causes are not the cause here.**

| Possible cause | Test | Result |
|---|---|---|
| The order of the object hash codes | Start the analyzer with `-XX:hashCode=2` | No effect. 28 of 36 stable, as before |
| Ties in the sort of the nodes | Count the equal pairs in the sorted list | **0 ties.** The sort is a full order |
| Parallel work only | Start the analyzer with `-XX:ActiveProcessorCount=1` | Less change (32 of 36), but the change stays |

Full experiment table. Each line is two runs of the same code.

| Configuration | source-sink | trace | rule and sink |
|---|---|---|---|
| Default (6 workers) | 28/36 | 11/36 | 36/36 |
| `-XX:hashCode=2` | 28/36 | 8/36 | 36/36 |
| `-XX:ActiveProcessorCount=1` | 32/36 | 19/36 | 36/36 |
| Both options together | 30/36 | 14/36 | 36/36 |

---

## 7. What is still unknown

One question stays open. This document does not answer it.

**Question:** which mechanism in Step 1 makes the graph different?

Three candidates:

1. The check `cancellation.isActive()` in the function `process`.
2. The memory guard that stops the work.
3. The state that the parallel tasks share.

The difference of 15 nodes (2421 against 2406) looks like a stop of the work. It does not look like a
different order. But the tests do not show this. More work is necessary.

---

## 8. The recommended change

**Summary: remove the flows from the fingerprint.**

The analyzer already has a definition of a finding. The file
`TaintAnalysisUnitStorage.kt:12-30` has this code:

```kotlin
private data class VulnerabilityIdentity(
    val ruleId: String,
    val statement: CommonInst,
)
```

The analyzer groups the findings by the rule and the statement. This is the definition of one finding.
The fingerprint is more exact than this definition. The additional part is the part that changes.

### Change 1 — a new fingerprint (small change, large effect)

Write a third key `vulnerabilitySinkHash/v1`. Use the same function, but do not put the flows into it.
Then make this key the default key in the CLI (`cli/internal/sarif/identity.go:21-25`).

Measurement of the three keys:

| Key | Unique in one run | Stable in nine runs | Same finding in two versions |
|---|---|---|---|
| `vulnerabilitySourceSinkHash/v1` | yes | no — 28 of 36 | 28 |
| `vulnerabilityWithTraceHash/v1` | yes | no — 8 of 36 | 8 |
| Rule and sink only | **yes, 36 of 36** | **yes, 36 of 36** | **35** |

The new key also gives the correct answer for the two versions of the project.
It reports **1 new finding and 0 fixed findings**. The new finding is in
`HardwareKeyStoreService.java:475`. This file is new in version 2.14. The old key reported 8 new
findings and 7 fixed findings for the same two versions.

**Limit of this change:** a sink is a class, a method and an instruction number. If you add a
statement before the sink, the instruction number changes. The fingerprint then changes. In the test,
35 of 36 findings kept the fingerprint across two releases. This is better than the old key.

### Change 2 — make the flow selection stable (larger change)

Change 1 makes the fingerprint stable. Change 1 does not make the report stable. Do these tasks:

1. Sort the nodes and the methods by their names. Do not use the order of the graph.
2. Stop the time slices. Use only the step count (`TraceResolver.kt:161-162`).
3. Break the ties in `MethodTraceSearch.kt:76-83` with a name, not with the heap order.

### Change 3 — do not remove findings without a message (small change)

The file `TaintAnalyzer.kt:211-213` removes each finding that has no flow. The analyzer does this
without a message. If the machine is slow, a finding can go away. The baseline then shows this finding
as "Fixed". Count these findings and write them in the report.

---

## 9. Files to look at

| File | What it does |
|---|---|
| `core/src/main/kotlin/org/opentaint/common/sast/sarif/SarifGenerator.kt:118-150` | Computes the fingerprint |
| `core/src/main/kotlin/org/opentaint/jvm/sast/sarif/JirSarifGenerator.kt:64-69` | Puts the class, the method and the instruction number into the fingerprint |
| `.../ap/ifds/trace/path/MethodTraceSearch.kt:193-284` | Selects the flows |
| `.../ap/ifds/trace/path/Source2SinkTraceGraph.kt` | Gives a number to each node |
| `.../ap/ifds/trace/path/Source2SinkMethodTraceGraph.kt` | Gives a number to each method |
| `.../ap/ifds/trace/TraceResolver.kt:161-162` | Stops the work after 100 ms |
| `.../ap/ifds/trace/ParallelProcessingContext.kt` | Runs the work in parallel |
| `.../ap/ifds/taint/TaintAnalysisUnitStorage.kt:12-30` | Defines one finding |

---

## 10. How to do the test again

Five steps.

1. Build the analyzer. Use the command `./core/gradlew -p core :projectAnalyzerJar`.
2. Scan a project one time. Keep the report.
3. Scan the same project again. Do not change the code.
4. Compare the values of `partialFingerprints` in the two reports.
5. Compare the lists in `codeFlows` for each finding that has a different fingerprint.

To see the internal data, apply the patch `drift-probe.patch`. Then set the environment variable
`OPENTAINT_DRIFT_DEBUG=1`. The analyzer then writes two lines for each finding:

- `DRIFT-NODES` shows the size and the content of the graph.
- `DRIFT` shows the method order and the selected flows.

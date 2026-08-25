# The conductor fact explosion at `anyUnrollLimit = 100`

Measured 2026-08-25 on `saloed/7-fact-explosion-report`, on top of the absorbing-prepend build
(`7cacb0494`). One entry point, one rule, `L = 100` in every arm.

Earlier documents in this series measured `L = -1` (the unroll on, budget off) and `L = 0`. Their
conclusion — *the node mass is in `concat`, and the unroll is 2 % of it* — survives at `L = 100`,
but almost nothing else does: at this budget the unroll is **330 materialised copies and 1,418
nodes**, and the explosion has to be explained without it. This document does that, and names the
code — in conductor and in the engine — that produces it.

The new thing here is **attribution**. Every previous number was a global total; the operation was
known, the line of the analysed program was not. Four counters were added for this run
(§7), and they bill each grafted node to a call statement, to a method, to a fact base, and to the
shape of the type filter that ran there. `noSite = 0`: every one of the 175 M nodes is attributed.

---

## 1. Arms

Harness `scoped-harness/scoped-run.sh` (see `[[conductor-single-endpoint-witness]]`): conductor,
`-Xmx8g`, IFDS budget 300 s, `springEpFilter = WorkflowResource#rerun`
(`ep_kept: 1 of 107 handlers`), `--semgrep-rule-set rulesets/single-rule` (`rules_selected: 4 from
8`). The control swaps in `rulesets/single-rule-nostar`, which differs in **one character class** —
`$TYPE $*UNTRUSTED` becomes `$TYPE $UNTRUSTED` in
`java/lib/spring/untrusted-data-source.yaml:54`.

Five star replicates and three control replicates, because the volume counters move run to run and a
single sample cannot be told apart from a trend.

| arm | rc | wall | progress | concat calls | concat resultNodes | nodes/call | graft points/call | `[any]` reads | SARIF |
|---|---|---|---|---|---|---|---|---|---|
| star ×5 | **254** (IFDS timeout) | 282–299 s | 745 k–897 k | 1.44–1.91 M | **126–225 M** | 88–123 | **12.6–17.2** | 133 k–706 k | 2 (×4), 0 (×1) |
| nostar ×3 | **0** | 62–67 s | 187–189 k | 102–105 k | **1.30–1.63 M** | 12.7–15.6 | **1.91–2.32** | **0** | 0 |

`Total vulnerabilities: 2` in all five star arms including the one whose SARIF is 0 — that arm logs
`Filter out 2 vulnerabilities without traces`, the trace-resolution timeout documented in
`[[any-unroll-budget-trace-resolution-cost]]`. **The control's 0 is real**: removing the star loses
both findings.

---

## 2. The answer in one paragraph

The rule's `$*` seeds `arg(i).[any]` on both handler parameters. `[any]` is a wildcard the type
checker cannot see through, so from that point the access-path language is no longer bounded by
conductor's field types. Conductor then supplies three multipliers in the same class: a **self-
recursive method that passes the tainted map to itself unchanged** (`WorkflowExecutorOps#rerunWF`,
`:1891`), a **god object passed by reference into a 25-way virtual dispatch** (`decide:1216`,
`scheduleTask:1740` — `workflowSystemTask.execute(workflow, task, this)`), and a **type graph with
four one-step cycles and 21 erased slots**. The facts these produce are grafted by
`concatToLeafAbstractNodes` at **every abstract node of the summary conclusion** — 12.6–17.2 of them
per call instead of the control's 1.9–2.3 — and half the grafted node mass lands at a graft point
where the type filter is an unconditional accept. **78–93 % of every node the graft creates is
created inside `WorkflowExecutorOps`.**

---

## 3. Which line of conductor makes the nodes

`apop G-site` bills each `concatToLeafAbstractNodes` result to the call statement being applied.

**By class** (top-30 methods, ≥99 % of the attributed total, two replicates):

| share | class |
|---|---|
| **78.4 % / 92.9 %** | `com.netflix.conductor.core.execution.WorkflowExecutorOps` |
| 18.8 % / 5.5 % | `com.netflix.conductor.service.WorkflowTestService` |
| ≤1.2 % each | everything else (`DoWhile`, `SubWorkflow`, `WorkflowServiceImpl`, …) |

**By method**, the top two are always the same pair, in either order:

| replicate | `#rerunWF` | `#decide(WorkflowModel)` | `#scheduleTask` | `#terminateWorkflow` | `#endExecution` |
|---|---|---|---|---|---|
| `full-L100` | **36.5 %** | 30.4 % | 8.2 % | 5.3 % | 4.6 % |
| `full2-L100` | 16.1 % | **35.4 %** | 7.0 % | 6.9 % | — |

Those are exactly the members of the mutual-recursion SCC of `WorkflowExecutorOps` — `decide` →
`endExecution` → `terminate` → `terminateWorkflow` → `startWorkflow` → `createAndEvaluate` →
`createAndEvaluateWithLock` → `decide` — plus the self-recursive `rerunWF`.

**By single line.** One statement carries **16.4–21.3 %** of all graft node mass across four
replicates. It is one of two, and they are the same shape:

```java
// WorkflowExecutorOps.java:1216   -- 19.8 % / 21.3 % / 16.4 %
workflowSystemTask.execute(workflow, task, this)

// WorkflowExecutorOps.java:1891   -- 19.8 %, and 295.62 nodes per call, 59.21 graft points per call
if (rerunWF(subWorkflowId, taskId, taskInput, null, null)) {
```

Both hand a **whole object graph across a call boundary by reference**, and both are called from
inside a recursion.

`:1891` is the sharper of the two. `rerunWF(String workflowId, String taskId, Map taskInput, Map
workflowInput, String correlationId)` recurses on itself with `taskInput` **passed through
unchanged** — the same `Map<String,Object>` object at every depth — while `workflowId` changes. So
the analyser must consider the tainted map reaching an unbounded stack of `rerunWF` frames, and each
frame's summary is applied to the caller's fact.

`:1216` and `:1740` are the fan-out. `workflowSystemTask` comes from
`systemTaskRegistry.get(task.getTaskType())`, an interface-typed value, and there are **25
`WorkflowSystemTask` implementations** in this project. `this` is `WorkflowExecutorOps`, which holds
**13 injected DAO/service fields**. The census below shows the consequence: **53 distinct
`arg(2) @ …#execute(WorkflowModel, TaskModel, WorkflowExecutor)` bases each holding an identical
25,497-node tree** — the same god object, re-rooted once per implementation.

---

## 4. What the fact actually looks like

`tifaDiag` + `tifaLongLabels` retain and dump the largest initial-fact abstraction.

**Every one of the top 40 bases is `<static>`**, at 20,563–26,797 nodes and depth 107–108. That is
not forty trees: `AccessPathBase.ClassStatic` is a **`data object`** (`Accessors.kt:33`) — one global
base for the statics of every class, the class name demoted to the first accessor — and
`JIRMethodCallFactMapper.kt:219` delivers it into every callee with no reachability test:

```kotlin
if (factBase is AccessPathBase.ClassStatic) {
    onMappedFact(factAp, factBase)
}
```

Census of the top 2,500 of 11,325 `(method, base)` pairs:

| base | pairs | nodes | note |
|---|---|---|---|
| `<static>` | 1,080 | 1,511,379 | one global tree, delivered everywhere |
| `arg(2)` | **53** | **875,777** | 16,524 each — the executor passed to `execute`/`start` |
| `<this>` | 657 | 401,197 | `WorkflowExecutorOps` itself |
| `arg(0)` | 572 | 83,286 | |

The three big rows are **the same object graph viewed from three roots**.

### 4.1 Multiplicity, not shape

The retained tree: **552 distinct nodes, 23,348 paths — a ratio of 42.3**, built from 1,135
arrivals of which **69.3 % add no new distinct node at all** while 87.1 % still move the path count.
The explosion is a path count over a small DAG, which is why an instrument that samples node
identity sees nothing wrong.

### 4.2 The erasure, verbatim

```
n2*   .conductorProperties {com.netflix.conductor.redis.dao.BaseDynoDAO : …ConductorProperties} => n3
n3*   .stack               {…ConductorProperties : java.lang.String}                            => n4
n4*   .[any]                                                                                    => n5
      .buffer              {org.apache.commons.lang3.text.StrBuilder : java.lang.Object}         => n6
```

`ConductorProperties.stack` is `private String stack = "test";`
(`core/config/ConductorProperties.java:35`). The fact reads `.buffer` off it — a field of an
**unrelated** class, declared `java.lang.Object`. One level down, that `Object` node carries **17
children from 12 unrelated classes at once**: `.Element {java.lang.Iterable}`, `.MapKey
{java.util.Map}`, `.entries {org.springframework.messaging.simp.stomp.StompHeaders}`, `.uri`/`.method`
`{HttpTask$Input}`, `.bootStrapServers`/`.value` `{KafkaPublishTask$Input}`, `.tasks {WorkflowDef}`,
`.name {StartWorkflowRequest}`, `.name {WorkflowTask}`, … — the union of every field accessor the
analysis has ever demanded, attached at one position.

Conductor supplies the cycles that keep this going. In the type closure reachable from
`RerunWorkflowRequest` and `WorkflowModel` there are **four one-step cycles**, all self-loops on
`WorkflowTask` — `decisionCases` (`WorkflowTask.java:90`), `defaultCase` (`:101`), `forkTasks`
(`:104`), `loopOver` (`:139`) — plus a length-3 cycle through
`SubWorkflowParams.workflowDefinition : Object` (`SubWorkflowParams.java:42`, declared `Object`
only to dodge a protobuf import cycle, `:39-40`). The same closure has **21 erased slots**, two of
them bare `java.lang.Object`. Both seed fields are erased — `RerunWorkflowRequest.taskInput` and
`.workflowInput` are `Map<String, Object>` (`:33`, `:27`) — and both are installed by reference into
two more erased slots with no defensive copy: `workflow.setInput(workflowInput)`
(`WorkflowExecutorOps.java:1861`, `:1912` → `WorkflowModel.java:197`) and
`rerunFromTask.setInputData(taskInput)` (`:1951` → `TaskModel.java:240`).

---

## 5. The engine side, measured

### 5.1 The star is the switch

`$*UNTRUSTED` compiles to two positions, not one
(`AutomataToTaintRuleConversion.kt:1297`):

```kotlin
return if (!star) listOf(pos) else listOf(pos, pos.withAnyField())
```

Everything downstream follows from the second element. In the control arm, with the star removed:

| counter | star | nostar |
|---|---|---|
| `[any]` reads (`getChild` synthesis) | 133 k–706 k, **62–70 % returning a child the fact does not hold** | **0** |
| unroll calls | 178 | **0** |
| `delta()` reads crossing an `[any]` | 36 k–266 k, **99.6 % keeping the `[any]`** | **0** |
| grafts whose delta carries an `[any]` | 4–29 % of calls, **99.0–99.5 % keeping it** | **0** |
| graft points per call | 12.6–17.2 | **1.91–2.32** |
| biggest single graft | 34,167 nodes | **159 nodes** |
| outcome | timeout, 8 GB | **converges, 62 s** |

`isCoveredByAny` returns `true` for **every** `FieldAccessor` in production
(`TaintAnalyzer.kt:75-77`), and `AccessNode.getChild`'s `isCoveredByAny` arm
(`AccessTree.kt:692-733`) **takes no `FactTypeChecker` at all**. So a read through an `[any]`
manufactures a concrete child of any name, and `filterStartsWith`'s fold
(`AccessTree.kt:2432-2438`) materialises it as a stored edge. That is how `.buffer` gets under a
`String`.

### 5.2 The graft is where the nodes are, and half of it is untyped

`concatToLeafAbstractNodes` attaches the delta at **every abstract node of the receiver**. The
receiver is the summary's **conclusion** (short, concrete — mean 27 nodes) and the delta is the
**caller's remainder** (mean 44 nodes, and up to 34,167). `receiverCarriesAny` is ~0 in every arm:
the `[any]` travels in the delta, not in the thing being extended.

The new `apop I-filter` counter records what the type filter can do at each graft point.
`JIRFactTypeChecker.accessorActualType` reads **only** `accessPath.lastOrNull()`
(`JIRFactTypeChecker.kt:194`) and returns `null` — an unconditional-accept filter — for an empty
path and for a path ending in `[any]` (`:184`, `:206`).

| graft points | count | share of points | delta nodes | share of delta mass |
|---|---|---|---|---|
| **empty path → always accept** | 943,594 | 3.5 % | **77,857,770** | **50.8 %** |
| path ends in `[any]` → always accept | **113** | 0.0004 % | 226 | 0.0001 % |
| typed | 25,920,409 | 96.5 % | 75,346,871 | 49.2 % |

**Half the grafted node mass is attached where no type test runs at all.** Note what this does *not*
say: the same hole is present in the control (89,269 empty-path points carrying 73.9 % of its delta
mass) and the control converges. The hole is structural; the star changes the **size of the delta
that flows through it**, not whether the filter is consulted.

The two standing gate failures are this hole, pinned as tests:
`JIRFactTypeCheckerUnrollFilterTest.object typed model field rejects an unrelated field` and
`chained model fields reject an unrelated field` both ask the checker to reject `java.net.URL#host`
after one `Object`-typed step, and it accepts. They fail at the base commit too — the engine does not
have the behaviour those tests ask for, and §4.2's 17-children node is what that costs on conductor.

And where the filter *is* consulted it is shallow: it checks the delta's top accessor only
(`AccessNode.filterAccessNode`, `AccessTree.kt:1909-1927`, recurses solely on the element arm's
`FilterNext`). Everything below the first field edge of a grafted delta is never type-checked.

### 5.3 Not the unroll

At `L = 100` the whole `unrollAnyAccessors` mechanism is 178 calls, 330 materialised copies and
1,418 nodes added — **0.001 %** of the 126–225 M. Any account of this explosion that runs through the
unroll is an account of a different arm.

---

## 6. The chain, each link with its number

1. `$TYPE $*UNTRUSTED` on a Spring handler parameter seeds `arg(i)` **and** `arg(i).[any]`
   (`AutomataToTaintRuleConversion.kt:1297`). Removing the star converges in 62 s and loses both
   findings.
2. `[any]` reads synthesise children with **no type check** (`AccessTree.kt:692-733`,
   `TaintAnalyzer.kt:75-77`): 133 k–706 k reads, 62–70 % of them returning something the fact does
   not hold. Zero in the control.
3. Those children include type-infeasible steps — `String` → `.buffer {StrBuilder : Object}` — and
   once a position is `java.lang.Object` the checker accepts every field
   (`JIRFactTypeChecker.kt:108`, `:245`, `JIRTypes.kt:83`). One such node carries 17 children from
   12 unrelated classes.
4. Conductor's type graph closes the loop: 4 one-step cycles on `WorkflowTask`, a 5th through an
   `Object` slot, 21 erased slots, both seed fields erased and installed by reference into two more.
5. `rerunWF:1891` passes the tainted map to itself unchanged; `decide:1216` and `scheduleTask:1740`
   pass `this` — 13 injected services — into a 25-way virtual dispatch, giving **53 identical
   25,497-node `arg(2)` trees**.
6. `AccessPathBase.ClassStatic` is one global base (`Accessors.kt:33`) broadcast unconditionally
   (`JIRMethodCallFactMapper.kt:219`): the top 40 bases are all `<static>`, 1,080 of the top 2,500
   pairs, 52 % of their node mass.
7. `concatToLeafAbstractNodes` grafts the caller's remainder at **every** abstract node of the
   conclusion: **12.6–17.2 points per call** against the control's 1.91–2.32, max 3,568–4,000,
   producing **126–225 M nodes** against the control's 1.3–1.6 M.
8. The result is multiplicity, not shape: 552 distinct nodes carrying 23,348 paths, 69.3 % of
   arrivals adding no new node.

---

## 7. Instrumentation added for this investigation

All in `ApOpDiagnostics` (`-Dopentaint.apOpDiag=true`), all off by default.

- **`apop G-site`** — the graft billed to a call statement, keyed by statement identity, formatted
  once at report time. `MethodAnalyzer.applyMethodAnySummaries` parks the statement in
  `TifaDiagnostics.callSite` (now save/restore, via `withCallSite`, because a summary application
  runs inside a call step that has already parked one). `noSite = 0` on every run.
- **`apop G-method`** — the same totals rolled up per method over **all** sites, not just the
  printed top 30, so a per-class share is a total rather than a lower bound.
- **`apop H-base`** — the graft split by the root the receiver hangs off, because `<static>` is one
  base for every class and the site rows cannot draw that line.
- **`apop I-filter`** — the shape of the accessor path handed to `accessPathFilter` at each graft
  point: empty / `[any]`-tailed / typed, with delta node counts. This is what turned "the `[any]`
  disables the type check" from a code reading into a measurement — and falsified the `[any]`-tail
  half of it (113 events).

`gate.sh` — see §8.

---

## 8. Premise population: the top five methods, and the facts behind them

The graft answers "where do the NODES come from". A separate question is where the **premises** come
from — the initial facts a method's summaries are keyed on, one storage entry each
(`-Dopentaint.summaryPremiseDiag=true`, `MethodInitialToFinalApSummaries`).

**54,169 premises over 14,696 methods.** Top five:

| # | premises | id | ap | carry `[any]` | maxLinks | method |
|---|---|---|---|---|---|---|
| 1 | **6,537** | 434 | 6,103 | **9** | 11 | `WorkflowExecutorOps#decide(WorkflowModel)` |
| 2 | 1,882 | 35 | 1,847 | 0 | 9 | `WorkflowExecutorOps#rerunWF(String, String, Map, Map, String)` |
| 3 | 1,548 | 42 | 1,506 | 17 | 11 | `DoWhile#execute(WorkflowModel, TaskModel, WorkflowExecutor)` |
| 4 | 1,263 | 42 | 1,221 | 7 | 11 | `WorkflowExecutorOps#terminate(WorkflowModel, TerminateWorkflowException)` |
| 5 | 1,241 | 16 | 1,225 | 4 | 11 | `WorkflowExecutorOps#terminateWorkflow(WorkflowModel, String, String)` |

The top five hold **23 %** of every premise in the run, and eleven of the top twelve are
`WorkflowExecutorOps` methods or a `WorkflowSystemTask` taking a `WorkflowExecutor`. The control has
25,581 premises over the same 14,696 methods, its top method is `Stream#map` with 835 (820 of them
identity), and `decide(WorkflowModel)` falls from **6,537 to 373** — a 17.5× cut, with `maxLinks`
11 → 5.

**The premises do not carry `[any]`** — 9 of 6,537. This is the load-bearing observation of this
section. The star does not fill summary storage with wildcards; it fills it with **concrete
enumerations of the paths a wildcard denotes**. Across 4,000 traced premises of `decide` there are
only **61 distinct accessor labels**, and the population is (a subset of) the sequences over that
alphabet: `.headerValues` 716, `.Element` 670, `.headerValue` 634, `.inputPayload` 415, `.inputData`
357, `.workflowTask` 212, `.inputParameters` 157, `.outputPayload` 148, `.workflowDefinition` 100,
`.outputData` 93, `.buffer` 91. `headerValue`/`headerValues` are fields of
`org.springframework.http.HttpHeaders` — 1,350 links of premises *about conductor's workflow model*
are Spring HTTP header fields, which is §4.2's erasure seen from the storage side.

### 8.1 The fact behind them: small trees emit, big trees do not

`tifaDiag` reports, per `(base, method)`, the size of the accumulated fact (`added`) and how many
premises walking it emitted (`emits`). Lining the two up inverts the obvious guess:

| method | base | `added` | `adds` | **`emits`** |
|---|---|---|---|---|
| `decide(WorkflowModel)` | **arg(0)** | **414** | 372 | **5,667** |
| `decide(WorkflowModel)` | `<static>` | 310 | 520 | 1,252 |
| `decide(WorkflowModel)` | `<this>` | 62 | 70 | 14 |
| `rerunWF` | `<this>` | **56,729** | 3,203 | **16** |
| `rerunWF` | `<static>` | 10,216 | 1,654 | 3,824 |
| `DoWhile#execute` | **arg(2)** | **64,583** | 3,052 | **14** |
| `terminate` | `<this>` | **65,407** | 3,901 | **14** |
| `terminateWorkflow` | arg(0) | 304 | 374 | 1,408 |

**A 414-node fact emits 5,667 premises; a 65,407-node fact emits 14.** The god-object trees of §4 —
`<this>`, and the `arg(2)` executor — are the biggest objects in the run and they are nearly silent,
because nothing downstream demands paths into them. Premise population is driven by **demand**, not
by fact size, and the demanded base is `arg(0)`: the `WorkflowModel`.

`TreeInitialFactAbstraction.addAbstractInitialFact` re-walks `facts.allAddedFacts()` — the whole
accumulated tree — on **every** registration, emitting one premise per abstract path found. So
`emits ≈ adds × paths`, and `paths` is the multiplicity of §4.1's DAG, not its node count.

### 8.2 Where the arg(0) fact comes from

The full arrival ladder for `arg(0) @ WorkflowExecutorOps#decide(WorkflowModel)`:

- **222 arrivals, from exactly two call sites** — `WorkflowExecutorOps#decide(String):1137`
  (`this.decide(workflow)`, 128 arrivals) and `#createAndEvaluateWithLock:2185` (`this.decide(workflow)`,
  94). Both are inside the mutual-recursion SCC of §3.
- It ends at **93 distinct nodes carrying 370 paths**, depth 66.
- **71.2 % of arrivals add no new distinct node** — the same re-derivation ratio as §4.1.

So the whole 6,537-premise population of the run's largest premise holder rests on a 93-node fact
delivered by two statements, walked 372 times.

### 8.3 What demands 61 labels

`decide` itself reads only five paths off its argument (`WorkflowExecutorOps.java:1170`, `:1211`,
`:1212`, `:1237`, `:1249`). The demand comes from underneath it, and two conductor patterns account
for its shape:

- **Recursive traversal of the task tree.** `DeciderService` reaches `WorkflowDef.getTasks()` at
  `:359`, `:366`, `:490`, and everything routing through `WorkflowDef.collectTasks()`
  (`WorkflowDef.java:445-451`) into `WorkflowTask.collectTasks()` (`WorkflowTask.java:650-659`),
  which recurses through `children()` (`:629-648`) — `decisionCases.values()`, `defaultCase`,
  `forkTasks`, `loopOver`. Those are exactly §4.2's four one-step cycles, walked by real code.
- **Generic iteration of an erased map.** `ParametersUtils.replace(Map<String, Object>)`
  (`ParametersUtils.java:187-207`) is mutually recursive with `replaceList(List<?>)` (`:209-226`):
  it iterates arbitrary keys, recurses into any nested `Map`, and recurses into any nested `List`.
  It is reached from `DeciderService:702-707` and `:978-980` with
  `WorkflowTask.getInputParameters()`. That is the code that turns one map into "any key, any value,
  at any depth" — and `WorkflowTask` has 35 fields, `TaskModel` 53, `WorkflowModel` 30,
  `WorkflowDef` 28.

`DoWhile#execute` (rank 3) is the same shape at the task level: it iterates
`doWhileTaskModel.getWorkflowTask().getLoopOver()` (`DoWhile.java:287-294`) and drives
`WorkflowTask.has()`/`next()` (`WorkflowTask.java:736-758`, `:661-734`), which recurse over
`children()` again.

## 9. What the `[any]` actually does to the premises

The premises of §8 are 96 % `[any]`-free, and the trees that hold the facts behind them are made of
almost nothing else. Both are true; this section is how they fit together.

### 9.1 The trees are `[any]` structures

Profiles of the largest `added` trees, `anyEdges` against the tree's DISTINCT node count:

| base @ method | size | distinct | `[any]` edges | share of distinct | depth | emits |
|---|---|---|---|---|---|---|
| `<this>` @ `rerunWF` | 53,049 | 1,620 | 1,604 | **99.0 %** | 115 | 16 |
| `<this>` @ `terminate` | 44,858 | 6,331 | 5,469 | 86.4 % | 115 | 14 |
| `arg(2)` @ `DoWhile#execute` | 43,553 | 6,298 | 5,468 | 86.8 % | 115 | 14 |
| `<static>` @ `rerunWF` | 10,216 | 107 | 95 | 88.8 % | 81 | 3,824 |
| `<static>` @ `terminate` | 5,793 | 168 | 93 | 55.4 % | 82 | 1,145 |

`.[any]` is the single most common accessor in every one of them, and `anyDepths` runs `[3 … 13]` —
they are stacked at every level, which is also where the depth of 115 comes from
(`ANY_ACCESSOR_DEPTH_CHARGE` is 10 per `[any]`-owning node).

### 9.2 The `[any]` is what gives a node its fan-out

Out-degree in the one tree retained in full — 538 distinct nodes carrying 22,211 paths:

| | nodes | mean out-degree | max |
|---|---|---|---|
| owns an `[any]` edge | **452** (84 %) | **10.50** | 77 |
| does not | 86 | **1.47** | 5 |

**A node that owns an `[any]` has 7.1× the fan-out of one that does not.**

A correction to the first version of this paragraph, which attributed that fan-out to
`AccessNode.getChild`'s `isCoveredByAny` arm: **a read cannot grow a stored fact.** `getChild`
returns a node assembled from subtrees of the receiver, and the receiver is unchanged. The only
operations that give an existing node another child are the merges — `mergeAdd` of arrivals into
`added`, the graft at an abstract node, and `filterStartsWith`'s re-prepend. Fan-out is built by
prepend and concat; what the untyped read (§5.1) does is let an `[any]`-carrying fact *answer* a
demand, so that the fact is derived and delivered at all.

What survives the correction is the association and its size: nodes that own an `[any]` are the ones
many facts converge on, and `added` is their union — §4.2's `.buffer` node with 17 children from 12
unrelated classes is what that union looks like. Path count is the product of out-degrees along a
path: 538 nodes, 22,211 paths.

### 9.3 4 % of arrivals carry 52 % of the growth

Arrivals at an initial-fact abstraction, split by whether the INCOMING fact carried an `[any]`:

| | arrivals | incoming nodes | mean incoming | nodes actually added to `added` |
|---|---|---|---|---|
| incoming carries `[any]` | **12,570 (4.2 %)** | 18,463,174 | **1,469** | **2,160,332 (51.6 %)** |
| incoming is concrete | 284,302 | 26,057,585 | 92 | 2,026,213 |
| **control, both columns** | 43,549 | 311,762 | 7 | **64,131** |

An `[any]`-carrying fact is **16× larger** on arrival and contributes **24× more** per arrival. The
control's `added` grows by 64,131 nodes over the whole run against the star arm's 4,186,545 — **65×**.

**So the user-visible claim is confirmed: the huge `added` trees are `[any]`-built.** Not by the
unroll (330 copies, §5.3) and not by anything local to the abstraction, but by arrivals that are
large *because* every node on them answers every read.

### 9.4 …and then the `[any]` is spent, not stored

The premise walk emits 87,535 premises. Split by how the `[any]` was involved:

| | count | share |
|---|---|---|
| names an `[any]` in the emitted chain | 3,452 | 3.9 % |
| walk was governed by an `[any]` (`governingAnyId != null`) | 3,452 | 3.9 % |
| emitted from a HOISTED `[any]` subtree (the zero-times descent) | **854** | **1.0 %** |
| plain concrete walk | ~83,000 | ~95 % |

The first two columns being *identical* is itself a result: `governingAnyId` becomes non-null only on
the descent that names the `[any]`, so "under an `[any]`" and "carries an `[any]`" are the same set.

And the third column falsifies the obvious guess about the mechanism. `[any]` is zero-or-more, so
`abstractAccessPath` also descends into the `[any]`'s subtree *without* extending the prefix
(`TreeInitialFactAbstraction.kt`, the "`[any]` taken ZERO times" branch), which hoists everything
below an `[any]` up to the current level as concrete premises. That descent fires 106,453 times
(`anyDescents`) and produces **854 premises — 1 %**. It is not the multiplier.

**The `[any]` is therefore entirely upstream of the premise.** It does not appear in what is stored
(9 of `decide`'s 6,537, §8), it is not what the walk is standing under when it emits (3.9 %), and it
is not the hoist (1.0 %). What it does is make the FACT big — 7.1× fan-out per node, 52 % of all
`added` growth from 4 % of arrivals — and the walk then enumerates that fact's paths, concretely, one
premise each. `decide(WorkflowModel)` goes 373 → 6,537 premises between the control and the star arm
without the premises themselves ever mentioning an `[any]`.

## 10. Why the manager's limit does not guard the fan-out

The `[any]` manager was built on the hypothesis that a budget would make the absorbing prepend start
folding accessors back into the `[any]` and hold the tree down. §9.2 says the tree's cost is fan-out —
10.50 children per `[any]`-owning node. This section is why `L = 100` does not touch that, in four
steps, each one measured.

### 10.1 The fact-side read cannot refuse

`AccessNode.getChild`'s `isCoveredByAny` arm is the only place a concrete accessor is synthesised out
of an `[any]`. It consults the manager — and then ignores the answer:

```kotlin
val childState = if (record) manager.anyUnroll.readChild(anyId, accessor) else manager.anyUnroll.peekChild(anyId, accessor)
val anyAccessorNoRepeats = anyAccessorNode.clearChild(accessor)
val originalAnyNoRepeats = anyAccessorNoRepeats.addParentIfPossible(ANY_ACCESSOR_IDX, childState ?: anyId)
```

`childState` is used only as the state *tag* on the rebuilt `[any]` edge, and `childState ?: anyId`
falls back to the parent state. `resultNode` was already computed a few lines above with no manager
involvement. And `readChild` itself never returns null on the enabled path — that is step 3 of the
absorbing-prepend design, "the read records past the limit instead of refusing":

```kotlin
val dag = current.dag.find()
val paid = dag.total < limit                     // the ONLY thing the pot decides
val child = mint(current, accessor, dag, paid)
```

The one entry point that *does* refuse is `readChildPaidOnly`, used solely by the initial-fact
abstraction's unroll. That is the entire meaning of `refused = 50`.

### 10.2 …and 99.9 % of reads never reach the pot anyway

`readChild`'s fast path returns an existing transition before `dag` is even resolved:

| arm | reads | reused free | reads that reached `dag.total < limit` |
|---|---|---|---|
| `L = 100` | 556,279 | **99.88 %** | 601 |
| `L = 8` | 631,193 | **99.91 %** | 560 |
| `L = 0` | 1,737,057 | **99.98 %** | 386 |

Whatever `L` is set to, it can influence **at most one read in eight hundred**, and even then it
changes a label rather than an outcome.

### 10.3 Absorption is switched OFF while the budget is unspent

```kotlin
fun writesAbove(state: AnyUnrollState?): Boolean {
    if (!enabled || state == null) return true
    val kind = state.find().kind
    return kind == AnyUnrollKind.ORIGIN || kind == AnyUnrollKind.PAID
}
```

`true` means "write the step, do not absorb". Only `CREDIT` states — states minted *after* the pot was
spent — may absorb. So the knob runs backwards from the hypothesis: **a higher limit keeps states
`PAID` for longer and makes absorption strictly less likely.**

| arm | absorptions | of which `absorbStay` (self-loop, no structural change) | prepends declined by `writesAbove` |
|---|---|---|---|
| `L = 100` | 54,579 | 0.1 % | **20,876,190** |
| `L = 8` | 88,199 | 0.0 % | **26,533,199** |
| `L = 0` | 14,355,560 | **99.7 %** | 8,783 |

At `L = 100`, `writesAbove` accounts for 99.7 % of every decline; `guardBlocked` and `uncovered` are
both **0**, so §4.3's subtree probe and the coverage test exonerate themselves. And `L = 0`, the only
setting that turns absorption on in volume, spends 99.7 % of it on self-loops — absorbing in place,
which rewrites nothing.

### 10.4 …and an absorption could not remove a child even if it fired

`installAbove` takes a node `N` with children `{[any] → A} ∪ C` and a step `a` to install above it:

- without absorption: `a.N` — the parent has **one** child;
- with absorption: `a.rest ⊕ [any]@pred.A` — the parent has **two**, unless `C` is empty.

It removes one level of **depth on the `[any]`-rooted branch** and, where the node has concrete
siblings, it *raises* the parent's child count from 1 to 2 (§4.4's SPLIT, which exists precisely so
that dropping the step does not silently rewrite the concrete siblings too). Nothing in the manager or
the tree caps a node's child count; the only limiters in the package are
`SUBSEQUENT_ARRAY_ELEMENTS_LIMIT = 2`, `limitFieldAccess` (repeats of *one* field), and a query visit
budget.

### 10.5 The measurement

Out-degree of `[any]`-owning nodes in the largest retained tree, across four limits:

| arm | rc | progress | tree | `[any]`-owning | mean out | max | other | mean out |
|---|---|---|---|---|---|---|---|---|
| `L = 100` | 254 | 789,495 | 538 | 452 | **10.50** | 77 | 86 | 1.47 |
| `L = 8` | 254 | 911,879 | 252 | 199 | **14.48** | 54 | 53 | 1.08 |
| `L = 0` | 254 | 682,656 | 415 | 276 | **8.36** | 55 | 139 | 11.75 |
| `L = -1` (off) | 253 | 2,127,666 | 2,599 | **0** | — | — | 2,599 | **15.45** |

**Tightening the limit does not reduce the fan-out.** `L = 8` is *higher* than `L = 100`. At `L = 0`
the `[any]` nodes thin out and the fan-out simply moves onto the concrete ones (139 nodes at 11.75).
With the manager off the `[any]` is gone from the tree entirely — the unroll converted it — and
out-degree is 15.45, the highest of the four. Every arm sits in the same 8–15 band.

### 10.6 What the manager does bound, and why that is a different axis

The hypothesis was not wrong about the mechanism it was built for. That mechanism is **depth**: the
delta/concat round trip, where a premise reads through an `[any]`, consumes nothing, and the graft
re-attaches the remainder under the conclusion's prefix — one concrete link longer, `[any]` intact,
per lap. The manager does bound it: `AnyDeltaConcatRoundTripTest` closes four laps into a loop with
depth constant, and `depthGain` fell 19.87 M → 16.34 M at `L = 8` on this workload.

Conductor's cost is **breadth**. A node that owns an `[any]` answers every read anyone ever makes, so
it collects one child per demanded accessor — 10.50 of them, untyped (§5.1, §9.2) — and the path count
is the product of those degrees. The manager has exactly one lever on the tree, the state tag on an
`[any]` edge, and by §10.1 that tag cannot decline a child. Depth and breadth are different axes, and
the budget is an instrument on the wrong one.

## 11. Why absorption does not fire, at L = 100

§10 answered a question about the knob. This is the question about the **fact patterns**: with the
limit left at 100, what do the declining prepends actually look like, and would absorption have had
anything to do had it been allowed?

A counterfactual probe answers it directly. Every prepend the kind gate declines now runs the *rest*
of the probe — subtree guard, coverage, backward step — with the counters suppressed, and records
where it would have landed.

### 11.1 The result

11,126,048 prepends declined, and the kind that declined them is not the one the design's argument
leaned on:

| declined at a state whose kind is | count |
|---|---|
| `ORIGIN` | **507** |
| `PAID` | **11,125,541** |

Had the gate been open:

| would have | count | share |
|---|---|---|
| **moved to a real predecessor** | **3,562,561** | **32.0 %** |
| absorbed into ITSELF (self-loop, rewrites nothing) | **6,505,790** | **58.5 %** |
| found no incoming edge for that accessor at all | 1,057,697 | 9.5 % |
| been stopped by the §4.3 subtree guard | **0** | — |
| been stopped by coverage | **0** | — |

**Two thirds of the declined prepends were never absorbable.** The automaton either had no transition
labelled with that accessor into that position (9.5 %), or the only one it had was a self-loop
`p --a--> p`, where absorbing means staying put and the fact comes out unchanged (58.5 %). Only
**32 %** is structure the kind gate is genuinely holding back — and that is the ceiling on what this
mechanism could remove here, before any question of whether removing it would help.

### 11.2 The fact pattern is always the same

Every sampled `[any]` position — 80 of 80, across both sampled outcomes and every accessor — has the
same subtree:

```
prepend .Element   above a node whose [any] subtree is   ![MARK].$
prepend .tasks     above a node whose [any] subtree is   ![MARK].$
prepend .MapValue  above a node whose [any] subtree is   ![MARK].$
```

The `[any]` carries **the taint mark and nothing else** — the seed shape the star source produces,
`arg(i).[any]![mark]`, arriving unchanged at a prepend millions of times. Two consequences follow:

- The §4.3 subtree guard can never fire, because the `[any]` subtree has no field children to collide
  with. `guardBlocked = 0` is structural, not luck. Same for coverage: every sampled accessor is a
  field or an element.
- The accessors split cleanly by whether they were ever *read* through this position. Would-move:
  `.Element`, `.MapKey`, `.MapValue`, `.tasks`, `.input`, `.workflowDef`, `.taskId`, `.partETags`,
  `.contentType`, `.event`. No-predecessor: `.entries`, `.outputData`, `.status`, `.name`,
  `.payload`, `.workerId`, `.uploadUrl`, `.fileHandleId`, `.lambdaCSArg$0/$2/$3`. The first list is
  the hot model spine; the second is what one caller demanded once and no read ever crossed an
  `[any]` with.

### 11.3 One state decides for millions of facts

The kind is a property of an **automaton state**. This run has 159 origins and 596 transitions, 439
of them tagged `PAID` — and those few hundred states are the positions of **11.1 million** prepends.
A single state tagged `PAID` declines millions of rewrites at once.

That is why the gate dominates the counters. It is not that the budget was set badly: `writesAbove`
makes a per-state decision on behalf of a fact population four orders of magnitude larger, and a
state stays `PAID` for as long as its origin-component's pot is solvent. The pots *do* cross —
`maxPotTotal = 400` against `limit = 100` — but crossing only tags the transitions minted afterwards
(`mintKind = [paid: 439, credit: 157]`), and the states already stamped `PAID` keep the stamp.

### 11.4 What this leaves

Three obstacles, and they are not the same size:

1. **58.5 % self-loops.** The automaton says reading `a` from this position returns to this position;
   absorbing is a no-op. Nothing done to the gate reaches these.
2. **9.5 % no incoming edge.** Reads mint transitions, and with 596 transitions in the whole run
   against millions of prepends, most prepended accessors have never been read through an `[any]`.
3. **32.0 % blocked by the kind gate alone.** The only part where opening the gate changes the
   output.

## 12. Why the states are `PAID` — it is not the pot

§11 left the gate declining 11–18 M prepends at `PAID` states and did not say why those states were
`PAID` when the automaton is far larger than `L`. Four arms answer it, all at `L = 100`.

### 12.1 The pot is per component, and the components are tiny

The `[any]` progress line, which reports the pots directly:

| arm | live origin-components | **components that ever reached `L`** | states | max states/dag | transitions |
|---|---|---|---|---|---|
| `L = 100` | 141 | **1** | 321 | 123 | 3,773 |
| `L = 8` | 249 | **2** | 497 | 147 | 9,977 |
| `L = 0` | 264 | 264 | 452 | 154 | 11,099 |

One pot of 141 crosses. Mean 2.3 states per component against a quota of 100 — so the aggregate
budget is `141 × L`, and `total` is not computing a wrong number, it is correctly counting the wrong
unit.

### 12.2 Changing the unit is not the fix — measured

`-Dopentaint.anyUnrollKindPolicy=global` makes the mint compare against one run-wide pot instead of
the component's, changing nothing else:

| | `perDag` | `global` |
|---|---|---|
| mints paid / credit | 399 / 159 | 393 / **241** |
| absorptions | 50,234 | **79,857** |
| absorptions as a share of prepends | 0.28 % | **0.37 %** |
| progress | 755,686 | 771,515 |
| rc | 254 | 254 |

52 % more `CREDIT` states, 59 % more absorptions, and the arm still does not converge.

### 12.3 The ceiling arm gives it away

`alwaysCredit` forces the fact-side read to mint `CREDIT` unconditionally — the strict upper bound of
any rescue strategy, since nothing can demote more than everything. It reported
`mintKind = [paid: 437, credit: 142]`.

**437 `PAID` mints, with the fact-side read minting none.** So they are not coming from `readChild`
at all, and no policy on `readChild` can reach them.

### 12.4 Where they come from

A provenance flag on the state settles it:

```
mintKind=[paid:429(unroll:427), credit:120]
```

**427 of 429 `PAID` mints come from `readChildPaidOnly`** — the initial-fact abstraction's unroll.
That entry point passes `paid = true` unconditionally and has no `CREDIT` branch at all: past the
limit it **refuses** rather than crediting.

```kotlin
val dag = current.dag.find()
if (dag.total >= limit) { ...; return null }          // refuse -- not credit
val child = mint(current, accessor, dag, paid = true) // otherwise always PAID
```

And those are the states doing the declining. Top decliners, with provenance:

| state | kind / minted by | declines | share |
|---|---|---|---|
| #423 | `PAID` / **unroll** | 5,617,401 | **67.5 %** |
| #181 | `PAID` / **unroll** | 246,977 | 3.0 % |
| #319 | `PAID` / **unroll** | 238,884 | 2.9 % |
| #421 | `PAID` / **unroll** | 234,930 | 2.8 % |
| #392 | `PAID` / **unroll** | 196,799 | 2.4 % |
| #659 | `PAID` / read | 175,002 | 2.1 % |

Six of the top seven were minted by the unroll, and one state carries two thirds of every decline in
the run. An earlier arm without the provenance flag showed the same concentration — three states,
95.7 % of 18 M declines.

**So the answer to "why so many `PAID`" is not the budget.** It is that the unroll's mint is
`PAID`-by-construction, its states are the hot positions of the whole fact population, and a kind is
stamped once at mint and never revisited.

### 12.5 What a re-score would be worth

A re-score is the only proposal that can reach state #423, because #423 already exists and every
budget policy acts on mints. Its ceiling is measurable, and the counterfactual of §11 gives it: had
every declining state been `CREDIT`,

| | share of declines |
|---|---|
| would have moved to a real predecessor | **31.4 %** (2,608,808 of 8,319,534) |
| would have absorbed into itself — self-loop | 56.7 % |
| had no incoming edge for that accessor | 11.9 % |

Two independent runs put the movable fraction at 31.4 % and 32.0 %; a third, with a larger decline
count, put it at 5.3 %. So the prize is **at most about a third of the declines**, and two thirds of
them are patterns nothing can absorb. A re-score should be scoped against that number, not against
the 8–18 M decline count.

**Correction to the first version of this section**, which proposed giving `readChildPaidOnly` a
`CREDIT` branch. That is wrong, and the refusal is the intended behaviour: the unroll must not
materialise a state it cannot pay for — when the pot is spent it aborts the enumeration and the walk
emits the coarse `[any]` premise instead (§5.3's `enumerateAnyFrontier` arm). Crediting there would
put unpaid concrete states into the automaton, which is the population the budget exists to bound.
The re-score is the right instrument, and §13 builds it.

## 13. The dag-local re-score

§12 left one question open: the kind is stamped at the mint and never revisited, so a state minted
while its pot was solvent stays `PAID` after the pot has gone past `L`. Can a re-score reach the
states that matter?

### 13.1 It can — the pots are bimodal, and the hot states are in the one that crossed

A census of every pot at the end of the run, which the manager keeps no registry for and which the
progress line summarises only by its maximum:

```
dags live=140 crossedLimit=1 limit=100
  totals=[401/65, 6/7, 6/7, 6/7, 6/7, 5/3, 5/6, 4/5, 4/4, 4/5, 3/4, 3/4]   (total/states)
  byTotal=[<2:112, 2-3:18, 4-L/8:9, L/8-L/4:0, L/4-L/2:0, L/2-L:0, >=L:1]
```

One pot at **401 against a limit of 100**; the other 139 at 12 or below, 112 of them below 2. Nothing
in between. And the states doing the declining are all in the pot that crossed:

| state | kind / minted by | dag | dag total | declines |
|---|---|---|---|---|
| #705 | `PAID` / read | #43 | **401** | 26.7 % |
| #428 | `PAID` / **unroll** | #43 | **401** | 23.6 % |
| #46 | `PAID` / read | #46 | **401** | 17.8 % |
| #733 | `PAID` / read | #46 | **401** | 6.3 % |

**This corrects §12.1's reading.** "141 components and only one crosses" is true, and I took it to
mean the budget never bites. It bites in exactly the place that matters: the 139 small pots are
irrelevant, and the one that governs 82 % of all declines is at four times its limit with its states
still stamped `PAID`.

### 13.2 The implementation

`-Dopentaint.anyUnrollKindPolicy=rescore` mints exactly as `perDag` does and adds one rule: when a
dag's `total` reaches a threshold, re-assign the whole dag's kinds — breadth-first from the root,
charging the same `pathCount` the mint charges, keeping states `PAID` while a budget of `L` lasts and
demoting the rest to `CREDIT`.

Breadth-first and not depth-first because the automaton is allowed to be cyclic and a depth-first
walk would spend the whole budget down one accessor sequence. The threshold doubles after each
re-score, so a dag is re-scored O(log total) times — the kind lattice's termination argument assumes
a bounded number of kind changes per state, and a re-score firing on every mint would not have one.
A fusion takes the lower of the two thresholds, which is the "after merge the new total is more than
the limit" case.

### 13.3 It works

Three replicates each, `L = 100` throughout, same jar, arms differing only in the policy:

| | off (`perDag`) | on (`rescore`) |
|---|---|---|
| **absorptions** | 75,268 / 76,303 / 20,019 | **2,664,161 / 3,369,619 / 5,063,899** |
| **IFDS progress** | 808,696 / 784,539 / 875,157 | **911,332 / 958,979 / 941,602** |
| prepends declined | 27.3 M / 24.8 M / 15.0 M | 10.8 M / 14.8 M / 21.6 M |
| concat resultNodes | 211 M / 202 M / 226 M | 198 M / 240 M / 225 M |
| graft points per call | 20.40 / 19.95 / 16.11 | 15.46 / 17.30 / 17.50 |
| SARIF findings | 2 / 0 / 2 | 2 / 2 / 2 |
| rc | 254 | 254 |

Two columns separate cleanly:

- **Absorptions rise 35–250×**, and the ranges do not overlap. Every earlier `L = 100` arm in this
  document sits in the 15 k–90 k band; the re-score arms are 2.7 M–5.1 M.
- **Progress rises about 12 %** on the means, 823 k → 937 k, and the ranges do not overlap.

Two do not: `resultNodes` and `pointsPerCall` overlap between arms, so on three replicates the
re-score **does not reduce the graft's node mass** — the same conservation every other lever in this
document ran into. What it buys is throughput at unchanged mass, which is a different and smaller
claim than the design hoped for.

The cost is nothing: **9 re-scores, 613 states visited, 84 demotions** across a whole run.

### 13.4 What it does not do

No arm converges; every one still stops on the IFDS timeout at rc 254. 84 demotions turning 75 k
absorptions into 2.7 M is the mechanism working as designed, and it moves the throughput needle by
12 % — against a workload that needs a factor of several. The ceiling of §12.5 stands: about a third
of declines are movable, and the rest are self-loops and missing edges that no kind policy reaches.

## 14. The investigation re-run with the re-score on

Everything above was measured with the shipped policy. This section repeats the three questions —
which methods hold the premises, where their facts come from, and what the biggest fact looks like —
at `L = 100` with `-Dopentaint.anyUnrollKindPolicy=rescore`, and answers the standing question for
the biggest fact: **why is it not absorbed?**

### 14.1 Premises

**49,749 over 14,696 methods**, against 54,169 without the re-score.

| # | premises | of which carry `[any]` | method | without re-score |
|---|---|---|---|---|
| 1 | **4,684** | **152** | `WorkflowExecutorOps#decide(WorkflowModel)` | 6,537 / any 9 |
| 2 | 1,464 | 117 | `DoWhile#execute(WorkflowModel, TaskModel, WorkflowExecutor)` | 1,548 / any 17 |
| 3 | 1,078 | 61 | `WorkflowExecutorOps#terminateWorkflow` | 1,241 / any 4 |
| 4 | 1,054 | 78 | `WorkflowExecutorOps#terminate` | 1,263 / any 7 |
| 5 | 973 | 13 | `virtual Stream#map` (914 identity) | 966 |
| 6 | 907 | 4 | `WorkflowExecutorOps#rerunWF` | 1,882 |

The cast is unchanged, the counts fall 8 % overall and 28 % at the top — and the `[any]`-carrying
column rises **17×** at `decide`. That is the mechanism visible in the storage: the re-score converts
concrete enumerations into the wildcard they were enumerating. `decide`'s link histogram loses its
peak, `2,066 → 835` premises of five links.

### 14.2 Where the facts come from — the same inversion, sharper

| method | base | `added` | `adds` | `emits` | arrivals any/concrete | delta nodes any/concrete |
|---|---|---|---|---|---|---|
| `decide(WorkflowModel)` | **arg(0)** | **328** | 324 | **4,592** | 32 / 169 | 69 / 258 |
| `terminateWorkflow` | arg(0) | 334 | 393 | 1,561 | 54 / 208 | 75 / 258 |
| `rerunWF` | `<static>` | 1,859 | 773 | 2,397 | 10 / 177 | 795 / 1,064 |
| **`terminate`** | **`<this>`** | **26,189** | 2,742 | **16** | 30 / 796 | **8,463 / 17,725** |
| `DoWhile#execute` | **arg(2)** | **25,005** | 1,993 | **16** | 21 / 642 | **7,899 / 17,105** |

A 328-node fact emits 4,592 premises; a 26,189-node fact emits 16. And in both huge rows, **3–4 % of
arrivals carry an `[any]` and deliver 32 % of the growth**.

### 14.3 The biggest fact, and why it is not absorbed

Target: `<this> @ WorkflowExecutorOps#terminate(WorkflowModel, TerminateWorkflowException)`, retained
in full — **40,262 nodes by multiplicity, 7,296 distinct, depth 115**.

**Where it comes from.** 1,169 arrivals, and **1,168 of them from one statement**:
`WorkflowExecutorOps.java:1271`, the `terminate(workflow, twe)` in `decide`'s
`catch (TerminateWorkflowException twe)`. 70.1 % of arrivals add no new distinct node. The two
biggest arrivals bring 11,575 and 20,027 nodes already assembled, rooted at
`.metadataMapperService.metadataDAO.conductorProperties.stack.[any]` and
`.stack.buffer.Element.[any]` — §4.2's `String` → `Object` erasure, still the spine.

**Why `<this>` is a big object at all.** `WorkflowExecutorOps` has 13 injected fields, five of them
interface-typed with 6, 6, 8, 2 and 2 implementations, plus `ExecutionDAO` with 5 behind the facade.
And there is **no field-level cycle** back to the executor — the recursion is at the **parameter**
level: `this` is passed out at five call sites (`:1216`, `:1393`, `:1740`, `:1958`, `:2030`) into
`WorkflowSystemTask.execute/start/cancel` over 21 implementations, and five of those call back
(`SubWorkflow` → `terminateWorkflow`, `DoWhile` → `scheduleNextIteration`, `StartWorkflow` →
`startWorkflow`, …). `terminate` sits on that loop twice.

**Why it is not absorbed — the exact answer.** The tree dump now annotates every `[any]`-owning node
with its manager state, kind and pot:

| | count | share |
|---|---|---|
| distinct nodes | 7,296 | |
| **own an `[any]` edge** | **6,570** | **90 %** |
| mean out-degree, `[any]`-owning | **4.96** (max 94) | |
| mean out-degree, others | 0.39 | |
| **distinct `[any]` states governing all 6,570** | **2** | |
| governed by `s731`, kind **`PAID`** | **6,544** | **99.6 %** |
| governed by `s536`, kind `CREDIT` | 26 | 0.4 % |
| pots involved | **`dag#106`, total 400, limit 100** | |

**One state, `s731`, governs 99.6 % of every `[any]` position in a 40,262-node fact, and it is
`PAID`.** So `writesAbove` declines every prepend above any of those 6,544 nodes and the fact keeps
every step it was ever given.

And `s731` is not a bystander — it is **the top decliner of the entire run**:

| state | kind / minted by | dag | pot | declines | share |
|---|---|---|---|---|---|
| **#731** | `PAID` / read | #106 | **400** | **8,598,933** | **46.1 %** |
| #732 | `PAID` / read | #106 | **400** | 8,503,102 | 45.6 % |
| #509 | `PAID` / unroll | #106 | 400 | 1,207,186 | 6.5 % |

Two states are 91.7 % of all 18.6 M declines, and one of them is the state this fact is made of.

**And the re-score ran.** Nine times, 601 states visited, **103 demoted** — and it kept `s731` `PAID`.
That is not a bug in the implementation; it is what breadth-first from the root *means*. `s731` is
shallow, so the BFS reaches it while the budget is still intact and spends the budget on it. **The
states nearest the origin are the ones that govern the most facts, and BFS-from-root is exactly the
order that protects them.**

The cost model is the reason: the re-score charges `pathCount`, which counts paths **in the
automaton**. It has no way to see that `s731` governs 6,544 nodes of one fact and declines 8.6 M
prepends, while a sibling governing one node costs the same. A re-score weighted by governed
population — for which the decline count is a ready proxy — would demote `s731` first rather than
last.

### 14.4 The standing question, as a recipe

For any large fact, the three numbers that answer "why was this not absorbed" are now on one line of
the tree dump:

1. **How many of its nodes own an `[any]`** — 90 % here; if low, the fact is not an `[any]` structure
   and the manager is not the relevant instrument.
2. **How many distinct states govern them** — 2 here. A small number means one kind decision decides
   the whole fact.
3. **The kind of the governing state, and its pot** — `PAID`, `dag#106` at 400 against a limit of
   100. `PAID` with a pot over the limit is the diagnostic signature of a state the re-score chose to
   protect.

## 15. Caveats

- **Volume counters move a lot.** Across five star replicates of the same build and arm,
  `B-getChildAny calls` spans 133 k–706 k and `concatAnyDelta` spans 4 %–29 % of concat calls. Ranges
  are quoted throughout for that reason. The structural ratios are stable: graft points per call
  12.6–17.2 across all five, 1.91–2.32 across all three controls.
- **No arm converges.** The star arms all stop on the IFDS timeout with work outstanding, so every
  total is "what was produced in 300 s", not a fixed point. The control is the only converging arm
  and it is a different program.
- **The empty-path filter hole is not the differentiator.** It is present, and larger in proportion,
  in the converging control. What §5.2 licenses is "half the mass is untyped", not "the missing type
  check causes the explosion".
- **`.stack.buffer`'s writer is inferred, not observed.** The targeted ladder shows the edge already
  present in an incoming premise at arrival #7, attributed to no call site. §5.1 gives the mechanism
  that can build it; a stack capture at the moment of construction would pin which of
  `filterStartsWith`'s fold and the concat graft actually did.
- **Scoping the entry point does not scope the sources** — `WorkflowTestService#testWorkflow` is
  5.5–18.8 % of the graft mass and is not reachable from `rerun`. It is a source in its own right.
- **Premises are minted at the method exit, so they have no call site.** All 4,000 traced premises
  of `decide` report `no-call-site`, and every captured stack is the same:
  `NormalMethodAnalyzer.flushPendingSummaryEdges` (`MethodAnalyzer.kt:734`) ←
  `tabulationAlgorithmStep`. The trace therefore says WHAT each premise spells and in what order they
  appeared, not which caller asked for it; §8.2's ladder is what supplies the caller.
- **`decide`'s premise count is the one number that moved between the two premise runs** — 6,537 and
  6,356 — which is within the run-to-run spread of everything else here.
- **§9's arrival split counts nodes at merge time, not residency.** `addedDelta` is
  `after.size - before.size` per arrival, so it double-counts nothing but says nothing about what
  survives interning either.
- **§9.2's out-degree is one retained tree.** It is the largest one the run kept, 538 distinct nodes;
  the profile lines of §9.1 corroborate the share of `[any]`-owning nodes across five more trees, but
  the fan-out ratio itself is a single sample.
- **§10.5 compares four different trees.** Each arm retains its own largest `added`, so the rows are
  not the same object seen under four settings. What the table licenses is that the fan-out never
  leaves the 8–15 band, not a per-tree delta.
- **`mints` counts origins, not transitions.** `mints = 195` at `L = 100` is the number of `[any]`
  origins created; the per-transition mint does not touch that counter, which is why `transitions`
  (601) is the number to compare against `reads`.
- **§11's counterfactual is a probe, not a simulation.** It asks where each declined prepend *would*
  have landed given the automaton as it stands at that moment. Absorbing for real would change both
  the automaton and the facts, so the 32 % is an upper bound on reachable structure, not a prediction
  of what a rerun with the gate open would produce.
- **`wouldStay` drew no verbatim sample.** The 40-slot sample map filled with `noPredecessor` and
  `wouldMove` keys before the first self-loop arrived, so §11.2's shapes cover two of the three
  outcomes; the counts cover all three.
- **§12.5's movable fraction is unstable across runs** — 31.4 %, 32.0 % and 5.3 % on three arms with
  decline counts of 8.3 M, 11.1 M and 18.1 M. The ordering (self-loops ≫ movable) holds in all three;
  the ratio does not.
- **`alwaysCredit` and `global` are experiments, not proposals.** `budgetExhausted`, which governs the
  unroll, stays on the per-dag rule in every arm, so the arms differ in kind assignment alone — which
  is what makes §12.3's reading valid, and also what makes them silent about the unroll's own budget.
- **§13.3's two clean separations are three replicates each**, which is enough to separate
  non-overlapping ranges and not enough to put a confidence interval on the 12 %.
- **The re-score is behind a flag and off by default.** It changes kinds after facts have been built
  with the old ones; the design's argument that a state changes kind at most twice no longer holds,
  and the doubling threshold is what replaces it. That trade has not been re-derived, only bounded.
- **§14.3's fact is one retained tree from one run.** The concentration it shows — 90 % `[any]`-owning,
  two governing states, one of them `PAID` — is corroborated by the run-wide decline census, where the
  same two states are 91.7 % of all declines, but the tree itself is a single sample.
- **§14.1's `[any]`-carrying premise column is the clearest signal the re-score works**, and it is one
  run against one run. The absorption and throughput separations of §13.3 are the replicated claims.

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

**A node that owns an `[any]` has 7.1× the fan-out of one that does not.** That is the mechanism in
one number. `AccessNode.getChild`'s `isCoveredByAny` arm answers *every* field read off such a node —
`isCoveredByAny` is `true` for every `FieldAccessor` in production (`TaintAnalyzer.kt:75-77`) — with
no type check (§5.1). So the node accumulates a child per accessor anyone ever demands, which is
exactly §4.2's `.buffer` node with 17 children from 12 unrelated classes. Path count is the product
of out-degrees along a path: 538 nodes, 22,211 paths.

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

## 10. Caveats

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

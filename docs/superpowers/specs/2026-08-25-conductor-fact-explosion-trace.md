# One endpoint, one rule, 8 GB: tracing conductor's fact explosion to the statement

Branch `saloed/31-any-unroll-manager-design`. Follow-up to
`2026-08-25-any-unroll-manager-results.md`, which established that the `[any]` unroll manager
"bounds a mechanism conductor barely uses" and left the real driver unnamed. This document names it,
end to end, with a per-arrival trace carrying **line numbers of the analysed program**.

**The finding in one line:** a **3-node** fact — `arg(1).[any]![spring-source].$`, submitted **once** —
emits **42,074 summary premises**, and the concrete facts answering them accumulate into 269
`(method, base)` trees totalling 9.75 M nodes, of which 99% sit below an edge whose declared field
type is `java.lang.Object`, where the type filter rejects nothing by construction.

---

## 1. The configuration

Everything below is **one Spring handler and one taint rule** on conductor, with conductor's own
passthrough models and compiled approximations, `-Xmx8g`, IFDS budget 300 s.

| | |
|---|---|
| entry point | `com.netflix.conductor.rest.controllers.WorkflowResource#rerun(String, RerunWorkflowRequest)` — **1 of 107** Spring handlers |
| rule | `graaljs-polyglot-code-injection`: source `spring-untrusted-data-source`, sink `graalvm-polyglot-eval` (the 3-file `single-rule` set) |
| result | **`rc=253` — low-memory stop. 8 GB exhausted, 3 units still unfinished, 2 findings.** |

### 1.1 Two harness defects had to be fixed before this was even possible

Both are worth recording because they silently invalidate any "single entry point" claim.

**(a) `--debug-run-analysis-on-selected-entry-points` cannot restrict a Spring project, and fails
open.** `ProjectEntryPointsSelector.kt:14-18` appends `springEp` **unconditionally**:

```kotlin
val springEp = springWebProjectContext?.springWebProjectEntryPoints().orEmpty()
return when (projectKind) {
    ProjectKind.UNKNOWN -> allProjectEntryPoints(options) + springEp
```

`springWebProjectEntryPoints()` returns the synthetic `__spring_dispatcher__`, which fans out to
every controller. The selector filters only the *non*-Spring pool — and even there it is broken:

```kotlin
val (clsName, methodName) = debugEp.split('#')
return allMethods.filter { it.name == methodName && it.enclosingClass.name == clsName }
```

`it.name` is a bare method name, so **any selector carrying a parameter list matches nothing at
all**. The previously recorded "single-entry-point conductor witness" was in fact running the whole
Spring surface; I re-ran it and confirmed the non-Spring branch contributed zero.

Fixed for this investigation with a diagnostic knob that restricts the handler set where it is
built (`SpringWebProject.kt`, `createSpringProjectContext`):

```
-Dopentaint.springEpFilter=com.netflix.conductor.rest.controllers.WorkflowResource#rerun
→ Spring entry point filter '...#rerun': 1 of 107 handlers kept
```

**(b) Restricting entry points does not restrict taint sources.** A source rule is a *position* rule
attached to a method, not to an entry point. With one entry point, four handlers still fire as
sources — `rerun`, `testWorkflow`, `executeWorkflow`, `startWorkflow` — because the analysis reaches
them as ordinary methods. Both SARIF findings' flows in fact begin at `WorkflowResource.java:101`
(`executeWorkflow`) and `:444` (`testWorkflow`), not at `rerun`. The scoping is a ~25× cut in source
surface, not a reduction to one.

### 1.2 The instrument

`TifaDiagnostics` records `added` per `(method entry point, access-path base)` but only above 5,000
nodes, so its ladder could only ever show the *tail* of an explosion. Three additions:

| knob | what |
|---|---|
| `-Dopentaint.tifaTrace=<substring of the key>` | every arrival from the **seed**, numbered, with `size`/`distinct`/`depth` before and after |
| (always on with `tifaDiag`) | `SEED` — the first fact ever to arrive at *every* base, one string, affordable everywhere |
| `-Dopentaint.tifaLongLabels=true` | render field edges as `.name {declaringClass : fieldType}` instead of `.name` |

Arrivals are attributed to a **line of the analysed program**. The call statement is the only object
on the path that names one, and the abstraction cannot reach it, so `MethodAnalyzer.callStatementStep`
parks it in a thread local and the arrival reads it back (`finally`-cleared, so an arrival raised
outside a call step is attributed to nothing rather than to a stale statement).

Gate: **3,433 tests, 2 failures**, both pre-existing (see §6.1 — they are themselves evidence).

---

## 2. The control that settles causality

Same jar, same entry point, same sink, same approximations. The **only** change is
`$*UNTRUSTED` → `$UNTRUSTED` in the source rule — the star, which is what emits `[any]`.

| | star (`$*UNTRUSTED`) | no star (`$UNTRUSTED`) |
|---|---:|---:|
| exit | **253 — out of memory** | **0 — converged** |
| wall | 211.8 s | **38.6 s** |
| IFDS phase | 2 m 53 s | **3.5 s** |
| progress | 2,128,893, **5 units left** | 188,054, **0 left** |
| `addCalls` | 2,416,937 | 107,676 |
| `walkStates` | 45,156,182 | **111,622** (404×) |
| `anyDescents` | 11,621,844 | **0** |
| findings | 2 | **0** |

The star is the switch. It is also **load-bearing for both findings** — the same dichotomy this
codebase keeps running into, and the reason "just drop the star" is not a free win.

---

## 3. The trace, hop by hop

Facts below are verbatim `SEED` lines from the run; `added` and `emits` are that base's totals.

```java
// hop 0 — the source. WorkflowResource.java:309-315
@PostMapping(value = "/{workflowId}/rerun", produces = TEXT_PLAIN_VALUE)
public String rerun(@PathVariable("workflowId") String workflowId,
                    @RequestBody RerunWorkflowRequest request) {
    return workflowService.rerunWorkflow(workflowId, request);   // :314
}
```

`spring-untrusted-data-source` matches `$TYPE $*UNTRUSTED` on **both** parameters. `StarredPosition.bases()`
turns each star into two positions, so each parameter is seeded with `arg(i)![mark]` **and**
`arg(i).[any]![mark]`.

| # | base @ method | seed fact | `added` | `emits` |
|---|---|---|---:|---:|
| 1 | `arg(1) @ WorkflowServiceImpl#rerunWorkflow` | `.[any]![graaljs…#spring-source].$` | **3** | **42,074** |
| 1' | `arg(0) @ WorkflowServiceImpl#rerunWorkflow` | `.[any]![…].$` | 3 | 1 |
| 2 | `arg(0) @ WorkflowExecutorOps#rerun` | `/*` | 2,652 | 2,935 |
| 3 | `arg(2) @ WorkflowExecutorOps#rerunWF` (`taskInput`) | `/*` | 2,645 | 2,761 |
| 3' | `arg(3) @ WorkflowExecutorOps#rerunWF` (`workflowInput`) | `/*` | 3 | 3 |
| 4 | **`<this> @ WorkflowExecutorOps#rerunWF`** | `/*`, from `rerun:163` | **56,108** | 14 |

Hop 1 is the entire story in one row. **A three-node fact, submitted exactly once (`adds: 1`),
emits 42,074 premises.** It is not big; it *denotes* an unbounded language, and the walk enumerates it.

The two larger siblings behave identically:

| emits | `added` | `adds` | base @ method |
|---:|---:|---:|---|
| **58,613** | **3** | **1** | `arg(0) @ WorkflowTestService#testWorkflow(WorkflowTestRequest)` |
| 56,914 | 3,946 | 3,948 | `arg(0) @ WorkflowServiceImpl#startWorkflow(StartWorkflowRequest)` |
| **42,074** | **3** | **1** | `arg(1) @ WorkflowServiceImpl#rerunWorkflow(String, RerunWorkflowRequest)` |

Across the whole run, **233 of 11,226 bases carry an `[any]`. They hold 147,208 of 9,751,301 nodes
(1.5%) and produce 47% of every premise emitted.** `[any]` bases are microscopic and enormously
productive; the giant trees are downstream sediment.

The tainted values reach the model by ordinary stores, none of which are surprising:

```java
// WorkflowServiceImpl.java:288 — merges both source parameters into ONE object
request.setReRunFromWorkflowId(workflowId);

// WorkflowExecutorOps.java:1861 (and :1912) — stores the attacker's Map BY REFERENCE
if (workflowInput != null) { workflow.setInput(workflowInput); }
// WorkflowModel.java:192-198: `this.input = input;` — no defensive copy
```

---

## 4. Where the mass is: the census

Full per-base census, one endpoint, one rule (`-Dopentaint.tifaTop=20000`):

| | bases | share | accumulated nodes | share | largest |
|---|---:|---:|---:|---:|---:|
| `<static>` | 4,224 | 37% | 4,576,808 | **46%** | 92,850 |
| `<this>` | 3,836 | 34% | 1,457,310 | 14% | **157,892** |
| `arg(i)` | 3,166 | 28% | 3,717,183 | 38% | 114,596 |
| **total** | **11,226** | | **9,751,301** | | |

- **269 bases (2.4%) hold 95% of it.**
- **147 distinct methods each hold a ≥5,000-node `<static>` tree**, totalling 4.44 M nodes.
- Only **233 of 11,226** accumulators ever carried an `[any]`.

The 147 include `WorkflowModel#getWorkflowName()` (53,361 nodes), `WorkflowContext#get()`,
`Monitors#recordWorkflowStartError(String, String)` — trivial getters and metrics calls, each holding
a five-figure copy of one tree. Its ladder: 3,922 arrivals, **3,921 of them with no call site at
all** — they arrive cross-unit, not through `callStatementStep`.

---

## 5. The exact statement

`<this> @ WorkflowExecutorOps#rerunWF`, full ladder from the seed, 10,381 arrivals recorded:

| arrivals | attributed to |
|---:|---|
| **10,218 (98.4%)** | `WorkflowExecutorOps.java:1891` |
| 155 (1.5%) | `WorkflowExecutorOps.java:163` |

```java
// WorkflowExecutorOps.java:1886-1895 — line 1891 is the recursive self-call
// If not found look into sub workflows
if (rerunFromTask == null) {
    for (TaskModel task : workflow.getTasks()) {
        if (task.getTaskType().equalsIgnoreCase(TaskType.TASK_TYPE_SUB_WORKFLOW)) {
            String subWorkflowId = task.getSubWorkflowId();
            if (rerunWF(subWorkflowId, taskId, taskInput, null, null)) {     // <-- 1891
```

`rerunWF` calls itself, so `JIRMethodCallFactMapper.mapMethodCallToStartFlowFact`'s
`instanceBase == factBase` arm re-submits **every** `<this>`-rooted fact of `rerunWF` as an initial
fact of `rerunWF`. The accumulator feeds itself, and `mergeAddDelta(foldToAny = false)` has no
widening, so the loop is a monotone climb with no fixed point short of the whole field universe.

The shape of the climb:

| arrival | `size` | distinct | depth |
|---:|---:|---:|---:|
| #0 | 17 | 10 | 5 |
| #500 | 3,172 | 374 | 12 |
| #1000 | 10,339 | 391 | **13** |
| #2000 | 22,740 | 726 | 13 |
| #4000 | 53,491 | 1,499 | 13 |
| #5999 | 62,871 | 1,631 | 13 |

(the ladder caps at 6,000 arrivals; the base finishes at 78,728.)

Two things to read off it. **Depth saturates at 13 by arrival #1000 and never moves again — this is
breadth, not depth.** And **75% of arrivals add zero new distinct nodes**: three quarters of the
10,218 re-deliveries are pure re-merge cost.

Line 1891 is not a bug in conductor. It is the busiest carrier, and it is what turns a global
enumeration into a self-feeding loop on one accumulator.

---

## 6. Why the tree can grow at all — three amplifiers

### 6.1 `java.lang.Object` erases the type filter, and 99% of the tree is below one

The `[any]` unroll asks `JIRFactTypeChecker.accessPathFilter` whether a candidate field may follow a
prefix, and the answer comes from the *declared field type of the prefix's last accessor*
(`accessorActualType`, `JIRFactTypeChecker.kt:193-208`). When that type is `java.lang.Object`:

```kotlin
// JIRFactTypeChecker.kt:260-262
fun typeMayHaveSubtypeOf(typeName: String, requiredTypeName: String): Boolean {
    if (requiredTypeName == "java.lang.Object") return true
    if (typeName == "java.lang.Object") return true
```

Every field in the program is admissible. Not an approximation that usually holds — an
unconditional `return true`.

Measured on the largest `<this>` tree (`-Dopentaint.tifaLongLabels=true`, 3,125 nodes / 62,069 edges
/ 43 declaring classes):

| | |
|---|---:|
| field edges whose declared type is `java.lang.Object` | **9,266 of 61,148 (15%)** |
| distinct nodes reached directly by one | 1,217 |
| **nodes reachable from one** | **3,113 of 3,125 (99.6%)** |
| `.[any]` edges in the tree | **0** |

The erasing accessors, by frequency:

```
859  .<serialized-value> {java.lang.String            : java.lang.Object}
770  .MapKey            {java.util.Map                : java.lang.Object}
736  .Element           {java.util.Optional           : java.lang.Object}
644  .headerValues      {org.springframework.http.HttpHeaders : java.lang.Object}
622  .headerValue       {org.springframework.http.HttpHeaders : java.lang.Object}
593  .buffer            {java.io.ByteArrayOutputStream: java.lang.Object}
566  .<get-default>     {java.lang.Object             : java.lang.Object}
394  .body              {HttpTask$Input               : java.lang.Object}
394  .key / .value      {KafkaPublishTask$Input       : java.lang.Object}
394  .message           {java.lang.Throwable          : java.lang.Object}
```

Three of these are **modelled**, not real: `.java.util.Map#MapValue#java.lang.Object` and
`#MapKey#…` come from `model/java/config/*.yaml`, and
`.java.lang.String#<serialized-value>#java.lang.Object` comes from the Jackson / snakeyaml / fastjson
deserialization models. The last one attaches an `Object`-typed child to **every tainted String** in
the program, and conductor's model classes are mostly Strings.

That is why the tree wanders into `org.apache.http.HeaderIterator`,
`org.apache.commons.lang3.text.StrTokenizer` and `java.io.ByteArrayOutputStream` — 18 of the 43
declaring classes are non-conductor, contributing 7,905 edges. Three links from the root:

```
n1  .lock         {ExecutionLockService : com.netflix.conductor.core.sync.Lock}
n2  .heldByThread {PostgresLockDAO      : java.lang.ThreadLocal}
n3  .value        {java.lang.ThreadLocal: java.lang.Object}      <-- erased here
n4  .MapValue     {java.util.Map        : java.lang.Object}
```

**Independent corroboration.** The untracked test file
`core/opentaint-dataflow-core/opentaint-jvm-dataflow/src/test/kotlin/.../JIRFactTypeCheckerUnrollFilterTest.kt`
already pins this, in its own KDoc — *"Every field modifier emitted by `model/java/config` declares
`java.lang.Object` as that type, so these tests pin what the filter can still reject once a path has
crossed one modelled field."* Its `concrete field type rejects an unrelated field` passes; its two
`Object`-typed cases **fail**, at HEAD and on this branch alike. They are the two failures in every
gate run on this branch. The engine does not have the behaviour that test asks for, and §6.1 is the
workload-scale consequence.

### 6.2 All static state is one access-path base, broadcast into every callee

```kotlin
// Accessors.kt:33
data object ClassStatic : AccessPathBase
```

A **singleton**. Every class's statics share one root, selected by `ClassStaticAccessor(typeName)`.
Conductor's biggest tree is rooted there:

```
n0*
    <static>(__spring_registry__)                                    => n1
    <static>(com.netflix.conductor.core.events.ScriptEvaluator)      => n2716
    <static>(com.netflix.conductor.contribs.queue.amqp.AMQPConnection) => n2726
n1*
    .com.netflix.conductor.dao.ExecutionDAO        => n2
    .com.netflix.conductor.dao.PollDataDAO         => n308
    .com.netflix.conductor.service.WorkflowService => n311
    .com.netflix.conductor.redis.jedis.JedisCommands => n1518
    .com.netflix.conductor.core.execution.WorkflowExecutor => n2714
```

`__spring_registry__` is the analyzer's own synthetic class with **one static field per Spring bean**,
named after the bean's type (`SpringWebProject.kt`, `addComponent`). Dependency injection is modelled
as a read from it. So every bean, and everything reachable from every bean, hangs off a single
access-path root — the DI graph is one object.

And that root is copied into every callee unconditionally:

```kotlin
// JIRMethodCallFactMapper.kt:217-221
val factBase = factAp.base
if (factBase is AccessPathBase.ClassStatic) {
    onMappedFact(factAp, factBase)
}
```

No reachability test, no test that the callee touches statics at all. That is why 147 methods —
including `WorkflowModel#getWorkflowName()` — each hold a five-figure copy.

### 6.3 The model SCC, and `foldToAny = false`

`WorkflowModel.tasks : List<TaskModel>` → `TaskModel.workflowTask : WorkflowTask` →
`WorkflowTask.subWorkflowParam : SubWorkflowParams` → `workflowDefinition` → `WorkflowDef.tasks` → …
a type-level cycle. `limitFieldAccess` forbids `f.f` on a path but not `f.g.h`, so every permutation
of distinct fields within the cycle is a separate path. The label histogram is the signature: the
same field at 776–1,613 distinct positions each (`.externalInputPayloadStoragePath` 1,613,
`.status` 1,557, `.reasonForIncompletion` 1,548 …), from only 130 distinct labels.

`TreeInitialFactAbstraction` is the only place in the engine that passes `foldToAny = false`
(deliberately, `aba23d6a6`), so nothing folds a concrete branch into an `[any]` that already denotes
it. This is correct and must not be "fixed": `added` has to remember concrete arrivals or the walk
stops emitting their premises.

---

## 7. Corrections to the earlier write-up

`2026-08-25-any-unroll-manager-results.md` §4.4 said whole trees are *transplanted* by
`mapMethodCallToStartFlowFact` on `argBase == factBase`. Half right, and the wrong half matters:
the mapper is a **fact-count fan-out**, not a tree-growth operation. `AccessTree.rebase` shares the
`AccessNode` by reference, so `f(x, x, x)` emits three facts carrying one physical tree and adds zero
nodes. The N facts then land in N *different* base buckets and do not compound each other.

It also identified `WorkflowExecutorOps.this` as the god object. At single-endpoint scope the god
object is `<static>` — the Spring bean registry — which is larger (46% of all nodes), and which the
mapper really does broadcast unconditionally.

And the largest trees carry **no `[any]` at all** (0 of 62,069 edges). `[any]` is upstream: it
manufactures the concrete accessors that fill them. Any instrument that looks for `[any]` inside the
big trees will find none and conclude, wrongly, that `[any]` is not involved.

---

## 8. What this does and does not establish

**Established.**
- The star is the switch: converge in 38.6 s vs. 8 GB exhausted, everything else identical.
- One endpoint + one rule ⇒ 11,226 accumulators, 9.75 M nodes, 269 of them holding 95%.
- 98.4% of the growth of the largest `<this>` accumulator enters at `WorkflowExecutorOps.java:1891`.
- 99.6% of that tree lies below a `java.lang.Object`-typed edge, where the filter cannot reject.
- 233 `[any]`-carrying bases (1.5% of nodes) emit 47% of all premises; one 3-node fact emits 58,613.

**Not established.**
- **Whether fixing §6.1 preserves findings.** Every reduction attempt in this codebase so far has
  been sound-but-lossy or lossless-but-useless. `Map<String,Object>` genuinely can hold anything, so
  the `MapValue : Object` edge is *sound*; `String#<serialized-value> : Object` is the more
  questionable one and is the cheaper thing to test first. Not run.
- **Whether the `ClassStatic` broadcast can be narrowed.** A cheap test — deliver a `ClassStatic`
  fact only to callees that transitively read a static — is not written, and the trace resolver may
  depend on the unconditional arm.
- **Why 3,921 of 3,922 arrivals at a `<static>` base have no call site.** They arrive cross-unit; the
  path was not traced.
- Single samples throughout; no run-to-run variance measured. `foreign_overlap_pct` is 0 for every
  run quoted here except the first (35%), which is used only for orientation.

## 9. Reproduction

```bash
S=<scratchpad>
# jar: TifaDiagnostics seed + targeted ladder + long labels, and the Spring EP filter
bash $S/buildjar.sh trace4

# the exploding arm, with the full ladder for one base
bash $S/run2.sh w3-ladder $S/jars/trace4-*.jar \
  -Dopentaint.tifaDiag=true -Dopentaint.tifaTop=120 \
  '-Dopentaint.tifaTrace=@ com.netflix.conductor.core.execution.WorkflowExecutorOps#rerunWF'

# the control: identical but the source rule's star removed
RULES=$S/ruleset-nostar bash $S/run2.sh w4-nostar $S/jars/trace4-*.jar -Dopentaint.tifaDiag=true
```

`run2.sh` pins the handler with `-Dopentaint.springEpFilter` and uses the 3-file `single-rule` set.
Output prefixes in `console.log`: `TIFA` (census + seeds), `TIFATREE` (largest tree),
`TIFATRACE` (the targeted ladder).

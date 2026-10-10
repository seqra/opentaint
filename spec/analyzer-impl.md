# Analyzer core — implementation proposal

Status: implementation proposal for phase 2 of [bidirectional-task.md](../bidirectional-task.md), through F71. It implements
[`analyzer-core.md`](analyzer-core.md). The spec is normative, and this document does not change it. This document uses
the types of [`ap-impl.md`](ap-impl.md) with the names and the signatures that §2.2 lists. It does not define them
again. JVM only.

The normative spec now includes F72 with the F75 cleaner correction. The general proofs and restricted-run migration of this proposal are pending (`ap.md` §11.2).
The order is spec, proofs, then proposals. The code, invariants and tests below use the concrete restricted runs of F71.
The reference oracle uses F71 with the included local F75 cleaner (`ap-impl.md` §6); migrate its restricted-run rules and the engine together after the general F72 proofs.
The local F74 field-cleaner form and F75 selected-mark primitive are included after their local Lean checks (`ap.md` §10.13).
The F72 restricted-run migration remains pending.

Scope: the packages `org.opentaint.dataflow.bidi.engine`, `org.opentaint.dataflow.bidi.driver` and
`org.opentaint.dataflow.jvm.bidi`; the entities, the method analyzer, the pipeline, the scheduling, the driver, the
hand-offs, the confirmation; the interface of phase 3 (the trace resolution of phase 5 is out of scope, §8.2); the test plan.

Language: ASD-STE100 Simplified Technical English. Code first.

---

## 0. Conventions and design decisions

### 0.1 Conventions

| # | Convention |
|---|---|
| C1 | A bare `§n`, in the text and in the code, is a section of this document. A section of another document has the name of that document: `analyzer-core.md` §4.7, `ap-impl.md` §7.3. Exception: in a table column whose header names a document, `§n` is a section of that document. `ap-impl.md` has Part I in §0 to §8 and Part II in §20 to §34. |
| C2 | The rule ids O1–O5, E-1–E-3, P1–P6, Q1–Q4, W1–W3 and B1–B4 are those of `analyzer-core.md`. So a bare W1, W2 or W3 is a rule of the `Work` event (`analyzer-core.md` §6.2). E1–E7 are the events of `ap.md` §5.3. An id of another document has the name of that document: `ap.md` W3 (the field-limit invariant), `ap.md` W6, `interpreter.md` AC4. The ids DD1–DD13 (§0.2) and C1–C3 are local to this document: `ap-impl.md` has its own DD ids, and `ap.md` has its own C ids. |
| C3 | A path of today's code is relative to the repository root, with the abbreviations below. `path:n` is line `n` of that file. A bare `:n` is line `n` of the file that the table row or the enclosing code names. |

| Name | Path |
|---|---|
| `CORE` | `core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow` |
| `JVM` | `core/opentaint-dataflow-core/opentaint-jvm-dataflow/src/main/kotlin/org/opentaint/dataflow/jvm` |
| `SAST` | `core/opentaint-jvm-sast-dataflow/src/main/kotlin/org/opentaint` |
| `TEST` | `core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow` |

### 0.2 Design decisions

| # | Decision | Reason | Code |
|---|---|---|---|
| DD1 | The new code is in the Gradle modules of today's core (`opentaint-dataflow`, `opentaint-jvm-dataflow`), in new packages (`bidi.*`, `jvm.bidi`). | The new core uses many `internal` declarations and utilities of these modules. The old core stays unchanged, because the prescan runs it. | §1 |
| DD2 | The worklist item is the edge delta `EdgeDelta(premise, node, facts)`. `facts` is one of the three kinds of `ap.md` §7.2 (`Reach`, `FlowTree`, `TaintTree`) and holds the layer. There is no `Edge` class (`ZeroToZero`, `ZeroToFact`, `FactToFact`, `NDFactToFact`): the premise key and the kind replace it. | `analyzer-core.md` §4.3: an item is (premise key, layer, node, conclusions). | §4.1 |
| DD3 | The added facts of one link key (`CallerRef`, link layer, kind, base, and for FLOW the exclusion and the mark exclusion) are ONE `Facts` group in callee coordinates. Its leaves are the added facts. `add` returns the delta: the new links. `LinkIn`, `RunnerPort.link` and `Subscription` carry such a group. The replay and the delivery take the part of the group that satisfies a premise with ONE function, `ApOps.satisfying`. | The tree form of `ap.md` §7. Today `MethodTreeAccessPathSubscription` keeps caller fact trees too. One function for the two paths is P4. | §4.2, §5.3; `ap-impl.md` §5.4, §7.5 |
| DD4 | The engine compares `Facts` by value (`equals` is structural for each kind). TERMINATION needs this in two places: the repeat test of `RuleWorklist` and the inputs of a conjunctive sink. The engine also uses it for the unchanged set, the parts of `NdSummaryJoin`, the AC4 split, the layers of a conjunction input and the record deduplication of the replay. | Each operation makes new objects, and each store has its own node interner (`ap-impl.md` §4.1, §4.5). | §4.3, §4.4, §4.6, §4.9, §5.3 |
| DD5 | A summary with several premises (E6) joins in the `ConjunctionStore` of the caller (`ndJoin`, `NdSummaryJoin`). The analyzer is a thin adapter. The pipeline encoding of this closure is `PipelineNDZ.sysDNz` (`clDNz_iff`; no zero subscription in a join: `clDNz_ndpub_zero_sub`). | `analyzer-core.md` §5.4: both sides of the join are in the caller. `ap-impl.md` §7.10 has the join. | §4.11 |
| DD6 | `MethodContextCache` holds the forms per METHOD KEY (`MethodForms`) and makes one `DirectedForms` per run. The engine has no forms cache of its own. | The call plans and the entry rules read the context of the key (§10 row 2). `ap-impl.md` §23.7, §31.2 cache each form and its reversal. | §3.4 |
| DD7 | The zero rules `zin`, `seed` and `zret` act only on the edge `{zero} → zero` (a REACH on `{zero}`). A backward edge `jb → zero` (a REACH on `{jb}`) only passes over a call. | Lean `Backward.lean:158-180`: these rules read only `{zero} → zero`. A zero rule on `jb → zero` makes a false backward summary, and `persist` makes it a record. | §4.10 |
| DD8 | The source-seed filter and the source hits act only at the source-seed places: a statement summary, `RuleStatement.summary` and a `SOURCES` stage. They never act on an end fact. | `analyzer-core.md` §4.7; `ap-impl.md` §23.1. An end fact has the shape of a source, but it applies as usual. | §4.3, §4.9 |
| DD9 | `JIRBidiAnalysis` uses the `JIRFactTypeChecker` of the prescan (`JIRAnalysisManager.factTypeChecker`). The bidi entry copies the reference before it releases the prescan state. | Its filters do not depend on its state (`ap-impl.md` §25). One instance keeps one set of statistics. | §8.1 |
| DD10 | The test oracle is `NaiveClosure`: the closure of one run, per path, with the guards of the engine. It applies the forms with `FormApplier` over the per-path `ReferenceAlgebra`, and a call plan with the per-path walk `FormsReference.run` and the guards of the engine (`ap-impl.md` §23.3, §23.8; DD12). The schedule fuzzer compares the engine with it. | `analyzer-core.md` §13 item 1: "the naive fixed point of the closure". | §9.2 |
| DD11 | THE KINDS ARE TYPES. The engine reads the kind of a `Facts` only where a rule of `ap.md` §7.2 depends on it: the zero rules on REACH, the requests from FLOW, no FLOW in a restricted run, entry marks on TAINT. Every other place passes `Facts` to an operation of `ap-impl.md` §5, which dispatches on the kind. | `ap.md` §7.2: the kind follows from the premise, and the types enforce `ap.md` W1, W2, W6 and W8 (the layer of a TAINT tree names its any leaves: `[any-taint]` in a normal tree, `[any]` in a demand tree; a normal TAINT tree carries one exclusion for its `[any-taint]` leaves, a demand tree none). | §4.1 (the table), §4.2, §4.3, §4.10, §7.3 |
| DD12 | ONE IMPLEMENTATION PER RULE PATTERN. From the other parts: `FormApplier` (the three application modes, generic over the fact algebra; `ap-impl.md` §23.3), which the engine runs over `EngineAlgebra` and `NaiveClosure` over `ReferenceAlgebra` (`ap-impl.md` §23.8); `StageKind.originOf` (the `Origin` rule, `ap-impl.md` §23.5); the per-path plan walk `FormsReference.run` of `NaiveClosure` (`ap-impl.md` §23.8); `StandingJoin` (requests × links; `ap-impl.md` §7.10). Here: `RuleWorklist` (the rule order of a boundary, start and end, both directions), `cut` (every field-limit cut, named by its `ap.md` §4.4 row), `forEachDemandPiece` (both hand-offs: the publications of the summary leaves that are not crossable, `ap-history.md` F70), `fromCallees`, `applyMatch`. | No rule is written twice, so a fix applies everywhere, and the test oracle shares the mode logic with the engine. | §4.3, §4.4, §4.6, §4.8, §5.3, §7.2, §9.2 |
| DD13 | THE TAIL `[any-taint]` (`ap.md` W8, S15; `ap-history.md` F69) IS AP DATA, AND ONLY FORWARD. The AP gives it: the target tail of a micro edge (the interpreter gives `ANY_TAINT` to a source with an `[any]` target, a pass rule keeps `ANY`), the layer of a TAINT tree (its any leaves are `[any-taint]` in a normal tree, `[any]` in a demand tree), the ONE exclusion `E` of the `[any-taint]` leaves of a normal TAINT tree (in its group key, as for FLOW), the exclusion rows, the emission (`emit`), the start fact, the satisfaction, the restriction, the sink check, the cut and the cleaner rows. The backward run has no `[any-taint]` (`ap.md` W8 (d)). The engine reads `Tail.ANY_TAINT` in four places only: the record demotion (`applyRecord`), the support link and condition 2 of the confirmation (`Support`), the asserts of `addInitial` (no must-premise in run 1 and in a backward run), and the hand-off to the backward run (`HandOff.toBackward`: an `[any-taint]/E` pattern becomes `[any]`). It passes the may of a micro edge (`MicroEdge.may`: the forward target `[any]`, or a reversed conjunction literal, `MicroEdge.conjunctive`, F70) to `applyEdge`, so a reversed pass rule and a reversed conjunction give demand results (`EngineAlgebra`). The premise key holds the tail and the exclusion, so the stores that the premise key keys need no other change. | `analyzer-core.md` §3, §4.3: "the core reads the target tail of the micro edge; it needs no other flag". One place per rule (DD12). | §4.1, §4.2, §4.3, §4.6, §7.2, §7.5 |

---

## 1. Package map

```
CORE/bidi/engine/                                     (opentaint-dataflow, language-neutral)
  RunConfig.kt            RunConfig: the constants of one run; its ApMode
  SharedObjects.kt        SharedObjects: the objects of the analysis lifetime; the thread pool
  RunManager.kt           RunManager: unit routing, runner spawn, summary storages, InFlight, status, scope, join
  RunStatus.kt            RunStatus, RunResult
  InFlight.kt             InFlight: the counter of one run (Q1–Q4)
  UnitRunner.kt           UnitRunner: the event loop of one unit; implements RunnerPort
  RunnerPort.kt           RunnerPort, SubscriptionPort, SummaryApplier, ProtocolSteps
  EventDispatch.kt        RunnerPort.handle(event): the handler of each event (UnitRunner and the fuzzer share it)
  EventQueue.kt           the local priority queue with fixed keys
  RunEvent.kt             RunEvent, EdgeDelta
  RunMethodAnalyzer.kt    RunMethodAnalyzer (one class, private members): state, handlers, the engine algebra
                          (EngineAlgebra), the field-limit cut (`Cut`), the rule worklist of a boundary, the call
                          plan runner, summaries, requests, sinks, seeds, E6
  DeltaWorklist.kt        the worklist of edge deltas: the `unchanged` queue with its set, the `normal` queue
  SummaryStorage.kt       SummaryStorage, PublicationIndex, Publication
  SubscriptionManager.kt  SubscriptionManager, CalleeSubscriptions, Subscription, matches
  MethodContextCache.kt   MethodContextCache, MethodContextSource, RunMethodContext
CORE/bidi/driver/
  IterationDriver.kt      IterationDriver, Next: the guarded loop, one run and its barrier (with the barrier guard), the stop rules
  IterationPolicy.kt      IterationPolicy, FixedLimits (tests)
  HandOff.kt              HandOff: forward → backward, backward → forward (the demand edges only, F70)
  Seeds.kt                Seed, SeedIndex
  Support.kt              Support: the supported premise sets, the confirmation
  Report.kt               Report, ReportState, ReportBuilder, AnalysisEnd, EndReason
  Frontier.kt             Frontier, DemandCause, frontierOf: the frontier log of each complete run (§7.8)
  BidiEntry.kt            BidiEntry: the phase-3 hook (§8.1)
CORE/ap/ifds/TaintAnalysisManager.kt                  GENERALIZE: releasePrescan() (§8.1)
CORE/ap/ifds/TaintAnalysisUnitRunnerManager.kt        GENERALIZE: releasePrescan() (§8.1)
JVM/bidi/                                             (opentaint-jvm-dataflow)
  JIRBidiAnalysis.kt      the phase-3 entry (a BidiEntry): the prescan values in, Report out
  JIRMethodContextCache.kt MethodContextSource over JIRMethodEntries (ap-impl.md §31.2)
JVM/ap/ifds/analysis/JIRAnalysisManager.kt            GENERALIZE: prescanRuleIds(), releasePrescan() (here), prescanLambdas() (ap-impl.md §31.1)
```

---

## 2. Reuse map and the names of the other documents

### 2.1 Reuse map

`analyzer-core.md` §8 gives the decisions. The kinds:

| Kind | Meaning |
|---|---|
| REUSE | Import today's class and call it as it is. |
| GENERALIZE | Make today's class generic (a type parameter, an extracted interface), so that the old core and the new core both use it. The old core keeps its behaviour, because the prescan runs it. |
| ADAPT | Copy the algorithm into a new class and change it. The row says what changes. |
| REPLACE | The new core does not use today's class. The new class does its work. |
| REMOVE | The new core has no such function. |

| Today (`path:line`) | Kind | New | What changes |
|---|---|---|---|
| `TaintAnalysisUnitRunnerManager` (`CORE/ap/ifds/TaintAnalysisUnitRunnerManager.kt:56`) | ADAPT | `RunManager` (§3.2, §6.4) | Keep: unit routing `getOrSpawnUnitRunner` (:435-440), runner spawn (:458-494), the counter protocol (:496-514 → `InFlight`), the phantom event (:147, :162), the timeout (:174-184), the memory guard (:113-118), the memory guard of the confirmation (:374-384, threshold `TRACE_GENERATION_MEMORY_THRESHOLD` :645: the barrier guard, §7.1), the progress log (:166-171, :562-570: the event counts and the memory usage; `RunManager.logProgress`). Remove: `resetApManager` (:127-136), delayed units (:516-529), the sticky `status` (:69), `methodDependencies` (:81), the trace and confirmation calls (:216-425), the language and per-method statistics of the progress log (:572-624). Add: `RunConfig`, one `SupervisorJob` scope per run, the join, the map of `SummaryStorage`s, the first end wins (`status.compareAndSet`). |
| `TaintAnalysisUnitRunnerManager` as the prescan engine (`CORE/ap/ifds/TaintAnalysisUnitRunnerManager.kt:71`, `:79-81`) | GENERALIZE | `releasePrescan()` (§8.1) | one new member: it drops the runners, the unit storages, `methodDependencies` and the AP manager of the prescan. The old core never calls it, so its behaviour does not change. |
| `AnalysisUnitRunnerManager` (`CORE/ap/ifds/AnalysisUnitRunnerManager.kt:10`) | REPLACE | `RunManager.route` | the unknown-unit drop (:41-42) stays |
| `TaintAnalysisUnitRunner` (`CORE/ap/ifds/TaintAnalysisUnitRunner.kt:29`) | ADAPT | `UnitRunner` (§6.1) | Keep: the channel (:75), the priority queue (:74), the loop (:193-263), the quantum `RUNNER_STEPS_QUANT` (:517), `yield`. Change: the events of §5.1; fixed priority keys (`EventComparator` :47-72 reads mutable keys); one `SubscriptionManager` (not :82-83). |
| `AnalysisRunner` (`CORE/ap/ifds/AnalysisRunner.kt:12`) | REPLACE | `RunnerPort` (§3.3) | |
| `MethodAnalyzerStorage` (`CORE/ap/ifds/MethodAnalyzerStorage.kt:8`) | REUSE the pattern | `UnitRunner.analyzers` (§3.3) | the pattern stays: one analyzer per method key, made on demand (:12-13, :15-36, :49-59). The table has one thread (its runner; the driver reads it after the join), so it is a plain `LinkedHashMap`: no `ConcurrentReadSafeObject2IntMap` (`ap-impl.md` §2: the new core does not use it). No `EmptyMethodContext` twin (:38-47) and no empty-method branch (:23-31). The old class stays unchanged for the prescan. |
| `NormalMethodAnalyzer` (`CORE/ap/ifds/MethodAnalyzer.kt:161`) | REPLACE | `RunMethodAnalyzer` (§4) | the patterns stay: `analyzerEnqueued` (:186) → `queued`; drain then flush (:307-317); the unchanged set (:188, :603-607) → the `unchanged` queue of `DeltaWorklist`; summary at an end node (:674-689) |
| `EmptyMethodAnalyzer` (`CORE/ap/ifds/MethodAnalyzer.kt:1395`) | REMOVE | — | an empty method is never analysed and never a callee (`analyzer-core.md` §4.4; `interpreter.md` D28): the call resolver drops it, and a call with no other callee is an unresolved call |
| the liveness check `isReachable` (`CORE/ap/ifds/MethodAnalyzer.kt:296`; `JIRLocalVariableReachability`) | REMOVE | — | the new core drops no fact on a dead local (`analyzer-core.md` §4.3; `ap-history.md` F67). The alias analysis keeps its own inputs, as today. |
| `TimedMethodAnalyzer` (`CORE/ap/ifds/MethodAnalyzer.kt:1581`) | ADAPT | — | not in phase 2: debug only (`DEBUG_ANALYSIS_TIME = false`, :1391); `analyzer-core.md` §8 makes it a decorator (§10 row 5) |
| `MethodAnalyzerEdges` (`CORE/ap/ifds/MethodAnalyzerEdges.kt:13`) | REUSE the structure | `MethodEdgeStore` | `ap-impl.md` §2, §7.3 |
| `AccessPathBaseStorage` (`CORE/ap/ifds/AccessPathBaseStorage.kt:5`) | REPLACE | `MethodEdgeStore` | NOT USED: it rejects the `Zero` base (`ap-impl.md` §2); `MethodEdgeStore` keys its groups by base with a `Reference2ObjectOpenHashMap` (`ap-impl.md` §7.3). `analyzer-core.md` §8 says REUSE (§10 row 6) |
| `EdgeCollection.UnprocessedEdgeList` (`CORE/ap/ifds/EdgeCollection.kt:10-33`) | ADAPT | the `normal` queue of `DeltaWorklist` (§4.1) | two stacks, the zero-to-zero items first (a REACH on `{zero}`: today the `is Edge.ZeroToZero` test, :24), then LIFO; the item is `EdgeDelta`; no list compression (trees are interned) |
| `EdgeCollection.EdgeSet` (`CORE/ap/ifds/EdgeCollection.kt:177-181`) | ADAPT | the set of the `unchanged` queue of `DeltaWorklist` (§4.1) | `ObjectOpenHashSet<EdgeDelta>`; it lives until the `unchanged` queue is empty, not for one `Work` event (today `CORE/ap/ifds/MethodAnalyzer.kt:312-313` resets it at the event end) |
| `Edge` (`CORE/ap/ifds/Edge.kt`) | REPLACE | `PremiseKey` + `EdgeDelta` with the kinds `Reach`, `FlowTree`, `TaintTree` | DD2: `ZeroToZero` is REACH; `ZeroToFact` and a concrete `FactToFact` are TAINT; an abstract `FactToFact` is FLOW; `NDFactToFact` is TAINT on a `PremiseSet` (`ap.md` §7.2, §7.6) |
| `SummaryEdgeStorageWithSubscribers` (`CORE/ap/ifds/SummaryEdgeSubscription.kt:742`) | ADAPT | `SummaryStorage` (§5.2) | Keep: the `ConcurrentLinkedQueue` of subscribers (:752), insert then notify (:771-796), `subscribeOnEdges` (:910-912). Change: a lock on the read (P3; today the reads :914-992 take no lock); one index by premise member. |
| `MethodSummariesUnitStorage` (`CORE/ap/ifds/MethodSummariesUnitStorage.kt:10`) | ADAPT | `RunManager.summaryStorage` | the `computeIfAbsent` (:112-115) per method key, with no unit indirection |
| `SummaryEdgeSubscriptionManager` (`CORE/ap/ifds/SummaryEdgeSubscription.kt:23`) | ADAPT | `SubscriptionManager` (§5.3) | Keep: register on the first `getOrPut` (:29-34), the delta insert, the replay (:51-180), the match at delivery (:499-623). Change: one `matches` (P4), one manager per runner. |
| `CommonAPSub`, tree sub-storages (`CORE/ap/ifds/access/common/CommonAPSub.kt:15`, `access/tree/MethodTreeAccessPathSubscription.kt:115-197`) | ADAPT | `CalleeSubscriptions` (§5.3) | Keep: one merged caller tree per caller key, the delta on insert (`mergeAddDelta`, :148; now `AddedFactStore.add`). Replace: `AccessTreeIndex` (:199-283; literal accessors, the bypass under `INDEX_LIMIT = 10` :211-213, :235) by `PathTrie` over the leaf keys and `ApOps.satisfying`. |
| side-effect requirements and summaries, `TaintMarkFieldUnfoldRequest`, `MethodSideEffectSummaryHandler`, `triggerSideEffectRequirement` | REMOVE | the requests (§4.8) | |
| `ExternalMethodTracker` (`CORE/ap/ifds/taint/ExternalMethodTracker.kt`) | REUSE | `UnresolvedCallObserver` (`ap-impl.md` §28.5), called by the plan runner (§4.5) | today once per fact at an unresolved call (`JIRMethodCallFlowFunction.kt:285-295`) |
| fact-depth delay (`MethodAnalyzer.kt:204-206`, `:560-595`, `:1390`; `TaintAnalysisUnitRunner.kt:343-362`) | REMOVE | the field limit | |
| `InitialFactAbstraction` (`MethodAnalyzer.kt:173`) | REMOVE | `ApOps.policy`, `ApOps.emit` (§4.2) | |
| `MethodSummaryEdgeApplicationUtils`, `MethodCallSummaryHandler` | REPLACE | `ApOps.applySummary` + the plan runner | |
| `TaintSinkTracker`, the buckets of `TaintAnalysisUnitStorage` (`CORE/ap/ifds/taint/TaintAnalysisUnitStorage.kt:17-31`) | REPLACE | `ConcurrentVulnerabilityStore`, `ConjunctionStore` (`ap-impl.md` §7.12, §7.10) | no lossy merge: the store merges only the witnesses of one (key, alternative, method key, run, shape) (`ap-impl.md` §7.12) |
| `MethodCallResolver`, `JIRMethodCallResolver` (`JVM/ap/ifds/analysis/JIRMethodCallResolver.kt:36`) | ADAPT | the `Callees` stage of `CallPlan` | in `ap-impl.md` §28.4 |
| `TrackerWithSubscriber`, `JIRLambdaTracker` (`CORE/util/TrackerWithSubscriber.kt:5`, `JVM/ap/ifds/JIRLambdaTracker.kt:8`) | REUSE | `JIRAnalysisManager.prescanLambdas()` (`ap-impl.md` §31.1) | `forEachRegisteredValue` (:23-25) reads the prescan values |
| `MethodEntrypointResolver`, `UnitResolver`, `LanguageManager` (`CORE/ap/ifds/analysis/MethodEntrypointResolver.kt:7`, `CORE/ifds/UnitResolver.kt:21`, `CORE/ap/ifds/LanguageManager.kt:8`) | REUSE | `SharedObjects`, `RunMethodContext` | `getCallExpr` (:13) finds the call statements |
| `ApplicationGraph.reversed` (`CORE/graph/BackwardGraphs.kt:40-45`), `MethodInstGraph` (`CORE/graph/MethodInstGraph.kt:10`) | REUSE | `RunMethodContext.graph` | through `JIRMethodEntry.graph(direction)` (`ap-impl.md` §31.2) |
| `JIRMethodAnalysisContext` (`JVM/ap/ifds/analysis/JIRMethodAnalysisContext.kt:19`) | ADAPT | `MethodContextCache` + `RunMethodContext` (§3.4) | split into the cached part and the run part; the JIR content is in `ap-impl.md` §31 |
| `JIRAnalysisManager` (`JVM/ap/ifds/analysis/JIRAnalysisManager.kt:59`) | GENERALIZE | `prescanRuleIds()`, `releasePrescan()` (§8.1) | `relevantRuleIds` (:75) is private today; `prescanLambdas()` over `contexts` (:76) is in `ap-impl.md` §31.1; `releasePrescan()` clears `contexts` |
| `MemoryManager`, `Cancellation`, `RefManager` (`CORE/util/MemoryManager.kt:17`, `CORE/util/Cancellation.kt:5`, `CORE/util/RefManager.kt:6`) | REUSE | `RunManager`, `UnitRunner`, `ApManager`, `IterationDriver` | one `MemoryManager` per run and one per barrier (§7.1); the bidi analysis makes its own `Cancellation` (§8.1), and each `RunManager` activates it in its constructor (§3.2); `ApManager` takes the same `RefManager` for its soft trie tables (`ap-impl.md` DD5; §8.1) |
| `UnitRunnerStats`, `MethodStats`, `collectMethodStats` (`CORE/ap/ifds/UnitRunnerStats.kt:7`, `:9`) | REMOVE | `InFlight.handled` (§6.3) | today the progress job reads runner-local state from another thread; the new progress log reads only atomic counters |
| summary serialization (`storeSummaries`, `loadSummariesFromRunner`) | REMOVE | the records | |
| `trace/*`: the trace resolver | REMOVE | the SIMPLE trace (§8.1) | the trace resolution is out of scope (`analyzer-core.md` §9): no store of a run stays for a trace resolver (§7.7, §8.2) |
| `VulnerabilityWithTrace` (`CORE/ap/ifds/trace/VulnerabilityWithTrace.kt:11`), `TracePathGenerationResult.Simple` (`CORE/ap/ifds/trace/path/TracePath.kt:23`) | REUSE | the phase-3 output (§8.1) | the output types of today |
| `TaintAnalyzer.analyzeStaged` (`SAST/common/sast/dataflow/TaintAnalyzer.kt:118-131`) | ADAPT | §8.1 | phase 3; a sketch only |

### 2.2 Names from `ap-impl.md`

This document calls these names. Each one has the signature of the `ap-impl.md` section in the right column.

| Name | `ap-impl.md` |
|---|---|
| `AccessPathBase.Zero` | §0 (K3), §2 |
| `TaintMark`, `TaintMark.ZERO` | §3.1 |
| `Direction`, `Layer`, `Tail` (with `ANY_TAINT` and `isAny`, `ap.md` §3.4, W8), `ApMode`, `MarkSlot` | §3.2 |
| `PremiseKey` (`size`, `member(k)`, `isZero`, `nonZeroCount`, `members`, `forEachMember`); `InitialAp` (`base`, `path`, `pathArray`, `tail`, `exclusion`, `mark`, `isZero`, `toPattern()`; a must-premise `[any-taint]` can have an exclusion, `ap.md` §6.3), the key of a premise set with one member; `PremiseSet` (two or more members) | §3.4 (`ap.md` §7.1) |
| `Facts` (`base`, `layer`; structural `equals`; `groupKey`: the store key of `ap.md` §8.1 without the statement and the premise), `Reach` (`Reach.of(layer)`), `FlowTree` (`exclusion`, `markExclusion`), `TaintTree` (`exclusion`: the one exclusion of its `[any-taint]` leaves, Empty in the demand layer, `ap.md` §7.2) | §4, §7 (`ap.md` §7.2) |
| `ConclusionGroup` (`add`: the delta, `all`), `StoreInterners`: the conclusions of one premise key | §4.3 |
| `ApManager(cancellation, refManager)` (`zero`, `premiseOf(members)`, `union(a, b)`: it drops the zero fact (`ap.md` §4.6), `initial(Pattern)`, `path(List<AccessorIdx>)`, `path(IntArray)`, `newInterners()`) | §5.1 |
| `ApOut` (`result(f: Facts)`, `markRequest`, `positionRequest`) | §5.2 |
| `ApOps` (`manager`; `applyEdge`: the public application of one micro edge, with `may` (every result in the demand layer: a micro edge whose forward target is `[any]`); the internal `applyCompiledEdge` is the tree form of the delta-concat `concat` of `ap.md` §4.1) | §5.3 |
| `ApOps.satisfying` (it reads `ANY_TAINT` as `ANY`, one location set, and it reads the exclusions of the premise and of the added fact, `ap.md` §3.4, §4.3), `applySummary`, `applyCombination` | §5.4 |
| `TypeFilter`, `ApOps.filter` | §5.5 |
| `ApOps.clean` | §5.6 |
| `ApOps.limit`; the table of the cut points (`ap.md` §4.4) and of the places where a fact can exceed `L` | §5.7 |
| `MarkCheck` (`None`, `Request(mark)`, `Holds(facts, covered)`), `ApOps.checkMark`, `without`, `withoutMarks(c, marks)` (every leaf with a mark of `marks`, both tails, every depth, an `[any-taint]/E` leaf with its exclusion; the other leaves stay in their layer), `targetTree`; `ConjunctiveEdge` | §5.8 |
| `ApOps.startFact(j)` (a must-premise starts as itself, in the normal layer, with its exclusion; only a forward restricted run has one, `ap.md` §6.5), `policy`, `emit` (`ap.md` §6.3: the mark of `D-c` must admit the mark of the added fact; since F71 `*∖X` admits only the marks that are not in `X`), `restrict(j, g, d): List<Facts>` (`ap.md` §6.4 AS AN INTERSECTION, `ap-history.md` F70: the premise inside `D-c`, the meet of the tails at `D-p`; MARK-AWARE since F71: the marks of `j` in the marks of `D-c`, and the mark of each conclusion leaf meets the mark of `D-p`; up to three trees: one exclusion per normal TAINT tree), `demandPart(premise, g, direction)` (the leaves that are not crossable, F70; null: every leaf is crossable) | §5.9 |
| `RequestAction`, `ApOps.requestAction` | §5.10 |
| `ApOps.leaves` (every kind; a REACH gives the zero fact; an any leaf of a normal TAINT tree has the tail `ANY_TAINT` and the exclusion of the tree, of a demand tree `ANY`, `ap.md` §7.2) | §5.11 |
| `Reference.kt`: `PathFact`, `Pattern`, `PathEdge`, `Conclusion`, `DemandPattern`, `concat` (`EdgeOutcome`), `applicable`, `inside`, `satisfies`, `recordDemand` (`ap.md` §6.3), `overlap`, `policy`, `emit`, `restrict`, `startFact(i)`, `limit`, `cleanRes` (`CleanOut`), `markCheck` (`CheckResult`), `conjDemand`, `normalize`, `answer`, `subsumes`, `revEdge`, `insideLoc`, `crossK`, `cross`, `crossReversed` (F70); `insideDemand`, `marksMeet` (F71: the two mark tests of `restrict`, `ap.md` §6.4); `Cleaner`, `CleanReach` | §6 |
| `PathTrie` (`add`, `lookupPrefixes`, `lookupExtensions`) | §7.2 |
| `MethodEdgeStore` (`add`, `edgesAt`; REACH bits, FLOW and TAINT trees per the keys of `ap.md` §8.1) | §7.3 |
| `InitialFactStore` (`add`) | §7.4 |
| `CallerRef`, `Link`, `AddedFactStore` (`add`, `overlapping`, `links`; the added fact of a link keeps its tail and its exclusion: `[any-taint]/E` on a normal link, `ap.md` §8.3) | §7.5 |
| `RunSummaryStore` (`add`, `all`: the summaries before the restriction, for R1; `addDemand`, `demandEdges`: the demand edges of the run, for the hand-off, F70) | §7.6 |
| `DemandStore` (`near`: the emission query; `covering`: the restriction query, F70), `DemandStore.Builder` | §7.7 |
| `Record` (`reversedAt`: LEAF BY LEAF, `ap.md` §8.7 R3, §9.1: nothing for a must record; no reversal of an `[any-taint]/E` leaf with `E ≠ {}`, and the other leaves of the same record reverse; `$ -> [any-taint]` gives `[any] -> $`), `RecordStore` (`byEntry`, `byExit`, `view`, `persist`: the R1 filter, one notion of complete), `PersistentRecordStore` | §7.8 |
| `RequestKind`, `RequestStore` (`add`, `overlapping`) | §7.9 |
| `ConjunctionStore` (`add`, `Input`, `Combination`, `NdKey`, `ndJoin`), `NdSummaryJoin` (`addSubscription`, `addConclusion`), `KaryJoin`, `StandingJoin` (`newA`, `newB`) | §7.10 |
| `SourceHitStore` (`add`, `entries`) | §7.11 |
| `RuleId`, `VulnerabilityKey(rule, method: CommonMethod, statement)` (no context), `SinkEdge`, `SinkWitness(alternative, methodKey, edges, run, endFacts)`, `VulnerabilityStore`, `ConcurrentVulnerabilityStore` | §7.12 |
| `Interpreter`, `ExitNode`, `MicroEdge` (`isSource`, `isIdentity`, `forward`, `conjunctive`, `may`; the target tail `ANY_TAINT` of a source with an `[any]` target; `may`: the forward target tail is `ANY`, a pass rule, also in its reversal, `interpreter.md` I14, or `conjunctive`, the reversed literal of a conjunctive edge, F70), `ZERO_FACT`, `ZERO_PATTERN`, THE SOURCE-SEED PLACES | §23.1 |
| `StatementSummary` (`touched`, `edges`, `conjunctions`, `typeFilters`, `resultFilters`, `edgesOf`) | §23.2 |
| the three application modes STATEMENT, STAGE, GEN; `FormApplier` (`statement(.., sink, untouched)`, `stage`, `gen`), `FactAlgebra`, `Place` | §23.3 |
| `ReferenceAlgebra` (the per-path `FactAlgebra` of the test oracle), `ReferenceSink`, `FormsReference` (`applier`, `run`, `conclusions`), `PlanItem`, `PlanHooks` (`trigger`: the seeds of THE TRIGGER OF AN END FACT, F70) | §23.8 |
| `SinkRule` (`rule`, `alternative`, `patterns`, `endFacts`, `conjunctive`, `seedPatterns()`), `RuleStatement`, `ExitRules` (`globalStateDrop`, `entryMarks`, `entryMarkRemoval(base): MarkSet?`: the entry marks for `this` and `arg(i)`, else null; `interpreter.md` D35), `CleanStep` | §23.4 |
| `CallPoint`, `StageKind` (`statementEdges`, `originOf(me, prev)`), `Origin`, `Guard` (`SinkTriggered`, `MemoryEffect.admits`), `CallStage` (`Edges.trigger`: the sink alternative of a reversed `END_FACTS` stage, F70) | §23.5 |
| `CallPlan` (`touched`, `stages`, `sinks`, `entry`, `exit`, `stagesFrom`, `reversed`) | §23.6 |
| `FormsCache`, `MethodForms`, `DirectedForms` | §23.7 |
| `JIRInterpreter`, `isSummaryBase` | §25, §30 |
| `UnresolvedCallObserver` (`reached`) | §28.5 |
| the `statementEdge` argument of `applyEdge` at a call | §28.6 |
| the zero fact at a call | §28.7 |
| the entry rules, the exit rules (at both exits; at the exceptional exit `Result` reads `exc`, `interpreter.md` §4.7) | §29 |
| `PrescanLambdas`, `JIRAnalysisManager.prescanLambdas()` | §31.1 |
| `JIRMethodEntries` (`forms(interp, key)`, `[key].graph(direction)`), `JIRMethodEntry`, `JIRMethodForms` | §31.2 |

### 2.3 Additions to `analyzer-core.md` §10

The engine types of this document are those of `analyzer-core.md` §10, with these additions:

| Addition | Spec form | Reason |
|---|---|---|
| `RunEvent.LinkIn(callee, ref, linkLayer, added: Facts)`, `RunnerPort.link(callee, ref, linkLayer, added)` | `LinkIn(callee, link: Link)`, `link(callee, link)` | DD3: one event carries the new links of one link key as one group. |
| `Subscription(callee, ref, linkLayer, added: Facts, zeroOnly)` | `addedFact: Pattern` | DD3. |
| `matches(sub, pub, m, ops, mode): Facts?` | `matches(sub, pub, config): Boolean` | DD3: the result is the satisfying part of the group for premise member `m`. |
| `SinkEdge(premise, layer, facts: Facts)` (`ap-impl.md` §7.12) | the same since F68 (`analyzer-core.md` §10; before: `fact: Pattern`) | the triggered part (`MarkCheck.Holds.facts`) of one input: several sink facts in one edge; the leaves are the facts of the spec |
| `SummaryApplier.applySummary(part, pub, member)` | `applySummary(sub, pub)` | E6: the index of the member that the part satisfies (§4.11). |
| `SummaryStorage.candidates(part, mode): List<Pair<Publication, Int>>` | `candidates(a: Pattern, config)` | DD3: the input is a tree part; each candidate has its member index. |
| `RunResult.direction`; `RunResult.analyzers: List` | no such field; `Sequence` | the hand-off and `persist` read the direction. The driver reads `analyzers` more than once. |
| `RunResult.demandLayerEdges`, `recordCrossings` as sums over `analyzers` | constructor fields (since F70) | the same values: each analyzer counts (`RunMethodAnalyzer` counters, §4.1, the `counters` of `analyzer-core.md` §4.1) |
| the counters `edgeDeltas`, `demandLayerEdges`, `nonZeroInitial`, `crossableLeaves`, `recordCrossings`, `demandByCause` of `RunMethodAnalyzer`; `triggerSeeds` | `counters` (since F70); `triggerSeeds`: none | the named parts of `counters`; `triggerSeeds` counts the seeds of THE TRIGGER OF AN END FACT of a backward run (§4.9), which the exclusion test reads with the seeds of the hand-off (§9.1 row 30). `demandLayerEdges` counts THE DEMAND-LAYER OBJECTS of `analyzer-core.md` §4.1: the demand-layer deltas of `edges.add` (`push`), the demand-layer summary deltas (`summaryDelta`; an exit-rule cut gives one with no demand-layer `edges.add` delta) and the new DEMAND LINKS (`addLink`, a link whose added fact is in the demand layer, `ap.md` §8.3) (§10 row 7) |
| `HandOff(demand, seeds, demandEdges)`, `HandOff.of(config, result, report, shared)` | `HandOff(demand, seeds)`, `handOffOf(config, result, report)` (since F70) | `demandEdges`: the demand patterns per method key, for `frontierOf` (§7.8) |
| `nextConfig` checks the field limit | the same (since F70) | before F70 `HandOff.next` checked it |
| `frontierOf`, `Frontier.log()` | `frontierOf` (since F70); the log line | §7.8 |
| `IterationDriver.frontiers` | a local of `analyze` (since F70) | the tests read the frontiers after `analyze` (§9.1 rows 29, 30) |
| `ReportBuilder.confirmedCount` | none | the frontier log (`Frontier.confirmedVulnerabilities`) |
| `SeedIndex.size`, `SeedIndex.sinkMethods()` | none | the frontier log (`Frontier.seeds`); the exclusion property test (§9.1 row 30) |
| `SharedObjects.diagnostics` | none | the option `Frontier.demandByCause` (§7.8) |
| `restrictBy(ops, demand, key, j, g)` | none | DD12: one restriction for the publications and the demand edges (§4.7) |
| `InFlight.handled`, `InFlight.pending` | none | the progress log reads only these atomic counters (§3.2, §6.3) |
| `IterationPolicy.timeout(run, remaining)`, default `remaining` | the same since F68 (`analyzer-core.md` §7.1) | the budget of one run (§10 row 3, RESOLVED) |
| `IterationDriver(policy, shared, budget)` | the same since F68 (`analyzer-core.md` §7.1) | the budget of the analysis |
| `BidiEntry` (`gather`, `run`, `toVulnerabilities`, `status`) | none (`analyzer-core.md` §9 names the inputs and the output) | the phase-3 hook of `TaintAnalyzer` (§8.1) |
| `RunnerPort.onProcess`, `RunnerPort.onCut` | none | test hooks: the fuzzer records the processed items (§9.2); `CutPointTest` records each cut with its point (§9.1). They are null in production. |
| `Cut`, `EngineAlgebra` | none | DD12 |
| `SubscriptionPort`, `SummaryApplier`, `ProtocolSteps` | parts of `RunnerPort` | `SubscriptionManager` reads only `SubscriptionPort`. The fuzzer defers the replay and the notification through `ProtocolSteps` (§9.2). |
| `RunnerPort.shared`, `forms`, `subscriptions` | `interpreter`, `contexts`, `vulnerabilities` | the shared objects in one value; the forms of the run (DD6) |
| `MethodContextCache(interpreter, source)`: `forms(key)`, `graph(key, direction)`, `directed(direction)` | `forms(key: MethodKey)` since F68 (`analyzer-core.md` §4.8, §10; before: `get(method, direction)`) | DD6: `graph` and `directed` are additions. The JIR source is `JIRMethodContextCache`. |
| `SeedIndex.allowsSource(method, statement, forward)` | none | the source-seed filter of `analyzer-core.md` §4.7 |
| `SharedObjects.unresolvedObserver` | none | the external method tracker (`ap-impl.md` §28.5); the plan runner calls it (§4.5) |
| `RunConfig.mode`, `RunConfig.seededSources`, `Publication.layer` | none | values that the spec fields give |

---

## 3. Entities and lifetimes (`analyzer-core.md` §2)

### 3.1 `SharedObjects`, `RunConfig`

```kotlin
package org.opentaint.dataflow.bidi.engine

/** analyzer-core.md §2: the objects of the analysis lifetime. The driver makes them once; every run reads them. */
class SharedObjects(
    val ap: ApManager,                                  // ap-impl.md §5.1: the interners; thread-safe (O4)
    val ops: ApOps,                                     // ap-impl.md §5.3: stateless
    val interpreter: Interpreter,                       // JIRInterpreter (ap-impl.md §25)
    val language: LanguageManager,                      // REUSE: getCallExpr, instruction indices
    val contexts: MethodContextCache,                   // §3.4
    val records: RecordStore,                           // PERSISTENT: PersistentRecordStore (ap-impl.md §7.8)
    val vulnerabilities: VulnerabilityStore,            // PERSISTENT: ConcurrentVulnerabilityStore (ap-impl.md §7.12)
    val unitResolver: UnitResolver<CommonMethod>,       // REUSE
    val refManager: RefManager,                         // REUSE: the input of MemoryManager; ApManager holds its soft trie tables in it
    val cancellation: Cancellation,                     // REUSE: the bidi analysis's own (§8.1); ApManager checkpoints read it;
                                                        // each RunManager activates it; RunManager.fail and the barrier guard
                                                        // cancel it (a COMPLETE run does not)
    threads: Int = (Runtime.getRuntime().availableProcessors() / 2).coerceAtLeast(1),   // TaintAnalysisUnitRunnerManager.kt:91-94
    val cancellationTimeout: Duration = 30.seconds,
    val diagnostics: Boolean = false,                   // the option `Frontier.demandByCause` of the frontier log (§7.8)
) : AutoCloseable {
    /** One pool for the analysis. Each run has its own scope on it (§6.4). */
    @OptIn(DelicateCoroutinesApi::class)
    val dispatcher: ExecutorCoroutineDispatcher = newFixedThreadPoolContext(threads, "bidi-worker")
    /** ap-impl.md §28.5: JIRInterpreter implements it (the external method tracker). The plan runner calls it (§4.5). */
    val unresolvedObserver: UnresolvedCallObserver? get() = interpreter as? UnresolvedCallObserver
    override fun close() = dispatcher.close()
}

/** analyzer-core.md §3, unchanged, plus the ApMode of the run (ap-impl.md §3.2). */
class RunConfig(
    val index: Int,                     // 1, 2, 3, ...; FORWARD for an odd index
    val fieldLimit: Int,
    val demand: DemandStore?,           // null only in run 1
    val records: RecordStore,           // a read-only view (RecordStore.view())
    val seeds: SeedIndex,               // §7.4
    val roots: List<MethodKey>,
) {
    val direction: Direction get() = if (index % 2 == 1) Direction.FORWARD else Direction.BACKWARD
    val run1: Boolean get() = index == 1
    val restricted: Boolean get() = index > 1
    val mode: ApMode = ApMode(run1 = index == 1, direction = direction, fieldLimit = fieldLimit)
    /** analyzer-core.md §4.7: a forward restricted run fires an unconditional source only if it is a source seed. */
    val seededSources: Boolean get() = restricted && direction == Direction.FORWARD

    init { require(run1 == (demand == null)) }          // ApMode checks fieldLimit >= 1 for run 1 (ap.md S12 (d))
}
```

### 3.2 `RunManager`

```kotlin
/** analyzer-core.md §2, §6. One per run. ADAPT of TaintAnalysisUnitRunnerManager. */
class RunManager(val config: RunConfig, val shared: SharedObjects, val steps: ProtocolSteps = ProtocolSteps.Inline) {
    // analyzer-core.md §6.3: activate the Cancellation when the run is made, before a runner starts and before the
    // driver publishes this manager (§7.1). So no later activation undoes a cancel.
    init { shared.cancellation.activate() }

    private val job = SupervisorJob()                                          // analyzer-core.md §6.3: a scope per run
    private val scope = CoroutineScope(shared.dispatcher + job)
    private val runners = ConcurrentHashMap<UnitType, UnitRunner>()           // today runnerForUnit (:79)
    private val storages = ConcurrentHashMap<MethodKey, SummaryStorage>()    // O2
    private val completion = CompletableDeferred<RunStatus>()
    private val status = AtomicReference<RunStatus?>(null)                    // THE FIRST END WINS (analyzer-core.md §6.3)
    val ended: Boolean get() = status.get() != null                           // runLoop: a cancel comes only after an end (§6.1)
    val inFlight = InFlight {                                                  // Q4: one counter per run
        if (status.compareAndSet(null, RunStatus.COMPLETE)) completion.complete(RunStatus.COMPLETE)   // the quiescence
    }
    val forms: DirectedForms = shared.contexts.directed(config.direction)      // ap-impl.md §23.7: one per run (DD6)
    private val memory = MemoryManager(shared.refManager, OOM_THRESHOLD) { fail(RunStatus.OOM) }   // today :113-118

    /** O2: exactly one storage per method key and run, made on the first access by any thread. */
    fun summaryStorage(key: MethodKey): SummaryStorage =
        storages.computeIfAbsent(key) { SummaryStorage(it, shared.ap, shared.ops, steps) }

    /** Unit routing. UnknownUnit: not analysed, the event is dropped and not counted (today :435-440, :41-42). */
    fun runnerOf(method: MethodKey): UnitRunner? {
        val unit = shared.unitResolver.resolve(method.method)
        if (unit == UnknownUnit) return null
        return runners.computeIfAbsent(unit) { UnitRunner(it, this).also(::start) }
    }

    fun route(event: RunEvent) { runnerOf(event.target())?.post(event) }     // Q1 is in post

    fun run(timeout: Duration): RunResult = memory.runWithMemoryManager {
        val joined = runBlocking {
            val progress = launch {                                             // today :166-171
                var last = 0L
                while (isActive) { delay(PROGRESS_PERIOD); last = logProgress(last) }
            }
            try {                                                               // THE CALLER-THREAD CODE of the run
                inFlight.beforeSend()                                           // Q3: the phantom event (today :147)
                if (status.get() == null) for (root in config.roots) route(RunEvent.Start(root))   // a run that ended before its start starts nothing
                inFlight.afterHandler()                                         // Q3 ends (today :162)
                withTimeoutOrNull(timeout) { completion.await() } ?: fail(RunStatus.TIMEOUT)
            } catch (e: Throwable) {                                            // route, runnerOf, UnitRunner, start: every
                logger.error(e) { "Run ${config.index}: the driver thread failed" }   // Throwable, an Error included. The status
                fail(RunStatus.FAILED)                                          // first, then the cancel; the join below still
            }                                                                   // runs (analyzer-core.md §6.3)
            progress.cancel()
            stopAndJoin()                                                       // on every exit: the runners are joined
        }
        // The status is the first end of the run (`status`). ONE EXCEPTION: THE JOIN OVERRIDES THE FIRST END. A runner that
        // did not stop can still touch its analyzers: the run is FAILED, also after the quiescence, its stores are not read,
        // and the analysis stops (analyzer-core.md §6.3). The driver reads the stores of a COMPLETE run only
        // (analyzer-core.md §7.5), so only such a run gives its analyzers. A throw after the join (`freeze`) leaves `run`;
        // the driver ends the analysis FAILED (§7.1), and every runner is joined already.
        val end = if (joined) status.get()!! else RunStatus.FAILED.also { logger.error { "Run ${config.index}: a runner did not stop" } }
        val analyzers = if (end == RunStatus.COMPLETE) runners.values.flatMap { it.analyzers() }.onEach { it.freeze() } else emptyList()
        runners.clear(); storages.clear()                                       // analyzer-core.md §7.6: these end here
        RunResult(end, analyzers, config.index, config.direction, shared.vulnerabilities)
    }

    /** analyzer-core.md §6.3, `RunManager.fail(s)`: THE STATUS IS SET BEFORE EVERY CANCEL, so every cancel has a known
     *  cause: the timeout (`TIMEOUT`), the memory guard of the run (`OOM`) or a runner failure (`FAILED`: a runner
     *  exception, or a throw of the caller-thread code of `run`). The first end sets `s` by compare-and-set; then `fail`
     *  cancels the `Cancellation` and completes the run, together: the other runners stop at their next checkpoint, with
     *  no wait for the timeout (ap-history.md F68). THE FIRST END WINS: after the quiescence (COMPLETE) or an earlier end,
     *  `fail` does nothing. So a late memory guard or a late timeout while the runners join does not turn a complete run
     *  into an incomplete one. One exception: the join overrides the first end (`run`). */
    fun fail(s: RunStatus) {
        if (!status.compareAndSet(null, s)) return
        shared.cancellation.cancel()
        completion.complete(s)
    }

    /** The progress log of today (:562-570). It reads only the atomic counters of InFlight and the memory usage, never a
     *  runner-local state (today's per-method statistics, :572-624, are not kept). */
    private fun logProgress(last: Long): Long {
        val handled = inFlight.handled
        logger.info { "Run ${config.index}: $handled events (+${handled - last}), ${inFlight.pending} in flight" }
        logger.info { "Memory usage: ${MemoryManager.currentMemoryUsage()}/${Runtime.getRuntime().maxMemory()}" }
        return handled
    }

    /** A runner exception: every Throwable, an Error included. A JVM OutOfMemoryError is FAILED too: the status OOM comes
     *  only from a memory guard (ap-history.md F68). `fail` sets FAILED, then cancels: the run ends before its timeout. */
    private fun start(r: UnitRunner) {
        val handler = CoroutineExceptionHandler { _, e ->
            logger.error(e) { "Runner ${r.unit} failed, run ${config.index} stops" }
            fail(RunStatus.FAILED)
        }
        scope.launch(handler) { r.runLoop() }                                  // runLoop catches Cancellation.Cancelled (§6.1)
    }

    /** analyzer-core.md §6.3: join every runner before `run` returns. False: a runner did not stop; the analysis stops. */
    private suspend fun stopAndJoin(): Boolean {
        runners.values.forEach { it.close() }
        job.cancel()
        return withTimeoutOrNull(shared.cancellationTimeout) { job.children.toList().joinAll(); true } ?: false
    }

    companion object {
        const val OOM_THRESHOLD = 0.90                                          // today OOM_DETECTION_THRESHOLD (:644)
        val PROGRESS_PERIOD = 10.seconds                                        // today :168
    }
}

fun RunEvent.target(): MethodKey = when (this) {
    is RunEvent.Start -> root
    is RunEvent.LinkIn -> callee
    is RunEvent.ZeroIn -> callee
    is RunEvent.RequestIn -> method
    is RunEvent.Delivery, is RunEvent.Work -> error("$this goes to a known runner, not by method")
}
```

`RunStatus` and `RunResult` (`analyzer-core.md` §10, with the additions of §2.3):

```kotlin
/** No CANCELLED: the status is set before every cancel, so every cancel has a known cause: the timeout, a memory guard
 *  (of a run or of the barrier, §7.1) or a runner failure (analyzer-core.md §6.3). */
enum class RunStatus { COMPLETE, TIMEOUT, OOM, FAILED }

/** `analyzers` is empty unless the run is COMPLETE (RunManager.run). */
class RunResult(
    val status: RunStatus,
    val analyzers: List<RunMethodAnalyzer>,
    val runIndex: Int,
    val direction: Direction,
    val vulnerabilities: VulnerabilityStore,
) {
    /** The witnesses of THIS run per vulnerability key (rule, method, statement): every alternative, every method key. */
    fun witnessesByKey(): Map<VulnerabilityKey, List<SinkWitness>> =
        vulnerabilities.witnessesOf(runIndex).groupBy({ it.first }, { it.second })

    /** analyzer-core.md §10 (ap-history.md F70): the sums of the `counters` of the analyzers (§4.1). The edge stores are
     *  dropped by `freeze`, so each analyzer counts during the run. `demandLayerEdges`: the demand-layer objects of the
     *  run (the demand-layer edge deltas and summary deltas, and the demand links); 0 after a forward run gives the stop
     *  rule NO_DEMAND_EDGE (§7.1). The DEMAND vulnerabilities are a state of the REPORT, not of one run
     *  (`ReportBuilder.hasDemandVulnerability`, §7.6). */
    val demandLayerEdges: Long get() = analyzers.sumOf { it.demandLayerEdges }
    val recordCrossings: Long get() = analyzers.sumOf { it.recordCrossings }
}
```

### 3.3 `UnitRunner`, `RunnerPort`, the analyzer table

```kotlin
/** analyzer-core.md §6.1. The runner interface that the analyzer uses. DD3: `link` carries the group of new links. */
interface RunnerPort : SubscriptionPort {
    val shared: SharedObjects
    val forms: DirectedForms                                         // the forms of this run (§3.4)
    val subscriptions: SubscriptionManager
    fun send(event: RunEvent)                                       // Q1, then the channel of the target runner
    fun enqueue(analyzer: RunMethodAnalyzer)                        // W1: a Work event into the local queue
    fun analyzer(key: MethodKey): RunMethodAnalyzer                 // this unit only; made on demand
    fun subscribe(sub: Subscription)                                // the SubscriptionManager of this runner
    fun link(callee: MethodKey, ref: CallerRef, linkLayer: Layer, added: Facts)      // same unit: a direct addLink
    /** Test hook (§9.2): every PROCESSED item (both queues of DeltaWorklist). Production: null. */
    val onProcess: ((MethodKey, EdgeDelta) -> Unit)? get() = null
    /** Test hook (§9.1 CutPointTest): every cut, with its point and the facts before the cut. Production: null. */
    val onCut: ((Cut, Facts) -> Unit)? get() = null
}

/** The part of the runner that the SubscriptionManager reads (a fake implements it in §9.4). */
interface SubscriptionPort {
    val config: RunConfig
    val ops: ApOps
    val steps: ProtocolSteps
    fun summaryStorage(key: MethodKey): SummaryStorage              // any unit (O2)
    fun applier(caller: MethodKey): SummaryApplier                  // the analyzer of the caller (this unit)
    fun post(event: RunEvent.Delivery)                              // Q1, then the channel of THIS runner
}

interface SummaryApplier {
    fun applySummary(part: Subscription, pub: Publication, member: Int)
    fun applyRecord(part: Subscription, record: Record)
}

/** analyzer-core.md §5.5: the two shared actions that the model splits into two steps. Production runs them inline. The
 *  fuzzer (§9.2) defers them, so the other actors act between the halves. */
interface ProtocolSteps {
    fun replay(step: () -> Unit)
    fun notify(step: () -> Unit)
    object Inline : ProtocolSteps {
        override fun replay(step: () -> Unit) = step()
        override fun notify(step: () -> Unit) = step()
    }
}
```

```kotlin
/** analyzer-core.md §2, §6.1. One coroutine per unit and run. ADAPT of TaintAnalysisUnitRunner. */
class UnitRunner(val unit: UnitType, private val run: RunManager) : RunnerPort {
    private val channel = Channel<RunEvent>(Channel.UNLIMITED)                 // today :75
    private val queue = EventQueue()                                           // today :74, with fixed keys (§6.2)
    private val analyzers = LinkedHashMap<MethodKey, RunMethodAnalyzer>()      // the pattern of MethodAnalyzerStorage (below)
    override val subscriptions = SubscriptionManager(this)
    override val config get() = run.config
    override val shared get() = run.shared
    override val forms get() = run.forms
    override val ops get() = run.shared.ops
    override val steps get() = run.steps

    fun post(event: RunEvent) { run.inFlight.beforeSend(); channel.trySend(event) }   // Q1 (today :278-282)
    override fun post(event: RunEvent.Delivery) = post(event as RunEvent)
    override fun send(event: RunEvent) = run.route(event)
    override fun enqueue(analyzer: RunMethodAnalyzer) {                        // W1; only this runner's thread calls it
        run.inFlight.beforeSend()
        queue.add(RunEvent.Work(analyzer))
    }
    override fun analyzer(key: MethodKey): RunMethodAnalyzer = analyzers.getOrPut(key) {
        check(shared.unitResolver.resolve(key.method) == unit) { "$key is not in $unit" }
        RunMethodAnalyzer(key, this)
    }
    override fun applier(caller: MethodKey): SummaryApplier = analyzer(caller)
    override fun subscribe(sub: Subscription) = subscriptions.subscribe(sub)
    override fun summaryStorage(key: MethodKey) = run.summaryStorage(key)
    override fun link(callee: MethodKey, ref: CallerRef, linkLayer: Layer, added: Facts) {
        if (shared.unitResolver.resolve(callee.method) == unit) analyzer(callee).addLink(ref, linkLayer, added)   // analyzer-core.md §6.1, direct call 2
        else send(RunEvent.LinkIn(callee, ref, linkLayer, added))
    }
    fun close() = channel.cancel()
    fun analyzers(): List<RunMethodAnalyzer> = analyzers.values.toList()       // RunManager.run, after the join
    suspend fun runLoop() { /* §6.1 */ }
}
```

THE ANALYZER TABLE is the pattern of `MethodAnalyzerStorage` (`CORE/ap/ifds/MethodAnalyzerStorage.kt:12-13`, `:15-36`,
`:49-59`): one analyzer per method key, made on demand. It has ONE thread: its runner writes and reads it, and the
driver reads it only after the join (`RunManager.run`). So it is a plain `LinkedHashMap`, not the
`ConcurrentReadSafeObject2IntMap` of today (`ap-impl.md` §2: the new core does not use that map). The old class stays
unchanged for the prescan. No method key is an empty method (§3.4), so the table has no empty-method branch.

### 3.4 `MethodContextCache` (`analyzer-core.md` §4.8)

The CACHED part holds the per-method entries and the per-key `MethodForms` of `ap-impl.md` §31.2 (DD6). There,
`FormsCache` keeps each form and its reversal, so the engine has no forms cache of its own. The RUN part is
`RunMethodContext`: the `DirectedForms` of the run and the method graph in the direction of the run.

```kotlin
/** The language part of the cache: JVM/bidi/JIRMethodContextCache.kt (below). */
interface MethodContextSource {
    fun forms(key: MethodKey): MethodForms                              // ap-impl.md §31.2: JIRMethodEntries.forms(interp, key)
    fun graph(key: MethodKey, direction: Direction): MethodInstGraph    // ap-impl.md §31.2: JIRMethodEntries[key].graph(direction)
}

/** analyzer-core.md §4.8, the CACHED part. Analysis lifetime. */
class MethodContextCache(val interpreter: Interpreter, private val source: MethodContextSource) {
    fun forms(key: MethodKey): MethodForms = source.forms(key)
    fun graph(key: MethodKey, direction: Direction): MethodInstGraph = source.graph(key, direction)
    /** analyzer-core.md §4.9, the table "What the core uses in each direction" (ap-impl.md §23.7). One per run. */
    fun directed(direction: Direction): DirectedForms = DirectedForms(interpreter, direction, ::forms)
}

/** analyzer-core.md §4.8, the RUN part: made by the run, bound to it. RunMethodAnalyzer holds one until freeze (§4.11). */
class RunMethodContext(val key: MethodKey, val forms: DirectedForms, val config: RunConfig, val shared: SharedObjects) {
    /** analyzer-core.md §4.4: an empty method (no instruction) has no method key. The call resolver drops it from the
     *  callees (interpreter.md D28), and it is never a root. So every method here has a graph and an edge store. */
    private val graph: MethodInstGraph = shared.contexts.graph(key, config.direction)  // wired backward (analyzer-core.md §4.4)
    private val ends: Set<CommonInst> = forms.endNodes(key).toHashSet()
    /** analyzer-core.md §4.3: forward, the exit rules of an exceptional exit apply there, but it is not an end node (no
     *  summary). Backward, an exceptional exit is a start node of the zero fact only (analyzer-core.md §4.4), so none. */
    private val exceptionalExits: Set<CommonInst> =
        if (config.direction != Direction.FORWARD) emptySet()
        else shared.interpreter.exitNodes(key).filter { it.exceptional }.mapTo(HashSet()) { it.node }
    val mode: ApMode get() = config.mode
    val ops: ApOps get() = shared.ops
    val ap: ApManager get() = shared.ap
    val vulnerabilities: VulnerabilityStore get() = shared.vulnerabilities
    fun isEnd(n: CommonInst): Boolean = n in ends
    fun isExceptionalExit(n: CommonInst): Boolean = n in exceptionalExits
    fun forEachSuccessor(n: CommonInst, body: (CommonInst) -> Unit) { graph.forEachSuccessor(shared.language, n, body) }
    fun callAt(n: CommonInst): CommonCallExpr? = shared.language.getCallExpr(n)       // today MethodAnalyzer.kt:299
}
```

```kotlin
package org.opentaint.dataflow.jvm.bidi

/** The JIR source of the cache. The content (graphs, alias analysis, prescan lambdas, forms) is ap-impl.md §31. */
class JIRMethodContextCache(private val interp: JIRInterpreter, private val entries: JIRMethodEntries) : MethodContextSource {
    override fun forms(key: MethodKey): MethodForms = entries.forms(interp, key)
    override fun graph(key: MethodKey, direction: Direction): MethodInstGraph = entries[key].graph(direction)
}
```

### 3.5 One call, in sequence

The caller `c` is in unit U1 (runner R1). The callee `m` is in unit U2 (runner R2). Forward run.

```kotlin
// R1, Work(c): process(EdgeDelta(i, s, t))       t: Facts; s is a call; plan = forms.call(c, s, call)
//   flow(BEFORE) -> BIND_IN -> BOUND: checkSinks (witnesses) -> Clean -> ADDED: a
//   enterCallees(a):
//     R1.subscribe(Subscription(m, ref = CallerRef(c, i, t.layer, s), a.layer, a))
//       SubscriptionManager.subscribe:
//         byCallee.getOrPut(m) { storage(m).addSubscriber(this) }   // P1: register first (CLQ add)
//         part = entry.add(sub) ?: return                           // E-3: exact (AddedFactStore), the new links only
//         steps.replay { storage(m).candidates(part) }               // P3: read under the lock
//           -> matches(part, pub, k) -> c.applySummary(...)        // P4; direct call 1 (analyzer-core.md §6.1)
//     R1.link(m, ref, a.layer, a)                                   // other unit:
//       RunManager.route(LinkIn(m, ...)) -> R2.post: inFlight+1, channel.trySend   // Q1
// R1: Work(c) ends when the worklist is empty and pending is flushed; inFlight-1   // Q2, W3
//
// R2, LinkIn(m): m.addLink(ref, layer, a)
//   links.add -> delta -> ops.policy(delta) -> addInitial -> startAt -> edges.add -> push -> requestWork   // W1
// R2, Work(m): ... a result at the normal exit -> endAt (RuleWorklist, cut EXIT_RULES) -> summaryDelta(j, g)
//   summaries.add -> delta -> pending += Publication(j, delta) (run 1: no restriction)
//   work() ends: flushPublications -> SummaryStorage(m).publish(pending)
//     synchronized(lock) { published.addAll } -> delta                    // P2: insert ...
//     steps.notify { for (s in subscribers) s.notify(m, delta) }          // ... then notify
//       -> R1.post(Delivery(m, delta)): inFlight+1                        // Q1 on R2's thread
//
// R1, Delivery(m): subscriptions.onDelivery(m, pubs)                       // P6: match against the subscriptions NOW
//   entry.candidates(pub, k) -> matches(part, pub, k) -> c.applySummary(part', pub, k)   // P4: the same matches
//     ops.applySummary(part'.added, j, g) -> RETURNED -> Rewrite -> REWRITTEN -> BIND_BACK, ALIASES -> AFTER
//     -> cut(CALL) -> emitAfter(i, s, r): edges.add at each successor -> push -> requestWork
```

---

## 4. `RunMethodAnalyzer` (`analyzer-core.md` §4)

One class in one file (`RunMethodAnalyzer.kt`). The subsections show its members in parts; every member belongs to
`RunMethodAnalyzer`, except the top-level types that a comment names.

### 4.1 State (`analyzer-core.md` §4.1)

```kotlin
private typealias ResultSink = (PremiseKey, Facts) -> Unit                    // top level: a result with its premise set

// PremiseKey.forEachMember, PremiseKey.members: ap-impl.md §3.4 (the members of a premise key, ap.md §7.1).

class RunMethodAnalyzer(val key: MethodKey, port: RunnerPort) : SummaryApplier {
    private var port: RunnerPort? = port                          // null after freeze (§7.7)
    private var rctx: RunMethodContext? = RunMethodContext(key, port.forms, port.config, port.shared)   // null after freeze
    private val p: RunnerPort get() = port!!
    private val r: RunMethodContext get() = rctx!!
    private val config: RunConfig get() = r.config                // the demand and the seeds of the run: dropped by freeze
    private val forms: DirectedForms get() = r.forms              // DirectedForms of the run (ap-impl.md §23.7)
    private val ops = port.shared.ops                             // analysis lifetime
    private val ap = port.shared.ap
    private val mode = port.config.mode                           // three constants
    private val limit = port.config.fieldLimit
    private val forward = port.config.direction == Direction.FORWARD

    // The RUN stores (ap.md §8; ap-impl.md §7). O1: this analyzer is their only writer. `freeze` drops the edge stores
    // and the links of a backward run at the end of the run: the barrier never reads them (analyzer-core.md §7.6; §7.7).
    private var edgeStore: MethodEdgeStore? = MethodEdgeStore(ap, key, port.shared.language, limit)   // ap.md §8.1: REACH
                                                                  // bits, FLOW and TAINT trees; the assert of ap.md W3 (ap-impl.md §5.7)
    private var initialStore: InitialFactStore? = InitialFactStore()   // ap.md §8.2; the confirmation reads Support, not a store (§7.5)
    private var linkStore: AddedFactStore? = AddedFactStore(ap)    // ap.md §8.3: per (CallerRef, link layer, ...), EXACT
    val edges: MethodEdgeStore get() = edgeStore!!
    val initials: InitialFactStore get() = initialStore!!
    val links: AddedFactStore get() = linkStore!!                  // forward: the confirmation reads it at the barrier (§7.5)
    val summaries = RunSummaryStore(ap)                           // ap.md §8.5: BEFORE the restriction. `persist` (R1) reads
                                                                  // it; the hand-off reads the publications of its leaves
                                                                  // that are not crossable (§7.2, F70)
    val sourceHits: SourceHitStore? = if (forward) null else SourceHitStore()            // ap.md §8.11
    private var requests: RequestStore? = if (config.run1) RequestStore() else null      // ap.md §8.8
    private var conjunctions: ConjunctionStore? = ConjunctionStore(ap)                    // ap.md §8.9: literals, sink literals, E6 (DD5)
    private val triggered = HashSet<Pair<CommonInst, SinkRule>>()                          // backward: THE TRIGGER OF AN END FACT,
                                                                                           // once per (statement, alternative) (§4.9)
    private val applier = FormApplier(EngineAlgebra())             // the three application modes (ap-impl.md §23.3)

    private var worklist = DeltaWorklist()                        // the two queues and the set of the unchanged path (below)
    private var pending = ArrayList<Publication>()                 // analyzer-core.md §4.6 item 3
    var queued = false; private set                               // analyzer-core.md §6.2 (MethodAnalyzer.kt:186)
    var steps = 0L; private set                                   // the priority key (§6.2); the frontier (§7.8)
    val hasZeroWork: Boolean get() = worklist.hasZeroWork          // the priority key (§6.2)

    // THE COUNTERS (analyzer-core.md §4.1 `counters`, §7.1, §7.8; ap-history.md F70). Only this runner writes them; the
    // driver reads them at the barrier, after the join (B1). `freeze` keeps them: they replace the edge stores, which it
    // drops (§7.7).
    var edgeDeltas = 0L; private set                              // the deltas of `edges.add` and the summary deltas
    var demandLayerEdges = 0L; private set                        // the stop rule NO_DEMAND_EDGE: THE DEMAND-LAYER OBJECTS,
                                                                  // those deltas in the demand layer (`push`, §4.3;
                                                                  // `summaryDelta`, §4.7) and the new demand links
                                                                  // (`addLink`, §4.2)
    var nonZeroInitial = false; private set                       // a non-zero initial fact (`addInitial`): in the frontier
    var crossableLeaves = 0L; private set                         // summary leaves out of the hand-off: records (`summaryDelta`)
    var recordCrossings = 0L; private set                         // record applications with a result (`applyRecord`, §4.6)
    var triggerSeeds = 0L; private set                            // backward: the seeds of THE TRIGGER OF AN END FACT
                                                                  // (`fireTriggerSeeds`, §4.9); the exclusion test (§9.1 row 30)
    val demandByCause: LongArray? =                               // AN OPTION: the demand-layer results per cause (§7.8);
                                                                  // the sites of the table of §7.8 count
        if (port.shared.diagnostics) LongArray(DemandCause.entries.size) else null
```

The worklist item and the worklist (DD2; `analyzer-core.md` §4.3, §10; ADAPT of `EdgeCollection.UnprocessedEdgeList`
and of the unchanged set, `MethodAnalyzer.kt:188`, `:603-607`):

```kotlin
/** DD2: the facts BEFORE the statement of `node`. `facts` holds the kind and the layer (ap.md §7.2). Value equality (DD4). */
data class EdgeDelta(val premise: PremiseKey, val node: CommonInst, val facts: Facts) {
    val zeroToZero: Boolean get() = premise.isZero && facts is Reach          // today the `is Edge.ZeroToZero` test (EdgeCollection.kt:24)
}

/** analyzer-core.md §4.3 THE TWO QUEUES. `unchanged`: the items of the unchanged path (ap.md §8.1), which do not go
 *  through edges.add; its SET drops a repeat. `normal`: the deltas of edges.add, the zero-to-zero items first, then LIFO
 *  (as today). The step takes an `unchanged` item while that queue is not empty, and a `normal` item only when it is
 *  empty. The set goes when the step finds `unchanged` empty: after the last `unchanged` item put its successors into the
 *  queues. So a loop of statements that do not touch a base ends (the set holds the items of the loop), and the set stays
 *  across the end of a Work event. */
class DeltaWorklist {
    private val unchanged = ArrayList<EdgeDelta>()
    private var seen = ObjectOpenHashSet<EdgeDelta>()            // the set of `unchanged` (DD4: by value)
    private var zeroUnchanged = 0                                // the zero-to-zero items in `unchanged`
    private val zero = ArrayList<EdgeDelta>()                    // `normal`: the zero-to-zero items
    private val other = ArrayList<EdgeDelta>()                   // `normal`: the other items

    val isEmpty: Boolean get() = unchanged.isEmpty() && zero.isEmpty() && other.isEmpty()
    /** A zero-to-zero item in either queue: the priority of the runner (§6.2) and the W2 test of `work` (§4.3). */
    val hasZeroWork: Boolean get() = zero.isNotEmpty() || zeroUnchanged > 0
    val size: Int get() = unchanged.size + zero.size + other.size

    /** A delta of edges.add (the `normal` queue). */
    fun add(d: EdgeDelta) { if (d.zeroToZero) zero += d else other += d }

    /** An item of the unchanged path. False: a repeat that the set holds; the item does not go into the queue again. */
    fun addUnchanged(d: EdgeDelta): Boolean {
        if (!seen.add(d)) return false
        unchanged += d
        if (d.zeroToZero) zeroUnchanged++
        return true
    }

    /** `unchanged` first. When the step finds `unchanged` empty, the set goes (a new empty set), and a `normal` item
     *  comes next. */
    fun removeNext(): EdgeDelta {
        unchanged.removeLastOrNull()?.let { if (it.zeroToZero) zeroUnchanged--; return it }
        if (seen.isNotEmpty()) seen = ObjectOpenHashSet()
        return zero.removeLastOrNull() ?: other.removeLast()
    }
}
```

A repeat that comes after the worklist became empty, while the set still holds the items of the last drain, gives
nothing new: its application gives only repeats (`edges.add`, the conjunction inputs, the witnesses and the source hits
deduplicate). So the set is exact.

THE KINDS IN THE ENGINE (DD11). The kind follows from the premise (`ap.md` §7.2), so the engine reads it where a rule
depends on it, and nowhere else. Every other place passes `Facts` to an operation of `ap-impl.md` §5:

| Rule of the kinds (`ap.md` §7.2) | Code |
|---|---|
| the zero-to-zero items go first (in the `normal` queue) | `DeltaWorklist`: `EdgeDelta.zeroToZero` (`premise.isZero && facts is Reach`) |
| the zero rules `zpass`, `zin`, `seed`, `zret` read REACH; a backward `{jb} → zero` only passes | `runCall`: `c is Reach` → `zeroAtCall` (§4.10) |
| every request comes from a FLOW fact (a premise with the mark `*`) | `raise` (§4.3): `check(input is FlowTree && premise is InitialAp)` |
| a restricted run has REACH and TAINT only | `emit` (§4.2): a `FlowTree` added fact is an error; `checkKinds` (in `push`, `summaryDelta`) asserts it |
| an ND edge (a `PremiseSet` premise) is always TAINT; no member is the zero fact (`ap.md` §4.6) | `checkKinds` (§4.3); `ndMatch` (§4.11); `ApManager.union` drops the zero fact |
| a FLOW part never meets a TAINT summary, and the application raises no request | `matches` → `satisfying` (§5.3); `applyParts` (§4.6) |
| E6 conclusions are TAINT (`ap.md` §4.6, `ap.md` W7); E6 never takes the zero subscription | `ndMatch`, `applyCombination(g: TaintTree)` (§4.11) |
| a zero-premise conclusion is REACH or a TAINT source result; only a TAINT one carries entry marks | `endAt` step 4 (§4.7) |
| the demand of each kind in the hand-offs | the table of §7.3 |
| a TAINT tree names its any leaves by its layer: `[any-taint]` in a normal tree, `[any]` in a demand tree; a normal TAINT tree has ONE exclusion for its `[any-taint]` leaves (its group key, as for FLOW), a demand tree none; a FLOW tree has no `[any-taint]` leaf and no exclusion of one (Lean `AnyTaintExKinds.D6X_flow_no_any_taint`, `D6X_flow_no_excl`, `kinds_D6X`); a normal edge of a restricted run has a `$` premise or a must-premise with a concrete mark (`AnyTaintExKinds.DRX_normal_premise`, `AnyTaintExKinds.DRX_must_premise`, under `AnyTaintEx.EmitCopiesMarkX`, which `AnyTaintEx.emitX_copies` gives; `AnyTaintExKinds.DRXs_normal_premise` is the instance of the earlier restriction, the record of the earlier design); the backward run has no `[any-taint]` (`ap.md` W8, §7.2, §8.1) | no engine code: `TaintTree` (`ap-impl.md` §4.1) and the AP operations; `checkKinds` needs no new test (DD13) |

THE PREMISE KEY HOLDS THE TAIL AND THE EXCLUSION (`analyzer-core.md` §4.1; `ap.md` §7.1). `InitialAp` has the tail and
the exclusion, so the must-premise `(x, p, [any-taint], E, T)`, a must-premise `(x, p, [any-taint], E', T)` with another
exclusion and the `[any]` premise `(x, p, [any], T)` of one path are THREE premise keys. A forward restricted run gets
them when `[any-taint]` added facts with the exclusions `E` and `E'` (normal on their links) and an `[any]` added fact (a
demand link) meet a demand at that path (§4.2 `emit`). The stores that the premise key keys keep them apart with no
other code: `initials`, `edges` (`EdgeDelta.premise`), `summaries`, `conjunctions`, `pending`, and on the callee side
`PublicationIndex` (§5.2). A must-premise starts in the normal layer with its exclusion, the `[any]` premise in the
demand layer (`ap.md` §6.5). The backward run has no must-premise (`ap.md` W8 (d)). Lean: the must flag and the premise
exclusion of `AnyTaintEx.XObj` (`init M j must jex`, `edge M j must jex n f`).

### 4.2 Handlers (`analyzer-core.md` §4.2)

```kotlin
    fun addRootZero() = addInitial(ap.zero)                                  // ap.md §6.1

    fun addZeroEntry() { check(!forward); addInitial(ap.zero) }              // rule zin (ap.md §9.2)

    /** E1, E2. DD3: `added` is one group of added facts; its delta holds the new links. A NEW DEMAND LINK (its added fact
     *  is in the demand layer, ap.md §8.3; analyzer-core.md §4.2 `addLink`) is a demand-layer object of the run: it adds
     *  one to `demandLayerEdges` (the stop rule NO_DEMAND_EDGE, §7.1). With every edge normal, a demand link alone can
     *  hold a DEMAND entry (a call cleaner demotes the bound fact, ap.md §2.2; then the emission `[any] ∩ $ = $` gives a
     *  normal start, ap.md §6.5), and a later run can confirm it (§9.1 row 21). */
    fun addLink(ref: CallerRef, linkLayer: Layer, added: Facts) {
        val delta = links.add(ref, linkLayer, added) ?: return                // E-3: exact deduplication (ap-impl.md §7.5)
        if (delta.layer == Layer.DEMAND) demandLayerEdges++                   // the counters (§4.1): a demand link
        emit(delta)                                                           // E1 (initials.add drops an old fact)
        val join = requestJoin ?: return                                      // E2: run 1 only
        for (leaf in ops.leaves(delta)) join.newB(Link(leaf, linkLayer, ref))   // one leaf = one new link (§4.8)
    }

    /** E5, E7: a request of this method, raised here or climbed from a callee (RequestIn). */
    fun addRequest(premise: InitialAp, kind: RequestKind) {
        val join = checkNotNull(requestJoin) { "a request in a restricted run (ap.md §6.1 rule 4)" }
        if (requests!!.add(premise, kind)) join.newA(premise to kind)        // E-3, then the standing join (§4.8)
    }

    override fun applySummary(part: Subscription, pub: Publication, member: Int) { /* §4.6 */ }
    override fun applyRecord(part: Subscription, record: Record) { /* §4.6 */ }
    fun work(quantum: Int): Boolean { /* §4.3 */ }

    /** analyzer-core.md §4.4: the initial facts of new added facts. Run 1: the policy (ap.md §6.2). Restricted: the
     *  emission (ap.md §6.3). The kinds (ap.md §7.2): REACH gives the zero fact in both (the implicit zero demand of
     *  DemandStore.near, ap-impl.md §7.7); a restricted run has no FLOW added fact.
     *  THE TAIL OF THE EMITTED FACT (ap.md §6.3, the meet table; analyzer-core.md §4.4): `delta` holds the layer of its
     *  link (ap-impl.md §7.5: linkLayer == added.layer), so an any leaf of a normal `delta` is an `[any-taint]` added fact
     *  and of a demand `delta` an `[any]` one (ap.md W8). For an added fact and a pattern that both have an any tail,
     *  `emit` keeps the tail of the ADDED FACT: an `[any-taint]` added fact gives a must-premise, an `[any]` one an `[any]`
     *  premise. The patterns of a forward run come from the backward run, so they have no `[any-taint]` tail (ap.md W8 (d)).
     *  THE EXCLUSION (ap.md §6.3): `emit` reads the exclusion `E` of `delta` as a part of the location set. A pattern
     *  below the added fact at a step that `E` excludes gives nothing; at a step that `E` admits it gives the pattern
     *  chain with no exclusion; a pattern at the path of the added fact or above it gives a premise with the exclusion
     *  `E` (a must-premise for an any-tail meet; a `$` premise has none) (Lean AnyTaintEx.emitX, emitTX; the vectors
     *  AnyTaintEx.Vec.emit_at, emit_above_excluded, emit_above_exact).
     *  THE MARK OF THE EMISSION (ap.md §6.3; analyzer-core.md §4.4; ap-history.md F71): the initial fact has the mark of
     *  the leaf, and the mark of `D-c` must admit it: `T` only `T`, `*` every mark, `*∖X` every mark that is not in `X`
     *  (Lean markMatchB; for a concrete leaf it is markSub, Handoff.RAux.markMatchB_conc). `ops.emit` tests it per leaf.
     *  `DemandStore.near` reads the locations only, so it also gives the patterns whose mark does not admit the leaf;
     *  `ops.emit` gives nothing for them. An entry pattern has the mark `*∖X` only in a backward run (a run-1 summary
     *  conclusion after a cleaner, §7.2): a requirement with a mark in `X` gets no initial fact from it, because that
     *  summary does not pass the mark (Handoff.RVec.vEmit_starEx_T; a mark not in `X`: vEmit_starEx_U). Before F71 `*∖X`
     *  counted as `*` (vEmit_starEx_T_pre70). Every leaf of a restricted run has a concrete mark, so the initial fact
     *  lies inside `D-c` in its locations and its mark (Handoff.emitM_insideB; with the exclusion
     *  HandoffX.emitX_insideXB), and the restriction of its summaries keeps it (§4.7). */
    private fun emit(delta: Facts) {
        if (config.run1) { addInitial(ops.policy(delta)); return }              // one group has one base
        when (delta) {
            is Reach -> addInitial(ap.zero)
            is TaintTree -> {
                val demand = config.demand!!
                val found = LinkedHashSet<DemandPattern>()
                for (leaf in ops.leaves(delta)) found += demand.near(key, leaf.fact.base, ap.path(leaf.fact.path))   // ap.md §8.6
                for (d in found) ops.emit(d, delta).forEach(::addInitial)       // one per leaf
            }
            is FlowTree -> error("a restricted run is concrete (ap.md §6.3, §7.2)")
        }
    }

    /** E3. The InitialAp is the premise key of its one-member premise set (ap.md §7.1). A must-premise
     *  `(x, p, [any-taint], E, T)` (forward restricted runs only, ap.md W8 (c)) starts as itself,
     *  `(x, p, [any-taint], E, T)`, in the normal layer (ap.md §6.5; Lean AnyTaintEx.startX). The start fact reads no
     *  direction: the backward run has no must-premise (ap.md W8 (d)). */
    private fun addInitial(j: InitialAp) {
        check(!config.run1 || j.tail != Tail.ANY_TAINT) { "run 1 has no must-premise (ap.md W8 (c))" }   // DD13
        check(forward || j.tail != Tail.ANY_TAINT) { "the backward run has no `[any-taint]` (ap.md W8 (d))" }
        if (!initials.add(j)) return
        if (!j.isZero) nonZeroInitial = true                                  // the frontier (§7.8)
        val start = ops.startFact(j)                                          // ap.md §6.5: REACH, FLOW or TAINT
        for (n in forms.startNodes(key, zero = j.isZero)) startAt(j, n, start)
    }
```

### 4.3 The application modes, the field limit, the step (`analyzer-core.md` §4.3)

ONE FORM APPLIER (DD12). `ap-impl.md` §23.3 gives the three application modes of a `StatementSummary`, and
`FormApplier` (`ap-impl.md` §23.3, §23.8) writes them once, generic over a `FactAlgebra`. Each application gets a `Place`
(the node, the static exception of a statement micro edge, a source-seed place). The engine gives `EngineAlgebra`
(below): the trees of `ap-impl.md` §4 through `ApOps`. `NaiveClosure` gives the per-path `ReferenceAlgebra` of
`ap-impl.md` §23.8 (§9.2). So the test oracle and the engine share the mode logic and differ only in the fact algebra.
`FormApplier.stage` gives each result with the micro edge that made it (null: a conjunction); the plan runner reads the
`Origin` from it (§4.5). At a source-seed place `FormApplier` calls `allowsSource` before the micro edge and `sourceHit`
for each micro edge that gives a result (`ap-impl.md` §23.3). So the hit is recorded whatever `edges.add` gives, also
when the store drops the result as a repeat (`analyzer-core.md` §4.7).

The engine algebra, its `ApOut` and the field limit:

```kotlin
    /** The engine side of FormApplier (ap-impl.md §23.3): the trees of ap-impl.md §4 through ApOps. A micro edge goes
     *  through the public ApOps.applyEdge (ap-impl.md §5.3; inside it, the internal `applyCompiledEdge` is the tree form
     *  of the delta-concat of ap.md §4.1).
     *  THE LAYER OF AN ANY-TAIL RESULT (analyzer-core.md §4.3; ap.md W6, W8): applyEdge reads the target tail of the micro
     *  edge, in every mode. An `[any]` target (a pass rule, a may) puts the result in the demand layer; an `[any-taint]`
     *  target (a source with an `[any]` target, ap.md S15) keeps the layer of the input; a demand-layer `[any-taint]`
     *  result is `[any]` with no exclusion. The interpreter gives the target tail by the rule kind of the edge
     *  (interpreter.md I14). Lean AnyTaint.w6t, AnyTaintEx.w6tX.
     *  THE EXCLUSION ROWS (ap.md §4.1, §4.2, §4.7): `applyEdge` and `clean` give an `[any-taint]/E` result its exclusion,
     *  in the layer of the input: the keep edge of a strong write gives `E ∪ {f}`, a read through an accessor in `E`
     *  gives nothing, a read through another accessor gives no exclusion, a copy keeps `E`, the cleaners `atAndBelow` and
     *  `below` one accessor below add the accessor to `E`. The engine reads none of it (DD13; Lean AnyTaintEx.annX,
     *  cleanResX).
     *  BACKWARD (analyzer-core.md §4.3; ap.md §9.2; interpreter.md I14, §4.9): the reversal of a micro edge whose FORWARD
     *  target is `[any]` (a pass rule with an `AnyField` target, a may) gives EVERY result in the demand layer, also a `$`
     *  result. The forward form of the micro edge tells it: `me.may` is `me.forward.to.tail == ANY` (ap-impl.md §23.1),
     *  so the forms carry no rule-kind flag, and the call passes it to `applyEdge` (forward, W6 gives the same layer). The
     *  reversal of a source edge (the forward target `[any-taint]`, a must) follows the ordinary rows of ap.md §4.1.
     *  Argued, as the backward W6 (ap.md §11.2).
     *  THE REVERSAL OF A CONJUNCTION (ap.md §9.1, §9.2; interpreter.md §4.9 STATEMENTS, §5.3; ap-history.md F70): a
     *  conjunctive micro edge `L1 ∧ … ∧ Lk → z` with two or more positive literals (an ND source; a conjunctive exit
     *  source, §4.4) reverses into the `k` micro edges `rev(Lj, z)`, an OR (ap-impl.md §23.2 `StatementSummary.reversed`).
     *  A requirement that reaches one literal is not a converse flow of the conjunction, so each of these edges gives
     *  EVERY result in the demand layer, as the reversal of a may: the reversed literal is `conjunctive`, so `me.may` is
     *  true for it (ap-impl.md §23.1; analyzer-core.md §4.9 `MicroEdge(edge, forward, conjunctive)`). So no
     *  backward summary through it is a record (R1) or crossable (Lean `Handoff.CrossB`), the hand-off gives it to the
     *  next forward run as a demand edge (case 3, §7.3), and that run analyses the callee with every member. This fixes
     *  a false CONFIRMED that existed before F70: R3 reversed the normal one-literal backward record into a forward
     *  record that drops the other literals (program CONJ, §9.1 row 32). Argued: the model has no restricted run with ND
     *  edges (ap.md §11.2). */
    private inner class EngineAlgebra : FactAlgebra<PremiseKey, Facts> {
        override fun base(c: Facts) = c.base
        override fun filter(c: Facts, filter: TypeFilter) = ops.filter(c, filter)
        override fun applyEdge(me: MicroEdge, c: Facts, premise: PremiseKey, statementEdge: Boolean, out: ResultSink) =
            ops.applyEdge(c, premise, me.edge, statementEdge, mode, collect(premise, c, out), may = me.may)   // a may: demand results
        override fun conjunction(cj: ConjunctiveEdge, premise: PremiseKey, c: Facts, node: CommonInst, out: ResultSink) =
            this@RunMethodAnalyzer.conjunction(cj, premise, c, node, out)
        override fun allowsSource(node: CommonInst, me: MicroEdge) =
            !config.seededSources || config.seeds.allowsSource(key, node, me.forward)
        override fun sourceHit(node: CommonInst, me: MicroEdge) { sourceHits?.add(key, node, me.forward) }
    }

    /** The ApOut of one input `c` (ap-impl.md §5.2). A result keeps the premise of the input. */
    private fun collect(premise: PremiseKey, c: Facts, sink: ResultSink): ApOut = object : ApOut {
        override fun result(f: Facts) = sink(premise, f)
        override fun markRequest(mark: TaintMark) = raise(premise, c, RequestKind.Mark(mark))
        override fun positionRequest(position: PathNode) = raise(premise, c, RequestKind.Position(position))
    }

    /** ap.md §4.5, §4.10: EVERY REQUEST COMES FROM A FLOW FACT (ap.md §7.2): the mark gate, a sink, a literal and a
     *  cleaner `part` raise one only on an abstract mark. A FLOW fact has one premise with the mark `*` (a policy fact or
     *  a position answer of run 1), so the request goes to that premise. RequestStore.add checks the premise again. */
    private fun raise(premise: PremiseKey, input: Facts, kind: RequestKind) {
        check(input is FlowTree && premise is InitialAp) { "a request needs a FLOW fact (ap.md §7.2)" }
        addRequest(premise, kind)
    }

    /** THE FIELD LIMIT (ap.md §4.4). Every cut of the engine is a call of this helper, and `point` names the cut point.
     *  ap-impl.md §5.7 has the table: the cut point, its call site, what it cuts, and where a fact can exceed L. A REACH
     *  passes; a tree within L passes in O(1) (`boundedDepth`). A cut `[any-taint]/E` fact becomes `[any]` in the demand
     *  layer and loses `E`: not every location below the cut path carries the mark (ap.md §4.4; Lean AnyTaintEx.limitFX,
     *  AnyTaintEx.Vec.cut_drops; program CUT: AnyTaintExCases.CUT.cut_ops). */
    private fun cut(point: Cut, premise: PremiseKey, f: Facts, sink: ResultSink) {
        p.onCut?.invoke(point, f)                                            // test hook (§9.1 CutPointTest)
        ops.limit(f, limit, collect(premise, f, sink))
    }
```

```kotlin
/** Top level. The cut points of ap.md §4.4: one value per call site of `cut` (the table below). */
enum class Cut { STATEMENT, CALL, ENTRY_RULES, EXIT_RULES, SEED }
```

Every call of `cut`, with its row of `ap.md` §4.4. `ap-impl.md` §5.7 gives, per row, what is cut and where a fact can
exceed `L` before the cut:

| `ap.md` §4.4 row | `Cut` | Call site |
|---|---|---|
| the statement transfer, after the micro edges and the lhs type filter; the read sources | `STATEMENT` | `runStatement` (§4.3), after the result filters |
| the call return, after the rewriter, the binding back and the aliases (a summary, a record, the unresolved callee) | `CALL` | `flow` at the exit point of the plan (§4.5): ONE site for every result of a call |
| the source results and the end facts of a sink at a call, after their binding back and the aliases | `CALL` | the same site |
| the results of the entry rules at the method start | `ENTRY_RULES` | `RuleWorklist` of `startAt` (forward, §4.4); backward, of `endAt` (the reversed entry rules, §4.7) |
| the results of the exit rules at an exit, normal or exceptional | `EXIT_RULES` | `RuleWorklist` of `endAt` (forward, both exits, §4.7); backward, of `startAt` (the reversed exit rules, §4.4) |
| the conjunction result; the application of a summary with several premises (E6) | `STATEMENT`, `CALL`, `EXIT_RULES` | a conjunction of a statement: `runStatement`; of a stage (an ND source; a pass rule never makes one, `interpreter.md` §4.2) and E6 (`applyCombination`, §4.11): the plan exit; of a conjunctive exit source (an ND edge at the exit, `interpreter.md` D31): `RuleWorklist` of `endAt` (§4.4, §4.7) |
| the backward seed | `SEED` | `seedFact` (§4.9): the seeds of the hand-off (`fireSinkSeeds`) and the seeds of THE TRIGGER OF AN END FACT (`fireTriggerSeeds`); a seed at a call is cut again at the plan exit (no change) |

The conjunction of a statement or of a stage (`ap.md` §4.6, §8.9). The literal check is `checkMark` (`MarkCheck`, `ap-impl.md`
§5.8), the same check as a sink:

```kotlin
    /** ap.md §4.6: one input per literal that `c` matches; each NEW full combination gives the target (a TAINT tree) with
     *  the union of the premise sets WITHOUT the zero fact (`{zero}` only if every input has `{zero}`; ApManager.union).
     *  So a conjunction of a `{zero}` input and an `{i}` input gives an `{i}` edge. The caller cuts the result
     *  (Cut.STATEMENT or Cut.CALL).
     *  THE TAIL `[any-taint]` (ap.md §4.6): a normal `[any-taint]` input that overlaps its literal and passes the mark
     *  gate is a NORMAL input also when the literal does not cover it (every location carries the mark; Lean
     *  AnyTaintND.conjLayerT): `MarkCheck.Holds.normalPart` reads it (ap-impl.md §5.8). `checkMark` reads the exclusion
     *  `E` of the input as a part of its location set: a literal that meets only excluded locations gives `None` (Lean
     *  AnyTaintEx.checkX; the conjunction with exclusions is argued, ap.md §11.2). The `[any]` target of a conjunctive
     *  source is `[any-taint]` (S15); `targetTree(cj.target, DEMAND)` names it `[any]` (W8). */
    private fun conjunction(cj: ConjunctiveEdge, premise: PremiseKey, c: Facts, node: CommonInst, sink: ResultSink) {
        val store = conjunctions!!
        for ((k, lit) in cj.literals.withIndex()) {
            if (lit.fact.base != c.base) continue
            val holds = when (val m = ops.checkMark(c, lit, mode)) {
                MarkCheck.None -> continue
                is MarkCheck.Request -> { raise(premise, c, RequestKind.Mark(m.mark)); continue }   // rule reqConj (run 1)
                is MarkCheck.Holds -> m
            }
            for (layer in listOfNotNull(Layer.NORMAL.takeIf { holds.normalPart }, Layer.DEMAND.takeIf { holds.demandPart }))   // ND.conjLayer
                for (comb in store.add(cj, node, cj.literals.size, k, ConjunctionStore.Input(premise, layer)))
                    sink(comb.premise, ops.targetTree(cj.target, comb.layer))   // comb.premise: ApManager.union, no zero member
        }
    }

```

The step:

```kotlin
    /** The Work handler. True: the event ends (Q2). W2: false keeps it counted and in the local queue. The set of the
     *  unchanged queue is not reset here: it lives until the unchanged queue is empty (DeltaWorklist). */
    fun work(quantum: Int): Boolean {
        val zeroAtStart = worklist.hasZeroWork
        var n = 0
        while (!worklist.isEmpty) {
            if (n++ >= quantum || worklist.hasZeroWork != zeroAtStart) return false   // W2 (TaintAnalysisUnitRunner.kt:217-221)
            process(worklist.removeNext())                                   // the unchanged queue first
        }
        flushPublications()                                                  // W3: before the event ends
        queued = false
        return true
    }

    /** NO LIVENESS CHECK (analyzer-core.md §4.3): an item on a dead local goes on (today MethodAnalyzer.kt:296 drops it). */
    private fun process(item: EdgeDelta) {
        steps++
        p.onProcess?.invoke(key, item)                                       // test hook (§9.2)
        if (r.callAt(item.node) != null) runCall(item) else runStatement(item)
    }

    /** A non-call statement: ap.md §4.2 steps 2–6. Backward: the reversed summary (no filter, ap-impl.md §23.2). */
    private fun runStatement(item: EdgeDelta) {
        applier.statement(forms.statement(key, item.node), item.premise, item.facts, Place(item.node, config.run1, sources = true),
            sink = { pr, x -> cut(Cut.STATEMENT, pr, x) { p2, t -> emitAfter(p2, item.node, t) } },   // step 6: ap.md §4.4 rows 1 and 6
            untouched = { _, _ -> emitUnchanged(item) })                                              // step 2: the unchanged path
    }

    /** A result after `node`: the exit rules at an exit (§4.7), then each successor through edges.add. */
    private fun emitAfter(premise: PremiseKey, node: CommonInst, t: Facts) {
        exitRulesAt(premise, node, t)
        r.forEachSuccessor(node) { s -> edges.add(s, premise, t)?.let { push(EdgeDelta(premise, s, it)) } }
    }

    /** THE UNCHANGED PATH (ap.md §8.1): no edges.add; the `unchanged` queue, whose set drops a repeat (DeltaWorklist).
     *  No post-processor, so the input edge goes on as it is (today MethodAnalyzer.kt:643-656 propagates the wrong
     *  variable; interpreter.md D14). The facts are those of a pushed item, so checkKinds holds already. */
    private fun emitUnchanged(item: EdgeDelta) {
        exitRulesAt(item.premise, item.node, item.facts)
        r.forEachSuccessor(item.node) { s -> if (worklist.addUnchanged(EdgeDelta(item.premise, s, item.facts))) requestWork() }
    }

    /** analyzer-core.md §4.3: the end rules at an end node. Forward, also the exit rules of an exceptional exit, with no
     *  summary: its facts end there (interpreter.md §4.7, §3.4). A forward exceptional exit has no successor. */
    private fun exitRulesAt(premise: PremiseKey, node: CommonInst, t: Facts) {
        if (r.isEnd(node)) endAt(premise, node, t, summary = true)
        else if (r.isExceptionalExit(node)) endAt(premise, node, t, summary = false)
    }

    private fun push(d: EdgeDelta) {                                     // the normal queue
        checkKinds(d.premise, d.facts)
        edgeDeltas++                                                       // the counters (§4.1)
        if (d.facts.layer == Layer.DEMAND) demandLayerEdges++              // the stop rule NO_DEMAND_EDGE (§7.1)
        worklist.add(d); requestWork()
    }

    /** ap.md §7.2, §4.6 (DD11): a restricted run is concrete; an edge whose premise set has two or more members (an ND
     *  edge) is ALWAYS a TaintTree. Users: push (every stored edge goes to the worklist), summaryDelta (a summary edge and
     *  its publications). */
    private fun checkKinds(premise: PremiseKey, f: Facts) {
        check(config.run1 || f !is FlowTree)
        check(premise !is PremiseSet || f is TaintTree)
    }
    private fun requestWork() { if (!queued) { queued = true; p.enqueue(this) } }   // W1 (today MethodAnalyzer.kt:609-616)
```

### 4.4 The rule order of a boundary; start nodes and start rules (`analyzer-core.md` §4.4)

ONE RULE WORKLIST (DD12) runs the rule order of a method boundary in both directions. Users: `startAt` (forward the
entry rules; backward the reversed exit rules and the exit sink seeds) and `endAt` (§4.7: forward the exit rules at both
exits; backward the reversed entry rules).

```kotlin
    /** THE RULE ORDER OF A BOUNDARY (interpreter.md §4.3, §4.7; reversed: analyzer-core.md §4.4, interpreter.md §4.9).
     *  1. each input goes through the rule summary (STATEMENT: it passes or keeps; the sources add);
     *  2. forward, each item meets the sinks, and the end facts of a triggered sink (GEN on the zero fact, in the layer of
     *     the sink edge) re-enter as items; backward, the reversed end facts (GEN) apply to each item, per sink
     *     alternative: a reversed end-fact edge of the alternative `s` that gives a result also fires the sink seeds of
     *     `s` here (THE TRIGGER OF AN END FACT, §4.9), and each seed is an input of step 1 with the premise `{zero}`, as a
     *     seed of the hand-off at an exit (`startAt`).
     *  Every result is cut at `point`. `after` sees each item with its triggers (endAt: steps 3 to 5).
     *  TERMINATION (DD4): `seen` compares (PremiseKey, Facts) by VALUE. Every step makes new objects, and an end fact can
     *  trigger its own sink again; with identity equality the loop does not end. The trigger seeds fire once per
     *  (statement, alternative) (`triggered`). */
    private inner class RuleWorklist(private val rules: RuleStatement, private val node: CommonInst, private val point: Cut) {
        val items = ArrayList<Pair<PremiseKey, Facts>>()
        private val seen = HashSet<Pair<PremiseKey, Facts>>()
        private val add: ResultSink = { pr, x -> cut(point, pr, x) { p2, t -> if (seen.add(p2 to t)) items += p2 to t } }
        /** Backward: the reversed end-fact edges of each sink alternative of the rules (`rules.endFacts` is their union;
         *  a reversed edge keeps its forward form, ap-impl.md §23.4 `RuleStatement.reversed`). */
        private val reversedEnds: List<Pair<SinkRule, List<MicroEdge>>> = if (forward) emptyList() else
            rules.sinks.mapNotNull { s -> rules.endFacts.edges.filter { me -> s.endFacts.any { it.forward == me.forward } }
                .takeIf { it.isNotEmpty() }?.let { s to it } }

        /** Step 1. The Place: in run 1 the static exception of ap.md §4.10 item 1 acts at the entry and exit rule
         *  statements; a source here is at a source-seed place. NaiveClosure.boundary uses the same Place (§9.2).
         *  A CONJUNCTIVE EXIT SOURCE (an alternative with two or more positive literals) is an ND edge at the exit, as at a
         *  call (interpreter.md D31; ap-history.md F68): `FormApplier.statement` gives `rules.summary.conjunctions` to
         *  `conjunction` (§4.3), which stores the input of each literal in the ConjunctionStore of this method key, per
         *  (edge, exit statement, literal index) (ap.md §8.9). A full combination is an item with the union of the premise
         *  sets (no zero member, ApManager.union), after the cut (`add`); it goes through steps 2 to 5 of endAt and becomes
         *  a summary at the normal exit, an ND summary if its premise set has two or more members, which the callers
         *  apply by E6 (§4.11). At the exceptional exit it ends after
         *  step 2 (`summary = false`). It is no rule error (analyzer-core.md §4.4). The forms cache gives the same
         *  ConjunctiveEdge on every call, so the store key is stable (ap-impl.md §23.7). */
        fun input(premise: PremiseKey, f: Facts) =
            applier.statement(rules.summary, premise, f, Place(node, config.run1, sources = true), sink = add)

        fun drain(after: (PremiseKey, Facts, Triggers) -> Unit = { _, _, _ -> }) {
            var k = 0
            while (k < items.size) {
                val (pr, t) = items[k++]
                val tr = checkSinks(pr, node, t, rules.sinks)                                 // step 2 (NONE backward)
                for ((sink, layer) in tr.fired) applier.gen(sink.endFacts, ap.zero, Reach.of(layer), add)
                for ((s, rev) in reversedEnds) {                                                 // the reversed end facts
                    var applied = false
                    applier.gen(rev, pr, t) { p2, x -> applied = true; add(p2, x) }
                    if (applied) fireTriggerSeeds(node, s) { seed -> input(ap.zero, seed) }       // THE TRIGGER OF AN END FACT
                }
                after(pr, t, tr)
            }
        }
    }

    /** E3 at one start node. Forward: the entry rules (interpreter.md §4.3: the zero keep, the context filter, the
     *  entry-point sources, the entry sinks) on the start fact. Backward: the reversed exit rules of THAT exit, normal or
     *  exceptional, on the start fact and on each sink seed of the exit sinks of that exit (§4.9). A seed enters where the
     *  forward exit sink checks (interpreter.md §4.7 step 2), so the reversal of step 1 applies to it: the reversed exit
     *  sources (a source hit) and the reversed end facts (interpreter.md §4.9 SEEDS; analyzer-core.md §4.4). */
    private fun startAt(premise: PremiseKey, n: CommonInst, start: Facts) {
        val w = RuleWorklist(forms.startRules(key, n), n, if (forward) Cut.ENTRY_RULES else Cut.EXIT_RULES)
        w.input(premise, start)
        if (!forward && premise.isZero) fireSinkSeeds(n) { seed -> w.input(ap.zero, seed) }   // rule seed
        w.drain()
        for ((pr, t) in w.items) edges.add(n, pr, t)?.let { push(EdgeDelta(pr, n, it)) }
    }
```

The entry sinks are unconditional (`interpreter.md` §4.1): they trigger only on the zero fact. So step 2 on the other
items of the start (the source results, the end facts) finds nothing, as the entry order of `interpreter.md` §4.3 says.

### 4.5 The call plan runner (`analyzer-core.md` §4.5)

One algorithm for both directions. The plan is a DAG of six points. `flow` takes the facts at a point through every
stage that starts there (`CallPlan.stagesFrom`). A fact at the exit point is cut and goes to the return node. The
reversed plan (`ap-impl.md` §23.6) is the same data: entry `AFTER`, exit `BEFORE`, no guard, no filter, and the
`PASS_OVER` stage `AFTER → BEFORE` of the alias bases. The runner applies it as every other stage. A reversed
`END_FACTS` stage keeps the sink alternative of its forward guard as `trigger`: when it gives a result, the runner fires
the sink seeds of that alternative (THE TRIGGER OF AN END FACT, §4.9).

```kotlin
    /** Facts at a point of a plan. `origin` (ap-impl.md §23.5 Origin): where a forward fact at REWRITTEN comes from; null before. */
    private class PlanFact(val premise: PremiseKey, val facts: Facts, val origin: Origin?)

    /** The call of one input edge. `callerLayer`: the layer of the caller edge (E-2). */
    private class CallCtx(val node: CommonInst, val call: CommonCallExpr, val plan: CallPlan, val callerLayer: Layer)

    private val CallPlan.callees: CallStage.Callees? get() = stages.firstNotNullOfOrNull { it as? CallStage.Callees }

    private fun runCall(item: EdgeDelta) {
        val call = r.callAt(item.node)!!
        val ctx = CallCtx(item.node, call, forms.call(key, item.node, call), item.facts.layer)
        val c = item.facts
        if (c is Reach) { zeroAtCall(item, ctx); return }                             // the zero rules read REACH (§4.10)
        if (c.base !in ctx.plan.touched) { emitUnchanged(item); return }              // step 1: relevance
        flow(ctx, ctx.plan.entry, listOf(PlanFact(item.premise, c, null)))
    }

    private fun flow(ctx: CallCtx, point: CallPoint, facts: List<PlanFact>) {
        if (point == ctx.plan.exit) {                                                  // the exit point
            for (f in facts) cut(Cut.CALL, f.premise, f.facts) { pr, t -> emitAfter(pr, ctx.node, t) }   // ap.md §4.4 rows 2, 3, 6
            return
        }
        val triggers = if (forward && point == CallPoint.BOUND)                       // the rule point (forward)
            facts.fold(Triggers.NONE) { acc, f -> acc + checkSinks(f.premise, ctx.node, f.facts, ctx.plan.sinks) }
        else Triggers.NONE
        if (config.run1 && point == CallPoint.ADDED) observeUnresolved(ctx, facts)
        for (stage in ctx.plan.stagesFrom[point].orEmpty()) {                          // same inputs: any order
            val out = applyStage(ctx, stage, facts, triggers)
            if (out.isNotEmpty()) flow(ctx, stage.to, out)
        }
    }

    private fun applyStage(ctx: CallCtx, stage: CallStage, facts: List<PlanFact>, triggers: Triggers): List<PlanFact> {
        val out = ArrayList<PlanFact>()
        when (stage) {
            is CallStage.Edges -> {
                when (val guard = stage.guard) {
                    is Guard.SinkTriggered ->                                           // END_FACTS (forward only)
                        for ((sink, layer) in triggers.fired) if (sink === guard.sink) {
                            val at = Place(ctx.node, statementEdge = false, sources = false)
                            applier.stage(stage.summary, ap.zero, Reach.of(layer), at) { pr, x, me -> out += PlanFact(pr, x, stage.kind.originOf(me, null)) }
                        }
                    else -> for (f in facts) {
                        if (guard == Guard.MemoryEffect && !Guard.MemoryEffect.admits(checkNotNull(f.origin))) continue   // interpreter.md AC3, AC4
                        val at = Place(ctx.node,
                            statementEdge = config.run1 && stage.kind.statementEdges,     // ap.md §4.10 item 1 (ap-impl.md §28.6)
                            sources = stage.kind == StageKind.SOURCES)                     // THE SOURCE-SEED PLACES
                        applier.stage(stage.summary, f.premise, f.facts, at) { pr, x, me -> out += PlanFact(pr, x, stage.kind.originOf(me, f.origin)) }
                    }
                }
                // THE TRIGGER OF AN END FACT AT A CALL (§4.9; analyzer-core.md §4.5): a reversed END_FACTS stage (no guard)
                // keeps the sink alternative of its forward guard as `trigger` (ap-impl.md §23.5). When it gives a result
                // on a requirement, the sink seeds of that alternative fire at this call, once per (statement,
                // alternative). The stage goes REWRITTEN → BOUND, so its results and these seeds arrive at BOUND, where the
                // seeds of the hand-off enter too (zeroAtCall, §4.10).
                val s = stage.trigger
                if (s != null && out.isNotEmpty()) fireTriggerSeeds(ctx.node, s) { t -> out += PlanFact(ap.zero, t, null) }
            }
            is CallStage.Clean -> for (f in facts) cleanChain(stage.steps, f, ctx.node) { out += it }
            is CallStage.Rewrite -> for (f in facts) cleanChain(stage.steps, f, ctx.node) { out += it }
            is CallStage.Callees -> for (f in facts) enterCallees(ctx, stage, f)        // the results arrive later
        }
        return out
    }

    /** interpreter.md §4.5 step 5.1 (and the rewriter): the steps in their directed order; each acts on the survivors.
     *  F74: a field action uses ordinary read/clean/write operations, then drops its temporary. Primitive requests
     *  still use collect on the incoming premise; F75 requests on every same-base abstract fact in run 1 and suppresses requests in later runs. */
    private fun cleanChain(steps: List<CleanStep>, f: PlanFact, node: CommonInst, emit: (PlanFact) -> Unit) {
        fun statement(s: StatementSummary, x: PlanFact): List<PlanFact> = buildList {
            applier.statement(s, x.premise, x.facts, Place(node, config.run1, sources = false),
                sink = { pr, t -> cut(Cut.STATEMENT, pr, t) { p2, y -> add(PlanFact(p2, y, x.origin)) } },
                untouched = { pr, t -> add(PlanFact(pr, t, x.origin)) })
        }
        var cur = listOf(f)
        for (step in steps) {
            val next = ArrayList<PlanFact>()
            for (x in cur) when (step) {
                is CleanStep.Clean -> ops.clean(x.facts, x.premise, step.cleaner, mode, collect(x.premise, x.facts) { pr, t -> next += PlanFact(pr, t, x.origin) })
                is CleanStep.Kill -> applier.statement(step.keepEdges, x.premise, x.facts,
                    Place(node, config.run1, sources = false),
                    sink = { pr, t -> next += PlanFact(pr, t, x.origin) })
                is CleanStep.Field -> for (a in statement(step.read, x))
                    ops.clean(a.facts, a.premise, step.cleaner, mode, collect(a.premise, a.facts) { pr, t ->
                        next += statement(step.write, PlanFact(pr, t, a.origin)).filter { it.facts.base != step.temporary }
                    })
            }
            cur = next
        }
        cur.forEach(emit)
    }

    /** ap-impl.md §28.5: in run 1, each new added-fact delta at the UNRESOLVED stages goes to the observer (the external
     *  method tracker), once per fact: the two UNRESOLVED stages (the identity, the pass rules) share ADDED.
     *  The zero fact (REACH) is not tracked, as today (JIRMethodCallFlowFunction.kt:285-295). No effect on facts. */
    private fun observeUnresolved(ctx: CallCtx, facts: List<PlanFact>) {
        val observer = r.shared.unresolvedObserver ?: return
        if (ctx.plan.stagesFrom[CallPoint.ADDED].orEmpty().none { it is CallStage.Edges && it.kind == StageKind.UNRESOLVED }) return
        for (f in facts) if (f.facts !is Reach) observer.reached(ctx.call, f.facts.base, ctx.plan)
    }

    /** SUBSCRIBE and LINK for each resolved callee (forward ADDED → RETURNED; backward RETURNED → ADDED). */
    private fun enterCallees(ctx: CallCtx, stage: CallStage.Callees, a: PlanFact) {
        val ref = CallerRef(key, a.premise, ctx.callerLayer, ctx.node)                  // E-2
        for (m in stage.callees) {
            p.subscribe(Subscription(m, ref, a.facts.layer, a.facts))                   // the replay may call THIS analyzer
            p.link(m, ref, a.facts.layer, a.facts)                                       // same unit: a direct addLink
        }
    }
```

`FormApplier.stage` (`ap-impl.md` §23.3) gives each result with the micro edge that made it, so the plan runner reads the
`Origin` with no second edge loop. The `Origin` rule is `StageKind.originOf` (`ap-impl.md` §23.5): the engine and the
per-path walk `FormsReference.run` (§9.2) call the same code.

### 4.6 The results of the callees stage (`analyzer-core.md` §4.2 `applySummary`, `applyRecord`)

```kotlin
    /** A MUST-PREMISE j (the tail `[any-taint]`, with an exclusion or none; forward restricted runs only, ap.md W8 (c)):
     *  `matches` gave the part that j with its exclusion lies INSIDE, the exclusions read (ap.md §4.3; Lean
     *  AnyTaintEx.satX, SatInsideX, satX_inside), so `applySummary` needs no other test. A part on a demand link (an
     *  `[any]` added fact) gives a demand result: the layer of the part enters the application (ap-impl.md §5.4). Only a
     *  normal `[any-taint]` link gives a normal result. A summary with an exclusion (a `*/E` conclusion, an
     *  `[any-taint]/E` conclusion) applies by the exclusion rows of the AP (ap.md §4.1, §4.3): no demotion here. This
     *  holds also for a ZERO-PREMISE summary on the zero subscription (a REACH part; the factory `mk` of
     *  analyzer-core.md §13 item 25 gives `{zero} -> (ret, ., [any-taint], {name, k}, T)`): the REACH branch of the AP
     *  gives the result the target exclusion of the summary leaf (ap.md §4.1, the case below with an `[any-taint]/Et`
     *  target; ap-impl.md §5.3 `EdgeApplication.reach`), so the caller gets `[any-taint]/{name, k}`, not
     *  `[any-taint]/{}`. */
    override fun applySummary(part: Subscription, pub: Publication, member: Int) {
        val j = when (val pk = pub.premise) {
            is PremiseSet -> { ndMatch(part, pub, pk, member); return }                // E6 (§4.11)
            is InitialAp -> pk                                                          // one member: the key IS the fact
        }
        fromCallees(part.ref) { results ->
            if (part.zeroOnly) results += PlanFact(part.ref.premise, pub.conclusion, Origin.SUMMARY_EFFECT)   // zret: no test
            else applyParts(part, j, pub.conclusion, results)
        }
    }

    /** ap.md §8.7 R3, R4; a record is not restricted. `part` satisfies the record premise j by `applicable || inside`
     *  (replayRecords, §5.3).
     *  THE RECORD DEMOTION (analyzer-core.md §4.2 `applyRecord`; ap.md §4.3, the reference form `recordDemand`): a MUST
     *  RECORD (j has the tail `[any-taint]`, with an exclusion or none) needs every location of j. The leaves that j lies
     *  INSIDE, the exclusions read, give the result of the application; the other leaves (`applicable` only: they lie
     *  inside j, or at j with an exclusion that j does not have) give the same facts in the DEMAND layer, with no
     *  exclusion (Lean AnyTaintEx.recLayerX; AnyTaint.recLayer, recLayer_fact; necessary: AnyTaintExact.CexApp.cex_app).
     *  A must record is only forward: R3 reverses no record with an `[any-taint]` premise, and the backward run has no
     *  `[any-taint]` (ap.md §8.7 R3, W8 (d)). NO OTHER DEMOTION: a record with an exclusion (the `*/E` record of a setter, an
     *  `[any-taint]/E` conclusion) applies by the exclusion rows of the AP, in the layer of the part (ap.md §4.1, §4.3;
     *  Lean the rule `retRec` of AnyTaintEx.DRX; program S: AnyTaintExCases.S.record_app).
     *  A demoted result is a DEMAND-layer record result, so it is SUMMARY_EFFECT and goes to the
     *  aliases (analyzer-core.md §4.5 THE ALIAS GUARD). The raise at the end point of the callees stage gives the facts
     *  of Lean recLayerX OR A SUPERSET (sound). Lean raises after the binding back and before the cut (`limitFX` of
     *  `recLayerX`; the two commute). Here the raise comes before the binding back: each later stage keeps a demand-layer
     *  fact in the demand layer, but it reads the layer of a TAINT input (`EdgeApplication.taint` reads the must and the
     *  exclusion of a normal tree only, `TaintClean` names the any leaf by the layer, ap-impl.md §5.3, §5.6), and a demand
     *  tree has no exclusion, so the binding back, the rewriter and the cut can give more facts than the Lean raise after
     *  them. The alias facts of a demoted result are extra facts outside the Lean closures (analyzer-core.md §11 THE
     *  ANALYZER ACTIONS OUTSIDE THE CLOSURES).
     *  A RECORD CROSSING (analyzer-core.md §4.2; ap-history.md F70): each application with a result adds one to
     *  `recordCrossings` (the frontier log, §7.8): in a forward run a forward record (R4) or a reversed backward record
     *  (R3), in a backward run the reverse. A crossable leaf of the run before is not in the demand (§7.2), so this is
     *  where a run crosses a callee that it does not analyse again. */
    override fun applyRecord(part: Subscription, record: Record) = fromCallees(part.ref) { results ->
        val j = record.premise
        if (j.tail != Tail.ANY_TAINT) applyParts(part, j, record.conclusion, results)
        else {
            check(forward) { "a must record is only forward (ap.md §8.7 R3)" }
            val inside = ops.satisfying(part.added, j, mode)                          // restricted mode: the `inside` part
            inside?.let { applyParts(part.copy(added = it), j, record.conclusion, results) }
            val only = if (inside == null) part.added else ops.without(part.added, inside)   // `applicable` only
            if (only != null) {
                val demoted = ArrayList<PlanFact>()
                applyParts(part.copy(added = only), j, record.conclusion, demoted)
                for (x in demoted) results += PlanFact(x.premise, toDemand(x.facts), Origin.SUMMARY_EFFECT)
            }
        }
        if (results.isNotEmpty()) recordCrossings++                                     // the counters (§4.1)
    }

    /** The record demotion: the same facts in the demand layer. A must record has a concrete premise, so its results are
     *  TAINT (ap.md §7.2); the layer of a TAINT tree names its any leaves, so the raise is the W8 (b) normal form. A
     *  demand tree has no exclusion: the factory gives it the Empty exclusion (Lean recLayerX drops it; a larger
     *  location set, sound). */
    private fun toDemand(f: Facts): Facts = when (f) {
        is TaintTree -> if (f.layer == Layer.DEMAND) f else ap.taintTree(f.base, Layer.DEMAND, f.root)
        is Reach -> Reach.of(Layer.DEMAND)
        is FlowTree -> error("a must record has TAINT results (ap.md §7.2)")
    }

    /** The results of the callees stage go on from its end point (RETURNED forward, ADDED backward). Users: applySummary,
     *  applyRecord, applyCombination (§4.11). */
    private inline fun fromCallees(ref: CallerRef, fill: (MutableList<PlanFact>) -> Unit) {
        val ctx = ctxOf(ref)
        val results = ArrayList<PlanFact>()
        fill(results)
        flow(ctx, ctx.plan.callees!!.to, results)
    }

    /** interpreter.md §3.8 AC4 PER SUMMARY EDGE: a conclusion delta can hold the identity leaf and effect leaves (the
     *  first delta of the FLOW summary `x.* -> {x.*, x.f.*}`, or of the TAINT summary `x.$ (T) -> {x.$ (T), x.f.$ (T)}`).
     *  Split it, so the alias guard sees the identity part as IDENTITY. The split needs the group key of `startFact(j)`
     *  (`summaryParts`).
     *  THE KINDS (ap.md §7.2; ap-impl.md §5.4): FLOW a × FLOW g → FLOW; TAINT a × FLOW g → TAINT (a run-1 record is a
     *  transfer function); TAINT a × TAINT g → TAINT; TAINT a × REACH g → REACH (backward: the requirement `a` reached a
     *  source in the callee, `jb -> zero`; the case-3 chain below); REACH a × (REACH or TAINT) g → the same kind. A FLOW
     *  part never comes here with a TAINT summary: its premise mark is concrete, so `satisfying` rejects the part (§5.3,
     *  P4), and no request is raised (Coverage.summary_step). The callee raised the standing request when its rule met its
     *  policy fact; the link of this caller makes it climb (§4.8).
     *  THE CASE-3 CHAIN (a source in a callee, reached through a return value: `h(){ t = g(); sink(t); }`,
     *  `g(){ return src(); }`). Backward run 2: the requirement on `t` enters `g` as `ret.$ (T)`, meets the reversed
     *  source and gives the publication `{ret.$ (T)} -> zero` (REACH); `h` applies it to its TAINT subscription (TAINT ×
     *  REACH → REACH). If that REACH edge is in the demand layer, the hand-off gives `g` the demand `(zero, ret.$ (T))`
     *  (§7.3, case 3), and forward run 3 publishes the source summary `{zero} -> ret.$ (T)` of `g` by it. A NORMAL one is a
     *  backward record (F70): its reversal `{zero} -> ret.$ (T)` is crossable, so the hand-off gives `g` no demand, and
     *  forward run 3 applies that reversal to the zero fact at the call (§5.3 `replayRecords`; HandOffTest, §9.1). */
    private fun applyParts(part: Subscription, j: InitialAp, g: Facts, results: MutableList<PlanFact>) {
        for ((gp, origin) in summaryParts(j, g))
            ops.applySummary(part.added, j, gp, mode, collect(part.ref.premise, part.added) { pr, t -> results += PlanFact(pr, t, origin) })
    }

    /** ap-impl.md §23.5 Origin; analyzer-core.md §4.5 THE ALIAS GUARD. A result is IDENTITY only if it is in the NORMAL
     *  layer AND it equals the start fact of j (today JIRMethodCallSummaryHandler.hasMemoryEffect). Every other leaf is
     *  SUMMARY_EFFECT: every DEMAND-layer result (an incomplete result always goes to the aliases; the `ap.md` W2 start
     *  `(x, p, [any], T)` of a `*`-T premise is coarser than the premise, so its leaf is no identity), and every result
     *  of a zero premise. The identity needs the same group key (ap.md §8.1: kind, base, layer; FLOW also exclusion and
     *  mark exclusion; a normal TAINT tree also its exclusion): `x.*/E` with E ≠ {} is an effect. The start of a
     *  must-premise `(x, p, [any-taint], E, T)` is itself, normal, with its exclusion (ap.md §6.5), so a normal leaf equal
     *  to it, with the same exclusion, is an IDENTITY; `(x, p, [any-taint], E ∪ {f}, T)` (a strong write) is an effect. */
    private fun summaryParts(j: InitialAp, g: Facts): List<Pair<Facts, Origin>> {
        val id = ops.startFact(j)
        if (j.isZero || g.layer != Layer.NORMAL || g.groupKey != id.groupKey) return listOf(g to Origin.SUMMARY_EFFECT)
        val effect = ops.without(g, id)                                              // ap-impl.md §5.8: the leaves not in id
        val identity = if (effect == null) g else ops.without(g, effect)
        return listOfNotNull(effect?.let { it to Origin.SUMMARY_EFFECT }, identity?.let { it to Origin.IDENTITY })
    }

    private fun ctxOf(ref: CallerRef): CallCtx {
        val call = r.callAt(ref.call)!!
        return CallCtx(ref.call, call, forms.call(key, ref.call, call), ref.callerLayer)
    }
```

The end point of the callees stage is `RETURNED` forward and `ADDED` backward. A result at an end node of the run goes
through the end rules there (`emitAfter`), also when the end node is a call (`analyzer-core.md` §4.3).

### 4.7 End rules, summary edges, publications (`analyzer-core.md` §4.6)

`DirectedForms.endRules` gives an `ExitRules` in both directions (backward: the reversed entry rules, no global-state
rule, no entry marks; `ap-impl.md` §23.7). Forward, it gives the exit rules of each exit, normal or exceptional
(`interpreter.md` §4.7; at the exceptional exit the rule position `Result` reads `exc`). So `endAt` is the
`RuleWorklist` of §4.4 plus steps 3 to 5:

```kotlin
    /** interpreter.md §4.7 forward; the reversed entry rules backward. Then the summary edges (analyzer-core.md §4.6).
     *  `summary = false`: a forward exceptional exit (analyzer-core.md §4.3). Steps 1 and 2 only: the exit sources, the
     *  exit sinks with their witnesses and their end facts. The facts end there: no global-state drop, no entry-mark
     *  removal, no summary edge. */
    private fun endAt(premise: PremiseKey, node: CommonInst, f: Facts, summary: Boolean) {
        val er = forms.endRules(key, node)                                              // ExitRules, both directions
        val w = RuleWorklist(er.rules, node, if (forward) Cut.EXIT_RULES else Cut.ENTRY_RULES)
        w.input(premise, f)                                                             // 1: f, the exit sources
        w.drain { pr, t, tr ->                                                          // 2 ran on (pr, t)
            if (!summary) return@drain                                                    // exceptional exit: the item ends
            var g: Facts? = t
            // 3: THE GLOBAL-STATE RULE (interpreter.md §4.7 step 3, G2, D30; ap-history.md F68): only on an item whose
            // premise is the zero fact (a state that this method or its callees set). A caller-set S fact is evaluated
            // (step 2: it can report, D21; a conjunctive literal stores it) but not dropped: it returns to the caller through
            // the summary, also the run-1 FLOW summary and its record. As today: the exit sinks run only on zero-premise
            // edges (SAST/jvm/sast/dataflow/JIRMethodExitRuleProvider.kt:18-19).
            if (er.globalStateDrop && pr.isZero && t.base == AccessPathBase.ClassStatic)
                for (part in tr.parts) g = g?.let { ops.without(it, part) }             //    the EVALUATED statics (checkSinks, §4.9)
            // 4: THE ENTRY MARKS (interpreter.md §4.7 step 4, G2, deviation D35): a source result (ap.md §7.2) on `this` or
            // `arg(i)` loses EVERY leaf with an entry mark, at every depth and with both tails: a `$` leaf and an
            // `[any-taint]` leaf (the Spring DTO source; its exclusion goes with it). The other leaves stay in their layer.
            // Today `TaintMarkRemover` (JVM/ap/ifds/analysis/JIRMethodSequentFlowFunction.kt:301-314) removes only the root
            // leaf `(b, [], $, m)`: a non-mark accessor is accepted with its whole subtree (D35).
            if (pr.isZero && t is TaintTree)
                er.entryMarkRemoval(t.base)?.let { marks ->                             //    null: not `this`, not `arg(i)`
                    g = g?.let { ops.withoutMarks(it, marks) } }                        //    (ap-impl.md §5.8, §23.4)
            g?.let { summaryDelta(pr, it) }                                             // 5
        }
    }

    /** analyzer-core.md §4.6 items 1–3 for one new summary delta j → g (E4). A publication carries the premise key with
     *  the tail and the exclusion of each member, and the restriction does not change it: the summaries of two
     *  must-premises with two exclusions and of the `[any]` premise of one path are three publications
     *  (analyzer-core.md §4.1, §4.6; Lean the must flag and the exclusion of the publication in
     *  PipelineAnyTaintEx.sysDRX).
     *  THE DEMAND EDGES (ap-history.md F70; analyzer-core.md §4.6; ap-impl.md §5.9 THE CALLS OF `demandPart`): the
     *  published pieces of the leaves of `delta` that are NOT crossable go to `summaries.addDemand`; the hand-off reads
     *  only them (§7.2). `demandPart` gives `delta` itself when no leaf is crossable (a summary with several premises, a
     *  demand-layer delta, a backward `{zero}` summary), so the publications serve twice; null when every leaf is
     *  crossable (a record, R1). The restriction acts leaf by leaf, so these pieces are exactly the publications of the
     *  non-crossable leaves (Lean Handoff.handF with Handoff.pubD or Handoff.pubR; Handoff.demOfN). */
    private fun summaryDelta(premise: PremiseKey, g: Facts) {
        checkKinds(premise, g)
        if (!r.shared.interpreter.isSummaryBase(g.base)) return                    // not a local
        val delta = summaries.add(premise, g) ?: return                                // item 1: no restriction
        edgeDeltas++                                                                   // the counters (§4.1); an exit fact is
        if (delta.layer == Layer.DEMAND) demandLayerEdges++                          // not pushed (§4.3), so count it here
        val pubs = published(premise, delta)                                           // item 2
        for (x in pubs) pending += Publication(premise, x)
        val part = ops.demandPart(premise, delta, config.direction)                    // F70: the leaves that are not crossable
        val pieces = if (part === delta) pubs else part?.let { published(premise, it) }.orEmpty()
        for (x in pieces) summaries.addDemand(premise, x)                              // the demand edges of the run
        if (part !== delta) crossableLeaves += ops.leaves(delta).count() - (part?.let { ops.leaves(it).count() } ?: 0)
        if (pubs.isNotEmpty()) requestWork()                                           // W1: a pending publication
    }

    /** analyzer-core.md §4.6 item 2 (Lean Handoff.pubD, Handoff.pubR): run 1 publishes the delta as it is; so does a backward
     *  {zero} summary (the balanced return of ap.md §9.2, unrestricted); a restricted run publishes the intersections
     *  with its demand patterns, in the locations and the marks (F71), by every pattern over the members, each result
     *  once (`restrictBy`, below). */
    private fun published(premise: PremiseKey, g: Facts): Collection<Facts> = when {
        config.run1 -> listOf(g)
        !forward && premise.isZero -> listOf(g)
        else -> LinkedHashSet<Facts>().also { out -> premise.forEachMember { j -> out += restrictBy(ops, config.demand!!, key, j, g) } }
    }

    private fun flushPublications() {                                    // today flushPendingSummaryEdges, MethodAnalyzer.kt:717-722
        if (pending.isEmpty()) return
        p.summaryStorage(key).publish(pending)
        pending = ArrayList()
    }
```

```kotlin
/** Top level. THE ONE RESTRICTION of a summary by the demand of its run, for ONE member `j` (DD12): `published` calls it
 *  for the publications and for the demand edges (`summaryDelta`). ap.md §6.4 AS AN INTERSECTION, IN THE LOCATIONS AND
 *  THE MARKS (ap-history.md F70, F71; Lean Handoff.restrictI, with the exclusion HandoffX.restrictIX): a demand edge `d`
 *  gives a result only if `j` lies INSIDE `D-c` in its locations AND its marks (Lean Handoff.insideB: the location part
 *  Handoff.insideLocB and the mark part markSubB; HandoffX.insideXB reads the exclusion of `j` too; the reference
 *  `insideDemand`), not only if it overlaps `D-c`: the marks of `j` must be a subset of the marks of `D-c` (`*` admits
 *  every mark, `T` only `T`, `*∖X` every mark that is not in `X`). THE MARK OF THE CONCLUSION: a conclusion leaf gives a
 *  result only if its mark meets the mark of `D-p` (Lean Handoff.concMarkB; the reference `marksMeet`): two concrete
 *  marks must be the same, a `*∖X` side does not admit a concrete mark in `X`, a `*` side meets every mark. A tree can
 *  hold leaves of several marks, so `ops.restrict` tests the mark of each leaf. In a restricted run both marks are
 *  concrete, so the test is "the same mark": the leaf `(ret, .f, $, T)` of the premise `(x, ., $, T)` against
 *  `D-c = (x, ., $, T)`, `D-p = (ret, .f, $, U)` gives nothing (Handoff.RVec.vMark_user_restrictI; with
 *  `D-p = (ret, .f, $, T)` it is kept, vMark_user_same). The test does not change the mark: a leaf with an abstract mark
 *  that the test keeps stays as it is (no restricted run has one). Before F71 the restriction read `D-c` and `D-p` as
 *  locations only, so it published that leaf (vMark_user_loc), and the hand-off could give it to the next run: a cost in
 *  precision and work, not a lost flow. The conclusion: below `D-p` the leaf as it is, if the tail of `D-p` admits the
 *  step; AT `D-p` the meet of the tails (`[any] ∩ $ = $`, `[any-taint]/E ∩ $ = $`,
 *  `[any-taint]/E ∩ */E2 = [any-taint]/(E ∪ E2)`; `[any] ∩ */E` keeps `[any]`, ap.md W2; `$` stays); above `D-p` an
 *  any leaf gives the chain of `D-p` (`$` for a `$` `D-p`; an `[any-taint]/E` leaf only if `E` admits the step down,
 *  and above a `*/E2` `D-p` with `E2`), a `$` leaf nothing. The layer stays. A restricted run has REACH and TAINT
 *  conclusions only (ap.md §7.2), and the patterns have no `[any-taint]` tail (ap.md W8 (d)). `ops.restrict` gives a
 *  LIST of trees (a normal TAINT tree has one exclusion, ap-impl.md §5.9); each is one publication. The restriction
 *  acts LEAF BY LEAF (ap-impl.md §8 test 7: `restrict` against its per-leaf reference form), so the restriction of the
 *  non-crossable part of a delta is the set of the publications of its leaves (the demand edges, `summaryDelta`). It
 *  only removes pairs, and it keeps every pair of a premise inside `D-c` (in its locations and its marks) whose exit
 *  location `D-p` covers with its mark (C5; Lean Handoff.restrictI_sub, Handoff.restrictI_contract;
 *  HandoffX.restrictIX_ok, HandoffX.restrictIX_contract): the mark test removes no such pair (Handoff.RAux.concMarkB_of_den). The form of C5 that reads the locations only is false for
 *  this restriction (Handoff.restrictI_contract_loc_false, HandoffX.XVec.restrictIX_contract_loc_false: the example
 *  above). An emitted premise lies inside its entry pattern with its mark (Handoff.emitM_insideB,
 *  HandoffX.emitX_insideXB; §4.2 `emit`), so the restriction loses nothing that the coverage needs. THE QUERY is
 *  `DemandStore.covering` (ap-impl.md §7.7): the patterns whose `D-c` is at or above `j`, the only ones that can hold
 *  `j` inside; before F70 it was `near` (every pattern that overlaps `j`). The query reads the locations only;
 *  `ops.restrict` tests the marks. */
fun restrictBy(ops: ApOps, demand: DemandStore, key: MethodKey, j: InitialAp, g: Facts): Sequence<Facts> =
    demand.covering(key, j.base, j.path).asSequence().flatMap { d -> ops.restrict(j, g, d) }
```

### 4.8 Requests (`analyzer-core.md` §4.6; `ap.md` §4.5, §4.10)

Both sides of the join are in one analyzer (§4.2: `addLink`, `addRequest`). It is a STANDING JOIN: a request stands for
the whole run, and a link that comes later meets it too. The engine uses the standing-join utility of `ap-impl.md`
§7.10, in its two-type form `StandingJoin<A, B>` (`newA`, `newB`; `KaryJoin` is the k-ary form over one type). The two Part I stores
are the sides: they deduplicate (E-3) and they are the indexes. `ap-impl.md` §5.10 gives the action of one pair:

```kotlin
    /** E2, E5, E7 (ap.md §8.8; `Store.standing_complete`). A side: requests (RequestStore) or links (AddedFactStore). */
    private var requestJoin: StandingJoin<Pair<InitialAp, RequestKind>, Link>? = if (!config.run1) null else StandingJoin(
        nearB = { (i, kind) -> when (kind) {                                                   // the links that a new request meets
            is RequestKind.Mark -> links.overlapping(i.base, i.path)
            is RequestKind.Position -> links.overlapping(AccessPathBase.ClassStatic, kind.path)   // the match reads (S, p)
        } },
        nearA = { link -> requests!!.overlapping(link.addedFact) },                              // the requests that a new link meets
        meet = { (i, kind), link -> act(i, kind, link.addedFact, link.caller) })

    private fun act(i: InitialAp, kind: RequestKind, a: Pattern, caller: CallerRef) =
        when (val x = ops.requestAction(i, kind, a, caller)) {
            is RequestAction.Answer -> addInitial(x.initial)                                 // a new initial fact (E3)
            is RequestAction.Climb -> p.send(RunEvent.RequestIn(caller.caller, x.premise, x.request))   // to the caller
            RequestAction.None -> Unit
        }
```

`freeze` drops `requestJoin` with `requests` (§4.11).

### 4.9 Sinks, witnesses, seeds, source hits (`analyzer-core.md` §4.7)

```kotlin
    /** The result of the sink check of one place: the triggered (sink, layer) pairs, and the EVALUATED parts: every part on
     *  which a pattern of a sink holds, also when a conjunctive sink has no full combination yet (endAt step 3 drops them
     *  from a zero-premise item only). */
    private class Triggers(val fired: List<Pair<SinkRule, Layer>>, val parts: List<Facts>) {
        operator fun plus(o: Triggers) = Triggers((fired + o.fired).distinct(), parts + o.parts)
        companion object { val NONE = Triggers(emptyList(), emptyList()) }
    }

    /** ap.md §4.9, §8.9, §8.10. Forward only: the backward run has no sink check. The check of one literal is checkMark
     *  (ap-impl.md §5.8), the same check as a conjunction literal (§4.3).
     *  THE GLOBAL-STATE RULE (analyzer-core.md §4.7; interpreter.md §4.7 step 3, D30): `parts` gets the part of EVERY
     *  literal that holds, plain or conjunctive, so endAt drops each evaluated static from the summary edge of a
     *  zero-premise item, also when the conjunctive sink has no full combination yet. A caller-set S fact (a premise that
     *  is not zero) is evaluated here, but endAt does not drop it (ap-history.md F68). The conjunctive branch stores the
     *  same evaluated part `m.facts` as the input of literal k (ConjunctionStore.Input.facts): it is the assumption of the
     *  later evaluations of the sink, so a later item can complete the combination with it (ap-history.md F67). */
    private fun checkSinks(premise: PremiseKey, node: CommonInst, c: Facts, sinks: List<SinkRule>): Triggers {
        if (!forward || sinks.isEmpty()) return Triggers.NONE
        val fired = ArrayList<Pair<SinkRule, Layer>>()
        val parts = ArrayList<Facts>()
        for (s in sinks) for ((k, lit) in s.patterns.withIndex()) when (val m = ops.checkMark(c, lit, mode)) {
            MarkCheck.None -> Unit
            is MarkCheck.Request -> raise(premise, c, RequestKind.Mark(m.mark))     // a FLOW fact (run 1, ap.md §4.5)
            is MarkCheck.Holds -> {                                               // REACH, or the TAINT leaves with the mark
                parts += m.facts                                                  // EVALUATED: dropped at a normal exit
                if (!s.conjunctive) {
                    witness(s, node, listOf(SinkEdge(premise, m.facts.layer, m.facts)))
                    fired += s to m.facts.layer
                } else for (comb in conjunctions!!.add(s, node, s.patterns.size, k,      // per alternative (s), statement, literal;
                        ConjunctionStore.Input(premise, m.facts.layer, m.facts))) {     // the evaluated part is the input.
                                                                                        // TERMINATION: Input is compared by
                                                                                        // VALUE (DD4; ap-impl.md §7.10)
                    witness(s, node, comb.inputs.map { SinkEdge(it.premise, it.layer, it.facts!!) })   // one witness per sink edge set
                    fired += s to comb.layer
                }
            }
        }
        return Triggers(fired.distinct(), parts)
    }

    /** ap.md §8.10; analyzer-core.md §4.7. THE KEY is (rule, method, statement) with the METHOD of the method key, without
     *  the context: one sink statement in several contexts is one vulnerability (ap-history.md F67). The WITNESS names its
     *  alternative and its method key: the confirmation reads the support of its premise set in that method key (§7.5).
     *  The store keeps one entry per (key, alternative, method key, run, shape) whose facts are the union (ap-impl.md
     *  §7.12): witnesses of two alternatives or two method keys never merge, so no merge sees two group keys. */
    private fun witness(s: SinkRule, node: CommonInst, edges: List<SinkEdge>) =
        r.vulnerabilities.add(VulnerabilityKey(s.rule, key.method, node),
            SinkWitness(s.alternative, key, edges, config.index, s.endFacts.map { it.edge.to }))

    /** ap.md §9.2 rule seed: where the zero fact reaches `node`, Zero → requirement (a TAINT fact: the seed has a
     *  concrete mark), cut by the field limit. The seeds of the hand-off (`SeedIndex`, §7.2). */
    private fun fireSinkSeeds(node: CommonInst, emit: (Facts) -> Unit) {
        for (seed in config.seeds.at(key, node)) if (seed is Seed.Sink) seedFact(seed.requirement, emit)
    }

    /** THE TRIGGER OF AN END FACT (ap.md §9.2; analyzer-core.md §4.5; ap-history.md F70). An end fact exists only after
     *  its sink triggers, so its reversal demands the trigger: a reversed end-fact edge of the sink alternative `s` at
     *  `node` gave a result on a requirement (`RuleWorklist.drain`, §4.4; `CallStage.Edges.trigger`, §4.5), so the seeds
     *  of `s` fire at `node`: one per positive literal (`SinkRule.seedPatterns()`; none if unconditional), ONCE per
     *  (node, s) in this method key (`triggered`). Also when the vulnerability of `s` is CONFIRMED: the hand-off seeds only the DEMAND
     *  vulnerabilities (§7.2), and without this seed the next forward run does not demand the witness of the trigger, so
     *  the sink does not trigger and the end fact is lost (program END, §9.1 row 31). The seeds come from the forms of the
     *  sink, not from the `SeedIndex`, which stays read-only (analyzer-core.md A4). Argued: the model has no end facts
     *  (ap.md §11.2). */
    private fun fireTriggerSeeds(node: CommonInst, s: SinkRule, emit: (Facts) -> Unit) {
        if (!triggered.add(node to s)) return
        for (lit in s.seedPatterns()) { triggerSeeds++; seedFact(lit, emit) }        // the counters (§4.1)
    }

    /** One seed requirement: Zero → `p` in the normal layer (`targetTree` puts an `[any]` requirement in the demand layer,
     *  ap.md W6), cut by the field limit (ap.md §4.4 row 7). */
    private fun seedFact(p: Pattern, emit: (Facts) -> Unit) =
        cut(Cut.SEED, ap.zero, ops.targetTree(p.fact, Layer.NORMAL)) { _, t -> emit(t) }
```

`targetTree` puts an `[any]` requirement in the demand layer (`ap.md` W6). So the seed of an `[any]` sink pattern is
`[any]`, a demand edge: the backward run has no `[any-taint]` (`ap.md` W8 (d), §9.2). The rules of `analyzer-core.md` §4.7
are in this code:

| Rule | Code |
|---|---|
| a witness per sink edge or per sink edge set; the key without the context; the witness names its alternative and its method key | `checkSinks` → `witness` |
| the global-state rule: every evaluated static of a zero-premise item goes; a caller-set `S` fact is evaluated and stays (`interpreter.md` D30); a conjunctive sink stores it as the literal input | `checkSinks` (`parts`, `ConjunctionStore.Input.facts`) → `endAt` step 3 (`pr.isZero`, §4.7) |
| exit sinks at both exits; no summary at an exceptional exit (`analyzer-core.md` §4.3) | `exitRulesAt` → `endAt(summary = false)` (§4.3, §4.7) |
| sink seed at a call | `zeroAtCall` (§4.10) → `fireSinkSeeds` → `flow(BOUND)` |
| an `[any-taint]/E` sink fact triggers as `[any]` on its ADMITTED locations only; a normal `[any-taint]` sink edge can be confirmed (`ap.md` §4.9) | `checkSinks` → `checkMark` (`ANY_TAINT` reads as `ANY`; the exclusion `E` is a part of the location set, Lean `AnyTaintEx.checkX`: a sink pattern in the excluded part gives no witness, `AnyTaintExCases.S.run1_name_no_trigger`); `SinkEdge(premise, layer, facts)` keeps the layer; `Support.confirm` reads the layer only (§7.5) |
| sink seed of an exit sink, at a normal or an exceptional exit | `startAt` (backward, zero premise): then the reversed exit rules of that exit (§4.4) |
| THE TRIGGER OF AN END FACT (backward; `analyzer-core.md` §4.5): a reversed end-fact edge of the sink alternative `A` at the statement `s` that applies to a requirement gives the zero fact and fires the sink seeds of `A` at `s`, once per (method key, `s`, `A`), also when the vulnerability of `A` is CONFIRMED | at a boundary `RuleWorklist.drain` (§4.4), at a call the reversed `END_FACTS` stage (`applyStage`: its `trigger`, `ap-impl.md` §23.5; §4.5) → `fireTriggerSeeds` → `seedFact`; the seeds enter where the seeds of the hand-off enter (step 1 of the boundary; `BOUND` of the call) |
| source seed filter | `FormApplier` (`ap-impl.md` §23.3) → `EngineAlgebra.allowsSource` at a source-seed place: a statement summary, `RuleStatement.summary`, a `SOURCES` stage (DD8; `ap-impl.md` §23.1). It does not filter a record: a zero-premise record of a source in a crossable callee applies whatever the source seeds (Lean `HandoffSrc.SrcRec.found_unseeded`; it adds facts of the program and removes none: precision only) |
| a source hit whatever `edges.add` gives, also for a duplicate zero result | `FormApplier` → `EngineAlgebra.sourceHit`, once per micro edge that gives a result; the hit does not read the edge store |
| the end facts are not sources | `FormApplier.gen`, and the `END_FACTS` stage with `sources = false` |
| no sink check backward | `checkSinks` returns at once |

### 4.10 The zero fact at a call (`analyzer-core.md` §4.5; rules `zpass`, `zin`, `zret`)

```kotlin
    /** `item.facts` is REACH (ap.md §7.2): the zero fact. */
    private fun zeroAtCall(item: EdgeDelta, ctx: CallCtx) {
        emitUnchanged(item)                                    // never touched: it passes (zpass; rule pass for any premise)
        // DD7, Lean Backward.lean:158-180: zin, seed and zret read ONLY the edge {zero} -> zero. A backward `jb -> zero`
        // (a reversed source or end fact reached the zero fact, ap.md §7.2) only passes over the call. The forward run has
        // no other REACH edge.
        if (!item.premise.isZero) { check(!forward); return }
        if (forward) {                                                                   // BIND_IN has `zero.* -> zero.*`:
            flow(ctx, ctx.plan.entry, listOf(PlanFact(item.premise, item.facts, null)))  // sinks, sources, ADDED (ap-impl.md §28.7)
            return
        }
        val seeds = ArrayList<PlanFact>()
        fireSinkSeeds(item.node) { t -> seeds += PlanFact(ap.zero, t, null) }           // a zero-to-fact edge (rule seed)
        if (seeds.isNotEmpty()) flow(ctx, CallPoint.BOUND, seeds)                        // then the reversed BIND_IN
        val ref = CallerRef(key, ap.zero, ctx.callerLayer, item.node)
        for (m in ctx.plan.callees?.callees.orEmpty()) {
            p.subscribe(Subscription(m, ref, ctx.callerLayer, item.facts, zeroOnly = true))   // zret: zero-premise publications
            p.send(RunEvent.ZeroIn(m))                                                   // zin
        }
    }
```

The `zret` application is the `part.zeroOnly` branch of `applySummary` (§4.6): the conclusion itself, at `ADDED`, with
the zero premise of the caller.

### 4.11 Summaries with several premises (E6, `analyzer-core.md` §5.4)

The join is `ConjunctionStore.ndJoin` of `ap-impl.md` §7.10 (DD5): one `NdSummaryJoin<Subscription>` per
`NdKey(callee, premise key, layer of the publication, call statement)`. `NdSummaryJoin` is a `KaryJoin` (`ap-impl.md`
§7.10). The analyzer is a thin adapter:

```kotlin
    /** A part satisfies member `m` of `pub` (a part goes under EVERY index that it satisfies: `matches` is called per
     *  index). First the new part with every stored conclusion, then the new delta with every full combination. No member
     *  of a PremiseSet is the zero fact (ap.md §4.6), so a zero subscription never satisfies one and never comes here. */
    private fun ndMatch(part: Subscription, pub: Publication, premise: PremiseSet, m: Int) {
        check(!part.zeroOnly && part.added !is Reach && !premise.member(m).isZero)    // E6 never takes the zero subscription
        val conclusion = checkNotNull(pub.conclusion as? TaintTree) { "an ND edge is TAINT (ap.md §4.6)" }
        val join = conjunctions!!.ndJoin<Subscription>(ConjunctionStore.NdKey(part.callee, premise, pub.layer, part.ref.call))
        for ((combo, g) in join.addSubscription(m, part)) applyCombination(combo, premise, g)
        for ((combo, g) in join.addConclusion(conclusion)) applyCombination(combo, premise, g)
    }

    /** One full combination and one conclusion. The result premise is the union of the caller premise sets, ApManager.union:
     *  it drops the zero fact, so it is `{zero}` only if every caller premise is `{zero}` (ap.md §4.6). The conclusion of an
     *  ND summary is a TaintTree (ap.md §4.6, ap.md W7; NdSummaryJoin gives TaintTree values, ap-impl.md §7.10), so no
     *  request comes from it. The results are cut at the plan exit (Cut.CALL, ap.md §4.4 row 6). */
    private fun applyCombination(parts: List<Subscription>, premise: PremiseSet, g: TaintTree) {
        val union = parts.map { it.ref.premise }.reduce(ap::union)
        fromCallees(parts[0].ref) { results ->                          // one call statement (the key)
            ops.applyCombination(parts.mapIndexed { k, s -> s.added to premise.member(k) }, g, mode,
                collect(union, g) { pr, t -> results += PlanFact(pr, t, Origin.SUMMARY_EFFECT) })
        }
    }

    /** analyzer-core.md §7.6: the run ended. The edge stores (`edges`, `initials`) and the links of a backward run go now:
     *  the barrier never reads them (§7.7). The stores that the barrier reads stay until the driver drops the RunResult
     *  (the return of `runOnce`, §7.1): the links of a forward run (the confirmation), the summaries (`persist`, the
     *  hand-off), the source hits (backward). The run machinery and the run context (its RunConfig: the demand, the
     *  seeds, the record view) go now. No handler runs after it. */
    fun freeze() {
        port = null; rctx = null; worklist = DeltaWorklist(); pending = ArrayList()
        requests = null; requestJoin = null; conjunctions = null; triggered.clear()
        edgeStore = null; initialStore = null; if (!forward) linkStore = null       // analyzer-core.md §7.6
    }
}   // end of RunMethodAnalyzer
```

THE ZERO FACT IN E6. No member of a `PremiseSet` is the zero fact: a conjunction drops it from the union of the premise
sets (`ap.md` §4.6; `analyzer-core.md` §5.4). So the zero subscription never takes part in E6 (`ndMatch` asserts it),
and `matches` gives null for a REACH part and a member that is not zero. The backward run has no summary with several
premises (`ap.md` §9.2).

---

## 5. The pipeline (`analyzer-core.md` §5)

### 5.1 Events

```kotlin
/** analyzer-core.md §5.1, §10. DD3: LinkIn carries the new links of one link key as one group of facts. */
sealed interface RunEvent {
    data class Start(val root: MethodKey) : RunEvent
    data class LinkIn(val callee: MethodKey, val ref: CallerRef, val linkLayer: Layer, val added: Facts) : RunEvent
    data class ZeroIn(val callee: MethodKey) : RunEvent
    data class RequestIn(val method: MethodKey, val premise: InitialAp, val request: RequestKind) : RunEvent
    data class Delivery(val callee: MethodKey, val publications: List<Publication>) : RunEvent
    class Work(val analyzer: RunMethodAnalyzer) : RunEvent
}

/** The handler of each event. True: the event ends (Q2). UnitRunner and the fuzzer share it. */
internal fun RunnerPort.handle(event: RunEvent): Boolean {
    when (event) {
        is RunEvent.Start -> analyzer(event.root).addRootZero()
        is RunEvent.LinkIn -> analyzer(event.callee).addLink(event.ref, event.linkLayer, event.added)
        is RunEvent.ZeroIn -> analyzer(event.callee).addZeroEntry()
        is RunEvent.RequestIn -> analyzer(event.method).addRequest(event.premise, event.request)
        is RunEvent.Delivery -> subscriptions.onDelivery(event.callee, event.publications)
        is RunEvent.Work -> return event.analyzer.work(RUNNER_STEPS_QUANT)
    }
    return true
}

const val RUNNER_STEPS_QUANT = 1000                                   // today TaintAnalysisUnitRunner.kt:517
```

### 5.2 `SummaryStorage` and `PublicationIndex` (callee side)

```kotlin
/** analyzer-core.md §10. A delta of a published summary (after the restriction in a restricted run). `premise` holds the
 *  tail and the exclusion of each member: a must-premise `[any-taint]/E`, a must-premise with another exclusion and the
 *  `[any]` premise of one path are three premise keys, so three publications (analyzer-core.md §4.6; Lean
 *  PipelineAnyTaintEx: a publication carries the callee premise with its flag and its exclusion). */
data class Publication(val premise: PremiseKey, val conclusion: Facts) {
    val layer: Layer get() = conclusion.layer
}

/** analyzer-core.md §5.2. One per method key and run (O2). ADAPT of SummaryEdgeStorageWithSubscribers. */
class SummaryStorage(val method: MethodKey, ap: ApManager, ops: ApOps, private val steps: ProtocolSteps) {
    private val lock = Any()
    private val published = PublicationIndex(ap, ops)
    private val subscribers = ConcurrentLinkedQueue<SubscriptionManager>()   // today :752

    /** Only the runner of `method` calls it. P2: insert, then notify (today addEdges :771-796). */
    fun publish(pubs: List<Publication>) {
        val delta = synchronized(lock) { published.addAll(pubs) }            // ap.md T4: the new part only
        if (delta.isEmpty()) return
        steps.notify { for (s in subscribers) s.notify(method, delta) }       // one Delivery per subscribed runner
    }

    fun addSubscriber(s: SubscriptionManager) { subscribers.add(s) }        // today subscribeOnEdges :910-912

    /** P3: a linearizable read (the lock). The result is a snapshot list; `matches` runs outside the lock. */
    fun candidates(part: Subscription, mode: ApMode): List<Pair<Publication, Int>> =
        synchronized(lock) { published.candidates(part, mode) }
}

/** The publications of one method key: a path trie keyed by base :: path of each premise MEMBER (analyzer-core.md §5.2).
 *  Under the lock of its SummaryStorage (ap-impl.md §7.1: a PathTrie has one owner). */
class PublicationIndex(private val ap: ApManager, private val ops: ApOps) {
    private data class Member(val premise: PremiseKey, val index: Int)
    private val interners = ap.newInterners()                        // ap-impl.md §5.1, DD5: the node interner of this index
    private val merged = HashMap<PremiseKey, ConclusionGroup>()      // ap-impl.md §4.3: merge and delta per premise key; NOT the
                                                                      // hand-off store. The publication is the merged conclusion.
    private val byMember = PathTrie<Member>()                         // ap-impl.md §7.2; two premise keys at one path (other
                                                                      // tail or exclusion) are two Members (analyzer-core.md §5.2)

    fun addAll(pubs: List<Publication>): List<Publication> {
        val out = ArrayList<Publication>()
        for (pub in pubs) {
            val group = merged.getOrPut(pub.premise) {
                for (m in 0 until pub.premise.size) pub.premise.member(m).let { j -> byMember.add(j.base, j.pathArray, Member(pub.premise, m)) }
                ConclusionGroup(ap, interners)
            }
            val d = group.add(pub.conclusion) ?: continue
            out += Publication(pub.premise, d)                         // the notification sends the delta only
        }
        return out
    }

    /** The replay column of the table of analyzer-core.md §5.3, per leaf of the part: run 1 `applicable` (j at or above
     *  a) = lookupPrefixes; restricted `inside` (j at or below a) = lookupExtensions. PipelineStore.replay_run1,
     *  replay_restricted. The replay gives the MERGED conclusion of each candidate premise (one Facts per group key,
     *  ConclusionGroup.all), not each stored delta: one `matches` and one `applySummary` per (premise, group key), and no
     *  second copy of the conclusion. P4 holds: `matches` reads only the premise member. */
    fun candidates(part: Subscription, mode: ApMode): List<Pair<Publication, Int>> {
        val members = LinkedHashSet<Member>()
        if (part.zeroOnly) byMember.lookupExtensions(AccessPathBase.Zero, IntArray(0)).filterTo(members) { it.premise.isZero }
        else for (leaf in ops.leaves(part.added)) {
            val path = leaf.fact.path.toIntArray()
            members += if (mode.run1) byMember.lookupPrefixes(leaf.fact.base, path) else byMember.lookupExtensions(leaf.fact.base, path)
        }
        return members.flatMap { m -> merged.getValue(m.premise).all().map { Publication(m.premise, it) to m.index }.toList() }
    }
}
```

P3 alternative: the writer publishes an immutable snapshot of `merged` and `byMember` with a volatile write; the reader
reads the snapshot with no lock. The first implementation uses the lock.

### 5.3 `SubscriptionManager` and `CalleeSubscriptions` (caller side)

```kotlin
/** analyzer-core.md §10, in the tree form of DD3: the added facts of one link key. Equality by value (E-3). The link key
 *  holds the group key of `added`, so an `[any-taint]` added fact keeps its tail (the layer) and its exclusion (the tree
 *  exclusion, ap.md §8.3; Lean PipelineAnyTaintEx: a link carries the added fact with its flag and its exclusion). */
data class Subscription(
    val callee: MethodKey,
    val ref: CallerRef,
    val linkLayer: Layer,
    val added: Facts,                          // a REACH for a zero subscription
    val zeroOnly: Boolean = false,             // backward rule zret
) {
    val caller: MethodKey get() = ref.caller
}

/** P4: the ONE match function of the replay and of the delivery (ap.md §4.3; DD3). The part of `sub.added` that
 *  satisfies member `m` of `pub`, or null. `satisfying` is `applicable` in run 1 and `inside` in a restricted run.
 *  A must-premise (`[any-taint]`, with its exclusion) occurs only in a forward restricted run, so `matches` gives it
 *  `inside`, the test that its summaries need (analyzer-core.md §5.3; Lean AnyTaintEx.SatInsideX, satX_inside);
 *  `satisfying` reads `ANY_TAINT` as `ANY` and reads the exclusions of both sides as a part of their location sets: a
 *  member at a step that the exclusion of the added fact excludes is not inside it (Lean AnyTaintEx.satX, insideExB).
 *  THE KINDS (ap.md §7.2): a FLOW part never satisfies a member with a concrete mark (`applicable` needs `markSub(T, *)`),
 *  so a FLOW added fact never meets a TAINT summary; the result is null and no request is raised (§4.6). */
fun matches(sub: Subscription, pub: Publication, m: Int, ops: ApOps, mode: ApMode): Facts? =
    if (sub.zeroOnly) sub.added.takeIf { pub.premise.isZero }              // zret: no test
    else ops.satisfying(sub.added, pub.premise.member(m), mode)
```

```kotlin
/** analyzer-core.md §5.3. One per runner (O3). ADAPT of SummaryEdgeSubscriptionManager. */
class SubscriptionManager(private val port: SubscriptionPort) {
    private val byCallee = HashMap<MethodKey, CalleeSubscriptions>()        // runner-local (O3)
    private val mode get() = port.config.mode
    private val ops get() = port.ops

    /** analyzer-core.md §4.5 SUBSCRIBE. */
    fun subscribe(sub: Subscription) {
        val storage = port.summaryStorage(sub.callee)                         // O2: any unit
        val entry = byCallee.getOrPut(sub.callee) {
            CalleeSubscriptions(ops).also { storage.addSubscriber(this) }     // P1: register first
        }
        val part = entry.add(sub) ?: return                                   // E-3: an old link key and no new leaf
        port.steps.replay { replay(storage, part) }                           // P1: the read after the registration
    }

    private fun replay(storage: SummaryStorage, part: Subscription) {
        for ((pub, m) in storage.candidates(part, mode)) applyMatch(part, pub, m)   // P3, then P4
        if (!part.zeroOnly && port.config.restricted) replayRecords(part)        // run 1 reads no record
    }

    /** P4: the ONE match and its application, for the replay and the delivery. */
    private fun applyMatch(part: Subscription, pub: Publication, m: Int) =
        matches(part, pub, m, ops, mode)?.let { port.applier(part.caller).applySummary(part.copy(added = it), pub, m) }

    /** ap.md §8.7 R2–R4 (ap-impl.md §7.8): byEntry in this direction; byExit and Record.reversedAt for the other
     *  direction. Records are read-only (analyzer-core.md A4): only the replay reads them. One record applies once per
     *  part (`seen`). THE KINDS (ap.md §7.2): a run-1 record with a `*` premise has a FLOW conclusion; it applies to a
     *  TAINT part as a transfer function and gives TAINT, so the restricted run stays concrete.
     *  THE TAIL `[any-taint]`: a MUST RECORD (a forward record with an `[any-taint]` premise) applies in its direction
     *  with the record demotion of `applyRecord` (§4.6), and `rec.reversedAt` gives no reversal of it (ap.md §8.7 R3;
     *  Lean AnyTaintExact.CexRev.cex_rev). R3 IS LEAF BY LEAF (`byExit` keys each leaf): of any other record,
     *  `reversedAt` gives no reversal of an `[any-taint]/E` conclusion leaf with `E ≠ {}`, and the other leaves of the
     *  same record reverse. A forward record `$ -> [any-taint]` (`E = {}`) reverses into `[any] -> $`: a backward record with
     *  an `[any]` premise (ap.md §9.1). It applies only to an `[any]` requirement, which is in the demand layer, so its
     *  results are demand as every result of an `[any]` requirement (a reuse limit, analyzer-core.md §11).
     *  A CROSSABLE RECORD REPLACES THE ANALYSIS (ap-history.md F70; ap.md §8.7): the hand-off gives no demand edge for a
     *  crossable summary leaf (§7.2), so the callee gets no initial fact for it, and this replay is the only way the
     *  call returns that result: by the record in its direction, or by its reversal in the other direction (Lean
     *  Handoff.FlowRR, the case `rcall`; Handoff.cross_applies: a crossable premise is satisfied by `inside` or `applicable`
     *  for every CONCRETE added fact that covers one of its locations; every restricted run is concrete). The zero fact
     *  still enters the callee: F70 does not localize it (analyzer-core.md §11). A zero-premise record of a source in the
     *  callee applies whatever the source seeds of the run (Lean HandoffSrc.SrcRec.found_unseeded: the source seeds do not
     *  filter the records; precision only). */
    private fun replayRecords(part: Subscription) {
        val records = port.config.records
        val direction = port.config.direction
        val applier = port.applier(part.caller)
        val seen = HashSet<Any>()
        fun applyRec(rec: Record) =                                           // R4: applicable || inside
            ops.satisfying(part.added, rec.premise, mode, record = true)?.let { applier.applyRecord(part.copy(added = it), rec) }
        for (leaf in ops.leaves(part.added)) {
            for (rec in records.byEntry(part.callee, leaf))
                if (rec.direction == direction && seen.add(rec)) applyRec(rec)
            for (rec in records.byExit(part.callee, leaf))
                if (rec.direction != direction)
                    for (rev in rec.reversedAt(leaf))                        // only the mark-reversible leaves
                        if (seen.add(rev.premise to rev.conclusion)) applyRec(rev)   // by value (DD4): new facts per call
        }
    }

    /** The notification of a callee storage. Any thread; reads no state of this manager (O3). */
    fun notify(callee: MethodKey, pubs: List<Publication>) = port.post(RunEvent.Delivery(callee, pubs))

    /** The handler of a Delivery. P6: match against the subscriptions NOW. */
    fun onDelivery(callee: MethodKey, pubs: List<Publication>) {
        val entry = byCallee[callee] ?: return
        for (pub in pubs) for (m in 0 until pub.premise.size)
            for (part in entry.candidates(pub, m, mode)) applyMatch(part, pub, m)   // complete for `matches`; P4
    }
}
```

```kotlin
/** ap.md §8.4: the subscriptions of one runner to one callee. One merged tree per link key, the delta on insert
 *  (as MethodTreeAccessPathSubscription.kt:127-160). The index replaces AccessTreeIndex (:199-283). */
class CalleeSubscriptions(private val ops: ApOps) {
    private val trees = AddedFactStore(ops.manager)   // ap-impl.md §7.5: EXACT merge per link key; add → the new links
    private val parts = ArrayList<Subscription>()     // every inserted delta; never removed (P5)
    private val index = PathTrie<Int>()               // the key of each leaf → part id
    private val zeroParts = LinkedHashMap<CallerRef, Int>()

    fun add(sub: Subscription): Subscription? {
        if (sub.zeroOnly) {
            if (sub.ref in zeroParts) return null
            zeroParts[sub.ref] = parts.size; parts += sub
            return sub
        }
        val delta = trees.add(sub.ref, sub.linkLayer, sub.added) ?: return null
        val part = sub.copy(added = delta)
        val id = parts.size; parts += part
        for (leaf in ops.leaves(delta)) index.add(leaf.fact.base, leaf.fact.path.toIntArray(), id)
        return part
    }

    /** The delivery column of the table of analyzer-core.md §5.3: run 1 `applicable` (a at or below j) =
     *  lookupExtensions(j); restricted `inside` (a at or above j) = lookupPrefixes(j). PipelineStore.deliver_run1,
     *  deliver_restricted. */
    fun candidates(pub: Publication, m: Int, mode: ApMode): Sequence<Subscription> {
        val j = pub.premise.member(m)
        val ids = if (mode.run1) index.lookupExtensions(j.base, j.pathArray) else index.lookupPrefixes(j.base, j.pathArray)
        val zero = if (pub.premise.isZero) zeroParts.values else emptyList()
        return (ids + zero).distinct().asSequence().map { parts[it] }
    }
}
```

```kotlin
// Why the two paths agree (DD3, P4): both call `matches`, so both call `satisfying` on the WHOLE part. The index only
// picks candidates; each lookup is complete per leaf (PipelineStore). `satisfying` is per leaf, so the parts (deltas)
// of one link key give the applications of the merged tree. No INDEX_LIMIT bypass, no literal-accessor walk.
```

`IndexCompletenessTest` checks it (§9.1).

### 5.4 P1–P6 in the code

| # | Condition | Code |
|---|---|---|
| P1 | register before read | `SubscriptionManager.subscribe`: `storage.addSubscriber(this)` in `getOrPut`, then `steps.replay { replay(...) }` |
| P2 | insert before notify | `SummaryStorage.publish`: `synchronized(lock) { published.addAll }`, then `steps.notify { for (s in subscribers) ... }` |
| P3 | linearizable read | `SummaryStorage.candidates`: `synchronized(lock) { published.candidates(...) }` |
| P4 | one match function, complete candidates | `applyMatch` (the one call of `matches`) in `replay` and in `onDelivery`; `PublicationIndex.candidates`, `CalleeSubscriptions.candidates` (the table of `analyzer-core.md` §5.3) |
| P5 | no removal | `subscribers`, `parts`, `index`, `merged` only grow; `RunManager.run` drops them after the join |
| P6 | match at delivery | `onDelivery` reads `byCallee` when the runner handles the `Delivery` |
| E-3 | exact deduplication | `links.add`, `CalleeSubscriptions.add` (exact `AddedFactStore`), `requests.add`, `initials.add`; `edges.add` also subsumes |

---

## 6. Scheduling (`analyzer-core.md` §6)

### 6.1 The runner loop

The loop of today (`TaintAnalysisUnitRunner.kt:193-263`). The changes: the events of §5.1, the shared `handle`, fixed
priority keys, `Work` into the local queue (W1), and the catch of `Cancellation.Cancelled`.

```kotlin
    // UnitRunner
    suspend fun runLoop() = coroutineScope {
        var events = 0
        while (isActive) {
            if (queue.isEmpty()) queue.add(channel.receive())                     // today :196-198
            while (true) queue.add(channel.tryReceive().getOrNull() ?: break)     // today :200-203
            val event = queue.poll()!!
            val ended = try { handle(event) }                                     // EventDispatch.kt
                catch (e: Cancellation.Cancelled) {                               // a checkpoint of the ApManager or the alias
                    check(run.ended) { "a cancel with no end" }                   // analysis: RunManager.fail set the status
                    return@coroutineScope                                         // first; the run keeps the status of its cause
                }
            if (ended) run.inFlight.afterHandler()                                // Q2: after the handler and its sends
            else queue.add(event)                                                 // W2: still counted; a new fixed key
            if (event is RunEvent.Work || ++events >= RUNNER_STEPS_QUANT) { events = 0; yield() }   // today :205-208
        }
    }
```

`Cancellation.Cancelled` is a `CancellationException` (`CORE/util/Cancellation.kt:6`), so the
`CoroutineExceptionHandler` of `RunManager.start` never sees it. EVERY CANCEL HAS A KNOWN CAUSE (`analyzer-core.md`
§6.3): the status is set before every cancel. The causes in a run: the timeout of the run (`fail(TIMEOUT)` in
`RunManager.run`), the memory guard of the run (`fail(OOM)`, the `MemoryManager` callback) and a runner failure
(`fail(FAILED)`: the handler of `RunManager.start`, or the catch of the caller-thread code of `run`). `RunManager.fail`
sets the status first, then cancels and completes the run together. So the runner only stops: the run keeps the status
of its cause, and `run.ended` is true (the `check`). The barrier guard (§7.1) also cancels, but no runner is alive then.
There is no external cancel.

A `Work` event runs at most `RUNNER_STEPS_QUANT` steps. It also stops when the zero-work state of the analyzer changes.
Then the analyzer goes back into the queue with a new key. Both rules are as today (`TaintAnalysisUnitRunner.kt:217-221`).

### 6.2 The local queue with fixed keys

```kotlin
/** The local priority queue. The key of an event is computed ONCE, when the event enters the queue
 *  (analyzer-core.md §6.1). The order of today (EventComparator, TaintAnalysisUnitRunner.kt:47-72): analyzers with
 *  zero-to-zero work, then other events, then analyzers with fewer steps. */
class EventQueue {
    private class Entry(val event: RunEvent, val rank: Int, val steps: Long, val seq: Long)
    private val heap = PriorityQueue(compareBy<Entry>({ it.rank }, { it.steps }, { it.seq }))
    private var seq = 0L

    fun add(e: RunEvent) {
        val (rank, steps) = when (e) {
            is RunEvent.Work -> (if (e.analyzer.hasZeroWork) 0 else 2) to e.analyzer.steps
            else -> 1 to 0L
        }
        heap.add(Entry(e, rank, steps, seq++))
    }
    fun poll(): RunEvent? = heap.poll()?.event
    fun isEmpty(): Boolean = heap.isEmpty()
}
```

### 6.3 `InFlight` and local work

```kotlin
/** analyzer-core.md §6.2, §10. One per run (Q4). `onZero` is the quiescence: RunManager sets the status there by
 *  `compareAndSet(null, COMPLETE)`, so the first end of the run wins (§3.2). */
class InFlight(private val onZero: () -> Unit) {
    private val count = AtomicLong(0)
    private val handledCount = AtomicLong(0)                              // the progress log only
    val pending: Long get() = count.get()
    val handled: Long get() = handledCount.get()
    fun beforeSend() { count.incrementAndGet() }                          // Q1
    fun afterHandler() { handledCount.incrementAndGet(); if (count.decrementAndGet() == 0L) onZero() }   // Q2
}
```

| Rule | Code |
|---|---|
| Q1 increment before send | `UnitRunner.post`, `UnitRunner.enqueue`; `RunManager.route` counts only when a runner exists |
| Q2 decrement after the handler | `runLoop`: `afterHandler()` after `handle` returns true; `InFlight.handled` counts it for the progress log |
| Q3 guard during the start | `RunManager.run`: `beforeSend()` before the `Start` events, `afterHandler()` after |
| Q4 one counter per run | `RunManager.inFlight`; a new `RunManager` per run; the join (§6.4) stops old runners |
| W1 `queued`, then `Work` | `RunMethodAnalyzer.requestWork`, called by `push` (every `normal` add), by `emitUnchanged` (every new `unchanged` item) and by `summaryDelta` (a pending publication), also from `addLink`, the replay and a request answer |
| W2 back to the local queue, still counted | `work` returns false; `runLoop` re-adds it with no `afterHandler` |
| W3 end only when empty and flushed | `work`: `flushPublications()`, then `queued = false`, then true |

### 6.4 Abnormal end, the run scope, the join

| `analyzer-core.md` §6.3 rule | Code |
|---|---|
| status `COMPLETE`, `TIMEOUT`, `OOM`, `FAILED` | `RunStatus`; `RunManager.fail` |
| the first end wins | `RunManager.status`: the quiescence (`InFlight` zero) does `compareAndSet(null, COMPLETE)`; `fail` does `compareAndSet(null, s)`; `run` reports `status.get()` |
| the status is set before every cancel, so every cancel has a known cause: the timeout, a memory guard (of a run or of the barrier) or a runner failure | `RunManager.run`: `fail(TIMEOUT)`; the `MemoryManager` callback: `fail(OOM)`; the runner handler and the catch of `run`: `fail(FAILED)`; at the barrier the barrier guard is the only canceller (§7.1); `runLoop` catches `Cancellation.Cancelled` and only stops (§6.1) |
| the `Cancellation` is activated when the run is made | `RunManager.init` (§3.2), before the driver publishes the manager |
| no run after an incomplete run; the incomplete run adds nothing | `IterationDriver.runOnce` gives `Next.End`, and `analyze` returns the report of the earlier complete runs (§7.1) |
| a `SupervisorJob` scope per run | `RunManager.job`, `scope`; a failed runner calls `fail(FAILED)`, which ends THIS run before its timeout (the other runners stop at their next checkpoint); it cannot cancel a later run |
| join every runner, on every exit; a runner that does not stop stops the analysis; the join overrides the first end | `RunManager.stopAndJoin`, also after a throw of the caller-thread code of `run` (its catch, §3.2); false: `run` reports `FAILED`, also after the quiescence, and gives no analyzers (§3.2) |
| cancel and complete together | `RunManager.fail`: `cancellation.cancel()` and `completion.complete(s)` |
| a `Throwable` on the driver thread ends the analysis with the report so far | `IterationDriver.analyze`: one `catch (e: Throwable)` over the whole loop body (§7.1): `FAILED`, `ABNORMAL` |

No external cancel exists, and there is no `CANCELLED` status. The status is set before every cancel, so every cancel
has a known cause: the timeout of a run, a memory guard (of a run or of the barrier) or a runner failure. A run end goes
through `RunManager.fail` with its own status; at the barrier the barrier guard is the only canceller, so its cancel
gives `OOM` (§7.1). The driver starts no
run after an incomplete run (§7.1). A run that the memory guard ends before its start routes no `Start` event (§3.2).
The constructor of `RunManager` activates the `Cancellation` before the driver publishes the manager, so no activation
undoes a cancel.

---

## 7. The driver (`analyzer-core.md` §7)

### 7.1 `IterationDriver`, `IterationPolicy`

```kotlin
package org.opentaint.dataflow.bidi.driver

/** analyzer-core.md §7.1. `timeout` gives one run its part of the ONE budget of the analysis (analyzer-core.md §0 item
 *  5, §7.1). THE ANALYSIS HAS ONE BUDGET (`IterationDriver.budget`; ap-history.md F70): by default each run gets the rest
 *  of it. */
interface IterationPolicy {
    fun fieldLimit(runIndex: Int): Int                                    // not decreasing (ap.md W3); run 1 >= 1: checked (below)
    /** Asked only after a complete FORWARD run that no stop rule ended: a complete backward run always goes on to the next
     *  forward run. `frontiers`: the frontier of every complete run so far, in run order; the last one is that of `run`
     *  (§7.8). A practical stop strategy reads them (analyzer-core.md §7.8; out of scope). */
    fun continueAfter(run: RunConfig, result: RunResult, frontiers: List<Frontier>): Boolean
    fun timeout(run: RunConfig, remaining: Duration): Duration = remaining
}

/** For the tests: the limits of the runs in order. It stops after the last forward run that the list covers. */
class FixedLimits(private val limits: List<Int>) : IterationPolicy {
    override fun fieldLimit(runIndex: Int) = limits[runIndex - 1]
    override fun continueAfter(run: RunConfig, result: RunResult, frontiers: List<Frontier>) =
        run.index + 2 <= limits.size                                      // the next forward run
}

/** analyzer-core.md §7.1, §10: what one run and its barrier give: the next run, or the end of the analysis. */
sealed interface Next {
    class Run(val config: RunConfig) : Next
    class End(val status: RunStatus, val reason: EndReason = EndReason.ABNORMAL) : Next
}

class IterationDriver(private val policy: IterationPolicy, private val shared: SharedObjects, private val budget: Duration) {
    /** THE FRONTIER LOG (analyzer-core.md §7.8; ap-history.md F70): the frontier of every complete run, in run order,
     *  made and logged at its barrier. `continueAfter` gets it; the tests read it after `analyze` (§9.1 rows 29, 30). One
     *  driver runs one analysis. */
    val frontiers: List<Frontier> get() = frontierLog
    private val frontierLog = ArrayList<Frontier>()

    /** ONE GUARDED REGION (analyzer-core.md §6.3, §7.1; ap-history.md F68): the whole loop body, with the RunConfig of
     *  run 1 and its check, RunManager(...), run(...) and the barrier. Every Throwable on the driver thread, an Error
     *  included, ends the analysis with the report so far: FAILED, ABNORMAL (phase 3: EXCEPTION). A JVM OutOfMemoryError
     *  is FAILED too: the status OOM comes only from a memory guard. The runners are joined on every exit: `run` joins
     *  them also when its own code throws (§3.2), and no runner lives outside `run`. */
    fun analyze(roots: List<MethodKey>): Report {
        val start = TimeSource.Monotonic.markNow()
        val report = ReportBuilder()                                            // §7.6
        var index = 1                                                           // the current run: AnalysisEnd names it
        fun end(status: RunStatus, reason: EndReason) = report.build(AnalysisEnd(status, index,   // Report.end at each return
            if (index % 2 == 1) Direction.FORWARD else Direction.BACKWARD, reason))                 // (analyzer-core.md §7.1)
        try {                                                                   // ONE GUARDED REGION: the whole loop body
            require(policy.fieldLimit(1) >= 1) { "ap.md S12 (d): run 1 needs a field limit of at least 1" }
            var config = RunConfig(1, policy.fieldLimit(1), demand = null, records = shared.records.view(),
                seeds = SeedIndex.EMPTY, roots = roots)
            while (true) {
                index = config.index
                when (val next = runOnce(config, report, policy.timeout(config, budget - start.elapsedNow()))) {
                    is Next.Run -> config = next.config                         // the RunResult of the run is garbage now (§7.7)
                    is Next.End -> return end(next.status, next.reason)
                }
            }
        } catch (e: Throwable) {                                                // an Error too: FAILED, never OOM
            logger.error(e) { "Run $index failed; the analysis ends with the report so far" }
            return end(RunStatus.FAILED, EndReason.ABNORMAL)                    // the earlier runs stay (analyzer-core.md §7.1)
        }
    }

    /** One run and its barrier. The RunResult is a local of this frame: it is garbage when runOnce returns, before the
     *  driver makes the next RunManager, so no live slot keeps it during the next run (analyzer-core.md §7.6; §7.7).
     *  THE BARRIER MEMORY GUARD (analyzer-core.md §7.2 B4; ap-history.md F68): the barrier runs under its own
     *  MemoryManager, as today's confirmation (CORE/ap/ifds/TaintAnalysisUnitRunnerManager.kt:374-384, threshold :645). So
     *  the soft-reference managers stay enabled at the barrier, and `persist` interns with live tables: the persisted
     *  records share nodes. A hit cancels the Cancellation; the barrier stops at its next checkpoint (one per analyzer in
     *  Support, `persist` and the hand-off; the checkpoints of the ApManager) by Cancellation.Cancelled. At the barrier the
     *  guard is the ONLY canceller: no runner is alive, and a late `fail` after COMPLETE does not cancel (§3.2). So a
     *  Cancellation.Cancelled there, or a Cancellation that is not active after the barrier (a hit after the last
     *  checkpoint: the next RunManager would activate it again), ends the iteration with (OOM, ABNORMAL) and the report
     *  so far. Any other Throwable goes to the catch of `analyze` (FAILED).
     *  NO DEADLINE: the barrier is one pass over the stores that §7.7 keeps. A slow barrier shortens the next run; after
     *  the last run, the analysis can end later than its budget by the time of that barrier (analyzer-core.md §11). */
    private fun runOnce(config: RunConfig, report: ReportBuilder, timeout: Duration): Next {
        val result = RunManager(config, shared).run(timeout)                    // its constructor activates the Cancellation
        if (result.status != RunStatus.COMPLETE)                                // analyzer-core.md §6.3, §7.5: an incomplete run
            return Next.End(result.status)                                      // adds nothing and refutes nothing
        val guard = MemoryManager(shared.refManager, BARRIER_MEMORY_THRESHOLD) { shared.cancellation.cancel() }
        val next = try {
            guard.runWithMemoryManager { barrier(config, result, report) }      // the soft references stay enabled
        } catch (e: Cancellation.Cancelled) {
            Next.End(RunStatus.OOM)                                             // the barrier guard is the only canceller here
        }
        if (shared.cancellation.isActive()) return next
        logger.error { "Run ${config.index}: the barrier memory guard fired; the analysis ends with the report so far" }
        return Next.End(RunStatus.OOM)                                          // also a hit after the last checkpoint
    }

    /** THE BARRIER (analyzer-core.md §7.2): the run is complete and every runner is joined (B1). */
    private fun barrier(config: RunConfig, result: RunResult, report: ReportBuilder): Next {
        val forward = config.direction == Direction.FORWARD
        if (forward) {
            Support(result, config.roots, shared).confirm()                     // analyzer-core.md §7.5 steps 1, 2
            report.add(config, result)                                          // analyzer-core.md §7.5 step 3
        }
        shared.records.persist(config.direction,                                // ap.md §8.7 R1 (ap-impl.md §7.8 filters R1;
            result.analyzers.asSequence().map { it.key to it.summaries })       // it checkpoints once per method key, B4)
        // R1 WITH `[any-taint]` (analyzer-core.md §7.3, §7.4; ap.md §8.7 R1): ONE NOTION OF COMPLETE, a normal edge.
        // FORWARD: every normal one-premise summary, also with `[any-taint]/E` leaves and also of a must-premise with its
        // exclusion (a must record: END-EXACT on the admitted locations, AnyTaintExExact.recs_of_DRX_valid). BACKWARD: every
        // normal summary with a premise that is not zero, as before F69: the backward run has no `[any-taint]` (W8 (d)).
        // A CROSSABLE leaf is a record now, and the hand-off gives no demand edge for it (§7.2, F70): its record replaces
        // the analysis of its callee in the next runs.
        val handOff = HandOff.of(config, result, report, shared)                // §7.2, §7.3: every complete run, the last too
        val frontier = frontierOf(config, result, handOff, report)              // §7.8: THE FRONTIER LOG
        frontierLog += frontier
        frontier.log()
        // THE STOP RULES (analyzer-core.md §7.1; ap-history.md F70), only after a forward run; they read no frontier.
        if (forward && !report.hasDemandVulnerability())                        // no DEMAND key in the report: no sink seed
            return Next.End(RunStatus.COMPLETE, EndReason.STOP_RULE)
        if (forward && result.demandLayerEdges == 0L)                           // no demand-layer edge, summary or link
            return Next.End(RunStatus.COMPLETE, EndReason.NO_DEMAND_EDGE)       // in the run (argued)
        if (forward && !policy.continueAfter(config, result, frontierLog))
            return Next.End(RunStatus.COMPLETE, EndReason.POLICY)
        return Next.Run(nextConfig(config, handOff))                            // B2
    }

    /** The RunConfig of the next run (analyzer-core.md §7.1 `nextConfig`). A decreasing field limit fails the `require`:
     *  FAILED, ABNORMAL (the table below). */
    private fun nextConfig(config: RunConfig, handOff: HandOff): RunConfig {
        val limit = policy.fieldLimit(config.index + 1)
        require(limit >= config.fieldLimit) { "ap.md W3: the field limit must not decrease ($limit < ${config.fieldLimit})" }
        return RunConfig(config.index + 1, limit, handOff.demand, shared.records.view(), handOff.seeds, config.roots)
    }

    companion object {
        const val BARRIER_MEMORY_THRESHOLD = 0.99        // today TRACE_GENERATION_MEMORY_THRESHOLD (TaintAnalysisUnitRunnerManager.kt:645)
    }
}
```

THE END OF THE ANALYSIS (`analyzer-core.md` §7.1). Each `return` of `analyze` sets `Report.end`:

| Return | `AnalysisEnd.status` | `reason` |
|---|---|---|
| after a complete forward run, the report has no DEMAND vulnerability (`ReportBuilder.hasDemandVulnerability` is false), so there is no sink seed | `COMPLETE` | `STOP_RULE` |
| after a complete forward run with a DEMAND vulnerability, the run has no demand-layer object: no demand-layer edge delta, no demand-layer summary delta and no demand link (`RunResult.demandLayerEdges == 0`) | `COMPLETE` | `NO_DEMAND_EDGE` |
| `continueAfter` is false after a complete forward run | `COMPLETE` | `POLICY` |
| an incomplete run, forward or backward | its status: `TIMEOUT`, `OOM`, `FAILED` | `ABNORMAL` |
| the barrier memory guard | `OOM` | `ABNORMAL` |
| a `Throwable` on the driver thread, an `Error` included: the run-1 check, the first `RunConfig`, `RunManager(...)`, `run(...)` after its join, the barrier, also a failed `require` of `nextConfig` (`ap.md` W3) | `FAILED` | `ABNORMAL` |

`run` and `direction` are those of the last run (run 1, `FORWARD` for a throw before run 1). In every case the report
holds the results of the complete forward runs before the end (§7.6). So the iteration ends only after a forward run,
as `PipelineDriver.driver_iteration_upto` asks, or at an abnormal end.

THE STOP RULES (`analyzer-core.md` §7.1; `ap-history.md` F70). The barrier of every complete run makes the hand-off
and logs the frontier (§7.2, §7.8), also after the last run. Then, only after a forward run, the driver tests the
stop rules in the order of the table; they read no frontier:

* `STOP_RULE`: the report has no DEMAND vulnerability (`ReportBuilder.hasDemandVulnerability`, §7.6): every key of the
  latest complete forward run is CONFIRMED, by it or by an earlier complete forward run. CONFIRMED is final
  (`AnyTaintExExact.confirmed_realX_valid`), so the report is final for its CONFIRMED part: every real vulnerability is
  CONFIRMED by a complete forward run up to this one (Lean `HandoffMain.iteration_generalN` with the cumulative `C`;
  for the driver `PipelineHandoffDriverExt.driver_iterationNX_upto`, with `C k` = confirmed by a complete forward run up
  to `k`, `ap.md` §4.9). The sink seeds of the hand-off are the witnesses of the DEMAND vulnerabilities only (§7.2),
  so the next backward run has no seed and no requirement except the zero fact. That every later forward run only
  repeats the zero fact and the records is argued (`HandoffExclusion.zinv_all` with every method and no seed, then
  `HandoffExclusion.exclusion_demand` per method; the composition is not stated, `analyzer-core.md` §11).
* `NO_DEMAND_EDGE`: the run has no DEMAND-LAYER OBJECT (`RunResult.demandLayerEdges == 0`: the counters of `addLink`,
  `push` and `summaryDelta`, §4.2, §4.3, §4.7): no demand-layer edge delta, no demand-layer summary delta and no DEMAND
  LINK (a link whose added fact is in the demand layer, `ap.md` §8.3). Then every sink witness and every link of the
  run is normal, so a DEMAND entry fails only the joint support of a conjunction (`ap.md` §4.9 condition 3: no one
  call supplies all the premises of its sink edges). That a later run cannot supply it is argued, and it is an open
  question (`analyzer-core.md` §11). This rule does not claim that the report is final.
* `POLICY`: `continueAfter(config, result, frontiers)` is false.

THE BUDGET. The analysis has ONE budget (`IterationDriver.budget`): each run gets `policy.timeout(config, remaining)`,
by default the rest of the budget. With no stop rule the iteration does not stop by itself (the field limit grows),
but the fact-to-fact demand only shrinks: every demand pattern with an exit pattern (case 3 of §7.3) of forward run
`n + 2` lies inside a demand pattern of forward run `n` of the same method key, in its locations and its marks, with no
exception (Lean `HandoffNoStar.narrowing_canon_loc_exactM`; in the locations only `narrowing_canon_loc_exact`;
`ap-history.md` F71; the spec closures: §7.8). The theorem does not narrow the zero demand and
the patterns `(gb, none)` of the seed paths (case 2): as locations they shrink when the backward field limit grows
(argued), and their count can grow. The frontier log shows how fast (§7.8).

AN INCOMPLETE RUN 1 (`ap-history.md` F68; `analyzer-core.md` §7.5, §9 OUTPUT). No forward run is complete, so the report
has no entry and the output is empty; `Report.end` gives the cause. The same holds for a throw or a guard hit before
`report.add` of run 1. This is a stated deviation from today: a full scan that times out outputs the vulnerabilities
that it found so far (`SAST/common/sast/dataflow/TaintAnalyzer.kt:157-223`).

### 7.2 Forward run `n` → backward run `n + 1` (`analyzer-core.md` §7.3)

```kotlin
/** analyzer-core.md §7.3, §7.4, §10: what a complete run hands to the next run of the other direction. `demand`: the
 *  demand edges only; `seeds`: the sink seeds of the DEMAND vulnerabilities (forward run) or the source seeds (backward
 *  run). `demandEdges` (an addition, §2.3): the demand patterns per method key, for the frontier log (§7.8). */
class HandOff(val demand: DemandStore, val seeds: SeedIndex, val demandEdges: Map<MethodKey, Int>) {
  companion object {
    /** analyzer-core.md §10 `handOffOf`: the barrier calls it after EVERY complete run (§7.1), the last one too. */
    fun of(config: RunConfig, result: RunResult, report: ReportBuilder, shared: SharedObjects): HandOff {
        val counts = LinkedHashMap<MethodKey, Int>()                                 // the frontier log (§7.8)
        val (demand, seeds) =
            if (config.direction == Direction.FORWARD) toBackward(result, report, shared, counts)
            else toForward(result, shared, counts)
        return HandOff(demand, seeds, counts)
    }

    /** THE ONE SUMMARY ITERATION of both hand-offs (DD12): THE DEMAND EDGES OF THE RUN (ap-history.md F70; analyzer-core.md
     *  §7.3, §7.4; ap.md §9.2), `RunSummaryStore.demandEdges()`: the PUBLISHED pieces of the summary leaves that are not
     *  crossable (`ApOps.demandPart`, restricted as the publications, in `summaryDelta`, §4.7; Lean Handoff.handF with
     *  Handoff.pubD or Handoff.pubR, Handoff.demOfN). A crossable leaf gives no demand edge: `persist` made it a record at this barrier
     *  (R1), and the next run crosses its call by the record (R4) or by the reversal (R3). Before F70 the hand-off read
     *  every summary edge, in every layer, before the restriction (Lean Backward.revSummaryDemand, Backward.demOf), so a
     *  complete callee was analysed again in every run (program WRAP: HandoffCases.Wrap.wrap_old_vs_new). One conclusion
     *  leaf at a time: `ops.leaves` reads every kind; a REACH gives the zero fact. One checkpoint per analyzer: the barrier
     *  guard stops it (§7.1). */
    private inline fun forEachDemandPiece(result: RunResult, shared: SharedObjects, body: (MethodKey, PremiseKey, Pattern) -> Unit) {
        for (a in result.analyzers) {
            shared.cancellation.checkpoint()
            for ((premise, g) in a.summaries.demandEdges()) for (leaf in shared.ops.leaves(g)) body(a.key, premise, leaf)
        }
    }

    /** Lean Handoff.handF (forward to backward): every published piece `j → g'` of a summary leaf that is not crossable
     *  gives the backward demand edge `(D-c = g', D-p = j)`, one per member `j` of the premise key (a summary with several
     *  premises is never a record, R1, so every leaf of it is a demand edge; argued, ap.md §11.2). THE MARKS OF A PATTERN
     *  (analyzer-core.md §7.3; ap-history.md F71): the pattern keeps the marks: `D-c` has the mark of the piece `g'`, and
     *  `D-p` the mark of `j`. The backward run reads both: its emission tests the mark of a requirement against `D-c`
     *  (§4.2 `emit`), and its restriction tests the mark of a backward conclusion against `D-p` (§4.7 `restrictBy`). A
     *  run-1 leaf after a cleaner can have the mark `*∖X`; the pattern keeps it, and the backward run reads it EXACTLY: a
     *  requirement with a mark in `X` gets no premise from it, because that summary does not pass the mark, so no flow is
     *  lost (ap.md §6.3, §9.2; before F71 `*∖X` counted as `*` there). THE BACKWARD RUN HAS NO
     *  `[any-taint]` (analyzer-core.md §7.3; ap.md W8 (d), §9.2): the hand-off reads a forward leaf and a forward premise as
     *  a location set, so an `[any-taint]/E` leaf or must-premise gives the pattern `[any]` with no exclusion (`located`).
     *  Dropping `E` gives a larger backward demand, so it is sound (ap.md §9.2); the model drops it too: the backward run
     *  reads the forward run with the exclusions and the must flags dropped (Lean AnyTaintExCov.forget6, forgetX;
     *  PipelineAnyTaintExDriver.resultSeqX; with F70 the publication HandoffX.pubRX, PipelineHandoffDriver.pubSeqXst). */
    private fun toBackward(result: RunResult, report: ReportBuilder, shared: SharedObjects,
                           counts: MutableMap<MethodKey, Int>): Pair<DemandStore, SeedIndex> {
        val demand = DemandStore.Builder(shared.ap)                                 // ap-impl.md §7.7
        forEachDemandPiece(result, shared) { m, premise, piece ->
            premise.forEachMember { j ->                                            // one per member
                demand.add(m, DemandPattern(entry = located(piece), exit = located(j.toPattern())))
                counts.merge(m, 1, Int::plus)
            }
        }
        // THE SINK SEEDS (analyzer-core.md §7.3; ap-history.md F70): ONLY THE DEMAND VULNERABILITIES, the keys whose REPORT
        // state is DEMAND after this run (`ReportBuilder.demandEntries`, §7.6: reported by this run, and confirmed by no
        // complete forward run so far). CONFIRMED is final (AnyTaintExExact.confirmed_realX_valid), so a key that this run
        // or an earlier run confirmed is never seeded again. Lean HandoffMain.iteration_generalN: `hseeds` is "confirmed
        // (C k) or seeded", here with C k = "a complete forward run up to k confirmed it" (ap.md §4.9); so every real
        // vulnerability is, at every forward run, reported by it or confirmed by an earlier one. For the pipeline driver:
        // PipelineHandoffDriverExt.driver_iterationNX_demand, finite PipelineHandoffDriverExt.driver_iterationNX_upto
        // (PipelineHandoffDriver.driver_iterationNX is the form with EVERY reported vulnerability seeded;
        // PipelineHandoffDriverExt.driver_iterationNX_confirmed takes a weaker C, a normal-layer report, not the
        // confirmation of ap.md §4.9). The backward run also fires, by itself, the seeds of THE TRIGGER OF AN END FACT,
        // also of a CONFIRMED key (§4.9; argued). A key is (rule, method, statement) with no
        // context; the seeds of a witness are at its METHOD KEY and its statement (analyzer-core.md §4.7). The sink rule
        // fires there (ap.md §9.2) with the patterns of every alternative of the rule (interpreter.md §7.2 item 14): a
        // sound superset of the witnessed ones. `Entry.witnesses` are the witnesses of this run (the latest).
        val seeds = ArrayList<Seed>()
        for (entry in report.demandEntries())
            for (mk in entry.witnesses.mapTo(LinkedHashSet()) { it.methodKey })
                for (sink in sinksAt(shared, mk, entry.key.statement)) if (sink.rule == entry.key.rule)
                    for (lit in sink.seedPatterns())                                // one per positive literal; none if unconditional
                        seeds += Seed.Sink(entry.key.rule, mk, entry.key.statement, lit)
        return demand.build() to SeedIndex.of(seeds.distinct())
    }

    /** A forward pattern as a backward pattern (ap.md W8 (d), §9.2): `[any-taint]/E` gives `[any]` with no exclusion; every
     *  other pattern stays (a `*/E` pattern keeps its exclusion, as before F69). The mark stays in both cases, also a
     *  `*∖X` mark (F71): this view changes only the tail and the exclusion. DD13. */
    private fun located(p: Pattern): Pattern =
        if (p.fact.tail != Tail.ANY_TAINT) p else Pattern(p.fact.copy(tail = Tail.ANY), ExclusionSet.Empty)

    /** The forward sinks at a statement: a call (the plan), an exit, normal or exceptional (the exit rules of that exit,
     *  interpreter.md §4.7). An entry sink is unconditional: it seeds nothing (ap.md §9.2). MethodForms caches the forms
     *  (ap-impl.md §23.7), so this makes no new form. */
    private fun sinksAt(shared: SharedObjects, key: MethodKey, s: CommonInst): List<SinkRule> {
        val forms = shared.contexts.forms(key)
        shared.language.getCallExpr(s)?.let { return forms.call(Direction.FORWARD, s, it).sinks }
        return if (shared.interpreter.exitNodes(key).any { it.node == s })
            forms.exitRules(Direction.FORWARD, s).rules.sinks else emptyList()
    }
```

The driver persists the records of each complete run at the barrier (§7.1). The records are not a hand-off
(`analyzer-core.md` §1).

THE DEMAND EDGES ONLY (`ap-history.md` F70; `analyzer-core.md` §7.3; `ap.md` §9.2). A summary leaf is CROSSABLE (Lean
`Handoff.Cross`) if it is normal, its premise is `$` or `*` with the Empty exclusion (not `[any]`, not a must-premise
`[any-taint]`), it is mark-reversible, and its reversal has such a premise too, so the leaf has no any tail. Its record
then applies to every CONCRETE added fact or requirement (every restricted run is concrete) that covers one of its
locations, by `inside` or by `applicable` (`Handoff.cross_applies`), in both directions. So the hand-off gives no demand
edge for it. THE EXCLUSION (§7.8): if forward run `n` hands off no demand edge of a method key and no sink seed of
backward run `n + 1` (also of THE TRIGGER OF AN END FACT, §4.9) lies in its call subtree, backward run `n + 1` and
forward run `n + 2` analyse it only from the zero fact (`HandoffExclusion.exclusion_theorem`); a sufficient condition
is that every summary leaf of the key in run `n` is crossable (`HandoffExclusion.exclusion_round`; on the run sequence
`HandoffMain.exclusion_canon`; on the spec closures `HandoffXMain.exclusion_canonX`). The test is
`ApOps.demandPart` (`ap-impl.md` §5.9), in `summaryDelta` (§4.7). EVERY LEAF IS A DEMAND EDGE for a summary with
several premises, a demand-layer summary (also a backward summary through a reversed may or a reversed conjunction
literal, §4.3), a backward zero-premise summary and a premise that is not crossable (`[any]`,
a must-premise, `*/E` with `E ≠ {}`); of a normal forward TAINT tree, every `[any-taint]` leaf (its reversed premise is
`[any]`, `HandoffCases.revRec_any_premise`, `HandoffCases.not_cross_of_any`, and a `$` requirement neither lies inside it nor is
covered by it, `HandoffCases.dollar_blocked`; with such a leaf dropped, a real vulnerability is lost:
`HandoffCases.AnyW.cegar_cross_anyw`, `HandoffCases.AnyM.cegar_cross_anym`). PROGRAM WRAP: run 1 gives `wrap` the one
crossable summary `(arg, ., *) → (ret, .f, *)` (`HandoffCases.Wrap.w1_exit_cross`), so `wrap` has no demand edge
(`HandoffCases.Wrap.handF_w1_exact`); backward run 2 crosses `wrap` by the reversal (`HandoffCases.Wrap.bn_cross`) and
enters it only with the zero fact (`HandoffCases.Wrap.bn_wrap_zero_only`); forward run 3 enters `wrap` only with the
zero fact (`HandoffCases.Wrap.fn_wrap_zero_only`, `HandoffCases.Wrap.fn_wrap_edges_zero`), crosses the call by the
record (`HandoffCases.Wrap.fn_record_applicable`: by `applicable`), cuts in the root
(`HandoffCases.Wrap.fn_cut_in_root`) and still reports the vulnerability (`HandoffCases.Wrap.fn_found`). The hand-off
before F70 entered `wrap` in runs 2 and 3 and cut inside it (`HandoffCases.Wrap.old_f3_wrap_cut`).

### 7.3 Backward run `n + 1` → forward run `n + 2` (`analyzer-core.md` §7.4)

```kotlin
    /** Lean Handoff.demOfN (backward to forward); FSeeds.srcHit. 1: the zero demand of every method key (F70 does not
     *  localize the zero fact, analyzer-core.md §11). 2: every zero-premise backward edge `(gb, none)`: never a record (the
     *  seed paths, R1: of the seeds of the hand-off and of the seeds of THE TRIGGER OF AN END FACT, §4.9), so `demandPart`
     *  keeps all of it, unrestricted (§4.7). 3: every published piece `jb → gb'` of a backward leaf with a non-zero
     *  premise that is not crossable (Lean ¬ Handoff.CrossB): `(gb', jb)`, with the marks of `gb'` and `jb`
     *  (analyzer-core.md §7.4; ap-history.md F71). `jb` is an emitted requirement with its concrete mark, and it covers
     *  the forward exit location of each backward pair with its mark, so the next forward run publishes through this
     *  pattern only a conclusion with the mark of `jb` (§4.7 `restrictBy`), and a real flow through the call is DEMANDED
     *  with both marks (Lean Handoff.FlowRR.call: `p.covers l2`; HandoffBackward.seg_genN). A NORMAL backward leaf
     *  whose reversal is crossable is a backward record (R1), and the next forward run crosses the call by its reversal
     *  (R3; program getter: HandoffCases.Getter.revRec_g_crossB, HandoffCases.Getter.demG_exact,
     *  HandoffCases.Getter.fg_found). A demand-layer backward leaf is always a demand edge: R1 persists only normal
     *  edges (Lean Handoff.CrossB: normal and Cross of its reversal); so is a backward leaf through a reversed may or a
     *  reversed conjunction literal (§4.3). No pattern has the `[any-taint]` tail: the backward run has none (ap.md
     *  W8 (d); analyzer-core.md §7.4). */
    private fun toForward(result: RunResult, shared: SharedObjects,
                          counts: MutableMap<MethodKey, Int>): Pair<DemandStore, SeedIndex> {
        val demand = DemandStore.Builder(shared.ap)                                 // 1: (zero, none) is implicit (ap-impl.md §7.7)
        forEachDemandPiece(result, shared) { m, jb, piece ->                   // the edges at the forward entry
            demand.add(m, when (jb) {
                is InitialAp -> if (jb.isZero) DemandPattern(piece, null)            // 2: (gb, none)
                                else DemandPattern(piece, jb.toPattern())            // 3: (gb', jb)
                is PremiseSet -> error("the backward run has no ND summary (ap.md §9.2)")
            })
            counts.merge(m, 1, Int::plus)
        }
        val seeds = ArrayList<Seed>()
        for (a in result.analyzers) for ((m, s, e) in a.sourceHits!!.entries()) seeds += Seed.Source(m, s, e)   // ap.md §8.11
        return demand.build() to SeedIndex.of(seeds)
    }
  }   // companion object
}
```

Case 3 with `gb` the zero fact is `(zero, jb)`: it restricts the zero-premise summaries of the forward run. It needs
the edge `jb → zero` in the backward edge store (`ap-impl.md` §7.3 keeps a REACH bit per premise key). Since F70 it
occurs only for a demand-layer edge `jb → zero` or for a premise `jb` with a tail other than `$` (`[any]` or `*`: the
reversal `{zero} → jb` then has an any tail, so it is not crossable): the reversal of a normal `jb → zero` with a `$`
premise is the forward source record `{zero} → jb`, which is crossable, and the next forward run applies it to the
zero fact at the call (§5.3 `replayRecords`, `ap-impl.md` §7.8 `reversedAt`). In a restricted forward run a
zero-premise summary is published ONLY through such a pattern: the zero demand `(zero, none)` has no `D-p`, so it
gives no publication (`ap.md` §6.4; Lean `HandoffCases.restrictI_none`). So a method key with only the zero demand
publishes nothing, and it gives no demand edge from the zero fact (THE EXCLUSION, §7.8).

THE KINDS IN THE HAND-OFFS (`ap.md` §7.2). The demand patterns come from the leaves of each kind, only from the
demand edges (`demandEdges()`, F70):

| Run | Summary kinds | Demand |
|---|---|---|
| forward run 1 | FLOW (`*` premise), TAINT (`{zero}`: a source; a concrete premise), REACH (`{zero} → zero`) | one pattern per (leaf of a piece, member), for the leaves that are not crossable. A normal FLOW value under the policy fact `*/{}` (also with `*/E` leaves: the reversed premise has the Empty exclusion, `ap.md` §9.1) and a normal REACH value are crossable (no pattern); a demand FLOW value (its `[any]` leaves) and a TAINT `[any-taint]` leaf are not |
| forward run ≥ 3 | TAINT, REACH (a restricted run is concrete) | the same rows without FLOW; a normal `$` leaf of a `$` premise is crossable, an `[any-taint]` leaf and every leaf of a must-premise are not |
| backward | TAINT (`{zero}`: from a seed; `{jb}`), REACH (`{zero} → zero`; `{jb} → zero`: a requirement reached a source) | TAINT: `(gb, none)` (always), or `(gb', jb)` if the leaf is demand or its reversal is not crossable. REACH on `{zero}`: `(zero, none)`, the implicit zero demand (`DemandStore.Builder` drops it). REACH on `{jb}`: `(zero, jb)`, case 3, if the edge is demand or `jb` has a tail other than `$` |

### 7.4 `Seed`, `SeedIndex`

```kotlin
/** analyzer-core.md §10, unchanged. RuleId = CommonTaintConfigurationSink (ap-impl.md §7.12). */
sealed interface Seed {
    val method: MethodKey
    val statement: CommonInst
    data class Sink(val rule: RuleId, override val method: MethodKey, override val statement: CommonInst,
                    val requirement: Pattern) : Seed
    data class Source(override val method: MethodKey, override val statement: CommonInst, val edge: PathEdge) : Seed
}

/** analyzer-core.md §10, plus the source test of analyzer-core.md §4.7 (§2.3). */
class SeedIndex(private val byPlace: Map<Pair<MethodKey, CommonInst>, List<Seed>>) {
    private val sources: Set<Triple<MethodKey, CommonInst, PathEdge>> =
        byPlace.values.flatten().filterIsInstance<Seed.Source>().mapTo(HashSet()) { Triple(it.method, it.statement, it.edge) }

    fun at(method: MethodKey, statement: CommonInst): List<Seed> = byPlace[method to statement].orEmpty()
    fun allowsSource(method: MethodKey, statement: CommonInst, forward: PathEdge): Boolean =
        Triple(method, statement, forward) in sources
    val size: Int get() = byPlace.values.sumOf { it.size }                   // the frontier log (§7.8)
    /** The method keys of the sink seeds: the frontier log and the exclusion test (§7.8, §9.1 row 30). */
    fun sinkMethods(): Set<MethodKey> = byPlace.values.flatten().filterIsInstance<Seed.Sink>().mapTo(HashSet()) { it.method }

    companion object {
        val EMPTY = SeedIndex(emptyMap())
        fun of(seeds: List<Seed>) = SeedIndex(seeds.groupBy { it.method to it.statement })
    }
}
```

### 7.5 `Support` and the confirmation (`analyzer-core.md` §7.5)

The support is a property of a premise SET in one METHOD KEY. It is the least fixed point over the links of the run.
The links carry the data (E-2): `Link(addedFact, linkLayer, CallerRef(caller, premise, callerLayer, call))`. The driver
computes it at the barrier; no store of a run keeps it (`analyzer-core.md` §7.5). So `InitialFactStore` (`ap.md` §8.2)
has no field for the supported premise sets: the confirmation reads `Support`.

```kotlin
/** ap.md §4.9 condition 3 (Lean Confirmed.Sup, RExact.SupM, NDConfirmed.SupN). */
class Support(private val result: RunResult, roots: List<MethodKey>, shared: SharedObjects) {
    private data class Site(val callee: MethodKey, val caller: MethodKey, val call: CommonInst)
    private val roots = roots.toHashSet()
    private val ap = shared.ap
    private val zeroKey: PremiseKey = ap.zero                                            // ap.md §7.1: the InitialAp is the key
    private val atSite = HashMap<Site, HashMap<Pattern, MutableList<PremiseKey>>>()   // normal links: added fact → caller premises
    private val restricted = result.runIndex > 1                                       // a forward restricted run (ap.md §4.9)
    private val anyAtSite = HashMap<Site, MutableList<Pair<Pattern, PremiseKey>>>()   // normal `[any-taint]/E` links (restricted)
    private val sitesOf = HashMap<MethodKey, MutableSet<Site>>()
    private val fedBy = HashMap<Pair<MethodKey, PremiseKey>, MutableSet<Site>>()       // (caller, caller premise) → sites
    private val questions = HashMap<MethodKey, MutableSet<PremiseKey>>()               // the caller premise sets of m's own links
    private val sup = HashSet<Pair<MethodKey, PremiseKey>>()

    init {
        for (callee in result.analyzers) {
            shared.cancellation.checkpoint()                                                  // one per analyzer: the barrier guard (§7.1)
            for (link in callee.links.links()) {
                val ref = link.caller
                if (link.linkLayer != Layer.NORMAL || ref.callerLayer != Layer.NORMAL) continue   // 3.2.2, the normal caller edge
                val site = Site(callee.key, ref.caller, ref.call)
                atSite.getOrPut(site, ::HashMap).getOrPut(link.addedFact, ::ArrayList) += ref.premise
                if (restricted && link.addedFact.fact.tail == Tail.ANY_TAINT)                  // 3.2.3, the second case
                    anyAtSite.getOrPut(site, ::ArrayList) += link.addedFact to ref.premise
                sitesOf.getOrPut(callee.key, ::HashSet) += site
                fedBy.getOrPut(ref.caller to ref.premise, ::HashSet) += site
                questions.getOrPut(ref.caller, ::HashSet) += ref.premise
            }
        }
        val work = ArrayDeque<Pair<MethodKey, PremiseKey>>()
        for (r in this.roots) if (sup.add(r to zeroKey)) work += r to zeroKey               // 3.1
        while (work.isNotEmpty()) {
            val q = work.removeFirst()
            for (site in fedBy[q].orEmpty()) for (p in questions[site.callee].orEmpty())
                if ((site.callee to p) !in sup && suppliedAt(site, p.members)) {            // 3.2
                    sup += site.callee to p; work += site.callee to p
                }
        }
    }

    /** 3.2: ONE call statement supplies every member: the member passes condition 2, a normal link at that call supplies
     *  it (3.2.3, `suppliers`), and the caller premise set of that link is supported (3.2.1). Different members can use
     *  different caller edges (a tree). Lean Confirmed.Sup.call, RExact.SupM.call, NDConfirmed.SupSlots.cons;
     *  AnyTaintEx.SupX. */
    private fun suppliedAt(site: Site, members: Collection<InitialAp>): Boolean =
        members.all { j -> condition2(j) && suppliers(site, j).any { (site.caller to it) in sup } }

    /** 3.2.3: the caller premises of the normal links at `site` that supply the member j. (1) The added fact is EQUAL to
     *  j (`jm = a`), the exclusion included. (2) In a forward restricted run: the added fact `a` has the tail
     *  `[any-taint]` and an exclusion `E` (so it is normal on its link, ap.md W8), j is `$` or a must-premise
     *  `[any-taint]/E'`, j lies INSIDE `a` with the exclusions read (`inside`, Reference.kt: j is not at a step that `E`
     *  excludes, and at the path of `a` `E ⊆ E'`) and has the SAME concrete mark. Every admitted location of `a` carries
     *  its mark, so every admitted location of j is supplied (Lean AnyTaintEx.SupLinkX). The same mark makes the
     *  condition explicit: for a concrete premise `inside` already gives it (AnyTaintExact.markSub_conc); without it the
     *  link would accept a `*`-mark premise (AnyTaintExact.CexSupMark.cex_sup_mark). The link carries the tail and the
     *  exclusion of its added fact (analyzer-core.md §7.5), so this needs no other data. */
    private fun suppliers(site: Site, j: InitialAp): Sequence<PremiseKey> {
        val p = j.toPattern()
        val equal = atSite[site]?.get(p).orEmpty().asSequence()
        if (!restricted || j.isZero || (j.tail != Tail.EXACT && j.tail != Tail.ANY_TAINT)) return equal
        return equal + anyAtSite[site].orEmpty().asSequence()
            .filter { (a, _) -> a.fact.mark == j.mark && inside(p, a) }.map { it.second }
    }

    /** ap.md §4.9 condition 2: the member is the zero fact, an exact concrete fact, or (in a forward restricted run) a
     *  must-premise `(x, p, [any-taint], E, T)` with any exclusion, an emitted fact (ap.md §6.3; Lean AnyTaintEx.SupX,
     *  ConfirmedX). Run 1 has no must-premise (W8 (c)). Users: suppliedAt, confirm. */
    private fun condition2(j: InitialAp) = j.isZero ||
        (j.mark is MarkSlot.Concrete && (j.tail == Tail.EXACT || (restricted && j.tail == Tail.ANY_TAINT)))

    fun isSupported(m: MethodKey, members: Collection<InitialAp>): Boolean =
        (m in roots && members.all { it.isZero }) || sitesOf[m].orEmpty().any { suppliedAt(it, members) }

    /** analyzer-core.md §7.5 step 2. A sink edge set is confirmed as a whole: the union of its premise sets (without the
     *  zero fact, ap.md §4.6), jointly. A witness reads the support IN ITS OWN METHOD KEY (`w.methodKey`): the
     *  vulnerability key has no context. A merged entry of ap-impl.md §7.12 has one premise set and one layer per
     *  literal, so it is confirmed exactly when each of its witnesses is. */
    fun confirm() {
        for ((_, w) in result.vulnerabilities.witnessesOf(result.runIndex)) {
            val members = w.supportPremise(ap).members                         // ap.md §4.6: the union drops the zero fact (ap-impl.md §7.12)
            w.confirmed = w.edges.all { it.layer == Layer.NORMAL } &&       // condition 1: the layer only, so a normal
                                                                            // `[any-taint]/E` sink edge counts (AnyTaintEx.Confirmed6X)
                members.all(::condition2) &&                                                               // condition 2
                isSupported(w.methodKey, members)                                                        // condition 3
        }
    }
}
```

The fixed point reads only the caller premise sets (`questions`). `isSupported` checks a witness at the end. A pair
enters `sup` only after its callers: so `sup` is the least fixed point. Each pair enters `work` once.

THE TAIL `[any-taint]` (`analyzer-core.md` §7.5; `ap.md` §4.9). Condition 1 reads the layer only, so a normal sink edge
with the `[any-taint]/E` tail can be confirmed. The sink edge exists only when the sink pattern meets an ADMITTED
location of the fact: `checkMark` reads `E` (§4.9; Lean `AnyTaintEx.checkX`), so `confirm` needs no exclusion test.
Conditions 2 and 3.2.3 read the tail in a forward restricted run only: there a must-premise is a member like an exact
fact, and a normal `[any-taint]/E` link supplies a `$` member or a must-premise `[any-taint]/E'` inside it, the
exclusions read, with the same mark. A demand link (an `[any]` added fact, no exclusion) supplies nothing (3.2.2). The
inside test of `suppliers` is linear in the `[any-taint]` links of one call site; a `PathTrie` per site
(`lookupPrefixes`) is the alternative if a profile shows it. Lean: `AnyTaintEx.Confirmed6X` (run 1), `ConfirmedX`,
`SupX`, `SupLinkX`. A confirmed vulnerability is real: run 1 `AnyTaintExExact.confirmed_real_valid6X`, a forward
restricted run `confirmed_realX_valid` (with the spec rules `AnyTaintEx.emitX`, `AnyTaintEx.satX` and
`HandoffX.restrictIX`, its hypotheses are `AnyTaintEx.emitX_copies`, `AnyTaintEx.satX_inside`, `HandoffX.restrictIX_ok`;
`AnyTaintExExact.confirmed_realXs` is its instance with the earlier restriction `AnyTaintEx.restrictX`, the record of
the earlier design), and over the run sequence `AnyTaintExExact.seq_confirmed_realX_valid` when every record is an
exit edge of an earlier forward run of the same program (`AnyTaintExExact.RecsFromRunsX`), with no exactness
hypothesis on the records. With the reversed backward records and
with the source seeds this is argued (`ap.md` §8.7 R4, §11.2).

### 7.6 `Report`

```kotlin
enum class ReportState { CONFIRMED, DEMAND }
/** analyzer-core.md §7.1 (the table of §7.1). NO_DEMAND_EDGE: ap-history.md F70. */
enum class EndReason { STOP_RULE, NO_DEMAND_EDGE, POLICY, ABNORMAL }

/** analyzer-core.md §7.1: the end of the analysis. `run`, `direction`: the last run (the table of §7.1). */
data class AnalysisEnd(val status: RunStatus, val run: Int, val direction: Direction, val reason: EndReason)

/** analyzer-core.md §7.5, §10; ap.md §8.10 (its Kotlin form is `Report.Entry`). The result of the analysis. `Entry.run`:
 *  the run of the state (the first complete forward run that confirmed the key, or the latest complete forward run).
 *  `Entry.witnesses` (analyzer-core.md §9 OUTPUT, §10; ap.md §8.10): the witnesses of the key in that run, of every
 *  alternative and method key, with the fields of ap.md §8.10 (the alternative, the method key, the sink edges, the
 *  `confirmed` flag, the end facts). The pattern of a witness is DERIVED, not stored: `SinkRule.patterns` of its
 *  alternative of the rule at the statement in its method key (the same in every run, interpreter.md I5; the hand-off
 *  reads it so, §7.2). The VulnerabilityStore keeps the witnesses of every run, each with its run. */
class Report(val entries: List<Entry>, val end: AnalysisEnd) {
    class Entry(val key: VulnerabilityKey, val state: ReportState, val run: Int, val witnesses: List<SinkWitness>)
}

/** analyzer-core.md §7.5: built from the COMPLETE forward runs only. An incomplete run (forward or backward) adds
 *  nothing and refutes nothing: the driver never calls `add` for it (§7.1). */
class ReportBuilder {
    private val confirmed = LinkedHashMap<VulnerabilityKey, Report.Entry>()     // final
    private var demand = LinkedHashMap<VulnerabilityKey, Report.Entry>()        // of the LATEST complete forward run

    /** A complete forward run, after its confirmation. A key is CONFIRMED if one witness of this run is confirmed (any
     *  alternative, any method key); the first run that confirms it stays. The demand set replaces the old one: a demand
     *  key of an earlier run that this run does not report is refuted (ap.md §8.10). A key whose taint comes from an
     *  `[any]`-target source (the `[any-taint]` tail) can be CONFIRMED: in run 1, also through a setter (program S:
     *  `sink(dto.email)` is CONFIRMED in run 1, `sink(dto.name)` is not reported), or in a later forward run (program G:
     *  DEMAND in run 1, CONFIRMED in run 3). Only a key that rests on a DEMOTION of ap.md §2.2 stays DEMAND
     *  (analyzer-core.md §7.5; ap-history.md F69): the field-limit cut; a cleaner `part` row other than `atAndBelow` and
     *  `below` one accessor below the fact (the `exact` cleaner at the path of the fact or below it, any cleaner two or
     *  more accessors below it); a may target (the `[any]` target of a pass rule with an `AnyField` target); a demand
     *  input (a demand fact, summary or record); the must-record demotion (`recLayer`, §4.6 `applyRecord`). */
    fun add(config: RunConfig, result: RunResult) {
        val next = LinkedHashMap<VulnerabilityKey, Report.Entry>()
        for ((key, ws) in result.witnessesByKey())
            if (ws.any { it.confirmed }) confirmed.putIfAbsent(key, Report.Entry(key, ReportState.CONFIRMED, config.index, ws))
            else next[key] = Report.Entry(key, ReportState.DEMAND, config.index, ws)
        demand = next                                                             // one step (analyzer-core.md §7.5 step 3)
    }

    /** analyzer-core.md §1, §7.3 (ap-history.md F70): THE DEMAND VULNERABILITIES after the latest complete forward run:
     *  its keys that NO complete forward run confirmed (a key that an earlier run confirmed is final, also if the latest
     *  run reports it only in the demand layer). Their witnesses of that run are the sink seeds (§7.2). */
    fun demandEntries(): List<Report.Entry> = demand.values.filter { it.key !in confirmed }

    /** analyzer-core.md §7.1: false gives the stop rule STOP_RULE (no DEMAND vulnerability, so no sink seed). */
    fun hasDemandVulnerability(): Boolean = demandEntries().isNotEmpty()

    /** The CONFIRMED vulnerabilities so far (the frontier log, §7.8; an addition, §2.3). */
    val confirmedCount: Int get() = confirmed.size

    /** One key from several runs: CONFIRMED wins (ap.md §8.10). */
    fun build(end: AnalysisEnd): Report = Report(confirmed.values + demandEntries(), end)
}
```

### 7.7 What stays after a run, as code (`analyzer-core.md` §7.6)

| Data | Stays until | The reference that holds it | Where it is dropped |
|---|---|---|---|
| run summary stores (the summaries for `persist`, the demand edges for the hand-off, F70); `sourceHits` of a backward run | its hand-off | `RunResult.analyzers[*].summaries`, `.sourceHits` | the return of `IterationDriver.runOnce` (§7.1): the `RunResult` is a local of its frame, garbage before the next `RunManager` |
| links of a forward run | its confirmation | `RunResult.analyzers[*].links` | the same |
| the frontier counters of each analyzer (§4.1) | its barrier | `RunResult.analyzers[*]` | the same; the `Frontier` of the run stays in `IterationDriver.frontiers` (§7.8): counts and method keys only |
| edges and initials of every run; the links of a backward run | the end of the run | `RunMethodAnalyzer.edgeStore`, `.initialStore`, `.linkStore` | `RunMethodAnalyzer.freeze()` in `RunManager.run` (§4.11): the barrier never reads them, and no store of a run stays for a trace resolver (§8.2) |
| the stores of an incomplete run | the end of `RunManager.run` | — | `RunManager.run` gives no analyzers for it (§3.2) |
| `SummaryStorage`, `SubscriptionManager`, runners | the end of the run | `RunManager.storages`, `.runners` | `RunManager.run`: `runners.clear(); storages.clear()` |
| worklist, pending, requests and the request join, conjunctions (with the E6 joins), the trigger set `triggered` (§4.9), the port | the end of the run | `RunMethodAnalyzer` fields | `RunMethodAnalyzer.freeze()` |
| the witnesses of the reported keys | the end of phase 3 | `Report.Entry.witnesses` | the caller drops the `Report` |
| `RecordStore`, `VulnerabilityStore`, `MethodContextCache` (the entries and forms of `ap-impl.md` §31.2), `ApManager` | the analysis | `SharedObjects` | `JIRBidiAnalysis.run` returns (`SharedObjects.close()` closes the pool) |

### 7.8 The frontier log (`analyzer-core.md` §7.8)

THE FRONTIER of a complete run is the part of the program that the later runs still analyse: the method keys with a
non-zero initial fact, and the demand edges that the hand-off gives the next run, per method key (`ap-history.md` F70).
The barrier of every complete run makes it after the hand-off and before the stop rules (§7.1), logs it, and gives the
list of every frontier so far to `continueAfter`; the driver keeps the list (`IterationDriver.frontiers`). It is the
localization of the remaining work, and the input of later stop strategies.
Two theorems tell what it can show. Both are proved for the base sequence (`HandoffMain.canonState`) and for the
spec closures with the `[any-taint]` tail and its exclusion (`HandoffXIter.canonStateX`), with the forms below.
THE EXCLUSION: if forward run `n` hands off no demand edge of a method key `M` and no sink seed of backward run `n + 1`
(of the hand-off or of THE TRIGGER OF AN END FACT, §4.9) lies in the call subtree of `M`, then `M` has only
zero-premise edges of the zero fact in backward run `n + 1`, and only the zero fact as an initial fact, with
zero-premise edges only, in forward run `n + 2` (`HandoffExclusion.exclusion_theorem`; the model has no end facts, so
the trigger seeds are argued; program hypotheses: `HandoffExclusion.NoZeroGenP`, no cleaner on the zero base;
the seeds have concrete marks, `BExact.SeedsConc`). A sufficient condition for the first hypothesis is that every
summary leaf of `M` in run `n` is crossable (`HandoffExclusion.exclusion_round`; on the run sequence
`HandoffMain.exclusion_canon`; on the spec closures `HandoffXMain.exclusion_roundX`, `HandoffXMain.exclusion_canonX`).
With only the zero demand, `M` publishes nothing in forward run `n + 2` (a zero-premise summary is published only
through a pattern `(zero, jb)`, §7.3), so it gives no demand edge again. Over several rounds the exclusion is the
one-round theorem applied again, while no seed lies in the call subtree (argued).
THE NARROWING: every demand pattern with an exit pattern (case 3, §7.3) of forward run `n + 2` lies inside a demand
pattern of forward run `n` of the same method key, IN ITS LOCATIONS AND ITS MARKS, WITH NO EXCEPTION
(`HandoffNoStar.narrowing_canon_loc_exactM`, with its halves `HandoffNoStar.narrowing_canon_fwd_exactM` and
`HandoffNoStar.narrowing_canon_back_exactM`; `ap-history.md` F71; the forms in the locations only,
`HandoffNoStar.narrowing_canon_loc_exact`, `HandoffNoStar.narrowing_canon_fwd_exact` and
`HandoffNoStar.narrowing_canon_back_exact`, stay true; hypotheses: the seeds have concrete marks and no `*` tail, as
every sink pattern, `HandoffNoStar.nonstar_of_sinkK`). THE MARKS: each restriction puts its premise inside `D-c` and
its result inside `D-p` in the marks too (§4.7 `restrictBy`), except at a conclusion with an abstract mark, which the
mark test keeps as it is (`Handoff.restrictI_interM`, `Handoff.restrictI_narrowM`; the cell is real,
`Handoff.RVec.inter_exc_absmark`). Every run of the sequence is concrete (`RExact.DR_concrete`, `BExact.DB_concrete`),
so that cell does not occur, and the marks have no exception (`Handoff.restrictI_narrow_conc`,
`Handoff.handF_narrow_DRM`). THE LOCATIONS: with the hand-off of the demand edges, run 1 hands off no
pattern with a `*` entry tail (every normal FLOW leaf of run 1 is crossable, and a demand FLOW leaf is `[any]`,
`ap.md` W2: `HandoffNoStar.handF_run1_nonstar`), and the backward run then has no `*` premise and no `*` conclusion
(`HandoffNoStar.DB_edge_nonstar`, `HandoffNoStar.demOfN_nonstar`). So the cells of `Handoff.RExc` do not occur: the
forward narrowing is exact from forward run 3 (`HandoffNoStar.narrowing_canon_fwd_exact`), and the backward one too
(`HandoffNoStar.narrowing_canon_back_exact`; after run 1 the only cell is (a) at a `*/{}` exit pattern, which adds no
location, `HandoffNoStar.narrowing_canon_back_loc`). On the spec closures (`HandoffNoStar.narrowing_canonX_loc_exact`)
the exit side is exact, also on the view of the hand-off with no exclusions; the entry side is exact except for a
premise with the Universe exclusion (an `[any-taint]` premise read only at its own path), and there only at a location
that the dropped exclusion excludes (`HandoffXMain.Dropped`; the cell is real in the operations of the model,
`HandoffNoStar.NSVec.entry_univ`). The AP has no Universe exclusion (`ap.md` §1: `ExclusionSet` is Empty or a finite
set; the model keeps `Excl.univ` only to encode a `$` premise), so the cell never occurs in the engine, and the property
test asserts that its count is 0. On the spec closures THE MARKS narrow in every cell, also in the cells where the
locations have an exception (`HandoffXMain.narrowing_canonXM`, with its halves `HandoffXMain.narrowing_canonX_fwdM` and
`HandoffXMain.narrowing_canonX_backM`: the X runs and the backward runs are concrete). `HandoffMain.narrowing_canon_loc`
is an earlier form with loose exceptions (its cells hold for every `*` exit pattern,
`HandoffNoStar.base_loc_exception_weak`); this document does not cite it as the narrowing. The theorem does not narrow
the zero demand and the patterns `(gb, none)` of the seed paths (case 2): as locations they shrink when the backward
field limit grows (argued), and their count can grow. So the case-3 patterns of `demandEdges` only become smaller, in
the locations and the marks; the log shows how fast.
A stop strategy reads the list in `continueAfter`; `analyzer-core.md` §7.8 gives examples, and this document chooses
none. THE ZERO FACT is not localized (`analyzer-core.md` §11): it still enters every callee, and the log gives its work
as a measure (`zeroOnly`, `zeroOnlyEdges`).

```kotlin
package org.opentaint.dataflow.bidi.driver

// Frontier and DemandCause: analyzer-core.md §10, unchanged.

/** analyzer-core.md §10 `frontierOf`: the frontier of one complete run, in one pass over the counters of its analyzers
 *  (§4.1), the hand-off (§7.2) and the report. Counts and method keys only, no fact, so it stays for the whole analysis
 *  (§7.7). After a backward run the vulnerability counts are 0, `recordCrossings` are the crossings of that run (its
 *  backward records, R4, and the reversed forward records, R3), and `seeds` are the source seeds. */
fun frontierOf(config: RunConfig, result: RunResult, handOff: HandOff, report: ReportBuilder): Frontier {
    val forward = config.direction == Direction.FORWARD
    val a = result.analyzers
    val zeroOnly = a.filter { !it.nonZeroInitial }                     // the zero fact reached them, no other fact
    return Frontier(config.index, config.direction,
        analysed = a.filter { it.nonZeroInitial }.mapTo(LinkedHashSet()) { it.key },
        demandEdges = handOff.demandEdges,                             // the implicit zero demand is not counted
        crossableLeaves = a.sumOf { it.crossableLeaves },
        recordCrossings = result.recordCrossings,
        demandVulnerabilities = if (forward) report.demandEntries().size else 0,
        confirmedVulnerabilities = if (forward) report.confirmedCount else 0,
        seeds = handOff.seeds.size,
        zeroOnly = zeroOnly.mapTo(LinkedHashSet()) { it.key },
        zeroOnlyEdges = zeroOnly.sumOf { it.edgeDeltas },               // THE WORK OF THE ZERO FACT
        demandByCause = a.mapNotNull { it.demandByCause }.takeIf { it.isNotEmpty() }
            ?.let { arrays -> DemandCause.entries.associateWith { c -> arrays.sumOf { it[c.ordinal] } } })
}

/** The log line of `IterationDriver.barrier` (THE FRONTIER LOG). The method keys go to the debug log. */
fun Frontier.log() {
    logger.info { "Run $run ($direction) frontier: analysed ${analysed.size}, demand edges ${demandEdges.values.sum()} " +
        "in ${demandEdges.size} method keys, left ${(analysed - demandEdges.keys).size}, crossable leaves " +
        "$crossableLeaves, record crossings $recordCrossings, DEMAND $demandVulnerabilities, CONFIRMED " +
        "$confirmedVulnerabilities, seeds $seeds, zero only ${zeroOnly.size} ($zeroOnlyEdges edges)" }
    logger.debug { "Run $run frontier: analysed $analysed; demand edges $demandEdges" }
    demandByCause?.let { logger.info { "Run $run demand-layer results per cause: $it" } }
}
```

`analysed - demandEdges.keys` are the method keys that LEAVE the frontier: a non-zero initial fact in this run, and no
demand edge for the next run. After a forward run, those with no sink seed in their call subtree are analysed only from
the zero fact in the next forward run (THE EXCLUSION, above; the property test of §9.1 row 30).

THE DEMAND CAUSES (AN OPTION; `SharedObjects.diagnostics`, off by default; `Frontier.demandByCause`). Per run, the
number of demand-layer results per operation that set the layer. Each site compares the layer of its input and of its
result: a NORMAL input with a DEMAND result counts for the site, and a DEMAND input with a DEMAND result counts as
`DEMAND_INPUT`. It is a diagnostic: no rule reads it, and the stop rules do not need it.

| `DemandCause` | The site (`demandByCause[c.ordinal]++` in the analyzer) |
|---|---|
| `FIELD_LIMIT_CUT` | `cut` (§4.3): a result of `ops.limit` (the field-limit cut, `ap.md` §4.4) |
| `MAY_TARGET` | `EngineAlgebra.applyEdge` (§4.3) with `me.may` (a pass rule with an `AnyField` target; backward its reversal) |
| `CLEANER_ROW` | `cleanChain` of the clean stage of a call (§4.5; `ops.clean`, `ap-impl.md` §5.6): a `part` row that demotes |
| `MUST_RECORD` | `applyRecord` (§4.6): each result of `toDemand` (the must-record demotion) |
| `DEMAND_INPUT` | every site above, and `applySummary`, `applyRecord` and a conjunction, for a demand-layer input (a demand fact, link, summary or record) |

---

## 8. Phase 3 and phase 5

### 8.1 The phase-3 entry: `JIRBidiAnalysis`

THE PRESCAN STATE (`analyzer-core.md` §9 PRESCAN MEMORY). The bidi entry first gathers the prescan values: the prescan
rule ids, the prescan lambdas, the fact type checker (DD9) and the external method tracker. Then the caller releases
the WHOLE prescan state before run 1: the prescan runners, the unit storages, the analyzers, the AP manager of the
prescan and `JIRAnalysisManager.contexts`. Today `fullScan` only resets them (`resetApManager`, `TaintAnalyzer.kt:154`)
and keeps the runners, and the bidi path does not call `fullScan`. The GENERALIZE members below do it. The old core
never calls them, so its behaviour does not change:

```kotlin
// CORE/ap/ifds/TaintAnalysisManager.kt: one new member, a no-op by default.
    /** Phase 3: drop the method contexts of the prescan, after the bidi entry copied the prescan values. */
    fun releasePrescan() {}

// JVM/ap/ifds/analysis/JIRAnalysisManager.kt: two new members. ap-impl.md §31.1 adds prescanLambdas().
    /** The reduced rule set of the prescan (relevantRuleIds :75). */
    fun prescanRuleIds(): Set<String> = relevantRuleIds.toSet()

    /** The contexts of the prescan (:76): their alias analyses, liveness and lambda trackers. Call it only after
     *  prescanLambdas(). factTypeChecker (DD9) and externalMethodTracker stay. */
    override fun releasePrescan() = contexts.clear()

// CORE/ap/ifds/TaintAnalysisUnitRunnerManager.kt: one new member. `activeApManager` (:71) becomes nullable, and
// `apManager` (:72) reads `activeApManager!!` (the old core always sets it first, :128).
    /** Phase 3: the whole prescan engine state goes. resetApManager (:127-136) resets the runners and keeps them; this
     *  drops them. A runner that did not stop in the prescan keeps only its own state, until it ends. The Cancellation of
     *  the prescan stays cancelled, so its checkpoints keep failing: the bidi analysis has its own (JIRBidiAnalysis). */
    fun releasePrescan() {
        runnerForUnit.clear()                       // the runners: queues, subscriptions, method analyzers (:79)
        unitStorage.clear()                         // the summaries and the vulnerabilities of the prescan (:80)
        methodDependencies.clear()                  // :81
        activeApManager = null                      // the AP manager of the prescan and its interners (:71)
    }
```

The hook of `TaintAnalyzer` (`CORE/bidi/driver/BidiEntry.kt`):

```kotlin
package org.opentaint.dataflow.bidi.driver

/** analyzer-core.md §9: the phase-3 hook of TaintAnalyzer. JIRBidiAnalysis implements it. */
interface BidiEntry {
    /** Copies the prescan values: the rule ids, the lambdas, the roots, the fact type checker, the external method
     *  tracker. After it, the bidi analysis reads no prescan state, so the caller releases it. */
    fun gather(manager: TaintAnalysisManager, startMethods: List<MethodWithContext>)
    fun run(budget: Duration): Report
    fun toVulnerabilities(report: Report): List<VulnerabilityWithTrace>
    fun status(report: Report): TaintAnalysisUnitRunnerManager.Status
}
```

```kotlin
package org.opentaint.dataflow.jvm.bidi

/** analyzer-core.md §9. It copies the prescan values once (`gather`), then runs the driver (`run`). It keeps no prescan
 *  context. It has no external cancel: the status is set before every cancel, and only the timeout of a run, a memory
 *  guard (of a run or of the barrier) and a runner failure cancel (analyzer-core.md §6.3). */
class JIRBidiAnalysis(
    private val cp: JIRClasspath,
    private val graph: JApplicationGraph,                        // TaintAnalyzer.ifdsAnalysisGraph (TaintAnalyzer.kt:60-62)
    private val unitResolver: JIRUnitResolver,                   // the same units as the old core (JIRTaintAnalyzer.kt:95)
    private val taintConfig: TaintRulesProvider,
    private val params: JIRAnalysisManager.Params,               // alias params, default get model (JIRTaintAnalyzer.kt:52-57)
    private val policy: IterationPolicy,
    private val refManager: RefManager,                          // SHARED with the prescan: the memory guard sees its soft tables
) : BidiEntry {
    /** OWN Cancellation, not the one of the prescan (TaintAnalyzer.kt:85-86): RunManager.init activates it, and a shared one
     *  would make the checkpoints of a prescan runner that did not stop pass again (§8.1, releasePrescan). ApManager,
     *  JIRMethodEntries and SharedObjects take it. */
    private val cancellation = Cancellation()

    /** The prescan values. None of them refers to a context or a store of the prescan. */
    class PrescanResult(
        val ruleIds: Set<String>,                                // JIRAnalysisManager.prescanRuleIds()
        val lambdas: PrescanLambdas,                             // JIRAnalysisManager.prescanLambdas() (ap-impl.md §31.1)
        val roots: List<MethodEntryPoint>,                       // the entry points of the start methods
        val checker: JIRFactTypeChecker,                         // DD9: JIRAnalysisManager.factTypeChecker (JIRAnalysisManager.kt:68)
        val externalMethodTracker: ExternalMethodTracker?,       // JIRAnalysisManager.externalMethodTracker (:63)
    )

    private var prescan: PrescanResult? = null

    override fun gather(manager: TaintAnalysisManager, startMethods: List<MethodWithContext>) {
        val m = manager as JIRAnalysisManager
        val resolver = JIRMethodEntrypointResolver(graph)
        val roots = startMethods.flatMap { s ->                  // as today (TaintAnalysisUnitRunner.kt:284-293)
            resolver.resolveEntryPoints(s.method, s.ctx).map { MethodEntryPoint(s.ctx, it) }
        }
        prescan = PrescanResult(m.prescanRuleIds(), m.prescanLambdas(), roots, m.factTypeChecker, m.externalMethodTracker)
    }

    override fun run(budget: Duration): Report {
        val pre = checkNotNull(prescan) { "gather() comes first" }.also { prescan = null }
        taintConfig.selectRules(pre.ruleIds)                     // the reduced rules (today JVM/ap/ifds/analysis/JIRAnalysisManager.kt:86)
        val ap = ApManager(cancellation, refManager)             // ap-impl.md §5.1; the memory guard clears its soft trie tables (ap-impl.md DD5)
        val language = JIRLanguageManager(cp)                    // REUSE
        val callResolver = JIRCallResolver(cp, unitResolver)     // REUSE (today JIRAnalysisManager.kt:98)
        val entries = JIRMethodEntries(graph, language, callResolver, taintConfig, params.aliasAnalysisParams,
            cancellation, pre.lambdas)                           // ap-impl.md §31.2: the lambdas, copied once
        val interpreter = JIRInterpreter(ap, taintConfig, pre.checker, callResolver,
            JIRMethodEntrypointResolver(graph), entries, params.defaultGetModel, pre.externalMethodTracker)   // ap-impl.md §25
        val contexts = MethodContextCache(interpreter, JIRMethodContextCache(interpreter, entries))
        @Suppress("UNCHECKED_CAST")
        SharedObjects(ap, ApOps(ap), interpreter, language, contexts, PersistentRecordStore(ap),
            ConcurrentVulnerabilityStore(ap), unitResolver as UnitResolver<CommonMethod>, refManager, cancellation).use { shared ->
            return IterationDriver(policy, shared, budget).analyze(pre.roots)
        }
    }

    /** analyzer-core.md §9 OUTPUT, TRACE (ap-history.md F68). EVERY ENTRY OF THE REPORT, CONFIRMED and DEMAND: the
     *  CONFIRMED vulnerabilities and the DEMAND vulnerabilities of the latest complete forward run (ap.md §8.10), each with
     *  the SIMPLE trace of today: the trace with only the sink statement (TracePathGenerationResult.Simple,
     *  CORE/ap/ifds/trace/path/TracePath.kt:23). So the soundness claim "the analysis can stop at any complete forward
     *  run" (ap.md §0.1, §6.6) holds for the output. The vulnerability has the form of today's unconditional
     *  vulnerability (TaintSinkTracker.kt:114). ITS METHOD KEY: the method key of a confirmed witness if the entry has
     *  one, else of the first witness. The log gives the count per state. THE STATE OF AN `[any]`-SOURCE FINDING
     *  (ap-history.md F69): a finding whose taint comes from a source with an `[any]` target (for example the
     *  whole-object DTO source of a Spring entry point) can be CONFIRMED, also after a setter on the object (the strong
     *  write gives an exclusion, not a demand fact). Only a finding that rests on a demotion of ap.md §2.2 stays DEMAND
     *  (analyzer-core.md §7.5; ReportBuilder.add, §7.6): the field-limit cut; a cleaner `part` row other than `atAndBelow`
     *  and `below` one accessor below the fact (the `exact` cleaner at the path of the fact or below it, any cleaner two or
     *  more accessors below it); a may target (the `[any]` target of a pass rule with an `AnyField` target); a demand
     *  input (a demand fact, summary or record); the must-record demotion (`recLayer`). EXPECTED FALSE POSITIVES (ap.md
     *  §11.1; analyzer-core.md §11): a WEAK update below such an
     *  object (a write through an alias, the constructor pass-over, the default identity of an unresolved callee, a
     *  call-result alias) keeps the object whole, so a finding on the overwritten field is CONFIRMED (DEMAND before
     *  F69), as for a `$` fact today.
     *  KNOWN GAP (ap.md §11.1): no end-fact check of today's VulnerabilityChecker, so a vulnerability of a sink rule with
     *  end-fact actions is in the output also when no end fact reaches the end of the analysis. */
    override fun toVulnerabilities(report: Report): List<VulnerabilityWithTrace> {
        val count = report.entries.groupingBy { it.state }.eachCount()
        logger.info { "Bidi analysis: ${count[ReportState.CONFIRMED] ?: 0} CONFIRMED, ${count[ReportState.DEMAND] ?: 0} DEMAND vulnerabilities" }
        return report.entries.map { e ->
            val rule = e.key.rule
            val witness = e.witnesses.firstOrNull { it.confirmed } ?: e.witnesses.first()
            val node = TaintSinkTracker.TaintVulnerabilityRuleNode.Unconditional(witness.methodKey)
            VulnerabilityWithTrace(TaintSinkTracker.TaintVulnerability(e.key.statement, rule.id, hashMapOf(rule to node)),
                TracePathGenerationResult.Simple)
        }
    }

    /** analyzer-core.md §9: Report.end to today's status (TaintAnalysisUnitRunnerManager.Status, :65-67). */
    override fun status(report: Report): TaintAnalysisUnitRunnerManager.Status = when (report.end.status) {
        RunStatus.COMPLETE -> Status.OK                          // STOP_RULE, NO_DEMAND_EDGE or POLICY
        RunStatus.TIMEOUT -> Status.TIMEOUT
        RunStatus.OOM -> Status.OOM                              // a memory guard, of a run or of the barrier (never a JVM OutOfMemoryError)
        RunStatus.FAILED -> Status.EXCEPTION                     // a runner failure, a runner that did not stop, a Throwable of the driver
    }
}
```

How `TaintAnalyzer` calls it in phase 3 (a sketch; `SAST/common/sast/dataflow/TaintAnalyzer.kt:118-131`):

```kotlin
    /** Phase 3. JIRTaintAnalyzer gives its JIRBidiAnalysis; null: the old full scan. */
    open fun bidiEntry(): BidiEntry? = null

    private fun analyzeStaged(entryPoints: List<Method>): Pair<List<VulnerabilityWithTrace>, Status> {
        val analysisStart = TimeSource.Monotonic.markNow()
        val startMethods = entryPoints.map { MethodWithContext(it, EmptyMethodContext) }
        prescan(startMethods)                                        // the old core, unchanged (:133-146)
        val bidi = bidiEntry() ?: return fullScan(analysisStart, entryPoints, startMethods)   // today (:148-224)
        val report = runCatching {                                   // the bidi analysis, as today's runCatching (:157-158)
            bidi.gather(analysisManager, startMethods)               // 1: the prescan values (analyzer-core.md §9)
            analysisManager.releasePrescan()                         // 2: then the WHOLE prescan state goes: the contexts,
            ifdsEngine.releasePrescan()                              //    the runners, the unit storages, the AP manager
            bidi.run(options.ifdsTimeout - analysisStart.elapsedNow())   // the driver itself returns the report so far (§7.1)
        }.getOrElse { e ->                                           // a throw outside the driver (the setup of `run`)
            logger.error(e) { "Bidi analysis failed" }
            return emptyList<VulnerabilityWithTrace>() to
                Status(TaintAnalysisUnitRunnerManager.Status.EXCEPTION, TaintAnalysisUnitRunnerManager.Status.OK)
        }
        var vulnerabilities = bidi.toVulnerabilities(report)
        if (options.analysisCwe != null) vulnerabilities = vulnerabilities.filter {   // the CWE filter of today (:191-198)
            val cwe = (it.vulnerability.rule.meta as TaintSinkMeta).cwe
            cwe?.intersect(options.analysisCwe)?.isNotEmpty() ?: true
        }
        return vulnerabilities to Status(bidi.status(report), TaintAnalysisUnitRunnerManager.Status.OK)
    }

    // JIRTaintAnalyzer. `ifdsAnalysisGraph` (TaintAnalyzer.kt:60-62) becomes protected. `bidiPolicy` is a new constructor
    // parameter (null: the old full scan); the production policy is a phase-3 option (analyzer-core.md §0). The bidi
    // analysis takes the RefManager of TaintAnalyzer and makes its own Cancellation (JIRBidiAnalysis).
    override fun bidiEntry(): BidiEntry? = bidiPolicy?.let { policy ->
        JIRBidiAnalysis(cp, ifdsAnalysisGraph as JApplicationGraph, analysisUnit, taintConfig, analysisParams, policy,
            refManager)
    }
```

The trace resolution status is `OK`: phase 3 resolves no trace. The CWE filter of today (`TaintAnalyzer.kt:191-198`)
applies to the output, as in `fullScan`.

### 8.2 The phase-5 read API: out of scope

The trace resolution is out of scope (`analyzer-core.md` §9 TRACE). The core keeps no store of a run for a trace
resolver: the edge stores of each run go at the end of the run and the other stores after its barrier (§7.7), and the
report holds only the witnesses of its keys (`Report.Entry.witnesses`, §7.6). The phase-3 output gives each
vulnerability of the report, CONFIRMED and DEMAND, the SIMPLE trace of today (§8.1). This document gives no read API for
a trace resolver.

---

## 9. Test plan (`analyzer-core.md` §13)

### 9.1 Test classes and the TDD order

Tests use `kotlin.test` as today. The engine tests are in `TEST/bidi/engine/`, the driver tests in `TEST/bidi/driver/`,
the JVM tests in `opentaint-jvm-dataflow/src/test/.../jvm/bidi/`. Test fixtures (test-only, this document):

* `ApFixtures`: patterns to `InitialAp` (`ApManager.initial`), `Facts` of each kind (`Reach.of`; `ApOps.startFact` of
  a `*` premise for FLOW; `ApOps.targetTree` for TAINT: `tree(base, path, tail, mark, layer, exclusion)`, by default in
  the layer that the tail gives, demand for `ANY` and normal for `ANY_TAINT` and `EXACT`, `ap.md` W6, W8, and with the
  Empty exclusion; `initial(base, path, tail, mark, exclusion)` the same for `InitialAp`), `CallerRef`s and fake call
  statements;
* `ToyInterpreter`, `ToyProgram` (§9.2): a test `Interpreter` and `MethodContextSource` that build the forward forms of
  `ap-impl.md` §23 (`StatementSummary`, `CallPlan` with `StageKind`s, `RuleStatement`, `ExitRules`) from a small program
  DSL (bindings, field read and write, a source, a sink, a cleaner, a `throw` to an exceptional exit, exit rules at each
  exit, a native callee); `ToyPrograms` holds the programs of `ap.md` §6.3, §6.4, program 3 (a source two levels below a
  return value: `h(){ t = g(); sink(t); }`, `g(){ return f(); }`, `f(){ return src(); }`), the backward cases, a
  method that throws, and the programs of the tail `[any-taint]` and its exclusion (`ap.md` §10.11): G, C, I and P
  (`PassRule`) of `AnyTaintCases`, with their results in the refined closures `AnyTaintEx.D6X`/`DRXs` in
  `AnyTaintExCases2` (`DRXs`: with the earlier restriction `AnyTaintEx.restrictX`, the record of the earlier design);
  S, SD, B, X, R and CL of `AnyTaintExCases`; CUT1, the cut of `AnyTaintExCases.CUT` at `L = 1`
  (`x = srcAny(); x.f.g.h = c; sink(x.f.g.k); sink(x.f.k)`, §9.1 row 24: run 1 has `L >= 1` and the limit never
  decreases, `ap-impl.md` §3.2 `ApMode`, so `CUT` with `L = 0` is a unit test of `ap-impl.md` Part I §8 test 23); and the
  factory MK of `analyzer-core.md` §13 item 25 (`root(){ r = mk(); sink(r.name); sink(r.email); }`,
  `mk(){ d = srcAny(); d.setName(c); d.k = srcU(); return d; }`, `srcU` a source with the target `$` and the mark `U`:
  the zero-premise summary with the two normal leaves `{zero} -> (ret, ., [any-taint], {name, k}, T)` and
  `{zero} -> (ret, .k, $, U)`); and the programs of F70 (`HandoffCases`): WRAP (`root(){ x.a.b.c = source();
  r = wrap(x); sink(r.f.a.b.c); }`, `wrap(x){ ret.f = x; }`, the field limits 1, 2, 3) and the getter
  (`root(){ x.f.a = source(); r = get(x); sink(r.a); }`, `get(x){ return x.f; }`); and the three regression programs
  of the review of F70, with no Lean program (§9.1 rows 21, 31, 32): END (THE TRIGGER OF AN END FACT, §4.9), CONJ (THE
  REVERSAL OF A CONJUNCTION, §4.3) and DLINK (a demand link and `NO_DEMAND_EDGE`, §4.2); and the two programs of F71,
  with the demand written by hand and with no Lean program (the Lean data are the vectors `Handoff.RVec`; §9.1 rows 33,
  34): MARK (`root(){ a = src(); r = m(a); }`, `m(x){ ret.f = x; }`, and its demand-layer variant
  `m(x){ ret.f.g = x; }` at `L = 1`) and STAREX (`root(){ r = m(a); sinkT(r); sinkU(r); }`, `m(x){ ret = x; }`).
  X and CUT1 write a path in ONE toy statement
  (`ToyMethod.writePath`, the keep edges `strongKeep(x, [f, g])`, `ap-impl.md` §23.1, §24): the JVM has no such
  statement (`x.f.g = c` is `t = x.f; t.g = c`, an alias write, `interpreter.md` A3, G7), so X and CUT1 are toy and AP
  tests, not JVM tests. The DSL is `ToyMethod` (§9.2). `ToyInterpreter` CACHES one `MethodForms` per method key and gives
  the same objects on every call, as `FormsCache` does (`ap-impl.md` §23.7, §31.2): `ConjunctionStore`,
  `NaiveClosure.conjInputs`/`sinkInputs` and `sink === guard.sink` (§4.5) compare `SinkRule` and `ConjunctiveEdge` by
  IDENTITY, so with a rebuilt form no conjunction ever combines.

| Order | Class | What it checks (item n: `analyzer-core.md` §13) | Mirrors |
|---|---|---|---|
| 1 | `InFlightTest` | Q1–Q3: zero exactly at quiescence; a decrement at handler start ends early | `Pipeline.Quiesce.creach_inv`, `cnt_zero_iff`, `bad_early_done` |
| 2 | `EventQueueTest`, `DeltaWorklistTest` | the order of today; a key does not change in the queue. Item 15: the `unchanged` items come before the `normal` items; a repeat in `unchanged` is dropped; a loop of statements that do not touch a base ends; the set stays across two `Work` events and goes when the step finds `unchanged` empty; `hasZeroWork` sees a zero-to-zero item in either queue; through a `RunMethodAnalyzer` over a `ToyInterpreter`, a fact on a dead local still reaches a later sink (no liveness check) | `analyzer-core.md` §4.3, §6.1 |
| 3 | `EngineAlgebraTest` | DD12, through a `RunMethodAnalyzer` over a `ToyInterpreter` (`EngineAlgebra` is private; `RunnerPort.onProcess` records the items and `onCut` the results): the three modes of `FormApplier` (`ap-impl.md` §23.3) over `EngineAlgebra` and over `ReferenceAlgebra` (`ap-impl.md` §23.8) give the same per-path results (`ops.leaves`) on random statement summaries and inputs; the source-seed filter and the source hit only at a source-seed place, never in GEN; a request only from a FLOW input; the `BIND_IN` stage of a call (`zero.* -> zero.*`) on `Reach.NORMAL` gives `Reach.NORMAL` | `ap-impl.md` §23.3; `Reverse.Stmt.rev` |
| 4 | `SummaryStorageProtocolTest` | mock storages that break P1, P2, P3, P4 lose a summary in the fixed schedule; the real one does not | `Pipeline.PCex.cex_P1` … `cex_P4`, `step_finds_edge` |
| 5 | `IndexCompletenessTest` | `PublicationIndex.candidates` and `CalleeSubscriptions.candidates` return every part that `matches` accepts (random trees) | `PipelineStore.replay_run1`, `deliver_run1`, `replay_restricted`, `deliver_restricted` |
| 6 | `AnyDeliveryTest` (§9.4) | item 3, in a restricted run (§10 row 1); also an `[any-taint]` caller fact and the summary of its must-premise, the `[any]` premise of the same path as a second premise key, a must-premise with another exclusion as a third, and an `[any-taint]/E` caller fact that no member at a step of `E` satisfies | `Pipeline.PCex.cex_P4`, `PipelineStore.deliver_restricted`; `PipelineAnyTaintEx.no_lost_summary_DRX` |
| 7 | `RecordReplayTest` | item 5: direction, reversal, `inside` | `PipelineStore.record_lookup`, rule `retRec` |
| 8 | `NdJoinAdapterTest` | item 4: member 1 by delivery, member 2 by replay, the conclusion in two deltas, through `ndMatch`; the zero fact reaches the same call, and the ND summary never takes the zero subscription (the assert of `ndMatch` holds, and no combination has a zero member); the result premise is the union of the caller premise sets without the zero fact | `PipelineAP.clDN_npart` |
| 9 | `CallPlanRunnerTest` | item 8: the reversed plan of a JVM call runs the steps of `interpreter.md` §4.9 in order (the table of `ap-impl.md` §23.6); seeds at `BOUND`; `PASS_OVER`; the alias guard forward only: the identity part of a delta of `x.$ (T) -> {x.$ (T), x.f.$ (T)}` (TAINT) or of `x.* -> {x.*, x.f.*}` (FLOW) is not aliased, its effect part is (`interpreter.md` AC4 per summary edge); the two `UNRESOLVED` stages; `UnresolvedCallObserver` once per added fact in run 1, never in a later run. Item 17: a demand-layer summary result equal to its start fact goes to the aliases, a normal one does not (`summaryParts`, §4.6); a sink with an end-fact action that triggers on a demand-layer sink edge gives a demand-layer end fact on `{zero}`. THE ZERO BINDING (§4.10): forward, the zero fact (a REACH on `{zero}`) at a call passes over it AND goes through `BIND_IN` to `BOUND` (an unconditional call sink fires), the sources stage and `ADDED` (one `Subscription` and one `LinkIn` per callee, with a REACH added fact; the callee starts the zero fact); backward, a reversed source at a call gives a REACH on `{jb}` at `BOUND` that reaches `BEFORE` through the reversed zero binding, and a REACH on `{jb}` before a call only passes over it. THE REWRITER (`interpreter.md` D23): the `Rewrite` stage of a selected user source removes `T` from a zero-premise summary result and from the default identity of an unresolved callee; on an `AnyField` action position `P.[any]` it cleans `(P, atAndBelow, T)` for a selected source (`interpreter.md` D34) and `(P, below, T)` for a selected cleaner (its row of `interpreter.md` §5.2, as today), every other position `(P, exact, T)` | `Reverse.Call.rev` (argued); `Backward.DB` rules `zpass`, `zin` |
| 10 | `ModesTest` | item 8: a request in a restricted run fails; no sink check backward; the zero fact enters every callee backward. DD7: a requirement reaches a source above a seeded sink call; no backward summary `jb → requirement-of-the-seed` exists, and `persist` writes no such record. Item 16: a call whose only callee is a native method is an unresolved call (the pass rules and the default identity act; no analyzer, no link); a call with a native callee and a callee with a body links only to the second one | `RExact.DR_no_request`; the premises of `Backward.DB` rules `zin`, `seed`, `zret` |
| 11 | `FactKindsTest` | DD11 (`ap.md` §7.2): a restricted run never pushes a FLOW item (forward and backward); `raise` rejects a request from a TAINT or a REACH input; run 1: a FLOW added fact and a TAINT summary (a concrete premise mark) give no application and no request, and the standing request of the callee climbs through the link of that caller; a FLOW record applies to a TAINT added fact as a transfer function (TAINT result); an edge with a `PremiseSet` premise is TAINT (`checkKinds`); a conjunction of a `{zero}` input and an `{i}` input gives an `{i}` edge, and of two `{zero}` inputs a `{zero}` edge (`ap.md` §4.6) | `Coverage.summary_step`, `Coverage.req_initial_star`, `climbsB` |
| 12 | `ExitRulesTest` | `analyzer-core.md` §4.3, §4.4; `interpreter.md` §4.7 and §7.2 items 13, 15. Forward: an exit sink on `Result` at the exceptional exit triggers on the thrown tainted value (a witness at that exit); an end fact of it triggers a second exit sink there, and the end order stops (DD4); an exit source at the exceptional exit and a fact that reaches it give no summary edge, and no global-state drop or entry-mark removal acts there, while the same facts at the normal exit give their summaries. Backward: `HandOff` seeds that exit sink when its vulnerability is DEMAND in the report (F70; else the test writes the seed by hand); the seed enters at the exceptional exit with the premise `{zero}` and goes through the reversed exit rules of that exit (an exit source of the same exit records its source hit; `interpreter.md` §4.9 SEEDS, `analyzer-core.md` §4.4); a fact that is not zero does not start at the exceptional exit. Item 18, THE GLOBAL-STATE RULE: a conjunctive exit sink `ContainsMark(S.<C>, STATE) ∧ ContainsMark(Result, T)`: at an exit where only the `S` literal holds on a zero-premise item, the `S` part leaves the summary edge and is the stored input of that literal; a later item with `Result` tainted completes the combination with it (a witness). A CALLER-SET STATE (`interpreter.md` D30; `ap-history.md` F68): `main(){ setup(); use(); after(); }` with the exit sink on `use` and a sink on the state in `after`: `use` evaluates the `S` fact (its premise is not zero), does not drop it, and `after` still sees it after the call (run 1 and a restricted run); `NaiveClosure.end` agrees. Item 21, A CONJUNCTIVE EXIT SOURCE (`interpreter.md` D31): an exit source with two positive literals stores the input of each literal; the full combination, in either order of arrival, gives a summary at the normal exit with the union of the premise sets, with two non-zero premises an ND summary that a caller applies by E6 (§4.11); the exit items stay in the summary; no rule error. THE ENTRY MARKS (`interpreter.md` §4.7 step 4, G2, D35, §7.2 item 35; `endAt` step 4): at the normal exit a zero-premise TAINT result on `arg0` with the entry mark `m` loses EVERY leaf of `m`, at every depth and with both tails: the Spring DTO entry fact `{arg0.$ (m), arg0.[any-taint] (m)}`, the same object after a setter `arg0.[any-taint]/{f} (m)`, and `arg0.f.$ (m)` give no summary leaf with `m`; a leaf with another mark stays in its layer; a zero-premise result on `ret` or on a static keeps `m`, and so does a result with a premise that is not zero; `NaiveClosure.end` agrees | `Backward.DB` rule `seed`; `FSeeds.srcHit` |
| 13 | `CutPointTest` | the field limit (`ap.md` §4.4; the table of `ap-impl.md` §5.7): a toy program reaches every value of `Cut` (`RunnerPort.onCut`) with a fact deeper than `L`; after each cut no stored fact has more than `L` counted accessors (the `ap.md` W3 assert at `MethodEdgeStore.add` does not fire); a REACH passes every cut | `limitF_sound` |
| 14 | `RequestJoinTest` | `addLink`/`addRequest` through `StandingJoin` with `ApOps.requestAction` on the `main1`/`main2` example of `ap.md` §4.5 (a new caller edge of an old added fact climbs); request first or link first: each pair meets once | `answerInit_covers`, `climbsB`, `Store.standing_complete` |
| 15 | `NaiveClosureTest` | the reference itself on programs 1 and 2: it reports the vulnerabilities of `RCases.p1_found_M`, `p2_found_M`; with the hand-off before F70 read on its closures, its demand after run 2 is `Backward.dem1_exact`, `dem2_exact`. F70: on WRAP and the getter its demand edges (`demandEdges`) give the hand-offs `HandoffCases.Wrap.handF_w1_exact`, `HandoffCases.Wrap.demN_exact`, `HandoffCases.Getter.handF_g1_exact`, `HandoffCases.Getter.demG_exact`, and on WRAP its run-3 closure has only the zero fact in `wrap` | `Backward.p1_found`, `p2_found`, `dem1_exact`, `dem2_exact`; `HandoffCases.Wrap.inv_fn`, `HandoffCases.Wrap.fn_wrap_zero_only` |
| 16 | `ScheduleFuzzTest` (§9.2) | item 1; also on the programs G, C, I, P, S, SD, B, X, R, CL, CUT1 and MK (§9.1; the tail `[any-taint]` and its exclusion), and WRAP, the getter, END, CONJ and DLINK (F70), and MARK and STAREX (F71: the publications, the demand edges and the initial facts of the engine equal those of the reference with its mark tests). F70: the demand edges of the engine (`RunSummaryStore.demandEdges()`) equal those of the reference (`NaiveClosure.demandEdges`), in every schedule; in a backward run of END the trigger seeds of the engine and of the reference give the same facts | `Pipeline.quiescent_exact`, `quiescent_dominates`; `PipelineAnyTaintEx.result_D6X`, `result_DRX` (with the spec rules `AnyTaintEx.emitX`, `AnyTaintEx.satX`, `HandoffX.restrictIX`; `PipelineAnyTaintEx.result_DRXs` is its instance with the earlier restriction); `PipelineHandoffDriver.pubSeqXst_pubSeqNX` |
| 17 | `RunManagerLifecycleTest` | item 6: a late send keeps the run open; a new `RunManager` after an aborted one analyses every method; a failed runner does not cancel the next run. Item 12: after `fail(OOM)` a handler that throws `Cancellation.Cancelled` stops its runner, and the run ends `OOM` before its timeout; a `fail()` after the quiescence leaves the run `COMPLETE` (the first end wins); a `fail()` before `run` starts no root; a runner that does not stop gives `FAILED` and no analyzers, also after the quiescence (the join overrides the first end). A RUNNER FAILURE (`ap-history.md` F68): a handler that throws an `Exception` or an `Error` ends the run `FAILED` before its timeout, and the other runners stop; a throw of the caller-thread code of `run` (a `route` that throws) gives `FAILED`, and `run` still joins every runner | `analyzer-core.md` §6.3 |
| 18 | `SupportTest` | the support tree; two premises at two calls are not supported; a set is confirmed as a whole; a merged witness (`ap-impl.md` §7.12). Item 14: one sink statement that two contexts reach is one vulnerability key; a confirmed witness in one context makes it CONFIRMED, and each witness reads the support in its own method key; two alternatives of one sink rule that trigger on two bases with the same premise set give two witnesses, and the store does not fail | `Confirmed.Sup`, `NDConfirmed.SupN`, `NDConfirmed.CexSites.cex_sites`, `Confirmed.Weak.weak_support_gap` |
| 19 | `HandOffTest` | item 7, WITH F70 (the test makes the runs with `RunManager` and `HandOff.of` itself, with no stop rule). `HandOff.of` reads only `demandEdges()`, never `all()`: each demand edge gives the pattern of the table of §7.3 (forward: `(D-c = piece, D-p = member)`, an `[any-taint]/E` leaf or must-premise as `[any]` with no exclusion; backward: `(gb, none)` for the zero premise, `(gb', jb)` else, `(zero, jb)` for a REACH piece), each with the marks of the piece and of the member (F71: `located` changes only the tail and the exclusion), and `demandEdges` counts them per method key. Program 1: the demand of run 3 equals `Backward.dem1_exact` (no call of program 1 returns, so case 3 is empty, `HandoffRCases.p1_no_exit`; the new hand-off gives these patterns, `HandoffRCases.p1_handoff`), and run 3 reports the vulnerability (`HandoffRCases.p1_chain`). Program 2: the demand of run 3 equals `Backward.dem2_exact` (the summaries of `c` are a demand-layer getter, not crossable, `HandoffRCases.r1_c_not_cross`, `HandoffRCases.b2_not_crossB`, and the intersection keeps the same pieces, `HandoffRCases.b2_restrictI_eq_U`, `HandoffRCases.f3_restrictI_eq_U`; the mark tests of F71 pass there, `HandoffRCases.b2_insideB`, `HandoffRCases.b2_concMark`, `HandoffRCases.f3_insideB`, `HandoffRCases.f3_concMark`, so the pieces do not change; the new hand-off gives this pattern, `HandoffRCases.p2_handoff`; that it gives no other pattern is checked by hand), and run 3 reports the vulnerability (`HandoffRCases.p2_chain`). WRAP and the getter: the exact hand-offs (row 29). Program 3 (§4.6, the case-3 chain; the seed of `sink(t)` written by hand, because run 1 confirms it and `HandOff.of` seeds only DEMAND vulnerabilities): the run-1 summaries `{zero} → ret.$ (T)` of `f` and `g` are crossable, so there is no demand edge for them; backward run 2 crosses `g` by the reversed record `ret.$ (T) → zero` and has only the zero fact in `f` and `g`; the forward demand of `f` and `g` is the zero demand only; run 3 reports the sink of `h` with a confirmed witness. THE SEEDS (`analyzer-core.md` §13 item 38): only the witnesses of `ReportBuilder.demandEntries()`: of two vulnerabilities, run 1 confirms one and reports the other as DEMAND, and backward run 2 seeds only the DEMAND one; a key that an earlier complete forward run confirmed and that the latest run reports in the demand layer has no seed; the report after run 3 holds both; the seeds of a witness are at its method key. `nextConfig` rejects a decreasing field limit | `Backward.dem1_exact`, `p1_found`, `p2_found` (the hand-off before F70); `HandoffRCases.p1_handoff`, `HandoffRCases.p1_chain`, `HandoffRCases.p2_handoff`, `HandoffRCases.p2_chain` (F70); `HandoffRCases.b2_insideB`, `HandoffRCases.b2_concMark`, `HandoffRCases.f3_insideB`, `HandoffRCases.f3_concMark` (F71); `HandoffMain.iteration_generalN` (the DEMAND seeds: `hseeds` "confirmed or seeded"), `PipelineHandoffDriverExt.driver_iterationNX_demand`; `HandoffCases.Wrap.handF_w1_exact`, `HandoffCases.Wrap.demN_exact`, `HandoffCases.Getter.handF_g1_exact`, `HandoffCases.Getter.demG_exact` |
| 20 | `SourceSeedsTest` | item 10 (a source at a call, an entry, an exit, a read; end facts never filtered). F70: a source on the witness outside a recorded call fires; a source inside a crossable callee is not hit (the backward run crosses the callee by the reversed record), so it is no source seed and does not fire, and the zero-premise record of the callee still gives its result (an engine test with the records written by hand, as row 25: `root(){ x = mk(); sink(x); }`, `mk(){ ret = source(); }`, a restricted forward run with no source seed in `mk` and the run-1 record `{zero} → (ret, ., $, T)` of `mk`: the sink is reported in the normal layer; Lean `HandoffSrc.SrcRec.found_unseeded`: the source seeds do not filter the records, precision only) | `FSeeds.srcHit`, `srcHit_applies`, `PipelineSeeds.driver_iteration_src`; F70: `HandoffSrc.B_srcN`, `HandoffSrc.iteration_srcN`, `HandoffSrc.iteration_srcNX`, `PipelineHandoffDriverExt.driver_iteration_srcNX` (finite: `HandoffSrc.iteration_srcN_upto`, `PipelineHandoffDriverExt.driver_iteration_srcNX_upto`), `HandoffSrc.SrcRec.found_unseeded` |
| 21 | `StopRuleTest`, `ReportTest` | item 9; item 12: the stop rule gives `STOP_RULE`, the policy `POLICY`, an exception at the barrier `ABNORMAL` with the status `FAILED` and the report of the earlier runs. THE STOP RULES OF F70 (`analyzer-core.md` §7.1): `STOP_RULE` reads the REPORT: a key that run 1 CONFIRMED and run 3 reports only in the demand layer is no DEMAND vulnerability (`ReportBuilder.hasDemandVulnerability` is false with no other key), gives no sink seed, and the end is `STOP_RULE` after run 3; `NO_DEMAND_EDGE`: a forward run whose only DEMAND vulnerability fails only the joint support (two premises that two call statements supply, row 18) and that has no demand-layer object ends with `NO_DEMAND_EDGE`, and `continueAfter` is not asked; a demand-layer summary delta alone (an exit-rule cut, `Cut.EXIT_RULES`) counts as a demand-layer object (`RunResult.demandLayerEdges > 0`), so the iteration goes on; A DEMAND LINK ALONE COUNTS TOO (program DLINK, the regression of the review of F70; `IterationDriver` with `FixedLimits(listOf(1, 2, 3, 4, 5))`): `root(){ dto = srcAny(); c(dto); }`, `c(x){ y = x.q.r; m(y); }` with the exact call cleaner `CleanMark(T, arg0.g.k)` at `m(y)`, `m(p){ sink(p.g.h); throw E(); }` (`sink` with the pattern `(p, .g.h, $, T)`; `m` has no normal exit, so no summary and no record): run 1 reports V DEMAND; backward run 2 hands off `c` the pattern `((x, .q.r, [any], T), none)` (the cut at `L = 2`) and hits `srcAny`; in forward run 3 the bound fact `(p, ., [any-taint], T)` of `m(y)` is demoted by the cleaner to `(p, ., [any], T)` on a DEMAND link, the emission gives the premise `(p, .g.h, $, T)` with a normal start, the sink edge is normal and V is DEMAND (condition 3.2.2), and every edge and summary of run 3 is normal: `demandLayerEdges` is 1 (the demand link, `addLink`), so the end is NOT `NO_DEMAND_EDGE` after run 3; backward run 4 gives `c` the pattern `((x, .q.r.g.h, $, T), none)`, forward run 5 has a normal link at `m(y)` and CONFIRMS V, and the end is `STOP_RULE` after run 5; the order of the table of §7.1 (`STOP_RULE` before `NO_DEMAND_EDGE` before `POLICY`). THE FRONTIER LOG: one `Frontier` per complete run, backward runs and the last run included, in run order; `continueAfter` gets the list, whose last entry is the run that it asks about. Item 13: run 1 complete (one CONFIRMED and one DEMAND vulnerability), run 2 complete, run 3 incomplete: the report is that of run 1 and run 3 refutes nothing; `continueAfter` is never asked after a backward run. AN INCOMPLETE RUN 1 (`ap-history.md` F68): run 1 incomplete (`TIMEOUT`): the report has no entry, `end = (TIMEOUT, 1, FORWARD, ABNORMAL)`, and the output is empty. THE BARRIER (F68): stub `RecordStore`s whose `persist` throws an `OutOfMemoryError` or an `Exception`: the report of the earlier runs, `ABNORMAL`, the status `FAILED` for both (a JVM `OutOfMemoryError` is not `OOM`); a stub `persist` that cancels the `Cancellation`, as the barrier guard does, and then reaches a checkpoint (`Cancellation.Cancelled`) or returns (a cancel after the last checkpoint) gives `OOM`, `ABNORMAL` and the report so far. A policy with `fieldLimit(1) = 0`: `FAILED`, `ABNORMAL`, no entry. A throw in `RunManager(...)` of a later run: `FAILED`, `ABNORMAL`, the report so far, and no runner alive after the return (`analyzer-core.md` §13 item 12) | `PipelineDriver.driver_iteration_upto`; F70: `HandoffMain.iteration_generalN`, `PipelineHandoffDriverExt.driver_iterationNX_upto` (`STOP_RULE` with the DEMAND seeds; `NO_DEMAND_EDGE` is argued, `analyzer-core.md` §11; DLINK has no Lean program) |
| 22 | JVM regression | item 11: the existing analysis tests through phase 3; the output has every vulnerability of the report, CONFIRMED and DEMAND (a finding from an `[any]`-target source, also a Spring DTO entry-point argument, can be CONFIRMED: in run 1 when the sink reads the object in the method of the source, also after a setter on it (the setter field itself is not reported), in forward run 3 through a getter or a sink in a callee; a finding that rests on a demotion of `ap.md` §2.2 is DEMAND (the list of `ReportBuilder.add`, §7.6: the field-limit cut; a cleaner `part` row other than `atAndBelow` and `below` one accessor below the fact, so the `exact` cleaner at the path of the fact or below it and any cleaner two or more accessors below it; a may target, the `[any]` target of a pass rule with an `AnyField` target; a demand input, a demand fact, summary or record; the must-record demotion `recLayer`); a weak update below the object (an alias write, the constructor pass-over, the default identity of an unresolved callee, a call-result alias; the four of `ap.md` §11.1) is an expected CONFIRMED false positive, also the two-level write `x.f.g = c` of program X, which the JVM gives as `t = x.f; t.g = c` (an alias write, `interpreter.md` G7: `sink(x.f.g)`, `sink(x.f.h)` and `sink(x.k)` CONFIRMED; the exact results of X are a toy and AP test, row 24); the cut on the JVM runs with `L = 1`: the source `dto.f.g = srcAny()` gives `(dto, .f, [any], T)` in the demand layer with no exclusion, so a sink below `dto.f` is a DEMAND entry (`AnyTaintCases.Cut.cut_transfer`); `ap.md` W6, W8, `analyzer-core.md` §13 items 20, 22 to 24, 28, 31), each with the SIMPLE trace, on the method key of a confirmed witness or else of the first witness, and the log gives the count per state (§8.1). `JIRBidiAnalysis.status`: one `Report` per status maps `COMPLETE` to `OK`, `TIMEOUT` to `TIMEOUT`, `OOM` to `OOM` and `FAILED` to `EXCEPTION`. The CWE filter of `analyzeStaged` keeps only the vulnerabilities of `options.analysisCwe`; a throw of `JIRBidiAnalysis.run` gives an empty output with `EXCEPTION` | — |
| 23 | `PrescanReleaseTest` (JVM) | `ap-history.md` F67 (18), `analyzer-core.md` §9 PRESCAN MEMORY: after `gather` and both `releasePrescan()` calls, weak references to the prescan `ApManager`, to one prescan runner and to one `JIRMethodAnalysisContext` are cleared after `System.gc()` (poll a few times); the bidi analysis has its own `Cancellation` (§8.1) | — |
| 24 | `AnyTaintLayerTest` | items 24, 27 to 30, and item 31 at `L = 1` (program CUT1) (the tail `[any-taint]` and its exclusion, through a `RunMethodAnalyzer` over a `ToyInterpreter`; `RunnerPort.onProcess` and `onCut` record the items): program P: the micro edge `P.$ (T) → Q.[any] (T)` as a source (`ToyMethod.anyEdge(source = true)`) gives a normal TAINT item with an `[any-taint]` leaf, and run 1 confirms the vulnerability; as a pass rule it gives `[any]` in the demand layer, and the vulnerability stays DEMAND; in a backward run the reversal of the pass rule gives the requirement `(P, ., $, T)` in the DEMAND layer (`MicroEdge.may`, §4.3), and of the source the ordinary rows. THE EXCLUSION ROWS (no demotion): the keep edge of a strong write gives `[any-taint]/{f}`, normal (program S; program X, the one toy statement `writePath(x, [f, g], c)`: exactly the two results `(x, ., [any-taint], {f}, T)` and `(x, .f, [any-taint], {g}, T)`, `sink(x.f.g)` no witness, `sink(x.f.h)` and `sink(x.k)` confirmed); a read through an excluded accessor gives no item, through another one `[any-taint]` with no exclusion (program R); the named field actions of F74 retain normal `E ∪ {f}` for every reach; `below` also returns normal `(x, .f, $, T)`, and `exact` also returns demand `(x, .f, [any], T)`; program CL tests the primitive AP operation separately; a sink pattern in the excluded part gives no witness. THE DEMOTIONS to `[any]` in the demand layer, with no exclusion (the list of `ReportBuilder.add`, §7.6): the cut at each `Cut` point (`onCut`; program CUT1 with `L = 1`: `writePath(x, [f, g, h], c)` gives `(x, ., [any-taint], {f}, T)` and `(x, .f, [any-taint], {g}, T)`, normal, and its third result `(x, .f.g, [any-taint], {h}, T)` is cut to `(x, .f, [any], T)`, demand, no exclusion; `sink(x.f.g.k)` is a DEMAND witness and `sink(x.f.k)` a confirmed one); the primitive AP `exact` cleaner at the path of the fact and one accessor below it, and a primitive AP cleaner two accessors below it (direct `ops.clean` on `(x, ., [any-taint], T)`); the may target of a pass rule (program P); the must-record demotion (row 26). NO ABSORPTION IN A NORMAL TREE (`ap.md` §7.2 T5, §8.1): `x = srcAny(); y = src(); x.g = y` as a weak write (`write(weak = true)`, both marks `T`) gives the normal tree `{x: [any-taint] (T), x.g: $ (T)}` and keeps the `$` leaf; after the lowered `clean(x.f, exact)` the outside-field `[any-taint]/{f}` fact is normal, and `sink(x.g)` is still CONFIRMED; also test the direct primitive demotion as a separate AP fixture. A conjunctive source with an `[any]` target gives an `[any-taint]` result; a normal `[any-taint]` input that overlaps a `$` literal gives a normal result and a confirmed witness | `AnyTaintExCases2.PassRule.source_confirmed`, `pass_not_confirmed`; `AnyTaintExCases.S.record_app`, `S.run1_name_no_trigger`, `X.two_results`, `X.fh_confirmed`, `R.reads`, `R.z_confirmed`, `CL.atAndBelow_result`, `CL.below_result`, `CL.exact_result` (primitive AP fixtures); `FieldCleanerX.exact_vector`, `below_vector`, `atAndBelow_vector` (lowered actions); the cut row `AnyTaintEx.limitFX`, `AnyTaintEx.Vec.cut_drops` (the Lean program with `L = 0`, `AnyTaintExCases.CUT.cut_ops`, `AnyTaintExCases.CUT.cut_reports`, is the unit test of `ap-impl.md` Part I §8 test 23); `AnyTaintExExact.CexExactCleaner.cex_exact_cleaner`; `AnyTaintND.Example.layer_new`, `confirmed`; `AnyTaint.Sanity` |
| 25 | `MustPremiseTest` | items 25, 27 (and `ap.md` §13 item 11; `analyzer-core.md` §4.1, §4.4, §4.6): in a restricted forward run, an `[any-taint]` added fact (a normal link) and an `[any]` added fact (a demand link) at one path of one callee give two initial facts, two premise keys, two `PublicationIndex` entries and two publications; two `[any-taint]` added facts with the exclusions `{}` and `{h}` at one path give two must-premise keys; every cell of the emission table (`emit`), with the exclusion: a pattern below the added fact at an excluded step gives nothing, at an admitted step the chain with no exclusion, at the path of the added fact the must-premise with its exclusion; the must-premise starts as itself, normal, with its exclusion; a must-premise summary applies only by `inside` (the exclusions read), and through a demand `[any]` link its result is demand; `addInitial` fails on an `[any-taint]` initial fact in run 1 and in a backward run. PROGRAM B IN RUN 3, an engine test with the demand and the records WRITTEN BY HAND (through `IterationDriver` B ends after run 1 with `STOP_RULE`, row 28, so no driver run reaches its run 3): the forward restricted `RunConfig` with the broad demand `dBroad = ((this, ., [any], T), (this, ., [any], T))` of `setName` and the run-1 records of B; the added fact `(this, ., [any-taint], {}, T)` emits the must-premise `(this, ., [any-taint], {}, T)`, its summary is `(this, ., [any-taint], {name}, T)`, normal; `sink(d.name)` has no witness and `sinkAny(e)` has a witness that `Support` confirms | `AnyTaintEx.emitX`, `emitTX`, `startX`, `satX`; `AnyTaintEx.Vec.emit_at`, `emit_above_excluded`, `emit_above_exact`; `AnyTaint.EmitVec`; `AnyTaintExCases.B.run3_must`, `B.run3_summary`, `B.inv3`, `B.run3_name_not_reported`, `B.run3_anyE_confirmed`, `B.run3_with_records`; `PipelineAnyTaintEx.clDRX_pub` |
| 26 | `RecordDemotionTest` | items 5, 25 (`analyzer-core.md` §4.2 `applyRecord`, §5.3, §7.3, §7.4): the must record `(p, ., [any-taint], T) → (ret, ., [any-taint], T)` of `get(p) { ret = p.g }` applied to the added fact `(p, .f, [any-taint], T)` (`applicable`, not `inside`) gives `(x, ., [any], T)` in the demand layer with the origin `SUMMARY_EFFECT`; applied to `(p, ., [any-taint], T)` (`inside`) it gives the normal `(x, ., [any-taint], T)`; applied to `(p, ., [any-taint], {h}, T)` (at the premise with an exclusion that the premise does not have: `applicable` only) it gives the demand `(x, ., [any], T)` with no exclusion; NO OTHER DEMOTION: the run-1 record of a setter `(this, ., *, {}, *) → (this, ., */{name}, *)` applied to `(this, ., [any-taint], T)` gives the normal `(this, ., [any-taint], {name}, T)` (program S); in a backward run `reversedAt` gives no reversal of a must record (no leaf); R3 IS LEAF BY LEAF (`ap.md` §8.7): of the forward record with the two leaves `{zero} → (ret, ., [any-taint], {name, k}, T)` and `{zero} → (ret, .k, $, U)` (the summary of `mk` of the factory MK, §9.1) it reverses only the `$` leaf, into `(ret, .k, $, U) → zero`, which applies in the backward run, and `NaiveClosure.retRec` (`reversibleLeaf`) gives the same; a forward record `$ → [any-taint]` reverses to `[any] → $`, which applies to an `[any]` requirement with a demand result and not to a `$` requirement; `applyRecord` fails on a must record in a backward run; at the barrier `persist` keeps a normal forward summary with an `[any-taint]/E` leaf and a must record with its exclusion, and a normal backward summary as before F69 (the backward run has no `[any-taint]`) | `AnyTaintExact.CexApp.cex_app`, `CexRev.cex_rev`; `AnyTaintEx.recLayerX`; `AnyTaintExCases.S.record_app`; `AnyTaintExExact.recs_of_DRX_valid` |
| 27 | `AnyTaintSupportTest` | item 26, and the confirmation of `ap.md` §13 item 17 (`Support`, §7.5): a normal `[any-taint]/E` sink edge is confirmed; in a restricted forward run a normal `[any-taint]/E` link supplies a `$` member and a must-premise `[any-taint]/E'` inside it with the same mark (at the path of the link only if `E ⊆ E'`); it does not supply a member below it through an accessor in `E` and a `$` member with another concrete mark, and in run 1 it supplies only an equal member; a demand `[any]` link supplies nothing; condition 2 accepts a must-premise in a restricted run only. The mark test is necessary (`AnyTaintExact.CexSupMark.cex_sup_mark`), but its member, a must-premise with the mark `*`, is a model-only object: `InitialAp.init` rejects it (`ap-impl.md` §3.4; tested in `KindTest`), so the test uses a `$` member of another mark. THE REFERENCE FORMS: `Support.condition2` and `Support.suppliers` equal `confirmableMember` and `supplies` (`ap-impl.md` §7.12) on every (member, link) pair of the cases | `AnyTaintEx.SupLinkX`, `SupX`, `Confirmed6X`, `ConfirmedX`; `AnyTaintExact.CexSupMark.cex_sup_mark`, `markSub_conc`; `AnyTaintExExact.confirmed_realX_valid` (with `HandoffX.restrictIX_ok`; `AnyTaintExExact.confirmed_realXs` is the instance of the earlier restriction) |
| 28 | `AnyTaintIterationTest` | items 22, 23 and the run-1 part of item 25 (analysis tests through `IterationDriver` with `FixedLimits(listOf(1, 2, 3))`, as item 13): program G: run 1 reports the key DEMAND (the getter summary is the case `above`); the seed of the `[any]` sink pattern is `[any]` in the demand layer; backward run 2 hands off the demand `((p, .f, [any], T), (ret, ., [any], T))` of `get` (no `[any-taint]` pattern in the `DemandStore`; with F70 the same, because that backward summary is in the demand layer, so it is a demand edge); run 3 emits the must-premise `(p, .f, [any-taint], T)`, its sink edge is normal, the report has the key CONFIRMED with `Entry.run = 3`, and the end is `STOP_RULE`. Program C is CONFIRMED in run 3. Program I (`root(){ dto = srcAny(); x = id(dto); sinkAny(x); }`, `id(p){ return p; }`): the FLOW summary `(p, ., *) → (ret, ., *)` of `id` on the added fact `(p, ., [any-taint], T)` gives `(x, ., [any-taint], T)`, normal, run 1 CONFIRMS `sinkAny(x)` and has no DEMAND entry, so the end is `STOP_RULE` after run 1. Program S: run 1 CONFIRMS `sink(dto.email)`, reports nothing for `sink(dto.name)` and has no DEMAND entry, so the end is `STOP_RULE` after run 1; program SD gives the same; program B: run 1 CONFIRMS `sinkAny(e)`, does not report `sink(d.name)` and has no DEMAND entry, so the driver ends B after run 1 (`STOP_RULE`; the run-3 results of B are the hand-made engine test of row 25). The factory MK (§9.1; item 25): run 1 gives `(r, ., [any-taint], {name, k}, T)`, normal, in `root` (the zero-premise summary of `mk` keeps its exclusion through the zero subscription, §4.6), so `sink(r.name)` is not reported, `sink(r.email)` is CONFIRMED, and the end is `STOP_RULE` after run 1 | `AnyTaintExCases2.G.run1_not_confirmed`, `G.handoffX_get`, `G.HX_exact`, `G.run3_must`, `G.run3_sink_normal`, `G.run3_confirmed_handoff`; `AnyTaintExCases2.C.run3_supported`, `C.run3_confirmed_handoff`; `AnyTaintExCases2.I.run1_flow`, `I.app_normal`, `I.run1_confirmed`, `I.run1_no_demand`; `AnyTaintExCases.S.run1_email_confirmed`, `S.run1_name_not_reported`, `S.run1_no_demand`, `SD.same_result`, `B.run1_anyE_confirmed`, `B.run1_name_not_reported`, `B.inv1`; MK has no Lean program (the target exclusion of the summary conclusion in `AnyTaintEx.applySummaryX`; `AnyTaintExCov.applySummaryX_sound`); `PipelineAnyTaintExDriver.driver_iterationX` |
| 29 | `DemandEdgeTest` | items 32 to 35 (THE DEMAND EDGES ONLY, `ap-history.md` F70; `analyzer-core.md` §7.3, §7.4, §7.8; item 36, the restriction vectors, is `ap-impl.md` Part I §8 test 17, which also has the AP-level mark vectors of items 41 and 42, F71), through `IterationDriver` with `FixedLimits(listOf(1, 2, 3))`, read through `IterationDriver.frontiers` and `RunnerPort.onCut`. PROGRAM WRAP (§9.1): run 1 reports `sink(r.f.a.b.c)` DEMAND (the cut in the root) and seeds it; the one summary `(arg, ., *) → (ret, .f, *)` of `wrap` is crossable (`demandPart` is null), so run 1 has no demand edge of `wrap` (`Frontier.demandEdges` has only the root) and `crossableLeaves >= 1`; backward run 2 has `wrap` in `zeroOnly`, not in `analysed`, and `recordCrossings >= 1` (the reversed record crosses the call, by `applicable`); the forward demand of `wrap` is the zero demand only; forward run 3 has `wrap` in `zeroOnly` with zero-premise edges only, `onCut` records cuts in `root` and none in `wrap`, the record of `wrap` applies in the root, and run 3 reports the key. A CROSSABLE CALLEE IS NEVER ENTERED BY THE BACKWARD RUN (item 33): also a setter `set(v){ this.f = v; }` and an identity `id(p){ return p; }` in place of `wrap` are only in `zeroOnly` of backward run 2, and the requirement still reaches the source in the caller (a source hit). THE GETTER (§9.1): run 1 gives the demand-layer summary of `get` (the case `above`), a demand edge; backward run 2 gives the normal backward summary `(ret, .a, $, T) → (arg, .f.a, $, T)`, whose reversal is crossable (so it is `Handoff.CrossB`), so the forward demand of `get` is the zero demand only; forward run 3 has `get` in `zeroOnly`, crosses it by the reversed record and CONFIRMS the key (a normal sink edge), and the end is `STOP_RULE`. THE CEGAR OF `Cross` (programs ANYW and ANYM; engine tests with the demand and the records WRITTEN BY HAND, as row 25): in a restricted forward run, the normal summary of `anyw(arg){ ret = anyTaint(arg); }` with a `$` premise and an `[any-taint]` conclusion is a demand edge (`demandPart` keeps every `[any-taint]` leaf: its reversed premise is `[any]`); the backward run with that hand-off and the seed of `sink(r.f)` enters `anyw` and reaches the source of the root (a source hit), and the next forward run with that source seed reports `sink(r.f)`; with a stub `ApOps` whose `demandPart` tests only the forward conditions (Lean `HandoffCases.CrossL`), the backward run reaches no source and the next forward run does not report it. ANYM (the source in a callee `mk`, no source seeds): the same loss with the stub, and the report without it. `anyTaint` is a toy micro edge `(arg, ., *) → (ret, ., [any-taint])` that keeps the mark (`ToyMethod.anyTaint`); the interpreter gives a normal `[any-taint]` target only to a source (`interpreter.md` I14), so ANYW and ANYM are toy tests, as X and CUT1 | `HandoffCases.Wrap.wrap_old_vs_new`, `HandoffCases.Wrap.w1_exit_cross`, `HandoffCases.Wrap.handF_w1_exact`, `HandoffCases.Wrap.bn_cross`, `HandoffCases.Wrap.bn_wrap_zero_only`, `HandoffCases.Wrap.demN_exact`, `HandoffCases.Wrap.fn_wrap_zero_only`, `HandoffCases.Wrap.fn_wrap_edges_zero`, `HandoffCases.Wrap.fn_record_applicable`, `HandoffCases.Wrap.fn_cut_in_root`, `HandoffCases.Wrap.fn_found`; `HandoffCases.Getter.g1_exit_demand`, `HandoffCases.Getter.handF_g1_exact`, `HandoffCases.Getter.revRec_g_cross`, `HandoffCases.Getter.revRec_g_crossB`, `HandoffCases.Getter.demG_exact`, `HandoffCases.Getter.fg_getter_zero_only`, `HandoffCases.Getter.fg_found`; `HandoffCases.revRec_any_premise`, `HandoffCases.not_cross_of_any`, `HandoffCases.dollar_blocked`, `HandoffCases.AnyW.cegar_cross_anyw` (`HandoffCases.AnyW.bs_srcHit`, `HandoffCases.AnyW.bl_no_srcHit`, `HandoffCases.AnyW.fs_found`, `HandoffCases.AnyW.fl_lost`), `HandoffCases.AnyM.cegar_cross_anym` (`HandoffCases.AnyM.fsm_found`, `HandoffCases.AnyM.flm_lost`) |
| 30 | `FrontierPropertyTest` | item 37 and THE LOCALIZATION (`ap-history.md` F70; `analyzer-core.md` §7.8). Item 37 on WRAP through `IterationDriver` with `FixedLimits(listOf(1, 2, 3, 4, 5))`: `wrap` is in `analysed` in run 1 and in no later run; the root has only the patterns `(gb, none)` of the seed paths (`HandoffCases.Wrap.demN_exact`), which the narrowing theorem does not cover, so the test asserts no narrowing on them; every complete run logs one frontier; backward run 2 has a record crossing (reversed) and run 3 one too; THE SEED CONDITION IS NEEDED: if `wrap` calls a callee with the sink of a DEMAND vulnerability on the argument of `wrap`, `wrap` is in `analysed` again in the next forward run. PROPERTY TESTS on every program of `ToyPrograms` and on random toy programs (a seeded generator over the DSL of §9.2: up to six methods, calls with and without a result, field reads and writes, sources, sinks, no cleaner on the zero base; 500 programs). The test makes the runs with `RunManager`, `HandOff.of` and `frontierOf` itself, with no stop rule (row 19), with the field limits `1, 2, 3, 3, 3, 3, 3`. THE NARROWING, IN THE LOCATIONS AND THE MARKS, with no exception (`HandoffNoStar.narrowing_canon_loc_exactM`; `ap-history.md` F71): for every forward run `n >= 5` and every pattern `d''` of its `DemandStore` with an exit pattern (case 3 of §7.3; the test asserts nothing on the zero demand and on the patterns `(gb, none)` of the seed paths: the theorem does not cover them), some pattern `d` of the same method key in the `DemandStore` of forward run `n - 2` has every location of `D-c(d'')`, with its mark, in `D-c(d)` and every location of `D-p(d'')`, with its mark, in `D-p(d)` (`insideDemand(D-c(d''), D-c(d))` and `insideDemand(D-p(d''), D-p(d))`, `ap-impl.md` §6: the location part `insideLoc` and the mark part `markSub`). The test reports the two parts apart: a pattern that passes `insideLoc` and fails `markSub` shows a lost mark test (of the restriction, §4.7 `restrictBy`, or of the emission, §4.2 `emit`), which the test in the locations only (before F71) did not see. On the programs with the `[any-taint]` tail the model allows one more cell in the locations (an entry location of `d''` whose forward premise has the Universe exclusion, at a location that this exclusion excludes: `HandoffNoStar.narrowing_canonX_loc_exact`, `HandoffXMain.Dropped`); the AP has no Universe exclusion (§7.8), so the test asserts that this cell has the count 0. THE MARKS of the X runs narrow in every cell, also in that one (`HandoffXMain.narrowing_canonXM`), so the test asserts the mark part on every pattern of these programs too. Any other pattern fails the test; so does a `*` pattern after run 1 (`HandoffNoStar.canon_dem_nonstar`: no cell of `Handoff.RExc` occurs). The counts of `Frontier.demandEdges` are not checked: the narrowing is of locations and marks, not of counts. THE EXCLUSION: a method key with no demand edge after forward run `n` (not in `Frontier.demandEdges` of run `n`) and no sink seed of backward run `n + 1` in its call subtree (the seeds of the hand-off, `SeedIndex.sinkMethods()`, and the method keys of backward run `n + 1` with `triggerSeeds > 0`, THE TRIGGER OF AN END FACT; with the static call graph of the program) is not in `analysed` of backward run `n + 1` and of forward run `n + 2` (`nonZeroInitial` is false: only the zero fact, so only zero-premise edges); the toy programs satisfy the hypotheses (`HandoffExclusion.NoZeroGenP`: no binding into the zero base except the zero binding; no cleaner on the zero base). Such a method key stays out of `analysed` in every later run while no seed lies in its call subtree (argued over several rounds, `analyzer-core.md` §7.8) | `HandoffNoStar.narrowing_canon_loc_exactM` (in the locations only `HandoffNoStar.narrowing_canon_loc_exact`), `HandoffNoStar.narrowing_canonX_loc_exact`, `HandoffXMain.narrowing_canonXM`, `HandoffNoStar.canon_dem_nonstar`, `HandoffNoStar.NSVec.entry_univ`; `HandoffExclusion.exclusion_theorem`, `HandoffExclusion.exclusion_round`, `HandoffMain.exclusion_canon`, `HandoffXMain.exclusion_canonX` |
| 31 | `EndFactTriggerTest` | item 39: THE TRIGGER OF AN END FACT (§4.9; `analyzer-core.md` §4.5, §7.3; `ap.md` §9.2; a regression of the review of F70), through `IterationDriver` with `FixedLimits(listOf(1, 2, 3))`. PROGRAM END (§9.1): `root(){ x = source(); r = M(x); sinkAny(r); }`, `M(p){ y = sinkCall(p); w = wrap(y); return w; }`; `sinkCall` is the sink `ContainsMark(arg0, T)` with the end-fact action `AssignMark(U, Result)` (V1; `ToyMethod.sinkEnd`), `w = wrap(y)` the may `y.$ (U) → w.[any] (U)` (`ToyMethod.anyEdge` with `source = false`), `sinkAny` the sink `ContainsMarkOnAnyField(arg0, U)` (V2, real: `r` holds `y`, and `y` carries `U`). Run 1: V1 CONFIRMED; the end fact `zero → (y, ., $, U)`; `zero → (ret, ., [any], U)` in the demand layer, a demand edge of `M`; V2 DEMAND; the hand-off seeds V2 only. Backward run 2: the seed `(r, ., [any], U)` enters `M` by that demand edge; the reversed may gives `(y, ., [any], U)` (demand); the reversed end-fact edge of `sinkCall` applies to it, gives the zero fact AND fires the seed `(p, ., $, T)` of the `sinkCall` alternative at the sink statement of `M` (`triggerSeeds` of `M` is 1: one positive literal, once per statement and alternative; `SeedIndex.at` has no seed there); the backward summary `(ret, ., [any], U) → zero` is demand, so the hand-off gives `M` the pattern `(zero, (ret, ., [any], U))` (case 3) and, from the trigger seed, `((p, ., $, T), none)` (case 2); the requirement reaches `x`, and `source()` is a source hit. Forward run 3: the source seed fires, `sinkCall` triggers again (V1 stays CONFIRMED), the end fact is made, `M` publishes `zero → (ret, ., [any], U)` through `(zero, (ret, ., [any], U))`, and run 3 reports V2 (DEMAND: the may). Before the trigger, run 3 did not report V2, the report had no DEMAND entry, and the analysis ended with `STOP_RULE` and the real V2 lost. The variants of the review give the same results: the end-fact target `Result.a.b` cut at `L = 1` with an `[any]` sink pattern for V2 (no may); V1 confirmed in one context of `M` and its end fact needed in another | — (argued: the model has no end facts, `ap.md` §11.2) |
| 32 | `ConjunctionReversalTest` | item 40: THE REVERSAL OF A CONJUNCTION (§4.3; `ap.md` §9.1, §9.2; `interpreter.md` §4.9 STATEMENTS; a regression of the review of F70, a false positive that existed before F70), through `IterationDriver` with `FixedLimits(listOf(1, 2, 3))`. PROGRAM CONJ (§9.1): `root(){ a = srcT1(); b = srcT2(); r1 = M(a, b); y.f.g = r1; sinkT(y.f.g); r2 = M(a, c); sinkT(r2); }`, `M(p1, p2){ ret = lib(p1, p2); return ret; }`; `lib` is the conjunctive source `ContainsMark(arg0, T1) ∧ ContainsMark(arg1, T2) → Result.$ (T)` (an ND source, `ToyMethod.conjSource`); `c` carries no `T2`. Run 1: the ND summary `{(p1, [], $, T1), (p2, [], $, T2)} → (ret, ., $, T)` (never a record); V1 (`sinkT(y.f.g)`) is DEMAND by the cut at `L = 1`; V2 (`sinkT(r2)`) is not reported. Backward run 2: the reversed literals give `(ret, ., $, T) → (p1, ., $, T1)` and `(ret, ., $, T) → (p2, ., $, T2)` in the DEMAND layer (`MicroEdge.may`, §4.3), so `persist` adds no backward record of `M`, and the hand-off gives `M` the two case-3 patterns `((p1, ., $, T1), (ret, ., $, T))` and `((p2, ., $, T2), (ret, ., $, T))`; both sources of the root are hits. Forward run 3: `M` is in `analysed` with both members, call 1 CONFIRMS V1, call 2 gives no result, and V2 is not reported. Before the fix both backward summaries were normal and crossable (`Handoff.CrossB`), forward run 3 crossed call 2 by the one-literal record `(p1, ., $, T1) → (ret, ., $, T)`, and V2 was a false CONFIRMED. A conjunctive exit source with two positive literals (`ToyMethod.exitSource` with two conditions, §4.4) gives the same demand-layer reversal | — (argued: the model has no restricted run with ND edges, `ap.md` §11.2) |
| 33 | `MarkRestrictionTest` | item 41: THE MARK-AWARE RESTRICTION (`ap-history.md` F71; `analyzer-core.md` §4.6; `ap.md` §6.4; §4.7 `restrictBy`), an engine test through a `RunMethodAnalyzer` over a `ToyInterpreter`, with the demand and the records WRITTEN BY HAND (as row 25). PROGRAM MARK (§9.1): a restricted forward `RunConfig` (run 3), the toy method `m(x){ ret.f = x; }` (`write("ret", "f", "x")`, as `wrap` of WRAP) and its caller `root(){ a = src(); r = m(a); }` (`src` with the target `$` and the mark `T`, a source seed). THE USER'S EXAMPLE: the demand of `m` is the one pattern `D-c = (x, ., $, T)`, `D-p = (ret, .f, $, U)`. The emission gives the premise `(x, ., $, T)`, and `summaries.all()` holds the delta `(x, ., $, T) → (ret, .f, $, T)` (item 1 of §4.7: no restriction). The premise lies inside `D-c`, but the mark `T` of the leaf does not meet the mark `U` of `D-p`, so `restrictBy` gives nothing: no `Publication` in `pending` and in the `SummaryStorage` of `m`, and `root` gets no fact on `r`. With `D-p = (ret, .f, $, T)`: one publication `(x, ., $, T) → (ret, .f, $, T)`, and `root` gets `(r, .f, $, T)`. THE PREMISE MARK: a second pattern `((x, ., $, U), (ret, .f, $, T))` of `m` next to the first one (with `D-p = (ret, .f, $, U)`): it emits nothing for the added fact `(x, ., $, T)` (§4.2 `emit`), and `covering` returns it for the premise `(x, ., $, T)` (the query reads the locations only), but the premise is not inside it in its marks, so it gives no publication too; `m` publishes nothing. THE DEMAND EDGES: the leaf of the user's example is CROSSABLE (normal, a `$` premise, a `$` leaf, mark-reversible), so `demandPart` keeps none of it with either `D-p`: `summaries.demandEdges()` is empty, `persist` keeps the record, and `Frontier.demandEdges` has no entry of `m` (§10 row 12). So the mark test on the demand edges is read on a DEMAND-LAYER variant: `m(x){ ret.f.g = x; }` (`writePath("ret", listOf("f", "g"), "x")`) with the field limit 1 gives the leaf `(ret, .f, [any], T)` in the demand layer (the cut); against `D-p = (ret, .f, $, U)` no publication and no demand edge; against `D-p = (ret, .f, $, T)` the publication `(x, ., $, T) → (ret, .f, $, T)` in the demand layer (the meet `[any] ∩ $ = $`), which `summaries.addDemand` stores, and `HandOff.of` gives `m` the backward pattern `((ret, .f, $, T), (x, ., $, T))` (`Frontier.demandEdges[m] = 1`). THE STUB (the CEGAR of the location form of C5): with a stub `ApOps` whose `restrict` reads `D-c` and `D-p` as locations only (the test before F71), the user's example publishes the leaf through both patterns (one publication) and the demand-layer variant stores a demand edge with `D-p = (ret, .f, $, U)`. `NaiveClosure` (the reference `restrict`, §9.2) gives the same publications and demand edges as the engine. THE `*∖X` CELLS of the restriction, the abstract conclusion mark, a tree with leaves of several marks and the X form are AP-level tests (`ap-impl.md` Part I §8 test 17): no restricted run has an abstract conclusion mark, and no spec run has a `*∖X` exit pattern (`ap.md` §6.4) | `Handoff.RVec.vMark_user_inside`, `Handoff.RVec.vMark_user_concMark`, `Handoff.RVec.vMark_user_restrictI`, `Handoff.RVec.vMark_user_loc`, `Handoff.RVec.vMark_user_restrictU`, `Handoff.RVec.vMark_user_same`, `Handoff.RVec.vMark_prem_loc`, `Handoff.RVec.vMark_prem_inside`, `Handoff.RVec.vMark_prem_restrictI`; `Handoff.restrictI_contract`, `Handoff.restrictI_contract_loc_false`, `Handoff.RAux.concMarkB_of_den`; AP level: `Handoff.RVec.vMark_inStarEx_T`, `Handoff.RVec.vMark_inStarEx_U`, `Handoff.RVec.vMark_outStarEx_T`, `Handoff.RVec.vMark_outStarEx_U`, `Handoff.RVec.inter_exc_absmark`, `HandoffX.XVec.vM_user`, `HandoffX.XVec.vM_prem`, `HandoffX.XVec.vM_inStarEx`, `HandoffX.XVec.vM_outStarEx`, `HandoffX.XVec.restrictIX_contract_loc_false` |
| 34 | `StarExEmissionTest` | item 42: THE `*∖X` EMISSION (`ap-history.md` F71; `analyzer-core.md` §4.4; `ap.md` §6.3; §4.2 `emit`), an engine test through a `RunMethodAnalyzer` over a `ToyInterpreter`, with the demand, the records and the seeds WRITTEN BY HAND. PROGRAM STAREX (§9.1): a backward `RunConfig` (run 2), the toy method `m(x){ ret = x; }` and its caller `root(){ r = m(a); sinkT(r); sinkU(r); }` (two call sinks with the marks `T` and `U`), the sink seeds `(r, ., $, T)` and `(r, ., $, U)` of the two sinks, and the one demand pattern of `m` `D-c = (ret, ., $, *∖{T})`, `D-p = (x, ., *, *)` (in a real run a backward entry pattern with the mark `*∖X` comes from a run-1 summary conclusion after a cleaner, §7.2, and `D-p` is a run-1 premise, the policy fact). The two requirements reach the forward exit of `m` as the added facts `(ret, ., $, T)` and `(ret, ., $, U)`, and `DemandStore.near` returns the pattern for both (it reads the locations only). `initials` of `m` holds `(ret, ., $, U)` and the zero fact (rule `zin`), and NOT `(ret, ., $, T)`: the summary of `D-c` does not pass `T`, so a requirement with the mark `T` cannot come from it. The backward summary `(ret, ., $, U) → (x, ., $, U)` of `m` is published (the mark `U` lies in `*∖{T}`, and it meets the mark `*` of `D-p`), and `root` gets the requirement `(a, ., $, U)` only. THE STUBS: with a stub `ApOps` whose `emit` reads `*∖X` as `*` (the cell before F71, Lean `Handoff.RVec.markMatchB70`), `initials` of `m` also holds `(ret, ., $, T)`, but the restriction still gives no publication for its summary `(ret, ., $, T) → (x, ., $, T)` (the premise is not inside `D-c` in its marks, §4.7), so `root` gets no `(a, ., $, T)`; only with a stub that has both tests before F71 (also `restrict` in the locations only) does `root` get `(a, ., $, T)`. So each of the two mark tests blocks the mark `T` alone. `NaiveClosure` (the reference `emit`, §9.2) gives the same initial facts as the engine | `Handoff.RVec.vEmit_starEx_T`, `Handoff.RVec.vEmit_starEx_T_pre70` (`Handoff.RVec.emitM70`), `Handoff.RVec.vEmit_starEx_U`, `Handoff.emitM_insideB`, `RCore.emitM_contract`, `RCore.emitM_contract_I` (the `*∖X` cell of `markMatchB`); AP level (`ap-impl.md` Part I §8 test 17): `HandoffX.XVec.vM_emit`, `Handoff.RVec.vEmit_abstract` |

### 9.2 The schedule fuzzer

The fuzzer runs the production analyzer, `SubscriptionManager` and `SummaryStorage` on one thread. Each method is its
own unit. One pool holds every event, every `Work`, every deferred replay and every deferred notification. The next
action is a random member of the pool. So every interleaving of the model `Step` (`analyzer-core.md` §5.5) can occur.
The direct calls are events too: `link` always sends `LinkIn`, and `ProtocolSteps` defers the replay and the
notification.

```kotlin
/** analyzer-core.md §13 item 1. Deterministic for a seed. */
class FuzzRun(private val config: RunConfig, private val shared: SharedObjects, seed: Long,
              private val maxQuantum: Int = 4) : ProtocolSteps {
    private val random = Random(seed)
    private val pool = ArrayList<() -> Unit>()
    private val ports = HashMap<MethodKey, Port>()
    private val storages = HashMap<MethodKey, SummaryStorage>()
    private val forms = shared.contexts.directed(config.direction)
    /** What the engine PROCESSED (RunnerPort.onProcess), not what it stored: the unchanged path stores nothing (§4.3). */
    private val processed = LinkedHashSet<Pair<MethodKey, EdgeDelta>>()

    override fun replay(step: () -> Unit) { pool += step }        // the model step `replay`; P1 holds already
    override fun notify(step: () -> Unit) { pool += step }        // the model step `notify`; P2 holds already

    fun run(): FuzzResult {
        config.roots.forEach { post(RunEvent.Start(it)) }
        while (pool.isNotEmpty()) {                               // quiescence: the pool is empty
            val k = random.nextInt(pool.size)
            val action = pool[k]
            pool[k] = pool[pool.lastIndex]; pool.removeAt(pool.lastIndex)
            action()
        }
        val analyzers = ports.values.map { it.analyzer.also(RunMethodAnalyzer::freeze) }
        return FuzzResult.of(processed, analyzers, shared, config)   // runs Support (§7.5) on a RunResult of the analyzers
    }

    private fun port(key: MethodKey) = ports.getOrPut(key) { Port(key) }
    private fun post(e: RunEvent) { val p = port(e.target()); pool += { p.handle(e) } }

    private inner class Port(val key: MethodKey) : RunnerPort {
        val analyzer: RunMethodAnalyzer by lazy { RunMethodAnalyzer(key, this) }
        override val config get() = this@FuzzRun.config
        override val shared get() = this@FuzzRun.shared
        override val forms get() = this@FuzzRun.forms
        override val ops get() = shared.ops
        override val steps: ProtocolSteps get() = this@FuzzRun
        override val subscriptions = SubscriptionManager(this)
        override val onProcess: (MethodKey, EdgeDelta) -> Unit = { m, d -> processed += m to d }
        override fun send(event: RunEvent) = post(event)
        override fun post(event: RunEvent.Delivery) { pool += { handle(event) } }
        override fun enqueue(analyzer: RunMethodAnalyzer) { pool += { work(analyzer) } }
        private fun work(a: RunMethodAnalyzer) { if (!a.work(1 + random.nextInt(maxQuantum))) pool += { work(a) } }   // W2
        override fun analyzer(key: MethodKey) = port(key).analyzer.also { check(key == this.key) }
        override fun applier(caller: MethodKey): SummaryApplier = analyzer(caller)
        override fun subscribe(sub: Subscription) = subscriptions.subscribe(sub)
        override fun summaryStorage(key: MethodKey) =
            storages.getOrPut(key) { SummaryStorage(key, shared.ap, shared.ops, this@FuzzRun) }
        override fun link(callee: MethodKey, ref: CallerRef, linkLayer: Layer, added: Facts) =
            post(RunEvent.LinkIn(callee, ref, linkLayer, added))  // the direct call 2 as an event
    }
}
```

The reference is `NaiveClosure` (DD10). It is the closure that the engine computes in one run: Lean `D` with `DS`
and `DN` (run 1), `DR` (a restricted forward run), `Backward.DB` (a backward run); with the tail `[any-taint]` and its
exclusion, run 1 is `AnyTaintEx.D6X` and a restricted forward run `AnyTaintEx.DRX` with the spec rules
`AnyTaintEx.emitX`, `AnyTaintEx.satX` and `HandoffX.restrictIX` (`ap.md` §10.11, §10.12; `AnyTaintEx.DRXs` is the
instance with the earlier restriction, the record of the earlier design); the backward run stays `Backward.DB` (it
has no `[any-taint]`). Two rules of the review of F70 are in the closure and not in a Lean closure (argued): the
trigger of an end fact (`boundary`; at a call the hook `PlanHooks.trigger`, `ap-impl.md` §23.8) and the demand layer
of a reversed conjunction literal (`MicroEdge.conjunctive`, which `MicroEdge.may` and so `ReferenceAlgebra` read). The reference forms carry the tail and exclusion rules (`concat`,
`normalize`, `emit`, `startFact`, `inside`, `restrict`, `markCheck`, `cleanRes`, `limit`, `recordDemand`) and the mark
tests of `emit` and `restrict` (F71: `markSub`, `insideDemand`, `marksMeet`), and
`ReferenceAlgebra` reads `MicroEdge.may` as the engine does (§4.3; `ap-impl.md` §23.8), so the closure adds only the record demotion, the R3 filter of the reversal and the support link (below). It
works per path, on the reference
forms (`ap-impl.md` §6). It applies the forms with `FormApplier` over `ReferenceAlgebra` (`ap-impl.md` §23.3, §23.8), so the oracle
and the engine share the mode logic and differ only in the fact algebra (DD12). It has no tree, no edge store, no
subscription index, no thread and no subsumption. It reads the demand and the records of its `RunConfig` through their
lookups (`DemandStore.near`, `RecordStore.byEntry`, `byExit`; their completeness is a test of `ap-impl.md` §8) and
tests each candidate itself. Since F70 it also gives THE DEMAND EDGES of the run per path (`demandEdges`, from the
reference forms `cross`, `crossReversed` and `restrict`), and the fuzzer compares them with
`RunSummaryStore.demandEdges()` of the engine (`summaryDelta`, §4.7; `ApOps.demandPart`, `ap-impl.md` §5.9).

At a call it runs the one per-path plan walk `FormsReference.run` (`ap-impl.md` §23.8) with the guards of the engine
(`PlanHooks`): the closure writes no plan walk and no `Origin` rule of its own. It is test-only
(`TEST/bidi/engine/NaiveClosure.kt`). Each rule body follows the rule of the engine that its comment names. Every form
applies at the `Place` of the engine: a statement and the rule statements of a boundary at
`Place(node, run1, sources = true)` (so in run 1 the static exception of `ap.md` §4.10 item 1 acts at the entry and exit
rule statements, as in `RuleWorklist.input`, §4.4), a stage by its kind (`FormsReference.run`).

The program, the results and the comparison (test-only):

```kotlin
/** TEST/bidi/engine/ToyPrograms.kt. One test program. Its ToyInterpreter gives the SAME forms to the engine (as
 *  Interpreter and MethodContextSource, through `shared()`) and to NaiveClosure (`directedForms`). */
interface ToyProgram {
    val ap: ApManager
    val interpreter: ToyInterpreter
    fun directedForms(direction: Direction): DirectedForms = DirectedForms(interpreter, direction, interpreter::forms)
    fun callAt(node: CommonInst): CommonCallExpr?                                          // as LanguageManager.getCallExpr
    fun successors(m: MethodKey, node: CommonInst, direction: Direction): List<CommonInst> // the graph of the run (wired backward)
    /** Run 1, a restricted forward run, a backward run. The demand, the seeds and the records of runs 2 and 3 are written
     *  by hand (not by HandOff), so the oracle does not depend on the hand-off: programs 1 and 2 from the Lean
     *  `Backward.dem1_exact`, `dem2_exact` (the hand-off before F70: any demand is a valid input of one run); WRAP and the
     *  getter from `HandoffCases.Wrap.handF_w1_exact`, `HandoffCases.Wrap.demN_exact`,
     *  `HandoffCases.Getter.handF_g1_exact`, `HandoffCases.Getter.demG_exact` (F70); MARK and STAREX from the demand of
     *  §9.1 rows 33, 34 (F71). HandOffTest checks HandOff against the F70 values (§9.1 rows 19, 29). */
    fun runs(): List<RunConfig>
    /** New stores on each call (a ConcurrentVulnerabilityStore, a PersistentRecordStore); the engine reads the records of
     *  a run from its RunConfig. */
    fun shared(): SharedObjects
}

/** The forms of the toy programs (ap-impl.md §23) from the DSL of §9.1. `forms(key)` gives the CACHED MethodForms of the
 *  key: the same SinkRule and ConjunctiveEdge objects on every call (§9.1; the identity keys of ap-impl.md §31.2). */
interface ToyInterpreter : Interpreter, MethodContextSource

/** TEST/bidi/engine/ToyPrograms.kt: the DSL of §9.1, one builder per method. Each call adds one statement (in order; the
 *  next statement is the successor) and makes its forward forms ONCE with the language-neutral builders of ap-impl.md:
 *  MicroEdgeBuilder (ap-impl.md §24) for a statement summary and a rule statement, the CallStage and CallPlan
 *  constructors (ap-impl.md §23.5, §23.6) for a call, SinkRule, RuleStatement and ExitRules (ap-impl.md §23.4) for a
 *  sink and the exit rules. The backward forms
 *  are their `reversed()`, made once too. ToyInterpreter keeps them per method key (above). */
interface ToyMethod {
    val name: String
    fun assign(to: String, from: String?)                                     // `x = y`; null: the kill (MicroEdgeBuilder.move)
    fun read(to: String, base: String, field: String)                         // `x = y.f` (read)
    fun write(base: String, field: String, value: String, weak: Boolean = false)   // `x.f = y` (write)
    fun writePath(base: String, fields: List<String>, value: String)          // `x.f.g = y` as ONE strong write (strongKeep):
                                                                              // toy only, the JVM has none (programs X, CUT1)
    fun call(callee: String, args: List<String>, result: String? = null)      // the bindings and the callees stage
    fun native(callee: String)                                                // a callee with no body: an unresolved call
    fun source(to: String, mark: String)                                      // a read source (a source-seed place)
    fun sourceAny(to: String, mark: String)                                   // a read source with an `[any]` target: `to.[any-taint] (T)` (ap.md S15)
    fun anyEdge(from: String, to: String, mark: String, source: Boolean)      // `from.$ (T) → to.[any] (T)`: a conditional source
                                                                              // (target `[any-taint]`) or a pass rule (target `[any]`); program P
    fun anyTaint(to: String, from: String)                                    // `(from, ., *) → (to, ., [any-taint])`, the mark kept:
                                                                              // toy only (ANYW, ANYM of HandoffCases, §9.1 row 29)
    fun sink(mark: String, vararg values: String)                             // a call sink; two values: a conjunctive sink
    fun sinkEnd(mark: String, value: String, endTo: String, endMark: String)  // a call sink with the end-fact action
                                                                              // `AssignMark(endMark, endTo)` (program END)
    fun sinkAny(mark: String, value: String)                                  // a call sink `ContainsMarkOnAnyField`: the pattern `[any]`
    fun conjSource(to: String, mark: String, vararg cond: Pair<String, String>)   // a call source with two or more condition
                                                                              // literals (value, mark): an ND source (program CONJ)
    fun cleaner(value: String, mark: String, reach: CleanReach = CleanReach.EXACT)   // a cleaner action of the next call;
                                                                              // named field `x.f`: fieldCleanStep (F74), every reach
    fun throws(value: String)                                                 // `throw v`: the exceptional exit
    fun exitSource(exceptional: Boolean, to: String, mark: String, vararg cond: Pair<String, String>)   // cond: (value, mark)
    fun exitSink(exceptional: Boolean, vararg literals: Pair<String, String>, globalStateDrop: Boolean = false)
}

/** THE ONE PER-PATH KEY of the comparison: (method, node, premise set as patterns). A summary has no node. */
data class PathKey(val method: MethodKey, val node: CommonInst?, val premise: Set<Pattern>)
typealias PerPath = Map<PathKey, List<Conclusion>>

/** `this` dominates `b`: every conclusion of `b` at a key has a conclusion of `this` at the same key that subsumes it
 *  (`subsumes`, Reference.kt; ap.md §8.1). edges.add drops a dominated conclusion, so two schedules can process
 *  different but equivalent items (Pipeline.quiescent_dominates). */
fun PerPath.dominates(b: PerPath): Boolean =
    b.all { (k, ns) -> val ss = this[k].orEmpty(); ns.all { n -> ss.any { s -> subsumes(s, n) } } }

class ClosureResult(val facts: PerPath, val summaries: PerPath, val demandEdges: PerPath,
                    val vulnerabilityKeys: Set<VulnerabilityKey>, val confirmed: Set<VulnerabilityKey>,
                    val hits: Set<Triple<MethodKey, CommonInst, PathEdge>>)

class FuzzResult(val processed: PerPath, val summaries: PerPath, val demandEdges: PerPath,
                 val vulnerabilityKeys: Set<VulnerabilityKey>, val confirmed: Set<VulnerabilityKey>,
                 val hits: Set<Triple<MethodKey, CommonInst, PathEdge>>) {
    companion object {
        /** The conversions of the engine state: a premise key → its members as patterns; a Facts → its leaves
         *  (FormsReference.conclusions, per layer); the run summary stores → `summaries`; SourceHitStore → the hits.
         *  Support (§7.5) on a COMPLETE RunResult of the analyzers marks the witnesses (forward). */
        fun of(processed: Collection<Pair<MethodKey, EdgeDelta>>, analyzers: List<RunMethodAnalyzer>, shared: SharedObjects,
               config: RunConfig): FuzzResult {
            val view = FormsReference(shared.ops)
            fun premise(k: PremiseKey) = k.members.mapTo(LinkedHashSet()) { it.toPattern() }
            fun perPath(xs: List<Pair<PathKey, Facts>>): PerPath =
                xs.groupBy({ it.first }, { view.conclusions(it.second) }).mapValues { (_, cs) -> cs.flatten().distinct() }
            val facts = perPath(processed.map { (m, d) -> PathKey(m, d.node, premise(d.premise)) to d.facts })
            val summaries = perPath(analyzers.flatMap { a ->
                a.summaries.all().map { (p, g) -> PathKey(a.key, null, premise(p)) to g }.toList() })
            val demandEdges = perPath(analyzers.flatMap { a ->                     // F70: what the hand-off reads (§7.2)
                a.summaries.demandEdges().map { (p, g) -> PathKey(a.key, null, premise(p)) to g }.toList() })
            val result = RunResult(RunStatus.COMPLETE, analyzers, config.index, config.direction, shared.vulnerabilities)
            if (config.direction == Direction.FORWARD) Support(result, config.roots, shared).confirm()
            val byKey = result.witnessesByKey()
            val hits = analyzers.flatMapTo(HashSet()) { it.sourceHits?.entries().orEmpty().asIterable() }
            return FuzzResult(facts, summaries, demandEdges, byKey.keys,
                byKey.filterValues { ws -> ws.any { it.confirmed } }.keys, hits)
        }
    }
}
```

The closure:

```kotlin
/** One input of a literal in the naive join: (premise set, demand bit). */
private typealias JoinInput = Pair<Set<Pattern>, Boolean>

class NaiveClosure(private val program: ToyProgram, private val config: RunConfig, private val ap: ApManager) {
    data class PFact(val method: MethodKey, val premise: Set<Pattern>, val node: CommonInst, val c: Conclusion)   // BEFORE node
    data class PLink(val callee: MethodKey, val added: Conclusion, val caller: PFact)     // caller: the caller edge at the call
    data class PSummary(val method: MethodKey, val premise: Set<Pattern>, val g: Conclusion)
    data class PRequest(val method: MethodKey, val premise: Pattern, val kind: RequestKind)
    /** A witness: the key with no context, the alternative and the method key of the witness (§4.9). */
    data class PVuln(val key: VulnerabilityKey, val alternative: Int, val methodKey: MethodKey, val premise: Set<Pattern>,
                     val demand: Boolean)

    val facts = LinkedHashSet<PFact>(); val links = LinkedHashSet<PLink>(); val summaries = LinkedHashSet<PSummary>()
    val zeroSubs = LinkedHashSet<Pair<MethodKey, PFact>>()          // DB: (callee, the caller edge {zero} -> zero at the call)
    val initials = LinkedHashSet<Pair<MethodKey, Pattern>>(); val requests = LinkedHashSet<PRequest>()
    val vulnerabilities = LinkedHashSet<PVuln>(); val hits = LinkedHashSet<Triple<MethodKey, CommonInst, PathEdge>>()
    private val forms = program.directedForms(config.direction)     // the same forms as the engine (ToyInterpreter)
    private val zero = ap.zero.toPattern()
    private val forward = config.direction == Direction.FORWARD
    private val ops = ApOps(ap)
    private val refs = HashMap<MethodKey, FormsReference>()
    /** ap-impl.md §23.8: one FormsReference per method over a ReferenceAlgebra (one Conclusion per fact, a premise SET of
     *  patterns). Its `applier` gives the three modes, its `run` the plan walk. The hooks give the rules of the closure.
     *  ReferenceAlgebra raises only reqStmt and sreqStmt (its `request`); reqConj is raised once, by `conj`. */
    private fun ref(m: MethodKey) = refs.getOrPut(m) {
        FormsReference(ops, ReferenceAlgebra(config.mode,
            request = { premise, kind -> requests += PRequest(m, premise.single(), kind) },            // reqStmt, sreqStmt
            allowsSource = { node, me -> !config.seededSources || config.seeds.allowsSource(m, node, me.forward) },
            sourceHit = { node, me -> hits += Triple(m, node, me.forward) },                           // srcHit
            manager = ap,
            conjunction = { cj, premise, c, node, out -> conj(m, cj, premise, c, node, out) }))       // conj, reqConj
    }
    private fun applier(m: MethodKey) = ref(m).applier
    private fun Conclusion.p() = Pattern(fact, exclusion)
    private fun zeroIn(layer: Layer) = Conclusion(zero.fact, ExclusionSet.Empty, demand = layer == Layer.DEMAND)

    /** ap.md §4.6: the union of premise sets WITHOUT the zero fact; `{zero}` only if every input is `{zero}`. Users: conj,
     *  fireSinks, ndRet (publish). */
    private fun union(sets: List<Set<Pattern>>): Set<Pattern> =
        sets.flatMapTo(LinkedHashSet()) { it }.apply { remove(zero) }.ifEmpty { setOf(zero) }

    /** The stored inputs of each literal (ap.md §8.9): of a conjunctive edge per (method, edge, node); of a conjunctive
     *  sink per (alternative, node). */
    private val conjInputs = HashMap<Triple<MethodKey, ConjunctiveEdge, CommonInst>, Array<LinkedHashSet<JoinInput>>>()
    private val sinkInputs = HashMap<Pair<SinkRule, CommonInst>, Array<LinkedHashSet<JoinInput>>>()

    /** The naive k-ary join (Lean ND.conj; `Store.standing_complete`): `input` goes into slot k of `key`; a NEW input gives
     *  every combination with the stored inputs of the other slots. Users: conj, fireSinks. */
    private fun <K> join(store: HashMap<K, Array<LinkedHashSet<JoinInput>>>, key: K, arity: Int, k: Int,
                         input: JoinInput): List<List<JoinInput>> {
        val slots = store.getOrPut(key) { Array(arity) { LinkedHashSet() } }
        if (!slots[k].add(input)) return emptyList()
        return product(List(arity) { j -> if (j == k) listOf(input) else slots[j].toList() })
    }
    private fun <T> product(xs: List<List<T>>): List<List<T>> =
        xs.fold(listOf(emptyList())) { acc, x -> acc.flatMap { p -> x.map { p + it } } }

    /** conj (ap.md §4.6; Lean ND.conj): a fact on which `markCheck` (Reference.kt) gives Holds is one input of the literal,
     *  with the demand bit `conjDemand` (a normal `[any-taint]` input that overlaps its literal is normal, Lean
     *  AnyTaintND.conjLayerT; `markCheck` reads the exclusion of `c`, AnyTaintEx.checkX); a NEW input meets every stored
     *  combination of the other literals (`join`); the
     *  result is the target with the `union` of the premise sets (no zero member), demand if one input is demand,
     *  normalized (ap.md W6, W8: a demand `[any-taint]` target is `[any]`). On Request: reqConj (run 1), on the one
     *  premise of the `*` fact. */
    private fun conj(m: MethodKey, cj: ConjunctiveEdge, premise: Set<Pattern>, c: Conclusion, node: CommonInst,
                     out: ReferenceSink) {
        for ((k, lit) in cj.literals.withIndex()) {
            if (lit.fact.base != c.fact.base) continue
            when (val r = markCheck(premise.first(), c, lit)) {             // the premise is read only on a request
                CheckResult.None -> continue
                is CheckResult.Request -> { requests += PRequest(m, premise.single(), RequestKind.Mark(r.mark)); continue }
                CheckResult.Holds -> Unit
            }
            for (comb in join(conjInputs, Triple(m, cj, node), cj.literals.size, k, premise to conjDemand(c, lit)))
                out(union(comb.map { it.first }), normalize(cj.target, ExclusionSet.Empty, demand = comb.any { it.second }))
        }
    }

    fun run(): ClosureResult {
        for (r in config.roots) addInitial(r, zero)                  // root
        do {
            val before = size()
            for (f in facts.toList()) step(f)
            for (l in links.toList()) { linkRules(l); retRec(l) }
            for (q in requests.toList()) for (l in links.toList()) if (l.callee == q.method) requestRule(q, l)   // E2, E5
            for (s in summaries.toList()) publish(s)
            for (z in zeroSubs.toList()) zret(z)
        } while (size() != before)
        return ClosureResult(
            facts = facts.groupBy({ PathKey(it.method, it.node, it.premise) }, { it.c }),
            summaries = summaries.groupBy({ PathKey(it.method, null, it.premise) }, { it.g }),
            demandEdges = demandEdges(),
            vulnerabilityKeys = vulnerabilities.mapTo(HashSet()) { it.key },
            confirmed = naiveSupport(), hits = hits)
    }

    /** F70 (Lean Handoff.handF, Handoff.demOfN; ap-impl.md §6 `cross`, `crossReversed`): THE DEMAND EDGES of the run per
     *  path, the reference of `RunSummaryStore.demandEdges()` (§4.7 `summaryDelta`). A summary leaf that is crossable
     *  gives nothing; every other leaf gives its publications (run 1 and a backward {zero} summary: the leaf; else
     *  `restricted`). A summary with several premises and a backward zero-premise summary are never crossable (R1). */
    private fun demandEdges(): PerPath = summaries.flatMap { s ->
        val j = s.premise.singleOrNull()
        val crossable = j != null && !(!forward && j == zero) && (if (forward) cross(j, s.g) else crossReversed(j, s.g))
        val pieces = when {
            crossable -> emptyList()
            config.run1 || (!forward && j == zero) -> listOf(s.g)
            else -> restricted(s)
        }
        pieces.map { PathKey(s.method, null, s.premise) to it }
    }.groupBy({ it.first }, { it.second })

    /** The step of one fact before its node (§4.3; no liveness check): a call goes to zeroAtCall (the zero fact) or to the
     *  plan walk; another statement to `statement`. */
    private fun step(f: PFact) {
        val call = program.callAt(f.node)
        when {
            call == null -> statement(f)
            f.c.fact.base == AccessPathBase.Zero -> zeroAtCall(f, call)
            else -> walk(f, call, listOf(PlanItem(f.premise, f.c, null)))
        }
    }

    /** step, pass (runStatement, §4.3): the STATEMENT mode of FormApplier at the Place of the engine (conj, reqStmt,
     *  sreqStmt, srcHit and the source-seed filter come from ReferenceAlgebra and its hooks); each result is cut by
     *  `limit` (Cut.STATEMENT); an untouched input goes on as it is (the unchanged path). */
    private fun statement(f: PFact) =
        applier(f.method).statement(forms.statement(f.method, f.node), f.premise, f.c, Place(f.node, config.run1, sources = true),
            sink = { pr, x -> after(f.method, f.node, pr, limit(x, config.fieldLimit)) },
            untouched = { pr, x -> after(f.method, f.node, pr, x) })

    /** A fact after `node` (emitAfter, exitRulesAt, §4.3): the end rules at an end node, or, forward, the exit rules of an
     *  exceptional exit with no summary; then a PFact at each successor. */
    private fun after(m: MethodKey, node: CommonInst, premise: Set<Pattern>, c: Conclusion) {
        if (node in forms.endNodes(m)) end(m, node, premise, c, summary = true)
        else if (forward && forms.interp.exitNodes(m).any { it.node == node && it.exceptional }) end(m, node, premise, c, summary = false)
        for (s in program.successors(m, node, config.direction)) facts += PFact(m, premise, s, c)
    }

    /** The zero fact at a call (zeroAtCall, §4.10; DD7, Backward.lean:158-180). Forward (premise {zero} only): the walk from
     *  the entry gives zpass and the zero binding (the unconditional sinks, the sources, the callees). Backward: zpass for
     *  every premise; for {zero} ONLY also seed (the sink seeds, a walk from BOUND), zin (the zero fact of each resolved
     *  callee) and a zeroSubs entry per resolved callee (zret). */
    private fun zeroAtCall(f: PFact, call: CommonCallExpr) {
        val isZero = f.premise == setOf(zero)
        if (forward) { check(isZero); walk(f, call, listOf(PlanItem(f.premise, f.c, null))); return }
        after(f.method, f.node, f.premise, f.c)                                                 // zpass
        if (!isZero) return                                                                     // `jb -> zero` only passes
        val seeds = sinkSeeds(f.method, f.node).map { PlanItem(f.premise, it, null) }           // seed
        if (seeds.isNotEmpty()) walk(f, call, seeds, from = CallPoint.BOUND)
        for (m in forms.call(f.method, f.node, call).stages.filterIsInstance<CallStage.Callees>().flatMap { it.callees }) {
            addInitial(m, zero)                                                                 // zin
            zeroSubs += m to f                                                                  // zret
        }
    }

    /** ap.md §5.3 per path, with the guards of the engine: `FormsReference.run` (ap-impl.md §23.8) does the walk (the
     *  relevance, the zero fact passes over and enters, every stage in STAGE mode, `StageKind.originOf`, the END_FACTS
     *  and MemoryEffect guards, PASS_OVER backward, and backward the `trigger` of a reversed END_FACTS stage). The closure
     *  gives its rules as hooks. `from`: the entry; BOUND for a seed; the end point of the callees stage (RETURNED
     *  forward, ADDED backward) for a summary result (`resume`). Every item at the exit point is a fact after the call. */
    private fun walk(f: PFact, call: CommonCallExpr, items: List<PlanItem>, from: CallPoint? = null) {
        val plan = forms.call(f.method, f.node, call)
        val hooks = PlanHooks(
            guards = forward,                                                        // a reversed plan has no guard
            atBound = { xs -> fireSinks(f.method, f.node, plan.sinks, xs).sinks },   // vuln, reqSink; the fired sinks
            callees = { st, i ->                                                     // a PLink per callee; the results come
                for (m in st.callees) links += PLink(m, i.c, f.copy(premise = i.premise))   // by `publish`, `retRec` (resume)
                emptyList() },
            clean = { cl, i ->                                                       // cleanRes (Reference.kt); reqClean
                val o = cleanRes(cl, i.c)
                if (config.run1) o.request?.let { t -> requests += PRequest(f.method, i.premise.single(), RequestKind.Mark(t)) }
                o.facts.map { PlanItem(i.premise, it, i.origin) } },
            statementCut = { i -> i.copy(c = limit(i.c, config.fieldLimit)) },        // F74 read and write
            exit = { i -> i.copy(c = limit(i.c, config.fieldLimit)) },               // ap.md §4.4 rows 2, 3, 6
            trigger = { s -> trigger(f, s) })                                        // backward: THE TRIGGER OF AN END FACT
        val at = Place(f.node, statementEdge = false, sources = false)              // `run` sets both by the stage kind
        for ((p, i) in ref(f.method).run(plan, items, at, hooks, from ?: plan.entry))
            if (p == plan.exit) after(f.method, f.node, i.premise, i.c)
    }

    /** THE TRIGGER OF AN END FACT at a call (the `trigger` of a reversed END_FACTS stage, §4.5; the hook `PlanHooks.trigger`
     *  of `FormsReference.run`, ap-impl.md §23.8): the stage gave a result, so the seeds of its sink alternative `s` go on
     *  from BOUND, one zero-premise item per positive literal, once per (method key, statement, alternative), as `seed`. */
    private val triggered = HashSet<Triple<MethodKey, CommonInst, SinkRule>>()
    private fun trigger(f: PFact, s: SinkRule): List<PlanItem> =
        if (!triggered.add(Triple(f.method, f.node, s))) emptyList()
        else s.seedPatterns().map { PlanItem(setOf(zero), seedOf(it), null) }

    /** The sinks that triggered (with the layer of the sink edge or of the combination), and the EVALUATED facts. */
    private class Fired(val sinks: List<Pair<SinkRule, Layer>>, val evaluated: Set<Conclusion>) {
        companion object { val NONE = Fired(emptyList(), emptySet()) }
    }

    /** vuln, reqSink (checkSinks, §4.9; forward only): `markCheck` (Reference.kt) of each pattern of each sink on each
     *  item. A plain sink: a witness per item that a pattern holds on, in the layer of the item. A conjunctive sink: the
     *  item is the input of that literal (`join`, per alternative and node); a witness per new combination, with the
     *  `union` of the premise sets, demand if one input is demand. Every item that a pattern holds on is EVALUATED, also
     *  with no full combination (the global-state rule, `end` step 3). */
    private fun fireSinks(m: MethodKey, node: CommonInst, sinks: List<SinkRule>, items: List<PlanItem>): Fired {
        val fired = LinkedHashSet<Pair<SinkRule, Layer>>()
        val evaluated = HashSet<Conclusion>()
        for (i in items) for (s in sinks) for ((k, lit) in s.patterns.withIndex()) when (val r = markCheck(i.premise.first(), i.c, lit)) {
            CheckResult.None -> Unit
            is CheckResult.Request -> requests += PRequest(m, i.premise.single(), RequestKind.Mark(r.mark))     // reqSink
            CheckResult.Holds -> {
                evaluated += i.c
                val input: JoinInput = i.premise to i.c.demand
                for (comb in if (s.conjunctive) join(sinkInputs, s to node, s.patterns.size, k, input) else listOf(listOf(input))) {
                    val demand = comb.any { it.second }
                    vulnerabilities += PVuln(VulnerabilityKey(s.rule, m.method, node), s.alternative, m, union(comb.map { it.first }), demand)
                    fired += s to if (demand) Layer.DEMAND else Layer.NORMAL
                }
            }
        }
        return Fired(fired.toList(), evaluated)
    }

    /** THE RULE ORDER OF A BOUNDARY (RuleWorklist, §4.4), at the SAME Place: step 1 the rule summary in STATEMENT mode at
     *  Place(node, run1, sources = true); step 2 forward the sinks (`fireSinks`) and the end facts of each fired sink (GEN
     *  on the zero fact, in the layer of the trigger), backward the reversed end facts (GEN) per sink alternative, and
     *  THE TRIGGER OF AN END FACT: an alternative whose reversed end-fact edge gives a result fires its seeds, as step-1
     *  inputs with the premise {zero}. Every result is cut by `limit` and kept once (by value, DD4). Gives each item with
     *  its flag: a sink pattern held on it. */
    private fun boundary(m: MethodKey, rules: RuleStatement, node: CommonInst,
                         inputs: List<Pair<Set<Pattern>, Conclusion>>): List<Triple<Set<Pattern>, Conclusion, Boolean>> {
        val items = ArrayList<Pair<Set<Pattern>, Conclusion>>()
        val seen = HashSet<Pair<Set<Pattern>, Conclusion>>()
        val add: ReferenceSink = { pr, x -> val t = limit(x, config.fieldLimit); if (seen.add(pr to t)) items += pr to t }
        for ((pr, c) in inputs) applier(m).statement(rules.summary, pr, c, Place(node, config.run1, sources = true), add)   // 1
        val out = ArrayList<Triple<Set<Pattern>, Conclusion, Boolean>>()
        var k = 0
        while (k < items.size) {
            val (pr, c) = items[k++]
            val fired = if (forward) fireSinks(m, node, rules.sinks, listOf(PlanItem(pr, c, null))) else Fired.NONE   // 2
            for ((sink, layer) in fired.sinks) applier(m).gen(sink.endFacts, setOf(zero), zeroIn(layer), add)
            if (!forward) for (s in rules.sinks) {                                              // the reversed end facts,
                val rev = rules.endFacts.edges.filter { me -> s.endFacts.any { it.forward == me.forward } }   // per alternative
                var hit = false
                applier(m).gen(rev, pr, c) { p2, x -> hit = true; add(p2, x) }
                if (hit && triggered.add(Triple(m, node, s))) for (lit in s.seedPatterns())     // THE TRIGGER OF AN END FACT
                    applier(m).statement(rules.summary, setOf(zero), seedOf(lit), Place(node, config.run1, sources = true), add)
            }
            out += Triple(pr, c, c in fired.evaluated)
        }
        return out
    }

    /** The end rules (endAt, §4.7; DirectedForms.endRules, both directions): steps 1 and 2 by `boundary`; at a normal
     *  exit also 3 (an EVALUATED static of a {zero} item goes; a caller-set one stays, interpreter.md D30), 4 (every
     *  conclusion of a {zero} result on `this` or `arg(i)` with an entry mark goes: any path, `$` or `[any-taint]` with
     *  its exclusion, interpreter.md D35) and 5 (a PSummary if isSummaryBase). `summary = false`: a
     *  forward exceptional exit, steps 1 and 2 only. Backward: the reversed entry rules (their ExitRules have no step 3
     *  or 4). A conjunctive exit source joins in `conj`, as at a call (interpreter.md D31). */
    private fun end(m: MethodKey, node: CommonInst, premise: Set<Pattern>, c: Conclusion, summary: Boolean) {
        val er = forms.endRules(m, node)
        for ((pr, x, evaluated) in boundary(m, er.rules, node, listOf(premise to c))) {
            if (!summary) continue                                                              // the facts end there
            if (er.globalStateDrop && pr == setOf(zero) && x.fact.base == AccessPathBase.ClassStatic && evaluated) continue   // 3 (D30)
            val mk = x.fact.mark
            if (pr == setOf(zero) && mk is MarkSlot.Concrete &&
                er.entryMarkRemoval(x.fact.base)?.let { mk.mark in it } == true) continue        // 4: every leaf of the mark
            if (forms.interp.isSummaryBase(x.fact.base)) summaries += PSummary(m, pr, x)         // 5
        }
    }

    /** initA (run 1: the policy fact, `policy`, ap.md §6.2), initR (restricted: `emit` for each demand pattern of the
     *  callee near the added fact, ap.md §6.3); the zero fact for the zero added fact (the zero demand). E2 is the
     *  request loop of `run`. The tail of `a` names its layer on the link (W8: an any tail is `[any-taint]` on a normal
     *  link, `[any]` on a demand link), so `emit` keeps the tail of the added fact (the meet table of ap.md §6.3); `a`
     *  carries the exclusion `E` of an `[any-taint]/E` added fact, and `emit` reads it (Lean AnyTaintEx.emitX). The
     *  reference `emit` tests the mark of `a` against the mark of `D-c` with `markSub` (F71: a `*∖X` entry pattern does
     *  not admit a mark in `X`; Lean markMatchB, Handoff.RAux.markMatchB_conc), as `ops.emit` does (§4.2). */
    private fun linkRules(l: PLink) {
        val a = l.added.p()
        when {
            a.fact.base == AccessPathBase.Zero -> addInitial(l.callee, zero)
            config.run1 -> addInitial(l.callee, policy(a))
            else -> for (d in config.demand!!.near(l.callee, a.fact.base, ap.path(a.fact.path)))
                emit(d.entry, a)?.let { addInitial(l.callee, it) }
        }
    }

    /** Run 1 only (a restricted run has no request). The rows of ap.md §4.5 and §4.10 items 2 to 4 for one (request,
     *  link): answer and sanswer give a new initial fact (`answer`, Reference.kt); reqUp and sreqUp give a PRequest in the
     *  caller, on the one premise of the caller edge. */
    private fun requestRule(q: PRequest, l: PLink) {
        val a = l.added.p()
        val up = l.caller.premise.singleOrNull()
        when (val k = q.kind) {
            is RequestKind.Mark -> if (overlap(a, q.premise)) when (val am = a.fact.mark) {
                is MarkSlot.Concrete -> if (am.mark == k.mark) addInitial(q.method, answer(q.premise, a, k.mark))   // answer
                is MarkSlot.Star -> if (k.mark !in am.excluded) requests += PRequest(l.caller.method, up!!, k)        // reqUp
            }
            is RequestKind.Position -> {
                val p = k.path.toList()
                if (a.fact.base != AccessPathBase.ClassStatic) return
                if (a.fact.path.startsWith(p))                                                    // sanswer (item 2)
                    addInitial(q.method, Pattern(PathFact(AccessPathBase.ClassStatic, p, Tail.STAR, MarkSlot.STAR), ExclusionSet.Empty))
                else if (p.startsWith(a.fact.path) && up?.fact?.base == AccessPathBase.ClassStatic)
                    requests += PRequest(l.caller.method, up, k)                                  // sreqUp (item 3)
            }
        }
    }

    /** ret (applySummary, §4.6): a summary of the callee applies to each link whose added fact satisfies its premise
     *  (`satisfies`: run 1 `applicable`, restricted `inside`, the exclusions read; a must-premise occurs in a forward
     *  restricted run only, so it gets `inside`, and a demand `[any]` link gives a demand result); a restricted run first
     *  restricts it (`restricted`). ndRet
     *  (ndMatch, §4.11; ND.DN.ndBind): a premise set of k members needs one link per member at ONE call statement; the
     *  result premise is the `union` of the caller premise sets (no member is zero, so no zero link), demand if one
     *  application is demand. A backward {zero} summary goes to zret only. Each result goes on from the end point of the
     *  callees stage (`resume`) with its Origin (`origin`). */
    private fun publish(s: PSummary) {
        if (!forward && s.premise == setOf(zero)) return                                        // zret only
        val members = s.premise.toList()
        val gs = if (config.run1) listOf(s.g) else restricted(s)
        for (calls in links.filter { it.callee == s.method }.groupBy { it.caller.method to it.caller.node }.values) for (g in gs) {
            val choices = members.map { j -> calls.mapNotNull { l ->
                if (!satisfies(j, l.added.p(), config.restricted)) null else applyS(l.added, j, g)?.let { l to it } } }
            if (members.size == 1)
                for ((l, x) in choices[0]) resume(l.caller, PlanItem(l.caller.premise, x, origin(members[0], g)))      // ret
            else for (combo in product(choices))                                                                    // ndRet
                resume(combo[0].first.caller, PlanItem(union(combo.map { it.first.caller.premise }),
                    combo[0].second.copy(demand = combo.any { it.second.demand }), Origin.SUMMARY_EFFECT))
        }
    }

    /** ap.md §6.4 (restrict, §4.7): the conclusion restricted by every demand pattern near each member; each result once.
     *  The reference `restrict` is the intersection since F70, mark-aware since F71: the premise inside `D-c` in its
     *  locations and its marks (`insideDemand`: `insideLoc` and `markSub`), and the mark of the conclusion meets the mark
     *  of `D-p` (`marksMeet`; Lean Handoff.restrictI, HandoffX.restrictIX). `near` and `covering` read the locations
     *  only, so the wider query `near` gives the results of `covering` (ap-impl.md §7.7). */
    private fun restricted(s: PSummary): List<Conclusion> = s.premise.flatMap { j ->
        config.demand!!.near(s.method, j.fact.base, ap.path(j.fact.path)).mapNotNull { d -> restrict(j, s.g, d) }.toList()
    }.distinct()

    /** ap.md §4.3 per path: applySummary(a, j, g) = concat(a, j -> g, edgeDemand = the layer of g). A satisfied premise
     *  raises no request (Coverage.summary_step). */
    private fun applyS(a: Conclusion, j: Pattern, g: Conclusion): Conclusion? =
        (concat(a, summaryEdge(j, g), edgeDemand = g.demand,
            restricted = config.restricted) as? EdgeOutcome.Fact)?.conclusion

    /** The summary edge j -> g as one PathEdge (ap.md §4.1): the one exclusion of its `*` sides, and the own exclusions
     *  of its ANY_TAINT sides (a must-premise `[any-taint]/Ej`, a conclusion `[any-taint]/Et`, W8; Lean the `fex` and
     *  `tex` of AnyTaintEx.applySummaryX). */
    private fun summaryEdge(j: Pattern, g: Conclusion): PathEdge {
        val jOwn = j.fact.tail == Tail.ANY_TAINT
        val gOwn = g.fact.tail == Tail.ANY_TAINT
        return PathEdge(j.fact, g.fact,
            (if (jOwn) ExclusionSet.Empty else j.exclusion).union(if (gOwn) ExclusionSet.Empty else g.exclusion),
            fromExclusion = if (jOwn) j.exclusion else ExclusionSet.Empty,
            toExclusion = if (gOwn) g.exclusion else ExclusionSet.Empty)
    }

    /** THE ALIAS GUARD per path (summaryParts, §4.6): IDENTITY only for a NORMAL conclusion equal to the start fact of j;
     *  every other one, every DEMAND one and every one of a zero premise is SUMMARY_EFFECT. */
    private fun origin(j: Pattern, g: Conclusion) =
        if (j != zero && !g.demand && g == startFact(j)) Origin.IDENTITY else Origin.SUMMARY_EFFECT

    /** retRec (replayRecords, §5.3; ap.md §8.7 R2–R4): restricted runs only. A record of this direction applies when
     *  `applicable || inside`; a record of the other direction applies through `revEdge` of each conclusion leaf (R3; the
     *  new premise has the empty exclusion, ap.md §9.1). A record is not restricted. R3, LEAF BY LEAF (`reversibleLeaf`): no
     *  leaf of a MUST RECORD (an `[any-taint]` premise) and no `[any-taint]/E` leaf with `E ≠ {}` is reversed; every other
     *  leaf of the same record is; `$ -> [any-taint]` reverses to `[any] -> $` (`revEdge`). The reversed edge of a leaf is
     *  `revEdge` of its per-path summary edge (`summaryEdge`: the own exclusion of an `[any-taint]` leaf in `toExclusion`),
     *  the per-path form of `Record.reversedAt` (ap-impl.md §7.8). A must record (only forward) gives its result in the
     *  demand layer, with no exclusion, when it applies by `applicable` only (`recordDemand`, ap.md §4.3; Lean
     *  AnyTaintEx.recLayerX); a demoted result is SUMMARY_EFFECT (applyRecord, §4.6). No other demotion: an exclusion
     *  applies by `concat`. */
    private fun retRec(l: PLink) {
        if (config.run1) return                                                                 // run 1 reads no record
        val a = l.added.p()
        val edges = LinkedHashSet<Pair<Pattern, Conclusion>>()                                  // (premise, conclusion), by value
        for (r in config.records.byEntry(l.callee, a)) if (r.direction == config.direction)
            for (g in ops.leaves(r.conclusion)) edges += r.premise.toPattern() to Conclusion(g.fact, g.exclusion, demand = false)
        fun reversibleLeaf(r: Record, g: Pattern) = r.premise.tail != Tail.ANY_TAINT &&              // R3, leaf by leaf
            !(g.fact.tail == Tail.ANY_TAINT && g.exclusion != ExclusionSet.Empty)
        for (r in config.records.byExit(l.callee, a)) if (r.direction != config.direction) {
            val p = r.premise.toPattern()
            for (g in ops.leaves(r.conclusion)) if (reversibleLeaf(r, g))
                revEdge(summaryEdge(p, Conclusion(g.fact, g.exclusion, demand = false)))              // as Record.reversedAt
                ?.let { e -> edges += Pattern(e.from, ExclusionSet.Empty) to Conclusion(e.to, e.exclusion, demand = false) }
        }
        for ((j, g) in edges) if (applicable(j, a) || inside(j, a))
            applyS(l.added, j, g)?.let { x ->
                val demoted = recordDemand(j, a, resultDemand = false)                           // the record demotion
                val y = if (demoted) normalize(x.fact, x.exclusion, demand = true) else x        // W8 (b): `[any]`, no exclusion
                resume(l.caller, PlanItem(l.caller.premise, y, if (demoted) Origin.SUMMARY_EFFECT else origin(j, g)))
            }
    }

    /** zret (Backward.DB; the zeroOnly branch of applySummary, §4.6): a {zero} -> g summary of the callee applies to the
     *  caller edge {zero} -> zero with no test and no restriction; the result has the zero premise of the caller. */
    private fun zret(z: Pair<MethodKey, PFact>) {
        val (callee, caller) = z
        for (s in summaries.toList()) if (s.method == callee && s.premise == setOf(zero))
            resume(caller, PlanItem(caller.premise, s.g, Origin.SUMMARY_EFFECT))
    }

    /** A result of the callees stage goes on from its end point (RETURNED forward, ADDED backward), as fromCallees (§4.6). */
    private fun resume(caller: PFact, item: PlanItem) {
        val call = program.callAt(caller.node)!!
        val callees = forms.call(caller.method, caller.node, call).stages.first { it is CallStage.Callees }
        walk(caller, call, listOf(item), from = callees.to)
    }

    /** rule seed (ap.md §9.2; fireSinkSeeds, §4.9): each sink seed at (m, n): the requirement in the normal layer (an
     *  `[any]` requirement is demand, ap.md W6; the backward run has no `[any-taint]`, W8 (d)), cut by `limit`. */
    private fun sinkSeeds(m: MethodKey, n: CommonInst): List<Conclusion> =
        config.seeds.at(m, n).filterIsInstance<Seed.Sink>().map { seedOf(it.requirement) }

    /** One seed requirement (seedFact, §4.9): of the hand-off (`sinkSeeds`) or of the trigger of an end fact. */
    private fun seedOf(p: Pattern): Conclusion = limit(normalize(p.fact, ExclusionSet.Empty, demand = false), config.fieldLimit)

    /** start (addInitial, §4.2): each new initial fact starts with its start fact (`startFact`, ap.md §6.5) at every start
     *  node of its kind; a must-premise (forward restricted runs only) starts as itself, normal, with its exclusion. */
    private fun addInitial(m: MethodKey, j: Pattern) {
        if (initials.add(m to j)) for (n in forms.startNodes(m, j.fact.base == AccessPathBase.Zero))
            startRules(m, setOf(j), n, startFact(j))
    }

    /** The start rules (startAt, §4.4), by `boundary`: forward the entry rules; backward the reversed exit rules of that
     *  exit (normal or exceptional) on the start fact and, for the premise {zero}, on each sink seed of that exit. */
    private fun startRules(m: MethodKey, premise: Set<Pattern>, n: CommonInst, c: Conclusion) {
        val seeds = if (!forward && premise == setOf(zero)) sinkSeeds(m, n).map { setOf(zero) to it } else emptyList()
        for ((pr, x, _) in boundary(m, forms.startRules(m, n), n, listOf(premise to c) + seeds)) facts += PFact(m, pr, n, x)
    }

    /** The confirmation of the reference (Support, §7.5; Lean Confirmed.Sup, NDConfirmed.SupN): a naive least fixed point
     *  over `links`. (m, P) is supported if m is a root and P = {zero}, or if every member of P is zero or exact concrete
     *  and ONE call statement has, per member, a normal link (normal added fact, normal caller edge) with an EQUAL added
     *  fact whose caller premise set is supported. A witness is confirmed if it is normal, its premise set (the `union`)
     *  has only zero or exact concrete members, and the set is supported in the method key of the witness. THE TAIL
     *  `[any-taint]` (a forward restricted run; ap.md §4.9 conditions 2 and 3.2.3; Lean AnyTaintEx.SupX, SupLinkX): a
     *  must-premise is a member like an exact fact, and a normal `[any-taint]/E` added fact supplies a `$` member or a
     *  must-premise that lies inside it, the exclusions read (`inside`), with the same mark. */
    private fun naiveSupport(): Set<VulnerabilityKey> {
        val must = config.restricted                                                    // forward here: run >= 3
        fun exactOrZero(j: Pattern) = j == zero ||
            (j.fact.mark is MarkSlot.Concrete && (j.fact.tail == Tail.EXACT || (must && j.fact.tail == Tail.ANY_TAINT)))
        fun supplies(a: Pattern, j: Pattern) = a == j || (must && a.fact.tail == Tail.ANY_TAINT && j != zero &&
            a.fact.mark == j.fact.mark && inside(j, a))                                  // 3.2.3, the second case
        val normal = links.filter { !it.added.demand && !it.caller.c.demand }
        val sup = config.roots.mapTo(HashSet()) { it to setOf(zero) }
        fun supplied(m: MethodKey, p: Set<Pattern>) = p.all(::exactOrZero) &&
            normal.filter { it.callee == m && (it.caller.method to it.caller.premise) in sup }
                .groupBy { it.caller.method to it.caller.node }.values
                .any { site -> p.all { j -> site.any { supplies(it.added.p(), j) } } }
        val candidates = facts.mapTo(LinkedHashSet()) { it.method to it.premise } + vulnerabilities.map { it.methodKey to it.premise }
        do {
            val before = sup.size
            for ((m, p) in candidates) if ((m to p) !in sup && supplied(m, p)) sup += m to p
        } while (sup.size != before)
        return vulnerabilities.filter { !it.demand && it.premise.all(::exactOrZero) && (it.methodKey to it.premise) in sup }
            .mapTo(HashSet()) { it.key }
    }

    private fun size() = facts.size + links.size + summaries.size + zeroSubs.size + initials.size + requests.size +
        vulnerabilities.size + hits.size
}
```

```kotlin
class ScheduleFuzzTest {
    @Test
    fun `every schedule reaches the same closure`() {
        for (program in ToyPrograms.all) {                    // programs 1 (ap.md §6.3), 2 (ap.md §6.4), 3 (§9.1), the backward cases,
                                                              // G, C, I, P (AnyTaintCases; AnyTaintExCases2), S, SD,
                                                              // B, X, R, CL (AnyTaintExCases), CUT1, MK (§9.1),
                                                              // WRAP, the getter (HandoffCases.Wrap, Getter; F70),
                                                              // END, CONJ, DLINK (the review of F70, §9.1)
            for (config in program.runs()) {                  // run 1, a restricted forward run, a backward run
                val reference = NaiveClosure(program, config, program.ap).run()
                repeat(200) { seed ->
                    val got = FuzzRun(config, program.shared(), seed.toLong()).run()
                    assertEquals(reference.vulnerabilityKeys, got.vulnerabilityKeys, "seed $seed")
                    assertEquals(reference.confirmed, got.confirmed, "seed $seed")
                    assertEquals(reference.hits, got.hits, "seed $seed")                    // backward: the source hits
                    assertTrue(got.processed.dominates(reference.facts) && reference.facts.dominates(got.processed), "seed $seed")
                    assertTrue(got.summaries.dominates(reference.summaries) && reference.summaries.dominates(got.summaries), "seed $seed")
                    assertTrue(got.demandEdges.dominates(reference.demandEdges) &&            // F70: the demand edges
                        reference.demandEdges.dominates(got.demandEdges), "seed $seed")
                }
            }
        }
    }
}
```

`FuzzResult.processed` holds, per `PathKey`, the leaves (`FormsReference.conclusions`) of every processed item, from
both queues of `DeltaWorklist`. The two results compare per `PathKey` with `dominates` in both directions.
`program.shared()` makes new stores per seed (a new `ConcurrentVulnerabilityStore`, `PersistentRecordStore`).

### 9.3 Proof-first map

Each test names the Lean theorem or counterexample in the table of §9.1. The protocol tests follow the traces of the
namespace `PCex` in `PipelineProofs.lean`: one test per counterexample, with a mock that breaks the condition, and the
same schedule on the real code. The hand-off of the demand edges only (F70) follows `HandoffCases.lean` (the programs
WRAP and getter, and the CEGAR programs ANYW and ANYM with a stub that breaks the fourth condition of `Handoff.Cross`:
§9.1 row 29), and its two theorems on the run sequence, the narrowing (in the locations and the marks,
`HandoffNoStar.narrowing_canon_loc_exactM`, F71) and the exclusion (`HandoffExclusion.exclusion_theorem`), are
property tests (§9.1 row 30). The mark tests of F71 follow the vectors `Handoff.RVec` and `HandoffX.XVec` of
`HandoffRestrict.lean` and `HandoffXRestrict.lean`: the engine tests of §9.1 rows 33 and 34 run the user's example and
the `*∖X` emission, each with a stub that has the test before F71 (the CEGAR `Handoff.restrictI_contract_loc_false`;
the old cell `Handoff.RVec.markMatchB70`), and the other cells are AP-level tests (`ap-impl.md` Part I §8 test 17). The three
regressions of the review of F70 (§9.1 rows 21, 31, 32: DLINK, END, CONJ) have no Lean program: the model has no end
facts and no restricted run with ND edges, and `NO_DEMAND_EDGE` is argued (`ap.md` §11.2).

### 9.4 A protocol test: the `[any]` delivery (P4)

The test runs in a RESTRICTED forward run: there a fact with `[any]` above the premise satisfies it (`inside`). In run 1,
`applicable` rejects a fact above the premise, so the case does not exist there.

```kotlin
class AnyDeliveryTest {
    private val ap = ApManager(Cancellation())
    private val ops = ApOps(ap)
    private val f = ApFixtures(ap, ops)                       // test builders: patterns → InitialAp, Facts, CallerRef

    /** A SubscriptionPort that records the applications and keeps the deliveries in an inbox. */
    private class RecordingPort(override val config: RunConfig, override val ops: ApOps) : SubscriptionPort {
        override val steps = ProtocolSteps.Inline
        val storages = HashMap<MethodKey, SummaryStorage>()
        val inbox = ArrayDeque<RunEvent.Delivery>()
        val applied = ArrayList<Triple<Subscription, Publication, Int>>()
        override fun summaryStorage(key: MethodKey) = storages.getOrPut(key) { SummaryStorage(key, ops.manager, ops, steps) }
        override fun applier(caller: MethodKey) = object : SummaryApplier {
            override fun applySummary(part: Subscription, pub: Publication, member: Int) { applied += Triple(part, pub, member) }
            override fun applyRecord(part: Subscription, record: Record) = Unit
        }
        override fun post(event: RunEvent.Delivery) { inbox += event }
    }

    @Test
    fun `a caller fact with any above the premise gets a summary published after its subscription`() {
        val config = RunConfig(3, fieldLimit = 3, demand = DemandStore.Builder(ap).build(),
            records = PersistentRecordStore(ap).view(), seeds = SeedIndex.EMPTY, roots = emptyList())
        val port = RecordingPort(config, ops)
        val manager = SubscriptionManager(port)
        val callee = f.method("callee"); val caller = f.method("caller")
        repeat(12) { k ->                                     // >= 10 entries: today the literal index is active (MethodTreeAccessPathSubscription.kt:211-213)
            manager.subscribe(Subscription(callee, f.ref(caller, call = k), Layer.NORMAL,
                f.tree("arg0", listOf("f$k"), Tail.EXACT, mark = "T")))
        }
        val any = Subscription(callee, f.ref(caller, call = 99), Layer.DEMAND, f.tree("arg0", emptyList(), Tail.ANY, mark = "T"))
        manager.subscribe(any)                                // the replay reads an empty storage
        assertTrue(port.applied.isEmpty())

        val j = f.initial("arg0", listOf("g", "h"), Tail.EXACT, mark = "T")    // (arg0, .g.h, $, T) lies inside (arg0, ., [any], T)
        val pub = Publication(j, f.tree("ret", emptyList(), Tail.EXACT, mark = "T"))   // one member: the key is j itself
        port.summaryStorage(callee).publish(listOf(pub))     // P2: insert, then notify → one Delivery
        while (port.inbox.isNotEmpty()) port.inbox.removeFirst().let { manager.onDelivery(it.callee, it.publications) }   // P6

        val hit = port.applied.single { it.first.ref.call == f.call(99) }
        assertEquals(pub, hit.second)
        assertEquals(ops.satisfying(any.added, j, config.mode), hit.first.added)   // P4: the replay function
        assertTrue(port.applied.none { it.first.ref.call != f.call(99) })           // (arg0, .f_k, $) does not contain j
    }

    @Test
    fun `an any-taint caller fact gets the summaries of every premise key of one path that lies inside it`() {
        val config = RunConfig(3, fieldLimit = 3, demand = DemandStore.Builder(ap).build(),
            records = PersistentRecordStore(ap).view(), seeds = SeedIndex.EMPTY, roots = emptyList())
        val port = RecordingPort(config, ops)
        val manager = SubscriptionManager(port)
        val callee = f.method("callee"); val caller = f.method("caller")
        val must = Subscription(callee, f.ref(caller, call = 7), Layer.NORMAL,             // a normal link: its any leaf
            f.tree("arg0", emptyList(), Tail.ANY_TAINT, mark = "T"))                       // is `[any-taint]` (ap.md W8)
        val excl = Subscription(callee, f.ref(caller, call = 8), Layer.NORMAL,             // `[any-taint]/{g}`: a setter of `g`
            f.tree("arg0", emptyList(), Tail.ANY_TAINT, mark = "T", exclusion = listOf("g")))
        manager.subscribe(must); manager.subscribe(excl)                                   // the replay reads an empty storage

        val jMust = f.initial("arg0", listOf("g"), Tail.ANY_TAINT, mark = "T")            // the must-premise
        val jMustH = f.initial("arg0", listOf("g"), Tail.ANY_TAINT, mark = "T", exclusion = listOf("h"))   // another exclusion
        val jMay = f.initial("arg0", listOf("g"), Tail.ANY, mark = "T")                   // the `[any]` premise of the same path
        assertEquals(3, setOf<PremiseKey>(jMust, jMustH, jMay).size)                       // three premise keys (analyzer-core.md §4.1)
        port.summaryStorage(callee).publish(listOf(
            Publication(jMust, f.tree("ret", emptyList(), Tail.EXACT, mark = "T")),       // normal: a must-premise starts normal
            Publication(jMustH, f.tree("ret", emptyList(), Tail.EXACT, mark = "T")),
            Publication(jMay, f.tree("ret", emptyList(), Tail.EXACT, mark = "T", layer = Layer.DEMAND))))   // three index entries
        while (port.inbox.isNotEmpty()) port.inbox.removeFirst().let { manager.onDelivery(it.callee, it.publications) }

        assertEquals(setOf<PremiseKey>(jMust, jMustH, jMay),                                // all three lie inside `must`
            port.applied.filter { it.first.ref.call == f.call(7) }.mapTo(HashSet()) { it.second.premise })
        assertTrue(port.applied.none { it.first.ref.call == f.call(8) })                    // `g` is excluded: none lies inside
        for ((part, pub, m) in port.applied)                                               // P4: `inside`, the one match function
            assertEquals(ops.satisfying(must.added, pub.premise.member(m), config.mode), part.added)
    }
}
```

It mirrors `Pipeline.PCex.cex_P4`: the same trace (`proc sub`, `replay sub` on an empty storage, `proc pub`,
`notify pub`, `deliver`), with the one match function, so the analyzer processes the join (`PCex.step_finds_edge`). A
second test publishes first and subscribes after; it asserts the same `hit.first.added` through the replay. Both
`assertEquals` on trees read the structural `Facts.equals` (DD4).

The `[any-taint]` test (`analyzer-core.md` §13 item 3, its last sentence; item 25) mirrors
`PipelineAnyTaintEx.no_lost_summary_DRX`: the link carries the added fact with its flag (`[any-taint]`: normal on the
link) and its exclusion, each publication carries the flag and the exclusion of its callee premise, and the join does
not read them (`analyzer-core.md` §5.5 THE ENCODING WITH `[any-taint]`). The three premise keys of one path are three
`Member`s of `PublicationIndex` and three applications; the exclusion `{g}` of the second link removes the members at
`.g` (`satisfying` reads it, Lean `AnyTaintEx.satX`).

---

## 10. Spec issues

This document implements `analyzer-core.md` as it is. These points of the spec need a decision; the right column says
what this document does:

| # | `analyzer-core.md` | Problem | What this document does |
|---|---|---|---|
| 1 | §13 item 3 | The `[any]` delivery case exists only in a restricted run (`inside`). In run 1, `applicable` rejects a fact above the premise. | `AnyDeliveryTest` runs in run 3 (§9.4). RESOLVED (F68): `analyzer-core.md` §13 item 3 says "in a restricted run (`inside`)". |
| 2 | §4.8, §4.9 | The cache keeps the forms per method, or per (method, direction). But the call plans and the entry rules read the context of the method key (the callees, the start filter). | The forms are per method key (DD6; `ap-impl.md` §31.2). RESOLVED (F68): `analyzer-core.md` §4.8, §4.9 and §10 (`MethodContextCache.forms(key)`) cache the call plans and the entry rules per method key, the statement summaries and the exit rules per method. |
| 3 | §0, §6.3, §7.1 | `analyzer-core.md` §0 puts the budget in the iteration policy, and `analyzer-core.md` §6.3 ends a run by a timeout. But `IterationPolicy` and `RunManager.run()` take no budget. | `IterationPolicy.timeout`, `IterationDriver(policy, shared, budget)`, `RunManager.run(timeout)` (§3.2, §7.1). RESOLVED (F68): `analyzer-core.md` §7.1 has `IterationPolicy.timeout`, the budget, `RunManager.run(timeout)` and the run-1 check. |
| 4 | §8 | The spec keeps the progress log. Today's progress job reads runner-local statistics from another thread. | The progress log reads only the atomic counters of `InFlight` and the memory usage (§3.2); today's per-method statistics are not kept (§2.1). |
| 5 | §8 | `TimedMethodAnalyzer` becomes a decorator of the new interface. | No decorator in phase 2: it is debug only (`DEBUG_ANALYSIS_TIME = false`, `CORE/ap/ifds/MethodAnalyzer.kt:1391`; §2.1). |
| 6 | §8 | The reuse table says "REUSE the structure" for `AccessPathBaseStorage`. It rejects the `Zero` base (`ap-impl.md` §2). | Not used: `MethodEdgeStore` keys its groups by base inside `ConclusionGroup` (§2.1; `ap-impl.md` §7.3, §34 SI18). RESOLVED (F68): `analyzer-core.md` §8 says NOT USED. |
| 7 | §7.1, §10 (F70) | `RunResult.demandLayerEdges` counts "the deltas of `edges.add` in the demand layer". An exit fact goes to the exit rules and to `summaryDelta`, not to `edges.add` (§4.3), so a cut of the exit rules (`Cut.EXIT_RULES`) can give a demand-layer summary with no demand-layer `edges.add` delta. | `demandLayerEdges` also counts a demand-layer summary delta (§4.7) and a new demand link (§4.2). RESOLVED (F70, the review round): `analyzer-core.md` §4.1 `counters`, §4.2 `addLink` and §7.1 count the DEMAND-LAYER OBJECTS: the demand-layer deltas of `edges.add`, the demand-layer summary deltas and the demand links (a call cleaner can demote a bound fact on a link while every edge stays normal; program DLINK, §9.1 row 21). |
| 8 | §10 `handOffOf` (F70) | The spec computes the publications of the leaves that are not crossable AGAIN at the barrier, from `summaries` and `config.demand`. `ap-impl.md` §5.9, §7.6 (DD17) has the analyzer keep them during the run (`ApOps.demandPart`, `RunSummaryStore.addDemand`, `demandEdges()`). | This document follows `ap-impl.md`: `summaryDelta` adds the pieces (§4.7), and `HandOff.of` reads only `demandEdges()` (§7.2). The restriction acts leaf by leaf, so the pieces are the same (Lean `Handoff.pubD`, `pubR`; the fuzzer compares them with the reference, §9.2). The cost moves from a second restriction at the barrier to a second conclusion group per premise key during the run. RESOLVED (F70, the review round): the demand pieces are STORED DURING THE RUN in both texts (`analyzer-core.md` §4.1, §4.6, §7.3, §7.4, §10 `handOffOf`; `ap-impl.md` DD17, `RunSummaryStore.addDemand`, `demandEdges()`). |
| 9 | §7.4 (F70) | The first form of Lean `Handoff.demOfN` tested only `Cross (revRec (jb, gb))`, and `revRec` makes the record normal, so a demand-layer backward leaf with a crossable reversal was no demand edge. R1 persists only normal backward edges, so no record can cross it. | `ApOps.demandPart` keeps every demand-layer leaf (§7.3). RESOLVED (F70): Lean `Handoff.CrossB` (normal and `Cross` of the reversal) in `demOfN` case 3 (`ap-impl.md` §34 SI21). |
| 10 | §7.7 (F70) | The pipeline form of the driver theorem with the new hand-off, `PipelineHandoffDriver.driver_iterationNX`, seeds EVERY reported vulnerability. The driver seeds only the DEMAND vulnerabilities (§7.2). | The spec-closure form with the DEMAND seeds is proved: `HandoffXIter.iteration_generalNX` and its inclusion form `HandoffXIter.iteration_generalNX_incl` (`hseeds`: confirmed by a complete forward run up to `k`, or seeded). RESOLVED (F70, the review round): the pipeline form with the DEMAND seeds is `PipelineHandoffDriverExt.driver_iterationNX_demand` (`C k`: confirmed by a forward run up to `k`, in the sense of `ap.md` §4.9), its finite form `PipelineHandoffDriverExt.driver_iterationNX_upto` (the runs complete only up to the last forward run `K`; the induction stops at `K`), and with the source seeds `PipelineHandoffDriverExt.driver_iteration_srcNX` and `PipelineHandoffDriverExt.driver_iteration_srcNX_upto`. `PipelineHandoffDriver.driver_iterationNX` stays as the form with every reported vulnerability seeded. `PipelineHandoffDriverExt.driver_iterationNX_confirmed` takes a weaker `C` (a normal-layer report, not the support of `ap.md` §4.9); this document does not cite it as the confirmation of the spec (§7.1, §7.2). |
| 11 | §1, §3, §4.4, §4.6, §7.3, §7.4, §7.7, §7.8 (F71) | The restriction read `D-c` and `D-p` as locations only (the marks ignored), the demanded witness read the exit location without its mark (Lean `p.coversLoc l2` in `Handoff.FlowRR.call`), and an entry pattern `*∖X` counted as `*` in the emission. So a demand with the concrete mark `T` did not ask for `T`: the restriction published a conclusion with another mark, the hand-off could give it to the next run, and the narrowing was exact in the locations only. The cost was precision and work, not a lost flow and not a false CONFIRMED. | `restrictBy` reads the two mark tests of `ApOps.restrict` (§4.7: the premise inside `D-c` in its marks, Lean `Handoff.insideB`; the mark of each conclusion leaf meets the mark of `D-p`, Lean `Handoff.concMarkB`); `ApOps.emit` reads `*∖X` exactly (§4.2; Lean `markMatchB`); the hand-off keeps the marks of a pattern (§7.2, §7.3); the narrowing property test asserts the marks (§9.1 row 30: `HandoffNoStar.narrowing_canon_loc_exactM`, `HandoffXMain.narrowing_canonXM`); §9.1 rows 33 and 34 test `analyzer-core.md` §13 items 41 and 42. RESOLVED (F71): `ap.md` §1, §6.1, §6.3, §6.4, §9.2 and `analyzer-core.md` §1, §3, §4.4, §4.6, §7.3, §7.4, §7.7, §7.8 read the marks, and the Lean contracts take `Handoff.insideB` and `p.covers l2` (`Handoff.restrictI_contract`; the location form is false, `Handoff.restrictI_contract_loc_false`). |
| 12 | §13 item 41 (F71) | The item says that the delta of the user's example against `D-p = (ret, .f, $, T)` "is published and stored". But the leaf `(x, ., $, T) → (ret, .f, $, T)` is normal, has a `$` premise and a `$` leaf, and is mark-reversible, so it is CROSSABLE (§1; `ap.md` §1). `demandPart` keeps none of it, and the run stores no demand edge for it with either `D-p`: `persist` keeps it as a record. So the check "no demand edge" with `D-p = (ret, .f, $, U)` holds also with no mark test, and the check "stored" with `D-p = (ret, .f, $, T)` fails. | §9.1 row 33 tests the publications on the user's example, and the demand edges on a DEMAND-LAYER variant that is not crossable (`m(x){ ret.f.g = x; }` at `L = 1`: the leaf `(ret, .f, [any], T)`, which the meet with `D-p = (ret, .f, $, T)` makes `(ret, .f, $, T)` in the demand layer). Proposed text for `analyzer-core.md` §13 item 41: "is published; its leaf is crossable, so it is a record and no demand edge. A demand-layer form of the same delta is published and stored as a demand edge with `D-p = (ret, .f, $, T)`, and not with `D-p = (ret, .f, $, U)`". RESOLVED: `analyzer-core.md` §13 item 41 has this text now (the coordinator, F71). |

# Analyzer core — specification

Status: design spec of the new analyzer core (phase 2 of [bidirectional-task.md](../bidirectional-task.md)). This
document is normative. It uses two other specs and does not repeat them:

* [`ap.md`](ap.md): the fact, the edge, the AP operations, the runs, the stores and their theorems;
* [`interpreter.md`](interpreter.md): the micro edges of the IR and the order of the rules.

This document defines the ENTITIES of the analyzer, who owns which data, the METHOD ANALYZER, the COMMUNICATION
PIPELINE between the methods, the scheduling and the end of a run, and the ITERATION DRIVER with the hand-offs between
the runs. Appendix A gives the analysis of today's analyzer that the design starts from.

The formal model is in [`spec/lean`](lean): `Pipeline.lean`, `PipelineProofs.lean`, `PipelineAP.lean`,
`PipelineStore.lean`, `PipelineDriver.lean`, `PipelineSeeds.lean` (with `ForwardSeeds.lean`), `PipelineNDZ.lean` (with
`NDZ.lean`, `NDZeroBase.lean`), `PipelineAnyTaintEx.lean` and `PipelineAnyTaintExDriver.lean` (with the
`AnyTaintEx*.lean` files of the tail `[any-taint]` and its exclusion, and the `AnyTaint*.lean` files that they reuse,
`ap.md` §10.11). Every theorem named here
is machine-checked and constructive (`ap.md` §10 defines the term). §11 lists what is argued and not proved.

Language: ASD-STE100 Simplified Technical English.

---

## 0. Scope

The analyzer core:

1. runs one run (`ap.md` §6): one direction, one field limit, one mode (run 1 or restricted), to a fixed point;
2. exchanges the edges between the methods of a run with no loss (§5);
3. detects the end of a run (§6);
4. runs the sequence of runs and computes the hand-off from each run to the next (§7);
5. gives the report: the vulnerabilities and the end of the analysis (§7.5, §9).

The core is for the JVM. Go is out of scope.

Out of scope:

* the IR interpreter (`interpreter.md`); §4.9 gives only its interface to the core;
* the prescan, the rule reduction and the `TaintAnalyzer` wiring (phase 3); §9 gives the interface;
* the trace resolution. The core keeps no store of a run for a trace resolver (§7.6). The phase-3 output holds every
  entry of the report, CONFIRMED and DEMAND, and gives each one a simple trace (§9; `ap-history.md` F68);
* the iteration policy: the field limit of each run, the budget and the stop rule for a budget (`ap.md` §6.6). The
  driver takes the policy and the budget as parameters (§7.1).

### 0.1 Assumptions

| # | Assumption |
|---|---|
| A1 | The AP operations and stores satisfy `ap.md`. The interpreter satisfies `interpreter.md` I1–I14. The proofs of this document use only the closures of `ap.md` (Lean `D`, `DR`, also `DR` of the seeded program `FSeeds.keepSources P σ` (§7.7), `Backward.DB`, `Statics.DS`, and with the conjunctions `NDZ.DNz`, the closure of the spec (§5.5), with its list model `ND.DN`). With the tail `[any-taint]` (`ap.md` W8, §10.11) they also use run 1 with the layer rules W6 and W8 and the exclusion of `[any-taint]` (`AnyTaintEx.D6X`) and the restricted forward run with must-premises and exclusions (`AnyTaintEx.DRX`; with the spec rules `AnyTaintEx.DRXs`). The backward run has no `[any-taint]`: it stays `Backward.DB`. |
| A2 | LINEARIZABLE SHARED ACTIONS. Each shared action of §5.2 and §5.3 is atomic: register a handler, insert a publication, read the storage, read the handler list. All of them have one total order. This order agrees with the program order of each thread. The Lean model is an interleaving model with these actions as steps. P3 (§5.3) is the implementation rule. |
| A3 | RELIABLE EVENTS. An event that a thread sends to the channel of a runner arrives exactly once, unless the run is cancelled. The send happens before the receive (Kotlin `Channel`). |
| A4 | READ-ONLY INPUTS. These inputs do not change during a run: the program, the rules, the lambda resolutions, the demand store, the record store and the seeds. The driver makes them before the run starts. The start of the run publishes them to every runner. |
| A5 | A handler (the code of one event) ends. Only the end of a run needs this (§6). The no-loss theorem does not need it (§5.5). |

---

## 1. Terms

`ap.md` §1 defines the AP terms (fact, edge, premise set, layer, link, added fact, run, demand pattern, record, request,
and others). This document adds:

| Term | Meaning |
|---|---|
| method key | `ap.md` §1: the `MethodEntryPoint` of the method (context and FORWARD entry statement). The backward run uses the same key. Its start nodes are the forward exits (§4.4). An empty method has no method key (§4.4). |
| vulnerability key | `(rule, method, statement)`: the sink rule, the METHOD of the method key (without the context) and the sink statement (§4.7). One sink statement that the analysis reaches in several contexts is ONE vulnerability. |
| sink alternative | One DNF cube of a sink rule at one place, with one array choice (`interpreter.md` §4.1, §4.2). Its index (`SinkRule.alternative`) is the same in every run and in every context (`interpreter.md` I5). |
| sink witness | One sink edge, or one sink edge set of a conjunctive sink, of one sink alternative in one method key and one run (§4.7). |
| unit | A group of methods that one runner owns (today a package; `UnitResolver`). |
| runner | The single coroutine of one unit in one run. It runs one event at a time. |
| actor | The owner of a set of objects. Each method analyzer is an actor. Its runner runs it. |
| method analyzer | The actor of one method key in one run (§4). It owns the intra-procedural edges and every RUN store of its method. |
| event | One message in the channel of a runner (§5.1). Its HANDLER is the code that the runner runs for it. |
| subscription | A caller-side record `(caller edge, call statement, added fact)` (`ap.md` §8.4). |
| publication | A summary edge that the callee gives to its subscribers. In a restricted run it is the result of the restriction (`ap.md` §6.4). It carries its premise key with the tail of each member and the exclusion of an `[any-taint]` member (§4.1, §4.6). |
| storage with subscription | The callee-side store of the publications, with the list of the subscribed runners (§5.2). |
| replay | The read of the storage when a subscription is new (§5.3). |
| notification | The send of a new publication to every subscribed runner (§5.2). |
| delivery | The event that carries a notification to one runner (§5.3). |
| quiescence | The state of a run with no event in a channel or a local queue, no running handler, no worklist item and no pending publication (§6.2). |
| barrier | The point between two runs: the first run is quiescent, and the next run has not started (§7.2). |
| hand-off | What one run gives to the next run: the demand and the seeds (`ap.md` §8, §9.2). The records are PERSISTENT, not a hand-off (`ap.md` §8.7). |
| complete run | A run that ended at quiescence. A run that ended by a timeout, its memory guard or an exception (every `Throwable`, §6.3) is INCOMPLETE. An incomplete run adds nothing to the report and refutes nothing (§7.5). |

---

## 2. Entities and ownership

The layout is the layout of today: a manager, one runner per unit, one analyzer per method that keeps its own edges,
and storages with subscription between the methods. The differences: a NEW engine for each run, and one driver above
the runs.

```
IterationDriver                                   lifetime: the analysis
 ├ ApManager, MethodContextCache, RecordStore, VulnerabilityStore, executor (thread pool)
 └ for each run: RunManager(RunConfig)            lifetime: one run
     ├ summaryStorage(methodKey) → SummaryStorage one per method key, made on the first access by any thread
     └ for each unit: UnitRunner                  one coroutine
         ├ MethodAnalyzerStorage → RunMethodAnalyzer (one per method key)
         └ SubscriptionManager                    caller side: the subscriptions of the unit
```

| Entity | Lifetime | Thread | Owns | From today |
|---|---|---|---|---|
| `IterationDriver` | analysis | the caller thread | the run sequence (§7) and the shared objects below | new |
| `ApManager` | analysis | any (thread-safe) | the interners of the AP (`ap.md` §7.5) | the new AP (`ap.md` §7) |
| `MethodContextCache` | analysis | the runner of the method during a run | the parts of the method context that do not depend on the run (§4.8) | split of `JIRMethodAnalysisContext` |
| `RecordStore` | analysis (PERSISTENT) | the driver writes it at a barrier; read-only during a run | the records (`ap.md` §8.7) | new |
| `VulnerabilityStore` | analysis (PERSISTENT) | any runner adds (concurrent); the driver reads it at a barrier | the sink witnesses per vulnerability key, each with its alternative, its method key and its run (§4.7) | replaces the buckets of `TaintAnalysisUnitStorage` |
| `RunManager` | one run | the caller thread and the runners | unit routing, runner spawn, the map of the `SummaryStorage`s, the in-flight counter, the run status (§6) | `TaintAnalysisUnitRunnerManager` |
| `UnitRunner` | one run | its coroutine | the event loop, its analyzers, its `SubscriptionManager` | `TaintAnalysisUnitRunner` |
| `RunMethodAnalyzer` | one run | the runner of its unit | the RUN stores of its method (§4.1) | replaces `NormalMethodAnalyzer`; `EmptyMethodAnalyzer` goes (an empty method is never analysed, §4.4) |
| `SummaryStorage` | one run | the runner of its method inserts; each subscribing runner registers and reads | the publications of one method key and the subscribed runners (§5.2) | `SummaryEdgeStorageWithSubscribers` |
| `SubscriptionManager` | one run | the runner of its unit | the subscriptions of the unit, per callee (§5.3) | `SummaryEdgeSubscriptionManager` (today two per runner, internal and external; one is enough) |
| `DemandStore` | one run, read-only | any | the demand patterns of the run (`ap.md` §8.6) | new |

Ownership rules:

* O1. A method analyzer is the only writer of its RUN stores. Only its runner calls it.
* O2. A `SummaryStorage` has one INSERTING thread: the runner of its method. A subscribing runner only registers its
  handler and reads (§5.3). `RunManager.summaryStorage(key)` makes exactly one storage per method key and run. It
  makes it atomically, on the first access by any thread (a `computeIfAbsent` on a concurrent map). The storage can
  exist before the runner of the method exists.
* O3. A `SubscriptionManager` is local to its runner. Another thread calls only its `notify`, which reads no state of
  the manager.
* O4. During a run, the other shared objects are read-only (A4), write-only (`VulnerabilityStore`), or thread-safe by
  their own contract (`ApManager`).
* O5. After a complete run, the driver reads the stores of the run that §7.6 keeps. No runner runs then (§7.2). After
  an incomplete run, the driver reads no store of the run (§7.5).

---

## 3. The run configuration

```kotlin
/** One run of ap.md §6.6. `Direction` is the enum of ap.md §8.7. */
class RunConfig(
    val index: Int,                          // 1, 2, 3, ...; the direction is FORWARD for an odd index
    val fieldLimit: Int,                     // ap.md §4.4; run 1 needs fieldLimit >= 1 (ap.md S12 (d))
    val demand: DemandStore?,                // null only in run 1
    val records: RecordStore,                // a read-only view; run 1 reads no record
    val seeds: SeedIndex,                    // after run 1: sink seeds (backward), source seeds (forward) (§4.7)
    val roots: List<MethodKey>,              // the root methods; the same in every run
) {
    val direction: Direction get() = if (index % 2 == 1) Direction.FORWARD else Direction.BACKWARD
    val run1: Boolean get() = index == 1
    val restricted: Boolean get() = index > 1
}
```

The mode decides these rules (`ap.md` §6.1):

| Rule | Run 1 (forward) | Restricted forward run | Backward run |
|---|---|---|---|
| initial facts of an added fact | the policy fact (`ap.md` §6.2) and the request answers | the emission `a ∩ D-c` (`ap.md` §6.3); the zero fact for the zero added fact | the emission; the zero fact enters every callee (rule `zin`) |
| a summary applies to an added fact `a` if | `applicable(j, a)` | `inside(j, a)`, after the restriction in the callee | as the restricted forward run; a zero-premise summary applies to the zero fact of the caller with no test and no restriction (rule `zret`) |
| records (`ap.md` §8.7 R3, R4) | none | the FORWARD records by `byEntry`, and the reversed BACKWARD records by `byExit`; each when `applicable(p, a)` or `inside(p, a)`. A forward record with an `[any-taint]` premise that applies by `applicable` only gives its results in the demand layer (`ap.md` §4.3; §4.2 `applyRecord`) | the BACKWARD records by `byEntry`, and the reversed FORWARD records by `byExit`; each when `applicable(p, a)` or `inside(p, a)`. The reversal is LEAF BY LEAF: no leaf of a forward record with an `[any-taint]` premise has a reversal; of any other record, an `[any-taint]/E` leaf with `E ≠ {}` has none, and the other leaves reverse (`ap.md` §8.7 R3; §5.3) |
| mark and position requests, static rule | yes (`ap.md` §4.5, §4.10) | no (assert) | no (assert) |
| sinks | the sink check (`ap.md` §4.9) | the sink check | no sink check; the sink seeds (`ap.md` §9.2) |
| unconditional sources | every source fires | only the source seeds fire (`ap.md` §6.1 rule 6); a zero-premise forward record still applies (`ap.md` §9.2) | every reversed source edge, with no seed filter (the backward run is on the full program, Lean `Reverse.Program.rev P`); it records the source hits (`ap.md` §8.11) |
| type filters | yes | yes | no |
| the tail `[any-taint]` (`ap.md` W8, S15) | a source rule with an `[any]` target gives `[any-taint]` on a normal input: a complete edge (on a demand input `[any]`, W8). A pass rule with an `[any]` target keeps `[any]`: a may, in the demand layer (`ap.md` W6). A normal `[any-taint]` conclusion can carry an EXCLUSION `E` of first accessors, `(x, p, [any-taint], E, T)`: an exclusion edge (the keep edge of a strong write, a `*/E'` summary) gives `E ∪ E'` and the result stays normal (§4.3). Only the demotions of §4.3 make `[any]` of it (demand, no exclusion): the field-limit cut, a cleaner `part` row other than `atAndBelow` and `below` one accessor below it, a may target, a demand-layer input and (in a restricted run) the must-record demotion. No premise has the `[any-taint]` tail | as run 1. Also the `[any-taint]` premise (a MUST-PREMISE) of the emission (§4.4), with the exclusion that the emission gives it: it starts as itself in the normal layer, and its normal edges are complete | no `[any-taint]` (a forward-only tail, `ap.md` W8). The seed of an `[any]` sink pattern and the reversal of an `[any]` condition literal give `[any]`, in the demand layer (`ap.md` W6). Every result of the reversal of a micro edge whose forward target is `[any]` (a pass rule with an `AnyField` target) is in the demand layer, also a `$` result (§4.3). A complete edge is a normal edge, as before F69 (`ap.md` §8.7 R1) |

No run has a liveness check (§4.3).

---

## 4. The method analyzer

The method analyzer `RunMethodAnalyzer` replaces `NormalMethodAnalyzer`. It keeps the pattern of today: the
intra-procedural edges stay inside the analyzer, the analyzer has a worklist, and its runner runs it in steps. One
class serves every direction and every mode. The `RunConfig` gives the differences of the mode. The direction changes
only the forms that the analyzer reads: the forward forms of the interpreter, or their reversals (§4.9).

### 4.1 State

| Field | Store | Content |
|---|---|---|
| `edges` | method edge store (`ap.md` §8.1) | the edges, keyed per kind (`ap.md` §7.2): REACH per (statement, premise key, layer); FLOW per (statement, premise key, layer, base, exclusion, mark exclusion); TAINT per (statement, premise key, layer, base), and a normal TAINT tree also per the one exclusion of its `[any-taint]` leaves (`ap.md` §7.2) |
| `initials` | initial fact store (`ap.md` §8.2) | the initial facts of the run: zero, emissions, answers |
| `links` | added fact store (`ap.md` §8.3) | each added fact with its links: the caller reference and the layer of the added fact on the link |
| `summaries` | run summary store (`ap.md` §8.5) | the summary edges BEFORE the restriction, per premise key and layer |
| `requests` | request store (`ap.md` §8.8) | run 1 only: the standing mark and position requests and their answers |
| `sourceHits` | source hit store (`ap.md` §8.11) | backward run only: the unconditional sources of this method that a requirement reached |
| `conjunctions` | conjunction store (`ap.md` §8.9) | the standing literal inputs per (conjunctive micro edge or sink alternative, statement, literal index), with the evaluated `S` parts of the exit sinks (§4.7); the combinations of the callee summaries with several premises (§5.4) |
| `worklist` | `DeltaWorklist` (§4.3, §10) | the edge deltas to process: the `unchanged` queue with its set, and the `normal` queue |
| `pendingPublications` | | the publications that the analyzer has not yet given to its `SummaryStorage` (§4.6) |
| `queued` | | true while the analyzer has a `Work` event in its runner (§6.2) |
| `context` | `MethodContextCache` entry and run part | the method graph, the alias analysis, the lambda resolutions, the rule context of the run (§4.8) |

The subscriptions are not in the analyzer. They are in the `SubscriptionManager` of the runner of the caller
(`ap.md` §8.4; §5.3).

THE PREMISE KEY HOLDS THE TAIL AND THE EXCLUSION. An `[any-taint]` premise (a MUST-PREMISE) with its exclusion `E` and
an `[any]` premise with the same base, path and mark are two different premise keys (`InitialAp` with the tail
`ANY_TAINT` and the exclusion `E`, or with the tail `ANY`, `ap.md` §7.1). Two must-premises of one path with different
exclusions are two premise keys too. Two added facts of one method (an `[any-taint]` one and an `[any]` one) can give
them at one path. So `initials` holds both, and every store of the table that has the premise key in its key
(`edges`, `summaries`, `conjunctions`) keeps them apart. A forward run only: the backward run has no `[any-taint]`.
Lean: the must flag and the exclusion of the objects `AnyTaintEx.XObj` (`init M j must jex`, `edge M j must jex n f`).

### 4.2 Handlers

The runner calls these handlers. Each handler is part of one event (§5.1).

| Handler | When | Actions | `ap.md` |
|---|---|---|---|
| `addRootZero()` | the run starts at a root | the zero fact is an initial fact | §6.1 |
| `addLink(link)` | a caller binds a fact into this method | add the link (exact deduplication). A new added fact: emit its initial facts (§4.4). A new link: check the standing requests (§4.6). The zero added fact emits the zero fact. No request matches it. Its link serves the support (§7.5). | E1, E2 |
| `addZeroEntry()` | backward: the zero fact of a caller reaches a call to this method | the zero fact is an initial fact (rule `zin`) | §9.2 |
| `addRequest(premise, request)` | run 1: a callee climbs a request through a link of this method | store it (exact deduplication); check it against every link of this method (§4.6) | E5, E7 |
| `applySummary(sub, pub)` | the `SubscriptionManager` matched a publication with a subscription of this method | one premise: apply the summary to the added fact (`ap.md` §4.3), then the stages after the callees stage (§4.5). Several premises: the combination of §5.4. | §4.3, E2, E4, E6 |
| `applyRecord(sub, record)` | a new subscription of this method; the record (already reversed by the `SubscriptionManager` if it is from the other direction) covers or contains its added fact | apply the record, then the stages after the callees stage (§4.5). A record with an `[any-taint]` premise whose premise covers the added fact (`applicable`) but does not lie inside it with the exclusions (not `inside`) gives each result in the demand layer: the result keeps its base, path and mark, and its layer goes up (an `[any-taint]` result becomes `[any]` and loses its exclusion, `ap.md` W8; the must-premise needs every location; Lean `AnyTaintEx.recLayerX`, necessary by `AnyTaintExact.CexApp.cex_app`) | §4.3, §8.7 R3, R4 |
| `step(quantum)` | a `Work` event | process at most `quantum` worklist items (§4.3) | §6.1 (S6: any order) |

A new initial fact `j` (from any handler) is event E3: the analyzer adds the start edges of `j` to the worklist
(§4.4).

### 4.3 The worklist and the step

* An item of the worklist is an edge delta (`EdgeDelta`, §10): (premise key, layer, node, conclusions). The
  conclusions are one of the kinds of `ap.md` §7.2: REACH, a FLOW tree or a TAINT tree. The edge is the fact BEFORE
  the statement of the node, as today.
* `edges.add` returns the delta of the merge (`ap.md` §7.2 T4). A null delta adds nothing, and the analyzer drops it.
  Else the analyzer adds the delta to the `normal` queue of the worklist.
* NO LIVENESS CHECK. No run drops a fact because its local is not live at the node. (Today the forward runs prune by
  `isReachable` of `JIRLocalVariableReachability`.) The alias analysis does not change: it keeps its own inputs, as
  today (§4.8). This is a decision (`ap-history.md` F67).
* The step takes one item and applies its node:
  * a non-call statement: the statement transfer (`ap.md` §4.2; `interpreter.md` §2, §4.4; the STATEMENT mode of
    §4.9) with the primitives that the interpreter puts at the statement (`interpreter.md` §5); then the field limit
    at the cut points (`ap.md` §4.4);
  * a call statement: the call steps (§4.5).
* THE LAYER OF AN ANY-TAIL RESULT (`ap.md` W6, W8). The AP sets it on each application of a micro edge, in every mode
  of §4.9.
  * FORWARD. The result of a micro edge with an `[any]` target (a may: a pass rule with an `AnyField` target) goes to
    the demand layer; the result of a micro edge with an `[any-taint]` target (a source rule, `ap.md` S15) keeps its
    layer. A demand-layer result with the `[any-taint]` tail becomes `[any]` and loses its exclusion. An exclusion does
    not demote a normal `[any-taint]/E` fact: the result carries the exclusion and keeps its layer (`ap.md` §4.1, §4.2,
    §4.7): an exclusion edge at the path of the fact gives `E ∪ E'`; the case below keeps `E`; the case above applies
    only if `E` admits the step down and gives the exclusion of the edge; a read through an accessor in `E` gives
    nothing, a read through another accessor gives the empty exclusion; a copy of the object keeps `E`; the cleaners
    `atAndBelow` and `below` at `P.f` add `f` to `E` (`below` also keeps `(x, P.f, $, T)`). These rows are not
    demotions. THE DEMOTIONS: only these operations make `[any]` of an `[any-taint]` fact, in the demand layer and
    with no exclusion (`ap.md` §2.2 THE DEMOTIONS):
    * the field-limit cut (`ap.md` §4.4);
    * a cleaner `part` row of `ap.md` §4.7 other than the `atAndBelow` and `below` rows one accessor below the fact: so
      the `exact` cleaner at the path of the fact or one accessor below it, and every cleaner two or more accessors
      below it;
    * a may target: the `[any]` target of a pass rule (W6);
    * a demand-layer input: a demand fact (also another input of a conjunction), a demand-layer summary edge or
      record, a demand link (an `[any]` added fact);
    * the must-record demotion (a restricted run; §4.2 `applyRecord`).

    Lean: `AnyTaintEx.w6tX`, `transferX`, `limitFX`, `cleanResX` (`partX`), `recLayerX`; the rows `AnyTaintEx.annX`.
  * BACKWARD. The run has no `[any-taint]` (`ap.md` W8). Every result of a reversed micro edge whose FORWARD target is
    `[any]` goes to the demand layer, whatever its tail, also a `$` result (`ap.md` §9.1): the may belongs to the
    forward rule. W6 puts every `[any]` result in the demand layer. The reversal of a source edge (forward target
    `[any-taint]`, a must) follows the ordinary rows of `ap.md` §4.1. This rule is argued, as the backward W6 (§11).

  The core reads the target tail of the FORWARD form of the micro edge (`MicroEdge.forward`, §4.9): `[any]` is a may
  (a pass rule), `[any-taint]` a must (a source). So the core needs no rule-kind flag, in either direction.
* A result AT AN END NODE of the run (§4.4) goes through the end rules and makes the summary edges (§4.6). This holds
  for every handler that makes such a result: `step`, and also `applySummary`, `applyRecord` and `zret` when the end
  node is a call (for example a backward end node whose forward entry statement is a call). An end node is a
  statement like every other: its transfer or its call steps come first. (Today: `handleStatementEdge`, the edge
  post-processor, then `tryEmmitSummaryEdge`; the new core has no post-processor.)
* A forward result AT AN EXCEPTIONAL EXIT goes through the exit rules of that exit (`interpreter.md` §4.7 steps 1 and
  2: the exit sources, the exit sinks and their end facts, with `Result` read as `exc`; the unconditional exit rules
  fire there on the zero fact, `interpreter.md` D26). Its results end there: an exceptional exit is not an end node
  and makes no summary edge.
* Each result goes to every successor node in the graph of the run, through `edges.add`.
* THE UNCHANGED PATH stays as today (`ap.md` §8.1). If the statement does not touch the base of an edge, the
  analyzer puts the edge for each successor into the `unchanged` queue with no `edges.add` (today
  `addSequentialUnchangedEdge`). The new core has no edge post-processor (`interpreter.md` D14), so an unchanged edge
  always goes on as it is.
* THE TWO QUEUES. The worklist (`DeltaWorklist`, §10) has two queues:
  * `unchanged`: the items of the unchanged path. A SET discards the repetitions: an item that the set holds does not
    go into the queue again (today `enqueuedUnchangedEdges`);
  * `normal`: the deltas of `edges.add`. The zero-to-zero items (REACH on `{zero}`) come first, then the other items
    in LIFO order, as today.

  The step always takes an `unchanged` item while that queue is not empty. The step takes a `normal` item only when
  the `unchanged` queue is empty. When the step finds the `unchanged` queue empty (after the last `unchanged` item
  put its successors into the queues), the analyzer drops the set (it starts a new empty set). The set stays at the
  end of a `Work` event (today the event end resets it). So a loop of statements that do not touch a base ends: the
  set holds the items of the loop until the `unchanged` queue is empty.
* The analyzer does not delay an edge by its depth. There is no fact-depth limit: the field limit of the run is the
  only depth bound (`ap.md` §4.4; `bidirectional-task.md` §5 item 1).

### 4.4 Initial facts, start nodes and start rules

Initial facts:

* RUN 1. For an added fact `a`: the policy fact `(a.base, [], *, {}, *)`, or the zero fact for the zero fact
  (`ap.md` §6.2). The request answers are initial facts too (`ap.md` §4.5, §4.10).
* RESTRICTED RUN. For an added fact `a`, the emission query `near(a.base :: a.path)` returns demand patterns of the
  method (`ap.md` §8.6). Each one whose emission is not empty gives one initial fact `a ∩ D-c` (`ap.md` §6.3).
  The tail of `a ∩ D-c` follows the emission table of `ap.md` §6.3: for an added fact and a pattern that both have an
  any tail, it is the tail of the ADDED FACT. So an `[any-taint]` added fact (it is normal on its link, `ap.md` W8)
  gives an `[any-taint]` initial fact, a MUST-PREMISE, and an `[any]` added fact gives an `[any]` initial fact. The
  emission reads the exclusion `E` of an `[any-taint]/E` added fact as part of its location set: a premise at the path
  of the added fact keeps `E` (a `$` premise has none); the pattern chain below the added fact, at `a.path ++ r`,
  gives a premise with no exclusion, and only if `E` admits `r` (else the emission is empty: no common location). The
  backward run gives patterns with the tails `$`, `*/E` and `[any]` only (§7.3): the must flag comes from the added
  fact, not from the pattern (Lean: `AnyTaintEx.emitX`, `emitTX`; the vectors `AnyTaintEx.Vec.emit_at`,
  `emit_above_excluded`, `emit_above_exact`, and the table without exclusions `AnyTaint.EmitVec`).
* THE ZERO DEMAND. `(zero, none)` is part of the demand of EVERY method key, also when the demand store has no entry
  for it. So the zero added fact always emits the zero fact. The zero fact of a root is an initial fact.
* BACKWARD RUN. As a restricted run. Also, `addZeroEntry` makes the zero fact an initial fact (rule `zin`).
* `initials.add` deduplicates. Each new initial fact starts with its start fact (`ap.md` §6.5) at every start node of
  its kind, then the start rules. The start fact of a must-premise `(x, p, [any-taint], E, T)` is the premise itself,
  `(x, p, [any-taint], E, T)`, in the normal layer (a forward restricted run only: the backward run has no
  must-premise). Its edges are END-EXACT (`ap.md` §1; Lean: `AnyTaintEx.startX`; `AnyTaintExExact.startX_must_end`).

Start nodes, end nodes and their rules. The interpreter gives the forward ones; the backward ones are their reversal
(§4.9):

| Direction | Start nodes | Start rules | End nodes | End rules |
|---|---|---|---|---|
| forward | the entry statement of the method key | the ENTRY RULES (`interpreter.md` §4.3): the zero fact with the entry sinks and the entry-point sources; another fact with the filter by the context type | every normal exit | the EXIT RULES (`interpreter.md` §4.7). The exit rules also apply at an exceptional exit, with `Result` read as `exc`, but it is not an end node: no summary |
| backward | the zero fact: every forward exit, normal and exceptional (`ap.md` S4). Another initial fact: every normal exit (exceptions are out of scope, `interpreter.md` G1) | the reversed exit rules of that exit (normal or exceptional): the reversed exit sources and end-fact edges; and the sink seeds of its exit sinks (§4.7), which then take the reversed exit sources of that exit too (`interpreter.md` §4.9 SEEDS) | the forward entry statement | the reversed entry rules: the reversed entry-point sources and end-fact edges (no context filter: the backward run has no type filter) |

The exits: the normal exit is `JMethodExitNormalInst`; the exceptional exit is `JMethodExitExceptionalInst`.

THE BOUNDARY RULE STATEMENTS. The entry rules and the exit rules are rule statements in the STATEMENT mode (§4.9). Their
touched bases and keep edges are those of `interpreter.md` §4.3 and §4.7 (`ap-impl.md` §29, `keep`): the zero base with
its keep edge; at the exit, each base that a literal of an exit source reads, with the identity edge `b.* → b.*`; at the
start, each base with a context filter, with the identity edge and that filter as its operand filter. A source target
is a gen-only target (not touched). So a fact on a read base stays in the worklist (`interpreter.md` §4.7 step 1), an
initial fact passes unchanged or passes its context filter, and in the backward run a requirement on a read base or on a
target passes.

A CONJUNCTIVE EXIT SOURCE (an exit source with two or more positive literals in one alternative of its condition) is an
ND edge at the exit, as at a call (`interpreter.md` §4.7 step 1, D31; `ap-history.md` F68). It is a `ConjunctiveEdge`
of the exit rules (`RuleStatement.summary.conjunctions`, §4.9). Each literal stores its input in the conjunction store of
the method key, per (edge, exit statement, literal index) (`ap.md` §8.9). A full combination is an exit item with the
union of the premise sets (without the zero fact, `ap.md` §4.6), after the field limit. It goes through the exit steps 2
to 5 (`interpreter.md` §4.7) and becomes a summary at the normal exit, an ND summary if its premise set has two or more
members; the callers apply it by E6 (§5.4). At the exceptional exit it goes through step 2 only and ends there (§4.3).
It is not a rule error. The backward run reverses it into one micro edge per literal (`StatementSummary.reversed`,
§4.9).

The backward graph is the reversed graph (`ApplicationGraph.reversed`) with the EXIT WIRING. A node that reaches no
forward exit gets an edge to an exceptional exit (`interpreter.md` I11 (e); today `JIRBackwardExitWiringGraph` on
`saloed/backward-main`). Only the zero fact uses an exceptional exit. The `MethodContextCache` keeps the wired graph per
method (today the code computes the wiring again on every call).

AN EMPTY METHOD (no instruction: a native method, an abstract method, a method with no body) cannot be analysed. The
core never analyses it: it has no method key, no method analyzer and no `SummaryStorage`, and it is never a root. The
call resolver never resolves a call to an empty method: it drops the empty method from the callees of the call (§4.5).
So a call with an empty and a non-empty resolution result enters only the non-empty callee, and a flow through the empty
target is lost (`interpreter.md` G12). If every resolution result of a call is an empty method, the call is an
UNRESOLVED call (`interpreter.md` §3.7: the pass rules and the default identity). This is a decision (`ap-history.md`
F67). Today `EmptyMethodAnalyzer` publishes the identity summaries of the most abstract facts.

### 4.5 The call plan

A call is a small graph: six POINTS and the STAGES between them. This is the CALL PLAN. The interpreter gives the
FORWARD plan (`interpreter.md` §4.5, §4.6). The backward plan is its REVERSAL (`CallPlan.reversed`, §4.9). It gives the
backward call order of `interpreter.md` §4.9 step by step, so the analyzer runs one algorithm in both directions.

| Point | Coordinates | Content in the forward plan |
|---|---|---|
| `BEFORE` | caller | the caller fact before the call |
| `BOUND` | callee | the bound fact, before the cleaners; the RULE POINT of the call (its sinks) |
| `ADDED` | callee | the added fact: the entry of the callee |
| `RETURNED` | callee | a result of the callee: a summary result or an unresolved result |
| `REWRITTEN` | callee | a result after the summary rewriter |
| `AFTER` | caller | the result in the caller, before the field limit |

The forward stages of a JVM call `r = m(o, a1, …, an)` (the step numbers of `interpreter.md` §4.5):

| Stage | Forward | Content | Step |
|---|---|---|---|
| binding in | `BEFORE → BOUND` | the binding edges into the callee (with the zero binding), with the caller-side type filters (`interpreter.md` §3.1) | 2 |
| end facts | `BOUND → REWRITTEN` | the end-fact edges of the sinks of the call; GUARD: the sink triggers. It takes no input fact (THE END-FACT STAGE, below) | 3 |
| sources | `BOUND → REWRITTEN` | the rule statement of the call: the sources and the conjunctions (`interpreter.md` §4.1) | 4 |
| cleaners | `BOUND → ADDED` | the cleaners and the `RemoveAllMarks` kill on `S`, in the rule order | 5.1 |
| callees | `ADDED → RETURNED` | the resolved callees (with the lambdas of the prescan), never an empty method (§4.4): SUBSCRIBE and LINK (below) | 5.2 |
| unresolved | `ADDED → RETURNED` | the statement summary of the unresolved callee (`interpreter.md` §3.7); also of a call whose every resolution result is an empty method (§4.4) | 5.3 |
| constructor | `ADDED → REWRITTEN` | JVM `<init>`: the identity of every bound position (`S`, the receiver, the arguments); it skips the callee and the rewriter (`interpreter.md` §3.5) | 5.2 |
| rewriter | `RETURNED → REWRITTEN` | the summary rewriter (`interpreter.md` §5.2) | 6 |
| binding back | `REWRITTEN → AFTER` | the binding edges back, with the result-side type filters | 6 |
| aliases | `REWRITTEN → AFTER` | the alias edges `P.* → b.q.*` (`interpreter.md` §3.8 AC2); GUARD: the selection of AC3 and AC4 (THE ALIAS GUARD, below) | 6 |

The plan also has its TOUCHED caller bases (`S`, `o`, every `ai`, `r`; step 1) and the SINKS of the call at `BOUND`
(step 3).

HOW THE ANALYZER RUNS A PLAN (both directions):

* A caller fact on a base that the plan does not touch passes over the call (step 1). The zero base is never touched.
* A fact at a point goes through every stage that starts at that point. Each result arrives at the end point of its
  stage. The stages that start at one point read the same facts, so their order does not matter. (So the sinks see
  the uncleaned bound fact, as `interpreter.md` §4.5 asks.)
* An `Edges` stage applies its summary in the STAGE mode (§4.9 THE APPLICATION MODES): only its edges give results.
  The touched bases of the plan do the pass-over (step 1). The kill on `S` in the cleaners stage applies in the
  STATEMENT mode.
* A fact at the exit point of the plan gets the field limit and goes to the return node of the call.
* The callees stage is not local: SUBSCRIBE and LINK, and its results arrive later through `applySummary` and
  `applyRecord`, at its end point.
* At the rule point `BOUND`, the forward run checks the sinks of the call (§4.7). The backward run checks no sink: it
  fires the sink seeds of these sinks there (§4.7).
* The sources stage applies the source seeds (forward restricted run) and records the source hits (backward run) (§4.7).

THE END-FACT STAGE (`BOUND → REWRITTEN`) takes no input fact. Its trigger is a sink of the call at `BOUND`: a sink edge
of a plain sink, or a new full combination of a conjunctive sink (§4.7). On a trigger, the analyzer applies the
end-fact edges of that sink to the zero fact, in the layer of the sink edge or of the combination (`ap.md` §2.2,
§4.9). Each result is a zero-to-fact edge (premise set `{zero}`), and it arrives at `REWRITTEN`. The same rule holds
for the end facts of the entry sinks and of the exit sinks (§4.4). The backward run has no trigger: the reversed
end-fact edges apply to every requirement (THE REVERSAL, below).

THE ALIAS GUARD (`Guard.MemoryEffect`; `interpreter.md` §3.8 AC3, AC4). Each forward result at `REWRITTEN` has an
ORIGIN (`Origin`, §4.9): the stage that made it. The sources stage gives SOURCE, the end-fact stage END_FACT, a pass
rule of the unresolved stage PASS. The default identity of the unresolved stage and the constructor stage give
IDENTITY. A summary result or a record result (the callees stage) is an IDENTITY only in one case: it is in the NORMAL
layer, and it is equal to the start fact of its premise (`ap.md` §6.5). Every other summary result has a memory effect
(SUMMARY_EFFECT): a DEMAND-layer result always goes to the aliases, and so does every result of a zero-premise
summary (`ap-history.md` F67). The cleaners and the rewriter keep the origin of their input. The alias stage takes
every result whose origin is not IDENTITY.

THE REVERSAL (`CallPlan.reversed`; the rules of `ap.md` §9.1, §9.2):

* The entry point and the exit point change places (backward: `AFTER` is the entry, `BEFORE` the exit). Each stage goes
  from its forward end point to its forward start point.
* A micro-edge stage gets the reversed summary (`StatementSummary.reversed`, §4.9).
* A GUARD is a forward-only selection, so the reversal drops it: the reversed alias edges apply to every requirement
  (`interpreter.md` AC5), and the reversed end-fact edges too. The reversal also drops every type filter.
* The cleaners, the kill and the rewriter stay the same: a cleaner and a keep edge are their own reversal.
* The callees stage stays the same: in the backward run it gives the backward summaries.
* The sinks stay at `BOUND`.
* The touched bases: the forward touched bases and the alias bases (the target bases of a stage that ends at the
  forward exit and that the forward plan does not touch). Forward, an alias base passes over the call. Backward, its
  requirement passes over by the PASS-OVER stage `AFTER → BEFORE` (kind `PASS_OVER`, §4.9), with the identity edge
  `b.* → b.*` of each alias base (`interpreter.md` A5). This stage is the exact reversal of the forward pass-over. A
  target base that the forward plan touches (an argument, `S`) gets no pass-over.

The reversed plan is the backward call order of `interpreter.md` §4.9:

| Backward step (`interpreter.md` §4.9) | Reversed stage |
|---|---|
| 1 relevance | the reversed touched bases |
| 1 the pass-over of the alias bases that the forward plan does not touch | `AFTER → BEFORE` |
| 2 reversed binding back and alias edges | `AFTER → REWRITTEN` |
| 3 reversed sources and end-fact edges; their results arrive at step 7 | `REWRITTEN → BOUND` |
| 4 reversed rewriter | `REWRITTEN → RETURNED` |
| 5.1 resolved callees | `RETURNED → ADDED` |
| 5.2 unresolved callee | `RETURNED → ADDED` |
| 5.3 JVM constructor: from step 2 to step 6 | `REWRITTEN → ADDED` |
| 6 reversed cleaners and the keep edges of the kill | `ADDED → BOUND` |
| 7 the seeds and the read positions | the rule point `BOUND` |
| 8 reversed binding in | `BOUND → BEFORE` |
| 9 the field limit | the exit point `BEFORE` |

The core reverses only a forward plan. The reversal is not an involution: it drops the guards and the filters, and it
adds identity edges.

SUBSCRIBE: the analyzer gives the subscription `(caller edge, s, a)` for the callee `m` to the `SubscriptionManager`
of its runner (§5.3). The replay applies the publications of `m` that `a` satisfies, and the records of `m` that apply
to `a`.

LINK: the analyzer sends the link `(a, caller edge)` to `m`. For `m` in another unit, it sends the event `LinkIn`. For
`m` in the same unit, it may call `m.addLink` directly (as today `submitMethodInitialFact`; §6.1 permits it).

The zero fact at a call. The zero base is not touched, so the zero fact passes over the call in both directions (rule
`zpass` in the backward run). It also acts at the rule point:

* forward: the zero binding takes it to `BOUND`. There the unconditional sinks fire, and the sources stage fires on it
  (in a forward restricted run, only the source seeds, §4.7). No cleaner acts on the zero base, so it goes on to
  `ADDED` and enters every resolved callee: a subscription and a link;
* backward: the zero fact at the call fires the sink seeds at `BOUND` (§4.7); they go on through the reversed binding
  in. The analyzer adds a ZERO SUBSCRIPTION for each resolved callee `m` (it matches the zero-premise publications of
  `m`, §5.3) and sends `ZeroIn` to `m` (rule `zin`). A zero-premise publication applies to the zero fact of the caller
  with no test (rule `zret`). Its results arrive at `ADDED`, the end point of the reversed callees stage.

### 4.6 Summary edges, publications and requests

At an end node of the run, after the end rules, each new delta `j → g` (a summary delta, event E4):

1. goes to `summaries` (the run summary store), with no restriction;
2. gives the publications:
   * run 1: `j → g` itself;
   * a restricted forward run, and a backward summary whose premise set is not `{zero}`: `restrict(j, g, d)` for each
     demand pattern `d` that the restriction query returns (`ap.md` §6.4, §8.6). Each non-null result is published
     once. The query is `near(j.base :: j.path)`. For a premise set with several members, it is the union of `near`
     over the members;
   * a backward summary with the premise set `{zero}`: `j → g` itself, with no restriction (`ap.md` §6.4);

   A publication carries the premise key of `j` with the tail of each member and the exclusion of an `[any-taint]`
   member, so the summaries of an `[any-taint]` premise and of an `[any]` premise of one path are different
   publications (§4.1). The restriction does not change the premise. It reads the exclusion of an `[any-taint]/E`
   conclusion as part of its location set: a conclusion above `D-p` gives the chain `D-p` with no exclusion only if
   `E` admits the step down (`ap.md` §6.4). Lean: the object `pub m j mj jex g` of `PipelineAnyTaintEx.sysDRX`
   carries the must flag `mj` and the exclusion `jex`; `AnyTaintEx.restrictX`;
3. goes to `pendingPublications`.

The analyzer gives `pendingPublications` to its `SummaryStorage` (§5.2) before its `Work` event ends (§6.2, W3), as
today `flushPendingSummaryEdges` does.

Requests (run 1 only; `ap.md` §4.5, §4.10, §8.8):

* A rule that raises a request `(m, i, T)` or `(m, i, p)` in this method adds it to `requests` (E5, E7).
* A new request reads every link that overlaps it. A new link reads every standing request that overlaps its added
  fact. Both use the overlap query of `ap.md` §8.8.
* For each (request, link) pair, the rule of `ap.md` §4.5 (mark) or of §4.10 items 2 to 4 (position, static premise)
  gives one of three actions:
  * ANSWER: a new initial fact of this method;
  * CLIMB: send `RequestIn` to the caller of the link, with the caller premise;
  * nothing: the added fact has another concrete mark or excludes the mark; or, for a position request, the added
    fact is above the position and the caller premise is not on `S`.
* Both sides of this join are in one analyzer, so one handler sees both. The join needs no protocol.
* In a restricted run a request is an error (assert; `ap.md` §6.1 rule 4).

### 4.7 Sinks, vulnerabilities, seeds and source hits

* A triggered sink adds its WITNESS to the `VulnerabilityStore` under the VULNERABILITY KEY `(rule, method,
  statement)` (`ap.md` §8.10). `method` is the method of the method key, WITHOUT the context. So one sink statement
  that the analysis reaches in several contexts is ONE vulnerability (`ap-history.md` F67). A witness is one sink edge,
  or the sink edge set of a conjunctive sink. Each witness names its sink ALTERNATIVE (`SinkRule.alternative`, §4.9),
  its METHOD KEY and its RUN. The confirmation of a witness reads the support of its premise set in its own method key
  (§7.5).
* The store keeps several witnesses for one vulnerability key: one entry per (vulnerability key, alternative, method
  key, run, shape). The SHAPE of a witness is the list of the premise set, the layer and the group key of the facts
  (`ap.md` §8.1: the base, the kind and the layer) of each of its sink edges. Two witnesses of one entry merge their
  sink facts. The confirmation reads only the method key, the premise sets and the layers, so this merge changes no
  confirmation. Witnesses of different alternatives or of different method keys never merge, so a merge never joins
  two group keys at one literal.
* A conjunctive sink uses the conjunction store, per (sink alternative, statement, literal index). Each sink edge set
  is one witness (`ap.md` §4.9).
* THE GLOBAL-STATE RULE (exit sinks; `interpreter.md` §4.7 step 3, D30). At a normal exit, the analyzer drops the
  EVALUATED statics of a ZERO-PREMISE item: if a part of an item on the static base `S` whose premise is the zero fact
  (a state that the method or its callees set) satisfies a mark literal (`ContainsMark`, `ContainsMarkOnAnyField`) of
  an exit sink, plain or conjunctive, the analyzer drops that part from the summary edge. The rest of the item stays.
  For a conjunctive exit sink, the analyzer also stores the evaluated part as the input of that literal in the
  conjunction store. A stored input is an assumption for the later evaluations of the sink: a later item can complete
  the combination with it. The analyzer drops the part also when the combination is not complete (`ap-history.md`
  F67).
* A CALLER-SET `S` FACT (an item on `S` whose premise is not the zero fact) is evaluated: it can report
  (`interpreter.md` D21), and a conjunctive literal stores it as an input. The analyzer does not drop it: it returns to
  the caller through the callee summary, in run 1 also through the FLOW summary and its record (§7.4 THE STATIC BASE)
  (`ap-history.md` F68). As today: today's exit sinks run only on zero-premise edges
  (`JIRMethodExitRuleProvider.kt:18-19`), and only a reached sink drops (`JIRSequentTaintUtil.kt:76-85`). The false
  positives that this keeps (a later sink in the caller sees the state; the exit sink of the caller evaluates it again)
  are expected (`interpreter.md` G2, `ap.md` §11.1).
* SEEDS. After run 1, every run has seeds. The driver gives a `SeedIndex` per (method key, statement):
  * a backward run: the SINK SEEDS, the requirements of the vulnerabilities that the forward run before reported
    (`ap.md` §9.2). A sink pattern gives one requirement. A conjunctive sink gives one requirement per positive
    literal. An unconditional sink gives none. The requirement of an `[any]` sink pattern (`ContainsMarkOnAnyField`)
    has the tail `[any]`: the backward run has no `[any-taint]` (`ap.md` W8, §9.2), so its seed is in the demand
    layer (`ap.md` W6), as before F69. The seeds of a witness are at its method key and its statement;
  * a forward restricted run: the SOURCE SEEDS, the unconditional sources that the backward run before reached
    (`ap.md` §6.1 rule 6, §8.11).
* A sink seed enters as a zero-to-fact edge where the zero fact reaches its statement, cut by the field limit. A call
  sink seeds at the rule point `BOUND` of the reversed plan (§4.5). An exit sink seeds in the start rules (§4.4).
* A source seed is a filter on the SOURCES: the micro edges whose forward form (`MicroEdge.forward`, §4.9) goes from
  the zero fact to another base. In a forward restricted run, the analyzer applies a source only if `SeedIndex` has
  its forward form for that (method key, statement). The sources are at a statement (a read source, an exit source),
  in the sources stage of a call (§4.5) and in the entry and exit rules. The end facts of a sink and every other micro
  edge apply as usual.
* SOURCE HITS (backward run). When the analyzer applies a reversed source to a requirement and gets a result, it adds
  `(method key, statement, forward form)` to `sourceHits` (`ap.md` §8.11). This holds at each place of a reversed
  source: a statement, the reversed sources stage of a call (§4.5), and the reversed exit and entry rules (§4.4). The
  analyzer records the hit whatever `edges.add` gives: also when the store drops the zero result as a duplicate.
* The backward run has no sink check.

### 4.8 The method context

Today `JIRMethodAnalysisContext` holds the alias analysis, the local-variable reachability, the lambda resolutions,
the flow-function caches and the taint rule context. The new core splits it:

* the CACHED part, in `MethodContextCache`:
  * per method: the method graph, the alias analysis (with its own inputs, as today: the local-variable reachability is
    one of them; the core does not read it, §4.3), the lambda resolutions of the prescan and the wired backward graph.
    Every context of the method shares them (today the `EmptyMethodContext` twin analyzer does this);
  * per method: the forward forms of the interpreter that do not read the context of a method key, with their
    reversals (§4.9): the statement summaries and the exit rules (the entry marks of the exit rules come from the
    entry-point sources, which read no context);
  * per METHOD KEY (with its context): the forward forms that read the context, with their reversals: the call plans
    (the callees: the resolver reads the type constraints of the context, `interpreter.md` §3.6) and the entry rules
    (the start filter by the context type, `interpreter.md` §4.3). So a second context of a method never takes the
    callees or the start filter of the first one (`ap-impl.md` DD11);
* the RUN part, made by the run: the rule context bound to the run (the `VulnerabilityStore`, the conjunction store,
  the run mode).

Runs are sequential, so in each run the runner of the method is the only user of its cache entry. This removes the
double construction of the context that `saloed/backward-main` has.

### 4.9 The interpreter interface and the reversal

The interpreter (`interpreter.md`) gives the FORWARD semantics only. The core calls it only through this interface,
and the core makes every backward form by a reversal. The core owns the order of the actions; the interpreter gives
the micro edges and the rules.

```kotlin
interface Interpreter {
    /** §4.4: the forward entry statement, and the forward exits (normal and exceptional). A method key is never an
     *  empty method (§4.4), so a method key always has its entry statement. */
    fun entryNode(method: MethodKey): CommonInst
    fun exitNodes(method: MethodKey): List<ExitNode>
    /** interpreter.md §4.3 and §4.7: the entry rules (they read the context: cached per method key, §4.8) and the exit
     *  rules (cached per method). */
    fun entryRules(method: MethodKey): RuleStatement
    fun exitRules(method: MethodKey, exit: CommonInst): ExitRules
    /** interpreter.md I1: the touched bases, the micro edges and the type filters of a non-call statement. */
    fun statementSummary(method: MethodKey, statement: CommonInst): StatementSummary
    /** §4.5: the forward plan of a call. Its callees stage has no empty method; a call whose every resolution result
     *  is an empty method has the unresolved stage (§4.4). The callees read the context of `caller`: cached per method
     *  key (§4.8). */
    fun callPlan(caller: MethodKey, statement: CommonInst, call: CommonCallExpr): CallPlan
    /** a summary edge exists only for these bases (not a local; today isValidMethodExitFact). */
    fun isSummaryBase(base: AccessPathBase): Boolean
}

class ExitNode(val node: CommonInst, val exceptional: Boolean)

/** One micro edge with the forward form of the edge (the edge itself in a forward summary). A SOURCE is an edge
 *  whose forward form goes from the zero fact to another base; the forward form identifies it in both runs (§4.7).
 *  The interpreter gives the target tail `[any-taint]` to a source rule with an `[any]` target (unconditional,
 *  conditional or conjunctive, and an end-fact action; a must); a pass rule with an `[any]` target keeps `[any]` (a
 *  may); a pass rule with an `AnyField` position on its premise side is a rule error (ap.md S15, W6; interpreter.md
 *  I14, D33). A reversed edge keeps its forward form: the backward AP reads its forward target tail, and every result
 *  of an edge whose forward target is `[any]` is in the demand layer (§4.3). No other flag tells the rule kind. */
class MicroEdge(val edge: PathEdge, val forward: PathEdge)

/** interpreter.md I1: a statement summary. The AP applies it (ap.md §4.2). `typeFilters`: the operand filters, on the
 *  input (interpreter.md §2.1 step 3). `resultFilters`: the lhs and binding-back filters, on the results
 *  (interpreter.md §2.1 step 5, §3.1). One base can have both (`x = x.f`), so they are two maps. */
class StatementSummary(val touched: Set<AccessPathBase>, val edges: List<MicroEdge>,
                       val conjunctions: List<ConjunctiveEdge>, val typeFilters: Map<AccessPathBase, TypeFilter>,
                       val resultFilters: Map<AccessPathBase, TypeFilter> = emptyMap()) {
    /** ap.md §9.1, §9.2: each edge reversed; a conjunctive edge gives one edge per literal; the identity edge
     *  `b.* → b.*` for each target base that the summary does not touch (A5); the touched bases with the targets;
     *  no type filter. The reversal gives no `[any-taint]` (ap.md W8, §9.1): the reversal of an `[any]` condition
     *  literal (`ContainsMarkOnAnyField`, also of a conjunctive edge) has the target tail `[any]`, and a forward target
     *  `[any-taint]` becomes the premise `[any]`. Each reversed edge keeps its `forward` form (§4.3). */
    fun reversed(): StatementSummary
}

/** The rules of a method boundary (the entry rules, the exit rules): a statement summary with the sources (STATEMENT
 *  mode; its touched bases and keep edges: §4.4 THE BOUNDARY RULE STATEMENTS, interpreter.md §4.3, §4.7), the end-fact
 *  edges of its sinks (GEN mode) and the sinks. At an exit, `summary.conjunctions` holds the conjunctive exit sources,
 *  an ND edge at the exit (§4.4). The reversal reverses the summary, keeps the sinks as the place of the sink seeds and
 *  drops the context filter. */
class RuleStatement(val summary: StatementSummary, val endFacts: StatementSummary, val sinks: List<SinkRule>) {
    fun reversed(): RuleStatement
}

/** The exit rules (interpreter.md §4.7) and, forward only, the global-state drop (step 3: the analyzer drops the part
 *  of a zero-premise `S` item that satisfies a mark literal of an exit sink, and stores it as the input of that literal
 *  of a conjunctive exit sink; a caller-set `S` item is evaluated, not dropped, §4.7) and the removal of the entry marks
 *  of a zero-premise fact (step 4: every leaf with an entry mark, at any depth, of a zero-premise fact on `this` or
 *  `arg(i)`, also an `[any-taint]` leaf with its exclusion; a deviation from today, which removes only the root leaf:
 *  interpreter.md D35). The reversal drops the two removals (interpreter.md §4.9). */
class ExitRules(val rules: RuleStatement, val globalStateDrop: Boolean, val entryMarks: Set<TaintMark>) {
    fun reversed(): RuleStatement
}

/** ap.md §4.9: one ALTERNATIVE of one sink rule at one place (one DNF cube with one array choice; interpreter.md
 *  §4.1, §4.2). `alternative`: its index among the alternatives of the rule at the place; the same in every run and
 *  every context (interpreter.md I5). `patterns`: one per positive literal; two or more make a conjunctive sink; the
 *  zero pattern makes an unconditional sink. A `ContainsMarkOnAnyField` literal is a pattern with the `[any]` tail,
 *  and its sink seed has the tail `[any]` (§4.7). A fact with the `[any-taint]` tail triggers a pattern as an `[any]`
 *  fact does, if the pattern meets a location that its exclusion admits (ap.md §4.9; Lean `AnyTaintEx.checkX`).
 *  `endFacts`: its end-fact edges `zero.$ → P.$ (T)`, or `zero.$ → P.[any-taint] (T)` for an `AnyField` position
 *  (interpreter.md I14) (GEN mode, §4.5). */
class SinkRule(val rule: RuleId, val alternative: Int, val patterns: List<Pattern>, val endFacts: List<MicroEdge>)

/** ap.md §4.6: a conjunctive micro edge `x1.ρ1.t1(T1) ∧ … ∧ xk.ρk.tk(Tk) → z.π.t(T)`, k >= 2: an ND source
 *  (interpreter.md §5.3): in the sources stage of a call (§4.5), or at an exit (§4.4). Each literal and the
 *  target have a concrete mark and no `*` tail (S9, W7). The `[any]` target of a conjunctive source is
 *  `[any-taint]` (ap.md §4.6, S15). A literal reads the exclusion of an `[any-taint]/E` input as part of its location
 *  set (ap.md §4.6). */
class ConjunctiveEdge(val literals: List<Pattern>, val target: PathFact)

/** ap.md §4.8: the type filter `filter(b, may)` of one base; `may` is prefix-closed (S5; today a
 *  `FactTypeChecker.FactApFilter`). `markPolicy`: the primitive mark policy of interpreter.md §5.1, or null (no level
 *  of the static type is primitive or boxed). */
class TypeFilter(val may: FactApFilter, val markPolicy: MarkPolicy? = null)

/** interpreter.md §5.1 `markPolicyKeeps`: keeps `mark` on the value at `[e]^elements` below the base (`elements = 0`:
 *  the base itself; `elements = k`: the k-th element type). A leaf below a field or a class accessor has no policy. */
fun interface MarkPolicy { fun keeps(mark: TaintMark, elements: Int): Boolean }

/** ap.md §4.7: the cleaner `clean(position, reach, mark)` (interpreter.md §5.2); `mark == null`: every mark. Never on
 *  the zero base. */
class Cleaner(val base: AccessPathBase, val path: PathNode?, val reach: CleanReach, val mark: TaintMark?)
enum class CleanReach { EXACT, BELOW, AT_AND_BELOW }

/** One step of the cleaners stage, in the rule order: a cleaner, or the `RemoveAllMarks` kill on `S` (a statement
 *  summary of keep edges, not a cleaner; interpreter.md §1.4, I12 (e)). Each one is its own reversal. */
sealed interface CleanStep {
    class Clean(val cleaner: Cleaner) : CleanStep
    class Kill(val keepEdges: StatementSummary) : CleanStep
}

enum class CallPoint { BEFORE, BOUND, ADDED, RETURNED, REWRITTEN, AFTER }

/** interpreter.md §3.8 AC3, AC4: where a forward result at REWRITTEN comes from (§4.5 THE ALIAS GUARD). */
enum class Origin { SOURCE, END_FACT, PASS, SUMMARY_EFFECT, IDENTITY }

/** A forward-only selection of the inputs of a stage (§4.5). The reversal drops it. */
sealed interface Guard {
    /** The end-fact stage: it applies on a trigger of `sink`, to the zero fact (§4.5 THE END-FACT STAGE). */
    class SinkTriggered(val sink: SinkRule) : Guard
    /** The alias stage: every result whose origin is not IDENTITY (§4.5 THE ALIAS GUARD). */
    data object MemoryEffect : Guard { fun admits(o: Origin): Boolean = o != Origin.IDENTITY }
}

/** The kind of an `Edges` stage (ap-impl.md §23.5). SOURCES and UNRESOLVED hold statement micro edges: the static
 *  exception of run 1 acts on them (THE APPLICATION MODES, below). The source seeds and the source hits act on SOURCES
 *  (§4.7). PASS_OVER: reversed plans only, the identity of the alias bases (§4.5 THE REVERSAL). */
enum class StageKind { BIND_IN, END_FACTS, SOURCES, UNRESOLVED, CONSTRUCTOR, BIND_BACK, ALIASES, PASS_OVER }

/** One stage of a call plan (§4.5): it takes the facts at `from` to `to`. */
sealed interface CallStage {
    val from: CallPoint
    val to: CallPoint
    fun reversed(): CallStage
    /** A binding, the sources, the end facts, the unresolved summary, the constructor identity, the aliases, and (in a
     *  reversed plan only) the pass-over of the alias bases (STAGE mode; `kind`). A guard is a forward-only selection
     *  of the inputs (the sink trigger, AC3 and AC4); the reversal drops it. */
    data class Edges(override val from: CallPoint, override val to: CallPoint, val kind: StageKind,
                     val summary: StatementSummary, val guard: Guard? = null) : CallStage
    data class Clean(override val from: CallPoint, override val to: CallPoint, val steps: List<CleanStep>) : CallStage
    data class Rewrite(override val from: CallPoint, override val to: CallPoint, val cleaners: List<Cleaner>) : CallStage
    data class Callees(override val from: CallPoint, override val to: CallPoint, val callees: List<MethodKey>) : CallStage
}

/** §4.5: the plan of one call. The interpreter gives the forward plan: entry BEFORE, exit AFTER. */
class CallPlan(val touched: Set<AccessPathBase>, val stages: List<CallStage>, val sinks: List<SinkRule>,
               val entry: CallPoint, val exit: CallPoint) {
    /** §4.5 THE REVERSAL: also the PASS_OVER stage `AFTER → BEFORE` of the alias bases. */
    fun reversed(): CallPlan
}
```

What the core uses in each direction:

| Place | Forward | Backward |
|---|---|---|
| start nodes | `entryNode` | `exitNodes` (the zero fact at every one; another fact at the normal ones) |
| start rules | `entryRules` | `exitRules(…).reversed()` and the sink seeds of the exit sinks |
| a non-call statement | `statementSummary` | `statementSummary(…).reversed()` |
| a call | `callPlan` | `callPlan(…).reversed()` |
| end nodes | the normal `exitNodes` | `entryNode` |
| end rules | `exitRules` | `entryRules(…).reversed()` |

A reversal of a statement summary is `Reverse.Stmt.rev` of the Lean model; the reversal of the bindings is
`Reverse.Call.rev`. The core caches the forward forms and their reversals in the `MethodContextCache` (§4.8): per
(method, statement) for a statement summary and the exit rules; per (method key, statement) for a call plan; per method
key for the entry rules. The
AP operations of `ap.md` §4 apply the micro edges; the interpreter never applies them. `PathFact`, `Pattern` and
`PathEdge` are the types of `ap.md` §3.4 and §4.1. `SinkRule`, `ConjunctiveEdge`, `TypeFilter` and `Cleaner` (above)
are the short forms of the sink of `ap.md` §4.9, the conjunctive edge of §4.6, the type filter of §4.8 and the cleaner
of §4.7.

THE APPLICATION MODES. The core applies a `StatementSummary` in one of three modes. The place of the form gives the
mode, not a field of the form:

| Mode | Forms | Rule |
|---|---|---|
| STATEMENT | a statement summary (`statementSummary`), the rule summary of a method boundary (`RuleStatement.summary`, with the touched bases and keep edges of §4.4 THE BOUNDARY RULE STATEMENTS), the kill on `S` (`CleanStep.Kill.keepEdges`) | `interpreter.md` §2.1 steps 2 to 5: a fact on an untouched base passes; a fact on a touched base keeps only what an edge gives |
| STAGE | the summary of a call stage (`CallStage.Edges.summary`) | only the edges give results. The touched bases of the plan (`CallPlan.touched`) do the pass-over (§4.5). A stage summary has every base of its edges in its touched set, so its reversal adds no identity edge (the reversed plan has the PASS_OVER stage of the alias bases instead, §4.5) |
| GEN | the end-fact edges at the method boundaries (`RuleStatement.endFacts`, the `SinkRule.endFacts` of an entry or exit sink) | the input stays where it is; the edges add results (`interpreter.md` §4.1 END FACTS, §4.7 step 2). An end-fact edge reads the zero fact: on a trigger of its sink, it applies to the zero fact in the layer of the sink edge or of the combination (§4.5 THE END-FACT STAGE). At a call the end facts are the end-fact `Edges` stage (`END_FACTS`, STAGE mode, on the zero fact, on a trigger, §4.5), whose reversal adds no identity |

THE STATIC EXCEPTION. In run 1 the static exception of `ap.md` §4.10 item 1 acts on the statement micro edges: the
statement summaries, the edges of the sources and the unresolved stages of a call (`StageKind.SOURCES`, `UNRESOLVED`),
the kill on `S` and the boundary rule statements. At a call it is tested on the caller edge. It acts on no other stage.

---

## 5. The communication pipeline

### 5.1 Events and channels

Each runner has one channel and one local priority queue, as today. The events:

| Event | Goes to the channel of | Handler | `ap.md` | From today |
|---|---|---|---|---|
| `Start(root)` | the runner of `root` (sent by the driver) | `addRootZero` | §6.1 | the `MethodWithContext` start event |
| `LinkIn(callee, link)` | the runner of `callee` | `addLink` | E1, E2 | `ExternalInputFact.InputFact` |
| `ZeroIn(callee)` | the runner of `callee` (backward) | `addZeroEntry` | §9.2 `zin` | `ExternalInputFact.InputZero` |
| `RequestIn(method, premise, request)` | the runner of `method` (the caller; run 1) | `addRequest` | E5, E7 | replaces the side-effect channels |
| `Delivery(callee, publications)` | the SUBSCRIBED runner; the publisher's thread sends it | `SubscriptionManager.onDelivery` | E4 | `NewSummaryEdgeEvent` |
| `Work(analyzer)` | the runner of the analyzer (its local queue) | `step` | | the `MethodAnalyzer` event |

Removed:

* the side-effect requirements and summaries, and the mark-unfold requests (`TaintMarkFieldUnfoldRequest`): the
  requests of run 1 replace them (§4.6);
* the delayed-analysis events (`MethodAnalysisDelayed`, `DelayedAnalysisResume`): the field limit replaces them;
* `LambdaResolvedEvent`: the prescan resolves every lambda before run 1 (§9). The call plan reads the lambdas from the
  context cache.

Rules:

* E-1. A handler sends events only through the channels, or by the direct calls that §6.1 permits.
* E-2. Every link carries its caller reference `(caller method key, caller premise key, caller layer, call statement)`.
  The callee needs it to climb a request (§4.6) and to compute the support (§7.5).
* E-3. Duplicates are permitted. `links.add`, `requests.add`, `initials.add` and the subscription insert drop only an
  equal item. `edges.add` also drops a conclusion that a stored conclusion subsumes (`ap.md` §8.1).

### 5.2 The storage with subscription (callee side)

One `SummaryStorage` per method key of the run (O2). It keeps the publications in a path trie keyed by
`base :: premise path`, one entry per member of a premise set, and the list of the subscribed runners. An entry keeps
the tail of its member and the exclusion of an `[any-taint]` member: an `[any-taint]` premise and an `[any]` premise at
one path are two entries (§4.1).

```kotlin
class SummaryStorage(val method: MethodKey) {
    private val lock = Any()
    private val published = PublicationIndex()                  // path trie, ap.md §8; delta on insert (T4)
    private val subscribers = ConcurrentLinkedQueue<SubscriptionManager>()

    /** Only the runner of `method` calls it. P2: insert, then notify. */
    fun publish(pubs: List<Publication>) {
        val delta = synchronized(lock) { published.addAll(pubs) }            // the new part only
        if (delta.isEmpty()) return
        for (s in subscribers) s.notify(method, delta)                         // one Delivery per runner
    }

    fun addSubscriber(s: SubscriptionManager) { subscribers.add(s) }

    /** P3: a linearizable read. The candidates for the added fact `a`; complete for `matches` (§5.3). */
    fun candidates(a: Pattern, config: RunConfig): List<Publication> =
        synchronized(lock) { published.candidates(a, config) }
}
```

P3 asks for the lock on the read (Appendix A gives the defect of today). An implementation may replace the lock by an
immutable snapshot that the writer publishes with a volatile write.

### 5.3 The subscription manager (caller side)

One `SubscriptionManager` per runner. Per callee, it keeps the subscriptions of the unit in a path trie keyed by
`base :: added fact path` (`ap.md` §8.4).

```kotlin
class SubscriptionManager(private val runner: UnitRunner, private val config: RunConfig) {
    private val byCallee = HashMap<MethodKey, CalleeSubscriptions>()       // runner-local (O3)

    /** §4.5 SUBSCRIBE. */
    fun subscribe(sub: Subscription) {
        val storage = runner.summaryStorage(sub.callee)                    // O2: any unit
        val entry = byCallee.getOrPut(sub.callee) {
            CalleeSubscriptions().also { storage.addSubscriber(this) }       // P1: register the handler first
        }
        if (!entry.add(sub)) return                                          // an equal subscription: no replay
        val analyzer = runner.analyzer(sub.caller)
        for (pub in storage.candidates(sub.addedFact, config))               // P1: read after the registration; P3
            if (matches(sub, pub, config)) analyzer.applySummary(sub, pub)   // P4
        if (sub.zeroOnly) return
        val a = sub.addedFact
        for (rec in config.records.byEntry(sub.callee, a))                   // records: read-only (A4); `around`
            if (rec.direction == config.direction && recordApplies(rec.premise.toPattern(), a))
                analyzer.applyRecord(sub, rec)
        for (rec in config.records.byExit(sub.callee, a))                    // the other direction (ap.md §8.7 R3)
            if (rec.direction != config.direction)
                for (rev in rec.reversedAt(a))                               // one reversal per leaf that byExit returns
                    if (recordApplies(rev.premise.toPattern(), a)) analyzer.applyRecord(sub, rev)
    }

    /** The notification of a callee storage: one Delivery event to the channel of this runner. */
    fun notify(callee: MethodKey, pubs: List<Publication>) = runner.send(Delivery(callee, pubs))

    /** The handler of a Delivery. P6: match against the subscriptions NOW. */
    fun onDelivery(callee: MethodKey, pubs: List<Publication>) {
        val entry = byCallee[callee] ?: return
        for (pub in pubs)
            for (sub in entry.candidates(pub, config))                       // complete for `matches`
                if (matches(sub, pub, config)) runner.analyzer(sub.caller).applySummary(sub, pub)  // P4
    }
}

/** P4: the ONE match function of the replay and of the delivery (ap.md §4.3). */
fun matches(sub: Subscription, pub: Publication, config: RunConfig): Boolean {
    val premise = pub.premise                                                // PremiseKey, ap.md §7.1
    if (sub.zeroOnly) return premise.isZero                                  // backward rule zret: no test
    return (0 until premise.size).any { k ->                                 // one member; several members: §5.4
        satisfies(premise.member(k).toPattern(), sub.addedFact, config.restricted)   // ap.md §6.3 `satisfies`
    }
}

/** ap.md §8.7 R4, Lean `DR.retRec`: a record applies by `applicable` or by `inside`. A record with an `[any-taint]`
 *  premise that only `applicable` accepts gives its results in the demand layer (§4.2 `applyRecord`; Lean
 *  `AnyTaintEx.DRX.retRec` with `recLayerX`). In a restricted run `inside` reads the exclusions of both sides
 *  (ap.md §4.3; Lean `AnyTaintEx.satX`). */
fun recordApplies(p: Pattern, a: Pattern): Boolean = applicable(p, a) || inside(p, a)
```

`byEntry` and `byExit` use the lookup `around` (`ap.md` §8.7 R2). `rec.reversedAt(a)` gives the reversal (`ap.md`
§9.1) of each mark-reversible conclusion leaf of `rec` that `byExit` returns for `a`: R3 reverses a record LEAF BY
LEAF (`ap.md` §8.7 R3; the `byExit` index keys each leaf path). Two kinds of leaf have no reversal, and `reversedAt`
gives nothing for them:

* every leaf of a record with an `[any-taint]` premise (a must record): it is END-EXACT only, so its reversal has a
  pair that is not a converse flow, and it is not an exact backward record (Lean `AnyTaintExact.CexRev.cex_rev`);
* an `[any-taint]/E` leaf with `E ≠ {}`: its reversal would need an `[any]` premise with an exclusion, and the
  backward run has none (`ap.md` W8).

The other leaves of the same record reverse as usual (a `$` leaf, a `*/E` leaf, an `[any-taint]` leaf with the empty
exclusion): the premise of such a record has the Empty exclusion (in run 1 the policy premise `*` with `{}`; in a
restricted run a `$` premise, since a normal edge has a `$` premise or a must-premise:
`AnyTaintExKinds.DRXs_normal_premise`), so each leaf that R3 reverses reverses exactly
(`Reverse.rev_exact_of_empty_premise`; `ap.md` §8.7 R3).

The reversal of an `[any-taint]` leaf with the empty exclusion (a leaf `$ → [any-taint]`) has the premise `[any]` in
the backward run (`ap.md` §9.1). It applies only to an `[any]` requirement, which is in the demand layer (W6), so its
results are in the demand layer. It gives no normal backward edge: a reuse limit (§11).

A must-premise needs every location of it, so a summary of an `[any-taint]` premise applies only to an added fact that
the premise lies INSIDE, with the exclusions of both (`ap.md` §4.3; Lean `AnyTaintEx.SatInsideX`: the exactness needs
it, `satX` has it, `AnyTaintEx.satX_inside`). An `[any-taint]` premise occurs only in a forward restricted run, and
there `matches` is `inside`; so `matches` needs no other test. A normal edge of a must-premise is END-EXACT: every
admitted location of its conclusion gets its value from some admitted location of the premise. It is not exact pair
by pair (`AnyTaintEx.EndExactX`; `AnyTaintExact.CexApp.record_not_pair_exact`).

The index queries (`ap.md` §8; keys `base :: path`):

| Test | Replay (publications for a new `a`) | Delivery (subscriptions for a new `j`) |
|---|---|---|
| run 1, `applicable(j, a)`: `a` at or below `j` | `lookupPrefixes(a.base :: a.path)` | `lookupExtensions(j.base :: j.path)` |
| restricted, `inside(j, a)`: `j` at or below `a` | `lookupExtensions(a.base :: a.path)` | `lookupPrefixes(j.base :: j.path)` |
| a record, `applicable` or `inside` | `around(a.base :: a.path)` on `byEntry`, and on `byExit` with the reversed premise as the key | (records are read-only) |

Each lookup returns every entry that its exact test accepts (`PipelineStore.replay_run1`, `deliver_run1`,
`replay_restricted`, `deliver_restricted`, `record_lookup`). Both paths then call `matches`.

The subscription insert deduplicates exactly. It never drops a subscription that a stored subscription subsumes.
Reason: the run-1 test is not monotone in the added fact (a fact above `j` does not satisfy `j`). So a subsumed
subscription can match a publication that the stored one does not match. The same holds for the links.

THE PROTOCOL CONDITIONS. The model step `Step` (§5.5) builds in P1 to P6, A3 and the exact part of E-3 (the
subsumption part is `Pipeline.StepD`, §5.5). P1 to P4 are necessary: each has a counterexample in
`PipelineProofs.lean`, a reachable quiescent state that misses an object of the closure.

| # | Condition | Today | In the model |
|---|---|---|---|
| P1 | REGISTER BEFORE READ: the subscriber registers its handler on the storage before the replay read. | yes (the first `getOrPut` registers) | `proc`; counterexample `PCex.cex_P1` |
| P2 | INSERT BEFORE NOTIFY: the publisher inserts the publication before it reads the handler list. | yes (`addEdges`) | `proc`, `notify`; counterexample `PCex.cex_P2` |
| P3 | LINEARIZABLE READ: the replay read sees every publication whose insert came before it (A2). | not formally (no lock on the read) | `replay`; counterexample `PCex.cex_P3` |
| P4 | ONE MATCH FUNCTION: the replay and the delivery use the same exact test on complete candidate sets. | no (Appendix A) | `replay`, `deliver` both use `join`; counterexample `PCex.cex_P4` |
| P5 | NO REMOVAL: a handler, a subscription and a stored publication stay until the run ends. | yes (`cleanup` runs after the run) | built in: no step removes them |
| P6 | MATCH AT DELIVERY: a delivery matches against the subscriptions of the runner when the runner handles it. | yes (`processMethodSummary`) | `deliver`. The no-loss theorem would also hold with a match at notification time. The code needs P6 because the subscriptions are local to their runner (O3). |

### 5.4 Summaries with several premises (E6)

A publication `{j1, …, jk} → g` (`ap.md` §4.6) reaches the caller by the replay or the delivery like every other
publication. The caller combines it in its conjunction store (`ap.md` §8.9):

* Key: (callee, premise key, layer of the publication, call statement). Value: the merged conclusion that has arrived
  so far, and per premise index `m` the subscriptions at that call statement whose added fact satisfies `jm`.
* A subscription goes under EVERY index that it satisfies. No member is the zero fact (`ap.md` §4.6: a conjunction
  drops the zero fact), so the zero subscription never takes part (`PipelineNDZ.clDNz_ndpub_no_zero`,
  `clDNz_ndpub_zero_sub`; run 1; a restricted run is argued, `ap.md` §11.2). The backward run has no summary with several
  premises: it reverses a conjunction into one micro edge per literal (`ap.md` §9.2).
* A new subscription under an index: combine it with the stored subscriptions of the other indexes (one per index,
  every combination), and apply the stored conclusion to each full combination.
* A new conclusion delta: apply it to every full combination.

The key does not contain the conclusion. So a combination meets every delta of the conclusion, in any order of the
replays and the deliveries. Both sides of this join are in the caller.

### 5.5 The no-loss theorem

THEOREM (never lose a summary edge). Let a reachable state of a well-formed encoded system be quiescent (§6.2). Then:

* every join of processed subscriptions with a processed publication has its result processed
  (`Pipeline.no_lost_join`): the caller has the application of every publication to every subscription that satisfies
  it;
* every object of the closure is processed (`Pipeline.quiescent_complete`): every link reaches its callee, and every
  (request, link) pair for which §4.6 gives an ANSWER or a CLIMB has it.

The model (`Pipeline.lean`) is a rule system with owners (`Sys`). It has LOCAL rules, whose premises all belong to one
actor, and JOINS of subscriptions with a publication. Its closure `Cl` is the concept. The implementation is an
interleaving transition system (`Step`) with these steps:

* `proc`: an actor processes an object and fires its local rules. A subscription registers its handler and schedules
  its replay. A publication is inserted and schedules its notification.
* `replay`, `notify`, `deliver`: the three shared steps of §5.2 and §5.3.
* `dup`: a duplicate is dropped.

The model lets every actor act between the two parts of a subscription and of a publication. A real schedule lets
only the actors of the other runners act there. So every real schedule (A2) is a schedule of the model, and the
theorems hold for every real schedule.

| Theorem | Statement |
|---|---|
| `Pipeline.reach_sound` | every object that a reachable state holds is in `Cl` |
| `Pipeline.quiescent_complete` | for a well-formed system, at a reachable quiescent state, every object of `Cl` is processed |
| `Pipeline.quiescent_exact` | for a well-formed system, at a reachable quiescent state, the processed objects are exactly `Cl` |
| `Pipeline.no_lost_join` | for a well-formed system, at a reachable quiescent state, every join of processed subscriptions with a processed publication has its result processed |
| `Pipeline.PCex.cex_P1` to `cex_P4` | without P1, P2, P3 or P4: a reachable quiescent state that misses an object of `Cl`. In the variants of P1 and P2, the read and the write are two steps. `PCex.step_finds_edge`: the correct protocol finds the object in the same system |
| `PipelineAP.clD_iff`, `clDR_iff`, `clDB_iff`, `clDS_iff`, `clDN_iff` | On the objects of the AP closure, the closure of the encoded system is exactly the AP closure. The closures: run 1 (`D`), a restricted run (`DR`), the backward run (`DB`), run 1 with the static rule (`DS`), run 1 with the conjunctions (`DN`). The partial matches of `DN` are internal to the k-ary join (`clDN_npart`). |
| `PipelineAP.clD_link`, `clD_sub`, `clD_pub` and their `DR`, `DB`, `DS`, `DN` forms | the link, the subscription and the publication objects are exactly the data that the closure rules read |
| `PipelineAP.sysD_wf` and the other `*_wf` | each encoded system is well-formed (`Pipeline.Sys.WF`): every local rule has at least one premise, all of one actor; every join has subscriptions of one actor and one topic and a publication |
| `PipelineNDZ.sysDNz_wf`, `clDNz_iff`, `result_DNz`, the object theorems (`clDNz_link`, `clDNz_sub`, `clDNz_pub`, `clDNz_ndpub`, `clDNz_npart`) | the encoding of the ND closure of the spec, `NDZ.DNz` (the union of the premise sets without the zero fact, `ap.md` §4.6, §10.10): it is well formed, and at a reachable quiescent state the processed objects are exactly `DNz` (no partial match) |
| `PipelineNDZ.clDNz_ndpub_no_zero`, `clDNz_ndpub_zero_sub`, `joinNz_nd_no_zero_sub` | no index of a k-ary join is the zero fact, and (under `NDZeroBase.NoZeroGen` and `AlphaZero`, which the run-1 policy satisfies, `NDZeroBase.policy1_alphaZero`; run 1) the zero subscription satisfies no index (§5.4) |
| `PipelineAnyTaintEx.sysD6X_wf`, `sysDRX_wf`, `clD6X_iff`, `clDRX_iff`, `result_D6X`, `result_DRX`, `result_DRXs`, the object theorems (`clD6X_link`, `clD6X_sub`, `clD6X_pub`, `clDRX_link`, `clDRX_sub`, `clDRX_pub`) | the encodings of the closures of the tail `[any-taint]` with its exclusion (`ap.md` §10.11): run 1 with the layer rules W6 and W8 and the exclusion (`AnyTaintEx.D6X`) and a restricted forward run with must-premises and exclusions (`AnyTaintEx.DRX`; the spec instance `AnyTaintEx.DRXs`). They are well formed, and at a reachable quiescent state the processed objects are exactly the closure, with the must flags and the exclusions (THE ENCODING WITH `[any-taint]`, below). `PipelineAnyTaintEx.SanityX.d6x_ann`, `drx_ann`: a normal `[any-taint]/{name}` edge is in both closures, so the encodings are not vacuous on the exclusion |
| `PipelineAnyTaintEx.known_D6X`, `known_DRX`, `no_lost_summary_D6X`, `no_lost_summary_DRX` | every processed object of a reachable state is in the closure (`Pipeline.reach_sound`), and the summary edge is never lost (`Pipeline.no_lost_join`): in `PipelineAnyTaintEx.sysDRX` a subscription of the caller premise and a publication of the callee premise, each with its must flag and its exclusion, whose join condition holds have their caller edge processed |

The encoding (`PipelineAP.lean`): actor = method, topic = callee.

| AP rule | In the pipeline | Owner of the premises → of the conclusion |
|---|---|---|
| `root` | a root object | → the root method |
| `start`, `step`, `pass`, `clean`, `filt`, `reqStmt`, `reqClean`, `reqSink`, `vuln`, `retRec`, `zpass`, `seed`, `conj`, `reqConj` | local rule | the method → the method |
| `added` | local rule that makes the LINK (a message to the callee); then the local rule `link → added` | caller → callee |
| `initA`, `initR`, `answer`, `sanswer`, `sreqStmt` | local rule | the method → the method |
| `reqUp`, `sreqUp` | local rule on `[request, link]` in the callee; the result goes to the caller | callee → caller |
| `ret` | the caller makes the SUBSCRIPTION, the callee makes the PUBLICATION (after the restriction); their JOIN gives the caller edge | join |
| `sret` | a second join of the same subscription and publication (the overlap reading `Statics.SCtx.fbOK`). The final static rule `Statics.Design` has `fb = off`, so it gives nothing, and `matches` has no test for it | join |
| `zin` | local rule of the caller; the result goes to the callee | caller → callee |
| `zret` | the zero subscription of the caller and the zero-premise publication of the callee; their JOIN | join |
| `ND.DN.ndOpen`, `ndBind`, `ndRet` | a k-ary JOIN: one subscription per premise, all at one call statement, with the publication of the summary | join |

THE ENCODING WITH `[any-taint]` (`PipelineAnyTaintEx.lean`). An edge of `AnyTaintEx.D6X` and of `AnyTaintEx.DRX` has an
annotated conclusion (`AnyTaintEx.XFact`: a fact with its exclusion), so `PipelineAnyTaintEx.sysD6X` and `sysDRX`
have their own objects (`PipelineAnyTaintEx.XPObj6`, `XPObj`) and rules. In `sysD6X` a link carries the added fact
and the exclusion of the bound fact (the request climb reads it; the policy reads only the fact), a subscription
carries the bound fact with its exclusion (the application reads it), and a publication carries the exit fact with
its exclusion. In `sysDRX` the
objects carry the must flags and the exclusions (the must flag is the tail `[any-taint]` of a premise, §4.1). A link
carries the added fact with its flag (`[any-taint]`: an any tail, normal on the link) and its exclusion. A
subscription carries the caller premise with its flag and its exclusion, and the result of its join is an edge of
that premise. A publication carries the callee premise with its flag and its exclusion (two premise keys, §4.6). The
join reads the exclusions (`inside`, `AnyTaintEx.satX`), not the flag of the publication, and the layer of its result
is as in `DR`. The record rule with its demotion (`AnyTaintEx.recLayerX`, §4.2 `applyRecord`) is a local rule of the
caller: the records are read-only (A4). Both are forward runs, so they have no zero subscription and no zero
publication.

THE ZERO PUBLICATION (argued, §11). `PipelineAP.sysDB` has two publications of a zero-premise backward summary: the
restricted one (for `ret`) and the unrestricted `PipelineAP.PObj.zpub` (for `zret`). §4.6 publishes only the
unrestricted one. The two agree because no ordinary subscription satisfies the zero premise: no call binds the zero base
(`ap.md` S11 (c), Lean `Backward.NoZeroBack`). No Lean statement says this, and `Backward.NoZeroBack` is not a
hypothesis of `PipelineDriver.result_DB`. The publication of the code is a superset, so a mismatch could only add
results, never lose them.

So at quiescence the analyzer computes exactly the closure that `ap.md` proves sound and exact, in each mode
(`Pipeline.quiescent_exact` with the `cl*_iff` theorems; `PipelineDriver.result_D`, `result_DR`, `result_DB`). With
conjunctions the closure is `NDZ.DNz`, the ND closure with the zero-drop of `ap.md` §4.6 (`PipelineNDZ.result_DNz`).
With the tail `[any-taint]` the closure of run 1 is `AnyTaintEx.D6X` and the closure of a restricted forward run is
`AnyTaintEx.DRXs` (`PipelineAnyTaintEx.result_D6X`, `result_DRXs`); the backward run is `Backward.DB` as before
(`PipelineAP.sysDB`).
This holds for the rules that the closures have. The end facts (`ap.md` §11.1), the aliases and their guard (`ap.md`
§11.2, S2), and the global-state rule with the entry-mark removal (`interpreter.md` G2, D35) are outside them (§11 THE
ANALYZER ACTIONS OUTSIDE THE CLOSURES).

THE MODEL AND THE CODE. Actor: a `RunMethodAnalyzer`. `known`: the RUN stores of the analyzers, the
`SubscriptionManager` tries and the `SummaryStorage` tries. `inbox`: the channels, the local queues, the worklists,
the `pendingPublications` and a direct call in progress. `store`: the `published` index of each `SummaryStorage`.
`Pipeline.St.replays`: the replay inside `subscribe`. `notifies`: a publication between the insert and the end of the
loop over `subscribers`. `deliv`: the `Delivery` events. `handlers`: the `subscribers` lists.

SUBSUMPTION (`Pipeline.quiescent_dominates`). Let `dom` be a preorder on the objects. Let the rules and the joins
SIMULATE it. That is: take a rule (or a join) and, for each premise, an object that dominates it. Then the same rule (or
join) on these objects gives a conclusion that dominates the first conclusion. Let the step `StepD` also drop an
in-flight object that a processed object of the same owner dominates. Then, for a well-formed system, at a reachable
quiescent state, a processed object dominates every object of `Cl`. Soundness stays (`reach_soundD`). That the AP
operations simulate the subsumption of the edge stores is argued (§11). The simulation fails for `applicable` on the
subscriptions, so the subscriptions and the links deduplicate exactly (§5.3).

---

## 6. Scheduling and the end of a run

### 6.1 The runner loop

The loop of today stays: an unlimited channel, a local priority queue, a quantum of `RUNNER_STEPS_QUANT` steps per
`Work` event, and the priority of the analyzers with zero-fact work. Changes:

* The events of §5.1 replace the old events.
* Two direct calls are permitted, as today:
  1. the analyzer calls `subscribe` of its own `SubscriptionManager`. The replay then calls `applySummary` and
     `applyRecord` of the SAME analyzer. These only add to its edge store and its worklist;
  2. the analyzer calls `addLink` of a callee in the same unit (§4.5). `addLink` only changes the stores of the callee
     and sends events. A recursive call calls `addLink` of the same analyzer, which is permitted for the same reason.

  Every other interaction between two analyzers is an event.
* The priority keys must not change while the event is in the queue. Today `EventComparator` reads `analyzerSteps` and
  the zero-work flag, which change. This breaks the heap order but loses no event.

The runner interface that the analyzer uses:

```kotlin
interface RunnerPort {
    val config: RunConfig
    val interpreter: Interpreter
    val contexts: MethodContextCache
    val vulnerabilities: VulnerabilityStore
    /** Q1: count, then put into the channel of the target runner (§5.1: by `callee`, `method`, or THIS runner for
     *  a Delivery, which the publisher's thread sends through the subscriber's `notify`). */
    fun send(event: RunEvent)
    fun enqueue(analyzer: RunMethodAnalyzer)               // W1: a Work event if the analyzer is not queued
    fun analyzer(key: MethodKey): RunMethodAnalyzer        // this unit only; made on demand
    fun subscribe(sub: Subscription)                       // the SubscriptionManager of this runner
    fun summaryStorage(key: MethodKey): SummaryStorage     // RunManager.summaryStorage: any unit (O2)
    fun link(callee: MethodKey, link: Link)                // same unit: a direct addLink; else LinkIn
}
```

### 6.2 The in-flight counter

The counter protocol of today stays, with one counter object per run:

* Q1. Increment before send: the counter goes up before the event goes into a channel or a local queue.
* Q2. Decrement after the handler: the counter goes down after the handler ends, after all its sends.
* Q3. A guard during the start: the run counts one phantom event while it sends the `Start` events.
* Q4. One counter per run: an event of an old run cannot change the counter of a new run.

Local work is inside an event:

* W1. An action that adds a worklist item or a pending publication to an analyzer with `queued = false` sets `queued`
  and sends `Work` (counted by Q1). This includes the direct `addLink`, the replay's `applySummary` and a request
  answer.
* W2. When the quantum ends and work is left, the runner puts the analyzer back into its local queue. The `Work`
  event stays counted.
* W3. The `Work` event ends (Q2) only when the worklist is empty and the pending publications are in the storage. Then
  `queued = false`.

THEOREM (`Pipeline.Quiesce.creach_inv`, `cnt_zero_iff`, `done_iff`, `done_final`). With Q1 to Q3, the counter equals
the number of events in the channels and the local queues plus the number of running handlers. So it is zero exactly
when no event waits and no handler runs, and after that no step is possible. `Pipeline.Quiesce.bad_early_done`: if the
counter goes down when the handler STARTS (not Q2), the run can end while an event is still pending. With W1 to W3,
zero means quiescence (argued, §11).

### 6.3 Abnormal end

* A timeout, the memory guard (`MemoryManager`) or an exception makes the run INCOMPLETE. The `RunManager` returns
  the status: `COMPLETE`, `TIMEOUT`, `OOM` or `FAILED`.
* AN EXCEPTION IS EVERY `Throwable`, an `Error` too (for example a JVM `OutOfMemoryError` or a `StackOverflowError`).
  In a runner, in the code of a run on the caller thread, or at the barrier (§7.1), it gives `FAILED` (phase 3:
  `EXCEPTION`, §9), and the driver returns the report so far. A JVM `OutOfMemoryError` does not give `OOM`: the status
  `OOM` comes only from a memory guard, the guard of a run or the guard of the barrier (§7.2 B4) (`ap-history.md` F68).
* THE FIRST END WINS. The status of a run is set once, by a compare-and-set. The quiescence sets `COMPLETE` in the
  same way. So a late end (the memory guard or the timeout while the `RunManager` joins the runners) does not turn a
  complete run into an incomplete one. One exception: the join overrides the first end. A runner that does not stop
  makes the run `FAILED`, also after the quiescence, because its stores can still change.
* EVERY CANCELLATION HAS A KNOWN CAUSE. The status is set before every cancel, so every cancel has a known cause: the
  timeout, a memory guard (of a run or of the barrier), or a runner failure. Three ends of a run cancel the analysis:
  the timeout of the run (`TIMEOUT`), the memory guard of the run (`OOM`) and a runner exception (`FAILED`). Each one
  is `RunManager.fail(status)`: it first sets the status of the run by the compare-and-set, then cancels the
  `Cancellation` and completes the run. After the quiescence or an earlier end, `fail` does nothing (the first end
  wins). So a runner exception ends the run at once, with no wait for the timeout, and the other runners stop at their
  next checkpoint. After a cancel, a handler can throw `Cancellation.Cancelled` (a checkpoint of the `ApManager` or of
  the alias analysis). The runner loop catches it and only stops: the run keeps the status of its cause. So the status
  always gives the real reason, and there is no `CANCELLED` status and no external cancel. The `RunManager` activates
  its `Cancellation` when it is made (in its constructor), before a runner starts, so a cancel is never undone by a
  later activation. The guard of the barrier also cancels, with the status `OOM` of the iteration; no runner is alive
  then (§7.2 B4).
* A throw in the code of a run on the caller thread (for example the routing of the `Start` events or the wait for the
  end) is `fail(FAILED)`: the `RunManager` still joins its runners and returns `FAILED`.
* The hand-off of an incomplete run is not complete. The theorems of `ap.md` §6.6 do not apply to the runs after it,
  so the driver does not start a run after an incomplete run (§7.1). The incomplete run adds nothing to the report
  (§7.5).
* Each run has its own coroutine scope with a `SupervisorJob`. The exception of one runner does not cancel the scope
  of a later run. (Today one failed runner cancels `analyzerScope` for every later run.)
* The `RunManager` joins every runner coroutine before it returns, on every exit, also when its own code throws. If a
  runner does not stop, the run ends as `FAILED` (the driver reads none of its stores), the analysis stops, and no
  later run starts. (Today a runner that does not stop in `cancellationTimeout` stays and can change the next run.)
* A cancellation must also complete the run. Today every `cancel()` of the analysis comes with its status
  (`updateFailureStatus(TIMEOUT)` or `(OOM)`) and with `analysisCompletion.complete`; keep the three calls together
  (`RunManager.fail`).

---

## 7. The iteration driver and the hand-offs

### 7.1 The run sequence

```kotlin
interface IterationPolicy {
    fun fieldLimit(runIndex: Int): Int                               // not decreasing (ap.md W3); run 1: >= 1, checked
    /** Asked only after a complete FORWARD run (the budget; out of scope, ap.md §6.6). */
    fun continueAfter(run: RunConfig, result: RunResult): Boolean
    /** The timeout of one run. `remaining`: the budget minus the time so far (§0: the budget is in the policy). */
    fun timeout(run: RunConfig, remaining: Duration): Duration = remaining
}

/** What one run and its barrier give: the next run, or the end of the analysis. */
sealed interface Next {
    class Run(val config: RunConfig) : Next
    class End(val status: RunStatus, val reason: EndReason = EndReason.ABNORMAL) : Next
}

class IterationDriver(private val policy: IterationPolicy, private val shared: SharedObjects,
                      private val budget: Duration) {
    fun analyze(roots: List<MethodKey>): Report {
        val start = TimeSource.Monotonic.markNow()
        val report = ReportBuilder()                                  // §7.5
        var index = 1                                                 // the current run: AnalysisEnd names it
        fun end(status: RunStatus, reason: EndReason) = report.build(AnalysisEnd(status, index,
            if (index % 2 == 1) Direction.FORWARD else Direction.BACKWARD, reason))
        try {                                                         // ONE GUARDED REGION: the whole loop body (§6.3)
            require(policy.fieldLimit(1) >= 1) { "ap.md S12 (d): run 1 needs a field limit of at least 1" }
            var config = RunConfig(1, policy.fieldLimit(1), demand = null, records = shared.records.view(),
                seeds = SeedIndex.EMPTY, roots = roots)
            while (true) {
                index = config.index
                when (val next = runOnce(config, report, policy.timeout(config, budget - start.elapsedNow()))) {
                    is Next.Run -> config = next.config               // the result of the run is garbage now (§7.6)
                    is Next.End -> return end(next.status, next.reason)
                }
            }
        } catch (e: Throwable) {                                      // an Error too: FAILED, never OOM (§6.3)
            logger.error(e) { "Run $index failed; the analysis ends with the report so far" }
            return end(RunStatus.FAILED, EndReason.ABNORMAL)          // the report so far: the earlier runs stay
        }
    }

    /** One run and its barrier. The `RunResult` is a local of this frame, so no live slot keeps it during the next run
     *  (§7.6). */
    private fun runOnce(config: RunConfig, report: ReportBuilder, timeout: Duration): Next {
        val result = RunManager(config, shared).run(timeout)          // a new engine (§2); it joins its runners (§6.3)
        if (result.status != RunStatus.COMPLETE)                      // §7.5: adds nothing, refutes nothing
            return Next.End(result.status)
        // THE BARRIER (§7.2): no runner runs now. Its own memory guard (B4): a hit cancels the Cancellation, and the
        // barrier stops at its next checkpoint.
        val guard = MemoryManager(shared.refManager, BARRIER_MEMORY_THRESHOLD) { shared.cancellation.cancel() }
        val next = try {
            guard.runWithMemoryManager { barrier(config, result, report) }   // the soft references stay enabled
        } catch (e: Cancellation.Cancelled) {
            Next.End(RunStatus.OOM)                                   // the barrier guard is the only canceller here
        }
        return if (shared.cancellation.isActive()) next else Next.End(RunStatus.OOM)   // a hit after the last checkpoint
    }

    private fun barrier(config: RunConfig, result: RunResult, report: ReportBuilder): Next {
        val forward = config.direction == Direction.FORWARD
        if (forward) {
            confirm(result)                                           // §7.5 steps 1, 2: the support, the witnesses
            report.add(config, result)                                // §7.5 step 3
        }
        shared.records.persist(config, result)                        // ap.md §8.7 R1
        if (forward && !result.hasDemandVulnerability()) return Next.End(RunStatus.COMPLETE, EndReason.STOP_RULE)
        if (forward && !policy.continueAfter(config, result)) return Next.End(RunStatus.COMPLETE, EndReason.POLICY)
        return Next.Run(handOff(config, result))                      // §7.3, §7.4
    }

    private fun handOff(config: RunConfig, result: RunResult): RunConfig {
        val limit = policy.fieldLimit(config.index + 1)
        require(limit >= config.fieldLimit) { "ap.md W3: the field limit must not decrease" }
        return RunConfig(config.index + 1, limit, demandOf(result), shared.records.view(), seedsOf(result), config.roots)
    }

    companion object {
        /** Today's threshold of the confirmation: `TRACE_GENERATION_MEMORY_THRESHOLD`
         *  (TaintAnalysisUnitRunnerManager.kt:645). */
        const val BARRIER_MEMORY_THRESHOLD = 0.99
    }
}
```

* The run sequence is `ap.md` §6.6: run 1 (forward), run 2 (backward), run 3 (forward), and so on.
* A forward run stops the iteration if every vulnerability that it reports has a confirmed witness (a sink edge or a
  sink edge set) of this run (`ap.md` §6.6). `hasDemandVulnerability` reads the witnesses of the run in the
  `VulnerabilityStore`, grouped by the vulnerability key (§4.7, §10). The policy can stop earlier.
* The driver asks `continueAfter` only after a complete FORWARD run. A complete backward run always goes on to the next
  forward run: its only output is the hand-off of that run (§7.4). So the iteration always ends after a forward run
  (as `PipelineDriver.driver_iteration_upto`, §7.7), or at an abnormal end.
* The driver checks the field limit of each run: run 1 has at least 1 (`ap.md` S12 (d)), and the limit does not
  decrease (`ap.md` W3). A policy that breaks either is an error: the `require` fails, and the iteration ends as at a
  throw in the guarded region (`FAILED`; for run 1 the report has no entry).
* THE TIMEOUT OF A RUN is `policy.timeout(config, remaining)`, where `remaining` is the budget minus the time so far
  (by default the whole rest of the budget). The `RunManager` gets it in `run(timeout)`.
* THE END OF THE ANALYSIS is an output: `Report.end = AnalysisEnd(status, run, direction, reason)` (§10). `run` and
  `direction` are those of the last run. The reasons:
  * `STOP_RULE`: a complete forward run with no demand vulnerability; `status` is `COMPLETE`;
  * `POLICY`: `continueAfter` gave false after a complete forward run; `status` is `COMPLETE`;
  * `ABNORMAL`: an incomplete run (`status` is its status: `TIMEOUT`, `OOM` or `FAILED`), a throw in the guarded
    region of the driver (`status` is `FAILED`), or a hit of the memory guard of the barrier (`status` is `OOM`).
* ONE GUARDED REGION. The whole loop body of the driver is one guarded region (`catch (e: Throwable)`): the
  `RunConfig` of run 1 and its check, `RunManager(...)`, `run(...)` and the barrier (the confirmation, `persist`, the
  hand-off). A throw there, an `Error` too (§6.3), ends the iteration with `FAILED`. The driver returns the report so
  far: the results of the earlier runs stay (`ap-history.md` F67, F68). The `RunManager` joins its runners on every exit
  (§6.3), so no runner of the run runs when the driver returns.
* THE MEMORY GUARD OF THE BARRIER (§7.2 B4). A hit at the barrier ends the iteration with `AnalysisEnd(OOM, run,
  direction, ABNORMAL)` and the report so far. The barrier has no deadline (§11).

### 7.2 The barrier

* B1. The driver computes the hand-off only after the run is complete and no runner of the run is alive (§6.3).
* B2. The next run starts only after the hand-off is complete.
* B3. The driver may read the stores of the finished run in parallel, read-only.
* B4. The barrier runs under its own memory guard (`MemoryManager`), as today's confirmation: the threshold of today
  (`TRACE_GENERATION_MEMORY_THRESHOLD = 0.99`) and the same mechanism (`TaintAnalysisUnitRunnerManager.kt:374-384`,
  `:645`). The soft-reference managers stay enabled during the barrier, so `persist` interns with live tables and the
  persisted records share nodes. A hit cancels the `Cancellation`; the loops of the barrier (the support, `persist`,
  the hand-off) call `Cancellation.checkpoint` once per analyzer, so the barrier stops at its next checkpoint. The
  iteration then ends with `AnalysisEnd(OOM, run, direction, ABNORMAL)` and the report so far (§7.1). The driver also
  checks the `Cancellation` after the barrier, so a hit after the last checkpoint is not lost (the next `RunManager`
  would activate the `Cancellation` again). The barrier has no deadline (§11).

With B1, the hand-off reads the closure of the run (`PipelineDriver.result_D`, `result_DR`, `result_DB`). So the
hand-off is exactly the hand-off of `ap.md` §9.2.

### 7.3 Forward run `n` to backward run `n + 1`

From the `summaries` (run summary store) of every method analyzer and the sink edges of run `n`:

* DEMAND. For every summary edge `j → g` of the method, in every layer, BEFORE the restriction: one backward demand
  pattern `(D-c = g, D-p = j)` per leaf of `g` (Lean `Backward.revSummaryDemand`). For a summary with several premises:
  one pattern per member (`ap.md` §9.2; argued, `ap.md` §11.2). The driver builds the `DemandStore` of run `n + 1`
  from them. The backward run has no `[any-taint]` (`ap.md` W8), so the driver reads a forward summary as a location
  set: a leaf or a premise with the `[any-taint]` tail gives a pattern with the tail `[any]`, and the hand-off drops
  the exclusion `E` of an `[any-taint]/E` leaf or premise (a larger backward demand: sound; `ap.md` §9.2). Lean: the
  driver reads each forward run with its exclusions and must flags dropped (`AnyTaintExCov.forget6`, `forgetX`;
  `PipelineAnyTaintExDriver.resultSeqX`). The hand-off of a run with the exclusion can be SMALLER than that of the
  same run without it: the exclusion removes summaries (`AnyTaintExCov.CexRoute.route_a_false`); the driver theorem
  reads each refined run directly (§7.7).
* SINK SEEDS. The `SeedIndex` of the vulnerabilities that run `n` reported (§4.7; `ap.md` §9.2).
* RECORDS. The `RecordStore` persists the normal summary edges with one premise (`ap.md` §8.7 R1, forward).
  COMPLETE is one notion: a normal edge. A normal forward edge is complete also with an `[any-taint]` leaf (with its
  exclusion) or an `[any-taint]` premise, so `persist` keeps it with the tails and the exclusions. (The premise of a
  normal edge of a restricted forward run is a `$` premise or a must-premise `[any-taint]` with a concrete mark:
  `AnyTaintExKinds.DRXs_normal_premise`, `DRXs_must_premise`.) A record with an `[any-taint]` premise keeps that tail
  and its exclusion: it applies by `inside`, or by `applicable` with demand results (§3), and no leaf of it is ever
  reversed (§5.3). Of any other record, an `[any-taint]/E` leaf with `E ≠ {}` is not reversed; the other leaves of
  its record are (R3 is leaf by leaf, §5.3).

### 7.4 Backward run `n + 1` to forward run `n + 2`

From the `summaries` of every backward method analyzer, for every method `M` (`ap.md` §9.2; Lean `Backward.demOf`):

1. the zero demand `(D-c = zero, D-p = none)` (implicit for every method key, §4.4);
2. for every zero-premise backward edge at the forward entry of `M`, with the conclusion `gb`: `(D-c = gb, none)`;
3. for every backward summary `jb → gb` of `M` whose premise `jb` is not the zero fact, in every layer:
   `(D-c = gb, D-p = jb)`.

SOURCE SEEDS: the `SeedIndex` of the `sourceHits` of every backward method analyzer (§4.7; `ap.md` §8.11, §9.2;
Lean `FSeeds.srcHit`).

RECORDS: the `RecordStore` persists the normal backward summary edges with one premise that is not the zero fact
(`ap.md` §8.7 R1, backward). The backward run has no `[any-taint]`, so a backward edge is complete when it is normal,
as before F69. The may stays out of the records: an `[any]` requirement is in the demand layer (W6), and so is every
result of a reversed micro edge whose forward target is `[any]` (§4.3).

THE DEMAND PATTERNS of the backward run have the tails `$`, `*/E` and `[any]`. The emission of the next forward run
gives the tail of the ADDED fact for two any tails (`ap.md` §6.3), so an `[any-taint]` added fact still gives a
must-premise from an `[any]` pattern (§4.4; Lean `AnyTaintEx.emitTX`).

THE STATIC BASE. `S` is touched at every call, in every run (`interpreter.md` §3.3), so the driver gives no static
input. A callee that touches no static gives the static fact back through its run-1 identity summary, which is a
record in every later run (`ap.md` §8.7). This needs no rule at the call.

### 7.5 Confirmation and the report

After a complete forward run, at the barrier:

1. Compute the SUPPORTED premise sets (`ap.md` §4.9 condition 3) as a least fixed point over the links:
   * the set `{zero}` of a root is supported;
   * a premise set of a callee is supported if one call statement supplies each member. A member is supplied by a
     link at that call statement whose added fact is normal on the link and equal to the member. The caller edge of
     the link must be normal, and its premise set must be supported.
   * in a restricted forward run, a member is also supplied by a link whose added fact has the `[any-taint]` tail
     (normal on the link; the caller edge as above) if the member has the SAME concrete mark, lies inside the added
     fact with the exclusions of both (`inside`: a member below an `[any-taint]/E` added fact at `a.path ++ r` needs
     `E` to admit `r`), and is an exact fact `$` or an `[any-taint]` must-premise (`ap.md` §4.9 condition 3; Lean
     `AnyTaintEx.SupLinkX`, `SupX`). For a concrete member `inside` already gives the same mark
     (`AnyTaintExact.markSub_conc`); the explicit condition rejects a member with the mark `*`
     (`AnyTaintExact.CexSupMark.cex_sup_mark`). The link carries the tail and the exclusion of its added fact, so the
     support needs no other data.

   The support is a property of a premise set in one method key. The links carry the data (E-2).
2. Mark each sink witness of the run (a sink edge, or a sink edge set) confirmed or not (`ap.md` §4.9 conditions 1 to
   3). A witness reads the support in its own method key (§4.7). A sink edge set is confirmed only as a whole: the
   union of its premise sets WITHOUT the zero fact (`{zero}` if every edge has `{zero}`; `ap.md` §4.6) must be
   supported jointly. A sink edge with the `[any-taint]` tail in the normal layer is a normal sink edge, so it can be
   confirmed (condition 1). With an exclusion `E` its sink pattern meets a location that `E` admits: the sink check
   reads `E` (`ap.md` §4.9), so the confirmation needs no other test. In a restricted forward run a member of its
   premise set can be an `[any-taint]` must-premise (condition 2). Lean: `AnyTaintEx.Confirmed6X` (run 1),
   `ConfirmedX` (a restricted forward run); a confirmed vulnerability is real (`AnyTaintExExact.confirmed_real_valid6X`,
   `confirmed_realX_valid`; under S7 and S13, and in a restricted run with the spec rules, which have the rule
   hypotheses, `AnyTaintExExact.specX_rules`, and with exact records in normal form, `AnyTaintEx.RecsExactX`,
   `AnyTaintExExact.RecsConcX`, `RecsWFX`; `ap.md` §10.11). Over the run sequence
   (`AnyTaintExExact.seq_confirmed_realX_valid`) this holds when every record is an exit edge of an earlier forward
   run of the same program (`AnyTaintExExact.RecsFromRunsX`), with no exactness hypothesis on the records; with the
   reversed backward records and with the source seeds it is argued (`ap.md` §8.7 R4, §11.2).
3. Update the `VulnerabilityStore` and the report (`ap.md` §8.10). The report takes the entries of the run in one
   step, after step 2.

The support is a fixed point over the whole run, so it can change until the run ends (`ap.md` §4.9). The barrier is
the first point where it is final. The driver computes the support at the barrier; no store of a run keeps it.

THE REPORT uses only COMPLETE forward runs (`ap-history.md` F67). It has two states (`ReportState`, §10):

* CONFIRMED: every vulnerability that a complete forward run confirmed. This state is final;
* DEMAND: every other vulnerability of the LATEST complete forward run.

A vulnerability is confirmed in a run if one of its witnesses of that run is confirmed: any alternative, any method
key. One key can come from several runs; the state CONFIRMED wins (`ap.md` §8.10). A demand vulnerability of an
earlier forward run that the latest complete forward run does not report is REFUTED, so it leaves the report.

THE OUTPUT holds EVERY entry of the report: the CONFIRMED and the DEMAND vulnerabilities, each with the simple trace
(§9; `ap-history.md` F68). So the output holds every vulnerability of the latest complete forward run, and the claim
of `ap.md` §0.1 and §6.6 (the analysis can stop at any complete forward run) holds for the output too: a complete
forward run holds every real vulnerability in some layer (`PipelineDriver.driver_iteration_upto`, with the tail
`[any-taint]` `PipelineAnyTaintExDriver.driver_iteration_uptoX`, §7.7), and the report keeps every vulnerability of the
latest complete forward run, in one of its two states. A vulnerability that stays DEMAND in every run (for example one
whose taint passes only through a pass rule with an `AnyField` target, a may `[any]`: `ap.md` W6 forward, and the
demand layer of its reversal backward, §4.3) is output with the state DEMAND.

AN `[any]`-TARGET SOURCE. Its result has the tail `[any-taint]`: a normal edge (`ap.md` W8). So a vulnerability whose
taint comes from such a source CAN BE CONFIRMED (`ap-history.md` F69). Run 1 can confirm it if a normal sink edge
under a supported premise set reaches the sink (`ap.md` §4.9 conditions 1 to 3; Lean
`AnyTaintExCases2.PassRule.source_confirmed`; through an identity callee `id(p): return p`,
`AnyTaintExCases2.I.run1_confirmed`). This holds also through a SETTER: the run-1 summary
`(this, ., *, {}, *) → (this, ., */{name}, *)` of `setName(n): this.name = n` on the added fact
`(this, ., [any-taint], T)` gives `(this, ., [any-taint], {name}, T)` in the normal layer, so after
`dto.setName(c)` run 1 CONFIRMS `sink(dto.email)` and does not report `sink(dto.name)`, which is not real (Lean
program `AnyTaintExCases.S`: `run1_dto_ann`, `run1_email_confirmed`, `run1_name_not_reported`, `name_not_real`; the
first F69 form demoted at the exclusion and gave two DEMAND entries, `S.run1T_not_confirmed`). A flow through a callee
that reads a field of the object (a getter) is in the demand layer in run 1: the run-1 summary of the getter is the
case `above` of `ap.md` §4.1, and in run 1 an edge whose premise has the mark `*` (a FLOW edge, as the run-1
summary of the getter from the policy fact) has no normal `[any-taint]` conclusion
(`AnyTaintExCases2.G.run1_flow_above`, `G.run1_not_confirmed`; `AnyTaintExKinds.D6X_flow_no_any_taint`, under S7,
S10 and S15). Run 3 emits the must-premise in the getter, and the sink edge is normal: run 3 confirms the vulnerability
(`AnyTaintExCases2.G.run3_must`, `G.run3_sink_normal`, `G.run3_confirmed_handoff`, a program with no exclusion; with
an exclusion and a must-premise, `AnyTaintExCases.B.run3_anyE_confirmed`). With the sink in the callee, the
must-premise is supported through its link (the `[any-taint]` added fact, `AnyTaintEx.SupLinkX`) and run 3 confirms
the vulnerability too (`AnyTaintExCases2.C.run3_supported`, `C.run3_confirmed_handoff`). Only the demotions of §4.3
(the field-limit cut, a cleaner `part` row other than `atAndBelow` and `below` one accessor below the fact, a may
target, a demand-layer input, the must-record demotion) make `[any]` of an `[any-taint]` fact, and they can keep a
vulnerability DEMAND; a weak update can give a CONFIRMED false positive (§11 PRECISION WITH `[any-taint]`).

AN INCOMPLETE RUN (forward or backward) adds nothing to the report and refutes nothing. The refutation of `ap.md`
§8.10 needs the coverage theorem of run `n + 2`, which needs complete runs. The confirmation needs the support at the
fixed point of the run, which an incomplete run does not reach. So the driver computes no confirmation for an
incomplete run, and the report has no state for its vulnerabilities. The report stays that of the earlier complete
forward runs, and `Report.end` tells how the analysis ended (§7.1).

AN INCOMPLETE RUN 1. If run 1 is incomplete, no forward run is complete: the report has no entry and the output has no
vulnerability; `Report.end` gives the cause (the status). Today a full scan that times out outputs the vulnerabilities
that it found before the timeout (`TaintAnalyzer.kt:157-223`). This is a deviation from today (`ap-history.md` F67
(4), F68; §11).

### 7.6 What stays after a run

| Data | Stays until | Read by |
|---|---|---|
| the run summary stores of a run, and the `sourceHits` of a backward run | its hand-off is computed (the end of its barrier) | §7.3, §7.4; `persist` (`ap.md` §8.7 R1) |
| the links of a forward run | its confirmation is computed | §7.5 |
| the edge stores, the initial fact stores, and the links of a backward run | the end of the run | — (the barrier never reads them) |
| `SummaryStorage`, `SubscriptionManager`, the runners, the backward analyzers | the end of the run, or its hand-off | — |
| `RecordStore`, `VulnerabilityStore`, `MethodContextCache`, `ApManager` | the end of the analysis | every run |

THE BARRIER READS ONLY: the links of a forward run (the support), the summaries (`persist`, the hand-off), the
`sourceHits` of a backward run (the hand-off), the `VulnerabilityStore` (the confirmation, the report, the stop rule,
the sink seeds) and the forms of the `MethodContextCache` (the seed patterns). So the `RunManager` keeps of a complete
run only what the barrier reads: at the end of the run it drops the edge stores, the initial fact stores and the links
of a backward run. The barrier holds the stores that it reads under its own memory guard (§7.2 B4). The driver keeps
the result of a run only in the frame of its barrier (`runOnce`, §7.1), so no live slot keeps it during the next run.
Every other object of a run is garbage after the run: the edge stores too. No store of a run stays for a trace resolver
(the trace resolution is out of scope, §9). An incomplete run keeps no store after it ends (§7.5). The engine of a run
is never used again (§2), so no state of one run can leak into the next run. This removes the leaks of today's reuse
(Appendix A).

### 7.7 The driver theorems

THEOREM (`PipelineDriver.driver_iteration`). Hypotheses:

* the program satisfies the hypotheses of `Backward.iteration_general` (`ap.md` §6.6): `P.WF`, `Reverse.BindTargetsStar`,
  `Backward.StmtsMarkRev`, `NoZeroBack`, `ZeroKept`, `ExitReach`, and every sink pattern has the tail `$` or `[any]`;
* run 1 uses `policy1`. The forward restricted runs use `emitM`, `satI` and `restrictU`. The backward runs use the
  same three on `Reverse.Program.rev P`, with no sinks and with the zero rules (`zbind = true`). The field limits and the
  record sets are free;
* every run is complete: `stF k` (forward run `2k + 1`) and `stB k` (backward run `2k + 2`) are reachable quiescent
  states of their encoded systems;
* the hand-offs CONTAIN those of §7.3 and §7.4, computed from the final states:
  * the backward demand contains `revSummaryDemand` of forward run `2k + 1` (`hdemB`);
  * the seeds contain the sink of every vulnerability of that run (`hseeds`);
  * the forward demand contains `demOf` of backward run `2k + 2` (`hdem`).

Conclusion: for every real flow to a sink (a reachable location that a sink pattern with a concrete mark covers),
every forward run holds the vulnerability, in some layer.

`PipelineDriver.driver_iteration_upto` is the same theorem for a FINITE sequence: the driver stops after forward run
`2K + 1`, and only the runs up to it must be complete. This is the stop structure of the driver of §7.1, for the
forward runs without source seeds: the driver stops only after a complete forward run (the stop rule or
`continueAfter`), or at an abnormal end, which adds nothing to the report (§7.5). With the source seeds:
`PipelineSeeds.driver_iteration_src` (below), its finite form argued (§11); the static rule and the conjunctions: §11.
The proof extends the sequence after `K` with the full demand and with every sink as a seed.

The records are not hypotheses: the record sets are free. For the runs with the static rule, `ap.md` proves the
iteration (`StaticsIter.iteration_general_DS`), and `PipelineAP.clDS_iff` gives the closure equality; the pipeline form
of that theorem is argued (§11).

THEOREM (`PipelineSeeds.driver_iteration_src`). The same, with the source seeds (§4.7). Forward run `2k + 3` analyzes
the program `FSeeds.keepSources P σ_k`; `σ_k` contains the source hits of backward run `2k + 2`, computed from its
final state (`FSeeds.srcHit`). The conclusion is the same: every forward run holds every real vulnerability of `P`. The
proof joins `PipelineDriver.result_D`, `result_DR`, `result_DB` with `FSeeds.iteration_src`. Its finite form (as
`PipelineDriver.driver_iteration_upto`) is argued (§11).

THEOREM (`PipelineAnyTaintExDriver.driver_iterationX`; the tail `[any-taint]` with its exclusion, `ap.md` §10.11). The
same, with run 1 a run of `PipelineAnyTaintEx.sysD6X` and every forward restricted run a run of `sysDRX` with the spec
rules `emitX`, `satX`, `restrictX` (the closure `AnyTaintEx.DRXs`); every backward run is a run of
`PipelineAP.sysDB`, as before (the backward run has no `[any-taint]`). The driver reads each forward run with its
exclusions and must flags dropped (`PipelineAnyTaintExDriver.resultSeqX`; `AnyTaintExCov.forget6`, `forgetX`): the
hand-offs of §7.3 and §7.4 have no exclusion and no must flag. This hand-off can be smaller than that of the same run
without the exclusion (`AnyTaintExCov.CexRoute.route_a_false`), so the proof reads each refined run directly: every
refined run justifies its own witnesses (`AnyTaintExCov.iteration_reportsX`). The hypotheses are those of
`PipelineDriver.driver_iteration` (every sink pattern has the tail `$` or `[any]`); there is no hypothesis on the taint
edges and on the records. The conclusion is the same: every forward run holds every real vulnerability, in some layer.
The proof joins `PipelineAnyTaintEx.result_D6X`, `result_DRXs` and `PipelineDriver.result_DB` with
`AnyTaintExCov.iteration_reportsX` (through `PipelineAnyTaintExDriver.resultSeqX_runSeqX`).
`PipelineAnyTaintExDriver.driver_iteration_uptoX` is the finite form, and `driver_iteration_srcX` the form with the
source seeds (as `PipelineSeeds.driver_iteration_src`; `AnyTaintExCov.iteration_srcX`; its finite form argued, §11).

---

## 8. Code reuse

| Today | Decision | Note |
|---|---|---|
| `TaintAnalysisUnitRunnerManager`, `AnalysisUnitRunnerManager` | REFACTOR into `RunManager` | keep the unit routing, the runner spawn, the counter, the timeout, the memory guard and the progress log; remove `resetApManager`, the delayed units and the cross-run fields; add `RunConfig`, the per-run scope, the join of the runners and the map of the `SummaryStorage`s |
| `TaintAnalysisUnitRunner` | REFACTOR into `UnitRunner` | keep the channel, the priority queue, the quantum and `MethodAnalyzerStorage`; the events of §5.1 |
| `AnalysisRunner` | REPLACE by `RunnerPort` (§6.1) | |
| `MethodAnalyzerStorage` | REUSE with a factory | the `EmptyMethodContext` twin goes; the context cache shares the per-method parts (§4.8) |
| `MethodAnalyzer`, `NormalMethodAnalyzer` | REPLACE by `RunMethodAnalyzer` | §4; `TimedMethodAnalyzer` becomes a decorator of the new interface |
| `EmptyMethodAnalyzer` | REMOVE | an empty method is never analysed and never a callee (§4.4) |
| `MethodAnalyzerEdges`, `EdgeCollection` | REUSE the structure | the new keys of `ap.md` §8.1; the list of `EdgeCollection` becomes the `normal` queue of `DeltaWorklist` (§4.3) |
| `AccessPathBaseStorage`, `MethodAnalyzerEdges.EdgeStorage` | NOT USED, REPLACE | `AccessPathBaseStorage` rejects the zero base; the conclusion group of `ap-impl.md` §4.3 (one premise key, every base and kind) replaces `EdgeStorage` (`ap.md` §7.6) |
| `JIRLocalVariableReachability` (`isReachable`) | NOT USED by the core | no liveness check (§4.3); the alias analysis keeps it as its own input (§4.8) |
| `Edge` (`ZeroToZero`, `ZeroToFact`, `FactToFact`, `NDFactToFact`) | REPLACE | `ap.md` §7.6 |
| `SummaryEdgeStorageWithSubscribers`, `MethodSummariesUnitStorage` | REUSE the pattern | publications per premise key and layer; the lock of P3 (§5.2); one storage per method key in the `RunManager` |
| `SummaryEdgeSubscriptionManager`, `CommonAPSub`, the tree sub-storages | REUSE the pattern | the registration on the first `getOrPut`, the delta insert, the replay, the match at delivery; P4 with one `matches`; one manager per runner |
| side-effect requirements and summaries, `TaintMarkFieldUnfoldRequest`, `MethodSideEffectSummaryHandler`, `triggerSideEffectRequirement` | REMOVE | the requests over the links (§4.6) |
| fact-depth delay (`INITIAL_ALLOWED_FACT_DEPTH`, `MethodAnalysisDelayed`, `DelayedAnalysisResume`, `factLimit`) | REMOVE | the field limit (`ap.md` §4.4) |
| `InitialFactAbstraction` (tree, automata, cactus) | REMOVE | the policy and the emission (§4.4) |
| `MethodSummaryEdgeApplicationUtils`, `MethodCallSummaryHandler` | REPLACE | `applySummary` (`ap.md` §4.3); the rewriter moves to the interpreter |
| `TaintSinkTracker`, the vulnerability buckets of `TaintAnalysisUnitStorage` | REPLACE | the `VulnerabilityStore` (§4.7) and the conjunction store (`ap.md` §8.9); no lossy merge |
| `MethodCallResolver`, `JIRMethodCallResolver` | ADAPT | today it is typed to `TaintAnalysisUnitRunner` and calls back with a `MethodCallHandler` per edge kind; the new one gives the resolved callees to `callPlan`, with no empty method (§4.4) |
| `TrackerWithSubscriber`, `LambdaTracker` | REUSE as the source of the prescan values | no lambda event in the new core (§5.1) |
| `MethodEntrypointResolver`, `UnitResolver`, `LanguageManager` | REUSE | |
| `ApplicationGraph.reversed`, `MethodInstGraph` | REUSE | `JIRAnalysisManager` downcasts the graph to `JApplicationGraph`; ADAPT it to accept the reversed graph |
| `JIRBackwardExitWiringGraph` (`saloed/backward-main`) | PORT | with a cache per method (§4.4) |
| `StatementSummaryBuilder`, `buildReversed`, the JVM flow functions | ADAPT | the forward interpreter of §4.9 (`interpreter.md`); `buildReversed` becomes `StatementSummary.reversed` in the core |
| `JIRMethodAnalysisContext` | SPLIT | the cached part and the run part (§4.8) |
| `MemoryManager`, `Cancellation`, `UnitRunnerStats`, `MethodStats` | REUSE | one instance per run where it has run state; the `RunManager` activates the `Cancellation` in its constructor (§6.3); one more `MemoryManager` for each barrier, with the threshold of today's confirmation (§7.2 B4) |
| summary serialization (`storeSummaries`, `loadSummariesFromRunner`) | NOT USED | the records are the reuse between runs |
| `trace/*` | OUT OF SCOPE | no store of a run stays for it (§7.6); phase 3 gives every report entry, CONFIRMED and DEMAND, the simple trace `TracePathGenerationResult.Simple` (§9) |

Do not copy the defects of today that Appendix A lists. Each one has its rule in this document: P3 and P4 (§5.3),
no edge post-processor (§4.3), the new engine per run (§2, §7.6), the per-run scope (§6.3), the fixed priority keys
(§6.1), and the correct interners of the `ApManager` (O4).

---

## 9. Interface to the prescan and the output

* PRESCAN (phase 3). The prescan runs the current core. It gives the new core:
  * the reduced rule set (`relevantRuleIds`, the prescan rule ids);
  * the lambda resolutions per call site (the prescan lambdas: the values of the `TrackerWithSubscriber` of each call
    site);
  * the fact type checker and the external method tracker;
  * the root methods.

  The core copies the resolutions into the `MethodContextCache` once, before run 1. It keeps no reference to a context
  of the prescan.
* PRESCAN MEMORY. The caller gathers the prescan info above. Then, before run 1, it releases the WHOLE prescan state:
  the prescan runners, the unit storage, the analyzers, the AP manager of the prescan and `JIRAnalysisManager.contexts`.
  No prescan edge, summary or alias analysis stays alive during the runs (`ap-history.md` F67).
* OUTPUT (phase 3). The core gives the `Report` (§10): the entries, each with its state CONFIRMED or DEMAND (§7.5) and
  the witnesses of its key in the run of that state (the fields of `ap.md` §8.10), and `end`, the end of the analysis
  (`AnalysisEnd`, §7.1). The phase-3 output holds EVERY entry of the report: the CONFIRMED vulnerabilities and the
  DEMAND vulnerabilities of the latest complete forward run, each with the simple trace (TRACE, below; `ap-history.md`
  F68). The method key of an output vulnerability is the method key of a confirmed witness if the entry has one, else
  of the first witness. Phase 3 maps `end` to today's `TaintAnalyzer.Status`. If run 1 is incomplete, the report has no
  entry and the output is empty; the status gives the cause. Today a full scan that times out outputs the
  vulnerabilities that it found before the timeout (`TaintAnalyzer.kt:157-223`): this is a deviation from today (§7.5,
  §11).
* TRACE. The trace resolution is out of scope. The core keeps no store of a run for a trace resolver (§7.6). The
  phase-3 output gives every entry, CONFIRMED and DEMAND, a SIMPLE trace: the trace with only the sink statement (today
  `TracePathGenerationResult.Simple`,
  `core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/ap/ifds/trace/path/TracePath.kt:48-51`).
  Phase 3 logs the count of the entries per state (CONFIRMED, DEMAND).
* NO EXTERNAL CANCEL (phase 3). The phase-3 entry has no `cancel()`: the timeout of a run, a memory guard (of a run or
  of the barrier) and a runner exception are the only causes of a cancellation (§6.3). So phase 3 maps the status one
  to one: `COMPLETE` → `OK`, `TIMEOUT` → `TIMEOUT`, `OOM` → `OOM`, `FAILED` → `EXCEPTION`.
* THE PHASE-3 GUARD. Phase 3 calls the analysis inside `runCatching`, as today (`TaintAnalyzer.kt:157-158`). A throw
  outside the driver (the setup of the analysis) gives an empty output and the status `EXCEPTION`. A throw inside the
  driver never reaches phase 3: the driver returns the report so far (§7.1).

---

## 10. Reference code

The types of the messages and the stores. `PathFact`, `Pattern`, `InitialAp`, `PremiseKey` (`size`, `member(k)`,
`isZero`), `PathNode`, `Facts` (`Reach`, `FlowTree`, `TaintTree`), `PathEdge`, `Direction`, `Record`, `RecordStore`
and the tests are those of `ap.md` §3.4, §4, §7 and §8.7. The premise key is the premise set of `ap.md` §4.6 and §8.1.

```kotlin
typealias MethodKey = MethodEntryPoint            // ap.md §1: context and forward entry statement

enum class Layer { NORMAL, DEMAND }

/* PremiseKey (ap.md §7.1): the InitialAp itself for one member; a PremiseSet for two or more. Interned. */

/** The caller side of a link (E-2). */
data class CallerRef(val caller: MethodKey, val premise: PremiseKey, val callerLayer: Layer, val call: CommonInst)

/** A link (ap.md §8.3): the added fact, its layer on the link, the caller edge. An added fact with the `[any-taint]`
 *  tail is normal on its link (ap.md W8) and holds its exclusion: the emission and the support read its tail and its
 *  exclusion (§4.4, §7.5). */
data class Link(val addedFact: Pattern, val linkLayer: Layer, val caller: CallerRef)

/** A subscription (ap.md §8.4). `zeroOnly`: the backward zero subscription (rule zret). Equality by value (E-3). */
data class Subscription(val callee: MethodKey, val addedFact: Pattern, val linkLayer: Layer, val ref: CallerRef,
                        val zeroOnly: Boolean = false) {
    val caller: MethodKey get() = ref.caller
}

/** A publication: a summary edge of the callee, after the restriction in a restricted run. Its layer is
 *  `conclusion.layer`. `premise` holds the tail of each member and the exclusion of an `[any-taint]` member: an
 *  `[any-taint]` premise and an `[any]` premise of one path are two premise keys, so two publications (§4.6; Lean:
 *  the must flag and the exclusion of `pub` in `PipelineAnyTaintEx.sysDRX`). */
data class Publication(val premise: PremiseKey, val conclusion: Facts)

/** A request of run 1 (ap.md §4.5, §4.10). A position is an interned path of the new AP (ap.md §7.1). */
sealed interface RequestKind {
    data class Mark(val mark: TaintMark) : RequestKind
    data class Position(val path: PathNode) : RequestKind
}

/** A seed (§4.7). A sink seed (backward run): one requirement of a reported sink; the requirement of an `[any]` sink
 *  pattern has the tail `[any]`, in the demand layer (the backward run has no `[any-taint]`, ap.md W8, §9.2). A
 *  source seed (forward restricted run): one unconditional source edge that the backward run reached, in its forward
 *  form; the method key, the statement and the edge identify it in both runs (ap.md §8.11). */
sealed interface Seed {
    val method: MethodKey
    val statement: CommonInst
    data class Sink(val rule: RuleId, override val method: MethodKey, override val statement: CommonInst,
                    val requirement: Pattern) : Seed
    data class Source(override val method: MethodKey, override val statement: CommonInst,
                      val edge: PathEdge) : Seed
}

/** The seeds per (method key, statement). */
class SeedIndex(private val byPlace: Map<Pair<MethodKey, CommonInst>, List<Seed>>) {
    fun at(method: MethodKey, statement: CommonInst): List<Seed> = byPlace[method to statement].orEmpty()
    companion object { val EMPTY = SeedIndex(emptyMap()) }
}

sealed interface RunEvent {
    data class Start(val root: MethodKey) : RunEvent
    data class LinkIn(val callee: MethodKey, val link: Link) : RunEvent
    data class ZeroIn(val callee: MethodKey) : RunEvent
    data class RequestIn(val method: MethodKey, val premise: InitialAp, val request: RequestKind) : RunEvent
    data class Delivery(val callee: MethodKey, val publications: List<Publication>) : RunEvent
    data class Work(val analyzer: RunMethodAnalyzer) : RunEvent
}

/** ap.md §8.10, §4.7: the key of a vulnerability record. `method` is the method of the method key, WITHOUT the
 *  context: one sink statement in several contexts is one vulnerability. */
data class VulnerabilityKey(val rule: RuleId, val method: CommonMethod, val statement: CommonInst)

/** ap.md §4.9: a sink edge (premise set, layer, sink facts). `facts`: REACH (the zero fact) for an unconditional sink,
 *  else a TAINT tree, so the sink facts of two witnesses of one entry merge (§4.7); as `ap-impl.md` §7.12. A normal
 *  TAINT tree can have `[any-taint]` leaves, with one exclusion for them in the tree key (ap.md §7.2): such a sink
 *  edge is normal and can be confirmed (§7.5). */
class SinkEdge(val premise: PremiseKey, val layer: Layer, val facts: Facts)

/** A sink witness (§4.7): one sink edge, or the sink edge set of a conjunctive sink (one edge per literal), of one sink
 *  alternative (`SinkRule.alternative`, §4.9) in one method key. It is confirmed as a whole (§7.5 step 2), with the
 *  support in `methodKey`. `endFacts`: the end facts of the sink (ap.md §8.10). The sink patterns of a witness are not
 *  stored: they are `SinkRule.patterns` of `alternative` of the rule at the statement in `methodKey` (the same in every
 *  run, interpreter.md I5). */
class SinkWitness(val alternative: Int, val methodKey: MethodKey, val edges: List<SinkEdge>, val run: Int,
                  val endFacts: List<PathFact> = emptyList()) {
    var confirmed: Boolean = false                                             // set only at a barrier (§7.5)
}

/** ap.md §8.10: the vulnerability records. One entry per (key, alternative, method key, run, shape); the shape is the
 *  (premise, layer, group key of the facts) list of the edges. Two witnesses of one entry merge their sink facts;
 *  witnesses of different alternatives or method keys never merge (§4.7). */
interface VulnerabilityStore {
    fun add(key: VulnerabilityKey, witness: SinkWitness)                         // concurrent (O4)
    fun witnessesOf(run: Int): Sequence<Pair<VulnerabilityKey, SinkWitness>>
}

/** §6.3. TIMEOUT: the timeout of the run. OOM: a memory guard (of the run, or of the barrier, §7.2 B4), never a JVM
 *  `OutOfMemoryError`. FAILED: a `Throwable` (an `Error` too) in a runner, in the code of the run or at the barrier, or a
 *  runner that does not stop at the join. No CANCELLED: every cancel has a known cause (§6.3). */
enum class RunStatus { COMPLETE, TIMEOUT, OOM, FAILED }

/** The result of one run. The driver reads its stores only if `status == COMPLETE` (§7.5). */
class RunResult(val status: RunStatus, val analyzers: Sequence<RunMethodAnalyzer>, val runIndex: Int,
                val vulnerabilities: VulnerabilityStore) {
    /** §7.1: a vulnerability key of THIS run with no confirmed witness of this run (any alternative, any method key). */
    fun hasDemandVulnerability(): Boolean =
        vulnerabilities.witnessesOf(runIndex).groupBy({ it.first }, { it.second }).values
            .any { witnesses -> witnesses.none { it.confirmed } }
}

/** §7.1: why the iteration ended. ABNORMAL: an incomplete run (its status), a throw in the guarded region of the driver
 *  (FAILED), or a hit of the memory guard of the barrier (OOM). */
enum class EndReason { STOP_RULE, POLICY, ABNORMAL }

/** §7.1: the end of the analysis. `run`, `direction`: the last run. */
data class AnalysisEnd(val status: RunStatus, val run: Int, val direction: Direction, val reason: EndReason)

enum class ReportState { CONFIRMED, DEMAND }

/** §7.5, ap.md §8.10: the report of the analysis. `Entry.run`: the run of the state (the run that confirmed it, or the
 *  latest complete forward run). `Entry.witnesses`: the witnesses of the key in that run, of every alternative and
 *  method key (the fields of ap.md §8.10: the alternative, the method key, the sink edges, `confirmed`, the end facts;
 *  §9 OUTPUT). The phase-3 output holds every entry, CONFIRMED and DEMAND (§9; ap-history.md F68). */
class Report(val entries: List<Entry>, val end: AnalysisEnd) {
    class Entry(val key: VulnerabilityKey, val state: ReportState, val run: Int, val witnesses: List<SinkWitness>)
}

/** §7.5: built from the COMPLETE forward runs only. */
class ReportBuilder {
    private val confirmed = LinkedHashMap<VulnerabilityKey, Report.Entry>()
    private var demand = LinkedHashMap<VulnerabilityKey, Report.Entry>()          // of the latest complete forward run

    /** A complete forward run, after its confirmation. Its demand set replaces the old one: refutation. */
    fun add(config: RunConfig, result: RunResult) {
        val byKey = result.vulnerabilities.witnessesOf(result.runIndex).groupBy({ it.first }, { it.second })
        val next = LinkedHashMap<VulnerabilityKey, Report.Entry>()
        for ((key, ws) in byKey)
            if (ws.any { it.confirmed }) confirmed.putIfAbsent(key, Report.Entry(key, ReportState.CONFIRMED, config.index, ws))
            else next[key] = Report.Entry(key, ReportState.DEMAND, config.index, ws)
        demand = next                                                               // one step (§7.5 step 3)
    }

    fun build(end: AnalysisEnd): Report =
        Report(confirmed.values + demand.values.filter { it.key !in confirmed }, end)
}

/** §4.3: an item of the worklist. The layer is `facts.layer`. */
data class EdgeDelta(val premise: PremiseKey, val node: CommonInst, val facts: Facts) {
    val zeroToZero: Boolean get() = premise.isZero && facts is Reach
}

/** §4.3: the worklist of one method analyzer: two queues. */
class DeltaWorklist {
    private val unchanged = ArrayDeque<EdgeDelta>()
    private var seen = HashSet<EdgeDelta>()                     // the set of `unchanged`: it discards the repetitions
    private var zeroUnchanged = 0                               // the zero-to-zero items in `unchanged`
    private val zero = ArrayDeque<EdgeDelta>()                  // `normal`: the zero-to-zero items first
    private val other = ArrayDeque<EdgeDelta>()                 // `normal`: then LIFO

    /** A delta of `edges.add`. */
    fun add(d: EdgeDelta) { if (d.zeroToZero) zero.addLast(d) else other.addLast(d) }

    /** An item of the unchanged path; false for a repeat. */
    fun addUnchanged(d: EdgeDelta): Boolean =
        seen.add(d).also { if (it) { unchanged.addLast(d); if (d.zeroToZero) zeroUnchanged++ } }

    /** `unchanged` first. When the step finds `unchanged` empty, the set goes, and a `normal` item comes next. */
    fun removeNext(): EdgeDelta {
        if (unchanged.isNotEmpty()) return unchanged.removeLast().also { if (it.zeroToZero) zeroUnchanged-- }
        if (seen.isNotEmpty()) seen = HashSet()
        return if (zero.isNotEmpty()) zero.removeLast() else other.removeLast()
    }

    val isEmpty: Boolean get() = unchanged.isEmpty() && zero.isEmpty() && other.isEmpty()
    /** A zero-to-zero item in either queue: the priority of the runner (§6.1). */
    val hasZeroWork: Boolean get() = zero.isNotEmpty() || zeroUnchanged > 0
    val size: Int get() = unchanged.size + zero.size + other.size
}

/** The counter of one run (§6.2). `onZero` is the quiescence: it sets the status by `compareAndSet(null, COMPLETE)`,
 *  so the first end of the run wins (§6.3). */
class InFlight(private val onZero: () -> Unit) {
    private val count = AtomicLong(0)
    fun beforeSend() { count.incrementAndGet() }                       // Q1
    fun afterHandler() { if (count.decrementAndGet() == 0L) onZero() } // Q2
}
```

Other names: `SharedObjects` holds the shared objects of §2. `confirm` computes steps 1 and 2 of §7.5 on the links of
a complete forward run and sets `SinkWitness.confirmed`. `handOff` makes the `RunConfig` of the next run by §7.3 and
§7.4: `demandOf` builds the `DemandStore` and `seedsOf` the `SeedIndex` from the stores of the run.
`RecordStore.view` gives the read-only view of a run; `RecordStore.persist` adds the records of `ap.md` §8.7 R1 at a
barrier. `CalleeSubscriptions` and `PublicationIndex` are the path tries of §5.3 and §5.2.
`MethodContextCache.forms(key: MethodKey)` gives the cached forms of §4.8 for a method key, in both directions: the
per-method forms that every context shares and the per-key forms of that context. `RunManager.fail(status)` is the
abnormal end of §6.3: if the compare-and-set of the run status from "no end" to `status` succeeds, it cancels the
`Cancellation` and completes the run; else (after the quiescence or an earlier end) it does nothing. The timeout of the
run (`TIMEOUT`), the memory guard of the run (`OOM`), a runner exception and a throw in the code of the run on the
caller thread (`FAILED`) call it. `RunManager.run(timeout)` joins the runners on every exit (§6.3).

---

## 11. Limits

ARGUED, NOT PROVED:

* SUBSUMPTION. The AP operations simulate the subsumption of the edge stores (`Subsume.subsumesB`, the tree merges T1
  to T5). `Pipeline.quiescent_dominates` needs this as a hypothesis. For a join it needs: if a stored added fact
  dominates the added fact of a subscription, the join with the stored one gives a dominating result. `inside` has
  this property.
  `applicable` has it only through the invariants of run 1 (the policy premises are at the root path,
  `Statics.no_any_above`). So the subscriptions and the links deduplicate exactly (§5.3).
* TREES. The model publishes path facts. The code publishes the deltas of trees: a subscriber gets every delta, and
  the union of the deltas is the tree (`ap.md` §7.2 T4). The subscription side is the same: the delta insert of an
  added fact tree replays only the new paths, and the old paths were replayed before.
* LOCAL STORES. The model has one global `known` set. The code has one store per actor. Each encoded system is
  well-formed (`*_wf`: the premises of a local rule have one owner, and the subscriptions of a join have one owner), so
  each rule reads only the store of one actor. No theorem states this equality.
* THE k-ARY JOIN. The model joins the subscriptions of all premises at once. The code joins them in the conjunction
  store of the caller (§5.4), with the partial matches as its state.
* HANDLERS. The model registers one handler per (actor, topic). The code registers one handler per (runner, callee),
  and a delivery matches every subscription of the runner (P6). This is a batch form of the model's handlers. The
  model's `notify` reads the handler list atomically. The code iterates a `ConcurrentLinkedQueue`, which is weakly
  consistent: an iteration sees every element added before it started. A2 asks for this.
* UNITS. The model has one actor per method. A runner runs several actors one event at a time. This is one of the
  interleavings of the model.
* COUNTER. The link from the counter model to the quiescence of the pipeline (W1 to W3), and the order of Q1 (an
  increment and its enqueue are one step in the model).
* A2 (the shared actions are linearizable) for the lock of P3, and A3 for the Kotlin `Channel`.
* THE CALL PLAN. The reversed plan gives the backward call order of `interpreter.md` §4.9 (the step table of §4.5).
  The model reverses the statements and the bindings (`Reverse.Stmt.rev`, `Reverse.Call.rev`); it has no call plan
  with the inner points of a call.
* THE SOURCE SEEDS at a call, at the method start and at the method exit: the model restricts the statement sources
  (`FSeeds.keepSources`); the others are the same micro edges at another place (`ap.md` §11.2). The exactness of a
  seeded run for `P` (`ap.md` §11.2). The source seeds in a finite sequence: extend it after `K` with every source as
  a seed (`FSeeds.flow_keep_all_iff`), as `PipelineDriver.driver_iteration_upto` does with the sinks.
* THE DRIVER with the static rule and with the conjunctions. The closure equalities hold (`PipelineAP.clDS_iff`,
  `clDN_iff`). The pipeline form of `StaticsIter.iteration_general_DS`, and the iteration with conjunctions (`ap.md`
  §11.2), are argued.

* THE UNCHANGED PATH (§4.3). Its items skip `edges.add`. Its set discards only an item equal to an item that the
  `unchanged` queue already took, so a discarded item gives no new result. The model stores every edge. Not storing
  the item loses no rule: every rule with two premises reads a stored subscription, link, request or publication, or
  the conjunction store, which keeps the literal input of the item when the item is processed.
* THE VULNERABILITY KEY (§4.7). The model has no contexts. The key drops the context; each witness keeps its method key,
  and its confirmation reads the support in that method key, as in the model.
* THE ZERO PUBLICATION (§5.5). The one unrestricted zero-premise publication of §4.6 gives the closure of
  `PipelineAP.sysDB`, because under `Backward.NoZeroBack` no ordinary subscription satisfies the zero premise. The code
  publishes a superset, so it can add results, never lose them.
* THE ANALYZER ACTIONS OUTSIDE THE CLOSURES (§5.5). `D`, `DR`, `Backward.DB`, `Statics.DS` and `NDZ.DNz` (and
  `AnyTaintEx.D6X`, `AnyTaintEx.DRX`) have no end facts, no aliases and no exit-rule removal. So the summary store at
  quiescence is the closure of §5.5 only for the rules that the closures have. The end facts with their trigger and
  layer (§4.5; `ap.md` §11.1), the aliases with their guard (§4.5; `ap.md` §11.2, S2), and the global-state rule with
  the removal of the entry marks (§4.7; `interpreter.md` G2, D35) are outside them.
* THE TAIL `[any-taint]` AND ITS EXCLUSION (`ap.md` W8, §10.11). The pipeline encodes only run 1 (`AnyTaintEx.D6X`)
  and the restricted forward run (`AnyTaintEx.DRX`) with the tail and its exclusion; these are argued:
  * the dominance: `Pipeline.quiescent_dominates` has no instance for `PipelineAnyTaintEx.sysD6X` and `sysDRX`, as
    for `PipelineAP` (SUBSUMPTION, above). Merge rule 2, the subsumption, T5 and the tree key with the exclusion
    (`ap.md` §7.2, §8.1) are not in the model: an `[any-taint]/E` leaf subsumes in its own layer only, as a `*/E` leaf
    does, and in a normal TAINT tree it absorbs no `$` leaf at or below it (a later demotion of the `[any-taint]`
    leaf, for example by an `exact` cleaner, must leave that `$` leaf normal; `ap.md` §7.2 T5, §8.1);
  * the driver with the static rule and with the conjunctions: W6T and the exclusion on `Statics.DS` and on `NDZ.DNz`
    are argued (`ap.md` §11.2), as the driver item above. `AnyTaintND.DNzT` has the conjunction rule of `ap.md` §4.6
    for an `[any-taint]` input, with no exclusion and no W6T;
  * the backward run: the pipeline and the driver use `Backward.DB` with no layer rule. W6 in the backward run and the
    demand layer of every result of a reversed micro edge whose forward target is `[any]` (§4.3) are argued, as the
    backward W6 before F69. They are not a pure layer raise in `Backward.DB`: a demoted requirement can reach the zero
    fact as a demand zero fact, and `Backward.DB` reads the normal zero fact. But wherever such a zero-premise
    requirement reaches the zero fact, the normal zero edge of the zero premise is already at that node (the rules
    `start` and `zpass` from the seed node, with `Backward.ZeroKept`), and `Backward.demOf` and `FSeeds.srcHit` read
    every layer. So the rule only removes normal backward edges, so only records (`ap.md` §11.2);
  * `[any-taint]` in a restricted forward run with ND edges (§5.4): `AnyTaintEx.DRX` has no ND edge, and
    `AnyTaintND.DNzT` has no must-premise and no exclusion (`ap.md` §11.2);
  * the cleaners stage and the rewriter of a call (§4.5) on an `[any-taint]/E` fact: the cleaner rows of `ap.md` §4.7
    with the exclusion (Lean `AnyTaintEx.cleanResX` on a statement cleaner), argued for the call as the other call
    cleaners. The rewriter cleans an `AnyField` action position of a selected SOURCE with `(P, atAndBelow, T)`
    (`interpreter.md` D34), an `AnyField` action position of a selected CLEANER with the cleaner of its row of
    `interpreter.md` §5.2, `(P, below, T)`, as today (`JIRMethodCallRuleBasedSummaryRewriter.kt:105`), and every other
    action position with `(P, exact, T)` (`ap.md` §4.7, §11.2);
  * the confirmation in the seeded forward runs with exclusions, and the backward reuse of the reversed `[any-taint]`
    records: `AnyTaintExExact` does not cover them. R3 reverses a record leaf by leaf: no leaf of a must record and no
    `[any-taint]/E` leaf with `E ≠ {}`; the other leaves reverse (§5.3). The reversal `[any] → $` of a leaf
    `$ → [any-taint]` gives only demand results (§5.3), a reuse limit.

NOT IN THE MODEL: the priorities, the quantum, the order of the worklist (the two queues of §4.3), the memory guards (of
a run and of the barrier), the timeout and the failures (a `Throwable` gives `FAILED`, §6.3). They change the order of
the steps or stop the run. They do not change the closure of a complete run. The barrier has no deadline: it is one
pass over the stores that §7.6 keeps. A slow barrier shortens the next run. After the last run, the analysis can end
later than its budget by the time of that barrier.

DEVIATION FROM TODAY: AN INCOMPLETE RUN 1 gives an empty report and an empty output; the status gives the cause. Today a
timed-out scan outputs the vulnerabilities that it found so far (`TaintAnalyzer.kt:157-223`). A report holds only the
results of complete forward runs (§7.5; `ap-history.md` F67 (4), F68).

PRECISION WITH `[any-taint]`. An exclusion does not demote an `[any-taint]` fact (`ap.md` W8): a strong write into a
field of an `[any-taint]` object, a setter, a two-level write and the cleaners `atAndBelow` and `below` at `P.f` give an
`[any-taint]/E` fact in its layer (Lean `AnyTaintExCases.S.record_app`, `X.two_results`, `CL.atAndBelow_result`,
`CL.below_result`). These are not demotions. Only the demotions of §4.3 (`ap.md` §2.2 THE DEMOTIONS) make `[any]` of
it, in the demand layer and with no exclusion:

* the field-limit cut: the cut path is above the fact, so it drops the exclusion (`ap.md` §4.4;
  `AnyTaintExCases.CUT.run1_cut`, `cut_reports`: `sink(x.f.h)`, confirmed with a larger limit, is a DEMAND entry);
* a cleaner `part` row of `ap.md` §4.7 other than the `atAndBelow` and `below` rows one accessor below the fact: the
  `exact` cleaner at the path of the fact or one accessor below it, and every cleaner two or more accessors below it.
  There is no shape for "every location but one" (`AnyTaintExCases.CL.exact_result`; the demotion is necessary,
  `AnyTaintExExact.CexExactCleaner.cex_exact_cleaner`: `[any-taint]/{f}` would miss the real `x.f.g`, and a normal
  `[any-taint]/{}` would claim the cleaned `x.f`);
* a may target: the `[any]` target of a pass rule (`ap.md` W6);
* a demand-layer input: a demand fact (also another input of a conjunction), a demand-layer summary edge or record, a
  demand link (an `[any]` added fact);
* the must-record demotion (§4.2 `applyRecord`; `AnyTaintEx.recLayerX`).

This is a precision loss, not a soundness loss: the vulnerability stays in the report as a DEMAND entry.

THE ALIAS GAP (an expected false-positive source, `ap.md` §11.1). A WEAK UPDATE keeps an `[any-taint]` object whole: a
deep write through a local (`a = dto.address; a.city = clean`: the alias edge is gen-only, `interpreter.md` G7) or
through a call-result alias such as a getter (`interpreter.md` §3.8 AC2), the constructor pass-over (`interpreter.md`
G8), and the default identity of an unresolved callee (`interpreter.md` §3.7: a library setter `dto.setName(clean)`).
The object keeps `(dto, ., [any-taint], E, T)` in the normal layer, so a sink on the cleaned field is a CONFIRMED
false positive. Before F69 the same finding was a DEMAND entry. A `$` fact has the same gap today.

---

## 12. The formal model

| File | Content |
|---|---|
| `Pipeline.lean` | the rule system with owners, its closure, the state and the steps of the protocol (frozen definitions) |
| `PipelineProofs.lean` | `reach_sound`, `quiescent_complete`, `quiescent_exact`, `no_lost_join`; the counterexamples `PCex.cex_P1` to `cex_P4` and `PCex.step_finds_edge`; the counter model (`Quiesce.creach_inv`, `cnt_zero_iff`, `done_iff`, `done_final`, `bad_early_done`); the dominance theorems (`quiescent_dominates`, `reach_soundD`) |
| `PipelineAP.lean` | the encodings of `D`, `DR`, `DB`, `DS`, `DN`; the `*_wf` theorems; `clD_iff`, `clDR_iff`, `clDB_iff`, `clDS_iff`, `clDN_iff`; the object theorems (`clD_link`, `clD_sub`, `clD_pub` and the other forms) |
| `PipelineStore.lean` | the completeness of the index lookups of §5.3 (`replay_run1`, `deliver_run1`, `replay_restricted`, `deliver_restricted`, `record_lookup`) |
| `PipelineDriver.lean` | `result_D`, `result_DR`, `result_DB`, `driver_iteration`, `driver_iteration_upto` |
| `PipelineNDZ.lean` (with `NDZ.lean`, `NDZeroBase.lean`) | `PipelineNDZ.sysDNz_wf`, `clDNz_iff`, `result_DNz`, `clDNz_ndpub_zero_sub`: the encoding of `NDZ.DNz` (§5.4, §5.5) |
| `ForwardSeeds.lean`, `PipelineSeeds.lean` | the source seeds: `FSeeds.keepSources`, `srcHit`, `srcHit_applies`, `B_src`, `iteration_src`; `PipelineSeeds.driver_iteration_src` (`ap.md` §10.9) |
| `PipelineAnyTaintEx.lean` (with `AnyTaintExDefs.lean`) | the encodings of the closures of the tail `[any-taint]` with its exclusion (§5.5): `sysD6X`, `sysDRX`, `XPObj6`, `XPObj`, `sysD6X_wf`, `sysDRX_wf`, `clD6X_iff`, `clDRX_iff`, the object theorems, `known_D6X`, `known_DRX`, `result_D6X`, `result_DRX`, `result_DRXs`, `no_lost_summary_D6X`, `no_lost_summary_DRX`, `SanityX` |
| `PipelineAnyTaintExDriver.lean` (with `AnyTaintExCov.lean`) | the driver with the tail `[any-taint]` and its exclusion (§7.7): `resultSeqX`, `resultSeqX_runSeqX`, `driver_iterationX`, `driver_iteration_uptoX`, `driver_iteration_srcX` |
| `AnyTaintExDefs.lean`, `AnyTaintExCov.lean`, `AnyTaintExExact.lean`, `AnyTaintExKinds.lean`, `AnyTaintExCases.lean`, `AnyTaintExCases2.lean` | the AP model of the tail `[any-taint]` with its exclusion: THE SPEC CLOSURES (`ap.md` §10.11). This document cites: the closures `AnyTaintEx.D6X`, `DRX`, `DRXs`, the objects `XObj`, `XFact`, the operations `w6tX`, `transferX`, `limitFX`, `cleanResX`, `partX`, `annX`, `checkX`, `emitX`, `emitTX`, `satX`, `restrictX`, `startX`, `recLayerX` (with `DRX.retRec`), the predicates `SatInsideX` (`satX_inside`), `EndExactX`, `RecsExactX`, `SupLinkX`, `SupX`, `Confirmed6X`, `ConfirmedX`, the vectors `Vec`; `AnyTaintExCov.forget6`, `forgetX`, `iteration_reportsX`, `iteration_srcX`, `CexRoute.route_a_false`; `AnyTaintExExact.startX_must_end`, `confirmed_real_valid6X`, `confirmed_realX_valid`, `seq_confirmed_realX_valid`, `RecsFromRunsX`, `specX_rules`, `RecsConcX`, `RecsWFX`, `recs_of_DRX`, `CexExactCleaner.cex_exact_cleaner`; `AnyTaintExKinds.D6X_flow_no_any_taint` (run 1, under S7, S10 and S15: an edge whose premise has the mark `*`, a FLOW edge, has no normal `[any-taint]` conclusion), `D6X_any_conc`, `DRXs_normal_premise`, `DRXs_must_premise` (a normal edge of a restricted run has a `$` premise or a must-premise `[any-taint]` with a concrete mark); the worked programs of `AnyTaintExCases` (§13) and of `AnyTaintExCases2` (the round-1 programs G, C, I and PassRule re-derived in `D6X` and `DRXs`; §7.5, §13) |
| `AnyTaintDefs.lean`, `AnyTaintSim.lean`, `AnyTaintExact.lean`, `AnyTaintND.lean`, `AnyTaintCases.lean`, `PipelineAnyTaint.lean`, `PipelineAnyTaintDriver.lean` | the model of the first F69 form (the demotion at an exclusion, `AnyTaint.D6T`, `DRT`), not the spec closures. This document cites from it only what still states a rule of the spec: the taint edges `AnyTaint.TaintEdges`; the counterexamples `AnyTaintExact.CexApp.cex_app`, `CexApp.record_not_pair_exact`, `CexRev.cex_rev`, `CexSupMark.cex_sup_mark` and the lemma `markSub_conc`; the conjunction `AnyTaintND.DNzT`, `Example`; the transfer with no exclusion `AnyTaintCases.Cut.cut_transfer` (§13 item 31); the vectors `AnyTaint.EmitVec`, `Sanity`. The round-1 programs G, C, I and PassRule of `AnyTaintCases.lean` are only the program terms that `AnyTaintExCases2.lean` imports: their results in the spec closures are those of `AnyTaintExCases2` |

THE TAIL `[any-taint]` AGAINST THE MODEL. The base model has three tail kinds (`.star e`, `.any`, `.exact`). The spec
has four, and the forward `[any-taint]` can carry an exclusion (`ap.md` W8). The spec closures are the refined ones,
`AnyTaintEx.D6X` and `DRXs` (an annotated fact `AnyTaintEx.XFact` is a base fact with its exclusion):

| Spec | Model |
|---|---|
| `*/E` | `.star e` |
| `$` | `.exact` |
| `[any]` (a may) | a `.any` fact in the demand layer, with no exclusion (`AnyTaintEx.normX`) |
| `[any-taint]/E` conclusion (a must) | a `.any` fact in the normal layer with a concrete mark and the exclusion `E` (`AnyTaintEx.XFact`, `carriesB`; in run 1 every normal `.any` conclusion has a concrete mark, `AnyTaintExKinds.D6X_any_conc`) |
| `[any-taint]/E` premise (a must-premise) | a premise with the must flag and the exclusion of `AnyTaintEx.XObj` (`init M j true jex`, `edge M j true jex n f`); it has the tail `.any` and a concrete mark (`AnyTaintExKinds.DRXs_must_premise`) |
| `[any-taint]/E` added fact | `added M a true aex`: `.any`, normal on its link, with the exclusion `aex` |
| the sources with an `[any]` target (`ap.md` S15) | the taint edges `AnyTaint.TaintEdges` (`AnyTaintEx.w6tX` reads them) |
| the backward run (no `[any-taint]`) | `Backward.DB`: no must flag, no exclusion; the driver reads each forward run with them dropped (`AnyTaintExCov.forget6`, `forgetX`) |

In the model `AFact.complete` is false on every `.any` fact: it is the backward reading of COMPLETE only. With the tail
`[any-taint]` the forward records and the confirmation read only the layer: the normal exit edges of a run, `.any`
included, are exact records, or END-EXACT records for a must-premise, on the locations that their exclusions admit
(`AnyTaintEx.RecsExactX`; `AnyTaintExExact.recs_of_DRX`), and a confirmed vulnerability has a normal sink edge
(`AnyTaintEx.Confirmed6X`, `ConfirmedX`). The backward records keep the base reading.

---

## 13. Test plan (TDD)

1. SCHEDULE FUZZING. A test runner picks the next event at random (seeded) from all channels and queues. It runs the
   direct calls as events too. For small programs (the programs of `ap.md` §6.3, §6.4 and the backward cases), compare
   the result of many seeds with a reference: the naive fixed point of the closure. Every seed must give the same
   edges, summaries and vulnerabilities.
2. PROTOCOL TESTS. A mock storage that breaks P1, P2, P3 or P4 loses a summary in the fixed schedule of the
   counterexample. The real storage does not.
3. THE `[any]` DELIVERY. In a restricted run (`inside`), a caller fact with `[any]` above the premise of a summary that
   the callee publishes AFTER the subscription, with 10 or more subscriptions: the caller gets the summary (P4). The
   same with an `[any-taint]` caller fact and the summary of its must-premise. With an `[any-taint]/E` caller fact, a
   premise below it through an accessor in `E` gets no summary, and a premise through another accessor gets it.
4. SEVERAL PREMISES. A summary `{j1, j2} → g`: premise 1 matched by a delivery, premise 2 by a replay, with the
   conclusion in two deltas: the caller applies both deltas (§5.4).
5. RECORDS. A forward record does not apply in its forward form in a backward run; its reversal applies. A backward
   record applies to a forward fact only through its reversal. A record applies by `inside` in a restricted run
   (§5.3).
6. COUNTER. A handler that sends after a delay: the run does not end before the send (Q2). A new `RunManager` made
   after an aborted one (test harness) analyzes every method (§6.3, §7.6).
7. HAND-OFF. Programs 1 and 2 of `ap.md` §6.3, §6.4: the demand of run 3 equals `Backward.dem1_exact` (program 1) and
   `dem2_exact` (program 2); run 3 reports the vulnerability (`Backward.p1_found`, `p2_found`).
8. MODES. A request in a restricted run fails the assert. A backward run has no sink check. The zero fact enters every
   callee in the backward run. The reversed plan of a JVM call gives the steps of `interpreter.md` §4.9 in its order
   (the table of §4.5), with the reversed source results and the seeds at the rule point `BOUND`. The reversed alias
   edges apply to every requirement; the forward ones only to the results that AC3 and AC4 select.
9. STOP RULE. A forward run whose vulnerabilities all have a confirmed sink edge stops the iteration, also when they
   have demand-layer sink edges too (§7.1).
10. SOURCE SEEDS. In forward run 3, a source that backward run 2 did not reach does not fire; a source on the witness
    of a reported vulnerability fires, and run 3 reports the vulnerability. A requirement that reaches a source records
    exactly one hit for that (method key, statement, source edge) (§4.7). A source at a call, at a method entry, at a
    method exit and at a read each records its hit. Two sources of one statement that give the same zero result both
    record a hit.
11. REGRESSION. The existing analysis tests, through phase 3 (`bidirectional-task.md` phase 4).
12. END OF A RUN AND OF THE ANALYSIS. After the memory guard ends a run (`OOM`), a handler that throws
    `Cancellation.Cancelled` stops its runner, and the run ends `OOM` before its timeout. A `RunManager.fail` after the
    quiescence leaves the run COMPLETE (the first end wins). A handler that throws ends the run `FAILED` before its
    timeout, and the other runners stop. A runner that does not stop at the join makes the run `FAILED`. An exception at
    the barrier returns the report of the earlier runs with `AnalysisEnd.reason == ABNORMAL` and the status FAILED; so
    does an `Error` at the barrier (a stub `RecordStore` whose `persist` throws `OutOfMemoryError`): the report so far,
    `ABNORMAL`, the status `FAILED` (not `OOM`). A hit of the barrier memory guard (a `Cancellation.Cancelled` at a
    barrier checkpoint, or a cancel after the last one) gives the report so far, `ABNORMAL` and `OOM`. A throw in
    `RunManager(...)`, in `run(...)` on the caller thread, or a policy with `fieldLimit(1) < 1` gives `FAILED` and the
    report so far (empty for run 1), and no runner is alive after the return. A stop by the stop rule and by the policy
    gives `STOP_RULE` and `POLICY` (§6.3, §7.1).
13. REPORT. Run 1 complete (one CONFIRMED and one DEMAND vulnerability), run 2 complete, run 3 incomplete: the report
    is that of run 1, and run 3 refutes nothing. `continueAfter` is never asked after a backward run (§7.1, §7.5).
    Run 1 incomplete (TIMEOUT): the report has no entry, `end = (TIMEOUT, 1, FORWARD, ABNORMAL)`, and the output is
    empty (§7.5 AN INCOMPLETE RUN 1).
14. VULNERABILITY KEY AND WITNESSES. One sink statement that two contexts reach is one vulnerability; a confirmed
    witness in one context makes it CONFIRMED. Two alternatives of one sink rule that trigger on two bases with the
    same premise set give two witnesses, and the store does not fail (§4.7).
15. WORKLIST. The `unchanged` items come before the `normal` items; a loop of statements that do not touch a base
    ends; the set stays across two `Work` events. A fact on a dead local still reaches a later sink (no liveness check,
    §4.3).
16. EMPTY METHODS. A call whose only callee is a native method is an unresolved call: the pass rules and the default
    identity apply. A call with a native callee and a callee with a body links only to the second one (§4.4).
17. END FACTS AND ALIASES. A sink with an end-fact action that triggers on a demand-layer sink edge gives a
    demand-layer end fact on `{zero}`. A demand-layer summary result that is equal to its start fact goes to the
    aliases; a normal one does not (§4.5).
18. GLOBAL-STATE RULE. A conjunctive exit sink `ContainsMark(S.<C>, STATE) ∧ ContainsMark(Result, T)`: at an exit
    where only the `S` literal holds on a zero-premise item, the `S` part leaves the summary edge and is stored as the
    literal input; a later item with `Result` tainted completes the combination with it (§4.7). A CALLER-SET state
    (`root(){ acquire(); release(); after(); }`, where `acquire` sets the state, `release` has the exit sink and `after`
    a sink on the same position): the exit sink of `release` evaluates the state, the state is not dropped, and the
    caller still sees it after the call (the sink of `after` reports) (§4.7; `ap-history.md` F68).
19. PRESCAN RELEASE. After the prescan info is gathered and the prescan state is released (§9 PRESCAN MEMORY), weak
    references to the prescan AP manager, to one prescan runner and to one prescan method context are cleared after a
    GC (poll a few times).
20. PHASE-3 OUTPUT AND STATUS. The output holds every entry of the report, CONFIRMED and DEMAND (a vulnerability whose
    taint passes only through a pass rule with an `AnyField` target, a may `[any]`, `ap.md` W6, is output with the
    state DEMAND; a vulnerability from a source with an `[any]` target can be CONFIRMED, items 22, 23), each with the
    simple trace; the method key is that of a confirmed witness, else of the first witness; the log has the count per
    state. The status
    maps `COMPLETE` to `OK`, `TIMEOUT` to `TIMEOUT`, `OOM` to `OOM` and `FAILED` to `EXCEPTION` (one `Report` per
    status). A throw in the setup of the analysis gives an empty output and `EXCEPTION` (§9).
21. CONJUNCTIVE EXIT SOURCE. An exit source `AssignMark(U, Result) if ContainsMark(Argument(0), A) ∧
    ContainsMark(Argument(1), B)`, with the exit items `(arg(0), $, A)` under the premise `i0` and `(arg(1), $, B)` under
    `i1`: the full combination gives the ND summary `{i0, i1} → ret.$ (U)`, and the caller applies it by E6; each
    literal input stays in the conjunction store; the exit items stay in the summary (§4.4).
22. THE `[any]`-TARGET SOURCE IS CONFIRMED (analysis test; program G, a Spring DTO through a getter; the results in the
    spec closures `AnyTaintEx.D6X`, `DRXs` are those of `AnyTaintExCases2`). `root(): dto = srcAny(); x = get(dto);
    sinkAny(x)`, `get(p): return p.f`, where `srcAny` is a source with an `[any]` target and `sinkAny` a
    `ContainsMarkOnAnyField` sink. Run 1 reports the vulnerability as DEMAND (the getter summary is the case `above`;
    `AnyTaintExCases2.G.run1_flow_above`, `G.run1_not_confirmed`). Backward run 2 hands off the demand
    `(D-c = (p, .f, [any], T), D-p = (ret, ., [any], T))` of `get` (the backward run has no `[any-taint]`, §7.4; it
    reads the refined run 1 with the exclusions dropped: `G.HX_exact`, `G.handoffX_get`). In run 3 the added fact
    `(p, ., [any-taint], {}, T)` of `get` emits the must-premise `(p, .f, [any-taint], {}, T)` (`G.run3_must`,
    `G.run3_must_supported`), the sink edge in `root` is normal (`G.run3_sink_normal`), and run 3 CONFIRMS the
    vulnerability (`G.run3_confirmed_handoff`); the report has it as CONFIRMED and the iteration stops (§7.1).
    Program C (the sink in the callee: `use(o): sinkAny(o.f)`) is CONFIRMED in run 3 too, with the must-premise
    supported through its link (`AnyTaintExCases2.C.run3_supported`, `C.run3_confirmed_handoff`). Program I (`get`
    with `return p`) is CONFIRMED in run 1, with no DEMAND entry, so the iteration stops after run 1
    (`AnyTaintExCases2.I.run1_flow`, `I.run1_confirmed`, `I.run1_no_demand`).
23. THE SETTER KEEPS `[any-taint]` WITH AN EXCLUSION (analysis test; program S of `AnyTaintExCases`, a Spring DTO
    through a setter). `root(): dto = srcAny(); dto.setName(c); sink(dto.name); sink(dto.email)`,
    `setName(n): this.name = n`, `c` clean. The run-1 summary `(this, ., *, {}, *) → (this, ., */{name}, *)` of
    `setName` on the added fact `(this, ., [any-taint], T)` gives `(this, ., [any-taint], {name}, T)` in the normal
    layer, and `dto` is `(dto, ., [any-taint], {name}, T)`, normal (`AnyTaintExCases.S.record_app`, `run1_dto_ann`).
    Run 1 reports no vulnerability for `sink(dto.name)`, in no layer (`S.run1_name_not_reported`; it is not real,
    `S.name_not_real`), CONFIRMS `sink(dto.email)` (`S.run1_email_confirmed`) and has no DEMAND entry
    (`S.run1_no_demand`), so the driver stops after run 1 (`STOP_RULE`). The same through a deeper setter
    (`AnyTaintExCases.SD.run1_email_confirmed`, `SD.same_result`). Program B also has no DEMAND entry in run 1
    (`AnyTaintExCases.B.inv1`), so the driver never starts its run 3: its run-3 results are a test of one restricted
    run with the broad demand `(D-c = (this, ., [any], T), D-p = (this, ., [any], T))` of `setName` given by hand and
    the records of run 1 (`AnyTaintExCases.B.run3_must`, `B.run3_anyE_confirmed`, `B.run3_name_not_reported`).
24. SOURCE AGAINST PASS RULE (program PassRule; the results in the spec closure `AnyTaintEx.D6X` are those of
    `AnyTaintExCases2.PassRule`). The same micro edge `P.$ (T) → Q.[any] (T)` as a source (target `[any-taint]`)
    gives a normal edge, and run 1 confirms the vulnerability; as a pass rule (target `[any]`) it gives a demand edge,
    and the vulnerability stays DEMAND (`AnyTaintExCases2.PassRule.source_vs_pass`, `source_confirmed`,
    `pass_demand`, `pass_not_confirmed`). In the backward run the reversal `Q.[any] (T) → P.$ (T)` of the pass rule
    gives the requirement `(P, ., $, T)` in the demand layer (its forward target is `[any]`, §4.3), so the backward
    summary through it is not a record, and no later forward run confirms the vulnerability through the pass rule. The
    core reads only `MicroEdge.forward` for this (no rule-kind flag).
25. TWO PREMISE KEYS AND THE MUST RECORD. In a restricted run, an `[any-taint]` added fact and an `[any]` added fact at
    one path give two initial facts, two premise keys and two publications (§4.1, §4.6); two must-premises of one path
    with different exclusions give two premise keys. A forward record with an `[any-taint]` premise applied to an
    added fact that lies inside its premise (`applicable`, not `inside`) gives a demand-layer result with no exclusion
    (§4.2; the program of `AnyTaintExact.CexApp.cex_app`). `rec.reversedAt` gives no reversal of any leaf of it in a
    backward run (§5.3; `AnyTaintExact.CexRev.cex_rev`). R3 is LEAF BY LEAF: the zero-premise summary of
    `mk(): d = srcAny(); d.setName(c); d.k = srcU(); return d` (`srcU` a source with the target `$` and the mark `U`)
    has the two leaves `(ret, ., [any-taint], {name, k}, T)` and `(ret, .k, $, U)`, both normal; `rec.reversedAt`
    gives the reversal of the `$` leaf only, and that reversal applies in the backward run. In run 1 the caller
    `root(): r = mk(); sink(r.name); sink(r.email)` applies this summary to its zero fact with the exclusion of the
    leaf (`ap.md` §4.1, the case below: the target exclusion of the edge): `(r, ., [any-taint], {name, k}, T)`, normal,
    so `sink(r.name)` is not reported and `sink(r.email)` is CONFIRMED. The reversal `[any] → $` of a leaf
    `$ → [any-taint]` applies to an `[any]` requirement with a demand-layer result, and not to a `$` requirement
    (§5.3). No backward edge has the `[any-taint]` tail.
26. THE SUPPORT NEEDS THE SAME MARK. A must-premise with the mark `*` inside an `[any-taint]` added fact is not
    supported (§7.5; `AnyTaintExact.CexSupMark.cex_sup_mark`). A `$` member below an `[any-taint]/E` added fact through
    an accessor in `E` is not supported; through another accessor it is.
27. VECTORS. The emission table (§4.4; `AnyTaint.EmitVec`; with the exclusion `AnyTaintEx.Vec.emit_at`,
    `emit_above_excluded`, `emit_above_exact`), the A2 rows (`AnyTaintEx.Vec.setter_keep`, `read_excluded`,
    `read_admitted`, `above_star_excl`, `below_keeps`, `below_new_fact`, `cut_drops`), the source result as a normal
    `[any-taint]` edge in run 1 and in a restricted run and the pass-rule result as a demand edge (`AnyTaint.Sanity`),
    the encodings with the exclusion (`PipelineAnyTaintEx.SanityX.d6x_ann`, `drx_ann`), and the conjunction of an
    `[any-taint]` input that its literal does not cover: a normal result, confirmed (`AnyTaintND.Example`).
28. THE TWO-LEVEL WRITE (program X of `AnyTaintExCases`; an AP-level test: the write `x.f.g = c` is ONE statement, a
    synthetic statement summary on the AP with the keep edges `x.* →_{f} x.*` and `x.f.* →_{g} x.f.*`).
    `x = srcAny(); x.f.g = c; sink(x.f.g); sink(x.f.h); sink(x.k)`: the write gives exactly
    `(x, ., [any-taint], {f}, T)` and `(x, .f, [any-taint], {g}, T)`, both normal (`AnyTaintExCases.X.two_results`).
    `sink(x.f.g)` is not reported (`X.fg_not_reported`); run 1 CONFIRMS `sink(x.f.h)` and `sink(x.k)`
    (`X.fh_confirmed`, `X.k_confirmed`). On the JVM a two-level write goes through a local (`t = x.f; t.g = c`): the
    write into `x` is the weak alias write (`interpreter.md` G7), so `x` keeps `(x, ., [any-taint], {}, T)`. A JVM
    analysis test of this program expects `sink(x.f.g)` CONFIRMED, the documented false positive of the alias gap
    (§11 THE ALIAS GAP), and `sink(x.f.h)` and `sink(x.k)` CONFIRMED.
29. THE READS (program R of `AnyTaintExCases`). After the setter of item 23, `y = dto.name` gives nothing and
    `z = dto.email` gives `(z, ., [any-taint], {}, T)`, normal (`AnyTaintExCases.R.reads`). `sinkAny(y)` is not
    reported (`R.y_not_reported`); run 1 CONFIRMS `sinkAny(z)` (`R.z_confirmed`).
30. THE CLEANERS (program CL of `AnyTaintExCases`). `x = srcAny(); clean(x.f, reach); sink(x.f); sink(x.f.g);
    sink(x.k)`: `atAndBelow` gives `(x, ., [any-taint], {f}, T)`, normal, so only `sink(x.k)` is reported, and it is
    CONFIRMED (`AnyTaintExCases.CL.atAndBelow_result`); `below` gives it and
    `(x, .f, $, T)`, both normal, so `sink(x.f)` is CONFIRMED (`CL.below_result`); `exact` gives `(x, ., [any], T)` in
    the demand layer, so every sink is a DEMAND entry (`CL.exact_result`).
31. THE CUT (program CUT of `AnyTaintExCases`; an AP-level test: the AP field limit with `L = 0` on the results of
    item 28; no run has `L = 0`, since run 1 needs `L >= 1`, §7.1). Program X with the field limit 0: the cut gives
    `(x, ., [any], T)` in the demand layer with no exclusion (`AnyTaintExCases.CUT.run1_cut`), and `sink(x.f.h)` is a
    DEMAND entry (`CUT.cut_reports`). A JVM analysis test of the cut runs with `L = 1` and a fact deeper than the
    limit: the source `dto.f.g = srcAny()` gives `(dto, .f, [any], T)` in the demand layer with no exclusion
    (`AnyTaintCases.Cut.cut_transfer`, a transfer with no exclusion), so a sink below `dto.f` is a DEMAND entry.

---

## Appendix A. Today's analyzer

The analysis of the current core (`core/opentaint-dataflow-core`, the code of `origin/main`). The design of this
document starts from it.

ENTITIES.

* `TaintAnalysisUnitRunnerManager` (one per analysis): spawns one `TaintAnalysisUnitRunner` per unit (a package; an
  unknown unit is not analyzed). It routes the work between the units and counts the events. It ends a run at
  quiescence, at a timeout or at the memory guard. The prescan and the full scan reuse it after `resetApManager`.
* `TaintAnalysisUnitRunner` (one coroutine per unit): a channel and a priority queue. The events:
  `MethodWithContext`, `ExternalInputFact` (zero, fact, side-effect requirement), `MethodAnalyzer`,
  `NewSummaryEdgeEvent`, `NewSideEffectRequirementEvent`, `NewSideEffectSummaryEvent`, `LambdaResolvedEvent`,
  `MethodAnalysisDelayed`, `DelayedAnalysisResume`.
* `NormalMethodAnalyzer` (one per `MethodEntryPoint`): the tabulation over four edge kinds (zero-to-zero,
  zero-to-fact, fact-to-fact, ND); a LIFO worklist; `MethodAnalyzerEdges` with merge and subsumption; the initial-fact
  abstraction; the fact-depth delay. The summaries, the side-effect requirements and the side-effect summaries wait
  until the worklist is empty. `EmptyMethodAnalyzer` publishes the identity summaries of the most abstract facts.
* `SummaryEdgeStorageWithSubscribers` (callee side, one per entry point, in the unit storage): one writer (the runner
  of the callee) under a monitor, and the subscribers in a `ConcurrentLinkedQueue`. The new part of an insert goes to
  every subscriber as an event.
* `SummaryEdgeSubscriptionManager` (caller side, two per runner: internal and external): registers its handler on the
  first subscription to a callee, inserts the caller fact (delta), replays the callee storage synchronously, and
  matches every delivered summary against its subscriptions when the event runs.

PIPELINES.

* A caller fact goes to the callee as an initial fact: synchronously in the same unit, as an `ExternalInputFact`
  event across units. The subscription and its replay come first.
* A summary goes from the exit of the callee to its storage, then as an event to every subscribed runner, then to the
  caller analyzers whose subscriptions match.
* The refinements travel up as side-effect requirements (the exclusion of an initial fact) and side-effect summaries
  (the mark-unfold request after `[any]`). A zero-to-fact caller with a concrete fact answers the unfold request
  directly to the method that asked.
* The counter: increment before the send, decrement after the event. Zero ends the run, or starts a deepening round
  when analyzers are delayed.

DEFECTS FOUND (none of them is in the design above).

* P3: the replay read of a callee storage takes no lock. It reads fastutil maps and plain fields while the writer
  changes them (`SummaryEdgeStorageWithSubscribers.factEdges` and the other finders; the
  `ConcurrentReadSafeInt2ObjectMap` reads). This works on x86 and HotSpot, but the Java memory model does not guarantee
  it: a replay can miss an old summary, and no notification gives it again.
* P4: the delivery index (`AccessTreeIndex.findStartsWith`, `MethodTreeAccessPathSubscription.kt`) follows literal
  accessors and misses a caller fact with `[any]` above the summary premise; the replay treats `[any]` as a wildcard.
  When a sub-storage has 10 or more entries, a summary published after the subscription is lost for that fact. The
  summaries with several premises (by base on the replay, by prefix on the delivery) and the requirements (exact
  children on the replay) also use different filters on the two paths.
* The tree summary storage does not notify when only the exclusion of a summary grows; today the requirement channel
  covers it. The new core has no such channel, so every growth must be a delta.
* `handleUnchangedStatementEdge`: the unchanged edge normally goes through `addSequentialUnchangedEdge`, which is
  correct. When the edge post-processor returns a NEW edge object, the code propagates the input edge (as a changed
  edge) and drops the processed one. `JIRMethodSummaryEdgeProcessor` returns a new object for every fact-to-fact edge
  at an exit. So a PARTIAL exit compatibility filter is lost for a fact that is unchanged at the exit; a full
  rejection (an empty list) works. Precision only. The new core has no post-processor (`interpreter.md` D14).
* Across runs: `analyzerEnqueued`, the runner `factLimit`, the sticky `status` and the counters survive. A failed
  runner cancels the shared scope. A runner that does not stop can run into the next run.
* `EventComparator` reads mutable keys. `ConcurrentReadSafeObject2IntMap` can hang the interner (non-volatile reads in
  a retry loop).

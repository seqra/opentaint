# Analyzer core — specification

Status: design spec of the new analyzer core (phase 2 of [bidirectional-task.md](../bidirectional-task.md)). This
document is normative. It uses two other specs and does not repeat them:

* [`ap.md`](ap.md): the fact, the edge, the AP operations, the runs, the stores and their theorems;
* [`interpreter.md`](interpreter.md): the micro edges of the IR and the order of the rules.

This document defines the ENTITIES of the analyzer, who owns which data, the METHOD ANALYZER, the COMMUNICATION
PIPELINE between the methods, the scheduling and the end of a run, and the ITERATION DRIVER with the hand-offs between
the runs. Appendix A gives the analysis of today's analyzer that the design starts from.

The formal model is in [`spec/lean`](lean): `Pipeline.lean`, `PipelineProofs.lean`, `PipelineAP.lean`,
`PipelineStore.lean`, `PipelineDriver.lean`. Every theorem named here is machine-checked and constructive (`ap.md` §10
defines the term). §11 lists what is argued and not proved.

Language: ASD-STE100 Simplified Technical English.

---

## 0. Scope

The analyzer core:

1. runs one run (`ap.md` §6): one direction, one field limit, one mode (run 1 or restricted), to a fixed point;
2. exchanges the edges between the methods of a run with no loss (§5);
3. detects the end of a run (§6);
4. runs the sequence of runs and computes the hand-off from each run to the next (§7).

Out of scope:

* the IR interpreter (`interpreter.md`); §4.9 gives only its interface to the core;
* the prescan, the rule reduction and the `TaintAnalyzer` wiring (phase 3); §9 gives the interface;
* the trace resolution (phase 5); §7.6 lists the data that the core keeps for it;
* the iteration policy: the field limit of each run, the budget and the stop rule for a budget (`ap.md` §6.6). The
  driver takes the policy as a parameter (§7.1).

### 0.1 Assumptions

| # | Assumption |
|---|---|
| A1 | The AP operations and stores satisfy `ap.md`. The interpreter satisfies `interpreter.md` I1–I13. The proofs of this document use only the closures of `ap.md` (Lean `D`, `DR`, `Backward.DB`, `Statics.DS`, `ND.DN`). |
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
| method key | `ap.md` §1: the `MethodEntryPoint` of the method (context and FORWARD entry statement). The backward run uses the same key. Its start nodes are the forward exits (§4.4). |
| unit | A group of methods that one runner owns (today a package; `UnitResolver`). |
| runner | The single coroutine of one unit in one run. It runs one event at a time. |
| actor | The owner of a set of objects. Each method analyzer is an actor. Its runner runs it. |
| method analyzer | The actor of one method key in one run (§4). It owns the intra-procedural edges and every RUN store of its method. |
| event | One message in the channel of a runner (§5.1). Its HANDLER is the code that the runner runs for it. |
| subscription | A caller-side record `(caller edge, call statement, added fact)` (`ap.md` §8.4). |
| publication | A summary edge that the callee gives to its subscribers. In a restricted run it is the result of the restriction (`ap.md` §6.4). |
| storage with subscription | The callee-side store of the publications, with the list of the subscribed runners (§5.2). |
| replay | The read of the storage when a subscription is new (§5.3). |
| notification | The send of a new publication to every subscribed runner (§5.2). |
| delivery | The event that carries a notification to one runner (§5.3). |
| quiescence | The state of a run with no event in a channel or a local queue, no running handler, no worklist item and no pending publication (§6.2). |
| barrier | The point between two runs: the first run is quiescent, and the next run has not started (§7.2). |
| hand-off | What one run gives to the next run: the demand and the seeds (`ap.md` §8, §9.2). The records are PERSISTENT, not a hand-off (`ap.md` §8.7). |
| complete run | A run that ended at quiescence. A run that ended by a timeout, the memory guard, a cancellation or an exception is INCOMPLETE. |

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
| `VulnerabilityStore` | analysis (PERSISTENT) | any runner adds (concurrent); the driver reads it at a barrier | the vulnerability records, with the run of each sink edge (§4.7) | replaces the buckets of `TaintAnalysisUnitStorage` |
| `RunManager` | one run | the caller thread and the runners | unit routing, runner spawn, the map of the `SummaryStorage`s, the in-flight counter, the run status (§6) | `TaintAnalysisUnitRunnerManager` |
| `UnitRunner` | one run | its coroutine | the event loop, its analyzers, its `SubscriptionManager` | `TaintAnalysisUnitRunner` |
| `RunMethodAnalyzer` | one run | the runner of its unit | the RUN stores of its method (§4.1) | replaces `NormalMethodAnalyzer`, `EmptyMethodAnalyzer` |
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
* O5. After a complete run, the driver reads every store of the run. No runner runs then (§7.2).

---

## 3. The run configuration

```kotlin
/** One run of ap.md §6.6. `Direction` is the enum of ap.md §8.7. */
class RunConfig(
    val index: Int,                          // 1, 2, 3, ...; the direction is FORWARD for an odd index
    val fieldLimit: Int,                     // ap.md §4.4; run 1 needs fieldLimit >= 1 (ap.md S12 (d))
    val demand: DemandStore?,                // null only in run 1
    val records: RecordStore,                // a read-only view; run 1 reads no record
    val seeds: SeedIndex,                    // the backward run only (§4.7)
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
| records (`ap.md` §8.7 R3, R4) | none | the FORWARD records by `byEntry`, and the reversed BACKWARD records by `byExit`; each when `applicable(p, a)` or `inside(p, a)` | the BACKWARD records by `byEntry`, and the reversed FORWARD records by `byExit`; each when `applicable(p, a)` or `inside(p, a)` |
| mark and position requests, static rule | yes (`ap.md` §4.5, §4.10) | no (assert) | no (assert) |
| sinks | the sink check (`ap.md` §4.9) | the sink check | no sink check; the seeds (`ap.md` §9.2) |
| type filters | yes | yes | no |
| liveness pruning (`isLive`) | yes, as today | yes, as today | no |

---

## 4. The method analyzer

The method analyzer `RunMethodAnalyzer` replaces `NormalMethodAnalyzer`. It keeps the pattern of today: the
intra-procedural edges stay inside the analyzer, the analyzer has a worklist, and its runner runs it in steps. One
class serves every direction and every mode. The `RunConfig` and the interpreter of the direction give the
differences.

### 4.1 State

| Field | Store | Content |
|---|---|---|
| `edges` | method edge store (`ap.md` §8.1) | the edges per (statement, premise key, layer, base, exclusion, mark exclusion) |
| `initials` | initial fact store (`ap.md` §8.2) | the initial facts of the run: zero, emissions, answers |
| `links` | added fact store (`ap.md` §8.3) | each added fact with its links: the caller reference and the layer of the added fact on the link |
| `summaries` | run summary store (`ap.md` §8.5) | the summary edges BEFORE the restriction, per premise key and layer |
| `requests` | request store (`ap.md` §8.8) | run 1 only: the standing mark and position requests and their answers |
| `conjunctions` | conjunction store (`ap.md` §8.9) | the standing literal facts; the combinations of the callee summaries with several premises (§5.4) |
| `worklist` | `EdgeCollection` (today) | the new edge deltas to process |
| `pendingPublications` | | the publications that the analyzer has not yet given to its `SummaryStorage` (§4.6) |
| `queued` | | true while the analyzer has a `Work` event in its runner (§6.2) |
| `context` | `MethodContextCache` entry and run part | the method graph, the alias analysis, the lambda resolutions, the rule context of the run (§4.8) |

The subscriptions are not in the analyzer. They are in the `SubscriptionManager` of the runner of the caller
(`ap.md` §8.4; §5.3).

### 4.2 Handlers

The runner calls these handlers. Each handler is part of one event (§5.1).

| Handler | When | Actions | `ap.md` |
|---|---|---|---|
| `addRootZero()` | the run starts at a root | the zero fact is an initial fact | §6.1 |
| `addLink(link)` | a caller binds a fact into this method | add the link (exact deduplication). A new added fact: emit its initial facts (§4.4). A new link: check the standing requests (§4.6). The zero added fact emits the zero fact. No request matches it. Its link serves the support (§7.5). | E1, E2 |
| `addZeroEntry()` | backward: the zero fact of a caller reaches a call to this method | the zero fact is an initial fact (rule `zin`) | §9.2 |
| `addRequest(premise, request)` | run 1: a callee climbs a request through a link of this method | store it (exact deduplication); check it against every link of this method (§4.6) | E5, E7 |
| `applySummary(sub, pub)` | the `SubscriptionManager` matched a publication with a subscription of this method | one premise: apply the summary to the added fact (`ap.md` §4.3), then POST (§4.5). Several premises: the combination of §5.4. | §4.3, E2, E4, E6 |
| `applyRecord(sub, record)` | a new subscription of this method; the record (already reversed by the `SubscriptionManager` if it is from the other direction) covers or contains its added fact | apply the record, then POST | §8.7 R3, R4 |
| `step(quantum)` | a `Work` event | process at most `quantum` worklist items (§4.3) | §6.1 (S6: any order) |

A new initial fact `j` (from any handler) is event E3: the analyzer adds the start edges of `j` to the worklist
(§4.4).

### 4.3 The worklist and the step

* An item of the worklist is an edge delta: (premise key, layer, node, `EdgeTree`). The edge is the fact BEFORE the
  statement of the node, as today.
* `edges.add` returns the delta of the merge (`ap.md` §7.2 T4). A null delta adds nothing, and the analyzer drops it.
  Else the analyzer adds the delta to the worklist.
* The forward runs prune an edge whose base is not live at the node (`isLive`, today `isReachable`). The backward run
  does not prune.
* The step takes one item and applies its node:
  * a non-call statement: the statement transfer (`ap.md` §4.2; `interpreter.md` §2, §4.4) with the primitives that
    the interpreter puts at the statement (`interpreter.md` §5); then the field limit at the cut points (`ap.md` §4.4);
  * a call statement: the call steps (§4.5).
* A result AT AN END NODE of the run (§4.4) goes through the end rules and makes the summary edges (§4.6). This holds
  for every handler that makes such a result: `step`, and also `applySummary`, `applyRecord` and `zret` when the end
  node is a call (for example a backward end node whose forward entry statement is a call). An end node is a
  statement like every other: its transfer or its call steps come first. (Today: `handleStatementEdge`, the edge
  post-processor, then `tryEmmitSummaryEdge`.)
* Each result goes to every successor node in the graph of the run, through `edges.add`.
* "Unchanged" propagation may skip the store, as today (`ap.md` §8.1). The propagated item must be the processed item
  (today `handleUnchangedStatementEdge` propagates the input edge instead). The set that deduplicates the unchanged
  items lives for one `Work` event (§6.2).
* The analyzer does not delay an edge by its depth. There is no fact-depth limit: the field limit of the run is the
  only depth bound (`ap.md` §4.4; `bidirectional-task.md` §5 item 1).

### 4.4 Initial facts, start nodes and start rules

Initial facts:

* RUN 1. For an added fact `a`: the policy fact `(a.base, [], *, {}, *)`, or the zero fact for the zero fact
  (`ap.md` §6.2). The request answers are initial facts too (`ap.md` §4.5, §4.10).
* RESTRICTED RUN. For an added fact `a`, the emission query `near(a.base :: a.path)` returns demand patterns of the
  method (`ap.md` §8.6). Each one whose emission is not empty gives one initial fact `a ∩ D-c` (`ap.md` §6.3).
* THE ZERO DEMAND. `(zero, none)` is part of the demand of EVERY method key, also when the demand store has no entry
  for it. So the zero added fact always emits the zero fact. The zero fact of a root is an initial fact.
* BACKWARD RUN. As a restricted run. Also, `addZeroEntry` makes the zero fact an initial fact (rule `zin`).
* `initials.add` deduplicates. Each new initial fact starts with its start fact (`ap.md` §6.5) at every start node of
  its kind, then the start rules.

Start nodes, end nodes and their rules (the interpreter gives them, §4.9):

| Direction | Start nodes | Start rules | End nodes | End rules |
|---|---|---|---|---|
| forward | the entry statement of the method key | `interpreter.md` §4.3: the zero fact with the entry sinks and the entry-point sources; another fact with the filter by the context type | every normal exit | the exit order of `interpreter.md` §4.7; no summary at an exceptional exit |
| backward | the zero fact: every forward exit, normal and exceptional (`ap.md` S4). Another initial fact: every normal exit (exceptions are out of scope, `interpreter.md` G1) | the seeds of the exit sinks of the method (§4.7); the reversed exit sources and the reversed end-fact edges of the exit sinks (`interpreter.md` §4.9, rule roles) | the forward entry statement | the reversed entry-point sources and the reversed end-fact edges of the entry sinks (`interpreter.md` §4.9); no context filter (the backward run has no type filter) |

Exits per language:

* JVM: the normal exit is `JMethodExitNormalInst`; the exceptional exit is `JMethodExitExceptionalInst`.
* Go: each `Return` instruction is a normal exit; each `Panic` instruction is an exceptional exit.

The backward graph is the reversed graph (`ApplicationGraph.reversed`) with the EXIT WIRING. A node that reaches no
forward exit gets an edge to an exceptional exit (`interpreter.md` I11 (e); today `JIRBackwardExitWiringGraph` on
`saloed/backward-main`). A Go function with no `Panic` gets a synthetic exceptional exit for this. Only the zero fact
uses an exceptional exit. The `MethodContextCache` keeps the wired graph per method (today the code computes the wiring
again on every call).

AN EMPTY METHOD (no instruction, or a graph with no node) is an ordinary method. Its start node and its end node are
the entry statement of its method key, in both directions. So each initial fact gives its own identity summary
(`interpreter.md` I8). An implementation may use a special class for it, with the same results.

### 4.5 The call steps

The interpreter gives the order of the steps at a call (`interpreter.md` §4.5, §4.6 forward; §4.9 backward). The
analyzer runs the order in three parts: PRE, CALLEE and POST. The numbers are the step numbers of
`interpreter.md`.

| Part | Forward (`interpreter.md` §4.5) | Backward (`interpreter.md` §4.9) |
|---|---|---|
| PRE: from the caller fact | 1 relevance; 2 binding in; 3 sinks (their end facts go to POST, with no rewriter); 4 sources and the ND conjunctions (their results go to POST, with no rewriter); 5.1 the cleaners and the `RemoveAllMarks` kill on `S`, in the rule order. The results are the ADDED FACTS. | 1 relevance; 2 reversed binding back and the alias edges; 3 reversed sources and reversed end-fact edges on the result of step 2 (their results enter POST at step 7); 4 reversed rewriter on the result of step 2. The results are the ADDED FACTS. |
| CALLEE: for each added fact `a` | 5.2 resolved callees: SUBSCRIBE, then LINK (below); 5.3 the unresolved callee: its statement summary as local micro edges; the JVM constructor: `a` also passes over the call | 5.1 resolved callees: SUBSCRIBE, then LINK; 5.2 the unresolved callee: the reversed statement summary; 5.3 the JVM constructor: the result of step 2 (not an added fact) enters POST at step 6 |
| POST: the results of the callee and the other inputs above | 6 the rewriter (not for the end facts, the source and conjunction results and the constructor pass-over), the binding back with its filters, the aliases, the field limit | the callee results and the constructor requirement enter at 6, the results of step 3 and the seeds at 7: 6 reversed cleaners and the keep edges of the `RemoveAllMarks` kill on `S`, in the rule order; 7 the seeds of the sinks of this call (from the `SeedIndex`, §4.7) and the read positions of step 3; 8 reversed binding in; 9 the field limit |

SUBSCRIBE: the analyzer gives the subscription `(caller edge, s, a)` for the callee `m` to the `SubscriptionManager`
of its runner (§5.3). The replay applies the publications of `m` that `a` satisfies, and the records of `m` that apply
to `a`.

LINK: the analyzer sends the link `(a, caller edge)` to `m`. For `m` in another unit, it sends the event `LinkIn`. For
`m` in the same unit, it may call `m.addLink` directly (as today `submitMethodInitialFact`; §6.1 permits it).

The zero fact at a call:

* forward: it passes over the call. The unconditional rules fire (`interpreter.md` §4.6). It enters every resolved
  callee as the added fact `zero`: a subscription and a link, as above.
* backward: it passes over the call (rule `zpass`). The analyzer adds a ZERO SUBSCRIPTION for `m` (it matches the
  zero-premise publications of `m`, §5.3) and sends `ZeroIn` to `m` (rule `zin`). A zero-premise publication applies
  to the zero fact of the caller at this call with no test (rule `zret`). Its results go through POST. The seeds of
  the sinks of this call enter at POST step 7, where the zero fact reaches the call (§4.7), then steps 8 and 9.

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

### 4.7 Sinks, vulnerabilities and seeds

* A triggered sink adds its WITNESS to the `VulnerabilityStore` under the key `(rule, method key, statement)`, with
  the index of the run (`ap.md` §8.10). A witness is one sink edge, or the sink edge set of a conjunctive sink. The
  store keeps every witness. It never merges two witnesses into one.
* A conjunctive sink uses the conjunction store. Each sink edge set is one witness (`ap.md` §4.9).
* SEEDS (backward run). The driver gives a `SeedIndex`: per (method key, statement), the requirements of the
  vulnerabilities that the forward run before reported (`ap.md` §9.2 SEEDS). A sink pattern gives one requirement. A
  conjunctive sink gives one requirement per positive literal. An unconditional sink gives none.
* A seed enters as a zero-to-fact edge where the zero fact reaches its statement, cut by the field limit. A call sink
  seeds at POST step 7 (§4.5). An exit sink seeds in the start rules (§4.4).
* The backward run has no sink check.

### 4.8 The method context

Today `JIRMethodAnalysisContext` holds the alias analysis, the local-variable reachability, the lambda resolutions,
the flow-function caches and the taint rule context. The new core splits it:

* the CACHED part, in `MethodContextCache`:
  * per method: the method graph, the alias analysis, the local-variable reachability and the lambda resolutions of
    the prescan. Every context of the method shares them (today the `EmptyMethodContext` twin analyzer does this);
  * per (method, direction): the wired backward graph and the statement summaries of the interpreter;
* the RUN part, made by the run: the rule context bound to the run (the `VulnerabilityStore`, the conjunction store,
  the run mode).

Runs are sequential, so in each run the runner of the method is the only user of its cache entry. This removes the
double construction of the context that `saloed/backward-main` has.

### 4.9 The interpreter interface

The interpreter (`interpreter.md`) is language-specific and direction-specific. The core calls it only through this
interface. The core owns the order of the actions. The interpreter gives the micro edges and the rules.

```kotlin
interface Interpreter {
    val direction: Direction
    /** §4.4: the start nodes for the zero fact and for the other facts; the end nodes. For an empty method:
     *  the entry statement of the method key, also when the graph has no node. */
    fun startNodes(method: MethodKey, zero: Boolean): List<CommonInst>
    fun endNodes(method: MethodKey): List<CommonInst>
    /** §4.4: the start rules (with the context filter, forward) and the end rules. The core adds the seeds of the
     *  backward run from its `SeedIndex` (§4.7); the interpreter does not get them. */
    fun startRules(method: MethodKey, node: CommonInst): RuleStatement
    fun endRules(method: MethodKey, node: CommonInst): EndRules
    /** interpreter.md I1: the touched bases, the micro edges and the type filters of a non-call statement. */
    fun statementSummary(method: MethodKey, statement: CommonInst): StatementSummary
    /** §4.5: the three parts of a call. */
    fun callPlan(caller: MethodKey, statement: CommonInst, call: CommonCallExpr): CallPlan
    /** the sinks and the conjunctive rules of a statement (forward). */
    fun sinks(method: MethodKey, statement: CommonInst): List<SinkRule>
    /** forward only: the base is live at the statement (today isReachable). */
    fun isLive(method: MethodKey, base: AccessPathBase, statement: CommonInst): Boolean
    /** a summary edge exists only for these bases (not a local; today isValidMethodExitFact). */
    fun isSummaryBase(base: AccessPathBase): Boolean
}

/** interpreter.md I1: a statement summary. The AP applies it (ap.md §4.2). */
class StatementSummary(val touched: Set<AccessPathBase>, val microEdges: List<PathEdge>,
                       val typeFilters: Map<AccessPathBase, TypeFilter>)

/** The micro edges and the rules of one place: a rule statement (interpreter.md §4.1) and the sinks. */
class RuleStatement(val summary: StatementSummary, val conjunctions: List<ConjunctiveEdge>, val sinks: List<SinkRule>)

/** One step of the cleaner part of a call, in the rule order (interpreter.md §4.5 step 5.1, §4.9 step 6): a
 *  cleaner, or the `RemoveAllMarks` kill on `S`. The kill is a statement summary, not a cleaner (interpreter.md §1.4,
 *  I12 (e)). */
sealed interface CleanStep {
    class Clean(val cleaner: Cleaner) : CleanStep
    class Kill(val keepEdges: StatementSummary) : CleanStep
}

/** The end rules (interpreter.md §4.7): the exit rules, and, forward only, the global-state drop (step 3) and the
 *  removal of the entry marks for a zero-premise fact (step 4). Both read the premise and the triggered sinks. */
class EndRules(val rules: RuleStatement, val globalStateDrop: Boolean, val entryMarks: Set<TaintMark>)

/** §4.5: one call in the direction of the interpreter. */
class CallPlan(
    val touched: Set<AccessPathBase>,              // relevance (PRE step 1)
    val bindIn: List<PathEdge>,                    // forward step 2 / backward step 2 (with the alias edges)
    val bindInFilters: Map<AccessPathBase, TypeFilter>,
    val preRules: RuleStatement,                   // forward steps 3, 4 / backward step 3 (sources and end facts)
    val rewriter: List<Cleaner>,                   // forward step 6 (on the callee results) / backward step 4
    val cleanSteps: List<CleanStep>,               // forward step 5.1 / backward step 6, in the rule order
    val callees: List<MethodKey>,                  // the resolved callees, also the lambdas of the prescan
    val unresolved: StatementSummary?,             // the summary of the unresolved callee (interpreter.md §3.7)
    val constructorPassOver: Boolean,              // JVM constructor (interpreter.md §3.5)
    val readPositions: List<PathEdge>,             // backward step 7: the read positions of the conditional sources
    val bindBack: List<PathEdge>,                  // forward step 6 / backward step 8
    val bindBackFilters: Map<AccessPathBase, TypeFilter>,
    val aliases: List<AliasEdge>,                  // forward: interpreter.md §3.8, AC3 and AC4 select the results
)
```

The backward interpreter gives the reversed micro edges (`interpreter.md` §4.9; today `StatementSummaryBuilder.
buildReversed`). The AP operations of `ap.md` §4 apply the micro edges. The interpreter never applies them. `PathEdge`,
`Cleaner` and the conjunctive edge are the types of `ap.md` §4.

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
`base :: premise path`, one entry per member of a premise set, and the list of the subscribed runners.

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
fun matches(sub: Subscription, pub: Publication, config: RunConfig): Boolean =
    if (sub.zeroOnly) pub.premise.isZero                                     // backward rule zret: no test
    else pub.premise.initials.any { satisfies(it.toPattern(), sub.addedFact, config.restricted) }
                                                                             // ap.md §6.3 `satisfies`; several members: §5.4

/** ap.md §8.7 R4, Lean `retRec`: a record applies by `applicable` or by `inside`. */
fun recordApplies(p: Pattern, a: Pattern): Boolean = applicable(p, a) || inside(p, a)
```

`byEntry` and `byExit` use the lookup `around` (`ap.md` §8.7 R2). `rec.reversedAt(a)` gives the reversal (`ap.md`
§9.1) of each conclusion leaf of `rec` that `byExit` returns for `a`, if that leaf is mark-reversible.

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
subsumption part is `StepD`, §5.5). P1 to P4 are necessary: each has a counterexample in `PipelineProofs.lean`, a
reachable quiescent state that misses an object of the closure.

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
* A subscription goes under EVERY index that it satisfies. The subscription of the zero added fact supplies the member
  `zero` (forward; the backward run has no summary with several premises, because it reverses a conjunction into one
  micro edge per literal, `ap.md` §9.2).
* A new subscription under an index: combine it with the stored subscriptions of the other indexes (one per index,
  every combination), and apply the stored conclusion to each full combination.
* A new conclusion delta: apply it to every full combination.

The key does not contain the conclusion. So a combination meets every delta of the conclusion, in any order of the
replays and the deliveries. Both sides of this join are in the caller.

### 5.5 The no-loss theorem

THEOREM (never lose a summary edge). Let a reachable state of a well-formed encoded system be quiescent (§6.2). Then:

* every join of processed subscriptions with a processed publication has its result processed (`no_lost_join`): the
  caller has the application of every publication to every subscription that satisfies it;
* every object of the closure is processed (`quiescent_complete`): every link reaches its callee, and every
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
| `PipelineAP.sysD_wf` and the other `*_wf` | each encoded system is well-formed (`Sys.WF`): every local rule has at least one premise, all of one actor; every join has subscriptions of one actor and one topic and a publication |

The encoding (`PipelineAP.lean`): actor = method, topic = callee.

| AP rule | In the pipeline | Owner of the premises → of the conclusion |
|---|---|---|
| `root` | a root object | → the root method |
| `start`, `step`, `pass`, `clean`, `filt`, `reqStmt`, `reqClean`, `reqSink`, `vuln`, `retRec`, `zpass`, `seed`, `conj`, `reqConj` | local rule | the method → the method |
| `added` | local rule that makes the LINK (a message to the callee); then the local rule `link → added` | caller → callee |
| `initA`, `initR`, `answer`, `sanswer`, `sreqStmt` | local rule | the method → the method |
| `reqUp`, `sreqUp` | local rule on `[request, link]` in the callee; the result goes to the caller | callee → caller |
| `ret` | the caller makes the SUBSCRIPTION, the callee makes the PUBLICATION (after the restriction); their JOIN gives the caller edge | join |
| `sret` | a second join of the same subscription and publication (the overlap reading `fbOK` of `Statics`). The final static rule `Statics.Design` has `fb = off`, so it gives nothing, and `matches` has no test for it | join |
| `zin` | local rule of the caller; the result goes to the callee | caller → callee |
| `zret` | the zero subscription of the caller and the zero-premise publication of the callee; their JOIN | join |
| `ndOpen`, `ndBind`, `ndRet` | a k-ary JOIN: one subscription per premise, all at one call statement, with the publication of the summary | join |

THE ZERO PUBLICATION. `sysDB` has two publications of a zero-premise backward summary: the restricted one (for `ret`)
and the unrestricted `zpub` (for `zret`). §4.6 publishes only the unrestricted one. The two agree because no ordinary
subscription satisfies the zero premise: no call binds the zero base (`ap.md` S11 (c), Lean `NoZeroBack`).

So at quiescence the analyzer computes exactly the closure that `ap.md` proves sound and exact, in each mode
(`quiescent_exact` with the `cl*_iff` theorems; `PipelineDriver.result_D`, `result_DR`, `result_DB`).

THE MODEL AND THE CODE. Actor: a `RunMethodAnalyzer`. `known`: the RUN stores of the analyzers, the
`SubscriptionManager` tries and the `SummaryStorage` tries. `inbox`: the channels, the local queues, the worklists,
the `pendingPublications` and a direct call in progress. `store`: the `published` index of each `SummaryStorage`.
`replays`: the replay inside `subscribe`. `notifies`: a publication between the insert and the end of the loop over
`subscribers`. `deliv`: the `Delivery` events. `handlers`: the `subscribers` lists.

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

* A timeout, the memory guard (`MemoryManager`), a cancellation or an exception makes the run INCOMPLETE. The
  `RunManager` returns the status: `COMPLETE`, `TIMEOUT`, `OOM`, `CANCELLED` or `FAILED`.
* The hand-off of an incomplete run is not complete. The theorems of `ap.md` §6.6 do not apply to the runs after it,
  so the driver does not start a run after an incomplete run (§7.1).
* Each run has its own coroutine scope with a `SupervisorJob`. The exception of one runner does not cancel the scope
  of a later run. (Today one failed runner cancels `analyzerScope` for every later run.)
* The `RunManager` joins every runner coroutine before it returns. If a runner does not stop, the analysis stops, and
  no later run starts. (Today a runner that does not stop in `cancellationTimeout` stays and can change the next run.)
* A cancellation must also complete the run. Today every `cancel()` of the analysis comes with
  `analysisCompletion.complete`; keep the two calls together.

---

## 7. The iteration driver and the hand-offs

### 7.1 The run sequence

```kotlin
interface IterationPolicy {
    fun fieldLimit(runIndex: Int): Int                               // not decreasing (ap.md W3); run 1 needs >= 1
    fun continueAfter(run: RunConfig, result: RunResult): Boolean    // the budget; out of scope (ap.md §6.6)
}

class IterationDriver(private val policy: IterationPolicy, private val shared: SharedObjects) {
    fun analyze(roots: List<MethodKey>): Report {
        var config = RunConfig(1, policy.fieldLimit(1), demand = null, records = shared.records.view(),
            seeds = SeedIndex.EMPTY, roots = roots)
        val report = Report()
        while (true) {
            val result = RunManager(config, shared).run()             // a new engine (§2)
            if (result.status != RunStatus.COMPLETE) return report.addIncomplete(config, result)   // §7.5
            // the barrier (§7.2): no runner runs now
            report.add(config, result)                                // the confirmation, §7.5
            shared.records.persist(config, result)                    // ap.md §8.7 R1
            if (config.direction == Direction.FORWARD && !result.hasDemandVulnerability()) return report
            if (!policy.continueAfter(config, result)) return report
            config = handOff(config, result)                          // §7.3, §7.4
        }
    }
}
```

* The run sequence is `ap.md` §6.6: run 1 (forward), run 2 (backward), run 3 (forward), and so on.
* A forward run stops the iteration if every vulnerability that it reports has a confirmed witness (a sink edge or a
  sink edge set) of this run (`ap.md` §6.6). `hasDemandVulnerability` reads the witnesses of the run in the
  `VulnerabilityStore` (§4.7, §10). The policy can stop earlier.

### 7.2 The barrier

* B1. The driver computes the hand-off only after the run is complete and no runner of the run is alive (§6.3).
* B2. The next run starts only after the hand-off is complete.
* B3. The driver may read the stores of the finished run in parallel, read-only.

With B1, the hand-off reads the closure of the run (`PipelineDriver.result_D`, `result_DR`, `result_DB`). So the
hand-off is exactly the hand-off of `ap.md` §9.2.

### 7.3 Forward run `n` to backward run `n + 1`

From the `summaries` (run summary store) of every method analyzer and the sink edges of run `n`:

* DEMAND. For every summary edge `j → g` of the method, in every layer, BEFORE the restriction: one backward demand
  pattern `(D-c = g, D-p = j)` per leaf of `g` (Lean `Backward.revSummaryDemand`). For a summary with several premises:
  one pattern per member (`ap.md` §9.2; argued, `ap.md` §11.2). The driver builds the `DemandStore` of run `n + 1`
  from them.
* SEEDS. The `SeedIndex` of the vulnerabilities that run `n` reported (§4.7; `ap.md` §9.2 SEEDS).
* RECORDS. The `RecordStore` persists the normal summary edges with one premise (`ap.md` §8.7 R1, forward).

### 7.4 Backward run `n + 1` to forward run `n + 2`

From the `summaries` of every backward method analyzer, for every method `M` (`ap.md` §9.2; Lean `Backward.demOf`):

1. the zero demand `(D-c = zero, D-p = none)` (implicit for every method key, §4.4);
2. for every zero-premise backward edge at the forward entry of `M`, with the conclusion `gb`: `(D-c = gb, none)`;
3. for every backward summary `jb → gb` of `M` whose premise `jb` is not the zero fact, in every layer:
   `(D-c = gb, D-p = jb)`.

RECORDS: the `RecordStore` persists the normal backward summary edges with one premise that is not the zero fact
(`ap.md` §8.7 R1, backward).

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

   The links carry the data (E-2).
2. Mark each sink witness of the run (a sink edge, or a sink edge set) confirmed or not (`ap.md` §4.9 conditions 1 to
   3). A sink edge set is confirmed only as a whole: the union of its premise sets must be supported jointly.
3. Update the `VulnerabilityStore` and the report (`ap.md` §8.10).

The support is a fixed point over the whole run, so it can change until the run ends (`ap.md` §4.9). The barrier is
the first point where it is final.

AN INCOMPLETE RUN (forward or backward) refutes nothing: the refutation of `ap.md` §8.10 needs the coverage theorem of
run `n + 2`, which needs complete runs. The report keeps every vulnerability that a complete run confirmed, and every
demand vulnerability of the last COMPLETE forward run, with the state DEMAND. An incomplete forward run adds its own
vulnerabilities:

* if every runner of the run was joined (§6.3), the driver computes steps 1 and 2 on its stores. The support grows
  with the links, so a witness that is confirmed in the incomplete run is confirmed in the complete run too. These go
  to the report as CONFIRMED;
* every other vulnerability of the run, and every vulnerability of a run whose runners were not all joined, goes with
  the state INCOMPLETE. No coverage theorem applies to them.

One key can come from several runs. The state CONFIRMED wins (`ap.md` §8.10); else DEMAND wins over INCOMPLETE.

### 7.6 What stays after a run

| Data | Stays until | Read by |
|---|---|---|
| the run summary stores of a run | its hand-off is computed | §7.3, §7.4 |
| the links of a forward run | its confirmation is computed | §7.5 |
| the edge stores, the links and the run summary stores of the LATEST forward run whose vulnerabilities are in the report (complete or incomplete) | the next forward run ends, or the trace resolution ends (phase 5) | the trace resolver |
| `SummaryStorage`, `SubscriptionManager`, the runners, the backward analyzers | the end of the run, or its hand-off | — |
| `RecordStore`, `VulnerabilityStore`, `MethodContextCache`, `ApManager` | the end of the analysis | every run |

Every other object of a run is garbage after the run. The engine of a run is never used again (§2), so no state of
one run can leak into the next run. This removes the leaks of today's reuse (Appendix A).

### 7.7 The driver theorems

THEOREM (`PipelineDriver.driver_iteration`). Hypotheses:

* the program satisfies the hypotheses of `Backward.iteration_general` (`ap.md` §6.6): `P.WF`, `BindTargetsStar`,
  `StmtsMarkRev`, `NoZeroBack`, `ZeroKept`, `ExitReach`, and every sink pattern has the tail `$` or `[any]`;
* run 1 uses `policy1`. The forward restricted runs use `emitM`, `satI` and `restrictU`. The backward runs use the
  same three on `Program.rev P`, with no sinks and with the zero rules (`zbind = true`). The field limits and the
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
`2K + 1`, and only the runs up to it must be complete. The proof extends the sequence after `K` with the full demand
and with every sink as a seed.

The records are not hypotheses: the record sets are free. For the runs with the static rule, `ap.md` proves the iteration (`StaticsIter.iteration_general_DS`), and
`clDS_iff` gives the closure equality; the pipeline form of that theorem is argued (§11).

---

## 8. Code reuse

| Today | Decision | Note |
|---|---|---|
| `TaintAnalysisUnitRunnerManager`, `AnalysisUnitRunnerManager` | REFACTOR into `RunManager` | keep the unit routing, the runner spawn, the counter, the timeout, the memory guard and the progress log; remove `resetApManager`, the delayed units and the cross-run fields; add `RunConfig`, the per-run scope, the join of the runners and the map of the `SummaryStorage`s |
| `TaintAnalysisUnitRunner` | REFACTOR into `UnitRunner` | keep the channel, the priority queue, the quantum and `MethodAnalyzerStorage`; the events of §5.1 |
| `AnalysisRunner` | REPLACE by `RunnerPort` (§6.1) | |
| `MethodAnalyzerStorage` | REUSE with a factory | the `EmptyMethodContext` twin goes; the context cache shares the per-method parts (§4.8) |
| `MethodAnalyzer`, `NormalMethodAnalyzer`, `EmptyMethodAnalyzer` | REPLACE by `RunMethodAnalyzer` | §4; `TimedMethodAnalyzer` becomes a decorator of the new interface |
| `MethodAnalyzerEdges`, `EdgeCollection`, `AccessPathBaseStorage` | REUSE the structure | the new keys of `ap.md` §8.1 |
| `Edge` (`ZeroToZero`, `ZeroToFact`, `FactToFact`, `NDFactToFact`) | REPLACE | `ap.md` §7.6 |
| `SummaryEdgeStorageWithSubscribers`, `MethodSummariesUnitStorage` | REUSE the pattern | publications per premise key and layer; the lock of P3 (§5.2); one storage per method key in the `RunManager` |
| `SummaryEdgeSubscriptionManager`, `CommonAPSub`, the tree sub-storages | REUSE the pattern | the registration on the first `getOrPut`, the delta insert, the replay, the match at delivery; P4 with one `matches`; one manager per runner |
| side-effect requirements and summaries, `TaintMarkFieldUnfoldRequest`, `MethodSideEffectSummaryHandler`, `triggerSideEffectRequirement` | REMOVE | the requests over the links (§4.6) |
| fact-depth delay (`INITIAL_ALLOWED_FACT_DEPTH`, `MethodAnalysisDelayed`, `DelayedAnalysisResume`, `factLimit`) | REMOVE | the field limit (`ap.md` §4.4) |
| `InitialFactAbstraction` (tree, automata, cactus) | REMOVE | the policy and the emission (§4.4) |
| `MethodSummaryEdgeApplicationUtils`, `MethodCallSummaryHandler` | REPLACE | `applySummary` (`ap.md` §4.3); the rewriter moves to the interpreter |
| `TaintSinkTracker`, the vulnerability buckets of `TaintAnalysisUnitStorage` | REPLACE | the `VulnerabilityStore` (§4.7) and the conjunction store (`ap.md` §8.9); no lossy merge |
| `MethodCallResolver`, `JIRMethodCallResolver` | ADAPT | today it is typed to `TaintAnalysisUnitRunner` and calls back with a `MethodCallHandler` per edge kind; the new one gives the resolved callees to `callPlan` |
| `TrackerWithSubscriber`, `LambdaTracker`, `GoClosureTracker` | REUSE as the source of the prescan values | no lambda event in the new core (§5.1) |
| `MethodEntrypointResolver`, `UnitResolver`, `LanguageManager` | REUSE | |
| `ApplicationGraph.reversed`, `MethodInstGraph` | REUSE | `JIRAnalysisManager` downcasts the graph to `JApplicationGraph`; ADAPT it to accept the reversed graph |
| `JIRBackwardExitWiringGraph` (`saloed/backward-main`) | PORT | with a cache per method; the Go exits (§4.4) |
| `StatementSummaryBuilder`, `buildReversed`, the JVM and Go flow functions | ADAPT | the interpreter of §4.9 (`interpreter.md`) |
| `JIRMethodAnalysisContext` | SPLIT | the cached part and the run part (§4.8) |
| `MemoryManager`, `Cancellation`, `UnitRunnerStats`, `MethodStats` | REUSE | one instance per run where it has run state |
| summary serialization (`storeSummaries`, `loadSummariesFromRunner`) | NOT USED | the records are the reuse between runs |
| `trace/*` | OUT OF SCOPE | phase 5; §7.6 |

Do not copy the defects of today that Appendix A lists. Each one has its rule in this document: P3 and P4 (§5.3),
the processed item (§4.3), the new engine per run (§2, §7.6), the per-run scope (§6.3), the fixed priority keys
(§6.1), and the correct interners of the `ApManager` (O4).

---

## 9. Interface to the prescan and to the trace resolution

* PRESCAN (phase 3). The prescan runs the current core. It gives the new core:
  * the reduced rule set (`relevantRuleIds`);
  * the lambda and closure resolutions per call site (the values of the `TrackerWithSubscriber` of each call site);
  * the root methods.

  The core copies the resolutions into the `MethodContextCache` once, before run 1. It keeps no reference to a context
  of the prescan.
* TRACE (phase 5). The trace resolution reads the data that §7.6 keeps:
  * the edge stores (`ap.md` §8.1 `edgesAt`);
  * the links: the callers of a method and the caller edges;
  * the run summary stores;
  * the sink edges of the `VulnerabilityStore`.

---

## 10. Reference code

The types of the messages and the stores. `Pattern`, `InitialAp`, `EdgeTree`, `PathEdge`, `Direction`, `Record`,
`RecordStore` and the tests are those of `ap.md` §3.4, §4, §7 and §8.7. The premise key is the premise set of
`ap.md` §4.6 and §8.1.

```kotlin
typealias MethodKey = MethodEntryPoint            // ap.md §1: context and forward entry statement

enum class Layer { NORMAL, DEMAND }

/** A premise set (ap.md §4.6, §8.1): {zero}, {i} or {i1, ..., ik}; interned, so equal sets are equal values. */
data class PremiseKey(val initials: List<InitialAp>) {
    val isZero: Boolean get() = initials.size == 1 && initials[0].isZero
}

/** The caller side of a link (E-2). */
data class CallerRef(val caller: MethodKey, val premise: PremiseKey, val callerLayer: Layer, val call: CommonInst)

/** A link (ap.md §8.3): the added fact, its layer on the link, the caller edge. */
data class Link(val addedFact: Pattern, val linkLayer: Layer, val caller: CallerRef)

/** A subscription (ap.md §8.4). `zeroOnly`: the backward zero subscription (rule zret). Equality by value (E-3). */
data class Subscription(val callee: MethodKey, val addedFact: Pattern, val linkLayer: Layer, val ref: CallerRef,
                        val zeroOnly: Boolean = false) {
    val caller: MethodKey get() = ref.caller
}

/** A publication: a summary edge of the callee, after the restriction in a restricted run. Its layer is
 *  `conclusion.demand`. */
data class Publication(val premise: PremiseKey, val conclusion: EdgeTree)

/** A request of run 1 (ap.md §4.5, §4.10). */
sealed interface RequestKind {
    data class Mark(val mark: TaintMark) : RequestKind
    data class Position(val path: List<Accessor>) : RequestKind
}

/** A seed of the backward run (§4.7): one requirement of a reported sink. */
data class Seed(val rule: RuleId, val method: MethodKey, val statement: CommonInst, val requirement: Pattern)

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

/** ap.md §8.10: the key of a vulnerability record. */
data class VulnerabilityKey(val rule: RuleId, val method: MethodKey, val statement: CommonInst)

/** ap.md §4.9: a sink edge (premise set, layer, sink fact). */
data class SinkEdge(val premise: PremiseKey, val layer: Layer, val fact: Pattern)

/** A sink witness: one sink edge, or the sink edge set of a conjunctive sink (one edge per literal). It is confirmed
 *  as a whole (§7.5 step 2). */
class SinkWitness(val edges: List<SinkEdge>, val run: Int) {
    var confirmed: Boolean = false                                             // set only at a barrier (§7.5)
}

/** ap.md §8.10: the vulnerability records; each witness has the index of its run. */
interface VulnerabilityStore {
    fun add(key: VulnerabilityKey, witness: SinkWitness)                         // concurrent (O4)
    fun witnessesOf(run: Int): Sequence<Pair<VulnerabilityKey, SinkWitness>>
}

enum class RunStatus { COMPLETE, TIMEOUT, OOM, CANCELLED, FAILED }

class RunResult(val status: RunStatus, val analyzers: Sequence<RunMethodAnalyzer>, val runIndex: Int,
                val vulnerabilities: VulnerabilityStore) {
    /** §7.1: a vulnerability of THIS run with no confirmed witness of this run. */
    fun hasDemandVulnerability(): Boolean =
        vulnerabilities.witnessesOf(runIndex).groupBy({ it.first }, { it.second }).values
            .any { witnesses -> witnesses.none { it.confirmed } }
}

/** The counter of one run (§6.2). */
class InFlight(private val onZero: () -> Unit) {
    private val count = AtomicLong(0)
    fun beforeSend() { count.incrementAndGet() }                       // Q1
    fun afterHandler() { if (count.decrementAndGet() == 0L) onZero() } // Q2
}
```

Other names: `SharedObjects` holds the shared objects of §2. `Report` holds the vulnerabilities of `ap.md` §8.10 and
the state of each. `handOff` makes the `RunConfig` of the next run by §7.3 and §7.4. `RecordStore.view` gives the
read-only view of a run; `RecordStore.persist` adds the records of `ap.md` §8.7 R1 at a barrier. `CalleeSubscriptions`
and `PublicationIndex` are the path tries of §5.3 and §5.2. `MethodContextCache.get(method, direction)` gives the
cached part of §4.8.

---

## 11. Limits

ARGUED, NOT PROVED:

* SUBSUMPTION. The AP operations simulate the subsumption of the edge stores (`subsumesB`, the tree merges T1 to T5).
  `quiescent_dominates` needs this as a hypothesis. For a join it needs: if a stored added fact dominates the added
  fact of a subscription, the join with the stored one gives a dominating result. `inside` has this property.
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
* THE DRIVER with the static rule and with the conjunctions. The closure equalities hold (`clDS_iff`, `clDN_iff`). The
  pipeline form of `StaticsIter.iteration_general_DS`, and the iteration with conjunctions (`ap.md` §11.2), are argued.

NOT IN THE MODEL: the priorities, the quantum, the memory guard and the timeout. They change the order of the steps or
stop the run. They do not change the closure of a complete run.

---

## 12. The formal model

| File | Content |
|---|---|
| `Pipeline.lean` | the rule system with owners, its closure, the state and the steps of the protocol (frozen definitions) |
| `PipelineProofs.lean` | `reach_sound`, `quiescent_complete`, `quiescent_exact`, `no_lost_join`; the counterexamples `PCex.cex_P1` to `cex_P4` and `PCex.step_finds_edge`; the counter model (`Quiesce.creach_inv`, `cnt_zero_iff`, `done_iff`, `done_final`, `bad_early_done`); the dominance theorems (`quiescent_dominates`, `reach_soundD`) |
| `PipelineAP.lean` | the encodings of `D`, `DR`, `DB`, `DS`, `DN`; the `*_wf` theorems; `clD_iff`, `clDR_iff`, `clDB_iff`, `clDS_iff`, `clDN_iff`; the object theorems (`clD_link`, `clD_sub`, `clD_pub` and the other forms) |
| `PipelineStore.lean` | the completeness of the index lookups of §5.3 (`replay_run1`, `deliver_run1`, `replay_restricted`, `deliver_restricted`, `record_lookup`) |
| `PipelineDriver.lean` | `result_D`, `result_DR`, `result_DB`, `driver_iteration`, `driver_iteration_upto` |

---

## 13. Test plan (TDD)

1. SCHEDULE FUZZING. A test runner picks the next event at random (seeded) from all channels and queues. It runs the
   direct calls as events too. For small programs (the programs of `ap.md` §6.3, §6.4 and the backward cases), compare
   the result of many seeds with a reference: the naive fixed point of the closure. Every seed must give the same
   edges, summaries and vulnerabilities.
2. PROTOCOL TESTS. A mock storage that breaks P1, P2, P3 or P4 loses a summary in the fixed schedule of the
   counterexample. The real storage does not.
3. THE `[any]` DELIVERY. A caller fact with `[any]` above the premise of a summary that the callee publishes AFTER the
   subscription, with 10 or more subscriptions: the caller gets the summary (P4).
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
   callee in the backward run. A backward call runs PRE, CALLEE and POST in the order of `interpreter.md` §4.9, with
   the reversed source results and the seeds at POST step 7.
9. STOP RULE. A forward run whose vulnerabilities all have a confirmed sink edge stops the iteration, also when they
   have demand-layer sink edges too (§7.1).
10. REGRESSION. The existing analysis tests, through phase 3 (`bidirectional-task.md` phase 4).

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
* `handleUnchangedStatementEdge` propagates the input edge, not the processed edge: the exit filter is lost for the
  unchanged facts.
* Across runs: `analyzerEnqueued`, the runner `factLimit`, the sticky `status` and the counters survive. A failed
  runner cancels the shared scope. A runner that does not stop can run into the next run.
* `EventComparator` reads mutable keys. `ConcurrentReadSafeObject2IntMap` can hang the interner (non-volatile reads in
  a retry loop).

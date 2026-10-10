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
`ap.md` §10.11), and, for the hand-off of the demand edges only, the `Handoff*.lean` files,
`PipelineHandoffDriver.lean` and `PipelineHandoffDriverExt.lean` (`ap.md` §10.12; §7.3 to §7.8). Every theorem named here
is machine-checked and constructive (`ap.md` §10 defines the term). §11 lists what is argued and not proved.

THE RULES OF F72 WITH THE F75 CLEANER CORRECTION ARE NORMATIVE; their general proofs are pending (`ap-history.md`). A restricted run can
analyse with the abstract mark `*` (§3 THE MARKS OF A RESTRICTED RUN). The theorems that this document names for the
restricted runs and for the iteration (§5.5, §7.7, §7.8, §12) are proved for the CONCRETE restricted runs of F70 and
F71 (the emission `emitM`, the closures with request rules that never fire, `RExact.DR_concrete`). For the rules of
F72 those general results remain pending. The checked local F72 results and their assumptions are in `ap.md` §10.13.
Section 11 states the remaining obligations. The earlier theorem names stay as evidence for the concrete design.

Language: ASD-STE100 Simplified Technical English.

---

## 0. Scope

The analyzer core:

1. runs one run (`ap.md` §6): one direction, one field limit, one mode (run 1 or restricted), to a fixed point. Only
   run 1 has requests. A restricted run analyses with the abstract mark `*` where its demand has a `*` pattern, and
   with a concrete mark only where a concrete-mark demand exists (§3; `ap-history.md` F72);
2. exchanges the edges between the methods of a run with no loss (§5);
3. detects the end of a run (§6);
4. runs the sequence of runs and computes the hand-off from each run to the next: only the DEMAND EDGES and the
   seeds of the DEMAND vulnerabilities (§1, §7.3, §7.4);
5. stops the sequence by its STOP RULES and by ONE BUDGET for the whole analysis: each run gets the rest of the budget
   (§7.1). It LOCALIZES the remaining work: after each complete run it logs the FRONTIER, the part of the program that
   the later runs still analyse (§7.8);
6. gives the report: the vulnerabilities and the end of the analysis (§7.5, §9).

The core is for the JVM. Go is out of scope.

Out of scope:

* the IR interpreter (`interpreter.md`); §4.9 gives only its interface to the core;
* the prescan, the rule reduction and the `TaintAnalyzer` wiring (phase 3); §9 gives the interface;
* the trace resolution. The core keeps no store of a run for a trace resolver (§7.6). The phase-3 output holds every
  entry of the report, CONFIRMED and DEMAND, and gives each one a simple trace (§9; `ap-history.md` F68);
* the iteration policy: the field limit of each run, and a practical STOP STRATEGY that reads the frontier log
  (`continueAfter`, §7.8). The driver takes the policy as a parameter (§7.1). The stop rules and the one budget are
  in scope (item 5);
* the localization of the ZERO FACT. The zero fact still enters every callee in every run (the backward rule `zin`,
  the forward zero demand, §4.4), and its work is in the frontier log only as a measure (§7.8, §11 THE ZERO FACT;
  `ap-history.md` F70).

### 0.1 Assumptions

| # | Assumption |
|---|---|
| A1 | The AP operations and stores satisfy `ap.md`. The interpreter satisfies `interpreter.md` I1–I14. The proofs of this document use only the closures of `ap.md` (Lean `D`, `DR`, also `DR` of the seeded program `FSeeds.keepSources P σ` (§7.7), `Backward.DB`, `Statics.DS`, and with the conjunctions `NDZ.DNz`, the closure of the spec (§5.5), with its list model `ND.DN`). With the tail `[any-taint]` (`ap.md` W8, §10.11) they also use run 1 with the layer rules W6 and W8 and the exclusion of `[any-taint]` (`AnyTaintEx.D6X`) and the restricted forward run with must-premises and exclusions (`AnyTaintEx.DRX`; with the spec rules `emitX`, `satX` and the restriction as an INTERSECTION `HandoffX.restrictIX`, `ap.md` §6.4; before F70 the spec instance was `AnyTaintEx.DRXs`, with `restrictX`). The backward run has no `[any-taint]`: it stays `Backward.DB`, with the intersection `Handoff.restrictI`. These are the closures of the CONCRETE restricted runs (F70, F71): they keep the request rules, which never fire there. The restricted closures of F72 (no request rules; the emission `emitW`, the satisfaction `satW`, the hand-offs with the mark normalization; Lean: `Abs.DRA`, `Abs.DBA`) are defined in the base model (`ap.md` §10.13); their general coverage, X-tail extension and pipeline instance remain pending (§11). |
| A2 | LINEARIZABLE SHARED ACTIONS. Each shared action of §5.2 and §5.3 is atomic: register a handler, insert a publication, read the storage, read the handler list. All of them have one total order. This order agrees with the program order of each thread. The Lean model is an interleaving model with these actions as steps. P3 (§5.3) is the implementation rule. |
| A3 | RELIABLE EVENTS. An event that a thread sends to the channel of a runner arrives exactly once, unless the run is cancelled. The send happens before the receive (Kotlin `Channel`). |
| A4 | READ-ONLY INPUTS. These inputs do not change during a run: the program, the rules, the lambda resolutions, the demand store, the record store and the seeds. The driver makes them before the run starts. The start of the run publishes them to every runner. |
| A5 | A handler (the code of one event) ends. Only the end of a run needs this (§6). The no-loss theorem does not need it (§5.5). |

---

## 1. Terms

`ap.md` §1 defines the AP terms (fact, edge, premise set, layer, link, added fact, run, demand pattern, record, request,
and others; since F72 also the FLOW FORM of a `*` pattern, the FLOW PREMISE and the SHARING of the emission). This
document adds:

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
| publication | A summary edge that the callee gives to its subscribers. In a restricted run it is the result of the restriction (`ap.md` §6.4): the INTERSECTION of the summary edge with one demand pattern, in the locations AND the marks (`ap-history.md` F71): the premise lies inside `D-c` with its mark, and the mark of the conclusion meets the mark of `D-p` (§4.6). It carries its premise key with the tail of each member and the exclusion of an `[any-taint]` member (§4.1, §4.6). The hand-off reads the publications, not the summary edges before the restriction (§7.3, §7.4). |
| crossable | A summary leaf `j → g` (one leaf of the conclusion tree of a summary edge, `ap.md` §7.2) that the next run of EITHER direction crosses by a record, with no analysis of the callee (Lean `Handoff.Cross`). All of these hold: (1) the leaf is a leaf of a RECORD (`ap.md` §8.7 R1: a normal summary edge with one premise; a backward premise is not the zero fact); (2) the premise `j` has the tail `$`, or `*` with the Empty exclusion: not `[any]` and not a must-premise `[any-taint]`; (3) `j → g` is mark-reversible (`ap.md` §1); (4) the leaf `g` has no any tail: not `[any]`, and not `[any-taint]` with or without its exclusion. So the reversal of the leaf (`ap.md` §9.1) has a `$` or `*` (Empty) premise too. A backward leaf `jb → gb` is crossable if it is NORMAL (a backward record) and its reversal satisfies (2) to (4) (Lean `Handoff.CrossB`: the reversal `revRec` is always normal, so the test reads the layer of `gb` itself). Then the record of the leaf applies to EVERY CONCRETE added fact (forward) or requirement (backward) that covers one of its locations, by `inside` or by `applicable` (Lean `Handoff.cross_applies`, proved for the concrete runs). Since F72 a restricted run can also have an added fact or a requirement with the mark `*` or `*∖X` (§3 THE MARKS OF A RESTRICTED RUN): a record applies to it only if the premise of the record has the mark `*` (the mark test of `inside` and of `applicable`, `ap.md` §4.3); this form of `cross_applies` is PENDING (§11). The reversal of the leaf is exact (`ap.md` §8.7 R3; Lean `Reverse.rev_exact_of_empty_premise`: the converse pairs; as a record, `ap.md` S14). §7.3 shows that (4) is necessary. |
| demand edge | A published summary piece of a run that the next run of the other direction cannot reuse as a record: a publication (§4.6) of a summary leaf that is NOT crossable (Lean `Handoff.handF`, `demOfN`). Also, from a backward run, every zero-premise backward edge at the forward entry (§7.4 case 2). The run stores its demand edges when it publishes them (§4.6). The hand-off gives the next run only the demand edges (§7.3, §7.4); each one gives one demand pattern of the next run per member of its premise. The zero demand is not a demand edge: it is implicit for every method key (§4.4). A demand edge is not the same as a DEMAND-LAYER edge (`ap.md` §1): a normal leaf that is not crossable (an `[any-taint]` leaf, for example) is a demand edge too. |
| DEMAND vulnerability | A vulnerability key whose state in the report is DEMAND after a complete forward run (§7.5): the latest complete forward run reports it, and NO complete forward run so far confirmed it. A key that an earlier run confirmed is CONFIRMED (final), also when the latest run reports it only in the demand layer. Only the sink witnesses of the DEMAND vulnerabilities are sink seeds of the hand-off (§7.3). The backward run also fires the sink seeds of a sink whose end fact a requirement reaches, also of a CONFIRMED vulnerability (§4.5 THE TRIGGER OF AN END FACT). |
| frontier | The part of the program that the later runs still analyse after a complete run: the method keys with a non-zero initial fact in the run, and the demand edges that the run hands off, per method key (§7.8). The driver logs the frontier of each complete run (THE FRONTIER LOG, §7.8). |
| storage with subscription | The callee-side store of the publications, with the list of the subscribed runners (§5.2). |
| replay | The read of the storage when a subscription is new (§5.3). |
| notification | The send of a new publication to every subscribed runner (§5.2). |
| delivery | The event that carries a notification to one runner (§5.3). |
| quiescence | The state of a run with no event in a channel or a local queue, no running handler, no worklist item and no pending publication (§6.2). |
| barrier | The point between two runs: the first run is quiescent, and the next run has not started (§7.2). |
| hand-off | What one run gives to the next run: the demand edges and the seeds (`ap.md` §8, §9.2; §7.3, §7.4). The records are PERSISTENT, not a hand-off (`ap.md` §8.7): a crossable leaf goes to the records and not to the hand-off. |
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
| initial facts of an added fact | the policy fact (`ap.md` §6.2) and the request answers | the emission of `ap.md` §6.3 (§4.4; F72 R2): an entry pattern `D-c` with the mark `*` gives its FLOW FORM, one initial fact for every added fact under it (SHARING); a `D-c` with a concrete mark gives `a ∩ D-c` with the mark of `a`, only for an `a` with that mark: an added fact with the mark `*` or `*∖X` under a concrete pattern emits NOTHING (the user's decision: "The added fact can't satisfy the demand"); the zero fact for the zero added fact | the same emission, with the requirement as the added fact: a `*` pattern weakens the requirement to the FLOW form of the pattern (§4.4); after the hand-off normalization no entry pattern has the mark `*∖X` (§7.3); the zero fact enters every callee (rule `zin`) |
| the marks of the facts | `*` and `*∖X` (the policy facts and their FLOW edges), and concrete marks (the answers, the zero fact, the sources) | NOT CONCRETE since F72: the edges of a FLOW premise (the mark `*`) have the marks `*` and `*∖X` (FLOW trees, `ap.md` §7.2), and their callees can get added facts with these marks; the edges of a concrete premise and of the zero fact have concrete marks. Before F72 every restricted run was concrete | as the restricted forward run |
| a summary applies to an added fact `a` if | `applicable(j, a)` | `inside(j, a)`; for a FLOW premise (the mark `*`) also `applicable(j, a)` (`ap.md` §4.3; F72 R3; §5.3 `matches`). This test applies after the restriction in the callee (the INTERSECTION with a demand pattern, in the locations and the marks, `ap.md` §6.4; §4.6). A callee has a non-zero premise only where a demand pattern of it emits one (§4.4): a callee whose only demand pattern is the zero demand publishes no summary of a non-zero premise, and its callers cross it by its records (next row) | as the restricted forward run; a zero-premise summary applies to the zero fact of the caller with no test and no restriction (rule `zret`) |
| records (`ap.md` §8.7 R3, R4) | none | the FORWARD records by `byEntry`, and the reversed BACKWARD records by `byExit`; each when `applicable(p, a)` or `inside(p, a)`. A forward record with an `[any-taint]` premise that applies by `applicable` only gives its results in the demand layer (`ap.md` §4.3; §4.2 `applyRecord`). A CROSSABLE leaf (§1) of the run before is not in the demand (§7.3, §7.4): its record REPLACES the analysis of the callee, and the run crosses the call by the record. A callee of which the forward run before hands off no demand edge (for example, all its summary leaves are crossable), with no seed in its call subtree, is analysed only from the zero fact (§7.8 THE EXCLUSION) | the BACKWARD records by `byEntry`, and the reversed FORWARD records by `byExit`; each when `applicable(p, a)` or `inside(p, a)`. The reversal is LEAF BY LEAF: no leaf of a forward record with an `[any-taint]` premise has a reversal; of any other record, an `[any-taint]/E` leaf with `E ≠ {}` has none, and the other leaves reverse (`ap.md` §8.7 R3; §5.3). A crossable forward leaf is not in the backward demand (§7.3): the backward run crosses the call by its reversal and never enters the callee for it |
| mark and position requests, static rule | yes (`ap.md` §4.5, §4.10); a selected-mark cleaner requests T for every same-base abstract fact, before the path test (F75) | no request rule and no static rule (F72 R4). On a fact with the mark `*` or `*∖X`, a concrete mark gate or sink gives nothing; a selected-mark cleaner keeps every same-base fact with mark `*∖(X ∪ {T})`, including disjoint paths (F75, `ap.md` §4.7). No request is raised | as the restricted forward run (the backward run has no sink check) |
| sinks | the sink check (`ap.md` §4.9) | the sink check; on a `*` or `*∖X` fact it gives nothing (no request, `ap.md` §4.9) | no sink check; the sink seeds (`ap.md` §9.2) |
| unconditional sources | every source fires | only the source seeds fire (`ap.md` §6.1 rule 6); a zero-premise forward record still applies (`ap.md` §9.2) | every reversed source edge, with no seed filter (the backward run is on the full program, Lean `Reverse.Program.rev P`); it records the source hits (`ap.md` §8.11) |
| type filters | yes | yes | no |
| the tail `[any-taint]` (`ap.md` W8, S15) | a source rule with an `[any]` target gives `[any-taint]` on a normal input: a complete edge (on a demand input `[any]`, W8). A pass rule with an `[any]` target keeps `[any]`: a may, in the demand layer (`ap.md` W6). A normal `[any-taint]` conclusion can carry an EXCLUSION `E` of first accessors, `(x, p, [any-taint], E, T)`: an exclusion edge (the keep edge of a strong write, a `*/E'` summary) gives `E ∪ E'` and the result stays normal (§4.3). Only the demotions of §4.3 make `[any]` of it (demand, no exclusion): the field-limit cut, a cleaner `part` row other than `atAndBelow` and `below` one accessor below it, a may target, a demand-layer input and (in a restricted run) the must-record demotion. No premise has the `[any-taint]` tail | as run 1. Also the `[any-taint]` premise (a MUST-PREMISE) of the emission (§4.4), with the exclusion that the emission gives it: it starts as itself in the normal layer, and its normal edges are complete | no `[any-taint]` (a forward-only tail, `ap.md` W8). The seed of an `[any]` sink pattern and the reversal of an `[any]` condition literal give `[any]`, in the demand layer (`ap.md` W6). Every result of the reversal of a micro edge whose forward target is `[any]` (a pass rule with an `AnyField` target) is in the demand layer, also a `$` result (§4.3). So is every result of the reversal of a conjunctive micro edge (§4.3). A complete edge is a normal edge, as before F69 (`ap.md` §8.7 R1) |

No run has a liveness check (§4.3).

THE MARKS OF A RESTRICTED RUN (`ap-history.md` F72; the AP rules are in `ap.md` §4.3, §4.5, §6.1, §6.3, §6.4, §6.6,
§9.2). THE RULE: a restricted run analyses with a concrete mark only if a concrete-mark demand exists. Run 1 keeps its
requests; their answers make the concrete-mark summaries where the marks matter, and the hand-off gives them to the
next run as concrete patterns (or, if they are crossable, as records). A forward demand with `*` gives a backward
demand with `*`, and a concrete demand stays concrete. The core part of each rule:

* R1, THE HAND-OFF NORMALIZATION (§7.3, §7.4). Every hand-off replaces the mark `*∖X` of a demand pattern by `*`, in
  `D-c` and in `D-p`: a larger demand, so it is sound. The summaries and the records keep `*∖X`: it blocks a mark that
  the summary cannot pass. A demand for a mark in `X` comes as its own demand edge, with the concrete mark;
* R2, THE EMISSION (§4.4). The initial fact is the WEAKEST fact inside `D-c` that covers the common part with the added
  fact (the requirement in the backward run). A `*` pattern gives its FLOW FORM, which does not depend on the added
  fact (SHARING); a concrete pattern gives `a ∩ D-c` with the mark of `a`, as before F72;
* R3, THE SATISFACTION (§5.3). A summary of a FLOW premise applies by `inside` or by `applicable`; a summary of a
  concrete premise by `inside`, as before;
* R4, NO REQUEST AFTER RUN 1, in both directions (§4.6). On a `*` or `*∖X` fact an operation that needs a concrete
  mark gives nothing (the table above);
* R5, THE RESTRICTION (§4.6). The mark-aware intersection of F71. A FLOW premise lies inside its own `*` pattern, and
  inside no concrete pattern;
* R6, THE CLAIM (PENDING, §11): every flow that needs a concrete mark is demanded by a concrete pattern or crossed by a
  concrete record, and every flow that a `*` pattern demands needs no concrete mark. So no request is needed after
  run 1, and every forward run still reports every real vulnerability that no earlier run confirmed. A sink fires only
  under a concrete premise (the method of a sink gets a concrete demand from its seed, and the chain of calls down
  stays concrete), so the confirmation does not change (§7.5).

WHAT F72 REPLACES: decision F35 (version 4), "no request after run 1, so a restricted run is CONCRETE", and its cost
(`ap.md` §6.3): NO SHARING, one initial fact per distinct added fact (path, tail, mark), so the premises are a product
of the marks. Since F72 a restricted run (forward or backward) can have `*` premises (FLOW premises), FLOW conclusions,
added facts and requirements with the marks `*` and `*∖X`, and `*∖X` marks on its summaries. Two consequences: the
backward weakening makes the backward demand coarser (for example the requirement `ret.*` in place of `ret`, §7.4), and
the restricted runs have no request rules. The Lean model of these rules is PENDING (§11).

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
| `summaries` | run summary store (`ap.md` §8.5) | two parts: the summary edges BEFORE the restriction, per premise key and layer (`persist` takes the records from them, `ap.md` §8.7 R1), and the DEMAND EDGES of the run: the published pieces of the summary leaves that are not crossable (§1, §4.6; `ap-impl.md` DD17, `RunSummaryStore.addDemand`, `demandEdges()`). The hand-off reads only the demand edges (§7.3, §7.4) |
| `counters` | | the counters of the frontier log (§7.8) and of the stop rule `NO_DEMAND_EDGE` (§7.1): the DEMAND-LAYER OBJECTS of the run (the deltas of `edges.add` in the demand layer, the summary deltas in the demand layer (§4.6) and the new DEMAND LINKS, the links whose added fact is in the demand layer, §4.2 `addLink`, `ap.md` §8.3), the crossable summary leaves (counted at each summary delta, §4.6), the record applications at a call (§4.2 `applyRecord`), a flag that is true if a non-zero initial fact exists, the edges of the zero premise; as an option, the demand-layer results per demotion (§4.3) |
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
| `addLink(link)` | a caller binds a fact into this method | add the link (exact deduplication). A new added fact: emit its initial facts (§4.4). A new link: check the standing requests (§4.6). A new link whose added fact is in the demand layer (a DEMAND LINK, `ap.md` §8.3) adds one to the demand-layer objects of `counters` (§4.1; the stop rule `NO_DEMAND_EDGE`, §7.1). The zero added fact emits the zero fact. No request matches it. Its link serves the support (§7.5). | E1, E2 |
| `addZeroEntry()` | backward: the zero fact of a caller reaches a call to this method | the zero fact is an initial fact (rule `zin`) | §9.2 |
| `addRequest(premise, request)` | run 1: a callee climbs a request through a link of this method | store it (exact deduplication); check it against every link of this method (§4.6) | E5, E7 |
| `applySummary(sub, pub)` | the `SubscriptionManager` matched a publication with a subscription of this method | one premise: apply the summary to the added fact (`ap.md` §4.3), then the stages after the callees stage (§4.5). Several premises: the combination of §5.4. | §4.3, E2, E4, E6 |
| `applyRecord(sub, record)` | a new subscription of this method; the record (already reversed by the `SubscriptionManager` if it is from the other direction) covers or contains its added fact | apply the record, then the stages after the callees stage (§4.5). A record with an `[any-taint]` premise whose premise covers the added fact (`applicable`) but does not lie inside it with the exclusions (not `inside`) gives each result in the demand layer: the result keeps its base, path and mark, and its layer goes up (an `[any-taint]` result becomes `[any]` and loses its exclusion, `ap.md` W8; the must-premise needs every location; Lean `AnyTaintEx.recLayerX`, necessary by `AnyTaintExact.CexApp.cex_app`). Each application with a result is a RECORD CROSSING: it adds one to `counters` (§4.1; the frontier log, §7.8) | §4.3, §8.7 R3, R4 |
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
    THE REVERSAL OF A CONJUNCTION (`ap.md` §9.1; `ap-history.md` F70). The reversal of a CONJUNCTIVE micro edge with
    two or more positive literals (also of a conjunctive exit source, §4.4) gives EVERY result in the demand layer, as
    the reversal of a may: a requirement that reaches one literal is not a converse flow of the conjunction. So no
    backward summary through it is a record (`ap.md` §8.7 R1) or crossable (§1), and the hand-off gives it to the next
    forward run (§7.4 case 3), which analyses the callee with all the members. This fixes a false positive that
    existed before F70: a normal backward summary from the conclusion to ONE literal was a record, and its reversal
    (R3) was a forward record of one literal, which drops the other literals (§11). Argued (§11).

  The core reads the target tail of the FORWARD form of the micro edge (`MicroEdge.forward`, §4.9): `[any]` is a may
  (a pass rule), `[any-taint]` a must (a source). The reversed literal of a conjunctive edge carries
  `MicroEdge.conjunctive` (§4.9), a property of the form (the reversal made it), not of the rule kind. So the core
  needs no rule-kind flag, in either direction.
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
  method (`ap.md` §8.6). Each one whose common part with `a` is not empty (`a ∩ D-c`, `ap.md` §6.3) gives ONE initial
  fact: THE WEAKEST FACT INSIDE `D-c` THAT COVERS THE COMMON PART (`ap-history.md` F72 R2; Lean, PENDING: `emitW`):
  * A `D-c` WITH THE MARK `*`: its FLOW FORM `(D-c.base, D-c.path, flowK(D-c.tail), *)`, with `flowK(*/E) = */E`,
    `flowK([any]) = */{}` and `flowK($) = $` (`ap.md` §6.3). It does not depend on `a`: every added fact under the
    pattern gets the same initial fact, whatever its mark, path and tail (SHARING), and `initials.add` stores it once.
    The FLOW premise has FLOW edges (`ap.md` §7.2), and its summaries pass the mark of each added fact;
  * A `D-c` WITH A CONCRETE MARK: `a ∩ D-c` with the mark of `a`, as before F72 (Lean `emitM`). No weaker normal
    premise lies inside a concrete pattern: a `*` tail with a concrete mark starts as `[any]` in the demand layer
    (`ap.md` W2, §6.5), and a must-premise is a stronger assumption. The rest of this bullet is about this case.

  The tail of `a ∩ D-c` follows the emission table of `ap.md` §6.3: for an added fact and a pattern that both have an
  any tail, it is the tail of the ADDED FACT. So an `[any-taint]` added fact (it is normal on its link, `ap.md` W8)
  gives an `[any-taint]` initial fact, a MUST-PREMISE, and an `[any]` added fact gives an `[any]` initial fact. The
  emission reads the exclusion `E` of an `[any-taint]/E` added fact as part of its location set: a premise at the path
  of the added fact keeps `E` (a `$` premise has none); the pattern chain below the added fact, at `a.path ++ r`,
  gives a premise with no exclusion, and only if `E` admits `r` (else the emission is empty: no common location). The
  must flag comes from the added fact, not from the pattern (Lean: `AnyTaintEx.emitX`, `emitTX`; the vectors
  `AnyTaintEx.Vec.emit_at`, `emit_above_excluded`, `emit_above_exact`, and the table without exclusions
  `AnyTaint.EmitVec`). The backward run gives the forward run concrete patterns with the tails `$` and `[any]` (§7.4).
  Since F72 it also gives `*` patterns, and every forward pattern with a `*` tail has the mark `*` (a concrete mark has
  no `*` tail, W2): the emission gives its FLOW form, so the meet of the tails never reads a `*/E` forward pattern.
  THE MARK OF THE EMISSION (`ap.md` §6.3; `ap-history.md` F71, F72). A concrete `T` in `D-c` admits only an added fact
  with the mark `T`, and the initial fact has that mark (Lean `markMatchB`). AN ABSTRACT ADDED FACT UNDER A CONCRETE
  PATTERN EMITS NOTHING (the user's decision, 2026-10-10: "If an added fact is * and the demand is T -- nothing is
  emitted. That is OK. The added fact can't satisfy the demand."). So an added fact with the mark `*` or `*∖X` (since
  F72 a restricted run has them, under a FLOW premise) gets no initial fact from a pattern with a concrete mark, and
  no request asks for the mark (R4). This is the emission `emitM` as it is (`markMatchB T * = false`; `ap.md` §6.3,
  the table of the marks). A `*` in `D-c` admits every mark and gives the FLOW form, with the mark `*`. THE
  `*∖X` CELL IS DEAD SINCE F72: the hand-off replaces every `*∖X` pattern mark by `*` (R1, §7.3, §7.4). Before F72 a
  backward entry pattern with the mark `*∖X` (a run-1 summary conclusion after a cleaner) admitted every mark that is
  not in `X`, and a requirement with a mark in `X` got no initial fact from it (`Handoff.RVec.vEmit_starEx_T`;
  `vEmit_starEx_U`; before F71 `*∖X` counted as `*`, `vEmit_starEx_T_pre70`). The implementation can keep the test of
  the cell. The emitted premise lies inside its `D-c`, in its locations and its mark: for a concrete added fact under a
  concrete pattern this is proved (Lean `Handoff.emitM_insideB`; with the exclusion `HandoffX.emitX_insideXB`); for
  the FLOW form it is PENDING (§11; R5: it lies inside its own `*` pattern). So the restriction of its summaries keeps
  it (§4.6).
* THE ZERO DEMAND. `(zero, none)` is part of the demand of EVERY method key, also when the demand store has no entry
  for it. So the zero added fact always emits the zero fact. The zero fact of a root is an initial fact. The zero fact
  is not localized: it enters every callee that it reaches, in every run (§11 THE ZERO FACT).
* A METHOD KEY WHOSE ONLY DEMAND PATTERN IS THE ZERO DEMAND has only the zero fact as an initial fact (a seed of a
  backward run is a zero-to-fact edge, not an initial fact). In a restricted FORWARD run its callers get its non-zero
  results only from its records (§3); in a backward run its zero-premise summaries (the seed paths) also return (rule
  `zret`). So the hand-off of the demand edges decides which method keys a run analyses from a non-zero fact (§7.8).
* BACKWARD RUN. As a restricted run, with the requirement as the added fact (`ap.md` §9.2; F72 R2). A `*` pattern
  weakens the requirement to its FLOW form. Example, the getter `get(p): ret = p.name`: the requirement
  `(ret, ., $, T)` under the pattern `(ret, ., [any], *)` (the run-1 summary of the getter is in the demand layer, so
  it is a demand edge, §7.3) gives the FLOW premise `(ret, ., *, {}, *)`, and a requirement with another mark under
  the same pattern gives the same premise (SHARING, `ap.md` §6.3). Also, `addZeroEntry` makes the zero fact an initial
  fact (rule `zin`).
* `initials.add` deduplicates. Each new initial fact starts with its start fact (`ap.md` §6.5) at every start node of
  its kind, then the start rules. The start fact of a must-premise `(x, p, [any-taint], E, T)` is the premise itself,
  `(x, p, [any-taint], E, T)`, in the normal layer (a forward restricted run only: the backward run has no
  must-premise). Its edges are END-EXACT (`ap.md` §1; Lean: `AnyTaintEx.startX`; `AnyTaintExExact.startX_must_end`).
  The start fact of a FLOW premise (F72, forward and backward) is that of `ap.md` §6.5.

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
§4.9), and every result of such a reversed edge is in the demand layer (§4.3 THE REVERSAL OF A CONJUNCTION).

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

THE TRIGGER OF AN END FACT (`ap.md` §9.2; `ap-history.md` F70). An end fact exists only after its sink triggers, so
its reversal must demand the trigger. When the reversed end-fact edge of a sink alternative `A` at the statement `s`
of the method key `M` applies to a requirement, it gives the zero fact (as before), and the analyzer also fires the
sink seeds of `A` at `(M, s)` (SINK SEEDS, §4.7), once per `(M, s, A)`. So the next forward run demands the witness of
the trigger, also when the vulnerability of `A` is CONFIRMED. The seeds of the hand-off do not change: only the DEMAND
vulnerabilities are seeded at the barrier (§7.3). The same rule holds for the reversed end-fact edges of an entry sink
and of an exit sink (§4.4); an unconditional sink (an entry sink, for example) has no sink seed (§4.7), so its trigger
needs only the zero fact. The analyzer makes these seeds from the forms of the sink (`SinkRule.patterns`), not from
the `SeedIndex`, so A4 holds. Argued: the model has no end facts (§11 THE TRIGGER OF AN END FACT).

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
  (`interpreter.md` AC5), and the reversed end-fact edges too. A reversed end-fact edge that applies also fires the
  sink seeds of its sink (THE TRIGGER OF AN END FACT, above). The reversal also drops every type filter.
* A primitive cleaner is its own reversal. Reverse the action order in the cleaners stage and the rewriter.
  A field action is reversed write, clean temporary, reversed read (F74); reverse each statement summary.
  The static kill keeps its keep edges.
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

1. goes to `summaries` (the run summary store), with no restriction. A delta in the demand layer adds one to the
   demand-layer objects of `counters` (§4.1; the stop rule `NO_DEMAND_EDGE`, §7.1);
2. gives the publications:
   * run 1: `j → g` itself;
   * a restricted forward run, and a backward summary whose premise set is not `{zero}`: `restrict(j, g, d)` for each
     demand pattern `d` that the restriction query returns (`ap.md` §6.4, §8.6). Each non-null result is published
     once. The query is `covering(j.base :: j.path)`: the demand patterns of the method whose `D-c` is at or above
     `j` (`ap.md` §8.6; `ap-impl.md` §7.7 `DemandStore.covering`). For a premise set with several members, it is the
     union of `covering` over the members;
   * a backward summary with the premise set `{zero}`: `j → g` itself, with no restriction (`ap.md` §6.4);

   THE RESTRICTION IS AN INTERSECTION, IN THE LOCATIONS AND THE MARKS (`ap.md` §6.4; `ap-history.md` F70, F71). It
   reads `D-c` and `D-p` with their marks:
   * THE PREMISE `j` must lie INSIDE `D-c`, in its locations and its marks: every location of `j` is a location of
     `D-c`, and the marks of `j` are a subset of the marks of `D-c` (a `*` pattern admits every mark, a concrete `T`
     only `T`, a `*∖X` pattern every mark that is not in `X`; Lean `Handoff.insideB`, that is `insideLocB` and
     `markSubB`). Overlap is not enough. An emitted premise always lies inside the entry pattern that emitted it, with
     its mark (Lean `Handoff.emitM_inside`, `emitM_insideB`; with the exclusion `HandoffX.emitX_inside`,
     `emitX_insideXB`; §4.4). A FLOW premise (F72 R5) lies inside its own `*` pattern, and inside NO concrete pattern
     (`markSubB T * = false`): so a concrete pattern never publishes a summary of a FLOW premise, and a `*` pattern
     publishes the summaries of its FLOW premise and of every concrete premise inside it (the Lean form for the FLOW
     premise is PENDING, §11). After the hand-off normalization (R1) no pattern has the mark `*∖X`, so that cell of
     the test is dead.
   * THE MARK OF THE CONCLUSION must meet the mark of `D-p` (Lean `Handoff.concMarkB`): two concrete marks must be the
     same; a `*∖X` side does not admit a concrete mark in `X`; a `*` side meets every mark. Under a concrete premise
     both marks are concrete, so the test is "the same mark": the conclusion `(ret, .f, $, T)` against
     `D-p = (ret, .f, $, U)` gives no publication (`Handoff.RVec.vMark_user_restrictI`; with `D-p = (ret, .f, $, T)`
     it is published, `vMark_user_same`). A conclusion with an abstract mark (`*` or `*∖X`) stays as it is (no form is
     the intersection of a pass-through mark with `T`): the test keeps it if it can pass a mark of `D-p`. Before F72 it
     never occurred in a restricted run. Since F72 it is the conclusion of a FLOW premise (§3).

   Below `D-p` the conclusion stays whole if the tail of `D-p` admits the step. At the path of `D-p` the conclusion
   tail is met with the tail of `D-p` (`[any] ∩ $ = $`, `[any-taint]/E ∩ $ = $`,
   `[any-taint]/E ∩ */E2 = [any-taint]/(E ∪ E2)`; `[any] ∩ */E` keeps `[any]`). The layer and the mark stay. The
   restriction only removes pairs. It keeps every pair `(l1, l2)` of a premise inside `D-c` (in the locations and the
   marks) if `D-p` covers `l2` with its mark: contract C5 (Lean `Handoff.restrictI_sub`, `restrictI_contract`; with
   the exclusion `HandoffX.restrictIX_ok`, `restrictIX_contract`). The form of C5 that reads the locations only is
   false for this restriction (`Handoff.restrictI_contract_loc_false`,
   `HandoffX.XVec.restrictIX_contract_loc_false`: the example above). Before F71 the restriction read `D-c` and `D-p`
   as locations only: it published that conclusion with another mark (`vMark_user_loc`), and the hand-off could give
   it to the next run. That cost precision and work; it lost no flow and gave no false CONFIRMED.

   A publication carries the premise key of `j` with the tail of each member and the exclusion of an `[any-taint]`
   member, so the summaries of an `[any-taint]` premise and of an `[any]` premise of one path are different
   publications (§4.1). The restriction does not change the premise. It reads the exclusion of a must-premise in the
   inside test, together with the mark test (Lean `HandoffX.insideXB`, that is `insideLocXB` and `markSubB`; the
   conclusion test `concMarkB` is that of `restrictI`), and the exclusion of an `[any-taint]/E` conclusion as part of
   its location set: a conclusion above `D-p` gives the chain of `D-p` only if `E` admits the step down, and that
   chain has the exclusion `E2` of a `*/E2` exit pattern, else no exclusion (`ap.md` §6.4). Lean: the object
   `pub m j mj jex g` of `PipelineAnyTaintEx.sysDRX` carries the must flag `mj` and the exclusion `jex`;
   `HandoffX.restrictIX` (before F70 `AnyTaintEx.restrictX`); the backward run `Handoff.restrictI`;
3. goes to `pendingPublications`.

THE HAND-OFF READS THE PUBLICATIONS (`ap.md` §8.5; Lean `Handoff.pubD`, `pubR`). Run 1 publishes every summary edge
as it is. A restricted run publishes the intersections. Each publication of a leaf that is NOT crossable (§1) is a
demand edge of the run, and it gives one demand pattern of the next run per member of its premise (§7.3, §7.4). A
crossable leaf gives no demand edge: `persist` keeps it as a record. THE RUN STORES ITS DEMAND EDGES: at each summary
delta the analyzer also stores the published pieces of the leaves that are not crossable (`ApOps.demandPart`, then the
same restriction as the publications; `RunSummaryStore.addDemand`, `ap-impl.md` DD17), and it counts the crossable
leaves of the delta (`counters`, §4.1). The restriction acts leaf by leaf, so these pieces are the publications of the
non-crossable leaves. The hand-off reads only these stored pieces (`demandEdges()`, §7.3, §7.4).

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
* A RESTRICTED RUN HAS NO REQUEST RULE (forward and backward; `ap.md` §4.5, §6.1 rule 4; `ap-history.md` F72 R4).
  It can have facts with the mark `*` or `*∖X` (§3), but an operation that needs a concrete mark on such a fact gives
  NOTHING and raises no request: the mark gate of a micro edge with a concrete premise mark, the sink check, and the
  T branch of every same-base selected-mark cleaner (the fact continues as `*∖(X ∪ {T})`, also on disjoint paths;
  F75, `ap.md` §4.7). These are the mark rows of `interpreter.md` §5.4:
  also a conditional source, a `CopyMark(T)` pass rule, an ND literal, a literal of a conjunctive sink and the summary
  rewriter. The analyzer of a restricted run has no `requests` store, so `addRequest` and `RequestIn` do not occur there:
  the AP operations of a restricted run make no request (`RunConfig.run1` selects the mode). Before F72 the reason was
  that a restricted run had no `*` fact, and the implementation asserted that no request occurred (decision F35).
  That every flow which needs a concrete mark is still found after run 1 is the claim R6 (§3; PENDING, §11): the
  answers of run 1 make the concrete-mark summaries, and the hand-off carries them as concrete patterns or records.

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
  * a backward run: the SINK SEEDS, the requirements of the sink witnesses of the DEMAND vulnerabilities after the
    forward run before (§1, §7.3; `ap.md` §9.2). A CONFIRMED vulnerability gives no seed of the hand-off: its state
    is final (§7.5). The backward run also fires, by itself, the sink seeds of a sink alternative whose reversed
    end-fact edge applies to a requirement, also of a CONFIRMED vulnerability (§4.5 THE TRIGGER OF AN END FACT).
    A sink pattern gives one requirement. A conjunctive sink gives one requirement per positive
    literal. An unconditional sink gives none. The requirement of an `[any]` sink pattern (`ContainsMarkOnAnyField`)
    has the tail `[any]`: the backward run has no `[any-taint]` (`ap.md` W8, §9.2), so its seed is in the demand
    layer (`ap.md` W6), as before F69. The seeds of a witness are at its method key and its statement;
  * a forward restricted run: the SOURCE SEEDS, the unconditional sources that the backward run before reached
    (`ap.md` §6.1 rule 6, §8.11).
* A sink seed enters as a zero-to-fact edge where the zero fact reaches its statement, cut by the field limit. A call
  sink seeds at the rule point `BOUND` of the reversed plan (§4.5). An exit sink seeds in the start rules (§4.4). A
  sink seed of the trigger of an end fact (§4.5) enters in the same way, at the place of its sink.
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
* THE SINK CHECK ON A `*` FACT (a forward restricted run; F72 R4). The check needs a concrete effective mark
  (`ap.md` §4.9). On a fact whose effective mark is `*` or `*∖X` it gives nothing and raises no request. A FLOW
  premise has only edges with abstract marks (§3), so no sink edge has a FLOW premise in its premise set: a sink
  fires only under a concrete premise or the zero fact (R6; PENDING, §11).

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
 *  of an edge whose forward target is `[any]` is in the demand layer (§4.3). `conjunctive`: a reversed literal of a
 *  conjunctive edge (`StatementSummary.reversed`); every result of it is in the demand layer too (§4.3 THE REVERSAL OF
 *  A CONJUNCTION). No other flag tells the rule kind. */
class MicroEdge(val edge: PathEdge, val forward: PathEdge, val conjunctive: Boolean = false)

/** interpreter.md I1: a statement summary. The AP applies it (ap.md §4.2). `typeFilters`: the operand filters, on the
 *  input (interpreter.md §2.1 step 3). `resultFilters`: the lhs and binding-back filters, on the results
 *  (interpreter.md §2.1 step 5, §3.1). One base can have both (`x = x.f`), so they are two maps. */
class StatementSummary(val touched: Set<AccessPathBase>, val edges: List<MicroEdge>,
                       val conjunctions: List<ConjunctiveEdge>, val typeFilters: Map<AccessPathBase, TypeFilter>,
                       val resultFilters: Map<AccessPathBase, TypeFilter> = emptyMap()) {
    /** ap.md §9.1, §9.2: each edge reversed; a conjunctive edge gives one edge per literal (an OR of the requirements,
     *  each with `conjunctive = true`: every result of it is in the demand layer, §4.3); the identity edge
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
 *  set (ap.md §4.6). Its reversal gives one micro edge per literal, and every result of it is in the demand layer
 *  (§4.3 THE REVERSAL OF A CONJUNCTION). */
class ConjunctiveEdge(val literals: List<Pattern>, val target: PathFact)

/** ap.md §4.8: the type filter `filter(b, may)` of one base; `may` is prefix-closed (S5; today a
 *  `FactTypeChecker.FactApFilter`). `markPolicy`: the primitive mark policy of interpreter.md §5.1, or null (no level
 *  of the static type is primitive or boxed). */
class TypeFilter(val may: FactApFilter, val markPolicy: MarkPolicy? = null)

/** interpreter.md §5.1 `markPolicyKeeps`: keeps `mark` on the value at `[e]^elements` below the base (`elements = 0`:
 *  the base itself; `elements = k`: the k-th element type). A leaf below a field or a class accessor has no policy. */
fun interface MarkPolicy { fun keeps(mark: TaintMark, elements: Int): Boolean }

/** ap.md §4.7: one primitive cleaner; `mark == null`: every mark. Never on the zero base.
 *  A field action lowers to CleanStep.Field (F74, interpreter.md §5.2). */
class Cleaner(val base: AccessPathBase, val path: PathNode?, val reach: CleanReach, val mark: TaintMark?)
enum class CleanReach { EXACT, BELOW, AT_AND_BELOW }

/** One action of the cleaners stage. A field action holds its three ordinary operations and a fresh temporary.
 *  Each statement uses STATEMENT mode and its field-limit cut. Project away the temporary at the action's end,
 *  in both directions. Reverse the action order and each action's operations (F74). */
sealed interface CleanStep {
    class Clean(val cleaner: Cleaner) : CleanStep
    class Kill(val keepEdges: StatementSummary) : CleanStep
    class Field(val temporary: AccessPathBase, val read: StatementSummary,
                val cleaner: Cleaner, val write: StatementSummary) : CleanStep
    fun reversed(): CleanStep
}

enum class CallPoint { BEFORE, BOUND, ADDED, RETURNED, REWRITTEN, AFTER }

/** interpreter.md §3.8 AC3, AC4: where a forward result at REWRITTEN comes from (§4.5 THE ALIAS GUARD). */
enum class Origin { SOURCE, END_FACT, PASS, SUMMARY_EFFECT, IDENTITY }

/** A forward-only selection of the inputs of a stage (§4.5). The reversal drops it. */
sealed interface Guard {
    /** The end-fact stage: it applies on a trigger of `sink`, to the zero fact (§4.5 THE END-FACT STAGE). The reversal
     *  drops the selection, but the reversed `END_FACTS` stage keeps `sink`: a reversed end-fact edge that applies
     *  fires the sink seeds of `sink` (§4.5 THE TRIGGER OF AN END FACT). */
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
    data class Rewrite(override val from: CallPoint, override val to: CallPoint, val steps: List<CleanStep>) : CallStage
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
| STATEMENT | a statement summary (`statementSummary`), the rule summary of a method boundary (`RuleStatement.summary`, with the touched bases and keep edges of §4.4 THE BOUNDARY RULE STATEMENTS), the kill on `S` (`CleanStep.Kill.keepEdges`), the read and write of a field cleaner (`CleanStep.Field`) | `interpreter.md` §2.1 steps 2 to 5: a fact on an untouched base passes; a fact on a touched base keeps only what an edge gives |
| STAGE | the summary of a call stage (`CallStage.Edges.summary`) | only the edges give results. The touched bases of the plan (`CallPlan.touched`) do the pass-over (§4.5). A stage summary has every base of its edges in its touched set, so its reversal adds no identity edge (the reversed plan has the PASS_OVER stage of the alias bases instead, §4.5) |
| GEN | the end-fact edges at the method boundaries (`RuleStatement.endFacts`, the `SinkRule.endFacts` of an entry or exit sink) | the input stays where it is; the edges add results (`interpreter.md` §4.1 END FACTS, §4.7 step 2). An end-fact edge reads the zero fact: on a trigger of its sink, it applies to the zero fact in the layer of the sink edge or of the combination (§4.5 THE END-FACT STAGE). Reversed, it applies to every requirement and fires the sink seeds of its sink (§4.5 THE TRIGGER OF AN END FACT). At a call the end facts are the end-fact `Edges` stage (`END_FACTS`, STAGE mode, on the zero fact, on a trigger, §4.5), whose reversal adds no identity |

THE STATIC EXCEPTION. In run 1 the static exception of `ap.md` §4.10 item 1 acts on the statement micro edges: the
statement summaries, the edges of the sources and the unresolved stages of a call (`StageKind.SOURCES`, `UNRESOLVED`),
the kill on `S`, the read and write of a field cleaner (F74), and the boundary rule statements.
At a call it is tested on the caller edge. It acts on no other stage.

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
        satisfies(premise.member(k).toPattern(), sub.addedFact, config.restricted)   // ap.md §6.3 `satisfies`:
        // restricted: inside; for a FLOW premise (the mark *) also applicable (F72 R3)
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
`AnyTaintExKinds.DRX_normal_premise`, under `AnyTaintEx.EmitCopiesMarkX`, which `emitX` satisfies,
`AnyTaintEx.emitX_copies`), so each leaf that R3 reverses reverses exactly
(`Reverse.rev_exact_of_empty_premise`; `ap.md` §8.7 R3). THIS IS THE CONCRETE DESIGN. Since F72 the emission does not
copy the mark of a `*` pattern (`EmitCopiesMarkX` does not hold), and a normal edge of a restricted run can also have
a FLOW premise (§3). A FLOW premise of a `*/E` pattern has the exclusion `E`, and `Reverse.rev_exact_of_empty_premise`
does not apply to its records when `E ≠ {}`. The exactness of the normal edges of a FLOW premise and of their
reversals is PENDING (§11, lemma L5).

The reversal of an `[any-taint]` leaf with the empty exclusion (a leaf `$ → [any-taint]`) has the premise `[any]` in
the backward run (`ap.md` §9.1). It applies only to an `[any]` requirement, which is in the demand layer (W6), so its
results are in the demand layer. It gives no normal backward edge: a reuse limit (§11).

A must-premise needs every location of it, so a summary of an `[any-taint]` premise applies only to an added fact that
the premise lies INSIDE, with the exclusions of both (`ap.md` §4.3; Lean `AnyTaintEx.SatInsideX`: the exactness needs
it, `satX` has it, `AnyTaintEx.satX_inside`). An `[any-taint]` premise occurs only in a forward restricted run, and
there `matches` is `inside`; so `matches` needs no other test. A FLOW PREMISE (the mark `*`, a restricted run since
F72) is satisfied by `inside` or by `applicable` (`ap.md` §4.3; F72 R3; Lean: `Abs.satW` in the base model; the X-tail extension is pending): it passes the mark
of the added fact, as the policy premise of run 1 and a `*`-premise record do. `satisfies` reads the mark of the
premise, so `matches` needs no other test. A concrete premise is satisfied by `inside` only. A normal edge of a
must-premise is END-EXACT: every
admitted location of its conclusion gets its value from some admitted location of the premise. It is not exact pair
by pair (`AnyTaintEx.EndExactX`; `AnyTaintExact.CexApp.record_not_pair_exact`).

The index queries (`ap.md` §8; keys `base :: path`):

| Test | Replay (publications for a new `a`) | Delivery (subscriptions for a new `j`) |
|---|---|---|
| run 1, `applicable(j, a)`: `a` at or below `j` | `lookupPrefixes(a.base :: a.path)` | `lookupExtensions(j.base :: j.path)` |
| restricted, `inside(j, a)`: `j` at or below `a` | `lookupExtensions(a.base :: a.path)` | `lookupPrefixes(j.base :: j.path)` |
| restricted, a FLOW premise `j` (F72): `inside(j, a)` or `applicable(j, a)` | both lookups of the two rows above, on the publications of FLOW premises | both lookups of the two rows above, for a new FLOW premise `j` |
| a record, `applicable` or `inside` | `around(a.base :: a.path)` on `byEntry`, and on `byExit` with the reversed premise as the key | (records are read-only) |

Each lookup returns every entry that its exact test accepts (`PipelineStore.replay_run1`, `deliver_run1`,
`replay_restricted`, `deliver_restricted`, `record_lookup`). For a FLOW premise the union of the two candidate sets
contains every entry that `inside` or `applicable` accepts. Both paths then call `matches`.

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
  premises: it reverses a conjunction into one micro edge per literal, with every result in the demand layer
  (`ap.md` §9.1, §9.2; §4.3 THE REVERSAL OF A CONJUNCTION).
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
| `PipelineAnyTaintEx.sysD6X_wf`, `sysDRX_wf`, `clD6X_iff`, `clDRX_iff`, `result_D6X`, `result_DRX`, `result_DRXs`, the object theorems (`clD6X_link`, `clD6X_sub`, `clD6X_pub`, `clDRX_link`, `clDRX_sub`, `clDRX_pub`) | the encodings of the closures of the tail `[any-taint]` with its exclusion (`ap.md` §10.11): run 1 with the layer rules W6 and W8 and the exclusion (`AnyTaintEx.D6X`) and a restricted forward run with must-premises and exclusions (`AnyTaintEx.DRX`, generic in the rules; the spec instance has `emitX`, `satX` and `HandoffX.restrictIX`, before F70 `AnyTaintEx.DRXs`). They are well formed, and at a reachable quiescent state the processed objects are exactly the closure, with the must flags and the exclusions (THE ENCODING WITH `[any-taint]`, below). `PipelineAnyTaintEx.SanityX.d6x_ann`, `drx_ann`: a normal `[any-taint]/{name}` edge is in both closures, so the encodings are not vacuous on the exclusion |
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
`AnyTaintEx.DRX` with the spec rules `emitX`, `satX` and the intersection `HandoffX.restrictIX`
(`PipelineAnyTaintEx.result_D6X`, `result_DRX`, generic in the rules; before F70 the instance `AnyTaintEx.DRXs` with
`restrictX`, `result_DRXs`); the backward run is `Backward.DB` as before, with the intersection `Handoff.restrictI`
(`PipelineAP.sysDB`, generic in the restriction).
This holds for the rules that the closures have. The end facts (`ap.md` §11.1), the aliases and their guard (`ap.md`
§11.2, S2), and the global-state rule with the entry-mark removal (`interpreter.md` G2, D35) are outside them (§11 THE
ANALYZER ACTIONS OUTSIDE THE CLOSURES).
THE F72 BASE CLOSURES ARE DEFINED (`Abs.DRA`, `Abs.DBA`); their pipeline encoding is pending (§11). `DR`, `DRX` and `Backward.DB` keep the request
rules; with the emission `emitM` (`emitX`) no request rule fires (`RExact.DR_no_request`, `BExact.DB_no_request`).
With the emission of F72 a restricted run has `*` facts, so the closures of F72 have no request rules (`DRA`, `DBA`,
§11). The protocol model (`Pipeline.lean`, a rule system with owners) does not depend on the rules, so only their
encoding (the `*_wf` and `cl*_iff` theorems) is new work.

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
    /** Asked only after a complete FORWARD run that no stop rule ended. `frontiers`: the frontier of every complete run
     *  so far, in run order; the last one is that of `run` (§7.8). A practical stop strategy reads them (out of
     *  scope). */
    fun continueAfter(run: RunConfig, result: RunResult, frontiers: List<Frontier>): Boolean
    /** The timeout of one run. `remaining`: the ONE budget of the analysis minus the time so far (§0). Default: the
     *  run gets the rest of the budget. */
    fun timeout(run: RunConfig, remaining: Duration): Duration = remaining
}

/** What one run and its barrier give: the next run, or the end of the analysis. */
sealed interface Next {
    class Run(val config: RunConfig) : Next
    class End(val status: RunStatus, val reason: EndReason = EndReason.ABNORMAL) : Next
}

class IterationDriver(private val policy: IterationPolicy, private val shared: SharedObjects,
                      private val budget: Duration) {                // ONE budget for the whole analysis (§0)
    fun analyze(roots: List<MethodKey>): Report {
        val start = TimeSource.Monotonic.markNow()
        val report = ReportBuilder()                                  // §7.5
        val frontiers = ArrayList<Frontier>()                         // §7.8: one per complete run
        var index = 1                                                 // the current run: AnalysisEnd names it
        fun end(status: RunStatus, reason: EndReason) = report.build(AnalysisEnd(status, index,
            if (index % 2 == 1) Direction.FORWARD else Direction.BACKWARD, reason))
        try {                                                         // ONE GUARDED REGION: the whole loop body (§6.3)
            require(policy.fieldLimit(1) >= 1) { "ap.md S12 (d): run 1 needs a field limit of at least 1" }
            var config = RunConfig(1, policy.fieldLimit(1), demand = null, records = shared.records.view(),
                seeds = SeedIndex.EMPTY, roots = roots)
            while (true) {
                index = config.index
                when (val next = runOnce(config, report, frontiers,
                        policy.timeout(config, budget - start.elapsedNow()))) {
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
    private fun runOnce(config: RunConfig, report: ReportBuilder, frontiers: MutableList<Frontier>,
                        timeout: Duration): Next {
        val result = RunManager(config, shared).run(timeout)          // a new engine (§2); it joins its runners (§6.3)
        if (result.status != RunStatus.COMPLETE)                      // §7.5: adds nothing, refutes nothing
            return Next.End(result.status)
        // THE BARRIER (§7.2): no runner runs now. Its own memory guard (B4): a hit cancels the Cancellation, and the
        // barrier stops at its next checkpoint.
        val guard = MemoryManager(shared.refManager, BARRIER_MEMORY_THRESHOLD) { shared.cancellation.cancel() }
        val next = try {
            guard.runWithMemoryManager { barrier(config, result, report, frontiers) }   // soft references stay enabled
        } catch (e: Cancellation.Cancelled) {
            Next.End(RunStatus.OOM)                                   // the barrier guard is the only canceller here
        }
        return if (shared.cancellation.isActive()) next else Next.End(RunStatus.OOM)   // a hit after the last checkpoint
    }

    private fun barrier(config: RunConfig, result: RunResult, report: ReportBuilder,
                        frontiers: MutableList<Frontier>): Next {
        val forward = config.direction == Direction.FORWARD
        if (forward) {
            confirm(result)                                           // §7.5 steps 1, 2: the support, the witnesses
            report.add(config, result)                                // §7.5 step 3
        }
        shared.records.persist(config, result)                        // ap.md §8.7 R1: the crossable leaves among them
        val handOff = handOffOf(config, result, report)               // §7.3, §7.4: the demand edges and the seeds
        val frontier = frontierOf(config, result, handOff, report)    // §7.8
        frontiers += frontier
        logger.info { frontier.toString() }                           // THE FRONTIER LOG (§7.8), every complete run
        if (forward && !report.hasDemandVulnerability())              // no DEMAND vulnerability, so no seed
            return Next.End(RunStatus.COMPLETE, EndReason.STOP_RULE)
        if (forward && result.demandLayerEdges == 0L)                 // no demand-layer edge, summary or link (argued)
            return Next.End(RunStatus.COMPLETE, EndReason.NO_DEMAND_EDGE)
        if (forward && !policy.continueAfter(config, result, frontiers))
            return Next.End(RunStatus.COMPLETE, EndReason.POLICY)
        return Next.Run(nextConfig(config, handOff))
    }

    private fun nextConfig(config: RunConfig, handOff: HandOff): RunConfig {
        val limit = policy.fieldLimit(config.index + 1)
        require(limit >= config.fieldLimit) { "ap.md W3: the field limit must not decrease" }
        return RunConfig(config.index + 1, limit, handOff.demand, shared.records.view(), handOff.seeds, config.roots)
    }

    companion object {
        /** Today's threshold of the confirmation: `TRACE_GENERATION_MEMORY_THRESHOLD`
         *  (TaintAnalysisUnitRunnerManager.kt:645). */
        const val BARRIER_MEMORY_THRESHOLD = 0.99
    }
}
```

* The run sequence is `ap.md` §6.6: run 1 (forward), run 2 (backward), run 3 (forward), and so on.
* THE STOP RULES (`ap-history.md` F70). After a complete forward run, the barrier applies these rules, in this order:
  1. `STOP_RULE`: after the run the report has NO DEMAND VULNERABILITY (§1): every vulnerability that the run reports
     is CONFIRMED, by this run or by an earlier complete forward run (`ReportBuilder.hasDemandVulnerability`, §10).
     Then the hand-off gives no sink seed (§7.3), so the next backward run has no requirement except the zero fact.
     The CONFIRMED part of the report is final (a CONFIRMED state never changes, §7.5), and every real vulnerability
     is CONFIRMED in it. Reason: each forward run reports every real vulnerability that no earlier complete forward
     run confirmed (§7.7, `HandoffMain.iteration_generalN`; for the driver
     `PipelineHandoffDriverExt.driver_iterationNX_demand`, finite `driver_iterationNX_upto`), and this run reports only
     CONFIRMED ones. That every later forward run only
     repeats the zero fact and the records is ARGUED (`HandoffExclusion.zinv_all` with no seed in any method, then
     `HandoffExclusion.exclusion_demand` per method; the composition is not stated, §11 THE STOP RULE `STOP_RULE`);
  2. `NO_DEMAND_EDGE` (the user's rule, `task.md`): the run has NO DEMAND-LAYER OBJECT: no demand-layer edge delta,
     no demand-layer summary delta and no DEMAND LINK (a link whose added fact is in the demand layer, `ap.md` §8.3)
     (`RunResult.demandLayerEdges == 0`, the `counters` of §4.1). Then every sink witness and every link of the run is
     normal, so each sink witness satisfies conditions 1 and 2 of `ap.md` §4.9 and the condition on the layer of the
     link, and a DEMAND entry fails only the JOINT support of a premise set with several members (a conjunction,
     `ap.md` §4.6): no one call supplies all its members. That a later forward run cannot supply them at one call
     either is ARGUED, not proved, and it is an open question (§11 THE STOP RULE `NO_DEMAND_EDGE`). The stop keeps
     every real vulnerability in the report (§7.5 THE OUTPUT);
  3. `POLICY`: `continueAfter(config, result, frontiers)` gave false (a practical stop strategy that reads the
     frontier log, §7.8; out of scope).

  At every stop after a complete forward run, the report holds every real vulnerability, CONFIRMED or DEMAND (§7.5
  THE OUTPUT; for the driver `PipelineHandoffDriverExt.driver_iterationNX_upto`, with `C` = confirmed by a complete
  forward run up to `k`). The three rules differ only in what a later run can still change: after `STOP_RULE` every
  real vulnerability is CONFIRMED already; after `NO_DEMAND_EDGE` a later run confirms no more (argued, an open
  question); after `POLICY` a later run can confirm more or refute a DEMAND entry.
* The driver applies the stop rules and asks `continueAfter` only after a complete FORWARD run. A complete backward run
  always goes on to the next forward run: its only output is the hand-off of that run (§7.4). So the iteration always
  ends after a forward run, or at an abnormal end (§7.7).
* The driver checks the field limit of each run: run 1 has at least 1 (`ap.md` S12 (d)), and the limit does not
  decrease (`ap.md` W3). A policy that breaks either is an error: the `require` fails, and the iteration ends as at a
  throw in the guarded region (`FAILED`; for run 1 the report has no entry).
* THE BUDGET. The analysis has ONE budget (`budget`, a parameter of the driver, §0). THE TIMEOUT OF A RUN is
  `policy.timeout(config, remaining)`, where `remaining` is the budget minus the time so far: by default each run gets
  the whole rest of the budget. The `RunManager` gets it in `run(timeout)`. A run that its timeout ends is incomplete
  (§6.3), and the analysis ends with the report of the earlier complete forward runs (§7.5).
* THE FRONTIER LOG. After EVERY complete run (forward and backward, also the last one), the barrier computes the
  hand-off and logs the frontier of the run (§7.8). The stop rules do not read the frontier. `continueAfter` gets the
  frontiers of every complete run so far.
* THE END OF THE ANALYSIS is an output: `Report.end = AnalysisEnd(status, run, direction, reason)` (§10). `run` and
  `direction` are those of the last run. The reasons:
  * `STOP_RULE`: a complete forward run with no DEMAND vulnerability; `status` is `COMPLETE`;
  * `NO_DEMAND_EDGE`: a complete forward run with a DEMAND vulnerability and no demand-layer object (edge delta,
    summary delta, link); `status` is `COMPLETE`;
  * `POLICY`: `continueAfter` gave false after a complete forward run; `status` is `COMPLETE`;
  * `ABNORMAL`: an incomplete run (`status` is its status: `TIMEOUT`, `OOM` or `FAILED`), a throw in the guarded
    region of the driver (`status` is `FAILED`), or a hit of the memory guard of the barrier (`status` is `OOM`).
* ONE GUARDED REGION. The whole loop body of the driver is one guarded region (`catch (e: Throwable)`): the
  `RunConfig` of run 1 and its check, `RunManager(...)`, `run(...)` and the barrier (the confirmation, `persist`, the
  hand-off, the frontier log). A throw there, an `Error` too (§6.3), ends the iteration with `FAILED`. The driver
  returns the report so far: the results of the earlier runs stay (`ap-history.md` F67, F68). The `RunManager` joins
  its runners on every exit (§6.3), so no runner of the run runs when the driver returns.
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
  the hand-off, the frontier) call `Cancellation.checkpoint` once per analyzer, so the barrier stops at its next
  checkpoint. The
  iteration then ends with `AnalysisEnd(OOM, run, direction, ABNORMAL)` and the report so far (§7.1). The driver also
  checks the `Cancellation` after the barrier, so a hit after the last checkpoint is not lost (the next `RunManager`
  would activate the `Cancellation` again). The barrier has no deadline (§11).

With B1, the hand-off reads the closure of the run (`PipelineDriver.result_D`, `result_DR`, `result_DB`; with the
tail `[any-taint]` `PipelineAnyTaintEx.result_D6X`, `result_DRX`): the demand edges that the run stored are its
publications of the non-crossable leaves (§4.6). So the hand-off is exactly the hand-off of `ap.md` §9.2 (Lean
`Handoff.handF`, `demOfN`; `PipelineHandoffDriver.driver_iterationNX` reads them from the final states, §7.7).

### 7.3 Forward run `n` to backward run `n + 1`

THE RULE (`ap-history.md` F70). After run 1, every publication of a run (forward or backward) is the INTERSECTION of
one of its summary edges with a DEMAND EDGE of the run before it (§1, §4.6). A crossable leaf never goes into the
demand: the next run reuses it as a record (in its own direction by `ap.md` §8.7 R4, in the other direction by its
reversal, R3). So a method key whose summary leaves are all crossable hands off no demand edge. If also no seed of the next backward run
lies in its call subtree, the next backward run and the next FORWARD run analyse it only from the zero fact (§7.8 THE
EXCLUSION; one round: `HandoffExclusion.exclusion_round`, `HandoffMain.exclusion_canon`, with the tail `[any-taint]`
`HandoffXMain.exclusion_canonX`; over several rounds argued).
The earlier hand-off read EVERY summary edge, in every layer, BEFORE the restriction (Lean
`Backward.revSummaryDemand`, `Backward.demOf`): a complete callee was analysed again in every run, and the search
space did not shrink (the program WRAP, §7.8).

From the demand edges that each method analyzer of run `n` stored (`summaries.demandEdges()`, §4.6) and the report
after run `n` (§7.5):

* DEMAND (the demand edges of run `n`; `ap.md` §9.2; Lean `Handoff.handF`). For every summary edge `j → g` of the
  method (one premise key, one layer) and every leaf of `g` that is NOT CROSSABLE (§1), every PUBLICATION `j → g'` of
  that leaf (§4.6) gives one backward demand pattern `(D-c = g', D-p = j)`. Run 1 publishes every leaf as it is
  (`g' = g`; Lean `pubD`). A restricted forward run publishes the intersections with its demand patterns, in the
  locations and the marks (`ap.md` §6.4; §4.6; Lean `pubR` with `restrictI`). The run stores these pieces when it
  publishes them (`RunSummaryStore.addDemand`, §4.6), and the hand-off reads only the stored pieces
  (`demandEdges()`). The driver builds the `DemandStore` of run `n + 1` from these patterns.
  * THE MARKS OF A PATTERN (`ap-history.md` F71, F72). The pattern keeps the marks of the piece, with one change, THE
    HAND-OFF NORMALIZATION (F72 R1; Lean, PENDING: `handFA`): a mark `*∖X` becomes `*`. So `D-c` has the mark of `g'`
    and `D-p` the mark of `j`, each with `*∖X` read as `*`. The backward run reads both marks: its emission gives the
    FLOW form for a `*` `D-c` and tests the mark of the requirement against a concrete `D-c` (§4.4), and its
    restriction tests the mark of its conclusion against `D-p` (§4.6). A leaf of run 1 after a cleaner can have the
    mark `*∖X`: its pattern has the mark `*`, a larger demand, so it is sound. For the demand the `*∖X` has no
    meaning: the summary and its record keep `*∖X`, and there it stops a mark in `X` at the application (`ap.md` §4.1
    step 5, §4.3). If a mark `T` in `X` is really demanded, an own demand edge with the concrete mark `T` exists: in run
    1 the cleaner raises the request for `T`, and the summary of its answer is a concrete piece (the user's rule; the
    claim R6, PENDING, §11). Between F71 and F72 the backward entry pattern kept `*∖X` and admitted
    every concrete mark that is not in `X` (`ap.md` §6.3, §9.2); before F71 `*∖X` counted as `*` there, as it does
    again since F72.
  * A CROSSABLE leaf gives no demand pattern. The backward run crosses the call by the reversal of its record
    (`ap.md` §8.7 R3; Lean `revRec`, `HandoffBackward.cross_step`): the requirement covers a location of the
    reversed premise, so the reversed record applies by `inside` or `applicable` (`Handoff.cross_applies`). The
    backward run never enters the callee for that leaf.
  * A NORMAL leaf that is not crossable IS a demand edge: a leaf with an any tail (`[any]`, `[any-taint]` with or
    without `E`), a leaf of a must-premise, a leaf that is not mark-reversible. The backward run cannot cross it: the
    reversal of an `[any]` leaf has the premise `[any]`, and a `$` requirement neither satisfies that premise nor is
    covered by it (Lean `HandoffCases.revRec_any_premise`, `not_cross_of_any`, `dollar_blocked`). Condition (4) of CROSSABLE is NECESSARY: a hand-off that drops a normal `[any]` leaf (the
    looser test `HandoffCases.CrossL`, the forward conditions only) loses a real vulnerability, with the source seeds
    (`HandoffCases.AnyW.cegar_cross_anyw`) and without them (`HandoffCases.AnyM.cegar_cross_anym`).
  * A summary with several premises `{j1, …, jk} → g` is never a record (`ap.md` §8.7 R1), so no leaf of it is
    crossable. Each publication of a leaf gives one pattern `(D-c = g', D-p = jm)` per member `jm` (`ap.md` §9.2;
    argued, `ap.md` §11.2).
  * A zero-premise summary edge follows the same rules: a crossable leaf of it is a record (R1), and a leaf that is
    not crossable gives `(D-c = g', D-p = zero)` for each publication. In a restricted run a zero-premise summary has
    a publication only through a demand pattern with a `D-p` (§4.6).
  * The backward run has no `[any-taint]` (`ap.md` W8), so the driver reads a forward summary as a location set: a
    leaf or a premise with the `[any-taint]` tail gives a pattern with the tail `[any]`, and the hand-off drops the
    exclusion `E` of an `[any-taint]/E` leaf or premise (a larger backward demand: sound; `ap.md` §9.2). The marks
    stay, except the normalization of `*∖X` to `*` (above): this view changes only the tails and the exclusions. Lean: the
    driver reads each forward run with its exclusions and must flags dropped (`AnyTaintExCov.forget6`, `forgetX`;
    `PipelineAnyTaintExDriver.resultSeqX`; the publication `HandoffX.pubRX`). The crossable test reads the same view:
    an `[any-taint]` leaf or premise is `[any]` there, so it is never crossable. The hand-off of a run with the
    exclusion can be SMALLER than that of the same run without it: the exclusion removes summaries
    (`AnyTaintExCov.CexRoute.route_a_false`); the driver theorem reads each refined run directly (§7.7).
* SINK SEEDS (Lean `seeds k`). The `SeedIndex` of the sink witnesses of the DEMAND vulnerabilities after run `n` (§1):
  the vulnerability keys that run `n` reports and that NO complete forward run so far confirmed (the DEMAND entries
  of the report, `ReportBuilder.demandEntries`, §10). Every sink witness of such a key in run `n` gives its seeds
  (§4.7; `ap.md` §9.2). A CONFIRMED vulnerability gives no seed, also when run `n` reports it only in the demand
  layer: its state is final (§7.5), and a confirmed vulnerability is real (`ap.md` §8.10). The iteration theorem
  needs only this: every vulnerability that run `n` reports is CONFIRMED by a run up to `n` or seeded (the hypothesis
  `hseeds` of `HandoffMain.iteration_generalN` and of `PipelineHandoffDriverExt.driver_iterationNX_demand`, with
  `C k` = "a complete forward run up to `k` confirmed the key", §7.7). With no DEMAND vulnerability there is no seed,
  and the driver stops (`STOP_RULE`, §7.1).
  THE TRIGGER OF AN END FACT. These are the seeds of the hand-off. The backward run also fires, by itself, the sink
  seeds of a sink alternative whose reversed end-fact edge applies to a requirement, also of a CONFIRMED
  vulnerability (§4.5 THE TRIGGER OF AN END FACT): an end fact exists only after its sink triggers, so a requirement
  on it demands the trigger. Without this rule a real DEMAND vulnerability whose flow starts at the end fact of a
  CONFIRMED sink is refuted: the next forward run does not demand the witness of the CONFIRMED sink, the sink does not
  trigger, and the end fact is not made. Argued (§11 THE TRIGGER OF AN END FACT).
* RECORDS. The `RecordStore` persists the normal summary edges with one premise (`ap.md` §8.7 R1, forward). Every
  crossable leaf is a leaf of such a record (§1): it goes to the records and not to the demand. A normal leaf that is
  not crossable goes to both: its record applies in the later forward runs (R4), and its publications are demand
  edges.
  COMPLETE is one notion: a normal edge. A normal forward edge is complete also with an `[any-taint]` leaf (with its
  exclusion) or an `[any-taint]` premise, so `persist` keeps it with the tails and the exclusions. (The premise of a
  normal edge of a restricted forward run is a `$` premise or a must-premise `[any-taint]` with a concrete mark:
  `AnyTaintExKinds.DRX_normal_premise`, `DRX_must_premise`, under `AnyTaintEx.EmitCopiesMarkX`, §5.3. These lemmas
  describe the concrete design: since F72 the premise of a normal edge can also be a FLOW premise, and the emission of
  a `*` pattern does not copy the mark, §5.3.) A record with
  an `[any-taint]` premise keeps that tail
  and its exclusion: it applies by `inside`, or by `applicable` with demand results (§3), and no leaf of it is ever
  reversed (§5.3). Of any other record, an `[any-taint]/E` leaf with `E ≠ {}` is not reversed; the other leaves of
  its record are (R3 is leaf by leaf, §5.3).

### 7.4 Backward run `n + 1` to forward run `n + 2`

The same rule as §7.3, in the other direction. From the demand edges that each backward method analyzer stored
(`summaries.demandEdges()`, §4.6), for every method `M` (`ap.md` §9.2; Lean `Handoff.demOfN`):

1. the zero demand `(D-c = zero, D-p = none)` (implicit for every method key, §4.4);
2. for every zero-premise backward edge at the forward entry of `M`, with the conclusion `gb`: `(D-c = gb, none)`.
   A zero-premise backward edge is never a record (`ap.md` §8.7 R1: the seed paths), so it is always a demand edge.
   It is not restricted (§4.6), and it is not localized (§11 THE ZERO FACT);
3. for every backward summary `jb → gb` of `M` whose premise `jb` is not the zero fact, and every leaf of `gb` that is
   NOT CROSSABLE (§1: the leaf is not normal, or its reversal is not crossable; Lean `¬ Handoff.CrossB jb gb`), every
   PUBLICATION `jb → gb'` of that leaf (§4.6: the intersection with a backward demand pattern of `M`, in the
   locations and the marks) gives `(D-c = gb', D-p = jb)`, with the hand-off normalization: a mark `*∖X` of `gb'`
   becomes `*` (F72 R1, §7.3; Lean, PENDING: `demOfNA`). The exit pattern `jb` is an emitted requirement: a concrete
   requirement with its mark, or (since F72) a FLOW requirement with the mark `*` (§4.4). It covers the forward exit
   location of each backward pair with its mark. So the next forward run publishes through a concrete `jb` only a
   conclusion with the mark of `jb` (§4.6), and a real flow through the call is DEMANDED with both marks (§7.7; Lean
   `HandoffBackward.seg_genN`, for the concrete design; with the FLOW requirements of F72 this is contract B with the
   modes, PENDING, §11). The run stores these pieces (§4.6), and the
   hand-off reads them (`demandEdges()`). A backward summary through the reversal of a conjunction is in the demand
   layer (§4.3 THE REVERSAL OF A CONJUNCTION), so it is never crossable, and this case hands it off. A CROSSABLE leaf
   gives none: the next forward run crosses the call by the reversal of its record (`ap.md` §8.7 R3; Lean `revRec`,
   the record set
   `HandoffBackward.rcNextOf`: each record from the backward run is the reversal of a NORMAL backward leaf,
   `HandoffBackward.rcNextOf_back_normal`), with no analysis of the callee for it. Example: the getter `get(x): ret = x.f` has a run-1 summary in the demand layer, so
   it is a demand edge; its backward summary `(ret, .a, $, T) → (arg, .f.a, $, T)` is normal and its reversal is
   crossable (`Handoff.CrossB`), so forward run 3 crosses `get` by the reversed record, analyses `get` only from the
   zero fact, and reports the vulnerability in the NORMAL layer (Lean `HandoffCases.Getter`: `g1_exit_demand`,
   `revRec_g_cross`, `revRec_g_crossB`, `demG_exact`, `fg_getter_zero_only`, `fg_record_sat`, `fg_found`; these are
   results of the concrete design). SINCE F72 (PENDING the model) the pattern of `get` is `(ret, ., [any], *)`, a `*`
   pattern, so backward run 2 weakens the requirement `(ret, .a, $, T)` to the FLOW premise `(ret, ., *, {}, *)`
   (§4.4): the backward demand is coarser, `ret.*` in place of `ret.a`. The backward summary is
   `(ret, ., *, {}, *) → (arg, .f, *, {}, *)`. It is normal and its reversal `(arg, .f, *, {}, *) → (ret, ., *, {}, *)`
   is crossable, so forward run 3 crosses `get` by the reversed record, now by `applicable` (the added fact
   `(arg, .f.a, $, T)` lies below its premise), analyses `get` only from the zero fact and reports the vulnerability in
   the NORMAL layer. The one record serves every mark.

SOURCE SEEDS: the `SeedIndex` of the `sourceHits` of every backward method analyzer (§4.7; `ap.md` §8.11, §9.2;
Lean `FSeeds.srcHit`). A source in a callee that the backward run crosses by a record is not hit, so it does not fire
in the next forward run. Its result still reaches that run: through the record (a zero-premise forward record of the
callee applies whatever the seeds, `ap.md` §9.2), or through a demand edge of the callee, which makes the backward run
enter the callee and hit the source. PROVED: contract B with the source seeds (`HandoffSrc.B_srcN`: the recorded calls
read no seed) and the iteration (`HandoffSrc.iteration_srcN`, `iteration_srcN_canon`, finite `iteration_srcN_upto`;
with the tail `[any-taint]` `HandoffSrc.iteration_srcNX`, `iteration_srcNX_upto`; the driver
`PipelineHandoffDriverExt.driver_iteration_srcNX`, `driver_iteration_srcNX_upto`). THE SOURCE SEEDS DO NOT FILTER THE
RECORDS: a source inside a crossable callee applies through its record in every later run, whatever the seeds
(`HandoffSrc.SrcRec.found_unseeded`). This adds only facts of the full program: a precision point, not a loss.

RECORDS: the `RecordStore` persists the normal backward summary edges with one premise that is not the zero fact
(`ap.md` §8.7 R1, backward). The backward run has no `[any-taint]`, so a backward edge is complete when it is normal,
as before F69. The may stays out of the records: an `[any]` requirement is in the demand layer (W6), and so is every
result of a reversed micro edge whose forward target is `[any]` and of a reversed conjunctive micro edge (§4.3). So a
demand-layer backward leaf is never crossable, also when its reversal has crossable tails: it is a demand edge (case
3; Lean `Handoff.CrossB` reads the layer).

THE DEMAND PATTERNS that the backward run hands off. From a concrete requirement they are concrete, with the tails `$`
and `[any]`: no `*` tail, for seeds with concrete marks and no `*` tail. Before F72 every backward requirement was
concrete, so no pattern had a `*` tail (Lean `HandoffNoStar.demOfN_nonstar`, `canon_dem_nonstar`; §7.8). THIS DOES NOT
HOLD FOR F72: a FLOW requirement (§4.4) has FLOW conclusions, so the backward run also hands off patterns with the
mark `*`, also with a `*` tail (`*/E`); the next forward run emits their FLOW form (§4.4). The emission of the next
forward run gives the tail of the ADDED fact for two any tails under a concrete pattern (`ap.md` §6.3), so an
`[any-taint]` added fact still gives a must-premise from a concrete `[any]` pattern (§4.4; Lean `AnyTaintEx.emitTX`).
Under a `*` pattern it gets the FLOW premise.

THE STATIC BASE. `S` is touched at every call, in every run (`interpreter.md` §3.3), so the driver gives no static
input. A callee that touches no static gives the static fact back through its run-1 identity summary, which is a
record in every later run (`ap.md` §8.7). This needs no rule at the call. The identity summary `(S, ., *) → (S, ., *)`
is crossable (§1), so it is never a demand edge: no run enters such a callee for the static fact.

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
   * a FLOW premise (F72) never takes part in the support: no sink edge has a FLOW premise (§4.7), and every edge of a
     FLOW premise has an abstract mark, so its caller edges never supply a concrete member. So the confirmation does
     not change with F72 (R6, PENDING the model, §11).

   The support is a property of a premise set in one method key. The links carry the data (E-2).
2. Mark each sink witness of the run (a sink edge, or a sink edge set) confirmed or not (`ap.md` §4.9 conditions 1 to
   3). A witness reads the support in its own method key (§4.7). A sink edge set is confirmed only as a whole: the
   union of its premise sets WITHOUT the zero fact (`{zero}` if every edge has `{zero}`; `ap.md` §4.6) must be
   supported jointly. A sink edge with the `[any-taint]` tail in the normal layer is a normal sink edge, so it can be
   confirmed (condition 1). With an exclusion `E` its sink pattern meets a location that `E` admits: the sink check
   reads `E` (`ap.md` §4.9), so the confirmation needs no other test. In a restricted forward run a member of its
   premise set can be an `[any-taint]` must-premise (condition 2). Lean: `AnyTaintEx.Confirmed6X` (run 1),
   `ConfirmedX` (a restricted forward run); a confirmed vulnerability is real (`AnyTaintExExact.confirmed_real_valid6X`,
   `confirmed_realX_valid`; under S7 and S13, and in a restricted run with the spec rules (`emitX`, `satX` and the
   intersection `restrictIX` of F70), which have the rule hypotheses (`HandoffX.restrictIX_ok`: the hypothesis
   `AnyTaintExExact.RestrictOKX`; for the earlier restriction `restrictX`, `AnyTaintExExact.specX_rules`), and with
   exact records in normal form, `AnyTaintEx.RecsExactX`, `AnyTaintExExact.RecsConcX`, `RecsWFX`; `ap.md` §10.11).
   Over the run sequence
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
(§9; `ap-history.md` F68). So the output holds every vulnerability of the latest complete forward run and every
vulnerability that an earlier complete forward run confirmed, and the claim of `ap.md` §0.1 and §6.6 (the analysis
can stop at any complete forward run) holds for the output too. With the seeds of the DEMAND vulnerabilities only
(§7.3), a complete forward run need not report a vulnerability that an earlier run confirmed. But every real
vulnerability is, at every complete forward run, reported by that run (in some layer) or CONFIRMED by an earlier one
(`HandoffMain.iteration_generalN`, with the tail `[any-taint]` `HandoffXIter.iteration_generalNX`; for the driver
`PipelineHandoffDriverExt.driver_iterationNX_demand`, finite `driver_iterationNX_upto`; §7.7). The report
keeps both: the CONFIRMED state is final, and the DEMAND state holds every vulnerability of the latest complete
forward run that no run confirmed. The refutation stays sound: a DEMAND vulnerability that no run confirmed and that
the latest complete forward run does not report is not real (the same theorem). A vulnerability that stays DEMAND in
every run (for example one whose taint passes only through a pass rule with an `AnyField` target, a may `[any]`:
`ap.md` W6 forward, and the demand layer of its reversal backward, §4.3) is output with the state DEMAND.

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
| the run summary stores of a run (the summaries before the restriction and the stored demand edges, §4.1, §4.6) and the `sourceHits` of a backward run | its hand-off is computed (the end of its barrier) | §7.3, §7.4 (the demand edges, the source hits); `persist` (the summaries, `ap.md` §8.7 R1) |
| the `counters` of every analyzer of a run (§4.1) | its frontier is logged (the end of its barrier) | §7.1 (`NO_DEMAND_EDGE`), §7.8 |
| the frontier of a run (counts and method keys, no edge) | the end of the analysis | §7.8; `continueAfter` |
| the links of a forward run | its confirmation is computed | §7.5 |
| the edge stores, the initial fact stores, and the links of a backward run | the end of the run | — (the barrier never reads them) |
| `SummaryStorage`, `SubscriptionManager`, the runners, the backward analyzers | the end of the run, or its hand-off | — |
| `RecordStore`, `VulnerabilityStore`, `MethodContextCache`, `ApManager` | the end of the analysis | every run |

THE BARRIER READS ONLY: the links of a forward run (the support), the summaries before the restriction (`persist`),
the stored demand edges (the hand-off, §4.6), the `sourceHits` of a backward run (the hand-off), the `counters` (the
stop rule `NO_DEMAND_EDGE`, the frontier), the `VulnerabilityStore` and the report (the confirmation,
the report, the stop rule `STOP_RULE`, the sink seeds of the DEMAND vulnerabilities) and the forms of the
`MethodContextCache` (the seed patterns). So the `RunManager` keeps of a complete run only what the barrier reads: at
the end of the run it drops the edge stores, the initial fact stores and the links of a backward run. Before it drops
an initial fact store, it sets the `counters` that the frontier reads (a non-zero initial fact exists or not). The
barrier holds the stores that it reads under its own memory guard (§7.2 B4). The driver keeps the result of a run
only in the frame of its barrier (`runOnce`, §7.1), so no live slot keeps it during the next run.
Every other object of a run is garbage after the run: the edge stores too. No store of a run stays for a trace resolver
(the trace resolution is out of scope, §9). An incomplete run keeps no store after it ends (§7.5). The engine of a run
is never used again (§2), so no state of one run can leak into the next run. This removes the leaks of today's reuse
(Appendix A).

### 7.7 The driver theorems

THE THEOREMS OF THIS SECTION ARE FOR THE CONCRETE RESTRICTED RUNS (`ap-history.md` F70, F71). Their restricted runs
are `DR … emitM satI restrictI` (`AnyTaintEx.DRX … emitX satX restrictIX`) and `Backward.DB … emitM satI restrictI`:
the emission copies the mark of the added fact, so every restricted run is concrete (`RExact.DR_concrete`,
`BExact.DB_concrete`), and the closures keep request rules that never fire (`RExact.DR_no_request`,
`BExact.DB_no_request`). THE RULES OF F72 (§3) change the emission (`emitW`), the satisfaction (`satW`), the two
hand-offs (the normalization R1: `handFA`, `demOfNA`) and the closures (no request rules: `DRA`, `DBA`). FOR THEM THE
THEOREMS BELOW ARE NOT YET PROVED: the task is §11 PENDING: THE LEAN MODEL OF F72 (the modes, the lemmas L1 to L6, the
iteration). The names below stay: they hold for the concrete design. They rest on the mark-copying emission (the
hypothesis `EmitCopiesMark`), which is false for `emitW` (a `*` pattern gives the mark `*`), so these claims DO NOT
HOLD FOR F72: `RExact.DR_concrete` and
`BExact.DB_concrete` (a restricted run has `*` facts), `RExact.DR_no_request` and `BExact.DB_no_request` (with `emitW`
the request rules of `DR` and `DB` can fire; the F72 closures have none). The proofs that use them have to be done
again with the modes (L2, L4).

The driver of §7.1 with the hand-off of §7.3 and §7.4 (`ap-history.md` F70; `ap.md` §10.12). The theorems join three
parts:

LEAN NUMBERING. The Lean theorems count the forward runs only: the forward run `k` of Lean is the run `2k + 1` of
§7.1 (run 1 is `k = 0`), and the backward run after it is the run `2k + 2`.

* THE FORWARD CONTRACT of a restricted forward run (`Handoff.CoversN`). Every witness whose calls that return are
  DEMANDED (one demand pattern has a `D-c` that covers the entry location WITH ITS MARK and a `D-p` that covers the
  exit location WITH ITS MARK; Lean `Handoff.FlowRR.call`, `p.covers l2`) or RECORDED (a crossable record of the run
  has the pair) is JUSTIFIED by the run (by a publication or a crossable record), and the run reports its
  vulnerability. Proved for `DR … emitM satI restrictI` (`Handoff.coversN_DR`, by `coverageRN`: a demanded call uses
  the emission inside `D-c` with its mark, `emitM_insideB`, and the contract of the intersection,
  `restrictI_contract`: a premise inside `D-c` in its locations and its marks, and an exit location that `D-p` covers
  with its mark; a recorded call uses `cross_applies`). Before F71 the demanded witness read the exit location without
  its mark (`p.coversLoc l2`); with the mark-aware restriction that form of the contract is false
  (`Handoff.restrictI_contract_loc_false`). With the tail `[any-taint]`: `DRX … emitX satX restrictIX`, read with the
  exclusions dropped, with the base records embedded (`HandoffX.coversN_DRXI`, `RecsEmbed`; its hypotheses
  `HandoffX.EmitInsideX` and `RestrictInsideX` read the marks too, by `insideXB` and `p.covers l2`). Run 1 justifies
  every real witness and reports it (`Handoff.run1_justifies`; with `[any-taint]` `HandoffX.run0X_contract`).
* THE BACKWARD CONTRACT (`Handoff.BackwardContractN`). Every witness that forward run `k` justifies, of a SEEDED sink,
  is demanded or recorded in the next forward run. Proved for `Backward.DB` of `Reverse.Program.rev P` with `emitM`,
  `satI`, `restrictI`, the demand `handF`, the backward records `recsBOf` (the reversals of the crossable records)
  and the next forward records `rcNextOf` (`HandoffBackward.B_generalN`, `B_generalN_canon`; a crossable call:
  `HandoffBackward.cross_step`). The backward run gives the demanded witness WITH THE MARKS: its emitted premise lies
  inside `D-c` with its mark (in the concrete design the requirement is concrete, `HandoffBackward.emitM_insideB_B`;
since F72 a FLOW requirement lies inside its `*` pattern, R5, PENDING), and `D-p = j` covers
  the exit location of the backward pair with its mark (`j` covers it by the forward pair), so the mark-aware
  restriction keeps the pair (`restrictI_contract_B`); its premise `jb` covers the exit location of the next forward
  run with its mark (`HandoffBackward.seg_genN`).
* THE ITERATION (`HandoffIter.iteration_abstract_or`): run 1 and the two contracts, with "every vulnerability that a
  forward run reports is confirmed or seeded", give the conclusion below.

THEOREM (`HandoffMain.iteration_generalN`). The canonical run sequence of the spec rules (`HandoffMain.canonState`):
run 1 is `D … policy1` with the publication `pubD` and no record; the backward run after forward run `k` is
`Backward.DB` of `Reverse.Program.rev P` with `emitM`, `satI`, `restrictI`, the demand `handF` of run `k`, the records
`recsBOf`, no sinks, the zero rules (`zbind = true`) and the seeds `seeds k`; the next forward run is
`DR … emitM satI restrictI` with the demand `demOfN` of that backward run, the publication `pubR` and the records
`rcNextOf`. The field limits are free. Hypotheses:

* the program satisfies the hypotheses of `Backward.iteration_general` (`ap.md` §6.6): `P.WF`, `Reverse.BindTargetsStar`,
  `Backward.StmtsMarkRev`, `NoZeroBack`, `ZeroKept`, `ExitReach`, and every sink pattern has the tail `$` or `[any]`;
* THE SEEDS (`hseeds`): every vulnerability that forward run `k` reports satisfies a predicate `C k` or is in
  `seeds k`.

Conclusion: for every real flow to a sink (a reachable location that a sink pattern with a concrete mark covers), at
every forward run `k`, an earlier forward run satisfies `C` for it, or run `k` reports it, in some layer.

The seeds of §7.3 satisfy `hseeds` with `C k` = "a complete forward run up to `k` confirmed the vulnerability key"
(cumulative): a vulnerability that run `k` reports is CONFIRMED in the report after run `k`, or it is a DEMAND
vulnerability, and its witnesses are seeds. So after every complete forward run the report holds every real
vulnerability (§7.5 THE OUTPUT), and `STOP_RULE` keeps every real vulnerability CONFIRMED (§7.1). For the driver of
§7.1 this is the pipeline form with the DEMAND seeds (below).

* `HandoffMain.iteration_generalN_all`: `C` false, every reported vulnerability seeded: every forward run reports
  every real vulnerability.
* `HandoffMain.iteration_generalN_incl`, THE INCLUSION FORM: the driver may hand off MORE than the canonical sets.
  The backward demand contains `handF` of run `k` (`hdemB`), the backward records contain the reversed crossable
  records (`hrecB`), the forward demand contains `demOfN` of the backward run (`hdem`), and the records of the next
  forward run contain `rcNextOf` (`HandoffBackward.NextRecs`, `hrc`). So an implementation may also hand off a
  crossable leaf or keep more records (`HandoffMain.flowRR_mono`, `reachRR_mono`, `flowRDN_mono_rc`,
  `reachRDN_mono_rc`).

THEOREM, WITH THE TAIL `[any-taint]` (`HandoffXIter.iteration_generalNX`; `ap.md` §10.11). The same on the canonical
sequence of the spec closures (`HandoffXIter.canonStateX`): run 1 is `AnyTaintEx.D6X … policy1`, read by
`AnyTaintExCov.forget6`; the next forward run is `AnyTaintEx.DRX … emitX satX restrictIX` with the base records
embedded (`HandoffXIter.embedRecs`), read by `forgetX`, with the publication `HandoffX.pubRX`; the backward runs are
as above (the backward run has no `[any-taint]`). Also `HandoffXIter.iteration_generalNX_all`,
`HandoffXIter.iteration_reportsNX_canon`, and the inclusion forms `HandoffXIter.iteration_generalNX_incl` (with `C`)
and `HandoffXIter.iteration_reportsNX` (every vulnerability seeded); their X records of the next forward run contain
the embedded crossable base records (`hrecX`), and may contain more. The hypotheses are those of
`AnyTaintExCov.iteration_reportsX`. PROVED.

THEOREM, THE PIPELINE FORM (`PipelineHandoffDriver.driver_iterationNX`). Hypotheses: those of
`HandoffXIter.iteration_reportsNX`; every run is complete: `st1` (run 1, `PipelineAnyTaintEx.sysD6X`), `stR k` (the
restricted forward run `2k + 3` of §7.1, `sysDRX … emitX satX restrictIX`) and `stB k` (the backward run `2k + 2`,
`PipelineAP.sysDB … emitM satI restrictI`) are reachable quiescent states; the driver computes the hand-offs from the
final states (`pubSeqXst`): the backward demand contains `handF` (`hdemB`), the backward records the reversed
crossable records (`hrecB`), the base records `NextRecs` (`hrcN`), the X records embed them (`hrecX`), the forward
demand contains `demOfN` (`hdem`), and the seeds contain EVERY vulnerability of the forward run (`hseeds`).
Conclusion: every forward run holds every real vulnerability, in some layer. The proof joins
`PipelineAnyTaintEx.result_D6X`, `result_DRX` and `PipelineDriver.result_DB` (both generic in the rules) with
`HandoffXIter.iteration_reportsNX` (through `PipelineHandoffDriver.resultSeqX_runSeqNX`, `pubSeqXst_pubSeqNX`). This
is the form with ALL the seeds.

THEOREM, THE PIPELINE FORM WITH THE DEMAND SEEDS (`PipelineHandoffDriverExt.driver_iterationNX_demand`). The
hypotheses of `PipelineHandoffDriver.driver_iterationNX`, with `hseeds` in the form "every vulnerability that forward
run `k` reports satisfies `C k` or is seeded". With `C k` = "a complete forward run up to `k` confirmed the key"
(CONFIRMED in the sense of `ap.md` §4.9; the seeds of §7.3 satisfy `hseeds`), the conclusion is: at every forward run
`k`, every real vulnerability is reported by run `k`, in some layer, or confirmed by an earlier forward run. On the
final states: `PipelineHandoffDriverExt.driver_iterationNX_demand_known`. PROVED. The instance
`PipelineHandoffDriverExt.driver_iterationNX_confirmed` fixes a weaker `C` (a run up to `k` reported the key in the
NORMAL layer, with no test of the support): it is not the confirmation of §7.5, so it is not the form of this driver.

THE DRIVER OF §7.1 AGAINST THESE THEOREMS:

* THE SEEDS OF THE DEMAND VULNERABILITIES. The AP forms with `C` (`HandoffMain.iteration_generalN`,
  `HandoffXIter.iteration_generalNX` and their inclusion forms) and the pipeline form
  (`PipelineHandoffDriverExt.driver_iterationNX_demand`) are proved.
* A FINITE SEQUENCE. The driver stops after a complete forward run (a stop rule or `continueAfter`), or at an abnormal
  end, which adds nothing to the report (§7.5). The finite forms stop the induction at the last complete forward run
  `K`: they need the hypotheses only for the runs before `K`, and they read no run after `K`
  (`HandoffUpto.iteration_generalN_upto`, `iteration_generalN_canon_upto`, `iteration_generalNX_upto`,
  `iteration_generalNX_canon_upto`; the driver `PipelineHandoffDriverExt.driver_iterationNX_upto`). PROVED.
* THE STOP RULES. The report part of `STOP_RULE` follows from the iteration theorem (§7.1); that every later forward
  run only repeats the zero fact and the records is argued (§11). `NO_DEMAND_EDGE` is argued (§11).
* THE SOURCE SEEDS (§7.4): PROVED, with the forward runs on the seeded program `FSeeds.keepSources P σ`
  (`HandoffSrc.B_srcN`, `iteration_srcN`, `iteration_srcN_canon`, `iteration_srcNX`; the driver
  `PipelineHandoffDriverExt.driver_iteration_srcNX`; finite `HandoffSrc.iteration_srcN_upto`, `iteration_srcNX_upto`,
  `PipelineHandoffDriverExt.driver_iteration_srcNX_upto`). The sources at a call, at the method start and at the method
  exit, and the exactness of a seeded run, are argued (§11 THE SOURCE SEEDS).
* THE STATIC RULE AND THE CONJUNCTIONS with the new hand-off: argued (§11). The forward runs of the theorems above
  have no ND edge, and the backward run of the model has no reversed conjunction (§4.3 THE REVERSAL OF A CONJUNCTION).
* THE END FACTS and THE TRIGGER OF AN END FACT (§4.5): outside the model (§11).
* THE EXCLUSION AND THE NARROWING: §7.8.

THE EARLIER HAND-OFF (before F70). `PipelineDriver.driver_iteration`, `driver_iteration_upto`,
`PipelineSeeds.driver_iteration_src`, `PipelineAnyTaintExDriver.driver_iterationX`, `driver_iteration_uptoX` and
`driver_iteration_srcX` state that every forward run holds every real vulnerability for the hand-off of EVERY summary
edge, in every layer, BEFORE the restriction (`Backward.revSummaryDemand`, `Backward.demOf`), with the restriction
`restrictU` (`restrictX`) and with every reported vulnerability seeded. Their hypotheses say that the hand-offs
CONTAIN those sets. The hand-off of §7.3 and §7.4 does not contain them (it leaves out the crossable leaves and reads
the intersections), so the driver of §7.1 is not an instance of these theorems. They stay true for the earlier
design, with the source seeds (`FSeeds.keepSources`, `FSeeds.srcHit`, `FSeeds.iteration_src`; with the tail
`[any-taint]` `AnyTaintExCov.iteration_srcX`) and with a finite sequence; the new hand-off has its own forms of both
(`HandoffSrc`, `HandoffUpto`, `PipelineHandoffDriverExt`, above). For
the runs with the static rule, `ap.md` proves the iteration of the earlier hand-off
(`StaticsIter.iteration_general_DS`), and `PipelineAP.clDS_iff` gives the closure equality (§11). With the tail
`[any-taint]` the driver reads each forward run with its exclusions and must flags dropped (`AnyTaintExCov.forget6`,
`forgetX`; `PipelineAnyTaintExDriver.resultSeqX`). That hand-off can be smaller than that of the same run without the
exclusion (`AnyTaintExCov.CexRoute.route_a_false`), so every proof reads each refined run directly
(`AnyTaintExCov.iteration_reportsX`; with the new hand-off `HandoffXIter.iteration_generalNX`).

### 7.8 Localization and the frontier

The hand-off of the demand edges only (§7.3, §7.4) LOCALIZES the remaining work: a run analyses from a non-zero fact
only the method keys that a demand edge of the run before reaches (§4.4). Two theorems tell how this part changes from
run to run, and the frontier log measures it (`task.md`; `ap-history.md` F70). As in §7.7, THE TWO THEOREMS ARE FOR
THE CONCRETE RESTRICTED RUNS; for the rules of F72 (§3) they are NOT YET PROVED (§11 PENDING: THE LEAN MODEL OF F72).
The narrowing with no exception uses facts that F72 makes false (WHY THERE IS NO EXCEPTION, below).

THE EXCLUSION THEOREM (`HandoffExclusion.exclusion_theorem`; from the leaves `HandoffExclusion.exclusion_round`; on
the canonical sequence `HandoffMain.exclusion_canon`; on the spec closures with the tail `[any-taint]`, forward runs
`AnyTaintEx.DRX … emitX`, `HandoffXMain.exclusion_roundX` and, on `HandoffXIter.canonStateX`,
`HandoffXMain.exclusion_canonX`). Lean numbering (§7.7): `k` counts the forward runs only, so forward run `k + 1` of
Lean is the forward run after forward run `k`. Let a method key `M` satisfy, after forward run `k`:

* forward run `k` hands off NO DEMAND EDGE of `M` (the frontier field `demandEdges[M]` is 0; Lean `hdem : ∀ d, ¬ demB
  M d` with `demB` = the hand-off `handF` of run `k`). A SUFFICIENT CONDITION: every summary leaf of `M` in run `k`
  is crossable (§1), every exit edge of every initial fact, the zero fact too (`HandoffExclusion.exclusion_round`,
  `HandoffMain.exclusion_canon`);
* no seed of the backward run after run `k` lies in the CALL SUBTREE of `M`: `M` and every method that `M` reaches
  through calls (Lean `HandoffExclusion.Reaches`). A seed here is a seed of the hand-off or a seed that the backward
  run fires by THE TRIGGER OF AN END FACT (§4.5): both give seed paths, which return to every caller (rule `zret`).

Then in the backward run after run `k` every edge of `M` is the zero edge, and in forward run `k + 1` the only
initial fact of `M` is the zero fact, and every edge of `M` has the zero premise. The program hypotheses:
`HandoffExclusion.NoZeroGenP` (the conditions (a) to (c) of `NDZeroBase.NoZeroGen`: the only statement micro edge
into the zero base is the zero keep edge, the only binding into the zero base of a callee is the zero binding, and no
binding back goes to the zero base) and no cleaner on the zero base; the seeds have concrete marks
(`BExact.SeedsConc`). The steps: with no demand edge of `M`, the backward run emits no non-zero initial fact in `M`
(`HandoffExclusion.init_zero_nodem`); with no seed below `M`, every backward edge of `M` is the zero edge
(`HandoffExclusion.zinv_all`, `exclusion_backward_nodem`); so `demOfN` gives `M` only the zero demand
(`HandoffExclusion.exclusion_demand`); so the next forward run emits only the zero fact in `M`
(`HandoffExclusion.forward_zero_init`, `forward_zero_edges`; all in `HandoffExclusion.exclusion_theorem`).

A METHOD KEY THAT LEAVES THE FRONTIER STAYS OUT while no seed lies in its call subtree. In forward run `k + 1` the
only demand pattern of `M` is the zero demand `(zero, none)`. In a restricted run a zero-premise summary is published
only through a demand pattern `(zero, jb)` with a `D-p` (§7.3), and a restriction with no `D-p` has no result
(`HandoffCases.restrictI_none`). So `M` publishes nothing, and forward run `k + 1` hands off no demand edge of `M`,
also no demand edge from the zero fact. The condition of the first bullet holds again, so the one-round theorem
(`HandoffExclusion.exclusion_theorem`) applies to the next round. This composition over several rounds is ARGUED:
each round is a Lean theorem, the induction is not (§11). It is the observation of `task.md`: a method key with no
demand edge after forward run `i` gets none in a later run, while no seed lies in its call subtree.

PROGRAM WRAP (`HandoffCases.Wrap`; the field limits 1, 2, 3):

```java
root():  x.a.b.c = source();  r = wrap(x);  sink(r.f.a.b.c);
wrap(x): z = new Z();  z.f = x;  return z;               // the model: ret.f = arg
```

Run 1 gives `wrap` only the complete summary `(arg, ., *) → (ret, .f, *)`, and it is crossable
(`Wrap.w1_exit_cross`, `w1_wrap_exits_cross`). The root cuts the source to `(x, .a, [any], T)` and reports the
vulnerability in the demand layer, so its sink is a seed (`seedsW_exact`).

* THE EARLIER HAND-OFF analyses `wrap` again. Backward run 2 enters `wrap` with `(ret, .f.a, [any], T)`
  (`Wrap.old_b2_wrap_init`) and hands off `((arg, .a, [any], T), (ret, .f.a, [any], T))` (`old_dem_w`); forward run
  3 emits `(arg, .a.b.c, $, T)` in `wrap` (`old_f3_wrap_init`) and cuts INSIDE `wrap` (`old_f3_wrap_cut`): a
  demand-layer edge in `wrap`, which had none in run 1.
* THE HAND-OFF OF §7.3 gives only the leaf of the root (`Wrap.handF_w1_exact`). Backward run 2 crosses `wrap` by the
  reversed record (`bn_cross`, by `applicable`) and has only the zero fact in `wrap` (`bn_wrap_zero_only`,
  `bn_wrap_edges_zero`). The forward demand is the zero demand and `((x, .a, [any], T), none)` of the root
  (`demN_exact`). Forward run 3 has only the zero fact in `wrap` (`fn_wrap_zero_only`, `fn_wrap_edges_zero`), applies
  the record of `wrap` in the root (`fn_record_applicable`: by `applicable`, not by `satI`; the call is a RECORDED
  call, `wrap_reachRR`), cuts in the ROOT (`fn_cut_in_root`) and still reports the vulnerability (`fn_found`). All in
  one statement: `Wrap.wrap_old_vs_new`.

THE NARROWING THEOREM (the concrete design; for F72 PENDING, WHY THERE IS NO EXCEPTION below): the search space only
shrinks, in the LOCATIONS AND THE MARKS, with NO EXCEPTION (`HandoffNoStar.narrowing_canon_loc_exactM`; its two halves `HandoffNoStar.narrowing_canon_fwd_exactM` and
`HandoffNoStar.narrowing_canon_back_exactM`; one hand-off: `Handoff.handF_narrowM`, `handF_narrow_locM`,
`demOfN_narrowM`, `handF_narrow_DR_exactM`; the forms in the locations only, `HandoffNoStar.narrowing_canon_loc_exact`,
`narrowing_canon_fwd_exact`, `narrowing_canon_back_exact`, `Handoff.handF_narrow`, `handF_narrow_loc`,
`demOfN_narrow`, `handF_narrow_DR_exact`, stay true). Let forward runs `n` and `n + 2` be restricted runs (`n >= 3`;
in the Lean numbering of §7.7 they are the forward runs `k + 1` and `k + 2`). Every demand pattern of forward run
`n + 2` WITH AN EXIT PATTERN (case 3 of §7.4: a fact-to-fact demand edge `(gb', jb)`) lies inside a demand pattern `d`
of forward run `n` of the same method key, in its LOCATIONS AND ITS MARKS: every location of its exit pattern `jb`,
with its mark, is a location of `D-p` of `d` with its mark, and every location of its entry pattern `gb'`, with its
mark, is a location of `D-c` of `d` with its mark. The reason: it comes from `d` through a forward exit edge `j → g`
(piece `g'`) and a backward exit edge `jb → gb` (piece `gb'`), and each restriction puts its premise inside `D-c` and
its result inside `D-p` of the demand pattern that published it, in the locations and the marks
(`Handoff.restrictI_narrow`; with the marks `restrictI_narrowM`, and for a concrete conclusion mark
`restrictI_narrow_conc`). So `jb ⊆ g' ⊆ D-p(d)` and `gb' ⊆ j ⊆ D-c(d)`. The hypotheses: the seeds have concrete
marks and no `*` tail (`BExact.SeedsConc`; a sink pattern has the tail `$` or `[any]`,
`HandoffNoStar.nonstar_of_sinkK`). THE THEOREM DOES NOT NARROW the zero demand and the seed-path patterns
`(gb, none)` (case 2 of §7.4): as locations they shrink when the backward field limit grows (argued), but their COUNT
can grow (§11 THE SEED PATHS). The induction over the rounds is in the theorem: it holds for every round of the
canonical sequence.

WHY THERE IS NO EXCEPTION (`ap-history.md` F70). The intersection keeps two cells whole (`Handoff.RExc`,
`restrictI_inter`): (a) an `[any]` conclusion at or above a `*/E` exit pattern keeps `[any]` (W2: a concrete mark has
no `*` tail), and (b) a `*` conclusion stays as it is. Both need a `*` tail, and in the CONCRETE DESIGN, with the
hand-off of the demand edges, no demand pattern after run 1 has one:

* run 1 hands off no pattern with a `*` entry tail, and its exit patterns (premises of run 1) have the tail `$` or
  `*/{}`: every normal FLOW leaf of run 1 is crossable (§1), and W2 leaves no demand-layer `*` (Lean
  `HandoffNoStar.handF_run1_nonstar`, `run1_exit_star_cross`);
* a backward run with such a demand and with the seeds above emits no `*` premise and has no `*` conclusion
  (`HandoffNoStar.DB_edge_nonstar`), so its hand-off has no `*` pattern (`HandoffNoStar.demOfN_nonstar`); so no demand
  pattern of a forward run has a `*` tail (`HandoffNoStar.canon_dem_nonstar`);
* a restricted forward run has no `*` conclusion (`Handoff.DR_exit_not_star`), and with no `*` exit pattern the
  forward narrowing is exact (`Handoff.handF_narrow_DR_exact`).

F72 MAKES THE LAST TWO BULLETS FALSE. A FLOW requirement of a backward run has `*` conclusions, so the backward
hand-off gives `*` patterns (the claims of `HandoffNoStar.DB_edge_nonstar`, `demOfN_nonstar` and `canon_dem_nonstar`
do not hold for F72), and a FLOW premise of a restricted forward run has `*` conclusions (the claim of
`Handoff.DR_exit_not_star` does not hold). The first bullet still holds: F72 does not change run 1, and the
normalization R1 changes only marks (`handF_run1_nonstar` and `run1_exit_star_cross` read run 1 only). So with F72 the
cells (a) and (b) can occur after backward run 2, and the `_exact` forms below are not the narrowing of the F72
sequence. The candidate is the form with the two cells as exceptions (`HandoffMain.narrowing_canon`,
`narrowing_canon_loc` and their `M` forms); it is not yet proved for the F72 runs (PENDING, §11).

In the concrete design a `*/E` exit pattern occurs only in backward run 2, as a run-1 premise `*/{}`, and there cell (a) adds no location
(`HandoffNoStar.rexc_empty_loc`, `narrowing_canon_back_loc`). The older statements `HandoffMain.narrowing_canon`,
`narrowing_canon_loc` keep both cells as exceptions; the exceptions of `narrowing_canon_loc` are loose (an existential cell that every `*` exit pattern satisfies), so the `_exact` forms are
the narrowing theorem. Their forms with the marks, `HandoffMain.narrowing_canon_fwdM`, `narrowing_canon_backM`,
`narrowing_canonM` and `narrowing_canon_locM`, keep the same two cells for the locations, but in these cells the marks
still narrow. The narrowing is of locations and marks, not of counts: one demand pattern can give several pieces.

THE MARKS HAVE NO EXCEPTION (`ap-history.md` F71). The mark test of the restriction keeps a conclusion with an
abstract mark (`*` or `*∖X`) against a concrete `D-p`, so for one restriction the marks narrow except at an abstract
conclusion mark (`Handoff.restrictI_interM`, `restrictI_narrowM`; the cell is real, `Handoff.RVec.inter_exc_absmark`).
In the concrete design every run of the sequence is concrete: the restricted forward runs (`RExact.DR_concrete`), and
the backward runs with seeds of concrete marks (`BExact.SeedsConc`, `BExact.DB_concrete`). So this cell never occurs
on the sequence, and the narrowing with the marks has no mark exception (`Handoff.restrictI_inter_conc`,
`restrictI_narrow_conc`, `handF_narrow_DRM`; the `M` forms above). THIS DOES NOT HOLD FOR F72: a FLOW premise has
conclusions with abstract marks (§3), so the cell can occur, and the normalization R1 replaces `*∖X` by the larger
`*`. The narrowing of the marks for F72 is PENDING (§11).

WITH THE TAIL `[any-taint]` (forward runs `AnyTaintEx.DRX … emitX satX restrictIX`). One hand-off:
`HandoffX.handF_narrowX`, `handF_narrowX_DRX` (the exceptions `HandoffX.RExcX`), exact with the exclusions. Over a
round on `HandoffXIter.canonStateX`: `HandoffXMain.narrowing_canonX`, `narrowing_canonX_loc`, and with no `*` pattern
`HandoffNoStar.narrowing_canonX_fwd_exact`, `narrowing_canonX_loc_exact`. With the marks (`restrictIX` has the mark
tests of `restrictI`, `HandoffX.insideXB` and `concMarkB`): one hand-off `HandoffX.handF_narrowXM`,
`handF_narrowX_DRXM`, and over a round `HandoffXMain.narrowing_canonX_fwdM`, `narrowing_canonX_backM`,
`narrowing_canonXM`; in the exception cells the marks still narrow. The hand-off reads each forward run with the
exclusions dropped (§7.3). In general a handed-off pattern can then reach past the earlier one at an excluded
location (the `Dropped` alternative of `HandoffXMain.narrowing_canonX_loc`; `HandoffX.XVec.v_inside_only_with_excl`,
`HandoffXMain.XMVec.exit_dropped`, which need a `*/E` demand pattern). With no `*` pattern, as on the sequence of the concrete design (not of F72, which has `*` patterns),
the exit side is exact, and the entry side is exact unless the premise exclusion is Universe, which the AP never has
(`ap.md` §1: no exclusion is Universe; the model keeps `Excl.univ` only to encode a `$` premise;
`HandoffNoStar.narrowing_canonX_loc_exact`).

THE FRONTIER LOG. After each complete run the driver logs the frontier of the run (§7.1; `Frontier`, §10). The log
has counts and method keys, no edge, so it costs one pass over the analyzers of the run (the `counters`, §4.1) and
over the hand-off:

* forward run: the method keys with a non-zero initial fact (`analysed`); the demand edges that the run hands off,
  per method key (`demandEdges`, §7.3); the crossable summary leaves (`crossableLeaves`: the records that replace an
  analysis in the next runs); the record applications that crossed a call in this run (`recordCrossings`); the
  DEMAND and the CONFIRMED vulnerabilities after the run (`demandVulnerabilities`, `confirmedVulnerabilities`); the
  sink seeds that it hands off (`seeds`);
* backward run: the method keys with a non-zero initial fact; the demand edges that it hands off (§7.4); the
  crossable backward leaves; the record applications at a call (`recordCrossings`: the backward records and the
  reversed forward records); the source seeds;
* both: THE WORK OF THE ZERO FACT, the part that §11 THE ZERO FACT leaves: the method keys that the run analysed
  only from the zero fact (`zeroOnly`) and the number of their edges (`zeroOnlyEdges`);
* AN OPTION (a diagnostic): per run, the number of demand-layer results per operation that set the layer
  (`demandByCause`): the field-limit cut, a may target, a cleaner row, the must-record demotion, a demand-layer input
  (§4.3).

By the narrowing theorem the demand patterns with an exit pattern only shrink, in the locations and the marks, per
method key (not the seed-path patterns `(gb, none)`, and not as counts); by the exclusion theorem a method key leaves
`analysed` when the run hands off no demand edge of it (for example, all its leaves are crossable) and no seed is in
its call subtree. The log shows how fast this happens on a real program. For the rules of F72 both theorems are
PENDING (§11), so the log is also the measure of these properties until the proofs are done.

HOW A LATER STOP STRATEGY CAN READ THE LOG (not normative: the policy is out of scope, §0). `continueAfter` gets the
frontiers of every complete run (§7.1). Examples:

* THE FRONTIER IS STABLE: two forward runs with the same set `analysed`, the same demand edges per method key and no
  new CONFIRMED vulnerability. Between them only the field limit changed: by the narrowing theorem the demand patterns
  with an exit pattern cannot grow in the locations or the marks (the seed-path patterns are outside the theorem; for
  F72 the theorem is PENDING), so a further pair of runs can gain only by the larger field limit;
* THE FRONTIER IS SMALL against the work of the zero fact (`zeroOnlyEdges`): a further pair of runs costs mostly a
  full pass of the zero fact (§11) for a small part of the program;
* THE BUDGET: the time of the last pair of runs and the size of the frontier give an estimate of the next pair. If the
  next forward run cannot complete in the rest of the budget, a stop now gives the same report as that incomplete run
  (§7.5: an incomplete run adds nothing) and ends earlier.

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

/** A publication: a summary edge of the callee, after the restriction in a restricted run (the intersection with
 *  one demand pattern, in the locations and the marks: the premise lies inside `D-c` with its mark, and the
 *  conclusion mark meets the mark of `D-p`; ap.md §6.4; §4.6). Its layer is `conclusion.layer`, and its marks are
 *  those of the summary edge. `premise` holds the tail of each member and the exclusion of an `[any-taint]` member: an
 *  `[any-taint]` premise and an `[any]` premise of one path are two premise keys, so two publications (§4.6; Lean:
 *  the must flag and the exclusion of `pub` in `PipelineAnyTaintEx.sysDRX`). */
data class Publication(val premise: PremiseKey, val conclusion: Facts)

/** A request of run 1 (ap.md §4.5, §4.10). A position is an interned path of the new AP (ap.md §7.1). */
sealed interface RequestKind {
    data class Mark(val mark: TaintMark) : RequestKind
    data class Position(val path: PathNode) : RequestKind
}

/** A seed (§4.7). A sink seed (backward run): one requirement of a sink witness of a DEMAND vulnerability (§1, §7.3);
 *  a CONFIRMED vulnerability gives none in the hand-off. The backward run also makes sink seeds by itself: those of a
 *  sink alternative whose reversed end-fact edge applies to a requirement (§4.5 THE TRIGGER OF AN END FACT), once per
 *  (method key, statement, alternative); they are not in the `SeedIndex`. The requirement of an `[any]` sink
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

/** The result of one run. The driver reads its stores only if `status == COMPLETE` (§7.5). `demandLayerEdges`: the sum
 *  of the `counters` of its analyzers (§4.1): the demand-layer objects of the run, that is the deltas of `edges.add`
 *  and the summary deltas in the demand layer and the new demand links (§4.2 `addLink`, §4.6); 0 gives the stop rule
 *  NO_DEMAND_EDGE after a forward run (§7.1). `recordCrossings`: the record applications at a call (§4.2, §7.8). The
 *  DEMAND vulnerabilities are a state of the REPORT, not of one run: `ReportBuilder.hasDemandVulnerability`. */
class RunResult(val status: RunStatus, val analyzers: Sequence<RunMethodAnalyzer>, val runIndex: Int,
                val vulnerabilities: VulnerabilityStore, val demandLayerEdges: Long, val recordCrossings: Long)

/** §7.3, §7.4: what a complete run hands to the next run of the other direction. `demand`: the patterns of the demand
 *  edges only (the publications of the leaves that are not crossable, which the run stored, `summaries.demandEdges()`,
 *  §4.6; from a backward run also the zero-premise edges; the zero demand is implicit, §4.4); each pattern keeps the
 *  marks of its piece, with `*∖X` replaced by `*` (F72 R1), and the next run reads them (§7.3 THE MARKS OF A
 *  PATTERN). `seeds`: the sink seeds of
 *  the DEMAND vulnerabilities (forward run), or the source seeds (backward run). */
class HandOff(val demand: DemandStore, val seeds: SeedIndex)

/** §7.8: THE FRONTIER of one complete run, for the log and for `continueAfter`. Counts and method keys only, no edge.
 *  The vulnerability counts are 0 after a backward run. `demandByCause`: an option (a diagnostic), null if the AP does
 *  not count the demotions (§4.3). */
data class Frontier(
    val run: Int,
    val direction: Direction,
    val analysed: Set<MethodKey>,                    // the method keys with a non-zero initial fact
    val demandEdges: Map<MethodKey, Int>,            // the demand edges that the run hands off, per method key
    val crossableLeaves: Long,                       // the crossable summary leaves (records that replace an analysis)
    val recordCrossings: Long,                       // record applications at a call (forward and reversed records)
    val demandVulnerabilities: Int,                  // the DEMAND vulnerabilities after the run (forward)
    val confirmedVulnerabilities: Int,               // the CONFIRMED vulnerabilities after the run (forward)
    val seeds: Int,                                  // the seeds that the run hands off
    val zeroOnly: Set<MethodKey>,                    // the method keys analysed only from the zero fact (§11)
    val zeroOnlyEdges: Long,                         // the edges of those method keys: the work of the zero fact
    val demandByCause: Map<DemandCause, Long>? = null,
)

/** §4.3, §7.8: the operations that put a result into the demand layer (the option `Frontier.demandByCause`). */
enum class DemandCause { FIELD_LIMIT_CUT, MAY_TARGET, CLEANER_ROW, MUST_RECORD, DEMAND_INPUT }

/** §7.1: why the iteration ended. STOP_RULE: no DEMAND vulnerability after a complete forward run. NO_DEMAND_EDGE: a
 *  complete forward run with no demand-layer edge delta, summary delta or link (argued, §11). POLICY: `continueAfter`
 *  gave false. ABNORMAL: an
 *  incomplete run (its status), a throw in the guarded region of the driver (FAILED), or a hit of the memory guard of
 *  the barrier (OOM). */
enum class EndReason { STOP_RULE, NO_DEMAND_EDGE, POLICY, ABNORMAL }

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

    /** §1, §7.3: the DEMAND vulnerabilities after the latest complete forward run: its keys that NO complete forward
     *  run confirmed (a key that an earlier run confirmed is final, also if the latest run reports it only in the
     *  demand layer). Their witnesses of that run are the sink seeds. */
    fun demandEntries(): List<Report.Entry> = demand.values.filter { it.key !in confirmed }

    /** §7.1: false gives the stop rule STOP_RULE (no DEMAND vulnerability, so no seed). */
    fun hasDemandVulnerability(): Boolean = demandEntries().isNotEmpty()

    fun build(end: AnalysisEnd): Report = Report(confirmed.values + demandEntries(), end)
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
a complete forward run and sets `SinkWitness.confirmed`. `handOffOf(config, result, report)` gives the `HandOff` of a
complete run by §7.3 and §7.4: `demandOf` builds the `DemandStore` of the next run from `summaries.demandEdges()` of
every analyzer (the stored publications of the leaves that are not crossable, §4.6; a backward run also gives its
zero-premise edges), with every pattern mark `*∖X` replaced by `*` (the hand-off normalization, F72 R1, §7.3), and
`seedsOf` the `SeedIndex` (a forward run: the witnesses of `report.demandEntries()`; a
backward run: the `sourceHits`). `ApOps.demandPart` (`ap-impl.md` §5.9) gives the non-crossable part of a summary
value at each summary delta (§4.6); its per-leaf forms are `cross` and `crossReversed` (`ap-impl.md` §6; Lean
`Handoff.Cross`, `Handoff.CrossB`). `nextConfig` makes the `RunConfig` of the next run. `frontierOf(config, result, handOff, report)` makes the frontier of §7.8 in one pass over the `counters` of the
analyzers (§4.1), the hand-off and the report.
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

PENDING: THE LEAN MODEL OF F72 (`ap-history.md` F72). The checked results and their assumptions are in
`ap.md` §10.13; the remaining proof plan is in `ap.md` §11.2. This is the single proof-status list for both specs.
The local model now defines the normalized hand-offs, shared emission, satisfaction, and the two closures without
requests. It proves base-model normal-edge exactness (L5), guarded emission (L6), and index query equivalence.
The F70/F71 iteration and pipeline theorems do not transfer to F72 through these local results.

The full F72 proof must include the field-cleaner lowering condition (`ap.md` §4.7, F74), then general L1 to L4,
the X-tail guard, confirmation support, narrowing, localization,
the X-tail extension and the pipeline instance. The local CEGAR kernels are not proofs of the exact IR programs of
§13. The proposals keep the F71 restricted-run rules until the proofs are complete (the order of `ap.md` §11.2).
They include the independently checked local F74 field-action lowering.

CEGAR FOUND A MODE-CONTRACT GAP. In `get(p) { clean(q, T); return p; }`, with different bases `p` and `q`, the AP
keeps the FLOW fact and raises no request. The old abstract mode rejects the cleaner because its mark is `T`.
Run 1 reports the real sink but does not meet the old mode contract (`ReviewDemand.Before.not_run1_contract_with_modes`).
The user approved the fact-dependent cleaner rule (F73, `ap.md` §6.6). Disjointness must be tested against the propagated fact: two paths on
one base can be disjoint, while a coarser FLOW fact can overlap the same cleaner (`ReviewDemand.same_base_disjoint_flow`).
A test on the concrete witness location alone is insufficient.

THE FIELD-CLEANER MODEL NEEDED A CORRECTION. `ReviewReversal` uses an atomic cleaner on `p.g`, which can lose a flow
after backward FLOW emission. The user's F74 rule is `tmp = p.g; clean(tmp, T); p.g = tmp`, with the ordinary
strong-write keep edges. The backward run keeps `p.*/{g}` with mark `*`, disjoint from the cleaner on `tmp`.
The atomic kernel is not the interpreter program. The general proof must state and use this lowering condition.

A SEPARATE ROOT-EXACT GAP remains. `ReviewRootCleaner` changes the action to `clean(p, EXACT, T)`.
It has the empty path and preserves the concrete `p.n` flow. Run 1 is disjoint and raises no request, but the
backward FLOW fact `p.*` loses T. The exact 1, 2, 3 trace has no source hit and no run-3 finding (`ap.md` §10.13).
This action has no field lowering. Its rule correction awaits the user's decision.

L6 HAS A GUARD. An abstract entry pattern needs the tail `$`, `[any]`, or `*/{}`. For an abstract pattern with
`*/E`, `E ≠ {}`, common locations alone do not make the emitted FLOW premise satisfiable (`Abs.emitW_needs_patTail`).
The guard holds for run 1 (`Abs.handFA_run1_PatTail`) and the explicit alternating base sequence with concrete,
non-star seeds (`AbsHandoff.shapeSeq_PatTail`). The X-tail and pipeline forms remain open. L6 for a concrete pattern also requires a concrete added mark. These are explicit proof assumptions, not
established properties of every F72 run.

The earlier concreteness, no-star-exit and no-star-demand theorems remain evidence for F70/F71 only (`ap.md` §11.2).
The F72 no-request property follows from its closure rules; it does not follow from those earlier concreteness proofs.

ARGUED, NOT PROVED:

* SUBSUMPTION. The AP operations simulate the subsumption of the edge stores (`Subsume.subsumesB`, the tree merges T1
  to T5). `Pipeline.quiescent_dominates` needs this as a hypothesis. For a join it needs: if a stored added fact
  dominates the added fact of a subscription, the join with the stored one gives a dominating result. `inside` has
  this property.
  `applicable` has it only through the invariants of run 1 (the policy premises are at the root path,
  `Statics.no_any_above`). Since F72 a restricted run also applies the summaries of a FLOW premise by `applicable`
  (§5.3), and a FLOW premise is not always at the root path: there the property is not argued. So the subscriptions
  and the links deduplicate exactly (§5.3).
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
  seeded run for `P` (`ap.md` §11.2). The soundness of the source seeds with the new hand-off is proved, also in a
  finite sequence: the finite forms stop the induction at the last run (`HandoffSrc.iteration_srcN_upto`,
  `iteration_srcNX_upto`, `PipelineHandoffDriverExt.driver_iteration_srcNX_upto`; §7.4, §7.7).
* THE DRIVER with the static rule and with the conjunctions. The closure equalities hold (`PipelineAP.clDS_iff`,
  `clDN_iff`). The pipeline form of `StaticsIter.iteration_general_DS`, and the iteration with conjunctions (`ap.md`
  §11.2), are argued, for the earlier hand-off and for the hand-off of the demand edges.
* THE HAND-OFF OF THE DEMAND EDGES (§7.3, §7.4, §7.7; `ap-history.md` F70). In the concrete design (for F72 see
  PENDING, above), proved for the AP closures (with `C`),
  for the pipeline with the tail `[any-taint]` (with all the seeds, `PipelineHandoffDriver.driver_iterationNX`, and
  with the DEMAND seeds, `PipelineHandoffDriverExt.driver_iterationNX_demand`), in the finite form (`HandoffUpto`,
  `PipelineHandoffDriverExt.driver_iterationNX_upto`) and with the source seeds (`HandoffSrc`,
  `PipelineHandoffDriverExt.driver_iteration_srcNX`). Argued:
  * TREES: the model has one path fact per exit edge. The code tests each leaf of a conclusion tree (§1) and restricts
    a tree leaf by leaf (§4.6), with the mark test of the conclusion on the mark of each leaf;
  * THE BACKWARD LAYER IN THE CROSSABLE TEST. `Handoff.demOfN` hands off every backward leaf with `¬ Handoff.CrossB`:
    a demand-layer backward leaf is always a demand edge and never a record, as in the spec (§1, §7.4; `ap.md` §8.7
    R1). But `Backward.DB` has no backward W6 layer rule (below): the layer that the spec gives a backward edge (every
    result of a reversed may edge) is not the layer of the model. So the hand-off is the spec hand-off of the layers
    that `Backward.DB` computes; with the layers of the spec it is argued, as the backward W6 itself;
  * THE STORED PIECES (§4.6): the restriction acts leaf by leaf, so the pieces that the run stores for the
    non-crossable part of a summary delta are the publications of the non-crossable leaves (the union over the deltas
    equals the pieces of the whole summary). The model has the relations `Handoff.pubD`, `pubR`; the fuzzer compares
    the stored pieces with the reference (`analyzer-impl.md` §9.2);
  * A SUMMARY WITH SEVERAL PREMISES: never a record, so every publication of it gives one demand pattern per member
    (as the earlier hand-off; `ap.md` §11.2). Its restriction reads the marks as for one premise: each member lies
    inside a `D-c` in its locations and its mark, and the mark of the conclusion meets the mark of `D-p` (`ap.md`
    §6.4);
  * THE TRIGGER OF AN END FACT (§4.5, §7.3). The model has no end facts (§5.5). Before F70 every reported
    vulnerability was seeded, so the witness of the trigger of an end fact was demanded in every run. With the seeds
    of the DEMAND vulnerabilities only, a CONFIRMED sink is not seeded at the barrier, and without the rule of §4.5 a
    later forward run does not make its end facts: a real DEMAND vulnerability whose flow starts at such an end fact
    is refuted, and the analysis can stop with `STOP_RULE` without it. The rule fires the sink seeds of the trigger
    when a requirement reaches the reversed end-fact edge, so the next forward run demands the witness of the trigger
    and makes the end fact again;
  * THE REVERSAL OF A CONJUNCTION (§4.3). Restricted runs with ND edges are not modelled (`ap.md` §11.2). The rule
    fixes a false positive that existed before F70: the OR-reversal gave a NORMAL backward summary from the
    conclusion to one literal, R1 persisted it, and R3 reversed it into a forward record of that literal alone, which
    drops the other literals of the conjunction (a CONFIRMED false positive at a call that supplies only one literal).
    With every result of the reversal in the demand layer, no such backward summary is a record or crossable, case 3
    of §7.4 hands it off, and the next forward run analyses the callee with all the members;
  * A COST LIMIT. Normal and demand trees of one premise key are separate edges, and no subsumption crosses the
    layers. So a demand-layer piece whose every pair a crossable piece of the same premise and the same demand
    pattern already has is still a demand edge: the backward run enters the callee for nothing, and the callee stays
    in the frontier while its seed exists (for example a may next to an exact write of the same field). A rule that
    drops such a piece needs a Lean variant of `HandoffBackward.seg_genN` (the crossable branch justifies the
    witness); it is a later task. Cost only, not a loss.
* THE EXCLUSION OVER SEVERAL ROUNDS (§7.8). One round is proved (`HandoffExclusion.exclusion_theorem`, with the
  sufficient condition of `HandoffExclusion.exclusion_round`; `HandoffMain.exclusion_canon`; with the tail
  `[any-taint]` `HandoffXMain.exclusion_roundX`, `exclusion_canonX`). The next round is
  `HandoffExclusion.exclusion_theorem` again, with `HandoffCases.restrictI_none` for "no demand edge". The induction
  over the rounds ("it stays out while no seed is below it") is not stated in Lean. (The concrete design; for F72 the
  one round is PENDING too, above.)
* THE SEED PATHS (§7.8). The narrowing theorem (`HandoffNoStar.narrowing_canon_loc_exactM`, in the locations and the
  marks, and `narrowing_canon_loc_exact`; with the tail `[any-taint]` `HandoffNoStar.narrowing_canonX_loc_exact` and
  `HandoffXMain.narrowing_canonXM`) does not narrow the patterns `(gb, none)` (case 2 of
  §7.4) and the zero demand. As locations the seed paths shrink when the backward field limit grows (argued), but
  their COUNT can grow. (The exclusions that the hand-off drops, §7.3, are no gap of the theorem: with no `*`
  pattern the X narrowing is exact except at a Universe premise exclusion, which the AP never has (`ap.md` §1),
  `HandoffNoStar.narrowing_canonX_loc_exact`; the general form `HandoffXMain.narrowing_canonX_loc` has the `Dropped`
  alternative. Since F72 the sequence has `*` patterns, so for F72 this is part of the PENDING narrowing, above.)
* THE STOP RULE `STOP_RULE` (§7.1). That every real vulnerability is CONFIRMED in the report is proved (§7.7). That
  every later forward run only repeats the zero fact and the records is argued: in a backward run with no seed every
  edge of every method is the zero edge (`HandoffExclusion.zinv_all` for each method, with no seed anywhere), so
  `HandoffExclusion.exclusion_demand` gives each method only the zero demand. The composition over every method and
  over the later rounds is not stated in Lean.
* THE STOP RULE `NO_DEMAND_EDGE` (§7.1). With no demand-layer edge delta, no demand-layer summary delta and no demand
  link, every sink witness and every link of the run is normal, so a remaining DEMAND entry fails only the joint
  support of a premise set with several members (a conjunction). A demand link is counted because a call cleaner can
  demote an `[any-taint]` bound fact to `[any]` on a link (`ap.md` §2.2 THE DEMOTIONS) while every edge of the callee
  stays normal (the emission `[any] ∩ $` gives a `$` premise that starts normal). AN OPEN QUESTION: in a complete
  restricted forward run with no demand-layer object, if no one call supplies every member of the premise set of a
  sink witness, can a later forward run (a narrower demand, a larger field limit, more records) have one call that
  supplies every member of a sink witness of the same key? No counterexample is known: with every link normal, an
  emitted member equals its added fact or lies inside a normal `[any-taint]` link. But the seed paths (case 2 of
  §7.4) are not narrowed, and restricted runs with ND edges are not modelled (`ap.md` §11.2). No Lean statement has
  this. The stop keeps every real vulnerability in the report (§7.7); the argument is only about a later
  confirmation.
* THE ZERO FACT IS NOT LOCALIZED (§0; a later task, `ap-history.md` F70). In every run the zero fact enters every
  callee that it reaches: the backward rule `zin` (§4.5) and the forward zero demand with the zero binding (§4.4).
  Every zero-premise backward edge at a forward entry is a demand edge `(gb, none)` (§7.4): it is never a record and
  it is not narrowed. So the work of the zero fact repeats in every run, whatever the frontier: it is the floor of the
  cost of a run, and the frontier log measures it (`zeroOnly`, `zeroOnlyEdges`, §7.8). The exclusion theorem is about
  the non-zero facts: an excluded method key is still analysed from the zero fact. With only the zero demand it
  publishes nothing in a restricted run, so it gives no demand edge from the zero fact (§7.8).

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
    `start` and `zpass` from the seed node, with `Backward.ZeroKept`), and `Handoff.demOfN` (before F70
    `Backward.demOf`) and `FSeeds.srcHit` read every layer. So the rule only moves normal backward edges out of the
    records: with the hand-off of §7.4 such a leaf becomes a demand edge (THE BACKWARD LAYER IN THE CROSSABLE TEST,
    above; `ap.md` §11.2);
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
* a primitive AP cleaner `part` row of `ap.md` §4.7 other than the `atAndBelow` and `below` rows one accessor below the fact: the
  `exact` cleaner at the path of the fact or one accessor below it, and every cleaner two or more accessors below it.
  There is no shape for "every location but one" (`AnyTaintExCases.CL.exact_result`; the demotion is necessary,
  `AnyTaintExExact.CexExactCleaner.cex_exact_cleaner`: `[any-taint]/{f}` would miss the real `x.f.g`, and a normal
  `[any-taint]/{}` would claim the cleaned `x.f`);
* a may target: the `[any]` target of a pass rule (`ap.md` W6);
* a demand-layer input: a demand fact (also another input of a conjunction), a demand-layer summary edge or record, a
  demand link (an `[any]` added fact);
* the must-record demotion (§4.2 `applyRecord`; `AnyTaintEx.recLayerX`).

This is a precision loss, not a soundness loss: the vulnerability stays in the report as a DEMAND entry.

A named field action uses F74, rather than applying the primitive directly to the old base. For a normal
`(x, p, [any-taint], E, T)` input and a field `f ∉ E`, every reach keeps the normal outside-field fact with
`E ∪ {f}`. `exact` also returns demand `(x, p.f, [any], T)`; `below` also returns normal `(x, p.f, $, T)`;
`atAndBelow` returns only the outside-field fact. A demotion of the temporary does not demote the outside-field
fact. `FieldCleanerX` checks these three local vectors. These checks do not prove the F72 X iteration.

THE ALIAS GAP (an expected false-positive source, `ap.md` §11.1). A WEAK UPDATE keeps an `[any-taint]` object whole: a
deep write through a local (`a = dto.address; a.city = clean`: the alias edge is gen-only, `interpreter.md` G7) or
through a call-result alias such as a getter (`interpreter.md` §3.8 AC2), the constructor pass-over (`interpreter.md`
G8), and the default identity of an unresolved callee (`interpreter.md` §3.7: a library setter `dto.setName(clean)`).
The object keeps `(dto, ., [any-taint], E, T)` in the normal layer, so a sink on the cleaned field is a CONFIRMED
false positive. Before F69 the same finding was a DEMAND entry. A `$` fact has the same gap today.

---

## 12. The formal model

The files of this table model the CONCRETE restricted runs (`ap-history.md` F70, F71). The checked F72 base modules,
their assumptions and the remaining obligations are listed in `ap.md` §10.13 and §11.2. The F72 pipeline instance
is pending (§11). The existing concrete-design theorems keep their scope.

| File | Content |
|---|---|
| `Pipeline.lean` | the rule system with owners, its closure, the state and the steps of the protocol (frozen definitions) |
| `PipelineProofs.lean` | `reach_sound`, `quiescent_complete`, `quiescent_exact`, `no_lost_join`; the counterexamples `PCex.cex_P1` to `cex_P4` and `PCex.step_finds_edge`; the counter model (`Quiesce.creach_inv`, `cnt_zero_iff`, `done_iff`, `done_final`, `bad_early_done`); the dominance theorems (`quiescent_dominates`, `reach_soundD`) |
| `PipelineAP.lean` | the encodings of `D`, `DR`, `DB`, `DS`, `DN`; the `*_wf` theorems; `clD_iff`, `clDR_iff`, `clDB_iff`, `clDS_iff`, `clDN_iff`; the object theorems (`clD_link`, `clD_sub`, `clD_pub` and the other forms) |
| `PipelineStore.lean` | the completeness of the index lookups of §5.3 (`replay_run1`, `deliver_run1`, `replay_restricted`, `deliver_restricted`, `record_lookup`) |
| `PipelineDriver.lean` | `result_D`, `result_DR`, `result_DB` (generic in the rules: also the backward run with `restrictI`), `driver_iteration`, `driver_iteration_upto` (the earlier hand-off, §7.7) |
| `PipelineNDZ.lean` (with `NDZ.lean`, `NDZeroBase.lean`) | `PipelineNDZ.sysDNz_wf`, `clDNz_iff`, `result_DNz`, `clDNz_ndpub_zero_sub`: the encoding of `NDZ.DNz` (§5.4, §5.5) |
| `ForwardSeeds.lean`, `PipelineSeeds.lean` | the source seeds: `FSeeds.keepSources`, `srcHit`, `srcHit_applies`, `B_src`, `iteration_src`; `PipelineSeeds.driver_iteration_src` (`ap.md` §10.9) |
| `PipelineAnyTaintEx.lean` (with `AnyTaintExDefs.lean`) | the encodings of the closures of the tail `[any-taint]` with its exclusion (§5.5): `sysD6X`, `sysDRX`, `XPObj6`, `XPObj`, `sysD6X_wf`, `sysDRX_wf`, `clD6X_iff`, `clDRX_iff`, the object theorems, `known_D6X`, `known_DRX`, `result_D6X`, `result_DRX`, `result_DRXs`, `no_lost_summary_D6X`, `no_lost_summary_DRX`, `SanityX` |
| `PipelineAnyTaintExDriver.lean` (with `AnyTaintExCov.lean`) | the driver with the tail `[any-taint]` and its exclusion, for the earlier hand-off (§7.7): `resultSeqX`, `resultSeqX_runSeqX`, `driver_iterationX`, `driver_iteration_uptoX`, `driver_iteration_srcX` |
| `HandoffDefs.lean` | the hand-off of the demand edges only (`ap-history.md` F70; `ap.md` §10.12), the definitions (namespace `Handoff`): the intersection `restrictI` in the locations and the marks (`ap-history.md` F71: the premise test `insideB`, that is `insideLocB` and `markSubB`; the conclusion mark test `concMarkB`; `meetConcK`, `restrictConcI`), the demanded call `FlowRR.call` with `p.covers l2` (the exit location with its mark), the crossable test `CrossK`, `Cross`, the backward test `CrossB` and the reversed record `revRec` (§1), the publications `Pub`, `pubD`, `pubR` (§4.6), the two hand-offs `handF` (§7.3) and `demOfN` (§7.4), the witnesses `FlowRR`, `ReachRR` (demanded or recorded) and `FlowRDN`, `ReachRDN` (justified), the contracts `CoversN`, `BackwardContractN` (§7.7) |
| `HandoffRestrict.lean`, `HandoffCoverage.lean` | the intersection (namespace `Handoff`): `restrictI_sub`, `restrictI_contract` (a premise inside `D-c` by `insideB`, an exit location that `D-p` covers with its mark), `restrictI_contract_loc_false` (its form in the locations only is false: the user's example), `restrictI_of`, `restrictI_someM`, `restrictI_not_RestrictContract` (the old contract form, a premise that only overlaps `D-c`, is false), `emitM_inside`, `emitM_insideB` (a concrete added fact: the premise lies inside `D-c` with its mark), `insideB_covers`, `insideLoc_coversLoc`, `restrictI_inter` with its exceptions `RExc`, with the marks `restrictI_interM` (the exception of an abstract conclusion mark, `Invariant.AbsMark`) and `restrictI_inter_conc`, `restrictI_narrow`, `restrictI_narrowM`, `restrictI_narrow_conc`, `pubD_sub`, `pubR_sub`; the narrowing of one hand-off `handF_narrow`, `handF_narrow_loc`, `demOfN_narrow`, `handF_narrow_DR`, `handF_narrow_DR_exact`, with the marks `handF_narrowM`, `handF_narrow_locM`, `demOfN_narrowM`, `handF_narrow_DRM`, `handF_narrow_DR_exactM`, and `handF_DR_nonstar`, `DR_exit_not_star`; the vectors `RVec.v64_restrictI`, `v64_restrictU`, `vOverlap_restrictI`, `vOverlap_restrictU`, `vNoExit`, every row `RVec.row_*` of `restrictConcI`, the mark tests `RVec.vMark_user_inside`, `vMark_user_concMark`, `vMark_user_restrictI`, `vMark_user_restrictU`, `vMark_user_loc`, `vMark_user_same`, `vMark_prem_loc`, `vMark_prem_inside`, `vMark_prem_restrictI`, `vMark_inStarEx_T`, `vMark_inStarEx_U`, `vMark_outStarEx_T`, `vMark_outStarEx_U`, `inter_exc_absmark`, and the emission of `*∖X` `RVec.vEmit_starEx_T`, `vEmit_starEx_T_pre70`, `vEmit_starEx_U`; the forward contract `cross_applies`, `coverageRN`, `reach_strongRN`, `coversN_DR`, run 1 `run1_justifies` (§7.7) |
| `HandoffBackward.lean`, `HandoffIter.lean` | the backward contract (namespace `HandoffBackward`): `cross_step`, `seg_genN` (with the local copies of the mark-aware forms `emitM_insideB_B`, `concMarkB_of_den_B`, `restrictI_contract_B`), `reach_of_db_genN`, `demanded_genN`, `B_generalN`, `B_generalN_canon`, `NextRecs`, `recsBOf`, `rcNextOf`, `rcNextOf_back_normal` (a record from the backward run is the reversal of a normal backward leaf), `crossB_em`; the iteration (namespace `HandoffIter`): `Run0Contract`, `iteration_invariantN`, `iteration_abstract_or`, `iteration_abstract`, `iteration_abstract_neg`, `iteration_all_seeded` (§7.7) |
| `HandoffExclusion.lean` | THE EXCLUSION (namespace `HandoffExclusion`, §7.8): `NoZeroGenP`, `Reaches`, `zinv_all`, `exclusion_backward`, `init_zero_nodem`, `exclusion_backward_nodem`, `exclusion_demand`, `forward_zero_init`, `forward_zero_edges`, `exclusion_theorem` (the hypothesis: no demand edge of the method key), `exclusion_round` (the sufficient condition: every summary leaf crossable) |
| `HandoffMain.lean` | the canonical sequence of the spec rules (namespace `HandoffMain`): `canonState`; THE ITERATION `iteration_generalN`, `iteration_generalN_all`, `iteration_generalN_incl` (with `flowRR_mono`, `reachRR_mono`, `flowRDN_mono_rc`, `reachRDN_mono_rc`); the exclusion `exclusion_canon`; the narrowing with both cells of `Handoff.RExc` as exceptions `narrowing_canon_fwd`, `narrowing_canon_back`, `narrowing_canon`, `narrowing_canon_loc`, and its forms with the marks `narrowing_canon_fwdM`, `narrowing_canon_backM`, `narrowing_canonM`, `narrowing_canon_locM` (in the two cells the marks still narrow; the exact form is in `HandoffNoStar.lean`) (§7.7, §7.8) |
| `HandoffCases.lean` | the worked programs (namespace `HandoffCases`, §7.8, §13): `restrictI_none`; WRAP (`Wrap.w1_exit_cross`, `w1_wrap_exits_cross`, `seedsW_exact`, `old_b2_wrap_init`, `old_dem_w`, `old_f3_wrap_init`, `old_f3_wrap_cut`, `handF_w1_exact`, `bn_cross`, `bn_wrap_zero_only`, `bn_wrap_edges_zero`, `demN_exact`, `fn_wrap_zero_only`, `fn_wrap_edges_zero`, `fn_record_applicable`, `fn_cut_in_root`, `fn_found`, `wrap_reachRR`, `wrap_old_vs_new`); the CEGAR of `Cross` (`revRec_any_premise`, `not_cross_of_any`, `dollar_blocked`, `CrossL`, `handFL`, `AnyW.cegar_cross_anyw`, `AnyM.cegar_cross_anym`); the getter (`Getter.g1_exit_demand`, `revRec_g_cross`, `revRec_g_crossB`, `demG_exact`, `fg_getter_zero_only`, `fg_record_sat`, `fg_found`) |
| `HandoffRCases.lean` | programs 1 and 2 of `ap.md` §6.3, §6.4 with the intersection `restrictI` and the hand-off of the demand edges (namespace `HandoffRCases`, §13 item 7): `p1_no_exit`, `p1_found_I`, `p1_handoff`, `p1_chain`; `r1_c_not_cross`, `b2_handF`, `b2_inside`, `b2_insideB`, `b2_concMark`, `b2_restrictI_eq_U`, `b2_not_crossB`, `p2_handoff`, `f3_inside`, `f3_insideB`, `f3_concMark`, `f3_restrictI_eq_U`, `p2_found_I`, `p2_chain` (the mark tests pass, so the results are those before F71) |
| `HandoffUpto.lean` | THE FINITE FORMS (namespace `HandoffUpto`, §7.7): the induction stops at the last run `K`, with the hypotheses only for the runs before `K`: `iteration_generalN_upto`, `iteration_generalN_canon_upto`, `iteration_generalNX_upto`, `iteration_generalNX_canon_upto` |
| `HandoffSrc.lean` | THE SOURCE SEEDS with the hand-off of the demand edges (namespace `HandoffSrc`, §7.4, §7.7): contract B into the seeded program `B_srcN` (the recorded calls read no seed); the iteration `iteration_srcN`, `iteration_srcN_upto`, `iteration_srcN_canon`, with the tail `[any-taint]` `iteration_srcNX`, `iteration_srcNX_upto`; the program `SrcRec` (`SrcRec.found_unseeded`: a record applies a source that the seeds drop; the source seeds do not filter the records) |
| `HandoffXMain.lean` | the exclusion and the narrowing over a round on the spec closures with the tail `[any-taint]` (namespace `HandoffXMain`, §7.8): `forward_zero_initX`, `forward_zero_edgesX`, `exclusion_roundX`, `exclusion_canonX`; `narrowing_canonX_fwd`, `narrowing_canonX_back`, `narrowing_canonX`, `narrowing_canonX_loc` (with the `Dropped` alternative: the hand-off drops the exclusions); with the marks `narrowing_canonX_fwdM`, `narrowing_canonX_backM`, `narrowing_canonXM`; the vectors `XMVec.exit_dropped`, `entry_dropped` |
| `HandoffNoStar.lean` | NO `*` DEMAND PATTERN, AND THE EXACT NARROWING, for the concrete design (F72 has `*` patterns after run 1, so the claims about the sequence and the backward run do not hold for F72; the run-1 results and the general lemmas stay, §7.8, §11) (namespace `HandoffNoStar`, §7.8): run 1 `run1_exit_star_cross`, `handF_run1_nonstar`; the backward run `DB_edge_nonstar`, `demOfN_nonstar`; the sequence `canon_dem_nonstar`, `canon_handF_nonstar`; cell (a) at `*/{}` `rexc_empty_loc`; THE NARROWING `narrowing_canon_fwd_exact`, `narrowing_canon_back_exact`, `narrowing_canon_back_loc`, `narrowing_canon_loc_exact`, and in the locations AND the marks `narrowing_canon_fwd_exactM`, `narrowing_canon_back_exactM`, `narrowing_canon_loc_exactM`; with the tail `[any-taint]` `handF_run1X_nonstar`, `canonX_dem_nonstar`, `narrowing_canonX_fwd_exact`, `narrowing_canonX_loc_exact`; the seeds `nonstar_of_sinkK` |
| `PipelineHandoffDriverExt.lean` | the pipeline forms of the driver of §7.1 (namespace `PipelineHandoffDriverExt`, §7.7): the DEMAND seeds `driver_iterationNX_demand`, `driver_iterationNX_demand_known`; the instance with a weaker `C` (a report in the normal layer) `driver_iterationNX_confirmed`; the finite form `driver_iterationNX_upto`; the source seeds `driver_iteration_srcNX`, `driver_iteration_srcNX_upto` |
| `HandoffXRestrict.lean`, `HandoffXCoverage.lean`, `HandoffXIter.lean`, `PipelineHandoffDriver.lean` | the hand-off of the demand edges on the spec closures with the tail `[any-taint]` (§4.6, §7.7, §7.8): the intersection with the exclusion (namespace `HandoffX`) `restrictIX` (with the mark tests of `restrictI`), `insideLocXB`, `insideXB` (`insideLocXB` and `markSubB`), `restrictIX_ok`, `restrictIX_contract`, `restrictIX_contract_base`, `restrictIX_of`, `emitX_inside`, `emitX_insideXB`, `restrictIX_inter` with `RExcX`, `restrictIX_interM`, `restrictIX_inter_conc`, `restrictIX_narrowM`, `pubRX`, `handF_narrowX`, `handF_narrowX_DRX`, `handF_narrowXM`, `handF_narrowX_DRXM`, the vectors `XVec.v64_demand`, `v64_taint`, `v_taint_star`, `v_at_rows`, `v_above_rows`, `v_below_rows`, `v_overlap`, `v_inside_only_with_excl`, `v_old_above_not_inter`, the mark tests `XVec.vM_user`, `vM_prem`, `vM_inStarEx`, `vM_outStarEx`, `vM_emit`, `XVec.restrictIX_contract_loc_false`; the forward contract `coversN_DRXI` (`RecsEmbed`; the hypotheses `EmitInsideX`, `RestrictInsideX` read the marks) and run 1 `run0X_contract`; the iteration (namespace `HandoffXIter`) `canonStateX`, `embedRecs`, `iteration_generalNX`, `iteration_generalNX_all`, `iteration_reportsNX_canon`, `iteration_generalNX_incl`, `iteration_reportsNX`; the pipeline form `PipelineHandoffDriver.driver_iterationNX` (`resultSeqX_runSeqNX`, `pubSeqXst_pubSeqNX`) |
| `AnyTaintExDefs.lean`, `AnyTaintExCov.lean`, `AnyTaintExExact.lean`, `AnyTaintExKinds.lean`, `AnyTaintExCases.lean`, `AnyTaintExCases2.lean` | the AP model of the tail `[any-taint]` with its exclusion: THE SPEC CLOSURES (`ap.md` §10.11). This document cites: the closures `AnyTaintEx.D6X`, `DRX`, `DRXs`, the objects `XObj`, `XFact`, the operations `w6tX`, `transferX`, `limitFX`, `cleanResX`, `partX`, `annX`, `checkX`, `emitX`, `emitTX`, `satX`, `restrictX`, `startX`, `recLayerX` (with `DRX.retRec`), the predicates `SatInsideX` (`satX_inside`), `EndExactX`, `RecsExactX`, `SupLinkX`, `SupX`, `Confirmed6X`, `ConfirmedX`, the vectors `Vec`; `AnyTaintExCov.forget6`, `forgetX`, `iteration_reportsX`, `iteration_srcX`, `CexRoute.route_a_false`; `AnyTaintExExact.startX_must_end`, `confirmed_real_valid6X`, `confirmed_realX_valid`, `seq_confirmed_realX_valid`, `RecsFromRunsX`, `specX_rules`, `RecsConcX`, `RecsWFX`, `recs_of_DRX`, `CexExactCleaner.cex_exact_cleaner`; `AnyTaintExKinds.D6X_flow_no_any_taint` (run 1, under S7, S10 and S15: an edge whose premise has the mark `*`, a FLOW edge, has no normal `[any-taint]` conclusion), `D6X_any_conc`, `DRX_normal_premise`, `DRX_must_premise` (under `AnyTaintEx.EmitCopiesMarkX`, `AnyTaintEx.emitX_copies`: a normal edge of a restricted run has a `$` premise or a must-premise `[any-taint]` with a concrete mark; before F70 `DRXs_normal_premise`, `DRXs_must_premise`); the worked programs of `AnyTaintExCases` (§13) and of `AnyTaintExCases2` (the round-1 programs G, C, I and PassRule re-derived in `D6X`, and their restricted runs in `DRXs` with the earlier restriction `restrictX` and the earlier hand-off, the record of the earlier design; §7.5, §13) |
| `AnyTaintDefs.lean`, `AnyTaintSim.lean`, `AnyTaintExact.lean`, `AnyTaintND.lean`, `AnyTaintCases.lean`, `PipelineAnyTaint.lean`, `PipelineAnyTaintDriver.lean` | the model of the first F69 form (the demotion at an exclusion, `AnyTaint.D6T`, `DRT`), not the spec closures. This document cites from it only what still states a rule of the spec: the taint edges `AnyTaint.TaintEdges`; the counterexamples `AnyTaintExact.CexApp.cex_app`, `CexApp.record_not_pair_exact`, `CexRev.cex_rev`, `CexSupMark.cex_sup_mark` and the lemma `markSub_conc`; the conjunction `AnyTaintND.DNzT`, `Example`; the transfer with no exclusion `AnyTaintCases.Cut.cut_transfer` (§13 item 31); the vectors `AnyTaint.EmitVec`, `Sanity`. The round-1 programs G, C, I and PassRule of `AnyTaintCases.lean` are only the program terms that `AnyTaintExCases2.lean` imports: their results in the spec closures are those of `AnyTaintExCases2` |

THE TAIL `[any-taint]` AGAINST THE MODEL. The base model has three tail kinds (`.star e`, `.any`, `.exact`). The spec
has four, and the forward `[any-taint]` can carry an exclusion (`ap.md` W8). The spec closures are the refined ones,
`AnyTaintEx.D6X` and `DRX` with `emitX`, `satX` and `HandoffX.restrictIX` (before F70 `DRXs`, with `restrictX`) (an
annotated fact `AnyTaintEx.XFact` is a base fact with its exclusion):

| Spec | Model |
|---|---|
| `*/E` | `.star e` |
| `$` | `.exact` |
| `[any]` (a may) | a `.any` fact in the demand layer, with no exclusion (`AnyTaintEx.normX`) |
| `[any-taint]/E` conclusion (a must) | a `.any` fact in the normal layer with a concrete mark and the exclusion `E` (`AnyTaintEx.XFact`, `carriesB`; in run 1 every normal `.any` conclusion has a concrete mark, `AnyTaintExKinds.D6X_any_conc`) |
| `[any-taint]/E` premise (a must-premise) | a premise with the must flag and the exclusion of `AnyTaintEx.XObj` (`init M j true jex`, `edge M j true jex n f`); it has the tail `.any` and a concrete mark (`AnyTaintExKinds.DRX_must_premise`) |
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
   premise below it through an accessor in `E` gets no summary, and a premise through another accessor gets it. A
   FLOW premise (F72, §5.3): a caller fact below the premise (`applicable`) and a caller fact above it (`inside`) both
   get the summary, by the replay and by the delivery; a summary of a concrete premise does not reach a `*` caller
   fact.
4. SEVERAL PREMISES. A summary `{j1, j2} → g`: premise 1 matched by a delivery, premise 2 by a replay, with the
   conclusion in two deltas: the caller applies both deltas (§5.4).
5. RECORDS. A forward record does not apply in its forward form in a backward run; its reversal applies. A backward
   record applies to a forward fact only through its reversal. A record applies by `inside` in a restricted run
   (§5.3).
6. COUNTER. A handler that sends after a delay: the run does not end before the send (Q2). A new `RunManager` made
   after an aborted one (test harness) analyzes every method (§6.3, §7.6).
7. HAND-OFF. Programs 1 and 2 of `ap.md` §6.3, §6.4: the demand of run 3 equals `Backward.dem1_exact` (program 1) and
   `dem2_exact` (program 2); run 3 reports the vulnerability (`Backward.p1_found`, `p2_found`). These Lean results are
   of the earlier hand-off (`Backward.demOf`, `restrictU`). `dem1_exact` holds for every backward demand and record
   set, and no call of program 1 returns, so it holds for the hand-off of §7.4 too. With the intersection and the
   hand-off of the demand edges both programs are proved (`HandoffRCases`): program 1 (`p1_handoff`, `p1_found_I`,
   `p1_chain`) and program 2 (the summary of `c` is not crossable, `r1_c_not_cross`; the backward summary is in the
   demand layer, `b2_not_crossB`; the mark tests of the restriction pass, `b2_insideB`, `b2_concMark`, `f3_insideB`,
   `f3_concMark`; the intersection gives the pieces of `restrictU`, `b2_restrictI_eq_U`, `f3_restrictI_eq_U`;
   `p2_handoff`, `p2_found_I`, `p2_chain`). The Lean results show that the hand-off CONTAINS
   these patterns; that it EQUALS them (the demand of run 3 is exactly `dem1_exact`, `dem2_exact`) is checked by hand
   (`ap.md` §6.4).
8. MODES. A restricted run (forward and backward) raises no request (F72 R4): on a `*` fact the mark gate of a micro
   edge with a concrete premise mark gives no result, the sink check gives no witness, and a partial cleaner of `T`
   gives the fact `*∖{T}`; the run has no request store, and its request counter is 0. Run 1 raises the requests of
   the same program. A backward run has no sink check. The zero fact enters every
   callee in the backward run. The reversed plan of a JVM call gives the steps of `interpreter.md` §4.9 in its order
   (the table of §4.5), with the reversed source results and the seeds at the rule point `BOUND`. The reversed alias
   edges apply to every requirement; the forward ones only to the results that AC3 and AC4 select.
9. STOP RULES (§7.1). A forward run whose vulnerabilities all have a confirmed sink edge stops the iteration
   (`STOP_RULE`), also when they have demand-layer sink edges too. So does a forward run whose only unconfirmed
   vulnerability an EARLIER run confirmed: it is not a DEMAND vulnerability, it gives no seed, and the driver stops
   with `STOP_RULE`. A forward run with a DEMAND vulnerability and no demand-layer object (a conjunctive sink whose
   literals come from two different call statements, so the joint support fails) stops with `NO_DEMAND_EDGE`; the
   report keeps the DEMAND entry. A demand-layer summary delta alone (a cut of the exit rules) and a demand link alone
   each count as a demand-layer object, so the driver goes on (program DLINK, `analyzer-impl.md` §9.1 row 21):
   `root(): dto = srcAny(); c(dto)`, `c(x): y = x.q.r; m(y)` with the call cleaner `clean(T, arg0.g.k, exact)` at
   `m(y)`, `m(p): sink(p.g.h); throw`, and the field limits 1 to 5: forward run 3 has only normal edges, but the cleaner demotes the bound fact to
   `(p, ., [any], T)` on a DEMAND link, so it does not stop with `NO_DEMAND_EDGE`, and forward run 5 CONFIRMS the
   vulnerability (§7.1). The seeds of the hand-off of a backward run are exactly the witnesses of the DEMAND
   vulnerabilities: a vulnerability that an earlier run confirmed and that the latest run reports in the demand layer
   gives no seed (§7.3).
10. SOURCE SEEDS. In forward run 3, a source that backward run 2 did not reach does not fire; a source on the witness
    outside a recorded call fires, and run 3 reports the vulnerability. A source inside a crossable callee is not hit
    and does not fire, and the record of the callee gives its result (`x = mk(); sink(x)`, `mk(): ret = source()`:
    run 3 reports the vulnerability in the normal layer through the record, `HandoffSrc.SrcRec.found_unseeded`). A
    requirement that reaches a source records exactly one hit for that (method key, statement, source edge) (§4.7). A source at a call, at a method entry, at a
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
    report so far (empty for run 1), and no runner is alive after the return. A stop by the two stop rules and by the
    policy gives `STOP_RULE`, `NO_DEMAND_EDGE` and `POLICY` (§6.3, §7.1). Each complete run, also the last one, logs
    one frontier, and `continueAfter` gets the frontiers of every complete run in run order (§7.8).
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
22. THE `[any]`-TARGET SOURCE IS CONFIRMED (analysis test; program G, a Spring DTO through a getter; the Lean results
    are those of `AnyTaintExCases2`: run 1 in the spec closure `AnyTaintEx.D6X`, run 3 in `AnyTaintEx.DRXs` with the
    earlier restriction `restrictX` and the earlier hand-off, the record of the earlier design). `root(): dto = srcAny(); x = get(dto);
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
    SINCE F72 (PENDING the model; the Lean results above are of the concrete design): the run-1 pattern of `get` is
    `(D-c = (ret, ., [any], *), D-p = (p, ., *, {}, *))`, a `*` pattern, so backward run 2 weakens the requirement
    `(ret, ., [any], T)` to the FLOW premise `(ret, ., *, {}, *)` (§4.4). Its backward summary
    `(ret, ., *, {}, *) → (p, .f, *, {}, *)` is normal and its reversal is crossable, so `get` hands off no demand edge.
    Forward run 3 crosses `get` by the reversed record, which applies to the added fact `(p, ., [any-taint], {}, T)`
    by `inside` with a normal result (the case `above` of an `[any-taint]` fact, `ap.md` §4.3), and the expected
    result is the same: run 3 CONFIRMS the vulnerability. The test asserts the hand-off and the result of run 3.
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

The items 32 to 42 test the hand-off of the demand edges, the stop rules and the frontier (`ap-history.md` F70; §4.3,
§4.5, §7.3 to §7.8), and the marks of the restriction and of the emission (`ap-history.md` F71; §4.4, §4.6). The
items 22 and 23 cite Lean results of the earlier hand-off (`AnyTaintExCases2.G.handoffX_get`,
`AnyTaintExCases.B.run3_must`, with `restrictX`): there the summaries that the hand-off reads are not crossable (a
demand-layer getter, a demand given by hand), and the intersection keeps the same pieces, so the expected values do
not change (argued).

32. WRAP (§7.8; `HandoffCases.Wrap`, the field limits 1, 2, 3). `root(): x.a.b.c = source(); r = wrap(x);
    sink(r.f.a.b.c)`, `wrap(x): z = new Z(); z.f = x; return z`. Run 1: the summary of `wrap` is crossable, and the
    vulnerability is DEMAND. The frontier of run 1 has no demand edge of `wrap`. Backward run 2 has only the zero fact
    in `wrap`: it crosses `wrap` by the reversed record. Forward run 3 analyses `wrap` only from the zero fact (`wrap`
    is in `zeroOnly`, not in `analysed`), applies the record of `wrap` in the root (one record crossing), cuts in the
    root and reports the vulnerability (`Wrap.wrap_old_vs_new`). A test hand-off that reads every summary edge before
    the restriction (the earlier hand-off) makes runs 2 and 3 analyse `wrap` from a non-zero fact, with a demand-layer
    edge in `wrap` in run 3 (`Wrap.old_b2_wrap_init`, `old_f3_wrap_cut`).
33. A CROSSABLE CALLEE IS NEVER ENTERED BY THE BACKWARD RUN. A callee whose run-1 summary leaves are all crossable (the
    `wrap` of item 32, a setter `set(v): this.f = v`, an identity `id(p): return p`) has no non-zero initial fact in
    the backward run (`HandoffCases.Wrap.bn_wrap_zero_only`, `bn_wrap_edges_zero`). The requirement crosses it by the
    reversed record (`bn_cross`, by `applicable`) and still reaches the source in the caller, so the next forward run
    fires that source and reports the vulnerability (`fn_found`).
34. THE GETTER IS CROSSED BY THE REVERSED BACKWARD RECORD (§7.4; `HandoffCases.Getter`). `root(): x.f.a = source();
    r = get(x); sink(r.a)`, `get(x): ret = x.f`. The run-1 summary of `get` is in the demand layer, so it is a demand
    edge (`Getter.g1_exit_demand`). Backward run 2 enters `get` and gives the NORMAL backward summary
    `(ret, .a, $, T) → (arg, .f.a, $, T)`; it is normal and its reversal is crossable, so it is not a demand edge
    (`revRec_g_cross`, `revRec_g_crossB`, `demG_exact`: `get` gets only the zero demand). Forward run 3 analyses `get` only from the zero fact
    (`fg_getter_zero_only`), crosses the call by the reversed record (by `satI`, `fg_record_sat`) and reports the
    vulnerability in the NORMAL layer under the zero premise of the root (`fg_found`), so run 3 confirms it and the
    driver stops (`STOP_RULE`). These Lean results are of the concrete design. SINCE F72 (PENDING the model; §7.4):
    backward run 2 emits the FLOW premise `(ret, ., *, {}, *)` in `get` (the pattern of `get` has the mark `*`), and
    the backward summary is `(ret, ., *, {}, *) → (arg, .f, *, {}, *)`; it is normal and its reversal is crossable, so
    `get` still gets only the zero demand. Forward run 3 crosses the call by the reversed record by `applicable`, and
    the result is the same: the vulnerability in the NORMAL layer, CONFIRMED, `STOP_RULE`.
35. THE CONDITION ON THE REVERSAL IN `Cross` (CEGAR regression tests, `HandoffCases.AnyW`, `AnyM`; AP-level). A callee
    `anyw` whose summary has a NORMAL leaf with an any tail (in the model `(arg, ., *) → (ret, ., [any])`, the
    `[any-taint]` of F69): the hand-off of §7.3 gives the leaf as a demand edge, the backward run enters `anyw`,
    reaches the source and the next forward run reports the vulnerability. A test hand-off with the looser test
    (`HandoffCases.CrossL`: the forward conditions only, `handFL`) drops the leaf; the `$` requirement cannot cross the
    reversed premise `[any]` (`dollar_blocked`), and the next forward run reports nothing: with the source seeds
    (ANYW, `AnyW.cegar_cross_anyw`; the source in the root) and without them (ANYM, `AnyM.cegar_cross_anym`; the
    source in a callee `mk`, whose summary is in the demand layer).
36. THE RESTRICTION VECTORS (`ap.md` §6.4; §4.6). The intersection against the earlier restriction: `[any]` against
    `D-p = $` gives `$` (`Handoff.RVec.v64_restrictI`; `restrictU` keeps `[any]`, `v64_restrictU`); a premise that only
    overlaps `D-c` gives no result (`vOverlap_restrictI`; `restrictU` gives one, `vOverlap_restrictU`); no `D-p` gives
    none (`vNoExit`); every row of the conclusion restriction (`RVec.row_*`). With the exclusion (`HandoffX.XVec`):
    the same example (`v64_demand`, `v64_taint`), `[any-taint]/{4} ∩ */{5} = [any-taint]/{4, 5}` (`v_taint_star`),
    the rows at, above and below `D-p` (`v_at_rows`, `v_above_rows`, `v_below_rows`), a premise that only overlaps
    `D-c` (`v_overlap`), a premise inside `D-c` only with its exclusion (`v_inside_only_with_excl`), and the cell above
    a `*/E2` exit pattern, where `restrictX` was not the intersection (`v_old_above_not_inter`). The mark tests of the
    restriction: item 41.
37. THE FRONTIER (§7.8). The frontier log of item 32 over runs 1 to 5 (the field limits 1 to 5): `wrap` is in
    `analysed` in run 1 and in no later run while no seed is in its call subtree (`HandoffMain.exclusion_canon`; the
    later rounds argued, §11); every demand pattern WITH AN EXIT PATTERN of run 5 lies inside a demand pattern of
    run 3 of the same method key, in the locations and the marks (`HandoffNoStar.narrowing_canon_loc_exactM`; the
    concrete design. WRAP has no `*` pattern after run 1, so the expected values do not change with F72; for F72 the
    theorem is PENDING, §11). The
    demand of the root is the zero demand and the seed-path pattern `((x, .a, [any], T), none)`
    (`HandoffCases.Wrap.demN_exact`): these are
    not part of the theorem (§11 THE SEED PATHS), so the test does not assert the narrowing for them; every complete
    run logs one frontier with every field of §7.8; the
    backward run 2 has at least one reversed crossing, and run 3 at least one record crossing. The condition on the
    seeds is needed: if `wrap` calls a callee with the sink of a DEMAND vulnerability on the argument of `wrap`, the
    seed gives a zero-premise backward edge of `wrap` with a non-zero requirement (§7.4 case 2), and `wrap` is in
    `analysed` again in the next forward run, although its summary leaves are crossable.
38. THE SEEDS OF THE DEMAND VULNERABILITIES (§7.3). Two vulnerabilities: run 1 confirms one and reports the other as
    DEMAND. Backward run 2 seeds only the DEMAND one. Forward run 3 need not report the CONFIRMED one; the report after
    run 3 still holds both: the first as CONFIRMED (final), the second as CONFIRMED or DEMAND by run 3 (§7.5).
39. THE TRIGGER OF AN END FACT (§4.5, §7.3; argued, §11; program END, `analyzer-impl.md` §9.1 row 31).
    `root(): x = source(); r = M(x); sinkAny(r)`, `M(p): y = sinkCall(p); w = wrap(y); return w`, where `sinkCall` is a sink `ContainsMark(arg0, T)` with the end-fact
    action `AssignMark(U, Result)`, `wrap` an unresolved callee with the pass rule `CopyAllMarks(arg0 →
    Result.[AnyField])` (a may) and `sinkAny` a sink `ContainsMarkOnAnyField(arg0, U)`. Run 1 CONFIRMS the sink of
    `sinkCall` (V1) and reports `sinkAny(r)` (V2) as DEMAND; the hand-off seeds only V2. In backward run 2 the
    requirement of V2 reaches the reversed end-fact edge in `M`, and the analyzer fires the sink seed `(p, ., $, T)` of
    V1 at that statement, once; its seed path gives `M` the pattern `((p, ., $, T), none)` and reaches `source()` in
    the root (a source hit). Forward run 3 triggers V1 again, makes the end fact, publishes
    `zero → (ret, ., [any], U)` of `M` through the pattern `(zero, (ret, ., [any], U))`, and reports V2. A test
    analyzer with no trigger seeds does not report V2 in run 3, and the driver ends with `STOP_RULE` without it.
40. THE REVERSAL OF A CONJUNCTION (§4.3; a regression of a false positive that existed before F70; argued, §11;
    program CONJ, `analyzer-impl.md` §9.1 row 32).
    `root(): a = srcT1(); b = srcT2(); r1 = M(a, b); y.f.g = r1; sinkT(y.f.g); r2 = M(a, c); sinkT(r2)`,
    `M(p1, p2): ret = lib(p1, p2); return ret`, where `lib` is a conjunctive source `ContainsMark(arg0, T1) ∧
    ContainsMark(arg1, T2) → Result.$ (T)` and `c` is clean; the field limits 1, 2, 3. Run 1 reports `sinkT(y.f.g)`
    as DEMAND (the cut) and does not report `sinkT(r2)`. In backward run 2 the reversal of the conjunction in `M` gives
    `(ret, ., $, T) → (p1, ., $, T1)` and `(ret, ., $, T) → (p2, ., $, T2)` in the DEMAND layer: no record, not
    crossable, both handed off (§7.4 case 3). Forward run 3 analyses `M` with both members: the first call CONFIRMS
    `sinkT(y.f.g)`, and the second call gives nothing, so `sinkT(r2)` is not reported. A test reversal that keeps the
    normal layer makes both backward summaries records, and run 3 reports `sinkT(r2)` CONFIRMED (the false positive).
41. THE MARK-AWARE RESTRICTION (`ap.md` §6.4; §4.6; `ap-history.md` F71). THE USER'S EXAMPLE, a core test: a
    restricted forward run with a demand store given by hand, a method key with the one demand pattern
    `D-c = (x, ., $, T)`, `D-p = (ret, .f, $, U)`, and the summary delta `(x, ., $, T) → (ret, .f, $, T)` at its exit.
    The premise lies inside `D-c`, but the conclusion mark `T` is not the mark `U` of `D-p`: the analyzer publishes
    nothing for it. The same delta against `D-p = (ret, .f, $, T)` is published; its leaf is crossable (normal, a `$`
    premise and a `$` leaf, mark-reversible; §1), so it is a record and no demand edge with either `D-p`. A
    demand-layer form of the same delta (`m(x){ ret.f.g = x; }` at the field limit 1: the leaf `(ret, .f, [any], T)`,
    which the meet with `D-p = (ret, .f, $, T)` makes `(ret, .f, $, T)` in the demand layer) is published and stored
    as a demand edge (`summaries.demandEdges()`) with `D-p = (ret, .f, $, T)`, and not with `D-p = (ret, .f, $, U)`;
    the frontier counts its demand edge only in the first case. The AP-level data
    (`Handoff.RVec`): the premise test passes (`vMark_user_inside`), the conclusion mark test fails
    (`vMark_user_concMark`), so no result (`vMark_user_restrictI`); the locations alone match, so the test in the
    locations only (before F71) and `restrictU` keep the edge (`vMark_user_loc`, `vMark_user_restrictU`); with the mark
    `T` in `D-p` it is kept (`vMark_user_same`). A premise mark that `D-c` does not admit (`(x, ., $, T)` against
    `D-c = (x, ., $, U)`): inside as locations, not as marks, so no result (`vMark_prem_loc`, `vMark_prem_inside`,
    `vMark_prem_restrictI`). THE `*∖X` CELLS: `D-c = (x, ., $, *∖{T})` gives no result for a premise with the mark `T`
    and keeps a premise with the mark `U` (`vMark_inStarEx_T`, `vMark_inStarEx_U`); `D-p = (ret, .f, $, *∖{T})` gives
    no result for a conclusion with the mark `T` and keeps one with the mark `U` (`vMark_outStarEx_T`,
    `vMark_outStarEx_U`). (Since F72 the `*∖X` pattern cells are dead in a real run: the hand-off normalization R1
    replaces `*∖X` by `*`; the vectors stay as tests of the test function.) An abstract conclusion mark stays whole
    (`inter_exc_absmark`). Before F72 this was AP-level only; since F72 a restricted run has such conclusions, the
    conclusions of a FLOW premise (§3, §4.6). In the X form (with the exclusions): `HandoffX.XVec.vM_user`, `vM_prem`, `vM_inStarEx`,
    `vM_outStarEx`. The
    contract in the locations only is false on the user's example (`Handoff.restrictI_contract_loc_false`,
    `HandoffX.XVec.restrictIX_contract_loc_false`).
42. THE `*∖X` EMISSION (`ap.md` §6.3; §4.4; `ap-history.md` F71). A core test: a backward run with a demand store
    given by hand, a method key with a demand pattern whose entry pattern is `D-c = (ret, ., $, *∖{T})` (between F71
    and F72 a backward entry pattern with the mark `*∖X` came from a run-1 summary conclusion after a cleaner, §7.3;
    since F72 the hand-off replaces `*∖X` by `*`, so no real run has this pattern, and this test only checks the cell
    of the emission), and two requirements at its forward exit, `(ret, ., $, T)` and `(ret, ., $, U)`. Only
    the second gives an initial fact, `(ret, ., $, U)`: a requirement with a mark in `X` cannot come from that summary,
    because the summary does not pass the mark. The AP-level data: the entry pattern `(x, ., $, *∖{T})` and the added
    fact `(x, ., $, T)` give nothing (`Handoff.RVec.vEmit_starEx_T`; before F71 `*∖X` counted as `*`, and the emission
    gave `(x, ., $, T)`, `vEmit_starEx_T_pre70`); the added fact `(x, ., $, U)` gives `(x, ., $, U)`, which lies inside
    the entry pattern with its mark (`vEmit_starEx_U`); in the X form `HandoffX.XVec.vM_emit`.

The items 43 to 47 test the rules of F72 (§3; `ap-history.md` F72). Their Lean model is PENDING (§11): the items
43, 45 and 46 are the CEGAR programs of the plan (`AbsCases.lean`, (i) to (iv)). Until the model is done, each test
records what the iteration gives; a real vulnerability that the F72 iteration misses is a counterexample to R6, and
the coordinator gets the program.

43. SHARING: THE GETTER WITH TWO MARKS (CEGAR (i); §4.4). `root(): a = srcT(); b = srcU(); x = get(a); y = get(b);
    sinkT(x); sinkU(y)`, `get(p): return p.name`, with `srcT`, `srcU` sources with the marks `T`, `U` and `sinkT`,
    `sinkU` sinks of these marks. The run-1 summary of `get` is in the demand layer (the case `above`), so its pattern
    is `(D-c = (ret, ., [any], *), D-p = (p, ., *, {}, *))`, a `*` pattern. Backward run 2 has ONE non-zero initial
    fact in `get`, the FLOW premise `(ret, ., *, {}, *)`, for both requirements (one `initials.add` stores it). A
    restricted run never has more than one initial fact per `*` pattern in `get`: if forward run 3 emits in `get`, it
    emits ONE FLOW premise for both added facts; if the backward FLOW summary is crossable, run 3 crosses `get` by its
    reversed record and has only the zero fact there. Both vulnerabilities are reported. Before F72 the restricted
    runs had one initial fact per mark (NO SHARING).
44. THE HAND-OFF NORMALIZATION AND THE CONCRETE PATTERN (R1, R2; §7.3, §4.4). `m(x): y = x.f; clean(T, y);
    return y`, with a cleaner of `T`. Its run-1 summary has a `*∖{T}` conclusion in the demand layer, so it is a
    demand edge. The `DemandStore` of backward run 2 has the pattern with the mark `*` (not `*∖{T}`), and the stored
    publication keeps `*∖{T}`; the record and the summary still stop the mark `T` at the application. The requirements
    `(ret, ., $, T)` and `(ret, ., $, U)` both get the FLOW premise. THE USER'S CELL: a core test with a demand store
    given by hand, the pattern `D-c = (x, ., $, T)` and the added fact `(x, ., $, *)` (or `(x, ., $, *∖{U})`): no
    initial fact, and no request (§4.4: "The added fact can't satisfy the demand").
45. NO REQUEST AFTER RUN 1 (R4; CEGAR (ii), (iii); §4.6). In both programs the callee `c` reads a field of its
    argument, so its run-1 FLOW summary is in the demand layer, not crossable, and its pattern has the mark `*`.
    (ii) A MARK-CHANGING PASS RULE: `root(): a.h = srcT(); r = c(a); sinkU(r)`, `c(p): y = p.h; q = lib(y);
    return q`, where `lib` is unresolved with a pass rule from `arg0` with the mark `T` to `Result` with the mark `U`.
    In each restricted run the FLOW premise of `c` gives no result at the pass rule and no request (the mark gate);
    the vulnerability is found through the concrete pattern that the request and the answer of run 1 made (the
    concrete-mark summary of `c`). (iii) A PARTIAL CLEANER of `T` under a `*` premise: `root(): a.h.f = srcT();
    a.h.g = srcT(); a.h.k = srcU(); r = c(a); sinkT(r.f); sinkT(r.g); sinkU(r.k)`, `c(p): y = p.h; clean(T, y.f);
    return y`. The FLOW fact continues as `*∖{T}` with no request. Expected: `sinkT(r.f)` is not reported, and
    `sinkT(r.g)` and `sinkU(r.k)` are reported; `sinkT(r.g)` only through the concrete pattern of run 1 (the request
    of the cleaner and its answer).
46. THE SEARCH FOR A COUNTEREXAMPLE TO R6 (CEGAR (iv)). A DIFFERENTIAL TEST on generated programs (the fuzzer of
    `analyzer-impl.md` §9.2) and on the programs of this list: the iteration with the rules of F72 against the
    iteration of the concrete design (the rules of F71, with the same field limits). The F72 report must hold every
    vulnerability of the concrete report, with the same or a better state. The generator aims at a flow that needs a
    concrete mark in a callee that only `*` patterns reach after run 1, for example a concrete demand that the
    backward weakening loses (a requirement `ret.a` with the mark `T` that only a `*` pattern `ret.*` covers, and a
    mark-specific rule below `ret.a`). A missed vulnerability is a counterexample: the test keeps the program.
47. THE BACKWARD WEAKENING (R2 backward; §4.4, §7.4). In the getter of item 34 the DemandStore of forward run 3 has no
    pattern of `get` except the zero demand, the backward initial fact of `get` is `(ret, ., *, {}, *)` (not
    `(ret, .a, $, T)`), and the frontier of backward run 2 has `get` in `analysed` with one initial fact.

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

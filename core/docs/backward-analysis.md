# Backward JVM taint analysis

`JIRBackwardAnalysisManager` (package `org.opentaint.dataflow.jvm.ap.ifds.backward`,
module `opentaint-jvm-dataflow`) is a second `TaintAnalysisManager` for JIR. It
runs the **unchanged** generic IFDS engine over the reversed application graph
(`ApplicationGraph.reversed`). `TaintAnalyzer` selects it with
`-Popentaint.analysis.direction=backward` (section 6). Trace resolution is out
of scope: backward vulnerabilities carry no traces.

## 1. Semantics: demands over the reversed graph

A fact is a *demand*: `x.f·M` held at a program point means "if `x.f` carries
mark `M` here, a sink is reached". Sinks create demands, the flow functions
move demands backwards through statements and calls, and a demand that meets
a source producing its mark is a source finding.

| Engine notion | Forward | Backward |
|---|---|---|
| method entry point | `JMethodEnterInst` | `JMethodExitNormalInst`, `JMethodExitExceptionalInst` (Zero only) |
| successors of `s` | forward successors | forward predecessors |
| summary emission point | method exits | `JMethodEnterInst` |
| edge at `s` | state before `s` | state after `s` |
| flow function at `s` | pre-state → post-state | post-state → pre-state |

* Valid summary facts are based on `Argument`, `This` or `ClassStatic`.
* Components that need the forward graph (`JIRLocalAliasAnalysis`,
  `JIRLocalVariableReachability`) get it from `graph.reversed`; alias analysis
  is seeded with the forward entry. `isReachable` is always `true`.
* Exceptional exit: only Zero enters there, so sink seeds on throwing paths
  exist and their zero-to-fact summaries are applied by callers, but no caller
  demand ever enters a callee through an exception (forward never propagates a
  fact to the caller along an exception either). No demand has the
  `Exception` base.

## 2. Components

| Hook | Class |
|---|---|
| manager | `JIRBackwardAnalysisManager` (created by `JIRAnalysisManager.createBackwardAnalysisManager`) |
| context | `JIRBackwardMethodAnalysisContext` (subclass of `JIRMethodAnalysisContext`, typed by `JIRAnalysisManagerBase`) |
| call fact mapper | `JIRBackwardMethodCallFactMapper` (delegates to the forward mapper) |
| start / sequent / call FF | `JIRBackwardMethodStartFlowFunction` / `...SequentFlowFunction` / `...CallFlowFunction` |
| summary handler | `JIRBackwardMethodCallSummaryHandler` |
| preconditions, side effects | trivial objects (`JIRBackwardPreconditions.kt`, `JIRBackwardMethodSideEffectHandler`) |
| rule inversion | `JIRBackwardTaintRules` (sink → demand seeds, demand → source match) |
| findings | `JIRBackwardFindingTracker` |
| end requirements | `JIRBackwardEndRequirement` |
| star unrolling | `JIRBackwardStarUnroller` |

Call-site mapping: a demand on the call's result variable maps to `Return`
only (for `x = f(x)` the post-call `x` is the result); every other base maps
like forward. Exit → return maps `Argument`/`This` back to the call locals and
answers nothing for `Return`.

## 3. Statement semantics

For `L = R` forward moves facts `R → L` and backward moves demands `L → R`;
both kill `L`.

| Statement | Demand after | Demands before |
|---|---|---|
| `x = y`, cast | `x.P` | `y.P` |
| `x = y.f` / `x = C.f` / `x = a[i]` | `x.P` | `y.f.P` / `ClassStatic.<C>.f.P` / `a.[e].P` |
| `x = a op b` | `x.P` | `a.P`, `b.P` |
| `x = const / new / ...` | `x.P` | none |
| `y.f = x`, `C.f = x` (strong) | `y.f.P` | `x.P`, plus `y` with `f` cleared |
| `a[i] = x` (weak) | `a.[e].P` | `x.P` and `a.[e].P` |
| `return x` / `throw x` | `Return.P` / `Exception.P` | `x.P` |

Type filters, the abstraction split (`removeAbstraction` plus an excluded
`abstractOnly` when a field is read from an abstract demand) and refinements
follow forward exactly. Field and array writes also move demands through the
`findAlias` aliases of the written instance (weak update). Rule hooks:

* `return x`: exit-sink seeds; exit-source matches before `Return` is rebased.
* `x = C.f`: static-field source matches.
* `JMethodEnterInst`: entry-sink seeds and entry-source matches on
  `Argument`/`This`/`ClassStatic` demands. An entry-source finding is
  suppressed when every initial fact of the edge is an `Argument`/`This` root
  carrying an entry mark: forward drops exactly those marks at the exit
  (`dropArgumentsLocalTaintMarks`).
* Zero-edge-only exit sinks: forward checks a method-exit sink only on facts
  of zero-to-fact edges (`JIRMethodExitRuleProvider`). When a restricted run
  (section 7) seeds only such sinks of the exited method, `JMethodEnterInst`
  does not propagate zero-to-fact demands to the callers.

A source match never kills the demand. Condition demands of a conditional
source are emitted next to it; refinements are propagated as in forward.

## 4. Call semantics

* Zero: demand seeds for every sink rule whose condition is not
  constant-false, from the positive mark literals of the condition
  (`position·M·$`; an any-field literal also demands `position.[any]·M`).
* Source match: `JIRMethodCallPrecondition.evaluateSourceRules` over the
  demand rebased to the callee base. Conditional sources turn into condition
  demands.
* Cleaners: a value in the demand after the call survived the cleaner, so the
  demand before the call is `clean(demand)`. The forward cleaner code
  (`JIRMethodCallCleaner`) runs on the demand itself; removed alternatives
  become `Drop`.
* Resolution failure: the caller demand is kept (except for `Return`), and
  pass-through rules are inverted: `JIRMethodCallPrecondition.evaluatePassRules`
  with a `TaintPassActionPreconditionEvaluator<FinalFactAp>` turns a demand on
  the rule's `to` into a demand on its `from`, filtered by the call's cleaners.
  The backward call FF implements the three `propagate*ResolutionFailure`
  hooks itself because it needs the start fact base.
* User-rule summary rewriting (`JIRMethodCallRuleBasedSummaryRewriter`): the
  forward rewriter is applied to the demands of the inverse pass and the kept
  unresolved demand; for summaries, `rewriteSummaryInitialFact` drops a
  fact-to-fact summary whose initial fact holds a mark removed by a user rule
  of the callee, or refines it when an abstract node is read.
* Call-site aliases: forward copies facts created by a call to the aliases of
  the call locals that persist through the call; backward inverts this by
  reading the demand through each such alias and processing the result like
  the original demand.
* Summaries: the handler emits a side-effect requirement whenever applying a
  summary refines the caller's initial fact, and does not apply call aliases
  (already inverted in the call FF).

## 5. Code shared with forward

| Concern | Shared code |
|---|---|
| assignments, `return`, `throw` | `JIRAssignTransfer` (`Direction.FORWARD` / `BACKWARD`): operand decomposition, type filters, `assignBase`, abstraction-splitting `readField` and `clearField`, accessor chains of memory accesses |
| edge-kind plumbing (Z2F, F2F, NDF2F refinement) | `JIRSequentEdge` |
| cleaners at a call | `JIRMethodCallCleaner` (backward adds only the `CleanerInputs` hook for star unrolling) |
| source match at a call | `JIRMethodCallPrecondition.evaluateSourceRules`, `TaintConfigUtils.evaluateSourceRule` |
| pass-through inversion | `JIRMethodCallPrecondition.evaluatePassRules` → `evaluatePassRulePrecondition` → `TaintPassActionPreconditionEvaluator<F>` (`InitialPreconditionFactBuilder` for trace resolution, `FinalPreconditionFactBuilder` with position type filters for backward) |
| user-rule rewriting | `JIRMethodCallRuleBasedSummaryRewriter` (`rewriteSummaryFact`, `rewriteSummaryInitialFact`), `JIRTaintCleanActionEvaluator.removeMarkPositions` |
| rule applicability, call-site aliases | `TaintConfigUtils.isApplicable`, `aliasesPersistedThroughCall` |

Direction-specific composition stays separate: forward keeps its array
re-emit hack, write aliasing and auxiliary bases; backward keeps the strong
two-level static write, weak array writes and findAlias-based write aliases.
The call → start mapping also differs from trace resolution (backward maps the
result variable to `Return` only), as do sink seeds versus `preconditionDnf`.

## 6. TaintAnalyzer pipeline

* Switch: `TaintAnalyzerOptions.analysisDirection`, defaulting to the system
  property `opentaint.analysis.direction` or the environment variable
  `OPENTAINT_ANALYSIS_DIRECTION` (else `FORWARD`). `configureDefaultTest`
  forwards the Gradle property to test JVMs. A manager that is not
  `BackwardCapableTaintAnalysisManager` (Go) falls back to forward.
* Generic API (`BackwardTaintAnalysisManager.kt`): `prepareRun(BackwardRun)`
  before a run, `runResult()` after it; `BackwardRun` is `Discovery` or
  `Restricted(occurrences)`, an occurrence is `(sink rule, statement)`.

`TaintAnalyzer.analyzeBackward`:

1. Forward prescan on the forward graph with the forward manager, exactly as
   in forward mode. It fills the `relevantRuleIds` set and the
   `JIRLambdaRegistry`, both shared with the backward manager. The backward
   manager never runs a prescan of its own.
2. A separate engine over the reversed graph. Every backward run is
   `selectPhase(FullScan)` (rule selection from the shared ids) →
   `prepareRun` → `resetApManager` → `runAnalysis(entry methods)`.
3. Discovery, grouped and isolated runs (section 7) within 90% of the
   timeout. When no time is left, unchecked occurrences keep their last
   verdict.
4. One `TaintVulnerability` per reported occurrence, merged by
   `(rule id, statement)`; the CWE filter and the vulnerability summary are
   applied as in forward.

Lambdas: forward resolves lambda calls from type-info facts created in the
prescan. The forward resolver records every resolved lambda in the
`JIRLambdaRegistry` (call site → lambda classes); the backward resolver
(`replayRegisteredLambdas`) resolves a lambda call to the registered classes
and additionally keeps the resolution failure, as forward does.

## 7. Sink attribution by isolation

Demands carry marks only, so a source finding does not say which sink
demanded it. Attribution restricts the seeds instead:

* A run records every seeded occurrence with its positive condition and end
  requirement. Satisfied marks are the marks of all source findings, closed
  under conditional sources whose condition holds. An occurrence is
  vulnerable when its condition holds under the satisfied marks and, in
  restricted runs, its end requirement was reached.
* Discovery seeds every occurrence. Its verdict is final only for a single
  seeded occurrence without end requirement that is not a zero-edge-only exit
  sink: demands of different sinks merge in one access path, so discovery is
  not an over-approximation of isolated runs.
* Grouped runs seed groups of occurrences with pairwise disjoint demanded
  marks (deterministic greedy grouping). A single-member group is final; the
  positives of larger groups are re-checked in isolated runs.

Satisfied marks are global to a run, so two literals on the same mark at
different positions are satisfied by either.

## 8. End-fact requirements

Forward confirms a sink with `trackFactsReachAnalysisEnd` only if the fact it
creates after the sink reaches the analysis end uncleaned.
`JIRBackwardEndRequirement` computes that fact like forward (single required
fact only). Restricted runs emulate the confirmation with end demands emitted
by the start flow function at the normal exit: the fact rebased to every local
of every analysed method, plus arguments, `this`, `Return` and `ClassStatic`
at the analysis entry methods. The demands flow backward and cleaners drop
them; at the occurrence's statement a demand containing the required position
and mark marks the requirement as reached.

## 9. Star unrolling before `Exact` cleaners

An any-field sink demands the star `x.[any]·M`. The residual of an `Exact`
cleaner `RemoveMark(x, M)` ("`M` below a path of length at least one") is not
representable, and `Cleaner.kt` removes the whole star. Before the cleaners of
a call run on such a demand, the call FF (`cleanerInputs`) replaces it by the
equivalent union of the demand without its root `[any]`, the star content at
length zero, and `a · demand.readAccessor(a)` for every accessor `a` of the
cleaned value's static type (`JIRBackwardStarUnroller`: the element accessor
for arrays; instance fields of the class, its superclasses and subclasses).
Interfaces and `Object` are not unrolled. Unrolling is skipped when the
cleaner's method has an any-field entry source for a cleaned mark, because
forward drops that concrete star whole.

## 10. Automata any-field exclusion depth

An any-field cleaner on an abstract Automata fact records the cleaned mark as
a deep exclusion of the abstract tail, enforced when a summary delta is
concatenated. `AccessGraphFinalFactAp` recorded it "from depth 1" even when
the abstraction point lies below the cleaned position, so the mark survived.
Mirroring `AccessTree`, `clearAllAccessorOccurrences` records it from depth 1
only when the start accessor is kept and the initial node is final, and
`concat` collapses the prefix exclusion to depth 0 when the delta's initial
node is not final. The code is shared with forward.

## 11. Known limitations

* No traces, preconditions or SARIF code flows; SARIF tests skip in backward
  mode.
* Side-effect summaries are not modelled; end requirements are only emulated
  in restricted runs, and not at exceptional exits.
* Code from which no exit is reachable is not analysed.
* Lambda calls outside `TaintAnalyzer` (no registry) resolve through failure;
  the registry merges all contexts of a method.
* Star unrolling covers only accessors of the static type, not rule-only
  fields (`<rule-storage>`, `Map#MapValue`).
* Mark literals of pass-through conditions are treated as satisfied; a
  cleaner condition naming a mark at another position than the demand does
  not fire.
* Cleaners of a call do not filter demands that a callee summary produces on
  its arguments (user-rule cleaners are covered by the summary rewriting).
* Forward fires method-entry sinks only for constant-true conditions and never
  reports constant-true exit sinks; backward seeds both.
* Base-only modes are field-insensitive in both directions; Cactus is
  unmaintained.

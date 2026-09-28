# Backward JVM taint analysis

`JIRBackwardAnalysisManager` (package `org.opentaint.dataflow.jvm.ap.ifds.backward`,
module `opentaint-jvm-dataflow`) wraps the forward `JIRAnalysisManager`.
It runs the **unchanged** generic IFDS engine once over the reversed application
graph (`ApplicationGraph.reversed`) with rules whose sources and sinks are
swapped per statement (section 7), so a finding is an ordinary sink report at the statement of
an unconditional source. `TaintAnalyzer` selects it with
`-Popentaint.analysis.direction=backward` (section 6). Trace resolution is out
of scope: backward vulnerabilities carry no traces.

## 1. Semantics: demands over the reversed graph

A fact is a *demand*: `x.f·M` held at a program point means "if `x.f` carries
mark `M` here, a sink is reached". Sinks create demands, the flow functions
move demands backwards through statements and calls, and a demand that meets
a source producing its mark is a source finding.

| Engine notion | Forward | Backward |
|---|---|---|
| method entry point | `JMethodEnterInst` | `JMethodExitNormalInst`; `JMethodExitExceptionalInst` (Zero only) |
| successors of `s` | forward successors | forward predecessors |
| summary emission point | method exits | `JMethodEnterInst` |
| edge at `s` | state before `s` | state after `s` |
| flow function at `s` | pre-state → post-state | post-state → pre-state |

* Valid summary facts are based on `Argument`, `This` or `ClassStatic`.
* The backward context of a method is its forward context (forward graph,
  forward entry, so `JIRLocalAliasAnalysis` and `JIRLocalVariableReachability`
  are the forward ones) re-keyed to the backward entry point.
  `isReachable` is always `true`.
* Exceptional exit: only Zero enters there, so sink seeds on throwing paths
  exist and their zero-to-fact summaries are applied by callers, but no caller
  demand ever enters a callee through an exception (forward never propagates a
  fact to the caller along an exception either). No demand has the
  `Exception` base.
* Code that reaches no exit (an infinite loop after a sink) has no forward
  path to an exit, so it would never be backward-reachable from the exits.
  `JIRBackwardExitWiringGraph` wraps the forward application graph: on every
  `methodGraph` request (no caching) it marks, in a `BitSet` over instruction
  indices, the statements from which an exit is reachable (walking
  predecessors from the exit points) and gives every other statement an
  extra forward edge to `JMethodExitExceptionalInst`. The backward manager
  builds its method inst graph from `JIRBackwardExitWiringGraph(forward).reversed`,
  so that code is backward-reachable from the exceptional exit. That start is
  zero-only, so sinks in the code are seeded while caller demands, which
  enter at the normal exit, do not flow into code that never returns.

## 2. Components

Backward reuses forward code through wrappers: every backward component
implements the engine interface itself and holds forward instances, delegating
with Kotlin interface delegation where the behaviour is the same and calling
forward members explicitly where roles are swapped. No forward class is open
and no backward class extends a forward class.

`JIRBackwardAnalysisManager(forward)` is created by
`JIRAnalysisManager.createBackwardAnalysisManager`. It implements
`TaintAnalysisManager` by delegation to its own `JIRAnalysisManager`
(`delegate`), built from the forward manager's classpath, reference manager,
rules, external method tracker, parameters and `relevantRuleIds` set. The
delegate supplies the phase, the call resolver (applied to `graph.reversed`),
language manager, context serializer, fact type checker and edge
post-processor; the backward manager overrides only:

| Hook | Backward |
|---|---|
| context | a `JIRMethodAnalysisContext` (see section 1) built from the delegate's forward context of the method, with the backward entry point, a `JIRBackwardTaintAnalysisContext` and `JIRBackwardMethodCallFactMapper` |
| entry points | entry points of the reversed method graph |
| method inst graph | built from `JIRBackwardExitWiringGraph(graph.reversed).reversed` (section 1) |
| start / sequent / call FF | `JIRBackwardMethodStartFlowFunction` / `...SequentFlowFunction` / `...CallFlowFunction` |
| summary handler | `JIRBackwardMethodCallSummaryHandler` |
| preconditions, side effects | trivial (`JIRBackwardPreconditions.kt`, empty handler) |

The method context is a real forward class instance rather than a wrapper
because the engine, `JIRCallResolver` and every forward helper downcast to
`JIRMethodAnalysisContext`. Its variation points are constructor parameters:
`taint` has the type of the extracted interface `JIRTaintRuleContext`
(implemented by `JIRTaintAnalysisContext`) and `methodCallFactMapper`
defaults to `JIRMethodCallFactMapper`.

| Backward component | Implements | Holds and delegates to |
|---|---|---|
| `JIRBackwardTaintAnalysisContext` | `JIRTaintRuleContext` by a forward `JIRTaintAnalysisContext` | the forward rule queries, swapped per statement (section 7); `bindAnalysisContext` binds both |
| `JIRBackwardMethodSequentFlowFunction` | `MethodSequentFlowFunction`, `JIRSequentTransfer` | a forward `JIRMethodSequentFlowFunction` created with `transfer = this`: its Z2F/F2F/NDF2F plumbing and operand decomposition call back the backward `propagate` and assignment primitives, which call the forward primitives explicitly (section 5) |
| `JIRBackwardMethodCallFlowFunction` | `MethodCallFlowFunction.Default` | a forward `JIRMethodCallFlowFunction`: `propagateZeroToZero`, `applyTaintRules`, `applyCleanersOrCallToStart` with the backward clean-action evaluator |
| `JIRBackwardMethodCallSummaryHandler` | `MethodCallSummaryHandler` by a forward `JIRMethodCallSummaryHandler(withCallAliases = false)` | everything except summary rewriting (`prepare*Summary` return the edge) |
| `JIRBackwardMethodStartFlowFunction` | `MethodStartFlowFunction` | the forward start FF for type checks |
| `JIRBackwardTaintCleanActionEvaluator` | supplies `removeFinalFact` to a forward `JIRTaintCleanActionEvaluator` | the core `TaintCleanActionEvaluator` (section 8) |
| `JIRBackwardMethodCallFactMapper` | `MethodCallFactMapper` by `JIRMethodCallFactMapper` | the forward mapper |
| `JIRBackwardExitWiringGraph` | `ApplicationGraph` by the forward graph | the forward method graphs (section 1) |

Call-site mapping: a demand on the call's result variable maps to `Return`
only (for `x = f(x)` the post-call `x` is the result); every other base maps
like forward. Exit → return maps `Argument`/`This` back to the call locals and
answers nothing for `Return`. The mapping is the context's `methodCallFactMapper`,
which `JIRMethodCallTaintUtil` also uses for rule conditions, so the same rule
code reads a pre-call fact in forward and a post-call demand in backward.

## 3. Statement semantics

For `L = R` forward moves facts `R → L` and backward moves demands `L → R`;
both kill `L`.

| Statement | Demand after | Demands before |
|---|---|---|
| `x = y`, cast | `x.P` | `y.P` |
| `x = y.f` / `x = C.f` / `x = a[i]` | `x.P` | `y.f.P` / `ClassStatic.<C>.f.P` / `a.[e].P` |
| `x = a op b` | `x.P` | `a.P`, `b.P` |
| `x = const / new / ...` | `x.P` | none |
| `y.f = x`, `C.f = x` (strong) | `y.f.P` / `ClassStatic.<C>.f.P` | `x.P`, plus `y` / `ClassStatic.<C>` with `f` cleared |
| `a[i] = x` (weak, as forward) | `a.[e].P` | `x.P` and the demand itself |
| `return x` / `throw x` | `Return.P` / `Exception.P` | `x.P` |

Type filters, the abstraction split (`removeAbstraction` plus an excluded
`abstractOnly` when a field is read from an abstract demand) and refinements
are the forward code itself (section 5). Field and array writes also move
demands through the `findAlias` aliases of the written instance. Rule hooks (all rules are the swapped ones of section 7; the forward rule
code applies them):

* `return x`: on Zero, the forward exit-source step (`applyMethodExitSourceRules`)
  seeds demands at `Return`/`Argument`/`This`/`ClassStatic` and unconditional
  exit sinks report (also at `throw x`); on a demand, the
  forward exit-sink step (`applyMethodExitSinkRules`) reports and the
  exit-source step adds condition demands. All resulting facts are post-return
  positions and go through the backward `Return := x` step.
* `x = C.f`: the context's static-field sinks (`sinkRulesForStaticField`) report and
  its static-field sources (`sourceRulesForStaticField`) add condition
  demands, both applied to a demand on `x` by `JIRSequentTaintUtil` with `x`
  as the result base.
* `JMethodEnterInst`: backward entry sinks report and backward entry sources
  (`sourceRulesForMethodEntry`) seed demands on Zero and add condition demands
  on a demand, all through `JIRSequentTaintUtil`. On a demand they are skipped
  when every initial fact of the edge is an `Argument`/`This` root carrying an
  entry mark: forward drops exactly those marks at the exit
  (`dropArgumentsLocalTaintMarks`).

A report never kills the demand; refinements are propagated as in forward.

## 4. Call semantics

* Rules: the forward `propagateZeroToZero` runs unchanged (unconditional
  derived sources seed pre-call demands on arguments and their call-site
  aliases; residual unconditional sinks report). On a demand and on each
  call-site alias demand, the forward `applyTaintRules` (the sink and source
  step of `propagateFact`) reports derived sinks and emits the condition
  demands of swapped conditional sources.
* Cleaners: a value in the demand after the call survived the cleaner, so the
  demand before the call is `clean(demand)`, computed by the forward cleaner
  step, except that an `Exact` cleaner keeps the `[any]` part of the demand;
  removed alternatives become `Drop`. Only unconditional cleaners are applied
  (section 8).
* Resolution failure: the caller demand is kept (except for `Return`), and
  pass-through rules are inverted by the forward `TaintPassActionEvaluator`
  with `from` and `to` swapped (a demand on the rule's `to` becomes a demand on
  its `from`), filtered by the call's cleaners.
* User rules: the forward `rewriteSummaryFact` is applied to the kept
  unresolved demand, to the inverse-pass demands and to the demand passed to
  the callee start (the inverse of forward rewriting the summary results).
* Call-site aliases: forward copies facts created by a call to the aliases of
  the call locals that persist through the call; backward inverts this by
  reading the demand through each such alias and processing the result like
  the original demand.
* Summaries: the forward handler without call aliases and summary rewriting.

## 5. Code shared with forward

Shared code stays in the forward classes. Members that backward calls are
`internal`, and the points where backward differs are constructor parameters or
function arguments whose default is the forward behaviour.

| Forward class | Change | Backward use |
|---|---|---|
| `JIRMethodSequentFlowFunction` | implements the internal `JIRSequentTransfer` (`propagate`, `simpleAssign`, `fieldRead`, `fieldWrite`); constructor parameter `transfer` (default: itself) receives the plumbing's `propagate` calls and the operand decomposition's primitive calls; `applyMethodExitSinkRules`, `applyMethodExitSourceRules` and `FactRefiner` are internal; the class is internal | `JIRBackwardMethodSequentFlowFunction` reuses the Z2F/F2F/NDF2F plumbing, operand decomposition and type filters and implements the three assignment primitives with roles swapped: `simpleAssign` moves `L → R` and kills `L`; `x = y.f` is the forward write move of the demand into `y.f` (from an auxiliary base, including forward write aliasing); `y.f = x` is the forward write with no value (strong clear, weak arrays) plus the forward read of `y.f` into `x` (including the abstraction split). The forward static write clears nothing (it tests `f` against a fact that starts with `<C>`; forward drops such findings in trace resolution), so `C.f = x` clears `<C>` from `ClassStatic` and `f` from the `<C>` subtree with two forward `RefAccess` writes and puts the rest back under `<C>` |
| `JIRMethodCallFlowFunction` | `applyTaintRules` extracted from `propagateFact`; `applyTaintRules` and `applyCleanersOrCallToStart` are internal, the latter takes the clean-action evaluator as an argument (default: `JIRTaintCleanActionEvaluator(typeResolver)`) | `JIRBackwardMethodCallFlowFunction` delegates `propagateZeroToZero` (seeds, unconditional sinks), applies `applyTaintRules` to every demand and runs the forward cleaner step with the backward evaluator |
| `JIRTaintCleanActionEvaluator` | constructor parameter `removeFinalFact` (default: `TaintCleanActionEvaluator.removeFinalFact`) | `JIRBackwardTaintCleanActionEvaluator` keeps the `[any]` subtree at the position of an `Exact` `RemoveMark` (section 8) |
| `JIRMethodCallSummaryHandler` | constructor parameter `withCallAliases` (default `true`); exit facts are mapped with the context's `methodCallFactMapper` | `JIRBackwardMethodCallSummaryHandler` delegates to it (backward exit mapping, no aliases) |
| `JIRTaintAnalysisContext` | implements the extracted interface `JIRTaintRuleContext` (its rule queries, `bindAnalysisContext`, `reset`, `externalMethodTracker`) | wrapped by `JIRBackwardTaintAnalysisContext` |
| `JIRMethodAnalysisContext` | `taint: JIRTaintRuleContext`; constructor parameter `methodCallFactMapper` | built by the backward manager (section 2) |
| `JIRAnalysisManager` | constructor parameter `relevantRuleIds`; `contexts` and `rootRefManager` are internal | delegate of the backward manager; the forward contexts' lambda trackers (section 6) |
| `JIRMethodCallTaintUtil`, `JIRSequentTaintUtil` (generic over source and sink types) | the call util maps rule conditions with the context's `methodCallFactMapper` | every report and every rule-created demand |
| `JIRMethodStartFlowFunction` | none | held by `JIRBackwardMethodStartFlowFunction` for type checks |
| `TaintPassActionEvaluator`, `TaintConfigUtils.accept` | none | inverse pass-through (swapped positions) |
| `JIRMethodCallRuleBasedSummaryRewriter.rewriteSummaryFact` | none | user-rule rewriting of demands |
| `aliasesPersistedThroughCall` | extracted from `forEachAliasAfterCallStatement` | call-site alias inversion |

`JIRTaintRuleContext` is extracted because the forward flow functions and
utilities read rules through `JIRMethodAnalysisContext.taint`, and each swapped
query is computed from several forward queries of the same statement; the
forward class only gains `override` modifiers.

## 6. TaintAnalyzer pipeline

* Switch: `TaintAnalyzerOptions.analysisDirection`, defaulting to the system
  property `opentaint.analysis.direction` or the environment variable
  `OPENTAINT_ANALYSIS_DIRECTION` (else `FORWARD`). `configureDefaultTest`
  forwards the Gradle property to test JVMs.
* Generic API (`BackwardTaintAnalysisManager.kt`): one interface, implemented
  by `JIRAnalysisManager`, with `createBackwardAnalysisManager()`.
  A manager that does not implement it (Go) runs forward.

`TaintAnalyzer.analyzeBackward`:

1. Forward prescan on the forward graph with the forward manager, exactly as
   in forward mode. It fills the `relevantRuleIds` set and the forward
   contexts' lambda trackers, both read by the backward manager.
2. One run of a separate engine over the reversed graph: `selectPhase(FullScan)`
   → `resetApManager` → `runAnalysis(entry methods)` with 90% of the timeout.
3. The engine's vulnerabilities, then the forward `reportedVulnerabilities`
   step (summary, CWE filter).

Lambdas: forward resolves lambda calls from type-info facts created in the
prescan and keeps them in the context's `lambdaCallResolution` trackers. A
backward context copies the trackers of all forward contexts of its method, so
the unchanged resolver resolves a lambda call to those classes and also keeps
the resolution failure, as forward does.

## 7. Backward taint context

`JIRBackwardTaintAnalysisContext` implements `JIRTaintRuleContext` by delegation
to a forward `JIRTaintAnalysisContext` bound to the same method context and
overrides the rule queries: each one asks the forward context for the
forward rules at the same statement, prepared as in forward (non-mark atoms
evaluated at that statement by `JIRMarkAwareConditionRewriter`), and swaps
them by the prepared condition. The forward rule code consumes the result
unchanged. The static-field sources, which forward prepares only when
unconditional, are prepared with the same rewriter.

A prepared condition is `False` (the rule is dropped by the preparation),
`True`, or an expression over mark literals. Negated literals are ignored: an
expression is *conditional* when it has a positive literal, and then its
*marks* are all its positive literals regardless of the `And`/`Or` structure;
otherwise the rule is *unconditional*. A mark `ContainsMarkOnAnyField(P, M)` is
assigned both at `P` and at `P.[any]`.

| Forward rule | Unconditional | Conditional |
|---|---|---|
| source (call, exit, entry point, static field), `AssignMark(M, P)` | sink of the matching kind (static fields: `sinkRulesForStaticField`, a method sink) with condition `ContainsMark(P, M)` (a disjunction over the actions; `P.[any]` becomes `ContainsMarkOnAnyField(P, M)`) | source of the same kind with the same condition, assigning the marks |
| sink (call, exit, method entry) | the sink, without `trackFactsReachAnalysisEnd` (reported on Zero) | source (call, exit, entry point) with condition `True`, assigning the marks; it fires on Zero (seeds) |
| cleaner | applied | ignored (section 8) |
| pass-through | unchanged (inverted by the flow functions) | unchanged |

`trackFactsReachAnalysisEnd` is ignored. Marks on `Result` are not assigned for
call, entry and static-field rules (a rule with no other mark derives
nothing): forward reads such a condition before the statement, where the
result holds no fact. Forward exit sinks are queried as on a zero-to-fact edge.
The summary rewriter's all-relevant sources are the forward ones; its
all-relevant cleaners drop those that are conditional at the call.

Positions: a call statement's backward edge is its post-state, so derived sinks
of call sources read the post-call demand (result as `Return`, arguments as
`Argument`), while call-sink seeds are pre-call demands (the call FF's
call-to-return output). Exit rules act on post-return positions and the
resulting facts cross `Return := x`; entry rules act at `JMethodEnterInst`.

Reported id and meta of a derived sink: `TaintRulesProvider.sinkMetaForSource`.
`JIRSemgrepRuleProvider` finds the semgrep rule (automaton) containing the
source's serialized item and takes the id and meta of any of its sinks;
`JIRCombinedTaintRulesProvider` asks its base, then the combined provider.
Without an answer (hand-written configs) the id is the source's serialized id,
else its mark names, with an empty warning meta and no CWE, which the CWE
filter keeps.

## 8. Cleaners

A cleaner condition with a mark literal reads the forward fact before the
call, which a demand does not determine, so backward ignores cleaners that
are conditional at the call (section 7) and applies the unconditional ones.
Demands pass the ignored cleaners unchanged.

`MethodTaintConfigurationResolver` (shared with forward) rewrites cleaner
conditions against their actions, so `resolveMethodRule` returns a list of
rules. A cleaner with several actions is split into one cleaner per action;
each condition is simplified against its own action and cleaners whose
simplified conditions are equal are joined again. `RemoveMark(M, P)` checks
`ContainsMark(P, M)` on the fact before removing (either reach), so it is a
no-op when that literal is false and the literal can be assumed: the condition
is put in negation normal form, the literal becomes `True` and its negation
`False`, and the result is folded (constants, flattening, duplicates). The
split is equivalent to the original cleaner because all applicable cleaners'
conditions are evaluated on the same fact before any action runs.
`RemoveAllMarks` implies no literal and keeps the original condition. For an
any-field position `P = base.[any]` both `ContainsMarkOnAnyField(base, M)` (the
form an any-field condition resolves to) and `ContainsMark(P, M)` are assumed.

`RemoveMark` cannot remove `[any]` unless its own position has `[any]`. The
forward step treats the `[any]` directly at the cleaned position as possibly
empty: `RemoveMark(M, x)` clears `M` on `x` and under `x.[any]`, which deletes
a whole star demand `x.[any]·M` although forward keeps `x.f·M` (the residual
"`M` below at least one accessor" is not representable). Backward
(`JIRBackwardTaintCleanActionEvaluator`, passed as the forward evaluator's
`removeFinalFact`) runs the forward step and, for an `Exact` `RemoveMark(M, P)` whose position `P` has no `[any]`, adds the
demand's subtree `P.[any]·…` back unchanged when the step changed the demand:
only the rest of the demand is cleaned. Concrete demands absorbed into the
star survive with it. This over-approximates on paths where `M` sits directly
on `P`: the kept star still matches a source of `M` on `P` that the cleaner
removed.

Cleaners whose reach includes the `[any]` subtree keep the forward step:
`ExactAndAnyField` reach and positions with `[any]` (they clear `M` at every
depth below the position), and `RemoveAllMarks` (it removes the whole subtree
at its position, `[any]` included, as forward does). The forward step handles
`[any]` specially only at the cleaned position, so no other part of the
demand needs keeping. The user-rule cleaners of the summary rewriter
(section 4) keep the forward step.

## 9. Automata any-field exclusion depth

An any-field cleaner on an abstract Automata fact records the cleaned mark as
a deep exclusion of the abstract tail, enforced when a summary delta is
concatenated. `AccessGraphFinalFactAp` recorded it "from depth 1" even when
the abstraction point lies below the cleaned position, so the mark survived.
Mirroring `AccessTree`, `clearAllAccessorOccurrences` records it from depth 1
only when the start accessor is kept and the initial node is final, and
`concat` collapses the prefix exclusion to depth 0 when the delta's initial
node is not final. The code is shared with forward.

## 10. Known limitations

* No traces, preconditions or SARIF code flows; SARIF tests skip in backward
  mode.
* A finding is reported when one demand of a sink reaches an unconditional
  source: conjunctions of marks are over-approximated (each mark is demanded
  on its own). Querylang cases that report in backward only for this
  reason: `ExampleTest.test rule return not inside prefix`,
  `ExampleTest.test rule with ellipsis method invocation and pattern not`,
  `IssuesTest.issue chain-pattern order-sensitive match` (a value mark in
  conjunction with the automaton's global state mark).
* Findings are located at the source statement and carry the derived rule; the
  JVM test harness judges backward results by presence only, and the querylang
  harness does not check negative samples in backward mode.
* Sinks with `trackFactsReachAnalysisEnd` are reported without checking that
  the fact they create reaches the analysis end. Querylang cases that report
  in backward for this reason: `ExampleTest.test rule with pattern-not-inside
  suffix`, `test rule pattern-not with signature`, `test rule with several
  suffix cleaners`, `test cleaner after sink 0` and `test cleaner after sink 1`.
* Unconditional exit sinks are reported whenever Zero reaches the exit;
  forward does not report them.
* Forward checks a method-exit sink only on facts of zero-to-fact edges
  (`JIRMethodExitRuleProvider`); backward exit-sink demands reach the callers
  like any other demand, so taint created by a caller is also reported.
* Side-effect summaries are not modelled.
* Lambda calls resolve only to lambdas the forward prescan found; the
  trackers of all forward contexts of a method are merged.
* A refined backward edge that produces no demand does not emit a side-effect
  requirement.
* Mark literals of pass-through conditions are treated as satisfied;
  cleaners that are conditional at the call are ignored (section 8).
* An any-field sink behind an `Exact` cleaner of its value is reported when
  the mark sits on the value itself, which the cleaner removed (section 8).
  JVM case: `CleanerDslAnalysisTest` matrix with a plain source
  (`Plain-Plain-AnyField-field-depth0`).
* Cleaners of a call do not filter demands that a callee summary produces on
  its arguments (user-rule cleaners are applied to the start demand).
* Base-only modes are field-insensitive in both directions; Cactus is
  unmaintained.

# Backward JVM taint analysis

`JIRBackwardAnalysisManager` is a second `TaintAnalysisManager` for JIR. It runs the
**unchanged** generic IFDS engine (`MethodAnalyzer`, `TaintAnalysisUnitRunnerManager`)
over the reversed application graph (`ApplicationGraph.reversed`,
`opentaint-dataflow/.../graph/BackwardGraphs.kt`).

Facts are *demands*: a fact `x.f.![M]` held at a program point means
"if `x.f` carries mark `M` here, some sink is reached". Sinks create demands,
the flow functions move demands backwards through statements and calls, and a
demand that meets a source producing its mark is a finding.

Trace resolution is out of scope. None of the `get*Precondition` hooks is
needed by the forward-style tabulation, so the backward manager does not provide
real preconditions (see "Out of scope").

## 1. Graph orientation

The engine is direction-agnostic: it only uses `methodGraph.successors`,
`exitPoints`, and the entry-point resolver. With `graph.reversed`
(built over `JApplicationSingleExitGraph`):

| Engine notion | Forward meaning | Backward meaning |
|---|---|---|
| method entry point (`MethodEntryPoint.statement`) | `JMethodEnterInst` | `JMethodExitNormalInst` (normal exit only) |
| successors of `s` | forward successors | forward predecessors |
| exit point (summary emission) | `JMethodExitNormalInst`/`JMethodExitExceptionalInst` | `JMethodEnterInst` |
| edge at statement `s` | facts **before** `s` executes | facts **after** `s` executes (forward order) |
| flow function at `s` | pre-state → post-state | post-state → pre-state |

Consequences:

* The backward entry-point resolver returns the reversed graph's entry points
  minus those with `producesExceptionalControlFlow` (drops
  `JMethodExitExceptionalInst`). This mirrors forward, which drops exceptional
  exits when it applies summaries.
* Summaries are emitted at `JMethodEnterInst`. Valid exit facts are based on
  `Argument`, `This` or `ClassStatic`. `Return`, `Exception` and `LocalVar` are
  not valid.
* The forward JIR components that need the forward graph are
  `JIRLocalAliasAnalysis`, `JIRLocalVariableReachability` and the downcast to
  `JApplicationGraph`. They get it from `graph.reversed`, which unwraps the
  backward graph back to the forward one. The alias analysis is seeded with the
  forward entry (`JMethodEnterInst`), not with `methodEntryPoint.statement`.
* `isReachable` always returns `true`. Liveness is a forward notion, and a
  demand on a variable that is never defined dies at `JMethodEnterInst`
  because it is not a valid exit fact.

Observed behaviour of the reversed single-exit graph (verified by the Phase 1
harness, see section 10):

* The flow function of a statement runs **before** the engine checks whether
  that statement is an exit point, so the sequent FF at `JMethodEnterInst`
  sees every demand and its output is what becomes the summary. The same holds
  for `JMethodExitNormalInst`: the start FF output is fed to the sequent FF at
  `JMethodExitNormalInst`, which must leave it unchanged.
* Backward successors of `JMethodExitNormalInst` are the method's
  `JIRReturnInst`s. Backward successors of the first real instruction include
  `JMethodEnterInst`. `JMethodEnterInst` has no backward successors.
* `JMethodExitExceptionalInst` is never an entry point, so `JIRThrowInst`s are
  reached only from their forward successors (catch handlers), never from the
  exceptional exit.
* For a method without boundary instructions (`MethodBoundary.of` returns
  `null`, e.g. the `JMethodBoundaryInstFeature` is not installed) the reversed
  entry points are the forward exit points (`return`/`throw`, throws dropped)
  and the summary statement is the first real instruction. The backward
  context then seeds alias analysis with that first instruction; it is `null`
  (alias analysis disabled) when the method has no forward entry at all.
* `MethodInstGraph.build` indexes the boundary instructions like any other
  instruction (they are the last three entries of `instList`), so
  `getInstIndex`/`getInstByIndex` need no special handling.

## 2. Components

The code lives in package `org.opentaint.dataflow.jvm.ap.ifds.backward`, module
`opentaint-jvm-dataflow`.

| Hook | Backward class |
|---|---|
| manager | `JIRBackwardAnalysisManager : JIRLanguageManager, TaintAnalysisManager` |
| analysis context | `JIRBackwardMethodAnalysisContext` (subclass of `JIRMethodAnalysisContext`, see section 7) |
| call fact mapper | `JIRBackwardMethodCallFactMapper : MethodCallFactMapper` |
| entry-point resolver | `JIRBackwardMethodEntrypointResolver` |
| start FF | `JIRBackwardMethodStartFlowFunction` |
| sequent FF | `JIRBackwardMethodSequentFlowFunction` |
| call FF | `JIRBackwardMethodCallFlowFunction : MethodCallFlowFunction.Default` |
| call summary handler | `JIRBackwardMethodCallSummaryHandler` |
| side-effect handler | `JIRBackwardMethodSideEffectHandler` (an `object`; interface defaults: no side effects) |
| preconditions | `JIRBackwardMethodStartPrecondition` / `JIRBackwardMethodSequentPrecondition` / `JIRBackwardMethodCallPrecondition` (trivial `object`s, file `JIRBackwardPreconditions.kt`) |
| edge post-processor | the existing `JIRMethodSummaryEdgeProcessor` (direction-neutral compatibility filter) |
| call resolver | the existing `JIRMethodCallResolver` / `JIRCallResolver` |
| findings | `JIRBackwardFindingTracker` |
| rule inversion helpers | `JIRBackwardTaintRules` (sink → demand seeds, source → match) |

Manager details:

* The constructor mirrors `JIRAnalysisManager`:
  `JIRBackwardAnalysisManager(cp, refManager, taintConfig, externalMethodTracker = null, params = JIRAnalysisManager.Params())`.
  It reuses `JIRAnalysisManager.Params` so both managers satisfy
  `JIRAnalysisManagerBase` with the same `params` type.
* `selectPhase` mirrors forward (`SelectedTaintRulesProvider`,
  `relevantRuleIds`, reset of every context's analysis cache) and additionally
  resets the finding tracker, so the tracker only holds the current phase's
  findings.
* `overApproximateMethodContext` is not overridden (no shallow-scan context
  merging), `isTraceRequiredInstruction` keeps the interface default (`false`).
* The start FF delegates `propagateFact` to the forward
  `JIRMethodStartFlowFunction.propagateFact` (the context type check has no
  side effects), and `propagateZero` returns only `Zero`.
* The backward context (`JIRBackwardMethodAnalysisContext`) additionally
  carries `forwardEntryPoint` (the forward entry used to seed alias analysis,
  reused for the empty-context analyzer like `localVariableReachability` and
  `aliasAnalysis`) and `findings` (the manager's tracker).
* The backward call FF is **not** cached per statement (forward caches it in
  `JIRMethodAnalysisContext.cachedCallFF`, typed to the forward class). Phase 2
  can add a cache to `JIRBackwardMethodAnalysisContext` if construction becomes
  expensive.

## 3. Call-site base mapping (`JIRBackwardMethodCallFactMapper`)

**call → start** (caller demand after the call → callee demand at its normal exit):

* If `fact.base == base(returnValue)`, map to `Return`, and **only** to `Return`.
  For `x = f(x)` the post-call `x` is the result, not the argument.
* Otherwise use the forward mapping: receiver → `This`, `args[i]` → `Argument(i)`,
  `ClassStatic` → itself, each with the forward type check.

**exit → return** (callee summary fact at `JMethodEnterInst` → caller demand
before the call): `Argument(i)` → `args[i]` base (constants dropped),
`This` → receiver base, `ClassStatic`/`Constant` → unchanged,
`Return`/`Exception`/`LocalVar` → none.

**Relevance** is the same as forward: the base is `ClassStatic`, the receiver,
an argument, or the result.

Type checks follow forward: call → start checks `Return` against the caller's
result variable type (`returnValue.type`), `This` against the callee's
enclosing class and `Argument(i)` against the argument type; exit → return
checks against the argument/receiver type. The `InitialFactAp` overloads apply
the same mapping without type checks.

Unlike the forward mapper, the backward call → start mapping **uses** its
`returnValue` parameter (forward ignores it and its call FF passes `null`). The
backward call FF must pass the real result variable.

## 4. Statement semantics (`JIRBackwardMethodSequentFlowFunction`)

Notation: `d` is the demand after the statement. The output is the set of
demands before it. The "unchanged" case is `Sequent.Unchanged`. Anything not
listed below is unchanged.

| Statement | Demand `d` | Result |
|---|---|---|
| `x = y` (also cast, with type filter) | `x.P` | `y.P` (x killed) |
| | other | unchanged |
| `x = y.f` | `x.P` | `y.f.P` (prepend `f`, rebase to `y`; x killed) |
| `x = C.f` (static) | `x.P` | `ClassStatic(C).<C>.f.P` |
| `x = a[i]` | `x.P` | `a.[e].P` |
| `x = a op b` | `x.P` | `a.P` and `b.P` |
| `x = const / new / other` | `x.P` | killed |
| `y.f = x` | `y.f.P` | `x.P`, plus `y` with `f` cleared (strong update) |
| | `y.g.P`, `g ≠ f` | unchanged |
| | abstract `y.*`, `f ∉ excl` | concrete part processed as above, plus abstract part with `f` excluded (`propagateFactWithAccessorExclude`) |
| `C.f = x` (static) | `ClassStatic(C).<C>.f.P` | `x.P`, plus the static fact with `f` cleared |
| `a[i] = x` | `a.[e].P` | `x.P` **and** `a.[e].P` (weak update) |
| `return x` | `Return.P` | `x.P` (`Return` killed) |
| `throw x` | `Exception.P` | `x.P` |

Self-referential forms (`x = x.f`, `x.f = x`) must follow the table exactly:
the killed `x` must not be resurrected.

The abstraction and exclusions discipline is **identical to forward**. Where
backward *reads* an accessor (`y.f = x`, or a static write) from an abstract
fact, it splits the fact exactly as forward `fieldRead` does
(`removeAbstraction` plus `abstractOnly`, with the accessor excluded). Where
backward *prepends* an accessor (field, static or array read), no refinement
is needed.

Aliases are used on backward writes, the same way `JIRMethodSequentPrecondition`
uses `forEachPossibleAliasAtStatement`, when `aliasAnalysis != null`.

Rule handling inside the sequent FF:

* **`return x`**
  * Zero: seed exit-sink demands (`sinkRulesForMethodExit`). A seed on `Return`
    is rebased to `x`; seeds on `Argument`/`This`/`ClassStatic` are kept as they are.
  * Fact: a demand `Return.P·M` or `Argument(i)·M` matching an exit source
    (`sourceRulesForMethodExit`) is recorded as a finding before `Return` is
    rebased.
* **`x = C.f` where `C.f` has a static-field source**: a demand `x·M` for the
  source's mark is a finding.
* **`JMethodEnterInst`** (the backward exit):
  * Fact: a demand on `Argument`/`This` that matches `sourceRulesForMethodEntry`
    is a finding.
  * Zero: seed demands for entry sinks (`sinkRulesForMethodEntry`).

## 5. Call semantics (`JIRBackwardMethodCallFlowFunction`)

The engine applies only the call FF at call statements, so the call FF owns
the whole statement.

**Zero → Zero**
* `CallToReturnZeroFact` and `CallToStartZeroFact`.
* A demand seed for every sink rule (`sinkRulesForCallStatement`) whose condition
  is not constant-false. Each seed is emitted as a `CallToReturnZFact`.
  * Seeds come from the **positive** `ContainsMarkLiteral`s of the rewritten
    condition (negated literals ignored, both `And` and `Or` branches taken):
    fact `position·M·$` built with `ExclusionSet.Universe`, then mapped
    callee → caller with the exit → return mapping. `Result` positions and
    constant arguments produce no seed.
  * A sink whose condition is constant-true has no mark to demand. It is
    recorded as an unconditional finding in the tracker.

**Fact** (`d`)
* Not relevant → `Unchanged` (`skipCall`).
* Source match: for every source rule (`sourceRulesForCallStatement`) whose
  `AssignMark(pos, M)` position holds `d`'s mark (`TaintSourceActionPreconditionEvaluator`
  on `d` rebased to the callee base), record a finding.
  * If the source condition itself needs marks (`evaluateSourceRulePrecondition`
    gives `Pass`), emit the condition's positive mark literals as new demands
    instead of a finding. These are `CallToReturn*` facts mapped callee → caller.
* Cleaner: if a cleaner rule removes `d`'s mark at `d`'s position, emit `Drop`
  for that start base. A tainted value there would have been cleaned.
* Otherwise emit `CallToStart(d, startBase)` using the section 3 mapping.
  Constructors additionally keep `d` call-to-return, mirroring forward.

**Resolution failure** (unresolved or library callee), per `startBase`:
* `startBase ≠ Return`: keep `d` call-to-return. An unknown callee is assumed
  not to write the heap, as in forward.
* Inverse pass-through: pass rules (`passRulesForCallStatement` plus
  `defaultGetModel`) evaluated with `TaintPassActionPreconditionEvaluator`.
  A demand on the rule's `to` becomes a demand on its `from`, mapped
  callee → caller and emitted call-to-return.
* `startBase == Return`: nothing else. The result demand dies unless a pass
  rule regenerates it.

Refinement: every `FinalFactReader` that read through an abstraction must feed
the refinement into the emitted edges, exactly as forward does
(`addCallToReturn(factReader, …)` / `addCallToStart(factReader, …)` /
`addSideEffectRequirement`).

Corrections to the above, found against the code:

* `MethodCallFlowFunction.Default.propagateUnresolvedCallFact` does **not**
  receive `startFactBase`. The `startBase == Return` rule is therefore
  implemented by overriding the three `propagate*ResolutionFailure` methods
  (return an empty set for `Return`, otherwise delegate to `super`). Their
  return types are narrowed by `Default` (`Set<CallToReturnZFact>`,
  `Set<FactCallFailureFact>`, `Set<CallToReturnNonDistributiveFact>`). The
  Phase 1 stub already contains these overrides.
* The resolution-failure hooks run once **per start base**, so a demand whose
  base is both receiver and argument is kept call-to-return twice; edge
  deduplication absorbs this.
* `TaintSourceActionPreconditionEvaluator` used to take an `InitialFactReader`.
  Demands are `FinalFactAp`, so its constructor now takes the `FactReader`
  interface (behaviour-preserving for the trace code). The backward source
  match passes a `FinalFactReader`, which records the refinement when the
  demand is abstract; that reader is returned to the caller (see the helper
  API) so its refinement can be merged into the emitted edges.
* `TaintPassActionPreconditionEvaluator` still needs an `InitialFactReader`:
  `copyAllFactsPrecondition` reads the `InitialFactAp` and rebuilds an
  `InitialFactAp`. It cannot evaluate a `FinalFactAp` demand. Phase 2 needs a
  `FinalFactAp` counterpart (a `PassActionEvaluator<EvaluatedPass>` that, for
  `CopyAllMarks(from, to)`, reads `to` from the demand and rebuilds the delta
  at `from`, and for `CopyMark(from, to, M)` checks `to·M·$` and emits
  `from·M·$`), or a generalisation of the existing evaluator.
* Conditions of cleaner, source and pass rules are evaluated with the rewritten
  condition of `prepareCallStatementRules`, which uses the **forward** alias
  analysis at the call statement. This is sound for backward because the call
  statement is the same instruction in both directions.

## 6. Summaries (`JIRBackwardMethodCallSummaryHandler`)

The handler inherits `MethodCallSummaryHandler`, with
`mapMethodExitToReturnFlowFact` set to the section 3 exit → return mapping.
No rule-based rewriting and no call aliases.

## 6a. Helper API (`JIRBackwardTaintRules`)

`JIRBackwardTaintRules(apManager, context: JIRBackwardMethodAnalysisContext)`
is a per-flow-function helper (create it lazily in the FF, it holds no state).
It turns rules into demand seeds and demand facts into source findings. It is
used by the Phase 1 stubs for the zero fact and is the intended entry point for
the Phase 2 call FF and sequent FF.

Result types:

```kotlin
sealed interface SinkDemand {
    val rule: TaintConfigurationSink
    data class Seed(rule, fact: FinalFactAp)       // demand already mapped to the caller/statement
    data class Unconditional(rule)                 // condition true, or only negated mark literals
}

sealed interface SourceMatch {
    val rule: TaintConfigurationSource
    val marks: Set<TaintMarkAccessor>              // marks of the matched AssignMark actions
    data class Found(rule, marks)                  // the demand is produced by this source
    data class ConditionDemand(rule, marks, facts: List<FinalFactAp>)  // source needs marks: new demands, mapped
}

class SourceMatchResult(val matches: List<SourceMatch>, val reader: FinalFactReader?) {
    val found: List<SourceMatch.Found>
    val conditionDemands: List<FinalFactAp>
}
```

Sink → demand seeds (zero fact):

| Function | Statement | Rules | Seed mapping |
|---|---|---|---|
| `callSinkDemands(statement, callExpr, returnValue): List<SinkDemand>` | call | `sinkRulesForCallStatement` | callee → caller (`mapCalleeToCaller`); `Return` and constant args dropped |
| `methodExitSinkDemands(statement: JIRReturnInst)` | `return x` | `sinkRulesForMethodExit` | `Return` → base of `x` (void/constant: dropped); `Argument`/`This`/`ClassStatic` kept; others dropped |
| `methodEntrySinkDemands(statement: JIRInst)` | `JMethodEnterInst` | `sinkRulesForMethodEntry` | `Argument`/`This`/`ClassStatic` kept; others dropped |
| `recordSinkDemands(statement, demands): List<FinalFactAp>` | any | – | records `BackwardDemandSeed` / `BackwardUnconditionalSink` in the tracker and returns the seed facts to emit |

Seeds are built from the positive `ContainsMarkLiteral`s of the rewritten
condition after `removeNegated()` (both `And` and `Or` branches, duplicates
removed): `apManager.mkAccessPath(position, ExclusionSet.Universe, mark)`,
i.e. `position·M·$`. The caller emits them as `CallToReturnZFact` (call FF) or
`Sequent.ZeroToFact` (sequent FF).

Demand → source match (fact):

| Function | Use at | Demand read as |
|---|---|---|
| `matchCallSources(statement, callExpr, returnValue, callerFact, startBase)` | call FF, for each `(callerFact, startBase)` of the section 3 call → start mapping | `callerFact.rebase(startBase)`; condition demands mapped callee → caller |
| `matchMethodExitSources(statement: JIRReturnInst, fact)` | sequent FF at `return x`, **before** `Return` is rebased to `x` | `fact` as is; condition demands on `Return` rebased to `x` |
| `matchMethodEntrySources(statement, fact)` | sequent FF at `JMethodEnterInst` | `fact` as is (only `Argument`/`This` bases can match) |
| `matchStaticFieldSources(statement: JIRAssignInst, fact)` | sequent FF at `x = C.f` | `fact.rebase(Return)` when `fact.base` is `x` |
| `recordSourceMatches(statement, result)` | any | records one `BackwardSourceFinding` per `(Found, mark)` |
| `mapCalleeToCaller(statement, calleeFact): FinalFactAp?` | any call | section 3 exit → return mapping, single result |

Matching uses `evaluateSourceRulePrecondition` with a
`TaintSourceActionPreconditionEvaluator` over a `FinalFactReader`: the demand
must contain `position·M·$` for an `AssignMark(position, M)` of the rule
(`[any]` positions also match their base). Negated mark literals of the source
condition count as satisfied; the remaining positive literals become
`ConditionDemand.facts`. The FF must:

1. call `recordSourceMatches` for the findings,
2. emit `conditionDemands` as new demands (`CallToReturnZFact`/`CallToReturn*`
   in the call FF, `Sequent.*ToFact` in the sequent FF),
3. merge `result.reader` into its own reader
   (`factReader.updateRefinement(result.reader)`) when the demand was abstract,
   so the refinement reaches the emitted edges.

A source match does not kill the demand: whether the demand keeps flowing past
the source (e.g. a source that also has a pass-through) is the FF's decision.

Not covered by the helper (Phase 2): cleaner checks, inverse pass-through (see
the notes at the end of section 5), aliases.

## 7. Required forward-side refactors

These keep the forward behaviour identical.

1. `JIRMethodAnalysisContext` becomes `open`, and its `analysisManager` field is
   typed by a small interface `JIRAnalysisManagerBase` (`phase`, `params`).
   Both managers implement it. The backward context overrides
   `methodCallFactMapper`. The only use site outside the context is
   `analysisContext.analysisManager.params.defaultGetModel` (forward call FF
   and `JIRMethodCallPrecondition`), which compiles unchanged.
2. `JIRMethodSummaryEdgeProcessor` is unchanged. It already takes a
   `JIRMethodAnalysisContext`.
3. `TaintSourceActionPreconditionEvaluator` (module `opentaint-dataflow`) takes
   a `FactReader` instead of an `InitialFactReader` (see section 5).

## 8. Findings (`JIRBackwardFindingTracker`)

`TaintSinkTracker` records *sink* vulnerabilities, so backward findings go to a
separate, thread-safe tracker owned by the manager:

```
BackwardSourceFinding(methodEntryPoint, statement, rule: TaintConfigurationSource, mark: TaintMarkAccessor)
BackwardUnconditionalSink(methodEntryPoint, statement, rule: TaintConfigurationSink)
```

A finding means "a value produced by source `rule` at `statement` with mark
`mark` may reach a sink that demands `mark`". Demands carry only the mark, so
the finding does not name the sink. Recovering the sink needs trace resolution,
which is out of scope.

A third record, `BackwardDemandSeed(methodEntryPoint, statement, rule: TaintConfigurationSink, fact: FinalFactAp)`,
is kept for every seed emitted by a sink rule. It is a debugging and test aid
(the Phase 1 smoke test asserts on it); it is not a finding.

API: `addSourceFinding` / `addUnconditionalSink` / `addDemandSeed`, snapshot
getters `sourceFindings()` / `unconditionalSinks()` / `demandSeeds()`, and
`reset()`. Storage is `ConcurrentHashMap.newKeySet`, so records are
deduplicated and safe to add from the runner threads. The manager exposes it
as `JIRBackwardAnalysisManager.findings` and resets it in `selectPhase`.

## 9. Out of scope / known limitations

* **Preconditions and trace resolution.** The `get*Precondition` hooks return
  trivial implementations, and backward findings have no traces.
* **Staged pipeline.** `StagedAnalysisRunner` filters traceless findings and is
  sink-oriented, so backward runs drive the engine directly
  (`selectPhase(FullScan())` → `resetApManager` → `runAnalysis`).
* **Lambdas.** Lambda call resolution relies on forward-flowing type-info facts
  created at the lambda allocation during `Prescan`. Backward cannot produce
  them, so lambda calls go through resolution failure (pass-through
  approximation).
* **Side-effect summaries and `trackFactsReachAnalysisEnd`** are not modelled.
* **Exceptional flow** is ignored, as in forward.
* **`ContainsMarkOnAnyAccessorLiteral`** (mark on any field) produces no seed
  and no source-condition demand. A sink whose condition has only such
  literals produces nothing.
* **Sinks with only negated mark literals** are recorded as unconditional,
  matching the "negated mark condition is satisfied" convention of
  `removeNegated` in the trace preconditions.
* **Rule selection without a prescan.** `selectPhase(FullScan())` calls
  `selectRules(relevantRuleIds)` exactly like forward. When the backward run
  skips `Prescan`, that set is empty. The test providers ignore
  `selectRules`, but a semgrep-backed provider would then select no rules.
  Run a `Prescan` phase first (it records the rule ids) when using such a
  provider.

## 10. Phase 1 status and test harness

Phase 1 delivers everything above except the fact-level flow functions:

* `JIRBackwardMethodSequentFlowFunction` (stub): zero → `ZeroToZero`, plus the
  exit-sink seeds at `return x` and the entry-sink seeds at `JMethodEnterInst`
  (both via the helper). Every fact → `Unchanged`.
  Constructor: `(apManager, analysisContext: JIRBackwardMethodAnalysisContext, currentInst: JIRInst)`.
* `JIRBackwardMethodCallFlowFunction` (stub): zero → `CallToReturnZeroFact`,
  `CallToStartZeroFact`, a `CallToReturnZFact` per sink seed, and
  unconditional-sink findings. Every fact → `Unchanged` (`skipCall`).
  Resolution failure keeps the fact call-to-return except for the `Return`
  start base. Constructor:
  `(apManager, analysisContext, returnValue: JIRImmediate?, callExpr: JIRCallExpr, statement: JIRInst)`.

Phase 2 replaces the fact-level bodies of these two classes.

Test harness: `core/src/test/kotlin/org/opentaint/jvm/sast/dataflow/backward/`.

* `BackwardAnalysisTest : AnalysisTest` builds
  `JIRSafeApplicationGraph(JApplicationSingleExitGraph(JApplicationGraphImpl(cp, usages)))`,
  reverses it, creates `JIRBackwardAnalysisManager` and
  `TaintAnalysisUnitRunnerManager` directly (`SingleLocationUnit`,
  `DummySerializationContext`), selects the `ApManager` from `apMode`
  (default `Tree`), and runs `selectPhase(FullScan())` → `resetApManager` →
  `runAnalysis(entry)`. It returns a `BackwardResult` with the runner status,
  the three tracker lists, the analysed methods and the facts per statement.
  Rule builders, the rules provider and the graph come from `AnalysisTest`
  (`findEntryPoint`, `createRulesProvider`, `createAnalysisGraph`,
  `SingleLocationUnit` are now `protected`).
* Assertions: `assertSourceReached(config, testCls, entryPointName, sourceMethodName, mark, testName)`
  and `assertNoSourceReached(config, testCls, entryPointName, testName)`.
* `BackwardSmokeTest` on `test.samples.SimpleDataFlowSample#simpleDataFlow`:
  * the sink seed is produced once, at the `sink(...)` call, on the caller
    local, with the `tainted` mark, and every callee is entered from its exit;
  * a method-entry sink on `sink` is seeded at `JMethodEnterInst` of `sink`,
    and its zero-to-fact summary is mapped back to the caller's argument local
    (visible at the `process(...)` call, the next backward statement);
  * the source-reach assertion is `@Disabled("phase 2")`.

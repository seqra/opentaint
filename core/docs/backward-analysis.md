# Backward JVM taint analysis

`JIRBackwardAnalysisManager` (package `org.opentaint.dataflow.jvm.ap.ifds.backward`,
module `opentaint-jvm-dataflow`) is a subclass of the forward `JIRAnalysisManager`.
It runs the **unchanged** generic IFDS engine once over the reversed application
graph (`ApplicationGraph.reversed`) with rules whose sources and sinks are
swapped (section 7), so a finding is an ordinary sink report at the statement of
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
| method entry point | `JMethodEnterInst` | `JMethodExitNormalInst`; `JMethodExitExceptionalInst` and non-exiting starts (Zero only) |
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
* Non-exiting starts: code with no forward path to any exit is never
  backward-reachable from the exits. `JIRBackwardNonExitingStarts` takes the
  statements of the forward method graph that are reachable from the entry
  and reach no exit, and adds one representative of every bottom strongly
  connected component of that region as an extra entry point; every statement
  of the region is backward-reachable from one of them. Like the exceptional
  exit they start with Zero only (no caller demands).

## 2. Components

`JIRBackwardAnalysisManager(forward)` is created by
`JIRAnalysisManager.createBackwardAnalysisManager` and shares the forward
manager's classpath, `relevantRuleIds` and parameters. Its rules are the
forward rules wrapped in `JIRBackwardTaintRulesProvider` (section 7). It
inherits the call resolver (applied to `graph.reversed`), method inst graph,
language manager, context serializer, fact type checker and edge
post-processor, and overrides only:

| Hook | Backward |
|---|---|
| context | `JIRBackwardMethodAnalysisContext` (see section 1; backward fact mapper) |
| entry points | entry points of the reversed method graph plus non-exiting starts |
| start / sequent / call FF | `JIRBackwardMethodStartFlowFunction` / `...SequentFlowFunction` / `...CallFlowFunction` |
| summary handler | `JIRBackwardMethodCallSummaryHandler` |
| preconditions, side effects | trivial (`JIRBackwardPreconditions.kt`, empty handler) |

Backward-only helpers: `JIRBackwardTaintRulesProvider`,
`JIRBackwardNonExitingStarts`, `JIRBackwardMethodCallFactMapper` (delegates to
the forward mapper).

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
* `x = C.f`: derived static-field sinks (`sinkRulesForStaticField`) are applied
  to a demand on `x` by `JIRSequentTaintUtil` with `x` as the result base.
* `JMethodEnterInst`: derived entry sinks are applied by `JIRSequentTaintUtil`
  (unconditional entry sinks on Zero). They are skipped when every initial fact
  of the edge is an `Argument`/`This` root carrying an entry mark: forward drops
  exactly those marks at the exit (`dropArgumentsLocalTaintMarks`). The demand
  then leaves the method without its zero-edge marks (section 8) unless an
  initial fact is abstract or carries one.

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
  (section 9).
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

Shared code stays in the forward classes; backward subclasses or calls them.

| Forward origin | Backward use |
|---|---|
| `JIRMethodSequentFlowFunction` (open; `propagate`, `simpleAssign`, `fieldRead`, `fieldWrite`, `FactRefiner` are protected) | `JIRBackwardMethodSequentFlowFunction` extends it and inherits the Z2F/F2F/NDF2F plumbing, operand decomposition and type filters. It overrides the three assignment primitives with roles swapped: `simpleAssign` moves `L → R` and kills `L`; `x = y.f` is the forward write move of the demand into `y.f` (from an auxiliary base, including forward write aliasing); `y.f = x` is the forward write with no value (strong clear, weak arrays) plus the forward read of `y.f` into `x` (including the abstraction split). The forward static write clears nothing (it tests `f` against a fact that starts with `<C>`; forward drops such findings in trace resolution), so `C.f = x` clears `<C>` from `ClassStatic` and `f` from the `<C>` subtree with two forward `RefAccess` writes and puts the rest back under `<C>` |
| `JIRMethodCallFlowFunction` (open; `applyTaintRules`, `applyCleanersOrCallToStart` protected, `cleanActionEvaluator` protected open) | `JIRBackwardMethodCallFlowFunction` extends it, inherits `propagateZeroToZero` (seeds, unconditional sinks), applies `applyTaintRules` to every demand and runs the forward cleaner step with `JIRBackwardTaintCleanActionEvaluator` |
| `JIRTaintCleanActionEvaluator` (open; `removeFinalFact` protected open) | `JIRBackwardTaintCleanActionEvaluator` extends it and keeps the `[any]` subtree at the position of an `Exact` `RemoveMark` (section 9) |
| `JIRMethodCallTaintUtil`, `JIRSequentTaintUtil` (generic over source and sink types), `applyMethodExitSinkRules` / `applyMethodExitSourceRules` (protected) | every report and every rule-created demand |
| `JIRMethodCallSummaryHandler` (open; `applyCallAliases` protected open) | `JIRBackwardMethodCallSummaryHandler` extends it (backward exit mapping, no aliases, no rewriting) |
| `JIRMethodStartFlowFunction` | held by `JIRBackwardMethodStartFlowFunction` for type checks |
| `TaintPassActionEvaluator`, `TaintConfigUtils.accept` | inverse pass-through (swapped positions) |
| `JIRMethodCallRuleBasedSummaryRewriter.rewriteSummaryFact` | user-rule rewriting of demands |
| `aliasesPersistedThroughCall` (extracted from `forEachAliasAfterCallStatement`) | call-site alias inversion |

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

## 7. Backward rule provider

`JIRBackwardTaintRulesProvider` wraps the forward provider and answers every
query with the swapped rules, derived once per rule. Conditions are split into
DNF cubes of positive mark literals plus other literals; negated mark literals
are dropped (forward treats them as satisfied) and a cube containing another
cube is dropped (absorption). A cube with no mark literal is *unconditional*.

| Forward rule | Backward rule |
|---|---|
| unconditional call / exit / entry-point / static-field source, `AssignMark(M, P)` | sink of the matching kind (call, exit, entry; static fields: `sinkRulesForStaticField`) at the same method with `ContainsMark(P, M)` (and its zero-edge copy), plus the source's other literals. `P.[any]` becomes `ContainsMarkOnAnyField(P, M)` |
| conditional call / exit source `C ⇒ AssignMark(M, P)` | per cube: source with condition `ContainsMark(P, M)` assigning the cube's marks at their positions (twice: plain and zero-edge marks) |
| conditional entry-point source | none (forward applies only unconditional entry sources) |
| call sink, positive literals `M@P` | per cube: source assigning `M@P`; it fires on Zero (pre-call demands) |
| method-exit sink | per cube: exit source assigning the zero-edge marks (section 8) |
| method-entry sink with mark literals | none (forward fires only unconditional entry sinks) |
| unconditional call / entry / exit sink | the sink itself with the mark-free cubes (reported on Zero) |
| pass-through | unchanged (inverted by the flow functions), plus zero-edge copies of `CopyMark` actions |
| cleaner | the disjunction of its mark-free cubes, plus zero-edge copies of `RemoveMark` actions; none when every cube has a mark literal (section 9) |

`trackFactsReachAnalysisEnd` is ignored: every derived rule is built as if the
sink had none.

Call-site cubes whose mark literal is on `Result` are dropped: forward reads a
call's condition before the call, where the result never holds a fact.
Queries with `allRelevant` (the summary rewriter) return the original sources.

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

## 8. Zero-edge-only exit sinks

Forward checks a method-exit sink only on facts of zero-to-fact edges
(`JIRMethodExitRuleProvider`): the taint must be created inside the method's
dynamic extent. Demands seeded by an exit sink therefore use *zero-edge marks*
(`M$zero-edge`). Every rule that reads, copies or clears `M` treats its
zero-edge copy the same way, and a derived sink reports either. At
`JMethodEnterInst` zero-edge marks are removed from the demand unless an
initial fact of the edge is abstract or carries one: seeded demands of the
method itself (zero edges, or initial facts without zero-edge marks) never
reach the callers, while zero-edge demands a caller passed in return to it
through the summary. Exit sinks are treated as zero-edge-only in every
chain, as `JIRMethodExitRuleProvider` makes them in all analysis
configurations.

## 9. Cleaners

A cleaner condition with a mark literal reads the forward fact before the
call, which a demand does not determine, so backward ignores such cleaners:
the provider keeps a cleaner only with the mark-free cubes of its condition
(evaluated at the call site like any other condition) and drops it when there
are none. Demands pass the ignored cleaners unchanged.

`MethodTaintConfigurationResolver` (shared with forward) rewrites a cleaner
condition against its actions. `RemoveMark(M, P)` checks `ContainsMark(P, M)`
on the fact before removing (either reach), so it is a no-op when that
literal is false and the literal can be assumed. The condition is put in
negation normal form, assumed literals become `True` and their negations
`False`, and the result is folded (constants, flattening, duplicates). A
literal is implied only for its own action, so the rewrite is kept only when
assuming each action's literal alone gives the same condition:
`ContainsMark(x, M)` with removals from `x` and `y` stays conditional. A
cleaner is left unchanged when an action implies no literal: `RemoveAllMarks`,
any-field positions (no presence check; the removal records an exclusion on
an abstract fact where `ContainsMarkOnAnyField` is false) and `String`
positions (the removal also clears `<string-bytes>`, which `new String(byte[])`
taints and the condition does not read).

`RemoveMark` cannot remove `[any]` unless its own position has `[any]`. The
forward step treats the `[any]` directly at the cleaned position as possibly
empty: `RemoveMark(M, x)` clears `M` on `x` and under `x.[any]`, which deletes
a whole star demand `x.[any]·M` although forward keeps `x.f·M` (the residual
"`M` below at least one accessor" is not representable). Backward
(`JIRBackwardTaintCleanActionEvaluator`) runs the forward step and, for an
`Exact` `RemoveMark(M, P)` whose position `P` has no `[any]`, adds the
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
* A finding is reported when one demand of a sink cube reaches an unconditional
  source: conjunctions of marks are over-approximated (each conjunct is
  demanded on its own). Querylang cases that report in backward only for this
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
* Side-effect summaries are not modelled.
* Lambda calls resolve only to lambdas the forward prescan found; the
  trackers of all forward contexts of a method are merged.
* A refined backward edge that produces no demand does not emit a side-effect
  requirement.
* Mark literals of pass-through conditions are treated as satisfied;
  cleaners whose conditions need a mark are ignored (section 9).
* An any-field sink behind an `Exact` cleaner of its value is reported when
  the mark sits on the value itself, which the cleaner removed (section 9).
  JVM case: `CleanerDslAnalysisTest` matrix with a plain source
  (`Plain-Plain-AnyField-field-depth0`).
* Cleaners of a call do not filter demands that a callee summary produces on
  its arguments (user-rule cleaners are applied to the start demand).
* Base-only modes are field-insensitive in both directions; Cactus is
  unmaintained.

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

A source match never kills the demand: the demand keeps flowing (to `x` at
`return x`, to the static field at `x = C.f`, unchanged at `JMethodEnterInst`).
Condition demands of a matched source (`SourceMatchResult.conditionDemands`)
are emitted next to it, from the same initial fact.

### 4.1 Implementation notes

The FF mirrors forward's callback structure. `propagate` receives one output
object per edge kind with `unchanged`, `propagateFact`,
`propagateFactWithRefinement(reader, fact)` and
`propagateFactWithAccessorExclude(fact, accessor)`. For `FactToFact` the last
two refine the initial fact exactly like forward (`reader.refineFact` on both
facts, or `exclude(accessor)` on both). `ZeroToFact` and `NDFactToFact` edges
cannot be refined; as in forward, a refinement there is an error. Demands on
these edges come from sink seeds (`position·M·$` with `ExclusionSet.Universe`),
so they are never abstract and never need one.

An output fact equal to the incoming one is emitted as `Sequent.Unchanged`,
any other one as a new edge. Every case below builds its outputs from the
incoming demand, so nothing is emitted "by default": this is what keeps the
self-referential forms exact.

* **Type filters.** Before an assignment is processed the incoming demand is
  filtered with `filterFactByLocalType` exactly where forward filters it: the
  lhs and every rhs base (cast operand with the cast type, array with the array
  type, field-ref instance with the instance type and with the field's
  enclosing type, both binary operands with their own types). A demand
  rejected by a filter is dropped. The filter depends only on the accessors, so
  filtering `x.P` with `x`'s type before rebasing to `y` is the same as
  filtering the result.
* **Constants.** A demand is never rebased to a `Constant` base: `x = "c"`,
  `x = a op 1` (for the constant operand), `y.f = "c"`, `a[i] = 0`,
  `return "c"` and `throw` of a constant kill the moved part.
* **Other rhs.** `new`, `newarray`, `length`, `instanceof`, unary negation,
  lambdas etc. kill a demand on the lhs, as forward does not propagate through
  them either.
* **Instance field write `y.f = x`** (strong update) on a demand with base `y`:
  1. abstract and `f ∉ excl`: the `removeAbstraction()` part is processed by
     the next two steps, and `y.*` (`abstractOnly()`) is emitted with `f`
     excluded. Abstraction is checked **first**, like forward, so a tree fact
     `y.{f.P, *}` moves `f.P` and refines the abstract part.
  2. does not start with `f`: unchanged.
  3. starts with `f`: `clearAccessor(f)` is kept (if non-empty) and
     `readAccessor(f)` is rebased to `x` (dropped if `x` is a constant).
* **Static write `C.f = x`** runs the same procedure over the two accessors
  `<C>` then `f` on the `ClassStatic` demand, re-prepending `<C>` to whatever is
  kept at the second level. An abstract demand is refined on `<C>` at the first
  level (`ClassStatic.*` with `<C>` excluded) and on `f` at the second one
  (`ClassStatic.<C>.*` with `f` excluded). Forward's aux-base trick is not
  needed because backward never has to rebuild the static prefix around a
  read.
* **Array write `a[i] = x`** (weak update) keeps the whole demand unchanged and
  additionally moves `a.[e].P` to `x.P`. An abstract `a.*` (with `[e]` not
  excluded) is kept unchanged and emitted again with `[e]` excluded, exactly
  the shape of forward `fieldRead` (unchanged original plus excluded
  `abstractOnly`).
* **Reads** (`x = y.f`, `x = C.f`, `x = a[i]`) prepend the accessor(s) and
  rebase; they never refine. A read on a demand whose base is not `x` is
  unchanged (the forward array-read "re-emit" hack is not mirrored; it only
  exists to force a new forward edge).
* **Throw** has no rules: `Exception.P → x.P`, other demands unchanged.
* **Entry rules** are matched only when `currentInst is JMethodEnterInst`, as
  the Phase 1 stub already did for entry-sink seeds. A method without boundary
  instructions therefore gets neither entry sinks nor entry sources.

**Aliases (field and array writes only).** When `aliasAnalysis != null` and the
demand base `z` differs from the written instance `y`, the FF asks
`aliasAnalysis.findAlias(y, currentInst)`, i.e. the alias state **before** the
statement. It is the right state for the backward direction because the object
written by `y.f = x` is fixed by the value of `y` before the statement, and a
write to a field does not change which locals alias `y` (it only changes the
heap). It is also the state forward uses (`forEachAliasAtStatement`) and the
one `JIRMethodSequentPrecondition` uses (`forEachPossibleAliasAtStatement`),
so the two directions agree on the same statement.

Every `AliasApInfo(base = z, accessors = [g1..gn])` of `y` (meaning
`y == z.g1…gn`) translates the demand to the instance: `d.readAccessor(g1)…readAccessor(gn)`
rebased to `y` (the same "unapply" as the precondition). If the translation
meets an abstract node whose exclusions do not contain `gi`, the original
demand is emitted with `gi` excluded, so the engine refines the initial fact
on the alias path. The translated demand only contributes its **moved** part
(`y.f.P → x.P`, with the same abstract refinement on `f`, applied to the
original demand). The original demand itself is kept unchanged: an alias is a
may-alias, so the update through it is weak. Static writes have no aliases
(the base is `ClassStatic`). Reads, simple assignments, returns and throws do
not use aliases: the demand is on the assigned variable itself.

**JIR shapes observed** (`BackwardSequentSample`): javac/JIR never produce a
literal `x = x.f` for `n = n.next`; it is split into `%t = n.next; n = %t`. The
direct form is still handled (the demand on `x` is moved, nothing else is
emitted). `x.f = x` does appear literally. `b2 = b` is coalesced into a single
local, so alias tests need a heap indirection (`h.box = b; b2 = h.box`).
Integer arithmetic is a `JIRBinaryExpr`; demands on primitives survive the
type filter only for marks ending in `%%primitive%%`
(`PrimitiveTaintExt.PRIMITIVE_TRACKING_ENABLED_MODE`), as in forward.

### 4.2 Status and tests (Phase 2b)

The sequent FF is complete (the section 10 stub description applies only to
the zero fact now). Tests, in `core/src/test/kotlin/org/opentaint/jvm/sast/dataflow/backward/`,
on `core/samples/src/main/java/test/samples/BackwardSequentSample.java`:

* `BackwardSequentFlowTest` (end to end, no call-FF fact handling needed): an
  entry-point source on `Argument(0)` of the analysed method plus a call sink
  on `sink(String)`/`sinkInt(int)`. The seed is produced at the sink call,
  flows backward through the sequent FF only, and must (or must not) be matched
  at `JMethodEnterInst`. Positive and negative cases for local copies and
  overwrites, casts, field write/read, strong field overwrite, other field,
  aliased field and array writes (heap indirection), array weak update, static
  write/read and strong static overwrite, static-field source at `x = C.f`,
  binary operands, both self-referential forms, branches and a loop-carried
  flow, and a method-exit sink on the analysed method.
* `BackwardSequentFlowFunctionTest` (unit): builds the FF for one instruction
  with a hand-made `JIRBackwardMethodAnalysisContext` (no alias analysis) and
  checks the exact `Sequent` sets for abstract `FactToFact` demands (field,
  array and two-level static refinement, read without refinement), concrete
  `ZeroToFact` demands (move/clear/keep, self write), and the exit-source match
  at `return x` (finding on the concrete demand, mark refinement on the
  abstract one). The unit fixture must call `selectPhase(FullScan())`: in
  `Prescan` the taint context keeps only pass-through rules.

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
* For every `(callerFact, startBase)` of the section 3 call → start mapping
  (with the real `returnValue`):
  * Source match: for every source rule (`sourceRulesForCallStatement`) whose
    `AssignMark(pos, M)` position holds `d`'s mark (`TaintSourceActionPreconditionEvaluator`
    on `d` rebased to the callee base), record a finding.
    * If the source condition itself needs marks (`evaluateSourceRulePrecondition`
      gives `Pass`), emit the condition's positive mark literals as new demands
      instead of a finding. These are `CallToReturn*` facts mapped callee → caller.
    * A source match does not kill `d`: the cleaner and call-to-start steps
      below still run. For `r = source()` the demand on `r` enters the source
      method (if it is analysed) as a `Return` demand and dies there.
  * Cleaner: see "Cleaner inversion" below. Surviving demands continue,
    removed alternatives become `Drop`.
  * Otherwise emit `CallToStart(d, startBase)` using the section 3 mapping.
    Constructors additionally keep `d` call-to-return, mirroring forward.

**Cleaner inversion.** A cleaner is a filter: forward `clean(f)` keeps the
part of `f` the cleaner does not remove. A value that is in the demand `d`
after the call was, before the call, a value that survived the cleaner, so the
demand before the call is `clean(d)`. The backward FF therefore runs the
**forward cleaner code on the demand itself**
(`TaintConfigUtils.applyCleaner` with `JIRTaintCleanActionEvaluator`, on
`d` rebased to the callee base), exactly as forward
`applyCleanersOrCallToStart` does:

* a removed alternative (`EvaluatedCleanAction.fact == null`) → `Drop`
  (with the rule trace for user-defined rules, as forward);
* every surviving fact → call-to-start (and constructor call-to-return).

Consequences:

* `RemoveMark(P, M)` drops a demand `P·M·$`; a demand `P.f·M·$` survives
  (reach `Exact`), a demand under `[any]` is split exactly as forward
  (`TaintCleanReach.Exact` vs `ExactAndAnyField` handled by `Cleaner.kt`).
* `RemoveAllMarks(P)` drops every demand at or below `P`.
* A `Result` cleaner drops a demand on the call result before it reaches
  the callee or pass-through. Forward applies user-defined `Result` cleaners
  to pass-through results through `JIRMethodCallRuleBasedSummaryRewriter`;
  the backward order (clean the result demand first) is the inverse, and it
  applies to every cleaner rule, not only user-defined ones.
* The cleaner **condition** is evaluated by `TaintFactAwareConditionEvaluator`
  over the demand rebased to the callee base, as forward evaluates it over the
  fact. Mark literals are therefore checked against the demanded marks. This
  is exact for the common self-referential form (`RemoveMark(P, M)` guarded by
  `ContainsMark(P, M)`); a cleaner whose condition names a mark at another
  position does not fire unless that position is the demand's.
* Inverse pass-through demands (resolution failure, below) go through the
  same cleaner filter: forward cleans the argument fact **before** the
  pass-through runs, so a pass-through source position whose mark is cleaned
  by the same call produces no demand.
* Aliases are not consulted (forward's cleaner does not consult them either).
* In the base-only AP modes a concrete demand `P·M·$` also reads as
  `P.[any]·M·$`, and the `Exact` split keeps the `[any]` alternative, so
  `RemoveMark` never fully drops the demand. This is the same field-insensitivity
  trait forward has in these modes; the Phase 2a tests run in `Tree` mode.

**Resolution failure** (unresolved or library callee), per `startBase`
(`callerFact` is the caller edge fact, `d = callerFact.rebase(startBase)`):
* `startBase ≠ Return`: keep `callerFact` call-to-return (trace `null`, as
  forward's default propagation). An unknown callee is assumed not to write
  the heap, as in forward.
* Inverse pass-through: pass rules (`passRulesForCallStatement` plus
  `defaultGetModel.defaultPropagationRules(callee)`) evaluated with
  `TaintPassActionInverseEvaluator` (see "Pass inversion"). A demand on the
  rule's `to` becomes a demand on its `from`, filtered by the cleaners of the
  call, mapped callee → caller (`mapCalleeToCaller`: `Return` results
  dropped) and emitted call-to-return with trace `Rule(rule, action)`.
* `startBase == Return`: nothing else. The result demand dies unless a pass
  rule regenerates it.

**Pass inversion** (`TaintPassActionInverseEvaluator`, `opentaint-dataflow`
`taint/Propagator.kt`, a sibling of `TaintPassActionEvaluator`; the trace
evaluator `TaintPassActionPreconditionEvaluator` is unchanged):

* `CopyAllMarks(from, to)`: if the demand contains `to`
  (`FinalFactReader.containsPosition`, refining an abstract demand exactly as
  forward), the demand is type-filtered by the `to` position type, the delta
  after `to` is read (`readPosition`) and rebuilt at `from` with the demand's
  exclusions, then type-filtered by the `from` position type.
* `CopyMark(from, to, M)`: if the demand contains `to·M·$`, emit
  `from·M·$` with the demand's exclusions, type-filtered by the `from` type.
* Unlike the forward evaluator it does not return the original fact: keeping
  the demand is the resolution-failure rule above (and does not apply to
  `Return`).
* Rule applicability: a rule is used when its rewritten condition is not
  constant-false. Mark literals of pass conditions are treated as satisfied
  (both positive and negated). Forward evaluates them against the fact at
  `from`, which the backward FF does not have; treating them as true
  over-approximates. Non-mark conditions (types, constants) are already
  folded into the rewritten condition by `prepareCallStatementRules`.

Not mirrored from forward (documented omissions):

* `JIRMethodCallRuleBasedSummaryRewriter` (user-rule-based rewriting of
  pass-through and default-propagation facts) is forward-only.
* The external-method tracker is not fed by backward resolution failures.
* Call-site aliases (`forEachAliasAfterCallStatement`) are not applied to
  emitted demands.
* No per-statement call FF cache (the FF is cheap to build; its helpers are
  lazy).

Refinement: every `FinalFactReader` that read through an abstraction must feed
the refinement into the emitted edges, exactly as forward does
(`addCallToReturn(factReader, …)` / `addCallToStart(factReader, …)` /
`addSideEffectRequirement`). Concretely:

* `propagateFact`: one reader over `d`. It absorbs the source-match reader
  (`SourceMatchResult.reader`), the cleaner condition reader and each
  surviving cleaner reader before the call-to-start / constructor
  call-to-return that uses it. Condition demands of conditional sources are
  emitted after all start bases were processed, so they carry the full
  refinement. If the reader was refined, `addSideEffectRequirement` is called.
* Resolution failure: the kept demand uses a fresh reader (as forward's
  default propagation). The pass reader over `d` absorbs the inverse pass
  reads and the cleaner readers of the generated demands and is used for the
  pass-generated edges; it is merged into the outer reader, which triggers
  `addSideEffectRequirement` when refined.
* Zero-to-fact and ND edges keep forward's "can't refine" checks. Demands on
  such edges are concrete (seeds and summary applications), so reads do not
  refine them.

Corrections to the above, found against the code:

* `MethodCallFlowFunction.Default.propagateUnresolvedCallFact` does **not**
  receive `startFactBase`. The backward FF therefore overrides the three
  `propagate*ResolutionFailure` methods, builds the same callbacks as
  `Default` (refinement checks for zero / ND edges, `refineFact` of initial
  and final facts and `SideEffectRequirement` for F2F edges) and calls a
  private `propagateUnresolvedDemand(fact, startFactBase, …)`. The inherited
  `propagateUnresolvedCallFact` is unreachable and throws. The override
  return types are narrowed by `Default` (`Set<CallToReturnZFact>`,
  `Set<FactCallFailureFact>`, `Set<CallToReturnNonDistributiveFact>`).
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
  `InitialFactAp`. It cannot evaluate a `FinalFactAp` demand, so Phase 2a
  added the sibling `TaintPassActionInverseEvaluator` (see "Pass inversion").
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

Not covered by the helper: cleaner checks and inverse pass-through (they live
in the call FF, section 5), aliases.

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

Phase 2a (call FF) status: `JIRBackwardMethodCallFlowFunction` implements
section 5 completely; the sequent FF is still the Phase 1 stub.
`BackwardCallFlowTest` (sample `test.samples.BackwardCallSample`, plus
`StringMethodDataFlowSample`) covers flows that need only the call FF:
`sink(source())`, default-config pass-through on `String`/`StringBuilder`
library calls, a user `CopyMark` pass rule (positive and other-mark
negative), a demand through a callee's argument heap effect (`fill(sb)`
appending a source inside the analysed callee, summarised back to the
caller), argument / result / receiver cleaners and their negatives, a
conditional source turning into a demand on its argument, and negative
cases. Flows through a callee's `return x` (e.g. `x = identity(source())`,
and the Phase 1 `SimpleDataFlowSample` source-reach test, whose `process`
returns its argument) need the sequent FF and stay `@Disabled`.

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

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
| method entry point (`MethodEntryPoint.statement`) | `JMethodEnterInst` | `JMethodExitNormalInst` and `JMethodExitExceptionalInst` (the latter Zero-only) |
| successors of `s` | forward successors | forward predecessors |
| exit point (summary emission) | `JMethodExitNormalInst`/`JMethodExitExceptionalInst` | `JMethodEnterInst` |
| edge at statement `s` | facts **before** `s` executes | facts **after** `s` executes (forward order) |
| flow function at `s` | pre-state → post-state | post-state → pre-state |

Consequences:

* The backward entry-point resolver returns all of the reversed graph's entry
  points, the exceptional exit included. An exceptional entry point
  (`producesExceptionalControlFlow`: `JMethodExitExceptionalInst`, or a `throw`
  for a method without boundary instructions) starts **only the Zero fact**:
  the start FF returns no fact for it (section 2). Rationale below.
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

Observed behaviour of the reversed single-exit graph (verified by the test
harness, see section 10):

* The flow function of a statement runs **before** the engine checks whether
  that statement is an exit point, so the sequent FF at `JMethodEnterInst`
  sees every demand and its output is what becomes the summary. The same holds
  for `JMethodExitNormalInst`: the start FF output is fed to the sequent FF at
  `JMethodExitNormalInst`, which must leave it unchanged.
* Backward successors of `JMethodExitNormalInst` are the method's
  `JIRReturnInst`s. Backward successors of the first real instruction include
  `JMethodEnterInst`. `JMethodEnterInst` has no backward successors.
* Backward successors of `JMethodExitExceptionalInst` are the method's
  `JIRThrowInst`s. Code that only reaches a `throw` (a branch ending in a
  throw, a catch handler that rethrows, a method that always throws) is
  reached backward only from the exceptional exit.
* For a method without boundary instructions (`MethodBoundary.of` returns
  `null`, e.g. the `JMethodBoundaryInstFeature` is not installed) the reversed
  entry points are the forward exit points (`return`/`throw`, throws Zero-only)
  and the summary statement is the first real instruction. The backward
  context then seeds alias analysis with that first instruction; it is `null`
  (alias analysis disabled) when the method has no forward entry at all.
* `MethodInstGraph.build` indexes the boundary instructions like any other
  instruction (they are the last three entries of `instList`), so
  `getInstIndex`/`getInstByIndex` need no special handling.

**Exceptional exit.** Forward analyses every statement reachable from the
method entry, including the ones that only lead to a `throw`: a sink before a
throw is reported. What forward ignores is the exceptional *exit*: summary
edges emitted at `JMethodExitExceptionalInst` (and at a `throw` without
boundary instructions) are filtered by `isApplicableExitToReturnEdge`, so no
fact leaves a method through an exception. The backward mirror is:

* Zero enters at the exceptional exit, so sink seeds on a throwing path are
  created and flow to `JMethodEnterInst`. Their zero-to-fact summaries are
  emitted at `JMethodEnterInst` (not an exceptional statement), so callers
  apply them: a caller argument that reaches a sink inside a callee before the
  callee throws is demanded, as forward reports it.
* No caller demand enters at the exceptional exit (`propagateFact` returns
  nothing there). A caller demand after the call describes a value the callee
  returns normally; forward never propagates a callee fact to the caller along
  an exception. The analyser for the exceptional entry point therefore holds
  only Zero-rooted edges.
* Consequently no demand has the `Exception` base: the `throw x` rule
  (`Exception.P → x.P`) never fires and every other demand passes a `throw`
  unchanged. `isValidMethodExitFact` and the exit → return mapping need no
  change (summaries are still emitted at `JMethodEnterInst` only).
* Code from which no exit is reachable (an infinite loop) is not analysed
  backward. Forward reports nothing for the `infiniteLoop` sample of
  `BackwardRegressionTest` either (not investigated further).

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
| call summary handler | `JIRBackwardMethodCallSummaryHandler` (section 6) |
| side-effect handler | `JIRBackwardMethodSideEffectHandler` (an `object`; interface defaults: no side effects) |
| preconditions | `JIRBackwardMethodStartPrecondition` / `JIRBackwardMethodSequentPrecondition` / `JIRBackwardMethodCallPrecondition` (trivial `object`s, file `JIRBackwardPreconditions.kt`) |
| edge post-processor | the existing `JIRMethodSummaryEdgeProcessor` (direction-neutral compatibility filter) |
| call resolver | the existing `JIRMethodCallResolver` / `JIRCallResolver` |
| findings | `JIRBackwardFindingTracker` |
| rule inversion helpers | `JIRBackwardTaintRules` (sink → demand seeds, source → match) |

Manager details:

* The constructor mirrors `JIRAnalysisManager`:
  `JIRBackwardAnalysisManager(cp, refManager, taintConfig, externalMethodTracker = null, params = JIRAnalysisManager.Params(), recordDemandSeeds = false)`.
  It reuses `JIRAnalysisManager.Params` so both managers satisfy
  `JIRAnalysisManagerBase` with the same `params` type. `recordDemandSeeds`
  enables the `BackwardDemandSeed` debugging records (section 8); the test
  harness turns it on.
* `selectPhase` mirrors forward (`SelectedTaintRulesProvider`,
  `relevantRuleIds`, reset of every context's analysis cache) and additionally
  resets the finding tracker, so the tracker only holds the current phase's
  findings.
* `overApproximateMethodContext` is not overridden (no shallow-scan context
  merging), `isTraceRequiredInstruction` keeps the interface default (`false`).
* The start FF delegates `propagateFact` to the forward
  `JIRMethodStartFlowFunction.propagateFact` (the context type check has no
  side effects), and `propagateZero` returns only `Zero`. At an exceptional
  entry point (the manager passes `producesExceptionalControlFlow(entry)`)
  `propagateFact` returns nothing (section 1).
* The backward context (`JIRBackwardMethodAnalysisContext`) additionally
  carries `forwardEntryPoint` (the forward entry used to seed alias analysis,
  reused for the empty-context analyzer like `localVariableReachability` and
  `aliasAnalysis`) and `findings` (the manager's tracker).
* The backward call FF is **not** cached per statement (forward caches it in
  `JIRMethodAnalysisContext.cachedCallFF`, typed to the forward class). A cache
  can be added to `JIRBackwardMethodAnalysisContext` if construction becomes
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

Implementation: the object delegates to the forward `JIRMethodCallFactMapper`
(`MethodCallFactMapper by JIRMethodCallFactMapper`) and overrides only the
differences: exit → return answers nothing for `Return` (forward maps it to
the call result) and otherwise calls forward; call → start maps a demand on
the result variable to `Return` (type-checked against `returnValue.type`) and
otherwise calls forward; `isValidMethodExitFact` accepts only
`Argument`/`This`/`ClassStatic` (forward accepts every non-local base).
Relevance is forward's.

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
    is a finding, unless the demand came from a caller through the root of an
    argument (below).
  * Zero: seed demands for entry sinks (`sinkRulesForMethodEntry`).

A source match never kills the demand: the demand keeps flowing (to `x` at
`return x`, to the static field at `x = C.f`, unchanged at `JMethodEnterInst`).
Condition demands of a matched source (`SourceMatchResult.conditionDemands`)
are emitted next to it, from the same initial fact. When a source match
refines an abstract demand and nothing is emitted afterwards (`return "c"`,
a void `return`), the refinement is reported as a `Sequent.SideEffectRequirement`
on a fact-to-fact edge, so the engine still creates the concrete initial fact
that the finding needs.

**Entry sources and caller demands.** Forward applies entry-point sources in
`propagateZero` of **every** analysed method, callees included, so the marks
live on zero-to-fact edges. They reach sinks inside the method and its
callees, and leave the method through `Return` and `ClassStatic` facts. At
the exit, `dropArgumentsLocalTaintMarks` removes the marks assigned on method
enter (`taintMarksAssignedOnMethodEnter`) from zero-to-fact facts whose base is
`Argument`/`This`. `TaintMarkRemover` returns `Accept` for any non-mark
accessor, so only a mark directly at the root is removed: `arg0·M` is
dropped, `arg1.sb·M` (the entry mark copied into an argument's field) is kept
and reaches the caller.

Backward sees the same flow from the other end. A backward fact-to-fact edge
starts at the method exit with a demand from a caller (its initial fact), and
an entry-source match at `JMethodEnterInst` on that edge stands for the
forward zero-to-fact fact created at entry that reached the exit as the
initial fact. The finding is therefore recorded unless the initial fact is
based on `Argument`/`This` **and** starts with a mark assigned by an entry
rule of this method (all marks of `sourceRulesForMethodEntry`, like
`taintMarksAssignedOnMethodEnter`). Consequences:

* zero-to-fact edges (sinks inside the method or its callees) always record;
* initial `Return` or `ClassStatic` bases always record (forward keeps them);
* initial `arg.f…·M` records, initial `arg·M` does not;
* a conditional source inside the method can turn the initial `arg·M1` into
  a demand for another mark `M2`; the finding for `M2` is suppressed only if
  `M1` is itself an entry mark, as forward drops `M1` at the root only then;
* a non-distributive edge is suppressed only when every initial fact
  qualifies (backward never creates such edges itself).

Not mirrored: forward's drop also removes an entry mark that a *call* source
inside the method put on an argument root; backward only suppresses entry
source findings.

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
* **Throw** has no rules: `Exception.P → x.P`, other demands unchanged. No
  demand has the `Exception` base (section 1), so in practice every demand
  passes a `throw` unchanged.
* **Entry rules** are matched only when `currentInst is JMethodEnterInst`. A
  method without boundary instructions therefore gets neither entry sinks nor
  entry sources.

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

The sequent FF is complete. Tests, in `core/src/test/kotlin/org/opentaint/jvm/sast/dataflow/backward/`,
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
* No per-statement call FF cache (the FF is cheap to build; its helpers are
  lazy).

**Call-site aliases.** Forward copies the facts a call creates (source
results, pass-through results, summary facts with a memory effect) to every
alias of their base that persists through the call
(`forEachAliasAfterCallStatement`: aliases before the call that are also
aliases after it). Forward only requires the *call local* to be a local
variable; the alias base `z` can be a local, `Argument`, `This` or
`ClassStatic` (`b = C.f` gives `AliasApInfo(ClassStatic, [<C>, f])`), only
`Constant` alias bases are skipped. The backward call FF inverts this on the
demand: for every call local `b` (receiver, arguments, result) and every alias
`AliasApInfo(base = z, accessors = g1..gn)` of `b` persisting through the call
with `z` the demand's base (any base; a demand is never `Constant`), the
demand is read through `g1..gn` (a `FinalFactReader.containsPosition` check
first, so an abstract demand is refined like any other read) and rebased to
`b`. The derived demand then goes through exactly the same processing as the
original one: source matching, cleaners, call-to-start and, on resolution
failure, the keep plus inverse pass-through. This is also what
`JIRMethodCallPrecondition` does for aliased trace facts. A demand irrelevant
to the call itself is still `Unchanged`; its derived demands are processed
next to it. Over-approximation: forward does not alias a fact the call leaves
unchanged (identity summary, unresolved-call keep), while the derived backward
demand is also kept through the call. `b` and `z` are aliases before the call
as well, so this only adds findings that forward misses because it never
aliases an unchanged fact.

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

* `MethodCallFlowFunction.Default.propagateUnresolvedCallFact` receives the
  `startFactBase` of the failed call (added for backward; the forward JIR and
  Go implementations ignore it). The backward FF implements it directly and
  inherits `Default`'s three `propagate*ResolutionFailure` adapters
  (refinement checks for zero / ND edges, `refineFact` of initial and final
  facts and `SideEffectRequirement` for F2F edges).
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

The handler implements `MethodCallSummaryHandler`, with
`mapMethodExitToReturnFlowFact` set to the section 3 exit → return mapping.

`handleSummary` mirrors forward's `JIRMethodCallSummaryHandler.handleSummary`
minus two parts:

* Kept: whenever applying a summary refines the caller's initial fact
  (`initialFactRefinement != null`), it also emits
  `createSideEffectRequirement(refinement)` (a `Sequent.SideEffectRequirement`
  on fact-to-fact edges, nothing on zero / ND edges, where the default
  handlers already require a universe refinement). The requirement is what
  makes the engine refine the caller's own callers; without it a refinement
  learned through a summary stays local to the edge.
* Dropped: call aliases (`applyCallAliases` for summaries with a memory
  effect and in `handleZeroToZero`). Backward inverts call-site aliases in
  the call FF, on the demand before it enters the callee (section 5); the
  summary is already mapped back to the call locals, and aliasing it again
  would duplicate that work in the opposite direction.
* Dropped: `prepareFactToFactSummary` / `prepareNDFactToFactSummary` rewriting
  (`JIRMethodCallRuleBasedSummaryRewriter`), forward-only (section 5).

## 6a. Helper API (`JIRBackwardTaintRules`)

`JIRBackwardTaintRules(apManager, context: JIRBackwardMethodAnalysisContext)`
is a per-flow-function helper (create it lazily in the FF, it holds no state).
It turns rules into demand seeds and demand facts into source findings for
the call FF and the sequent FF.

Result types:

```kotlin
class SinkDemand(
    rule: TaintConfigurationSink,
    condition: TaintMarkAwareConditionExpr?,       // positive condition; null: true, or only negated mark literals
    seeds: List<FinalFactAp>,                      // demands already mapped to the caller/statement
    endRequirement: JIRBackwardEndRequirement?,    // section 12.6
)

sealed interface SourceMatch {
    val rule: TaintConfigurationSource
    val marks: Set<TaintMarkAccessor>              // marks of the matched AssignMark actions
    data class Found(rule, marks)                  // the demand is produced by this source
    data class ConditionDemand(rule, marks, condition, facts: List<FinalFactAp>)  // source needs marks: new demands, mapped
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
| `recordSinkDemands(statement, demands): List<FinalFactAp>` | any | – | skips demands the run does not allow (`acceptsSeed`), records `BackwardSeededSink` and `BackwardDemandSeed` / `BackwardUnconditionalSink` in the tracker and returns the seed facts to emit |
| `matchEndRequirement(statement, fact): FinalFactReader?` | call, `return`, `JMethodEnterInst` | end-requirement targets of the run | records `BackwardEndRequirementReached` (12.6); the reader carries the refinement |

Seeds are built from the positive mark literals of the rewritten
condition after `removeNegated()` (both `And` and `Or` branches, duplicates
removed): `apManager.mkAccessPath(position, ExclusionSet.Universe, mark)`,
i.e. `position·M·$`. A `ContainsMarkOnAnyAccessorLiteral` (a `ContainsMark`
on a position with the `AnyField` modifier) matches, in forward, a fact
holding `M` at any path below the position, the position itself included; it
is seeded as the two demands `position·M·$` and `position.[any]·M·$`. Source
condition demands use the same expansion, but take the exclusions of the
matched demand (`Universe` on zero edges): a `FactToFact` edge rejects a final
fact with `Universe` exclusions, and forward builds facts created on a fact
edge with that fact's exclusions the same way. The caller emits them as `CallToReturnZFact` (call FF) or
`Sequent.ZeroToFact` (sequent FF).

Demand → source match (fact):

| Function | Use at | Demand read as |
|---|---|---|
| `matchCallSources(statement, callExpr, returnValue, callerFact, startBase)` | call FF, for each `(callerFact, startBase)` of the section 3 call → start mapping | `callerFact.rebase(startBase)`; condition demands mapped callee → caller |
| `matchMethodExitSources(statement: JIRReturnInst, fact)` | sequent FF at `return x`, **before** `Return` is rebased to `x` | `fact` as is; condition demands on `Return` rebased to `x` |
| `matchMethodEntrySources(statement, fact)` | sequent FF at `JMethodEnterInst` | `fact` as is (only `Argument`/`This` bases can match) |
| `matchStaticFieldSources(statement: JIRAssignInst, fact)` | sequent FF at `x = C.f` | `fact.rebase(Return)` when `fact.base` is `x` |
| `recordSourceMatches(statement, result)` | any | records one `BackwardSourceFinding` per `(Found, mark)` and one `BackwardConditionalSource` per `ConditionDemand` |
| `recordMethodEntrySourceMatches(statement, result, initialFacts)` | sequent FF at `JMethodEnterInst` | `recordSourceMatches` unless the edge's initial facts all come from a caller through an argument root (section 4) |
| `mapCalleeToCaller(statement, calleeFact): FinalFactAp?` | any call | section 3 exit → return mapping, single result |

Matching uses `evaluateSourceRulePrecondition` with a
`TaintSourceActionPreconditionEvaluator` over a `FinalFactReader`: the demand
must contain `position·M·$` for an `AssignMark(position, M)` of the rule
(`[any]` positions also match their base). Negated mark literals of the source
condition count as satisfied; the remaining positive literals become
`ConditionDemand.facts`. The FF must:

1. call `recordSourceMatches` (`recordMethodEntrySourceMatches` at
   `JMethodEnterInst`) for the findings,
2. emit `conditionDemands` as new demands (`CallToReturnZFact`/`CallToReturn*`
   in the call FF, `Sequent.*ToFact` in the sequent FF),
3. merge `result.reader` into its own reader
   (`factReader.updateRefinement(result.reader)`) when the demand was abstract,
   so the refinement reaches the emitted edges.

A source match does not kill the demand: whether the demand keeps flowing past
the source (e.g. a source that also has a pass-through) is the FF's decision.

Not covered by the helper: cleaner checks and inverse pass-through (they live
in the call FF, section 5), aliases.

Prescan rule registration (zero fact, `Prescan` phase only, results
discarded):

| Function | Called from | Queries |
|---|---|---|
| `registerPrescanCallSources(statement, callExpr, returnValue)` | call FF `propagateZeroToZero` | `sourceRulesForCallStatement` |
| `registerPrescanStatementSources(statement)` | sequent FF `propagateZeroToZero` | `sourceRulesForMethodExit` at `return`, `sourceRulesForMethodEntry` at `JMethodEnterInst`, `sourceRulesForStaticField` at `x = C.f` |

`JIRTaintAnalysisContext.handlePhase` adds the id of every rule it returns in
`Prescan` to `relevantRuleIds` (and then keeps only pass-through rules), and
`selectPhase(ShallowScan / FullScan)` hands that set to
`TaintRulesProvider.selectRules`. Forward queries sinks **and** sources on the
zero fact (call FF `propagateZeroToZero`, start FF `propagateZero`, sequent FF
unconditional sources at `return` and static reads), so both kinds are
registered. Backward matches sources only on demands, and `Prescan` has no
demands (sink rules are filtered out, so no seeds exist), so without these
calls no source id would be recorded and a semgrep-backed provider
(`SemgrepRuleProvider.reduceTaint`, which drops a taint rule whose source
group has no selected id) would drop the rule in the later phases. Cleaner
and pass-through rules are queried on facts only, in forward as well, so they
are not registered on the zero fact in either direction.

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
is kept for every seed emitted by a sink rule when the tracker is created with
`recordDemandSeeds = true` (manager constructor flag, off by default, on in
the test harness). It is a debugging and test aid (the smoke tests assert on
it); it is not a finding, and it would otherwise retain a fact per seed for
the whole run.

API: `addSourceFinding` / `addUnconditionalSink` / `addDemandSeed`, snapshot
getters `sourceFindings()` / `unconditionalSinks()` / `demandSeeds()`, and
`reset()`.

The `TaintAnalyzer` integration (section 12) adds three records and the run
configuration:

```
BackwardSeededSink(methodEntryPoint, statement, rule: TaintConfigurationSink, condition: TaintMarkAwareConditionExpr?, endRequirement: JIRBackwardEndRequirement?)
BackwardConditionalSource(methodEntryPoint, statement, rule: TaintConfigurationSource, marks, condition: TaintMarkAwareConditionExpr)
BackwardEndRequirementReached(statement, rule: TaintConfigurationSink)
```

`configureRun(restrictedTo)` sets the occurrences allowed to seed (`null`: all)
and derives the end-requirement targets per statement; `satisfiedMarks()` and
`vulnerableSinks(checkEndRequirements)` evaluate a run (12.5). The run
configuration survives `reset()`. Storage is `ConcurrentHashMap.newKeySet`, so records are
deduplicated and safe to add from the runner threads. The manager exposes it
as `JIRBackwardAnalysisManager.findings` and resets it in `selectPhase`.

## 9. Out of scope / known limitations

* **Preconditions and trace resolution.** The `get*Precondition` hooks return
  trivial implementations, and backward findings have no traces.
* **Staged pipeline.** `StagedAnalysisRunner` filters traceless findings and is
  sink-oriented, so backward runs drive the engine directly
  (`selectPhase(FullScan())` → `resetApManager` → `runAnalysis`); section 12
  describes the `TaintAnalyzer` integration.
* **Lambdas.** Lambda call resolution relies on forward-flowing type-info facts
  created at the lambda allocation during `Prescan`. Backward cannot produce
  them, so a standalone backward run resolves lambda calls through resolution
  failure (pass-through approximation). Inside `TaintAnalyzer` the backward
  manager replays the lambdas registered by the forward prescan (12.4).
* **Side-effect summaries** are not modelled. `trackFactsReachAnalysisEnd` is
  not modelled by the flow functions; `TaintAnalyzer` emulates forward's
  confirmation with end demands (12.6).
* **Exceptional flow.** As in forward, no fact leaves a method through an
  exception (no `Exception` demands, no summaries from the exceptional exit),
  but the statements that only reach a `throw` are analysed (section 1).
* **Code that reaches no exit** (an infinite loop) is never analysed.
* **Any-field demands.** A `ContainsMarkOnAnyAccessorLiteral` is demanded as
  the star path `x.[any]·M`. No access-path model can express "a path of
  length at least one", so an `Exact` cleaner on `x` cannot be inverted
  precisely on it (section 11).
* **Sinks with only negated mark literals** are recorded as unconditional,
  matching the "negated mark condition is satisfied" convention of
  `removeNegated` in the trace preconditions.
* **Rule selection.** `selectPhase(ShallowScan / FullScan)` calls
  `selectRules(relevantRuleIds)` exactly like forward, and the backward
  `Prescan` records sink and source rule ids (section 6a). A run that skips
  `Prescan` passes an empty set; the test providers ignore `selectRules`, but
  a semgrep-backed provider would then select no rules, so run `Prescan` first
  with such a provider (`BackwardAnalysisTest.runBackwardAnalysis(…,
  stagedRuleSelection = true)` does, with `RuleIdSelectingProvider`, a test
  provider that honours `selectRules`).

## 10. Test harness and tests

Both flow functions are complete (the phase 1 stubs, which handled only the
zero fact, are gone). The tests live in
`core/src/test/kotlin/org/opentaint/jvm/sast/dataflow/backward/`.

* `BackwardAnalysisTest : AnalysisTest` builds
  `JIRSafeApplicationGraph(JApplicationSingleExitGraph(JApplicationGraphImpl(cp, usages)))`,
  reverses it, creates `JIRBackwardAnalysisManager` (with
  `recordDemandSeeds = true`) and `TaintAnalysisUnitRunnerManager` directly
  (`SingleLocationUnit`, `DummySerializationContext`), selects the `ApManager`
  from `apMode` (default `Tree`), and runs `selectPhase(FullScan())` →
  `resetApManager` → `runAnalysis(entry)`. With `stagedRuleSelection = true`
  it wraps the rules provider in `RuleIdSelectingProvider` (drops rules whose
  `serializedId` was not passed to `selectRules`, like the semgrep provider)
  and runs a `Prescan` phase first, followed by `cleanup()`, as
  `StagedAnalysisRunner` does. It returns a `BackwardResult` with the runner
  status, the three tracker lists, the analysed methods and the facts per
  statement. Rule builders, the rules provider and the graph come from
  `AnalysisTest` (`findEntryPoint`, `createRulesProvider`,
  `createAnalysisGraph`, `SingleLocationUnit` are `protected`;
  `functionMatcher` is a companion function, shared with `ForwardSuiteCases`).
* Assertions: `assertSourceReached(config, testCls, entryPointName, sourceMethodName, mark, testName)`
  and `assertNoSourceReached(config, testCls, entryPointName, testName)`.
* `BackwardSmokeTest` on `test.samples.SimpleDataFlowSample#simpleDataFlow`:
  the sink seed is produced once, at the `sink(...)` call, on the caller
  local, with the `tainted` mark, and every callee is entered from its exit; a
  method-entry sink on `sink` is seeded at `JMethodEnterInst` of `sink`, and
  its zero-to-fact summary is mapped back to the caller's argument local; the
  sink demand reaches the source.
* `BackwardCallFlowTest` (sample `BackwardCallSample`, plus
  `StringMethodDataFlowSample`): `sink(source())`, default-config
  pass-through on `String`/`StringBuilder` library calls, a user `CopyMark`
  pass rule (positive and other-mark negative), a demand through a callee's
  argument heap effect, a result demand through a callee's `return x`,
  argument / result / receiver cleaners and their negatives, a conditional
  source turning into a demand on its argument, and negative cases.
* `BackwardSequentFlowTest` and `BackwardSequentFlowFunctionTest`: section 4.2.
* `BackwardRegressionTest` (sample `BackwardRegressionSample`): review
  regressions, each checked against forward on the same config. A sink on a
  branch ending in a throw, inside a callee that always throws, and in a catch
  handler that rethrows (exceptional exit, section 1); the heap effect of a
  callee that always throws does not reach the caller; a sink in a loop with
  no exit (neither direction reports it); call-site aliases rooted at an
  argument, `this`, a local and a static field (section 5); an entry source
  of a callee that does not reach the caller through the argument root, and
  does reach it through an argument field, the return value and a static
  field, and a sink inside the callee (section 4); an exit source on a method
  returning a constant (refinement without an emitted demand); and, with
  `stagedRuleSelection`, call, entry, exit and static-field sources surviving
  the prescan rule selection (section 6a).
* `BackwardForwardDifferentialTest`: section 11.

## 11. Differential validation

### 11.1 Harness

`BackwardForwardDifferentialTest` (`core/src/test/kotlin/org/opentaint/jvm/sast/dataflow/backward/`)
replays the forward end-to-end suites against the backward analysis. The cases
are re-declared, data-driven, in `ForwardSuiteCases` (the forward test classes
are unchanged): every case of `JavaDataFlowReachabilityTest` (including the
`@Disabled` `streamFlatMapFlow`, expected unreachable because forward misses
it), `KotlinDataFlowReachabilityTest`, `MultiReturnDataFlowTest`,
`CleanerDslAnalysisTest` (each parameterised run is one case),
`CleanerDslControlFlowAnalysisTest` and `CleanerFieldSensitivityAnalysisTest`,
with the suite's `useDefaultConfig` and unroll strategy. A case is
`(config, class, entry method, expected sink rule ids)`. Kotlin samples need
no special handling: `sourceFileExtension` only locates source files for SARIF
spans, the classes come from the same samples jar.

* **Sink groups.** A backward finding names a mark, not a sink. The sinks of a
  case are split greedily into groups whose demanded marks are pairwise
  distinct, and backward runs once per group, so a reported mark identifies
  the sink. The run agrees on a sink rule when "backward reports a source
  finding for its mark" equals "forward reports the rule".
* **Forward reference.** Forward runs once per sink rule, with the other sinks
  removed. With all sinks of a call in one config forward reports fewer
  rules: in BaseOnly `cleanThenRetain`, forward reports
  `newSourceAfterCleanSink-m1` alone but not next to the four other rules of
  the same call. In Tree mode forward on the full config is additionally
  checked against the forward suite's expected ids (this guards the
  re-declared configs).
* **Modes.** `Tree` is strict (backward must equal forward). `Automata`,
  `BaseOnly` and `BaseOnlyField` also accept a backward result equal to the
  forward suite's Tree-verified expectation: forward has its own
  mode-specific results there (section 11.4).
* **Divergences** pin the backward value of one `(case, sink rule, modes)` and
  carry the mechanism. An entry is checked to still differ from the
  reference, so a fixed divergence makes the test fail until the entry is
  removed.
* **Evidence cases.** `CleanerStarDualSample` (suite `CleanerStarDualEvidence`)
  is not a forward suite; its three cases isolate the star/Exact-cleaner
  mechanism of section 11.3 in both directions, with forward's actual result
  as the expectation.

Runtime: about one minute per mode (dominated by the per-rule forward runs).

### 11.2 Results

Tree: 631 sink groups; 628 of them come from the 130 forward-suite cases, 3 from the evidence cases.

| | groups |
|---|---|
| agree from the start | 609 |
| fixed (backward bugs, below) | 11 |
| accepted divergences (forward suites) | 8 groups, 18 sink rules |
| evidence cases (all three behave as predicted) | 3 |

Bugs fixed:

1. **Any-field sinks produced no demand** (9 groups:
   `CleanerDslControlFlowAnalysisTest` `sequentialMarks` ×5 and
   `cleanThenRetain`, the `CleanerDslAnalysisTest` helper controls and the
   recursive any-only source). `ContainsMark` on an `AnyField` position is
   rewritten to `ContainsMarkOnAnyAccessorLiteral`, which the seed builder
   skipped. Fix: seed it as `x·M` and `x.[any]·M` (section 6a).
2. **Call-site aliases were not mirrored** (`chainedAppend`, `namedReturn`).
   `sb.append("/").append(b)`: forward taints the intermediate receiver
   `%t` through the pass-through and copies the fact to `sb` because `%t`
   aliases `sb` after the call. The backward demand on `sb` never became a
   demand on `%t`. Fix: section 5, "Call-site aliases".

Accepted divergences (Tree):

| Case | Cause | Verdict |
|---|---|---|
| `JavaDataFlowReachability/lambdaCaptureFlow` | The sink is inside a lambda body reached through `fn.apply` on a captured `Function` parameter. Resolving it needs forward type-info facts (section 9). Verified: backward analyses `lambdaCaptureFlow`, `lambdaCapture`, the local lambda `g` and its body, never the sink lambda, and records no demand seed. | inherent (all modes) |
| `CleanerDsl/matrix-N-AnyField`, `…-AnyField-Plain-AnyField-field-depth0-markK` (5 groups, 15 rules), `CleanerDsl/field-store` `field-store-any`, `CleanerDslControlFlow/sequentialMarks` `sequenceNestedAfterPlainSink-m1` | Star path vs. `Exact` cleaner, section 11.3. Backward misses. | inherent to the access-path models |
| evidence `nestedStoreThenCleanerThenAnySink` | Same, minimal: `value.k.value = source(); applyPlainClean(value); anySink(value)`. Forward reaches, backward does not. | inherent |
| evidence `inlineCleanerThenFieldSink` | The dual: any-field entry fact, `Exact` cleaner in the same method, plain sink on `value.k`. Forward misses (it holds the star fact and the cleaner removes all of it), backward reaches (it demands the concrete `value.k·M`, which the cleaner keeps). `calleeCleanerThenFieldSink`, the same flow with the cleaner inside a callee, is reached by both. | inherent; forward result contradicts its own DSL matrix |

### 11.3 Star paths and `Exact` cleaners

`x.[any]·M` is a star: it covers `x·M` and every `x.f…·M`
(`TreeApManager`: `contains(M)` and `readAccessor` see through `[any]`). The
residual after an `Exact` cleaner `RemoveMark(x, M)`, "`M` below a path of
length at least one", is not representable. `Cleaner.kt`'s `Exact` branch
clears `M` directly after `[any]` and so removes the whole star (unit check:
`clean(arg0.[any]·M, Mark(arg0, M, Exact))` has no survivor in Tree and
Cactus; Automata returns the star unchanged; base-only has no `[any]`).

* Forward meets a star **fact** only from an `AnyField` source, and usually
  not at the cleaner: when the cleaner runs in a summarised callee, the
  callee sees an abstract fact and the summary materialises concrete
  `x.k…·M` paths, which survive. When the cleaner runs in the method that
  holds the star fact, forward loses the whole fact (`inlineCleanerThenFieldSink`).
* Backward meets a star **demand** from every any-field sink, and always
  concretely (seeds are never abstract). An `Exact` cleaner on its base drops
  it in Tree, even when the flow reaches the sink through a concrete field
  (`nestedStoreThenCleanerThenAnySink`, where forward holds
  `value.k.value·M`). In Automata the cleaner keeps the star, and the demand
  then also matches a root-level mark that the cleaner did remove (FP,
  section 11.4).

A precise fix needs a "non-empty star" node in the access-path models, or a
type-driven unrolling of the star at the cleaner.

### 11.4 Access-path modes

**Existing backward suite** (66 tests; the unit test always uses Tree):

| Mode | Result |
|---|---|
| Tree, Automata, Cactus | 66 / 66 |
| BaseOnly | 59 / 66: `fieldOverwrite`, `otherField`, `staticOverwrite`, `selfWriteNegative`, `selfReadNoResurrect` (`BackwardSequentFlowTest`), `cleanedArgument`, `cleanedResult` receiver-cleaner (`BackwardCallFlowTest`) report a finding |
| BaseOnlyField | 63 / 66: `selfWriteNegative`, `cleanedArgument`, `cleanedResult` receiver-cleaner |

Forward on the same configs and mode reports the same flows (BaseOnly:
6 of 7; BaseOnlyField: 3 of 3). The seventh, BaseOnly `staticOverwrite`, has
forward IFDS facts reaching `sink(a)`, and only the trace resolution drops
the vulnerability. Verdict: mode-inherent (field-insensitive access paths
cannot express strong updates, and `P·M` reads as `P.[any]·M`, so
`RemoveMark` never drops it). This confirms the call FF note of section 5.

**Differential in other modes** (631 groups each):

| Mode | Pinned divergences | Agree only with the suite expectation |
|---|---|---|
| Automata | 12 groups: lambda; `streamFlatMapFlow` (backward reaches); `matrix-N-Plain` `Plain-Plain-AnyField-field-depth0` (5 groups, 15 rules) and `sequentialMarks` `…-m1` at 5 checkpoints (backward FP) | `recursive-any-only-depth2` (forward misses) |
| BaseOnly | lambda only | none |
| BaseOnlyField | 13 groups, 21 rules: lambda; `field-store` plain and cleaned; `helperSourceAndCleanerExample-cleaned`; `sequentialMarks` m2–m4 at 6 checkpoints; `cleanThenRetain` m1/m2 at 3 checkpoints (backward FP) | 300 matrix groups (forward FP) |

Mechanisms:

* **Automata star kept.** An `Exact` cleaner leaves the Automata star demand
  unchanged (the self-loop `[any]` graph is returned as is), so the demand
  matches the root mark a `Plain` source produced after the cleaner removed
  it. Verified by the unit check and by the fact dumps.
* **Base-only root demand.** A base-only sink seed is `x·M` with an open
  field tail (`x![M].$/*`); any-field positions collapse to it, because
  `prependAccessor([any])` is absorbed. `Exact` cleaners never remove it,
  the any-field cleaner keeps root marks, and a field write `x.f = v` then
  moves it to `v` (a root `/*` fact starts with every field). Forward
  holds the concrete `x.child·M` after the same write (BaseOnlyField keeps one
  field level), which the any-field cleaner removes and a root sink check
  does not match. Verified by the fact dumps of `cleanThenRetain` and
  `field-store`. Plain BaseOnly has no field level for forward either, so
  both directions agree there.
* **Forward drops what its IFDS facts reach.** Automata `streamFlatMapFlow`
  (the element loop represents `List<List<T>>`) and `recursive-any-only-depth2`:
  forward IFDS facts reach the sink call with the mark, but forward reports
  nothing. Backward reports the flow the forward suite describes as real.
* **BaseOnlyField forward matrix FPs.** Forward reads a field from a root
  `P·M/*` fact and reports plain sources at depth ≥ 1. Backward's
  `containsPosition(P·M)` on the demand `P.k·M` is false, so it agrees with
  the forward suite.

**Cactus** is not part of the committed test: forward cannot run there
(`AccessCactus.equalTo` throws `NotImplementedError` in
`JIRMethodCallSummaryHandler.hasMemoryEffect`, even for `simpleDataFlow`).
Against the forward suite expectation, backward in Cactus disagrees on 24 of
631 groups:

* 3 groups crash (`deepCleanerPipeline`, `starred-depth2/3-sanitized`):
  Cactus summary application leaves an abstract node (`arg(0).*/*`) on a
  zero-to-fact demand, and the method-entry source match then refines a zero
  edge. Verified by dumping the facts without the entry source.
* 21 groups are FN or FP:
  * 9 groups match the Tree divergences of section 11.2: the depth-0
    `AnyField-Plain-AnyField` rule (only for `mark1`), `field-store-any`,
    `sequenceNestedAfterPlainSink-m1` and both evidence cases.
  * `streamFlatMapFlow`: backward reports the flow the forward suite calls a
    known false negative, as in Automata.
  * 11 groups are Cactus-only, which localises them to the Cactus access
    paths because the same backward code agrees with forward in Tree and
    Automata: the `sequentialMarks` checkpoints 0–4, both helper controls,
    `recursive-any-only-root`, `convergentJoinSink-m1`,
    `alwaysCleanReturnSink-m1` and `newSourceAfterCleanSink-m2`. They were not
    root-caused further. One visible difference: the Cactus star does not
    contain its root (`containsPosition(ret·M)` on `ret.[any]·M` is false,
    true in Tree and Automata).

Verdict: the Cactus access paths are unmaintained. Tree and Automata are the
references.

### 11.5 Forward observations

Found while validating; forward is unchanged:

* `inlineCleanerThenFieldSink`: an `Exact` cleaner in the method that holds an
  any-field fact removes the whole star, so a field-level flow that the
  cleaner DSL matrix declares surviving is lost. The result depends on
  whether the cleaner call sits in a summarised callee.
* Forward reports fewer rules when several sink rules share a call statement
  (per-rule runs report more).
* Automata `streamFlatMapFlow` / `recursive-any-only-depth2` and BaseOnly
  `staticOverwrite`: IFDS facts reach the sink, the reported result is empty.
* Cactus forward fails on every summary application with a memory-effect check.

## 12. Integration into TaintAnalyzer

`TaintAnalyzer` (module `opentaint-jvm-sast-dataflow`) runs either the forward
pipeline (the default, unchanged) or a backward pipeline. Trace resolution is
out of scope: every backward vulnerability is returned with
`TracePathGenerationResult.Simple`.

### 12.1 Switch

* `enum AnalysisDirection { FORWARD, BACKWARD }` and
  `TaintAnalyzerOptions.analysisDirection`. The default is
  `AnalysisDirection.fromEnvironment()`: the system property
  `opentaint.analysis.direction`, else the environment variable
  `OPENTAINT_ANALYSIS_DIRECTION` (case-insensitive, blank means unset), else
  `FORWARD`. An unknown value fails fast.
* Gradle: `configureDefaultTest` (`opentaint-common-build`,
  `DefaultConfiguration.kt`) forwards the Gradle property
  `-Popentaint.analysis.direction=…`, or the environment variable, to the test
  JVM as that system property, and declares it as a task input, so switching
  the direction re-runs the tests instead of reusing up-to-date results. Both
  `./gradlew :test --tests 'org.opentaint.jvm.*' -Popentaint.analysis.direction=backward`
  and `OPENTAINT_ANALYSIS_DIRECTION=backward ./gradlew …` work (verified: the
  test XML contains the backward pipeline log lines).
* A manager that is not `BackwardCapableTaintAnalysisManager` (Go) falls back
  to forward with a warning, so a globally set variable does not break other
  languages.
* Tests: `AnalysisTest.analysisDirection` (default: the environment) and a
  `direction` parameter of `AnalysisTest.runAnalysis`. The backward test
  classes (`BackwardAnalysisTest` subclasses) pin `FORWARD`, because they use
  `runAnalysis` as the forward reference. `AbstractSarifGeneratorTest` skips
  itself (JUnit assumption) in backward mode: SARIF code flows need traces.

### 12.2 Generic API (`opentaint-dataflow`, `BackwardTaintAnalysisManager.kt`)

```kotlin
interface BackwardCapableTaintAnalysisManager { fun createBackwardAnalysisManager(): BackwardTaintAnalysisManager }
interface BackwardTaintAnalysisManager : TaintAnalysisManager {
    fun prepareRun(run: BackwardRun)          // after selectPhase(FullScan), before resetApManager/runAnalysis
    fun runResult(): BackwardRunResult        // after runAnalysis
}
data class BackwardSinkOccurrence(rule: CommonTaintConfigurationSink, statement: CommonInst)
sealed interface BackwardRun { analysisEndMethods; Discovery; Restricted(occurrences) }
class BackwardRunResult(seeded: Map<Occurrence, Set<TaintMarkAccessor>>, vulnerable: Map<Occurrence, MethodEntryPoint>, exact: Boolean)
```

The test harnesses build anonymous `TaintAnalyzer`s whose `analysisManager()`
returns a `JIRAnalysisManager`, so the backward manager is derived from the
forward one: `JIRAnalysisManager.createBackwardAnalysisManager()` creates a
`JIRBackwardAnalysisManager` that shares the taint rules provider, the
`relevantRuleIds` set (filled by the forward prescan), `params`, the
`externalMethodTracker` and the lambda registry (12.4). The backward graph is
`analysisGraph().reversed`.

### 12.3 Pipeline (`TaintAnalyzer.analyzeBackward`)

1. Forward prescan, exactly as in forward mode (forward engine, forward
   manager, `Prescan`, `TreeApManager(AnyAccessorDisabled)`, 30% of the
   timeout). It records the relevant rule ids and the lambda resolutions. The
   forward engine is then `cleanup()`-ed; the shared data lives in the
   managers. The backward `Prescan` is not run.
2. A separate backward engine (`TaintAnalysisUnitRunnerManager` with the
   backward manager, the reversed graph, the same unit resolver and
   `DummySerializationContext`). Every backward run is
   `selectPhase(FullScan)` (rule selection from the shared ids, context caches
   and findings reset) → `prepareRun` → `resetApManager(apManager)` →
   `runAnalysis(entry methods)`.
3. Discovery, grouped runs, isolated runs (12.5). The budget is 90% of
   `ifdsTimeout` from the analysis start. Discovery gets half of what is left
   after the prescan. Grouped runs share the rest evenly (half of it when some
   group has several members, to leave time for isolation), isolated runs
   share what is left after them. A run that times out keeps its partial
   result: the attribution is monotone in the facts found, so a partial
   "vulnerable" is final. When no time is left, unchecked groups keep their
   discovery verdict and unchecked isolation candidates are kept, mirroring
   forward, which keeps unconfirmed vulnerabilities when no time is left for
   confirmation.
4. Result: one `TaintVulnerability(statement, rule.id, {rule → Unconditional(methodEntryPoint)})`
   per reported occurrence, merged by `(rule.id, statement)` like
   `TaintAnalysisUnitStorage`; the vulnerability summary and the
   `analysisCwe` filter are applied as in forward. Not done in backward mode:
   summary storing, `confirmVulnerabilities` (emulated, 12.6) and trace
   generation.
5. Status: the first non-`OK` status of the forward (prescan) and backward
   engines (an engine keeps its first failure over all runs); trace
   resolution status `OK`.

### 12.4 Lambdas (`JIRLambdaRegistry`)

Forward resolves a lambda call from the type-info facts created at the lambda
allocation in `Prescan` (`TypeInfoSequentFlowFunction`,
`JIRMethodCallResolver.tryExtractLambdaType`) and stores the lambda classes in
a per-context `JIRMethodAnalysisContext.lambdaCallResolution` tracker.
`JIRLambdaRegistry` is a manager-level map `(caller method, instruction index)
→ lambda classes`. The forward resolver additionally registers every lambda it
adds to a tracker; forward behaviour is unchanged (the registry is write-only
there). The backward resolver (`replayRegisteredLambdas = true`) resolves a
lambda call to the lambdas registered for that call site: it keeps the
resolution failure (as forward does) and calls `handleResolvedMethodCall` for
each registered lambda. The registry is complete after the prescan, because
forward only extracts lambda types in `Prescan`. It merges all contexts of a
method (an over-approximation of forward's per-context trackers). A backward
manager built without a registry (the backward unit tests) keeps the previous
behaviour. This fixes the `lambdaCaptureFlow` divergence of 11.2 in the
pipeline (`BackwardPipelineTest`).

### 12.5 Sink attribution

Demands carry marks only, so a source finding does not say which sink
demanded it. Encoding the sink in the mark name is rejected (callee
abstraction refines on the rule's mark accessor, so a renamed mark silently
misses source matches). Attribution is done by restricting the seeds.

* **Occurrence**: `(sink rule, sink statement)`, recorded
  (`BackwardSeededSink`) whenever a call, method-exit or method-entry sink is
  seeded and its condition is not constant-false. It keeps the positive
  condition (`removeNegated()`, negated literals count as true like forward;
  `null` = unconditional) and the end requirement (12.6). The method entry
  point is kept as information only: seeds of the same statement from the
  normal and the exceptional exit analyzers, or from several contexts, are
  the same occurrence. Its demanded marks are the positive condition marks
  plus the end-requirement mark.
* **Satisfied marks** (per run, `JIRBackwardFindingTracker.satisfiedMarks`):
  the marks of all `BackwardSourceFinding`s, closed under the conditional
  sources: a `BackwardConditionalSource` (a source whose condition needs marks,
  matched by a demand for one of its marks, recorded next to its condition
  demands) adds its marks once its positive condition holds. Fixpoint over
  marks.
* **Vulnerable**: the positive condition holds under the satisfied marks
  (evaluated directly on the And/Or tree, equivalent to the DNF cube check)
  and, in restricted runs, the end requirement holds (12.6).
* **Discovery run**: every occurrence is seeded, no end demands. It
  enumerates the occurrences and their marks. Its verdict is final only when
  a single occurrence was seeded and it has no end requirement (`exact`).
* **Why discovery is not a candidate filter** (deviation from the initial
  design, which isolated only the discovery positives): discovery is not an
  over-approximation of the isolated runs. Demands of different sinks with the
  same mark merge in one access path; in `Tree` the star `x.[any]·M` of an
  any-field sink absorbs the concrete `x.f·M` of a plain sink, and an `Exact`
  cleaner then removes the whole star (11.3), so the plain sink's flow is lost
  only when both are seeded together. Measured: the `CleanerDslAnalysisTest`
  matrix found 0 of 220 occurrences in discovery, while each occurrence alone
  is found (the same effect is why the 11.1 differential runs mark-disjoint
  sink groups).
* **Grouped runs** (`BackwardRun.Restricted`): the occurrences are split
  greedily (deterministic order: method, instruction index, rule id) into
  groups with pairwise disjoint demanded marks, as the 11.1 differential does.
  `JIRBackwardFindingTracker.acceptsSeed` lets only the group's occurrences
  seed; the others are neither seeded nor recorded. A single-member group is
  final. The positives of a larger group become candidates for isolation:
  marks are disjoint, but a conditional source can still turn one member's
  demand into a demand for another member's mark.
* **Isolated runs**: a restricted run with one candidate; its verdict is
  final.
* Runs: 1 discovery + one per group + one per positive of a multi-member
  group. Occurrences of the same rule share marks, so in practice every
  occurrence gets its own run.

Precision limit (mark level): satisfied marks are global to a run. A condition
with two literals on the same mark at different positions is satisfied when
either position reaches a source.

### 12.6 End-fact requirements (`trackFactsReachAnalysisEnd`)

Forward reports such a sink as `WithRequirement` with the facts its
`trackFactsReachAnalysisEnd` actions create after the sink, and
`VulnerabilityChecker` drops it when those facts cannot reach the analysis end
uncleaned. `VulnerabilityChecker` confirms a fact that reaches its method's
exit as a non-summary fact (a local), follows summary facts (`Argument`,
`This`, `Return`, `ClassStatic`) to the callers, confirms at a method without
callers, and treats a user-rule cleaner drop as a kill.

`JIRBackwardEndRequirement.of(rule, statement)` computes the required fact
like forward: call sinks evaluate the actions with
`TaintSourceActionEvaluator(Universe)` and map them with the **forward**
exit → return mapping, exit and entry sinks keep them unmapped. As in forward,
only a single required fact is checked (`requiredFacts.size != 1` is
`UNKNOWN`, kept); the requirement records the fact, its position rebased to
the mapped base, and its mark.

Emulation in restricted runs (`JIRBackwardAnalysisManager.endDemands`, emitted
by the start flow function as zero-to-fact facts at the **normal** exit):

* a `ClassStatic` requirement is demanded at the exit of the analysis entry
  methods (the `runAnalysis` start methods);
* any other requirement is demanded, rebased to every local variable, at the
  exit of **every** analysed method (forward confirms a local that reaches
  its method end), and additionally rebased to every argument, `this` and
  `Return` at the exit of the analysis entry methods (forward confirms summary
  facts at a method without callers). Demands on arguments and `Return` of
  other methods come from their callers through the ordinary call mapping.
* The demands flow backward like any other; cleaners drop them.
* At the occurrence's statement (the call FF for call sinks, the sequent FF at
  `return` for exit sinks and at `JMethodEnterInst` for entry sinks), a demand
  whose base is the requirement's base and that contains the requirement's
  position and mark records `BackwardEndRequirementReached`. The demand there
  is the state after the statement, i.e. forward's fact after the sink. The
  match is statement-local, so it is exact even when many sinks share marks;
  an abstract demand is refined through the reader like a source match.

Not mirrored: forward also confirms facts that reach an exceptional exit, and
the discovery run does not check requirements (it is never final when a
requirement exists).

### 12.7 Measured results (Phase 1)

Commands (from `core/`): `./gradlew :test --tests 'org.opentaint.jvm.*'` and
`./gradlew :opentaint-java-querylang:test`, with and without
`-Popentaint.analysis.direction=backward` (the core run in backward mode used
`OPENTAINT_ANALYSIS_DIRECTION=backward` to exercise the environment path);
results parsed from the JUnit XML.

| Suite | Forward before | Forward after | Backward |
|---|---|---|---|
| `org.opentaint.jvm.*` | 1671 tests, 0 failed, 8 skipped | 1676 tests, 0 failed, 8 skipped | 1676 tests, 10 failed, 30 skipped (8 + 22 SARIF) |
| `opentaint-java-querylang` | 207 tests, 0 failed, 23 skipped | 207 tests, 0 failed, 23 skipped | 207 tests, 4 failed, 23 skipped |

The five extra core tests are `BackwardPipelineTest`. Test time (sum of the
JUnit suite times): core 71 s backward vs 69 s forward (dominated by the
differential tests, which pin forward), querylang 23.5 s in both directions.
No run in either suite logged a runner exception, an IFDS timeout or a
budget exhaustion.

Infrastructure bugs found and fixed while measuring: the discovery run as a
candidate filter (12.5, lost the whole `CleanerDslAnalysisTest` matrix), end
requirements on locals (12.6, `ExampleTest` "cleaner after sink 1", "rule
pattern-not with signature", "rule with several suffix cleaners", "rule with
pattern-not-inside suffix" reported their negatives) and condition demands
with `Universe` exclusions on fact edges (6a, aborted the run with
"Incorrect FactToFact edge exclusion"; `ExampleTest` "test nd rule" missed
its positive, `IssuesTest` and "RuleWithEllipsisInvocationAndPatternNot"
aborted silently).

Backward failures by cause (inputs for Phase 2):

1. **Star demand and `Exact` cleaner** (11.3, inherent to the access-path
   models; exactly the 11.2 accepted divergences). FN.
   `CleanerDslAnalysisTest` "plain and AnyField matrix … (1..5 marks)" (only
   `AnyField-Plain-AnyField-field-depth0-markK`), "field stores distinguish a
   plain cleaner from an AnyField cleaner" (`field-store-any`),
   `CleanerDslControlFlowAnalysisTest` "marks are accumulated and removed
   independently in a long sequence" (`sequenceNestedAfterPlainSink-m1`).
2. **Automata any-field cleaner keeps the demand** (11.4 "Automata star
   kept"). FP, Automata only (the Tree variants pass).
   `AutomataDeepCleanSummaryAnalysisTest` "clean plus depth-2 constant store
   returns a silent object", "in-helper starred clean silences the read in
   the same summary", "in-helper nested starred clean silences the read"
   (starred `AnyField` cleaner, plain sink).
3. **User-rule summary rewriting not mirrored** (section 5,
   `JIRMethodCallRuleBasedSummaryRewriter`). FP. `ExampleTest` "test
   RuleReturnWithNotInsideSignature" and `CustomTest` "test
   RuleReturnWithNotInsideSignature str concat" (`Negative`: `return clean(o)`
   in an `@EntryPoint` method, method-exit sink on the entry mark). `clean` is
   analysed project code and carries a conditional semgrep source whose
   `relevantTaintMarks` include the entry mark; forward drops that mark from
   `clean`'s pass-through summary, backward walks through `clean`'s body
   (`return o`) back to the entry source.
4. **Cleaner condition on another position than the demand** (section 5,
   "cleaner condition"). FP. `ExampleTest` "test tricky pattern not"
   (`TrickyPatterNot$NegativeSimple`: `c = clean(s); return c`, method-exit
   sink). The semgrep cleaner on `clean` removes the mark from `arg0` and
   `Result` under `ContainsMark(arg0, M)`; the backward demand is on
   `Result`, so the condition evaluates to false on it and the demand passes
   (into `clean`'s body, cause 3, and on to `src()`).
5. **Entry sources on `ClassStatic` are not matched.** FN.
   `TypeAwarePatternTest` "test generic type args in method parameter"
   (`RuleWithGenericTypeArgs$PositiveMatchingGenericParam`): the semgrep
   `EntryPoint` rule assigns the state mark to the `ClassStatic` state
   variable (condition: parameter type `Map<String, Object>`), the sink
   demands it, but `JIRBackwardTaintRules.matchMethodEntrySources` returns
   early for any base other than `Argument`/`This`.

Other forward/backward differences noticed, not covered by a failing test:
forward fires method-entry sinks only for constant-true conditions and
method-exit sinks only on zero-to-fact edges (`JIRMethodExitRuleProvider`)
and never unconditionally; backward seeds all of them.

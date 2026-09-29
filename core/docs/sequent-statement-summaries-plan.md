# Sequent flow function via per-statement summaries — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Rewrite the JVM sequent flow function so exit rules live on the method-exit boundary instructions and fact transfer is driven by precomputed per-statement `InitialFactAp -> InitialFactAp` summaries applied with delta + concat.

**Architecture:** A statement is translated once into a `JIRStatementSummary` (edges + per-base type filters). The cached `JIRMethodSequentFlowFunction` applies the edges to an incoming fact with `MethodSummaryEdgeApplicationUtils.tryApplySummaryEdge` and the new `InitialFactAp.concat(typeChecker, FinalFactAp.Delta)`, then runs exit rules on `JMethodExitNormalInst` / `JMethodExitExceptionalInst`.

**Tech Stack:** Kotlin, Gradle (`core/` root build, included build `opentaint-dataflow-core`), JUnit 5 / kotlin.test.

**Spec:** `core/docs/sequent-statement-summaries.md` (read it first).

## Global Constraints

- Branch `saloed/sequent-summaries`; commit after every task; commit messages end with
  `Co-Authored-By: Claude Opus 5.5 (1M context) <noreply@anthropic.com>`.
- No comments in production source (rationale goes to the spec / commit messages).
- Match surrounding code style; public visibility is fine.
- Success = no per-test outcome change against the baseline (JVM 324 tests / 0 failed / 8 skipped,
  querylang 207 / 0 / 23, opentaint-dataflow 148 / 0, opentaint-jvm-dataflow 96 / 0) plus the new unit tests.
- Suite runner (≈20 min, run in background):
  `/tmp/claude-1002/-drive-testcomp-opentaint-go-rules-opentaint/2ef11665-476f-4ee2-ba20-29c3b650080d/scratchpad/seq/suites.sh <label>`
  then compare:
  `python3 /tmp/claude-1002/-drive-testcomp-opentaint-go-rules-opentaint/2ef11665-476f-4ee2-ba20-29c3b650080d/scratchpad/seq/compare.py baseline <label>`
  (`differences=0` is the pass condition; new unit tests show up as `- -> PASS`).
- Quick module test runs from `core/`:
  `./gradlew :opentaint-dataflow-core:opentaint-dataflow:test --tests '<pattern>'` and
  `./gradlew :opentaint-dataflow-core:opentaint-jvm-dataflow:test --tests '<pattern>'`
  (Go-dependent tasks need `PATH=/tmp/claude-1002/-drive-testcomp-opentaint-go-rules-opentaint/2ef11665-476f-4ee2-ba20-29c3b650080d/scratchpad/protoc/bin:$PATH`, the suite script sets it).

Path prefixes used below:
- `DF` = `core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/ap/ifds`
- `DFT` = `core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/ap/ifds`
- `JDF` = `core/opentaint-dataflow-core/opentaint-jvm-dataflow/src/main/kotlin/org/opentaint/dataflow/jvm/ap/ifds`
- `JDFT` = `core/opentaint-dataflow-core/opentaint-jvm-dataflow/src/test/kotlin/org/opentaint/dataflow/jvm`
- `JSAMPLES` = `core/opentaint-dataflow-core/opentaint-jvm-dataflow/samples/src/main/java`

## Review Focus

- Abstract incoming facts (`y.*`) on a field read must still trigger the `y.f.*` initial-fact refinement (FN risk) — pinned by the `x = y.f` edge set in Task 4 and the end-to-end suites in Task 5.
- `x = x.f`: concrete `x.g` must be killed and an abstract `x.*` must still request `x.f.*` — pinned by the composed kill edge `x/{f} -> ⊥` in Task 4 and its `SideEffectRequirement` emission in Task 5.
- Exit-sink vulnerabilities recorded on a boundary instruction: trace confirmation and SARIF location must not crash or lose the location — covered by Task 3 (`MultiReturnDataFlowTest`, SARIF exit-sink tests, querylang requirement sinks).
- Lambda / Spring generated methods must behave like ordinary methods after gaining boundaries — Task 2 probe + suites.
- Concurrent trace workers reading the cached flow function — Task 5 uses a synchronized cache and an immutable lazily-built summary.

---

### Task 1: `InitialFactAp.concat(typeChecker, FinalFactAp.Delta)`

**Files:**
- Modify: `DF/access/FactAp.kt` (interface `InitialFactAp`)
- Modify: `DF/access/tree/AccessPath.kt`
- Modify: `DF/access/automata/AccessGraphInitialFactAp.kt`
- Modify: `DF/access/cactus/AccessPathWithCycles.kt`
- Test: `DFT/access/InitialConcatFinalDeltaTest.kt` (create)

**Interfaces:**
- Produces: `fun InitialFactAp.concat(typeChecker: FactTypeChecker, delta: FinalFactAp.Delta): FinalFactAp?`
  — the result has the base and exclusions of the receiver; `null` when the type checker rejects the graft.

- [ ] **Step 1: Write the failing test**

```kotlin
package org.opentaint.dataflow.ap.ifds.access

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.access.automata.AutomataApManager
import org.opentaint.dataflow.ap.ifds.access.tree.TreeApManager
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.RefManager
import kotlin.test.Test
import kotlin.test.assertEquals

class InitialConcatFinalDeltaTest {
    private val x = AccessPathBase.LocalVar(1)
    private val y = AccessPathBase.LocalVar(2)
    private val a = FieldAccessor("C", "a", "C")
    private val b = FieldAccessor("C", "b", "C")
    private val c = FieldAccessor("C", "c", "C")

    private object UnrollStrategy : AnyAccessorUnrollStrategy {
        override fun unrollAccessor(accessor: Accessor): Boolean = false
    }

    private fun managers(): List<ApManager> = listOf(
        TreeApManager(UnrollStrategy, RefManager(), Cancellation()),
        AutomataApManager(UnrollStrategy, Cancellation()),
    )

    private fun ApManager.concrete(base: AccessPathBase, vararg path: Accessor): FinalFactAp =
        path.foldRight(createFinalAp(base, ExclusionSet.Empty)) { acc, f -> f.prependAccessor(acc) }

    private fun ApManager.abstractFinal(base: AccessPathBase, vararg path: Accessor): FinalFactAp =
        path.foldRight(mostAbstractFinalAp(base).replaceExclusions(ExclusionSet.Empty)) { acc, f -> f.prependAccessor(acc) }

    private fun ApManager.initial(base: AccessPathBase, vararg path: Accessor): InitialFactAp =
        path.foldRight(mostAbstractInitialAp(base)) { acc, f -> f.prependAccessor(acc) }

    @Test
    fun `node delta is grafted under the initial path`() {
        for (m in managers()) {
            val fact = m.concrete(x, a, b)
            val delta = fact.delta(m.initial(x, a)).single()
            val result = m.initial(y, c).concat(FactTypeChecker.Dummy, delta)
            assertEquals(m.concrete(y, c, b).toString(), result.toString(), m::class.simpleName)
        }
    }

    @Test
    fun `empty delta yields the abstract initial path`() {
        for (m in managers()) {
            val fact = m.abstractFinal(x, a)
            val delta = fact.delta(m.initial(x, a)).single { it.isEmpty }
            val result = m.initial(y, c).concat(FactTypeChecker.Dummy, delta)
            assertEquals(m.abstractFinal(y, c).toString(), result.toString(), m::class.simpleName)
        }
    }

    @Test
    fun `root initial concat keeps the whole delta`() {
        for (m in managers()) {
            val fact = m.concrete(x, a, b)
            val delta = fact.delta(m.initial(x)).single()
            val result = m.initial(y).concat(FactTypeChecker.Dummy, delta)
            assertEquals(m.concrete(y, a, b).toString(), result.toString(), m::class.simpleName)
        }
    }
}
```

- [ ] **Step 2: Run test to verify it fails**

Run (from `core/`): `./gradlew :opentaint-dataflow-core:opentaint-dataflow:test --tests '*InitialConcatFinalDeltaTest*'`
Expected: compilation FAIL, `concat` with two arguments is unresolved on `InitialFactAp`.

- [ ] **Step 3: Implement**

`FactAp.kt`, in `interface InitialFactAp` after `fun concat(delta: Delta): InitialFactAp`:

```kotlin
    fun concat(typeChecker: FactTypeChecker, delta: FinalFactAp.Delta): FinalFactAp?
```

`AccessPath.kt` (tree). Import `org.opentaint.dataflow.ap.ifds.access.tree.AccessTree.AccessNode.Companion.createAbstractNodeFromAccessors` and `it.unimi.dsi.fastutil.ints.IntArrayList` (already imported); add:

```kotlin
    override fun concat(typeChecker: FactTypeChecker, delta: FinalFactAp.Delta): FinalFactAp? {
        val node = with(apManager) {
            createAbstractNodeFromAccessors(access?.toList() ?: IntArrayList())
        }
        return AccessTree(apManager, base, node, exclusions).concat(typeChecker, delta)
    }
```

(`AccessTree.concat` grafts a `NodeAccessTreeDelta` at the abstract leaf through
`concatToLeafAbstractNodes`, so type filtering and access limits match summary application; an
`EmptyAccessTreeDelta` keeps the abstract leaf and merges the deep exclusion.) If
`createAbstractNodeFromAccessors` is not reachable as imported, call it the way
`MethodInitialToFinalApSummaries.kt:131-136` does (`with(apManager) { ... }`).

`AccessGraphInitialFactAp.kt` (automata):

```kotlin
    override fun concat(typeChecker: FactTypeChecker, delta: FinalFactAp.Delta): FinalFactAp? =
        AccessGraphFinalFactAp(base, access, exclusions).concat(typeChecker, delta)
```

`AccessPathWithCycles.kt` (cactus — its initial fact is a stub, the manager is not reachable):

```kotlin
    override fun concat(typeChecker: FactTypeChecker, delta: FinalFactAp.Delta): FinalFactAp? =
        error("Cactus initial fact does not support final delta concat")
```

- [ ] **Step 4: Run test to verify it passes**

Run: `./gradlew :opentaint-dataflow-core:opentaint-dataflow:test --tests '*InitialConcatFinalDeltaTest*'`
Expected: PASS (3 tests). If a `toString` comparison differs only in exclusion rendering, compare with
`replaceExclusions(ExclusionSet.Empty)` on both sides — the operation's contract is the access part.

- [ ] **Step 5: Run the whole module and commit**

Run: `./gradlew :opentaint-dataflow-core:opentaint-dataflow:test` → 151 tests, 0 failed.

```bash
git add core/opentaint-dataflow-core/opentaint-dataflow
git commit -m "feat(dataflow): concat a final-fact delta onto an initial fact"
```

---

### Task 2: Boundary instructions for generated methods

Generated methods override `instList` with a list built by `JIRInstListBuilder` and skip the
`JIRInstExtFeature` pipeline, so they have no `JMethodEnterInst` / `JMethodExitNormalInst` /
`JMethodExitExceptionalInst` (measured: 170 `JIRLambdaMethod` graphs in the reachability tests).

**Files:**
- Modify: `JDF/LambdaAnonymousClassFeature.kt` (`OpentaintLambdaProxyMethod` ~line 303, `JIRLambdaMethod` ~line 360)
- Modify: `core/src/main/kotlin/org/opentaint/jvm/sast/project/spring/SpringGeneratedMethod.kt`

**Interfaces:**
- Produces: every analysed method's `instList` ends with Enter / ExitNormal / ExitExceptional (non-empty lists).

- [ ] **Step 1: Check the lists are complete before first `instList` access**

Run: `grep -n "instList" core/opentaint-dataflow-core/opentaint-jvm-dataflow/src/main/kotlin/org/opentaint/dataflow/jvm/ap/ifds/LambdaAnonymousClassFeature.kt core/src/main/kotlin/org/opentaint/jvm/sast/project/spring/*.kt`
Expected: no read of `instList` of a method whose builder is still being filled. If there is one,
switch that read to the builder (`instructions`) instead.

- [ ] **Step 2: Add a temporary probe (not committed)**

In `core/opentaint-utils/opentaint-jvm-util/src/main/kotlin/org/opentaint/jvm/graph/JApplicationSingleExitGraph.kt` replace
`private val boundary by lazy { MethodBoundary.of(graph.method) }` with

```kotlin
        private val boundary by lazy { MethodBoundary.of(graph.method).also { if (it == null) System.err.println("BOUNDARY-PROBE missing: " + graph.method::class.java.simpleName + " " + graph.method) } }
```

Run (from `core/`, protoc on PATH): `./gradlew :test --tests '*KotlinDataFlowReachabilityTest*' --tests '*JavaDataFlowReachabilityTest*'`
then `grep -rhoE "BOUNDARY-PROBE missing: [A-Za-z]+" build/test-results/test | sort | uniq -c`
Expected: `170 BOUNDARY-PROBE missing: JIRLambdaMethod` (the failing state).

- [ ] **Step 3: Implement**

In both lambda method classes and in `SpringGeneratedMethod`, replace
`override val instList: JIRInstList<JIRInst> get() = instructions` with

```kotlin
    override val instList: JIRInstList<JIRInst> by lazy {
        JMethodBoundaryInstFeature.transformInstList(this, instructions)
    }
```

and add `import org.opentaint.jvm.graph.JMethodBoundaryInstFeature`.

- [ ] **Step 4: Re-run the probe**

Same command as Step 2. Expected: no `BOUNDARY-PROBE` lines. Then revert the probe:
`git checkout core/opentaint-utils/opentaint-jvm-util/src/main/kotlin/org/opentaint/jvm/graph/JApplicationSingleExitGraph.kt`

- [ ] **Step 5: Suites and commit**

Run `suites.sh task2` (background), then `compare.py baseline task2`. Expected: `differences=0`.
If differences appear, report them with the failure messages before changing anything else.

```bash
git add core/opentaint-dataflow-core/opentaint-jvm-dataflow/src/main/kotlin/org/opentaint/dataflow/jvm/ap/ifds/LambdaAnonymousClassFeature.kt core/src/main/kotlin/org/opentaint/jvm/sast/project/spring/SpringGeneratedMethod.kt
git commit -m "fix(jvm): add method boundary instructions to generated methods"
```

---

### Task 3: Exit rules on the exit boundary instructions

**Files:**
- Modify: `JDF/MethodFlowFunctionUtils.kt` (new helper)
- Modify: `JDF/analysis/JIRMethodSequentFlowFunction.kt`
- Modify: `JDF/trace/JIRMethodSequentPrecondition.kt`
- Modify: `DF/trace/MethodForwardTraceResolver.kt` (`resolveForwardTrace`, ~line 104)
- Modify: `core/src/main/kotlin/org/opentaint/jvm/sast/sarif/JirSarifGenerator.kt` (`statementLocation`, ~line 216)

**Interfaces:**
- Produces: `fun JIRInst.methodExitBase(): AccessPathBase?` in `MethodFlowFunctionUtils`
  — `AccessPathBase.Return` for `JMethodExitNormalInst`, `AccessPathBase.Exception` for
  `JMethodExitExceptionalInst`, `null` otherwise.

- [ ] **Step 1: Helper**

In `MethodFlowFunctionUtils` add (imports `org.opentaint.ir.api.jvm.cfg.JIRInst`,
`org.opentaint.jvm.graph.JMethodExitNormalInst`, `org.opentaint.jvm.graph.JMethodExitExceptionalInst`):

```kotlin
    fun JIRInst.methodExitBase(): AccessPathBase? = when (this) {
        is JMethodExitNormalInst -> AccessPathBase.Return
        is JMethodExitExceptionalInst -> AccessPathBase.Exception
        else -> null
    }
```

- [ ] **Step 2: Flow function**

In `JIRMethodSequentFlowFunction`:

1. `propagate(...)`: `JIRReturnInst` / `JIRThrowInst` become plain transfers and the exit boundaries run the rules:

```kotlin
        when (currentInst) {
            is JIRAssignInst -> { /* unchanged */ }

            is JIRReturnInst -> {
                val access = currentInst.returnValue?.let { accessPathBase(it) }
                simpleAssign(AccessPathBase.Return, access, factAp, { unchanged() }) {
                    propagateFact(it, TraceInfo.Flow)
                }
            }

            is JIRThrowInst -> {
                val access = accessPathBase(currentInst.throwable)
                simpleAssign(AccessPathBase.Exception, access, factAp, { unchanged() }) {
                    propagateFact(it, TraceInfo.Flow)
                }
            }

            else -> {
                val exitBase = currentInst.methodExitBase()
                if (exitBase == null) {
                    unchanged()
                } else {
                    propagateExitFact(initialFacts, exitBase, factAp, unchanged, propagateFactWithRefinement, sideEffect)
                }
            }
        }
```

2. `propagateExitFact`: drop the `access` parameter and the `simpleAssign` block; the start is

```kotlin
        val refiner = FactRefiner()
        val resultFacts = mutableListOf<Pair<FinalFactAp, TraceInfo>>()
        resultFacts += factAp to TraceInfo.Flow
        resultFacts += applyMethodExitSourceRules(exitBase, factAp, refiner)
```

   followed by the existing worklist loop unchanged (it already emits `unchanged()` when the fact is
   unchanged).
3. `applyUnconditionalSinks`: `if (currentInst !is JMethodExitNormalInst) return`.
4. `applyUnconditionalSources`: `if (currentInst is JMethodExitNormalInst) { ...exit sources... }`.

- [ ] **Step 3: Precondition**

In `JIRMethodSequentPrecondition.factPrecondition`:

```kotlin
        val exitBase = currentInst.methodExitBase()
        if (currentInst !is JIRAssignInst && currentInst !is JIRReturnInst && currentInst !is JIRThrowInst && exitBase == null) {
            return setOf(SequentPrecondition.Unchanged)
        }

        val results = mutableSetOf<SequentPrecondition>()
        results.computeFactPrecondition(fact, applyExitSourceRules = exitBase != null)
        return results
```

`preconditionForFact` returns `null` for the boundaries (existing `else -> return null`).

- [ ] **Step 4: Forward trace from an exit boundary**

In `MethodForwardTraceResolver.resolveForwardTrace`:

```kotlin
        if (!startAtStatement) {
            builder.handleEdgeToMethodEnd(initialEdge, initialEdge, EdgeReason.Unchanged)
            builder.propagateEdgeToSuccessors(initialEdge, initialEdge, EdgeReason.Unchanged)
        } else {
            builder.enqueue(initialEdge)
        }
```

(`handleEdgeToMethodEnd` returns immediately for non-exit statements; for an exit boundary it adds
the `MethodSummary` / `MethodEnd` successor that `VulnerabilityChecker` expects instead of hitting
`error("Non-final trace node without successors")`.)

- [ ] **Step 5: SARIF location of an exit-boundary vulnerability**

In `JirSarifGenerator.statementLocation`, before the `isGeneratedLocation` check:

```kotlin
        if (statement is JMethodExitNormalInst || statement is JMethodExitExceptionalInst) {
            val exitStatement = resolveExitStatement(statement as JIRInst, relevantLocations) ?: return null
            return statementLocation(exitStatement, type, relevantLocations)
        }
```

and the helper next to `unwrapBoundary`:

```kotlin
    private fun resolveExitStatement(
        statement: JIRInst,
        relevantLocations: List<List<IntermediateLocation>>?
    ): CommonInst? {
        val method = statement.location.method
        val isExit: (CommonInst) -> Boolean =
            if (statement is JMethodExitNormalInst) { inst -> inst is JIRReturnInst } else { inst -> inst is JIRThrowInst }

        relevantLocations?.forEach { flow ->
            flow.lastOrNull { it.inst.location.method == method && isExit(it.inst) }?.let { return it.inst }
        }

        return method.instList.instructions.lastOrNull(isExit)
    }
```

(Adapt the `IntermediateLocation` field name if it is not `inst`.)

- [ ] **Step 6: Build + focused tests**

Run (from `core/`, protoc on PATH): `./gradlew :test --tests '*MultiReturnDataFlowTest*' --tests '*SarifGeneratorTest*'`
Expected: PASS.

- [ ] **Step 7: Suites and commit**

Run `suites.sh task3`, then `compare.py baseline task3`. Expected: `differences=0`. If SARIF trace
tests lose the `return` step, extend `JIRAnalysisManager.isTraceRequiredInstruction` to
`inst is JIRReturnInst || inst is JMethodExitNormalInst` and re-run.

```bash
git add -A core/opentaint-dataflow-core core/src/main
git commit -m "refactor(jvm): apply method exit rules on exit boundary instructions"
```

---

### Task 4: `JIRStatementSummary`

**Files:**
- Create: `JDF/analysis/JIRStatementSummary.kt`
- Modify: `JDF/analysis/JIRAliasUtil.kt` (new alias-path helper)
- Create: `JSAMPLES/sample/sequent/StatementSummarySample.java`
- Test: `JDFT/ap/ifds/analysis/JIRStatementSummaryTest.kt` (create)

**Interfaces:**
- Consumes: `MethodFlowFunctionUtils.mkAccess`, `accessPathBase`, `Access` / `MemoryAccess` / `RefAccess` / `StaticRefAccess`.
- Produces:

```kotlin
class JIRStatementSummary(
    val edges: Map<AccessPathBase, List<Edge>>,
    val typeFilters: Map<AccessPathBase, List<JIRType>>,
) {
    data class Edge(val from: InitialFactAp, val to: InitialFactAp?)

    companion object {
        val Empty: JIRStatementSummary
        fun build(apManager: ApManager, inst: JIRInst, aliasAnalysis: JIRLocalAliasAnalysis?): JIRStatementSummary
    }
}

fun JIRLocalAliasAnalysis.forEachAliasPathAtStatement(
    statement: JIRInst, base: AccessPathBase, body: (AccessPathBase, List<Accessor>) -> Unit
)
```

`edges` is keyed by `from.base`; a base the statement touches but has no edge from maps to an
empty list (kill); a base absent from `edges` is untouched. `to == null` is a kill edge that keeps
the refinement of `from` (spec §3 "Kill edges").

- [ ] **Step 1: Sample**

```java
package sample.sequent;

public class StatementSummarySample {
    static Object sField;
    Object f;
    StatementSummarySample next;

    Object fieldRead(StatementSummarySample y) { return y.f; }
    void fieldWrite(StatementSummarySample y, Object x) { y.f = x; }
    Object staticRead() { return sField; }
    void staticWrite(Object x) { sField = x; }
    Object arrayRead(Object[] y) { return y[0]; }
    void arrayWrite(Object[] y, Object x) { y[0] = x; }
    void selfWrite(StatementSummarySample a) { a.f = a; }
    String cast(Object y) { return (String) y; }
    int binary(int a, int b) { return a + b; }

    StatementSummarySample selfRead(StatementSummarySample start) {
        StatementSummarySample n = start;
        while (n.next != null) {
            n = n.next;
        }
        return n;
    }
}
```

- [ ] **Step 2: Write the failing test**

```kotlin
package org.opentaint.dataflow.jvm.ap.ifds.analysis

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.tree.TreeApManager
import org.opentaint.dataflow.jvm.BasicTestUtils
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils.accessPathBase
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRStatementSummary.Edge
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.RefManager
import org.opentaint.ir.api.jvm.cfg.JIRArrayAccess
import org.opentaint.ir.api.jvm.cfg.JIRAssignInst
import org.opentaint.ir.api.jvm.cfg.JIRBinaryExpr
import org.opentaint.ir.api.jvm.cfg.JIRCastExpr
import org.opentaint.ir.api.jvm.cfg.JIRFieldRef
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.cfg.JIRReturnInst
import org.opentaint.ir.api.jvm.cfg.JIRValue
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class JIRStatementSummaryTest : BasicTestUtils() {
    private object UnrollStrategy : AnyAccessorUnrollStrategy {
        override fun unrollAccessor(accessor: Accessor): Boolean = false
    }

    private val ap = TreeApManager(UnrollStrategy, RefManager(), Cancellation())
    private val cls = "sample.sequent.StatementSummarySample"
    private val field = FieldAccessor(cls, "f", "java.lang.Object")
    private val next = FieldAccessor(cls, "next", cls)
    private val staticField = FieldAccessor(cls, "sField", "java.lang.Object")
    private val classStatic = ClassStaticAccessor(cls)

    private fun insts(method: String): List<JIRInst> = findMethod(cls, method).instList.instructions
    private fun assigns(method: String) = insts(method).filterIsInstance<JIRAssignInst>()
    private fun base(v: JIRValue) = accessPathBase(v)!!

    private fun p(base: AccessPathBase, vararg path: Accessor): InitialFactAp =
        path.foldRight(ap.mostAbstractInitialAp(base)) { a, f -> f.prependAccessor(a) }

    private fun summary(inst: JIRInst) = JIRStatementSummary.build(ap, inst, aliasAnalysis = null)
    private fun edges(inst: JIRInst) = summary(inst).edges.values.flatten().toSet()

    @Test
    fun `field read splits the instance and kills the target`() {
        val inst = assigns("fieldRead").first { it.rhv is JIRFieldRef }
        val x = base(inst.lhv)
        val y = base((inst.rhv as JIRFieldRef).instance!!)
        assertEquals(setOf(
            Edge(p(y).exclude(field), p(y)),
            Edge(p(y, field), p(y, field)),
            Edge(p(y, field), p(x)),
        ), edges(inst))
        assertEquals(emptyList(), summary(inst).edges[x])
    }

    @Test
    fun `field write is a strong update of the field`() {
        val inst = assigns("fieldWrite").first { it.lhv is JIRFieldRef }
        val y = base((inst.lhv as JIRFieldRef).instance!!)
        val x = base(inst.rhv as JIRValue)
        assertEquals(setOf(
            Edge(p(y).exclude(field), p(y)),
            Edge(p(x), p(x)),
            Edge(p(x), p(y, field)),
        ), edges(inst))
    }

    @Test
    fun `static read splits the class static base`() {
        val inst = assigns("staticRead").first { it.rhv is JIRFieldRef }
        val x = base(inst.lhv)
        val s = AccessPathBase.ClassStatic
        assertEquals(setOf(
            Edge(p(s).exclude(classStatic), p(s)),
            Edge(p(s, classStatic).exclude(staticField), p(s, classStatic)),
            Edge(p(s, classStatic, staticField), p(s, classStatic, staticField)),
            Edge(p(s, classStatic, staticField), p(x)),
        ), edges(inst))
    }

    @Test
    fun `static write is a strong update of the static field`() {
        val inst = assigns("staticWrite").first { it.lhv is JIRFieldRef }
        val x = base(inst.rhv as JIRValue)
        val s = AccessPathBase.ClassStatic
        assertEquals(setOf(
            Edge(p(s).exclude(classStatic), p(s)),
            Edge(p(s, classStatic).exclude(staticField), p(s, classStatic)),
            Edge(p(x), p(x)),
            Edge(p(x), p(s, classStatic, staticField)),
        ), edges(inst))
    }

    @Test
    fun `array read is split like a field read`() {
        val inst = assigns("arrayRead").first { it.rhv is JIRArrayAccess }
        val x = base(inst.lhv)
        val y = base((inst.rhv as JIRArrayAccess).array)
        assertEquals(setOf(
            Edge(p(y).exclude(ElementAccessor), p(y)),
            Edge(p(y, ElementAccessor), p(y, ElementAccessor)),
            Edge(p(y, ElementAccessor), p(x)),
        ), edges(inst))
    }

    @Test
    fun `array write is weak`() {
        val inst = assigns("arrayWrite").first { it.lhv is JIRArrayAccess }
        val y = base((inst.lhv as JIRArrayAccess).array)
        val x = base(inst.rhv as JIRValue)
        assertEquals(setOf(
            Edge(p(y), p(y)),
            Edge(p(x), p(x)),
            Edge(p(x), p(y, ElementAccessor)),
        ), edges(inst))
    }

    @Test
    fun `self write moves the old value into the field`() {
        val inst = assigns("selfWrite").first { it.lhv is JIRFieldRef }
        val a = base(inst.rhv as JIRValue)
        assertEquals(setOf(
            Edge(p(a).exclude(field), p(a)),
            Edge(p(a), p(a, field)),
        ), edges(inst))
    }

    @Test
    fun `self read is the composition of a read into a temporary and a move`() {
        val inst = assigns("selfRead").first {
            val rhv = it.rhv
            rhv is JIRFieldRef && rhv.instance?.let(::accessPathBase) == accessPathBase(it.lhv)
        }
        val x = base(inst.lhv)
        assertEquals(setOf(
            Edge(p(x).exclude(next), null),
            Edge(p(x, next), p(x)),
        ), edges(inst))
    }

    @Test
    fun `cast moves the operand and filters it by the cast type`() {
        val inst = assigns("cast").first { it.rhv is JIRCastExpr }
        val x = base(inst.lhv)
        val cast = inst.rhv as JIRCastExpr
        val y = base(cast.operand)
        assertEquals(setOf(Edge(p(y), p(y)), Edge(p(y), p(x))), edges(inst))
        assertTrue(cast.type in summary(inst).typeFilters[y].orEmpty())
    }

    @Test
    fun `binary expression moves both operands`() {
        val inst = assigns("binary").first { it.rhv is JIRBinaryExpr }
        val z = base(inst.lhv)
        val bin = inst.rhv as JIRBinaryExpr
        val a = base(bin.lhv)
        val b = base(bin.rhv)
        assertEquals(setOf(
            Edge(p(a), p(a)), Edge(p(a), p(z)),
            Edge(p(b), p(b)), Edge(p(b), p(z)),
        ), edges(inst))
    }

    @Test
    fun `return moves the value to the result and kills the old result`() {
        val inst = insts("cast").filterIsInstance<JIRReturnInst>().single()
        val x = base(inst.returnValue!!)
        assertEquals(setOf(Edge(p(x), p(x)), Edge(p(x), p(AccessPathBase.Return))), edges(inst))
        assertEquals(emptyList(), summary(inst).edges[AccessPathBase.Return])
    }
}
```

(If javac/JIR does not produce `n = n.next` with the same local in `selfRead`, the `first { }`
lookup throws: adjust the sample until it does — the case must be pinned, never skipped.)

- [ ] **Step 3: Run test to verify it fails**

Run: `./gradlew :opentaint-dataflow-core:opentaint-jvm-dataflow:test --tests '*JIRStatementSummaryTest*'`
Expected: compilation FAIL, `JIRStatementSummary` unresolved.

- [ ] **Step 4: Alias-path helper**

In `JIRAliasUtil.kt`:

```kotlin
fun JIRLocalAliasAnalysis.forEachAliasPathAtStatement(
    statement: JIRInst,
    base: AccessPathBase,
    body: (AccessPathBase, List<Accessor>) -> Unit
) {
    val local = base as? AccessPathBase.LocalVar ?: return
    val aliases = findAlias(local, statement) ?: return
    aliases.forEach { alias ->
        val info = alias.relevantApInfo() ?: return@forEach
        body(info.base, info.accessors.map { it.apAccessor() })
    }
}
```

(An alias `A` of `y` with accessors `acc` means the fact `y.p` also exists as `A.acc.p` — the same
fold `applyAlias` performs.)

- [ ] **Step 5: Implement `JIRStatementSummary.kt`**

The builder works on a small internal pattern (`base`, accessor list, exclusions), composes
patterns, then converts them to `InitialFactAp` once.

```kotlin
package org.opentaint.dataflow.jvm.ap.ifds.analysis

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils.accessPathBase
import org.opentaint.ir.api.jvm.JIRType
import org.opentaint.ir.api.jvm.cfg.JIRArrayAccess
import org.opentaint.ir.api.jvm.cfg.JIRAssignInst
import org.opentaint.ir.api.jvm.cfg.JIRBinaryExpr
import org.opentaint.ir.api.jvm.cfg.JIRCastExpr
import org.opentaint.ir.api.jvm.cfg.JIRExpr
import org.opentaint.ir.api.jvm.cfg.JIRFieldRef
import org.opentaint.ir.api.jvm.cfg.JIRImmediate
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.cfg.JIRReturnInst
import org.opentaint.ir.api.jvm.cfg.JIRThrowInst
import org.opentaint.ir.api.jvm.cfg.JIRValue

class JIRStatementSummary(
    val edges: Map<AccessPathBase, List<Edge>>,
    val typeFilters: Map<AccessPathBase, List<JIRType>>,
) {
    data class Edge(val from: InitialFactAp, val to: InitialFactAp?)

    companion object {
        val Empty = JIRStatementSummary(emptyMap(), emptyMap())

        fun build(apManager: ApManager, inst: JIRInst, aliasAnalysis: JIRLocalAliasAnalysis?): JIRStatementSummary {
            val builder = Builder(inst, aliasAnalysis)
            val transfer = builder.build() ?: return Empty
            return JIRStatementSummary(transfer.toEdges(apManager), builder.typeFilters)
        }

        private val temporary = AccessPathBase.LocalVar.create(-1)
    }

    private data class Pattern(
        val base: AccessPathBase,
        val accessors: List<Accessor> = emptyList(),
        val exclusions: Set<Accessor> = emptySet(),
    ) {
        fun exclude(accessor: Accessor) = copy(exclusions = exclusions + accessor)
        fun append(rest: List<Accessor>) = copy(accessors = accessors + rest)

        fun toFact(apManager: ApManager): InitialFactAp {
            val path = accessors.foldRight(apManager.mostAbstractInitialAp(base)) { a, f -> f.prependAccessor(a) }
            return exclusions.fold(path) { f, a -> f.exclude(a) }
        }
    }

    private data class PatternEdge(val from: Pattern, val to: Pattern?)

    private class Transfer {
        val edges = linkedMapOf<AccessPathBase, LinkedHashSet<PatternEdge>>()

        fun touch(base: AccessPathBase) = edges.getOrPut(base) { linkedSetOf() }

        fun add(from: Pattern, to: Pattern?) {
            touch(from.base) += PatternEdge(from, to)
        }

        fun then(second: Transfer): Transfer {
            val result = Transfer()
            for ((base, firstEdges) in edges) {
                result.touch(base)
                for (edge in firstEdges) {
                    val to = edge.to
                    val secondEdges = to?.let { second.edges[it.base] }
                    if (secondEdges == null) {
                        result.add(edge.from, to)
                        continue
                    }

                    var matched = false
                    for (next in secondEdges) {
                        val composed = compose(edge.from, to, next) ?: continue
                        result.add(composed.from, composed.to)
                        matched = true
                    }

                    if (!matched && edge.from.exclusions.isNotEmpty()) {
                        result.add(edge.from, null)
                    }
                }
            }

            for ((base, secondEdges) in second.edges) {
                if (base in edges) continue
                result.touch(base)
                secondEdges.forEach { result.add(it.from, it.to) }
            }

            return result
        }

        private fun compose(a: Pattern, b: Pattern, next: PatternEdge): PatternEdge? {
            val c = next.from
            val d = next.to
            if (c.base != b.base) return null

            if (b.accessors.size >= c.accessors.size && b.accessors.subList(0, c.accessors.size) == c.accessors) {
                val rest = b.accessors.subList(c.accessors.size, b.accessors.size)
                if (rest.isNotEmpty() && rest.first() in c.exclusions) return null
                val from = if (rest.isEmpty()) a.copy(exclusions = a.exclusions + c.exclusions) else a
                return PatternEdge(from, d?.append(rest))
            }

            if (c.accessors.subList(0, b.accessors.size) == b.accessors) {
                val rest = c.accessors.subList(b.accessors.size, c.accessors.size)
                if (rest.first() in a.exclusions) return null
                return PatternEdge(a.append(rest).copy(exclusions = c.exclusions), d)
            }

            return null
        }

        fun eliminate(base: AccessPathBase): Transfer {
            val result = Transfer()
            for ((from, fromEdges) in edges) {
                if (from == base) continue
                result.touch(from)
                fromEdges.filter { it.to?.base != base }.forEach { result.add(it.from, it.to) }
            }
            return result
        }

        fun toEdges(apManager: ApManager): Map<AccessPathBase, List<Edge>> =
            edges.mapValues { (_, patternEdges) ->
                patternEdges.map { Edge(it.from.toFact(apManager), it.to?.toFact(apManager)) }
            }
    }

    private class Builder(
        private val inst: JIRInst,
        private val aliasAnalysis: JIRLocalAliasAnalysis?,
    ) {
        val typeFilters = hashMapOf<AccessPathBase, MutableList<JIRType>>()

        fun build(): Transfer? = when (inst) {
            is JIRAssignInst -> Transfer().also { assign(it, inst.lhv, inst.rhv) }
            is JIRReturnInst -> Transfer().also { move(it, AccessPathBase.Return, inst.returnValue?.let { v -> accessPathBase(v) }) }
            is JIRThrowInst -> Transfer().also { move(it, AccessPathBase.Exception, accessPathBase(inst.throwable)) }
            else -> null
        }

        private fun filter(access: MethodFlowFunctionUtils.Access, type: JIRType?) {
            if (type == null) return
            typeFilters.getOrPut(access.base) { mutableListOf() } += type
        }

        private fun assign(t: Transfer, lhv: JIRValue, rhv: JIRExpr) {
            if (rhv is JIRBinaryExpr) {
                assign(t, lhv, rhv.lhv)
                assign(t, lhv, rhv.rhv)
                return
            }

            val from = when (rhv) {
                is JIRCastExpr -> MethodFlowFunctionUtils.mkAccess(rhv.operand)?.also { filter(it, rhv.type) } ?: return
                is JIRImmediate -> MethodFlowFunctionUtils.mkAccess(rhv)?.also { filter(it, rhv.type) } ?: return
                is JIRArrayAccess -> MethodFlowFunctionUtils.mkAccess(rhv)?.also { filter(it, rhv.array.type) } ?: return
                is JIRFieldRef -> MethodFlowFunctionUtils.mkAccess(rhv)
                    ?.also { filter(it, rhv.instance?.type) }
                    ?.also { filter(it, rhv.field.enclosingType) }
                    ?: return
                else -> null
            }

            val to = when (lhv) {
                is JIRImmediate -> MethodFlowFunctionUtils.mkAccess(lhv)?.also { filter(it, lhv.type) } ?: return
                is JIRArrayAccess -> MethodFlowFunctionUtils.mkAccess(lhv)?.also { filter(it, lhv.array.type) } ?: return
                is JIRFieldRef -> MethodFlowFunctionUtils.mkAccess(lhv)
                    ?.also { filter(it, lhv.instance?.type) }
                    ?.also { filter(it, lhv.field.enclosingType) }
                    ?: return
                else -> error("Assign to complex value: $lhv")
            }

            when {
                from is MethodFlowFunctionUtils.MemoryAccess -> {
                    check(to !is MethodFlowFunctionUtils.MemoryAccess) { "Complex assignment: $lhv = $rhv" }
                    if (to.base != from.base) {
                        read(t, to.base, from)
                    } else {
                        val first = Transfer().also { read(it, temporary, from) }
                        val second = Transfer().also { move(it, to.base, temporary) }
                        first.then(second).eliminate(temporary).edges.forEach { (base, edges) ->
                            t.touch(base).addAll(edges)
                        }
                    }
                }

                to is MethodFlowFunctionUtils.MemoryAccess -> write(t, to, from?.base)

                else -> move(t, to.base, from?.base)
            }
        }

        private fun move(t: Transfer, to: AccessPathBase, from: AccessPathBase?) {
            t.touch(to)
            if (from == null) return
            t.add(Pattern(from), Pattern(from))
            if (from != to) t.add(Pattern(from), Pattern(to))
        }

        private fun path(access: MethodFlowFunctionUtils.MemoryAccess): List<Accessor> = when (access) {
            is MethodFlowFunctionUtils.RefAccess -> listOf(access.accessor)
            is MethodFlowFunctionUtils.StaticRefAccess -> listOf(access.classStaticAccessor, access.accessor)
        }

        private fun split(t: Transfer, base: AccessPathBase, accessors: List<Accessor>) {
            for (i in accessors.indices) {
                val prefix = Pattern(base, accessors.subList(0, i))
                t.add(prefix.exclude(accessors[i]), prefix)
            }
        }

        private fun aliases(t: Transfer, base: AccessPathBase, accessor: Accessor) {
            aliasAnalysis?.forEachAliasPathAtStatement(inst, base) { aliasBase, aliasAccessors ->
                t.add(Pattern(base).exclude(accessor), Pattern(aliasBase, aliasAccessors))
            }
        }

        private fun read(t: Transfer, to: AccessPathBase, access: MethodFlowFunctionUtils.MemoryAccess) {
            val accessors = path(access)
            val source = Pattern(access.base, accessors)

            t.touch(to)
            split(t, access.base, accessors)
            t.add(source, source)
            t.add(source, Pattern(to))
            aliases(t, access.base, accessors.first())
        }

        private fun write(t: Transfer, access: MethodFlowFunctionUtils.MemoryAccess, from: AccessPathBase?) {
            val base = access.base
            val accessors = path(access)
            val target = Pattern(base, accessors)

            if (accessors.first() is ElementAccessor) {
                t.add(Pattern(base), Pattern(base))
            } else {
                split(t, base, accessors)
                aliases(t, base, accessors.first())
            }

            if (from == null) return
            if (from != base) t.add(Pattern(from), Pattern(from))
            t.add(Pattern(from), target)
            aliasAnalysis?.forEachAliasPathAtStatement(inst, base) { aliasBase, aliasAccessors ->
                t.add(Pattern(from), Pattern(aliasBase, aliasAccessors + accessors))
            }
        }
    }
}
```

Notes for the implementer (they encode the spec, do not deviate):
- `split(base, [a1..an])` emits `base.a1..ai/{a(i+1)} -> base.a1..ai` for every prefix: the identity of
  everything except the accessed path, which makes abstract incoming facts refine on the accessed accessor.
- `x = x.f` / `x = x[i]` are `read(tmp) then move(x, tmp)` with `tmp` eliminated (spec §3 "Composition").
  The composed kill edge `x/{f} -> ⊥` is load-bearing.
- An element write keeps the whole array (weak) and adds no abstract aliases.
- `AccessPathBase.LocalVar.create(-1)` is the same temporary base the old flow function used.

- [ ] **Step 6: Run the test**

Run: `./gradlew :opentaint-dataflow-core:opentaint-jvm-dataflow:test --tests '*JIRStatementSummaryTest*'`
Expected: PASS (11 tests). If an expectation fails because javac emitted a different shape, fix the
instruction lookup or the sample, never the expected edge set.

- [ ] **Step 7: Commit**

```bash
git add core/opentaint-dataflow-core/opentaint-jvm-dataflow
git commit -m "feat(jvm): per-statement transfer summaries"
```

---

### Task 5: Transfer through the statement summary, cached flow function

**Files:**
- Modify: `JDF/analysis/JIRMethodSequentFlowFunction.kt`
- Modify: `JDF/analysis/JIRMethodAnalysisContext.kt`
- Modify: `JDF/analysis/JIRAnalysisManager.kt` (`getMethodSequentFlowFunction`, ~line 190)

**Interfaces:**
- Consumes: `JIRStatementSummary.build` (Task 4), `InitialFactAp.concat(typeChecker, FinalFactAp.Delta)` (Task 1),
  `JIRInst.methodExitBase()` (Task 3), `MethodSummaryEdgeApplicationUtils.tryApplySummaryEdge`.
- Produces: `JIRMethodAnalysisContext.cachedSequentFF(stmtIdx: Int, generateTrace: Boolean, body: () -> JIRMethodSequentFlowFunction): JIRMethodSequentFlowFunction`.

- [ ] **Step 1: Cache**

`JIRMethodAnalysisContext`:

```kotlin
    fun cachedSequentFF(stmtIdx: Int, generateTrace: Boolean, body: () -> JIRMethodSequentFlowFunction): JIRMethodSequentFlowFunction {
        val cache = getSequentFFCache()
        val key = stmtIdx * 2 + if (generateTrace) 1 else 0
        return synchronized(cache) { cache.computeIfAbsent(key) { body() } }
    }

    private var sequentFFCache: Reference<Int2ObjectOpenHashMap<JIRMethodSequentFlowFunction>>? = null
    private fun getSequentFFCache(): Int2ObjectOpenHashMap<JIRMethodSequentFlowFunction> {
        sequentFFCache?.get()?.let { return it }
        return int2ObjectMap<JIRMethodSequentFlowFunction>().also {
            sequentFFCache = refManager.createRef(it)
        }
    }
```

and `sequentFFCache?.clear()` in `resetAnalysisCache()`.

`JIRAnalysisManager.getMethodSequentFlowFunction`:

```kotlin
        return analysisContext.cachedSequentFF(currentInst.location.index, generateTrace) {
            JIRMethodSequentFlowFunction(apManager, analysisContext, currentInst, generateTrace)
        }
```

- [ ] **Step 2: Transfer**

In `JIRMethodSequentFlowFunction`:

1. Add

```kotlin
    private val summary: JIRStatementSummary by lazy {
        JIRStatementSummary.build(apManager, currentInst, analysisContext.aliasAnalysis)
    }

    private fun transfer(factAp: FinalFactAp, emit: (FinalFactAp, ExclusionSet?) -> Unit, refine: (ExclusionSet) -> Unit): Boolean {
        val edges = summary.edges[factAp.base] ?: return false

        var fact = factAp
        summary.typeFilters[fact.base]?.forEach { type ->
            fact = factTypeChecker.filterFactByLocalType(type, fact) ?: return true
        }

        for (edge in edges) {
            for (effect in MethodSummaryEdgeApplicationUtils.tryApplySummaryEdge(fact, edge.from)) {
                val to = edge.to
                when (effect) {
                    is SummaryEdgeApplication.SummaryApRefinement -> {
                        if (to == null) continue
                        val result = to.concat(factTypeChecker, effect.delta) ?: continue
                        emit(result.replaceExclusions(fact.exclusions), null)
                    }

                    is SummaryEdgeApplication.SummaryExclusionRefinement -> {
                        if (to == null) {
                            refine(effect.exclusion)
                            continue
                        }
                        val result = to.concat(factTypeChecker, effect.delta) ?: continue
                        emit(result.replaceExclusions(effect.exclusion), effect.exclusion)
                    }
                }
            }
        }

        return true
    }
```

2. Replace the three `propagate*` entry points' bodies so the non-exit path goes through
   `transfer` and emits per edge kind:
   - Z2F: `emit = { f, refinement -> check(refinement == null || refinement is ExclusionSet.Universe); add(Sequent.ZeroToFact(f, TraceInfo.Flow)) }`
   - F2F: `emit = { f, refinement -> add(Sequent.FactToFact(if (refinement == null) initialFactAp else initialFactAp.replaceExclusions(refinement), f, TraceInfo.Flow)) }`,
     `refine = { ex -> initialFactAp.replaceExclusions(ex).takeIf { it != initialFactAp }?.let { add(Sequent.SideEffectRequirement(it)) } }`
   - Z2F / NDF2F: `refine = { }` (their exclusions are `Universe`, nothing to refine)
   - NDF2F: `emit = { f, refinement -> check(refinement == null || refinement is ExclusionSet.Universe); add(Sequent.NDFactToFact(initialFacts, f, TraceInfo.Flow)) }`

   `propagate(...)` becomes

```kotlin
        val exitBase = currentInst.methodExitBase()
        if (exitBase != null) {
            propagateExitFact(initialFacts, exitBase, factAp, unchanged, propagateFactWithRefinement, sideEffect)
            return
        }

        if (!transfer(factAp, propagateTransferred, refineInitial)) {
            unchanged()
        }
```

   with `propagateTransferred: (FinalFactAp, ExclusionSet?) -> Unit` and
   `refineInitial: (ExclusionSet) -> Unit` replacing the `propagateFact` and
   `propagateFactWithAccessorExclude` parameters.
3. Delete the now-unused per-fact transfer code: `sequentFlowAssign`, `filterFactBaseType`,
   `simpleAssign`, both `fieldRead`, both `fieldWrite`, `propagateAbstractFactWithFieldExcluded`, and the
   imports only they used (`mayReadAccessor`, `mayRemoveAfterWrite`, `readAccessorTo`,
   `writeToAccessor`, `clearField`, `excludeField`, `forEachAliasAtStatement`, JIR expression types).
   Keep `FactRefiner`, exit rules, zero-to-zero logic, `dropFinalFacts`, `dropArgumentsLocalTaintMarks`.

- [ ] **Step 3: Build**

Run: `./gradlew :opentaint-dataflow-core:opentaint-jvm-dataflow:compileKotlin` → BUILD SUCCESSFUL.

- [ ] **Step 4: Suites**

Run `suites.sh task5`, then `compare.py baseline task5`. Expected: `differences=0` except the new
unit tests (`- -> PASS`).

If there are differences: for each failing test collect the assertion message, write the smallest
reproducing sample in `JSAMPLES/sample/sequent/`, compare the old flow function (git stash) with the
new one on that statement, and fix the summary builder or `transfer` to match the spec. Report
any case where matching the old result needs a deviation from the spec (e.g. static write must stay
weak) instead of silently deviating.

- [ ] **Step 5: Commit**

```bash
git add -A core/opentaint-dataflow-core
git commit -m "refactor(jvm): sequent transfer through per-statement summaries"
```

---

### Task 6: Wrap-up

**Files:**
- Modify: `core/docs/sequent-statement-summaries.md` (status line; record any approved deviation)

- [ ] **Step 1:** `git diff origin/main --stat` and read the full diff of the flow function; confirm no dead code and no comments were added.
- [ ] **Step 2:** Final `suites.sh final` + `compare.py baseline final` → `differences=0` (plus new tests).
- [ ] **Step 3:** Update the spec status to "implemented" with the final commit hash and commit.

```bash
git add core/docs/sequent-statement-summaries.md
git commit -m "doc(dataflow): per-statement summary sequent flow function implemented"
```

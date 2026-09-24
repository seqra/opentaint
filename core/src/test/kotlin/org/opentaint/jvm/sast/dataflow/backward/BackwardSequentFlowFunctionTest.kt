package org.opentaint.jvm.sast.dataflow.backward

import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.EmptyMethodContext
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.TaintAnalysisManager
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.tree.TreeApManager
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.Sequent
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.TraceInfo
import org.opentaint.dataflow.ap.ifds.taint.TaintAnalysisUnitStorage
import org.opentaint.dataflow.ap.ifds.taint.TaintSinkTracker
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedRule
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintAssignAction
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalVariableReachability
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils
import org.opentaint.dataflow.jvm.ap.ifds.backward.JIRBackwardAnalysisManager
import org.opentaint.dataflow.jvm.ap.ifds.backward.JIRBackwardMethodAnalysisContext
import org.opentaint.dataflow.jvm.ap.ifds.backward.JIRBackwardMethodSequentFlowFunction
import org.opentaint.dataflow.jvm.ap.ifds.taint.JIRTaintAnalysisContext
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.RefManager
import org.opentaint.ir.api.jvm.cfg.JIRExpr
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.cfg.JIRValue
import org.opentaint.jvm.graph.JMethodEnterInst
import org.opentaint.jvm.graph.JMethodExitNormalInst

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class BackwardSequentFlowFunctionTest : BackwardAnalysisTest() {
    companion object {
        private const val CLS = "test.samples.BackwardSequentSample"
        private const val MARK = "tainted"
    }

    override val sourceFileExtension: String = "java"

    private val refManager = RefManager()
    private val apManager: ApManager by lazy { TreeApManager(analysisUnrollStrategy, refManager, Cancellation()) }

    private class Fixture(
        val ff: JIRBackwardMethodSequentFlowFunction,
        val manager: JIRBackwardAnalysisManager,
        val inst: JIRInst,
    )

    private fun fixture(method: String, inst: String, config: SerializedTaintConfig = SerializedTaintConfig()): Fixture {
        val jirMethod = findMethod(CLS, method)
        val statement = jirMethod.instList.firstOrNull { it.toString() == inst }
            ?: error("No '$inst' in $method: ${jirMethod.instList}")

        val manager = JIRBackwardAnalysisManager(cp, refManager, createRulesProvider(config))
        manager.selectPhase(TaintAnalysisManager.Phase.FullScan())
        val forwardGraph = createAnalysisGraph()
        val exit = jirMethod.instList.single { it is JMethodExitNormalInst }
        val enter = jirMethod.instList.single { it is JMethodEnterInst }

        val context = JIRBackwardMethodAnalysisContext(
            manager,
            refManager.softRefManager("test"),
            MethodEntryPoint(EmptyMethodContext, exit),
            manager.factTypeChecker,
            JIRLocalVariableReachability(jirMethod, forwardGraph, manager),
            aliasAnalysis = null,
            JIRTaintAnalysisContext(
                TaintSinkTracker(TaintAnalysisUnitStorage(apManager, manager)),
                createRulesProvider(config),
                relevantRuleIds = hashSetOf(),
            ),
            forwardEntryPoint = enter,
            findings = manager.findings,
        )

        return Fixture(JIRBackwardMethodSequentFlowFunction(apManager, context, statement), manager, statement)
    }

    private fun Fixture.base(name: String): AccessPathBase {
        val values = mutableListOf<JIRExpr>()
        fun collect(expr: JIRExpr) {
            values += expr
            expr.operands.forEach { collect(it) }
        }
        inst.location.method.instList.forEach { i -> i.operands.forEach { collect(it) } }
        return values.firstNotNullOfOrNull { value ->
            (value as? JIRValue)?.takeIf { it.toString() == name }?.let { MethodFlowFunctionUtils.accessPathBase(it) }
        } ?: error("No value $name")
    }

    private fun field(name: String, type: String = "java.lang.String") =
        FieldAccessor("$CLS\$Box", name, type)

    private val mark = TaintMarkAccessor(MARK)

    private fun abstract(base: AccessPathBase): FinalFactAp = apManager.mostAbstractFinalAp(base)
    private fun initial(): InitialFactAp = apManager.mostAbstractInitialAp(AccessPathBase.Return)
    private fun marked(base: AccessPathBase): FinalFactAp =
        apManager.createFinalAp(base, ExclusionSet.Universe).prependAccessor(mark)

    private fun f2f(initial: InitialFactAp, fact: FinalFactAp) = Sequent.FactToFact(initial, fact, TraceInfo.Flow)

    @Test
    fun `field write reads the written field from an abstract demand`() {
        val fx = fixture("fieldWriteRead", "b.f = p")
        val b = fx.base("b")
        val init = initial()

        val result = fx.ff.propagateFactToFact(init, abstract(b))
        assertEquals(setOf(f2f(init.exclude(field("f")), abstract(b).exclude(field("f")))), result)
    }

    @Test
    fun `field write moves the refined demand to the stored value`() {
        val fx = fixture("fieldWriteRead", "b.f = p")
        val b = fx.base("b")
        val p = fx.base("p")
        val init = initial()

        val demand = abstract(b).prependAccessor(field("f"))
        val result = fx.ff.propagateFactToFact(init, demand)
        assertEquals(setOf(f2f(init, abstract(p))), result)
    }

    @Test
    fun `field write keeps the other field and moves the written one`() {
        val fx = fixture("fieldWriteRead", "b.f = p")
        val b = fx.base("b")
        val p = fx.base("p")

        val onF = marked(b).prependAccessor(field("f"))
        val onG = marked(b).prependAccessor(field("g"))
        assertEquals(setOf(Sequent.ZeroToFact(marked(p), TraceInfo.Flow)), fx.ff.propagateZeroToFact(onF))
        assertEquals(setOf(Sequent.Unchanged), fx.ff.propagateZeroToFact(onG))
    }

    @Test
    fun `field read prepends the accessor without refinement`() {
        val fx = fixture("fieldWriteRead", "%2 = b.f")
        val tmp = fx.base("%2")
        val b = fx.base("b")
        val init = initial()

        val result = fx.ff.propagateFactToFact(init, abstract(tmp))
        assertEquals(setOf(f2f(init, abstract(b).prependAccessor(field("f")))), result)
    }

    @Test
    fun `array write keeps the abstract demand and refines the element`() {
        val fx = fixture("arrayWriteRead", "arr[0] = p")
        val arr = fx.base("arr")
        val init = initial()

        val result = fx.ff.propagateFactToFact(init, abstract(arr))
        assertEquals(
            setOf(Sequent.Unchanged, f2f(init.exclude(ElementAccessor), abstract(arr).exclude(ElementAccessor))),
            result
        )
    }

    @Test
    fun `array write keeps and moves a concrete element demand`() {
        val fx = fixture("arrayWriteRead", "arr[0] = p")
        val arr = fx.base("arr")
        val p = fx.base("p")

        val demand = marked(arr).prependAccessor(ElementAccessor)
        assertEquals(
            setOf(Sequent.Unchanged, Sequent.ZeroToFact(marked(p), TraceInfo.Flow)),
            fx.ff.propagateZeroToFact(demand)
        )
    }

    @Test
    fun `static write refines class and field accessors`() {
        val fx = fixture("staticWriteRead", "$CLS.STATIC_FIELD = p")
        val p = fx.base("p")
        val init = initial()
        val cls = ClassStaticAccessor(CLS)
        val staticField = FieldAccessor(CLS, "STATIC_FIELD", "java.lang.String")
        val static = AccessPathBase.ClassStatic

        assertEquals(
            setOf(f2f(init.exclude(cls), abstract(static).exclude(cls))),
            fx.ff.propagateFactToFact(init, abstract(static))
        )

        val classDemand = abstract(static).prependAccessor(cls)
        assertEquals(
            setOf(f2f(init.exclude(staticField), classDemand.exclude(staticField))),
            fx.ff.propagateFactToFact(init, classDemand)
        )

        val fieldDemand = abstract(static).prependAccessor(staticField).prependAccessor(cls)
        assertEquals(setOf(f2f(init, abstract(p))), fx.ff.propagateFactToFact(init, fieldDemand))
    }

    @Test
    fun `self write moves the field and clears it`() {
        val fx = fixture("selfWrite", "n.next = n")
        val n = fx.base("n")
        val next = FieldAccessor("$CLS\$Node", "next", "$CLS\$Node")
        val value = FieldAccessor("$CLS\$Node", "val", "java.lang.String")

        val demand = marked(n).prependAccessor(value).prependAccessor(next)
        assertEquals(
            setOf(Sequent.ZeroToFact(marked(n).prependAccessor(value), TraceInfo.Flow)),
            fx.ff.propagateZeroToFact(demand)
        )
    }

    @Test
    fun `return rebases the result demand`() {
        val fx = fixture("exitFlow", "return a")
        val a = fx.base("a")
        val init = initial()

        assertEquals(setOf(f2f(init, abstract(a))), fx.ff.propagateFactToFact(init, abstract(AccessPathBase.Return)))
        assertEquals(setOf(Sequent.Unchanged), fx.ff.propagateFactToFact(init, abstract(a)))
    }

    @Test
    fun `return matches exit sources before rebasing`() {
        val config = SerializedTaintConfig(
            methodExitSource = listOf(
                SerializedRule.MethodExitSource(
                    function = functionMatcher(CLS, "exitFlow"),
                    taint = listOf(
                        SerializedTaintAssignAction(
                            kind = MARK,
                            pos = PositionBaseWithModifiers.BaseOnly(PositionBase.Result),
                        )
                    ),
                )
            )
        )
        val fx = fixture("exitFlow", "return a", config)
        val a = fx.base("a")
        val init = initial()

        val demand = apManager.createFinalAp(AccessPathBase.Return, ExclusionSet.Universe).prependAccessor(mark)
        val concreteResult = fx.ff.propagateZeroToFact(demand)
        assertEquals(setOf(Sequent.ZeroToFact(marked(a), TraceInfo.Flow)), concreteResult)

        val finding = fx.manager.findings.sourceFindings().single()
        assertEquals(mark, finding.mark)
        assertEquals(fx.inst, finding.statement)

        val abstractResult = fx.ff.propagateFactToFact(init, abstract(AccessPathBase.Return))
        assertEquals(setOf(f2f(init.exclude(mark), abstract(a).exclude(mark))), abstractResult)
        assertEquals(1, fx.manager.findings.sourceFindings().size)
    }

    @Test
    fun `method enter keeps the demand`() {
        val fx = fixture("simpleAssign", "method enter")
        val init = initial()
        assertEquals(setOf(Sequent.Unchanged), fx.ff.propagateFactToFact(init, abstract(AccessPathBase.Argument(0))))
    }
}

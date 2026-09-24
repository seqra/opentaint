package org.opentaint.jvm.sast.dataflow.backward

import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.TaintAnalysisUnitRunnerManager
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedRule
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils
import org.opentaint.ir.api.jvm.cfg.JIRCallInst
import org.opentaint.ir.api.jvm.ext.cfg.callExpr
import org.opentaint.jvm.graph.JMethodEnterInst

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class BackwardSmokeTest : BackwardAnalysisTest() {
    companion object {
        private const val SAMPLE_PACKAGE = "test.samples"
        private const val TAINT_MARK = "tainted"
        private const val RULE_ID = "simple-flow-rule"
        private const val ENTRY_RULE_ID = "simple-entry-rule"
        private const val SIMPLE_CLS = "$SAMPLE_PACKAGE.SimpleDataFlowSample"
    }

    override val sourceFileExtension: String = "java"
    override val useDefaultConfig: Boolean = true

    private val simpleConfig by lazy {
        SerializedTaintConfig(
            source = listOf(sourceRule(SIMPLE_CLS, "source", TAINT_MARK)),
            sink = listOf(sinkRule(SIMPLE_CLS, "sink", RULE_ID, listOf(Argument(0) to TAINT_MARK)))
        )
    }

    @Test
    fun `simple flow - backward run completes and seeds the sink demand`() {
        val result = runBackwardAnalysis(simpleConfig, SIMPLE_CLS, "simpleDataFlow")

        assertEquals(TaintAnalysisUnitRunnerManager.Status.OK, result.status)
        val analyzed = result.analyzedMethods.mapTo(hashSetOf()) { it.name }
        assertTrue(
            analyzed.containsAll(listOf("simpleDataFlow", "sink", "process", "source")),
            "zero fact must enter every resolved callee from its exit: $analyzed"
        )
        assertTrue(result.unconditionalSinks.isEmpty(), "unexpected unconditional sinks: ${result.unconditionalSinks}")

        val seed = result.demandSeeds.singleOrNull()
            ?: error("expected exactly one sink demand seed, got ${result.demandSeeds}")

        assertEquals(RULE_ID, seed.rule.id)
        assertEquals("simpleDataFlow", seed.statement.location.method.name)
        assertEquals("sink", seed.statement.callExpr?.method?.name)
        assertTrue(seed.statement is JIRCallInst, "seed statement must be the sink call: ${seed.statement}")
        assertTrue(seed.fact.base is AccessPathBase.LocalVar, "seed must be mapped to the caller local: ${seed.fact}")
        assertTrue(seed.fact.startsWithAccessor(TaintMarkAccessor(TAINT_MARK)), "seed must demand the mark: ${seed.fact}")
    }

    @Test
    fun `entry sink - callee entry demand is mapped back to the caller argument`() {
        val config = SerializedTaintConfig(
            methodEntrySink = listOf(
                SerializedRule.MethodEntrySink(
                    function = functionMatcher(SIMPLE_CLS, "sink"),
                    condition = listOf(Argument(0) to TAINT_MARK).condition(),
                    id = ENTRY_RULE_ID,
                )
            )
        )

        val result = runBackwardAnalysis(config, SIMPLE_CLS, "simpleDataFlow")
        assertEquals(TaintAnalysisUnitRunnerManager.Status.OK, result.status)

        val seed = result.demandSeeds.singleOrNull()
            ?: error("expected exactly one entry sink seed, got ${result.demandSeeds}")
        assertEquals(ENTRY_RULE_ID, seed.rule.id)
        assertEquals("sink", seed.statement.location.method.name)
        assertTrue(seed.statement is JMethodEnterInst, "entry seed must be produced at the method enter: ${seed.statement}")
        assertEquals(AccessPathBase.Argument(0), seed.fact.base)

        val sinkCall = findMethod(SIMPLE_CLS, "simpleDataFlow").instList.single { it.callExpr?.method?.name == "sink" }
        val processCall = findMethod(SIMPLE_CLS, "simpleDataFlow").instList.single { it.callExpr?.method?.name == "process" }
        val sinkArgBase = MethodFlowFunctionUtils.accessPathBase(sinkCall.callExpr!!.args.single())

        val demandsBeforeSink = result.statementFacts[processCall].orEmpty()
        assertTrue(
            demandsBeforeSink.any { it.base == sinkArgBase && it.startsWithAccessor(TaintMarkAccessor(TAINT_MARK)) },
            "summary of the callee entry demand must reach the caller before the sink call: $demandsBeforeSink"
        )
    }

    @Test
    fun `simple flow - sink demand reaches the source`() {
        assertSourceReached(
            config = simpleConfig,
            testCls = SIMPLE_CLS,
            entryPointName = "simpleDataFlow",
            sourceMethodName = "source",
            mark = TAINT_MARK,
            testName = "simple flow"
        )
    }
}

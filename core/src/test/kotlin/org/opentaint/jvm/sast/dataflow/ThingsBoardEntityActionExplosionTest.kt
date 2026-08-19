package org.opentaint.jvm.sast.dataflow

import kotlinx.coroutines.runBlocking
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import org.opentaint.common.sast.dataflow.TaintAnalyzer
import org.opentaint.common.sast.dataflow.TaintAnalyzerOptions
import org.opentaint.dataflow.ap.ifds.EmptyMethodContext
import org.opentaint.dataflow.ap.ifds.MethodStats
import org.opentaint.dataflow.ap.ifds.MethodWithContext
import org.opentaint.dataflow.ap.ifds.TaintAnalysisManager
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy.AnyAccessorDisabled
import org.opentaint.dataflow.ap.ifds.access.ApMode
import org.opentaint.dataflow.ap.ifds.access.baseonly.BaseOnlyApManager
import org.opentaint.dataflow.ap.ifds.access.tree.TreeApManager
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.ClassStatic
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedRule
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintAssignAction
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig
import org.opentaint.dataflow.jvm.ap.ifds.JIRSafeApplicationGraph
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRAnalysisManager
import org.opentaint.dataflow.jvm.ap.ifds.taint.TaintRulesProvider
import org.opentaint.ir.api.jvm.JIRMethod
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.impl.features.usagesExt
import org.opentaint.jvm.graph.JApplicationGraphImpl
import org.opentaint.jvm.sast.dataflow.rules.TaintConfiguration
import org.opentaint.util.analysis.ApplicationGraph
import kotlin.time.Duration.Companion.minutes
import kotlin.time.Duration.Companion.seconds

class ThingsBoardEntityActionExplosionTest : AnalysisTest() {
    override val sourceFileExtension: String = "java"

    private val testClass = "test.samples.ThingsBoardEntityActionExplosionSample"
    private val ruleId = "thingsboard-entity-action-explosion"
    private val mark = "thingsboard-entity-action-taint"
    private val config = SerializedTaintConfig(
        source = listOf(sourceRule(testClass, "source", mark)),
        sink = listOf(sinkRule(testClass, "sink", ruleId, listOf(Argument(0) to mark))),
    )

    private val safeContextRuleId = "thingsboard-context-support-safe"
    private val taintedContextRuleId = "thingsboard-context-support-tainted"
    private val contextSupportConfig = SerializedTaintConfig(
        source = listOf(sourceRule(testClass, "source", mark)),
        sink = listOf(
            sinkRule(testClass, "safeContextSink", safeContextRuleId, listOf(Argument(0) to mark)),
            sinkRule(testClass, "taintedContextSink", taintedContextRuleId, listOf(Argument(0) to mark)),
        ),
    )

    private val classStaticRuleId = "thingsboard-class-static-context"
    private val classStaticState = ClassStatic("thingsboard.class-static-context")
    private val classStaticConfig = SerializedTaintConfig(
        source = listOf(
            sourceRule(testClass, "source", mark),
            SerializedRule.Source(
                function = functionMatcher(testClass, "seedClassStatic"),
                condition = listOf(Argument(0) to mark).condition(),
                taint = listOf(
                    SerializedTaintAssignAction(
                        kind = "ready",
                        pos = PositionBaseWithModifiers.BaseOnly(classStaticState),
                    )
                ),
            ),
        ),
        sink = listOf(
            sinkRule(testClass, "classStaticSink", classStaticRuleId, listOf(classStaticState to "ready")),
        ),
    )

    @Test
    fun `interface contexts multiply the branch-heavy entity action analysis`() {
        val single = measureShallowScan(config, "singleEntityAction", "pushEntityActionToRuleEngine")
        val contextual = measureShallowScan(config, "entityActionExplosion", "pushEntityActionToRuleEngine")

        assertEquals(setOf(ruleId), single.ruleIds)
        assertEquals(setOf(ruleId), contextual.ruleIds)

        // The default ContextIndependentFacts policy shares only Zero and ClassStatic flows, so an
        // ordinary interface-typed argument fact is still analyzed once per concrete context.
        assertTrue(
            contextual.stats.steps >= single.stats.steps * 4,
            "six concrete interface contexts must multiply the shallow scan: " +
                "single=${single.stats}, contextual=${contextual.stats}",
        )
        println("ThingsBoard entity-action shallow scan: single=${single.stats}, contextual=${contextual.stats}")
    }

    @Test
    fun `class-static fact propagation is shared across argument type contexts`() {
        val single = measureShallowScan(classStaticConfig, "singleClassStaticContext", "classStaticHotMethod")
        val contextual = measureShallowScan(classStaticConfig, "classStaticContextExplosion", "classStaticHotMethod")

        assertEquals(setOf(classStaticRuleId), single.ruleIds)
        assertEquals(setOf(classStaticRuleId), contextual.ruleIds)

        assertTrue(
            contextual.stats.steps < single.stats.steps * 2,
            "six type contexts should share context-independent zero and ClassStatic analysis: " +
                "single=${single.stats}, contextual=${contextual.stats}",
        )
        println("ThingsBoard class-static shallow scan: single=${single.stats}, contextual=${contextual.stats}")
    }

    @Test
    fun `context support batching preserves exact method contexts`() {
        for (mode in listOf(ApMode.Tree, ApMode.BaseOnlyField)) {
            val ruleIds = runAnalysis(
                config = contextSupportConfig,
                entryPointClass = testClass,
                entryPointMethod = "contextSupportedSideEffectBatch",
                apMode = mode,
            ).mapTo(mutableSetOf()) { it.vulnerability.rule.id }

            assertEquals(
                setOf(taintedContextRuleId),
                ruleIds,
                "$mode must not attach the tainted local transfer to the unsupported SafeContext",
            )
        }
    }

    @Test
    fun `identical fact propagation is multiplied by its exact context support`() {
        val single = analyzeContextWorkload("singleContextSupportedSideEffect")
        val contextual = analyzeContextWorkload("contextSupportedSideEffectBatch")

        assertTrue(
            contextual.steps >= single.steps * 4,
            "seven contexts carrying the same fact must expose duplicated local work: " +
                "single=$single, contextual=$contextual",
        )
        println("ThingsBoard exact-context support: single=$single, contextual=$contextual")
    }

    private fun analyzeContextWorkload(entryPoint: String): MethodStats.Stats {
        var processStats: MethodStats.Stats? = null
        val ruleIds = runAnalysis(
            config = contextSupportConfig,
            entryPointClass = testClass,
            entryPointMethod = entryPoint,
            apMode = ApMode.BaseOnlyField,
        ) { analyzer, _ ->
            val processMethod = cp.findClassOrNull(testClass)!!.declaredMethods
                .single { it.name == "processContext" }
            processStats = analyzer.ifdsEngine.collectMethodStats().stats[processMethod]
        }.mapTo(mutableSetOf()) { it.vulnerability.rule.id }

        assertEquals(
            setOf(taintedContextRuleId),
            ruleIds,
            "$entryPoint must retain the exact context-to-sink association",
        )
        return requireNotNull(processStats)
    }

    private class ShallowScanMeasurement(val ruleIds: Set<String>, val stats: MethodStats.Stats)

    private fun measureShallowScan(
        config: SerializedTaintConfig,
        entryPointMethod: String,
        hotMethodName: String,
    ): ShallowScanMeasurement {
        val cls = checkNotNull(cp.findClassOrNull(testClass))
        val entryPoint = cls.declaredMethods.single { it.name == entryPointMethod }
        val hotMethod = cls.declaredMethods.single { it.name == hotMethodName }

        val taintConfig = TaintConfiguration(cp).also { it.loadConfig(config) }
        var rulesProvider: TaintRulesProvider = JIRTaintRulesProvider(taintConfig)
        rulesProvider = JIRMethodExitRuleProvider(rulesProvider)
        rulesProvider = customizeRulesProvider(rulesProvider)

        val usages = runBlocking { cp.usagesExt() }
        val graph = JIRSafeApplicationGraph(
            JTryBoundaryExceptionsApplicationGraph(JApplicationGraphImpl(cp, usages)),
        )

        val managerHolder = arrayOfNulls<JIRAnalysisManager>(1)
        val analyzer = object : TaintAnalyzer<JIRMethod, JIRInst>(
            TaintAnalyzerOptions(ifdsTimeout = 1.minutes, ifdsApMode = ApMode.BaseOnlyField),
        ) {
            override val unrollStrategy = AnyAccessorDisabled
            override fun analysisGraph(): ApplicationGraph<JIRMethod, JIRInst> = graph
            override fun analysisManager() =
                JIRAnalysisManager(cp, refManager, rulesProvider).also { managerHolder[0] = it }
            override fun unitResolver() = this@ThingsBoardEntityActionExplosionTest
                .unitResolver(cls.declaration.location)
        }

        return analyzer.use {
            val engine = it.ifdsEngine
            val manager = checkNotNull(managerHolder[0])
            val startMethods = listOf(MethodWithContext(entryPoint, EmptyMethodContext))

            manager.selectPhase(TaintAnalysisManager.Phase.Prescan)
            engine.resetApManager(TreeApManager(AnyAccessorDisabled, it.refManager, it.cancellation))
            engine.runAnalysis(startMethods, timeout = 1.minutes, cancellationTimeout = 30.seconds)
            val afterPrescan = engine.collectMethodStats()

            manager.selectPhase(TaintAnalysisManager.Phase.ShallowScan)
            engine.resetApManager(BaseOnlyApManager(AnyAccessorDisabled, it.cancellation, fieldSensitive = true))
            engine.runAnalysis(startMethods, timeout = 1.minutes, cancellationTimeout = 30.seconds)

            val shallowDelta = engine.collectMethodStats().subtract(afterPrescan)
            val ruleIds = engine.getVulnerabilities().mapTo(hashSetOf()) { v -> v.ruleId }
            ShallowScanMeasurement(ruleIds, checkNotNull(shallowDelta.stats[hotMethod]))
        }
    }
}

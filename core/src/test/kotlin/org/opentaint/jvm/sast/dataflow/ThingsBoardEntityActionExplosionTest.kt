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
import org.opentaint.dataflow.ifds.SingletonUnit
import org.opentaint.dataflow.ifds.UnitType
import org.opentaint.dataflow.ifds.UnknownUnit
import org.opentaint.dataflow.jvm.ifds.JIRUnitResolver
import org.opentaint.ir.api.jvm.JIRMethod
import org.opentaint.ir.api.jvm.RegisteredLocation
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

        val usages = runBlocking { cp.usagesExt() }
        val graph = JIRSafeApplicationGraph(JApplicationGraphImpl(cp, usages))

        val managerHolder = arrayOfNulls<JIRAnalysisManager>(1)
        val analyzer = object : TaintAnalyzer<JIRMethod, JIRInst>(
            TaintAnalyzerOptions(ifdsTimeout = 1.minutes, ifdsApMode = ApMode.BaseOnlyField),
        ) {
            override val unrollStrategy = AnyAccessorDisabled
            override fun analysisGraph(): ApplicationGraph<JIRMethod, JIRInst> = graph
            override fun analysisManager() =
                JIRAnalysisManager(cp, refManager, rulesProvider).also { managerHolder[0] = it }
            override fun unitResolver() = SingleLocationUnit(cls.declaration.location)
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

    private class SingleLocationUnit(private val location: RegisteredLocation) : JIRUnitResolver {
        override fun resolve(method: JIRMethod): UnitType =
            if (method.enclosingClass.declaration.location == location) SingletonUnit else UnknownUnit

        override fun locationIsUnknown(loc: RegisteredLocation): Boolean = loc != location
    }
}

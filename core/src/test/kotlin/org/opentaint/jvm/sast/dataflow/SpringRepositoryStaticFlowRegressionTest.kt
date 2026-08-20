package org.opentaint.jvm.sast.dataflow

import kotlinx.coroutines.runBlocking
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import org.opentaint.common.sast.dataflow.TaintAnalyzer
import org.opentaint.common.sast.dataflow.TaintAnalyzerOptions
import org.opentaint.dataflow.ap.ifds.EmptyMethodContext
import org.opentaint.dataflow.ap.ifds.MethodWithContext
import org.opentaint.dataflow.ap.ifds.TaintAnalysisManager
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.ApMode
import org.opentaint.dataflow.ap.ifds.access.baseonly.BaseOnlyApManager
import org.opentaint.dataflow.ap.ifds.access.tree.TreeApManager
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig
import org.opentaint.dataflow.ifds.SingletonUnit
import org.opentaint.dataflow.ifds.UnitType
import org.opentaint.dataflow.ifds.UnknownUnit
import org.opentaint.dataflow.jvm.ap.ifds.JIRSafeApplicationGraph
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRAnalysisManager
import org.opentaint.dataflow.jvm.ap.ifds.taint.TaintRulesProvider
import org.opentaint.dataflow.jvm.ifds.JIRUnitResolver
import org.opentaint.ir.api.jvm.JIRMethod
import org.opentaint.ir.api.jvm.RegisteredLocation
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.impl.features.usagesExt
import org.opentaint.jvm.graph.JApplicationGraphImpl
import org.opentaint.jvm.sast.dataflow.rules.TaintConfiguration
import org.opentaint.jvm.sast.project.spring.GeneratedSpringControllerDispatcher
import org.opentaint.jvm.sast.project.spring.GeneratedSpringControllerDispatcherDispatchMethod
import org.opentaint.jvm.sast.project.spring.SpringRuleProvider
import org.opentaint.util.analysis.ApplicationGraph
import kotlin.time.Duration.Companion.minutes
import kotlin.time.Duration.Companion.seconds

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class SpringRepositoryStaticFlowRegressionTest : AnalysisTest() {
    companion object {
        private const val SAMPLE_CLASS = "test.samples.SpringRepositoryStaticFlowSample"
        private const val TAINT_MARK = "tainted"
        private const val RULE_ID = "spring-repository-static-flow"
    }

    override val sourceFileExtension: String = "java"

    override fun customizeRulesProvider(rulesProvider: TaintRulesProvider): TaintRulesProvider =
        SpringRuleProvider(rulesProvider, checkNotNull(context.springWebProjectContext))

    @Test
    fun `repository state saved by one controller action reaches another action with BaseOnly`() {
        val config = SerializedTaintConfig(
            entryPoint = listOf(entryPointRule(SAMPLE_CLASS, "update", TAINT_MARK, argIndex = 0)),
            sink = listOf(sinkRule(SAMPLE_CLASS, "sink", RULE_ID, listOf(Argument(0) to TAINT_MARK))),
        )

        val treeRules = analyzeForward(config, ApMode.Tree)
        val baseOnlyRules = analyzeForward(config, ApMode.BaseOnlyField)

        assertEquals(setOf(RULE_ID), treeRules)
        assertEquals(setOf(RULE_ID), baseOnlyRules)
    }

    private fun analyzeForward(config: SerializedTaintConfig, mode: ApMode): Set<String> {
        val noUnroll = object : AnyAccessorUnrollStrategy {
            override fun unrollAccessor(accessor: Accessor): Boolean = false
        }
        val dispatcher = checkNotNull(cp.findClassOrNull(GeneratedSpringControllerDispatcher))
            .declaredMethods.single { it.name == GeneratedSpringControllerDispatcherDispatchMethod }

        val taintConfig = TaintConfiguration(cp).also { it.loadConfig(config) }
        var rulesProvider: TaintRulesProvider = JIRTaintRulesProvider(taintConfig)
        rulesProvider = JIRMethodExitRuleProvider(rulesProvider)
        rulesProvider = customizeRulesProvider(rulesProvider)

        val usages = runBlocking { cp.usagesExt() }
        val graph = JIRSafeApplicationGraph(
            JTryBoundaryExceptionsApplicationGraph(JApplicationGraphImpl(cp, usages)),
        )
        val projectLocation = dispatcher.enclosingClass.declaration.location
        val unitResolver = object : JIRUnitResolver {
            override fun resolve(method: JIRMethod): UnitType =
                if (method.enclosingClass.declaration.location == projectLocation ||
                    DataFlowApproximationLoader.isApproximation(method)
                ) SingletonUnit else UnknownUnit

            override fun locationIsUnknown(loc: RegisteredLocation): Boolean = loc != projectLocation
        }

        val analysisManagerHolder = arrayOfNulls<JIRAnalysisManager>(1)
        val analyzer = object : TaintAnalyzer<JIRMethod, JIRInst>(
            TaintAnalyzerOptions(ifdsTimeout = 1.minutes, ifdsApMode = mode),
        ) {
            override val unrollStrategy = noUnroll
            override fun analysisGraph(): ApplicationGraph<JIRMethod, JIRInst> = graph
            override fun analysisManager(): JIRAnalysisManager = JIRAnalysisManager(
                cp,
                refManager,
                rulesProvider,
            ).also { analysisManagerHolder[0] = it }
            override fun unitResolver(): JIRUnitResolver = unitResolver
        }

        return analyzer.use {
            val engine = it.ifdsEngine
            val analysisManager = checkNotNull(analysisManagerHolder[0])
            val startMethods = listOf(MethodWithContext(dispatcher, EmptyMethodContext))

            analysisManager.selectPhase(TaintAnalysisManager.Phase.Prescan)
            engine.resetApManager(TreeApManager(noUnroll, it.refManager, it.cancellation))
            engine.runAnalysis(startMethods, timeout = 1.minutes, cancellationTimeout = 30.seconds)

            analysisManager.selectPhase(TaintAnalysisManager.Phase.ShallowScan)
            engine.resetApManager(
                when (mode) {
                    ApMode.Tree -> TreeApManager(noUnroll, it.refManager, it.cancellation)
                    ApMode.BaseOnlyField -> BaseOnlyApManager(noUnroll, it.cancellation, fieldSensitive = true)
                    else -> error("Unsupported test mode: $mode")
                },
            )
            engine.runAnalysis(startMethods, timeout = 1.minutes, cancellationTimeout = 30.seconds)
            engine.getVulnerabilities().mapTo(hashSetOf()) { vulnerability -> vulnerability.ruleId }
        }
    }
}

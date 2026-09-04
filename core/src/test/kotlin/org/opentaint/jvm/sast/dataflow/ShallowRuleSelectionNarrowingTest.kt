package org.opentaint.jvm.sast.dataflow

import kotlinx.coroutines.runBlocking
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import org.opentaint.common.sast.dataflow.TaintAnalyzer
import org.opentaint.common.sast.dataflow.TaintAnalyzerOptions
import org.opentaint.config.JavaDefaultConfigLoader
import org.opentaint.dataflow.ap.ifds.EmptyMethodContext
import org.opentaint.dataflow.ap.ifds.MethodWithContext
import org.opentaint.dataflow.ap.ifds.TaintAnalysisManager
import org.opentaint.dataflow.ap.ifds.TaintAnalysisUnitRunnerManager
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy.AnyAccessorDisabled
import org.opentaint.dataflow.ap.ifds.access.ApMode
import org.opentaint.dataflow.ap.ifds.access.baseonly.BaseOnlyApManager
import org.opentaint.dataflow.ap.ifds.access.tree.TreeApManager
import org.opentaint.dataflow.ap.ifds.taint.TaintSinkTracker
import org.opentaint.dataflow.ap.ifds.trace.ExactProcessingTimeBudget
import org.opentaint.dataflow.ap.ifds.trace.TraceResolver
import org.opentaint.dataflow.ap.ifds.trace.action.ActionableRulesCollectionResult
import org.opentaint.dataflow.ap.ifds.trace.action.mergeActionableRules
import org.opentaint.dataflow.configuration.CommonTaintAction
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
import org.opentaint.dataflow.configuration.jvm.TaintEntryPointSource
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedRule
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintAssignAction
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig
import org.opentaint.dataflow.ifds.SingletonUnit
import org.opentaint.dataflow.ifds.UnitType
import org.opentaint.dataflow.ifds.UnknownUnit
import org.opentaint.dataflow.jvm.ap.ifds.JIRSafeApplicationGraph
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRAnalysisManager
import org.opentaint.dataflow.jvm.ap.ifds.taint.TaintRulesProvider
import org.opentaint.dataflow.jvm.ifds.JIRUnitResolver
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst
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

private typealias SelectedRules = Map<CommonInst, Map<CommonTaintConfigurationItem, Set<CommonTaintAction>>>

/**
 * Pins the recall cost of deriving the full scan's rule set from the shallow scan.
 *
 * The staged pipeline resolves traces for the field-insensitive shallow discoveries, collects the
 * rules those traces visited, and then restricts the field-sensitive full scan to exactly that set
 * ([JIRAnalysisManager.selectPhase], `Phase.FullScan -> phaseTaintConfig.select(actionableRules)`).
 * A flow whose real path needs a source statement the shallow traces never visited therefore cannot
 * be reported, even though the full scan alone finds it.
 *
 * The restricted and unrestricted arms both end in a field-sensitive Tree pass. The decisive
 * comparison is between two `Phase.FullScan` arms that differ only in two map entries, so no
 * phase-dependent behaviour other than rule selection can explain the difference.
 */
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class ShallowRuleSelectionNarrowingTest : AnalysisTest() {
    companion object {
        private const val SAMPLE_CLASS = "test.samples.ShallowRuleSelectionSample"
        private const val TAINT_MARK = "tainted"
        private const val RULE_ID = "shallow-rule-selection"
    }

    override val sourceFileExtension: String = "java"

    override fun customizeRulesProvider(rulesProvider: TaintRulesProvider): TaintRulesProvider =
        SpringRuleProvider(rulesProvider, checkNotNull(context.springWebProjectContext))

    private fun multiArgEntryPointRule(methodName: String, vararg argIndices: Int) =
        SerializedRule.EntryPoint(
            function = functionMatcher(SAMPLE_CLASS, methodName),
            taint = argIndices.map { idx ->
                SerializedTaintAssignAction(
                    kind = TAINT_MARK,
                    pos = PositionBaseWithModifiers.BaseOnly(Argument(idx)),
                )
            },
        )

    private val config
        get() = SerializedTaintConfig(
            entryPoint = listOf(
                entryPointRule(SAMPLE_CLASS, "upload", TAINT_MARK, argIndex = 0),
                entryPointRule(SAMPLE_CLASS, "echo", TAINT_MARK, argIndex = 0),
            ),
            sink = listOf(sinkRule(SAMPLE_CLASS, "sink", RULE_ID, listOf(Argument(0) to TAINT_MARK))),
        )

    private data class Run(
        val shallowDiscoveries: Set<String>,
        val selection: SelectedRules,
        val fullScanDiscoveries: Set<String>,
        val vulnerabilityStatements: Map<String, CommonInst>,
    )

    @Test
    fun `a source rule keeps only the actions the shallow trace needed`() {
        val twoArgConfig = SerializedTaintConfig(
            entryPoint = listOf(multiArgEntryPointRule("echoSecond", 0, 1)),
            sink = listOf(sinkRule(SAMPLE_CLASS, "sink", RULE_ID, listOf(Argument(0) to TAINT_MARK))),
        )

        val run = runPipeline(restrictFullScan = true, config = twoArgConfig)
        assertEquals(setOf("echoSecond"), run.fullScanDiscoveries)

        val narrowed = run.selection.values
            .flatMap { it.entries }
            .filter { (rule, _) -> rule is TaintEntryPointSource }
            .map { (rule, actions) -> (rule as TaintEntryPointSource).actionsAfter.size to actions.size }

        assertEquals(
            listOf(4 to 2), narrowed,
            "the Spring entry point rule carries one action per argument, doubled by " +
                "SpringRuleProvider.taintObjectFields into {arg, arg.*}; only the two actions on the " +
                "argument the shallow trace walked survive relevantActions()",
        )
    }

    private fun runPipeline(
        restrictFullScan: Boolean,
        config: SerializedTaintConfig = this.config,
        extraRules: (TaintRulesProvider) -> SelectedRules = { emptyMap() },
    ): Run {
        val dispatcher = checkNotNull(cp.findClassOrNull(GeneratedSpringControllerDispatcher))
            .declaredMethods.single { it.name == GeneratedSpringControllerDispatcherDispatchMethod }

        val taintConfig = TaintConfiguration(cp).also { it.loadConfig(config) }
        JavaDefaultConfigLoader.loadConfig()?.let { defaults ->
            taintConfig.loadConfig(SerializedTaintConfig(passThrough = defaults.passThrough))
        }

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

        val managerHolder = arrayOfNulls<JIRAnalysisManager>(1)
        val analyzer = object : TaintAnalyzer<JIRMethod, JIRInst>(
            TaintAnalyzerOptions(ifdsTimeout = 2.minutes, ifdsApMode = ApMode.Tree),
        ) {
            override fun analysisGraph(): ApplicationGraph<JIRMethod, JIRInst> = graph
            override fun analysisManager(): JIRAnalysisManager =
                JIRAnalysisManager(cp, refManager, rulesProvider).also { managerHolder[0] = it }

            override fun unitResolver(): JIRUnitResolver = unitResolver
        }

        return analyzer.use {
            val engine = it.ifdsEngine
            val manager = checkNotNull(managerHolder[0])
            val startMethods = listOf(MethodWithContext(dispatcher, EmptyMethodContext))
            val entryPoints = setOf<CommonMethod>(dispatcher)

            manager.selectPhase(TaintAnalysisManager.Phase.Prescan)
            engine.resetApManager(TreeApManager(AnyAccessorDisabled, it.refManager, it.cancellation))
            engine.runAnalysis(startMethods, timeout = 1.minutes, cancellationTimeout = 30.seconds)

            val shallowManager = BaseOnlyApManager(it.unrollStrategy, it.cancellation, fieldSensitive = true)
            manager.selectPhase(TaintAnalysisManager.Phase.ShallowScan)
            engine.resetApManager(shallowManager)
            engine.runAnalysis(startMethods, timeout = 1.minutes, cancellationTimeout = 30.seconds)
            engine.cleanup()

            val shallowVulnerabilities = engine.confirmVulnerabilities(
                entryPoints, engine.getVulnerabilities(), 1.minutes, cancellationTimeout = 30.seconds,
            )
            val selection = collectRules(engine, shallowManager, entryPoints, shallowVulnerabilities)

            val installed = selection + extraRules(rulesProvider)
            manager.selectPhase(
                if (restrictFullScan) {
                    TaintAnalysisManager.Phase.FullScan(installed)
                } else {
                    TaintAnalysisManager.Phase.ShallowScan
                }
            )
            engine.resetApManager(TreeApManager(it.unrollStrategy, it.refManager, it.cancellation))
            engine.runAnalysis(startMethods, timeout = 1.minutes, cancellationTimeout = 30.seconds)
            engine.cleanup()

            val found = engine.getVulnerabilities()
            Run(
                shallowDiscoveries = shallowVulnerabilities.mapTo(hashSetOf()) { v ->
                    v.statement.location.method.name
                },
                selection = selection,
                fullScanDiscoveries = found.mapTo(hashSetOf()) { v -> v.statement.location.method.name },
                vulnerabilityStatements = found.associateBy({ v -> v.statement.location.method.name }) { v ->
                    v.statement
                },
            )
        }
    }

    private fun collectRules(
        engine: TaintAnalysisUnitRunnerManager,
        shallowManager: BaseOnlyApManager,
        entryPoints: Set<CommonMethod>,
        vulnerabilities: List<TaintSinkTracker.TaintVulnerability>,
    ): SelectedRules {
        if (vulnerabilities.isEmpty()) return emptyMap()
        shallowManager.enableTraceResolutionMode()
        val budget = ExactProcessingTimeBudget<TaintSinkTracker.TaintVulnerability>(10.seconds)
        val interProceduralTraces = engine.resolveVulnerabilityInterProceduralTraces(
            entryPoints, vulnerabilities,
            resolverParams = TraceResolver.Params(
                resolveEntryPointToStartTrace = false,
                resolveAllTraces = true,
            ),
            timeout = 1.minutes,
            cancellationTimeout = 30.seconds,
            exactTimeBudget = budget,
        )
        val results = engine.resolveVulnerabilityActionableRules(
            interProceduralTraces, timeout = 1.minutes, cancellationTimeout = 30.seconds,
            exactTimeBudget = budget,
        )
        return mergeActionableRules(results.filterIsInstance<ActionableRulesCollectionResult.Collected>())
    }
}

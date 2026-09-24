package org.opentaint.jvm.sast.dataflow.backward

import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.ap.ifds.EmptyMethodContext
import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.MethodWithContext
import org.opentaint.dataflow.ap.ifds.TaintAnalysisManager
import org.opentaint.dataflow.ap.ifds.TaintAnalysisUnitRunnerManager
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.ApMode
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.automata.AutomataApManager
import org.opentaint.dataflow.ap.ifds.access.baseonly.BaseOnlyApManager
import org.opentaint.dataflow.ap.ifds.access.cactus.CactusApManager
import org.opentaint.dataflow.ap.ifds.access.tree.TreeApManager
import org.opentaint.dataflow.configuration.jvm.TaintMethodSource
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig
import org.opentaint.dataflow.graph.reversed
import org.opentaint.dataflow.ifds.UnitResolver
import org.opentaint.dataflow.jvm.ap.ifds.backward.JIRBackwardAnalysisManager
import org.opentaint.dataflow.jvm.ap.ifds.backward.JIRBackwardFindingTracker
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.RefManager
import org.opentaint.common.sast.dataflow.DummySerializationContext
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.jvm.sast.dataflow.AnalysisTest
import org.opentaint.util.analysis.ApplicationGraph
import kotlin.time.Duration.Companion.minutes
import kotlin.time.Duration.Companion.seconds

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
abstract class BackwardAnalysisTest : AnalysisTest() {
    data class BackwardResult(
        val status: TaintAnalysisUnitRunnerManager.Status,
        val sourceFindings: List<JIRBackwardFindingTracker.BackwardSourceFinding>,
        val unconditionalSinks: List<JIRBackwardFindingTracker.BackwardUnconditionalSink>,
        val demandSeeds: List<JIRBackwardFindingTracker.BackwardDemandSeed>,
        val analyzedMethods: Set<CommonMethod>,
        val statementFacts: Map<CommonInst, Set<FinalFactAp>>,
    )

    fun runBackwardAnalysis(
        config: SerializedTaintConfig,
        entryPointClass: String,
        entryPointMethod: String,
        stagedRuleSelection: Boolean = false,
    ): BackwardResult {
        val ep = findEntryPoint(entryPointClass, entryPointMethod)
        val rulesProvider = createRulesProvider(config).let { if (stagedRuleSelection) RuleIdSelectingProvider(it) else it }

        @Suppress("UNCHECKED_CAST")
        val backwardGraph = createAnalysisGraph().reversed as ApplicationGraph<CommonMethod, CommonInst>

        val refManager = RefManager()
        val cancellation = Cancellation()
        val manager = JIRBackwardAnalysisManager(cp, refManager, rulesProvider, recordDemandSeeds = true)

        @Suppress("UNCHECKED_CAST")
        val engine = TaintAnalysisUnitRunnerManager(
            refManager, cancellation,
            manager,
            backwardGraph,
            SingleLocationUnit(ep.enclosingClass.declaration.location) as UnitResolver<CommonMethod>,
            DummySerializationContext,
            taintRulesStatsSamplingPeriod = null,
        )

        val startMethods = listOf(MethodWithContext(ep, EmptyMethodContext))
        return engine.use {
            if (stagedRuleSelection) {
                manager.selectPhase(TaintAnalysisManager.Phase.Prescan)
                it.resetApManager(createApManager(cancellation, refManager))
                it.runAnalysis(startMethods, timeout = 1.minutes, cancellationTimeout = 10.seconds)
                it.cleanup()
            }

            manager.selectPhase(TaintAnalysisManager.Phase.FullScan())
            it.resetApManager(createApManager(cancellation, refManager))
            it.runAnalysis(startMethods, timeout = 1.minutes, cancellationTimeout = 10.seconds)

            BackwardResult(
                status = it.status.get(),
                sourceFindings = manager.findings.sourceFindings(),
                unconditionalSinks = manager.findings.unconditionalSinks(),
                demandSeeds = manager.findings.demandSeeds(),
                analyzedMethods = it.collectMethodStats().stats.keys.toSet(),
                statementFacts = it.statementFacts(),
            )
        }
    }

    private fun TaintAnalysisUnitRunnerManager.statementFacts(): Map<CommonInst, Set<FinalFactAp>> {
        val result = hashMapOf<CommonInst, MutableSet<FinalFactAp>>()
        for (unit in allUnits()) {
            val runner = findUnitRunner(unit) ?: continue
            val runnerFacts = hashMapOf<MethodEntryPoint, Map<CommonInst, Set<FinalFactAp>>>()
            runner.collectAllIntraProceduralFacts(runnerFacts)
            for (statementFacts in runnerFacts.values) {
                for ((statement, facts) in statementFacts) {
                    result.getOrPut(statement, ::hashSetOf).addAll(facts)
                }
            }
        }
        return result
    }

    private fun createApManager(cancellation: Cancellation, refManager: RefManager) = when (apMode) {
        ApMode.Tree -> TreeApManager(analysisUnrollStrategy, refManager, cancellation)
        ApMode.Cactus -> CactusApManager(analysisUnrollStrategy, cancellation)
        ApMode.Automata -> AutomataApManager(analysisUnrollStrategy, cancellation)
        ApMode.BaseOnly -> BaseOnlyApManager(analysisUnrollStrategy, cancellation, fieldSensitive = false)
        ApMode.BaseOnlyField -> BaseOnlyApManager(analysisUnrollStrategy, cancellation, fieldSensitive = true)
    }

    fun BackwardResult.reachedSources(sourceMethodName: String, mark: String): List<JIRBackwardFindingTracker.BackwardSourceFinding> =
        sourceFindings.filter { finding ->
            val rule = finding.rule
            finding.mark == TaintMarkAccessor(mark) &&
                rule is TaintMethodSource && rule.method.name == sourceMethodName
        }

    fun assertSourceReached(
        config: SerializedTaintConfig,
        testCls: String,
        entryPointName: String,
        sourceMethodName: String,
        mark: String,
        testName: String,
    ) {
        val result = runBackwardAnalysis(config, testCls, entryPointName)
        assertEquals(TaintAnalysisUnitRunnerManager.Status.OK, result.status, "$testName: analysis status")
        assertTrue(
            result.reachedSources(sourceMethodName, mark).isNotEmpty(),
            "$testName: expected a sink demand for mark $mark to reach source $sourceMethodName, got ${result.sourceFindings}"
        )
    }

    fun assertNoSourceReached(
        config: SerializedTaintConfig,
        testCls: String,
        entryPointName: String,
        testName: String,
    ) {
        val result = runBackwardAnalysis(config, testCls, entryPointName)
        assertEquals(TaintAnalysisUnitRunnerManager.Status.OK, result.status, "$testName: analysis status")
        assertTrue(
            result.sourceFindings.isEmpty(),
            "$testName: expected no source to be reached, got ${result.sourceFindings}"
        )
    }
}

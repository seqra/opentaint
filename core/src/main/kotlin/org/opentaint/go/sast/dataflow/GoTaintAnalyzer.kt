package org.opentaint.go.sast.dataflow

import org.opentaint.dataflow.ap.ifds.EmptyMethodContext
import org.opentaint.dataflow.ap.ifds.MethodWithContext
import org.opentaint.dataflow.ap.ifds.TaintAnalysisUnitRunnerManager
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.tree.TreeApManager
import org.opentaint.dataflow.ap.ifds.taint.ExternalMethodTracker
import org.opentaint.dataflow.ap.ifds.trace.TraceResolver
import org.opentaint.dataflow.ap.ifds.trace.VulnerabilityWithTrace
import org.opentaint.dataflow.go.analysis.GoAnalysisManager
import org.opentaint.dataflow.go.graph.GoApplicationGraph
import org.opentaint.dataflow.go.rules.GoTaintRulesProvider
import org.opentaint.dataflow.ifds.UnitResolver
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.api.GoIRProgram
import org.opentaint.jvm.sast.dataflow.DummySerializationContext
import org.opentaint.util.analysis.ApplicationGraph
import kotlin.time.Duration
import kotlin.time.Duration.Companion.minutes
import kotlin.time.Duration.Companion.seconds

class GoTaintAnalyzer(
    private val cp: GoIRProgram,
    private val taintConfig: GoTaintRulesProvider,
    private val unitResolver: UnitResolver<GoIRFunction>,
    private val externalMethodTracker: ExternalMethodTracker? = null,
    private val analysisTimeout: Duration = 1.minutes,
    private val cancellationTimeout: Duration = 10.seconds,
) {
    @Suppress("UNCHECKED_CAST")
    fun analyzeWithIfds(entryPoints: List<GoIRFunction>): List<VulnerabilityWithTrace> {
        val ifdsGraph = GoApplicationGraph(cp, unitResolver)

        val engine = TaintAnalysisUnitRunnerManager(
            GoAnalysisManager(cp, taintConfig, externalMethodTracker = externalMethodTracker),
            ifdsGraph as ApplicationGraph<CommonMethod, CommonInst>,
            unitResolver = unitResolver as UnitResolver<CommonMethod>,
            apManager = TreeApManager(anyAccessorUnrollStrategy = AnyAccessorUnrollStrategy.AnyAccessorDisabled),
            summarySerializationContext = DummySerializationContext,
            taintRulesStatsSamplingPeriod = null,
        )

        val startMethods = entryPoints.map { MethodWithContext(it, EmptyMethodContext) }
        return engine.use { eng ->
            eng.runAnalysis(startMethods, timeout = analysisTimeout, cancellationTimeout = cancellationTimeout)
            val vulnerabilities = eng.getVulnerabilities()
            eng.resolveVulnerabilityTraces(
                entryPoints.toSet(), vulnerabilities,
                resolverParams = TraceResolver.Params(),
                timeout = analysisTimeout, cancellationTimeout = cancellationTimeout,
            ).filter { it.trace != null }
        }
    }
}

package org.opentaint.go.sast.dataflow

import org.opentaint.common.sast.dataflow.TaintAnalyzer
import org.opentaint.common.sast.dataflow.TaintAnalyzerOptions
import org.opentaint.dataflow.ap.ifds.taint.ExternalMethodTracker
import org.opentaint.dataflow.go.analysis.GoAnalysisManager
import org.opentaint.dataflow.go.graph.GoApplicationGraph
import org.opentaint.dataflow.go.rules.GoTaintRulesProvider
import org.opentaint.dataflow.ifds.UnitResolver
import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.api.GoIRProgram
import org.opentaint.ir.go.inst.GoIRInst

class GoTaintAnalyzer(
    private val cp: GoIRProgram,
    private val taintConfig: GoTaintRulesProvider,
    private val unitResolver: UnitResolver<GoIRFunction>,
    options: TaintAnalyzerOptions,
    externalMethodTracker: ExternalMethodTracker? = null,
) : TaintAnalyzer<GoIRFunction, GoIRInst>(options, externalMethodTracker) {
    override fun analysisGraph() = GoApplicationGraph(cp, unitResolver)
    override fun analysisManager() = GoAnalysisManager(cp, taintConfig, externalMethodTracker = externalMethodTracker)
    override fun unitResolver(): UnitResolver<GoIRFunction> = unitResolver
}

package org.opentaint.dataflow.ap.ifds

import org.opentaint.dataflow.ap.ifds.analysis.AnalysisManager
import org.opentaint.dataflow.ap.ifds.analysis.MethodAnalysisContext
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallResolver
import org.opentaint.dataflow.ap.ifds.taint.TaintAnalysisContext
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.util.analysis.ApplicationGraph

interface TaintAnalysisManager : AnalysisManager {
    sealed interface Phase {
        data object Init : Phase

        data class Prescan(
            val scopeMethods: Collection<CommonMethod>,
            val graph: ApplicationGraph<CommonMethod, CommonInst>,
        ) : Phase

        data object FullScan : Phase
    }

    fun selectPhase(phase: Phase)

    override fun getMethodAnalysisContext(
        methodEntryPoint: MethodEntryPoint,
        graph: ApplicationGraph<CommonMethod, CommonInst>,
        callResolver: MethodCallResolver,
        contextForEmptyMethod: MethodAnalysisContext?,
    ): MethodAnalysisContext {
        error("Taint context required")
    }

    fun getMethodAnalysisContext(
        methodEntryPoint: MethodEntryPoint,
        graph: ApplicationGraph<CommonMethod, CommonInst>,
        callResolver: MethodCallResolver,
        taintAnalysisContext: TaintAnalysisContext,
        contextForEmptyMethod: MethodAnalysisContext?,
    ): MethodAnalysisContext
}

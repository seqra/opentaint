package org.opentaint.dataflow.ap.ifds

import org.opentaint.dataflow.ap.ifds.analysis.AnalysisManager
import org.opentaint.dataflow.ap.ifds.analysis.MethodAnalysisContext
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallResolver
import org.opentaint.dataflow.ap.ifds.markset.MarkSetRecorder
import org.opentaint.dataflow.ap.ifds.taint.ActionableRules
import org.opentaint.dataflow.ap.ifds.taint.TaintAnalysisContext
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.util.analysis.ApplicationGraph

interface TaintAnalysisManager : AnalysisManager {
    sealed interface Phase {
        data object Prescan : Phase
        data object FullScan : Phase
    }

    fun selectPhase(phase: Phase)

    /** Non-null only for JVM with the mark-set scan on (spec §10). Go keeps the default. */
    fun markSetRecorder(): MarkSetRecorder? = null

    /** Installs the mark-set scan's selection (spec §10). Go keeps the no-op default. */
    fun selectStatementRules(rules: ActionableRules?, coveredStatements: Set<CommonInst>) {}

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

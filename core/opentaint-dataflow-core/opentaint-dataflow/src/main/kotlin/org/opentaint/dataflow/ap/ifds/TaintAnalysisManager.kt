package org.opentaint.dataflow.ap.ifds

import org.opentaint.dataflow.ap.ifds.analysis.AnalysisManager
import org.opentaint.dataflow.ap.ifds.analysis.MethodAnalysisContext
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallResolver
import org.opentaint.dataflow.ap.ifds.taint.ActionableRules
import org.opentaint.dataflow.ap.ifds.taint.TaintAnalysisContext
import org.opentaint.dataflow.configuration.CommonTaintAction
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.util.analysis.ApplicationGraph

interface TaintAnalysisManager : AnalysisManager {
    val supportsForwardActionableRuleFallback: Boolean
        get() = false

    fun relevantForwardActionableRules(
        rules: ActionableRules,
        uncoveredSinkRules: Set<CommonTaintConfigurationItem>,
    ): ActionableRules = rules

    sealed interface Phase {
        data object Prescan : Phase
        data object ShallowScan : Phase
        data class FullScan(val actionableRules: Map<CommonInst, Map<CommonTaintConfigurationItem, Set<CommonTaintAction>>>) : Phase
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

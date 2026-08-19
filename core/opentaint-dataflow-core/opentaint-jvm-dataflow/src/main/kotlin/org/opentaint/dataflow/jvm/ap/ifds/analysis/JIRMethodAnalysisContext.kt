package org.opentaint.dataflow.jvm.ap.ifds.analysis

import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.TaintAnalysisManager.Phase
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.analysis.MethodAnalysisContext
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFactMapper
import org.opentaint.dataflow.configuration.CommonTaintAction
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
import org.opentaint.dataflow.ap.ifds.trace.MethodCallPrecondition.CallPrecondition
import org.opentaint.dataflow.ap.ifds.trace.MethodSequentPrecondition.SequentPrecondition
import org.opentaint.dataflow.jvm.ap.ifds.JIRFactTypeChecker
import org.opentaint.dataflow.jvm.ap.ifds.JIRCallResolver
import org.opentaint.dataflow.jvm.ap.ifds.JIRLambdaTracker
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalVariableReachability
import org.opentaint.dataflow.jvm.ap.ifds.JIRMethodCallFactMapper
import org.opentaint.dataflow.jvm.ap.ifds.taint.JIRTaintAnalysisContext
import org.opentaint.dataflow.util.SoftReferenceManager
import org.opentaint.dataflow.util.int2ObjectMap
import org.opentaint.ir.api.common.cfg.CommonInst
import java.lang.ref.Reference

class JIRMethodAnalysisContext(
    val analysisManager: JIRAnalysisManager,
    val refManager: SoftReferenceManager,
    override val methodEntryPoint: MethodEntryPoint,
    val factTypeChecker: JIRFactTypeChecker,
    val localVariableReachability: JIRLocalVariableReachability,
    val aliasAnalysis: JIRLocalAliasAnalysis?,
    val taint: JIRTaintAnalysisContext,
    val callResolver: JIRCallResolver,
) : MethodAnalysisContext {
    init {
        taint.bindAnalysisContext(this)
    }

    val phase: Phase get() = analysisManager.phase

    fun recordForwardSourceAction(
        statement: CommonInst,
        rule: CommonTaintConfigurationItem,
        action: CommonTaintAction,
    ) {
        if (phase !is Phase.ShallowScan) return
        taint.taintSinkTracker.recordForwardActionableRule(statement, rule, action)
    }

    override val methodCallFactMapper: MethodCallFactMapper
        get() = JIRMethodCallFactMapper

    val taintMarksAssignedOnMethodEnter = hashSetOf<TaintMarkAccessor>()

    val lambdaCallResolution = Int2ObjectOpenHashMap<JIRLambdaTracker.LambdaTracker>()

    private val rawCallResolutionCache =
        int2ObjectMap<List<JIRCallResolver.MethodResolutionResult>>()

    fun cachedRawCallResolution(
        stmtIdx: Int,
        resolve: () -> List<JIRCallResolver.MethodResolutionResult>,
    ): List<JIRCallResolver.MethodResolutionResult> =
        rawCallResolutionCache.computeIfAbsent(stmtIdx) { resolve() }

    fun cachedCallFF(stmtIdx: Int, body: () -> JIRMethodCallFlowFunction): JIRMethodCallFlowFunction =
        getCallFFCache().computeIfAbsent(stmtIdx) { body() }

    fun cachedCallSH(stmtIdx: Int, body: () -> JIRMethodCallSummaryHandler): JIRMethodCallSummaryHandler =
        getCallSHCache().computeIfAbsent(stmtIdx) { body() }

    private var callFFCache: Reference<Int2ObjectOpenHashMap<JIRMethodCallFlowFunction>>? = null
    private fun getCallFFCache(): Int2ObjectOpenHashMap<JIRMethodCallFlowFunction> {
        callFFCache?.get()?.let { return it }
        return int2ObjectMap<JIRMethodCallFlowFunction>().also {
            callFFCache = refManager.createRef(it)
        }
    }

    private var callSHCache: Reference<Int2ObjectOpenHashMap<JIRMethodCallSummaryHandler>>? = null
    private fun getCallSHCache(): Int2ObjectOpenHashMap<JIRMethodCallSummaryHandler> {
        callSHCache?.get()?.let { return it }
        return int2ObjectMap<JIRMethodCallSummaryHandler>().also {
            callSHCache = refManager.createRef(it)
        }
    }

    fun resetAnalysisCache() {
        taint.reset()
        lambdaCallResolution.values.forEach { it.resetSubscribers() }
        taintMarksAssignedOnMethodEnter.clear()
        rawCallResolutionCache.clear()
        callFFCache?.clear()
        callSHCache?.clear()
    }
}

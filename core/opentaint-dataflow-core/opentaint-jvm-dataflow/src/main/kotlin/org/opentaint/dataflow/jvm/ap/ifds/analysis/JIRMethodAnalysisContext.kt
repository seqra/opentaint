package org.opentaint.dataflow.jvm.ap.ifds.analysis

import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.TaintAnalysisManager.Phase
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodAnalysisContext
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFactMapper
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
import java.lang.ref.Reference
import java.util.concurrent.ConcurrentHashMap

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

    override val methodCallFactMapper: MethodCallFactMapper
        get() = JIRMethodCallFactMapper

    val taintMarksAssignedOnMethodEnter = hashSetOf<TaintMarkAccessor>()

    val lambdaCallResolution = Int2ObjectOpenHashMap<JIRLambdaTracker.LambdaTracker>()

    private val rawCallResolutionCache =
        int2ObjectMap<List<JIRCallResolver.MethodResolutionResult>>()

    private data class TracePreconditionKey(
        val apManager: ApManager,
        val statementIndex: Int,
        val fact: InitialFactAp,
    )

    private class TracePreconditionCache {
        val sequent = ConcurrentHashMap<TracePreconditionKey, Set<SequentPrecondition>>()
        val call = ConcurrentHashMap<TracePreconditionKey, List<CallPrecondition>>()
    }

    @Volatile
    private var tracePreconditionCache: TracePreconditionCache? = null

    private fun tracePreconditionCache(): TracePreconditionCache {
        tracePreconditionCache?.let { return it }
        return synchronized(this) {
            tracePreconditionCache ?: TracePreconditionCache().also { tracePreconditionCache = it }
        }
    }

    fun cachedSequentTracePrecondition(
        apManager: ApManager,
        stmtIdx: Int,
        fact: InitialFactAp,
        compute: () -> Set<SequentPrecondition>,
    ): Set<SequentPrecondition> {
        val cache = tracePreconditionCache()
        return cache.sequent.computeIfAbsent(TracePreconditionKey(apManager, stmtIdx, fact)) {
            compute().toSet()
        }
    }

    fun cachedCallTracePrecondition(
        apManager: ApManager,
        stmtIdx: Int,
        fact: InitialFactAp,
        compute: () -> List<CallPrecondition>,
    ): List<CallPrecondition> {
        val cache = tracePreconditionCache()
        return cache.call.computeIfAbsent(TracePreconditionKey(apManager, stmtIdx, fact)) {
            compute().toList()
        }
    }

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
        tracePreconditionCache = null
        callFFCache?.clear()
        callSHCache?.clear()
    }
}

package org.opentaint.dataflow.python.alias

import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import org.opentaint.dataflow.ap.ifds.LanguageManager
import org.opentaint.dataflow.ap.ifds.analysis.alias.ContextInfo
import org.opentaint.dataflow.ap.ifds.analysis.alias.ImmutableState
import org.opentaint.dataflow.python.PIRCallResolver
import org.opentaint.dataflow.python.graph.PIRUnknownFunction
import org.opentaint.dataflow.python.util.PIRFlowFunctionUtils
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.python.PIRCall
import org.opentaint.ir.api.python.PIRCallArgKind
import org.opentaint.ir.api.python.PIRFunction
import org.opentaint.util.analysis.ApplicationGraph
import java.util.BitSet
import org.opentaint.dataflow.python.util.indexOfKeywordParam

/**
 * Inter-procedural call inlining support, mirroring the JVM `InterProcCallNode`.
 * A resolved call is inlined by analyzing the callee's graph from the caller's
 * current state, with the callee's parameter references substituted by the
 * caller-frame actuals via [NestedCallInstEvalCtx].
 *
 * Declaration order mirrors the JVM `InterProcCallNode`; the trailing
 * [RootInstEvalContext] / [GraphAnalysisState] / [ResolvedCallMethod] have no JVM
 * counterpart here (the JVM keeps them in `DSUAliasAnalysis`).
 */
interface CallResolver {
    fun resolveMethodCall(call: PIRCall, level: Int): List<PIRFunction>?
    fun buildMethodGraph(method: PIRFunction): PIRInstGraph?
}

class AliasCallResolver(
    private val callResolver: PIRCallResolver,
    private val graph: ApplicationGraph<CommonMethod, CommonInst>,
    private val languageManager: LanguageManager,
    private val params: PIRLocalAliasAnalysis.Params,
) : CallResolver {
    override fun resolveMethodCall(call: PIRCall, level: Int): List<PIRFunction>? {
        if (level >= params.aliasAnalysisInterProcCallDepth) return null
        // Synthetic unknown functions have no CFG to step into.
        val methods = callResolver.resolveCall(call).filter { it !is PIRUnknownFunction }
        return methods.takeIf { it.isNotEmpty() }
    }

    override fun buildMethodGraph(method: PIRFunction): PIRInstGraph? {
        val entry = graph.methodGraph(method).entryPoints().singleOrNull() ?: return null
        return buildPirInstGraph(languageManager, graph, method, entry)
    }
}

class CallTreeNode(val ctx: ContextInfo, val instEvalCtx: InstEvalContext) {
    private val emptyCalls = BitSet()
    private val calls = Int2ObjectOpenHashMap<Map<PIRFunction, ResolvedCallMethod>>()

    fun resolveCall(call: PIRCall, callResolver: CallResolver): Map<PIRFunction, ResolvedCallMethod>? {
        val callIdx = call.location.index
        if (emptyCalls.get(callIdx)) return null

        return calls.getOrPut(callIdx) {
            val resolved = resolveCallNoCache(call, ctx, instEvalCtx, callResolver)
            if (resolved == null) {
                emptyCalls.set(callIdx)
                return null
            }

            resolved
        }
    }
}

/**
 * Evaluates a callee's body in [ctx], substituting its parameter references with
 * the caller-frame actuals in [paramActuals], indexed by callee parameter index.
 * The implicit receiver (`self`/`cls`) is left unbound here, so it falls through
 * to the slot `Local(-1, ctx)` and is bound to the call's receiver separately by
 * `PIRDSUAliasAnalysis.bindReceiver` (via `call.callee.$PIR_SELF`). Other unbound
 * parameters (missing / star args) likewise become fresh context-local slots that
 * alias nothing.
 */
class NestedCallInstEvalCtx(
    private val paramActuals: Array<RefValue?>,
    private val ctx: ContextInfo,
) : InstEvalContext {
    override fun createArg(idx: Int): RefValue =
        paramActuals.getOrNull(idx) ?: RefValue.Local(-(idx + 1), ctx)

    override fun createLocal(idx: Int): RefValue.Local = RefValue.Local(idx, ctx)
}

private fun resolveCallNoCache(
    call: PIRCall,
    callerCtx: ContextInfo,
    callerCtxEval: InstEvalContext,
    callResolver: CallResolver,
): Map<PIRFunction, ResolvedCallMethod>? {
    val methods = callResolver.resolveMethodCall(call, callerCtx.level) ?: return null

    val resolved = methods.mapIndexedNotNull { idx, method ->
        val graph = callResolver.buildMethodGraph(method) ?: return@mapIndexedNotNull null
        val nestedCtx = ContextInfo(callerCtx.context + mkContextId(call, idx))
        val instEvalCtx = NestedCallInstEvalCtx(bindParamActuals(call, method, callerCtxEval), nestedCtx)
        val analysisState = GraphAnalysisState(graph.statements.size, CallTreeNode(nestedCtx, instEvalCtx))
        method to ResolvedCallMethod(graph, analysisState)
    }.toMap()

    return resolved.takeIf { it.isNotEmpty() }
}

/**
 * Binds each caller actual to the callee parameter it fills: a positional arg at raw
 * slot `s` to parameter `s + offset`, a keyword arg to the declared parameter of its
 * name. The result is indexed by callee parameter index (self/cls at 0, left unbound).
 */
private fun bindParamActuals(call: PIRCall, method: PIRFunction, callerCtxEval: InstEvalContext): Array<RefValue?> {
    val offset = PIRFlowFunctionUtils.implicitParamOffset(method)
    val actuals = arrayOfNulls<RefValue>(method.parameters.size)
    for ((slot, arg) in call.args.withIndex()) {
        val paramIdx = when (arg.kind) {
            PIRCallArgKind.POSITIONAL -> slot + offset
            PIRCallArgKind.KEYWORD -> arg.keyword?.let { method.indexOfKeywordParam(it) } ?: continue
            PIRCallArgKind.STAR, PIRCallArgKind.DOUBLE_STAR -> continue
        }

        if (paramIdx in actuals.indices) actuals[paramIdx] = callerCtxEval.refValue(arg.value)
    }
    return actuals
}

private fun mkContextId(call: PIRCall, methodIdx: Int): Int = call.location.index * 1000 + methodIdx

object RootInstEvalContext : InstEvalContext {
    override fun createArg(idx: Int): RefValue = RefValue.Arg(idx)
    override fun createLocal(idx: Int): RefValue.Local = RefValue.Local(idx, ContextInfo.rootContext)
}

class GraphAnalysisState(size: Int, val call: CallTreeNode) {
    val stateBeforeStmt = arrayOfNulls<ImmutableState>(size)
    val stateAfterStmt = arrayOfNulls<ImmutableState>(size)
}

class ResolvedCallMethod(val graph: PIRInstGraph, val state: GraphAnalysisState)

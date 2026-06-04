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
 * the caller-frame actuals: positional parameter `i` binds to `args[i - offset]`.
 * The implicit receiver (`self`/`cls`, when [offset] == 1) has no positional
 * actual, so it falls through to the unbound slot `Local(-1, ctx)` and is bound
 * to the call's receiver separately by `PIRDSUAliasAnalysis.bindReceiver` (via
 * `call.callee.$PIR_SELF`). Other unbound parameters (missing positional /
 * keyword / star args) likewise become fresh context-local slots that alias nothing.
 */
class NestedCallInstEvalCtx(
    private val args: List<RefValue?>,
    private val ctx: ContextInfo,
    private val offset: Int,
) : InstEvalContext {
    override fun createArg(idx: Int): RefValue =
        args.getOrNull(idx - offset) ?: RefValue.Local(-(idx + 1), ctx)

    override fun createLocal(idx: Int): RefValue.Local = RefValue.Local(idx, ctx)
}

private fun resolveCallNoCache(
    call: PIRCall,
    callerCtx: ContextInfo,
    callerCtxEval: InstEvalContext,
    callResolver: CallResolver,
): Map<PIRFunction, ResolvedCallMethod>? {
    val methods = callResolver.resolveMethodCall(call, callerCtx.level) ?: return null

    // Caller-frame positional actuals bound to the callee's parameters when inlining.
    // The receiver (self/cls) is bound separately via call.callee.$PIR_SELF.
    val args = call.args.map { arg ->
        if (arg.kind == PIRCallArgKind.POSITIONAL) callerCtxEval.refValue(arg.value) else null
    }

    val resolved = methods.mapIndexedNotNull { idx, method ->
        val graph = callResolver.buildMethodGraph(method) ?: return@mapIndexedNotNull null
        val nestedCtx = ContextInfo(callerCtx.context + mkContextId(call, idx))
        val offset = PIRFlowFunctionUtils.implicitParamOffset(method)
        val instEvalCtx = NestedCallInstEvalCtx(args, nestedCtx, offset)
        val analysisState = GraphAnalysisState(graph.statements.size, CallTreeNode(nestedCtx, instEvalCtx))
        method to ResolvedCallMethod(graph, analysisState)
    }.toMap()

    return resolved.takeIf { it.isNotEmpty() }
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

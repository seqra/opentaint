package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

import it.unimi.dsi.fastutil.objects.Object2IntOpenHashMap
import org.opentaint.dataflow.ap.ifds.analysis.alias.ContextInfo
import org.opentaint.dataflow.graph.MethodInstGraph
import org.opentaint.dataflow.jvm.ap.ifds.JIRCallResolver
import org.opentaint.dataflow.jvm.ap.ifds.JIRLanguageManager
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.Params
import org.opentaint.dataflow.jvm.ap.ifds.alias.CallTreeNode
import org.opentaint.dataflow.jvm.ap.ifds.alias.DSUAliasAnalysis.ResolvedCallMethod
import org.opentaint.dataflow.jvm.ap.ifds.alias.ExternalCallModelProvider
import org.opentaint.dataflow.jvm.ap.ifds.alias.JIRIntraProcAliasAnalysis.JIRInstGraph
import org.opentaint.dataflow.jvm.ap.ifds.alias.JirCallResolver
import org.opentaint.dataflow.jvm.ap.ifds.alias.Stmt
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.jvm.graph.JApplicationGraph
import org.opentaint.util.analysis.ApplicationGraph

/**
 * The JIR side of the inlining of resolved calls (IMPL §5.5). It builds the alias CFG of the
 * analyzed method and, on demand, the alias CFGs of the resolved callees.
 *
 * - Resolution: the resolution of main ([CallTreeNode.resolveCall] with a [JirCallResolver]). The
 *   depth limit is `Params.aliasAnalysisInterProcCallDepth` (production 1, tests 0). The DSU keeps
 *   its own use of these classes.
 * - Contexts: each `ContextInfo` of the call tree gets one engine context ([context]). The root
 *   context is [ROOT_CONTEXT]. A callee context is one for each call statement and override, so
 *   two call statements of one callee give two sets of sites and locals.
 * - Values: the `InstEvalContext` of the call tree node (`NestedCallInstEvalCtx`) maps the callee
 *   `this` and arguments to the values of the call, and the callee locals to the callee context.
 * - Models: one [JirCallResolver.externalCallModel] cache for the analysis.
 */
internal class JIRAliasInliner(
    private val tables: AliasTables,
    private val graph: JApplicationGraph,
    private val languageManager: JIRLanguageManager,
    callResolver: JIRCallResolver,
    models: ExternalCallModelProvider,
    params: Params,
) {
    private val contexts = Object2IntOpenHashMap<ContextInfo>().also {
        it.defaultReturnValue(NO_ID)
        it.put(ContextInfo.rootContext, ROOT_CONTEXT)
    }

    private val resolver = object : JirCallResolver(callResolver, graph, models, params) {
        override fun buildMethodJig(entryPoint: JIRInst): JIRInstGraph {
            @Suppress("UNCHECKED_CAST")
            val mig = MethodInstGraph.build(
                languageManager,
                graph as ApplicationGraph<CommonMethod, CommonInst>,
                entryPoint.location.method,
            )
            return JIRInstGraph(
                statements = mig.instructions.map { it as JIRInst },
                graph = mig.graph,
                initialIdx = languageManager.getInstIndex(entryPoint),
            )
        }
    }

    /** The engine context of [ctx]. */
    fun context(ctx: ContextInfo): Int {
        val known = contexts.getInt(ctx)
        if (known != NO_ID) return known
        val id = contexts.size
        contexts.put(ctx, id)
        return id
    }

    /** The alias CFG of the analyzed method, with [entry] as its entry. */
    fun rootCfg(entry: JIRInst): AliasCfg {
        val node = CallTreeNode(ContextInfo.rootContext, JIRAliasLowering.RootEvalContext)
        return AliasCfg.build(
            tables, lowering(node), entry.location.method, entry, graph, languageManager,
            context = ROOT_CONTEXT, callOnCycle = false,
        )
    }

    private fun lowering(node: CallTreeNode) = JIRAliasLowering(
        tables,
        evalCtx = node.instEvalCtx,
        bodyContext = context(node.ctx),
        contextOf = ::context,
        models = resolver::externalCallModel,
        resolve = { stmt -> bodies(node, stmt) },
    )

    /**
     * The bodies of the overrides of [stmt] in the body of [node], or `null` if the call is not
     * resolved or no override has a graph (then the call is unresolved, IMPL §5.5 step 2).
     */
    private fun bodies(node: CallTreeNode, stmt: Stmt.Call): CalleeBodies? {
        val methods = node.resolveCall(stmt, resolver) ?: return null
        val overrides = methods.values.toList()
        if (overrides.isEmpty()) return null
        return CalleeBodies { callOnCycle -> overrides.map { calleeCfg(it, callOnCycle) } }
    }

    private fun calleeCfg(m: ResolvedCallMethod, callOnCycle: Boolean): AliasCfg {
        val node = m.state.call
        return AliasCfg.build(
            tables, lowering(node), m.graph.statements, m.graph.graph, m.graph.initialIdx,
            context = context(node.ctx), callOnCycle = callOnCycle,
        )
    }
}

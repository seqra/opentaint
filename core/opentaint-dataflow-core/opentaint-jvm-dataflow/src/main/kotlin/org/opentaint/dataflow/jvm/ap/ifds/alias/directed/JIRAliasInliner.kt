package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

import org.opentaint.dataflow.ap.ifds.analysis.alias.ContextInfo
import org.opentaint.dataflow.graph.MethodInstGraph
import org.opentaint.dataflow.jvm.ap.ifds.JIRCallResolver
import org.opentaint.dataflow.jvm.ap.ifds.JIRLanguageManager
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.Params
import org.opentaint.dataflow.jvm.ap.ifds.alias.CallResolver
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
import java.util.IdentityHashMap

/**
 * The JIR side of the inlining of resolved calls (IMPL §5.5). It builds the alias CFG of the
 * analyzed method and, on demand, the alias CFGs of the resolved callees.
 *
 * - Resolution: the resolution of main ([CallTreeNode.resolveCall] with a [JirCallResolver]). The
 *   depth limit is `Params.aliasAnalysisInterProcCallDepth` (production 1, tests 0). The DSU keeps
 *   its own use of these classes.
 * - Contexts: each node of the call tree gets one engine context ([context]). The key is the
 *   identity of the `CallTreeNode`, not its `ContextInfo`: main makes the `ContextInfo` of the
 *   override `j` of the call statement `k` from `k * 1000 + j`, so two nodes can have equal
 *   `ContextInfo` values if a call has 1000 or more overrides. The root context is
 *   [ROOT_CONTEXT]. A callee context is one for each call statement and override, so two call
 *   statements of one callee give two sets of sites and locals.
 * - Locals: a body reads its own locals and, through the values of the call, the locals of the
 *   nodes above it. The `ContextInfo` of a local selects the node on the path from the body to the
 *   root ([contextOf]). The nodes of one path have different levels, so the selection is unique.
 * - Values: the `InstEvalContext` of the call tree node (`NestedCallInstEvalCtx`) maps the callee
 *   `this` and arguments to the values of the call, and the callee locals to the callee context.
 * - Models: one [JirCallResolver.externalCallModel] cache for the analysis.
 * - Overrides without a body: main drops an override without a method graph (a native method, for
 *   example) and inlines the others. The directed analysis must not lose the effect of the dropped
 *   override. So if the resolver gives an override that is not abstract and has no graph, the
 *   bodies have [CalleeBodies.hasBodilessOverride], and the inlining also applies the rule of the
 *   unresolved call (IMPL §4.4).
 */
internal class JIRAliasInliner(
    private val tables: AliasTables,
    private val graph: JApplicationGraph,
    private val languageManager: JIRLanguageManager,
    private val resolver: CallResolver,
) {
    constructor(
        tables: AliasTables,
        graph: JApplicationGraph,
        languageManager: JIRLanguageManager,
        callResolver: JIRCallResolver,
        models: ExternalCallModelProvider,
        params: Params,
    ) : this(tables, graph, languageManager, jirAliasCallResolver(graph, languageManager, callResolver, models, params))

    /** The engine context of each call tree node, by identity. */
    private val contexts = IdentityHashMap<CallTreeNode, Int>()

    /** The caller node of each callee node, by identity. */
    private val callers = IdentityHashMap<CallTreeNode, CallTreeNode>()

    /** The engine context of [node]. The first node is the root and gets [ROOT_CONTEXT]. */
    private fun context(node: CallTreeNode): Int =
        contexts.getOrPut(node) { ROOT_CONTEXT + contexts.size }

    /** The engine context of a local of [ctx] in the body of [node]: the node of [ctx] on the path to the root. */
    private fun contextOf(node: CallTreeNode, ctx: ContextInfo): Int {
        var cur: CallTreeNode? = node
        while (cur != null) {
            if (cur.ctx == ctx) return context(cur)
            cur = callers[cur]
        }
        error("No call tree node of $ctx above ${node.ctx}")
    }

    /** The alias CFG of the analyzed method, with [entry] as its entry. */
    fun rootCfg(entry: JIRInst): AliasCfg {
        val node = CallTreeNode(ContextInfo.rootContext, JIRAliasLowering.RootEvalContext)
        check(contexts.isEmpty()) { "One root for each inliner" }
        check(context(node) == ROOT_CONTEXT)
        return AliasCfg.build(
            tables, lowering(node), entry.location.method, entry, graph, languageManager,
            context = ROOT_CONTEXT, callOnCycle = false,
        )
    }

    private fun lowering(node: CallTreeNode) = JIRAliasLowering(
        tables,
        evalCtx = node.instEvalCtx,
        bodyContext = context(node),
        contextOf = { ctx -> contextOf(node, ctx) },
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
        for (m in overrides) callers.putIfAbsent(m.state.call, node)
        val bodiless = resolver.resolveMethodCall(stmt, node.ctx.level).orEmpty()
            .any { !it.isAbstract && it !in methods }
        return object : CalleeBodies {
            override fun build(callOnCycle: Boolean): List<AliasCfg> = overrides.map { calleeCfg(it, callOnCycle) }
            override val hasBodilessOverride: Boolean get() = bodiless
        }
    }

    private fun calleeCfg(m: ResolvedCallMethod, callOnCycle: Boolean): AliasCfg {
        val node = m.state.call
        return AliasCfg.build(
            tables, lowering(node), m.graph.statements, m.graph.graph, m.graph.initialIdx,
            context = context(node), callOnCycle = callOnCycle,
        )
    }
}

/**
 * The call resolver of main for the inliner: the overrides of `JIRCallResolver` within the depth
 * limit, the method graphs of [graph] and the pass-through models of [models].
 */
internal fun jirAliasCallResolver(
    graph: JApplicationGraph,
    languageManager: JIRLanguageManager,
    callResolver: JIRCallResolver,
    models: ExternalCallModelProvider,
    params: Params,
): JirCallResolver = object : JirCallResolver(callResolver, graph, models, params) {
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

package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

import mu.KLogging
import org.opentaint.dataflow.ap.ifds.analysis.alias.AnalysisCancellation
import org.opentaint.dataflow.ap.ifds.analysis.alias.withAnalysisCancellation
import org.opentaint.dataflow.jvm.ap.ifds.JIRCallResolver
import org.opentaint.dataflow.jvm.ap.ifds.JIRLanguageManager
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.Params
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalVariableReachability
import org.opentaint.dataflow.jvm.ap.ifds.taint.TaintRulesProvider
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.jvm.graph.JApplicationGraph

/**
 * The directed alias analysis of one method (IMPL §2). It takes the inputs of the DSU backend.
 *
 * This step builds the alias CFG and runs the fixpoint. It has no queries (step T5), no call
 * closure (step T4) and no inlining (step T6). [callResolver], [modelProvider] and
 * [localVariableReachability] are for these steps.
 *
 * [verifyPostFix]: check the post-fixpoint conditions of the result (tests).
 */
@Suppress("unused")
internal class JIRDirectedAliasAnalysis(
    private val entryPoint: JIRInst,
    private val graph: JApplicationGraph,
    private val callResolver: JIRCallResolver,
    private val modelProvider: TaintRulesProvider?,
    private val localVariableReachability: JIRLocalVariableReachability,
    private val cancellation: Cancellation,
    private val languageManager: JIRLanguageManager,
    private val params: Params,
    private val verifyPostFix: Boolean = false,
) {
    /** The result, or `null` if the time limit or the cancellation stops the analysis (as main). */
    fun compute(): DirectedAliasResult? =
        withAnalysisCancellation(
            timeLimit = params.aliasAnalysisTimeLimit,
            parentCancellation = cancellation,
            body = { compute(it) },
            onAnalysisCancelled = {
                logger.error {
                    "Directed alias analysis for ${entryPoint.location.method} exceed ${params.aliasAnalysisTimeLimit}"
                }
                null
            }
        )

    private fun compute(analysisCancellation: AnalysisCancellation): DirectedAliasResult {
        val tables = AliasTables(params.symDepth)
        val transfer = AliasTransfer(tables, analysisCancellation)
        val lowering = JIRAliasLowering(tables)
        val cfg = AliasCfg.build(
            tables, lowering, entryPoint.location.method, entryPoint, graph, languageManager,
        )
        return DirectedFixpoint(transfer, analysisCancellation).run(cfg, verifyPostFix)
    }

    private companion object {
        val logger = object : KLogging() {}.logger
    }
}

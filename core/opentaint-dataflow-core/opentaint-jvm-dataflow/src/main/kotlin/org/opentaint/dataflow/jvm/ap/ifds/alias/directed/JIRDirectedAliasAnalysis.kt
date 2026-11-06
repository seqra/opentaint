package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

import mu.KLogging
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.analysis.alias.AnalysisCancellation
import org.opentaint.dataflow.ap.ifds.analysis.alias.withAnalysisCancellation
import org.opentaint.dataflow.jvm.ap.ifds.JIRCallResolver
import org.opentaint.dataflow.jvm.ap.ifds.JIRLanguageManager
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasAccessor
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasInfo
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.Params
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalVariableReachability
import org.opentaint.dataflow.jvm.ap.ifds.alias.TaintRulesCallModelProvider
import org.opentaint.dataflow.jvm.ap.ifds.taint.TaintRulesProvider
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.jvm.graph.JApplicationGraph

/**
 * The directed alias analysis of one method (IMPL §2). It takes the inputs of the DSU backend.
 *
 * It builds the alias CFG and runs the fixpoint with the passive unresolved call and the
 * pass-through models of [modelProvider] (IMPL §4.4, §4.5). It has no inlining yet (step T6):
 * [callResolver] is for that step.
 *
 * The queries (IMPL §6) run the analysis one time, at the first query ([JIRAliasAnswers]). A query
 * gives `null` if the time limit or the cancellation stops the analysis, if the statement has no
 * state, if the analysis does not know the local, and if `useAliasAnalysis` is false (IMPL §1.3).
 *
 * [verifyPostFix]: check the post-fixpoint conditions of the result (tests).
 */
internal class JIRDirectedAliasAnalysis(
    private val entryPoint: JIRInst,
    private val graph: JApplicationGraph,
    @Suppress("unused") private val callResolver: JIRCallResolver,
    private val modelProvider: TaintRulesProvider?,
    private val localVariableReachability: JIRLocalVariableReachability,
    private val cancellation: Cancellation,
    private val languageManager: JIRLanguageManager,
    private val params: Params,
    private val verifyPostFix: Boolean = false,
) {
    /** The answers, or `null` if the analysis is off or has no result. Thread safe: computed one time. */
    private val answers: JIRAliasAnswers? by lazy {
        if (!params.useAliasAnalysis) return@lazy null
        val reachability = localVariableReachability
        compute()?.let { JIRAliasAnswers(it, { base, idx -> reachability.isReachable(base, idx) }, params.maxAccessors) }
    }

    /** The aliases of [base] in the state before [statement] (IMPL §6.1). */
    fun findAlias(base: AccessPathBase.LocalVar, statement: CommonInst): List<AliasInfo>? =
        answers?.findAlias(base.idx, languageManager.getInstIndex(statement), after = false)

    /** The aliases of [base] in the state after [statement] (IMPL §6.1). */
    fun findAliasAfterStatement(base: AccessPathBase.LocalVar, statement: CommonInst): List<AliasInfo>? =
        answers?.findAlias(base.idx, languageManager.getInstIndex(statement), after = true)

    /** The aliases of the elements of the array [base] in the state before [statement] (IMPL §6.3). */
    fun findArrayElementAliases(base: AccessPathBase.LocalVar, statement: CommonInst): List<AliasInfo>? =
        answers?.findArrayElementAliases(base.idx, languageManager.getInstIndex(statement))

    /** The aliases of the heap path `base.path` in the state before [statement] (spec §5.7). */
    fun findHeapAlias(base: AccessPathBase.LocalVar, path: List<AliasAccessor>, statement: CommonInst): List<AliasInfo>? =
        answers?.findHeapAlias(base.idx, path, languageManager.getInstIndex(statement))

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
        val callModels = TaintRulesCallModelProvider(modelProvider)
        val lowering = JIRAliasLowering(tables, models = callModels::provideModel)
        val cfg = AliasCfg.build(
            tables, lowering, entryPoint.location.method, entryPoint, graph, languageManager,
        )
        return DirectedFixpoint(transfer, analysisCancellation, params.maxCallClosure).run(cfg, verifyPostFix)
    }

    private companion object {
        val logger = object : KLogging() {}.logger
    }
}

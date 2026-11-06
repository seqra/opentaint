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
import org.opentaint.dataflow.jvm.ap.ifds.alias.AliasBackend
import org.opentaint.dataflow.jvm.ap.ifds.alias.AliasQueryKind
import org.opentaint.dataflow.jvm.ap.ifds.alias.AliasStats
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
 * pass-through models of [modelProvider] (IMPL §4.4, §4.5). A call that [callResolver] resolves
 * within `Params.aliasAnalysisInterProcCallDepth` is inlined (IMPL §5.5, [JIRAliasInliner]).
 *
 * The queries (IMPL §6) run the analysis one time, at the first query ([JIRAliasAnswers]). A query
 * gives `null` if the time limit or the cancellation stops the analysis, if the statement has no
 * state, if the analysis does not know the local, and if `useAliasAnalysis` is false (IMPL §1.3).
 *
 * [verifyPostFix]: check the post-fixpoint conditions of the result (tests).
 *
 * Statistics (IMPL §8): each [compute] records its time in `AliasStats.backend(DIRECTED)`, and the
 * work counters of a result in `AliasStats.directed`. The statistics do not change the result.
 */
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
    /** True after a [compute] that the time limit stopped. */
    @Volatile
    var timedOut: Boolean = false
        private set

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

    /**
     * The answer of a query of [kind] with its statistics. [path] is the heap path of a
     * [AliasQueryKind.HEAP] query. The answer list is the list of the query function of [kind].
     */
    fun answer(
        kind: AliasQueryKind,
        base: AccessPathBase.LocalVar,
        statement: CommonInst,
        path: List<AliasAccessor> = emptyList(),
    ): DirectedAnswer? {
        val answers = answers ?: return null
        val stmt = languageManager.getInstIndex(statement)
        return when (kind) {
            AliasQueryKind.BEFORE -> answers.findAliasAnswer(base.idx, stmt, after = false)
            AliasQueryKind.AFTER -> answers.findAliasAnswer(base.idx, stmt, after = true)
            AliasQueryKind.ARRAY_ELEMENT -> answers.findArrayElementAnswer(base.idx, stmt)
            AliasQueryKind.HEAP -> answers.findHeapAnswer(base.idx, path, stmt)
        }
    }

    /** The result, or `null` if the time limit or the cancellation stops the analysis (as main). */
    fun compute(): DirectedAliasResult? {
        var fixpointNanos = 0L
        val result = AliasStats.backend(AliasBackend.DIRECTED).measure({ timedOut }) {
            withAnalysisCancellation(
                timeLimit = params.aliasAnalysisTimeLimit,
                parentCancellation = cancellation,
                body = { c -> compute(c) { fixpointNanos = it } },
                onAnalysisCancelled = {
                    timedOut = true
                    logger.error {
                        "Directed alias analysis for ${entryPoint.location.method} exceed ${params.aliasAnalysisTimeLimit}"
                    }
                    null
                }
            )
        }
        if (result != null) AliasStats.directed.record(DirectedMethodStats.of(result, fixpointNanos))
        return result
    }

    private inline fun compute(
        analysisCancellation: AnalysisCancellation,
        fixpointTime: (Long) -> Unit,
    ): DirectedAliasResult {
        val tables = AliasTables(params.symDepth)
        val transfer = AliasTransfer(tables, analysisCancellation)
        val callModels = TaintRulesCallModelProvider(modelProvider)
        val inliner = JIRAliasInliner(tables, graph, languageManager, callResolver, callModels, params)
        val cfg = inliner.rootCfg(entryPoint)
        val start = System.nanoTime()
        val result = DirectedFixpoint(transfer, analysisCancellation, params.maxCallClosure).run(cfg, verifyPostFix)
        fixpointTime(System.nanoTime() - start)
        return result
    }

    private companion object {
        val logger = object : KLogging() {}.logger
    }
}

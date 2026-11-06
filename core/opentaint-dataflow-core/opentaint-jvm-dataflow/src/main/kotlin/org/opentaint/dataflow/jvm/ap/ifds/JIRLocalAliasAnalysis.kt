package org.opentaint.dataflow.jvm.ap.ifds

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.analysis.alias.LocalAliasAnalysis.CommonAliasApInfo
import org.opentaint.dataflow.jvm.ap.ifds.alias.JIRDsuAliasAnalysis
import org.opentaint.dataflow.jvm.ap.ifds.taint.TaintRulesProvider
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.jvm.graph.JApplicationGraph
import kotlin.time.Duration
import kotlin.time.Duration.Companion.seconds

/**
 * The local alias analysis of one method. The consumers use only this facade.
 *
 * [Params.mode] selects the backend. At this step, each mode uses the DSU backend ([JIRDsuAliasAnalysis]).
 * Thus each answer is the answer of main.
 */
class JIRLocalAliasAnalysis(
    entryPoint: JIRInst,
    graph: JApplicationGraph,
    callResolver: JIRCallResolver,
    modelProvider: TaintRulesProvider?,
    localVariableReachability: JIRLocalVariableReachability,
    cancellation: Cancellation,
    languageManager: JIRLanguageManager,
    params: Params,
) {
    data class Params(
        val useAliasAnalysis: Boolean = true,
        val aliasAnalysisInterProcCallDepth: Int = 0,
        val aliasAnalysisTimeLimit: Duration = 10.seconds,
        val mode: AliasAnalysisMode = AliasAnalysisMode.DSU,
        /** K: the maximum depth of the symbolic entry paths of the directed analysis. */
        val symDepth: Int = 7,
        /** D: the maximum number of accessors in an answer path of the directed analysis. */
        val maxAccessors: Int = 6,
        /** The maximum size of the call closure of the directed analysis. */
        val maxCallClosure: Int = 10_000,
    )

    private val dsu = JIRDsuAliasAnalysis(
        entryPoint, graph, callResolver, modelProvider,
        localVariableReachability, cancellation, languageManager, params
    )

    /** The aliases of [base] in the state before [statement]. */
    fun findAlias(base: AccessPathBase.LocalVar, statement: CommonInst): List<AliasInfo>? =
        dsu.findAlias(base, statement)

    /** The aliases of [base] in the state after [statement]. */
    fun findAliasAfterStatement(base: AccessPathBase.LocalVar, statement: CommonInst): List<AliasInfo>? =
        dsu.findAliasAfterStatement(base, statement)

    /**
     * The aliases of the elements of the array [base] in the state before [statement].
     *
     * The DSU backend gives the alias group that contains the path `base[*]`, as the vararg branch of
     * `JIRBasicAtomEvaluator` did on main. The answer also contains the path `base[*]`. If no group
     * contains the path, the result is `null`.
     */
    fun findArrayElementAliases(base: AccessPathBase.LocalVar, statement: CommonInst): List<AliasInfo>? {
        for (aliasSet in dsu.getAllAliasAtStatement(statement)) {
            for (info in aliasSet) {
                if (info !is AliasApInfo || info.base != base) continue
                val singleAccessor = info.accessors.singleOrNull() ?: continue
                if (singleAccessor is AliasAccessor.Array) {
                    return aliasSet
                }
            }
        }
        return null
    }

    /**
     * The aliases of the heap path `base.path` in the state before [statement]. The tests use it.
     *
     * The DSU backend gives the answers of `forEachHeapAlias` at the end of the path. If the analysis has
     * no result, the result is `null`.
     */
    internal fun findHeapAlias(
        base: AccessPathBase.LocalVar,
        path: List<AliasAccessor>,
        statement: CommonInst,
    ): List<AliasInfo>? {
        if (dsu.aliasInfo == null) return null

        val result = mutableListOf<AliasInfo>()
        dsu.forEachHeapAlias(
            base, statement, path,
            next = { rest -> if (rest.isEmpty()) emptyList() else listOf(rest.first() to rest.drop(1)) },
            handle = { info, rest -> if (rest.isEmpty()) result += info },
        )
        return result
    }

    sealed interface AliasAccessor {
        data class Field(val className: String, val fieldName: String, val fieldType: String) : AliasAccessor
        data object Array : AliasAccessor
        data class Static(val typeName: String) : AliasAccessor
    }

    sealed interface AliasInfo

    data class AliasApInfo(
        override val base: AccessPathBase,
        override val accessors: List<AliasAccessor>
    ) : AliasInfo,
        CommonAliasApInfo<AliasAccessor>

    data class AliasAllocInfo(val allocInst: Int) : AliasInfo
}

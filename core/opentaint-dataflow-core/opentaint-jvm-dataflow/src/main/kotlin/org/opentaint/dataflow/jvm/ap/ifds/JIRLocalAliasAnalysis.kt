package org.opentaint.dataflow.jvm.ap.ifds

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.analysis.alias.LocalAliasAnalysis.CommonAliasApInfo
import org.opentaint.dataflow.jvm.ap.ifds.alias.AliasBackend
import org.opentaint.dataflow.jvm.ap.ifds.alias.AliasQueryKind
import org.opentaint.dataflow.jvm.ap.ifds.alias.AliasShadowStats
import org.opentaint.dataflow.jvm.ap.ifds.alias.AliasStats
import org.opentaint.dataflow.jvm.ap.ifds.alias.AliasVolumeStats
import org.opentaint.dataflow.jvm.ap.ifds.alias.JIRDsuAliasAnalysis
import org.opentaint.dataflow.jvm.ap.ifds.alias.directed.JIRDirectedAliasAnalysis
import org.opentaint.dataflow.jvm.ap.ifds.taint.TaintRulesProvider
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.jvm.graph.JApplicationGraph
import java.util.concurrent.CancellationException
import java.util.concurrent.ConcurrentHashMap
import kotlin.time.Duration
import kotlin.time.Duration.Companion.seconds

/**
 * The local alias analysis of one method. The consumers use only this facade.
 *
 * [Params.mode] selects the backend:
 * - [AliasAnalysisMode.DSU]: the DSU backend ([JIRDsuAliasAnalysis]). Each answer is the answer of main.
 * - [AliasAnalysisMode.DIRECTED]: the directed backend ([JIRDirectedAliasAnalysis]). Its answers are sorted
 *   and have no duplicates. A local with no value gives an empty list (main gives `null`).
 * - [AliasAnalysisMode.SHADOW]: both backends run. Each answer is the answer of the DSU backend (the
 *   same list). The directed backend runs only for the statistics ([AliasShadowStats]). A failure or
 *   a time-out of the directed backend does not change a DSU answer: the facade counts it and stops
 *   the directed backend of this method. A cancellation ([CancellationException]) or an interrupt
 *   ([InterruptedException]) in the directed backend is counted, then it goes to the caller.
 *
 * Both backends give `null` on a time-out and on a statement that the analysis did not reach.
 *
 * Statistics (IMPL §8, [AliasStats]): if [Params.recordsStatistics] is true, the facade records each
 * query one time ([AliasVolumeStats] for the answering backends, [AliasShadowStats] in `SHADOW` mode).
 * A repeated query (the same kind, statement and local) is not recorded again. In `DSU` mode without
 * [Params.statistics], the facade records no query and keeps no statistics state: only the backend
 * records the time of its computation. The statistics never change an answer.
 */
class JIRLocalAliasAnalysis(
    private val entryPoint: JIRInst,
    graph: JApplicationGraph,
    callResolver: JIRCallResolver,
    modelProvider: TaintRulesProvider?,
    localVariableReachability: JIRLocalVariableReachability,
    cancellation: Cancellation,
    private val languageManager: JIRLanguageManager,
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
        /**
         * The full statistics in `DSU` mode (hidden CLI option `--experimental-alias-stats`). The
         * `SHADOW` and `DIRECTED` modes always record the full statistics.
         */
        val statistics: Boolean = false,
    ) {
        /** True if the facade records the queries and the analysis logs the `ALIAS-STATS` summary. */
        val recordsStatistics: Boolean get() = statistics || mode != AliasAnalysisMode.DSU
    }

    private val mode = params.mode

    private val directed: JIRDirectedAliasAnalysis? = if (mode != AliasAnalysisMode.DSU) {
        JIRDirectedAliasAnalysis(
            entryPoint, graph, callResolver, modelProvider,
            localVariableReachability, cancellation, languageManager, params
        )
    } else {
        null
    }

    private val dsu: JIRDsuAliasAnalysis? = if (mode != AliasAnalysisMode.DIRECTED) {
        JIRDsuAliasAnalysis(
            entryPoint, graph, callResolver, modelProvider,
            localVariableReachability, cancellation, languageManager, params
        )
    } else {
        null
    }

    /** True if this facade records the queries ([Params.recordsStatistics]). */
    private val stats = params.recordsStatistics

    /** The queries that the statistics recorded: `(statement, local, kind)`. `null` without statistics. */
    private val recorded: MutableSet<Long>? = if (stats) ConcurrentHashMap.newKeySet() else null

    /** The totals of this method analysis, made at the first recorded query. */
    @Volatile
    private var methodVolume: AliasVolumeStats.MethodVolume? = null

    /** SHADOW: true after the directed backend failed, timed out or was cancelled. */
    @Volatile
    private var directedStopped = false

    init {
        if (stats) AliasStats.noteConfig(params)
    }

    /** True if this facade keeps a statistics state: the set of the recorded queries or the method totals (tests). */
    internal val keepsStatisticsState: Boolean get() = recorded != null || methodVolume != null

    /** The aliases of [base] in the state before [statement]. */
    fun findAlias(base: AccessPathBase.LocalVar, statement: CommonInst): List<AliasInfo>? =
        query(AliasQueryKind.BEFORE, base, statement) { it.findAlias(base, statement) }

    /** The aliases of [base] in the state after [statement]. */
    fun findAliasAfterStatement(base: AccessPathBase.LocalVar, statement: CommonInst): List<AliasInfo>? =
        query(AliasQueryKind.AFTER, base, statement) { it.findAliasAfterStatement(base, statement) }

    /**
     * The aliases of the elements of the array [base] in the state before [statement].
     *
     * The DSU backend gives the alias group that contains the path `base[*]`, as the vararg branch of
     * `JIRBasicAtomEvaluator` did on main. The answer also contains the path `base[*]`. If no group
     * contains the path, the result is `null`.
     *
     * The directed backend gives the paths that alias `base[*]` (without `base[*]`) and the allocations and
     * the constants of the element value (IMPL §6.3).
     */
    fun findArrayElementAliases(base: AccessPathBase.LocalVar, statement: CommonInst): List<AliasInfo>? =
        query(AliasQueryKind.ARRAY_ELEMENT, base, statement) { dsuArrayElementAliases(it, base, statement) }

    private fun dsuArrayElementAliases(
        dsu: JIRDsuAliasAnalysis,
        base: AccessPathBase.LocalVar,
        statement: CommonInst,
    ): List<AliasInfo>? {
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
     * no result, the result is `null`. The directed backend gives the paths of the heap-path query of
     * spec §5.7, without the queried path.
     */
    internal fun findHeapAlias(
        base: AccessPathBase.LocalVar,
        path: List<AliasAccessor>,
        statement: CommonInst,
    ): List<AliasInfo>? =
        query(AliasQueryKind.HEAP, base, statement, path) { dsuHeapAlias(it, base, path, statement) }

    private fun dsuHeapAlias(
        dsu: JIRDsuAliasAnalysis,
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

    /**
     * One query of [kind]. [dsuAnswer] gives the DSU answer. The answer of the mode goes to the
     * caller. The first query of each `(kind, statement, local)` is recorded in the statistics.
     */
    private inline fun query(
        kind: AliasQueryKind,
        base: AccessPathBase.LocalVar,
        statement: CommonInst,
        path: List<AliasAccessor> = emptyList(),
        dsuAnswer: (JIRDsuAliasAnalysis) -> List<AliasInfo>?,
    ): List<AliasInfo>? {
        when (mode) {
            AliasAnalysisMode.DSU -> {
                val answer = dsuAnswer(dsu!!)
                if (stats && firstQuery(kind, base, statement)) {
                    AliasStats.volume.record(AliasBackend.DSU, kind, answer, methodVolume())
                }
                return answer
            }

            AliasAnalysisMode.DIRECTED -> {
                val answer = directed!!.answer(kind, base, statement, path)
                if (firstQuery(kind, base, statement)) {
                    AliasStats.volume.record(
                        AliasBackend.DIRECTED, kind, answer?.infos, methodVolume(), answer?.nullOnlyPaths ?: -1
                    )
                }
                return answer?.infos
            }

            AliasAnalysisMode.SHADOW -> {
                val dsu = dsu!!
                val answer = dsuAnswer(dsu)
                if (firstQuery(kind, base, statement)) shadow(kind, base, statement, path, dsu, answer)
                return answer
            }
        }
    }

    /**
     * SHADOW: records the DSU answer, runs the directed query, and compares both answers. It never
     * changes [dsuAnswer]. It throws only an [OutOfMemoryError], a cancellation and an interrupt
     * ([onDirectedThrowable]).
     */
    private fun shadow(
        kind: AliasQueryKind,
        base: AccessPathBase.LocalVar,
        statement: CommonInst,
        path: List<AliasAccessor>,
        dsu: JIRDsuAliasAnalysis,
        dsuAnswer: List<AliasInfo>?,
    ) {
        val volume = methodVolume()
        AliasStats.volume.record(AliasBackend.DSU, kind, dsuAnswer, volume)
        if (directedStopped) {
            AliasStats.shadow.skip(kind)
            return
        }
        val directed = directed!!
        val answer = try {
            directed.answer(kind, base, statement, path)
        } catch (e: OutOfMemoryError) {
            throw e
        } catch (e: Throwable) {
            AliasStats.shadow.skip(kind)
            onDirectedThrowable(e)
            return
        }
        if (answer == null && directed.timedOut) {
            stopDirected { AliasStats.shadow.directedTimeouts.increment() }
            AliasStats.shadow.skip(kind)
            return
        }
        AliasStats.volume.record(AliasBackend.DIRECTED, kind, answer?.infos, volume, answer?.nullOnlyPaths ?: -1)
        if (dsu.aliasInfo == null) {
            // The DSU timed out: its answers are null, a comparison has no meaning.
            AliasStats.shadow.skip(kind)
            return
        }
        val exclude = if (kind == AliasQueryKind.ARRAY_ELEMENT) AliasApInfo(base, listOf(AliasAccessor.Array)) else null
        AliasStats.shadow.record(kind, dsuAnswer, answer?.infos, exclude) {
            Triple(entryPoint.location.method.toString(), languageManager.getInstIndex(statement), base.idx)
        }
    }

    /**
     * SHADOW: counts a throwable [e] of the directed backend and stops the directed backend of this
     * method. A [CancellationException] (the parent cancellation) and an [InterruptedException] go
     * to the caller after the count: the analysis must stop. Another throwable is a failure: the
     * function returns, and the DSU answer stays.
     */
    internal fun onDirectedThrowable(e: Throwable) {
        when (e) {
            is CancellationException, is InterruptedException -> {
                stopDirected { AliasStats.shadow.directedCancelled.increment() }
                throw e
            }

            else -> stopDirected { AliasStats.shadow.failure(entryPoint.location.method.toString(), e) }
        }
    }

    private inline fun stopDirected(count: () -> Unit) {
        synchronized(this) {
            if (directedStopped) return
            directedStopped = true
        }
        count()
    }

    private fun firstQuery(kind: AliasQueryKind, base: AccessPathBase.LocalVar, statement: CommonInst): Boolean {
        if (kind == AliasQueryKind.HEAP) return true
        val stmt = languageManager.getInstIndex(statement).toLong()
        return recorded!!.add((stmt shl 32) or (base.idx.toLong() shl 2) or kind.ordinal.toLong())
    }

    private fun methodVolume(): AliasVolumeStats.MethodVolume =
        methodVolume ?: synchronized(this) {
            methodVolume ?: AliasStats.volume.newMethod().also { methodVolume = it }
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

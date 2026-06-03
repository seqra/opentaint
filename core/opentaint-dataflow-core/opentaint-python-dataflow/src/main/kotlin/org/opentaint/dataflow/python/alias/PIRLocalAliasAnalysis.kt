package org.opentaint.dataflow.python.alias

import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.LanguageManager
import org.opentaint.dataflow.python.PIRCallResolver
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.python.PIRInstruction
import org.opentaint.util.analysis.ApplicationGraph
import kotlin.time.Duration
import kotlin.time.Duration.Companion.seconds

/**
 * Public intra-procedural alias query API for Python, mirroring the JVM
 * `JIRLocalAliasAnalysis`. Lazily computes per-statement alias sets and answers
 * `findAlias` / `findAliasAfterStatement` for local-var bases.
 *
 * Member order mirrors the JVM `JIRLocalAliasAnalysis` to ease side-by-side review.
 */
class PIRLocalAliasAnalysis(
    private val entryPoint: PIRInstruction,
    private val graph: ApplicationGraph<CommonMethod, CommonInst>,
    private val callResolver: PIRCallResolver,
    private val languageManager: LanguageManager,
    private val cancellation: Cancellation?,
    private val params: Params,
) {
    data class Params(
        val useAliasAnalysis: Boolean = true,
        val aliasAnalysisInterProcCallDepth: Int = 1,
        val aliasAnalysisTimeLimit: Duration = 10.seconds,
    )

    private val aliasInfo by lazy { compute() }

    class MethodAliasInfo(
        val aliasBeforeStatement: Array<Int2ObjectOpenHashMap<List<AliasApInfo>>?>?,
        val aliasAfterStatement: Array<Int2ObjectOpenHashMap<List<AliasApInfo>>?>?,
    )

    private fun getLocalVarAliases(
        alias: Array<Int2ObjectOpenHashMap<List<AliasApInfo>>?>,
        instIdx: Int,
        base: AccessPathBase.LocalVar,
    ): List<AliasApInfo>? =
        alias.getOrNull(instIdx)?.get(base.idx)?.filter {
            // drop the base's trivial self-alias
            it.accessors.isNotEmpty() || it.base != base
        }

    fun findAlias(base: AccessPathBase.LocalVar, statement: CommonInst): List<AliasApInfo>? {
        val before = aliasInfo.aliasBeforeStatement ?: return null
        return getLocalVarAliases(before, languageManager.getInstIndex(statement), base)
    }

    fun findAliasAfterStatement(base: AccessPathBase.LocalVar, statement: CommonInst): List<AliasApInfo>? {
        val after = aliasInfo.aliasAfterStatement ?: return null
        return getLocalVarAliases(after, languageManager.getInstIndex(statement), base)
    }

    private fun compute(): MethodAliasInfo =
        PIRIntraProcAliasAnalysis(entryPoint, graph, callResolver, languageManager, cancellation, params).compute()
}

sealed interface AliasAccessor {
    data class Field(val name: String) : AliasAccessor
    data object Array : AliasAccessor
}

data class AliasApInfo(val base: AccessPathBase, val accessors: List<AliasAccessor>)

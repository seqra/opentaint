package org.opentaint.dataflow.python.alias

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.LanguageManager
import org.opentaint.dataflow.ap.ifds.analysis.alias.AAInfo
import org.opentaint.dataflow.ap.ifds.analysis.alias.AAInfoManager
import org.opentaint.dataflow.ap.ifds.analysis.alias.AnalysisCancellation
import org.opentaint.dataflow.ap.ifds.analysis.alias.ContextInfo
import org.opentaint.dataflow.ap.ifds.analysis.alias.HeapAlias
import org.opentaint.dataflow.ap.ifds.analysis.alias.State
import org.opentaint.dataflow.ap.ifds.analysis.alias.withAnalysisCancellation
import org.opentaint.dataflow.python.PIRCallResolver
import org.opentaint.dataflow.python.alias.PIRDSUAliasAnalysis.AnalysisResult
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.python.PIRInstruction
import org.opentaint.util.analysis.ApplicationGraph
import kotlin.time.Duration
import kotlin.time.Duration.Companion.seconds

/**
 * Public intra-procedural alias query API for Python, ported from the Go
 * `GoLocalAliasAnalysis`. Lazily runs the DSU simulator ([PIRDSUAliasAnalysis]) and
 * interprets its raw per-statement [State]s on demand: `findAlias` /
 * `findAliasAfterStatement` / `findHeapAlias` look up the state at a statement, find
 * the queried element in the [AAInfoManager], walk its alias set, and convert each
 * member into the public [AliasApInfo] form.
 *
 * Python's DSU has no pointers, so the Go `Ref` accessor (and `collapseRefs` /
 * `computeAliasWithRef`) are intentionally absent. Alloc-based aliases are dropped
 * (only local/argument bases surface), matching what downstream consumers use.
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

    companion object {
        private const val HEAP_CHAIN_LIMIT = 5
    }

    private val result: AnalysisResult by lazy { computeAliases() }

    fun findAlias(base: AccessPathBase.LocalVar, statement: CommonInst): List<AliasApInfo>? {
        val stmtAlias = result.statesBeforeStmt.getOrNull(languageManager.getInstIndex(statement)) ?: return null
        return stmtAlias.unsafeState().findLocalAlias(result.manager, base.idx)
    }

    fun findAliasAfterStatement(base: AccessPathBase.LocalVar, statement: CommonInst): List<AliasApInfo>? {
        val stmtAlias = result.statesAfterStmt.getOrNull(languageManager.getInstIndex(statement)) ?: return null
        return stmtAlias.unsafeState().findLocalAlias(result.manager, base.idx)
    }

    fun findHeapAliasAfterStatement(
        base: AccessPathBase.LocalVar,
        accessors: List<AliasAccessor>,
        statement: CommonInst,
    ): List<AliasApInfo>? {
        val stmtAlias = result.statesAfterStmt.getOrNull(languageManager.getInstIndex(statement)) ?: return null
        return stmtAlias.unsafeState().findHeapAlias(result.manager, base.idx, accessors)
    }

    // ── lazy result ──────────────────────────────────────────────────────────

    private fun computeAliases(): AnalysisResult =
        withAnalysisCancellation(
            timeLimit = params.aliasAnalysisTimeLimit,
            parentCancellation = cancellation,
            body = { computeAliases(it) },
            onAnalysisCancelled = { AnalysisResult(AAInfoManager(), emptyArray(), emptyArray()) },
        )

    private fun computeAliases(cancellation: AnalysisCancellation): AnalysisResult {
        val pig = buildPirInstGraph(languageManager, graph, entryPoint.location.method, entryPoint)
        val aliasCallResolver = AliasCallResolver(callResolver, graph, languageManager, params)
        return PIRDSUAliasAnalysis(aliasCallResolver, cancellation).analyze(pig)
    }

    // ── alias-set interpretation (ported from GoLocalAliasAnalysis) ───────────

    private fun State.findLocalAlias(manager: AAInfoManager, localIdx: Int): List<AliasApInfo>? {
        val localInfo = LocalAlias.SimpleLoc(RefValue.Local(localIdx, ContextInfo.rootContext))
        val localInfoIdx = manager.find(localInfo) ?: return null
        return convertAllAliases(localInfoIdx, manager)
    }

    private fun State.findHeapAlias(
        manager: AAInfoManager,
        localIdx: Int,
        accessors: List<AliasAccessor>,
    ): List<AliasApInfo>? {
        val localInfo = LocalAlias.SimpleLoc(RefValue.Local(localIdx, ContextInfo.rootContext))
        val localInfoIdx = manager.find(localInfo) ?: return null

        val heapInfoIdx = accessors.fold(localInfoIdx) { prev, accessor ->
            val instance = aliasGroupId(prev)
            val heapAccessor = when (accessor) {
                is AliasAccessor.Array -> ArrayAlias
                is AliasAccessor.Field -> FieldAlias(accessor)
            }
            manager.find(HeapAlias(instance, heapAccessor)) ?: return null
        }
        return convertAllAliases(heapInfoIdx, manager)
    }

    private fun State.convertAllAliases(infoIdx: Int, manager: AAInfoManager): MutableList<AliasApInfo> {
        val result = mutableListOf<AliasApInfo>()
        forEachAliasInSet(infoIdx) { aliasIdx ->
            if (aliasIdx != infoIdx) {
                result += convert(aliasIdx, manager, depth = 0)
            }
        }
        return result
    }

    private fun State.convert(infoIdx: Int, manager: AAInfoManager, depth: Int): List<AliasApInfo> =
        convert(manager.getElementUncheck(infoIdx), manager, depth)

    private fun State.convert(info: AAInfo, manager: AAInfoManager, depth: Int): List<AliasApInfo> {
        if (info !is HeapAlias) {
            return listOfNotNull(convertBase(info))
        }
        if (depth > HEAP_CHAIN_LIMIT) {
            return emptyList()
        }

        val instances = mutableListOf<AliasApInfo>()
        forEachAliasInSet(info.instance) { instances += convert(it, manager, depth + 1) }

        val accessor = when (val a = info.heapAccessor) {
            is ArrayAlias -> AliasAccessor.Array
            is FieldAlias -> a.field
            else -> error("Impossible heap accessor")
        }
        return instances.map { AliasApInfo(it.base, it.accessors + accessor) }
    }

    private fun convertBase(info: AAInfo): AliasApInfo? {
        if (info.ctx != ContextInfo.rootContext) return null
        return when (info) {
            is LocalAlias.SimpleLoc -> when (val loc = info.loc) {
                is RefValue.Local -> AliasApInfo(AccessPathBase.LocalVar(loc.idx), emptyList())
                is RefValue.Arg -> AliasApInfo(AccessPathBase.Argument(loc.idx), emptyList())
            }

            is LocalAlias.Alloc,
            is CallReturn,
            is Unknown -> null

            is HeapAlias -> error("unreachable")
            else -> error("Impossible aa-info")
        }
    }
}

sealed interface AliasAccessor {
    data class Field(val name: String) : AliasAccessor
    data object Array : AliasAccessor
}

data class AliasApInfo(val base: AccessPathBase, val accessors: List<AliasAccessor>)

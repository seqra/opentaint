package org.opentaint.dataflow.python.alias

import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.LanguageManager
import org.opentaint.dataflow.ap.ifds.analysis.alias.AAInfo
import org.opentaint.dataflow.ap.ifds.analysis.alias.AnalysisCancellation
import org.opentaint.dataflow.ap.ifds.analysis.alias.ContextInfo
import org.opentaint.dataflow.ap.ifds.analysis.alias.HeapAlias
import org.opentaint.dataflow.ap.ifds.analysis.alias.withAnalysisCancellation
import org.opentaint.dataflow.python.PIRCallResolver
import org.opentaint.dataflow.python.alias.PIRDSUAliasAnalysis.ConnectedAliases
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.python.PIRInstruction
import org.opentaint.util.analysis.ApplicationGraph

/**
 * Builds the per-method instruction graph, runs the DSU simulator, and converts
 * the resulting alias groups into the public [AliasApInfo] form. Mirror of the JVM
 * `JIRIntraProcAliasAnalysis`, minus reachability pruning (deferred — sound
 * over-approximation) and minus the compression step (kept simple for Phase 1).
 */
class PIRIntraProcAliasAnalysis(
    private val entryPoint: PIRInstruction,
    private val graph: ApplicationGraph<CommonMethod, CommonInst>,
    private val callResolver: PIRCallResolver,
    private val languageManager: LanguageManager,
    private val rootCancellation: Cancellation?,
    private val params: PIRLocalAliasAnalysis.Params,
) {
    companion object {
        private const val HEAP_CHAIN_LIMIT = 5
    }

    private fun getPIG(): PIRInstGraph =
        buildPirInstGraph(languageManager, graph, entryPoint.location.method, entryPoint)

    fun compute(): PIRLocalAliasAnalysis.MethodAliasInfo =
        withAnalysisCancellation(
            timeLimit = params.aliasAnalysisTimeLimit,
            parentCancellation = rootCancellation,
            body = { compute(it) },
            onAnalysisCancelled = { PIRLocalAliasAnalysis.MethodAliasInfo(null, null) },
        )

    private fun compute(cancellation: AnalysisCancellation): PIRLocalAliasAnalysis.MethodAliasInfo {
        val pig = getPIG()
        val aliasCallResolver = AliasCallResolver(callResolver, graph, languageManager, params)
        val daa = PIRDSUAliasAnalysis(aliasCallResolver, cancellation).analyze(pig)

        val before = arrayOfNulls<Int2ObjectOpenHashMap<List<AliasApInfo>>>(pig.statements.size)
        val after = arrayOfNulls<Int2ObjectOpenHashMap<List<AliasApInfo>>>(pig.statements.size)

        for (i in pig.statements.indices) {
            before[i] = resolveLocalVar(daa.statesBeforeStmt[i], cancellation)
            after[i] = resolveLocalVar(daa.statesAfterStmt[i], cancellation)
        }

        return PIRLocalAliasAnalysis.MethodAliasInfo(before, after)
    }

    private fun resolveLocalVar(
        daa: ConnectedAliases,
        cancellation: AnalysisCancellation,
    ): Int2ObjectOpenHashMap<List<AliasApInfo>> {
        val result = Int2ObjectOpenHashMap<List<AliasApInfo>>()

        for (group in daa.aliasGroups.values) {
            val converted = group
                .flatMap { it.convertToAliasInfo(daa.aliasGroups, depth = 0, cancellation) }
                .distinct()

            // size == 1 means only the local itself was converted; not meaningful
            if (converted.size <= 1) continue

            val locals = converted
                .filter { it.accessors.isEmpty() }
                .mapNotNull { it.base as? AccessPathBase.LocalVar }

            // Groups with no local base (only args/heap/return) are dropped.
            locals.forEach { local -> result[local.idx] = converted }
        }

        return result
    }

    private fun AAInfo.convertToAliasInfo(
        aliasGroups: Int2ObjectOpenHashMap<List<AAInfo>>,
        depth: Int,
        cancellation: AnalysisCancellation,
    ): List<AliasApInfo> {
        if (this !is HeapAlias) {
            return listOfNotNull(convertBaseAccessor(this))
        }

        if (depth > HEAP_CHAIN_LIMIT) return emptyList()

        cancellation.checkpoint()

        val instanceGroup = aliasGroups[instance] ?: return emptyList()
        val instances = instanceGroup.flatMap { it.convertToAliasInfo(aliasGroups, depth + 1, cancellation) }
        val accessor = when (val a = this.heapAccessor) {
            is ArrayAlias -> AliasAccessor.Array
            is FieldAlias -> a.field
            else -> error("Impossible heap accessor")
        }

        return instances.map { AliasApInfo(it.base, it.accessors + accessor) }
    }

    private fun convertBaseAccessor(cur: AAInfo): AliasApInfo? {
        if (cur.ctx != ContextInfo.rootContext) return null

        return when (cur) {
            is LocalAlias.SimpleLoc -> when (val loc = cur.loc) {
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

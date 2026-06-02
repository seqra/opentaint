package org.opentaint.dataflow.go.analysis.alias

import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import mu.KLogging
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.analysis.alias.AAInfo
import org.opentaint.dataflow.ap.ifds.analysis.alias.AnalysisCancellation
import org.opentaint.dataflow.ap.ifds.analysis.alias.ContextInfo
import org.opentaint.dataflow.ap.ifds.analysis.alias.HeapAlias
import org.opentaint.dataflow.ap.ifds.analysis.alias.withAnalysisCancellation
import org.opentaint.dataflow.go.analysis.alias.GoDSUAliasAnalysis.ConnectedAliases
import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.inst.GoIRInst
import kotlin.time.Duration
import kotlin.time.Duration.Companion.seconds

sealed interface GoAliasInfo
data class AliasApInfo(val base: AccessPathBase, val accessors: List<GoAliasAccessor>) : GoAliasInfo
data class AliasAllocInfo(val allocInst: Int) : GoAliasInfo

sealed interface GoAliasInfoNoRef
data class AliasApInfoNoRef(val base: AccessPathBase, val accessors: List<GoAliasAccessor.NoRef>) : GoAliasInfoNoRef
data class AliasAllocInfoNoRef(val allocInst: Int) : GoAliasInfoNoRef

class GoLocalAliasAnalysis(
    private val function: GoIRFunction,
    private val params: Params = Params(),
) {
    data class Params(
        val interProcCallDepth: Int = 0,
        val aliasAnalysisTimeLimit: Duration = 10.seconds,
    )

    companion object {
        private const val HEAP_CHAIN_LIMIT = 5
        private val logger = object : KLogging() {}.logger
    }

    class FunctionAliasInfo(
        val aliasBeforeStatement: Array<Int2ObjectOpenHashMap<List<GoAliasInfoNoRef>>>?,
        val aliasAfterStatement: Array<Int2ObjectOpenHashMap<List<GoAliasInfoNoRef>>>?,
        val unboundBeforeStatement: Array<List<List<GoAliasInfoNoRef>>>?,
    )

    private val result: FunctionAliasInfo by lazy {
        computeAliases()
    }

    fun findAlias(base: AccessPathBase, stmt: GoIRInst): List<GoAliasInfoNoRef>? {
        if (base !is AccessPathBase.LocalVar) return null

        val aliasBefore = result.aliasBeforeStatement ?: return null
        val stmtIdx = stmt.location.index
        val stmtAlias = aliasBefore.getOrNull(stmtIdx) ?: return null
        return stmtAlias.getOrDefault(base.idx, null)
    }

    private fun computeAliases(): FunctionAliasInfo = withAnalysisCancellation(
        params.aliasAnalysisTimeLimit, parentCancellation = null,
        body = { cancellation ->
            computeAliases(cancellation)
        },
        onAnalysisCancelled = {
            logger.error {
                "Alias analysis for $function exceed ${params.aliasAnalysisTimeLimit}"
            }
            FunctionAliasInfo(null, null, null)
        }
    )

    private fun computeAliases(cancellation: AnalysisCancellation): FunctionAliasInfo {
        val analyzer = GoDSUAliasAnalysis(function, params.interProcCallDepth, cancellation)
        val daa = analyzer.analyze(collapseRefs = true)

        val size = daa.statesBeforeStmt.size
        val aliasBeforeStatement = Array(size) { Int2ObjectOpenHashMap<List<GoAliasInfoNoRef>>() }
        val aliasAfterStatement = Array(size) { Int2ObjectOpenHashMap<List<GoAliasInfoNoRef>>() }

        val unboundAliasBeforeStatement = Array(size) { mutableListOf<List<GoAliasInfoNoRef>>() }
        val unboundAliasAfterStatement = Array(size) { mutableListOf<List<GoAliasInfoNoRef>>() }

        for (i in 0 until size) {
            resolveLocalVar(
                daa.statesBeforeStmt[i],
                aliasBeforeStatement[i], unboundAliasBeforeStatement[i],
                cancellation
            )

            resolveLocalVar(
                daa.statesAfterStmt[i],
                aliasAfterStatement[i], unboundAliasAfterStatement[i],
                cancellation
            )
        }

        @Suppress("UNCHECKED_CAST")
        return FunctionAliasInfo(
            aliasBeforeStatement,
            aliasAfterStatement,
            unboundAliasBeforeStatement as Array<List<List<GoAliasInfoNoRef>>>
        )
    }

    fun computeAliasWithRef(base: AccessPathBase, inst: GoIRInst): List<AliasApInfo> {
        val self = listOf(AliasApInfo(base, emptyList()))
        val idx = inst.location.index
        val analysisResult = aliasAnalysisWithRef()
        val connected = analysisResult.statesBeforeStmt.getOrNull(idx) ?: return self
        for (entry in connected.aliasGroups.values) {
            val converted = entry.flatMap { convert(it, connected.aliasGroups, 0) }.distinct()
            if (converted.any { it is AliasApInfo && it.accessors.isEmpty() && it.base == base }) {
                return converted.filterIsInstance<AliasApInfo>()
            }
        }
        return self
    }

    private fun aliasAnalysisWithRef(): GoDSUAliasAnalysis.AnalysisResult {
        val noCancellation = AnalysisCancellation(Duration.INFINITE, parentCancellation = null)
        return GoDSUAliasAnalysis(function, params.interProcCallDepth, noCancellation).analyze()
    }

    private fun convert(info: AAInfo, groups: Int2ObjectOpenHashMap<List<AAInfo>>, depth: Int): List<GoAliasInfo> {
        if (info !is HeapAlias) {
            val base = convertBase(info)
            val baseWithRef = when (base) {
                is AliasAllocInfoNoRef -> AliasAllocInfo(base.allocInst)
                is AliasApInfoNoRef -> AliasApInfo(base.base, base.accessors)
                null -> null
            }
            return listOfNotNull(baseWithRef)
        }
        if (depth > HEAP_CHAIN_LIMIT) return emptyList()
        val instanceGroup = groups[info.instance] ?: return emptyList()
        val instances = instanceGroup.flatMap { convert(it, groups, depth + 1) }
        val accessor = when (val a = info.heapAccessor) {
            is GoArrayAlias -> GoAliasAccessor.Array
            is GoRefAlias -> GoAliasAccessor.Ref
            is GoFieldAlias -> a.field
            else -> error("Unexpected heap accessor")
        }
        return instances.mapNotNull {
            when (it) {
                is AliasAllocInfo -> null
                is AliasApInfo -> AliasApInfo(it.base, it.accessors + accessor)
            }
        }
    }

    private fun convertBase(info: AAInfo): GoAliasInfoNoRef? {
        if (info.ctx != ContextInfo.rootContext) return null
        return when (info) {
            is GoLocalAlias.SimpleLoc -> when (val loc = info.loc) {
                is GoRefValue.Local -> AliasApInfoNoRef(AccessPathBase.LocalVar(loc.idx), emptyList())
                is GoRefValue.Arg -> AliasApInfoNoRef(AccessPathBase.Argument(loc.idx), emptyList())
                is GoRefValue.Global -> null // todo: globals
                is GoRefValue.FreeVarBase -> AliasApInfoNoRef(AccessPathBase.This, emptyList())
            }
            is GoLocalAlias.Alloc -> AliasAllocInfoNoRef(info.inst)
            is GoReturnValue -> null
            is GoUnknown -> null
            is HeapAlias -> error("unreachable")
            else -> null
        }
    }

    private fun resolveLocalVar(
        daa: ConnectedAliases,
        result: Int2ObjectOpenHashMap<List<GoAliasInfoNoRef>>,
        unboundAliases: MutableList<List<GoAliasInfoNoRef>>,
        cancellation: AnalysisCancellation,
    ) {
        daa.aliasGroups.forEach { (_, group) ->
            val converted = group
                .flatMap { it.convertToAliasInfo(daa.aliasGroups, depth = 0, cancellation) }
                .distinct()

            // size == 1 means only local was converted to AliasInfo; not really meaningful
            if (converted.size <= 1) return@forEach

            val locals = converted.filterIsInstance<AliasApInfoNoRef>()
                .filter { it.accessors.isEmpty() }
                .mapNotNull { it.base as? AccessPathBase.LocalVar }

            if (locals.isEmpty()) {
                unboundAliases += converted
                return@forEach
            }

            locals.forEach { local ->
                result[local.idx] = converted
            }
        }
    }

    private fun AAInfo.convertToAliasInfo(
        aliasGroups: Int2ObjectOpenHashMap<List<AAInfo>>,
        depth: Int,
        cancellation: AnalysisCancellation,
    ): List<GoAliasInfoNoRef> {
        if (this !is HeapAlias) {
            val base = convertBase(this)
            return listOfNotNull(base)
        }

        if (this.heapAccessor is GoRefAlias) {
            return emptyList()
        }

        if (depth > HEAP_CHAIN_LIMIT) {
            return emptyList()
        }

        cancellation.checkpoint()

        val instanceGroup = aliasGroups[instance] ?: return emptyList()
        val instances = instanceGroup.flatMap { it.convertToAliasInfo(aliasGroups, depth + 1, cancellation) }
        val accessor = when (val a = this.heapAccessor) {
            is GoArrayAlias -> GoAliasAccessor.Array
            is GoFieldAlias -> a.field
            else -> error("Impossible")
        }

        return instances.mapNotNull {
            when (it) {
                is AliasAllocInfoNoRef -> return@mapNotNull null
                is AliasApInfoNoRef -> AliasApInfoNoRef(it.base, it.accessors + accessor)
            }
        }
    }
}

package org.opentaint.dataflow.go.analysis.alias

import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.analysis.alias.AAInfo
import org.opentaint.dataflow.ap.ifds.analysis.alias.ContextInfo
import org.opentaint.dataflow.ap.ifds.analysis.alias.HeapAlias
import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.inst.GoIRInst

sealed interface GoAliasInfo
data class AliasApInfo(val base: AccessPathBase, val accessors: List<GoAliasAccessor>) : GoAliasInfo
data class AliasAllocInfo(val allocInst: Int) : GoAliasInfo

class GoLocalAliasAnalysis(
    private val function: GoIRFunction,
    private val params: Params = Params(),
) {
    data class Params(val interProcCallDepth: Int = 0)

    companion object {
        private const val HEAP_CHAIN_LIMIT = 5
    }

    private val result: GoDSUAliasAnalysis.AnalysisResult by lazy {
        GoDSUAliasAnalysis(function, params.interProcCallDepth).analyze()
    }

    fun findAlias(base: AccessPathBase, inst: GoIRInst): List<AliasApInfo> {
        val self = listOf(AliasApInfo(base, emptyList()))
        val idx = inst.location.index
        val connected = result.statesBeforeStmt.getOrNull(idx) ?: return self
        for (entry in connected.aliasGroups.values) {
            val converted = entry.flatMap { convert(it, connected.aliasGroups, 0) }.distinct()
            if (converted.any { it is AliasApInfo && it.accessors.isEmpty() && it.base == base }) {
                return converted.filterIsInstance<AliasApInfo>()
            }
        }
        return self
    }

    private fun convert(info: AAInfo, groups: Int2ObjectOpenHashMap<List<AAInfo>>, depth: Int): List<GoAliasInfo> {
        if (info !is HeapAlias) return listOfNotNull(convertBase(info))
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

    private fun convertBase(info: AAInfo): GoAliasInfo? {
        if (info.ctx != ContextInfo.rootContext) return null
        return when (info) {
            is GoLocalAlias.SimpleLoc -> when (val loc = info.loc) {
                is GoRefValue.Local -> AliasApInfo(AccessPathBase.LocalVar(loc.idx), emptyList())
                is GoRefValue.Arg -> AliasApInfo(AccessPathBase.Argument(loc.idx), emptyList())
                is GoRefValue.Global -> AliasApInfo(AccessPathBase.ClassStatic, emptyList())
            }
            is GoLocalAlias.Alloc -> AliasAllocInfo(info.inst)
            is GoReturnValue -> null
            is GoUnknown -> null
            is HeapAlias -> error("unreachable")
            else -> null
        }
    }
}

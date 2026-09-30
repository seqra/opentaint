package org.opentaint.dataflow.ap.ifds.summary

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.MethodSummaryEdgeApplicationUtils
import org.opentaint.dataflow.ap.ifds.MethodSummaryEdgeApplicationUtils.SummaryEdgeApplication
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.ir.api.common.CommonType

class StatementSummary(val transfers: Array<BaseTransfer>) {
    data class Edge(val from: InitialFactAp, val to: InitialFactAp?)

    class BaseTransfer(
        val base: AccessPathBase,
        val edges: Array<Edge>,
        val typeFilters: Array<CommonType>,
    )

    fun find(base: AccessPathBase): BaseTransfer? {
        for (transfer in transfers) {
            if (transfer.base == base) return transfer
        }
        return null
    }

    fun transfer(
        fact: FinalFactAp,
        typeChecker: FactTypeChecker,
        propagateFact: (FinalFactAp) -> Unit,
        refineInitial: (ExclusionSet) -> Unit,
    ): Boolean {
        val transfer = find(fact.base) ?: return false

        var filtered = fact
        for (type in transfer.typeFilters) {
            filtered = typeChecker.filterFactByLocalType(type, filtered) ?: return true
        }

        for (edge in transfer.edges) {
            val to = edge.to
            for (effect in MethodSummaryEdgeApplicationUtils.tryApplySummaryEdge(filtered, edge.from)) {
                when (effect) {
                    is SummaryEdgeApplication.SummaryApRefinement -> {
                        if (to == null) continue
                        val result = to.concat(typeChecker, effect.delta) ?: continue
                        propagateFact(result.replaceExclusions(filtered.exclusions))
                    }

                    is SummaryEdgeApplication.SummaryExclusionRefinement -> {
                        if (to == null) {
                            refineInitial(effect.exclusion)
                            continue
                        }
                        val result = to.concat(typeChecker, effect.delta) ?: continue
                        propagateFact(result.replaceExclusions(effect.exclusion))
                    }
                }
            }
        }

        return true
    }

    fun preconditions(fact: InitialFactAp): List<InitialFactAp>? {
        val transfer = find(fact.base) ?: return null
        val result = transfer.edges.flatMap { edge ->
            val to = edge.to ?: return@flatMap emptyList()
            fact.delta(edge.from).map { to.concat(it).replaceExclusions(fact.exclusions) }
        }.distinct()
        return result.takeIf { it != listOf(fact) }
    }

    companion object {
        val Empty = StatementSummary(emptyArray())
    }
}

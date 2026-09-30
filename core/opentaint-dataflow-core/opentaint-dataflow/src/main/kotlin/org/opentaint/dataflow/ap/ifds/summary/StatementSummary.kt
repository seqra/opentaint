package org.opentaint.dataflow.ap.ifds.summary

import org.opentaint.dataflow.ap.ifds.AccessPathBase
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

    fun preconditionFacts(fact: InitialFactAp): List<InitialFactAp>? {
        val transfer = find(fact.base) ?: return null
        return transfer.edges.flatMap { edge ->
            val to = edge.to ?: return@flatMap emptyList()
            fact.delta(edge.from).map { to.concat(it).replaceExclusions(fact.exclusions) }
        }.distinct()
    }

    companion object {
        val Empty = StatementSummary(emptyArray())
    }
}

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

    companion object {
        val Empty = StatementSummary(emptyArray())
    }
}

package org.opentaint.dataflow.ap.ifds.access.cactus

import org.opentaint.dataflow.ap.ifds.access.common.CommonZ2FSummary
import org.opentaint.ir.api.common.cfg.CommonInst

class MethodFinalTreeApSummariesStorage(
    methodInitialStatement: CommonInst,
) : CommonZ2FSummary<CactusFinalAccess>(methodInitialStatement),
    CactusFinalApAccess {
    override fun createStorage(): Storage<CactusFinalAccess> = MethodZeroToFactSummaryEdgeStorage()

    private class MethodZeroToFactSummaryEdgeStorage : Storage<CactusFinalAccess> {
        private var summaryEdgeAccess: CactusFinalAccess? = null

        override fun add(
            edges: List<CactusFinalAccess>,
            added: MutableList<Z2FBBuilder<CactusFinalAccess>>,
        ) {
            edges.mapNotNullTo(added) { add(it) }
        }

        private fun add(edgeAccess: CactusFinalAccess): Z2FBBuilder<CactusFinalAccess>? {
            val summaryAccess = summaryEdgeAccess
            if (summaryAccess == null) {
                summaryEdgeAccess = edgeAccess
                return ZeroEdgeBuilderBuilder().setNode(edgeAccess)
            }

            val mergedAccess = summaryAccess.mergeAdd(edgeAccess)
            if (summaryAccess === mergedAccess) return null
            summaryEdgeAccess = mergedAccess
            return ZeroEdgeBuilderBuilder().setNode(mergedAccess)
        }

        override fun collectEdges(dst: MutableList<Z2FBBuilder<CactusFinalAccess>>) {
            summaryEdgeAccess?.let { dst += ZeroEdgeBuilderBuilder().setNode(it) }
        }
    }

    private class ZeroEdgeBuilderBuilder : Z2FBBuilder<CactusFinalAccess>(), CactusFinalApAccess
}

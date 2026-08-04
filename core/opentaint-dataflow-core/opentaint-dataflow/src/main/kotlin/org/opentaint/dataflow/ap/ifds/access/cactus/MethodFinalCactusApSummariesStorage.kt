package org.opentaint.dataflow.ap.ifds.access.cactus

import org.opentaint.dataflow.ap.ifds.access.common.CommonZ2FSummary
import org.opentaint.ir.api.common.cfg.CommonInst

class MethodFinalTreeApSummariesStorage(
    override val cactusManager: CactusApManager,
    methodInitialStatement: CommonInst,
) : CommonZ2FSummary<AccessCactus.AccessNode>(methodInitialStatement),
    CactusFinalApAccess {
    override fun createStorage(): Storage<AccessCactus.AccessNode> = MethodZeroToFactSummaryEdgeStorage(cactusManager)

    private class MethodZeroToFactSummaryEdgeStorage(
        private val cactusManager: CactusApManager,
    ) : Storage<AccessCactus.AccessNode> {
        private var summaryEdgeAccess: AccessCactus.AccessNode? = null

        override fun add(
            edges: List<AccessCactus.AccessNode>,
            added: MutableList<Z2FBBuilder<AccessCactus.AccessNode>>,
        ) {
            edges.mapNotNullTo(added) { add(it) }
        }

        private fun add(edgeAccess: AccessCactus.AccessNode): Z2FBBuilder<AccessCactus.AccessNode>? {
            val summaryAccess = summaryEdgeAccess
            if (summaryAccess == null) {
                summaryEdgeAccess = edgeAccess
                return ZeroEdgeBuilderBuilder(cactusManager).setNode(edgeAccess)
            }

            val mergedAccess = summaryAccess.mergeAdd(edgeAccess)
            if (summaryAccess === mergedAccess) return null

            summaryEdgeAccess = mergedAccess
            return ZeroEdgeBuilderBuilder(cactusManager).setNode(mergedAccess)
        }

        override fun collectEdges(dst: MutableList<Z2FBBuilder<AccessCactus.AccessNode>>) {
            summaryEdgeAccess?.let { dst += ZeroEdgeBuilderBuilder(cactusManager).setNode(it) }
        }
    }

    private class ZeroEdgeBuilderBuilder(
        override val cactusManager: CactusApManager,
    ) : Z2FBBuilder<AccessCactus.AccessNode>(), CactusFinalApAccess
}

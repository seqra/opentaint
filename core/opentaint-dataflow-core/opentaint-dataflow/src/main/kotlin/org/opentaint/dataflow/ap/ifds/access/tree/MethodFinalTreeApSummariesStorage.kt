package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.access.common.CommonZ2FSummary
import org.opentaint.ir.api.common.cfg.CommonInst

class MethodFinalTreeApSummariesStorage(
    methodInitialStatement: CommonInst,
    override val apManager: TreeApManager,
) : CommonZ2FSummary<AccessTree.AccessNode>(methodInitialStatement),
    TreeFinalApAccess {
    override fun createStorage(): Storage<AccessTree.AccessNode> = MethodZeroToFactSummaryEdgeStorage(apManager)

    private class MethodZeroToFactSummaryEdgeStorage(val apManager: TreeApManager): Storage<AccessTree.AccessNode> {
        // finals without [any], and the [any] parts of finals
        private val completeStorage = MergingTreeSummaryStorage(apManager)
        private val anyStorage = MergingTreeSummaryStorage(apManager)

        override fun add(edges: List<AccessTree.AccessNode>, added: MutableList<Z2FBBuilder<AccessTree.AccessNode>>) {
            edges.forEach { final ->
                if (!final.containsAny) {
                    completeStorage.add(final)
                    return@forEach
                }

                val split = final.splitAny()
                split.complete?.let { completeStorage.add(it) }
                split.any?.let { anyStorage.add(it) }
            }

            completeStorage.getAndResetDelta()?.let { added += ZeroEdgeBuilderBuilder(apManager).setNode(it) }
            anyStorage.getAndResetDelta()?.let { added += ZeroEdgeBuilderBuilder(apManager).setNode(it) }
        }

        override fun collectEdges(dst: MutableList<Z2FBBuilder<AccessTree.AccessNode>>) {
            collectCompleteEdges(dst)
            collectAnyEdges(dst)
        }

        fun collectCompleteEdges(dst: MutableList<Z2FBBuilder<AccessTree.AccessNode>>) {
            completeStorage.edges()?.let { dst += ZeroEdgeBuilderBuilder(apManager).setNode(it) }
        }

        fun collectAnyEdges(dst: MutableList<Z2FBBuilder<AccessTree.AccessNode>>) {
            anyStorage.edges()?.let { dst += ZeroEdgeBuilderBuilder(apManager).setNode(it) }
        }
    }

    private class ZeroEdgeBuilderBuilder(
        override val apManager: TreeApManager,
    ) : Z2FBBuilder<AccessTree.AccessNode>(), TreeFinalApAccess
}

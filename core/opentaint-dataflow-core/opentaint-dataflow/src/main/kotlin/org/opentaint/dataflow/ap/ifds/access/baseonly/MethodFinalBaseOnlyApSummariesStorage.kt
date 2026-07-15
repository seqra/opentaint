package org.opentaint.dataflow.ap.ifds.access.baseonly

import it.unimi.dsi.fastutil.longs.LongOpenHashSet
import org.opentaint.dataflow.ap.ifds.access.common.CommonZ2FSummary
import org.opentaint.ir.api.common.cfg.CommonInst

class MethodFinalBaseOnlyApSummariesStorage(
    methodInitialStatement: CommonInst,
    override val apManager: BaseOnlyApManager,
) : CommonZ2FSummary<BaseOnlyAccess>(methodInitialStatement), BaseOnlyFinalApAccess {
    override fun createStorage(): Storage<BaseOnlyAccess> = SummaryStorage(apManager)

    private class SummaryStorage(private val manager: BaseOnlyApManager) : Storage<BaseOnlyAccess> {
        private val edges = LongOpenHashSet()

        override fun add(edges: List<BaseOnlyAccess>, added: MutableList<Z2FBBuilder<BaseOnlyAccess>>) {
            for (edge in edges) {
                if (edge.isCollapsed) continue
                if (this.edges.add(edge)) added += Builder(manager).setNode(edge)
            }
        }

        override fun collectEdges(dst: MutableList<Z2FBBuilder<BaseOnlyAccess>>) {
            edges.forEach { dst += Builder(manager).setNode(it) }
        }
    }

    private class Builder(override val apManager: BaseOnlyApManager) :
        Z2FBBuilder<BaseOnlyAccess>(), BaseOnlyFinalApAccess
}

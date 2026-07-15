package org.opentaint.dataflow.ap.ifds.access.baseonly

import it.unimi.dsi.fastutil.longs.LongArrayList
import it.unimi.dsi.fastutil.longs.LongOpenHashSet
import org.opentaint.dataflow.ap.ifds.access.common.CommonNDF2FSummary
import org.opentaint.dataflow.ap.ifds.access.common.ndf2f.DefaultNDF2FSummaryStorageWithAp
import org.opentaint.ir.api.common.cfg.CommonInst

class MethodNDInitialToFinalBaseOnlyApSummariesStorage(
    methodEntryPoint: CommonInst,
    override val apManager: BaseOnlyApManager,
) : CommonNDF2FSummary<BaseOnlyAccess>(methodEntryPoint), BaseOnlyFinalApAccess {

    private inner class Builder : NDF2FBBuilder<BaseOnlyAccess>(), BaseOnlyFinalApAccess {
        override val apManager: BaseOnlyApManager
            get() = this@MethodNDInitialToFinalBaseOnlyApSummariesStorage.apManager
    }

    override fun createStorage(): Storage<BaseOnlyAccess> = object :
        DefaultNDF2FSummaryStorageWithAp<BaseOnlyAccess, BaseOnlyAccess>(methodEntryPoint),
        BaseOnlyInitialApAccess {
        override val apManager: BaseOnlyApManager
            get() = this@MethodNDInitialToFinalBaseOnlyApSummariesStorage.apManager

        override fun createBuilder(): NDF2FBBuilder<BaseOnlyAccess> = Builder()

        override fun createStorage(idx: Int): Storage<BaseOnlyAccess, BaseOnlyAccess> = FactStorage(idx)

        private inner class FactStorage(
            override val storageIdx: Int,
        ) : Storage<BaseOnlyAccess, BaseOnlyAccess> {
            private val edges = LongOpenHashSet()
            private val edgesDelta = LongArrayList()

            override fun add(element: BaseOnlyAccess): Storage<BaseOnlyAccess, BaseOnlyAccess>? {
                if (element.isCollapsed) return null
                if (!edges.add(element)) return null
                edgesDelta.add(element)
                return this
            }

            override fun getAndResetDelta(delta: MutableList<BaseOnlyAccess>) {
                delta.addAll(edgesDelta)
                edgesDelta.clear()
            }

            override fun collectTo(dst: MutableList<BaseOnlyAccess>) {
                dst.addAll(edges)
            }
        }
    }
}

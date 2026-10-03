package org.opentaint.dataflow.ap.ifds.access.baseonly

import it.unimi.dsi.fastutil.longs.LongArrayList
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.common.CommonNDF2FSummary
import org.opentaint.dataflow.ap.ifds.access.common.ndf2f.DefaultNDF2FSummaryStorageWithAp
import org.opentaint.dataflow.util.forEachLong
import org.opentaint.dataflow.util.longSet
import org.opentaint.ir.api.common.cfg.CommonInst
import java.util.BitSet
import java.util.concurrent.ConcurrentHashMap

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
        BaseOnlyInitialApAccess,
        BaseOnlyFinalApAccess {
        override val apManager: BaseOnlyApManager
            get() = this@MethodNDInitialToFinalBaseOnlyApSummariesStorage.apManager

        private val initialAccessIndices =
            ConcurrentHashMap<AccessPathBase, BaseOnlyInitialAccessIndex<Int>>()

        override fun initialApAdded(idx: Int, ap: InitialFactAp) {
            val byAccess = initialAccessIndices.computeIfAbsent(ap.base) { BaseOnlyInitialAccessIndex() }
            val indexed = byAccess.getOrCreate(getInitialAccess(ap)) { idx }
            check(indexed == idx) { "Different ND initial facts have the same canonical BaseOnly access" }
        }

        override fun relevantInitialAp(summaryInitialFactPattern: FinalFactAp): BitSet {
            val pattern = getFinalAccess(summaryInitialFactPattern)
            val result = BitSet()
            initialAccessIndices[summaryInitialFactPattern.base]?.collectCandidates(pattern) { initial, idx ->
                if (baseOnlySummaryInitialMatches(pattern, initial)) result.set(idx)
            }
            return result
        }

        override fun createBuilder(): NDF2FBBuilder<BaseOnlyAccess> = Builder()

        override fun createStorage(idx: Int): Storage<BaseOnlyAccess, BaseOnlyAccess> = FactStorage(idx)

        private inner class FactStorage(
            override val storageIdx: Int,
        ) : Storage<BaseOnlyAccess, BaseOnlyAccess> {
            private val edges = longSet()
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
                edges.forEachLong(dst::add)
            }
        }
    }
}

package org.opentaint.dataflow.ap.ifds.access.common

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Edge
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactToFactEdgeBuilder
import org.opentaint.dataflow.ap.ifds.MethodSummaryFactEdgesForExitPoint
import org.opentaint.dataflow.ap.ifds.SummaryFactStorage
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialToFinalSummaryStorageStats
import org.opentaint.dataflow.ap.ifds.access.MethodInitialToFinalApSummariesStorage
import org.opentaint.dataflow.util.collectToListWithPostProcess
import org.opentaint.ir.api.common.cfg.CommonInst

abstract class CommonF2FSummary<IAP, FAP: Any>(val methodEntryPoint: CommonInst):
    MethodInitialToFinalApSummariesStorage, InitialApAccess<IAP>, FinalApAccess<FAP> {

    data class StorageEdge<IAP, FAP>(val initial: IAP, val final: FAP, val exclusion: ExclusionSet)

    interface Storage<IAP, FAP : Any> {
        fun add(edges: List<StorageEdge<IAP, FAP>>, added: MutableList<F2FBBuilder<IAP, FAP>>)
        fun collectSummariesTo(dst: MutableList<F2FBBuilder<IAP, FAP>>, initialFactPatter: FAP?)
        fun collectSummariesByFinalTo(dst: MutableList<F2FBBuilder<IAP, FAP>>, finalFactPattern: FAP) {
            collectSummariesTo(dst, initialFactPatter = null)
        }
        fun storageStats(): InitialToFinalSummaryStorageStats? = null
    }

    abstract fun createStorage(): Storage<IAP, FAP>

    private val storage = MethodTaintedSummariesStorage()

    override fun add(edges: List<Edge.FactToFact>, added: MutableList<FactToFactEdgeBuilder>) {
        storage.add(edges, added)
    }

    override fun filterEdgesTo(
        dst: MutableList<FactToFactEdgeBuilder>,
        initialFactPattern: FinalFactAp?,
        finalFactBase: AccessPathBase?
    ) {
        storage.filterEdgesTo(dst, EdgeStoragePattern(initialFactPattern, finalFactBase, finalFactPattern = null))
    }

    override fun filterEdgesByFinalTo(
        dst: MutableList<FactToFactEdgeBuilder>,
        finalFactPattern: FinalFactAp,
    ) {
        storage.filterEdgesTo(
            dst,
            EdgeStoragePattern(
                initialFactPattern = null,
                finalFactBase = finalFactPattern.base,
                finalFactPattern = finalFactPattern,
            ),
        )
    }

    override fun storageStats(): InitialToFinalSummaryStorageStats? = storage.storageStats()

    private class EdgeStoragePattern(
        val initialFactPattern: FinalFactAp?,
        val finalFactBase: AccessPathBase?,
        val finalFactPattern: FinalFactAp?,
    )

    private inner class MethodTaintedSummariesStorage : MethodSummaryFactEdgesForExitPoint<MethodFactToFactSummaries, EdgeStoragePattern>(methodEntryPoint) {

        override fun createStorage(): MethodFactToFactSummaries = MethodFactToFactSummaries()

        override fun storageAdd(
            storage: MethodFactToFactSummaries,
            edges: List<Edge.FactToFact>,
            added: MutableList<FactToFactEdgeBuilder>
        ) = storage.add(edges, added)

        override fun storageFilterEdgesTo(
            dst: MutableList<FactToFactEdgeBuilder>,
            storage: MethodFactToFactSummaries,
            containsPattern: EdgeStoragePattern
        ) {
            storage.filterTo(dst, containsPattern)
        }

        fun storageStats(): InitialToFinalSummaryStorageStats? = sumStorageStats { body ->
            forEachStorage { storage -> body(storage.storageStats()) }
        }
    }

    private inner class MethodFactToFactSummaries : SummaryFactStorage<MethodTaintedSummariesGroupedByFact>(methodEntryPoint) {
        override fun createStorage() = MethodTaintedSummariesGroupedByFact()

        fun add(edges: List<Edge.FactToFact>, added: MutableList<FactToFactEdgeBuilder>) {
            val sameInitialBaseEdges = edges.groupBy { it.initialFactAp.base }
            for ((initialBase, sameBaseEdges) in sameInitialBaseEdges) {
                collectToListWithPostProcess(
                    added,
                    { getOrCreate(initialBase).add(sameBaseEdges, it) },
                    { it.setInitialFactBase(initialBase).build() }
                )
            }
        }

        fun filterTo(dst: MutableList<FactToFactEdgeBuilder>, pattern: EdgeStoragePattern) {
            val initialFactBase = pattern.initialFactPattern?.base
            if (initialFactBase != null) {
                val storage = find(initialFactBase) ?: return
                filterTo(
                    dst,
                    storage,
                    initialFactBase,
                    pattern.finalFactBase,
                    getFinalAccess(pattern.initialFactPattern),
                    pattern.finalFactPattern?.let { getFinalAccess(it) },
                )
            } else {
                forEachValue { base, storage ->
                    filterTo(
                        dst,
                        storage,
                        base,
                        pattern.finalFactBase,
                        pattern.initialFactPattern?.let { getFinalAccess(it) },
                        pattern.finalFactPattern?.let { getFinalAccess(it) },
                    )
                }
            }
        }

        fun storageStats(): InitialToFinalSummaryStorageStats? = sumStorageStats { body ->
            forEachValue { _, storage -> body(storage.storageStats()) }
        }

        private fun filterTo(
            dst: MutableList<FactToFactEdgeBuilder>,
            storage: MethodTaintedSummariesGroupedByFact,
            initialFactBase: AccessPathBase,
            finalFactBase: AccessPathBase?,
            containsPattern: FAP?,
            finalFactPattern: FAP?,
        ) {
            collectToListWithPostProcess(dst, {
                storage.filterEdgesTo(it, containsPattern, finalFactBase, finalFactPattern)
            }, {
                it.setInitialFactBase(initialFactBase).build()
            })
        }
    }

    private inner class MethodTaintedSummariesGroupedByFact :
        SummaryFactStorage<Storage<IAP, FAP>>(methodEntryPoint) {
        override fun createStorage() = this@CommonF2FSummary.createStorage()

        fun storageStats(): InitialToFinalSummaryStorageStats? = sumStorageStats { body ->
            forEachValue { _, storage -> body(storage.storageStats()) }
        }

        fun add(edges: List<Edge.FactToFact>, added: MutableList<F2FBBuilder<IAP, FAP>>) {
            val sameExitBaseEdges = edges.groupBy { it.factAp.base }
            for ((exitBase, sameBaseEdges) in sameExitBaseEdges) {
                val edgesToAdd = sameBaseEdges.map {
                    StorageEdge(
                        getInitialAccess(it.initialFactAp),
                        getFinalAccess(it.factAp),
                        it.initialFactAp.exclusions
                    )
                }

                collectToListWithPostProcess(
                    added,
                    { getOrCreate(exitBase).add(edgesToAdd, it) },
                    { it.setExitFactBase(exitBase) }
                )
            }
        }

        fun filterEdgesTo(
            dst: MutableList<F2FBBuilder<IAP, FAP>>,
            containsPattern: FAP?,
            finalFactBase: AccessPathBase?,
            finalFactPattern: FAP?,
        ) {
            if (finalFactBase != null) {
                val storage = find(finalFactBase) ?: return
                collectTo(dst, storage, finalFactBase, containsPattern, finalFactPattern)
            } else {
                forEachValue { base, storage ->
                    collectTo(dst, storage, base, containsPattern, finalFactPattern)
                }
            }
        }

        private fun collectTo(
            dst: MutableList<F2FBBuilder<IAP, FAP>>,
            storage: Storage<IAP, FAP>,
            finalFactBase: AccessPathBase,
            containsPattern: FAP?,
            finalFactPattern: FAP?,
        ) = collectToListWithPostProcess(dst, {
            if (finalFactPattern == null) {
                storage.collectSummariesTo(it, containsPattern)
            } else {
                storage.collectSummariesByFinalTo(it, finalFactPattern)
            }
        }, {
            it.setExitFactBase(finalFactBase)
        })
    }

    private inline fun sumStorageStats(
        collect: ((InitialToFinalSummaryStorageStats?) -> Unit) -> Unit,
    ): InitialToFinalSummaryStorageStats? {
        var supported = false
        var edgeCount = 0L
        var finalFactSizeSum = 0L
        collect { stats ->
            if (stats != null) {
                supported = true
                edgeCount += stats.edgeCount
                finalFactSizeSum += stats.finalFactSizeSum
            }
        }
        return if (supported) InitialToFinalSummaryStorageStats(edgeCount, finalFactSizeSum) else null
    }

    abstract class F2FBBuilder<IAP, FAP: Any>(
        private var initialBase: AccessPathBase? = null,
        private var exitBase: AccessPathBase? = null,
        private var exclusion: ExclusionSet? = null,
        private var initialAp: IAP? = null,
        private var exitAp: FAP? = null,
    ): InitialApAccess<IAP>, FinalApAccess<FAP> {
        abstract fun nonNullIAP(iap: IAP?): IAP

        fun build(): FactToFactEdgeBuilder = FactToFactEdgeBuilder()
            .setInitialAp(createInitial(initialBase!!, nonNullIAP(initialAp), exclusion!!))
            .setExitAp(createFinal(exitBase!!, exitAp!!, exclusion!!))

        fun setInitialFactBase(base: AccessPathBase) = this.also { initialBase = base }
        fun setExitFactBase(base: AccessPathBase) = this.also { exitBase = base }
        fun setExclusion(exclusion: ExclusionSet) = this.also { this.exclusion = exclusion }
        fun setInitialAp(ap: IAP) = this.also { initialAp = ap }
        fun setExitAp(ap: FAP) = this.also { exitAp = ap }
    }
}

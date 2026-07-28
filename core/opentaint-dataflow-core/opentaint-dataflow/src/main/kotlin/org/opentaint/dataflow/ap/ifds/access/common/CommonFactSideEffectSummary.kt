package org.opentaint.dataflow.ap.ifds.access.common

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.SideEffectKind
import org.opentaint.dataflow.ap.ifds.SideEffectSummary.FactSideEffectSummary
import org.opentaint.dataflow.ap.ifds.SummaryFactStorage
import org.opentaint.dataflow.ap.ifds.access.FactSideEffectSummariesApStorage
import org.opentaint.dataflow.ap.ifds.access.FactDemandState
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.util.collectToListWithPostProcess
import org.opentaint.ir.api.common.cfg.CommonInst
import java.util.concurrent.ConcurrentHashMap

abstract class CommonFactSideEffectSummary<IAP, FAP: Any>(val methodEntryPoint: CommonInst):
    FactSideEffectSummariesApStorage, InitialApAccess<IAP>, FinalApAccess<FAP> {

    interface Storage<IAP, FAP : Any> {
        fun add(iap: IAP, se: Map<SideEffectKind, FactDemandState>, added: MutableList<FactSEBuilder<IAP>>)
        fun collectSummariesTo(dst: MutableList<FactSEBuilder<IAP>>, initialFactPattern: FAP?)
    }

    abstract fun createStorage(): Storage<IAP, FAP>

    private val storage = MethodTaintedSideEffectSummaries()

    override fun add(sideEffects: List<FactSideEffectSummary>, added: MutableList<FactSideEffectSummary>) {
        storage.add(sideEffects, added)
    }

    override fun filterTaintedTo(dst: MutableList<FactSideEffectSummary>, pattern: FinalFactAp?) {
        storage.filterSummariesTo(dst, pattern)
    }

    private inner class MethodTaintedSideEffectSummaries : SummaryFactStorage<Storage<IAP, FAP>>(methodEntryPoint) {
        override fun createStorage() = this@CommonFactSideEffectSummary.createStorage()

        fun add(sideEffects: List<FactSideEffectSummary>, added: MutableList<FactSideEffectSummary>) {
            val sameInitialBaseEdges = sideEffects.groupBy { it.initialFactAp.base }
            for ((initialBase, sameBaseEdges) in sameInitialBaseEdges) {
                val ses = sameBaseEdges.groupBy(
                    { getInitialAccess(it.initialFactAp) },
                    { Pair(it.kind, it.initialFactAp.demandState) }
                )

                val baseStorage = getOrCreate(initialBase)
                for ((iap, se) in ses) {
                    val sameKindSe = se.groupBy({ it.first }, { it.second })
                        .mapValues { (_, states) -> states.reduce(FactDemandState::join) }

                    collectToListWithPostProcess(
                        added,
                        { baseStorage.add(iap, sameKindSe, it) },
                        { it.setInitialFactBase(initialBase).build() }
                    )
                }
            }
        }

        fun filterSummariesTo(dst: MutableList<FactSideEffectSummary>, pattern: FinalFactAp?) {
            val patternBase = pattern?.base
            if (patternBase != null) {
                val storage = find(patternBase) ?: return
                collectTo(dst, storage, patternBase, getFinalAccess(pattern))
            } else {
                forEachValue { base, storage ->
                    collectTo(dst, storage, base, pattern?.let { getFinalAccess(it) })
                }
            }
        }

        private fun collectTo(
            dst: MutableList<FactSideEffectSummary>,
            storage: Storage<IAP, FAP>,
            initialFactBase: AccessPathBase,
            containsPattern: FAP?
        ) {
            collectToListWithPostProcess(dst, {
                storage.collectSummariesTo(it, containsPattern)
            }, {
                it.setInitialFactBase(initialFactBase).build()
            })
        }
    }

    abstract class SideEffectExclusionMergingStorage<IAP> {
        private val sideEffects = ConcurrentHashMap<SideEffectKind, FactDemandState>()

        abstract fun createBuilder(): FactSEBuilder<IAP>

        fun add(kind: SideEffectKind, demandState: FactDemandState): FactSEBuilder<IAP>? {
            val currentState = sideEffects.putIfAbsent(kind, demandState)
            if (currentState == null) {
                return toBuilder(kind, demandState)
            }

            val mergedState = currentState join demandState
            if (currentState === mergedState) return null

            sideEffects[kind] = mergedState
            return toBuilder(kind, mergedState)
        }

        fun summaries(): List<FactSEBuilder<IAP>> =
            sideEffects.map { (kind, demandState) ->
                toBuilder(kind, demandState)
            }

        private fun toBuilder(kind: SideEffectKind, demandState: FactDemandState) =
            createBuilder()
                .setKind(kind)
                .setDemandState(demandState)
    }

    abstract class FactSEBuilder<IAP>(
        private var initialBase: AccessPathBase? = null,
        private var initialAp: IAP? = null,
        private var demandState: FactDemandState? = null,
        private var kind: SideEffectKind? = null,
    ): InitialApAccess<IAP> {
        abstract fun nonNullIAP(iap: IAP?): IAP

        fun build(): FactSideEffectSummary =
            FactSideEffectSummary(createInitial(initialBase!!, nonNullIAP(initialAp), demandState!!), kind!!)

        fun setInitialFactBase(base: AccessPathBase) = this.also { initialBase = base }
        fun setDemandState(demandState: FactDemandState) = this.also { this.demandState = demandState }
        fun setKind(kind: SideEffectKind) = this.also { this.kind = kind }
        fun setInitialAp(ap: IAP) = this.also { initialAp = ap }
    }
}

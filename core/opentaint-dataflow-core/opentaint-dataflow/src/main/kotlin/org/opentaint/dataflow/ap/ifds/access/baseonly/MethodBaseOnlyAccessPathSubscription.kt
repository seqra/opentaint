package org.opentaint.dataflow.ap.ifds.access.baseonly

import it.unimi.dsi.fastutil.longs.LongOpenHashSet
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.common.CommonAPSub
import org.opentaint.dataflow.ap.ifds.access.common.CommonFactEdgeSubBuilder
import org.opentaint.dataflow.ap.ifds.access.common.CommonFactNDEdgeSubBuilder
import org.opentaint.dataflow.ap.ifds.access.common.CommonZeroEdgeSubBuilder
import org.opentaint.dataflow.ap.ifds.access.common.ndf2f.DefaultNDF2FSubStorageWithAp
import org.opentaint.ir.api.common.cfg.CommonInst
import java.util.BitSet

class MethodBaseOnlyAccessPathSubscription(
    override val apManager: BaseOnlyApManager,
) : CommonAPSub<BaseOnlyAccess, BaseOnlyAccess>(), BaseOnlyInitialApAccess, BaseOnlyFinalApAccess {

    override fun createZ2FSubStorage(callerEp: CommonInst): Z2FSubStorage<BaseOnlyAccess, BaseOnlyAccess> =
        Z2FSub(apManager)

    override fun createF2FSubStorage(callerEp: CommonInst): F2FSubStorage<BaseOnlyAccess, BaseOnlyAccess> =
        F2FSub(apManager)

    override fun createNDF2FSubStorage(callerEp: CommonInst): NDF2FSubStorage<BaseOnlyAccess, BaseOnlyAccess> =
        NDSub(callerEp, apManager)

    private class Z2FSub(private val manager: BaseOnlyApManager) :
        CommonAPSub.Z2FSubStorage<BaseOnlyAccess, BaseOnlyAccess> {
        private val edges = LongOpenHashSet()
        private val edgeIndex = BaseOnlyInitialAccessIndex<Unit>()

        override fun add(callerExitAp: BaseOnlyAccess): CommonZeroEdgeSubBuilder<BaseOnlyAccess>? {
            if (!edges.add(callerExitAp)) return null
            edgeIndex.getOrCreate(callerExitAp) { Unit }
            return ZeroBuilder(manager).setNode(callerExitAp)
        }

        override fun find(dst: MutableList<CommonZeroEdgeSubBuilder<BaseOnlyAccess>>, summaryInitialFact: BaseOnlyAccess) {
            edgeIndex.collectCandidates(summaryInitialFact) { exit, _ ->
                val match = BaseOnlyAccessOps.matchPrefix(exit, summaryInitialFact)
                if (match.emptyDelta || match.hasSuffix) {
                    dst += ZeroBuilder(manager).setNode(exit)
                }
            }
        }
    }

    private class F2FSub(private val manager: BaseOnlyApManager) :
        CommonAPSub.F2FSubStorage<BaseOnlyAccess, BaseOnlyAccess> {
        private val initialFactsByExit =
            BaseOnlyInitialAccessIndex<MutableSet<BaseOnlyInitialFactAp>>()

        override fun add(
            callerInitialAp: InitialFactAp,
            callerExitAp: BaseOnlyAccess,
        ): CommonFactEdgeSubBuilder<BaseOnlyAccess>? {
            callerInitialAp as BaseOnlyInitialFactAp
            val initialFacts = initialFactsByExit.getOrCreate(callerExitAp, ::hashSetOf)
            if (!initialFacts.add(callerInitialAp)) return null
            return FactBuilder(manager)
                .setCallerNode(callerExitAp)
                .setCallerInitialAp(callerInitialAp)
                .setCallerExclusion(callerInitialAp.exclusions)
        }

        override fun find(
            dst: MutableList<CommonFactEdgeSubBuilder<BaseOnlyAccess>>,
            summaryInitialFact: BaseOnlyAccess,
            emptyDeltaRequired: Boolean,
        ) {
            initialFactsByExit.collectCandidates(summaryInitialFact) { exit, initialFacts ->
                val match = BaseOnlyAccessOps.matchPrefix(exit, summaryInitialFact)
                if (!match.emptyDelta && !match.hasSuffix) return@collectCandidates
                collectExit(dst, exit, initialFacts)
            }
        }

        private fun collectExit(
            dst: MutableList<CommonFactEdgeSubBuilder<BaseOnlyAccess>>,
            exit: BaseOnlyAccess,
            initialFacts: Set<BaseOnlyInitialFactAp>,
        ) {
            initialFacts.forEach { initial ->
                dst += FactBuilder(manager)
                    .setCallerNode(exit)
                    .setCallerInitialAp(initial)
                    .setCallerExclusion(initial.exclusions)
            }
        }
    }

    private class NDSub(callerEp: CommonInst, private val manager: BaseOnlyApManager) :
        DefaultNDF2FSubStorageWithAp<BaseOnlyAccess, BaseOnlyAccess>(callerEp), BaseOnlyInitialApAccess {
        override val apManager: BaseOnlyApManager get() = manager

        override fun createBuilder(): CommonFactNDEdgeSubBuilder<BaseOnlyAccess> = NDBuilder(manager)

        override fun add(
            callerInitial: Set<InitialFactAp>,
            callerExitAp: BaseOnlyAccess,
        ): CommonFactNDEdgeSubBuilder<BaseOnlyAccess>? = super.add(
            callerInitial.mapTo(hashSetOf()) { it.replaceExclusions(ExclusionSet.Universe) },
            callerExitAp,
        )

        private var maxIdx = 0

        override fun createStorage(idx: Int): Storage<BaseOnlyAccess, BaseOnlyAccess> {
            maxIdx = maxOf(maxIdx, idx)
            return FactStorage()
        }

        override fun relevantStorageIndices(summaryInitialFact: BaseOnlyAccess): BitSet =
            BitSet().also { it.set(0, maxIdx + 1) }

        private inner class FactStorage : Storage<BaseOnlyAccess, BaseOnlyAccess> {
            private val edges = LongOpenHashSet()

            override fun add(element: BaseOnlyAccess): BaseOnlyAccess? =
                if (edges.add(element)) element else null

            override fun collect(dst: MutableList<BaseOnlyAccess>) {
                dst.addAll(edges)
            }

            override fun collect(dst: MutableList<BaseOnlyAccess>, summaryInitialFact: BaseOnlyAccess) {
                dst.addAll(edges)
            }
        }
    }

    private class ZeroBuilder(override val apManager: BaseOnlyApManager) :
        CommonZeroEdgeSubBuilder<BaseOnlyAccess>(), BaseOnlyFinalApAccess

    private class FactBuilder(override val apManager: BaseOnlyApManager) :
        CommonFactEdgeSubBuilder<BaseOnlyAccess>(), BaseOnlyFinalApAccess

    private class NDBuilder(override val apManager: BaseOnlyApManager) :
        CommonFactNDEdgeSubBuilder<BaseOnlyAccess>(), BaseOnlyFinalApAccess
}

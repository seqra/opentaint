package org.opentaint.dataflow.ap.ifds.access.cactus

import it.unimi.dsi.fastutil.objects.Object2ObjectOpenHashMap
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.common.CommonAPSub
import org.opentaint.dataflow.ap.ifds.access.common.CommonFactEdgeSubBuilder
import org.opentaint.dataflow.ap.ifds.access.common.CommonFactNDEdgeSubBuilder
import org.opentaint.dataflow.ap.ifds.access.common.CommonZeroEdgeSubBuilder
import org.opentaint.dataflow.ap.ifds.access.common.ndf2f.DefaultNDF2FSubStorageWithAp
import org.opentaint.ir.api.common.cfg.CommonInst
import java.util.BitSet

class MethodCactusAccessPathSubscription :
    CommonAPSub<CactusInitialAccess, CactusFinalAccess>(),
    CactusInitialApAccess, CactusFinalApAccess {
    override fun createZ2FSubStorage(callerEp: CommonInst): Z2FSubStorage<CactusInitialAccess, CactusFinalAccess> =
        SummaryEdgeFactTreeSubscriptionStorage()

    override fun createF2FSubStorage(callerEp: CommonInst): F2FSubStorage<CactusInitialAccess, CactusFinalAccess> =
        SummaryEdgeFactAbstractTreeSubscriptionStorage()

    override fun createNDF2FSubStorage(callerEp: CommonInst): NDF2FSubStorage<CactusInitialAccess, CactusFinalAccess> =
        NDSubStorage(callerEp)
}

private class SummaryEdgeFactAbstractTreeSubscriptionStorage: CommonAPSub.F2FSubStorage<CactusInitialAccess, CactusFinalAccess> {
    private val storage = Object2ObjectOpenHashMap<AccessPathWithCycles, CactusFinalAccess>()

    override fun add(
        callerInitialAp: InitialFactAp,
        callerExitAp: CactusFinalAccess
    ): CommonFactEdgeSubBuilder<CactusFinalAccess>? {
        callerInitialAp as AccessPathWithCycles

        val current = storage[callerInitialAp]
        if (current == null) {
            storage[callerInitialAp] = callerExitAp
            return FactEdgeSubBuilder()
                .setCallerNode(callerExitAp)
                .setCallerInitialAp(callerInitialAp)
                .setCallerDemandState(callerInitialAp.demandState)
        }

        val (mergedExitAp, delta) = current.mergeAddDelta(callerExitAp)
        if (delta == null) return null

        storage[callerInitialAp] = mergedExitAp

        return FactEdgeSubBuilder()
            .setCallerNode(delta)
            .setCallerInitialAp(callerInitialAp)
            .setCallerDemandState(callerInitialAp.demandState)
    }

    // todo: filter
    override fun find(
        dst: MutableList<CommonFactEdgeSubBuilder<CactusFinalAccess>>,
        summaryInitialFact: CactusInitialAccess,
        emptyDeltaRequired: Boolean
    ) {
        storage.mapTo(dst) { (callerInitialAp, callerExitAp) ->
            FactEdgeSubBuilder()
                .setCallerNode(callerExitAp)
                .setCallerInitialAp(callerInitialAp)
                .setCallerDemandState(callerInitialAp.demandState)
        }
    }
}

private class SummaryEdgeFactTreeSubscriptionStorage: CommonAPSub.Z2FSubStorage<CactusInitialAccess, CactusFinalAccess> {
    private var callerPathEdgeFactAp: CactusFinalAccess? = null

    override fun add(callerExitAp: CactusFinalAccess): CommonZeroEdgeSubBuilder<CactusFinalAccess>? {
        if (callerPathEdgeFactAp == null) {
            callerPathEdgeFactAp = callerExitAp
            return ZeroEdgeSubBuilder().setNode(callerExitAp)
        }

        val (mergedAccess, mergeAccessDelta) = callerPathEdgeFactAp!!.mergeAddDelta(callerExitAp)
        if (mergeAccessDelta == null) return null

        callerPathEdgeFactAp = mergedAccess

        return ZeroEdgeSubBuilder().setNode(mergeAccessDelta)
    }

    override fun find(
        dst: MutableList<CommonZeroEdgeSubBuilder<CactusFinalAccess>>,
        summaryInitialFact: CactusInitialAccess,
    ) {
        callerPathEdgeFactAp?.filterStartsWith(summaryInitialFact)?.let {
            dst += ZeroEdgeSubBuilder().setNode(it)
        }
    }
}

private class NDSubStorage(callerEp: CommonInst) :
    DefaultNDF2FSubStorageWithAp<CactusInitialAccess, CactusFinalAccess>(callerEp),
    CactusInitialApAccess {
    override fun createBuilder(): CommonFactNDEdgeSubBuilder<CactusFinalAccess> = FactNDEdgeSubBuilder()

    private var maxIdx = 0
    override fun createStorage(idx: Int): Storage<CactusInitialAccess, CactusFinalAccess> {
        maxIdx = maxOf(maxIdx, idx)
        return FactStorage()
    }

    private inner class FactStorage : Storage<CactusInitialAccess, CactusFinalAccess> {
        private var current: CactusFinalAccess? = null

        override fun add(element: CactusFinalAccess): CactusFinalAccess? {
            val cur = current
            if (cur == null) {
                current = element
                return element
            }

            val (mergedExitAp, delta) = cur.mergeAddDelta(element)
            if (delta == null) return null

            current = mergedExitAp
            return delta
        }

        override fun collect(dst: MutableList<CactusFinalAccess>) {
            current?.let { dst.add(it) }
        }

        override fun collect(dst: MutableList<CactusFinalAccess>, summaryInitialFact: CactusInitialAccess) {
            current?.filterStartsWith(summaryInitialFact)?.let { dst.add(it) }
        }
    }

    override fun relevantStorageIndices(summaryInitialFact: CactusInitialAccess): BitSet {
        return BitSet().also { it.set(0, maxIdx + 1) }
    }
}

private class ZeroEdgeSubBuilder : CommonZeroEdgeSubBuilder<CactusFinalAccess>(), CactusFinalApAccess
private class FactEdgeSubBuilder : CommonFactEdgeSubBuilder<CactusFinalAccess>(), CactusFinalApAccess
private class FactNDEdgeSubBuilder : CommonFactNDEdgeSubBuilder<CactusFinalAccess>(), CactusFinalApAccess

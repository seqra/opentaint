package org.opentaint.dataflow.ap.ifds.access.tree.suffix

import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.common.CommonAPSub
import org.opentaint.dataflow.ap.ifds.access.common.CommonFactEdgeSubBuilder
import org.opentaint.dataflow.ap.ifds.access.common.CommonFactNDEdgeSubBuilder
import org.opentaint.dataflow.ap.ifds.access.common.CommonZeroEdgeSubBuilder
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree
import org.opentaint.dataflow.ap.ifds.access.tree.SummaryEdgeFactTreeSubscriptionStorage
import org.opentaint.dataflow.ap.ifds.access.tree.TreeApManager
import org.opentaint.dataflow.ap.ifds.access.tree.TreeFinalApAccess
import org.opentaint.dataflow.util.collectToListWithPostProcess
import org.opentaint.ir.api.common.cfg.CommonInst

class MethodTreeSuffixAccessPathSubscription(
    override val apManager: TreeSuffixApManager,
) : CommonAPSub<FactAccess, FactAccess>(),
    TreeSuffixInitialFactAccess,
    TreeSuffixFinalFactAccess {

    override fun createF2FSubStorage(callerEp: CommonInst): F2FSubStorage<FactAccess, FactAccess> =
        SummaryEdgeFactAbstractTreeSuffixSubscriptionStorage(apManager)

    override fun createNDF2FSubStorage(callerEp: CommonInst): NDF2FSubStorage<FactAccess, FactAccess> =
        SummaryEdgeFactNDAbstractTreeSuffixSubscriptionStorage(apManager)

    override fun createZ2FSubStorage(callerEp: CommonInst): Z2FSubStorage<FactAccess, FactAccess> =
        SummaryEdgeFactTreeSuffixSubscriptionStorage(apManager)
}

private class SummaryEdgeFactAbstractTreeSuffixSubscriptionStorage(
    private val manager: TreeSuffixApManager,
) : CommonAPSub.F2FSubStorage<FactAccess, FactAccess> {
    override fun add(
        callerInitialAp: InitialFactAp,
        callerExitAp: FactAccess
    ): CommonFactEdgeSubBuilder<FactAccess>? {
        TODO("Not yet implemented")
    }

    override fun find(
        dst: MutableList<CommonFactEdgeSubBuilder<FactAccess>>,
        summaryInitialFact: FactAccess,
        emptyDeltaRequired: Boolean
    ) {
        TODO("Not yet implemented")
    }
}

private class SummaryEdgeFactNDAbstractTreeSuffixSubscriptionStorage(
    private val manager: TreeSuffixApManager,
) : CommonAPSub.NDF2FSubStorage<FactAccess, FactAccess> {
    override fun add(
        callerInitial: Set<InitialFactAp>,
        callerExitAp: FactAccess
    ): CommonFactNDEdgeSubBuilder<FactAccess>? {
        TODO("Not yet implemented")
    }

    override fun find(
        dst: MutableList<CommonFactNDEdgeSubBuilder<FactAccess>>,
        summaryInitialFact: FactAccess,
        emptyDeltaRequired: Boolean
    ) {
        TODO("Not yet implemented")
    }
}

private class SummaryEdgeFactTreeSuffixSubscriptionStorage(
    private val manager: TreeSuffixApManager,
) : CommonAPSub.Z2FSubStorage<FactAccess, FactAccess> {
    private val treeStorage = SummaryEdgeFactTreeSubscriptionStorage(manager.treeManager)

    override fun add(callerExitAp: FactAccess): CommonZeroEdgeSubBuilder<FactAccess>? {
        val treeNode = callerExitAp.toSingleTreeNode()
        val addedBuilder = treeStorage.add(treeNode)
            ?: return null

        val addedNode = addedBuilder.node()

        return ZeroEdgeSubBuilder(manager)
            .setNode(suffixOnlyAccess(addedNode))
    }

    override fun find(
        dst: MutableList<CommonZeroEdgeSubBuilder<FactAccess>>,
        summaryInitialFact: FactAccess
    ) {
        collectToListWithPostProcess(
            dst,
            { treeStorage.find(it, summaryInitialFact = null) }, // todo: filter
            {
                val node = it.node()
                ZeroEdgeSubBuilder(manager)
                    .setNode(suffixOnlyAccess(node))
            }
        )
    }
}

private class ZeroEdgeSubBuilder(
    override val apManager: TreeSuffixApManager,
) : CommonZeroEdgeSubBuilder<FactAccess>(), TreeSuffixFinalFactAccess

private class FactEdgeSubBuilder(
    override val apManager: TreeSuffixApManager,
) : CommonFactEdgeSubBuilder<FactAccess>(), TreeSuffixFinalFactAccess

private class FactNDEdgeSubBuilder(
    override val apManager: TreeSuffixApManager,
) : CommonFactNDEdgeSubBuilder<FactAccess>(), TreeSuffixFinalFactAccess

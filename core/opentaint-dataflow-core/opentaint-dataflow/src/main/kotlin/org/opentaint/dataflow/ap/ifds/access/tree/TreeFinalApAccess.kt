package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.access.FactDemandState
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.common.FinalApAccess

interface TreeFinalApAccess: FinalApAccess<AccessTree.AccessNode> {
    val apManager: TreeApManager

    override fun getFinalAccess(factAp: FinalFactAp): AccessTree.AccessNode =
        (factAp as AccessTree).access

    override fun createFinal(base: AccessPathBase, ap: AccessTree.AccessNode, demandState: FactDemandState): FinalFactAp {
        return AccessTree(apManager, base, ap, demandState.exclusions)
    }
}

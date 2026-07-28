package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.access.FactFlowState
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.common.FinalApAccess

interface TreeFinalApAccess: FinalApAccess<AccessTree.AccessNode> {
    val apManager: TreeApManager

    override fun getFinalAccess(factAp: FinalFactAp): AccessTree.AccessNode =
        (factAp as AccessTree).access

    override fun createFinal(base: AccessPathBase, ap: AccessTree.AccessNode, flowState: FactFlowState): FinalFactAp {
        check(flowState.deepCleanEffects.isEmpty) { "Tree cleaner effects must be structural" }
        return AccessTree(apManager, base, ap, flowState.exclusions)
    }
}

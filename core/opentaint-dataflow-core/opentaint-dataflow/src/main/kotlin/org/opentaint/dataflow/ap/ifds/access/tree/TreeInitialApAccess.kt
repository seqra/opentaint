package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.access.FactFlowState
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.common.InitialApAccess

interface TreeInitialApAccess: InitialApAccess<AccessPath.AccessNode?> {
    val apManager: TreeApManager

    override fun getInitialAccess(factAp: InitialFactAp): AccessPath.AccessNode? =
        (factAp as AccessPath).access

    override fun createInitial(base: AccessPathBase, ap: AccessPath.AccessNode?, flowState: FactFlowState): InitialFactAp {
        check(flowState.deepCleanEffects.isEmpty) { "Tree cleaner effects must be structural" }
        return AccessPath(apManager, base, ap, flowState.exclusions)
    }
}

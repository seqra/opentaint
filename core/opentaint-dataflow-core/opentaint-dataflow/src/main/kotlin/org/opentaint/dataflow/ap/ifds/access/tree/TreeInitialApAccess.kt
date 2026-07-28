package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.access.FactDemandState
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.common.InitialApAccess

interface TreeInitialApAccess: InitialApAccess<AccessPath.AccessNode?> {
    val apManager: TreeApManager

    override fun getInitialAccess(factAp: InitialFactAp): AccessPath.AccessNode? =
        (factAp as AccessPath).access

    override fun createInitial(base: AccessPathBase, ap: AccessPath.AccessNode?, demandState: FactDemandState): InitialFactAp {
        return AccessPath(apManager, base, ap, demandState.exclusions)
    }
}

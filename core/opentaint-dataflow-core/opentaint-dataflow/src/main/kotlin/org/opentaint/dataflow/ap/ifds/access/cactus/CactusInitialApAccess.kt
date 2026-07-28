package org.opentaint.dataflow.ap.ifds.access.cactus

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.access.FactFlowState
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.common.InitialApAccess

interface CactusInitialApAccess: InitialApAccess<AccessPathWithCycles.AccessNode?> {
    override fun getInitialAccess(factAp: InitialFactAp): AccessPathWithCycles.AccessNode? =
        (factAp as AccessPathWithCycles).access

    override fun createInitial(base: AccessPathBase, ap: AccessPathWithCycles.AccessNode?, flowState: FactFlowState): InitialFactAp =
        AccessPathWithCycles(base, ap, flowState.exclusions, flowState.deepCleanEffects)
}

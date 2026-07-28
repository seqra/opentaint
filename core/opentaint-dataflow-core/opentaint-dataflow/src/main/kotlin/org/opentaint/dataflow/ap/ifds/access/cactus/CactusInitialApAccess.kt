package org.opentaint.dataflow.ap.ifds.access.cactus

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.access.AnyFieldAccess
import org.opentaint.dataflow.ap.ifds.access.FactDemandState
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.common.InitialApAccess
import org.opentaint.dataflow.ap.ifds.access.forExclusions

typealias CactusInitialAccess = AnyFieldAccess<AccessPathWithCycles.AccessNode?>
typealias CactusFinalAccess = AnyFieldAccess<AccessCactus.AccessNode>

interface CactusInitialApAccess: InitialApAccess<CactusInitialAccess> {
    override fun getInitialAccess(
        factAp: InitialFactAp,
    ): CactusInitialAccess =
        (factAp as AccessPathWithCycles).let {
            AnyFieldAccess(it.access, it.anyFieldCleanerEffects)
        }

    override fun createInitial(
        base: AccessPathBase,
        ap: CactusInitialAccess,
        demandState: FactDemandState,
    ): InitialFactAp =
        AccessPathWithCycles(
            base,
            ap.access,
            demandState.exclusions,
            ap.cleanerEffects.forExclusions(demandState.exclusions),
        )
}

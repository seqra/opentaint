package org.opentaint.dataflow.ap.ifds.access.cactus

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.access.FactDemandState
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.common.FinalApAccess
import org.opentaint.dataflow.ap.ifds.access.forExclusions

interface CactusFinalApAccess: FinalApAccess<CactusFinalAccess> {
    override fun getFinalAccess(factAp: FinalFactAp): CactusFinalAccess =
        (factAp as AccessCactus).let {
            CactusFinalAccess(it.access, it.anyFieldCleanerEffects)
        }

    override fun createFinal(
        base: AccessPathBase,
        ap: CactusFinalAccess,
        demandState: FactDemandState,
    ): FinalFactAp =
        AccessCactus(
            base,
            ap.access,
            demandState.exclusions,
            ap.cleanerEffects.forExclusions(demandState.exclusions),
        )
}

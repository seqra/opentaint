package org.opentaint.dataflow.ap.ifds.access.cactus

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.common.FinalApAccess

data class CactusFinalAccess(
    val access: AccessCactus.AccessNode,
    val anyFieldMarkExclusions: CactusAnyFieldMarkExclusions,
)

interface CactusFinalApAccess: FinalApAccess<CactusFinalAccess> {
    override fun getFinalAccess(factAp: FinalFactAp): CactusFinalAccess =
        (factAp as AccessCactus).let {
            CactusFinalAccess(it.access, it.anyFieldMarkExclusions)
        }

    override fun createFinal(
        base: AccessPathBase,
        ap: CactusFinalAccess,
        exclusion: ExclusionSet,
    ): FinalFactAp =
        AccessCactus(
            base,
            ap.access,
            exclusion,
            ap.anyFieldMarkExclusions.forExclusions(exclusion),
        )
}

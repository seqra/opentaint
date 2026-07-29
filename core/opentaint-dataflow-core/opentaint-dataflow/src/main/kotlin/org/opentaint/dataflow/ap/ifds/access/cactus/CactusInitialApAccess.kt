package org.opentaint.dataflow.ap.ifds.access.cactus

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.common.InitialApAccess

typealias CactusInitialAccess = AccessPathWithCycles.AccessNode?

interface CactusInitialApAccess: InitialApAccess<CactusInitialAccess> {
    override fun getInitialAccess(
        factAp: InitialFactAp,
    ): CactusInitialAccess =
        (factAp as AccessPathWithCycles).access

    override fun createInitial(
        base: AccessPathBase,
        ap: CactusInitialAccess,
        exclusion: ExclusionSet,
    ): InitialFactAp = AccessPathWithCycles(base, ap, exclusion)
}

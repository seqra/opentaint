package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.common.FinalApAccess
import org.opentaint.dataflow.ap.ifds.access.common.InitialApAccess

interface BaseOnlyFinalApAccess : FinalApAccess<BaseOnlyAccess> {
    val apManager: BaseOnlyApManager

    override fun getFinalAccess(factAp: FinalFactAp): BaseOnlyAccess =
        (factAp as BaseOnlyFinalFactAp).access

    override fun createFinal(base: AccessPathBase, ap: BaseOnlyAccess, ex: ExclusionSet): FinalFactAp =
        BaseOnlyFinalFactAp(apManager, base, ap, ex)

}

interface BaseOnlyInitialApAccess : InitialApAccess<BaseOnlyAccess> {
    val apManager: BaseOnlyApManager

    override fun getInitialAccess(factAp: InitialFactAp): BaseOnlyAccess =
        (factAp as BaseOnlyInitialFactAp).access

    override fun createInitial(base: AccessPathBase, ap: BaseOnlyAccess, ex: ExclusionSet): InitialFactAp =
        BaseOnlyInitialFactAp(apManager, base, ap, ex)

}

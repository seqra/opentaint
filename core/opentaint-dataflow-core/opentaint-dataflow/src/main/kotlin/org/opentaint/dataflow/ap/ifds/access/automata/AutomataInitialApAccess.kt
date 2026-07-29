package org.opentaint.dataflow.ap.ifds.access.automata

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.common.InitialApAccess

typealias AutomataInitialAccess = AccessGraph

interface AutomataInitialApAccess: InitialApAccess<AutomataInitialAccess> {
    override fun getInitialAccess(factAp: InitialFactAp): AutomataInitialAccess =
        (factAp as AccessGraphInitialFactAp).access

    override fun createInitial(
        base: AccessPathBase,
        ap: AutomataInitialAccess,
        ex: ExclusionSet,
    ): InitialFactAp = AccessGraphInitialFactAp(base, ap, ex)
}

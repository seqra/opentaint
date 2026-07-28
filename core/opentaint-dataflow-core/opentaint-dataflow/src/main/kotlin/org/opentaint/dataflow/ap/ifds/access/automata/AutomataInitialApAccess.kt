package org.opentaint.dataflow.ap.ifds.access.automata

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.access.AnyFieldAccess
import org.opentaint.dataflow.ap.ifds.access.FactDemandState
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.common.InitialApAccess
import org.opentaint.dataflow.ap.ifds.access.forExclusions

typealias AutomataAccess = AnyFieldAccess<AccessGraph>

interface AutomataInitialApAccess: InitialApAccess<AutomataAccess> {
    override fun getInitialAccess(factAp: InitialFactAp): AutomataAccess =
        (factAp as AccessGraphInitialFactAp).let { AnyFieldAccess(it.access, it.anyFieldCleanerEffects) }

    override fun createInitial(
        base: AccessPathBase,
        ap: AutomataAccess,
        demandState: FactDemandState,
    ): InitialFactAp =
        AccessGraphInitialFactAp(
            base,
            ap.access,
            demandState.exclusions,
            ap.cleanerEffects.forExclusions(demandState.exclusions),
        )
}

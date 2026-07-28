package org.opentaint.dataflow.ap.ifds.access.automata

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.access.FactDemandState
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.common.FinalApAccess
import org.opentaint.dataflow.ap.ifds.access.forExclusions

interface AutomataFinalApAccess : FinalApAccess<AutomataAccess> {
    override fun getFinalAccess(factAp: FinalFactAp): AutomataAccess =
        (factAp as AccessGraphFinalFactAp).let {
            AutomataAccess(it.access, it.anyFieldCleanerEffects)
        }

    override fun createFinal(
        base: AccessPathBase,
        ap: AutomataAccess,
        demandState: FactDemandState,
    ): FinalFactAp =
        AccessGraphFinalFactAp(
            base,
            ap.access,
            demandState.exclusions,
            ap.cleanerEffects.forExclusions(demandState.exclusions),
        )
}

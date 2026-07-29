package org.opentaint.dataflow.ap.ifds.access.automata

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.access.AnyFieldMarkExclusions
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.common.FinalApAccess
import org.opentaint.dataflow.ap.ifds.access.forExclusions

data class AutomataFinalAccess(
    val access: AccessGraph,
    val anyFieldMarkExclusions: AnyFieldMarkExclusions,
)

interface AutomataFinalApAccess : FinalApAccess<AutomataFinalAccess> {
    override fun getFinalAccess(factAp: FinalFactAp): AutomataFinalAccess =
        (factAp as AccessGraphFinalFactAp).let {
            AutomataFinalAccess(it.access, it.anyFieldMarkExclusions)
        }

    override fun createFinal(
        base: AccessPathBase,
        ap: AutomataFinalAccess,
        ex: ExclusionSet,
    ): FinalFactAp =
        AccessGraphFinalFactAp(
            base,
            ap.access,
            ex,
            ap.anyFieldMarkExclusions.forExclusions(ex),
        )
}

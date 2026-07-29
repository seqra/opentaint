package org.opentaint.dataflow.ap.ifds.access.automata

import org.opentaint.dataflow.ap.ifds.access.common.CommonFinalFactList

class AutomataFinalFactList: CommonFinalFactList<AutomataFinalAccess>(), AutomataFinalApAccess {
    override val storage: AccessStorage<AutomataFinalAccess> = Default()
}

package org.opentaint.dataflow.ap.ifds.access.automata

import org.opentaint.dataflow.ap.ifds.access.common.CommonFinalFactList

class AutomataFinalFactList: CommonFinalFactList<AutomataAccess>(), AutomataFinalApAccess {
    override val storage: AccessStorage<AutomataAccess> = Default()
}

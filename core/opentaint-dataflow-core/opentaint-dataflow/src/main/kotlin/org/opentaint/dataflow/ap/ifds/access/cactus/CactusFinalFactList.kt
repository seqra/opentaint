package org.opentaint.dataflow.ap.ifds.access.cactus

import org.opentaint.dataflow.ap.ifds.access.common.CommonFinalFactList

class CactusFinalFactList: CommonFinalFactList<CactusFinalAccess>(), CactusFinalApAccess {
    override val storage: AccessStorage<CactusFinalAccess> = Default()
}

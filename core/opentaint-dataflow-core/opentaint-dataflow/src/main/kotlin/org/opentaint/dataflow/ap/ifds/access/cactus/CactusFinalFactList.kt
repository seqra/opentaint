package org.opentaint.dataflow.ap.ifds.access.cactus

import org.opentaint.dataflow.ap.ifds.access.common.CommonFinalFactList

class CactusFinalFactList(
    override val cactusManager: CactusApManager,
): CommonFinalFactList<AccessCactus.AccessNode>(), CactusFinalApAccess {
    override val storage: AccessStorage<AccessCactus.AccessNode> = Default()
}

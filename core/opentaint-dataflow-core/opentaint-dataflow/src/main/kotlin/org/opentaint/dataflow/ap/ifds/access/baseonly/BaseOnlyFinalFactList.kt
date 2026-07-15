package org.opentaint.dataflow.ap.ifds.access.baseonly

import it.unimi.dsi.fastutil.longs.LongArrayList
import org.opentaint.dataflow.ap.ifds.access.common.CommonFinalFactList

class BaseOnlyFinalFactList(
    override val apManager: BaseOnlyApManager,
) : CommonFinalFactList<BaseOnlyAccess>(), BaseOnlyFinalApAccess {
    override val storage: AccessStorage<BaseOnlyAccess> = LongAccessStorage()

    private class LongAccessStorage : AccessStorage<BaseOnlyAccess> {
        private val storage = LongArrayList()

        override fun add(fact: BaseOnlyAccess) {
            storage.add(fact)
        }

        override fun get(idx: Int): BaseOnlyAccess = storage.getLong(idx)

        override fun removeLast(): BaseOnlyAccess = storage.removeLong(storage.size - 1)
    }
}

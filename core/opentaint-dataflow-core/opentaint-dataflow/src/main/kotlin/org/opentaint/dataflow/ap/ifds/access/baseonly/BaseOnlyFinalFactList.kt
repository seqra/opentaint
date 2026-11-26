package org.opentaint.dataflow.ap.ifds.access.baseonly

import it.unimi.dsi.fastutil.longs.LongArrayList
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.common.CommonFinalFactList

class BaseOnlyFinalFactList(
    override val apManager: BaseOnlyApManager,
) : CommonFinalFactList<BaseOnlyAccess>(), BaseOnlyFinalApAccess {
    override val storage: AccessStorage<BaseOnlyAccess> = LongAccessStorage()

    override fun add(fact: FinalFactAp) {
        fact as BaseOnlyFinalFactAp
        if (fact.access.isCollapsed) return
        super.add(fact)
    }

    private class LongAccessStorage : AccessStorage<BaseOnlyAccess> {
        private val storage = LongArrayList()

        override fun add(fact: BaseOnlyAccess) {
            storage.add(fact)
        }

        override fun get(idx: Int): BaseOnlyAccess = storage.getLong(idx)

        override fun removeLast(): BaseOnlyAccess = storage.removeLong(storage.size - 1)
    }
}

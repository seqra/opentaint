package org.opentaint.dataflow.ap.ifds.access.tree.suffix

import org.opentaint.dataflow.ap.ifds.access.common.CommonFinalFactList

class FactList(
    override val apManager: TreeSuffixApManager,
) : CommonFinalFactList<FactAccess>(), TreeSuffixFinalFactAccess {
    override val storage: AccessStorage<FactAccess> = TreeSuffixFactAccessStorage(apManager)

    private class TreeSuffixFactAccessStorage(
        val apManager: TreeSuffixApManager,
    ) : AccessStorage<FactAccess> {
        override fun add(fact: FactAccess) {
            TODO("Not yet implemented")
        }

        override fun get(idx: Int): FactAccess {
            TODO("Not yet implemented")
        }

        override fun removeLast(): FactAccess {
            TODO("Not yet implemented")
        }
    }
}

package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.common.CommonFinalFactList

class TreeFinalFactList(
    override val apManager: TreeApManager
) : CommonFinalFactList<AccessTree.AccessNode>(), TreeFinalApAccess {
    override val storage: AccessStorage<AccessTree.AccessNode> = TreeNodeListStorage(apManager)

    private class TreeNodeListStorage(val apManager: TreeApManager) : AccessStorage<AccessTree.AccessNode> {
        private val storage = mutableListOf<AccessTree.AccessNode>()

        override fun add(fact: AccessTree.AccessNode) {
            storage.add(apManager.canonicalizeAccessTree(fact))
        }

        override fun get(idx: Int): AccessTree.AccessNode = storage[idx]
        override fun removeLast(): AccessTree.AccessNode = storage.removeLast()
    }

    companion object {
        fun factCompressionRequired(fact: FinalFactAp): Boolean =
            (fact as AccessTree).access.size > 100
    }
}

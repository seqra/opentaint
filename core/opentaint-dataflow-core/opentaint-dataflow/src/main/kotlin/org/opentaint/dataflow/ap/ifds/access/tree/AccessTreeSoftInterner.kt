package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree.AccessNode
import java.util.IdentityHashMap

class AccessTreeSoftInterner(
    private val apManager: TreeApManager,
) {
    fun intern(node: AccessNode): AccessNode =
        node.internNodes(getOrCreateInterner(), IdentityHashMap(), global = true)

    inline fun <T> withInterner(body: (AccessTreeInterner, IdentityHashMap<AccessNode, AccessNode>) -> T): T =
        body(getOrCreateInterner(), IdentityHashMap())

    fun getOrCreateInterner(): AccessTreeInterner = apManager.getOrCreateAccessTreeInterner()
}

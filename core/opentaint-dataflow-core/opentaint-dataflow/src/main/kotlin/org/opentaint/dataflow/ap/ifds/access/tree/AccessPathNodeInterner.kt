package org.opentaint.dataflow.ap.ifds.access.tree

import it.unimi.dsi.fastutil.objects.Object2ObjectOpenHashMap
import org.opentaint.dataflow.ap.ifds.access.tree.AccessPath.AccessNode

class AccessPathNodeInterner(
    private val maxEntries: Int = 250_000,
) {
    private val cache = Object2ObjectOpenHashMap<AccessNode, AccessNode>()

    init {
        require(maxEntries > 0)
    }

    @Synchronized
    fun intern(node: AccessNode): AccessNode {
        cache[node]?.let { return it }
        if (cache.size >= maxEntries) cache.clear()
        cache[node] = node
        return node
    }
}

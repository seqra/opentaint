package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree.AccessNode
import java.util.concurrent.atomic.AtomicReferenceArray

internal class AccessNodeFilterCache(slotCount: Int = 65_536) {
    private class Entry(
        val node: AccessNode,
        val filter: FactTypeChecker.CacheableFactApFilter,
        val result: CachedResult,
    )

    private sealed interface CachedResult {
        data class Node(val node: AccessNode) : CachedResult
        data object Empty : CachedResult
    }

    private val entries: AtomicReferenceArray<Entry>
    private val mask: Int

    init {
        require(slotCount > 0 && slotCount.countOneBits() == 1)
        entries = AtomicReferenceArray(slotCount)
        mask = slotCount - 1
    }

    fun getOrCompute(
        node: AccessNode,
        filter: FactTypeChecker.CacheableFactApFilter,
        compute: () -> AccessNode?,
    ): AccessNode? {
        val index = (System.identityHashCode(node) * -1640531527 + filter.hashCode()) and mask
        val entry = entries.get(index)
        if (entry != null && entry.node === node && entry.filter == filter) {
            return entry.result.unpack()
        }

        val computed = compute()
        val cached = computed?.let(CachedResult::Node) ?: CachedResult.Empty
        entries.set(index, Entry(node, filter, cached))
        return computed
    }

    private fun CachedResult.unpack(): AccessNode? = when (this) {
        is CachedResult.Node -> node
        CachedResult.Empty -> null
    }
}

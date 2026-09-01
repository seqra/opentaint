package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.SummaryFactStorage
import org.opentaint.dataflow.util.ConcurrentReadSafeObject2IntMap
import org.opentaint.dataflow.util.object2IntMap
import org.opentaint.ir.api.common.cfg.CommonInst
import java.util.BitSet

class AccessPathInterner(
    val manager: TreeApManager,
    methodEntryPoint: CommonInst
) {
    private var size = 0
    private val storage = BasedStorage(methodEntryPoint)

    fun getOrCreateIndex(
        base: AccessPathBase,
        node: AccessPath.AccessNode?,
        onNewIdx: (Int) -> Unit,
    ): Int {
        val interner = storage.getOrCreate(base)
        return interner.getOrCreate(node) {
            val nextIdx = size++
            onNewIdx(nextIdx)
            nextIdx
        }
    }

    fun findBaseIndices(base: AccessPathBase): BitSet? = storage.find(base)?.allIndices

    private class BasedStorage(methodEntryPoint: CommonInst) :
        SummaryFactStorage<ApInterner>(methodEntryPoint) {
        override fun createStorage(): ApInterner = ApInterner()
    }

    private class ApInterner {
        private class SingleEntry(
            @JvmField val access: AccessPath.AccessNode?,
            @JvmField val index: Int,
        )

        val allIndices = BitSet()
        @Volatile
        private var entries: Any? = null

        fun getOrCreate(ap: AccessPath.AccessNode?, nextIdx: () -> Int): Int {
            find(ap)?.let { return it }

            synchronized(this) {
                when (val current = entries) {
                    null -> {
                        val index = nextIdx()
                        entries = SingleEntry(ap, index)
                        allIndices.set(index)
                        return index
                    }

                    is SingleEntry -> {
                        if (current.access == ap) return current.index

                        val map = object2IntMap<AccessPath.AccessNode?>()
                        map.put(current.access, current.index)
                        val index = nextIdx()
                        map.put(ap, index)
                        entries = map
                        allIndices.set(index)
                        return index
                    }

                    else -> {
                        @Suppress("UNCHECKED_CAST")
                        val map = current as ConcurrentReadSafeObject2IntMap<AccessPath.AccessNode?>
                        val existing = map.getInt(ap)
                        if (existing != ConcurrentReadSafeObject2IntMap.NO_VALUE) return existing

                        val index = nextIdx()
                        map.put(ap, index)
                        allIndices.set(index)
                        return index
                    }
                }
            }
        }

        private fun find(ap: AccessPath.AccessNode?): Int? = when (val current = entries) {
            null -> null
            is SingleEntry -> current.index.takeIf { current.access == ap }
            else -> {
                @Suppress("UNCHECKED_CAST")
                val map = current as ConcurrentReadSafeObject2IntMap<AccessPath.AccessNode?>
                map.getInt(ap).takeIf { it != ConcurrentReadSafeObject2IntMap.NO_VALUE }
            }
        }
    }
}

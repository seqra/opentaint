package org.opentaint.dataflow.jvm.ap.ifds.alias

import it.unimi.dsi.fastutil.objects.Object2IntOpenHashMap
import org.opentaint.dataflow.jvm.ap.ifds.alias.LValue.Companion.getLValueOf
import java.util.BitSet

class AAInfoManager(
    private val elementToIndex: Object2IntOpenHashMap<AAInfo> = Object2IntOpenHashMap<AAInfo>(),
    private val indexToElement: MutableList<AAInfo> = mutableListOf(),
    private val heapElements: BitSet = BitSet()
) {
    init {
        elementToIndex.defaultReturnValue(NOT_PRESENT)
    }

    fun getOrAdd(x: AAInfo): Int {
        if (x is LValue) {
            return x.assignee.inv()
        }
        val index = elementToIndex.getInt(x)
        if (index != NOT_PRESENT) return index
        val newIndex = indexToElement.size
        elementToIndex[x] = newIndex
        indexToElement.add(x)

        if (x is HeapAlias) {
            heapElements.set(newIndex)
        }

        return newIndex
    }

    fun getElement(index: Int): AAInfo? {
        if (index.isLValue()) {
            val normalValue = getElement(index.inv()) ?: return null
            return getLValueOf(normalValue)
        }
        if (index >= indexToElement.size) return null
        return indexToElement[index]
    }

    fun getElementUncheck(index: Int): AAInfo {
        return getElement(index) ?: error("Expected element at $index, none found!")
    }

    fun isHeapAlias(index: Int): Boolean = index >= 0 && heapElements.get(index)

    fun getHeapRefUnchecked(index: Int): HeapAlias =
        getElementUncheck(index) as? HeapAlias
            ?: error("Heap alias expected")

    fun replaceHeapInstance(index: Int, newInstance: Int): Int {
        val element = getHeapRefUnchecked(index)
        val newElement = element.copy(instance = newInstance)
        return getOrAdd(newElement)
    }

    companion object {
        private const val NOT_PRESENT: Int = Int.MIN_VALUE
    }
}

@ConsistentCopyVisibility
data class LValue private constructor(val assignee: Int, override val ctx: ContextInfo) : AAInfo {
    override val infoKind: Int get() = 5

    override fun compareInfo(other: AAInfo): Int = compare(other as LValue)

    fun compare(other: LValue): Int = assignee.compareTo(other.assignee)

    companion object {
        fun AAInfoManager.getLValueOf(alias: AAInfo): AAInfo {
            if (alias is LValue)
                return alias
            return LValue(getOrAdd(alias), alias.ctx)
        }
    }
}

fun Int.isLValue() = this < 0

fun Int.ensureNonLValue() = if (this < 0) this.inv() else this

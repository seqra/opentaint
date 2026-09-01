package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree.AccessNode as AccessTreeNode
import java.util.Arrays

open class TreeSetWithCompression(
    private val columns: Int,
    val manager: TreeApManager,
) {
    protected class Row(@JvmField val keys: IntArray, @JvmField val values: Array<Any?>)

    @Volatile
    private var rows: Row? = null

    protected fun rows(): Row? = rows

    protected fun offsetOf(row: Row, instruction: Int): Int {
        val position = Arrays.binarySearch(row.keys, instruction)
        return if (position < 0) -1 else position * columns
    }

    protected fun rowsForWrite(instruction: Int): Row {
        val current = rows
        if (current != null && Arrays.binarySearch(current.keys, instruction) >= 0) return current

        val oldKeys = current?.keys ?: EMPTY_KEYS
        val oldValues = current?.values ?: EMPTY_VALUES
        val insertAt = -Arrays.binarySearch(oldKeys, instruction) - 1
        val keys = IntArray(oldKeys.size + 1)
        System.arraycopy(oldKeys, 0, keys, 0, insertAt)
        keys[insertAt] = instruction
        System.arraycopy(oldKeys, insertAt, keys, insertAt + 1, oldKeys.size - insertAt)

        val values = arrayOfNulls<Any?>((oldKeys.size + 1) * columns)
        System.arraycopy(oldValues, 0, values, 0, insertAt * columns)
        System.arraycopy(
            oldValues,
            insertAt * columns,
            values,
            (insertAt + 1) * columns,
            (oldKeys.size - insertAt) * columns,
        )
        return Row(keys, values).also { rows = it }
    }

    fun internIfRequired(node: AccessTreeNode): AccessTreeNode = manager.canonicalizeAccessTree(node)

    private companion object {
        private val EMPTY_KEYS = IntArray(0)
        private val EMPTY_VALUES = arrayOfNulls<Any?>(0)
    }
}

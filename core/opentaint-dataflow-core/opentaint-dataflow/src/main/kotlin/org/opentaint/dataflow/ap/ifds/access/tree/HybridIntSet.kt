package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.util.forEach
import java.util.Arrays
import java.util.BitSet

internal class HybridIntSet(private val sparseLimit: Int = 512) {
    private var sparse: IntArray? = EMPTY
    private var dense: BitSet? = null

    fun add(value: Int) {
        val values = sparse
        if (values == null) {
            dense!!.set(value)
            return
        }
        if (values.isNotEmpty() && values[values.lastIndex] == value) return

        val found = Arrays.binarySearch(values, value)
        if (found >= 0) return
        if (values.size >= sparseLimit) {
            val promoted = BitSet()
            for (existing in values) promoted.set(existing)
            promoted.set(value)
            dense = promoted
            sparse = null
            return
        }

        val insertAt = -found - 1
        val next = IntArray(values.size + 1)
        System.arraycopy(values, 0, next, 0, insertAt)
        next[insertAt] = value
        System.arraycopy(values, insertAt, next, insertAt + 1, values.size - insertAt)
        sparse = next
    }

    fun forEach(body: (Int) -> Unit) {
        val values = sparse
        if (values != null) {
            for (value in values) body(value)
        } else {
            dense!!.forEach(body)
        }
    }

    private companion object {
        private val EMPTY = IntArray(0)
    }
}

package org.opentaint.dataflow.ap.ifds.serialization

import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.access.DeepAccessorExclusion
import org.opentaint.dataflow.ap.ifds.access.util.AccessorIdx
import java.io.DataInputStream
import java.io.DataOutputStream

class DeepExclusionsSerializer(
    private val context: SummarySerializationContext,
    private val index: (Accessor) -> AccessorIdx,
    private val accessor: (AccessorIdx) -> Accessor,
) {
    fun DataOutputStream.writeAnyFieldAccessorExclusions(exclusions: DeepAccessorExclusion?) {
        writeAccessors(exclusions?.accessorsFromDepth0 ?: EMPTY)
        writeAccessors(exclusions?.accessorsFromDepth1 ?: EMPTY)
    }

    private fun DataOutputStream.writeAccessors(accessors: IntArray) {
        writeInt(accessors.size)
        accessors.forEach { writeLong(context.getIdByAccessor(accessor(it))) }
    }

    fun DataInputStream.readAnyFieldAccessorExclusions(): DeepAccessorExclusion? {
        val accessorsFromDepth0 = readAccessors()
        val accessorsFromDepth1 = readAccessors()
        return DeepAccessorExclusion.create(accessorsFromDepth0, accessorsFromDepth1)
    }

    private fun DataInputStream.readAccessors(): IntArray =
        IntArray(readInt()) {
            index(context.getAccessorById(readLong()))
        }.also(IntArray::sort)

    companion object {
        private val EMPTY = IntArray(0)
    }
}

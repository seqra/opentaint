package org.opentaint.dataflow.ap.ifds.serialization

import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.access.AnyFieldMarkExclusions
import org.opentaint.dataflow.ap.ifds.access.util.AccessorIdx
import java.io.DataInputStream
import java.io.DataOutputStream

class AnyFieldMarkExclusionsSerializer(
    private val context: SummarySerializationContext,
    private val index: (Accessor) -> AccessorIdx,
    private val accessor: (AccessorIdx) -> Accessor,
) {
    fun DataOutputStream.writeAnyFieldMarkExclusions(exclusions: AnyFieldMarkExclusions) {
        writeMarks(exclusions.marksFromDepth1)
        writeMarks(exclusions.marksFromDepth2)
    }

    private fun DataOutputStream.writeMarks(marks: IntArray) {
        writeInt(marks.size)
        marks.forEach { writeLong(context.getIdByAccessor(accessor(it))) }
    }

    fun DataInputStream.readAnyFieldMarkExclusions(): AnyFieldMarkExclusions {
        val depth1 = readMarks()
        val depth2 = readMarks()
        return AnyFieldMarkExclusions.create(depth1, depth2) ?: AnyFieldMarkExclusions.Empty
    }

    private fun DataInputStream.readMarks(): IntArray =
        IntArray(readInt()) {
            index(context.getAccessorById(readLong()))
        }.also(IntArray::sort)
}

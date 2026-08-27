package org.opentaint.dataflow.ap.ifds.serialization

import kotlinx.collections.immutable.persistentHashSetOf
import kotlinx.collections.immutable.toPersistentHashSet
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import java.io.DataInputStream
import java.io.DataOutputStream

class ExclusionSetSerializer(private val context: SummarySerializationContext) {
    fun DataOutputStream.writeExclusionSet(exclusionSet: ExclusionSet) {
        when (exclusionSet) {
            ExclusionSet.Empty -> writeEnum(ExclusionSetType.EMPTY)
            ExclusionSet.Universe -> writeEnum(ExclusionSetType.UNIVERSE)
            is ExclusionSet.Concrete -> if (exclusionSet.write.isEmpty()) {
                // Nothing to record beyond the accessor set, so stay on the pre-split shape. There is
                // no schema version on the persisted store, and an older build meeting an unknown tag
                // throws out of `readEnum` rather than invalidating, so only content that genuinely
                // needs the new shape should get it.
                writeEnum(ExclusionSetType.CONCRETE)
                writeAccessors(exclusionSet.flat)
            } else {
                writeEnum(ExclusionSetType.CONCRETE_RW)
                writeAccessors(exclusionSet.flat)
                writeAccessors(exclusionSet.write)
            }
        }
    }

    fun DataInputStream.readExclusionSet(): ExclusionSet {
        val kind = readEnum<ExclusionSetType>()
        return when (kind) {
            ExclusionSetType.EMPTY -> ExclusionSet.Empty
            ExclusionSetType.UNIVERSE -> ExclusionSet.Universe
            // Pre-split blobs carry no kinds; everything in them is a read demand.
            ExclusionSetType.CONCRETE -> ExclusionSet.Concrete.create(readAccessors(), EMPTY_ACCESSORS)
            ExclusionSetType.CONCRETE_RW -> {
                // Read order is part of the format; do not fold these into the call arguments.
                val flat = readAccessors()
                val write = readAccessors()
                ExclusionSet.Concrete.create(flat, write)
            }
        }
    }

    private fun DataOutputStream.writeAccessors(accessors: Set<Accessor>) {
        writeInt(accessors.size)
        accessors.forEach {
            writeLong(context.getIdByAccessor(it))
        }
    }

    private fun DataInputStream.readAccessors() =
        List(readInt()) { context.getAccessorById(readLong()) }.toPersistentHashSet()

    private enum class ExclusionSetType {
        EMPTY,
        UNIVERSE,

        /** Pre read/write-split shape: a single accessor set, all of it a read demand. */
        CONCRETE,
        CONCRETE_RW
    }

    private companion object {
        private val EMPTY_ACCESSORS = persistentHashSetOf<Accessor>()
    }
}

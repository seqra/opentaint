package org.opentaint.dataflow.ap.ifds.serialization

import org.opentaint.dataflow.ap.ifds.DeepMarkExclusion
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import java.io.DataInputStream
import java.io.DataOutputStream

class ExclusionSetSerializer(private val context: SummarySerializationContext) {
    fun DataOutputStream.writeExclusionSet(exclusionSet: ExclusionSet) {
        when (exclusionSet) {
            ExclusionSet.Empty -> writeEnum(ExclusionSetType.EMPTY)
            ExclusionSet.Universe -> writeEnum(ExclusionSetType.UNIVERSE)
            is ExclusionSet.Concrete -> {
                writeEnum(ExclusionSetType.CONCRETE)
                writeInt(exclusionSet.nonDeepExclusion().size)
                exclusionSet.nonDeepExclusion().forEach {
                    writeLong(context.getIdByAccessor(it))
                }
                writeInt(exclusionSet.deepExclusion().size)
                exclusionSet.deepExclusion().forEach {
                    writeLong(context.getIdByAccessor(it))
                }
            }
        }
    }

    fun DataInputStream.readExclusionSet(): ExclusionSet {
        val kind = readEnum<ExclusionSetType>()
        return when (kind) {
            ExclusionSetType.EMPTY -> ExclusionSet.Empty
            ExclusionSetType.UNIVERSE -> ExclusionSet.Universe
            ExclusionSetType.CONCRETE -> {
                val size = readInt()
                val accessors = List(size) { context.getAccessorById(readLong()) }
                val deepSize = readInt()
                val deepAccessors = List(deepSize) { context.getAccessorById(readLong()) as DeepMarkExclusion }
                return ExclusionSet.Concrete(accessors.toSet(), deepAccessors.toSet())
            }
        }
    }

    private enum class ExclusionSetType {
        EMPTY,
        UNIVERSE,
        CONCRETE
    }
}
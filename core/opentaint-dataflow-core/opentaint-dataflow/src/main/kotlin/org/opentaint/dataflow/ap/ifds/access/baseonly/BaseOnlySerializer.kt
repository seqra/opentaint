package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.serialization.AccessPathBaseSerializer
import org.opentaint.dataflow.ap.ifds.serialization.ApSerializer
import org.opentaint.dataflow.ap.ifds.serialization.ExclusionSetSerializer
import org.opentaint.dataflow.ap.ifds.serialization.SummarySerializationContext
import java.io.DataInputStream
import java.io.DataOutputStream

internal class BaseOnlySerializer(
    private val manager: BaseOnlyApManager,
    private val context: SummarySerializationContext,
) : ApSerializer {
    private val exclusionSetSerializer = ExclusionSetSerializer(context)

    override fun DataOutputStream.writeFinalAp(ap: FinalFactAp) {
        ap as BaseOnlyFinalFactAp
        writeFact(ap.base, ap.exclusions, ap.access)
    }

    override fun DataOutputStream.writeInitialAp(ap: InitialFactAp) {
        ap as BaseOnlyInitialFactAp
        writeFact(ap.base, ap.exclusions, ap.access)
    }

    override fun DataInputStream.readFinalAp(): FinalFactAp {
        val fact = readFact()
        return BaseOnlyFinalFactAp(manager, fact.base, fact.access, fact.exclusions)
    }

    override fun DataInputStream.readInitialAp(): InitialFactAp {
        val fact = readFact()
        return BaseOnlyInitialFactAp(manager, fact.base, fact.access, fact.exclusions)
    }

    private fun DataOutputStream.writeFact(base: AccessPathBase, exclusions: ExclusionSet, access: BaseOnlyAccess) {
        with(AccessPathBaseSerializer) { writeAccessPathBase(base) }
        with(exclusionSetSerializer) { writeExclusionSet(exclusions) }
        writeInt(access.size)
        access.forEachAccessorIdx { idx ->
            val accessor = manager.interner.accessor(idx) ?: error("Accessor not found: $idx")
            writeLong(context.getIdByAccessor(accessor))
        }
        writeBoolean(access.isSuffixAbstract)
    }

    private fun DataInputStream.readFact(): DeserializedFact {
        val base = with(AccessPathBaseSerializer) { readAccessPathBase() }
        val exclusions = with(exclusionSetSerializer) { readExclusionSet() }
        val size = readInt()
        val accessors = IntArray(size) {
            val accessor = context.getAccessorById(readLong())
            manager.interner.index(accessor)
        }
        val isAbstract = readBoolean()
        return DeserializedFact(base, exclusions, BaseOnlyAccessOps.build(accessors, isAbstract))
    }

    private class DeserializedFact(
        val base: AccessPathBase,
        val exclusions: ExclusionSet,
        val access: BaseOnlyAccess,
    )
}

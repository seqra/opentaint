package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.util.AccessorIdx
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
        BaseOnlyAccessOps.requireCanonical(access)
        with(AccessPathBaseSerializer) { writeAccessPathBase(base) }
        with(exclusionSetSerializer) { writeExclusionSet(exclusions) }
        writeSlot(access.staticIdx)
        writeSlot(access.fieldIdx)
        writeSlot(access.suffixIdx)
        writeByte(access.valueAccessorState.encoded)
    }

    private fun DataInputStream.readFact(): DeserializedFact {
        val base = with(AccessPathBaseSerializer) { readAccessPathBase() }
        val exclusions = with(exclusionSetSerializer) { readExclusionSet() }
        val staticIdx = readSlot()
        val fieldIdx = readSlot()
        val suffixIdx = readSlot()
        val valueAccessorState = BaseOnlyValueAccessorState.decode(readUnsignedByte())
        val access = BaseOnlyAccessOps.requireCanonical(
            packBaseOnlyAccess(staticIdx, fieldIdx, suffixIdx, valueAccessorState)
        )
        return DeserializedFact(base, exclusions, access)
    }

    private fun DataOutputStream.writeSlot(idx: AccessorIdx) {
        when (idx) {
            NO_ACCESSOR, ABSTRACT_MARK -> writeByte(idx)
            else -> {
                writeByte(ACCESSOR_SLOT)
                val accessor = manager.interner.accessor(idx) ?: error("Accessor not found: $idx")
                writeLong(context.getIdByAccessor(accessor))
            }
        }
    }

    private fun DataInputStream.readSlot(): AccessorIdx = when (val tag = readByte().toInt()) {
        NO_ACCESSOR, ABSTRACT_MARK -> tag
        ACCESSOR_SLOT -> manager.interner.index(context.getAccessorById(readLong()))
        else -> error("Unexpected BaseOnly access slot tag: $tag")
    }

    private class DeserializedFact(
        val base: AccessPathBase,
        val exclusions: ExclusionSet,
        val access: BaseOnlyAccess,
    )

    private companion object {
        const val ACCESSOR_SLOT = 0
    }
}

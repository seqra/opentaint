package org.opentaint.dataflow.ap.ifds.serialization

import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyFieldCleanerEffects
import java.io.DataInputStream
import java.io.DataOutputStream

class AnyFieldCleanerEffectsSerializer(
    private val context: SummarySerializationContext,
) {
    fun DataOutputStream.writeAnyFieldCleanerEffects(effects: AnyFieldCleanerEffects) {
        writeInt(effects.size)
        effects.forEach { writeLong(context.getIdByAccessor(it)) }
    }

    fun DataInputStream.readAnyFieldCleanerEffects(): AnyFieldCleanerEffects {
        var effects = AnyFieldCleanerEffects.Empty
        repeat(readInt()) {
            effects = effects.add(context.getAccessorById(readLong()) as TaintMarkAccessor)
        }
        return effects
    }
}

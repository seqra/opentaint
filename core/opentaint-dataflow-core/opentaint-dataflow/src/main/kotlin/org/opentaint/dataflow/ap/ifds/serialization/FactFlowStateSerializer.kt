package org.opentaint.dataflow.ap.ifds.serialization

import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.DeepCleanEffects
import org.opentaint.dataflow.ap.ifds.access.FactFlowState
import java.io.DataInputStream
import java.io.DataOutputStream

class FactFlowStateSerializer(
    private val context: SummarySerializationContext,
) {
    private val exclusionSerializer = ExclusionSetSerializer(context)

    fun DataOutputStream.writeFactFlowState(flowState: FactFlowState) {
        with(exclusionSerializer) {
            writeExclusionSet(flowState.exclusions)
        }
        writeInt(flowState.deepCleanEffects.size)
        flowState.deepCleanEffects.forEach { writeLong(context.getIdByAccessor(it)) }
    }

    fun DataInputStream.readFactFlowState(): FactFlowState {
        val exclusions = with(exclusionSerializer) { readExclusionSet() }
        var effects = DeepCleanEffects.Empty
        repeat(readInt()) {
            effects = effects.add(context.getAccessorById(readLong()) as TaintMarkAccessor)
        }
        return FactFlowState(exclusions, effects)
    }
}

package org.opentaint.dataflow.ap.ifds.serialization

import org.opentaint.dataflow.ap.ifds.access.FactDemandState
import java.io.DataInputStream
import java.io.DataOutputStream

class FactDemandStateSerializer(
    private val context: SummarySerializationContext,
) {
    private val exclusionSerializer = ExclusionSetSerializer(context)

    fun DataOutputStream.writeFactDemandState(demandState: FactDemandState) {
        with(exclusionSerializer) {
            writeExclusionSet(demandState.exclusions)
        }
    }

    fun DataInputStream.readFactDemandState(): FactDemandState {
        val exclusions = with(exclusionSerializer) { readExclusionSet() }
        return FactDemandState(exclusions)
    }
}

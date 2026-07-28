package org.opentaint.dataflow.ap.ifds.access.automata

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.FactFlowState
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.serialization.AccessPathBaseSerializer
import org.opentaint.dataflow.ap.ifds.serialization.ApSerializer
import org.opentaint.dataflow.ap.ifds.serialization.FactFlowStateSerializer
import org.opentaint.dataflow.ap.ifds.serialization.SummarySerializationContext
import java.io.DataInputStream
import java.io.DataOutputStream

internal class AccessGraphApSerializer(
    manager: AutomataApManager,
    context: SummarySerializationContext
) : ApSerializer {
    private val accessGraphSerializer = AccessGraph.Serializer(manager, context)
    private val flowStateSerializer = FactFlowStateSerializer(context)

    private fun DataOutputStream.writeAp(base: AccessPathBase, access: AccessGraph, flowState: FactFlowState) {
        with (AccessPathBaseSerializer) {
            writeAccessPathBase(base)
        }
        with (flowStateSerializer) {
            writeFactFlowState(flowState)
        }
        with (accessGraphSerializer) {
            writeGraph(access)
        }
    }

    private fun <T> DataInputStream.readAp(builder: (AccessPathBase, AccessGraph, FactFlowState) -> T): T {
        val base = with (AccessPathBaseSerializer) {
            readAccessPathBase()
        }
        val flowState = with (flowStateSerializer) {
            readFactFlowState()
        }
        val access = with (accessGraphSerializer) {
            readGraph()
        }
        return builder(base, access, flowState)
    }

    override fun DataOutputStream.writeFinalAp(ap: FinalFactAp) {
        (ap as AccessGraphFinalFactAp)
        writeAp(ap.base, ap.access, ap.flowState)
    }

    override fun DataOutputStream.writeInitialAp(ap: InitialFactAp) {
        (ap as AccessGraphInitialFactAp)
        writeAp(ap.base, ap.access, ap.flowState)
    }

    override fun DataInputStream.readFinalAp(): FinalFactAp {
        return readAp { base, access, state ->
            AccessGraphFinalFactAp(base, access, state.exclusions, state.deepCleanEffects)
        }
    }

    override fun DataInputStream.readInitialAp(): InitialFactAp {
        return readAp { base, access, state ->
            AccessGraphInitialFactAp(base, access, state.exclusions, state.deepCleanEffects)
        }
    }
}

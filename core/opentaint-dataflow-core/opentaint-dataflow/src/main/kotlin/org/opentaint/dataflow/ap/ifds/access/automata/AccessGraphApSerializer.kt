package org.opentaint.dataflow.ap.ifds.access.automata

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.FactDemandState
import org.opentaint.dataflow.ap.ifds.access.AnyFieldCleanerEffects
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.serialization.AccessPathBaseSerializer
import org.opentaint.dataflow.ap.ifds.serialization.ApSerializer
import org.opentaint.dataflow.ap.ifds.serialization.FactDemandStateSerializer
import org.opentaint.dataflow.ap.ifds.serialization.AnyFieldCleanerEffectsSerializer
import org.opentaint.dataflow.ap.ifds.serialization.SummarySerializationContext
import java.io.DataInputStream
import java.io.DataOutputStream

internal class AccessGraphApSerializer(
    manager: AutomataApManager,
    context: SummarySerializationContext
) : ApSerializer {
    private val accessGraphSerializer = AccessGraph.Serializer(manager, context)
    private val demandStateSerializer = FactDemandStateSerializer(context)
    private val cleanerEffectsSerializer = AnyFieldCleanerEffectsSerializer(context)

    private fun DataOutputStream.writeAp(
        base: AccessPathBase,
        access: AccessGraph,
        demandState: FactDemandState,
        cleanerEffects: AnyFieldCleanerEffects,
    ) {
        with (AccessPathBaseSerializer) {
            writeAccessPathBase(base)
        }
        with (demandStateSerializer) {
            writeFactDemandState(demandState)
        }
        with(cleanerEffectsSerializer) {
            writeAnyFieldCleanerEffects(cleanerEffects)
        }
        with (accessGraphSerializer) {
            writeGraph(access)
        }
    }

    private fun <T> DataInputStream.readAp(
        builder: (AccessPathBase, AccessGraph, FactDemandState, AnyFieldCleanerEffects) -> T,
    ): T {
        val base = with (AccessPathBaseSerializer) {
            readAccessPathBase()
        }
        val demandState = with (demandStateSerializer) {
            readFactDemandState()
        }
        val cleanerEffects = with(cleanerEffectsSerializer) {
            readAnyFieldCleanerEffects()
        }
        val access = with (accessGraphSerializer) {
            readGraph()
        }
        return builder(base, access, demandState, cleanerEffects)
    }

    override fun DataOutputStream.writeFinalAp(ap: FinalFactAp) {
        (ap as AccessGraphFinalFactAp)
        writeAp(ap.base, ap.access, ap.demandState, ap.anyFieldCleanerEffects)
    }

    override fun DataOutputStream.writeInitialAp(ap: InitialFactAp) {
        (ap as AccessGraphInitialFactAp)
        writeAp(ap.base, ap.access, ap.demandState, ap.anyFieldCleanerEffects)
    }

    override fun DataInputStream.readFinalAp(): FinalFactAp {
        return readAp { base, access, state, cleanerEffects ->
            AccessGraphFinalFactAp(base, access, state.exclusions, cleanerEffects)
        }
    }

    override fun DataInputStream.readInitialAp(): InitialFactAp {
        return readAp { base, access, state, cleanerEffects ->
            AccessGraphInitialFactAp(base, access, state.exclusions, cleanerEffects)
        }
    }
}

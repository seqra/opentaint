package org.opentaint.dataflow.ap.ifds.access.automata

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.serialization.AccessPathBaseSerializer
import org.opentaint.dataflow.ap.ifds.serialization.ApSerializer
import org.opentaint.dataflow.ap.ifds.serialization.ExclusionSetSerializer
import org.opentaint.dataflow.ap.ifds.serialization.DeepExclusionsSerializer
import org.opentaint.dataflow.ap.ifds.serialization.SummarySerializationContext
import java.io.DataInputStream
import java.io.DataOutputStream

internal class AccessGraphApSerializer(
    manager: AutomataApManager,
    context: SummarySerializationContext
) : ApSerializer {
    private val accessGraphSerializer = AccessGraph.Serializer(manager, context)
    private val exclusionSerializer = ExclusionSetSerializer(context)
    private val deepExclusionsSerializer = with(manager) {
        DeepExclusionsSerializer(context, { it.idx }, { it.accessor })
    }

    private fun DataOutputStream.writeInitialApFields(
        base: AccessPathBase,
        access: AccessGraph,
        exclusion: ExclusionSet,
    ) {
        with (AccessPathBaseSerializer) {
            writeAccessPathBase(base)
        }
        with (exclusionSerializer) {
            writeExclusionSet(exclusion)
        }
        with (accessGraphSerializer) {
            writeGraph(access)
        }
    }

    private fun <T> DataInputStream.readInitialApFields(
        builder: (AccessPathBase, AccessGraph, ExclusionSet) -> T,
    ): T {
        val base = with (AccessPathBaseSerializer) {
            readAccessPathBase()
        }
        val exclusion = with (exclusionSerializer) {
            readExclusionSet()
        }
        val access = with (accessGraphSerializer) {
            readGraph()
        }
        return builder(base, access, exclusion)
    }

    override fun DataOutputStream.writeFinalAp(ap: FinalFactAp) {
        (ap as AccessGraphFinalFactAp)
        with (AccessPathBaseSerializer) {
            writeAccessPathBase(ap.base)
        }
        with (exclusionSerializer) {
            writeExclusionSet(ap.exclusions)
        }
        with(deepExclusionsSerializer) {
            writeAnyFieldAccessorExclusions(ap.access.deepAccessorExclusion)
        }
        with (accessGraphSerializer) {
            writeGraph(ap.access)
        }
    }

    override fun DataOutputStream.writeInitialAp(ap: InitialFactAp) {
        (ap as AccessGraphInitialFactAp)
        writeInitialApFields(ap.base, ap.access, ap.exclusions)
    }

    override fun DataInputStream.readFinalAp(): FinalFactAp {
        val base = with(AccessPathBaseSerializer) { readAccessPathBase() }
        val exclusions = with(exclusionSerializer) { readExclusionSet() }
        val anyFieldAccessorExclusions = with(deepExclusionsSerializer) {
            readAnyFieldAccessorExclusions()
        }
        val access = with(accessGraphSerializer) { readGraph() }
        return AccessGraphFinalFactAp(
            base,
            access.withAnyFieldAccessorExclusions(anyFieldAccessorExclusions),
            exclusions,
        )
    }

    override fun DataInputStream.readInitialAp(): InitialFactAp {
        return readInitialApFields { base, access, exclusions ->
            AccessGraphInitialFactAp(base, access, exclusions)
        }
    }
}

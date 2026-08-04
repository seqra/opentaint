package org.opentaint.dataflow.ap.ifds.access.cactus

import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.serialization.AccessPathBaseSerializer
import org.opentaint.dataflow.ap.ifds.serialization.ApSerializer
import org.opentaint.dataflow.ap.ifds.serialization.DeepExclusionsSerializer
import org.opentaint.dataflow.ap.ifds.serialization.ExclusionSetSerializer
import org.opentaint.dataflow.ap.ifds.serialization.SummarySerializationContext
import java.io.DataInputStream
import java.io.DataOutputStream

internal class CactusSerializer(
    private val manager: CactusApManager,
    private val context : SummarySerializationContext
) : ApSerializer {
    private val accessNodeSerializer = AccessCactus.AccessNode.Serializer(context)
    private val exclusionSerializer = ExclusionSetSerializer(context)
    private val deepExclusionsSerializer = DeepExclusionsSerializer(
        context,
        { manager.interner.index(it) },
        { manager.interner.accessor(it) ?: error("Accessor not found: $it") },
    )

    override fun DataOutputStream.writeFinalAp(ap: FinalFactAp) {
        (ap as AccessCactus)
        with (AccessPathBaseSerializer) {
            writeAccessPathBase(ap.base)
        }
        with (exclusionSerializer) {
            writeExclusionSet(ap.exclusions)
        }
        with(deepExclusionsSerializer) {
            writeAnyFieldAccessorExclusions(ap.deepAccessorExclusion)
        }
        with (accessNodeSerializer) {
            writeAccessNode(ap.access)
        }
    }

    override fun DataOutputStream.writeInitialAp(ap: InitialFactAp) {
        (ap as AccessPathWithCycles)
        with (AccessPathBaseSerializer) {
            writeAccessPathBase(ap.base)
        }
        with (exclusionSerializer) {
            writeExclusionSet(ap.exclusions)
        }
        val nodes = ap.access?.toList() ?: emptyList()

        writeInt(nodes.size)
        nodes.forEach { (accessor, cycles) ->
            writeLong(context.getIdByAccessor(accessor))
            writeInt(cycles.size)
            cycles.forEach { cycle ->
                writeInt(cycle.size)
                cycle.forEach { accessor ->
                    writeLong(context.getIdByAccessor(accessor))
                }
            }
        }
    }

    override fun DataInputStream.readFinalAp(): FinalFactAp {
        val base = with (AccessPathBaseSerializer) {
            readAccessPathBase()
        }
        val exclusion = with (exclusionSerializer) {
            readExclusionSet()
        }
        val anyFieldAccessorExclusions = with(deepExclusionsSerializer) {
            readAnyFieldAccessorExclusions()
        }
        val access = with (accessNodeSerializer) {
            readAccessNode()
        }
        return AccessCactus(
            manager,
            base,
            access.withAnyFieldAccessorExclusions(anyFieldAccessorExclusions),
            exclusion,
        )
    }

    override fun DataInputStream.readInitialAp(): InitialFactAp {
        val base = with(AccessPathBaseSerializer) {
            readAccessPathBase()
        }
        val exclusion = with (exclusionSerializer) {
            readExclusionSet()
        }
        val nodesSize = readInt()
        val nodeBuilder = AccessPathWithCycles.AccessNode.Builder()
        repeat(nodesSize) {
            val accessor = context.getAccessorById(readLong())
            val cyclesSize = readInt()
            val cycles = List(cyclesSize) {
                val cycleSize = readInt()
                List(cycleSize) {
                    context.getAccessorById(readLong())
                }
            }
            nodeBuilder.append(accessor, cycles)
        }

        val access = nodeBuilder.build()
        return AccessPathWithCycles(base, access, exclusion)
    }
}

package org.opentaint.dataflow.ap.ifds.access.tree.suffix

import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.serialization.ApSerializer
import org.opentaint.dataflow.ap.ifds.serialization.SummarySerializationContext
import java.io.DataInputStream
import java.io.DataOutputStream

class Serializer(
    val context: SummarySerializationContext,
    val manager: TreeSuffixApManager
) : ApSerializer {
    override fun DataOutputStream.writeFinalAp(ap: FinalFactAp) {
        TODO("Not yet implemented")
    }

    override fun DataOutputStream.writeInitialAp(ap: InitialFactAp) {
        TODO("Not yet implemented")
    }

    override fun DataInputStream.readFinalAp(): FinalFactAp {
        TODO("Not yet implemented")
    }

    override fun DataInputStream.readInitialAp(): InitialFactAp {
        TODO("Not yet implemented")
    }
}

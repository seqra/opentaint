package org.opentaint.dataflow.go.analysis.alias

import org.opentaint.dataflow.ap.ifds.analysis.alias.ContextInfo
import org.opentaint.ir.go.api.GoIRFunction

class GoResolvedCallMethod(
    val function: GoIRFunction,
    val graph: GoInstGraph,
    val ctx: ContextInfo,
    val closureValue: GoRefValue?,
)

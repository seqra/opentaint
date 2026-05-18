package org.opentaint.dataflow.go.analysis

import org.opentaint.dataflow.ap.ifds.MethodContext
import org.opentaint.dataflow.ap.ifds.analysis.MethodEntrypointResolver
import org.opentaint.dataflow.go.graph.GoApplicationGraph
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.inst.GoIRInst

class GoMethodEntrypointResolver(private val graph: GoApplicationGraph) : MethodEntrypointResolver {
    override fun resolveEntryPoints(method: CommonMethod, context: MethodContext): List<GoIRInst> {
        return graph.methodGraph(method as GoIRFunction).entryPoints().toList()
    }
}

package org.opentaint.dataflow.go.analysis.alias

import org.opentaint.dataflow.graph.CompactGraph
import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.inst.GoIRInst
import org.opentaint.ir.go.inst.GoIRInstRef
import org.opentaint.ir.go.inst.index
import java.util.BitSet

class GoInstGraph(
    val statements: List<GoIRInst>,
    val graph: CompactGraph,
    val initialIdx: Int,
)

object GoCompactGraphBuilder {
    fun build(function: GoIRFunction): GoInstGraph? {
        val body = function.body ?: return null
        val statements = body.instructions
        if (statements.isEmpty()) return null

        val instGraph = body.instGraph
        val graph = CompactGraph.build(statements.size) { i ->
            val bits = BitSet()
            instGraph.successors(GoIRInstRef(i)).forEach { bits.set(it.index) }
            bits
        }
        val initialIdx = instGraph.entry.index
        return GoInstGraph(statements, graph, initialIdx)
    }
}

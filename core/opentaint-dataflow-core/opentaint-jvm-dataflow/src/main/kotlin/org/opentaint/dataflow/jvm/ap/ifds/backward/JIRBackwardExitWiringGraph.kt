package org.opentaint.dataflow.jvm.ap.ifds.backward

import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.jvm.graph.JMethodExitNormalInst
import org.opentaint.util.analysis.ApplicationGraph
import java.util.BitSet

class JIRBackwardExitWiringGraph(
    private val forward: ApplicationGraph<CommonMethod, CommonInst>,
) : ApplicationGraph<CommonMethod, CommonInst> by forward {

    override fun methodGraph(method: CommonMethod): ApplicationGraph.MethodGraph<CommonMethod, CommonInst> {
        val graph = forward.methodGraph(method)
        val normalExit = graph.exitPoints().firstOrNull { it is JMethodExitNormalInst } ?: return graph

        val exiting = BitSet()
        val unprocessed = ArrayDeque<CommonInst>()
        for (exit in graph.exitPoints()) {
            if (exiting.mark(exit)) unprocessed.addLast(exit)
        }
        while (unprocessed.isNotEmpty()) {
            for (predecessor in graph.predecessors(unprocessed.removeFirst())) {
                if (exiting.mark(predecessor)) unprocessed.addLast(predecessor)
            }
        }

        if (graph.statements().all { exiting.get(it.index) }) return graph
        return ExitWiredMethodGraph(this, graph, normalExit, exiting)
    }

    private class ExitWiredMethodGraph(
        override val applicationGraph: ApplicationGraph<CommonMethod, CommonInst>,
        private val graph: ApplicationGraph.MethodGraph<CommonMethod, CommonInst>,
        private val normalExit: CommonInst,
        private val exiting: BitSet,
    ) : ApplicationGraph.MethodGraph<CommonMethod, CommonInst> by graph {

        override fun successors(node: CommonInst): Sequence<CommonInst> {
            val successors = graph.successors(node)
            if (exiting.get(node.index)) return successors
            return successors + normalExit
        }

        override fun predecessors(node: CommonInst): Sequence<CommonInst> {
            val predecessors = graph.predecessors(node)
            if (node != normalExit) return predecessors
            return predecessors + graph.statements().filter { !exiting.get(it.index) }
        }
    }

    private companion object {
        val CommonInst.index: Int
            get() = (this as JIRInst).location.index

        fun BitSet.mark(inst: CommonInst): Boolean {
            if (get(inst.index)) return false
            set(inst.index)
            return true
        }
    }
}

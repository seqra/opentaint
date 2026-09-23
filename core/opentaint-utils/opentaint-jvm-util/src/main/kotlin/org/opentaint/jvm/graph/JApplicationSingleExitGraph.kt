package org.opentaint.jvm.graph

import org.opentaint.ir.api.jvm.JIRMethod
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.cfg.JIRReturnInst
import org.opentaint.ir.api.jvm.cfg.JIRThrowInst
import org.opentaint.util.analysis.ApplicationGraph

class JApplicationSingleExitGraph(
    private val graph: JApplicationGraph
) : JApplicationGraph by graph {

    class SingleExitMethodGraph(
        override val applicationGraph: JApplicationGraph,
        private val graph: ApplicationGraph.MethodGraph<JIRMethod, JIRInst>,
    ) : ApplicationGraph.MethodGraph<JIRMethod, JIRInst> by graph {

        private val boundary by lazy { MethodBoundary.of(graph.method) }

        override fun entryPoints(): Sequence<JIRInst> {
            val boundary = boundary ?: return graph.entryPoints()
            if (graph.entryPoints().none()) return emptySequence()
            return sequenceOf(boundary.enter)
        }

        override fun exitPoints(): Sequence<JIRInst> {
            val boundary = boundary ?: return graph.exitPoints()
            return sequenceOf(boundary.exitNormal, boundary.exitExceptional)
        }

        override fun successors(node: JIRInst): Sequence<JIRInst> {
            val boundary = boundary ?: return graph.successors(node)
            return when (node) {
                is JMethodEnterInst -> graph.entryPoints()
                is JMethodBoundaryInst -> emptySequence()
                is JIRReturnInst -> graph.successors(node) + boundary.exitNormal
                is JIRThrowInst -> graph.successors(node) + boundary.exitExceptional
                else -> graph.successors(node)
            }
        }

        override fun predecessors(node: JIRInst): Sequence<JIRInst> {
            val boundary = boundary ?: return graph.predecessors(node)
            return when (node) {
                is JMethodEnterInst -> emptySequence()
                is JMethodExitNormalInst -> boundary.returns()
                is JMethodExitExceptionalInst -> boundary.throws()
                else -> {
                    val predecessors = graph.predecessors(node)
                    if (graph.entryPoints().any { it == node }) {
                        predecessors + boundary.enter
                    } else {
                        predecessors
                    }
                }
            }
        }
    }

    override fun methodGraph(method: JIRMethod): ApplicationGraph.MethodGraph<JIRMethod, JIRInst> =
        SingleExitMethodGraph(this, graph.methodGraph(method))

    private class MethodBoundary(
        val enter: JMethodEnterInst,
        val exitNormal: JMethodExitNormalInst,
        val exitExceptional: JMethodExitExceptionalInst,
        private val instructions: List<JIRInst>,
    ) {
        fun returns(): Sequence<JIRInst> = instructions.asSequence().filterIsInstance<JIRReturnInst>()

        fun throws(): Sequence<JIRInst> = instructions.asSequence().filterIsInstance<JIRThrowInst>()

        companion object {
            fun of(method: JIRMethod): MethodBoundary? {
                val instructions = method.instList.instructions
                val size = instructions.size
                val enter = instructions.getOrNull(size - 3) as? JMethodEnterInst ?: return null
                val exitNormal = instructions.getOrNull(size - 2) as? JMethodExitNormalInst ?: return null
                val exitExceptional = instructions.getOrNull(size - 1) as? JMethodExitExceptionalInst ?: return null
                return MethodBoundary(enter, exitNormal, exitExceptional, instructions)
            }
        }
    }
}

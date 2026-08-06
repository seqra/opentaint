package org.opentaint.jvm.sast.dataflow

import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import org.opentaint.ir.api.jvm.JIRMethod
import org.opentaint.ir.api.jvm.cfg.JIRCatchInst
import org.opentaint.ir.api.jvm.cfg.JIRGraph
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.cfg.JIRThrowInst
import org.opentaint.jvm.graph.JApplicationGraph
import org.opentaint.util.analysis.ApplicationGraph
import java.util.BitSet
import kotlin.getValue

class JTryBoundaryExceptionsApplicationGraph(
    private val graph: JApplicationGraph
) : JApplicationGraph by graph {
    class CutMethodGraph(
        override val applicationGraph: JTryBoundaryExceptionsApplicationGraph,
        private val graph: ApplicationGraph.MethodGraph<JIRMethod, JIRInst>
    ) : ApplicationGraph.MethodGraph<JIRMethod, JIRInst> by graph {
        private val catcherIndicesBySource: Int2ObjectOpenHashMap<BitSet> by lazy {
            val flowGraph = graph.method.flowGraph()
            val result = Int2ObjectOpenHashMap<BitSet>()
            graph.statements().filterIsInstance<JIRCatchInst>().forEach { catcher ->
                selectExceptionSources(flowGraph, catcher).forEach { source ->
                    result.computeIfAbsent(source.location.index) { BitSet() }
                        .set(catcher.location.index)
                }
            }
            result
        }

        override fun successors(node: JIRInst): Sequence<JIRInst> {
            val flowGraph = node.location.method.flowGraph()
            val catcherIndices = catcherIndicesBySource[node.location.index]
            val catchers = if (catcherIndices == null) {
                emptySequence()
            } else {
                flowGraph.catchers(node).asSequence().filter { catcherIndices[it.location.index] }
            }
            return flowGraph.successors(node).asSequence() + catchers
        }

        override fun predecessors(node: JIRInst): Sequence<JIRInst> {
            val flowGraph = node.location.method.flowGraph()
            val exceptionSources = if (node is JIRCatchInst) {
                flowGraph.throwers(node).asSequence().filter { source ->
                    catcherIndicesBySource[source.location.index]?.get(node.location.index) == true
                }
            } else {
                emptySequence()
            }
            return flowGraph.predecessors(node).asSequence() + exceptionSources
        }

        private fun selectExceptionSources(flowGraph: JIRGraph, catcher: JIRCatchInst): Set<JIRInst> {
            val protectedStatements = flowGraph.throwers(catcher)
            val tryExits = protectedStatements.filter { statement ->
                flowGraph.successors(statement).any { successor -> successor !in protectedStatements }
            }
            return buildSet {
                protectedStatements.filterTo(this) { it is JIRThrowInst }
                addAll(tryExits)
            }
        }
    }

    override fun methodGraph(method: JIRMethod) = CutMethodGraph(this, graph.methodGraph(method))
}

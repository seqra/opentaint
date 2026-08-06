package org.opentaint.jvm.sast.dataflow

import org.opentaint.ir.api.jvm.JIRMethod
import org.opentaint.ir.api.jvm.cfg.JIRCatchInst
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.cfg.JIRThrowInst
import org.opentaint.jvm.graph.JApplicationGraph
import org.opentaint.util.analysis.ApplicationGraph

class JTryBoundaryExceptionsApplicationGraph(
    private val graph: JApplicationGraph
) : JApplicationGraph by graph {
    class CutMethodGraph(
        override val applicationGraph: JTryBoundaryExceptionsApplicationGraph,
        private val graph: ApplicationGraph.MethodGraph<JIRMethod, JIRInst>
    ) : ApplicationGraph.MethodGraph<JIRMethod, JIRInst> by graph {
        private val flowGraph = graph.method.flowGraph()

        private val exceptionSourcesByCatcher: Map<JIRCatchInst, Set<JIRInst>> by lazy {
            graph.statements()
                .filterIsInstance<JIRCatchInst>()
                .associateWith(::selectExceptionSources)
        }

        private val exceptionCatchersBySource: Map<JIRInst, Set<JIRCatchInst>> by lazy {
            val catchersBySource = hashMapOf<JIRInst, MutableSet<JIRCatchInst>>()
            exceptionSourcesByCatcher.forEach { (catcher, sources) ->
                sources.forEach { source ->
                    catchersBySource.getOrPut(source, ::hashSetOf).add(catcher)
                }
            }
            catchersBySource
        }

        override fun successors(node: JIRInst): Sequence<JIRInst> {
            return (flowGraph.successors(node) + exceptionCatchersBySource[node].orEmpty()).asSequence()
        }

        override fun predecessors(node: JIRInst): Sequence<JIRInst> {
            return (flowGraph.predecessors(node) + exceptionSourcesByCatcher[node].orEmpty()).asSequence()
        }

        private fun selectExceptionSources(catcher: JIRCatchInst): Set<JIRInst> {
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

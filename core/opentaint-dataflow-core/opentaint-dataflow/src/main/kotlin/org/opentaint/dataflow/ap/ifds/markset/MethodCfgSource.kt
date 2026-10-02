package org.opentaint.dataflow.ap.ifds.markset

import it.unimi.dsi.fastutil.ints.IntArrayList
import org.opentaint.dataflow.ap.ifds.LanguageManager
import org.opentaint.dataflow.graph.MethodInstGraph
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.util.analysis.ApplicationGraph

/**
 * The statement graph of every recorded method, read at seal time for option 3* (spec §9). It must
 * be the graph the IFDS engine analyzes the method on, with the engine's statement indices.
 */
interface MethodCfgSource {
    /** The index of [statement] in the graph of its method. */
    fun indexOf(statement: CommonInst): Int

    fun graphOf(method: CommonMethod): MethodGraph

    /**
     * @property stmtCount the statements are `0 until stmtCount`.
     * @property succ the successors of every statement.
     * @property entries the statements the engine starts the method at.
     * @property exits the statements the engine ends the method at.
     */
    class MethodGraph(val stmtCount: Int, val succ: Array<IntArray>, val entries: IntArray, val exits: IntArray)

    companion object {
        private val NO_STATEMENTS = IntArray(0)

        /**
         * The engine's graph: the [MethodInstGraph] of [graph] indexed by [languageManager] (what
         * `JIRAnalysisManager.getMethodInstGraph` builds for every analyzed method), entered at
         * `entryPoints()` (what the engine's `MethodEntrypointResolver` starts at).
         */
        fun of(languageManager: LanguageManager, graph: ApplicationGraph<CommonMethod, CommonInst>): MethodCfgSource =
            object : MethodCfgSource {
                override fun indexOf(statement: CommonInst): Int = languageManager.getInstIndex(statement)

                override fun graphOf(method: CommonMethod): MethodGraph {
                    val instGraph = MethodInstGraph.build(languageManager, graph, method)
                    val count = instGraph.instructions.size
                    val successors = IntArrayList()
                    val succ = Array(count) { s ->
                        successors.clear()
                        instGraph.graph.forEachSuccessor(s) { successors.add(it) }
                        if (successors.isEmpty) NO_STATEMENTS else successors.toIntArray()
                    }
                    val entries = graph.methodGraph(method).entryPoints()
                        .map { languageManager.getInstIndex(it) }.distinct().toList().toIntArray()
                    val exits = instGraph.exitPoints.stream().toArray()
                    return MethodGraph(count, succ, entries, exits)
                }
            }
    }
}

/** The statement graph cannot be built for the recorded program; option 3* fails open. */
class MethodCfgUnavailable(message: String) : RuntimeException(message)

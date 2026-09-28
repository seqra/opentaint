package org.opentaint.dataflow.jvm.ap.ifds.backward

import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.util.analysis.ApplicationGraph
import java.util.concurrent.ConcurrentHashMap

class JIRBackwardNonExitingStarts {
    private val starts = ConcurrentHashMap<CommonMethod, List<CommonInst>>()

    fun resolve(forward: ApplicationGraph.MethodGraph<CommonMethod, CommonInst>): List<CommonInst> =
        starts.computeIfAbsent(forward.method) { bottomComponentRepresentatives(forward) }

    fun isNonExitingStart(method: CommonMethod, statement: CommonInst): Boolean =
        starts[method]?.contains(statement) == true

    private fun bottomComponentRepresentatives(
        graph: ApplicationGraph.MethodGraph<CommonMethod, CommonInst>,
    ): List<CommonInst> {
        val reachable = closure(graph.entryPoints(), graph::successors)
        val exiting = closure(graph.exitPoints(), graph::predecessors)
        val region = reachable.filterTo(linkedSetOf()) { it !in exiting }
        if (region.isEmpty()) return emptyList()

        val component = hashMapOf<CommonInst, Int>()
        val components = mutableListOf<List<CommonInst>>()
        for (root in finishOrder(region, graph).asReversed()) {
            if (root in component) continue

            val members = mutableListOf(root)
            component[root] = components.size
            var next = 0
            while (next < members.size) {
                for (predecessor in graph.predecessors(members[next++])) {
                    if (predecessor in region && predecessor !in component) {
                        component[predecessor] = components.size
                        members += predecessor
                    }
                }
            }
            components += members
        }

        return components
            .filter { members -> members.all { s -> graph.successors(s).all { component[it] == component[s] } } }
            .map { it.first() }
    }

    private fun finishOrder(
        region: Set<CommonInst>,
        graph: ApplicationGraph.MethodGraph<CommonMethod, CommonInst>,
    ): List<CommonInst> {
        val order = mutableListOf<CommonInst>()
        val visited = hashSetOf<CommonInst>()
        val stack = ArrayDeque<Pair<CommonInst, Iterator<CommonInst>>>()

        for (root in region) {
            if (!visited.add(root)) continue
            stack.addLast(root to graph.successors(root).iterator())

            while (stack.isNotEmpty()) {
                val (node, successors) = stack.last()
                val successor = successors.asSequence().firstOrNull { it in region && visited.add(it) }
                if (successor == null) {
                    stack.removeLast()
                    order += node
                } else {
                    stack.addLast(successor to graph.successors(successor).iterator())
                }
            }
        }
        return order
    }

    private fun closure(
        roots: Sequence<CommonInst>,
        next: (CommonInst) -> Sequence<CommonInst>,
    ): Set<CommonInst> {
        val result = roots.toCollection(linkedSetOf())
        val queue = ArrayDeque(result)
        while (queue.isNotEmpty()) {
            for (s in next(queue.removeFirst())) {
                if (result.add(s)) queue.addLast(s)
            }
        }
        return result
    }
}

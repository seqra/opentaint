package org.opentaint.dataflow.graph

import org.opentaint.dataflow.util.Cancellation
import java.util.ArrayDeque
import java.util.BitSet

/** Instruction-only metadata. A kill certifies a committed overwrite on every successor. */
class LocalAccess(uses: BitSet, definiteDefinitions: BitSet, mentions: BitSet) {
    internal val uses = uses.clone() as BitSet
    internal val definitions = definiteDefinitions.clone() as BitSet
    internal val mentions = mentions.clone() as BitSet
}

/** Immutable boundary-only result. No instruction, fact, rule or alias provider is retained. */
class BlockLiveLocals private constructor(
    private val forwardTargets: Map<Int, BitSet>,
    private val backwardTargets: Map<Int, BitSet>,
) {
    val retainedMasks: Int get() = forwardTargets.size + backwardTargets.size
    val retainedWords: Long get() = (forwardTargets.values + backwardTargets.values).sumOf { it.size().toLong() / 64 }
    fun mayFollow(backward: Boolean, route: MethodBlockRoute, local: Int): Boolean =
        mayEnter(backward, route.to, local)

    fun mayEnter(backward: Boolean, target: Int, local: Int): Boolean =
        (if (backward) backwardTargets else forwardTargets)[target]?.get(local) ?: true

    companion object {
        fun build(layout: MethodBlockLayout, forward: CompactGraph, backward: CompactGraph,
                  access: List<LocalAccess>, cancellation: Cancellation): BlockLiveLocals {
            require(access.size == forward.size && backward.size == forward.size)
            fun solve(graph: CompactGraph, reverse: Boolean): Map<Int, BitSet> {
                val live = Array(graph.size) { BitSet() }
                val queue = ArrayDeque<Int>()
                val queued = BitSet(graph.size)
                for (s in 0 until graph.size) { queue += s; queued.set(s) }
                while (queue.isNotEmpty()) {
                    cancellation.checkpoint()
                    val s = queue.removeFirst(); queued.clear(s)
                    val next = (if (reverse) access[s].mentions else access[s].uses).clone() as BitSet
                    graph.forEachSuccessor(s) { to ->
                        val carry = live[to].clone() as BitSet
                        if (!reverse) carry.andNot(access[s].definitions)
                        next.or(carry)
                    }
                    if (next != live[s]) {
                        live[s] = next
                        graph.forEachPredecessor(s) { predecessor ->
                            if (!queued[predecessor]) { queued.set(predecessor); queue += predecessor }
                        }
                    }
                }
                // Empty regions and logical method starts can forward to an
                // original endpoint. Retain targets of all actual boundary
                // routes plus original graph starts/ends, not the solver.
                val targets = BitSet(graph.size)
                val directed = layout.directed(graph, reverse)
                for (from in 0 until graph.size) graph.forEachSuccessor(from) { to ->
                    if (directed.route(from, to).crossesBoundary || directed.route(from, to).discovery)
                        targets.set(to)
                }
                for (node in 0 until graph.size)
                    if (graph.predecessors[node] == CompactGraph.EMPTY || graph.successors[node] == CompactGraph.EMPTY)
                        targets.set(node)
                val result = LinkedHashMap<Int, BitSet>()
                var target = targets.nextSetBit(0)
                while (target >= 0) {
                    result[target] = live[target]
                    target = targets.nextSetBit(target + 1)
                }
                return result
            }
            return BlockLiveLocals(solve(forward, false), solve(backward, true))
        }
    }
}

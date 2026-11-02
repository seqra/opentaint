package org.opentaint.dataflow.graph

import it.unimi.dsi.fastutil.ints.Int2IntOpenHashMap
import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import it.unimi.dsi.fastutil.ints.IntArrayList
import org.opentaint.dataflow.util.forEach
import org.opentaint.dataflow.util.printer.PrintableGraph
import org.opentaint.dataflow.util.toBitSet
import org.opentaint.dataflow.util.toSet
import java.util.BitSet
import java.util.ArrayDeque

class IntGraph {
    private val successors = Int2ObjectOpenHashMap<BitSet>()

    fun addEdge(from: Int, to: Int) {
        var current = successors.get(from)
        if (current == null) {
            current = BitSet().also { successors.put(from, it) }
        }
        current.set(to)
    }

    fun nonTrivialSccs(): List<BitSet> {
        val allSccs = allSccs()
        return allSccs.filter { component ->
            if (component.cardinality() > 1) return@filter true

            val element = component.nextSetBit(0)
            val elementSuccessors = successors[element]
            elementSuccessors != null && elementSuccessors.get(element)
        }
    }

    private fun allNodes(): BitSet{
        val allNodes = successors.keys.toBitSet()
        successors.values.forEach { allNodes.or(it) }
        return allNodes
    }

    fun allSccs(): List<BitSet> {
        val allNodes = allNodes()

        var index = 0
        val nodeIndex = Int2IntOpenHashMap().apply { defaultReturnValue(NO_VALUE) }
        val nodeLowLink = Int2IntOpenHashMap().apply { defaultReturnValue(NO_VALUE) }
        val onStack = BitSet()
        val stack = IntArrayList()
        val result = mutableListOf<BitSet>()

        // Keep Tarjan's visit and component order, but put suspended DFS calls
        // on an explicit stack. A long CFG must not consume the JVM call stack.
        class Frame(val vertex: Int, val edges: BitSet?) {
            var next: Int = edges?.nextSetBit(0) ?: -1
        }
        val dfs = ArrayDeque<Frame>()

        fun enter(v: Int) {
            nodeIndex[v] = index
            nodeLowLink[v] = index
            index++
            stack.add(v)
            onStack.set(v)
            dfs.addLast(Frame(v, successors[v]))
        }

        allNodes.forEach { root ->
            if (nodeIndex[root] != NO_VALUE) return@forEach
            enter(root)
            while (dfs.isNotEmpty()) {
                val frame = dfs.peekLast()
                val v = frame.vertex
                val w = frame.next
                if (w >= 0) {
                    frame.next = frame.edges!!.nextSetBit(w + 1)
                    if (nodeIndex[w] == NO_VALUE) {
                        enter(w)
                    } else if (onStack[w]) {
                        nodeLowLink[v] = minOf(nodeLowLink[v], nodeIndex[w])
                    }
                    continue
                }

                dfs.removeLast()
                if (nodeLowLink[v] == nodeIndex[v]) {
                    val component = BitSet()
                    do {
                        val member = stack.removeInt(stack.lastIndex)
                        onStack.clear(member)
                        component.set(member)
                    } while (member != v)
                    result.add(component)
                }
                if (dfs.isNotEmpty()) {
                    val parent = dfs.peekLast().vertex
                    nodeLowLink[parent] = minOf(nodeLowLink[parent], nodeLowLink[v])
                }
            }
        }

        return result
    }

    @Suppress("unused")
    fun print() = Printable()

    inner class Printable: PrintableGraph<Int, Unit>{
        override fun allNodes(): List<Int> = this@IntGraph.allNodes().toSet().toList()
        override fun nodeLabel(node: Int): String = "$node"

        override fun successors(node: Int): List<Pair<Unit, Int>> =
            successors[node]?.toSet()?.map { Unit to it }.orEmpty()

        override fun edgeLabel(edge: Unit): String = ""
    }

    companion object {
        private const val NO_VALUE = -1
    }
}

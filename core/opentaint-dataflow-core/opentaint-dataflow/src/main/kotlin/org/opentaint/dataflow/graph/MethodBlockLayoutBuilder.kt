package org.opentaint.dataflow.graph

import java.util.ArrayDeque
import java.util.BitSet
import java.util.PriorityQueue

/** Build a stable BL/L/AL hierarchy without changing an instruction or CFG edge. */
object MethodBlockLayoutBuilder {
    fun build(graph: CompactGraph, entryPoints: Collection<Int> = emptyList()): MethodBlockLayout {
        val ports = ArrayList<MethodBlockPort>()
        val edgePorts = HashMap<Long, PortId>()
        for (from in 0 until graph.size) graph.forEachSuccessor(from) { to ->
            val port = MethodBlockPort(PortId(ports.size), from, to)
            ports += port
            edgePorts[MethodBlockLayout.edgeKey(from, to)] = port.id
        }
        val starts = BitSet(graph.size)
        for (entry in entryPoints) {
            require(entry in 0 until graph.size)
            starts.set(entry)
        }
        if (entryPoints.isEmpty()) for (index in 0 until graph.size)
            if (graph.predecessors[index] == CompactGraph.EMPTY) starts.set(index)

        val disabled = BitSet(ports.size)
        val root = Draft(MethodBlockKind.SEQUENTIAL)
        val pending = ArrayDeque<BuildWork>()
        pending.addLast(BuildWork(root, BitSet(graph.size).apply { set(0, graph.size) }))
        while (pending.isNotEmpty()) {
            val (target, vertices) = pending.removeLast()
            val components = orderedComponents(graph, vertices, edgePorts, disabled)
            val loopIndex = components.indexOfFirst { component -> isCyclic(graph, component, edgePorts, disabled) }
            if (loopIndex < 0) {
                target.instructions = vertices.toIndices()
                continue
            }
            val loopVertices = components[loopIndex]
            val beforeVertices = BitSet(graph.size)
            for (index in 0 until loopIndex) beforeVertices.or(components[index])
            val afterVertices = BitSet(graph.size)
            for (index in loopIndex + 1 until components.size) afterVertices.or(components[index])
            val headers = BitSet(graph.size)
            loopVertices.forEachIndex { vertex ->
                if (starts[vertex]) headers.set(vertex)
                graph.forEachPredecessor(vertex) { predecessor ->
                    val edge = edgePorts.getValue(MethodBlockLayout.edgeKey(predecessor, vertex))
                    if ((!loopVertices[predecessor] || disabled[edge.ordinal]) && vertices[vertex]) headers.set(vertex)
                }
            }
            if (headers.isEmpty) headers.set(loopVertices.nextSetBit(0))
            val repeat = ArrayList<PortId>()
            loopVertices.forEachIndex { from -> graph.forEachSuccessor(from) { to ->
                if (loopVertices[to] && headers[to]) {
                    val edge = edgePorts.getValue(MethodBlockLayout.edgeKey(from, to))
                    if (!disabled[edge.ordinal]) {
                        disabled.set(edge.ordinal)
                        repeat += edge
                    }
                }
            } }
            check(repeat.isNotEmpty()) { "A cyclic SCC must have a feedback edge into a header" }
            val before = Draft(MethodBlockKind.SEQUENTIAL)
            val loop = Draft(MethodBlockKind.LOOP, headers = headers.toIndices(), repeat = repeat)
            val after = Draft(MethodBlockKind.SEQUENTIAL)
            target.children = listOf(before, loop, after)
            pending.addLast(BuildWork(after, afterVertices))
            pending.addLast(BuildWork(loop, loopVertices))
            pending.addLast(BuildWork(before, beforeVertices))
        }
        val layout = freeze(root, graph.size, ports, edgePorts)
        validate(layout, graph)
        return layout
    }

    fun build(graph: MethodInstGraph, entryPoints: Collection<Int> = emptyList()): MethodBlockLayout =
        build(graph.graph, entryPoints)

    /** Validate unique ownership, compact preorder containment and exact routes. */
    fun validate(layout: MethodBlockLayout, graph: CompactGraph) {
        check(layout.instructionCount == graph.size)
        val seen = BitSet(graph.size)
        for (block in layout.blocks) {
            check(block.id.ordinal in layout.blocks.indices)
            check(block.parent == null || block.parent.ordinal < block.id.ordinal)
            for ((localIndex, instruction) in block.instructions.withIndex()) {
                check(!seen[instruction]) { "Instruction $instruction has two owners" }
                seen.set(instruction)
                check(layout.ownerOf(instruction) == block.id)
                check(layout.localIndex(instruction) == localIndex)
            }
            if (!block.isLeaf) check(block.children.size == 3)
            for (child in block.children) {
                check(layout[child].parent == block.id)
                check(layout[child].depth == block.depth + 1)
                check(layout.isAncestor(block.id, child))
            }
            for (repeat in block.repeatPorts) {
                check(block.isLoop)
                val port = layout.ports[repeat.ordinal]
                check(layout.contains(block.id, port.from) && layout.contains(block.id, port.to))
                check(port.to in block.headers)
                check(layout.route(port.from, port.to).feedbackLoop == block.id)
            }
        }
        check(seen.cardinality() == graph.size) { "Unowned instruction" }
        var edges = 0
        for (from in 0 until graph.size) graph.forEachSuccessor(from) { to ->
            val route = layout.route(from, to)
            check(route.from == from && route.to == to)
            check(route.fromBlock == layout.ownerOf(from) && route.toBlock == layout.ownerOf(to))
            val reversed = layout.route(to, from, backward = true)
            check(reversed.port == route.port && reversed.feedbackLoop == route.feedbackLoop)
            edges++
        }
        check(edges == layout.ports.size)
        // Every remaining physical owner-local edge must have an acyclic rank.
        val indegree = IntArray(graph.size)
        for (port in layout.ports) if (layout.route(port.from, port.to).feedbackLoop == null) indegree[port.to]++
        val ready = ArrayDeque<Int>()
        for (index in 0 until graph.size) if (indegree[index] == 0) ready.addLast(index)
        var visited = 0
        while (ready.isNotEmpty()) {
            val from = ready.removeFirst()
            visited++
            graph.forEachSuccessor(from) { to ->
                if (layout.route(from, to).feedbackLoop == null && --indegree[to] == 0) ready.addLast(to)
            }
        }
        check(visited == graph.size) { "Non-feedback layout retains a cycle" }
    }

    private class Draft(
        val kind: MethodBlockKind,
        val headers: List<Int> = emptyList(),
        val repeat: List<PortId> = emptyList(),
    ) {
        var instructions: List<Int> = emptyList()
        var children: List<Draft> = emptyList()
        var id: BlockId = BlockId.ROOT
        var parent: BlockId? = null
        var depth: Int = 0
        var end: Int = 0
    }

    private data class BuildWork(val target: Draft, val vertices: BitSet)

    private fun freeze(root: Draft, size: Int, ports: List<MethodBlockPort>,
                       edgePorts: Map<Long, PortId>): MethodBlockLayout {
        val preorder = ArrayList<Draft>()
        val stack = ArrayDeque<Pair<Draft, Boolean>>()
        stack.addLast(root to false)
        while (stack.isNotEmpty()) {
            val (node, finishing) = stack.removeLast()
            if (finishing) { node.end = preorder.size; continue }
            node.id = BlockId(preorder.size)
            preorder += node
            stack.addLast(node to true)
            for (child in node.children.asReversed()) {
                child.parent = node.id
                child.depth = node.depth + 1
                stack.addLast(child to false)
            }
        }
        val owners = IntArray(size) { -1 }
        val local = IntArray(size) { -1 }
        val feedback = HashMap<PortId, BlockId>()
        val blocks = preorder.map { node ->
            for ((index, inst) in node.instructions.withIndex()) {
                check(owners[inst] == -1)
                owners[inst] = node.id.ordinal
                local[inst] = index
            }
            for (port in node.repeat) check(feedback.put(port, node.id) == null)
            MethodBlock(node.id, node.parent, node.depth, node.kind,
                node.children.getOrNull(0)?.id, node.children.getOrNull(1)?.id,
                node.children.getOrNull(2)?.id, node.end, node.instructions,
                node.headers, node.repeat)
        }
        return MethodBlockLayout(blocks, ports, owners, local, edgePorts, feedback)
    }

    private fun isCyclic(graph: CompactGraph, component: BitSet,
                         edgePorts: Map<Long, PortId>, disabled: BitSet): Boolean {
        if (component.cardinality() > 1) return true
        val vertex = component.nextSetBit(0)
        var self = false
        graph.forEachSuccessor(vertex) { to ->
            if (to == vertex && !disabled[edgePorts.getValue(MethodBlockLayout.edgeKey(vertex, to)).ordinal]) self = true
        }
        return self
    }

    private fun orderedComponents(graph: CompactGraph, vertices: BitSet,
                                  edgePorts: Map<Long, PortId>, disabled: BitSet): List<BitSet> {
        if (vertices.isEmpty) return emptyList()
        val intGraph = IntGraph()
        vertices.forEachIndex { from -> graph.forEachSuccessor(from) { to ->
            if (vertices[to] && !disabled[edgePorts.getValue(MethodBlockLayout.edgeKey(from, to)).ordinal])
                intGraph.addEdge(from, to)
        } }
        val components = intGraph.allSccs().toMutableList()
        val indexed = BitSet(graph.size)
        for (component in components) indexed.or(component)
        vertices.forEachIndex { if (!indexed[it]) components += BitSet(graph.size).apply { set(it) } }
        val componentOf = IntArray(graph.size) { -1 }
        for ((index, component) in components.withIndex()) component.forEachIndex { componentOf[it] = index }
        val outgoing = Array(components.size) { BitSet(components.size) }
        val indegree = IntArray(components.size)
        vertices.forEachIndex { from -> graph.forEachSuccessor(from) { to ->
            if (vertices[to] && !disabled[edgePorts.getValue(MethodBlockLayout.edgeKey(from, to)).ordinal]) {
                val a = componentOf[from]
                val b = componentOf[to]
                if (a != b && !outgoing[a][b]) { outgoing[a].set(b); indegree[b]++ }
            }
        } }
        val ready = PriorityQueue<Int>(compareBy { components[it].nextSetBit(0) })
        for (index in components.indices) if (indegree[index] == 0) ready += index
        val result = ArrayList<BitSet>(components.size)
        while (ready.isNotEmpty()) {
            val index = ready.remove()
            result += components[index]
            outgoing[index].forEachIndex { if (--indegree[it] == 0) ready += it }
        }
        check(result.size == components.size) { "SCC condensation must be acyclic" }
        return result
    }

    private fun BitSet.toIndices(): List<Int> = buildList { forEachIndex { add(it) } }
    private inline fun BitSet.forEachIndex(body: (Int) -> Unit) {
        var index = nextSetBit(0)
        while (index >= 0) { body(index); index = nextSetBit(index + 1) }
    }
}

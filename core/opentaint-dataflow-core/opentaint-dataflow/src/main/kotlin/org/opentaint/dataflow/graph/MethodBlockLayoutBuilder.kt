package org.opentaint.dataflow.graph

import java.util.ArrayDeque
import java.util.BitSet
import java.util.PriorityQueue

/** Build a stable BL/L/AL hierarchy without changing an instruction or CFG edge. */
object MethodBlockLayoutBuilder {
    fun build(graph: CompactGraph, entryPoints: Collection<Int> = emptyList(),
              exceptionalExits: Collection<Int> = emptyList(),
              normalExits: Collection<Int>? = null): MethodBlockLayout {
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

        val exceptional = BitSet(graph.size).apply { for (exit in exceptionalExits) set(exit) }
        val normal = normalExits?.let { exits -> BitSet(graph.size).apply { for (exit in exits) set(exit) } }
        val disabled = BitSet(ports.size)
        val root = Draft(MethodBlockKind.SEQUENTIAL)
        val pending = ArrayDeque<BuildWork>()
        pending.addLast(BuildWork(root, BitSet(graph.size).apply { set(0, graph.size) }))
        while (pending.isNotEmpty()) {
            val (target, vertices, ancestorHeaders) = pending.removeLast()
            val components = orderedComponents(graph, vertices, edgePorts, disabled)
            val loopIndex = components.indexOfFirst { component -> isCyclic(graph, component, edgePorts, disabled) }
            if (loopIndex < 0) {
                target.instructions = vertices.toIndices()
                continue
            }
            val core = components[loopIndex]
            val expansion = expandNormalTails(graph, vertices, components, loopIndex, edgePorts, disabled, exceptional, normal, ancestorHeaders)
            val loopVertices = expansion.vertices
            val beforeVertices = BitSet(graph.size)
            for (index in 0 until loopIndex) beforeVertices.or(components[index])
            val afterVertices = BitSet(graph.size)
            for (index in loopIndex + 1 until components.size) afterVertices.or(components[index])
            afterVertices.andNot(loopVertices)
            val headers = BitSet(graph.size)
            core.forEachIndex { vertex ->
                if (starts[vertex]) headers.set(vertex)
                graph.forEachPredecessor(vertex) { predecessor ->
                    val edge = edgePorts.getValue(MethodBlockLayout.edgeKey(predecessor, vertex))
                    if ((!core[predecessor] || disabled[edge.ordinal]) && vertices[vertex]) headers.set(vertex)
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
            val loop = Draft(MethodBlockKind.LOOP, headers = headers.toIndices(), repeat = repeat,
                normalJoin = expansion.join, gap = expansion.gap)
            val after = Draft(MethodBlockKind.SEQUENTIAL)
            target.children = listOf(before, loop, after)
            pending.addLast(BuildWork(after, afterVertices, ancestorHeaders))
            pending.addLast(BuildWork(loop, loopVertices, ancestorHeaders + headers.toIndices()))
            pending.addLast(BuildWork(before, beforeVertices, ancestorHeaders))
        }
        val layout = freeze(root, graph.size, ports, edgePorts)
        validate(layout, graph)
        return layout
    }

    fun build(graph: MethodInstGraph, entryPoints: Collection<Int> = emptyList(),
              exceptionalExits: Collection<Int> = emptyList(), normalExits: Collection<Int>? = null): MethodBlockLayout =
        build(graph.graph, entryPoints, exceptionalExits, normalExits)

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
        for (normal in layout.normalExits) {
            check(normal.id.ordinal >= layout.ports.size)
            check(layout[normal.loop].isLoop && !layout.contains(normal.loop, normal.target))
            val parent = checkNotNull(layout[normal.loop].parent)
            val local = layout.contains(parent, normal.target)
            for (physical in normal.routes) {
                val port = layout.ports[physical.ordinal]
                check(layout.contains(normal.loop, port.from) && port.to == normal.target)
                val repeat = layout.route(port.from, port.to).feedbackLoop
                check(repeat != normal.loop) { "A loop's own repeat is not its normal exit" }
                if (!local) check(repeat != null && layout.isAncestor(repeat, normal.loop) &&
                    normal.target in layout[repeat].headers) { "An external join keeps its actual enclosing feedback boundary" }
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
        val normalJoin: Int? = null,
        val gap: List<Int> = emptyList(),
    ) {
        var instructions: List<Int> = emptyList()
        var children: List<Draft> = emptyList()
        var id: BlockId = BlockId.ROOT
        var parent: BlockId? = null
        var depth: Int = 0
        var end: Int = 0
    }

    private data class BuildWork(val target: Draft, val vertices: BitSet, val ancestorHeaders: List<Int> = emptyList())

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
        val normalExits = ArrayList<MethodBlockNormalExit>()
        val gaps = ArrayList<MethodBlockNormalExitGap>()
        for (node in preorder) if (node.kind == MethodBlockKind.LOOP) {
            if (node.gap.isNotEmpty()) gaps += MethodBlockNormalExitGap(node.id, node.headers, node.gap)
            val join = node.normalJoin ?: continue
            val outlets = ports.filter { port ->
                val owner = owners[port.from]
                owner in node.id.ordinal until node.end && port.to == join && feedback[port.id] != node.id
            }.map { it.id }
            if (outlets.isNotEmpty()) normalExits += MethodBlockNormalExit(
                PortId(ports.size + normalExits.size), node.id, join, outlets)
        }
        return MethodBlockLayout(blocks, ports, owners, local, edgePorts, feedback, normalExits, gaps)
    }

    private data class NormalExpansion(val vertices: BitSet, val join: Int?, val gap: List<Int> = emptyList())

    /** Postdominance on the condensation DAG ignores paths which cannot return.
     * The selected loop keeps those divergent tails, with their own nested SCCs.
     * Throw-only tails stay typed outlets. No physical edge is added or removed.
     */
    private fun expandNormalTails(graph: CompactGraph, vertices: BitSet, components: List<BitSet>,
                                  selected: Int, edgePorts: Map<Long, PortId>, disabled: BitSet,
                                  exceptional: BitSet, declaredNormal: BitSet?, ancestorHeaders: List<Int>): NormalExpansion {
        val count = components.size
        val of = IntArray(graph.size) { -1 }
        for ((index, component) in components.withIndex()) component.forEachIndex { of[it] = index }
        val next = Array(count) { BitSet(count) }
        val normalSink = BooleanArray(count)
        val exceptionalSink = BooleanArray(count)
        for ((index, component) in components.withIndex()) component.forEachIndex { from ->
            if (exceptional[from]) exceptionalSink[index] = true
            if (declaredNormal?.get(from) ?: (graph.successors[from] == CompactGraph.EMPTY && !exceptional[from]))
                normalSink[index] = true
            graph.forEachSuccessor(from) { to ->
                val port = edgePorts.getValue(MethodBlockLayout.edgeKey(from, to))
                if (!vertices[to]) {
                    // A labelled break/return to an ancestor is a typed outlet,
                    // not this region's ordinary loop-to-local-AL interface.
                    if (exceptional[to]) exceptionalSink[index] = true
                } else if (disabled[port.ordinal]) {
                    // The last real node before an inherited repeat is a
                    // possible local continuation; never alias the repeat edge.
                    if (exceptional[to]) exceptionalSink[index] = true else normalSink[index] = true
                } else if (of[to] != index) next[index].set(of[to])
            }
        }
        val normal = BooleanArray(count)
        val throws = BooleanArray(count)
        val diverges = BooleanArray(count)
        for (index in count - 1 downTo 0) {
            normal[index] = normalSink[index]
            throws[index] = exceptionalSink[index]
            diverges[index] = isCyclic(graph, components[index], edgePorts, disabled)
            next[index].forEachIndex { to ->
                normal[index] = normal[index] || normal[to]
                throws[index] = throws[index] || throws[to]
                diverges[index] = diverges[index] || diverges[to]
            }
        }
        val postdom = IntArray(count + 1) { count }
        fun common(a: Int, b: Int): Int {
            var left = a
            var right = b
            while (left != right) {
                if (left < right) left = postdom[left] else right = postdom[right]
            }
            return left
        }
        for (index in count - 1 downTo 0) if (normal[index]) {
            var parent: Int? = if (normalSink[index]) count else null
            next[index].forEachIndex { to -> if (normal[to]) parent = parent?.let { common(it, to) } ?: to }
            postdom[index] = parent ?: count
        }
        fun before(join: Int): BitSet {
            val included = BitSet(count)
            val work = ArrayDeque<Int>()
            work.addLast(selected)
            while (work.isNotEmpty()) {
                val index = work.removeFirst()
                if (index == join || included[index]) continue
                // A path which only throws remains an exceptional outlet.
                if (index != selected && !normal[index] && throws[index] && !diverges[index]) continue
                included.set(index)
                next[index].forEachIndex { work.addLast(it) }
            }
            return included
        }
        fun externalHeader(included: BitSet): NormalExpansion? {
            if (ancestorHeaders.isEmpty()) return null
            val body = BitSet(graph.size)
            included.forEachIndex { body.or(components[it]) }
            val targets = BitSet(graph.size)
            var compatible = true
            body.forEachIndex { from ->
                if (declaredNormal?.get(from) ?: (graph.successors[from] == CompactGraph.EMPTY && !exceptional[from]))
                    compatible = false
                graph.forEachSuccessor(from) { to ->
                    val port = edgePorts.getValue(MethodBlockLayout.edgeKey(from, to))
                    if (disabled[port.ordinal] || !vertices[to] && to in ancestorHeaders) {
                        if (to in ancestorHeaders && !body[to]) targets.set(to)
                        else if (!exceptional[to]) compatible = false
                    }
                }
            }
            return if (compatible && targets.cardinality() == 1)
                NormalExpansion(body, targets.nextSetBit(0)) else null
        }
        if (!normal[selected]) {
            val included = before(count)
            externalHeader(included)?.let { return it }
            val body = BitSet(graph.size)
            included.forEachIndex { body.or(components[it]) }
            return NormalExpansion(body, null)
        }
        var candidate = postdom[selected]
        while (candidate < count) {
            val included = before(candidate)
            val arrivals = BitSet(graph.size)
            included.forEachIndex { index -> components[index].forEachIndex { from ->
                graph.forEachSuccessor(from) { to ->
                    if (of[to] == candidate && !disabled[edgePorts.getValue(MethodBlockLayout.edgeKey(from, to)).ordinal])
                        arrivals.set(to)
                }
            } }
            if (arrivals.cardinality() == 1) {
                val body = BitSet(graph.size)
                included.forEachIndex { body.or(components[it]) }
                return NormalExpansion(body, arrivals.nextSetBit(0))
            }
            candidate = postdom[candidate]
        }
        externalHeader(before(count))?.let { return it }
        val outlets = BitSet(graph.size)
        components[selected].forEachIndex { from -> graph.forEachSuccessor(from) { to ->
            if (!components[selected][to] && !exceptional[to]) outlets.set(to)
        } }
        return NormalExpansion(components[selected], null, outlets.toIndices())
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

package org.opentaint.dataflow.graph

import java.util.Collections

/** Stable method-local identities. They do not participate in AP or rule equality. */
@JvmInline
value class BlockId(val ordinal: Int) {
    companion object { val ROOT = BlockId(0) }
}

@JvmInline
value class PortId(val ordinal: Int) {
    companion object {
        val ROOT_ENTRY = PortId(-1)
        val ROOT_EXIT = PortId(-2)
    }
}

enum class MethodBlockKind { SEQUENTIAL, LOOP }

/** A CFG edge is between the transfer at [from] and the transfer at [to]. */
data class MethodBlockPort(val id: PortId, val from: Int, val to: Int)

/**
 * One node in the containment tree. Composite nodes own child-result points, not
 * copies of the original instruction points. A LOOP can itself have BL/L/AL
 * children when its single traversal contains another loop.
 */
class MethodBlock internal constructor(
    val id: BlockId,
    val parent: BlockId?,
    val depth: Int,
    val kind: MethodBlockKind,
    val before: BlockId?,
    val loop: BlockId?,
    val after: BlockId?,
    internal val subtreeEnd: Int,
    instructions: List<Int>,
    headers: List<Int>,
    repeatPorts: List<PortId>,
) {
    val instructions: List<Int> = Collections.unmodifiableList(instructions.toList())
    val headers: List<Int> = Collections.unmodifiableList(headers.toList())
    val repeatPorts: List<PortId> = Collections.unmodifiableList(repeatPorts.toList())
    val children: List<BlockId> = Collections.unmodifiableList(listOfNotNull(before, loop, after))
    val isLeaf: Boolean get() = before == null
    val isLoop: Boolean get() = kind == MethodBlockKind.LOOP
}

/**
 * A compact routing certificate. [feedbackLoop] denotes the existing edge cut
 * to finish one traversal, even when both ends have the same lowest owner.
 * Ancestor paths are derived on demand instead of copied into every edge.
 */
data class MethodBlockRoute(
    val port: PortId,
    val from: Int,
    val to: Int,
    val fromBlock: BlockId,
    val toBlock: BlockId,
    val commonAncestor: BlockId,
    val feedbackLoop: BlockId?,
    val discovery: Boolean = false,
) {
    val crossesBoundary: Boolean get() = fromBlock != toBlock || feedbackLoop != null
}

/** Immutable, direction-independent topology, shared by every run of one form. */
class MethodBlockLayout internal constructor(
    blocks: List<MethodBlock>,
    ports: List<MethodBlockPort>,
    private val owners: IntArray,
    private val localIndices: IntArray,
    private val edgePorts: Map<Long, PortId>,
    private val feedback: Map<PortId, BlockId>,
) {
    val blocks: List<MethodBlock> = Collections.unmodifiableList(blocks.toList())
    val ports: List<MethodBlockPort> = Collections.unmodifiableList(ports.toList())
    val root: BlockId get() = BlockId.ROOT
    val instructionCount: Int get() = owners.size
    val hasLoops: Boolean = blocks.any { it.isLoop }

    operator fun get(id: BlockId): MethodBlock = blocks[id.ordinal]
    fun ownerOf(instruction: Int): BlockId = BlockId(owners[instruction])
    fun localIndex(instruction: Int): Int = localIndices[instruction]
    fun pointCount(block: BlockId): Int = get(block).instructions.size
    fun contains(block: BlockId, instruction: Int): Boolean = isAncestor(block, ownerOf(instruction))
    fun isAncestor(ancestor: BlockId, descendant: BlockId): Boolean =
        descendant.ordinal in ancestor.ordinal until get(ancestor).subtreeEnd

    /** Region iteration does not retain a quadratic array of descendant members. */
    fun instructions(block: BlockId): Sequence<Int> = sequence {
        for (index in block.ordinal until get(block).subtreeEnd)
            yieldAll(blocks[index].instructions)
    }

    fun port(from: Int, to: Int): MethodBlockPort? =
        edgePorts[edgeKey(from, to)]?.let { ports[it.ordinal] }

    fun route(from: Int, to: Int, backward: Boolean = false): MethodBlockRoute {
        val physical = if (backward) port(to, from) else port(from, to)
        require(physical != null) { "No physical CFG edge $from -> $to (backward=$backward)" }
        return route(physical.id, from, to, feedback[physical.id], discovery = false)
    }

    /**
     * Read the backend's actual directed graph. Backward discovery edges are
     * additional typed routes; they never alter the physical forward graph.
     */
    fun directed(graph: CompactGraph, backward: Boolean): DirectedMethodBlockLayout {
        require(graph.size == instructionCount)
        val routes = HashMap<Long, MethodBlockRoute>()
        var nextPort = ports.size
        for (from in 0 until graph.size) graph.forEachSuccessor(from) { to ->
            val physical = if (backward) port(to, from) else port(from, to)
            if (physical == null) {
                require(backward) { "Forward layout has an unknown CFG edge $from -> $to" }
                routes[edgeKey(from, to)] = route(PortId(nextPort++), from, to, null, discovery = true)
            } else {
                routes[edgeKey(from, to)] = route(physical.id, from, to, feedback[physical.id], discovery = false)
            }
        }
        // The overlay may add discovery, but cannot erase an ordinary edge.
        for (port in ports) {
            val key = if (backward) edgeKey(port.to, port.from) else edgeKey(port.from, port.to)
            require(routes.containsKey(key)) { "Directed graph lost physical CFG edge $port" }
        }
        return DirectedMethodBlockLayout(this, backward, routes)
    }

    fun commonAncestor(a: BlockId, b: BlockId): BlockId {
        var left = a
        var right = b
        while (get(left).depth > get(right).depth) left = get(left).parent!!
        while (get(right).depth > get(left).depth) right = get(right).parent!!
        while (left != right) {
            left = get(left).parent!!
            right = get(right).parent!!
        }
        return left
    }

    /** Lowest owner first; a repeat includes the loop whose traversal ends. */
    fun exitedBlocks(route: MethodBlockRoute): Sequence<BlockId> = sequence {
        val stop = route.feedbackLoop ?: route.commonAncestor
        var current = route.fromBlock
        while (current != stop) {
            yield(current)
            current = get(current).parent!!
        }
        if (route.feedbackLoop != null) yield(stop)
    }

    /** Outer boundary first. A repeat re-enters its existing loop state. */
    fun enteredBlocks(route: MethodBlockRoute): List<BlockId> {
        val stop = route.feedbackLoop ?: route.commonAncestor
        val reversed = ArrayList<BlockId>()
        var current = route.toBlock
        while (current != stop) {
            reversed += current
            current = get(current).parent!!
        }
        if (route.feedbackLoop != null) reversed += stop
        reversed.reverse()
        return reversed
    }

    private fun route(port: PortId, from: Int, to: Int, loop: BlockId?, discovery: Boolean): MethodBlockRoute {
        val source = ownerOf(from)
        val destination = ownerOf(to)
        return MethodBlockRoute(port, from, to, source, destination,
            commonAncestor(source, destination), loop, discovery)
    }

    companion object {
        internal fun edgeKey(from: Int, to: Int): Long = (from.toLong() shl 32) or (to.toLong() and 0xffffffffL)
    }
}

class DirectedMethodBlockLayout internal constructor(
    val layout: MethodBlockLayout,
    val backward: Boolean,
    private val routes: Map<Long, MethodBlockRoute>,
) {
    fun route(from: Int, to: Int): MethodBlockRoute =
        routes[MethodBlockLayout.edgeKey(from, to)] ?: error("No directed CFG edge $from -> $to")
}

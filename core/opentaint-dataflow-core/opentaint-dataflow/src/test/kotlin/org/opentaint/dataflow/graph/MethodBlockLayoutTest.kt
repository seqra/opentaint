package org.opentaint.dataflow.graph

import java.util.BitSet
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertFailsWith
import kotlin.test.assertNotEquals
import kotlin.test.assertTrue

class MethodBlockLayoutTest {
    private fun graph(size: Int, vararg edges: Pair<Int, Int>): CompactGraph = CompactGraph.build(size) { from ->
        BitSet(size).apply { edges.forEach { if (it.first == from) set(it.second) } }
    }

    @Test fun `acyclic method and isolated exits retain the single root fast path`() {
        val layout = MethodBlockLayoutBuilder.build(graph(5, 0 to 1, 1 to 2), listOf(0))
        assertFalse(layout.hasLoops)
        assertEquals(1, layout.blocks.size)
        assertEquals((0..4).toList(), layout[BlockId.ROOT].instructions)
        for (inst in 0..4) {
            assertEquals(BlockId.ROOT, layout.ownerOf(inst))
            assertEquals(inst, layout.localIndex(inst))
        }
        assertFalse(layout.route(0, 1).crossesBoundary)
    }

    @Test fun `successive loops decompose through the complete recursive AL`() {
        val g = graph(8, 0 to 1, 1 to 2, 2 to 1, 1 to 3,
            3 to 4, 4 to 3, 3 to 5, 5 to 6)
        val layout = MethodBlockLayoutBuilder.build(g, listOf(0))
        val root = layout[layout.root]
        assertEquals(listOf(0), layout[root.before!!].instructions)
        val loop1 = layout[root.loop!!]
        val al1 = layout[root.after!!]
        assertTrue(loop1.isLoop)
        assertEquals(listOf(1, 2), loop1.instructions)
        assertTrue(layout[al1.before!!].instructions.isEmpty())
        assertEquals(listOf(3, 4), layout[al1.loop!!].instructions)
        assertTrue(layout.isAncestor(root.after!!, layout.ownerOf(3)))
        assertFalse(layout.isAncestor(root.loop!!, layout.ownerOf(3)))
        val repeat = layout.route(2, 1)
        assertEquals(loop1.id, repeat.feedbackLoop)
        assertEquals(listOf(loop1.id), layout.exitedBlocks(repeat).toList())
        assertEquals(listOf(loop1.id), layout.enteredBlocks(repeat))
        val between = layout.route(1, 3)
        assertEquals(listOf(loop1.id), layout.exitedBlocks(between).toList())
        assertEquals(listOf(al1.id, al1.loop!!), layout.enteredBlocks(between))
        assertEquals(listOf(3, 4, 5, 6, 7), layout.instructions(al1.id).sorted().toList())
    }

    @Test fun `acyclic break tails remain in the loop traversal before one normal join`() {
        // while (...) { if (a) { sourceP(); break; } else { sourceQ(); break; } }
        // The cyclic core is only {1,7}; both acyclic branch tails belong to
        // this complete traversal, and meet at the one actual continuation 6.
        val g = graph(9, 0 to 1, 1 to 2, 1 to 4, 1 to 7, 7 to 1,
            2 to 3, 3 to 6, 4 to 5, 5 to 6)
        val layout = MethodBlockLayoutBuilder.build(g, listOf(0))
        val root = layout[layout.root]
        val loop = layout[checkNotNull(root.loop)]
        for (tail in listOf(2, 3, 4, 5)) assertTrue(layout.contains(loop.id, tail),
            "The complete loop traversal must contain acyclic break tail $tail")
        assertFalse(layout.contains(loop.id, 6), "The common continuation belongs to AL")
        assertTrue(layout.contains(checkNotNull(root.after), 6))
        assertEquals(loop.id, layout.route(7, 1).feedbackLoop)
        assertEquals(null, layout.route(3, 6).feedbackLoop)
        assertEquals(null, layout.route(5, 6).feedbackLoop)
        assertNotEquals(layout.route(3, 6).port, layout.route(5, 6).port,
            "Canonical normal interfaces must retain both original CFG routes")
    }

    @Test fun `nested loops belong below an outer loop iteration`() {
        val g = graph(7, 0 to 1, 1 to 2, 2 to 3, 3 to 2, 2 to 4, 4 to 1, 1 to 5)
        val layout = MethodBlockLayoutBuilder.build(g, listOf(0))
        val outer = layout[layout[layout.root].loop!!]
        assertFalse(outer.isLeaf)
        val inner = layout[outer.loop!!]
        assertTrue(inner.isLoop)
        assertTrue(layout.isAncestor(outer.id, inner.id))
        assertEquals(listOf(2, 3), inner.instructions)
        assertEquals(outer.id, layout.route(4, 1).feedbackLoop)
        assertEquals(inner.id, layout.route(3, 2).feedbackLoop)
        assertNotEquals(layout.route(4, 1).port, layout.route(3, 2).port)
    }

    @Test fun `nested break to an ancestor stays typed and ordinary normal interfaces are unique`() {
        // outer: while (...) { while (...) { if (stop()) break outer; } afterInner(); }
        val g = graph(9, 0 to 1, 1 to 2, 1 to 6, 2 to 3, 3 to 2,
            2 to 4, 4 to 1, 2 to 6, 6 to 7)
        val layout = MethodBlockLayoutBuilder.build(g, listOf(0), listOf(8), listOf(7))
        val outer = layout[checkNotNull(layout[layout.root].loop)]
        val inner = layout[checkNotNull(outer.loop)]
        assertTrue(layout.normalExitGaps.isEmpty(), layout.normalExitGaps.toString())
        assertEquals(4, layout.normalExits.single { it.loop == inner.id }.target)
        assertEquals(6, layout.normalExits.single { it.loop == outer.id }.target)
        assertEquals(layout.normalExits.flatMap { it.routes }.size,
            layout.normalExits.flatMap { it.routes }.distinct().size)
        val ancestorBreak = layout.route(2, 6)
        assertEquals(outer.id, layout.normalExitForRoute(ancestorBreak.port)?.loop)
        assertEquals(outer.id, layout.route(4, 1).feedbackLoop)
        assertEquals(null, layout.normalExitForRoute(layout.route(4, 1).port),
            "An inherited repeat stays a feedback port, not a normal interface")
    }

    @Test fun `inner continue outer tails share their actual enclosing header without merging outer feedback`() {
        // outer: while (a()) {
        //   while (b()) { if (c()) continue outer; }
        //   afterInner();
        // }
        val g = graph(10, 0 to 1, 1 to 2, 1 to 8, 2 to 3, 3 to 2,
            2 to 4, 4 to 6, 2 to 5, 5 to 1, 6 to 1)
        val layout = MethodBlockLayoutBuilder.build(g, listOf(0), listOf(9), listOf(8))
        val outer = layout[checkNotNull(layout[layout.root].loop)]
        val inner = layout[checkNotNull(outer.loop)]
        assertTrue(layout.normalExitGaps.isEmpty(), layout.normalExitGaps.toString())
        for (tail in listOf(4, 5, 6)) assertTrue(layout.contains(inner.id, tail))
        assertFalse(layout.contains(inner.id, 1), "The enclosing header remains outside the inner traversal")
        val normal = layout.normalExits.single { it.loop == inner.id }
        assertEquals(1, normal.target)
        val outerRepeats = setOf(layout.port(5, 1)!!.id, layout.port(6, 1)!!.id)
        assertEquals(outerRepeats, normal.routes.toSet())
        for (port in outerRepeats) {
            val physical = layout.ports[port.ordinal]
            assertEquals(outer.id, layout.route(physical.from, physical.to).feedbackLoop,
                "A normal inner completion retains its original outer feedback role")
        }
        assertEquals(inner.id, layout.route(3, 2).feedbackLoop)
        assertFalse(layout.port(3, 2)!!.id in normal.routes)
        assertTrue(layout[checkNotNull(outer.after)].instructions.isEmpty(),
            "All local normal leave tails end at the already existing enclosing boundary")
    }

    @Test fun `self loop and irreducible multi entry retain all physical ports`() {
        val self = MethodBlockLayoutBuilder.build(graph(2, 0 to 0, 0 to 1), listOf(0))
        val selfLoop = self[self[self.root].loop!!]
        assertEquals(listOf(0), selfLoop.headers)
        assertEquals(selfLoop.id, self.route(0, 0).feedbackLoop)
        val g = graph(5, 0 to 1, 0 to 2, 1 to 2, 2 to 1, 1 to 3, 2 to 4)
        val layout = MethodBlockLayoutBuilder.build(g, listOf(0))
        val loop = layout[layout[layout.root].loop!!]
        assertEquals(listOf(1, 2), loop.headers)
        assertNotEquals(layout.route(0, 1).port, layout.route(0, 2).port)
        assertEquals(loop.id, layout.route(1, 2).feedbackLoop)
        assertEquals(loop.id, layout.route(2, 1).feedbackLoop)
        assertEquals(2, loop.repeatPorts.size)
        assertTrue(layout.normalExitGaps.isNotEmpty(),
            "Untyped distinct terminal continuations must be reported explicitly")
    }

    @Test fun `bypass break return throw and handler edges retain exact endpoints`() {
        val g = graph(9, 0 to 1, 0 to 5, 1 to 2, 2 to 1, 1 to 3,
            2 to 4, 2 to 6, 4 to 7, 6 to 7, 3 to 8, 5 to 8)
        val layout = MethodBlockLayoutBuilder.build(g, listOf(0))
        val directed = layout.directed(g, backward = false)
        val reversed = CompactGraph.build(g.size) { from ->
            BitSet(g.size).apply { g.forEachPredecessor(from) { set(it) } }
        }
        val backward = layout.directed(reversed, backward = true)
        for (from in 0 until g.size) g.forEachSuccessor(from) { to ->
            val route = directed.route(from, to)
            val back = backward.route(to, from)
            assertEquals(from, route.from)
            assertEquals(to, route.to)
            assertEquals(route.port, back.port)
            assertEquals(route.fromBlock, back.toBlock)
            assertEquals(route.toBlock, back.fromBlock)
            assertEquals(route.feedbackLoop, back.feedbackLoop)
        }
        assertNotEquals(layout.route(2, 4).port, layout.route(2, 6).port)
        assertNotEquals(layout.route(2, 6).port, layout.route(1, 3).port)
    }

    @Test fun `backward exceptional discovery is an overlay and invents no forward leave`() {
        // Neither normal exit 3 nor exceptional exit 4 is forward-reachable.
        val g = graph(5, 0 to 1, 1 to 2, 2 to 1)
        val layout = MethodBlockLayoutBuilder.build(g, listOf(0))
        val back = CompactGraph.build(5) { from ->
            BitSet(5).apply {
                g.forEachPredecessor(from) { set(it) }
                if (from == 4) { set(0); set(1); set(2) }
            }
        }
        val view = layout.directed(back, backward = true)
        assertTrue(view.route(4, 2).discovery)
        assertTrue(view.route(4, 0).discovery)
        assertFalse(view.route(1, 2).discovery)
        assertEquals(3, layout.ports.size)
        assertEquals(null, layout.port(2, 3))
        assertFailsWith<IllegalArgumentException> { layout.route(2, 3) }
        assertFailsWith<IllegalArgumentException> { layout.directed(back, backward = false) }
    }

    @Test fun `layout and port IDs are deterministic and deep AL has no recursive build stack`() {
        val count = 250
        val edges = buildList {
            for (index in 0 until count) {
                val header = 2 * index
                add(header to header + 1)
                add(header + 1 to header)
                if (index + 1 < count) add(header to header + 2)
            }
        }
        val g = graph(2 * count, *edges.toTypedArray())
        val a = MethodBlockLayoutBuilder.build(g, listOf(0))
        val b = MethodBlockLayoutBuilder.build(g, listOf(0))
        assertEquals(count, a.blocks.count { it.isLoop })
        assertEquals(a.blocks.map { it.parent to it.instructions }, b.blocks.map { it.parent to it.instructions })
        assertEquals(a.ports, b.ports)
        assertTrue(a.blocks.maxOf { it.depth } >= count)
    }
}

package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.store.BlockScope
import org.opentaint.dataflow.graph.*
import org.opentaint.dataflow.util.Cancellation
import java.util.BitSet
import kotlin.test.*

class PreparedBlockExitsTest {
    private fun bits(values: List<Int>) = BitSet().apply { values.forEach(::set) }
    private fun graph(next: List<List<Int>>) = CompactGraph.build(next.size) { bits(next[it]) }
    private fun access(uses: List<Int> = emptyList(), defs: List<Int> = emptyList()) =
        LocalAccess(bits(uses), bits(defs), bits(uses + defs))
    private fun routes(layout: MethodBlockLayout, graph: CompactGraph, backward: Boolean): Map<PortId, MethodBlockRoute> {
        val directed = layout.directed(graph, backward)
        return buildMap { for (from in 0 until graph.size) graph.forEachSuccessor(from) { to ->
            val route = directed.route(from, to); put(route.port, route)
        } }
    }

    @Test fun `prepared routes equal the native predicate and keep repeat only local`() {
        val next = listOf(listOf(1),listOf(2,3),listOf(3),listOf(1,4),listOf(5),emptyList())
        val forward = graph(next)
        val backward = graph(next.indices.map { to -> next.indices.filter { to in next[it] } })
        val layout = MethodBlockLayoutBuilder.build(forward, listOf(0), normalExits = listOf(5))
        val live = BlockLiveLocals.build(layout, forward, backward,
            listOf(access(),access(),access(listOf(0),listOf(1)),access(listOf(1)),access(),access()), Cancellation())
        for (reverse in listOf(false,true)) {
            val directed = routes(layout, if (reverse) backward else forward, reverse)
            val directory = PreparedExitDirectory(layout,directed,reverse,live,setOf(5),0)
            val loop = layout.blocks.single { it.isLoop }
            val scope = BlockScope(loop.id, loop.repeatPorts.first())
            for ((id, route) in directed) for (local in 0..2) {
                val prepared = directory.getOrPrepare(scope,id,AccessPathBase.LocalVar(local))
                val expected = route.to == 0 || route.to == 5 || live.mayFollow(reverse,route,local)
                assertEquals(expected, prepared is PreparedExit.Routes, "$reverse $route local=$local")
                if (prepared is PreparedExit.Routes) assertEquals(listOf(route),prepared.routes)
                assertSame(prepared,directory.getOrPrepare(scope,id,AccessPathBase.LocalVar(local)))
            }
            for (normal in layout.normalExits) {
                val prepared = directory.getOrPrepare(scope,normal.id,AccessPathBase.Return) as PreparedExit.Routes
                assertEquals(normal.routes.map { directed.getValue(it) }, prepared.routes,
                    "Canonical normal interfaces keep every certified physical route")
            }
            if (!reverse) {
                assertTrue(directory.getOrPrepare(scope,layout.port(3,1)!!.id,AccessPathBase.LocalVar(1)) is PreparedExit.Routes)
                assertSame(PreparedExit.DeadData,directory.getOrPrepare(scope,layout.port(3,4)!!.id,AccessPathBase.LocalVar(1)))
            }
        }
    }

    @Test fun `logical empty entry has prepared membership without freezing actual starts`() {
        val next=listOf(listOf(1,2),listOf(0),listOf(3),emptyList())
        val forward=graph(next);val backward=graph(next.indices.map { to -> next.indices.filter { to in next[it] } })
        val layout=MethodBlockLayoutBuilder.build(forward,listOf(0),normalExits=listOf(3))
        val live=BlockLiveLocals.build(layout,forward,backward,
            listOf(access(),access(listOf(0)),access(),access()),Cancellation())
        val empty=layout.blocks.first { it.isLeaf && !it.isLoop && it.instructions.isEmpty() }
        val directory=PreparedExitDirectory(layout,routes(layout,forward,false),false,live,setOf(3),0)
        val scope=BlockScope(empty.id,PortId.ROOT_ENTRY)
        val prepared=directory.getOrPrepare(scope,PortId.ROOT_ENTRY,AccessPathBase.LocalVar(0)) as PreparedExit.ActualStarts
        val actualStarts=linkedSetOf(0)
        assertEquals(listOf(0),actualStarts.filter(prepared::allows))
        actualStarts+=2
        actualStarts+=3
        assertEquals(listOf(0,3),actualStarts.filter(prepared::allows),"Reachability can grow; dead targets stay excluded")
        assertEquals(1L,directory.targetMaskBuilds)
        assertSame(prepared,directory.getOrPrepare(scope,PortId.ROOT_ENTRY,AccessPathBase.LocalVar(0)))
    }

    @Test fun `typed method exits and missing masks retain native dispatch`() {
        val forward=graph(listOf(listOf(1),listOf(1,2),emptyList()))
        val layout=MethodBlockLayoutBuilder.build(forward,listOf(0),normalExits=listOf(2))
        val scope=BlockScope(layout.blocks.single { it.isLoop }.id,PortId.ROOT_ENTRY)
        val directory=PreparedExitDirectory(layout,routes(layout,forward,false),false,null,setOf(2),0)
        for (exit in listOf(PortId.ROOT_ENTRY,PortId.ROOT_EXIT,PortId(-4),PortId.STATIC_SHORTCUT))
            assertEquals(exit,(directory.getOrPrepare(scope,exit,AccessPathBase.LocalVar(99)) as PreparedExit.Terminal).exit)
        val physical=layout.ports.first().id
        assertTrue(directory.getOrPrepare(scope,physical,AccessPathBase.LocalVar(99)) is PreparedExit.Routes)
    }
}

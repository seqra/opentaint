package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.graph.*
import org.opentaint.dataflow.util.Cancellation
import java.util.BitSet
import kotlin.test.*

class BlockLiveLocalsTest {
    private fun bits(values: List<Int>) = BitSet().apply { values.forEach(::set) }
    private fun access(uses: List<Int> = emptyList(), defs: List<Int> = emptyList()) =
        LocalAccess(bits(uses),bits(defs),bits(uses+defs))
    private fun graph(next: List<List<Int>>) = CompactGraph.build(next.size) { bits(next[it]) }

    @Test fun `nonreturning feedback kills old copy destination but retains source`() {
        val next=listOf(listOf(1),listOf(2),listOf(1),emptyList())
        val forward=graph(next)
        val backward=graph(next.indices.map { to -> next.indices.filter { to in next[it] } })
        val layout=MethodBlockLayoutBuilder.build(forward,listOf(0),normalExits=listOf(3))
        val live=BlockLiveLocals.build(layout,forward,backward,
            listOf(access(),access(listOf(0),listOf(1)),access(listOf(1)),access()),Cancellation())
        val repeat=layout.route(2,1)
        assertTrue(live.mayFollow(false,repeat,0))
        assertFalse(live.mayFollow(false,repeat,1))
        val reversed=layout.route(1,2,backward=true)
        assertTrue(live.mayFollow(true,reversed,0))
        assertTrue(live.mayFollow(true,reversed,1),"Backward must include assignment lhs definitions")
        assertTrue(live.mayEnter(false,999,1),"Unknown synthetic targets keep native handling")
    }

    @Test fun `conditional definition cannot erase carried local and leave differs from repeat`() {
        val next=listOf(listOf(1),listOf(2,3),listOf(3),listOf(1,4),listOf(5),emptyList())
        val forward=graph(next); val backward=graph(next.indices.map { to -> next.indices.filter { to in next[it] } })
        val layout=MethodBlockLayoutBuilder.build(forward,listOf(0),normalExits=listOf(5))
        val live=BlockLiveLocals.build(layout,forward,backward,
            listOf(access(),access(),access(listOf(0),listOf(1)),access(listOf(1)),access(),access()),Cancellation())
        assertTrue(live.mayFollow(false,layout.route(3,1),1))
        assertFalse(live.mayFollow(false,layout.route(3,4),1))
    }

    @Test fun `read before write and uncertified overwrite preserve old value`() {
        val next=listOf(listOf(1),listOf(2),listOf(1,3),emptyList())
        val forward=graph(next); val backward=graph(next.indices.map { to -> next.indices.filter { to in next[it] } })
        val layout=MethodBlockLayoutBuilder.build(forward,listOf(0),normalExits=listOf(3))
        val selfRead=BlockLiveLocals.build(layout,forward,backward,
            listOf(access(),access(listOf(1),listOf(1)),access(),access()),Cancellation())
        assertTrue(selfRead.mayFollow(false,layout.route(2,1),1))
        val possibleThrow=BlockLiveLocals.build(layout,forward,backward,
            listOf(access(),access(listOf(0)),access(listOf(1)),access()),Cancellation())
        assertTrue(possibleThrow.mayFollow(false,layout.route(2,1),1))
    }
}

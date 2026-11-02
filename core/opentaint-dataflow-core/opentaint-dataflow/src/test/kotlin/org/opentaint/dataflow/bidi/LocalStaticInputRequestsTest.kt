package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.BlockScope
import org.opentaint.dataflow.graph.BlockId
import org.opentaint.dataflow.graph.PortId
import kotlin.test.*

class LocalStaticInputRequestsTest {
    private val f = StoreFixtures()
    private val ap = f.manager
    private val ops = f.ops
    private val mode = ApMode(true, Direction.FORWARD, 1)
    private val x = AccessPathBase.Argument(0)
    private val clazz = ap.accessors.index(ClassStaticAccessor("C"))
    private val field = f.field("staticField")
    private val left = f.field("left")
    private val right = f.field("right")
    private val t = f.mark("T")
    private val u = f.mark("U")
    private val initial = ap.initial(f.pattern(STATIC, listOf(clazz, field), Tail.STAR, MarkSlot.STAR))
    private val link = LocalLink(BlockScope(BlockId(1), PortId(2)), PortId(3), initial, Layer.DEMAND,
        BlockScope(BlockId(4), PortId(3)))
    private data class Answer(val link: LocalLink, val original: PremiseKey, val value: Facts)

    private inner class Harness {
        var ticket = 10L
        val interests = ArrayList<StaticInterest>()
        val answers = ArrayList<Answer>()
        var after: (() -> Unit)? = null
        val requests = LocalStaticInputRequests(ops, mode, f.method, { ++ticket }, interests::add) { link, p, value ->
            answers += Answer(link, p, value)
            after?.invoke()
        }
        fun answer(id: Long, mark: TaintMark): Boolean = requests.answer(
            StaticOwnerEffect.PointReady(f.method, id,
                RegionGroups(f.pattern(STATIC, listOf(clazz, field), Tail.STAR, MarkSlot.STAR), MarkSet.of(mark))))
    }

    private fun input(path: List<Int> = emptyList()): FlowTree =
        f.fact(x, path, Tail.STAR, MarkSlot.STAR, layer = Layer.DEMAND) as FlowTree

    @Test fun `the first mark request in a child resumes the boundary with its concrete static origin`() {
        val h = Harness()
        h.requests.request(link, input(), t)
        val interest = h.interests.single()
        assertEquals(initial.toPattern(), interest.region)
        assertEquals(MarkSet.of(t), interest.wanted)
        assertTrue(h.answers.isEmpty())
        assertTrue(h.answer(interest.id, t))
        val answer = h.answers.single()
        assertEquals(STATIC, answer.original.member(0).base)
        assertEquals(MarkSlot.Concrete(t), answer.original.member(0).mark)
        assertEquals(link.child, answer.link.child)
        assertEquals(link.point, answer.link.point)
        assertSame(answer.original, answer.link.original)
        assertEquals(f.pattern(x, tail = Tail.STAR, mark = MarkSlot.Concrete(t)), ops.leaves(answer.value).single())
        assertEquals(Layer.DEMAND, answer.value.layer)
    }

    @Test fun `pending image unions keep all paths and do not subscribe twice for one mark`() {
        val h = Harness()
        h.requests.request(link, input(listOf(left)), t)
        h.requests.request(link, input(listOf(right)), t)
        h.requests.request(link, input(listOf(left)), u)
        assertEquals(2, h.interests.size)
        assertEquals(h.interests[0].id, h.interests[1].id)
        assertTrue(h.answer(h.interests[0].id, t))
        assertEquals(setOf(listOf(left), listOf(right)), h.answers.map { ops.leaves(it.value).single().fact.path }.toSet())
        assertTrue(h.answer(h.interests[1].id, u))
        assertEquals(listOf(left), ops.leaves(h.answers.last().value).single().fact.path)
    }

    @Test fun `an answered row detaches before a reentrant request`() {
        val h = Harness()
        h.requests.request(link, input(), t)
        val first = h.interests.single().id
        h.after = { h.after = null; h.requests.request(link, input(listOf(left)), t) }
        assertTrue(h.answer(first, t))
        val next = h.interests.last().id
        assertNotEquals(first, next)
        assertTrue(h.answer(next, t))
        assertEquals(2, h.answers.size)
        assertFalse(h.answer(first, t), "A consumed ticket is no longer retained")
    }

    @Test fun `unknown physical tickets and non point effects stay with the physical directory`() {
        val h = Harness()
        assertFalse(h.answer(999, t))
        assertFalse(h.requests.answer(StaticOwnerEffect.ReadReady(f.method, 999, initial.toPattern())))
        h.requests.request(link, input(), t)
        h.requests.clear()
        assertFalse(h.answer(h.interests.single().id, t))
    }
}

package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.BlockScope
import org.opentaint.dataflow.graph.BlockId
import org.opentaint.dataflow.graph.PortId
import org.opentaint.dataflow.util.Cancellation
import kotlin.test.*

class StaticBoundaryInputRequestsTest {
    private val f = StoreFixtures()
    private val ap = f.manager
    private val ops = f.ops
    private val mode = ApMode(true, Direction.FORWARD, 1)
    private val clazz = ap.accessors.index(ClassStaticAccessor("C"))
    private val from = listOf(clazz, f.field("f"))
    private val secondFrom = listOf(clazz, f.field("f2"))
    private val target = listOf(clazz, f.field("g"))
    private val other = listOf(clazz, f.field("h"))
    private val t = f.mark("T")
    private val u = f.mark("U")
    private val cf = flowInitial(from)
    private val cf2 = flowInitial(secondFrom)
    private val cg = flowInitial(target)
    private val outer = BlockScope(BlockId(1), PortId.ROOT_EXIT)
    private val middle = BlockScope(BlockId(2), PortId.ROOT_EXIT)
    private val leaf = BlockScope(BlockId(3), PortId.ROOT_EXIT)

    private fun flowInitial(path: List<Int>): InitialAp =
        ap.initial(f.pattern(STATIC, path, Tail.STAR, MarkSlot.STAR))

    private fun flow(path: List<Int> = target): FlowTree =
        f.fact(STATIC, path, Tail.STAR, MarkSlot.STAR, layer = Layer.DEMAND) as FlowTree

    private fun link(parent: BlockScope, child: BlockScope, original: InitialAp = cg,
                     point: PortId = PortId.ROOT_EXIT): LocalLink =
        LocalLink(parent, point, original, Layer.DEMAND, child)

    private data class Delivery(val link: LocalLink, val matched: FlowTree, val mark: TaintMark)

    private inner class Harness(selectedMode: ApMode = mode) {
        val rootLink = link(BlockScope.ROOT, outer, cf)
        val rows = linkedMapOf(
            leaf to mutableListOf<Pair<LocalLink, Facts>>(link(middle, leaf) to flow()),
            middle to mutableListOf<Pair<LocalLink, Facts>>(link(outer, middle) to flow()),
            outer to mutableListOf<Pair<LocalLink, Facts>>(rootLink to flow()),
        )
        val borrowed = ArrayList<BlockScope>()
        val delivered = ArrayList<Delivery>()
        var beforeBorrow: ((BlockScope) -> Unit)? = null
        val requests = StaticBoundaryInputRequests(ops, selectedMode, { scope, visit ->
            borrowed += scope
            beforeBorrow?.invoke(scope)
            for ((input, value) in rows[scope].orEmpty().toList()) visit(input, value)
        }) { input, value, mark -> delivered += Delivery(input, value, mark) }
    }

    @Test fun `a real Cg request follows only identity continuations and preserves the root Cf relation`() {
        val h = Harness()
        h.requests.request(leaf, cg, t)
        assertEquals(listOf(leaf, middle, outer), h.borrowed)
        val delivered = h.delivered.single()
        assertSame(h.rootLink, delivered.link)
        assertSame(cf, delivered.link.original)
        assertEquals(t, delivered.mark)
        assertEquals(f.pattern(STATIC, target, Tail.STAR, MarkSlot.STAR), ops.leaves(delivered.matched).single())
        assertEquals(Layer.DEMAND, delivered.matched.layer)
    }

    @Test fun `the existing root path also receives an ordinary nonstatic FLOW origin`() {
        val h = Harness()
        val argument = ap.initial(f.pattern(AccessPathBase.Argument(0), tail = Tail.STAR, mark = MarkSlot.STAR))
        val ordinary = link(BlockScope.ROOT, outer, argument)
        h.rows[outer] = mutableListOf(ordinary to flow())
        h.requests.request(leaf, cg, t)
        assertSame(ordinary, h.delivered.single().link)
        assertSame(argument, h.delivered.single().link.original)
    }

    @Test fun `a known concrete Cg value is not evidence that the root Cf has the mark`() {
        val h = Harness()
        h.rows[leaf] = mutableListOf(link(middle, leaf) to
            f.fact(STATIC, target, Tail.STAR, MarkSlot.Concrete(t), layer = Layer.DEMAND))
        h.requests.request(leaf, cg, t)
        assertTrue(h.delivered.isEmpty())
        assertEquals(listOf(leaf), h.borrowed)

        h.rows[leaf] = mutableListOf(link(middle, leaf) to flow(other))
        h.requests.request(leaf, cg, t)
        assertTrue(h.delivered.isEmpty(), "Only an actually matching FLOW input can carry the request")
    }

    @Test fun `ordinary ports and a changed intermediate original are not identity continuations`() {
        val h = Harness()
        h.rows[leaf] = mutableListOf(link(middle, leaf, cf) to flow())
        h.requests.request(leaf, cg, t)
        assertTrue(h.delivered.isEmpty())

        h.rows[leaf] = mutableListOf(link(middle, leaf, point = PortId(7)) to flow())
        h.requests.request(leaf, cg, t)
        assertTrue(h.delivered.isEmpty())

        val ordinaryParent = middle.copy(entry = PortId(8))
        h.rows[leaf] = mutableListOf(link(ordinaryParent, leaf) to flow())
        h.requests.request(leaf, cg, t)
        assertTrue(h.delivered.isEmpty())

        val before = h.borrowed.size
        h.requests.request(leaf.copy(entry = PortId(9)), cg, t)
        h.requests.request(leaf, ap.initial(f.pattern(STATIC, target, mark = MarkSlot.Concrete(t))), t)
        assertEquals(before, h.borrowed.size)
    }

    @Test fun `visited scopes are local to a query and do not hide a late root input or a new mark`() {
        val h = Harness()
        h.requests.request(leaf, cg, t)
        val later = link(BlockScope.ROOT, outer, cf2)
        h.rows.getValue(outer) += later to flow()
        h.requests.request(leaf, cg, t)
        assertTrue(h.delivered.any { it.link == later && it.mark == t })
        h.requests.request(leaf, cg, u)
        assertTrue(h.delivered.any { it.link == later && it.mark == u })
        assertEquals(3, h.borrowed.count { it == leaf })
    }

    @Test fun `duplicate identity paths visit a shared scope once within one query`() {
        val h = Harness()
        h.rows.getValue(leaf) += link(middle, leaf) to flow()
        h.requests.request(leaf, cg, t)
        assertEquals(1, h.borrowed.count { it == middle })
        assertEquals(1, h.borrowed.count { it == outer })
        assertEquals(1, h.delivered.size)
    }

    @Test fun `cancellation stops input traversal and a later invocation has fresh scratch`() {
        val h = Harness()
        h.beforeBorrow = { f.cancellation.cancel() }
        assertFailsWith<Cancellation.Cancelled> { h.requests.request(leaf, cg, t) }
        assertTrue(h.delivered.isEmpty())
        f.cancellation.activate()
        h.beforeBorrow = null
        h.requests.request(leaf, cg, t)
        assertEquals(1, h.delivered.size)
    }

    @Test fun `backward and later runs do not relay run1 point requests`() {
        for (selectedMode in listOf(ApMode(false, Direction.BACKWARD, 1), ApMode(false, Direction.FORWARD, 2))) {
            val h = Harness(selectedMode)
            h.requests.request(leaf, cg, t)
            assertTrue(h.borrowed.isEmpty())
            assertTrue(h.delivered.isEmpty())
        }
    }

    @Test fun `only a genuine root static answer materializes CfT with a CgT image`() {
        val h = Harness()
        val interests = ArrayList<StaticInterest>()
        val replies = ArrayList<Triple<LocalLink, PremiseKey, Facts>>()
        var ticket = 0L
        val rootRequests = LocalStaticInputRequests(ops, mode, f.method, { ++ticket }, interests::add) { input, original, value ->
            replies += Triple(input, original, value)
        }
        val requests = StaticBoundaryInputRequests(ops, mode, { scope, visit ->
            for ((input, value) in h.rows[scope].orEmpty()) visit(input, value)
        }) { input, value, mark -> rootRequests.request(input, value, mark) }

        requests.request(leaf, cg, t)
        val interest = interests.single()
        assertEquals(cf.toPattern(), interest.region)
        assertEquals(MarkSet.of(t), interest.wanted)
        assertTrue(replies.isEmpty(), "A request or a Cg group is not a Cf answer")
        assertTrue(rootRequests.answer(StaticOwnerEffect.PointReady(f.method, interest.id,
            RegionGroups(cf.toPattern(), MarkSet.of(t)))))
        val (answeredLink, original, value) = replies.single()
        val concreteCf = ap.initial(f.pattern(STATIC, from, Tail.STAR, MarkSlot.Concrete(t)))
        assertEquals(concreteCf, original)
        assertEquals(outer, answeredLink.child)
        assertEquals(original, answeredLink.original)
        assertEquals(f.pattern(STATIC, target, Tail.STAR, MarkSlot.Concrete(t)), ops.leaves(value).single())
        assertEquals(Layer.DEMAND, value.layer)
    }
}

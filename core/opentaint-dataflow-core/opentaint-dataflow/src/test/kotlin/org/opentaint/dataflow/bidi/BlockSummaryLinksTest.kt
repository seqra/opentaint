package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.engine.Target
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.BlockScope
import org.opentaint.dataflow.graph.BlockId
import org.opentaint.dataflow.graph.PortId
import kotlin.test.*

class BlockSummaryLinksTest {
    private val fixture = StoreFixtures()
    private val ap = fixture.manager
    private val ops = fixture.ops
    private val x = AccessPathBase.Argument(0)
    private val y = AccessPathBase.Argument(1)
    private val ret = AccessPathBase.Return
    private val f = fixture.field("f")
    private val g = fixture.field("g")
    private val t = MarkSlot.Concrete(fixture.mark("T"))
    private val u = MarkSlot.Concrete(fixture.mark("U"))
    private val child = BlockScope(BlockId(4), PortId(11))
    private val parent = BlockScope(BlockId(1), PortId(2))
    private val exit = PortId(12)
    private val mode = ApMode(false, Direction.FORWARD, 10)

    private data class Data(val link: LocalLink, val exit: PortId, val row: PremiseKey,
                            val geometry: Pattern, val original: PremiseKey, val value: Facts)
    private data class Terminal(val link: LocalLink, val original: PremiseKey, val target: Target)
    private inner class Harness(selected: ApMode = mode) {
        val data = ArrayList<Data>()
        val terminals = ArrayList<Terminal>()
        val requests = ArrayList<Triple<LocalLink, Facts, TaintMark>>()
        val links = BlockSummaryLinks(ops, selected, child,
            { link, port, row, shape, original, value -> data += Data(link, port, row, shape, original, value) },
            { link, original, target -> terminals += Terminal(link, original, target) },
            { link, value, mark -> requests += Triple(link, value, mark) })
        fun drain() { while (links.hasPending) assertTrue(links.drain(1) > 0) }
    }

    private fun link(original: PremiseKey, layer: Layer = Layer.NORMAL,
                     parentScope: BlockScope = parent, point: PortId = PortId(10)) =
        LocalLink(parentScope, point, original, layer, child)
    private fun initial(base: AccessPathBase = x, mark: MarkSlot = t) =
        ap.initial(fixture.pattern(base, mark = mark))

    @Test fun `unary publication before and after the input produces the same parent relation`() {
        val rowInitial = ap.initial(fixture.pattern(x, listOf(f), Tail.STAR, MarkSlot.STAR))
        val original = initial(y)
        val actual = fixture.fact(x, listOf(f, g), mark = t)
        val row = Publication(rowInitial, fixture.fact(ret, tail = Tail.STAR, mark = MarkSlot.STAR))
        val old = Harness()
        old.links.publish(exit, listOf(row))
        assertFalse(old.links.hasPending)
        old.links.offer(link(original), actual)
        assertTrue(old.links.hasPending)
        assertTrue(old.data.isEmpty(), "Publication callbacks must remain queued")
        old.drain()
        val late = Harness()
        late.links.offer(link(original), actual)
        late.links.publish(exit, listOf(row))
        late.drain()
        assertEquals(old.data, late.data)
        val result = old.data.single()
        assertSame(original, result.original)
        assertEquals(fixture.pattern(ret, listOf(g), mark = t), ops.leaves(result.value).single())
        assertEquals(parent, result.link.parent)
        assertEquals(child, result.link.child)
        assertEquals(PortId(10), result.link.point)
        assertEquals(exit, result.exit)
        assertTrue(old.requests.isEmpty())
    }

    @Test fun `identical offers and publications are deduplicated before another delivery`() {
        val h = Harness()
        val i = initial()
        val input = fixture.fact(x, mark = t)
        val row = Publication(i, fixture.fact(ret, mark = u))
        h.links.offer(link(i), input)
        h.links.publish(exit, listOf(row))
        h.drain()
        assertEquals(1, h.data.size)
        h.links.offer(link(i), input)
        h.links.publish(exit, listOf(row))
        assertFalse(h.links.hasPending)
        assertEquals(1, h.links.inputGroups)
    }

    @Test fun `a complete ND row waits for every member and retains both parent origins`() {
        val h = Harness()
        val i1 = initial(x, t)
        val i2 = initial(y, u)
        val premise = ap.union(i1, i2)
        h.links.publish(exit, listOf(Publication(premise, fixture.fact(ret, mark = u))))
        h.links.offer(link(i1), fixture.fact(x, mark = t))
        h.drain()
        assertTrue(h.data.isEmpty(), "A unary restriction arm is not an executable ND relation")
        h.links.offer(link(i2), fixture.fact(y, mark = u))
        h.drain()
        assertEquals(1, h.data.size)
        assertEquals(setOf(i1, i2), h.data.single().original.members.toSet())
        assertEquals(premise, h.data.single().row)
    }

    @Test fun `ND inputs at different parent points or entries cannot complete each other`() {
        val h = Harness()
        val i1 = initial(x, t)
        val i2 = initial(y, u)
        h.links.publish(exit, listOf(Publication(ap.union(i1, i2), fixture.fact(ret, mark = u))))
        h.links.offer(link(i1), fixture.fact(x, mark = t))
        h.links.offer(link(i2, point = PortId(99)), fixture.fact(y, mark = u))
        h.links.offer(link(i2, parentScope = BlockScope(parent.block, PortId(98))), fixture.fact(y, mark = u))
        h.drain()
        assertTrue(h.data.isEmpty())
        h.links.offer(link(i2), fixture.fact(y, mark = u))
        h.drain()
        assertEquals(1, h.data.size)
    }

    @Test fun `late protected publication upgrades an existing output rather than losing its flag`() {
        val h = Harness()
        val i = initial()
        val plain = fixture.fact(ret, mark = u) as TaintTree
        h.links.offer(link(i), fixture.fact(x, mark = t))
        h.links.publish(exit, listOf(Publication(i, plain)))
        h.drain()
        assertNull((h.data.single().value as TaintTree).nonSubsumable)
        h.links.publish(exit, listOf(Publication(i, plain.withProtection(plain.root))))
        h.drain()
        assertEquals(2, h.data.size)
        assertNotNull((h.data.last().value as TaintTree).nonSubsumable)
        h.links.publish(exit, listOf(Publication(i, plain)))
        assertFalse(h.links.hasPending)
    }

    @Test fun `late protected input upgrades the same complete ND combination`() {
        val h = Harness()
        val i1 = initial(x, t)
        val i2 = initial(y, u)
        val a = fixture.fact(x, mark = t) as TaintTree
        h.links.publish(exit, listOf(Publication(ap.union(i1, i2), fixture.fact(ret, mark = u))))
        h.links.offer(link(i1), a)
        h.links.offer(link(i2), fixture.fact(y, mark = u))
        h.drain()
        val before = h.data.size
        h.links.offer(link(i1), a.withProtection(a.root))
        h.drain()
        assertTrue(h.data.size > before)
        assertNotNull((h.data.last().value as TaintTree).nonSubsumable)
        assertEquals(setOf(i1, i2), h.data.last().original.members.toSet())
    }

    @Test fun `NormalTarget composes only with a normal local input and is ignored backward`() {
        val i = initial()
        val target = Target.NormalTarget(ReportId(17))
        val normal = Harness()
        normal.links.publishTargets(listOf(TargetSummary(i, target)))
        normal.links.offer(link(i), fixture.fact(x, mark = t))
        normal.drain()
        assertEquals(listOf(Terminal(link(i), i, target)), normal.terminals)
        val demand = Harness()
        demand.links.offer(link(i, Layer.DEMAND), fixture.fact(x, mark = t, layer = Layer.DEMAND))
        demand.links.publishTargets(listOf(TargetSummary(i, target)))
        demand.drain()
        assertTrue(demand.terminals.isEmpty())
        val backward = Harness(ApMode(false, Direction.BACKWARD, 10))
        backward.links.publishTargets(listOf(TargetSummary(i, target)))
        backward.links.offer(link(i), fixture.fact(x, mark = t))
        backward.drain()
        assertTrue(backward.terminals.isEmpty())
    }

    @Test fun `ND NormalTarget waits for all normal members and cannot borrow another point`() {
        val h = Harness()
        val i1 = initial(x, t)
        val i2 = initial(y, u)
        val target = Target.NormalTarget(ReportId(18))
        h.links.publishTargets(listOf(TargetSummary(ap.union(i1, i2), target)))
        h.links.offer(link(i1), fixture.fact(x, mark = t))
        h.links.offer(link(i2, point = PortId(99)), fixture.fact(y, mark = u))
        h.drain()
        assertTrue(h.terminals.isEmpty())
        h.links.offer(link(i2), fixture.fact(y, mark = u))
        h.drain()
        assertEquals(setOf(i1, i2), h.terminals.single().original.members.toSet())
    }

    @Test fun `bounded draining keeps local callbacks visible to the method idle barrier`() {
        val h = Harness()
        val i = initial()
        h.links.offer(link(i), fixture.fact(x, mark = t))
        h.links.publish(exit, listOf(Publication(i, fixture.fact(ret, mark = u))))
        h.links.publish(PortId(13), listOf(Publication(i, fixture.fact(ret, listOf(f), mark = u))))
        assertTrue(h.links.hasPending)
        assertFailsWith<IllegalStateException> { h.links.clear() }
        assertEquals(1, h.links.drain(1))
        assertTrue(h.links.hasPending, "A remaining local delivery is counted work")
        assertEquals(1, h.links.drain(1))
        assertFalse(h.links.hasPending)
        assertEquals(setOf(exit, PortId(13)), h.data.map { it.exit }.toSet())
        h.links.clear()
        assertEquals(0, h.links.inputGroups)
    }

    @Test fun `release also clears terminal rows before a new local lifecycle`() {
        val h = Harness()
        val i = initial()
        h.links.publishTargets(listOf(TargetSummary(i, Target.DemandTarget)))
        h.links.clear()
        h.links.offer(link(i), fixture.fact(x, mark = t))
        assertFalse(h.links.hasPending)
        assertTrue(h.terminals.isEmpty())
    }

    @Test fun `run1 ZERO replays certified static FLOW at either publication order without another request`() {
        val clazz = ap.accessors.index(ClassStaticAccessor("C"))
        val i = ap.initial(fixture.pattern(STATIC, listOf(clazz, f), Tail.STAR, MarkSlot.STAR))
        val row = Publication(i, fixture.fact(x, tail = Tail.STAR, mark = MarkSlot.STAR, layer = Layer.DEMAND))
        for (publishFirst in listOf(false, true)) {
            val h = Harness(ApMode(true, Direction.FORWARD, 1))
            if (publishFirst) h.links.publish(exit, listOf(row))
            h.links.offer(link(ap.zero), Reach.NORMAL)
            if (!publishFirst) h.links.publish(exit, listOf(row))
            h.drain()
            val result = h.data.single()
            assertSame(i, result.original)
            assertSame(i, result.link.original)
            assertEquals(Layer.DEMAND, result.value.layer)
            assertEquals(fixture.pattern(x, tail = Tail.STAR, mark = MarkSlot.STAR), ops.leaves(result.value).single())
            assertTrue(h.requests.isEmpty())
        }
    }

    @Test fun `run1 exact static replay equals existing resolved pool input and creates no interest`() {
        val clazz = ap.accessors.index(ClassStaticAccessor("C"))
        val i = ap.initial(fixture.pattern(STATIC, listOf(clazz, f), Tail.EXACT, t))
        val result = fixture.fact(x, mark = u, layer = Layer.DEMAND)
        val service = Run1StaticService(ap)
        val supply = RegionGroups(fixture.pattern(STATIC, listOf(clazz, f), Tail.EXACT, MarkSlot.STAR), MarkSet.of(t.mark))
        val written = StaticBatch().also { it.supplies += supply }
        assertTrue(service.commit(written).isEmpty())
        val subscribed = StaticBatch().also { it.interests += StaticInterest(fixture.method, 7L, i.toPattern(), MarkSet.of(t.mark)) }
        val reply = service.commit(subscribed).filterIsInstance<StaticOwnerEffect.PointReady>().single()
        val actual = service.facts(reply.supply.region, reply.supply.groups)
        val expected = ArrayList<Pair<PremiseKey, Facts>>()
        LocalRelationApplication(ops, ApMode(true, Direction.FORWARD, 1)).applyCurrent(actual, i, i, result,
            object : LocalRelationOut {
                override fun data(original: PremiseKey, value: Facts) { expected += original to value }
                override fun target(original: PremiseKey, target: Target) = error("No Target")
                override fun markRequest(mark: TaintMark) = error("No request")
            })
        assertTrue(expected.isNotEmpty())
        val h = Harness(ApMode(true, Direction.FORWARD, 1))
        h.links.offer(link(ap.zero), Reach.NORMAL)
        h.links.publish(exit, listOf(Publication(i, result)))
        h.drain()
        assertEquals(expected, h.data.map { it.original to it.value })
        assertTrue(h.requests.isEmpty())
    }

    @Test fun `run1 static Target uses supplied DEMAND support and later runs cannot use ZERO for statics`() {
        val clazz = ap.accessors.index(ClassStaticAccessor("C"))
        val i = ap.initial(fixture.pattern(STATIC, listOf(clazz, f), Tail.EXACT, t))
        val h = Harness(ApMode(true, Direction.FORWARD, 1))
        h.links.publishTargets(listOf(TargetSummary(i, Target.DemandTarget), TargetSummary(i, Target.NormalTarget(ReportId(19)))))
        h.links.offer(link(ap.zero), Reach.NORMAL)
        h.drain()
        assertEquals(1, h.terminals.size)
        assertEquals(i, h.terminals.single().original)
        assertEquals(Target.DemandTarget, h.terminals.single().target)
        val later = Harness()
        later.links.offer(link(ap.zero), Reach.NORMAL)
        later.links.publish(exit, listOf(Publication(i, fixture.fact(x, mark = u, layer = Layer.DEMAND))))
        later.links.publishTargets(listOf(TargetSummary(i, Target.DemandTarget)))
        later.drain()
        assertTrue(later.data.isEmpty())
        assertTrue(later.terminals.isEmpty())
    }
}

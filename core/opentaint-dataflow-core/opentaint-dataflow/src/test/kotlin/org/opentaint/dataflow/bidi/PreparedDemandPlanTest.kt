package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.graph.BlockId
import org.opentaint.dataflow.graph.PortId
import kotlin.test.*

class PreparedDemandPlanTest {
    private val f = StoreFixtures()
    private val x = AccessPathBase.Argument(0)
    private val y = AccessPathBase.Argument(1)
    private val ret = AccessPathBase.Return
    private val t = MarkSlot.Concrete(f.mark("T"))
    private val u = MarkSlot.Concrete(f.mark("U"))
    private val a = f.field("a"); private val b = f.field("b"); private val c = f.field("c")
    private val policy = RestrictedInitialPolicy(3, 4, Direction.FORWARD, f.manager.marks)

    private fun exact(expected: List<Facts>, actual: List<Facts>?) {
        assertNotNull(actual)
        assertEquals(expected, actual)
        assertEquals(expected.map { (it as? TaintTree)?.nonSubsumable }, actual.map { (it as? TaintTree)?.nonSubsumable })
    }

    @Test fun `prepared local C5 preserves whole ND members exit ports budgets and protection`() {
        val scope = BlockScope(BlockId(3), PortId(7))
        val first = PortId(11); val second = PortId(12)
        val builder = DemandStore.Builder(f.manager)
        builder.add(f.method, scope, first, DemandPattern(f.pattern(x, mark = t), f.pattern(ret, listOf(a), Tail.ANY, t)))
        builder.add(f.method, scope, first, DemandPattern(f.pattern(y, mark = u), f.pattern(ret, listOf(a,b), Tail.ANY, t)))
        builder.add(f.method, scope, second, DemandPattern(f.pattern(x, mark = t), f.pattern(ret, listOf(c), Tail.ANY, t)))
        val view = builder.build().scope(f.method, scope)
        val original = f.manager.union(f.manager.initial(f.pattern(x, mark = t)), f.manager.initial(f.pattern(y, mark = u)))
        val raw = f.fact(ret, listOf(a,b,c), mark = t) as TaintTree
        for (exit in listOf(first, second)) {
            val plan = assertNotNull((view as PreparedScopeDemandView).prepareDataPlan(exit, original.members.map { it.toPattern() }, policy))
            for (value in listOf(raw, raw.withProtection(raw.root), raw.withLayer(Layer.DEMAND)))
                exact(view.intersect(exit, original, value, policy), plan.intersect(original, value))
        }
    }

    @Test fun `normalized FLOW STAR key keeps exact preimage acceptance`() {
        val demand = DemandStore.Builder(f.manager).apply {
            add(f.method, DemandPattern(f.pattern(x, tail = Tail.ANY, mark = MarkSlot.STAR),
                f.pattern(ret, tail = Tail.ANY, mark = MarkSlot.STAR)))
        }.build()
        val original = f.manager.initial(f.pattern(x, tail = Tail.STAR, mark = MarkSlot.STAR))
        val raw = f.fact(ret, tail = Tail.STAR, mark = MarkSlot.STAR)
        val plan = assertNotNull(demand.prepareDataPlan(f.method, listOf(original.toPattern()), policy))
        assertFalse(plan.emptyForBase(ret))
        exact(demand.intersect(f.method, original, raw, policy), plan.intersect(original, raw))
    }

    @Test fun `empty certificate is entry based and control static and run2 fall back`() {
        val builder = DemandStore.Builder(f.manager)
        builder.add(f.method, DemandPattern(f.pattern(x, mark = t), f.pattern(ret, mark = t)))
        val demand = builder.build()
        val wrong = f.manager.initial(f.pattern(x, mark = u))
        val plan = assertNotNull(demand.prepareDataPlan(f.method, listOf(wrong.toPattern()), policy))
        assertTrue(plan.emptyForBase(ret))
        assertNull(plan.intersect(wrong, Reach.DEMAND))
        assertNull(demand.prepareDataPlan(f.method, listOf(f.manager.zero.toPattern()), policy))
        assertNull(demand.prepareDataPlan(f.method, listOf(wrong.toPattern()), RestrictedInitialPolicy(2,4,Direction.BACKWARD,f.manager.marks)))
        val carry = DemandStore.Builder(f.manager).apply { withSharedStaticCarry() }.build()
        assertNull(carry.prepareDataPlan(f.method, listOf(wrong.toPattern()), policy))
    }

    @Test fun `oversize preparation falls back rather than returning an empty plan`() {
        val builder = DemandStore.Builder(f.manager)
        repeat(2049) { ordinal -> builder.add(f.method, DemandPattern(f.pattern(x, mark = t),
            f.pattern(ret, listOf(f.field("out$ordinal")), Tail.ANY, t))) }
        val original = f.manager.initial(f.pattern(x, mark = t))
        var checks = 0
        assertNull(builder.build().prepareDataPlan(f.method, listOf(original.toPattern()), policy) { checks++ })
        assertEquals(2047,checks, "Count real checks even when the completed plan cannot be retained")
    }
}

package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.*
import kotlin.test.*

/** Directed admission and paired C5 are separate from geometric AP intersection. */
class ControlDemandTest {
    private val f = StoreFixtures()
    private val ap = f.manager
    private val key = f.method
    private val t = MarkSlot.Concrete(f.mark("T"))
    private val arg = f.pattern()
    private val ret = f.pattern(base = AccessPathBase.Return)
    private val policy = RestrictedInitialPolicy(2, 3, Direction.BACKWARD, ap.marks)
    private fun store(vararg rows: PairedDemand): DemandStore = DemandStore.Builder(ap).also { b ->
        rows.forEach { assertTrue(b.add(key, it)) }
    }.build()

    @Test fun `ZERO needs an explicit local Zero or Target entry`() {
        val none = store()
        assertTrue(none.initials(key, Reach.NORMAL, policy).isEmpty())
        val ordinary = store(PairedDemand(DemandEntry.Data(arg), DemandExit.Zero))
        assertTrue(ordinary.initials(key, Reach.NORMAL, policy).isEmpty())
        for (entry in listOf(DemandEntry.Zero, DemandEntry.Target)) {
            val explicit = store(PairedDemand(entry, DemandExit.Data(arg)))
            assertEquals(setOf(existingZeroAdmission(ap.zero)), explicit.initials(key, Reach.NORMAL, policy))
            assertTrue(explicit.initials(f.key("other"), Reach.NORMAL, policy).isEmpty())
            assertTrue(explicit.initials(key, f.fact(), policy).isEmpty())
        }
    }

    @Test fun `a Data entry with a Zero exit still admits its data initial`() {
        val demand = store(PairedDemand(DemandEntry.Data(arg), DemandExit.Zero))
        assertEquals(setOf(AdmittedInitial(ap.initial(arg), Layer.NORMAL)), demand.initials(key, f.fact(), policy))
        assertTrue(demand.acceptsTarget(key, ap.initial(arg), policy))
        assertEquals(listOf(Reach.NORMAL), demand.intersect(key, ap.initial(arg), Reach.NORMAL, policy))
        assertTrue(demand.intersect(key, ap.initial(arg), f.fact(base = AccessPathBase.Return), policy).isEmpty())
    }

    @Test fun `Target entry admits only Zero and restricts AP output by its paired exit`() {
        val demand = store(PairedDemand(DemandEntry.Target, DemandExit.Data(ret)))
        val output = f.fact(base = AccessPathBase.Return)
        assertEquals(listOf(output), demand.intersect(key, ap.zero, output, policy))
        assertTrue(demand.intersect(key, ap.initial(arg), output, policy).isEmpty())
        assertTrue(demand.intersect(key, ap.zero, f.fact(), policy).isEmpty())
        assertFalse(demand.acceptsTarget(key, ap.zero, policy), "Data exit must reject a terminal result")
    }

    @Test fun `Target C5 uses one complete pair and accepts a complete origin through a member`() {
        val demand = store(
            PairedDemand(DemandEntry.Data(arg), DemandExit.Data(ret)),
            PairedDemand(DemandEntry.Zero, DemandExit.Zero),
        )
        assertFalse(demand.acceptsTarget(key, ap.initial(arg), policy))
        assertTrue(demand.acceptsTarget(key, ap.zero, policy))
        val selected = store(PairedDemand(DemandEntry.Data(arg), DemandExit.Zero))
        val both = ap.union(ap.initial(arg), ap.initial(f.pattern(base = AccessPathBase.Argument(1))))
        assertTrue(selected.acceptsTarget(key, both, policy))
        assertFalse(selected.acceptsTarget(f.key("other"), both, policy))
    }

    @Test fun `legacy canonical Zero endpoints become paired control rows without virtual permission`() {
        val builder = DemandStore.Builder(ap)
        assertFalse(builder.add(key, DemandPattern(ap.zero.toPattern(), null)))
        assertTrue(builder.add(key, DemandPattern(arg, ap.zero.toPattern())))
        assertFalse(builder.add(key, PairedDemand(DemandEntry.Data(arg), DemandExit.Zero)))
        val demand = builder.build()
        assertTrue(demand.acceptsTarget(key, ap.initial(arg), policy))
        assertTrue(demand.initials(key, Reach.NORMAL, policy).isEmpty())
    }

    @Test fun `an exact concrete demand admits a provisional MAY point while FLOW keeps its old cells`() {
        val field = f.field("field")
        for (run in listOf(2, 3, 4, 5)) {
            val q = RestrictedInitialPolicy(run, 3,
                if (run % 2 == 0) Direction.BACKWARD else Direction.FORWARD, ap.marks)
            for (mark in listOf(t, MarkSlot.STAR)) {
                val exact = arg.copy(fact = arg.fact.copy(mark = mark))
                val may = exact.copy(fact = exact.fact.copy(tail = Tail.ANY))
                if (mark is MarkSlot.Concrete) {
                    assertEquals(InitialEmission(exact, Layer.DEMAND), q.emitAdmission(exact, may, Layer.DEMAND))
                    val child = exact.copy(fact = exact.fact.copy(path = listOf(field)))
                    assertEquals(InitialEmission(child, Layer.DEMAND), q.emitAdmission(child, may, Layer.DEMAND))
                } else {
                    assertNull(q.emit(exact, may))
                    assertNull(q.emit(exact.copy(fact = exact.fact.copy(path = listOf(field))), may))
                }
                assertEquals(exact, q.emit(exact, exact))
                assertEquals(exact, q.emit(may, exact))
                assertEquals(exact, q.emit(exact, exact.copy(fact = exact.fact.copy(tail = Tail.ANY_TAINT))))
            }
        }
    }

    @Test fun `provisional exact data admission never grants ZERO entry or ZERO Target permission`() {
        val demand = store(PairedDemand(DemandEntry.Data(arg), DemandExit.Zero))
        val may = f.fact(tail = Tail.ANY, layer = Layer.DEMAND)
        repeat(3) { assertEquals(setOf(AdmittedInitial(ap.initial(arg), Layer.DEMAND)), demand.initials(key, may, policy)) }
        assertTrue(demand.initials(key, Reach.NORMAL, policy).isEmpty())
        assertFalse(demand.acceptsTarget(key, ap.zero, policy))
    }
}

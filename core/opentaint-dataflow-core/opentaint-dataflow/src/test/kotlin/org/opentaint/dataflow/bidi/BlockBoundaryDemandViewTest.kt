package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.BlockBoundaryDemandView
import org.opentaint.dataflow.bidi.engine.BlockEntryRole
import org.opentaint.dataflow.bidi.engine.Target
import org.opentaint.dataflow.bidi.engine.TargetSummary
import org.opentaint.dataflow.bidi.engine.ReportId
import org.opentaint.dataflow.bidi.engine.targetHandoffScope
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.BlockScope
import org.opentaint.dataflow.bidi.store.DemandStore
import org.opentaint.dataflow.bidi.store.PairedDemand
import org.opentaint.dataflow.bidi.store.DemandEntry
import org.opentaint.dataflow.bidi.store.DemandExit
import org.opentaint.dataflow.graph.BlockId
import org.opentaint.dataflow.graph.PortId
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue

class BlockBoundaryDemandViewTest {
    private val f = StoreFixtures()
    private val ap = f.manager
    private val p = AccessPathBase.Argument(0)
    private val t = MarkSlot.Concrete(f.mark("T"))
    private val u = MarkSlot.Concrete(f.mark("U"))
    private val block = BlockId(2)
    private val input = BlockScope(block, PortId(6))
    private val normal = BlockScope(block, PortId.ROOT_EXIT)
    private val output = PortId(3)
    private val policy = RestrictedInitialPolicy(2, 1, Direction.BACKWARD, ap.marks)

    private fun view(row: PairedDemand, role: BlockEntryRole, direction: Direction = Direction.BACKWARD,
                     outputs: Collection<PortId> = listOf(output)): BlockBoundaryDemandView {
        val store = DemandStore.Builder(ap).also { it.add(f.method, normal, output, row) }.build()
        return BlockBoundaryDemandView(ap, store.scope(f.method, input), store.scope(f.method, normal),
            direction, role, outputs)
    }

    @Test fun `reached backward exceptional ZERO borrows a whole normal pair with its actual output`() {
        val row = PairedDemand(DemandEntry.Target, DemandExit.Data(f.pattern(p, mark = t)))
        val demand = view(row, BlockEntryRole.EXCEPTIONAL_INTERFACE)
        assertTrue(demand.initials(Reach.NORMAL, policy).any { it.initial.isZero })
        assertEquals(listOf(f.fact(p, mark = t)), demand.intersect(output, ap.zero, f.fact(p, mark = t), policy))
        assertTrue(demand.intersect(output, ap.zero, f.fact(p, mark = u), policy).isEmpty())
        assertTrue(demand.intersect(PortId(4), ap.zero, f.fact(p, mark = t), policy).isEmpty())
        assertFalse(demand.acceptsTarget(PortId.ROOT_ENTRY, ap.zero, policy),
            "The Data exit of the borrowed pair is not a Target permission")
    }

    @Test fun `forward exceptional nonzero data and arbitrary mid block entries do not borrow`() {
        val row = PairedDemand(DemandEntry.Target, DemandExit.Zero)
        val forward = view(row, BlockEntryRole.EXCEPTIONAL_INTERFACE, Direction.FORWARD)
        assertTrue(forward.initials(Reach.NORMAL, policy).isEmpty())
        assertFalse(forward.acceptsTarget(PortId.ROOT_ENTRY, ap.zero, policy))
        val backward = view(row, BlockEntryRole.EXCEPTIONAL_INTERFACE)
        val original = ap.initial(f.pattern(p, mark = t))
        assertTrue(backward.initials(f.fact(p, mark = t), policy).isEmpty())
        assertTrue(backward.intersect(output, original, f.fact(p, mark = t), policy).isEmpty())
        assertFalse(backward.acceptsTarget(PortId.ROOT_ENTRY, original, policy))
        val mid = view(row, BlockEntryRole.MID_BLOCK)
        assertTrue(mid.initials(Reach.NORMAL, policy).isEmpty())
        assertFalse(mid.acceptsTarget(PortId.ROOT_ENTRY, ap.zero, policy))
    }

    @Test fun `normal Target endpoint uses genuine physical normal outputs without mixing their pairs`() {
        val row = PairedDemand(DemandEntry.Target, DemandExit.Zero)
        val demand = view(row, BlockEntryRole.NORMAL_INTERFACE)
        assertTrue(demand.initials(Reach.NORMAL, policy).any { it.initial.isZero })
        assertTrue(demand.acceptsTarget(PortId.ROOT_ENTRY, ap.zero, policy))
        assertFalse(view(row, BlockEntryRole.NORMAL_INTERFACE, outputs = listOf(PortId(4)))
            .acceptsTarget(PortId.ROOT_ENTRY, ap.zero, policy))
    }
    @Test fun `only borrowed backward ZERO DemandTarget handoff uses the normal invocation address`() {
        val zero = TargetSummary(ap.zero, Target.DemandTarget)
        val logical = input.copy(entry = PortId.ROOT_EXIT)
        assertEquals(logical, targetHandoffScope(input, Direction.BACKWARD, true, zero))
        assertEquals(input, targetHandoffScope(input, Direction.FORWARD, true, zero))
        assertEquals(input, targetHandoffScope(input, Direction.BACKWARD, false, zero))
        assertEquals(input, targetHandoffScope(input, Direction.BACKWARD, true,
            TargetSummary(ap.initial(f.pattern(p, mark = t)), Target.DemandTarget)))
        assertEquals(input, targetHandoffScope(input, Direction.BACKWARD, true,
            TargetSummary(ap.zero, Target.NormalTarget(ReportId(1)))))
        val demand = view(PairedDemand(DemandEntry.Target, DemandExit.Zero), BlockEntryRole.EXCEPTIONAL_INTERFACE)
        assertTrue(demand.admission(Reach.NORMAL, policy).borrowedExceptionalNormalZero)
        assertFalse(demand.admission(f.fact(p, mark = t), policy).borrowedExceptionalNormalZero)
    }

}

package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.graph.BlockId
import org.opentaint.dataflow.graph.PortId
import kotlin.test.*

/** C2 must not recover a refinement initial from a discarded MUST descendant. */
class CanonicalInitialAdmissionTest {
    private val f = StoreFixtures()
    private val ap = f.manager
    private val x = AccessPathBase.Argument(0)
    private val field = f.field("f")
    private val root = f.fact(x, tail = Tail.ANY_TAINT, mark = MarkSlot.STAR) as FlowTree
    private val child = f.fact(x, listOf(field), Tail.ANY_TAINT, MarkSlot.STAR) as FlowTree
    // Build an actual native packet, without going through an admitting store.
    private val packet = root.withRoot(FlowAlgebra.mergeAddDelta(root.root, child.root, ap.cancellation).first)
    private val demand = DemandPattern(f.pattern(x, tail = Tail.ANY, mark = MarkSlot.STAR),
        f.pattern(AccessPathBase.Return, tail = Tail.STAR, mark = MarkSlot.STAR))
    private val policy = RestrictedInitialPolicy(3, 2, Direction.FORWARD, ap.marks)
    private val scope = BlockScope(BlockId(1), PortId(3))
    private val exit = PortId(4)
    private val expected get() = setOf(AdmittedInitial(ap.initial(
        f.pattern(x, tail = Tail.ANY_TAINT, mark = MarkSlot.STAR)), Layer.NORMAL))

    @Test fun `method admission uses canonical actual packet only`() {
        val store = DemandStore.Builder(ap).also { it.add(f.method, demand) }.build()
        assertEquals(expected, store.initials(f.method, packet, policy))
    }

    @Test fun `block and loop observer admission use the same canonical packet`() {
        val store = DemandStore.Builder(ap).also { it.add(f.method, scope, exit, demand) }.build()
        val view = store.scope(f.method, scope)
        assertEquals(expected, view.initials(packet, policy))
        val scratch = LoopQueryScratch(ap, LoopQueryCounts())
        assertEquals(expected, scratch.initials(view, packet, policy))
    }

    @Test fun `direct AP emitter does not preserve discarded refinement history`() {
        assertEquals(expected.map { it.initial }.toSet(), f.ops.emit(demand, packet, policy).toSet())
    }
}

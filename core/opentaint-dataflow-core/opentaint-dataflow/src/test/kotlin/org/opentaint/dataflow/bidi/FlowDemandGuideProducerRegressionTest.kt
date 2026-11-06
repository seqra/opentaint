package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.HandOff
import org.opentaint.dataflow.bidi.engine.Publication
import org.opentaint.dataflow.bidi.engine.PublicationIndex
import org.opentaint.dataflow.bidi.fixtures.HandOffFixtures
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.graph.PortId
import kotlin.test.*

/** Required producer law from the 2026-11-06 demand-guidance correction.
 * Uses native current stores only. No overlay, replacement C2, or whole-program driver.
 */
class FlowDemandGuideProducerRegressionTest {
    private val fixture = StoreFixtures()
    private val m = fixture.manager
    private val x = AccessPathBase.Argument(0)
    private val field = fixture.field("f")
    private val listener = fixture.field("taskStatusListener")
    private val tag = fixture.mark("T")
    private val rootPath = emptyList<Int>()
    private val childPath = listOf(field)
    private val both = setOf(rootPath, childPath)
    private val original = m.initial(fixture.pattern(AccessPathBase.Return, listOf(listener), Tail.ANY,
        MarkSlot.STAR))

    private enum class Arrival { PACKET, ROOT_THEN_CHILD, CHILD_THEN_ROOT }
    private enum class Owner { POINT, SUMMARY, PUBLICATION }
    private fun flow(paths: List<List<Int>>, layer: Layer = Layer.DEMAND,
                     tail: Tail = Tail.ANY): FlowTree = m.flowTree(x, layer,
        ExclusionSet.Empty, MarkSet.EMPTY, paths.map {
            FlowAlgebra.prepend(m, m.path(it), FlowAlgebra.LEAF_NODE)
        }.reduce { a, b -> FlowAlgebra.mergeAdd(a, b) }, tail)
    private fun offers(order: Arrival, layer: Layer = Layer.DEMAND,
                       tail: Tail = Tail.ANY): List<FlowTree> = when (order) {
        Arrival.PACKET -> listOf(flow(listOf(rootPath, childPath), layer, tail))
        Arrival.ROOT_THEN_CHILD -> listOf(flow(listOf(rootPath), layer, tail), flow(listOf(childPath), layer, tail))
        Arrival.CHILD_THEN_ROOT -> listOf(flow(listOf(childPath), layer, tail), flow(listOf(rootPath), layer, tail))
    }
    private fun paths(values: Iterable<Facts>): Set<List<Int>> = values.flatMap { value ->
        fixture.ops.leaves(value).map { it.fact.path }.toList()
    }.toSet()
    private fun assertGuide(values: List<Facts>, expected: Set<List<Int>>, label: String) {
        assertEquals(expected, paths(values), label)
        for (value in values) {
            assertEquals(x, value.base, label)
            assertEquals(Layer.DEMAND, value.layer, label)
            assertTrue(value is FlowTree && value.tail == Tail.ANY, label)
            assertTrue(fixture.ops.leaves(value).all {
                it.fact.mark == MarkSlot.STAR && it.exclusion == ExclusionSet.Empty
            }, label)
        }
    }
    private fun checkGroup(order: Arrival) {
        val group = FlowGroup(m, m.newInterners().flow)
        for (offer in offers(order)) {
            assertGuide(group.addAll(offer), paths(listOf(offer)), "$order fresh coordinate delta")
        }
        assertGuide(group.all().toList(), both, "$order retained coordinates")
        assertTrue(group.addAll(flow(listOf(rootPath, childPath))).isEmpty(), "$order exact duplicate packet")
    }

    @Test fun `APManager cold FLOW DEMAND ANY packet retains explicit root and child`() {
        assertGuide(m.canonicalPackets(flow(listOf(rootPath, childPath))), both, "cold AP packet")
    }
    @Test fun `FlowGroup cold packet retains both coordinates`() = checkGroup(Arrival.PACKET)
    @Test fun `FlowGroup later child is fresh after root`() = checkGroup(Arrival.ROOT_THEN_CHILD)
    @Test fun `FlowGroup later root keeps the existing child`() = checkGroup(Arrival.CHILD_THEN_ROOT)
    @Test fun `an exact duplicate coordinate returns no fresh value`() {
        for (path in listOf(rootPath, childPath)) {
            val group = FlowGroup(m, m.newInterners().flow)
            val value = flow(listOf(path))
            assertGuide(group.addAll(value), setOf(path), "first coordinate")
            assertTrue(group.addAll(value).isEmpty(), "same coordinate is an exact duplicate")
            assertGuide(group.all().toList(), setOf(path), "duplicate leaves state unchanged")
        }
    }

    @Test fun `NORMAL FLOW MUST keeps existing prefix coverage`() {
        for (order in Arrival.entries) {
            val group = FlowGroup(m, m.newInterners().flow)
            offers(order, Layer.NORMAL, Tail.ANY_TAINT).forEach(group::addAll)
            assertEquals(setOf(rootPath), paths(group.all().toList()), "$order NORMAL FLOW MUST")
            assertTrue(group.addAll(flow(listOf(childPath), Layer.NORMAL, Tail.ANY_TAINT)).isEmpty())
        }
    }
    @Test fun `concrete TAINT MAY and MUST keep existing prefix coverage`() {
        for ((layer, tail) in listOf(Layer.DEMAND to Tail.ANY, Layer.NORMAL to Tail.ANY_TAINT)) {
            fun taint(paths: List<List<Int>>): TaintTree {
                val leaf = m.taintAlg.leafNode(m.taintLeaves(MarkSet.EMPTY, m.markSetOf(tag)))
                val root = paths.map { m.taintAlg.prepend(m, m.path(it), leaf) }
                    .reduce { a, b -> m.taintAlg.mergeAdd(a, b) }
                return m.taintTree(x, layer, root, ExclusionSet.Empty, tail)
            }
            for (order in Arrival.entries) {
                val inputs = when (order) {
                    Arrival.PACKET -> listOf(taint(listOf(rootPath, childPath)))
                    Arrival.ROOT_THEN_CHILD -> listOf(taint(listOf(rootPath)), taint(listOf(childPath)))
                    Arrival.CHILD_THEN_ROOT -> listOf(taint(listOf(childPath)), taint(listOf(rootPath)))
                }
                val group = TaintGroup(m, m.newInterners().taint)
                inputs.forEach(group::addAll)
                assertEquals(setOf(rootPath), paths(group.all().toList()), "$order concrete $layer/$tail")
                assertTrue(group.addAll(taint(listOf(childPath))).isEmpty())
            }
        }
    }

    /** Public native point/summary/publication owners, with the identical full P.
     * These inputs are prescribed as admitted: this test does not establish C5 admission.
     */
    private fun checkOwner(owner: Owner, order: Arrival) {
        val points = object : PointDirectory<Int> {
            override val size = 2
            override fun index(point: Int) = point
        }
        val point = ScopedEdgeStore(m, points, 1)
        val otherPointOwner = ScopedEdgeStore(m, points, 1)
        val ports = PortSummaryStores(m)
        val exit = PortId(7)
        val otherExit = PortId(8)
        val summary = ports.at(exit)
        val publications = PublicationIndex(m, fixture.ops)
        val otherPublicationOwner = PublicationIndex(m, fixture.ops)
        val mode = ApMode(false, Direction.BACKWARD, 1, MarkMode.FULL)
        val probe = m.factsOf(original.toPattern().fact, original.exclusion, Layer.DEMAND)
        fun published(index: PublicationIndex) = index.candidates(original, probe, mode).map { it.first }
        fun add(offer: FlowTree): List<Facts> = when (owner) {
            Owner.POINT -> point.addAll(0, original, offer)
            Owner.SUMMARY -> summary.addAdmittedAll(original, offer)
            Owner.PUBLICATION -> publications.addAll(listOf(Publication(original, offer))).map {
                assertSame(original, it.premise, "publication must retain the entire original P")
                it.conclusion
            }
        }
        for (offer in offers(order)) assertGuide(add(offer), paths(listOf(offer)), "$owner $order fresh delta")
        val stored = when (owner) {
            Owner.POINT -> point.edgesAt(0).toList()
            Owner.SUMMARY -> summary.all().toList()
            Owner.PUBLICATION -> published(publications).map { it.premise to it.conclusion }
        }
        stored.forEach { assertSame(original, it.first, "$owner must retain full P, including FLOW mx") }
        assertGuide(stored.map { it.second }, both, "$owner $order retained coordinates")
        assertTrue(add(flow(listOf(rootPath, childPath))).isEmpty(), "$owner exact packet duplicate")
        assertTrue(point.edgesAt(1).none(), "another point does not share a post-statement cell")
        assertTrue(otherPointOwner.edgesAt(0).none(), "another scope owner does not share the cell")
        assertNull(ports.existing(otherExit), "another exit does not share the summary endpoint")
        assertTrue(published(otherPublicationOwner).isEmpty(), "another publication owner is independent")
        if (owner == Owner.SUMMARY) assertGuide(summary.demandEdges(Direction.BACKWARD).map { it.second }.toList(), both, "outgoing SUMMARY guide view")
    }
    @Test fun `point owner retains guide coordinates for all arrivals`() {
        Arrival.entries.forEach { checkOwner(Owner.POINT, it) }
    }
    @Test fun `SUMMARY owner retains guide coordinates for all arrivals`() {
        Arrival.entries.forEach { checkOwner(Owner.SUMMARY, it) }
    }
    @Test fun `publication owner retains guide coordinates for all arrivals`() {
        Arrival.entries.forEach { checkOwner(Owner.PUBLICATION, it) }
    }

    private fun checkFrozenHandoff(order: Arrival) {
        HandOffFixtures(index = 2, L = 1).use { f ->
            assertEquals(MarkMode.FULL, f.config.mode.markMode)
            assertEquals(Direction.BACKWARD, f.config.direction)
            val key = f.key()
            val child = f.field("f")
            val taskExit = f.initial(AccessPathBase.Return, listOf(f.field("taskStatusListener")), Tail.ANY, MarkSlot.STAR)
            val otherExit = f.initial(AccessPathBase.Return, listOf(f.field("workflowStatusListener")), Tail.ANY, MarkSlot.STAR)
            fun packet(paths: List<List<Int>>) = f.manager.flowTree(x, Layer.DEMAND, ExclusionSet.Empty, MarkSet.EMPTY,
                paths.map { FlowAlgebra.prepend(f.manager, f.manager.path(it), FlowAlgebra.LEAF_NODE) }
                    .reduce { a, b -> FlowAlgebra.mergeAdd(a, b) }, Tail.ANY)
            val inputs = when (order) {
                Arrival.PACKET -> listOf(packet(listOf(emptyList(), listOf(child))))
                Arrival.ROOT_THEN_CHILD -> listOf(packet(listOf(emptyList())), packet(listOf(listOf(child))))
                Arrival.CHILD_THEN_ROOT -> listOf(packet(listOf(listOf(child))), packet(listOf(emptyList())))
            }
            inputs.forEach { f.summary(key, taskExit, it) }
            f.summary(key, otherExit, packet(listOf(emptyList())))
            val handoff = HandOff.of(f.config, f.result(), f.shared)
            fun entry(path: List<Int>) = f.pattern(x, path, Tail.ANY, MarkSlot.STAR)
            val expected = setOf(DemandPattern(entry(emptyList()), taskExit.toPattern()),
                DemandPattern(entry(listOf(child)), taskExit.toPattern()),
                DemandPattern(entry(emptyList()), otherExit.toPattern()))
            assertEquals(expected, handoff.demand.explicitRows(key).toSet(), "$order exact entry/exit pairs")
            assertEquals(mapOf(key to 3), handoff.demandEdges)
            assertFalse(DemandPattern(entry(listOf(child)), otherExit.toPattern()) in handoff.demand.explicitRows(key),
                "The child must not borrow workflowStatusListener's paired exit")
            assertTrue(handoff.demand.explicitRows(f.key("different-context")).isEmpty())
        }
    }
    @Test fun `frozen handoff preserves each entry and its own paired exit`() {
        Arrival.entries.forEach(::checkFrozenHandoff)
    }
    @Test fun `packed TAINT FLOW geometry surrogate remains canonical`() {
        val shape = m.initial(x, null, Tail.STAR, ExclusionSet.Empty, MarkSlot.STAR)
        val packet = DiagonalDelta(shape, x, Layer.DEMAND, flow(listOf(rootPath, childPath)).root,
            m.markSetOf(tag), false, Tail.ANY)
        val store = DiagonalRelations(m)
        assertNotNull(store.addDiagonal(packet), "native packed admission supports this complete geometry")
        val decoded = store.all().toList()
        assertEquals(1, store.rowCount)
        assertEquals(1, store.markMembershipCount)
        assertEquals(setOf(rootPath), paths(decoded.map { it.second }))
        assertTrue(decoded.all { (premise, facts) ->
            !premise.isFlow && facts is TaintTree && facts.layer == Layer.DEMAND && facts.anyTail == Tail.ANY
        }, "packed FLOW geometry is a typed TAINT surrogate, not a demand-guide FLOW packet")
        assertTrue(assertNotNull(store.addDiagonal(packet)).isEmpty(), "same canonical packed geometry is a duplicate")
    }
}

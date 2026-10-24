package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.NeutralRelationBatch
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.DiagonalRelations
import org.opentaint.dataflow.util.Cancellation
import kotlin.test.*

class DiagonalDeltaTest {
    private val fixture = StoreFixtures()
    private val m = fixture.manager
    private val f = fixture.field("f")
    private val g = fixture.field("g")
    private val t = fixture.mark("T")
    private val u = fixture.mark("U")
    private val v = fixture.mark("V")
    private val shape = m.initial(AccessPathBase.Argument(0), null, Tail.STAR, ExclusionSet.Empty, MarkSlot.STAR)
    private fun packet(marks: List<TaintMark> = listOf(t, u), protected: Boolean = false,
                       field: Int = f): DiagonalDelta = DiagonalDelta(shape, AccessPathBase.Return, Layer.DEMAND,
        FlowAlgebra.prepend(m, m.path(listOf(field)), FlowAlgebra.LEAF_NODE),
        m.intern(MarkSet(marks.map { it.id }.toIntArray())), protected)
    private fun decode(packet: DiagonalDelta): List<Pair<InitialAp, TaintTree>> =
        checkNotNull(NeutralRelationBatch.fromDiagonal(m, packet)).decode().toList()
    private fun observe(values: Sequence<Pair<PremiseKey, Facts>>): Pair<Set<Pair<PremiseKey, Pattern>>, Set<Pair<PremiseKey, Pattern>>> {
        val current = values.toList()
        return current.flatMap { (pr, value) -> fixture.ops.leaves(value).map { pr to it }.toList() }.toSet() to
            current.flatMap { (pr, value) -> (value as? TaintTree)?.protectedPart()?.let { flags ->
                fixture.ops.leaves(flags).map { pr to it }.toList()
            }.orEmpty() }.toSet()
    }

    @Test
    fun `same geometry packets merge exact mark masks and return only novel memberships`() {
        val store = DiagonalRelations(m)
        val first = packet()
        assertEquals(listOf(first), store.addDiagonal(first))
        assertEquals(emptyList(), store.addDiagonal(first))
        val overlap = packet(listOf(u, v))
        val fresh = assertNotNull(store.addDiagonal(overlap)).single()
        assertEquals(MarkSet.of(v), fresh.marks)
        assertFalse(fresh.protected)
        assertEquals(1, store.rowCount)
        assertEquals(3, store.markMembershipCount)
        assertEquals(first.marks, m.intern(MarkSet(intArrayOf(t.id, u.id))), "Input masks stay immutable")
        for ((initial, facts) in store.all()) {
            val mark = ((initial as InitialAp).mark as MarkSlot.Concrete).mark
            assertEquals(setOf(mark), fixture.ops.leaves(facts).map { (it.fact.mark as MarkSlot.Concrete).mark }.toSet())
        }
    }

    @Test
    fun `late packet protection is sticky and grows once for each mark`() {
        val store = DiagonalRelations(m)
        store.addDiagonal(packet())
        val first = assertNotNull(store.addDiagonal(packet(listOf(t), protected = true))).single()
        assertEquals(MarkSet.of(t), first.marks)
        assertTrue(first.protected)
        assertEquals(emptyList(), store.addDiagonal(packet(listOf(t), protected = true)))
        val second = assertNotNull(store.addDiagonal(packet(listOf(t, u, v), protected = true))).single()
        assertEquals(MarkSet(intArrayOf(u.id, v.id)), second.marks)
        assertTrue(second.protected)
        assertEquals(emptyList(), store.addDiagonal(packet(listOf(t, u, v))))
        val census = store.census()
        assertEquals(3, census.concreteOutputMemberships)
        assertEquals(3, census.protectedOutputMemberships)
        assertEquals(1, census.diagonalGeometryRows)
    }

    @Test
    fun `packet admission and scalar decoding have the same current relation and deltas`() {
        val sequences = listOf(
            listOf(packet(listOf(t)), packet(listOf(u)), packet(listOf(t, u), true), packet(listOf(t, u))),
            listOf(packet(listOf(t, u), true), packet(listOf(u)), packet(listOf(t, u), true)),
        )
        for (sequence in sequences) {
            val bulk = DiagonalRelations(m)
            val scalar = DiagonalRelations(m)
            for (offered in sequence) {
                val accepted = assertNotNull(bulk.addDiagonal(offered))
                val actual = accepted.flatMap(::decode).map { (initial, facts) ->
                    (initial as PremiseKey) to (facts as Facts)
                }.asSequence()
                val expected = decode(offered).mapNotNull { (initial, facts) ->
                    scalar.add(initial, facts)?.let { initial as PremiseKey to it }
                }.asSequence()
                assertEquals(observe(expected), observe(actual))
                assertEquals(observe(scalar.all()), observe(bulk.all()))
            }
        }
    }

    @Test
    fun `unsupported overlapping geometry returns fallback before any mask mutation`() {
        val store = DiagonalRelations(m)
        store.addDiagonal(packet(listOf(t)))
        val before = store.census()
        val different = packet(listOf(t, u), field = g)
        assertNull(store.addDiagonal(different))
        assertEquals(before, store.census())
        for ((initial, facts) in decode(different)) store.add(initial, facts)
        assertEquals(3, store.census().concreteOutputMemberships)
        assertNotNull(store.addDiagonal(packet(listOf(v), field = g)), "Disjoint marks can use a different geometry")
        assertEquals(4, store.census().concreteOutputMemberships)
    }

    @Test
    fun `packet contract rejects invalid full masks and foreign owner admission`() {
        assertFailsWith<IllegalArgumentException> { packet().copy(marks = MarkSet.EMPTY) }
        assertFailsWith<IllegalArgumentException> { packet().copy(marks = MarkSet.of(TaintMark.ZERO)) }
        val group = m.marks.runtimeAtom(t, MarkMode.GROUP)
        assertFailsWith<IllegalArgumentException> { packet().copy(marks = MarkSet.of(group)) }
        assertFailsWith<IllegalArgumentException> { packet().copy(initialShape = m.zero) }
        assertFailsWith<IllegalArgumentException> { packet().copy(geometry = FlowAlgebra.leafNode(FlowLeaf.NONE)) }
        val other = StoreFixtures().manager
        val foreign = other.initial(AccessPathBase.Argument(0), null, Tail.STAR, ExclusionSet.Empty, MarkSlot.STAR)
        val foreignMark = other.marks.mark("T")
        val store = DiagonalRelations(m)
        assertFailsWith<IllegalArgumentException> {
            store.addDiagonal(packet().copy(initialShape = foreign, marks = MarkSet.of(foreignMark)))
        }
        assertTrue(store.isEmpty)
    }

    @Test
    fun `cancelled packet admission leaves current geometry masks unchanged`() {
        val store = DiagonalRelations(m)
        val offered = packet()
        fixture.cancellation.cancel()
        try {
            assertFailsWith<Cancellation.Cancelled> { store.addDiagonal(offered) }
        } finally { fixture.cancellation.activate() }
        assertTrue(store.isEmpty)
        assertNotNull(store.addDiagonal(offered))
    }
}

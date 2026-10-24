package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.NeutralRelationBatch
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.ir.api.common.cfg.CommonInst
import kotlin.test.*

class NeutralRelationBatchTest {
    private val fixture = StoreFixtures()
    private val v = StoreValues(fixture)
    private val m = fixture.manager
    private val ops = fixture.ops
    private val mode = ApMode(true, Direction.FORWARD, 1)
    private val node = fixture.inst(1)

    private fun batch(mark: MarkSlot.Concrete, path: List<Int> = v.p(v.f), protected: Boolean = false): NeutralRelationBatch = with(v) {
        val facts = pack(leaf(path, Tail.ANY, mark, Layer.DEMAND)) as TaintTree
        return checkNotNull(NeutralRelationBatch.from(m, premise(tail = Tail.STAR, mark = mark),
            if (protected) facts.withProtection(facts.root) else facts))
    }

    @Test fun `mark independent cohorts keep exact original correlation`(): Unit = with(v) {
        val a = batch(mt)
        val b = batch(mu)
        assertEquals(a.geometryKey, b.geometryKey)
        assertTrue(a.mergeIfSameGeometry(b))
        assertEquals(2, a.size)
        val decoded = a.decode().toList()
        assertEquals(setOf(premise(tail = Tail.STAR, mark = mt), premise(tail = Tail.STAR, mark = mu)), decoded.map { it.first }.toSet())
        for ((initial, facts) in decoded) {
            assertEquals((initial.mark as MarkSlot.Concrete).mark,
                (ops.leaves(facts).single().fact.mark as MarkSlot.Concrete).mark)
        }
    }

    @Test fun `protected geometry is not merged with a plain cohort`(): Unit = with(v) {
        val plain = batch(mt)
        val flagged = batch(mu, protected = true)
        assertNotEquals(plain.geometryKey, flagged.geometryKey)
        assertFalse(plain.mergeIfSameGeometry(flagged))
        assertEquals(1, plain.size)
    }

    @Test fun `field geometry and complete headers partition cohorts`(): Unit = with(v) {
        assertFalse(batch(mt).mergeIfSameGeometry(batch(mu, p(g))))
        val origin = premise(p(g), tail = Tail.STAR, mark = mu)
        val other = checkNotNull(NeutralRelationBatch.from(m, origin,
            pack(leaf(p(f), Tail.ANY, mu, Layer.DEMAND))))
        assertFalse(batch(mt).mergeIfSameGeometry(other))
    }

    @Test fun `quantum slices retain only masks and scalar fallback consumes one`(): Unit = with(v) {
        val a = batch(mt)
        assertTrue(a.mergeIfSameGeometry(batch(mu)))
        val first = a.take(1)
        assertEquals(1, first.markCount)
        assertEquals(1, a.markCount)
        assertEquals(first.geometryKey, a.geometryKey)
        val one = first.removeFirst()
        val two = a.removeFirst()
        assertTrue(first.isEmpty)
        assertTrue(a.isEmpty)
        assertNotEquals(one.first, two.first)
        assertFails { a.removeFirst() }
    }

    @Test fun `neutral read matches scalar form semantics with one packed transfer`(): Unit = with(v) {
        val a = batch(mt)
        assertTrue(a.mergeIfSameGeometry(batch(mu)))
        val summary = StatementSummary(setOf(x), listOf(MicroEdge.of(starEdge(x, p(f), y, p()))), emptyList(), emptyMap())
        val expected = scalar(a.decode().toList(), summary)
        val actual = ArrayList<Pair<PremiseKey, Facts>>()
        assertTrue(a.apply(ops, summary, mode, { pr, f -> actual += pr to f }))
        assertEquals(observations(expected), observations(actual))
        assertEquals(2, actual.size)
        for ((initial, facts) in actual) {
            assertEquals((initial as InitialAp).mark, ops.leaves(facts).single().fact.mark)
        }
    }

    @Test fun `protected exact and ANY paths survive packed field cut`(): Unit = with(v) {
        fun member(mark: MarkSlot.Concrete): NeutralRelationBatch {
            val facts = pack(leaf(p(f, g), Tail.EXACT, mark, Layer.DEMAND),
                leaf(p(h), Tail.ANY, mark, Layer.DEMAND)) as TaintTree
            val protected = pack(leaf(p(f, g), Tail.EXACT, mark, Layer.DEMAND)) as TaintTree
            return checkNotNull(NeutralRelationBatch.from(m, premise(tail = Tail.STAR, mark = mark), facts.withProtection(protected.root)))
        }
        val a = member(mt)
        assertTrue(a.mergeIfSameGeometry(member(mu)))
        val summary = StatementSummary.identities(listOf(x))
        val expected = scalar(a.decode().toList(), summary)
        val actual = ArrayList<Pair<PremiseKey, Facts>>()
        assertTrue(a.apply(ops, summary, mode, { pr, f -> actual += pr to f }))
        assertEquals(observations(expected), observations(actual))
        assertTrue(actual.any { (it.second as TaintTree).nonSubsumable != null })
    }

    @Test fun `untouched input uses the unchanged callback and no generated callback`(): Unit = with(v) {
        val a = batch(mt)
        assertTrue(a.mergeIfSameGeometry(batch(mu)))
        val unchanged = ArrayList<Pair<PremiseKey, Facts>>()
        assertTrue(a.apply(ops, StatementSummary.EMPTY, mode, { _, _ -> fail("No generated output") },
            { pr, facts -> unchanged += pr to facts }))
        assertEquals(observations(a.decode().toList()), observations(unchanged))
    }

    @Test fun `rules static operations and primitive filters keep scalar fallback`(): Unit = with(v) {
        val a = batch(mt)
        val marked = PathEdge(PathFact(x, p(), Tail.EXACT, mt), PathFact(y, p(), Tail.EXACT, mu), ExclusionSet.Empty)
        val source = StatementSummary(setOf(x), listOf(MicroEdge.of(marked)), emptyList(), emptyMap())
        assertFalse(a.apply(ops, source, mode, { _, _ -> fail("Unsupported form made an output") }))
        val primitive = StatementSummary(setOf(x), listOf(identityEdge(x)), emptyList(),
            mapOf(x to TypeFilter(FactTypeChecker.AlwaysAcceptFilter, MarkPolicy { _, _ -> true })))
        assertFalse(NeutralRelationBatch.certifies(primitive))
        val staticEdge = StatementSummary(setOf(x), listOf(MicroEdge.of(starEdge(x, p(), STATIC, p(f)))), emptyList(), emptyMap())
        assertFalse(NeutralRelationBatch.certifies(staticEdge))
        assertEquals(1, a.size)
    }

    @Test fun `cross mark and static conclusions cannot enter a diagonal transport batch`(): Unit = with(v) {
        assertNull(NeutralRelationBatch.from(m, premise(tail = Tail.STAR, mark = mt), pack(leaf(p(), mark = mu))))
        assertNull(NeutralRelationBatch.from(m, premise(tail = Tail.STAR, mark = mt),
            pack(leaf(p(f), Tail.ANY, mt, Layer.DEMAND, base = STATIC))))
        assertNull(NeutralRelationBatch.from(m, premise(mark = mt), pack(leaf(p(), mark = mt))))
        val staticInitial = m.initial(STATIC, m.path(p(f)), Tail.STAR, ExclusionSet.Empty, mt)
        assertNotNull(NeutralRelationBatch.from(m, staticInitial, pack(leaf(p(), Tail.ANY, mt, Layer.DEMAND))))
    }

    @Test fun `GROUP atoms and nonempty field exclusions keep scalar fallback`(): Unit = with(v) {
        val grouped = MarkSlot.Concrete(m.marks.runtimeAtom(t, MarkMode.GROUP))
        assertNull(NeutralRelationBatch.from(m, premise(tail = Tail.STAR, mark = grouped),
            pack(leaf(p(), Tail.ANY, grouped, Layer.DEMAND))))
        val excluded = pack(leaf(p(), Tail.ANY_TAINT, mt, e = ex(g)))
        assertNull(NeutralRelationBatch.from(m, premise(tail = Tail.STAR, mark = mt), excluded))
    }

    @Test fun `packed callback reaches packet admission before any scalar output`(): Unit = with(v) {
        val a = batch(mt)
        assertTrue(a.mergeIfSameGeometry(batch(mu)))
        val summary = StatementSummary(setOf(x), listOf(MicroEdge.of(starEdge(x, p(f), y, p()))), emptyList(), emptyMap())
        val expected = scalar(a.decode().toList(), summary)
        val packets = ArrayList<DiagonalDelta>()
        var callbacks = 0
        assertTrue(a.applyPacked(ops, summary, mode, { shape, packed, mask ->
            callbacks++
            assertEquals(marks(t.id, u.id), mask)
            assertEquals(mask, m.taintAlg.foldAll(packed.root).any)
            packets += checkNotNull(NeutralRelationBatch.toDiagonal(m, shape, packed, mask))
        }))
        assertEquals(1, callbacks)
        assertEquals(1, packets.size)
        assertFalse(packets.single().protected)
        val restored = checkNotNull(NeutralRelationBatch.fromDiagonal(m, packets.single()))
        assertEquals(observations(expected), observations(restored.decode().toList()))
    }

    @Test fun `whole protected packet round trip keeps every origin marked`(): Unit = with(v) {
        val a = batch(mt, protected = true)
        assertTrue(a.mergeIfSameGeometry(batch(mu, protected = true)))
        var packet: DiagonalDelta? = null
        assertTrue(a.applyPacked(ops, StatementSummary.identities(listOf(x)), mode,
            { shape, packed, mask -> packet = checkNotNull(NeutralRelationBatch.toDiagonal(m, shape, packed, mask)) }))
        assertTrue(checkNotNull(packet).protected)
        val restored = checkNotNull(NeutralRelationBatch.fromDiagonal(m, checkNotNull(packet)))
        assertEquals(observations(a.decode().toList()), observations(restored.decode().toList()))
    }

    @Test fun `partial flag and nonuniform membership cells classify before scalar fallback`(): Unit = with(v) {
        val shape = m.initial(x, null, Tail.STAR, ExclusionSet.Empty, MarkSlot.STAR)
        val mixed = pack(leaf(p(), Tail.ANY, mt, Layer.DEMAND),
            leaf(p(f), Tail.ANY, mu, Layer.DEMAND)) as TaintTree
        val selected = marks(t.id, u.id)
        assertNull(NeutralRelationBatch.toDiagonal(m, shape, mixed, selected))
        val scalar = ArrayList<Pair<PremiseKey, Facts>>()
        NeutralRelationBatch.decodePacked(m, shape, mixed, selected) { pr, facts -> scalar += pr to facts }
        assertEquals(setOf(premise(tail = Tail.STAR, mark = mt) to leaf(p(), Tail.ANY, mt, Layer.DEMAND),
            premise(tail = Tail.STAR, mark = mu) to leaf(p(f), Tail.ANY, mu, Layer.DEMAND)), observations(scalar).first)

        val uniform = pack(leaf(p(), Tail.ANY, mt, Layer.DEMAND), leaf(p(), Tail.ANY, mu, Layer.DEMAND),
            leaf(p(f), Tail.ANY, mt, Layer.DEMAND), leaf(p(f), Tail.ANY, mu, Layer.DEMAND)) as TaintTree
        val partial = pack(leaf(p(f), Tail.ANY, mt, Layer.DEMAND), leaf(p(f), Tail.ANY, mu, Layer.DEMAND)) as TaintTree
        assertNull(NeutralRelationBatch.toDiagonal(m, shape, uniform.withProtection(partial.root), selected))
        assertNull(NeutralRelationBatch.toDiagonal(m, shape, pack(leaf(p(), Tail.EXACT, mt)) as TaintTree, m.markSetOf(t)))
        assertNull(NeutralRelationBatch.toDiagonal(m, shape,
            pack(leaf(p(f), Tail.ANY, mt, Layer.DEMAND, base = STATIC)) as TaintTree, m.markSetOf(t)))
    }

    private fun observations(values: List<Pair<PremiseKey, Facts>>): Pair<Set<Pair<PremiseKey, Conclusion>>, Set<Pair<PremiseKey, Conclusion>>> {
        val ordinary = values.flatMap { (pr, f) -> v.decoded(f).map { pr to it } }.toSet()
        val protected = values.flatMap { (pr, f) -> (f as? TaintTree)?.protectedPart()?.let { v.decoded(it).map { pr to it } }.orEmpty() }.toSet()
        return ordinary to protected
    }

    /** Use the existing complete FormApplier for the scalar differential control. */
    private fun scalar(values: List<Pair<InitialAp, TaintTree>>, summary: StatementSummary): List<Pair<PremiseKey, Facts>> {
        val results = ArrayList<Pair<PremiseKey, Facts>>()
        val algebra = object : FactAlgebra<PremiseKey, Facts> {
            override fun base(c: Facts) = c.base
            override fun filter(c: Facts, filter: TypeFilter) = ops.filter(c, filter)
            override fun applyEdge(me: MicroEdge, c: Facts, premise: PremiseKey, statementEdge: Boolean, out: (PremiseKey, Facts) -> Unit) {
                ops.applyEdge(c, premise, me.edge, statementEdge, mode, object : ApOut {
                    override fun result(f: Facts) = out(premise, f)
                    override fun markRequest(mark: TaintMark) = fail("Neutral control cannot request a mark")
                }, may = me.may)
            }
            override fun conjunction(cj: ConjunctiveEdge, premise: PremiseKey, c: Facts, node: CommonInst, out: (PremiseKey, Facts) -> Unit) = fail("No conjunction")
            override fun allowsSource(node: CommonInst, me: MicroEdge) = false
            override fun sourceHit(node: CommonInst, me: MicroEdge) = fail("No source")
        }
        val applier = FormApplier(algebra)
        for ((pr, facts) in values) applier.statement(summary, pr, facts, Place(node, true, false),
            sink = { premise, result -> ops.limit(result, mode.fieldLimit, object : ApOut {
                override fun result(f: Facts) { results += premise to f }
                override fun markRequest(mark: TaintMark) = fail("No limit request")
            }) }, untouched = { premise, result -> results += premise to result })
        return results
    }
}

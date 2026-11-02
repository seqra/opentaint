package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.engine.Target
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.BlockScope
import org.opentaint.dataflow.bidi.store.Record
import org.opentaint.dataflow.graph.BlockId
import org.opentaint.dataflow.graph.PortId
import kotlin.test.*

class LoopConsumerObservationTest {
    private val fixture = StoreFixtures()
    private val ap = fixture.manager
    private val ops = fixture.ops
    private val x = AccessPathBase.Argument(0)
    private val ret = AccessPathBase.Return
    private val f = fixture.field("f")
    private val g = fixture.field("g")
    private val t = MarkSlot.Concrete(fixture.mark("T"))
    private val u = MarkSlot.Concrete(fixture.mark("U"))
    private val scope = BlockScope(BlockId(2), PortId(4))
    private val mode = ApMode(false, Direction.FORWARD, 5)

    private fun views(
        records: List<LoopObservedRecord> = emptyList(),
        targets: List<LoopObservedTarget> = emptyList(),
        adjacent: (Facts) -> Set<AdmittedInitial> = { emptySet() },
        repeat: (Facts) -> Set<AdmittedInitial> = { emptySet() },
        intersect: (PortId, PremiseKey, Facts) -> List<Facts> = { _, _, f -> listOf(f) },
        acceptTarget: Boolean = false,
        targetSaved: Boolean = false,
        root: Boolean = false,
        publicBase: (AccessPathBase) -> Boolean = { true },
    ) = LoopConsumerViews(scope, root, adjacent, repeat, { records.asSequence() }, { _, _ -> targets.asSequence() },
        intersect, { _, _ -> acceptTarget }, { _, _ -> targetSaved }, publicBase)

    @Test
    fun `observer exhausts all three consumers and preserves original scope and actual exit`() {
        val original = ap.initial(fixture.pattern(x, mark = t))
        val row = Record(fixture.method, Direction.FORWARD, original, fixture.fact(ret, mark = t))
        var nextCalls = 0
        var repeatCalls = 0
        val expected = AdmittedInitial(original, Layer.NORMAL)
        val observer = LoopConsumerObservation(ops, mode, views(
            records = listOf(LoopObservedRecord(row, PortId(10)), LoopObservedRecord(row, PortId(11))),
            adjacent = { nextCalls++; setOf(expected) }, repeat = { repeatCalls++; setOf(expected) }))
        val observed = observer.observe(original, fixture.fact(x, mark = t))
        assertEquals(setOf(expected), observed.adjacentInitials)
        assertEquals(setOf(expected), observed.repeatInitials)
        assertEquals(1, nextCalls)
        assertEquals(1, repeatCalls)
        val full = observed.enclosingResults.map { it as LoopEnclosingResult.Data }
        assertEquals(setOf(PortId(10), PortId(11)), full.map { it.exit }.toSet())
        assertTrue(full.all { it.scope == scope && it.original === original })
    }

    @Test
    fun `enclosing C5 sees the complete normalized FLOW pair`() {
        val exactOriginal = ap.initial(fixture.pattern(x, tail = Tail.EXACT, mark = MarkSlot.STAR))
        val savedInitial = ap.initial(fixture.pattern(x, tail = Tail.STAR, mark = MarkSlot.STAR))
        val row = Record(fixture.method, Direction.FORWARD, savedInitial,
            fixture.fact(ret, tail = Tail.STAR, mark = MarkSlot.STAR))
        var called = false
        val observer = LoopConsumerObservation(ops, mode, views(records = listOf(LoopObservedRecord(row, PortId(9))),
            intersect = { exit, initial, result ->
                called = true
                assertEquals(PortId(9), exit)
                assertEquals(Tail.STAR, (initial as InitialAp).tail)
                assertEquals(Tail.STAR, (result as FlowTree).tail)
                listOf(result)
            }))
        val observation = observer.observe(exactOriginal, fixture.fact(x, tail = Tail.EXACT, mark = MarkSlot.STAR))
        assertTrue(called)
        val data = observation.enclosingResults.single() as LoopEnclosingResult.Data
        assertEquals(Tail.STAR, (data.original as InitialAp).tail)
        assertEquals(Tail.STAR, data.member.pattern.fact.tail)
    }

    @Test
    fun `internal local summaries survive while public root filter remains in force`() {
        val initial = ap.initial(fixture.pattern(x, mark = t))
        val local = AccessPathBase.LocalVar.create(12)
        val row = Record(fixture.method, Direction.FORWARD, initial, fixture.fact(local, mark = t))
        val records = listOf(LoopObservedRecord(row, PortId(9)))
        val publicOnly: (AccessPathBase) -> Boolean = { it !is AccessPathBase.LocalVar }
        val input = fixture.fact(x, mark = t)
        val internal = LoopConsumerObservation(ops, mode, views(records, publicBase = publicOnly)).observe(initial, input)
        val public = LoopConsumerObservation(ops, mode, views(records, root = true, publicBase = publicOnly)).observe(initial, input)
        assertFalse(internal.isEmpty)
        assertTrue(public.isEmpty)
    }

    @Test
    fun `structural native candidates with wrong marks or excluded fields cannot create an image`() {
        val initial = ap.initial(fixture.pattern(x, tail = Tail.ANY_TAINT, mark = t,
            exclusion = ExclusionSet.of(f)))
        val record = Record(fixture.method, Direction.FORWARD, initial, fixture.fact(ret, mark = t))
        val observer = LoopConsumerObservation(ops, mode, views(records = listOf(LoopObservedRecord(record, PortId(9)))))
        assertTrue(observer.observe(ap.zero, fixture.fact(x, mark = u)).isEmpty)
        assertTrue(observer.observe(ap.zero, fixture.fact(x, listOf(f), Tail.ANY_TAINT, t)).isEmpty)
        val wrongBase = Record(fixture.method, Direction.FORWARD,
            ap.initial(fixture.pattern(ret, mark = t)), fixture.fact(ret, mark = t))
        assertTrue(LoopConsumerObservation(ops, mode, views(records = listOf(LoopObservedRecord(wrongBase, PortId(9)))))
            .observe(ap.zero, fixture.fact(x, mark = t)).isEmpty)
    }

    @Test
    fun `backward source image retains typed Target and paired target admission`() {
        val source = Record(fixture.method, Direction.FORWARD, ap.zero, fixture.fact(ret, mark = t))
        val original = ap.initial(fixture.pattern(ret, mark = t))
        val input = fixture.fact(ret, mark = t)
        val backward = ApMode(false, Direction.BACKWARD, 5)
        val records = listOf(LoopObservedRecord(source, PortId(9)))
        assertTrue(LoopConsumerObservation(ops, backward, views(records, acceptTarget = false)).observe(original, input).isEmpty)
        val accepted = LoopConsumerObservation(ops, backward, views(records, acceptTarget = true)).observe(original, input)
        assertEquals(setOf<LoopEnclosingResult>(LoopEnclosingResult.Terminal(scope, PortId(9), original,
            Target.DemandTarget)), accepted.enclosingResults)
    }

    @Test
    fun `saved NormalTarget query keeps existing normal support and suppression rules`() {
        val initial = ap.initial(fixture.pattern(x, mark = t))
        val report = Target.NormalTarget(ReportId(6))
        val target = LoopObservedTarget(TargetSummary(initial, report), 0, PortId(9))
        val input = fixture.fact(x, mark = t)
        assertFalse(LoopConsumerObservation(ops, mode, views(targets = listOf(target))).observe(ap.zero, input).isEmpty)
        assertTrue(LoopConsumerObservation(ops, mode, views(targets = listOf(target), targetSaved = true)).observe(ap.zero, input).isEmpty)
        assertTrue(LoopConsumerObservation(ops, mode, views(targets = listOf(target))).observe(ap.zero,
            input.withLayer(Layer.DEMAND)).isEmpty)
        val backward = ApMode(false, Direction.BACKWARD, 5)
        assertTrue(LoopConsumerObservation(ops, backward, views(targets = listOf(target))).observe(ap.zero, input).isEmpty)
        val zero = LoopObservedTarget(TargetSummary(ap.zero, report), 0, PortId(9))
        assertTrue(LoopConsumerObservation(ops, mode, views(targets = listOf(zero))).observe(ap.zero, Reach.NORMAL).isEmpty)
    }

    @Test
    fun `a protected native image wins over its plain duplicate in complete observation`() {
        val initial = ap.initial(fixture.pattern(x, mark = t))
        val result = fixture.fact(ret, listOf(g), mark = t) as TaintTree
        val plain = Record(fixture.method, Direction.FORWARD, initial, result)
        val protected = Record(fixture.method, Direction.FORWARD, initial, result.withProtection(result.root))
        val records = listOf(LoopObservedRecord(plain, PortId(9)), LoopObservedRecord(protected, PortId(9)))
        val signature = LoopConsumerObservation(ops, mode, views(records)).observe(initial, fixture.fact(x, mark = t))
        val member = (signature.enclosingResults.single() as LoopEnclosingResult.Data).member
        assertTrue(member.nonSubsumable)
        assertEquals(listOf(g), member.pattern.fact.path)
    }
}

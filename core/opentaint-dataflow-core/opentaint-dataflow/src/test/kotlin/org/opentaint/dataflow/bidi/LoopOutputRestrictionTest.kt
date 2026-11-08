package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.BlockScope
import org.opentaint.dataflow.graph.BlockId
import org.opentaint.dataflow.graph.PortId
import kotlin.test.*

class LoopOutputRestrictionTest {
    private val fixture = StoreFixtures()
    private val ap = fixture.manager
    private val ops = fixture.ops
    private val gate = LoopOutputRestriction(ops)
    private val x = AccessPathBase.Argument(0)
    private val f = fixture.field("f")
    private val g = fixture.field("g")
    private val h = fixture.field("h")
    private val t = MarkSlot.Concrete(fixture.mark("T"))
    private val u = MarkSlot.Concrete(fixture.mark("U"))
    private val policy = RestrictedInitialPolicy(3, 10, Direction.FORWARD, ap.marks)
    private val growingInitial = ap.initial(fixture.pattern(x, tail = Tail.STAR, mark = MarkSlot.STAR))
    private val growingOutput = fixture.pattern(x, listOf(f), Tail.STAR, MarkSlot.STAR)

    private fun admissions(demand: Pattern, actual: Facts): Set<AdmittedInitial> = ops.leaves(actual).mapNotNull { leaf ->
        policy.emitAdmission(demand, leaf, actual.layer)?.let { AdmittedInitial(ap.initial(it.pattern), it.layer) }
    }.toSet()

    private fun observation(vararg adjacent: AdmittedInitial): LoopObservation<String> =
        LoopObservation(adjacent.toList(), emptyList(), emptyList())

    @Test
    fun `strict shape uses stored accessors and zero depth rather than applied suffix depth`() {
        val element = ap.accessors.index(ElementAccessor)
        val clazz = ap.accessors.index(ClassStaticAccessor("C"))
        assertEquals(0, loopFieldLength(ap.zero))
        assertEquals(0, loopFieldLength(ap.initial(fixture.pattern(STATIC, listOf(clazz), Tail.STAR, MarkSlot.STAR))))
        assertEquals(2, loopFieldLength(fixture.pattern(x, listOf(clazz, f, element))))
        assertTrue(loopSummaryGrows(ap.zero, fixture.pattern(x, listOf(f))))
        val shrinking = ap.initial(fixture.pattern(x, listOf(f), Tail.STAR, MarkSlot.STAR))
        val applied = fixture.fact(x, listOf(f, f, f), mark = t)
        assertFalse(loopSummaryGrows(shrinking, fixture.pattern(x, tail = Tail.STAR, mark = MarkSlot.STAR)))
        val kept = gate.restrict(false, shrinking, fixture.pattern(x, tail = Tail.STAR, mark = MarkSlot.STAR), applied) {
            error("A shrinking body does not query an unsatisfied adjacent consumer")
            @Suppress("UNREACHABLE_CODE") observation()
        }
        assertSame(applied, kept.single())
    }

    @Test
    fun `own ZERO summary bypasses the extra gate even with no DATA consumer`() {
        val raw = fixture.fact(x, listOf(f, f, f), mark = t)
        val kept = gate.restrict(false, ap.zero, fixture.pattern(x, listOf(f, f, f), mark = t), raw) {
            error("An own-ZERO result keeps its saved NORMAL repeat continuation")
            @Suppress("UNREACHABLE_CODE") observation()
        }
        assertSame(raw, kept.single())
        assertEquals(1L, gate.statistics.bypasses)
        assertEquals(0L, gate.statistics.observations)
    }

    @Test
    fun `native C2 keeps its first-field image while the raw binary path is cut`() {
        val demand = fixture.pattern(x, tail = Tail.ANY, mark = t)
        val raw = fixture.fact(x, listOf(f, g, h), mark = t)
        val expectedImage = admissions(demand, raw)
        assertEquals(Tail.STAR, expectedImage.single().initial.tail)
        val kept = gate.restrict(false, growingInitial, growingOutput, raw) { candidate ->
            LoopObservation(admissions(demand, candidate), emptyList<String>(), emptyList())
        }.single()
        assertEquals(listOf(f), ops.leaves(kept).single().fact.path)
        assertEquals(Tail.ANY, ops.leaves(kept).single().fact.tail)
        assertEquals(Layer.DEMAND, kept.layer)
        assertEquals(expectedImage, admissions(demand, kept))
        assertEquals(1L, gate.statistics.cuts)
    }

    @Test
    fun `next-body demand retains a source value which adjacent and enclosing consumers reject`() {
        // sourceFF(x); x=x.f; sinkRootT(x): the first body leaves x.f/T for the next read.
        val raw = fixture.fact(x, listOf(f), mark = t)
        val bodyDemand = fixture.pattern(x, listOf(f), Tail.ANY, t)
        val result = gate.restrict(false, growingInitial, fixture.pattern(x, listOf(f), mark = t), raw) { candidate ->
            LoopObservation(emptyList(), emptyList<String>(), admissions(bodyDemand, candidate))
        }
        assertEquals(raw, result.single())
        assertEquals(0L, gate.statistics.drops)
    }

    @Test
    fun `one positive family cannot hide a different image required by another family`() {
        val raw = fixture.fact(x, listOf(f, g, h), mark = t)
        val adjacent = fixture.pattern(x, tail = Tail.ANY, mark = t)
        val repeat = fixture.pattern(x, listOf(f), Tail.ANY, t)
        val kept = gate.restrict(false, growingInitial, growingOutput, raw) { candidate ->
            LoopObservation(admissions(adjacent, candidate), emptyList<String>(), admissions(repeat, candidate))
        }.single()
        assertEquals(listOf(f, g), ops.leaves(kept).single().fact.path)
        assertEquals(Tail.ANY, ops.leaves(kept).single().fact.tail)
        assertEquals(2L, gate.statistics.trials)
    }

    @Test
    fun `rejected precise fact is dropped without manufacturing a wider match`() {
        val raw = fixture.fact(x, listOf(f), mark = t)
        val demand = fixture.pattern(x, listOf(f, g), Tail.ANY, t)
        val kept = gate.restrict(false, growingInitial, fixture.pattern(x, listOf(f), mark = t), raw) { candidate ->
            LoopObservation(admissions(demand, candidate), emptyList<String>(), emptyList())
        }
        assertTrue(kept.isEmpty())
        assertEquals(1L, gate.statistics.observations)
        assertEquals(0L, gate.statistics.trials)
        assertEquals(1L, gate.statistics.drops)
    }

    @Test
    fun `normal exact admission requires the raw fallback instead of a demand witness`() {
        val raw = fixture.fact(x, listOf(f, g), mark = t)
        val demand = fixture.pattern(x, listOf(f, g), mark = t)
        assertEquals(Layer.NORMAL, admissions(demand, raw).single().layer)
        val kept = gate.restrict(false, growingInitial, growingOutput, raw) { candidate ->
            LoopObservation(admissions(demand, candidate), emptyList<String>(), emptyList())
        }.single()
        assertEquals(raw, kept)
        assertEquals(Layer.NORMAL, kept.layer)
        assertEquals(1L, gate.statistics.rawFallbacks)
    }

    @Test
    fun `run1 and a real non-growing ND arm bypass only the new gate`() {
        val raw = fixture.fact(x, listOf(f, g), mark = t)
        assertSame(raw, gate.restrict(true, growingInitial, growingOutput, raw) {
            error("run-1 has no previous demand")
            @Suppress("UNREACHABLE_CODE") observation()
        }.single())
        val short = ap.initial(fixture.pattern(x, mark = t))
        val long = ap.initial(fixture.pattern(x, listOf(f, g), mark = u))
        val nd = ap.premiseOf(listOf(short, long))
        assertSame(raw, gate.restrict(false, nd, fixture.pattern(x, listOf(f), mark = t), raw) {
            error("A real non-growing metadata arm retains this already complete result")
            @Suppress("UNREACHABLE_CODE") observation()
        }.single())
    }

    @Test
    fun `packed protection is clipped per membership and transported to the chosen prefix`() {
        val protected = fixture.fact(x, listOf(f, g, h), mark = t) as TaintTree
        val plain = fixture.fact(x, listOf(g, f, h), mark = u) as TaintTree
        val root = ap.taintAlg.mergeAdd(protected.root, plain.root, ap.cancellation)
        val packet = ap.taintTree(x, Layer.NORMAL, root, nonSubsumable = protected.root)
        val original = LoopObservedFacts(ops).also { it.add(packet) }.freeze()
        assertEquals(2, original.size)
        assertEquals(setOf(t), original.filter { it.nonSubsumable }.map { it.pattern.fact.mark }.toSet())
        val signal = AdmittedInitial(ap.initial(fixture.pattern(x, mark = t)), Layer.DEMAND)
        val kept = gate.restrict(false, growingInitial, growingOutput, packet) { observation(signal) }
        assertEquals(2, kept.size)
        val frozen = LoopObservedFacts(ops).also { collector -> kept.forEach(collector::add) }.freeze()
        assertEquals(setOf(t), frozen.filter { it.nonSubsumable }.map { it.pattern.fact.mark }.toSet())
        assertTrue(frozen.all { it.pattern.fact.path.size == 1 && it.pattern.fact.tail == Tail.ANY && it.layer == Layer.DEMAND })
    }

    @Test
    fun `flow prefix cuts preserve mark exclusions and clear field exclusions`() {
        val mx = MarkSlot.Star(ap.markSetOf(fixture.mark("U")))
        val raw = fixture.fact(x, listOf(f, g, h), Tail.STAR, mx, ExclusionSet.of(g))
        val signal = AdmittedInitial(growingInitial, Layer.NORMAL)
        val kept = gate.restrict(false, growingInitial, growingOutput, raw) { observation(signal) }.single() as FlowTree
        assertEquals(mx.excluded, kept.markExclusion)
        assertEquals(ExclusionSet.Empty, kept.exclusion)
        assertEquals(Tail.ANY, kept.tail)
        assertEquals(Layer.DEMAND, kept.layer)
    }

    @Test
    fun `frozen observations retain both protection classes while exact same-class duplicates deduplicate`() {
        val raw = fixture.fact(x, listOf(f), mark = t) as TaintTree
        val protected = raw.withProtection(raw.root)
        assertNotEquals(raw, protected, "Retained fact equality includes the protection membership")
        val plainSignature = LoopObservedFacts(ops).also { it.add(raw) }.freeze()
        val union = LoopObservedFacts(ops).also { it.add(raw); it.add(protected); it.add(raw) }.freeze()
        assertNotEquals(plainSignature, union)
        assertEquals(2, union.size)
        assertEquals(setOf(false, true), union.map { it.nonSubsumable }.toSet())
        val reverse = LoopObservedFacts(ops).also { it.add(protected); it.add(raw); it.add(protected) }.freeze()
        assertEquals(union, reverse, "Either arrival order preserves both independent classes")
        val source = arrayListOf(AdmittedInitial(growingInitial, Layer.NORMAL))
        val frozen = LoopObservation(source, union, emptyList())
        source.clear()
        assertEquals(1, frozen.adjacentInitials.size)
    }

    @Test
    fun `binary path family has two retained first-field images before the next body`() {
        val demand = fixture.pattern(x, tail = Tail.ANY, mark = t)
        val inputs = (0 until 16).map { bits ->
            (0 until 4).map { bit -> if (bits and (1 shl bit) == 0) f else g }
        }
        val results = LoopObservedFacts(ops)
        for (path in inputs) {
            val raw = fixture.fact(x, path, mark = t)
            for (kept in gate.restrict(false, growingInitial, fixture.pattern(x, path, mark = t), raw) { value ->
                LoopObservation(emptyList(), emptyList<String>(), admissions(demand, value))
            }) results.add(kept)
        }
        val retained = results.freeze()
        assertEquals(setOf(listOf(f), listOf(g)), retained.map { it.pattern.fact.path }.toSet())
        assertEquals(2, retained.size)
        assertTrue(retained.all { it.layer == Layer.DEMAND && it.pattern.fact.tail == Tail.ANY })
        assertEquals(16L, gate.statistics.cuts)
    }

    @Test
    fun `a static prefix cut retains the complete named field anchor`() {
        val clazz = ap.accessors.index(ClassStaticAccessor("C"))
        val raw = fixture.fact(STATIC, listOf(clazz, f, g, h), mark = t)
        val demand = fixture.pattern(STATIC, listOf(clazz, f), Tail.ANY, t)
        val kept = gate.restrict(false, growingInitial, fixture.pattern(STATIC, listOf(clazz, f), mark = t), raw) { value ->
            LoopObservation(admissions(demand, value), emptyList<String>(), emptyList())
        }.single()
        assertEquals(listOf(clazz, f, g), ops.leaves(kept).single().fact.path)
        assertEquals(Tail.ANY, ops.leaves(kept).single().fact.tail)
        assertEquals(Layer.DEMAND, kept.layer)
    }

    @Test
    fun `equal AP admissions at different entry ports are distinct observations`() {
        val admitted = AdmittedInitial(growingInitial, Layer.NORMAL)
        val first = LoopLabelledAdmission(BlockScope(BlockId(2), PortId(5)), LoopAdmissionFamily.ADJACENT, admitted)
        val otherPort = first.copy(scope = BlockScope(BlockId(2), PortId(6)))
        val otherFamily = first.copy(family = LoopAdmissionFamily.REPEAT)
        fun seen(value: LoopLabelledAdmission) = LoopObservation<String>(emptyList(), emptyList(), emptyList(), listOf(value))
        assertFalse(seen(first).isEmpty)
        assertNotEquals(seen(first), seen(otherPort))
        assertNotEquals(seen(first), seen(otherFamily))
    }
}

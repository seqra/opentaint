package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.engine.Target
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.DemandStore
import org.opentaint.dataflow.bidi.store.Record
import kotlin.test.*

class LocalRelationApplicationTest {
    private val fixture = StoreFixtures()
    private val ap = fixture.manager
    private val ops = fixture.ops
    private val x = AccessPathBase.Argument(0)
    private val y = AccessPathBase.Argument(1)
    private val ret = AccessPathBase.Return
    private val f = fixture.field("f")
    private val g = fixture.field("g")
    private val h = fixture.field("h")
    private val j = fixture.field("j")
    private val k = fixture.field("k")
    private val t = MarkSlot.Concrete(fixture.mark("T"))
    private val u = MarkSlot.Concrete(fixture.mark("U"))
    private val mode = ApMode(false, Direction.FORWARD, 10)
    private val application = LocalRelationApplication(ops, mode)

    private class Output : LocalRelationOut {
        val data = ArrayList<Pair<PremiseKey, Facts>>()
        val targets = ArrayList<Pair<PremiseKey, Target>>()
        val requests = ArrayList<TaintMark>()
        override fun data(original: PremiseKey, value: Facts) { data += original to value }
        override fun target(original: PremiseKey, target: Target) { targets += original to target }
        override fun markRequest(mark: TaintMark) { requests += mark }
    }

    @Test
    fun `local saved replay retains the complete parent original and applies its real suffix`() {
        val original = ap.initial(fixture.pattern(y, mark = t))
        val initial = ap.initial(fixture.pattern(x, listOf(f), Tail.STAR, MarkSlot.STAR))
        val row = Record(fixture.method, Direction.FORWARD, initial, fixture.fact(ret, tail = Tail.STAR, mark = MarkSlot.STAR))
        val out = Output()
        assertTrue(application.applyRecord(fixture.fact(x, listOf(f, g, h), mark = t), original, row, out))
        assertSame(original, out.data.single().first)
        val result = out.data.single().second
        assertEquals(fixture.pattern(ret, listOf(g, h), mark = t), ops.leaves(result).single())
        assertEquals(Layer.NORMAL, result.layer)
        assertTrue(out.targets.isEmpty())
        assertTrue(out.requests.isEmpty())
    }

    @Test
    fun `T to U to T cycle retains exact original protection across a local boundary`() {
        val original = ap.initial(fixture.pattern(y, mark = t))
        val trigger = ap.initial(fixture.pattern(x, mark = u))
        val out = Output()
        assertTrue(application.applyCurrent(fixture.fact(x, mark = u), original, trigger,
            fixture.fact(ret, mark = t), out))
        val result = out.data.single().second as TaintTree
        assertNotNull(result.nonSubsumable)
        assertSame(original, out.data.single().first)
    }

    @Test
    fun `native must definite lane stays normal and its provisional lane commits demand at the boundary`() {
        val initial = ap.initial(fixture.pattern(x, tail = Tail.ANY_TAINT, mark = t))
        val record = Record(fixture.method, Direction.FORWARD, initial, fixture.fact(ret, mark = u))
        val normal = Output()
        assertTrue(application.applyRecord(fixture.fact(x, tail = Tail.ANY_TAINT, mark = t), initial, record, normal))
        assertTrue(normal.data.isNotEmpty())
        assertTrue(normal.data.all { it.second.layer == Layer.NORMAL })

        val provisional = Output()
        val exactOriginal = ap.initial(fixture.pattern(x, mark = t))
        application.applyRecord(fixture.fact(x, listOf(f), Tail.ANY_TAINT, t), exactOriginal, record, provisional)
        assertTrue(provisional.data.isNotEmpty())
        assertTrue(provisional.data.all { it.second.layer == Layer.DEMAND })
        // An exact point cannot become a uniform NORMAL witness just by crossing an internal block.
        assertFalse(provisional.data.any { it.second.layer == Layer.NORMAL })
    }

    @Test fun `one saved native match and MUST split is reused across every output scalar`() {
        val initial = ap.initial(fixture.pattern(x, tail = Tail.ANY_TAINT, mark = t))
        val packed = ap.mergeAddDelta(fixture.fact(ret,listOf(f),mark=u),fixture.fact(ret,listOf(g),mark=u)).first
        val whole = Record(fixture.method,Direction.FORWARD,initial,packed)
        val actual = fixture.fact(x,listOf(f),Tail.ANY_TAINT,t)
        val original = ap.initial(fixture.pattern(y,mark=t))
        val lanes = assertNotNull(application.matchRecord(actual,original,whole))
        assertTrue(lanes.any { it.pendingDemotion })
        val expected = Output()
        val selected = Output()
        for (scalar in annotatedLoopScalars(ops,packed)) {
            val row = Record(fixture.method,Direction.FORWARD,initial,scalar)
            application.applyRecord(actual,original,row,expected)
            application.applyMatchedRecord(lanes,original,row,selected)
        }
        assertEquals(expected.data,selected.data)
        assertEquals(expected.targets,selected.targets)
        assertEquals(expected.requests,selected.requests)
        assertTrue(selected.data.all { it.second.layer == Layer.DEMAND })
    }

    @Test
    fun `reverse source discharge becomes DemandTarget while zero-to-zero stays control data`() {
        val backward = LocalRelationApplication(ops, ApMode(false, Direction.BACKWARD, 10))
        val original = ap.initial(fixture.pattern(ret, mark = t))
        val source = RecordLeafView(fixture.pattern(ret, mark = t),
            Conclusion(ap.zero.toPattern().fact, ExclusionSet.Empty, demand = false))
        val out = Output()
        assertTrue(backward.applyRecordView(fixture.fact(ret, mark = t), original, source, false, out))
        assertTrue(out.data.isEmpty())
        assertEquals(listOf<Pair<PremiseKey, Target>>(original to Target.DemandTarget), out.targets)

        val zero = Output()
        backward.applyRecordView(Reach.NORMAL, ap.zero, RecordLeafView(ap.zero.toPattern(),
            Conclusion(ap.zero.toPattern().fact, ExclusionSet.Empty, demand = false)), false, zero)
        assertEquals(listOf<Pair<PremiseKey, Facts>>(ap.zero to Reach.NORMAL), zero.data)
        assertTrue(zero.targets.isEmpty())
    }

    @Test
    fun `normal targets need normal support and never run backward`() {
        val initial = ap.initial(fixture.pattern(x, mark = t))
        val target = Target.NormalTarget(ReportId(3))
        assertEquals(Layer.NORMAL, application.targetArmLayer(fixture.fact(x, mark = t), initial, target, saved = true))
        assertNull(application.targetArmLayer(fixture.fact(x, mark = t, layer = Layer.DEMAND), initial, target, saved = true))
        val backward = LocalRelationApplication(ops, ApMode(false, Direction.BACKWARD, 10))
        assertNull(backward.targetArmLayer(fixture.fact(x, mark = t), initial, target, saved = true))
        assertEquals(Layer.DEMAND, application.targetArmLayer(fixture.fact(x, mark = t, layer = Layer.DEMAND), initial,
            Target.DemandTarget, saved = false))
    }

    @Test
    fun `run1 static-origin local effects retain the existing demand approximation`() {
        val clazz = ap.accessors.index(ClassStaticAccessor("C"))
        val initial = ap.initial(fixture.pattern(STATIC, listOf(clazz, f), Tail.STAR, MarkSlot.STAR))
        val raw = fixture.fact(STATIC, listOf(clazz, f), Tail.STAR, MarkSlot.STAR, layer = Layer.DEMAND)
        val run1 = LocalRelationApplication(ops, ApMode(true, Direction.FORWARD, 1))
        val out = Output()
        run1.applyMatched(raw, initial, initial, fixture.fact(x, tail = Tail.STAR, mark = MarkSlot.STAR), out)
        assertTrue(out.data.isNotEmpty())
        assertTrue(out.data.all { it.second.layer == Layer.DEMAND })
        assertSame(initial, out.data.single().first)
    }

    @Test
    fun `complete ND transfer keeps both originals and inherited protection`() {
        val i1 = ap.initial(fixture.pattern(x, mark = t))
        val i2 = ap.initial(fixture.pattern(y, mark = u))
        val a = fixture.fact(x, mark = t) as TaintTree
        val b = fixture.fact(y, mark = u) as TaintTree
        val output = Output()
        application.applyCombination(listOf(LocalRelationBinding(i1, i1, a.withProtection(a.root)),
            LocalRelationBinding(i2, i2, b)), fixture.fact(ret, mark = t) as TaintTree, output)
        assertEquals(setOf(i1, i2), output.data.single().first.members.toSet())
        assertNotNull((output.data.single().second as TaintTree).nonSubsumable)
        assertFailsWith<IllegalArgumentException> {
            application.applyCombination(listOf(LocalRelationBinding(i1, i1, a)), fixture.fact(ret, mark = t) as TaintTree, Output())
        }
    }

    @Test
    fun `loop observation preserves native suffix composition and full paired C5 limit`() {
        val original = ap.zero
        val afterInitial = ap.initial(fixture.pattern(x, listOf(f), Tail.STAR, MarkSlot.STAR))
        val after = Record(fixture.method, Direction.FORWARD, afterInitial,
            fixture.fact(ret, tail = Tail.STAR, mark = MarkSlot.STAR))
        val exit = fixture.pattern(ret, listOf(g), Tail.ANY, t)
        val demand = DemandStore.Builder(ap).also { it.add(fixture.method, DemandPattern(ap.zero.toPattern(), exit)) }.build()
        val policy = RestrictedInitialPolicy(3, 10, Direction.FORWARD, ap.marks)
        val raw = fixture.fact(x, listOf(f, g, h, j, k), mark = t)
        fun observe(value: Facts): LoopObservation<LoopObservedMember> {
            val out = Output()
            application.applyRecord(value, original, after, out)
            val full = LoopObservedFacts(ops)
            for ((parentOriginal, result) in out.data) {
                assertSame(original, parentOriginal)
                demand.intersect(fixture.method, parentOriginal, result, policy).forEach(full::add)
            }
            return LoopObservation(emptyList(), full.freeze(), emptyList())
        }
        val baseline = observe(raw)
        assertFalse(baseline.isEmpty)
        val growing = ap.initial(fixture.pattern(x, tail = Tail.STAR, mark = MarkSlot.STAR))
        val kept = LoopOutputRestriction(ops).restrict(false, growing,
            fixture.pattern(x, listOf(f), Tail.STAR, MarkSlot.STAR), raw, ::observe).single()
        assertEquals(baseline, observe(kept))
        assertEquals(listOf(f, g, h), ops.leaves(kept).single().fact.path)
        assertEquals(Tail.ANY, ops.leaves(kept).single().fact.tail)
    }
}

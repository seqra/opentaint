package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.fixtures.PipelineFixtures
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.store.*
import kotlin.test.*

/** Adapter controls for the all-run flag and record contracts of the constructive model. */
class CorrelatedConcreteEngineTest {
    private val fixture = StoreFixtures()
    private val m = fixture.manager
    private val ops = fixture.ops
    private val v = StoreValues(fixture)

    @Test fun `same atom assignment and selected cleaner protection have no phase gate`(): Unit = with(v) {
        for (mode in listOf(ApMode(false, Direction.FORWARD, 2), ApMode(false, Direction.BACKWARD, 1),
            ApMode(true, Direction.FORWARD, 1, markMode = MarkMode.GROUP))) {
            val atom = m.marks.runtimeAtom(t, mode.markMode)
            val input = fixture.fact(mark = MarkSlot.Concrete(atom)) as TaintTree
            val initial = m.initial(fixture.pattern(mark = MarkSlot.Concrete(atom)))
            val edge = PathEdge(fixture.pattern(mark = mt).fact,
                fixture.pattern(base = y, mark = mt).fact, ExclusionSet.Empty)
            val out = CollectingOut()
            ops.applyEdge(input, initial, edge, false, mode, out, ruleAssignment = true)
            assertTrue(out.results.isNotEmpty(), "$mode")
            assertTrue(out.results.all { it is TaintTree && it.nonSubsumable != null }, "$mode")
            val cleaned = CollectingOut()
            ops.clean(input, initial, Cleaner(x, m.path(p(f)), CleanReach.AT_AND_BELOW, t), mode, cleaned)
            assertNotNull((cleaned.results.single() as TaintTree).nonSubsumable, "$mode")
        }
    }

    @Test fun `normal FLOW record retains input and output exclusions and reverses both`(): Unit = with(v) {
        val initial = premise(tail = Tail.STAR, mark = MarkSlot.STAR, e = ex(f))
        val output = fixture.fact(base = y, tail = Tail.STAR, mark = MarkSlot.STAR, exclusion = ex(g))
        val summaries = RunSummaryStore(m, flowBacked = true)
        assertNotNull(summaries.add(initial, output))
        val records = PersistentRecordStore(m)
        records.persist(Direction.FORWARD, sequenceOf(fixture.method to summaries))
        val record = records.byEntry(fixture.method, initial.toPattern()).single()
        assertEquals(ex(f), record.premise.exclusion)
        assertEquals(ex(g), (record.conclusion as FlowTree).exclusion)
        val views = ArrayList<RecordLeafView>()
        record.forEachReversedAt(fixture.pattern(base = y, tail = Tail.STAR, mark = MarkSlot.STAR)) { view, flag ->
            assertFalse(flag)
            views += view
        }
        val reversed = views.single()
        assertEquals(ex(f, g), reversed.result.exclusion)
        assertEquals(ExclusionSet.Empty, reversed.premise.exclusion)
        val excludedInput = fixture.fact(path = p(f), mark = mt)
        assertNull(ops.satisfying(excludedInput, record.premise, ApMode(false, Direction.FORWARD, 2), record = true))
    }

    @Test fun `reversed native view carries the exact membership flag to actual output`(): Unit = with(v) {
        val initial = premise(mark = mt)
        val result = fixture.fact(base = y, mark = mt) as TaintTree
        val record = Record(fixture.method, Direction.FORWARD, initial, result.withProtection(result.root))
        val input = fixture.fact(base = y, mark = mt)
        var calls = 0
        record.forEachReversedAt(fixture.pattern(base = y, mark = mt)) { view, flag ->
            assertTrue(flag)
            val out = CollectingOut()
            ops.applyRecordLeaf(input, view, flag, ApMode(false, Direction.BACKWARD, 1), out, original = initial)
            assertNotNull((out.results.single() as TaintTree).nonSubsumable)
            calls++
        }
        assertEquals(1, calls)
    }

    @Test fun `subscription replay forwards a protected reversed view even after its plain view`() {
        PipelineFixtures(index = 2).use { p ->
            val mark = MarkSlot.Concrete(p.store.mark("T"))
            val initial = p.ap.initial(p.store.pattern(mark = mark))
            val conclusion = p.store.fact(base = AccessPathBase.Return, mark = mark) as TaintTree
            p.records.add(Record(p.callee, Direction.FORWARD, initial, conclusion))
            p.records.add(Record(p.callee, Direction.FORWARD, initial, conclusion.withProtection(conclusion.root)))
            val part = p.subscription(added = p.store.fact(base = AccessPathBase.Return, mark = mark))
            p.replayPersisted(part)
            assertEquals(listOf(false, true), p.views.map { it.nonSubsumable })
            assertEquals(1, p.views.map { it.view }.toSet().size,
                "Protection does not change semantic view identity")
        }
    }

    @Test fun `pool values stay independent while a selected field seed keeps STAR`(): Unit = with(v) {
        val cls = m.accessors.index(org.opentaint.dataflow.ap.ifds.ClassStaticAccessor("C"))
        val region = fixture.pattern(base = STATIC, path = p(cls, f), tail = Tail.STAR, mark = MarkSlot.STAR)
        val service = Run1StaticService(m, MarkMode.FULL)
        val value = service.facts(region, MarkSet.of(t)) as TaintTree
        assertEquals(Tail.ANY, value.anyTail)
        assertEquals(Layer.DEMAND, value.layer)
        val selected = m.initial(region.copy(fact = region.fact.copy(mark = mt)))
        assertEquals(Tail.STAR, (ops.startFact(selected) as TaintTree).anyTail)
        val exactClass = region.copy(fact = region.fact.copy(path = p(cls), tail = Tail.EXACT))
        assertEquals(Tail.EXACT, ops.leaves(service.facts(exactClass, MarkSet.of(t))).single().fact.tail)
    }

    @Test fun `late conjunction flag replays one existing binding and repeated flag is no work`(): Unit = with(v) {
        val store = ConjunctionStore(m)
        val node = fixture.inst(1)
        val a = fixture.fact(mark = mt) as TaintTree
        val b = fixture.fact(base = AccessPathBase.Argument(1), mark = mu) as TaintTree
        val ia = ConjunctionStore.Input(premise(mark = mt), Layer.NORMAL, a)
        val ib = ConjunctionStore.Input(m.initial(fixture.pattern(base = AccessPathBase.Argument(1), mark = mu)), Layer.NORMAL, b)
        assertTrue(store.add("rule", node, 2, 0, ia).isEmpty())
        val first = store.add("rule", node, 2, 1, ib).single()
        val flagged = ia.copy(facts = a.withProtection(a.root))
        val replay = store.add("rule", node, 2, 0, flagged).single()
        assertEquals(first.premise, replay.premise)
        assertNotNull((replay.inputs[0].facts as TaintTree).nonSubsumable)
        assertTrue(store.add("rule", node, 2, 0, flagged).isEmpty())
        assertTrue(store.add("rule", node, 2, 1, ib).isEmpty())
    }

    @Test fun `ND subscription annotation adds no member or product`(): Unit = with(v) {
        data class Member(val name: String) { var flag = false }
        val join = NdSummaryJoin<Member>(m, 2)
        val a = Member("a")
        val b = Member("b")
        assertTrue(join.addSubscription(0, a).isEmpty())
        assertTrue(join.addSubscription(1, b).isEmpty())
        assertEquals(1, join.addConclusion(fixture.fact(base = y, mark = mt) as TaintTree).size)
        val upgrade = Member("a").also { it.flag = true }
        fun add() = join.addSubscription(0, upgrade) { previous, incoming ->
            val fresh = incoming.flag && !previous.flag
            previous.flag = previous.flag || incoming.flag
            fresh
        }
        assertEquals(1, add().size)
        assertTrue(a.flag)
        assertEquals(2, join.memberCount)
        assertEquals(1, join.combinationCount)
        assertTrue(add().isEmpty())
    }

    @Test fun `later ND rule keeps the exact premise and propagates a late contributor flag`() {
        MethodAnalysisFixtures().use { f ->
            lateinit var service: RunMethodLocalServices
            f.core(index = 3, localFactory = MethodLocalServicesFactory { core ->
                RunMethodLocalServices(core).also { service = it }
            })
            val a = AccessPathBase.Argument(0)
            val b = AccessPathBase.Argument(1)
            val c = AccessPathBase.Return
            val t = MarkSlot.Concrete(f.store.mark("T"))
            val u = MarkSlot.Concrete(f.store.mark("U"))
            val target = MarkSlot.Concrete(f.store.mark("Fresh"))
            val pa = f.store.pattern(base = a, mark = t)
            val pb = f.store.pattern(base = b, mark = u)
            val edge = ConjunctiveEdge(listOf(pa, pb), f.store.pattern(base = c, mark = target).fact)
            val ia = f.manager.initial(pa)
            val ib = f.manager.initial(pb)
            val af = f.store.fact(base = a, mark = t) as TaintTree
            val bf = f.store.fact(base = b, mark = u)
            val results = ArrayList<Pair<PremiseKey, Facts>>()
            service.conjunction(edge, ia, af, f.inst(1)) { i, fact -> results += i to fact }
            service.conjunction(edge, ib, bf, f.inst(1)) { i, fact -> results += i to fact }
            assertEquals(setOf(ia, ib), results.single().first.members.toSet())
            assertNull((results.single().second as TaintTree).nonSubsumable)
            results.clear()
            service.conjunction(edge, ia, af.withProtection(af.root), f.inst(1)) { i, fact -> results += i to fact }
            assertEquals(setOf(ia, ib), results.single().first.members.toSet())
            assertNotNull((results.single().second as TaintTree).nonSubsumable)
            results.clear()
            service.conjunction(edge, ia, af.withProtection(af.root), f.inst(1)) { i, fact -> results += i to fact }
            assertTrue(results.isEmpty())
        }
    }
}

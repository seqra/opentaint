package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.*
import kotlin.test.*

class PreparedOutputProgramsTest {
    private val f = StoreFixtures()
    private val ap = f.manager
    private val x = AccessPathBase.Argument(0)
    private val y = AccessPathBase.Argument(1)
    private val ret = AccessPathBase.Return
    private val t = MarkSlot.Concrete(f.mark("T"))
    private val u = MarkSlot.Concrete(f.mark("U"))
    private val a = f.field("a")
    private val b = f.field("b")
    private val c = f.field("c")
    private val policy = RestrictedInitialPolicy(3, 4, Direction.FORWARD, ap.marks)

    private fun exact(expected: List<Facts>, actual: List<Facts>?) {
        assertNotNull(actual)
        // Class streams can be visited in a different order. Exact payload plus
        // protection membership is the correspondence contract; no class is lost.
        assertEquals(expected.toSet(),actual.toSet())
        assertEquals(expected.size,actual.size)
        assertEquals(expected.map { it to (it as? TaintTree)?.nonSubsumable }.toSet(),
            actual.map { it to (it as? TaintTree)?.nonSubsumable }.toSet())
    }

    @Test fun `equal accepted exits share one program after both ND entry checks`() {
        val demand = DemandStore.Builder(ap).apply {
            add(f.method, DemandPattern(f.pattern(x, mark = t), f.pattern(ret, listOf(a), Tail.ANY, t)))
            add(f.method, DemandPattern(f.pattern(y, mark = u), f.pattern(ret, listOf(a), Tail.ANY, t)))
        }.build()
        val original = ap.union(ap.initial(f.pattern(x, mark = t)), ap.initial(f.pattern(y, mark = u)))
        var checks = 0
        val plan = assertNotNull(demand.prepareDataPlan(f.method, original.members.map { it.toPattern() }, policy) { checks++ })
        assertEquals(2, checks, "Each complete paired occurrence must pass its own entry predicate")
        assertEquals(2, plan.rowChecks)
        assertEquals(1, plan.outputProgramCount, "Equal output functions must not repeat packet restriction")
        val raw = f.fact(ret, listOf(a, b, c), mark = t) as TaintTree
        exact(demand.intersect(f.method, original, raw.withProtection(raw.root), policy),
            plan.intersect(original, raw.withProtection(raw.root)))
    }

    @Test fun `rejected entries do not create executable output programs`() {
        val demand = DemandStore.Builder(ap).apply {
            add(f.method, DemandPattern(f.pattern(x, mark = u), f.pattern(ret, listOf(a), Tail.ANY, t)))
        }.build()
        val original = ap.initial(f.pattern(x, mark = t))
        val plan = assertNotNull(demand.prepareDataPlan(f.method, listOf(original.toPattern()), policy))
        assertEquals(1, plan.rowChecks)
        assertEquals(0, plan.outputProgramCount)
        assertTrue(plan.emptyForBase(ret))
        exact(emptyList(), plan.intersect(original, f.fact(ret, listOf(a), mark = t)))
    }

    @Test fun `first accepted native prefix occurrence orders programs before lower global row id`() {
        // Row 1 is at the root and is visited before row 0 at x.a.
        val demand = DemandStore.Builder(ap).apply {
            add(f.method, DemandPattern(f.pattern(x, listOf(a), Tail.ANY, t), f.pattern(ret, listOf(b), Tail.ANY, t)))
            add(f.method, DemandPattern(f.pattern(x, tail = Tail.ANY, mark = t), f.pattern(ret, listOf(a), Tail.ANY, t)))
        }.build()
        val original = ap.initial(f.pattern(x, listOf(a), mark = t))
        val raw = ap.mergeAddDelta(f.fact(ret, listOf(a), mark = t), f.fact(ret, listOf(b), mark = t)).first
        val expected = demand.intersect(f.method, original, raw, policy)
        assertEquals(listOf(listOf(a), listOf(b)), expected.map { f.ops.leaves(it).single().fact.path })
        val plan = assertNotNull(demand.prepareDataPlan(f.method, listOf(original.toPattern()), policy))
        exact(expected, plan.intersect(original, raw))
    }

    @Test fun `protected exact and uniform siblings retain independent native headers`() {
        val demand = DemandStore.Builder(ap).apply {
            add(f.method, DemandPattern(f.pattern(x, mark = t), f.pattern(ret, tail = Tail.ANY, mark = t)))
        }.build()
        val original = ap.initial(f.pattern(x, mark = t))
        val exactRoot = f.fact(ret, mark = t) as TaintTree
        val uniform = f.fact(ret, listOf(b), Tail.ANY_TAINT, t,
            exclusion = ExclusionSet.of(a)) as TaintTree
        val raw = ap.taintTree(ret, Layer.NORMAL,
            ap.taintAlg.mergeAdd(exactRoot.root, uniform.root, ap.cancellation),
            exclusion = ExclusionSet.of(a), anyTail = Tail.ANY_TAINT, nonSubsumable = exactRoot.root)
        val expected = demand.intersect(f.method, original, raw, policy)
        assertEquals(2, expected.size)
        val root = expected.first() as TaintTree
        val any = expected.last() as TaintTree
        assertEquals(ExclusionSet.Empty, root.exclusion)
        assertNotNull(root.nonSubsumable)
        assertEquals(ExclusionSet.of(a), any.exclusion)
        assertNull(any.nonSubsumable)
        val plan = assertNotNull(demand.prepareDataPlan(f.method, listOf(original.toPattern()), policy))
        exact(expected, plan.intersect(original, raw))
    }

    @Test fun `C5 concrete output selector meets allowed FLOW without changing its mark exclusions`() {
        val demand = DemandStore.Builder(ap).apply {
            add(f.method, DemandPattern(f.pattern(x, tail = Tail.ANY, mark = MarkSlot.STAR),
                f.pattern(ret, tail = Tail.ANY, mark = t)))
        }.build()
        val original = ap.initial(f.pattern(x, tail = Tail.STAR, mark = MarkSlot.STAR))
        val plan = assertNotNull(demand.prepareDataPlan(f.method, listOf(original.toPattern()), policy))
        for (excluded in listOf(u, t)) {
            val raw = f.fact(ret, listOf(a, b), Tail.STAR,
                MarkSlot.Star(ap.markSetOf(excluded.mark)))
            exact(demand.intersect(f.method, original, raw, policy), plan.intersect(original, raw))
        }
    }

    @Test fun `selected scalar reference overflow returns native fallback before any partial result`() {
        val demand = DemandStore.Builder(ap).apply {
            add(f.method, DemandPattern(f.pattern(x, mark = t), f.pattern(ret, tail = Tail.ANY, mark = t)))
        }.build()
        val original = ap.initial(f.pattern(x, mark = t))
        val leaf = ap.taintAlg.leafNode(ap.taintLeaves(ap.markSetOf(t.mark), MarkSet.EMPTY))
        var root: TaintNode? = null
        repeat(2049) { ordinal ->
            val one = ap.taintAlg.prepend(ap, ap.path(listOf(f.field("wide$ordinal"))), leaf)
            root = root?.let { ap.taintAlg.mergeAdd(it, one, ap.cancellation) } ?: one
        }
        val raw = ap.taintTree(ret, Layer.NORMAL, checkNotNull(root))
        val plan = assertNotNull(demand.prepareDataPlan(f.method, listOf(original.toPattern()), policy))
        assertTrue(demand.intersect(f.method, original, raw, policy).isNotEmpty())
        assertNull(plan.intersect(original, raw), "A bounded transpose must request native recomputation")
    }

    @Test fun `finite direct native oracle preserves mixed marks tails exclusions directions and protection`() {
        val demand = DemandStore.Builder(ap).apply {
            add(f.method, DemandPattern(f.pattern(x, tail = Tail.ANY, mark = t),
                f.pattern(ret, tail = Tail.ANY, mark = t)))
            add(f.method, DemandPattern(f.pattern(x, listOf(a), Tail.ANY, t),
                f.pattern(ret, listOf(a), Tail.STAR, MarkSlot.STAR)))
            add(f.method, DemandPattern(f.pattern(y, tail = Tail.ANY, mark = u),
                f.pattern(ret, listOf(b), Tail.EXACT, u)))
            add(f.method, DemandPattern(f.pattern(x, tail = Tail.ANY, mark = MarkSlot.STAR),
                f.pattern(ret, tail = Tail.ANY, mark = MarkSlot.STAR)))
            add(f.method, DemandPattern(f.pattern(y, tail = Tail.ANY, mark = u),
                f.pattern(ret, tail = Tail.ANY, mark = t)))
        }.build()
        val xt = ap.initial(f.pattern(x, mark = t))
        val originals = listOf(xt, ap.initial(f.pattern(x, listOf(a), mark = t)),
            ap.union(xt, ap.initial(f.pattern(y, mark = u))),
            ap.initial(f.pattern(x, tail = Tail.STAR, mark = MarkSlot.STAR)))
        val actuals = buildList {
            for (path in listOf(emptyList(), listOf(a), listOf(a,b,c), listOf(b)))
                for (mark in listOf(t,u)) for (tail in listOf(Tail.EXACT,Tail.ANY,Tail.ANY_TAINT)) {
                    val value = f.fact(ret,path,tail,mark)
                    add(value)
                    if (value is TaintTree) add(value.withProtection(value.root))
                }
            for (excluded in listOf(MarkSet.EMPTY,ap.markSetOf(t.mark)))
                add(f.fact(ret,listOf(a,b),Tail.STAR,MarkSlot.Star(excluded),exclusion=ExclusionSet.of(c)))
        }
        for (direction in Direction.entries) for (original in originals) {
            val queryPolicy = RestrictedInitialPolicy(3,4,direction,ap.marks)
            val plan = assertNotNull(demand.prepareDataPlan(f.method,original.members.map { it.toPattern() },queryPolicy))
            for (actual in actuals) exact(demand.intersect(f.method,original,actual,queryPolicy),
                plan.intersect(original,actual))
        }
    }

    @Test fun `prepared diagnostics count programs and keep bounded native row witnesses`() {
        val property = "org.opentaint.bidi.optimizationStatistics"
        val previous = System.getProperty(property)
        System.setProperty(property,"true")
        try {
            val demand = DemandStore.Builder(ap).apply {
                add(f.method,DemandPattern(f.pattern(x,mark=t),f.pattern(ret,tail=Tail.ANY,mark=t)))
                add(f.method,DemandPattern(f.pattern(y,mark=u),f.pattern(ret,tail=Tail.ANY,mark=t)))
            }.build()
            val original = ap.union(ap.initial(f.pattern(x,mark=t)),ap.initial(f.pattern(y,mark=u)))
            val plan = assertNotNull(demand.prepareDataPlan(f.method,original.members.map { it.toPattern() },policy))
            val raw = f.fact(ret,mark=t) as TaintTree
            assertNotNull(plan.intersect(original,raw.withProtection(raw.root)))
            assertNull(demand.prepareDataPlan(f.method,emptyList(),policy))
            assertNull(demand.prepareDataPlan(f.method,listOf(ap.zero.toPattern()),policy))
            assertNull(demand.prepareDataPlan(f.method,List(2049) { xt -> original.member(xt % 2).toPattern() },policy))
            assertNull(demand.prepareDataPlan(f.method,original.members.map { it.toPattern() },
                RestrictedInitialPolicy(2,4,Direction.BACKWARD,ap.marks)))
            val stats = demand.staticCompletionStatistics()
            for (part in listOf("c5PlanOccurrences=2","c5AcceptedOccurrences=2","c5OutputPrograms=1",
                "c5PacketStreams=1","c5ScalarEnumerations=1","c5SelectedReferencePeak=1",
                "c5PlanFallbackEmptyTemplates=1","c5PlanFallbackZeroTemplate=1",
                "c5PlanFallbackOversizeTemplates=1","c5PlanFallbackRun=1"))
                assertTrue(stats.orEmpty().split(' ').contains(part),stats)
            assertTrue(demand.diagnosticC5Samples().any { "matchingMember=" in it && "Dc=" in it && "admitted=" in it })
        } finally {
            if (previous == null) System.clearProperty(property) else System.setProperty(property,previous)
        }
    }
}

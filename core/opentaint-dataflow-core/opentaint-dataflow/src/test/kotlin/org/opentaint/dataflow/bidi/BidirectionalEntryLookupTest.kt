package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.EngineShellFixtures
import org.opentaint.dataflow.bidi.store.*
import kotlin.test.*

class BidirectionalEntryLookupTest {
    private class Fixture {
        val f = EngineShellFixtures()
        val ap = f.manager
        val t = MarkSlot.Concrete(ap.marks.mark("T"))
        val cls = ap.accessors.index(ClassStaticAccessor("C"))
        val field = f.field("f")
        fun p(base: AccessPathBase, mark: MarkSlot = MarkSlot.STAR) =
            Pattern(PathFact(base, emptyList(), Tail.STAR, mark), ExclusionSet.Empty)
        fun c(mark: MarkSlot = MarkSlot.STAR) =
            Pattern(PathFact(STATIC, listOf(cls, field), Tail.STAR, mark), ExclusionSet.Empty)
        val ret get() = p(AccessPathBase.Return)
        fun completion() = FrozenStaticCompletion.Builder(ap, DetachedStaticCallGraph.EMPTY).apply {
            addSeed(f.a, p(AccessPathBase.Argument(0), t), c(t))
            addSeed(f.a, c(), ret)
        }.build()
    }

    @Test fun `C2 projects entries and searches FLOW witnesses without asking for paired candidates`() {
        val f = Fixture()
        val completed = f.completion()
        fun entriesOnly(view: StaticDemandView) = object : StaticDemandView by view {
            override fun targets(actual: Pattern, prefixesOnly: Boolean): Sequence<StaticGuidanceEdge> =
                error("C2 must not enumerate paired candidates")
            override fun pairs(initial: InitialAp, outputs: List<Pattern>): Sequence<StaticGuidanceEdge> =
                error("C2 must not enumerate paired candidates")
        }
        val guarded = object : FrozenCompletion by completed {
            override fun local(method: MethodKey) = entriesOnly(completed.local(method))
            override fun visible(method: MethodKey) = entriesOnly(completed.visible(method))
        }
        val store = DemandStore.Builder(f.ap).apply { withCompletion(guarded) }.build()
        val actual = f.ap.factsOf(f.p(AccessPathBase.Return, f.t).fact, ExclusionSet.Empty, Layer.DEMAND)
        assertEquals(setOf(f.ap.initial(f.ret), f.ap.initial(f.p(AccessPathBase.Return, f.t))),
            store.initials(f.f.a, actual))
    }

    @Test fun `complete direct local keys stop before either local composition or graph visibility`() {
        val f = Fixture()
        val completed = f.completion()
        val local = completed.local(f.f.a)
        val guarded = object : FrozenCompletion by completed {
            override fun local(method: MethodKey) = object : StaticDemandView by local {
                override fun flowTargets(actual: Pattern): Sequence<StaticGuidanceEdge> =
                    error("A complete entry bound must stop before composition")
            }
            override fun visible(method: MethodKey): StaticDemandView =
                error("A complete local bound must not inspect the graph")
        }
        val tRet = f.p(AccessPathBase.Return, f.t)
        val store = DemandStore.Builder(f.ap).apply {
            add(f.f.a, DemandPattern(f.ret, null))
            add(f.f.a, DemandPattern(tRet, null))
            withCompletion(guarded)
        }.build()
        val actual = f.ap.factsOf(tRet.fact, ExclusionSet.Empty, Layer.DEMAND)
        assertEquals(setOf(f.ap.initial(f.ret), f.ap.initial(tRet)), store.initials(f.f.a, actual))
    }
}

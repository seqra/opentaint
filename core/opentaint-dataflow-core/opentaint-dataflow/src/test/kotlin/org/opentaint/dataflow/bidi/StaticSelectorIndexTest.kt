package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.*
import org.opentaint.dataflow.bidi.store.*
import kotlin.test.*

class StaticSelectorIndexTest {
    private class Fixture {
        val f = EngineShellFixtures()
        val ap = f.manager
        val t = ap.marks.mark("T")
        val u = ap.marks.mark("U")
        val g = ap.marks.group(ap.marks.groupOf(t))
        val cls = ap.accessors.index(ClassStaticAccessor("C"))
        val a = f.field("a")
        val b = f.field("b")
        fun static(field: Int, mark: MarkSlot = MarkSlot.STAR) =
            Pattern(PathFact(STATIC, listOf(cls, field), Tail.STAR, mark), ExclusionSet.Empty)
        fun mark(atom: TaintMark) = MarkSlot.Concrete(atom)
        fun ordinals(vararg rows: GuidanceMarks) = StaticOutputOrdinals.Builder(ap.marks).apply {
            rows.forEach(::add)
        }.build()
        fun selected(index: StaticOutputOrdinals, selection: StaticLabelSelection) =
            index.ordinals(selection).asSequence().toList()
    }

    @Test fun `FULL output lookup preserves exact identity and FLOW without duplicate ordinals`() {
        val f = Fixture()
        val index = f.ordinals(GuidanceMarks.Mapped(f.t, f.u), GuidanceMarks.Flow,
            GuidanceMarks.Mapped(f.u, f.t), GuidanceMarks.Mapped(f.t, f.g))
        assertEquals(listOf(1, 2, 3), f.selected(index,
            StaticLabelSelection.OutputCovers(checkNotNull(f.ap.marks.staticSelector(f.t)))))
        assertEquals(listOf(1), f.selected(index, StaticLabelSelection.FlowOnly))
        assertEquals(listOf(0, 1, 2, 3), f.selected(index, StaticLabelSelection.All))
    }

    @Test fun `GROUP coverage is directional but GROUP composition admits stored FULL members`() {
        val f = Fixture()
        val index = f.ordinals(GuidanceMarks.Mapped(f.t, f.t), GuidanceMarks.Flow,
            GuidanceMarks.Mapped(f.t, f.g), GuidanceMarks.Mapped(f.t, f.u))
        val group = checkNotNull(f.ap.marks.staticSelector(f.g))
        assertEquals(listOf(1, 2), f.selected(index, StaticLabelSelection.OutputCovers(group)))
        assertEquals(listOf(0, 1, 2), f.selected(index, StaticLabelSelection.OutputComposesWith(group)))
    }

    @Test fun `nullable endpoint ZERO differs from a nonnull control atom`() {
        val f = Fixture()
        val index = f.ordinals(GuidanceMarks.Mapped(f.t, null), GuidanceMarks.Flow,
            GuidanceMarks.Mapped(f.t, f.t))
        assertEquals(listOf(0, 1), f.selected(index, StaticLabelSelection.OutputCovers(StaticMarkSelector.Zero)))
        assertEquals(listOf(1), f.selected(index, StaticLabelSelection.OutputComposesWith(StaticMarkSelector.Zero)))
        assertEquals(StaticLabelSelection.FlowOnly, outputComposable(null, f.ap.marks))
        assertEquals(StaticLabelSelection.All, outputComposable(TaintMark.ZERO, f.ap.marks))
        val unknown = f.ordinals(GuidanceMarks.Mapped(f.t, TaintMark.ZERO), GuidanceMarks.Flow,
            GuidanceMarks.Mapped(f.t, f.t))
        assertEquals(listOf(0, 1, 2), f.selected(unknown,
            StaticLabelSelection.OutputCovers(checkNotNull(f.ap.marks.staticSelector(f.u)))))
    }

    @Test fun `finite mixed FULL GROUP and ZERO postings match the independent label predicate`() {
        val owner = MarkGroupKey.Rule("shared")
        val shell = EngineShellFixtures(markDeclarations = testDeclarations(TestMark("T", owner),
            TestMark("U", owner), TestMark("V")))
        val marks = shell.manager.marks
        val t = marks.mark("T")
        val u = marks.mark("U")
        val v = marks.mark("V")
        val group = marks.group(marks.groupOf(t))
        val labels = listOf(GuidanceMarks.Mapped(t, t), GuidanceMarks.Flow,
            GuidanceMarks.Mapped(u, t), GuidanceMarks.Mapped(t, group),
            GuidanceMarks.Mapped(t, u), GuidanceMarks.Mapped(t, v), GuidanceMarks.Mapped(t, null))
        val index = StaticOutputOrdinals.Builder(marks).apply { labels.forEach(::add) }.build()
        for (query in listOf(t, u, v, group)) for (compose in listOf(false, true)) {
            val key = checkNotNull(marks.staticSelector(query))
            val selection = if (compose) StaticLabelSelection.OutputComposesWith(key) else StaticLabelSelection.OutputCovers(key)
            val expected = labels.indices.filter { i -> when (val label = labels[i]) {
                GuidanceMarks.Flow -> true
                is GuidanceMarks.Mapped -> label.output?.let {
                    marks.coversAtom(it, query) || compose && marks.coversAtom(query, it)
                } == true
            } }
            assertEquals(expected, index.ordinals(selection).asSequence().toList(), "query=$query compose=$compose")
        }
        assertEquals(listOf(1, 6), index.ordinals(StaticLabelSelection.OutputCovers(StaticMarkSelector.Zero)).asSequence().toList())
    }

    @Test fun `C2 avoids unrelated bridge owner questions and local attachments stay in their full method context`() {
        val f = Fixture()
        val graph = DetachedStaticCallGraph.copyOf(mapOf(f.f.methodA to setOf(f.f.methodB)), f.f.cancellation)
        val property = "org.opentaint.bidi.optimizationStatistics"
        val old = System.getProperty(property)
        val snapshot = try {
            System.setProperty(property, "true")
            FrozenStaticCompletion.Builder(f.ap, graph).apply {
                addSeed(f.f.b, f.static(f.a), f.static(f.b))
                addSeed(f.f.b, f.static(f.a, f.mark(f.t)), f.static(f.b, f.mark(f.t)))
                addSeed(f.f.b, f.static(f.a, f.mark(f.u)), f.static(f.b, f.mark(f.u)))
                val retT = Pattern(PathFact(AccessPathBase.Return, emptyList(), Tail.STAR, f.mark(f.t)), ExclusionSet.Empty)
                addSeed(f.f.a, f.static(f.a, f.mark(f.t)), retT)
            }.build()
        } finally {
            if (old == null) System.clearProperty(property) else System.setProperty(property, old)
        }
        val view = snapshot.visible(f.f.a)
        assertEquals(setOf(f.static(f.b), f.static(f.b, f.mark(f.t))), view.entries(f.static(f.b, f.mark(f.t))).toSet())
        assertTrue("ownerBitQueries=2 " in snapshot.statistics(), snapshot.statistics())
        val ret = Pattern(PathFact(AccessPathBase.Return, emptyList(), Tail.STAR, f.mark(f.t)), ExclusionSet.Empty)
        assertEquals(listOf(ret), view.entries(ret).toList())
        assertTrue("ownerBitQueries=2 " in snapshot.statistics(), "Local R must not ask a graph owner")
        assertTrue(snapshot.visible(f.f.b).entries(ret).none(), "R from a different MethodKey is not visible")
    }

    @Test fun `selected C5 visits complete original pairs before its exact predicate`() {
        val f = Fixture()
        val snapshot = FrozenStaticCompletion.Builder(f.ap, DetachedStaticCallGraph.EMPTY).apply {
            for (input in listOf(f.t, f.u)) for (output in listOf(f.t, f.u))
                addSeed(f.f.a, f.static(f.a, f.mark(input)), f.static(f.b, f.mark(output)))
            addSeed(f.f.a, f.static(f.a), f.static(f.b))
        }.build()
        val view = snapshot.local(f.f.a)
        val all = view.targets(f.static(f.b)).toList()
        var tested = 0
        val selection = StaticRowQuery(StaticLabelSelection.OutputCovers(checkNotNull(f.ap.marks.staticSelector(f.t))))
        val actual = view.selectedTargets(f.static(f.b), false, selection, StaticCandidateFilter { _, _, _ ->
            tested++; true
        }).toList()
        assertEquals(all.filter { it.marks == GuidanceMarks.Flow || (it.marks as GuidanceMarks.Mapped).output == f.t }, actual)
        assertEquals(3, tested)
        assertEquals(5, all.size)
        assertEquals(setOf(f.t, f.u), actual.mapNotNull { (it.marks as? GuidanceMarks.Mapped)?.input }.toSet())
    }

    @Test fun `one output column avoids the remaining labels in a complete mark matrix`() {
        val f = Fixture()
        val marks = (0 until 20).map { f.ap.marks.mark("T$it") }
        val snapshot = FrozenStaticCompletion.Builder(f.ap, DetachedStaticCallGraph.EMPTY).apply {
            for (input in marks) for (output in marks)
                addSeed(f.f.a, f.static(f.a, f.mark(input)), f.static(f.b, f.mark(output)))
            addSeed(f.f.a, f.static(f.a), f.static(f.b))
        }.build()
        val view = snapshot.local(f.f.a)
        var tested = 0
        val query = StaticRowQuery(StaticLabelSelection.OutputCovers(checkNotNull(f.ap.marks.staticSelector(marks[7]))))
        val selected = view.selectedTargets(f.static(f.b), false, query,
            StaticCandidateFilter { _, _, _ -> tested++; true }).toList()
        assertEquals(401, view.targets(f.static(f.b)).count())
        assertEquals(21, tested)
        assertEquals(marks.toSet(), selected.mapNotNull { (it.marks as? GuidanceMarks.Mapped)?.input }.toSet())
        assertTrue(selected.all { it.marks == GuidanceMarks.Flow || (it.marks as GuidanceMarks.Mapped).output == marks[7] })
    }

    @Test fun `mapped geometry gate keeps FLOW and avoids all mapped predicate calls`() {
        val f = Fixture()
        val snapshot = FrozenStaticCompletion.Builder(f.ap, DetachedStaticCallGraph.EMPTY).apply {
            addSeed(f.f.a, f.static(f.a), f.static(f.b))
            addSeed(f.f.a, f.static(f.a, f.mark(f.t)), f.static(f.b, f.mark(f.t)))
        }.build()
        var tested = 0
        val rows = snapshot.local(f.f.a).selectedTargets(f.static(f.b), false,
            StaticRowQuery(StaticLabelSelection.All, mappedGeometryAllowed = { false }),
            StaticCandidateFilter { _, _, _ -> tested++; true }).toList()
        assertEquals(1, tested)
        assertEquals(listOf(GuidanceMarks.Flow), rows.map { it.marks })
    }

    @Test fun `C2 selects concrete entries and retains abstract FLOW without changing concrete exclusions`() {
        val f = Fixture()
        val excluded = ExclusionSet.of(f.f.field("child"))
        val t = f.static(f.b, f.mark(f.t)).copy(exclusion = excluded)
        val snapshot = FrozenStaticCompletion.Builder(f.ap, DetachedStaticCallGraph.EMPTY).apply {
            addSeed(f.f.a, f.static(f.a), f.static(f.b))
            addSeed(f.f.a, f.static(f.a, f.mark(f.t)), t)
            addSeed(f.f.a, f.static(f.a, f.mark(f.u)), f.static(f.b, f.mark(f.u)))
        }.build()
        val view = snapshot.local(f.f.a)
        assertEquals(setOf(f.static(f.b), t), view.entries(f.static(f.b, f.mark(f.t))).toSet())
        assertEquals(listOf(f.static(f.b)), view.entries(f.static(f.b)).toList())
    }
}

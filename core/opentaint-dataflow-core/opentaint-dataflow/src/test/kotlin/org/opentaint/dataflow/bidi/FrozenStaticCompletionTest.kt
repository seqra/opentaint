package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.EngineShellFixtures
import org.opentaint.dataflow.bidi.fixtures.HandOffFixtures
import org.opentaint.dataflow.bidi.driver.HandOff
import org.opentaint.dataflow.bidi.engine.RunResult
import org.opentaint.dataflow.bidi.engine.RunStatus
import org.opentaint.dataflow.bidi.fixtures.TestMark
import org.opentaint.dataflow.bidi.fixtures.testDeclarations
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.util.Cancellation
import kotlin.test.*

class FrozenStaticCompletionTest {
    private class Fixture(val f: EngineShellFixtures = EngineShellFixtures()) {
        val ap = f.manager
        val cls = ap.accessors.index(ClassStaticAccessor("C"))
        val fields = (0..3).map { f.field("f$it") }
        val t = MarkSlot.Concrete(ap.marks.mark("T"))
        val u = MarkSlot.Concrete(ap.marks.mark("U"))
        val v = MarkSlot.Concrete(ap.marks.mark("V"))
        val methods = listOf(f.a, f.b, f.unknown)
        fun c(index: Int, mark: MarkSlot = MarkSlot.STAR, tail: Tail = Tail.STAR) =
            Pattern(PathFact(STATIC, listOf(cls, fields[index]), tail, mark), ExclusionSet.Empty)
        fun local(base: AccessPathBase, mark: MarkSlot = MarkSlot.STAR, tail: Tail = Tail.STAR) =
            Pattern(PathFact(base, emptyList(), tail, mark), ExclusionSet.Empty)
        val x get() = local(AccessPathBase.Argument(0))
        val y get() = local(AccessPathBase.Return)
        fun edge(from: Pattern, to: Pattern) = StaticGuidanceEdge.of(from, to)
        fun graph(vararg calls: Pair<MethodKey, MethodKey>) = DetachedStaticCallGraph.copyOf(
            methods.associate { key -> key.method to calls.filter { it.first == key }.map { it.second.method }.toSet() },
            f.cancellation,
        )
        fun collect(view: FrozenCompletion, method: MethodKey, targets: List<Pattern>) =
            targets.flatMap { view.near(method, it).toList() }.toSet()
    }

    @Test fun `handoff consumes joined ZERO writer seeds after mutable catalogs have been released`() {
        HandOffFixtures().use { f ->
            val key = f.key()
            val path = listOf(f.manager.accessors.index(ClassStaticAccessor("C")), f.field("f"))
            val mark = MarkSlot.Concrete(f.mark("T"))
            val static = f.pattern(STATIC, path, Tail.STAR, mark)
            val ret = f.pattern(AccessPathBase.Return, tail = Tail.STAR, mark = mark)
            val completed = FrozenStaticCompletion.Builder(f.manager, DetachedStaticCallGraph.EMPTY).apply {
                addSeed(key, f.manager.zero.toPattern(), static)
                addSeed(key, static, ret)
            }.build()
            f.shared.releaseRun1CatalogCoverage()
            val result = RunResult<org.opentaint.dataflow.bidi.engine.RunMethodAnalyzer>(RunStatus.COMPLETE,
                emptyList(), 1, Direction.FORWARD, f.vulnerabilities, staticCompletion = completed)
            val handOff = HandOff.of(f.config, result, f.report, f.shared)
            assertTrue(DemandPattern(ret, f.manager.zero.toPattern()) in handOff.demand.near(key, ret))
            assertTrue(handOff.demand.hasStaticCompletion)
            assertTrue(handOff.demandEdges.isEmpty(), "Virtual completed pairs are not ordinary selected publications")
            assertTrue(f.records.byEntry(key, f.manager.zero.toPattern()).none(),
                "A completed guide does not become a normal record")
        }
    }

    @Test fun `one static geometry packs exact mark pairs without merging FLOW and same-mark colors`() {
        val f = Fixture()
        val labels = listOf(f.t, f.u, f.v)
        val interner = StaticGuidanceInterner(f.ap)
        val rows = labels.flatMap { from -> labels.map { to -> f.edge(f.c(0, from), f.c(1, to)) } } +
            f.edge(f.c(0), f.c(1))
        val ids = rows.map(interner::intern)
        assertEquals(rows.size, ids.toSet().size)
        assertEquals(ids, rows.map(interner::intern))
        assertEquals(rows, ids.map(interner::row))
        val view = FrozenStaticCompletion.Builder(f.ap, f.graph()).apply {
            for (row in rows) addBridge(f.f.a, row)
        }.build()
        assertEquals(1, view.seedGeometries)
        assertEquals(10, view.seedKeys)
        assertEquals(rows.map { DemandPattern(it.to, it.from) }.toSet(), view.near(f.f.a, f.c(1)).toSet())
    }

    @Test fun `GROUP closure guides an actual FULL mark without a group-member inventory`() {
        val f = Fixture(EngineShellFixtures(markDeclarations = testDeclarations(
            TestMark("T", MarkGroupKey.Rule("owner")), TestMark("U", MarkGroupKey.Rule("owner")),
            TestMark("V", MarkGroupKey.Rule("other")),
        )))
        val group = MarkSlot.Concrete(f.ap.marks.group(f.ap.marks.groupOf(f.t.mark)))
        val returned = f.local(AccessPathBase.Return, group)
        val view = FrozenStaticCompletion.Builder(f.ap, f.graph()).apply {
            addBridge(f.f.a, f.edge(f.c(0, group), f.c(1, group)))
            addBoundary(f.f.a, f.c(1, group), returned)
        }.build()
        val guide = DemandPattern(returned, f.c(0, group))
        assertTrue(guide in view.near(f.f.a, returned).toSet())
        val actual = f.f.fact(AccessPathBase.Return, tail = Tail.ANY, mark = f.u, layer = Layer.DEMAND)
        val starts = f.f.ops.emit(guide, actual)
        assertEquals(setOf(f.u), starts.map { it.mark }.toSet())
        assertTrue(starts.none { f.ap.marks.isGroup((it.mark as MarkSlot.Concrete).mark) })
    }

    @Test fun `all static compositions keep local bindings while B crosses sibling calls and recursive callers`() {
        val f = Fixture()
        val writer = f.edge(f.x, f.c(0))
        val first = f.edge(f.c(0), f.c(1))
        val second = f.edge(f.c(1), f.c(2))
        val reader = f.edge(f.c(2), f.y)
        val view = FrozenStaticCompletion.Builder(f.ap, f.graph(f.f.a to f.f.b, f.f.a to f.f.unknown,
            f.f.b to f.f.a)).apply {
            addBridge(f.f.b, first)
            addBridge(f.f.unknown, second)
            addBoundary(f.f.a, writer.from, writer.to)
            addBoundary(f.f.a, reader.from, reader.to)
        }.build()
        val all = f.collect(view, f.f.a, listOf(f.c(0), f.c(1), f.c(2), f.y))
        for (guide in listOf(DemandPattern(f.c(2), f.c(0)), DemandPattern(f.c(1), f.x),
            DemandPattern(f.c(2), f.x), DemandPattern(f.y, f.c(0)), DemandPattern(f.y, f.c(1)),
            DemandPattern(f.y, f.x))) assertTrue(guide in all, "$guide")
        assertTrue(view.near(f.f.b, f.y).none(), "W/R bindings do not travel by method adjacency")
        assertTrue(DemandPattern(f.c(1), f.c(0)) in view.near(f.f.b, f.c(1)).toSet())
    }

    @Test fun `shared B keys survive prescan release and do not copy context-local W R attachments`() {
        val f = Fixture()
        val targets = linkedSetOf(f.f.b.method)
        val source = linkedMapOf(f.f.a.method to targets, f.f.unknown.method to linkedSetOf(f.f.a.method))
        val graph = DetachedStaticCallGraph.copyOf(source, f.f.cancellation)
        targets.clear()
        source.clear()
        val otherContext = f.f.key(f.f.a.method, "other context")
        val bridge = f.edge(f.c(0), f.c(1))
        val view = FrozenStaticCompletion.Builder(f.ap, graph).apply {
            addBridge(f.f.b, bridge)
            addBridge(f.f.a, bridge)
            addBoundary(f.f.a, f.x, f.c(0))
            addBoundary(f.f.a, f.c(1), f.y)
        }.build()
        assertEquals(1, view.seedKeys)
        assertEquals(2L, view.seedMemberships)
        assertTrue(DemandPattern(f.c(1), f.c(0)) in view.near(f.f.unknown, f.c(1)).toSet(),
            "An actor absent in run-1 still sees the detached transitive call graph")
        assertTrue(DemandPattern(f.c(1), f.c(0)) in view.near(otherContext, f.c(1)).toSet())
        assertTrue(view.near(otherContext, f.y).none())
        assertFalse(view.near(otherContext, f.c(1)).any { it.exit?.fact?.base == AccessPathBase.Argument(0) })
    }

    @Test fun `colored round trip remains distinct from parallel FLOW and incompatible marks do not join`() {
        val f = Fixture()
        val view = FrozenStaticCompletion.Builder(f.ap, f.graph()).apply {
            addBridge(f.f.a, f.edge(f.c(0, f.t), f.c(1, f.u)))
            addBridge(f.f.a, f.edge(f.c(1, f.u), f.c(2, f.t)))
            addBridge(f.f.a, f.edge(f.c(0), f.c(2)))
            addBridge(f.f.a, f.edge(f.c(2, f.t), f.c(0, f.t)))
            addBridge(f.f.a, f.edge(f.c(2, f.v), f.c(3, f.v)))
        }.build()
        val all = f.collect(view, f.f.a, listOf(f.c(0), f.c(2), f.c(3)))
        assertTrue(DemandPattern(f.c(0, f.t), f.c(0, f.t)) in all)
        assertTrue(DemandPattern(f.c(2, f.t), f.c(0, f.t)) in all)
        assertTrue(DemandPattern(f.c(2), f.c(0)) in all)
        assertFalse(DemandPattern(f.c(3, f.v), f.c(0, f.t)) in all)
    }

    @Test fun `real ZERO source survives colored composition and a zero result never becomes an internal vertex`() {
        val f = Fixture()
        val zero = f.ap.zero.toPattern()
        val xT = f.local(AccessPathBase.Argument(0), f.t)
        val yU = f.local(AccessPathBase.Return, f.u)
        val view = FrozenStaticCompletion.Builder(f.ap, f.graph()).apply {
            addBoundary(f.f.a, zero, f.c(0, f.t))
            addBridge(f.f.a, f.edge(f.c(0), f.c(1)))
            addBridge(f.f.a, f.edge(f.c(1, f.t), f.c(2, f.u)))
            addBoundary(f.f.a, f.c(2, f.u), yU)
            addBoundary(f.f.a, f.c(3, f.t), zero)
            addBoundary(f.f.a, xT, f.c(3, f.t))
        }.build()
        assertTrue(DemandPattern(yU, zero) in view.near(f.f.a, yU).toSet())
        assertTrue(DemandPattern(zero, xT) in view.near(f.f.a, zero).toSet())
        assertFalse(DemandPattern(yU, xT) in view.near(f.f.a, yU).toSet(), "ZERO is not a composition middle")
    }

    @Test fun `near uses prefix and extension candidates while covering only uses entry prefixes`() {
        val f = Fixture()
        val ret = f.local(AccessPathBase.Return)
        val deeperRet = ret.copy(fact = ret.fact.copy(path = listOf(f.fields[3])))
        val view = FrozenStaticCompletion.Builder(f.ap, f.graph()).apply {
            addBoundary(f.f.a, f.c(0), deeperRet)
        }.build()
        val guide = DemandPattern(deeperRet, f.c(0))
        assertEquals(listOf(guide), view.near(f.f.a, ret).toList())
        assertTrue(view.covering(f.f.a, f.ap.initial(ret)).none())
        assertEquals(listOf(guide), view.covering(f.f.a, f.ap.initial(deeperRet)).toList())
    }

    @Test fun `field anchors exclude class markers and sibling fields despite common S prefix`() {
        val f = Fixture()
        val marker = Pattern(PathFact(STATIC, listOf(f.cls), Tail.EXACT, f.t), ExclusionSet.Empty)
        val out = f.local(AccessPathBase.Return, f.t)
        val view = FrozenStaticCompletion.Builder(f.ap, f.graph()).apply {
            addBoundary(f.f.a, f.x.copy(fact = f.x.fact.copy(mark = f.t)), f.c(0, f.t))
            addBoundary(f.f.a, f.c(1, f.t), out)
            addBoundary(f.f.a, marker, out)
        }.build()
        assertFalse(view.near(f.f.a, out).any { it.exit?.fact?.base == AccessPathBase.Argument(0) })
    }

    @Test fun `frozen view owns its input and checks cancellation during traversal`() {
        val f = Fixture()
        val builder = FrozenStaticCompletion.Builder(f.ap, f.graph())
        builder.addBridge(f.f.a, f.edge(f.c(0), f.c(1)))
        val view = builder.build()
        builder.addBridge(f.f.a, f.edge(f.c(1), f.c(2)))
        assertTrue(view.near(f.f.a, f.c(2)).none())
        f.f.cancellation.cancel()
        assertFailsWith<Cancellation.Cancelled> { view.near(f.f.a, f.c(1)).toList() }
    }

    @Test fun `factored production lookup equals the eager closure on every three-method directed graph`() {
        val f = Fixture()
        val possible = f.methods.flatMap { from -> f.methods.filter { it != from }.map { from to it } }
        val seeds = listOf(
            f.f.a to f.edge(f.x, f.c(0)),
            f.f.a to f.edge(f.c(2), f.y),
            f.f.b to f.edge(f.c(0), f.c(1)),
            f.f.unknown to f.edge(f.c(1), f.c(2)),
            f.f.b to f.edge(f.c(0, f.t), f.c(1, f.u)),
            f.f.unknown to f.edge(f.c(1, f.u), f.c(2, f.t)),
            f.f.b to f.edge(f.c(1, f.v), f.c(3, f.v)),
        )
        for (mask in 0 until (1 shl possible.size)) {
            val calls = possible.filterIndexed { index, _ -> mask and (1 shl index) != 0 }
            val builder = FrozenStaticCompletion.Builder(f.ap, f.graph(*calls.toTypedArray()))
            for ((owner, edge) in seeds) {
                if (edge.from.fact.base == STATIC && edge.to.fact.base == STATIC) builder.addBridge(owner, edge)
                else builder.addBoundary(owner, edge.from, edge.to)
            }
            val view = builder.build()
            val expected = eager(f, calls, seeds)
            for (method in f.methods) {
                val targets = (expected.getValue(method).map { it.to } + (0..3).map { f.c(it) } + f.y).distinct()
                val actual = f.collect(view, method, targets)
                val pairs = expected.getValue(method).map { DemandPattern(it.to, it.from) }.toSet()
                assertEquals(pairs, actual, "graph mask=$mask method=$method")
                for (target in targets) {
                    val expectedCover = pairs.filter { target.fact.base == it.entry.fact.base &&
                        target.fact.path.startsWith(it.entry.fact.path) }.toSet()
                    assertEquals(expectedCover, view.covering(method, f.ap.initial(target)).toSet(),
                        "cover graph mask=$mask method=$method target=$target")
                }
            }
        }
    }

    /** Small independent eager oracle; production stores no method-by-pair closure. */
    private fun eager(f: Fixture, calls: List<Pair<MethodKey, MethodKey>>,
                      seeds: List<Pair<MethodKey, StaticGuidanceEdge>>): Map<MethodKey, Set<StaticGuidanceEdge>> {
        val rows = f.methods.associateWith { LinkedHashSet<StaticGuidanceEdge>() }
        for ((method, edge) in seeds) rows.getValue(method) += edge
        fun compose(a: StaticGuidanceEdge, b: StaticGuidanceEdge): StaticGuidanceEdge? {
            if (a.to.fact.base != STATIC || b.from.fact.base != STATIC || a.to.fact.path != b.from.fact.path) return null
            val label = when (val left = a.marks) {
                GuidanceMarks.Flow -> b.marks
                is GuidanceMarks.Mapped -> when (val right = b.marks) {
                    GuidanceMarks.Flow -> left
                    is GuidanceMarks.Mapped -> if (left.output == right.input) GuidanceMarks.Mapped(left.input, right.output) else return null
                }
            }
            val input = if (label is GuidanceMarks.Mapped) MarkSlot.Concrete(checkNotNull(label.input)) else MarkSlot.STAR
            val output = if (label is GuidanceMarks.Mapped) MarkSlot.Concrete(checkNotNull(label.output)) else MarkSlot.STAR
            return StaticGuidanceEdge(a.from.copy(fact = a.from.fact.copy(mark = input)),
                b.to.copy(fact = b.to.fact.copy(mark = output)), label)
        }
        var changed: Boolean
        do {
            changed = false
            for ((caller, callee) in calls) for (edge in rows.getValue(callee).toList()) {
                if (edge.from.fact.base == STATIC && edge.to.fact.base == STATIC)
                    if (rows.getValue(caller).add(edge)) changed = true
            }
            for ((_, owned) in rows) for (a in owned.toList()) for (b in owned.toList()) {
                val combined = compose(a, b) ?: continue
                if (owned.add(combined)) changed = true
            }
        } while (changed)
        return rows
    }
}

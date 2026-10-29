package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.EngineShellFixtures
import org.opentaint.dataflow.bidi.fixtures.TestMark
import org.opentaint.dataflow.bidi.fixtures.testDeclarations
import org.opentaint.dataflow.bidi.store.*
import kotlin.test.*

/** The oracle saturates seed rows independently. It never asks the production completion for candidates. */
class DemandStorageDifferentialTest {
    private class Fixture {
        val f = EngineShellFixtures(markDeclarations = testDeclarations(
            TestMark("T", MarkGroupKey.Rule("owner")), TestMark("U", MarkGroupKey.Rule("owner")),
            TestMark("V", MarkGroupKey.Rule("other")),
        ))
        val ap = f.manager
        val ops = f.ops
        val cls = ap.accessors.index(ClassStaticAccessor("C"))
        val fields = (0..3).map { f.field("f$it") }
        val t = MarkSlot.Concrete(ap.marks.mark("T"))
        val u = MarkSlot.Concrete(ap.marks.mark("U"))
        val v = MarkSlot.Concrete(ap.marks.mark("V"))
        val group = MarkSlot.Concrete(ap.marks.group(ap.marks.groupOf(t.mark)))
        val methods = listOf(f.a, f.b, f.unknown)
        fun c(n: Int, mark: MarkSlot = MarkSlot.STAR, tail: Tail = Tail.STAR) =
            Pattern(PathFact(STATIC, listOf(cls, fields[n]), tail, mark), ExclusionSet.Empty)
        fun p(base: AccessPathBase, mark: MarkSlot = MarkSlot.STAR, tail: Tail = Tail.STAR) =
            Pattern(PathFact(base, emptyList(), tail, mark), ExclusionSet.Empty)
        val x get() = p(AccessPathBase.Argument(0))
        val ret get() = p(AccessPathBase.Return)
        fun row(a: Pattern, b: Pattern) = StaticGuidanceEdge.of(a, b)
        fun storage(calls: List<Pair<MethodKey, MethodKey>>, seeds: List<Pair<MethodKey, StaticGuidanceEdge>>,
                    explicit: List<Pair<MethodKey, DemandPattern>> = emptyList()): DemandStore {
            val graph = DetachedStaticCallGraph.copyOf(methods.associate { m ->
                m.method to calls.filter { it.first == m }.map { it.second.method }.toSet()
            }, f.cancellation)
            val view = FrozenStaticCompletion.Builder(ap, graph).apply {
                for ((owner, row) in seeds) addSeed(owner, row)
            }.build()
            return DemandStore.Builder(ap).apply {
                withCompletion(view)
                for ((owner, pair) in explicit) add(owner, pair)
            }.build()
        }

        /** Fixed-point relation on a deliberately small domain; ZERO is never a join vertex. */
        fun closure(calls: List<Pair<MethodKey, MethodKey>>, seeds: List<Pair<MethodKey, StaticGuidanceEdge>>)
            : Map<MethodKey, Set<StaticGuidanceEdge>> {
            val reachable = methods.associateWith { linkedSetOf(it) }
            var changed: Boolean
            do {
                changed = false
                for ((a, b) in calls) if (reachable.getValue(a).addAll(reachable.getValue(b))) changed = true
            } while (changed)
            return methods.associateWith { m ->
                val rows = seeds.filter { (owner, edge) ->
                    if (edge.from.fact.base == STATIC && edge.to.fact.base == STATIC)
                        reachable.getValue(m).any { it.method == owner.method }
                    else owner == m
                }.mapTo(linkedSetOf()) { it.second }
                do {
                    changed = false
                    val before = rows.toList()
                    for (left in before) for (right in before) {
                        if (left.to.fact.base != STATIC || right.from.fact.base != STATIC ||
                            left.to.fact.path.take(2) != right.from.fact.path.take(2) || !overlap(left.to, right.from)) continue
                        val marks = when (val a = left.marks) {
                            GuidanceMarks.Flow -> right.marks
                            is GuidanceMarks.Mapped -> when (val b = right.marks) {
                                GuidanceMarks.Flow -> a
                                is GuidanceMarks.Mapped -> if (a.output != null && b.input != null &&
                                    (ap.marks.coversAtom(a.output, b.input) || ap.marks.coversAtom(b.input, a.output)))
                                    GuidanceMarks.Mapped(a.input, b.output) else null
                            }
                        } ?: continue
                        val from = if (marks is GuidanceMarks.Mapped && left.from.fact.base != AccessPathBase.Zero)
                            left.from.copy(fact = left.from.fact.copy(mark = MarkSlot.Concrete(checkNotNull(marks.input))))
                        else left.from
                        val to = if (marks is GuidanceMarks.Mapped && right.to.fact.base != AccessPathBase.Zero)
                            right.to.copy(fact = right.to.fact.copy(mark = MarkSlot.Concrete(checkNotNull(marks.output))))
                        else right.to
                        if (rows.add(StaticGuidanceEdge(from, to, marks))) changed = true
                    }
                } while (changed)
                rows
            }
        }
        fun initials(pairs: Collection<DemandPattern>, actual: Facts): Set<InitialAp> =
            pairs.flatMap { ops.emit(it, actual) }.toSet()
        fun restrict(pairs: Collection<DemandPattern>, original: PremiseKey, raw: Facts): List<Facts> =
            original.members.flatMap { j -> pairs.flatMap { ops.restrict(j, raw, it) } }
        fun payload(values: List<Facts>): Set<Conclusion> = values.flatMap { value ->
            ops.leaves(value).map { Conclusion(it.fact, it.exclusion, value.layer == Layer.DEMAND) }.toList()
        }.toSet()
        fun flags(values: List<Facts>): Set<Pattern> = values.flatMap { value ->
            (value as? TaintTree)?.protectedPart()?.let { ops.leaves(it).toList() }.orEmpty()
        }.toSet()
        fun facts(pattern: Pattern, layer: Layer = Layer.DEMAND) = ap.factsOf(pattern.fact, pattern.exclusion, layer)
    }

    @Test fun `entry and paired queries equal explicit closure for all three-method call graphs`() {
        val f = Fixture()
        val possible = f.methods.flatMap { a -> f.methods.filter { it != a }.map { a to it } }
        val seeds = listOf(
            f.f.a to f.row(f.x, f.c(0)),
            f.f.a to f.row(f.p(AccessPathBase.Argument(0), f.t), f.c(0, f.t)),
            f.f.a to f.row(f.ap.zero.toPattern(), f.c(0, f.u)),
            f.f.a to f.row(f.c(2), f.ret),
            f.f.b to f.row(f.c(0), f.c(1)),
            f.f.unknown to f.row(f.c(1), f.c(2)),
            f.f.b to f.row(f.c(0, f.t), f.c(1, f.u)),
            f.f.unknown to f.row(f.c(1, f.u), f.c(2, f.t)),
            f.f.unknown to f.row(f.c(2), f.c(0)),
            f.f.b to f.row(f.c(0, f.group), f.c(3, f.group)),
            f.f.unknown to f.row(f.c(3), f.ret.copy(fact = f.ret.fact.copy(path = listOf(f.fields[3])))),
        )
        val locations = (0..3).map { f.c(it) } + f.ret
        val actuals = locations.flatMap { location -> listOf(MarkSlot.STAR, f.t, f.u, f.v).map { mark ->
            f.facts(location.copy(fact = location.fact.copy(mark = mark)))
        } } + Reach.NORMAL
        for (mask in 0 until (1 shl possible.size)) {
            val calls = possible.filterIndexed { i, _ -> mask and (1 shl i) != 0 }
            val store = f.storage(calls, seeds)
            val reference = f.closure(calls, seeds)
            for (m in f.methods) {
                val pairs = reference.getValue(m).map { DemandPattern(it.to, it.from) } +
                    DemandPattern(f.ap.zero.toPattern(), null)
                for (actual in actuals) {
                    assertEquals(f.initials(pairs, actual), store.initials(m, actual),
                        "C2 graph=$mask method=$m actual=${f.ops.leaves(actual).toList()}")
                    val original = f.ap.initial(f.ops.leaves(actual).single())
                    val raw = f.facts(f.p(AccessPathBase.Argument(0), f.t), Layer.NORMAL)
                    val expected = f.restrict(pairs, original, raw)
                    val found = store.intersect(m, original, raw)
                    assertEquals(expected.toSet(), found.toSet(), "C5 exact packets graph=$mask method=$m initial=$original")
                    assertEquals(f.payload(expected), f.payload(found), "C5 graph=$mask method=$m initial=$original")
                }
            }
        }
    }

    @Test fun `C5 retains each original ND member and the protection mask for ANY refinements`() {
        val f = Fixture()
        val ret = AccessPathBase.Return
        val j1 = f.ap.initial(f.p(ret, f.t))
        val j2 = f.ap.initial(f.p(AccessPathBase.Argument(1), f.t))
        val nd = f.ap.premiseOf(listOf(j1, j2))
        val out = f.p(AccessPathBase.Argument(0), f.t, Tail.ANY)
        val exact = out.copy(fact = out.fact.copy(path = listOf(f.fields[3]), tail = Tail.EXACT))
        val pairs = listOf(DemandPattern(j1.toPattern(), out), DemandPattern(j2.toPattern(), exact))
        val store = DemandStore.Builder(f.ap).apply { for (p in pairs) add(f.f.a, p) }.build()
        val raw = (f.facts(out) as TaintTree).let { it.withProtection(it.root) }
        val expected = f.restrict(pairs, nd, raw)
        val found = store.intersect(f.f.a, nd, raw)
        assertEquals(expected.toSet(), found.toSet(), "Different raw payloads must not be compacted")
        assertEquals(f.payload(expected), f.payload(found))
        assertEquals(f.flags(expected), f.flags(found))
        assertTrue(f.payload(found).any { it.fact.tail == Tail.EXACT }, "ANY completion must retain a separate EXACT output")
    }

    @Test fun `later snapshots have direct static demand but no inherited completion or static carry`() {
        val f = Fixture()
        val direct = DemandPattern(f.c(0, f.t), f.ret.copy(fact = f.ret.fact.copy(mark = f.t)))
        val store = DemandStore.Builder(f.ap).apply { add(f.f.a, direct) }.build()
        assertFalse(store.hasStaticCompletion)
        assertFalse(store.hasSharedStaticCarry)
        assertEquals(f.initials(listOf(direct), f.facts(f.c(0, f.t))), store.initials(f.f.a, f.facts(f.c(0, f.t))))
        assertTrue(store.initials(f.f.b, f.facts(f.c(0, f.t))).isEmpty())
        assertTrue(store.initials(f.f.a, f.facts(f.c(1, f.t))).isEmpty())
    }

    @Test fun `an unanswered FLOW reader color query interns only the emitted FLOW initial`() {
        val f = Fixture()
        val store = f.storage(emptyList(), listOf(f.f.a to f.row(f.c(0), f.ret)))
        val actual = f.facts(f.p(AccessPathBase.Return, f.t))
        val directory = ApManager::class.java.getDeclaredField("initials").apply { isAccessible = true }
        fun count() = (directory.get(f.ap) as Map<*, *>).size
        val before = count()
        val result = store.initials(f.f.a, actual)
        assertEquals(setOf(f.ap.initial(f.ret.copy(fact=f.ret.fact.copy(tail=Tail.EXACT)))), result)
        assertEquals(before + 1, count(), "The potential ret/T key must not be interned by coverage or a negative search")
    }

    @Test fun `static joins respect directional geometry exclusions and distinct EXACT class anchors`() {
        val f = Fixture()
        val left = f.f.field("left")
        val right = f.f.field("right")
        val written = f.c(0, f.t).let { it.copy(fact = it.fact.copy(path = it.fact.path + left)) }
        val marker = Pattern(PathFact(STATIC, listOf(f.cls), Tail.EXACT, f.t), ExclusionSet.Empty)
        val input = f.p(AccessPathBase.Argument(0), f.t)
        val actual = f.facts(f.p(AccessPathBase.Return, f.t))
        for (excluded in listOf(left, right)) {
            val seeds = listOf(
                f.f.a to f.row(input, written),
                f.f.b to f.row(f.c(0, f.t).copy(exclusion = ExclusionSet.of(excluded)), f.c(1, f.t)),
                f.f.a to f.row(f.c(1), f.ret),
                // A global class marker must never become a root for a named-field reader.
                f.f.a to f.row(input, marker),
            )
            val calls = listOf(f.f.a to f.f.b)
            val store = f.storage(calls, seeds)
            val pairs = f.closure(calls, seeds).getValue(f.f.a).map { DemandPattern(it.to, it.from) }
            assertEquals(f.initials(pairs, actual), store.initials(f.f.a, actual))
            val initial = f.ap.initial(f.p(AccessPathBase.Return, f.t).let { it.copy(fact=it.fact.copy(tail=Tail.EXACT)) })
            val expected = f.restrict(pairs, initial, f.facts(input))
            val found = store.intersect(f.f.a, initial, f.facts(input))
            assertEquals(f.payload(expected), f.payload(found))
            assertEquals(excluded == right, found.isNotEmpty(), "The admitted left path needs the matching writer")
        }
    }

    @Test fun `own bridges cross contexts but writer and reader attachments keep complete method keys`() {
        val f = Fixture()
        val other = f.f.key(f.f.a.method, "other")
        val store = f.storage(emptyList(), listOf(
            f.f.a to f.row(f.p(AccessPathBase.Argument(0), f.t), f.c(0, f.t)),
            f.f.a to f.row(f.c(1), f.ret),
            other to f.row(f.c(0), f.c(1)),
        ))
        val actual = f.facts(f.p(AccessPathBase.Return, f.t))
        assertEquals(setOf(f.ap.initial(f.ret.copy(fact=f.ret.fact.copy(tail=Tail.EXACT))), f.ap.initial(f.p(AccessPathBase.Return, f.t).let { it.copy(fact=it.fact.copy(tail=Tail.EXACT)) })),
            store.initials(f.f.a, actual))
        assertTrue(store.initials(other, actual).isEmpty(), "A different context has no local reader attachment")
    }
}

package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.EngineShellFixtures
import org.opentaint.dataflow.bidi.store.*
import kotlin.test.*

/** Compare retained guides with the unfiltered walk, and count admitted work separately. */
class C5StaticPruningTest {
    private class Fixture {
        val f = EngineShellFixtures()
        val ap = f.manager
        val cls = ap.accessors.index(ClassStaticAccessor("C"))
        val fields = (0..2).map { f.field("s$it") }
        val t = MarkSlot.Concrete(ap.marks.mark("T"))
        val u = MarkSlot.Concrete(ap.marks.mark("U"))
        fun at(base: AccessPathBase, mark: MarkSlot = t) = Pattern(PathFact(base, emptyList(), Tail.STAR, mark), ExclusionSet.Empty)
        fun c(i: Int, mark: MarkSlot = t) = Pattern(PathFact(STATIC, listOf(cls, fields[i]), Tail.STAR, mark), ExclusionSet.Empty)
        val p get() = at(AccessPathBase.Argument(0))
        val ret get() = at(AccessPathBase.Return)
        fun snapshot(vararg rows: Pair<Pattern, Pattern>) =
            FrozenStaticCompletion.Builder(ap, DetachedStaticCallGraph.EMPTY).apply {
                rows.forEach { (from, to) -> addSeed(f.a, from, to) }
            }.build()
        fun keep(entry: Pattern, initial: InitialAp): Boolean =
            entry.fact.base == initial.base && entry.fact.path == initial.toPattern().fact.path && entry.fact.mark == initial.mark

        fun optimized(snapshot: FrozenCompletion, outputs: List<Pattern>): Pair<Set<DemandPattern>, Long> {
            val accepted = linkedSetOf<DemandPattern>()
            val stats = DemandQueryStatistics()
            val initial = ap.initial(ret)
            StaticPairLookup(ap, snapshot, stats, ::keep).walk(f.a, initial, outputs, false,
                { member, pair -> if (keep(pair.entry, member) && pair.exit in outputs) accepted += pair }, { false })
            return accepted to Regex("c5States=(\\d+)").find(stats.toString())!!.groupValues[1].toLong()
        }

        /** The prior worklist algorithm, with independent finite label composition. */
        fun unfiltered(snapshot: FrozenCompletion, outputs: List<Pattern>): Pair<Set<DemandPattern>, Long> {
            val view = snapshot.local(f.a)
            val initial = ap.initial(ret)
            val accepted = linkedSetOf<DemandPattern>()
            val seen = linkedSetOf<StaticGuidanceEdge>()
            val queue = ArrayDeque<StaticGuidanceEdge>()
            fun add(edge: StaticGuidanceEdge) { if (seen.add(edge)) queue += edge }
            if (view.hasComposedEndpoints(initial, outputs)) {
                view.targets(initial.toPattern(), true).forEach(::add)
                while (queue.isNotEmpty()) {
                    val right = queue.removeFirst()
                    val pair = DemandPattern(right.to, right.from)
                    if (keep(pair.entry, initial) && pair.exit in outputs) accepted += pair
                    for (left in view.incoming(right.from)) {
                        if (left.to.fact.path != right.from.fact.path) continue
                        val marks = when (val a = left.marks) {
                            GuidanceMarks.Flow -> right.marks
                            is GuidanceMarks.Mapped -> when (val b = right.marks) {
                                GuidanceMarks.Flow -> a
                                is GuidanceMarks.Mapped -> if (a.output != null && b.input != null &&
                                    (ap.marks.coversAtom(a.output, b.input) || ap.marks.coversAtom(b.input, a.output)))
                                    GuidanceMarks.Mapped(a.input, b.output) else null
                            }
                        } ?: continue
                        fun endpoint(p: Pattern, m: TaintMark?): Pattern = when {
                            p.fact.base == AccessPathBase.Zero -> p
                            marks == GuidanceMarks.Flow -> p.copy(fact = p.fact.copy(mark = MarkSlot.STAR))
                            else -> p.copy(fact = p.fact.copy(mark = MarkSlot.Concrete(checkNotNull(m))))
                        }
                        val mapped = marks as? GuidanceMarks.Mapped
                        add(StaticGuidanceEdge(endpoint(left.from, mapped?.input), endpoint(right.to, mapped?.output), marks))
                    }
                }
            }
            return accepted to seen.size.toLong()
        }
    }

    @Test fun `fixed incompatible reader removes all predecessor work before queue admission`() {
        val f = Fixture()
        val pU = f.at(AccessPathBase.Argument(0), f.u)
        val snapshot = f.snapshot(pU to f.c(0, f.u), f.c(0, f.u) to f.at(AccessPathBase.Return, f.u))
        val before = f.unfiltered(snapshot, listOf(pU))
        val after = f.optimized(snapshot, listOf(pU))
        assertEquals(before.first, after.first)
        assertTrue(after.first.isEmpty())
        assertEquals(2L, before.second)
        assertEquals(0L, after.second)
    }

    @Test fun `unfixed FLOW reader survives until mapped writer supplies the mark`() {
        val f = Fixture()
        val snapshot = f.snapshot(f.p to f.c(0), f.c(0, MarkSlot.STAR) to f.at(AccessPathBase.Return, MarkSlot.STAR))
        val before = f.unfiltered(snapshot, listOf(f.p))
        val after = f.optimized(snapshot, listOf(f.p))
        assertEquals(setOf(DemandPattern(f.ret, f.p)), after.first)
        assertEquals(before, after)
        assertEquals(2L, after.second)
    }

    @Test fun `left endpoint can be repaired and source preflight does not apply target predicate`() {
        val f = Fixture()
        val snapshot = f.snapshot(f.p to f.c(0), f.c(0) to f.c(1), f.c(1) to f.ret)
        val before = f.unfiltered(snapshot, listOf(f.p))
        val after = f.optimized(snapshot, listOf(f.p))
        assertEquals(setOf(DemandPattern(f.ret, f.p)), after.first)
        assertEquals(before, after)
        assertEquals(3L, after.second)
    }

    @Test fun `full writer joins GROUP input without enumerating group members`() {
        val f = Fixture()
        val group = MarkSlot.Concrete(f.ap.marks.group(f.ap.marks.groupOf(f.t.mark)))
        val snapshot = f.snapshot(f.p to f.c(0), f.c(0, group) to f.ret)
        val before = f.unfiltered(snapshot, listOf(f.p))
        val after = f.optimized(snapshot, listOf(f.p))
        assertEquals(setOf(DemandPattern(f.ret, f.p)), after.first)
        assertEquals(before, after)
        assertEquals(2L, after.second)
    }

    @Test fun `packed concrete label is restored before demand exclusion normalization`() {
        val f = Fixture()
        val excluded = ExclusionSet.of(f.f.field("child"))
        val right = f.c(1).copy(exclusion = excluded)
        val snapshot = f.snapshot(f.c(0) to right)
        val seen = arrayListOf<Pattern>()
        val original = f.ap.initial(f.c(1))
        StaticPairLookup(f.ap, snapshot, null) { entry, _ -> seen += entry; false }
            .walk(f.f.a, original, listOf(f.c(0)), false, { _, _ -> fail("Rejected right endpoint") }, { false })
        assertTrue(seen.isNotEmpty())
        assertTrue(seen.all { it.fact.mark == f.t && it.exclusion == excluded },
            "A placeholder FLOW mark must not erase a concrete STAR endpoint's E")
    }

    @Test fun `genuine ZERO writer and cycles keep their correlated colored answer`() {
        val f = Fixture()
        val zero = f.ap.zero.toPattern()
        val snapshot = f.snapshot(zero to f.c(0), f.c(0) to f.c(1), f.c(1) to f.c(0), f.c(1) to f.ret)
        val before = f.unfiltered(snapshot, listOf(zero))
        val after = f.optimized(snapshot, listOf(zero))
        assertEquals(setOf(DemandPattern(f.ret, zero)), after.first)
        assertEquals(before, after)
        assertEquals(3L, after.second)
    }
}

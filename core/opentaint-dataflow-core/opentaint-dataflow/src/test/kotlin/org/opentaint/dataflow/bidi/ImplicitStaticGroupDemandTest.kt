package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.fixtures.TestMark
import org.opentaint.dataflow.bidi.fixtures.testDeclarations
import org.opentaint.dataflow.bidi.store.DemandStore
import org.opentaint.dataflow.bidi.store.guidancePattern
import org.opentaint.dataflow.util.Cancellation
import kotlin.test.*

/** The old root-wide group family is replaced by same-position carry for FULL and FLOW. */
class ImplicitStaticGroupDemandTest {
    private val fixture = StoreFixtures(markDeclarations = testDeclarations(
        TestMark("T", MarkGroupKey.Rule("outer")), TestMark("U", MarkGroupKey.Rule("outer")),
        TestMark("V", MarkGroupKey.Rule("other")), TestMark("late", MarkGroupKey.Model("late")),
    ))
    private val m = fixture.manager
    private val ops = fixture.ops
    private val method = fixture.key("visited")
    private val unvisited = fixture.key("not visited", 7)
    private val cls = m.accessors.index(ClassStaticAccessor("C"))
    private val f = fixture.field("f")
    private val g = fixture.field("g")
    private val fulls = listOf(fixture.mark("T"), fixture.mark("U"), fixture.mark("V"))
    private fun pattern(mark: MarkSlot, path: List<Int> = listOf(cls, f), tail: Tail = Tail.ANY,
                        exclusion: ExclusionSet = ExclusionSet.Empty, base: AccessPathBase = STATIC) =
        Pattern(PathFact(base, path, tail, mark), exclusion)
    private fun pair(actual: Pattern) = guidancePattern(actual).let { DemandPattern(it, it) }
    private fun enabled() = DemandStore.Builder(m).apply { withSharedStaticCarry() }.build()

    @Test fun `carry preserves the same slot and full identity even in a method without a run1 actor`() {
        val store = enabled()
        for (mark in fulls + fixture.mark("late")) for (key in listOf(method, unvisited)) {
            val actual = pattern(MarkSlot.Concrete(mark))
            assertEquals(listOf(pair(actual)), store.near(key, actual))
            assertEquals(listOf(pair(actual)), store.covering(key, m.initial(actual)))
        }
        assertTrue(DemandStore.Builder(m).build().near(method, pattern(MarkSlot.Concrete(fulls[0]))).isEmpty())
    }

    @Test fun `carry never adds an exact start to an ANY input and supports shared FLOW`() {
        val store = enabled()
        for (mark in fulls.map { MarkSlot.Concrete(it) } + MarkSlot.STAR) {
            for (tail in listOf(Tail.ANY, Tail.STAR)) {
                val actual = pattern(mark, tail = tail)
                val input = m.factsOf(actual.fact, actual.exclusion, Layer.DEMAND)
                val starts = store.near(method, actual).flatMap { ops.emit(it, input) }
                assertEquals(setOf(m.initial(if (mark is MarkSlot.Star) flowForm(actual) else actual)), starts.toSet())
                assertTrue(starts.none { it.tail == Tail.EXACT })
            }
        }
    }

    @Test fun `carry cannot connect different static fields or exact class markers`() {
        val store = enabled()
        val actual = pattern(MarkSlot.Concrete(fulls[0]))
        val initial = m.initial(actual)
        val guide = store.covering(method, initial).single()
        for (other in listOf(pattern(actual.fact.mark, listOf(cls, g)),
            pattern(actual.fact.mark, listOf(cls), Tail.EXACT))) {
            assertTrue(ops.restrict(initial, m.factsOf(other.fact, other.exclusion, Layer.DEMAND), guide).isEmpty())
        }
        val identity = m.factsOf(actual.fact, actual.exclusion, Layer.DEMAND)
        assertTrue(ops.restrict(initial, identity, guide).isNotEmpty())
    }

    @Test fun `FLOW carry drops demand mark exclusions without manufacturing a concrete mark`() {
        val store = enabled()
        val actual = pattern(MarkSlot.Star(m.markSetOf(fulls[0])), tail = Tail.STAR)
        val guide = store.near(method, actual).single()
        assertEquals(MarkSlot.STAR, guide.entry.fact.mark)
        val input = m.factsOf(actual.fact, actual.exclusion, Layer.DEMAND)
        assertTrue(ops.emit(guide, input).all { it.mark is MarkSlot.Star })
        val concrete = pair(pattern(MarkSlot.Concrete(fulls[0])))
        assertTrue(ops.emit(concrete, input).isEmpty())
    }

    @Test fun `ordinary and ZERO demand stay separate from the static family`() {
        val store = enabled()
        val nonstatic = pattern(MarkSlot.Concrete(fulls[0]), base = AccessPathBase.Argument(0))
        assertTrue(store.near(method, nonstatic).isEmpty())
        assertTrue(store.covering(method, m.initial(nonstatic)).isEmpty())
        assertEquals(listOf(DemandPattern(m.zero.toPattern(), null)), store.near(unvisited, m.zero.toPattern()))
        assertTrue(store.covering(unvisited, m.zero).isEmpty())
    }

    @Test fun `carry lookup checks cancellation`() {
        val store = enabled()
        val actual = pattern(MarkSlot.Concrete(fulls[0]))
        val initial = m.initial(actual)
        fixture.cancellation.cancel()
        assertFailsWith<Cancellation.Cancelled> { store.near(unvisited, actual) }
        assertFailsWith<Cancellation.Cancelled> { store.covering(unvisited, initial) }
    }
}

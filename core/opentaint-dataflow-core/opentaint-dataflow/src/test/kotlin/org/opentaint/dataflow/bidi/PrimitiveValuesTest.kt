package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.bidi.fixtures.testApManager

import org.opentaint.dataflow.bidi.ap.ReferenceRequestAction as RequestAction

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.ap.ReferenceRequestKind as RequestKind
import org.opentaint.dataflow.util.Cancellation
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFails
import kotlin.test.assertFalse
import kotlin.test.assertIs
import kotlin.test.assertSame
import kotlin.test.assertTrue

class PrimitiveValuesTest {
    private val m = testApManager(Cancellation())
    private val t = m.marks.mark("T")
    private val f = m.accessors.index(FieldAccessor("Box", "f", "Box"))
    private fun literal(base: AccessPathBase, tail: Tail = Tail.EXACT) =
        Pattern(PathFact(base, emptyList(), tail, MarkSlot.Concrete(t)), ExclusionSet.Empty)

    @Test
    fun `cleaner never targets zero and keeps its specified geometry`() {
        assertFails { Cleaner(AccessPathBase.Zero, null, CleanReach.EXACT, t) }
        val path = m.path(intArrayOf(f))
        val cleaner = Cleaner(AccessPathBase.This, path, CleanReach.BELOW, t)
        assertSame(path, cleaner.path)
        assertEquals(CleanReach.BELOW, cleaner.reach)
        assertEquals(t, cleaner.mark)
    }

    @Test
    fun `joint rules require concrete nonstar literals and exact or must targets`() {
        val a = literal(AccessPathBase.Argument(0))
        val b = literal(AccessPathBase.Argument(1), Tail.ANY)
        val target = PathFact(AccessPathBase.Return, emptyList(), Tail.ANY_TAINT, MarkSlot.Concrete(t))
        assertEquals(listOf(a, b), ConjunctiveEdge(listOf(a, b), target).literals)
        assertFails { ConjunctiveEdge(listOf(a), target) }
        assertFails { ConjunctiveEdge(listOf(a, b.copy(fact = b.fact.copy(mark = MarkSlot.STAR))), target) }
        assertFails { ConjunctiveEdge(listOf(a, b.copy(fact = b.fact.copy(tail = Tail.STAR))), target) }
        assertFails { ConjunctiveEdge(listOf(a, b), target.copy(tail = Tail.ANY)) }
        assertFails { ConjunctiveEdge(listOf(a, b), target.copy(mark = MarkSlot.STAR)) }
        assertFails { ConjunctiveEdge(listOf(a, b), target.copy(base = AccessPathBase.Zero)) }
    }

    @Test
    fun `path filter conjunction retains both successor constraints`() {
        val rejectElements = object : FactTypeChecker.FactApFilter {
            override fun check(accessor: org.opentaint.dataflow.ap.ifds.Accessor): FactTypeChecker.FilterResult =
                if (accessor == ElementAccessor) FactTypeChecker.FilterResult.Reject else FactTypeChecker.FilterResult.Accept
        }
        val first = object : FactTypeChecker.FactApFilter {
            override fun check(accessor: org.opentaint.dataflow.ap.ifds.Accessor) = FactTypeChecker.FilterResult.FilterNext(rejectElements)
        }
        val second = object : FactTypeChecker.FactApFilter {
            override fun check(accessor: org.opentaint.dataflow.ap.ifds.Accessor) =
                FactTypeChecker.FilterResult.FilterNext(FactTypeChecker.AlwaysAcceptFilter)
        }
        val result = assertIs<FactTypeChecker.FilterResult.FilterNext>(TypeFilter(first).and(TypeFilter(second)).may.check(ElementAccessor))
        assertSame(FactTypeChecker.FilterResult.Reject, result.filter.check(ElementAccessor))
        assertSame(FactTypeChecker.FilterResult.Accept, result.filter.check(FieldAccessor("Box", "f", "Box")))
        assertSame(FactTypeChecker.FilterResult.Reject,
            TypeFilter(FactTypeChecker.AlwaysAcceptFilter).and(TypeFilter(rejectElements)).may.check(ElementAccessor))
    }

    @Test
    fun `mark policy conjunction reads both policies at the same element level`() {
        val a = MarkPolicy { mark, _ -> mark == t }
        val b = MarkPolicy { _, level -> level == 2 }
        val filter = FactTypeChecker.AlwaysAcceptFilter
        val combined = requireNotNull(TypeFilter(filter, a).and(TypeFilter(filter, b)).markPolicy)
        assertTrue(combined.keeps(t, 2))
        assertFalse(combined.keeps(t, 1))
        assertFalse(combined.keeps(m.marks.mark("U"), 2))
        assertSame(a, TypeFilter(filter, a).and(TypeFilter(filter)).markPolicy)
        assertSame(b, TypeFilter(filter).and(TypeFilter(filter, b)).markPolicy)
    }

    @Test
    fun `level policy knows its boxed levels and the conjunction keeps the level decision (G6 drop form)`() {
        val u = m.marks.mark("U")
        // Level 0: Integer[] (no drop), level 1: Integer (boxed); a second type: int[] (level 1 primitive, not boxed).
        val boxed = LevelMarkPolicy(booleanArrayOf(false, true), booleanArrayOf(false, true), primitiveTracking = { it == u })
        val primitive = LevelMarkPolicy(booleanArrayOf(false, true), booleanArrayOf(false, false), primitiveTracking = { it == u })
        assertTrue(boxed.keeps(t, 0)); assertFalse(boxed.keeps(t, 1)); assertTrue(boxed.keeps(u, 1)); assertTrue(boxed.keeps(t, 2))
        assertFalse(boxed.boxedLevel(0)); assertTrue(boxed.boxedLevel(1)); assertFalse(boxed.boxedLevel(2))
        assertTrue(boxed.dropsValue(t, 1)); assertFalse(boxed.dropsValue(u, 1)); assertFalse(boxed.dropsValue(t, 0))
        assertFalse(primitive.boxedLevel(1)); assertFalse(primitive.dropsValue(t, 1)); assertFalse(primitive.keeps(t, 1))
        assertFails { LevelMarkPolicy(booleanArrayOf(false), booleanArrayOf(true), primitiveTracking = { false }) }
        val filter = FactTypeChecker.AlwaysAcceptFilter
        val both = requireNotNull(TypeFilter(filter, boxed).and(TypeFilter(filter, primitive)).markPolicy)
        assertFalse(both.keeps(t, 1)); assertTrue(both.keeps(t, 0)); assertTrue(both.boxedLevel(1)); assertTrue(both.dropsValue(t, 1))
        val plain = MarkPolicy { mark, _ -> mark == u }
        assertFalse(plain.boxedLevel(0)); assertFalse(plain.dropsValue(t, 0))
    }

    @Test
    fun `request action values retain the answered and caller premises separately`() {
        val initial = m.initial(literal(AccessPathBase.Argument(0)))
        val request = RequestKind.Mark(t)
        assertSame(initial, RequestAction.Answer(initial).initial)
        val climb = RequestAction.Climb(initial, request)
        assertSame(initial, climb.premise)
        assertEquals(request, climb.request)
        val position = requireNotNull(m.path(intArrayOf(f)))
        assertSame(position, RequestKind.Position(position).path)
        assertSame(RequestAction.None, RequestAction.None)
    }
}

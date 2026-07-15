package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.MethodSummaryEdgeApplicationUtils
import org.opentaint.dataflow.ap.ifds.MethodSummaryEdgeApplicationUtils.SummaryEdgeApplication
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertNull
import kotlin.test.assertTrue

class BaseOnlyDeltaTest {
    private val arg0 = AccessPathBase.Argument(0)
    private val field = FieldAccessor("A", "f", "B")
    private val mark = TaintMarkAccessor("m")
    private val mark2 = TaintMarkAccessor("m2")

    private fun mgr(fieldSensitive: Boolean = false) =
        BaseOnlyApManager(AnyAccessorUnrollStrategy.AnyAccessorDisabled, fieldSensitive = fieldSensitive)

    private fun BaseOnlyApManager.finalOf(vararg accessors: Accessor): BaseOnlyFinalFactAp {
        var f: FinalFactAp = createFinalAp(arg0, ExclusionSet.Empty)
        accessors.reversed().forEach { f = f.prependAccessor(it) }
        return f as BaseOnlyFinalFactAp
    }

    private fun BaseOnlyApManager.abstractInitialOf(vararg accessors: Accessor): InitialFactAp {
        var f = mostAbstractInitialAp(arg0)
        accessors.reversed().forEach { f = f.prependAccessor(it) }
        return f
    }

    @Test
    fun `delta yields the suffix beyond the initial prefix`() {
        val m = mgr()
        val f = m.finalOf(AnyAccessor, mark)
        val i = m.abstractInitialOf(AnyAccessor)
        val deltas = f.delta(i)
        assertEquals(1, deltas.size)
        val d = deltas.single()
        assertFalse(d.isEmpty)
        assertTrue(d.startsWithAccessor(mark))
    }

    @Test
    fun `concat re-appends the delta to reconstruct the fact`() {
        val m = mgr()
        val f = m.finalOf(AnyAccessor, mark)
        val prefix = m.mostAbstractFinalAp(arg0)
        val d = f.delta(m.abstractInitialOf(AnyAccessor)).single()
        assertEquals(f, prefix.concat(FactTypeChecker.Dummy, d))
    }

    @Test
    fun `equal fact and prefix yield empty delta`() {
        val m = mgr()
        val f = m.finalOf(mark)
        val i = m.abstractInitialOf(mark)
        assertTrue(f.hasEmptyDelta(i))
        assertTrue(f.delta(i).any { it.isEmpty })
    }

    @Test
    fun `value fact against abstract prefix yields a value delta not empty`() {
        val m = mgr()
        val f = m.finalOf()                        // arg0.$  (value itself)
        val i = m.abstractInitialOf(AnyAccessor)   // arg0.*
        val deltas = f.delta(i)
        assertTrue(deltas.none { it.isEmpty })
        val d = deltas.single()
        // concatenating onto an abstract result must stay a value (.$), not widen to .*
        val result = m.mostAbstractFinalAp(arg0).concat(FactTypeChecker.Dummy, d)
        assertEquals(m.finalOf(), result)
    }

    @Test
    fun `AP@suffix prefix is kind-strict on fields and AP@suffix with the field committed still matches`() {
        val m = mgr(fieldSensitive = true)
        val f = m.finalOf(field, AnyAccessor, mark)
        assertTrue(f.delta(m.abstractInitialOf(AnyAccessor)).isEmpty())
        val d = f.delta(m.abstractInitialOf(field, AnyAccessor)).single()
        assertFalse(d.isEmpty)
    }

    @Test
    fun `summary application produces a refinement for a non-empty delta`() {
        val m = mgr()
        val f = m.finalOf(AnyAccessor, mark)
        val i = m.abstractInitialOf(AnyAccessor)
        val results = MethodSummaryEdgeApplicationUtils.tryApplySummaryEdge(f, i)
        assertEquals(1, results.size)
        assertTrue(results.single() is SummaryEdgeApplication.SummaryApRefinement)
    }

    @Test
    fun `summary application produces an exclusion refinement for an empty delta`() {
        val m = mgr()
        val f = m.finalOf(mark)
        val i = m.abstractInitialOf(mark)
        val results = MethodSummaryEdgeApplicationUtils.tryApplySummaryEdge(f, i)
        assertTrue(results.any { it is SummaryEdgeApplication.SummaryExclusionRefinement })
    }

    @Test
    fun `equalTo matches a final fact against its final-accessor initial`() {
        val m = mgr()
        val f = m.finalOf(mark)
        var i = m.createFinalInitialAp(arg0, ExclusionSet.Empty)
        i = i.prependAccessor(mark)
        assertTrue(f.equalTo(i))
    }

    @Test
    fun `append does not stack a second terminal after a taint mark`() {
        val m = mgr()
        val terminated = m.finalOf(AnyAccessor, mark).access
        val extra = m.finalOf(mark2).access
        val appended = BaseOnlyAccessOps.append(terminated, extra)!!
        assertEquals(m.finalOf(AnyAccessor, mark).access, appended)
        var markCount = 0
        var hasMark2 = false
        appended.forEachAccessorIdx {
            if (it == m.interner.index(mark)) markCount++
            if (it == m.interner.index(mark2)) hasMark2 = true
        }
        assertEquals(1, markCount)
        assertFalse(hasMark2)
    }

    @Test
    fun `concat of a non-empty delta onto a closed mark fact is rejected`() {
        val m = mgr()
        val terminated = m.finalOf(AnyAccessor, mark)
        val delta = BaseOnlyNodeFinalDelta(m, m.finalOf(mark2).access)
        assertNull(terminated.concat(FactTypeChecker.Dummy, delta))
    }

    @Test
    fun `concat of a non-empty delta onto a closed value fact is rejected`() {
        val m = mgr()
        val delta = BaseOnlyNodeFinalDelta(m, m.finalOf(mark).access)
        assertNull(m.finalOf().concat(FactTypeChecker.Dummy, delta))
    }

    @Test
    fun `concat grafts a terminal onto an abstract receiver`() {
        val m = mgr()
        val delta = BaseOnlyNodeFinalDelta(m, m.finalOf(mark).access)
        assertEquals(m.finalOf(mark), m.mostAbstractFinalAp(arg0).concat(FactTypeChecker.Dummy, delta))
    }

    @Test
    fun `contains holds for an exact match and not for a proper prefix`() {
        val m = mgr()
        val f = m.finalOf(AnyAccessor, mark)
        assertTrue(f.contains(m.abstractInitialOf(AnyAccessor, mark)))
        assertFalse(f.contains(m.abstractInitialOf(AnyAccessor)))
    }
}

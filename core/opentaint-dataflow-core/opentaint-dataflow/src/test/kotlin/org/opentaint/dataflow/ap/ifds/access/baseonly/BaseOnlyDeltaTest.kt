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
import org.opentaint.dataflow.ap.ifds.FinalAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.ir.api.common.CommonType
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertNotNull
import kotlin.test.assertNull
import kotlin.test.assertTrue

class BaseOnlyDeltaTest {
    private val arg0 = AccessPathBase.Argument(0)
    private val field = FieldAccessor("A", "f", "B")
    private val mark = TaintMarkAccessor("m")
    private val mark2 = TaintMarkAccessor("m2")

    private fun mgr(fieldSensitive: Boolean = false) =
        BaseOnlyApManager(AnyAccessorUnrollStrategy.AnyAccessorDisabled, org.opentaint.dataflow.util.Cancellation(), fieldSensitive = fieldSensitive)

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
    fun `concat re-appends the semantic delta at the supplied abstract root`() {
        val m = mgr()
        val f = m.finalOf(AnyAccessor, mark)
        val prefix = m.mostAbstractFinalAp(arg0)
        val d = f.delta(m.abstractInitialOf(AnyAccessor)).single()
        val reconstructed = prefix.concat(FactTypeChecker.Dummy, d)
        assertEquals(m.finalOf(mark), reconstructed)
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
    fun `split delta preserves concrete field between field and suffix abstractions`() {
        val m = mgr(fieldSensitive = true)
        val callerFact = m.abstractInitialOf(field, AnyAccessor) as BaseOnlyInitialFactAp
        val fieldAbstractAccess = BaseOnlyAccessOps.abstractAt(NO_ACCESSOR, NO_ACCESSOR, 1)
        val summaryFinal = BaseOnlyFinalFactAp(m, arg0, fieldAbstractAccess, ExclusionSet.Empty)

        val (matched, delta) = callerFact.splitDelta(summaryFinal).single()
        assertEquals(fieldAbstractAccess, (matched as BaseOnlyInitialFactAp).access)
        assertTrue(delta is BaseOnlyNodeInitialDelta)
        assertEquals(callerFact.access, delta.access)

        val mappedSummaryInitial = BaseOnlyInitialFactAp(m, arg0, fieldAbstractAccess, ExclusionSet.Empty)
        assertEquals(callerFact, mappedSummaryInitial.concat(delta))
    }

    @Test
    fun `split delta preserves suffix abstraction after a field abstract summary`() {
        val m = mgr(fieldSensitive = true)
        val callerFact = m.abstractInitialOf(AnyAccessor) as BaseOnlyInitialFactAp
        val fieldAbstractAccess = BaseOnlyAccessOps.abstractAt(NO_ACCESSOR, NO_ACCESSOR, 1)
        val summaryFinal = BaseOnlyFinalFactAp(m, arg0, fieldAbstractAccess, ExclusionSet.Empty)

        val (matched, delta) = callerFact.splitDelta(summaryFinal).single()
        assertEquals(fieldAbstractAccess, (matched as BaseOnlyInitialFactAp).access)
        assertTrue(delta is BaseOnlyNodeInitialDelta)
        assertEquals(callerFact.access, delta.access)

        val mappedSummaryInitial = BaseOnlyInitialFactAp(m, arg0, fieldAbstractAccess, ExclusionSet.Empty)
        assertEquals(callerFact, mappedSummaryInitial.concat(delta))
    }

    @Test
    fun `split delta retains implicit Any continuation after structural alignment`() {
        val m = mgr(fieldSensitive = true)
        var callerFact = m.createFinalInitialAp(arg0, ExclusionSet.Empty)
        callerFact = callerFact.prependAccessor(mark)
        callerFact = callerFact.prependAccessor(field)
        val summaryAccess = BaseOnlyAccessOps.abstractAt(NO_ACCESSOR, m.interner.index(field), 2)

        val oneCompactBranchExcluded = BaseOnlyFinalFactAp(
            m,
            arg0,
            summaryAccess,
            ExclusionSet.Empty.add(mark),
        )
        val directRetained = callerFact.splitDelta(oneCompactBranchExcluded).single().second
            as BaseOnlyNodeInitialDelta
        assertEquals(BaseOnlyValueAccessorState.Normal, directRetained.access.valueAccessorState)

        val allBranchesExcluded = BaseOnlyFinalFactAp(
            m,
            arg0,
            summaryAccess,
            ExclusionSet.Universe,
        )
        assertTrue(callerFact.splitDelta(allBranchesExcluded).isEmpty())
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
    fun `AP@suffix Any prefix matches a retained concrete field`() {
        val m = mgr(fieldSensitive = true)
        val f = m.finalOf(field, AnyAccessor, mark)
        assertTrue(f.delta(m.abstractInitialOf(AnyAccessor)).isNotEmpty())
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

    @Test
    fun `final delta checks base before matching`() {
        val m = mgr()
        val initial = BaseOnlyInitialFactAp(
            m,
            AccessPathBase.Argument(1),
            m.finalOf(mark).access,
            ExclusionSet.Empty,
        )
        assertTrue(m.finalOf(mark).delta(initial).isEmpty())
    }

    @Test
    fun `final concat uses path filter rather than compatibility filter`() {
        val m = mgr()
        val checker = object : FactTypeChecker {
            override fun filterFactByLocalType(actualType: CommonType?, factAp: FinalFactAp): FinalFactAp? = factAp
            override fun accessPathFilter(accessPath: List<Accessor>): FactTypeChecker.FactApFilter =
                FactTypeChecker.AlwaysAcceptFilter
            override fun accessPathCompatibilityFilter(accessPath: List<Accessor>): FactTypeChecker.FactCompatibilityFilter =
                object : FactTypeChecker.FactCompatibilityFilter {
                    override fun check(accessor: Accessor): FactTypeChecker.CompatibilityFilterResult =
                        if (accessor == mark) FactTypeChecker.CompatibilityFilterResult.NotCompatible
                        else FactTypeChecker.CompatibilityFilterResult.Compatible
                }
        }
        val delta = BaseOnlyNodeFinalDelta(m, m.finalOf(mark).access)
        assertEquals(m.finalOf(mark), m.mostAbstractFinalAp(arg0).concat(checker, delta))
    }

    @Test
    fun `final concat advances the supplied path filter through the delta`() {
        val m = mgr(fieldSensitive = true)
        val seenPrefixes = mutableListOf<List<Accessor>>()
        val rejectAfterMark = object : FactTypeChecker.FactApFilter {
            override fun check(accessor: Accessor): FactTypeChecker.FilterResult =
                if (accessor == FinalAccessor) FactTypeChecker.FilterResult.Reject
                else FactTypeChecker.FilterResult.Accept
        }
        val checker = object : FactTypeChecker {
            override fun filterFactByLocalType(actualType: CommonType?, factAp: FinalFactAp): FinalFactAp? = factAp
            override fun accessPathFilter(accessPath: List<Accessor>): FactTypeChecker.FactApFilter {
                seenPrefixes += accessPath
                return object : FactTypeChecker.FactApFilter {
                    override fun check(accessor: Accessor): FactTypeChecker.FilterResult =
                        if (accessor == mark) FactTypeChecker.FilterResult.FilterNext(rejectAfterMark)
                        else FactTypeChecker.FilterResult.Reject
                }
            }
            override fun accessPathCompatibilityFilter(accessPath: List<Accessor>): FactTypeChecker.FactCompatibilityFilter =
                FactTypeChecker.AlwaysCompatibleFilter
        }
        val receiver = BaseOnlyFinalFactAp(
            m,
            arg0,
            BaseOnlyAccessOps.abstractAt(NO_ACCESSOR, m.interner.index(field), 2),
            ExclusionSet.Empty,
        )
        val delta = BaseOnlyNodeFinalDelta(m, m.finalOf(mark).access)

        assertNull(receiver.concat(checker, delta))
        assertEquals(listOf<Accessor>(field), seenPrefixes.single())
    }

    @Test
    fun `abstractOnly preserves existing AP position and collapsed facts are transient until rebase`() {
        val m = mgr(fieldSensitive = true)
        val fact = m.finalOf(field, AnyAccessor, mark)
        assertEquals(m.mostAbstractFinalAp(arg0), fact.abstractOnly())

        for (access in listOf(
            packBaseOnlyAccess(ABSTRACT_MARK, NO_ACCESSOR, NO_ACCESSOR),
            packBaseOnlyAccess(NO_ACCESSOR, ABSTRACT_MARK, NO_ACCESSOR),
        )) {
            val positioned = BaseOnlyFinalFactAp(m, arg0, access, ExclusionSet.Empty)
            assertEquals(positioned, positioned.abstractOnly())
        }

        val rootTransient = fact.abstractOnly().removeAbstraction()
        assertNotNull(rootTransient)
        assertFalse(rootTransient.isAbstract())
        assertEquals(fact.abstractOnly(), rootTransient.rebase(arg0))

        val collapsed = packBaseOnlyAccess(NO_ACCESSOR, m.interner.index(field), COLLAPSED_MARK)
        val transient = BaseOnlyFinalFactAp(m, arg0, collapsed, ExclusionSet.Empty)
        assertFalse(transient.isAbstract())
        assertEquals(
            BaseOnlyFinalFactAp(
                m,
                arg0,
                BaseOnlyAccessOps.abstractAt(NO_ACCESSOR, m.interner.index(field), 2),
                ExclusionSet.Empty,
            ),
            transient.rebase(arg0),
        )
        assertTrue(collapsed.isCollapsed)
    }
}

package org.opentaint.dataflow.ap.ifds.trace.action

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.baseonly.BaseOnlyApManager
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEdge
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEntryAction.TraceSummaryEdge
import org.opentaint.dataflow.util.Cancellation
import kotlin.test.Test
import kotlin.test.assertFalse
import kotlin.test.assertTrue

class TraceActionSummaryRelevanceTest {
    private val manager = BaseOnlyApManager(
        AnyAccessorUnrollStrategy.AnyAccessorDisabled,
        Cancellation(),
        fieldSensitive = true,
    )
    private val markA = TaintMarkAccessor("a")
    private val markB = TaintMarkAccessor("b")

    private fun fact(base: AccessPathBase, mark: TaintMarkAccessor? = null): InitialFactAp {
        val fact = manager.mostAbstractInitialAp(base)
        return if (mark == null) fact else fact.prependAccessor(mark)
    }

    private fun methodSummary(
        before: InitialFactAp,
        after: InitialFactAp,
    ): TraceSummaryEdge.MethodSummary {
        val initial = fact(AccessPathBase.Argument(0))
        return TraceSummaryEdge.MethodSummary(
            edge = TraceEdge.MethodTraceEdge(initial, before),
            edgeAfter = TraceEdge.MethodTraceEdge(initial, after),
            delta = null,
        )
    }

    @Test
    fun `method summary with the same mark is irrelevant`() {
        val summary = methodSummary(
            before = fact(AccessPathBase.This, markA),
            after = fact(AccessPathBase.Return, markA),
        )

        assertFalse(setOf(summary).introducesOrChangesTaintMarks())
    }

    @Test
    fun `method summary with a different mark is relevant`() {
        val summary = methodSummary(
            before = fact(AccessPathBase.This, markA),
            after = fact(AccessPathBase.Return, markB),
        )

        assertTrue(setOf(summary).introducesOrChangesTaintMarks())
    }

    @Test
    fun `method summary that introduces or removes a mark is relevant`() {
        val introduced = methodSummary(
            before = fact(AccessPathBase.This),
            after = fact(AccessPathBase.Return, markA),
        )
        val removed = methodSummary(
            before = fact(AccessPathBase.This, markA),
            after = fact(AccessPathBase.Return),
        )

        assertTrue(setOf(introduced).introducesOrChangesTaintMarks())
        assertTrue(setOf(removed).introducesOrChangesTaintMarks())
    }

    @Test
    fun `source summary is always relevant`() {
        val edge = TraceEdge.SourceTraceEdge(fact(AccessPathBase.Return, markA))
        val summary = TraceSummaryEdge.SourceSummary(edge, edge)

        assertTrue(setOf(summary).introducesOrChangesTaintMarks())
    }
}

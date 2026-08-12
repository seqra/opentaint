package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEdge
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEdges
import org.opentaint.dataflow.util.Cancellation
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertNotEquals
import kotlin.test.assertTrue

class BaseOnlyTracePremiseSubsumptionLawTest {
    @Test
    fun `abstract and mark-specific initial premises are distinct and do not subsume each other`() {
        val manager = BaseOnlyApManager(
            AnyAccessorUnrollStrategy.AnyAccessorDisabled,
            Cancellation(),
            fieldSensitive = true,
        )
        val base = AccessPathBase.Argument(0)
        val abstractPremise = manager.mostAbstractInitialAp(base)
            .replaceExclusions(ExclusionSet.Universe)
        val markPremise = manager.createFinalInitialAp(base, ExclusionSet.Universe)
            .prependAccessor(TaintMarkAccessor("trace-premise-cartesian"))
        val abstractIncoming = manager.mostAbstractFinalAp(base)
            .replaceExclusions(ExclusionSet.Universe)
        val markIncoming = manager.createFinalAp(base, ExclusionSet.Universe)
            .prependAccessor(TaintMarkAccessor("trace-premise-cartesian"))

        assertNotEquals(abstractPremise, markPremise)
        assertFalse(abstractPremise.contains(markPremise))
        assertFalse(markPremise.contains(abstractPremise))
        assertTrue(abstractIncoming.equalTo(abstractPremise))
        assertTrue(abstractIncoming.contains(abstractPremise))
        assertFalse(
            abstractIncoming.contains(markPremise),
            "$abstractIncoming satisfies $abstractPremise but not the stronger $markPremise",
        )
        assertFalse(markIncoming.contains(abstractPremise))
        assertTrue(markIncoming.equalTo(markPremise))
        assertTrue(markIncoming.contains(markPremise))
    }

    @Test
    fun `collapsing conjunctive conclusions distributes premises instead of OR merging them`() {
        val manager = BaseOnlyApManager(
            AnyAccessorUnrollStrategy.AnyAccessorDisabled,
            Cancellation(),
            fieldSensitive = true,
        )
        fun fact(base: AccessPathBase, mark: String) = manager
            .createFinalInitialAp(base, ExclusionSet.Universe)
            .prependAccessor(TaintMarkAccessor(mark))

        val leftConclusion = fact(AccessPathBase.Return, "left")
        val rightConclusion = fact(AccessPathBase.Return, "right")
        val target = fact(AccessPathBase.Return, "target")
        val leftPremises = listOf(
            fact(AccessPathBase.Argument(0), "a0"),
            fact(AccessPathBase.Argument(1), "a1"),
        )
        val rightPremises = listOf(
            fact(AccessPathBase.Argument(2), "b0"),
            fact(AccessPathBase.Argument(3), "b1"),
        )
        val formula = TraceEdges.of(
            leftPremises.map { TraceEdge.MethodTraceEdge(it, leftConclusion) } +
                rightPremises.map { TraceEdge.MethodTraceEdge(it, rightConclusion) }
        )

        val collapsed = formula.collapseToFact(target)
        val alternatives = collapsed.premisesByFinalFact.getValue(target)

        assertEquals(4, alternatives.size)
        assertTrue(alternatives.all { it is TraceEdge.MethodTraceNDEdge })
        assertEquals(
            setOf(
                setOf(leftPremises[0], rightPremises[0]),
                setOf(leftPremises[0], rightPremises[1]),
                setOf(leftPremises[1], rightPremises[0]),
                setOf(leftPremises[1], rightPremises[1]),
            ),
            alternatives.mapTo(hashSetOf()) { (it as TraceEdge.MethodTraceNDEdge).initialFacts },
        )
    }
}

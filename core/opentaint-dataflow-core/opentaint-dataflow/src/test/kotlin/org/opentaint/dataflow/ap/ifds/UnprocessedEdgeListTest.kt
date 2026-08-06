package org.opentaint.dataflow.ap.ifds

import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.baseonly.BaseOnlyApManager
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.CommonMethodParameter
import org.opentaint.ir.api.common.CommonTypeName
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.common.cfg.CommonInstLocation
import org.opentaint.ir.api.common.cfg.ControlFlowGraph
import java.lang.reflect.Proxy
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue

class UnprocessedEdgeListTest {
    private val method = object : CommonMethod {
        override val name: String = "method"
        override val parameters: List<CommonMethodParameter> = emptyList()
        override val returnType: CommonTypeName = object : CommonTypeName {
            override val typeName: String = "void"
        }

        override fun flowGraph(): ControlFlowGraph<CommonInst> = error("unused")
    }

    private fun statement(name: String) = object : CommonInst {
        override val location: CommonInstLocation = object : CommonInstLocation {
            override val method: CommonMethod = this@UnprocessedEdgeListTest.method
        }

        override fun toString(): String = name
    }

    @Test
    fun `zero to zero edges are removed before all other edges`() {
        val manager = BaseOnlyApManager(AnyAccessorUnrollStrategy.AnyAccessorDisabled, Cancellation())
        val entryStatement = statement("entry")
        val entryPoint = MethodEntryPoint(EmptyMethodContext, entryStatement)
        val queue = EdgeCollection.UnprocessedEdgeList(manager, entryPoint)
        val zeroFact = manager.createFinalAp(AccessPathBase.This, ExclusionSet.Universe)

        val ordinaryFirst = Edge.ZeroToFact(entryPoint, statement("ordinary-first"), zeroFact)
        val zeroFirst = Edge.ZeroToZero(entryPoint, statement("zero-first"))
        val ordinaryLast = Edge.ZeroToFact(entryPoint, statement("ordinary-last"), zeroFact)
        val zeroLast = Edge.ZeroToZero(entryPoint, statement("zero-last"))

        queue.add(ordinaryFirst)
        queue.add(zeroFirst)
        queue.add(ordinaryLast)
        queue.add(zeroLast)

        assertEquals(4, queue.size)
        assertTrue(queue.containsZeroToZeroEdges)
        assertEquals(zeroLast, queue.removeLast())
        assertTrue(queue.containsZeroToZeroEdges)
        assertEquals(zeroFirst, queue.removeLast())
        assertFalse(queue.containsZeroToZeroEdges)
        assertEquals(ordinaryLast, queue.removeLast())
        assertEquals(ordinaryFirst, queue.removeLast())
        assertTrue(queue.isEmpty)
    }

    @Test
    fun `analyzers with unprocessed zero to zero edges have highest event priority`() {
        val zeroToZeroAnalyzer = analyzer(containsZeroToZeroEdges = true, steps = 100)
        val earlyOrdinaryAnalyzer = analyzer(containsZeroToZeroEdges = false, steps = 1)
        val lateOrdinaryAnalyzer = analyzer(containsZeroToZeroEdges = false, steps = 10)
        val nonAnalyzerEvent = Any()
        val comparator = TaintAnalysisUnitRunner.EventComparator

        assertTrue(comparator.compare(zeroToZeroAnalyzer, earlyOrdinaryAnalyzer) < 0)
        assertTrue(comparator.compare(zeroToZeroAnalyzer, nonAnalyzerEvent) < 0)
        assertTrue(comparator.compare(nonAnalyzerEvent, earlyOrdinaryAnalyzer) < 0)
        assertTrue(comparator.compare(earlyOrdinaryAnalyzer, lateOrdinaryAnalyzer) < 0)
    }

    private fun analyzer(containsZeroToZeroEdges: Boolean, steps: Long): MethodAnalyzer =
        Proxy.newProxyInstance(
            MethodAnalyzer::class.java.classLoader,
            arrayOf(MethodAnalyzer::class.java),
        ) { _, method, _ ->
            when (method.name) {
                "getContainsUnprocessedZeroToZeroEdges" -> containsZeroToZeroEdges
                "getAnalyzerSteps" -> steps
                else -> error("Unexpected MethodAnalyzer operation: ${method.name}")
            }
        } as MethodAnalyzer
}

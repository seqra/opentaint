package org.opentaint.dataflow.ap.ifds.trace

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.EmptyMethodContext
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.baseonly.BaseOnlyApManager
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.SummaryTrace
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEdge
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEntry
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceKind
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.CommonMethodParameter
import org.opentaint.ir.api.common.CommonTypeName
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.common.cfg.CommonInstLocation
import org.opentaint.ir.api.common.cfg.ControlFlowGraph
import kotlin.test.Test
import kotlin.test.assertEquals

class SummaryTraceNormalizationTest {
    @Test
    fun `resolution identity ignores exclusions on every edge fact`() {
        val first = summary(ExclusionSet.Empty)
        val second = summary(ExclusionSet.Concrete(TaintMarkAccessor("excluded")))

        assertEquals(first.withUniverseExclusions(), second.withUniverseExclusions())
        first.withUniverseExclusions().final.edges.forEach { edge ->
            assertEquals(ExclusionSet.Universe, edge.fact.exclusions)
            when (edge) {
                is TraceEdge.MethodTraceEdge ->
                    assertEquals(ExclusionSet.Universe, edge.initialFact.exclusions)

                is TraceEdge.MethodTraceNDEdge -> edge.initialFacts.forEach {
                    assertEquals(ExclusionSet.Universe, it.exclusions)
                }

                is TraceEdge.SourceTraceEdge -> Unit
            }
        }
    }

    private fun summary(exclusions: ExclusionSet): SummaryTrace {
        val first = fact(AccessPathBase.Argument(0), "first", exclusions)
        val second = fact(AccessPathBase.Argument(1), "second", exclusions)
        val final = fact(AccessPathBase.Return, "final", exclusions)
        return SummaryTrace(
            MethodEntryPoint(EmptyMethodContext, statement),
            TraceEntry.Final(
                setOf(
                    TraceEdge.SourceTraceEdge(final),
                    TraceEdge.MethodTraceEdge(first, final),
                    TraceEdge.MethodTraceNDEdge(setOf(first, second), final),
                ),
                statement,
            ),
            TraceKind.SummaryTrace,
        )
    }

    private fun fact(base: AccessPathBase, mark: String, exclusions: ExclusionSet): InitialFactAp =
        manager.mostAbstractInitialAp(base)
            .prependAccessor(TaintMarkAccessor(mark))
            .replaceExclusions(exclusions)

    private val manager = BaseOnlyApManager(
        AnyAccessorUnrollStrategy.AnyAccessorDisabled,
        Cancellation(),
        fieldSensitive = true,
    )

    private val statement = object : CommonInst {
        override val location: CommonInstLocation = object : CommonInstLocation {
            override val method: CommonMethod = object : CommonMethod {
                override val name: String = "test"
                override val parameters: List<CommonMethodParameter> = emptyList()
                override val returnType: CommonTypeName = object : CommonTypeName {
                    override val typeName: String = "void"
                }

                override fun flowGraph(): ControlFlowGraph<CommonInst> = object : ControlFlowGraph<CommonInst> {
                    override val instructions: List<CommonInst> = emptyList()
                    override val entries: List<CommonInst> = emptyList()
                    override val exits: List<CommonInst> = emptyList()
                    override fun successors(node: CommonInst): Set<CommonInst> = emptySet()
                    override fun predecessors(node: CommonInst): Set<CommonInst> = emptySet()
                }
            }
        }
    }
}

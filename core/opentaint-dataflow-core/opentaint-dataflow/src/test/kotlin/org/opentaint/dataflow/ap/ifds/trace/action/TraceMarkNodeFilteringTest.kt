package org.opentaint.dataflow.ap.ifds.trace.action

import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.EmptyMethodContext
import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.baseonly.BaseOnlyApManager
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.FullStart2FinalTrace
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.Start2FinalTrace
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.SummaryTrace
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEdge
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEntry
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEntryAction
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceKind
import org.opentaint.dataflow.ap.ifds.trace.TraceResolver
import org.opentaint.dataflow.ap.ifds.trace.TraceResolver.CallKind
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.CompactIntSet
import org.opentaint.dataflow.configuration.CommonTaintAssignAction
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSink
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSinkMeta
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSource
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.CommonMethodParameter
import org.opentaint.ir.api.common.CommonTypeName
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.common.cfg.CommonInstLocation
import org.opentaint.ir.api.common.cfg.ControlFlowGraph
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertIs

class TraceMarkNodeFilteringTest {
    @Test
    fun `unchanged marks and covered zero start skip full trace resolution`() {
        val entryPoint = MethodEntryPoint(EmptyMethodContext, statement)
        val startFact = fact(AccessPathBase.Argument(0), markA)
        val predecessorFinalFact = fact(AccessPathBase.This, markA)
        val zeroFinalFact = fact(AccessPathBase.Return, markA)
        val predecessor = node(
            entryPoint,
            TraceEntry.MethodEntry(setOf(startFact), entryPoint),
            TraceEntry.Final(
                setOf(TraceEdge.MethodTraceEdge(startFact, predecessorFinalFact)),
                statement,
            ),
        )
        val zero = node(
            entryPoint,
            TraceEntry.SourceStartEntry(null, emptySet(), statement),
            TraceEntry.Final(setOf(TraceEdge.SourceTraceEdge(zeroFinalFact)), statement),
        )
        var materializations = 0

        val result = collectActionableRules(
            trace = sinkBranchTrace(predecessor, zero),
            sinkStatement = statement,
            sinkRules = setOf(sinkRule),
            materializeNode = {
                materializations++
                listOf(fullTrace(it as TraceResolver.InterProceduralStart2FinalTraceNode))
            },
            materializeSummary = { emptyList() },
        )

        assertIs<ActionableRulesCollectionResult.Collected>(result)
        assertEquals(0, materializations)
    }

    @Test
    fun `different marks retain full trace resolution`() {
        val entryPoint = MethodEntryPoint(EmptyMethodContext, statement)
        val startFact = fact(AccessPathBase.Argument(0), markA)
        val predecessorFinalFact = fact(AccessPathBase.This, markB)
        val zeroFinalFact = fact(AccessPathBase.Return, markA)
        val predecessor = node(
            entryPoint,
            TraceEntry.MethodEntry(setOf(startFact), entryPoint),
            TraceEntry.Final(
                setOf(TraceEdge.MethodTraceEdge(startFact, predecessorFinalFact)),
                statement,
            ),
        )
        val zero = node(
            entryPoint,
            TraceEntry.SourceStartEntry(null, emptySet(), statement),
            TraceEntry.Final(setOf(TraceEdge.SourceTraceEdge(zeroFinalFact)), statement),
        )
        var materializations = 0

        val result = collectActionableRules(
            trace = sinkBranchTrace(predecessor, zero),
            sinkStatement = statement,
            sinkRules = setOf(sinkRule),
            materializeNode = {
                materializations++
                listOf(fullTrace(it as TraceResolver.InterProceduralStart2FinalTraceNode))
            },
            materializeSummary = { emptyList() },
        )

        assertIs<ActionableRulesCollectionResult.Collected>(result)
        assertEquals(2, materializations)
    }

    @Test
    fun `covered zero start on source branch keeps its shallow source action`() {
        val entryPoint = MethodEntryPoint(EmptyMethodContext, statement)
        val finalFact = fact(AccessPathBase.Return, markA)
        val sourceEdge = TraceEdge.SourceTraceEdge(finalFact)
        val source = TraceEntryAction.CallSourceRule(
            sourceEdges = setOf(sourceEdge),
            rule = sourceRule,
            action = setOf(sourceAction),
        )
        val current = node(
            entryPoint,
            TraceEntry.SourceStartEntry(null, setOf(source), statement),
            TraceEntry.Final(setOf(sourceEdge), statement),
        )
        val summary = SummaryTrace(current.trace.method, current.trace.final, current.trace.traceKind)
        val predecessor = node(
            entryPoint,
            TraceEntry.SourceStartEntry(
                TraceEntryAction.CallSourceSummary(
                    summaryEdges = setOf(
                        TraceEntryAction.TraceSummaryEdge.SourceSummary(sourceEdge, sourceEdge)
                    ),
                    summaryTrace = summary,
                ),
                emptySet(),
                statement,
            ),
            TraceEntry.Final(setOf(sourceEdge), statement),
        )
        val materialized = mutableListOf<TraceResolver.InterProceduralTraceNode>()

        val result = collectActionableRules(
            trace = sourceBranchTrace(predecessor, current, summary),
            sinkStatement = statement,
            sinkRules = setOf(sinkRule),
            materializeNode = { traceNode ->
                materialized += traceNode
                listOf(fullTrace(traceNode as TraceResolver.InterProceduralStart2FinalTraceNode))
            },
            materializeSummary = { emptyList() },
        )

        assertIs<ActionableRulesCollectionResult.Collected>(result)
        assertEquals(listOf<TraceResolver.InterProceduralTraceNode>(predecessor), materialized)
        assertEquals(setOf(sourceAction), result.rules.getValue(statement).getValue(sourceRule))
    }

    private fun fact(base: AccessPathBase, mark: TaintMarkAccessor): InitialFactAp =
        apManager.mostAbstractInitialAp(base).prependAccessor(mark)

    private fun node(
        entryPoint: MethodEntryPoint,
        start: TraceEntry.StartTraceEntry,
        final: TraceEntry.Final,
    ): TraceResolver.InterProceduralStart2FinalTraceNode =
        TraceResolver.InterProceduralStart2FinalTraceNode(
            Start2FinalTrace(entryPoint, start, final, TraceKind.SummaryTrace)
        )

    private fun sinkBranchTrace(
        predecessor: TraceResolver.InterProceduralStart2FinalTraceNode,
        current: TraceResolver.InterProceduralStart2FinalTraceNode,
    ): TraceResolver.Trace {
        val call = TraceResolver.InterProceduralCall(
            kind = CallKind.CallToSink,
            statement = predecessor.trace.final.statement,
            summary = SummaryTrace(current.trace.method, current.trace.final, current.trace.traceKind),
            node = current,
        )
        return TraceResolver.Trace(
            entryPointToStart = null,
            sourceToSinkTrace = TraceResolver.SourceToSinkTrace(
                startNodes = setOf(predecessor),
                sinkNodes = setOf(current),
                successors = mapOf(predecessor to setOf(call)),
            ),
        )
    }

    private fun sourceBranchTrace(
        predecessor: TraceResolver.InterProceduralStart2FinalTraceNode,
        current: TraceResolver.InterProceduralStart2FinalTraceNode,
        summary: SummaryTrace,
    ): TraceResolver.Trace {
        val call = TraceResolver.InterProceduralCall(
            kind = CallKind.CallToSource,
            statement = predecessor.trace.startEntry.statement,
            summary = summary,
            node = current,
        )
        return TraceResolver.Trace(
            entryPointToStart = null,
            sourceToSinkTrace = TraceResolver.SourceToSinkTrace(
                startNodes = setOf(predecessor),
                sinkNodes = setOf(predecessor),
                successors = mapOf(predecessor to setOf(call)),
            ),
        )
    }

    private fun fullTrace(
        node: TraceResolver.InterProceduralStart2FinalTraceNode,
    ): FullStart2FinalTrace {
        val successors = Int2ObjectOpenHashMap<CompactIntSet>()
        successors[0] = CompactIntSet().also { it.add(1) }
        return FullStart2FinalTrace(
            method = node.trace.method,
            entries = arrayOf(node.trace.startEntry, node.trace.final),
            actionVariants = Int2ObjectOpenHashMap(),
            startEntryId = 0,
            finalId = 1,
            successors = successors,
            traceKind = node.trace.traceKind,
        )
    }

    private val apManager = BaseOnlyApManager(
        AnyAccessorUnrollStrategy.AnyAccessorDisabled,
        Cancellation(),
        fieldSensitive = true,
    )
    private val markA = TaintMarkAccessor("a")
    private val markB = TaintMarkAccessor("b")
    private val sinkRule = object : CommonTaintConfigurationSink {
        override val id: String = "sink"
        override val meta: CommonTaintConfigurationSinkMeta = object : CommonTaintConfigurationSinkMeta {
            override val message: String = "sink"
            override val severity: CommonTaintConfigurationSinkMeta.Severity =
                CommonTaintConfigurationSinkMeta.Severity.Error
        }
    }
    private val sourceRule = object : CommonTaintConfigurationSource {}
    private val sourceAction = object : CommonTaintAssignAction {}
    private val method: CommonMethod = object : CommonMethod {
        override val name: String = "test"
        override val parameters: List<CommonMethodParameter> = emptyList()
        override val returnType: CommonTypeName = object : CommonTypeName {
            override val typeName: String = "void"
        }

        override fun flowGraph(): ControlFlowGraph<CommonInst> = object : ControlFlowGraph<CommonInst> {
            override val instructions: List<CommonInst> = listOf(statement)
            override val entries: List<CommonInst> = listOf(statement)
            override val exits: List<CommonInst> = listOf(statement)
            override fun successors(node: CommonInst): Set<CommonInst> = emptySet()
            override fun predecessors(node: CommonInst): Set<CommonInst> = emptySet()
        }
    }
    private val statement: CommonInst = object : CommonInst {
        override val location: CommonInstLocation = object : CommonInstLocation {
            override val index: Int = 0
            override val method: CommonMethod
                get() = this@TraceMarkNodeFilteringTest.method
        }
    }
}

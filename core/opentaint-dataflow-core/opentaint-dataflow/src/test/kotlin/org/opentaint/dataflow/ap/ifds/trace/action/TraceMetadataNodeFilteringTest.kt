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
import org.opentaint.dataflow.ap.ifds.trace.TraceMetadata
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

class TraceMetadataNodeFilteringTest {
    @Test
    fun `metadata keeps a rule-free node valid without materializing its full trace`() {
        val entryPoint = MethodEntryPoint(EmptyMethodContext, statement)
        val start = TraceEntry.MethodEntry(emptySet(), entryPoint)
        val final = TraceEntry.Final(emptySet(), statement)
        val node = TraceResolver.InterProceduralStart2FinalTraceNode(
            Start2FinalTrace(entryPoint, start, final, TraceKind.SummaryTrace)
        )
        val sourceToSink = TraceResolver.SourceToSinkTrace(
            startNodes = setOf(node),
            sinkNodes = setOf(node),
            successors = emptyMap(),
            nodeMetadata = mapOf(node to TraceMetadata(requiresFullTraceResolution = false)),
        )
        var materializations = 0

        val result = collectActionableRules(
            trace = TraceResolver.Trace(entryPointToStart = null, sourceToSinkTrace = sourceToSink),
            sinkStatement = statement,
            sinkRules = setOf(sinkRule),
            shouldMaterializeNode = sourceToSink::requiresFullTraceResolution,
            materializeNode = {
                materializations++
                emptyList()
            },
            materializeSummary = { emptyList() },
        )

        val collected = assertIs<ActionableRulesCollectionResult.Collected>(result)
        assertEquals(0, materializations)
        assertEquals(setOf(sinkRule), collected.rules.getValue(statement).keys)
    }

    @Test
    fun `equal start and final taint marks skip rule resolution even when facts differ`() {
        val entryPoint = MethodEntryPoint(EmptyMethodContext, statement)
        val startFact = fact(AccessPathBase.Argument(0), markA)
        val finalFact = fact(AccessPathBase.Return, markA)
        val start = TraceEntry.MethodEntry(setOf(startFact), entryPoint)
        val final = TraceEntry.Final(
            setOf(TraceEdge.MethodTraceEdge(startFact, finalFact)),
            statement,
        )
        val node = start2FinalNode(entryPoint, start, final)
        var materializations = 0

        val result = collectActionableRules(
            trace = singleNodeTrace(node),
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
    fun `multiple equal start and final taint marks skip rule resolution`() {
        val entryPoint = MethodEntryPoint(EmptyMethodContext, statement)
        val startA = fact(AccessPathBase.Argument(0), markA)
        val startB = fact(AccessPathBase.Argument(1), markB)
        val finalA = fact(AccessPathBase.Return, markA)
        val finalB = fact(AccessPathBase.This, markB)
        val node = start2FinalNode(
            entryPoint,
            TraceEntry.MethodEntry(setOf(startA, startB), entryPoint),
            TraceEntry.Final(
                setOf(
                    TraceEdge.MethodTraceEdge(startA, finalA),
                    TraceEdge.MethodTraceEdge(startB, finalB),
                ),
                statement,
            ),
        )
        var materializations = 0

        val result = collectActionableRules(
            trace = singleNodeTrace(node),
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
    fun `over-approximate starts with the same full query are resolved once`() {
        val entryPoint = MethodEntryPoint(EmptyMethodContext, statement)
        val finalFact = fact(AccessPathBase.Return, markA)
        val final = TraceEntry.Final(setOf(TraceEdge.SourceTraceEdge(finalFact)), statement)
        val predecessor = start2FinalNode(
            entryPoint,
            TraceEntry.MethodEntry(setOf(fact(AccessPathBase.Argument(0), markB)), entryPoint),
            final,
            isStartOverApproximation = true,
        )
        val current = start2FinalNode(
            entryPoint,
            TraceEntry.MethodEntry(setOf(fact(AccessPathBase.Argument(1), markB)), entryPoint),
            final,
            isStartOverApproximation = true,
        )
        var materializations = 0

        val result = collectActionableRules(
            trace = twoNodeTrace(predecessor, current),
            sinkStatement = statement,
            sinkRules = setOf(sinkRule),
            materializeNode = {
                materializations++
                listOf(fullTrace(it as TraceResolver.InterProceduralStart2FinalTraceNode))
            },
            materializeSummary = { emptyList() },
        )

        val collected = assertIs<ActionableRulesCollectionResult.Collected>(result)
        assertEquals(1, materializations)
        assertEquals(setOf(sinkRule), collected.rules.getValue(statement).keys)
    }

    @Test
    fun `zero start is skipped when its predecessor has the same final taint marks`() {
        val entryPoint = MethodEntryPoint(EmptyMethodContext, statement)
        val predecessorStartFact = fact(AccessPathBase.Argument(0), markB)
        val predecessorFinalFact = fact(AccessPathBase.This, markA)
        val currentFinalFact = fact(AccessPathBase.Return, markA)
        val predecessor = start2FinalNode(
            entryPoint,
            TraceEntry.MethodEntry(setOf(predecessorStartFact), entryPoint),
            TraceEntry.Final(
                setOf(TraceEdge.MethodTraceEdge(predecessorStartFact, predecessorFinalFact)),
                statement,
            ),
        )
        val current = start2FinalNode(
            entryPoint,
            TraceEntry.SourceStartEntry(null, emptySet(), statement),
            TraceEntry.Final(setOf(TraceEdge.SourceTraceEdge(currentFinalFact)), statement),
        )
        val materialized = mutableListOf<TraceResolver.InterProceduralTraceNode>()

        val result = collectActionableRules(
            trace = twoNodeTrace(predecessor, current),
            sinkStatement = statement,
            sinkRules = setOf(sinkRule),
            materializeNode = { node ->
                materialized += node
                listOf(fullTrace(node as TraceResolver.InterProceduralStart2FinalTraceNode))
            },
            materializeSummary = { emptyList() },
        )

        assertIs<ActionableRulesCollectionResult.Collected>(result)
        assertEquals(listOf<TraceResolver.InterProceduralTraceNode>(predecessor), materialized)
    }

    @Test
    fun `zero start is resolved when its predecessor has different final taint marks`() {
        val entryPoint = MethodEntryPoint(EmptyMethodContext, statement)
        val predecessorStartFact = fact(AccessPathBase.Argument(0), markA)
        val predecessorFinalFact = fact(AccessPathBase.This, markB)
        val currentFinalFact = fact(AccessPathBase.Return, markA)
        val predecessor = start2FinalNode(
            entryPoint,
            TraceEntry.MethodEntry(setOf(predecessorStartFact), entryPoint),
            TraceEntry.Final(
                setOf(TraceEdge.MethodTraceEdge(predecessorStartFact, predecessorFinalFact)),
                statement,
            ),
        )
        val current = start2FinalNode(
            entryPoint,
            TraceEntry.SourceStartEntry(null, emptySet(), statement),
            TraceEntry.Final(setOf(TraceEdge.SourceTraceEdge(currentFinalFact)), statement),
        )
        val materialized = mutableListOf<TraceResolver.InterProceduralTraceNode>()

        val result = collectActionableRules(
            trace = twoNodeTrace(predecessor, current),
            sinkStatement = statement,
            sinkRules = setOf(sinkRule),
            materializeNode = { node ->
                materialized += node
                listOf(fullTrace(node as TraceResolver.InterProceduralStart2FinalTraceNode))
            },
            materializeSummary = { emptyList() },
        )

        assertIs<ActionableRulesCollectionResult.Collected>(result)
        assertEquals(
            listOf<TraceResolver.InterProceduralTraceNode>(predecessor, current),
            materialized,
        )
    }

    @Test
    fun `zero start on the source branch keeps its shallow source rule without full resolution`() {
        val entryPoint = MethodEntryPoint(EmptyMethodContext, statement)
        val finalFact = fact(AccessPathBase.Return, markA)
        val sourceEdge = TraceEdge.SourceTraceEdge(finalFact)
        val source = TraceEntryAction.CallSourceRule(
            sourceEdges = setOf(sourceEdge),
            rule = sourceRule,
            action = setOf(sourceAction),
        )
        val current = start2FinalNode(
            entryPoint,
            TraceEntry.SourceStartEntry(null, setOf(source), statement),
            TraceEntry.Final(setOf(sourceEdge), statement),
        )
        val summary = SummaryTrace(current.trace.method, current.trace.final, current.trace.traceKind)
        val callSource = TraceEntryAction.CallSourceSummary(
            summaryEdges = setOf(TraceEntryAction.TraceSummaryEdge.SourceSummary(sourceEdge, sourceEdge)),
            summaryTrace = summary,
        )
        val predecessor = start2FinalNode(
            entryPoint,
            TraceEntry.SourceStartEntry(callSource, emptySet(), statement),
            TraceEntry.Final(setOf(sourceEdge), statement),
        )
        val materialized = mutableListOf<TraceResolver.InterProceduralTraceNode>()

        val result = collectActionableRules(
            trace = sourceBranchTrace(predecessor, current, summary),
            sinkStatement = statement,
            sinkRules = setOf(sinkRule),
            materializeNode = { node ->
                materialized += node
                listOf(fullTrace(node as TraceResolver.InterProceduralStart2FinalTraceNode))
            },
            materializeSummary = { emptyList() },
        )

        assertIs<ActionableRulesCollectionResult.Collected>(result)
        assertEquals(
            listOf<TraceResolver.InterProceduralTraceNode>(predecessor),
            materialized,
        )
        assertEquals(setOf(sourceAction), result.rules.getValue(statement).getValue(sourceRule))
    }

    private fun fact(base: AccessPathBase, mark: TaintMarkAccessor): InitialFactAp =
        apManager.mostAbstractInitialAp(base).prependAccessor(mark)

    private fun start2FinalNode(
        entryPoint: MethodEntryPoint,
        start: TraceEntry.StartTraceEntry,
        final: TraceEntry.Final,
        isStartOverApproximation: Boolean = false,
    ): TraceResolver.InterProceduralStart2FinalTraceNode =
        TraceResolver.InterProceduralStart2FinalTraceNode(
            Start2FinalTrace(
                entryPoint,
                start,
                final,
                TraceKind.SummaryTrace,
                isStartOverApproximation = isStartOverApproximation,
            )
        )

    private fun singleNodeTrace(
        node: TraceResolver.InterProceduralStart2FinalTraceNode,
    ): TraceResolver.Trace = TraceResolver.Trace(
        entryPointToStart = null,
        sourceToSinkTrace = TraceResolver.SourceToSinkTrace(
            startNodes = setOf(node),
            sinkNodes = setOf(node),
            successors = emptyMap(),
        ),
    )

    private fun twoNodeTrace(
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
            override val method: CommonMethod
                get() = this@TraceMetadataNodeFilteringTest.method
        }
    }
}

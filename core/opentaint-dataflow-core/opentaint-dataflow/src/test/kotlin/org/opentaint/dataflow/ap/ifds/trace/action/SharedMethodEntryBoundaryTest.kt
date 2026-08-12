package org.opentaint.dataflow.ap.ifds.trace.action

import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.EmptyMethodContext
import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.baseonly.BaseOnlyApManager
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.FullStart2FinalTrace
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.Start2FinalTrace
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.SummaryTrace
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEdge
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEntry
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEntryAction
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceKind
import org.opentaint.dataflow.ap.ifds.trace.TraceResolver
import org.opentaint.dataflow.ap.ifds.trace.TraceResolver.CallKind
import org.opentaint.dataflow.ap.ifds.trace.path.createSource2SinkGraph
import org.opentaint.dataflow.ap.ifds.trace.path.allMethodTraces
import org.opentaint.dataflow.ap.ifds.trace.path.methodGraph
import org.opentaint.dataflow.ap.ifds.trace.path.nodesForPathResolution
import org.opentaint.dataflow.ap.ifds.trace.path.processMethodTrace
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.CompactIntSet
import org.opentaint.dataflow.configuration.CommonTaintAction
import org.opentaint.dataflow.configuration.CommonTaintAssignAction
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
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
import kotlin.test.assertFalse
import kotlin.test.assertIs

class SharedMethodEntryBoundaryTest {
    @Test
    fun `shared boundary has linear edges and preserves rules on both sides`() {
        val upstream = (0 until upstreamCount).map(::sourceNode)
        val downstream = (0 until downstreamCount).map(::sinkNode)
        val boundary = methodEntryBoundary()
        val sourceToSink = sharedBoundaryTrace(upstream, boundary, downstream)

        val graph = createSource2SinkGraph(sourceToSink)
        val boundaryId = graph.nodeIndices.getInt(boundary)
        val upstreamIds = upstream.mapTo(linkedSetOf()) { graph.nodeIndices.getInt(it) }
        val downstreamIds = downstream.mapTo(linkedSetOf()) { graph.nodeIndices.getInt(it) }

        assertEquals(upstreamCount + 1 + downstreamCount, graph.allNodes.size)
        assertEquals(upstreamCount + downstreamCount, graph.root2SinkFwd.values.sumOf { it.size })
        upstreamIds.forEach { upstreamId ->
            assertEquals(setOf(boundaryId), graph.root2SinkFwd.get(upstreamId).toSet())
            assertFalse(
                downstreamIds.any { it in graph.root2SinkFwd.get(upstreamId) },
                "upstream nodes must not be copied once per downstream continuation",
            )
        }
        assertEquals(downstreamIds, graph.root2SinkFwd.get(boundaryId).toSet())

        val materialized = linkedSetOf<TraceResolver.InterProceduralTraceNode>()
        val downstreamRuleByNode = downstream.zip(downstreamRules).toMap()
        val sinkStatement = downstream.first().trace.final.statement
        val result = collectActionableRules(
            trace = TraceResolver.Trace(entryPointToStart = null, sourceToSinkTrace = sourceToSink),
            sinkStatement = sinkStatement,
            sinkRules = setOf(sinkRule),
            materializeNode = { node ->
                materialized += node
                val start2Final = node as TraceResolver.InterProceduralStart2FinalTraceNode
                listOf(fullTrace(start2Final, downstreamRuleByNode[start2Final]))
            },
            materializeSummary = { emptyList() },
        )

        val collected = assertIs<ActionableRulesCollectionResult.Collected>(result)
        val expectedMaterialized: Set<TraceResolver.InterProceduralTraceNode> =
            (upstream + downstream).toSet()
        assertEquals(expectedMaterialized, materialized)
        assertFalse(boundary in materialized)
        sourceRules.forEachIndexed { index, rule ->
            assertEquals(
                setOf<CommonTaintAction>(sourceActions[index]),
                collected.rules.getValue(upstream[index].trace.startEntry.statement).getValue(rule),
            )
        }
        downstreamRules.forEachIndexed { index, rule ->
            assertEquals(
                setOf<CommonTaintAction>(downstreamActions[index]),
                collected.rules.getValue(downstream[index].trace.final.statement).getValue(rule),
            )
        }
        assertEquals(emptySet(), collected.rules.getValue(sinkStatement).getValue(sinkRule))
    }

    @Test
    fun `shared boundary is transparent during path resolution`() {
        val root = sourceNode(0)
        val boundary = methodEntryBoundary()
        val sink = sinkNode(0)
        val graph = createSource2SinkGraph(sharedBoundaryTrace(listOf(root), boundary, listOf(sink)))

        val rootId = graph.nodeIndices.getInt(root)
        val boundaryId = graph.nodeIndices.getInt(boundary)
        val sinkId = graph.nodeIndices.getInt(sink)
        val nodes = graph.nodesForPathResolution(
            sink2Root = intArrayOf(sinkId, boundaryId, rootId),
            root2Source = intArrayOf(rootId),
        )

        assertEquals(listOf(root), nodes.root2Source)
        assertEquals(listOf(sink), nodes.root2SinkNoRoot)
    }

    @Test
    fun `same method boundary is transparent during node path reconstruction`() {
        val root = sourceNode(0)
        val boundary = methodEntryBoundary()
        val sink = sinkNodeInMethod(0, boundary.entry.entryPoint)
        val graph = createSource2SinkGraph(sharedBoundaryTrace(listOf(root), boundary, listOf(sink)))
        val methodGraph = graph.methodGraph()

        val nodeTraces = methodGraph.allMethodTraces(limit = 1) { methodTrace ->
            graph.processMethodTrace(methodGraph, methodTrace) { it }
        }

        val nodeTrace = nodeTraces.single()
        assertEquals(
            listOf(sink, root),
            nodeTrace.sink2Root.map { graph.allNodes[it] },
        )
        assertEquals(
            listOf(root),
            nodeTrace.root2Source.map { graph.allNodes[it] },
        )
    }

    @Test
    fun `shared boundary preserves distinct action bearing summaries and transparent paths`() {
        val root = sourceNode(0)
        val boundary = methodEntryBoundary()
        val sink = sinkNode(0)
        val summaries = (0 until downstreamCount).map(::actionBearingSummary)
        val summaryNodes = summaries.map {
            TraceResolver.InterProceduralSummaryTraceNode(it.action.summaryTrace)
        }
        val summaryByTrace = summaries.associateBy { it.action.summaryTrace }
        val sourceToSink = factoredSummaryTrace(root, boundary, summaryNodes, sink)
        val materialized = linkedSetOf<TraceResolver.InterProceduralTraceNode>()

        val result = collectActionableRules(
            trace = TraceResolver.Trace(entryPointToStart = null, sourceToSinkTrace = sourceToSink),
            sinkStatement = sink.trace.final.statement,
            sinkRules = setOf(sinkRule),
            materializeNode = { node ->
                materialized += node
                when (node) {
                    is TraceResolver.InterProceduralStart2FinalTraceNode ->
                        listOf(fullTrace(node, downstreamRule = null))

                    is TraceResolver.InterProceduralSummaryTraceNode ->
                        listOf(summaryByTrace.getValue(node.trace).fullTrace)

                    is TraceResolver.InterProceduralMethodEntryNode ->
                        error("synthetic boundary must not be materialized")
                }
            },
            materializeSummary = { error("no nested summary is expected") },
        )

        val collected = assertIs<ActionableRulesCollectionResult.Collected>(result)
        assertEquals(setOf(root, sink) + summaryNodes, materialized)
        assertFalse(boundary in materialized)
        summaries.forEachIndexed { index, summary ->
            val actionStatement = summary.fullTrace.entries[1].statement
            assertEquals(
                setOf<CommonTaintAction>(downstreamActions[index]),
                collected.rules.getValue(actionStatement).getValue(downstreamRules[index]),
            )
        }

        val graph = createSource2SinkGraph(sourceToSink)
        val rootId = graph.nodeIndices.getInt(root)
        val boundaryId = graph.nodeIndices.getInt(boundary)
        val sinkId = graph.nodeIndices.getInt(sink)
        val summaryIds = summaryNodes.mapTo(linkedSetOf()) { graph.nodeIndices.getInt(it) }
        assertEquals(setOf(boundaryId), graph.root2SinkFwd.get(rootId).toSet())
        assertEquals(summaryIds, graph.root2SinkFwd.get(boundaryId).toSet())
        summaryNodes.forEach { summaryNode ->
            val summaryId = graph.nodeIndices.getInt(summaryNode)
            assertEquals(setOf(sinkId), graph.root2SinkFwd.get(summaryId).toSet())
            val nodes = graph.nodesForPathResolution(
                sink2Root = intArrayOf(sinkId, summaryId, boundaryId, rootId),
                root2Source = intArrayOf(rootId),
            )
            assertEquals(listOf(root), nodes.root2Source)
            assertEquals(listOf(summaryNode, sink), nodes.root2SinkNoRoot)
        }
    }

    @Test
    fun `alternative full traces preserve every distinct action rule`() {
        val node = sinkNode(0)
        val trace = TraceResolver.Trace(
            entryPointToStart = null,
            sourceToSinkTrace = TraceResolver.SourceToSinkTrace(
                startNodes = setOf(node),
                sinkNodes = setOf(node),
                successors = emptyMap(),
            ),
        )

        val result = collectActionableRules(
            trace = trace,
            sinkStatement = node.trace.final.statement,
            sinkRules = setOf(sinkRule),
            materializeNode = {
                listOf(
                    fullTrace(node, downstreamRules[0]),
                    fullTrace(node, downstreamRules[1]),
                )
            },
            materializeSummary = { error("no nested summary is expected") },
        )

        val collected = assertIs<ActionableRulesCollectionResult.Collected>(result)
        val rulesAtAction = collected.rules.getValue(node.trace.final.statement)
        assertEquals(setOf<CommonTaintAction>(downstreamActions[0]), rulesAtAction.getValue(downstreamRules[0]))
        assertEquals(setOf<CommonTaintAction>(downstreamActions[1]), rulesAtAction.getValue(downstreamRules[1]))
        assertEquals(emptySet(), rulesAtAction.getValue(sinkRule))
    }

    private fun factoredSummaryTrace(
        root: TraceResolver.InterProceduralStart2FinalTraceNode,
        boundary: TraceResolver.InterProceduralMethodEntryNode,
        summaries: List<TraceResolver.InterProceduralSummaryTraceNode>,
        sink: TraceResolver.InterProceduralStart2FinalTraceNode,
    ): TraceResolver.SourceToSinkTrace {
        val successors = linkedMapOf<
            TraceResolver.InterProceduralTraceNode,
            MutableSet<TraceResolver.InterProceduralCall>
        >()
        successors.getOrPut(root, ::linkedSetOf) += call(
            root.trace.final.statement,
            boundarySummary(boundary),
            boundary,
        )
        summaries.forEach { summary ->
            successors.getOrPut(boundary, ::linkedSetOf) += call(
                summary.trace.final.statement,
                summary.trace,
                summary,
            )
            successors.getOrPut(summary, ::linkedSetOf) += call(
                summary.trace.final.statement,
                SummaryTrace(sink.trace.method, sink.trace.final, sink.trace.traceKind),
                sink,
            )
        }
        return TraceResolver.SourceToSinkTrace(
            startNodes = setOf(root),
            sinkNodes = setOf(sink),
            successors = successors,
        )
    }

    private fun sharedBoundaryTrace(
        upstream: List<TraceResolver.InterProceduralStart2FinalTraceNode>,
        boundary: TraceResolver.InterProceduralMethodEntryNode,
        downstream: List<TraceResolver.InterProceduralStart2FinalTraceNode>,
    ): TraceResolver.SourceToSinkTrace {
        val successors = linkedMapOf<
            TraceResolver.InterProceduralTraceNode,
            MutableSet<TraceResolver.InterProceduralCall>
        >()
        upstream.forEach { node ->
            successors.getOrPut(node, ::linkedSetOf) += call(
                statement = node.trace.final.statement,
                summary = boundarySummary(boundary),
                node = boundary,
            )
        }
        downstream.forEach { node ->
            successors.getOrPut(boundary, ::linkedSetOf) += call(
                statement = node.trace.final.statement,
                summary = SummaryTrace(node.trace.method, node.trace.final, node.trace.traceKind),
                node = node,
            )
        }
        return TraceResolver.SourceToSinkTrace(
            startNodes = upstream.toSet(),
            sinkNodes = downstream.toSet(),
            successors = successors,
        )
    }

    private fun call(
        statement: CommonInst,
        summary: SummaryTrace,
        node: TraceResolver.InterProceduralTraceNode,
    ) = TraceResolver.InterProceduralCall(CallKind.CallToSink, statement, summary, node)

    private fun boundarySummary(boundary: TraceResolver.InterProceduralMethodEntryNode): SummaryTrace {
        val fact = boundary.entry.facts.single()
        return SummaryTrace(
            boundary.entry.entryPoint,
            TraceEntry.Final(setOf(TraceEdge.MethodTraceEdge(fact, fact)), boundary.entry.statement),
            TraceKind.SummaryTrace,
        )
    }

    private fun methodEntryBoundary(): TraceResolver.InterProceduralMethodEntryNode {
        val entryPoint = entryPoint("boundary")
        val fact = fact(AccessPathBase.This, boundaryMark)
        return TraceResolver.InterProceduralMethodEntryNode(
            TraceEntry.MethodEntry(setOf(fact), entryPoint)
        )
    }

    private fun sourceNode(index: Int): TraceResolver.InterProceduralStart2FinalTraceNode {
        val entryPoint = entryPoint("source-$index")
        val fact = fact(AccessPathBase.Return, TaintMarkAccessor("source-$index"))
        val edge = TraceEdge.SourceTraceEdge(fact)
        val source = TraceEntryAction.CallSourceRule(
            sourceEdges = setOf(edge),
            rule = sourceRules[index],
            action = setOf(sourceActions[index]),
        )
        return node(
            entryPoint,
            TraceEntry.SourceStartEntry(null, setOf(source), entryPoint.statement),
            TraceEntry.Final(setOf(edge), entryPoint.statement),
        )
    }

    private fun sinkNode(index: Int): TraceResolver.InterProceduralStart2FinalTraceNode {
        val entryPoint = entryPoint("sink-$index")
        return sinkNodeInMethod(index, entryPoint)
    }

    private fun sinkNodeInMethod(
        index: Int,
        entryPoint: MethodEntryPoint,
    ): TraceResolver.InterProceduralStart2FinalTraceNode {
        val initial = fact(AccessPathBase.Argument(index), boundaryMark)
        val final = fact(AccessPathBase.Return, TaintMarkAccessor("sink-$index"))
        return node(
            entryPoint,
            TraceEntry.MethodEntry(setOf(initial), entryPoint),
            TraceEntry.Final(
                setOf(TraceEdge.MethodTraceEdge(initial, final)),
                entryPoint.statement,
            ),
        )
    }

    private fun node(
        entryPoint: MethodEntryPoint,
        start: TraceEntry.StartTraceEntry,
        final: TraceEntry.Final,
    ) = TraceResolver.InterProceduralStart2FinalTraceNode(
        Start2FinalTrace(entryPoint, start, final, TraceKind.SummaryTrace)
    )

    private fun fullTrace(
        node: TraceResolver.InterProceduralStart2FinalTraceNode,
        downstreamRule: TestActionRule?,
    ): FullStart2FinalTrace {
        val successors = Int2ObjectOpenHashMap<CompactIntSet>()
        val entries = if (downstreamRule == null) {
            successors[0] = CompactIntSet().also { it.add(1) }
            arrayOf(node.trace.startEntry, node.trace.final)
        } else {
            successors[0] = CompactIntSet().also { it.add(1) }
            successors[1] = CompactIntSet().also { it.add(2) }
            arrayOf(
                node.trace.startEntry,
                TraceEntry.Action(node.trace.final.edges, node.trace.final.statement),
                node.trace.final,
            )
        }
        val variants = Int2ObjectOpenHashMap<List<MethodTraceResolver.ActionVariant>>()
        if (downstreamRule != null) {
            val index = downstreamRules.indexOf(downstreamRule)
            val callRule = TraceEntryAction.CallRule(
                edges = node.trace.final.edges,
                edgesAfter = node.trace.final.edges,
                rule = downstreamRule,
                action = setOf(downstreamActions[index]),
            )
            variants[1] = listOf(
                MethodTraceResolver.ActionVariant(
                    primaryAction = null,
                    otherActions = setOf(callRule),
                    unchanged = emptySet(),
                )
            )
        }
        return FullStart2FinalTrace(
            method = node.trace.method,
            entries = entries,
            actionVariants = variants,
            startEntryId = 0,
            finalId = entries.lastIndex,
            successors = successors,
            traceKind = node.trace.traceKind,
        )
    }

    private fun actionBearingSummary(index: Int): ActionBearingSummary {
        val entryPoint = entryPoint("nested-summary-$index")
        val initial = fact(AccessPathBase.Argument(0), boundaryMark)
        val before = fact(AccessPathBase.Return, boundaryMark)
        val after = fact(AccessPathBase.Return, TaintMarkAccessor("nested-$index"))
        val beforeEdge = TraceEdge.MethodTraceEdge(initial, before)
        val afterEdge = TraceEdge.MethodTraceEdge(initial, after)
        val summary = SummaryTrace(
            entryPoint,
            TraceEntry.Final(setOf(afterEdge), entryPoint.statement),
            TraceKind.SummaryTrace,
        )
        val callSummary = TraceEntryAction.CallSummary(
            summaryEdges = setOf(
                TraceEntryAction.TraceSummaryEdge.MethodSummary(
                    edge = beforeEdge,
                    edgeAfter = afterEdge,
                    delta = null,
                )
            ),
            summaryTrace = summary,
        )

        val actionStatement = TestStatement("nested-action-$index", entryPoint.method)
        val actionEntry = TraceEntry.Action(setOf(afterEdge), actionStatement)
        val callRule = TraceEntryAction.CallRule(
            edges = setOf(afterEdge),
            edgesAfter = setOf(afterEdge),
            rule = downstreamRules[index],
            action = setOf(downstreamActions[index]),
        )
        val variants = Int2ObjectOpenHashMap<List<MethodTraceResolver.ActionVariant>>()
        variants[1] = listOf(
            MethodTraceResolver.ActionVariant(
                primaryAction = null,
                otherActions = setOf(callRule),
                unchanged = emptySet(),
            )
        )
        val successors = Int2ObjectOpenHashMap<CompactIntSet>()
        successors[0] = CompactIntSet().also { it.add(1) }
        successors[1] = CompactIntSet().also { it.add(2) }
        val fullTrace = FullStart2FinalTrace(
            method = entryPoint,
            entries = arrayOf(
                TraceEntry.MethodEntry(setOf(initial), entryPoint),
                actionEntry,
                summary.final,
            ),
            actionVariants = variants,
            startEntryId = 0,
            finalId = 2,
            successors = successors,
            traceKind = TraceKind.SummaryTrace,
        )
        return ActionBearingSummary(callSummary, fullTrace)
    }

    private fun fact(base: AccessPathBase, mark: TaintMarkAccessor): InitialFactAp =
        apManager.mostAbstractInitialAp(base).prependAccessor(mark)

    private fun entryPoint(name: String): MethodEntryPoint {
        val method = TestMethod(name)
        return MethodEntryPoint(EmptyMethodContext, TestStatement(name, method))
    }

    private data class TestMethod(override val name: String) : CommonMethod {
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

    private data class TestStatement(
        val label: String,
        val method: CommonMethod,
    ) : CommonInst {
        override val location: CommonInstLocation = object : CommonInstLocation {
            override val method: CommonMethod
                get() = this@TestStatement.method
        }
    }

    private data class TestSourceRule(val name: String) : CommonTaintConfigurationSource
    private data class TestSourceAction(val name: String) : CommonTaintAssignAction
    private data class TestActionRule(val name: String) : CommonTaintConfigurationSource

    private data class ActionBearingSummary(
        val action: TraceEntryAction.CallSummary,
        val fullTrace: FullStart2FinalTrace,
    )

    private val apManager = BaseOnlyApManager(
        AnyAccessorUnrollStrategy.AnyAccessorDisabled,
        Cancellation(),
        fieldSensitive = true,
    )
    private val boundaryMark = TaintMarkAccessor("boundary")
    private val sourceRules = List(upstreamCount) { TestSourceRule("source-rule-$it") }
    private val sourceActions = List(upstreamCount) { TestSourceAction("source-action-$it") }
    private val downstreamRules = List(downstreamCount) { TestActionRule("downstream-rule-$it") }
    private val downstreamActions = List(downstreamCount) { TestSourceAction("downstream-action-$it") }
    private val sinkRule: CommonTaintConfigurationItem = object : CommonTaintConfigurationSink {
        override val id: String = "sink"
        override val meta: CommonTaintConfigurationSinkMeta = object : CommonTaintConfigurationSinkMeta {
            override val message: String = "sink"
            override val severity = CommonTaintConfigurationSinkMeta.Severity.Error
        }
    }

    private companion object {
        const val upstreamCount = 3
        const val downstreamCount = 2
    }
}

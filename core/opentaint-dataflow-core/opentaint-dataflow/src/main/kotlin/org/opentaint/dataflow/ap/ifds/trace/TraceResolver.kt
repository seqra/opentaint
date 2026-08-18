package org.opentaint.dataflow.ap.ifds.trace

import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.TaintAnalysisUnitRunnerManager
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.baseonly.BaseOnlyApManager
import org.opentaint.dataflow.ap.ifds.access.baseonly.BaseOnlyInitialFactAp
import org.opentaint.dataflow.ap.ifds.access.baseonly.NO_ACCESSOR
import org.opentaint.dataflow.ap.ifds.access.baseonly.fieldIdx
import org.opentaint.dataflow.ap.ifds.access.baseonly.rawSuffixSlot
import org.opentaint.dataflow.ap.ifds.access.baseonly.staticIdx
import org.opentaint.dataflow.ap.ifds.access.baseonly.suffixIdx
import org.opentaint.dataflow.ap.ifds.access.baseonly.valueAccessorState
import org.opentaint.dataflow.ap.ifds.taint.TaintSinkTracker
import org.opentaint.dataflow.ap.ifds.taint.TaintSinkTracker.TaintVulnerability
import org.opentaint.dataflow.ap.ifds.taint.TaintSinkTracker.TaintVulnerabilityRuleNode
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEntry.MethodEntry
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEntry.SourceStartEntry
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEntryAction
import org.opentaint.dataflow.ap.ifds.trace.TraceResolver.TraceResolutionResult.NoTrace
import org.opentaint.dataflow.ap.ifds.trace.TraceResolver.TraceResolutionResult.Resolved
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst
import java.util.PriorityQueue
import java.util.concurrent.ConcurrentHashMap
import kotlin.time.Duration.Companion.milliseconds
import kotlin.time.TimeMark
import kotlin.time.TimeSource

internal fun InitialFactAp.baseOnlyTraceFieldGeneralizationCovers(other: InitialFactAp): Boolean {
    if (this == other) return true
    val general = this as? BaseOnlyInitialFactAp ?: return false
    val concrete = other as? BaseOnlyInitialFactAp ?: return false
    if (general.base != concrete.base || general.exclusions != concrete.exclusions) return false
    return general.access.staticIdx == concrete.access.staticIdx &&
        general.access.fieldIdx == NO_ACCESSOR &&
        concrete.access.fieldIdx != NO_ACCESSOR &&
        general.access.suffixIdx != NO_ACCESSOR &&
        general.access.suffixIdx == concrete.access.suffixIdx &&
        general.access.valueAccessorState == concrete.access.valueAccessorState
}

class TraceResolver(
    private val entryPointMethods: Set<CommonMethod>,
    private val manager: TaintAnalysisUnitRunnerManager,
    private val params: Params,
    private val cancellation: Cancellation
) {
    data class StateDebugInfo(
        val phase: String,
        val request: String,
        val graph: String,
    )

    private val start2FinalTraceCache =
        ConcurrentHashMap<MethodTraceResolver.SummaryTrace, ResolvedStartTraces>()
    private val generalizedStart2FinalTraceCache =
        ConcurrentHashMap<FieldGeneralizationCacheKey, MutableList<CachedStartTrace>>()
    private val methodEntryCallerTraceCache =
        ConcurrentHashMap<MethodEntry, List<Pair<CommonInst, MethodTraceResolver.SummaryTrace>>>()

    private data class StartTraceCacheKey(
        val method: MethodEntryPoint,
        val statement: CommonInst,
        val traceKind: MethodTraceResolver.TraceKind,
    )

    private data class CachedStartTrace(
        val trace: MethodTraceResolver.SummaryTrace,
        val result: ResolvedStartTraces,
    )

    private data class FieldGeneralizationCacheKey(
        val start: StartTraceCacheKey,
        val edges: Map<FieldGeneralizationEdgeKey, Int>,
    )

    private sealed interface FieldGeneralizationEdgeKey {
        data class Source(
            val fact: FieldGeneralizationFactKey,
        ) : FieldGeneralizationEdgeKey

        data class Method(
            val initial: FieldGeneralizationFactKey,
            val final: FieldGeneralizationFactKey,
        ) : FieldGeneralizationEdgeKey

        data class Exact(
            val edge: MethodTraceResolver.TraceEdge,
        ) : FieldGeneralizationEdgeKey
    }

    private sealed interface FieldGeneralizationFactKey {
        data class BaseOnly(
            val base: AccessPathBase,
            val staticIdx: Int,
            val fieldIdx: Int,
            val rawSuffixSlot: Int,
            val exclusions: ExclusionSet,
        ) : FieldGeneralizationFactKey

        data class Exact(
            val fact: InitialFactAp,
        ) : FieldGeneralizationFactKey
    }

    private data class ResolvedStartTraces(
        val traces: List<MethodTraceResolver.Start2FinalTrace>,
        val metadata: TraceMetadata,
    )

    data class Params(
        val resolveEntryPointToStartTrace: Boolean = true,
        val resolveAllTraces: Boolean = false,
    )

    data class Trace(
        val entryPointToStart: EntryPointToStartTrace?,
        val sourceToSinkTrace: SourceToSinkTrace,
    )

    data class EntryPointToStartTrace(
        val entryPoints: Set<EntryPointTraceNode>,
        val successors: Map<TraceNode, Set<TraceNode>>
    )

    data class SourceToSinkTrace(
        val startNodes: Set<SourceToSinkTraceNode>,
        val sinkNodes: Set<SourceToSinkTraceNode>,
        val successors: Map<InterProceduralTraceNode, Set<InterProceduralCall>>,
        val nodeMetadata: Map<InterProceduralTraceNode, TraceMetadata> = emptyMap(),
    ) {
        fun requiresFullTraceResolution(node: InterProceduralTraceNode): Boolean =
            (nodeMetadata[node] ?: TraceMetadata.Unknown).requiresFullTraceResolution

        fun findSuccessors(
            node: InterProceduralTraceNode, kind: CallKind, statement: CommonInst
        ) = successors[node]?.filter { it.kind == kind && it.statement == statement }.orEmpty()

        fun findSuccessors(node: InterProceduralTraceNode, kind: CallKind) =
            successors[node]?.filter { it.kind == kind }.orEmpty()

        fun findSuccessors(
            node: InterProceduralTraceNode, kind: CallKind, statement: CommonInst, trace: MethodTraceResolver.SummaryTrace
        ) = successors[node]?.filter {
                it.kind == kind &&
                it.statement == statement &&
                it.summary.withUniverseExclusions() == trace.withUniverseExclusions()
        }.orEmpty()
    }

    sealed interface TraceNode {
        val location: CommonMethod
    }

    sealed interface EntryPointToStartTraceNode : TraceNode

    data class CallTraceNode(val statement: CommonInst, val methodEntryPoint: MethodEntryPoint) :
        EntryPointToStartTraceNode {
        override val location: CommonMethod
            get() = methodEntryPoint.method
    }
    data class EntryPointTraceNode(override val location: CommonMethod) : EntryPointToStartTraceNode

    sealed interface SourceToSinkTraceNode : TraceNode {
        val methodEntryPoint: MethodEntryPoint

        override val location: CommonMethod
            get() = methodEntryPoint.method
    }

    data class SimpleTraceNode(
        val statement: CommonInst,
        override val methodEntryPoint: MethodEntryPoint
    ) : SourceToSinkTraceNode

    sealed interface InterProceduralTraceNode: SourceToSinkTraceNode

    data class InterProceduralStart2FinalTraceNode(
        val trace: MethodTraceResolver.Start2FinalTrace
    ) : InterProceduralTraceNode {
        override val methodEntryPoint: MethodEntryPoint
            get() = trace.method
    }

    data class InterProceduralSummaryTraceNode(
        val trace: MethodTraceResolver.SummaryTrace,
    ) : InterProceduralTraceNode {
        override val methodEntryPoint: MethodEntryPoint
            get() = trace.method
    }

    data class InterProceduralMethodEntryNode(
        val entry: MethodEntry,
    ) : InterProceduralTraceNode {
        override val methodEntryPoint: MethodEntryPoint
            get() = entry.entryPoint
    }

    // Enum can give non-determinacy as its entries have new hash code on every JVM run.
    // Override hashcode() and equals() when using enum as a field in classes whose objects
    // can be stored in sets etc.
    enum class CallKind {
        CallToSource, CallToSink
    }

    @Suppress("EqualsOrHashCode")
    data class InterProceduralCall(
        val kind: CallKind,
        val statement: CommonInst,
        val summary: MethodTraceResolver.SummaryTrace,
        val node: InterProceduralTraceNode
    ) {
        override fun hashCode(): Int {
            var result = kind.ordinal.hashCode()
            result = 31 * result + statement.hashCode()
            result = 31 * result + summary.hashCode()
            result = 31 * result + node.hashCode()
            return result
        }
    }

    sealed interface TraceResolutionResult {
        data class Resolved(val vulnerability: TaintVulnerability, val trace: Trace) : TraceResolutionResult
        data class NoTrace(val vulnerability: TaintVulnerability) : TraceResolutionResult
        data class InProgress(val state: State) : TraceResolutionResult
    }

    fun resolveTrace(
        state: State,
        isActive: () -> Boolean = cancellation::isActive,
    ): TraceResolutionResult {
        when (state) {
            is State.Initial -> {
                val requests = mutableListOf<TraceResolutionRequest>()

                val vulnerability = state.vulnerability
                val unconditionalTrace = vulnerability.vulnerabilityRules.values.firstNotNullOfOrNull {
                    collectTraceResolutionRequests(requests, vulnerability.statement, it)
                }

                if (unconditionalTrace != null) {
                    return Resolved(vulnerability, unconditionalTrace)
                }

                val nextState = Source2SinkTraceResolutionState(
                    vulnerability,
                    InterProceduralTraceGraphBuilder(),
                    requests.distinct().sorted(),
                    nextRequestIdx = 0,
                    kind = ProcessingKind.ADD_NEXT_REQUEST,
                )

                return TraceResolutionResult.InProgress(nextState)
            }

            is Source2SinkTraceResolutionState -> when (state.kind) {
                ProcessingKind.ADD_NEXT_REQUEST -> {
                    if (state.nextRequestIdx >= state.requests.size) {
                        return NoTrace(state.vulnerability)
                    }

                    var nextState = addNextRequest(state)
                    if (params.resolveAllTraces) {
                        while (nextState.nextRequestIdx < state.requests.size) {
                            nextState = addNextRequest(nextState)
                        }
                    }

                    return TraceResolutionResult.InProgress(nextState)
                }

                ProcessingKind.PROCESS -> {
                    val timeLimit = TimeSource.Monotonic.markNow() + 100.milliseconds
                    state.builder.process(stepLimit = 100, timeLimit, isActive)

                    if (!state.builder.isEmpty()) {
                        return TraceResolutionResult.InProgress(state)
                    }

                    val trace = state.builder.createSource2SinkTrace()

                    if (trace.startNodes.isEmpty()) {
                        // trace is invalid, proceed with next request
                        val nextState = state.copy(kind = ProcessingKind.ADD_NEXT_REQUEST)
                        return TraceResolutionResult.InProgress(nextState)
                    }

                    val nextState = Ep2StartTraceResolutionState(state.vulnerability, trace)
                    return TraceResolutionResult.InProgress(nextState)
                }
            }

            is Ep2StartTraceResolutionState -> {
                val entryPointToStart = resolveEntryPointToStartTrace(state.trace.startNodes)
                val resultTrace = Trace(entryPointToStart, state.trace)
                return Resolved(state.vulnerability, resultTrace)
            }
        }
    }

    fun debugInfo(state: State): StateDebugInfo = when (state) {
        is State.Initial -> StateDebugInfo("initial", "-", "-")
        is Source2SinkTraceResolutionState -> StateDebugInfo(
            phase = state.kind.name,
            request = "${state.nextRequestIdx}/${state.requests.size}",
            graph = state.builder.debugInfo(),
        )
        is Ep2StartTraceResolutionState -> StateDebugInfo(
            phase = "ENTRY_POINT_TO_START",
            request = "-",
            graph = "startNodes=${state.trace.startNodes.size}",
        )
    }

    private fun addNextRequest(state: Source2SinkTraceResolutionState): Source2SinkTraceResolutionState {
        val request = state.requests[state.nextRequestIdx]
        manager.withMethodRunner(request.methodEntryPoint) {
            val traceResolver = methodTraceResolver(request.methodEntryPoint)
            val traces = traceResolver.resolveIntraProceduralTrace(
                state.vulnerability.statement,
                request.facts,
                request.includeStatement
            )

            for (trace in traces) {
                state.builder.createSinkNode(trace)
            }
        }

        val nextState = state.copy(
            nextRequestIdx = state.nextRequestIdx + 1,
            kind = ProcessingKind.PROCESS,
        )
        return nextState
    }

    private data class TraceResolutionRequest(
        val methodEntryPoint: MethodEntryPoint,
        val includeStatement: Boolean,
        val facts: Set<InitialFactAp>
    ) : Comparable<TraceResolutionRequest> {
        override fun compareTo(other: TraceResolutionRequest): Int {
            val factsCmp = compareFacts(other.facts)
            if (factsCmp != 0) return factsCmp

            val stmtCmp = includeStatement.compareTo(other.includeStatement)
            if (stmtCmp != 0) return stmtCmp

            return methodEntryPoint.toString().compareTo(other.methodEntryPoint.toString())
        }

        private fun compareFacts(other: Set<InitialFactAp>): Int {
            val sizeCmp = facts.sumOf { it.size }.compareTo(other.sumOf { it.size })
            if (sizeCmp != 0) return sizeCmp

            val thisFactsStr = facts.map { it.toString() }.sorted().joinToString()
            val otherFactsStr = other.map { it.toString() }.sorted().joinToString()
            return thisFactsStr.compareTo(otherFactsStr)
        }
    }

    sealed interface State {
        val vulnerability: TaintVulnerability

        data class Initial(override val vulnerability: TaintVulnerability) : State
    }

    private enum class ProcessingKind {
        ADD_NEXT_REQUEST, PROCESS
    }

    private data class Source2SinkTraceResolutionState(
        override val vulnerability: TaintVulnerability,
        val builder: InterProceduralTraceGraphBuilder,
        val requests: List<TraceResolutionRequest>,
        val nextRequestIdx: Int,
        val kind: ProcessingKind,
    ): State

    private class Ep2StartTraceResolutionState(
        override val vulnerability: TaintVulnerability,
        val trace: SourceToSinkTrace,
    ): State

    private fun collectTraceResolutionRequests(
        requests: MutableList<TraceResolutionRequest>,
        statement: CommonInst,
        node: TaintVulnerabilityRuleNode
    ) : Trace? = when (node) {
        is TaintVulnerabilityRuleNode.Unconditional -> {
            val node = SimpleTraceNode(statement, node.methodEntryPoint)
            val entryPointToStart = resolveEntryPointToStartTrace(setOf(node))
            val sourceToSinkTrace = SourceToSinkTrace(setOf(node), setOf(node), emptyMap())
            Trace(entryPointToStart, sourceToSinkTrace)
        }

        is TaintVulnerabilityRuleNode.WithRequirement -> {
            node.requirement.values.firstNotNullOfOrNull { collectTraceResolutionRequests(requests, statement, it) }
        }

        is TaintVulnerabilityRuleNode.Fact -> {
            val includeStatement = when (node.vulnerabilityTriggerPosition) {
                TaintSinkTracker.VulnerabilityTriggerPosition.BEFORE_INST -> false
                TaintSinkTracker.VulnerabilityTriggerPosition.AFTER_INST -> true
            }

            for ((methodEntryPoint, factGroups) in node.facts) {
                for (facts in factGroups.facts) {
                    requests += TraceResolutionRequest(methodEntryPoint, includeStatement, facts.facts)
                }
            }

            null
        }
    }

    private fun resolveEntryPointToStartTrace(startNodes: Set<SourceToSinkTraceNode>): EntryPointToStartTrace? {
        if (!params.resolveEntryPointToStartTrace) return null
        return EntryPointToStartTraceBuilder().build(startNodes)
    }

    @Suppress("EqualsOrHashCode")
    private data class BuilderUnprocessedTrace(
        val trace: MethodTraceResolver.SummaryTrace,
        val kind: CallKind,
        val depth: Int,
        val predecessor: InterProceduralCall? = null,
        val successor: InterProceduralCall? = null
    ) {
        override fun hashCode(): Int {
            var result = trace.hashCode()
            result = 31 * result + kind.ordinal.hashCode()
            result = 31 * result + (predecessor?.hashCode() ?: 0)
            result = 31 * result + (successor?.hashCode() ?: 0)
            return result
        }
    }

    private data class PrioritizedBuilderUnprocessedTrace(
        val event: BuilderUnprocessedTrace,
        val fieldSpecificity: Int,
    )

    private data class BuilderEventKey(
        val trace: MethodTraceResolver.SummaryTrace,
        val kind: CallKind,
        val predecessor: InterProceduralCall?,
        val successor: InterProceduralCall?,
    )

    private class SummaryConclusionShape(
        private val edges: Set<MethodTraceResolver.TraceEdge>,
    ) {
        private val conclusionCount: Int
        private val cachedHashCode: Int

        init {
            val conclusions = edges.mapTo(hashSetOf()) { it.fact }
            conclusionCount = conclusions.size
            cachedHashCode = conclusions.hashCode()
        }

        override fun hashCode(): Int = cachedHashCode

        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (other !is SummaryConclusionShape) return false
            if (cachedHashCode != other.cachedHashCode || conclusionCount != other.conclusionCount) return false
            return edges.all { edge -> other.edges.any { it.fact == edge.fact } }
        }
    }

    private data class ContextualStatementKey(
        val method: MethodEntryPoint,
        val statement: CommonInst,
        val traceKind: MethodTraceResolver.TraceKind,
    )

    private data class ContextFreeStatementKey(
        val method: CommonMethod,
        val statement: CommonInst,
        val traceKind: MethodTraceResolver.TraceKind,
    )

    private data class ContextualConclusionSiteKey(
        val method: MethodEntryPoint,
        val statement: CommonInst,
        val traceKind: MethodTraceResolver.TraceKind,
        val conclusions: SummaryConclusionShape,
    )

    private data class ContextFreeConclusionSiteKey(
        val method: CommonMethod,
        val statement: CommonInst,
        val traceKind: MethodTraceResolver.TraceKind,
        val conclusions: SummaryConclusionShape,
    )

    private data class ContextFreeExactSummaryKey(
        val method: CommonMethod,
        val statement: CommonInst,
        val traceKind: MethodTraceResolver.TraceKind,
        val edges: MethodTraceResolver.TraceEdges,
    )

    private sealed interface ContextFreeStartKey {
        data class Method(
            val method: CommonMethod,
            val statement: CommonInst,
            val facts: Set<InitialFactAp>,
        ) : ContextFreeStartKey

        data class Source(
            val entry: SourceStartEntry,
        ) : ContextFreeStartKey
    }

    private data class ContextFreeResolvedSummaryKey(
        val summary: ContextFreeExactSummaryKey,
        val starts: Set<ContextFreeStartKey>,
    )

    private data class MethodEntryPremiseGroupStats(
        val entryPoint: MethodEntryPoint,
        val premises: Int,
        val redundant: Int,
    )

    private inner class InterProceduralTraceGraphBuilder {
        val fullNodes =
            hashMapOf<MethodEntryPoint, MutableMap<Pair<MethodTraceResolver.Start2FinalTrace, CallKind>, InterProceduralTraceNode>>()
        val summaryNodes =
            hashMapOf<MethodEntryPoint, MutableMap<Pair<MethodTraceResolver.SummaryTrace, CallKind>, List<InterProceduralTraceNode>>>()
        val methodEntryNodes = hashMapOf<MethodEntry, InterProceduralMethodEntryNode>()

        val sinkNodes = hashSetOf<InterProceduralTraceNode>()
        val sourceNodes = hashSetOf<InterProceduralTraceNode>()
        val rootNodes = hashSetOf<InterProceduralTraceNode>()
        val successors = hashMapOf<InterProceduralTraceNode, MutableSet<InterProceduralCall>>()
        val nodeMetadata = hashMapOf<InterProceduralTraceNode, TraceMetadata>()
        private val seenEvents = hashSetOf<BuilderEventKey>()

        private val eventComparator = compareBy<PrioritizedBuilderUnprocessedTrace>(
            { it.fieldSpecificity },
            { -it.event.depth },
        )
        private val unprocessedCall2Source = PriorityQueue(eventComparator)
        private val unprocessedCall2Sink = PriorityQueue(eventComparator)

        fun createSinkNode(trace: MethodTraceResolver.SummaryTrace) {
            val nodes = resolveNode(trace, CallKind.CallToSink, depth = 0)
            sinkNodes.addAll(nodes)
        }

        private fun pollUnprocessedEvent(): BuilderUnprocessedTrace? {
            unprocessedCall2Sink.poll()?.let { return it.event }
            unprocessedCall2Source.poll()?.let { return it.event }
            return null
        }

        private fun addUnprocessedEvent(event: BuilderUnprocessedTrace) {
            val key = BuilderEventKey(event.trace, event.kind, event.predecessor, event.successor)
            if (!seenEvents.add(key)) return
            val prioritized = PrioritizedBuilderUnprocessedTrace(
                event,
                event.trace.fieldSpecificity(),
            )
            when (event.kind) {
                CallKind.CallToSource -> unprocessedCall2Source.add(prioritized)
                CallKind.CallToSink -> unprocessedCall2Sink.add(prioritized)
            }
        }

        fun isEmpty(): Boolean =
            unprocessedCall2Sink.isEmpty() && unprocessedCall2Source.isEmpty()

        @Synchronized
        fun debugInfo(): String {
            val fullNodeCount = fullNodes.values.sumOf { it.size }
            val summaryKeyCount = summaryNodes.values.sumOf { it.size }
            val summaryNodeCount = summaryNodes.values.sumOf { byTrace ->
                byTrace.values.sumOf { it.size }
            }
            val successorCount = successors.values.sumOf { it.size }
            val topSummaryMethods = summaryNodes.entries
                .groupingBy { it.key.method }
                .fold(0) { count, entry -> count + entry.value.size }
                .entries
                .sortedByDescending { it.value }
                .take(5)
                .joinToString { "${it.key.name}:${it.value}" }
            val queuedByMethod = sequenceOf(unprocessedCall2Sink, unprocessedCall2Source)
                .flatMap { it.asSequence() }
                .groupingBy { it.event.trace.method.method }
                .eachCount()
                .entries
                .sortedByDescending { it.value }
                .take(5)
                .joinToString { "${it.key.name}:${it.value}" }
            val summaryDimensions = summaryDimensionDebugInfo()
            val premiseRedundancy = methodEntryPremiseDebugInfo()
            return "queues=${unprocessedCall2Sink.size}/${unprocessedCall2Source.size}, " +
                "nodes=$fullNodeCount/$summaryKeyCount/$summaryNodeCount/${methodEntryNodes.size}, " +
                "edges=$successorCount, roots=${rootNodes.size}, " +
                "sources=${sourceNodes.size}, sinks=${sinkNodes.size}, " +
                "caches=${start2FinalTraceCache.size}/${generalizedStart2FinalTraceCache.size}, " +
                "events=${seenEvents.size}, " +
                "topSummary=[$topSummaryMethods], queued=[$queuedByMethod], " +
                "$summaryDimensions, $premiseRedundancy"
        }

        private fun summaryDimensionDebugInfo(): String {
            val traces = hashSetOf<MethodTraceResolver.SummaryTrace>()
            summaryNodes.values.forEach { byTrace ->
                byTrace.keys.forEach { traces += it.first }
            }

            val methods = hashSetOf<CommonMethod>()
            val entryPoints = hashSetOf<MethodEntryPoint>()
            val contexts = hashSetOf<Any>()
            val statements = hashSetOf<CommonInst>()
            val conclusionShapes = hashSetOf<SummaryConclusionShape>()
            val contextualStatements = hashSetOf<ContextualStatementKey>()
            val contextFreeStatements = hashSetOf<ContextFreeStatementKey>()
            val contextualConclusionSites = hashSetOf<ContextualConclusionSiteKey>()
            val contextFreeConclusionSites = hashSetOf<ContextFreeConclusionSiteKey>()
            val contextFreeExactSummaries = hashSetOf<ContextFreeExactSummaryKey>()
            val contextFreeResolvedSummaries = hashSetOf<ContextFreeResolvedSummaryKey>()

            for (trace in traces) {
                val method = trace.method
                val statement = trace.final.statement
                val shape = SummaryConclusionShape(trace.final.edges)
                methods += method.method
                entryPoints += method
                contexts += method.context
                statements += statement
                conclusionShapes += shape
                contextualStatements += ContextualStatementKey(method, statement, trace.traceKind)
                contextFreeStatements += ContextFreeStatementKey(method.method, statement, trace.traceKind)
                contextualConclusionSites += ContextualConclusionSiteKey(method, statement, trace.traceKind, shape)
                contextFreeConclusionSites += ContextFreeConclusionSiteKey(method.method, statement, trace.traceKind, shape)
                val exactKey = ContextFreeExactSummaryKey(
                    method.method,
                    statement,
                    trace.traceKind,
                    trace.final.edges,
                )
                contextFreeExactSummaries += exactKey
                start2FinalTraceCache[trace]?.let { resolved ->
                    val starts = resolved.traces.mapTo(hashSetOf()) { startTrace ->
                        when (val start = startTrace.startEntry) {
                            is MethodEntry -> ContextFreeStartKey.Method(
                                start.entryPoint.method,
                                start.entryPoint.statement,
                                start.facts,
                            )
                            is SourceStartEntry -> ContextFreeStartKey.Source(start)
                        }
                    }
                    contextFreeResolvedSummaries += ContextFreeResolvedSummaryKey(exactKey, starts)
                }
            }

            val tracesByMethod = traces.groupingBy { it.method.method }.eachCount()
            val contextualConclusionsByMethod = contextualConclusionSites.groupingBy { it.method.method }.eachCount()
            val contextFreeConclusionsByMethod = contextFreeConclusionSites.groupingBy { it.method }.eachCount()
            val statementsByMethod = contextFreeStatements.groupingBy { it.method }.eachCount()
            val topMethods = tracesByMethod.entries
                .sortedByDescending { it.value }
                .take(5)
                .joinToString { (method, traceCount) ->
                    val contextualConclusions = contextualConclusionsByMethod[method] ?: 0
                    val contextFreeConclusions = contextFreeConclusionsByMethod[method] ?: 0
                    val premiseExtra = traceCount - contextualConclusions
                    val contextExtra = contextualConclusions - contextFreeConclusions
                    "${method.name}:t=$traceCount/s=${statementsByMethod[method] ?: 0}" +
                        "/c=$contextualConclusions/p=$premiseExtra/x=$contextExtra"
                }

            return "summaryDims=" +
                "traces=${traces.size}/methods=${methods.size}/eps=${entryPoints.size}/ctx=${contexts.size}" +
                "/stmt=${statements.size}/stmtCtx=${contextualStatements.size}" +
                "/stmtNoCtx=${contextFreeStatements.size}/conclusions=${conclusionShapes.size}" +
                "/sites=${contextualConclusionSites.size}/sitesNoCtx=${contextFreeConclusionSites.size}" +
                "/exactNoCtx=${contextFreeExactSummaries.size}" +
                "/resolvedNoCtx=${contextFreeResolvedSummaries.size}" +
                "/premiseExtra=${traces.size - contextualConclusionSites.size}" +
                "/contextExtra=${contextualConclusionSites.size - contextFreeConclusionSites.size}, " +
                "topSummaryDims=[$topMethods]"
        }

        private fun methodEntryPremiseDebugInfo(): String {
            val groupStats = methodEntryNodes.keys
                .groupBy { it.entryPoint }
                .map { (entryPoint, entries) ->
                    val premiseSets = entries.map { it.facts }.sortedBy { it.size }
                    val minimalPremisesByFact = hashMapOf<InitialFactAp, MutableList<Set<InitialFactAp>>>()
                    var emptyPremiseSeen = false
                    var redundant = 0

                    for (premises in premiseSets) {
                        val covered = emptyPremiseSeen || premises.any { fact ->
                            minimalPremisesByFact[fact]?.any { minimal ->
                                minimal.size < premises.size && premises.containsAll(minimal)
                            } == true
                        }
                        if (covered) {
                            redundant++
                        } else if (premises.isEmpty()) {
                            emptyPremiseSeen = true
                        } else {
                            minimalPremisesByFact.getOrPut(premises.first(), ::arrayListOf).add(premises)
                        }
                    }

                    MethodEntryPremiseGroupStats(entryPoint, premiseSets.size, redundant)
                }

            val redundant = groupStats.sumOf { it.redundant }
            val variantGroups = groupStats.count { it.premises > 1 }
            val topGroups = groupStats
                .sortedWith(compareByDescending<MethodEntryPremiseGroupStats> { it.redundant }
                    .thenByDescending { it.premises })
                .take(5)
                .joinToString { stats ->
                    "${stats.entryPoint.method.name}@${Integer.toHexString(stats.entryPoint.hashCode())}:" +
                        "n=${stats.premises}/r=${stats.redundant}"
                }

            return "entryPremises=" +
                "nodes=${methodEntryNodes.size}/eps=${groupStats.size}/variantGroups=$variantGroups" +
                "/redundant=$redundant, topEntryPremises=[$topGroups]"
        }

        @Synchronized
        fun process(stepLimit: Int, timeLimit: TimeMark, isActive: () -> Boolean) {
            var steps = 0
            while (
                cancellation.isActive() && isActive() &&
                ++steps < stepLimit && timeLimit.hasNotPassedNow()
            ) {
                val event = pollUnprocessedEvent() ?: break
                val resolvedNodes = resolveNode(event.trace, event.kind, event.depth)

                for (resolved in resolvedNodes) {
                    event.predecessor?.let { predecessor ->
                        val predSucc = successors.getOrPut(predecessor.node, ::hashSetOf)
                        predSucc.add(predecessor.copy(node = resolved))
                    }

                    event.successor?.let { successor ->
                        val nodeSucc = successors.getOrPut(resolved, ::hashSetOf)
                        nodeSucc.add(successor)
                    }
                }
            }
        }

        fun createSource2SinkTrace(): SourceToSinkTrace {
            val canReachSource = entriesThatCanReach(successors, sourceNodes) { edge ->
                edge.takeIf { it.kind == CallKind.CallToSource }?.node
            }
            val canReachSink = entriesThatCanReach(successors, sinkNodes) { edge ->
                edge.takeIf { it.kind == CallKind.CallToSink }?.node
            }
            val rootsWithReachableSinks = rootNodes.filterTo(hashSetOf()) {
                it in canReachSource && it in canReachSink
            }

            if (rootsWithReachableSinks.isEmpty()) return SourceToSinkTrace(emptySet(), emptySet(), emptyMap())

            return SourceToSinkTrace(
                rootsWithReachableSinks,
                sinkNodes,
                successors,
                nodeMetadata,
            )
        }

        private fun resolveNode(
            trace: MethodTraceResolver.SummaryTrace,
            kind: CallKind,
            depth: Int,
        ): List<InterProceduralTraceNode> {
            val normalizedTrace = trace.withUniverseExclusions()
            val traceNodes = summaryNodes.getOrPut(normalizedTrace.method, ::hashMapOf)
            val cacheKey = normalizedTrace to kind
            val currentNode = traceNodes[cacheKey]
            if (currentNode != null) return currentNode

            val resolved = resolveStart2FinalTrace(normalizedTrace)

            val resultNodes = mutableListOf<InterProceduralTraceNode>()
            var retainedSummaryNode: InterProceduralSummaryTraceNode? = null

            for (s2fTrace in resolved.traces) {
                when (val start = s2fTrace.startEntry) {
                    is SourceStartEntry -> {
                        val node = resolveNode(s2fTrace, kind, depth)
                        resultNodes += node
                        recordMetadata(node, resolved.metadata)
                    }

                    is MethodEntry -> {
                        check(kind != CallKind.CallToSource) { "Unexpected trace: $normalizedTrace" }
                        if (manager.apManager is BaseOnlyApManager) {
                            val summaryNode = retainedSummaryNode
                                ?: InterProceduralSummaryTraceNode(normalizedTrace).also {
                                    retainedSummaryNode = it
                                    resultNodes += it
                                }
                            val existingBoundary = methodEntryNodes[start]
                            val boundary = existingBoundary
                                ?: InterProceduralMethodEntryNode(start).also {
                                    methodEntryNodes[start] = it
                                    nodeMetadata[it] = TraceMetadata(requiresFullTraceResolution = false)
                                }
                            successors.getOrPut(boundary, ::hashSetOf).add(
                                InterProceduralCall(
                                    kind,
                                    normalizedTrace.final.statement,
                                    normalizedTrace,
                                    summaryNode,
                                )
                            )
                            if (existingBoundary == null) {
                                for ((callerStatement, callerTrace) in resolveMethodEntry(start)) {
                                    addUnprocessedEvent(
                                        BuilderUnprocessedTrace(
                                            trace = callerTrace,
                                            kind = kind,
                                            depth = depth + 1,
                                            successor = InterProceduralCall(
                                                kind,
                                                callerStatement,
                                                normalizedTrace,
                                                boundary,
                                            ),
                                        )
                                    )
                                }
                            }
                            recordMetadata(summaryNode, resolved.metadata)
                        } else {
                            val node = InterProceduralStart2FinalTraceNode(s2fTrace)
                            val callerTraces = resolveMethodEntry(start)
                            for ((callerStatement, callerTrace) in callerTraces) {
                                addUnprocessedEvent(
                                    BuilderUnprocessedTrace(
                                        trace = callerTrace,
                                        kind = kind,
                                        depth = depth + 1,
                                        successor = InterProceduralCall(
                                            kind,
                                            callerStatement,
                                            normalizedTrace,
                                            node,
                                        ),
                                    )
                                )
                            }
                            resultNodes += node
                            recordMetadata(node, resolved.metadata)
                        }
                    }
                }
            }

            traceNodes[cacheKey] = resultNodes
            return resultNodes
        }

        private fun resolveStart2FinalTrace(
            trace: MethodTraceResolver.SummaryTrace,
        ): ResolvedStartTraces =
            start2FinalTraceCache.computeIfAbsent(trace) {
                val cacheKey = trace.fieldGeneralizationCacheKey()
                val generalized = generalizedStart2FinalTraceCache.computeIfAbsent(cacheKey) { mutableListOf() }

                synchronized(generalized) {
                    generalized.firstOrNull { it.trace.fieldGeneralizationCovers(trace) }?.let {
                        return@computeIfAbsent it.result
                    }
                }

                val resolved = manager.withMethodRunner(trace.method) {
                    // The over-approximate resolver intentionally does not traverse the complete
                    // start-to-final body. Consequently it cannot derive complete action metadata.
                    val traceResolver = methodTraceResolver(trace.method)
                    val traces = traceResolver.resolveIntraProceduralOverApproximateStart2FinalTrace(
                        trace,
                        cancellation,
                    )
                    ResolvedStartTraces(traces, TraceMetadata.Unknown)
                }

                synchronized(generalized) {
                    generalized.firstOrNull { it.trace.fieldGeneralizationCovers(trace) }?.let {
                        return@computeIfAbsent it.result
                    }
                    if (resolved.traces.isNotEmpty()) {
                        generalized.removeIf { trace.fieldGeneralizationCovers(it.trace) }
                        generalized += CachedStartTrace(trace, resolved)
                    }
                }
                resolved
            }

        private fun MethodTraceResolver.SummaryTrace.fieldGeneralizationCacheKey(): FieldGeneralizationCacheKey {
            val start = StartTraceCacheKey(method, final.statement, traceKind)
            val edges = final.edges
                .groupingBy { it.fieldGeneralizationKey() }
                .eachCount()
            return FieldGeneralizationCacheKey(start, edges)
        }

        private fun MethodTraceResolver.TraceEdge.fieldGeneralizationKey(): FieldGeneralizationEdgeKey =
            when (this) {
                is MethodTraceResolver.TraceEdge.SourceTraceEdge ->
                    FieldGeneralizationEdgeKey.Source(fact.fieldGeneralizationKey())

                is MethodTraceResolver.TraceEdge.MethodTraceEdge ->
                    FieldGeneralizationEdgeKey.Method(
                        initialFact.fieldGeneralizationKey(),
                        fact.fieldGeneralizationKey(),
                    )

                is MethodTraceResolver.TraceEdge.MethodTraceNDEdge ->
                    FieldGeneralizationEdgeKey.Exact(this)
            }

        private fun InitialFactAp.fieldGeneralizationKey(): FieldGeneralizationFactKey {
            val fact = this as? BaseOnlyInitialFactAp
                ?: return FieldGeneralizationFactKey.Exact(this)
            val projectedField = if (fact.access.suffixIdx == NO_ACCESSOR) {
                fact.access.fieldIdx
            } else {
                NO_ACCESSOR
            }
            return FieldGeneralizationFactKey.BaseOnly(
                fact.base,
                fact.access.staticIdx,
                projectedField,
                fact.access.rawSuffixSlot,
                fact.exclusions,
            )
        }

        private fun recordMetadata(node: InterProceduralTraceNode, metadata: TraceMetadata) {
            nodeMetadata.merge(node, metadata, TraceMetadata::merge)
        }

        private fun MethodTraceResolver.SummaryTrace.fieldGeneralizationCovers(
            other: MethodTraceResolver.SummaryTrace,
        ): Boolean {
            if (method != other.method ||
                traceKind != other.traceKind ||
                final.statement != other.final.statement ||
                final.edges.size != other.final.edges.size
            ) {
                return false
            }
            val available = final.edges.toMutableList()
            for (otherEdge in other.final.edges) {
                val coveringIdx = available.indexOfFirst { it.fieldGeneralizationCovers(otherEdge) }
                if (coveringIdx < 0) return false
                available.removeAt(coveringIdx)
            }
            return true
        }

        private fun MethodTraceResolver.SummaryTrace.fieldSpecificity(): Int =
            final.edges.sumOf { it.fieldSpecificity() }

        private fun MethodTraceResolver.TraceEdge.fieldSpecificity(): Int = when (this) {
            is MethodTraceResolver.TraceEdge.SourceTraceEdge -> fact.fieldSpecificity()
            is MethodTraceResolver.TraceEdge.MethodTraceEdge ->
                initialFact.fieldSpecificity() + fact.fieldSpecificity()

            is MethodTraceResolver.TraceEdge.MethodTraceNDEdge ->
                initialFacts.sumOf { it.fieldSpecificity() } + fact.fieldSpecificity()
        }

        private fun InitialFactAp.fieldSpecificity(): Int {
            val fact = this as? BaseOnlyInitialFactAp ?: return 0
            return if (fact.access.fieldIdx != NO_ACCESSOR && fact.access.suffixIdx != NO_ACCESSOR) 1 else 0
        }

        private fun MethodTraceResolver.TraceEdge.fieldGeneralizationCovers(
            other: MethodTraceResolver.TraceEdge,
        ): Boolean = when {
            this is MethodTraceResolver.TraceEdge.SourceTraceEdge &&
                other is MethodTraceResolver.TraceEdge.SourceTraceEdge ->
                fact.baseOnlyTraceFieldGeneralizationCovers(other.fact)

            this is MethodTraceResolver.TraceEdge.MethodTraceEdge &&
                other is MethodTraceResolver.TraceEdge.MethodTraceEdge ->
                initialFact.baseOnlyTraceFieldGeneralizationCovers(other.initialFact) &&
                    fact.baseOnlyTraceFieldGeneralizationCovers(other.fact)

            this is MethodTraceResolver.TraceEdge.MethodTraceNDEdge &&
                other is MethodTraceResolver.TraceEdge.MethodTraceNDEdge ->
                this == other

            else -> false
        }

        private fun resolveNode(trace: MethodTraceResolver.Start2FinalTrace, kind: CallKind, depth: Int): InterProceduralTraceNode {
            val traceNodes = fullNodes.getOrPut(trace.method, ::hashMapOf)
            val cacheKey = trace to kind
            val currentNode = traceNodes[cacheKey]
            if (currentNode != null) return currentNode

            when (val start = trace.startEntry) {
                is MethodEntry -> {
                    TODO("Method full traces not used in inter-procedural graph builder (yet)")
                }

                is SourceStartEntry -> {
                    val node = InterProceduralStart2FinalTraceNode(trace)
                    traceNodes[cacheKey] = node

                    if (kind == CallKind.CallToSink) {
                        rootNodes.add(node)
                    }

                    val callSummary = start.sourcePrimaryAction as? TraceEntryAction.CallSourceSummary
                    if (callSummary == null) {
                        sourceNodes.add(node)
                        return node
                    }

                    val normalizedSummary = callSummary.summaryTrace.withUniverseExclusions()
                    addUnprocessedEvent(
                        BuilderUnprocessedTrace(
                            trace = normalizedSummary,
                            kind = CallKind.CallToSource,
                            depth = depth + 1,
                            predecessor = InterProceduralCall(
                                CallKind.CallToSource,
                                start.statement,
                                normalizedSummary,
                                node
                            )
                        )
                    )

                    return node
                }
            }
        }

        private fun resolveMethodEntry(
            methodEntry: MethodEntry
        ): List<Pair<CommonInst, MethodTraceResolver.SummaryTrace>> =
            methodEntryCallerTraceCache.computeIfAbsent(methodEntry) {
                val callers = manager.findMethodCallers(
                    methodEntry.entryPoint,
                    collectZeroCallsOnly = manager.apManager !is BaseOnlyApManager,
                )
                callers.flatMap { caller ->
                    manager.withMethodRunner(caller.callerEp) {
                        val traceResolver = methodTraceResolver(caller.callerEp)
                        traceResolver.resolveIntraProceduralTraceFromCall(caller.statement, methodEntry)
                    }.map { caller.statement to it.withUniverseExclusions() }
                }.distinct()
            }
    }

    inner class EntryPointToStartTraceBuilder {
        private val entryPointNodes = hashSetOf<EntryPointTraceNode>()
        private val nodeSuccessors = hashMapOf<TraceNode, MutableSet<TraceNode>>()

        fun build(startNodes: Set<SourceToSinkTraceNode>): EntryPointToStartTrace {
            val unprocessedMethods = mutableListOf<Pair<MethodEntryPoint, TraceNode>>()
            startNodes.mapTo(unprocessedMethods) { it.methodEntryPoint to it }

            val visitedEp = hashSetOf<Pair<MethodEntryPoint, TraceNode>>()
            while (unprocessedMethods.isNotEmpty() && cancellation.isActive()) {
                val methodCall = unprocessedMethods.removeLast()
                if (!visitedEp.add(methodCall)) continue

                val (methodEp, methodCallNode) = methodCall
                if (methodEp.method in entryPointMethods) {
                    val epNode = EntryPointTraceNode(methodEp.method)
                    entryPointNodes.add(epNode)
                    nodeSuccessors.getOrPut(epNode, ::hashSetOf).add(methodCallNode)
                }

                val methodCallers = manager.findMethodCallers(methodEp)
                for (caller in methodCallers) {
                    val callNode = CallTraceNode(caller.statement, caller.callerEp)
                    nodeSuccessors.getOrPut(callNode, ::hashSetOf).add(methodCallNode)
                    unprocessedMethods += (caller.callerEp to callNode)
                }
            }

            return EntryPointToStartTrace(entryPointNodes, nodeSuccessors)
        }
    }
}

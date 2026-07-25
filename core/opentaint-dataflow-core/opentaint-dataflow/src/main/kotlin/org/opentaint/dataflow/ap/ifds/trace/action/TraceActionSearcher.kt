package org.opentaint.dataflow.ap.ifds.trace.action

import mu.KLogging
import org.opentaint.dataflow.ap.ifds.TaintAnalysisUnitRunnerManager
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.FullStart2FinalTrace
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.SummaryTrace
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEdge
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEntry
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEntryAction
import org.opentaint.dataflow.ap.ifds.trace.TraceResolver
import org.opentaint.dataflow.ap.ifds.trace.VulnerabilityWithInterproceduralTrace
import org.opentaint.dataflow.ap.ifds.trace.path.Source2SinkTraceGraph
import org.opentaint.dataflow.ap.ifds.trace.path.createSource2SinkGraph
import org.opentaint.dataflow.ap.ifds.trace.withMethodRunner
import org.opentaint.dataflow.configuration.CommonTaintAction
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSink
import org.opentaint.ir.api.common.cfg.CommonInst

private val logger = object : KLogging() {}.logger

private typealias Rules = Map<CommonInst, Map<CommonTaintConfigurationItem, Set<CommonTaintAction>>>

sealed interface ActionableRulesCollectionResult {
    data object Failed : ActionableRulesCollectionResult

    data class Collected(
        val rules: Map<CommonInst, Map<CommonTaintConfigurationItem, Set<CommonTaintAction>>>,
    ) : ActionableRulesCollectionResult
}

fun TaintAnalysisUnitRunnerManager.collectActionableRules(
    vulnerability: VulnerabilityWithInterproceduralTrace,
): ActionableRulesCollectionResult {
    val trace = vulnerability.trace ?: return ActionableRulesCollectionResult.Failed
    return collectActionableRules(
        trace = trace,
        sinkStatement = vulnerability.vulnerability.statement,
        sinkRules = vulnerability.vulnerability.vulnerabilityRules.keys,
        materializeNode = { node ->
            withMethodRunner(node.methodEntryPoint) {
                val resolver = methodTraceResolver(node.methodEntryPoint)
                when (node) {
                    is TraceResolver.InterProceduralStart2FinalTraceNode ->
                        resolver.resolveIntraProceduralFullStart2FinalTrace(
                            node.trace,
                            cancellation,
                            collapseUnchangedNodes = true,
                        )

                    is TraceResolver.InterProceduralSummaryTraceNode ->
                        resolver.resolveIntraProceduralFullStart2FinalTrace(
                            node.trace,
                            cancellation,
                            collapseUnchangedNodes = true,
                        )
                }
            }
        },
        materializeSummary = { summary ->
            withMethodRunner(summary.method) {
                methodTraceResolver(summary.method).resolveIntraProceduralFullStart2FinalTrace(
                    summary,
                    cancellation,
                    collapseUnchangedNodes = true,
                )
            }
        },
        isActive = cancellation::isActive,
    )
}

fun collectActionableRules(
    trace: TraceResolver.Trace,
    sinkStatement: CommonInst,
    sinkRules: Collection<CommonTaintConfigurationItem>,
    materializeNode: (TraceResolver.InterProceduralTraceNode) -> List<FullStart2FinalTrace>,
    materializeSummary: (SummaryTrace) -> List<FullStart2FinalTrace>,
    isActive: () -> Boolean = { true },
): ActionableRulesCollectionResult = runCatching {
    TraceActionCollector(
        trace,
        sinkStatement,
        sinkRules,
        materializeNode,
        materializeSummary,
        isActive,
    ).collect()
}.getOrElse {
    logger.error(it) { "Failed to collect actionable rules" }
    ActionableRulesCollectionResult.Failed
}

fun mergeActionableRules(
    results: Iterable<ActionableRulesCollectionResult.Collected>,
): Rules {
    val merged = RulesAccumulator()
    results.forEach { result -> merged.addAll(result.rules) }
    return merged.freeze()
}

internal fun SummaryTrace.shouldExpand(): Boolean {
    val facts = final.edges.flatMapTo(linkedSetOf()) { it.boundaryFacts() }
    if (facts.any { fact -> fact.getAllAccessors().any { it is TaintMarkAccessor } }) {
        return true
    }
    return facts.any { !it.isAbstract() }
}

private fun TraceEdge.boundaryFacts(): Set<InitialFactAp> = when (this) {
    is TraceEdge.SourceTraceEdge -> setOf(fact)
    is TraceEdge.MethodTraceEdge -> setOf(initialFact, fact)
    is TraceEdge.MethodTraceNDEdge -> initialFacts + fact
}

private class TraceActionCollector(
    private val trace: TraceResolver.Trace,
    private val sinkStatement: CommonInst,
    sinkRules: Collection<CommonTaintConfigurationItem>,
    private val materializeNode: (TraceResolver.InterProceduralTraceNode) -> List<FullStart2FinalTrace>,
    private val materializeSummary: (SummaryTrace) -> List<FullStart2FinalTrace>,
    private val isActive: () -> Boolean,
) {
    private enum class TraceOrigin {
        OuterNode,
        NestedSummary,
    }

    private sealed interface Evaluation {
        data class Valid(val rules: Rules) : Evaluation
        data object Invalid : Evaluation
        data object Failed : Evaluation
    }

    private val sinkRules = sinkRules.toSet()
    private val summaryResults = hashMapOf<SummaryTrace, Evaluation>()
    private val summariesInProgress = hashSetOf<SummaryTrace>()

    fun collect(): ActionableRulesCollectionResult {
        if (!isActive()) return ActionableRulesCollectionResult.Failed
        check(sinkRules.isNotEmpty()) { "No sink rule attached to the vulnerability" }
        check(sinkRules.all { it is CommonTaintConfigurationSink }) {
            "Actionable-rule collection was seeded with a non-sink rule"
        }

        val sourceToSink = trace.sourceToSinkTrace
        val endpointNodes = sourceToSink.startNodes + sourceToSink.sinkNodes
        if (endpointNodes.isNotEmpty() && endpointNodes.all { it is TraceResolver.SimpleTraceNode }) {
            return ActionableRulesCollectionResult.Collected(sinkRuleMap())
        }
        if (endpointNodes.any { it is TraceResolver.SimpleTraceNode }) {
            return ActionableRulesCollectionResult.Failed
        }

        val graph = createSource2SinkGraph(sourceToSink)
        if (!isActive()) return ActionableRulesCollectionResult.Failed

        val nodeResults = arrayOfNulls<Evaluation>(graph.allNodes.size)
        for (nodeId in graph.allNodes.indices) {
            if (!isActive()) return ActionableRulesCollectionResult.Failed
            val seed = if (graph.sinkNodes.contains(nodeId)) sinkRuleMap() else emptyMap()
            val result = evaluateNode(graph.allNodes[nodeId], seed)
            if (result === Evaluation.Failed) return ActionableRulesCollectionResult.Failed
            nodeResults[nodeId] = result
        }

        val validNodes = graph.allNodes.indices
            .filterTo(linkedSetOf()) { nodeResults[it] is Evaluation.Valid }
        val reachableValidNodes = graph.corridor(validNodes, isActive)
            ?: return ActionableRulesCollectionResult.Failed

        val collected = RulesAccumulator()
        for (nodeId in reachableValidNodes) {
            if (!isActive()) return ActionableRulesCollectionResult.Failed
            val result = nodeResults[nodeId] as? Evaluation.Valid ?: continue
            collected.addAll(result.rules)
        }

        val rules = collected.freeze()
        return if (rules.isEmpty()) {
            ActionableRulesCollectionResult.Failed
        } else {
            ActionableRulesCollectionResult.Collected(rules)
        }
    }

    private fun evaluateNode(
        node: TraceResolver.InterProceduralTraceNode,
        seed: Rules,
    ): Evaluation {
        val traces = materializeNode(node)
        if (traces.isEmpty()) return Evaluation.Invalid

        if (!isActive()) return Evaluation.Failed
        return evaluateResolvedTraces(traces, TraceOrigin.OuterNode, seed)
    }

    private fun evaluateSummary(summary: SummaryTrace): Evaluation {
        summaryResults[summary]?.let { return it }
        if (!summariesInProgress.add(summary)) return Evaluation.Invalid

        val traces = materializeSummary(summary)
        if (traces.isEmpty()) return Evaluation.Invalid

        val evaluation = evaluateResolvedTraces(traces, TraceOrigin.NestedSummary, emptyMap())
        summariesInProgress.remove(summary)

        if (evaluation !== Evaluation.Failed) {
            summaryResults[summary] = evaluation
        }
        return evaluation
    }

    private fun evaluateResolvedTraces(
        traces: List<FullStart2FinalTrace>,
        origin: TraceOrigin,
        seed: Rules,
    ): Evaluation {
        if (traces.isEmpty()) return Evaluation.Invalid

        val collected = RulesAccumulator()
        var hasValidTrace = false
        for (fullTrace in traces) {
            if (!isActive()) return Evaluation.Failed
            when (val result = evaluateFullTrace(fullTrace, origin, seed)) {
                is Evaluation.Valid -> {
                    hasValidTrace = true
                    collected.addAll(result.rules)
                }

                Evaluation.Invalid -> Unit
                Evaluation.Failed -> return Evaluation.Failed
            }
        }

        return if (hasValidTrace) Evaluation.Valid(collected.freeze()) else Evaluation.Invalid
    }

    /**
     * Evaluates one materialized intra-procedural trace.
     *
     * Relevant summaries are resolved first. An entry whose nested summary has
     * no valid full trace is removed, then reachability is recomputed without
     * all removed entries. Rules are projected only from the remaining
     * start-to-final corridor.
     */
    private fun evaluateFullTrace(
        trace: FullStart2FinalTrace,
        origin: TraceOrigin,
        seed: Rules,
    ): Evaluation {
        val invalidEntries = hashSetOf<Int>()
        val summaryRules = hashMapOf<Int, Rules>()

        for ((entryId, entry) in trace.entries.withIndex()) {
            if (!isActive()) return Evaluation.Failed
            val summary = entry.relevantSummary(origin) ?: continue
            when (val nestedResult = evaluateSummary(summary)) {
                is Evaluation.Valid -> summaryRules[entryId] = nestedResult.rules
                Evaluation.Invalid -> invalidEntries += entryId
                Evaluation.Failed -> return Evaluation.Failed
            }
        }

        val reachableEntries = trace.corridorWithout(invalidEntries, isActive)
        if (trace.finalId !in reachableEntries) return Evaluation.Invalid

        val collected = RulesAccumulator()
        collected.addAll(seed)
        for (entryId in reachableEntries) {
            if (!isActive()) return Evaluation.Failed
            summaryRules[entryId]?.let(collected::addAll)
            collected.addRuleActions(trace.entries[entryId])
        }

        val rules = collected.freeze()
        return if (rules.isEmpty()) Evaluation.Invalid else Evaluation.Valid(rules)
    }

    private fun TraceEntry.relevantSummary(origin: TraceOrigin): SummaryTrace? = when (this) {
        is TraceEntry.Action -> when (val action = primaryAction) {
            is TraceEntryAction.CallSourceSummary -> action.summaryTrace
            is TraceEntryAction.CallSummary -> action.summaryTrace.takeIf { it.shouldExpand() }
            else -> null
        }

        is TraceEntry.SourceStartEntry -> {
            val action = sourcePrimaryAction
            if (origin == TraceOrigin.NestedSummary && action is TraceEntryAction.CallSourceSummary) {
                action.summaryTrace
            } else {
                null
            }
        }

        else -> null
    }

    private fun RulesAccumulator.addRuleActions(entry: TraceEntry) {
        val actions: Iterable<TraceEntryAction> = when (entry) {
            is TraceEntry.Action -> entry.otherActions
            is TraceEntry.SourceStartEntry -> entry.sourceOtherActions
            else -> emptyList()
        }

        actions.forEach { action ->
            when (action) {
                is TraceEntryAction.CallRuleAction -> {
                    addAction(entry.statement, action.rule, action.action)
                }

                is TraceEntryAction.SequentialSourceRule -> {
                    addAction(entry.statement, action.rule, action.action)
                }

                is TraceEntryAction.CallSourceSummary,
                is TraceEntryAction.CallSummary,
                is TraceEntryAction.UnresolvedCallSkip,
                is TraceEntryAction.Sequential -> {
                    // skip, no rules
                }
            }
        }
    }

    private fun sinkRuleMap(): Rules {
        val rules = RulesAccumulator()
        sinkRules.forEach { rules.addSink(sinkStatement, it) }
        return rules.freeze()
    }
}

private class RulesAccumulator {
    private val rules =
        linkedMapOf<CommonInst, LinkedHashMap<CommonTaintConfigurationItem, MutableSet<CommonTaintAction>>>()

    fun addSink(statement: CommonInst, rule: CommonTaintConfigurationItem) {
        check(rule is CommonTaintConfigurationSink) { "Non-sink rule has an empty action set: $rule" }
        val statementRules = rules.getOrPut(statement) { linkedMapOf() }
        check(statementRules[rule]?.isNotEmpty() != true) {
            "Configuration item is both a sink and an action-owning rule: $rule"
        }
        statementRules.getOrPut(rule) { linkedSetOf() }
    }

    fun addAction(
        statement: CommonInst,
        rule: CommonTaintConfigurationItem,
        actions: Set<CommonTaintAction>,
    ) {
        check(actions.isNotEmpty()) { "Rule action has an empty action set: $rule" }
        check(rule !is CommonTaintConfigurationSink) { "Sink rule has actions: $rule" }
        rules.getOrPut(statement) { linkedMapOf() }
            .getOrPut(rule) { linkedSetOf() }
            .addAll(actions)
    }

    fun addAll(other: Rules) {
        other.forEach { (statement, statementRules) ->
            statementRules.forEach { (rule, actions) ->
                if (actions.isEmpty()) addSink(statement, rule) else addAction(statement, rule, actions)
            }
        }
    }

    fun freeze(): Rules = rules.mapValues { (_, statementRules) ->
        statementRules.mapValues { (_, actions) -> actions.toSet() }.toMap()
    }.toMap()
}

private fun FullStart2FinalTrace.corridorWithout(
    invalidEntries: Set<Int>,
    isActive: () -> Boolean,
): Set<Int> {
    val allowed = entries.indices.filterTo(hashSetOf()) { it !in invalidEntries }
    if (startEntryId !in allowed || finalId !in allowed || !isActive()) return emptySet()

    val reachable = reachableNodes(setOf(startEntryId), allowed, isActive) { entryId ->
        successors.get(entryId)?.let { successors ->
            buildList { successors.forEach { add(it) } }
        }.orEmpty()
    }

    val predecessors = Array(entries.size) { mutableSetOf<Int>() }
    for ((from, successors) in successors) {
        if (!isActive()) return emptySet()
        successors.forEach { to -> predecessors[to] += from }
    }
    val canReachFinal = reachableNodes(setOf(finalId), allowed, isActive) { predecessors[it] }
    return reachable.intersect(canReachFinal)
}

private fun Source2SinkTraceGraph.corridor(
    allowedNodes: Set<Int>,
    isActive: () -> Boolean,
): Set<Int>? {
    if (allowedNodes.isEmpty() || !isActive()) return null

    val sources = sourceNodes.toIntArray().filterTo(linkedSetOf()) { isActive() && it in allowedNodes }
    val sinks = sinkNodes.toIntArray().filterTo(linkedSetOf()) { isActive() && it in allowedNodes }
    val roots = rootNodes.toIntArray().filterTo(linkedSetOf()) { isActive() && it in allowedNodes }
    if (sources.isEmpty() || sinks.isEmpty() || roots.isEmpty()) return null

    val canReachSource = reachableNodes(sources, allowedNodes, isActive) {
        root2SourceBwd[it]?.toIntArray()?.asList().orEmpty()
    }
    val canReachSink = reachableNodes(sinks, allowedNodes, isActive) {
        root2SinkBwd[it]?.toIntArray()?.asList().orEmpty()
    }
    if (!isActive()) return null
    val completeRoots = roots.filterTo(linkedSetOf()) {
        isActive() && it in canReachSource && it in canReachSink
    }
    if (completeRoots.isEmpty()) return null

    val sourceForward = reachableNodes(completeRoots, allowedNodes, isActive) {
        root2SourceFwd[it]?.toIntArray()?.asList().orEmpty()
    }
    val sinkForward = reachableNodes(completeRoots, allowedNodes, isActive) {
        root2SinkFwd[it]?.toIntArray()?.asList().orEmpty()
    }
    if (!isActive()) return null
    val sourceCorridor = sourceForward.intersect(canReachSource)
    val sinkCorridor = sinkForward.intersect(canReachSink)
    return (sourceCorridor + sinkCorridor).takeIf { it.isNotEmpty() }
}

private fun reachableNodes(
    initial: Collection<Int>,
    allowed: Set<Int>,
    isActive: () -> Boolean,
    next: (Int) -> Iterable<Int>,
): Set<Int> {
    val reached = linkedSetOf<Int>()
    val pending = ArrayDeque<Int>()
    initial.filterTo(pending) { isActive() && it in allowed }
    while (pending.isNotEmpty()) {
        if (!isActive()) return emptySet()
        val node = pending.removeFirst()
        if (!reached.add(node)) continue
        for (successor in next(node)) {
            if (!isActive()) return emptySet()
            if (successor in allowed && successor !in reached) pending.addLast(successor)
        }
    }
    return reached
}

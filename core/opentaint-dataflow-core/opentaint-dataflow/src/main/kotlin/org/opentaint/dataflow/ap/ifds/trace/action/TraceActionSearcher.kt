package org.opentaint.dataflow.ap.ifds.trace.action

import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import it.unimi.dsi.fastutil.ints.IntArrayList
import mu.KLogging
import org.opentaint.dataflow.ap.ifds.TaintAnalysisUnitRunnerManager
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.ActionVariant
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
import org.opentaint.dataflow.util.CompactIntSet
import org.opentaint.dataflow.configuration.CommonTaintAction
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSink
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSource
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.ir.api.common.cfg.CommonInst

private val logger = object : KLogging() {}.logger

private typealias Rules = Map<CommonInst, Map<CommonTaintConfigurationItem, Set<CommonTaintAction>>>

private enum class RuleResolutionSkipReason {
    UnchangedTaintMarks,
    ZeroStartCoveredByPredecessor,
}

sealed interface ActionableRulesCollectionResult {
    data object Failed : ActionableRulesCollectionResult
    data object Unprocessed : ActionableRulesCollectionResult

    data class Collected(
        val rules: Map<CommonInst, Map<CommonTaintConfigurationItem, Set<CommonTaintAction>>>,
    ) : ActionableRulesCollectionResult
}

fun TaintAnalysisUnitRunnerManager.collectActionableRules(
    vulnerability: VulnerabilityWithInterproceduralTrace,
    operationCancellation: Cancellation = cancellation,
): ActionableRulesCollectionResult {
    val trace = vulnerability.trace ?: return ActionableRulesCollectionResult.Failed
    return collectActionableRules(
        trace = trace,
        sinkStatement = vulnerability.vulnerability.statement,
        sinkRules = vulnerability.vulnerability.vulnerabilityRules.keys,
        shouldMaterializeNode = trace.sourceToSinkTrace::requiresFullTraceResolution,
        materializeNode = { node ->
            withMethodRunner(node.methodEntryPoint) {
                val resolver = methodTraceResolver(node.methodEntryPoint)
                when (node) {
                    is TraceResolver.InterProceduralStart2FinalTraceNode ->
                        resolver.resolveIntraProceduralFullStart2FinalTrace(
                            node.trace,
                            operationCancellation,
                            collapseUnchangedNodes = true,
                        )

                    is TraceResolver.InterProceduralSummaryTraceNode ->
                        resolver.resolveIntraProceduralFullStart2FinalTrace(
                            node.trace,
                            operationCancellation,
                            collapseUnchangedNodes = true,
                        )

                    is TraceResolver.InterProceduralMethodEntryNode -> emptyList()
                }
            }
        },
        materializeSummary = { summary ->
            withMethodRunner(summary.method) {
                methodTraceResolver(summary.method).resolveIntraProceduralFullStart2FinalTrace(
                    summary,
                    operationCancellation,
                    collapseUnchangedNodes = true,
                )
            }
        },
        isActive = operationCancellation::isActive,
    )
}

fun collectActionableRules(
    trace: TraceResolver.Trace,
    sinkStatement: CommonInst,
    sinkRules: Collection<CommonTaintConfigurationItem>,
    shouldMaterializeNode: (TraceResolver.InterProceduralTraceNode) -> Boolean = { true },
    materializeNode: (TraceResolver.InterProceduralTraceNode) -> List<FullStart2FinalTrace>,
    materializeSummary: (SummaryTrace) -> List<FullStart2FinalTrace>,
    isActive: () -> Boolean = { true },
): ActionableRulesCollectionResult = runCatching {
    TraceActionCollector(
        trace,
        sinkStatement,
        sinkRules,
        shouldMaterializeNode,
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

internal fun Set<TraceEntryAction.TraceSummaryEdge>.introducesOrChangesTaintMarks(): Boolean =
    any { summaryEdge ->
        when (summaryEdge) {
            is TraceEntryAction.TraceSummaryEdge.SourceSummary -> true
            is TraceEntryAction.TraceSummaryEdge.MethodSummary ->
                summaryEdge.edge.fact.taintMarks() != summaryEdge.edgeAfter.fact.taintMarks()
        }
    }

private fun InitialFactAp.taintMarks(): Set<TaintMarkAccessor> =
    getAllAccessors().filterIsInstanceTo(linkedSetOf())

private class TraceActionCollector(
    private val trace: TraceResolver.Trace,
    private val sinkStatement: CommonInst,
    sinkRules: Collection<CommonTaintConfigurationItem>,
    private val shouldMaterializeNode: (TraceResolver.InterProceduralTraceNode) -> Boolean,
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
    private val callSummaryRelevance = hashMapOf<TraceEntryAction.CallSummary, Boolean>()
    private val sharedNodeResults = hashMapOf<SummaryTrace, Evaluation>()
    private var metadataFilteredNodes = 0
    private var unchangedTaintMarkNodes = 0
    private var coveredZeroStartNodes = 0
    private var sharedNodeResolutions = 0

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
        val finalTaintMarks = graph.allNodes.map { sourceToSink.finalTaintMarks(it) }

        val nodeResults = arrayOfNulls<Evaluation>(graph.allNodes.size)
        for (nodeId in graph.allNodes.indices) {
            if (!isActive()) return ActionableRulesCollectionResult.Failed
            val seed = if (graph.sinkNodes.contains(nodeId)) sinkRuleMap() else emptyMap()
            val result = when (graph.ruleResolutionSkipReason(nodeId, finalTaintMarks, sourceToSink)) {
                RuleResolutionSkipReason.UnchangedTaintMarks -> {
                    unchangedTaintMarkNodes++
                    Evaluation.Valid(seed)
                }

                RuleResolutionSkipReason.ZeroStartCoveredByPredecessor -> {
                    coveredZeroStartNodes++
                    evaluateZeroStartWithoutFullTrace(graph.allNodes[nodeId], seed)
                }

                null -> evaluateNode(graph.allNodes[nodeId], seed)
            }
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
        logger.debug {
            "Rule search skipped $metadataFilteredNodes metadata-filtered and " +
                "$unchangedTaintMarkNodes unchanged-mark and $coveredZeroStartNodes covered-Zero " +
                "full node resolutions out of ${graph.allNodes.size}; shared $sharedNodeResolutions " +
                "identical full queries"
        }
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
        if (!shouldMaterializeNode(node)) {
            metadataFilteredNodes++
            return Evaluation.Valid(seed)
        }

        val sharedQuery = node.sharedFullTraceQuery()
        if (sharedQuery != null) {
            sharedNodeResults[sharedQuery]?.let { result ->
                sharedNodeResolutions++
                return result.withSeed(seed)
            }
        }

        val traces = materializeNode(node)
        if (traces.isEmpty()) {
            if (sharedQuery != null) sharedNodeResults[sharedQuery] = Evaluation.Invalid
            return Evaluation.Invalid
        }

        if (!isActive()) return Evaluation.Failed
        val result = evaluateResolvedTraces(traces, TraceOrigin.OuterNode, emptyMap())
        if (sharedQuery != null && result !== Evaluation.Failed) sharedNodeResults[sharedQuery] = result
        return result.withSeed(seed)
    }

    private fun TraceResolver.InterProceduralTraceNode.sharedFullTraceQuery(): SummaryTrace? = when (this) {
        is TraceResolver.InterProceduralSummaryTraceNode -> null
        is TraceResolver.InterProceduralMethodEntryNode -> null
        is TraceResolver.InterProceduralStart2FinalTraceNode -> if (trace.isStartOverApproximation) {
            SummaryTrace(trace.method, trace.final, trace.traceKind)
        } else {
            null
        }
    }

    private fun Evaluation.withSeed(seed: Rules): Evaluation {
        if (this !is Evaluation.Valid || seed.isEmpty()) return this
        val collected = RulesAccumulator()
        collected.addAll(rules)
        collected.addAll(seed)
        return Evaluation.Valid(collected.freeze())
    }

    private fun evaluateZeroStartWithoutFullTrace(
        node: TraceResolver.InterProceduralTraceNode,
        seed: Rules,
    ): Evaluation {
        val startEntry = (node as TraceResolver.InterProceduralStart2FinalTraceNode)
            .trace.startEntry as TraceEntry.SourceStartEntry
        val collected = RulesAccumulator()
        collected.addAll(seed)
        collected.addRuleActions(startEntry)
        return Evaluation.Valid(collected.freeze())
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
        val entryRules = hashMapOf<Int, Rules>()

        for ((entryId, entry) in trace.entries.withIndex()) {
            if (!isActive()) return Evaluation.Failed

            if (entry is TraceEntry.Action) {
                when (val result = evaluateActionVariants(trace, entry, entryId, origin)) {
                    is Evaluation.Valid -> entryRules[entryId] = result.rules
                    Evaluation.Invalid -> invalidEntries += entryId
                    Evaluation.Failed -> return Evaluation.Failed
                }
                continue
            }

            val summary = entry.relevantSummary(origin) ?: continue
            when (val nestedResult = evaluateSummary(summary)) {
                is Evaluation.Valid -> entryRules[entryId] = nestedResult.rules
                Evaluation.Invalid -> invalidEntries += entryId
                Evaluation.Failed -> return Evaluation.Failed
            }
        }

        val collected = RulesAccumulator()
        collected.addAll(seed)

        fun collectEntry(entryId: Int) {
            entryRules[entryId]?.let(collected::addAll)
            val entry = trace.entries[entryId]
            if (entry !is TraceEntry.Action) {
                collected.addRuleActions(entry)
            }
        }

        if (invalidEntries.isEmpty()) {
            trace.entries.indices.forEach { entryId ->
                if (!isActive()) return Evaluation.Failed
                collectEntry(entryId)
            }
            return Evaluation.Valid(collected.freeze())
        }

        val reachableEntries = trace.corridorWithout(invalidEntries, isActive)
        if (!reachableEntries.contains(trace.finalId)) return Evaluation.Invalid
        reachableEntries.forEach { entryId ->
            if (!isActive()) return Evaluation.Failed
            collectEntry(entryId)
        }

        return Evaluation.Valid(collected.freeze())
    }

    private fun evaluateActionVariants(
        trace: FullStart2FinalTrace,
        entry: TraceEntry.Action,
        entryId: Int,
        origin: TraceOrigin,
    ): Evaluation {
        val variants = trace.actionVariants.get(entryId)

        var hasValidVariant = false
        val collected = RulesAccumulator()
        for (variant in variants) {
            if (!isActive()) return Evaluation.Failed

            val summary = variant.relevantSummary(origin)
            if (summary != null) {
                when (val nestedResult = evaluateSummary(summary)) {
                    is Evaluation.Valid -> collected.addAll(nestedResult.rules)
                    Evaluation.Invalid -> continue
                    Evaluation.Failed -> return Evaluation.Failed
                }
            }

            hasValidVariant = true
            collected.addRuleActions(entry.statement, variant.otherActions)
        }

        return if (hasValidVariant) {
            Evaluation.Valid(collected.freeze())
        } else {
            Evaluation.Invalid
        }
    }

    private fun ActionVariant.relevantSummary(origin: TraceOrigin): SummaryTrace? =
        when (val action = primaryAction) {
            is TraceEntryAction.CallSourceSummary -> action.summaryTrace
            is TraceEntryAction.CallSummary -> action.summaryTrace.takeIf { summary ->
                callSummaryRelevance.getOrPut(action) {
                    action.summaryEdges.introducesOrChangesTaintMarks() && summary.shouldExpand()
                }
            }
            else -> null
        }

    private fun TraceEntry.relevantSummary(origin: TraceOrigin): SummaryTrace? = when (this) {
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
            is TraceEntry.SourceStartEntry -> entry.sourceOtherActions
            else -> emptyList()
        }
        addRuleActions(entry.statement, actions)
    }

    private fun RulesAccumulator.addRuleActions(
        statement: CommonInst,
        actions: Iterable<TraceEntryAction>,
    ) {
        actions.forEach { action ->
            when (action) {
                is TraceEntryAction.CallRuleAction -> {
                    if (action.rule is CommonTaintConfigurationSource) {
                        addAction(statement, action.rule, action.action)
                    }
                }

                is TraceEntryAction.SequentialSourceRule -> {
                    addAction(statement, action.rule, action.action)
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

private fun Source2SinkTraceGraph.ruleResolutionSkipReason(
    nodeId: Int,
    finalTaintMarks: List<Set<TaintMarkAccessor>>,
    sourceToSink: TraceResolver.SourceToSinkTrace,
): RuleResolutionSkipReason? {
    val node = allNodes[nodeId]
    val finalMarks = finalTaintMarks[nodeId]

    if (node is TraceResolver.InterProceduralMethodEntryNode) {
        return RuleResolutionSkipReason.UnchangedTaintMarks
    }

    val trace = (node as? TraceResolver.InterProceduralStart2FinalTraceNode)?.trace ?: return null
    return when (val startEntry = trace.startEntry) {
        is TraceEntry.MethodEntry -> RuleResolutionSkipReason.UnchangedTaintMarks.takeIf {
            startEntry.facts.taintMarks() == finalMarks
        }

        is TraceEntry.SourceStartEntry -> RuleResolutionSkipReason.ZeroStartCoveredByPredecessor.takeIf {
            directPredecessors(nodeId).any { predecessorId ->
                finalTaintMarks[predecessorId] == finalMarks
            }
        }
    }
}

private fun Source2SinkTraceGraph.directPredecessors(nodeId: Int): Set<Int> = buildSet {
    root2SourceBwd[nodeId]?.forEach { add(it) }
    root2SinkBwd[nodeId]?.forEach { add(it) }
}

private fun TraceResolver.SourceToSinkTrace.finalTaintMarks(
    node: TraceResolver.InterProceduralTraceNode,
): Set<TaintMarkAccessor> =
    when (node) {
        is TraceResolver.InterProceduralStart2FinalTraceNode -> node.trace.final.taintMarks()
        is TraceResolver.InterProceduralSummaryTraceNode -> node.trace.final.taintMarks()
        is TraceResolver.InterProceduralMethodEntryNode -> node.entry.facts.taintMarks()
    }

private fun TraceEntry.Final.taintMarks(): Set<TaintMarkAccessor> =
    edges.mapToTaintMarks { it.fact }

private fun Set<InitialFactAp>.taintMarks(): Set<TaintMarkAccessor> =
    mapToTaintMarks { it }

private inline fun <T> Iterable<T>.mapToTaintMarks(
    fact: (T) -> InitialFactAp,
): Set<TaintMarkAccessor> = buildSet {
    for (element in this@mapToTaintMarks) {
        addAll(fact(element).taintMarks())
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
): CompactIntSet {
    fun isAllowed(entryId: Int): Boolean =
        entryId in entries.indices && entryId !in invalidEntries

    if (!isAllowed(startEntryId) || !isAllowed(finalId) || !isActive()) return CompactIntSet()

    val reachable = reachableCompactNodes(setOf(startEntryId), ::isAllowed, isActive, successors::get)

    val predecessors = Int2ObjectOpenHashMap<CompactIntSet>()
    reachable.forEach { from ->
        if (!isActive()) return CompactIntSet()
        successors.get(from)?.forEach { to ->
            if (reachable.contains(to)) {
                predecessors.computeIfAbsent(to) { CompactIntSet() }.add(from)
            }
        }
    }
    return reachableCompactNodes(setOf(finalId), reachable::contains, isActive, predecessors::get)
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

private fun reachableCompactNodes(
    initial: Collection<Int>,
    isAllowed: (Int) -> Boolean,
    isActive: () -> Boolean,
    next: (Int) -> CompactIntSet?,
): CompactIntSet {
    val reached = CompactIntSet()
    val pending = IntArrayList()
    initial.forEach {
        if (isActive() && isAllowed(it)) pending.add(it)
    }
    while (pending.isNotEmpty()) {
        if (!isActive()) return CompactIntSet()
        val node = pending.removeInt(pending.lastIndex)
        if (reached.contains(node)) continue
        reached.add(node)
        next(node)?.forEach { successor ->
            if (!isActive()) return CompactIntSet()
            if (isAllowed(successor) && !reached.contains(successor)) pending.add(successor)
        }
    }
    return reached
}

package org.opentaint.dataflow.ap.ifds.trace

import it.unimi.dsi.fastutil.ints.Int2IntOpenHashMap
import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import it.unimi.dsi.fastutil.ints.IntArrayList
import it.unimi.dsi.fastutil.objects.Object2IntOpenHashMap
import mu.KLogging
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.AnalysisRunner
import org.opentaint.dataflow.ap.ifds.AnalysisUnitRunnerManager
import org.opentaint.dataflow.ap.ifds.Edge
import org.opentaint.dataflow.ap.ifds.Edge.FactToFact
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.MethodAnalyzerEdgeSearcher
import org.opentaint.dataflow.ap.ifds.MethodAnalyzerEdges
import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.MethodWithContext
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FactAp
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.baseonly.ABSTRACT_EMPTY_ACCESS
import org.opentaint.dataflow.ap.ifds.access.baseonly.BaseOnlyApManager
import org.opentaint.dataflow.ap.ifds.access.baseonly.BaseOnlyFinalFactAp
import org.opentaint.dataflow.ap.ifds.access.baseonly.BaseOnlyInitialFactAp
import org.opentaint.dataflow.ap.ifds.access.baseonly.eraseFieldForSummaryGeneralization
import org.opentaint.dataflow.ap.ifds.analysis.AnalysisManager
import org.opentaint.dataflow.ap.ifds.analysis.MethodAnalysisContext
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFactMapper
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallResolver.MethodCallResolutionResult
import org.opentaint.dataflow.ap.ifds.trace.MethodCallPrecondition.CallPrecondition
import org.opentaint.dataflow.ap.ifds.trace.MethodCallPrecondition.CallPreconditionFact
import org.opentaint.dataflow.ap.ifds.trace.MethodSequentPrecondition.SequentPrecondition
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.PartiallyResolvedMergedCallAction.MergedPrimaryCall2StartAction
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.PartiallyResolvedMergedCallAction.MergedPrimaryUnresolvedCallSkip
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.PartiallyResolvedMergedCallAction.MergedRuleAction
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.PartiallyResolvedMergedCallAction.PartiallyResolvedMergedPrimaryCallAction
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEntryAction.CallSummary
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEntryAction.OtherAction
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEntryAction.PrimaryAction
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEntryAction.SequentialAction
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEntryAction.SourceOtherAction
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEntryAction.TraceSummaryEdge
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEntryAction.UnresolvedCallSkip
import org.opentaint.dataflow.ap.ifds.trace.TaintRulePrecondition.PassRuleCondition
import org.opentaint.dataflow.configuration.CommonTaintAction
import org.opentaint.dataflow.configuration.CommonTaintAssignAction
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSource
import org.opentaint.dataflow.graph.MethodInstGraph
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.CompactIntSet
import org.opentaint.dataflow.util.add
import org.opentaint.dataflow.util.bitSetOf
import org.opentaint.dataflow.util.cartesianProductMapTo
import org.opentaint.dataflow.util.collectToListWithPostProcess
import org.opentaint.dataflow.util.contains
import org.opentaint.dataflow.util.forEach
import org.opentaint.dataflow.util.forEachCartesianProduct
import org.opentaint.dataflow.util.forEachIntEntry
import org.opentaint.dataflow.util.toBitSet
import org.opentaint.ir.api.common.cfg.CommonAssignInst
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.common.cfg.CommonValue
import java.util.BitSet
import java.util.LinkedList
import java.util.Objects
import java.util.concurrent.ConcurrentHashMap

internal fun MethodTraceResolver.SummaryTrace.withUniverseExclusions(): MethodTraceResolver.SummaryTrace =
    copy(
        final = final.run {
            copy(
                edges = MethodTraceResolver.TraceEdges.conjoin(
                    edges.premisesByFinalFact.values.map { premises ->
                        MethodTraceResolver.TraceEdges.of(premises.map { it.withUniverseExclusions() })
                    }
                )
            )
        }
    )

private fun MethodTraceResolver.TraceEdge.withUniverseExclusions(): MethodTraceResolver.TraceEdge = when (this) {
    is MethodTraceResolver.TraceEdge.SourceTraceEdge -> MethodTraceResolver.TraceEdge.SourceTraceEdge(
        fact.replaceExclusions(ExclusionSet.Universe)
    )

    is MethodTraceResolver.TraceEdge.MethodTraceEdge -> MethodTraceResolver.TraceEdge.MethodTraceEdge(
        initialFact.replaceExclusions(ExclusionSet.Universe),
        fact.replaceExclusions(ExclusionSet.Universe)
    )

    is MethodTraceResolver.TraceEdge.MethodTraceNDEdge -> MethodTraceResolver.TraceEdge.MethodTraceNDEdge(
        initialFacts.mapTo(hashSetOf()) { it.replaceExclusions(ExclusionSet.Universe) },
        fact.replaceExclusions(ExclusionSet.Universe)
    )
}

class MethodTraceResolver(
    private val runner: AnalysisRunner,
    private val stats: TraceResolverStats,
    private val analysisContext: MethodAnalysisContext,
    private val edges: MethodAnalyzerEdges,
    private val graph: MethodInstGraph,
    private val traceSummarizer: TraceSummarizer? = null,
    traceResolutionActionHardLimit: Int? = null,
    private val cache: Cache = Cache(),
) {
    private val methodEntryPoint: MethodEntryPoint = analysisContext.methodEntryPoint
    private val analysisManager: AnalysisManager get() = runner.analysisManager
    private val manager: AnalysisUnitRunnerManager get() = runner.manager
    private val methodCallFactMapper: MethodCallFactMapper get() = analysisContext.methodCallFactMapper
    private val apManager: ApManager get() = runner.apManager
    private val traceResolutionActionHardLimit =
        traceResolutionActionHardLimit ?: TRACE_RESOLUTION_ACTION_HARD_LIMIT

    /**
     * Query-independent data used while resolving traces for one analyzed method.
     *
     * A cache may be shared by concurrent resolvers only while the method edge storage is stable.
     * [NormalMethodAnalyzer] owns one cache generation and replaces it with the method analysis state.
     */
    class Cache internal constructor() {
        private data class CallPassSummaryKey(
            val currentEdge: TraceEdge,
            val callee: MethodEntryPoint,
            val startFact: CallPreconditionFact.CallToStart,
            val statement: CommonInst,
        )

        private val entryEdgePresence =
            ConcurrentHashMap<CommonInst, ConcurrentHashMap<TraceEdge, Boolean>>()
        private val callPassSummaries = ConcurrentHashMap<CallPassSummaryKey, List<CallSummary>>()
        private val calleeEntryPoints = ConcurrentHashMap<CommonInst, List<MethodEntryPoint>>()
        private val zeroEntryFacts =
            ConcurrentHashMap<CommonInst, ConcurrentHashMap<AccessPathBase, List<FinalFactAp>>>()

        internal fun containsEntryEdge(
            statement: CommonInst,
            edge: TraceEdge,
            compute: () -> Boolean,
        ): Boolean = entryEdgePresence
            .computeIfAbsent(statement) { ConcurrentHashMap() }
            .computeIfAbsent(edge) { compute() }

        internal fun callPassSummaries(
            currentEdge: TraceEdge,
            callee: MethodEntryPoint,
            startFact: CallPreconditionFact.CallToStart,
            statement: CommonInst,
            compute: () -> List<CallSummary>,
        ): List<CallSummary> = callPassSummaries.computeIfAbsent(
            CallPassSummaryKey(currentEdge, callee, startFact, statement)
        ) { compute().toList() }

        internal fun calleeEntryPoints(
            statement: CommonInst,
            compute: () -> List<MethodEntryPoint>,
        ): List<MethodEntryPoint> = calleeEntryPoints.computeIfAbsent(statement) { compute().toList() }

        internal fun zeroEntryFacts(
            statement: CommonInst,
            base: AccessPathBase,
            compute: () -> List<FinalFactAp>,
        ): List<FinalFactAp> = zeroEntryFacts
            .computeIfAbsent(statement) { ConcurrentHashMap() }
            .computeIfAbsent(base) { compute().toList() }
    }
    // Enum can give non-determinacy as its entries have new hash code on every JVM run.
    // Override hashcode() and equals() when using enum as a field in classes whose objects
    // can be stored in sets etc.
    enum class TraceKind {
        TraceToFact, // Trace ends within the method
        TraceToFactAfterStatement, // Trace ends within the method, but the fact is after the statement
        SummaryTrace, // Trace summarizes method behaviour
    }

    data class FullStart2FinalTrace(
        val method: MethodEntryPoint,
        val entries: Array<TraceEntry>,
        val actionVariants: Int2ObjectOpenHashMap<List<ActionVariant>>,
        val startEntryId: Int,
        val finalId: Int,
        val successors: Int2ObjectOpenHashMap<CompactIntSet>,
        val traceKind: TraceKind,
    ) {
        val startEntry: TraceEntry.StartTraceEntry get() = entries[startEntryId] as TraceEntry.StartTraceEntry
        val final: TraceEntry.Final get() = entries[finalId] as TraceEntry.Final

        override fun hashCode(): Int = Objects.hash(method, final)

        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (other !is FullStart2FinalTrace) return false

            // note: FullTrace is uniquely defined by its start end final entries
            if (method != other.method) return false
            if (traceKind != other.traceKind) return false
            if (final != other.final) return false
            return startEntry == other.startEntry
        }
    }

    data class Start2FinalTrace(
        val method: MethodEntryPoint,
        val startEntry: TraceEntry.StartTraceEntry,
        val final: TraceEntry.Final,
        val traceKind: TraceKind,
        val isStartOverApproximation: Boolean = false,
    )

    @Suppress("EqualsOrHashCode")
    data class SummaryTrace(
        val method: MethodEntryPoint,
        val final: TraceEntry.Final,
        val traceKind: TraceKind,
    ) {
        override fun hashCode(): Int {
            var result = method.hashCode()
            result = 31 * result + final.hashCode()
            result = 31 * result + traceKind.ordinal.hashCode()
            return result
        }
    }

    sealed interface TraceEdge {
        val fact: InitialFactAp

        fun replaceFact(newFact: InitialFactAp): TraceEdge

        data class SourceTraceEdge(override val fact: InitialFactAp) : TraceEdge {
            override fun replaceFact(newFact: InitialFactAp): SourceTraceEdge = copy(fact = newFact)
        }

        data class MethodTraceEdge(val initialFact: InitialFactAp, override val fact: InitialFactAp) : TraceEdge {
            override fun replaceFact(newFact: InitialFactAp): MethodTraceEdge = copy(fact = newFact)
        }

        data class MethodTraceNDEdge(val initialFacts: Set<InitialFactAp>, override val fact: InitialFactAp) : TraceEdge {
            override fun replaceFact(newFact: InitialFactAp): MethodTraceNDEdge = copy(fact = newFact)
        }
    }

    /**
     * A conjunction of requested final facts. Premises for the same final fact are alternatives;
     * groups belonging to different final facts are conjunctive requirements.
     */
    class TraceEdges private constructor(
        val premisesByFinalFact: Map<InitialFactAp, Set<TraceEdge>>,
        private val flattened: Set<TraceEdge>,
    ) : Set<TraceEdge> by flattened {
        private val cachedHashCode = flattened.hashCode()

        init {
            check(premisesByFinalFact.isNotEmpty() || flattened.isEmpty())
            check(premisesByFinalFact.values.all { it.isNotEmpty() })
            check(premisesByFinalFact.all { (fact, premises) -> premises.all { it.fact == fact } })
            check(flattened == premisesByFinalFact.values.flatten().toSet())
        }

        override fun equals(other: Any?): Boolean =
            this === other || other is Set<*> && flattened == other

        override fun hashCode(): Int = cachedHashCode

        override fun toString(): String = premisesByFinalFact.toString()

        fun conjoin(other: TraceEdges): TraceEdges = conjoin(listOf(this, other))

        fun collapseToFact(fact: InitialFactAp): TraceEdges {
            if (premisesByFinalFact.size <= 1) return of(map { it.replaceFact(fact) })

            val collapsedPremises = linkedSetOf<TraceEdge>()
            val clauses = premisesByFinalFact.values.map { it.toList() }
            clauses.forEachCartesianProduct { selectedPremises ->
                val initialFacts = selectedPremises.flatMapTo(linkedSetOf()) { premise ->
                    when (premise) {
                        is TraceEdge.SourceTraceEdge -> emptySet()
                        is TraceEdge.MethodTraceEdge -> setOf(premise.initialFact)
                        is TraceEdge.MethodTraceNDEdge -> premise.initialFacts
                    }
                }
                collapsedPremises += when (initialFacts.size) {
                    0 -> TraceEdge.SourceTraceEdge(fact)
                    1 -> TraceEdge.MethodTraceEdge(initialFacts.single(), fact)
                    else -> TraceEdge.MethodTraceNDEdge(initialFacts, fact)
                }
            }
            return of(collapsedPremises)
        }

        companion object {
            val Empty = TraceEdges(emptyMap(), emptySet())

            fun of(edges: Iterable<TraceEdge>): TraceEdges {
                val grouped = edges.groupByTo(linkedMapOf(), TraceEdge::fact) { it }
                    .mapValuesTo(linkedMapOf()) { (fact, premises) ->
                        premises.mapTo(linkedSetOf()) { it.canonicalize(fact) }
                    }
                if (grouped.isEmpty()) return Empty
                val flattened = grouped.values.flatMapTo(linkedSetOf()) { it }
                return TraceEdges(grouped, flattened)
            }

            fun conjoin(requirements: Iterable<TraceEdges>): TraceEdges {
                val result = linkedMapOf<InitialFactAp, MutableSet<TraceEdge>>()
                for (requirement in requirements) {
                    for ((fact, premises) in requirement.premisesByFinalFact) {
                        result.getOrPut(fact, ::linkedSetOf).addAll(premises)
                    }
                }
                return of(result.values.flatten())
            }

            private fun TraceEdge.canonicalize(fact: InitialFactAp): TraceEdge = when (this) {
                is TraceEdge.SourceTraceEdge -> TraceEdge.SourceTraceEdge(fact)
                is TraceEdge.MethodTraceEdge -> TraceEdge.MethodTraceEdge(initialFact, fact)
                is TraceEdge.MethodTraceNDEdge -> when (initialFacts.size) {
                    0 -> TraceEdge.SourceTraceEdge(fact)
                    1 -> TraceEdge.MethodTraceEdge(initialFacts.single(), fact)
                    else -> TraceEdge.MethodTraceNDEdge(initialFacts, fact)
                }
            }
        }
    }

    sealed interface TraceEntryAction {
        sealed interface PrimaryAction : TraceEntryAction

        sealed interface OtherAction : TraceEntryAction

        sealed interface CallAction : TraceEntryAction

        sealed interface CallRuleAction : CallAction {
            val rule: CommonTaintConfigurationItem
            val action: Set<CommonTaintAction>
        }

        sealed interface PassAction : TraceEntryAction {
            val edges: TraceEdges
            val edgesAfter: TraceEdges
        }

        sealed interface SourceAction : TraceEntryAction {
            val sourceEdges: Set<TraceEdge.SourceTraceEdge>
        }

        sealed interface SourcePrimaryAction : SourceAction, PrimaryAction

        sealed interface SourceOtherAction : SourceAction, OtherAction

        sealed interface SequentialAction: TraceEntryAction

        data class Sequential(
            override val edges: TraceEdges,
            override val edgesAfter: TraceEdges,
        ) : SequentialAction, PrimaryAction, PassAction {
            constructor(edges: Set<TraceEdge>, edgesAfter: Set<TraceEdge>) :
                this(TraceEdges.of(edges), TraceEdges.of(edgesAfter))
        }

        data class SequentialSourceRule(
            override val sourceEdges: Set<TraceEdge.SourceTraceEdge>,
            val rule: CommonTaintConfigurationSource,
            val action: Set<CommonTaintAssignAction>,
        ) : SequentialAction, SourceOtherAction

        data class CallSourceRule(
            override val sourceEdges: Set<TraceEdge.SourceTraceEdge>,
            override val rule: CommonTaintConfigurationSource,
            override val action: Set<CommonTaintAssignAction>
        ) : SourceOtherAction, CallRuleAction

        data class EntryPointSourceRule(
            override val sourceEdges: Set<TraceEdge.SourceTraceEdge>,
            val entryPoint: MethodEntryPoint,
            override val rule: CommonTaintConfigurationSource,
            override val action: Set<CommonTaintAssignAction>
        ) : SourceOtherAction, CallRuleAction

        data class CallRule(
            override val edges: TraceEdges,
            override val edgesAfter: TraceEdges,
            override val rule: CommonTaintConfigurationItem,
            override val action: Set<CommonTaintAction>
        ) :  CallRuleAction, OtherAction, PassAction {
            constructor(
                edges: Set<TraceEdge>,
                edgesAfter: Set<TraceEdge>,
                rule: CommonTaintConfigurationItem,
                action: Set<CommonTaintAction>,
            ) : this(TraceEdges.of(edges), TraceEdges.of(edgesAfter), rule, action)
        }

        sealed interface TraceSummaryEdge {
            val edge: TraceEdge
            val edgeAfter: TraceEdge

            data class SourceSummary(
                override val edge: TraceEdge.SourceTraceEdge,
                override val edgeAfter: TraceEdge,
            ) : TraceSummaryEdge

            data class MethodSummary(
                override val edge: TraceEdge,
                override val edgeAfter: TraceEdge,
                val delta: TraceSummaryDelta?,
            ) : TraceSummaryEdge

            data class TraceSummaryDelta(
                val initialFact: InitialFactAp,
                val delta: InitialFactAp.Delta,
            )
        }

        data class CallSummary(
            val summaryEdges: Set<TraceSummaryEdge>,
            val summaryTrace: SummaryTrace,
            override val edges: TraceEdges = TraceEdges.conjoin(
                summaryEdges.map { TraceEdges.of(listOf(it.edge)) }
            ),
            override val edgesAfter: TraceEdges = TraceEdges.conjoin(
                summaryEdges.map { TraceEdges.of(listOf(it.edgeAfter)) }
            ),
        ) : CallAction, PrimaryAction, PassAction

        data class CallSourceSummary(
            val summaryEdges: Set<TraceSummaryEdge.SourceSummary>,
            val summaryTrace: SummaryTrace,
        ) : CallAction, SourcePrimaryAction {
            override val sourceEdges: Set<TraceEdge.SourceTraceEdge>
                get() = summaryEdges.mapTo(hashSetOf()) { it.edge }
        }

        data class UnresolvedCallSkip(
            override val edges: TraceEdges,
            override val edgesAfter: TraceEdges,
        ) : CallAction, PrimaryAction, PassAction {
            constructor(edges: Set<TraceEdge>, edgesAfter: Set<TraceEdge>) :
                this(TraceEdges.of(edges), TraceEdges.of(edgesAfter))
        }
    }

    data class ActionVariant(
        val primaryAction: PrimaryAction?,
        val otherActions: Set<OtherAction>,
        val unchanged: TraceEdges,
    ) {
        constructor(
            primaryAction: PrimaryAction?,
            otherActions: Set<OtherAction>,
            unchanged: Set<TraceEdge>,
        ) : this(primaryAction, otherActions, TraceEdges.of(unchanged))

        init {
            check(primaryAction != null || otherActions.isNotEmpty()) {
                "Entry is unchanged"
            }
        }

        val edges: TraceEdges = TraceEdges.conjoin(buildList {
            add(unchanged)
            if (primaryAction is TraceEntryAction.PassAction) add(primaryAction.edges)
            otherActions.filterIsInstance<TraceEntryAction.PassAction>().forEach { add(it.edges) }
        })

        private val cachedHashCode: Int = run {
            var result = primaryAction?.hashCode() ?: 0
            result = 31 * result + otherActions.hashCode()
            result = 31 * result + unchanged.hashCode()
            result
        }

        override fun hashCode(): Int = cachedHashCode

        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (other !is ActionVariant) return false

            if (cachedHashCode != other.cachedHashCode) return false
            if (primaryAction != other.primaryAction) return false
            if (otherActions != other.otherActions) return false
            if (unchanged != other.unchanged) return false

            return true
        }
    }

    sealed interface TraceEntry {
        val edges: TraceEdges
        val statement: CommonInst

        data class Action(
            override val edges: TraceEdges,
            override val statement: CommonInst,
        ) : TraceEntry {
            constructor(edges: Set<TraceEdge>, statement: CommonInst) : this(TraceEdges.of(edges), statement)
        }

        data class Unchanged(
            override val edges: TraceEdges,
            override val statement: CommonInst,
        ) : TraceEntry {
            constructor(edges: Set<TraceEdge>, statement: CommonInst) : this(TraceEdges.of(edges), statement)
        }

        data class Final(
            override val edges: TraceEdges,
            override val statement: CommonInst
        ) : TraceEntry {
            constructor(edges: Set<TraceEdge>, statement: CommonInst) : this(TraceEdges.of(edges), statement)
        }

        sealed interface StartTraceEntry: TraceEntry

        data class MethodEntry(
            val facts: Set<InitialFactAp>,
            val entryPoint: MethodEntryPoint,
        ) : StartTraceEntry {
            override val edges: TraceEdges get() = TraceEdges.of(facts.mapTo(hashSetOf()) {
                TraceEdge.MethodTraceEdge(it, it)
            })

            override val statement: CommonInst
                get() = entryPoint.statement
        }

        data class SourceStartEntry(
            val sourcePrimaryAction: TraceEntryAction.SourcePrimaryAction?,
            val sourceOtherActions: Set<SourceOtherAction>,
            override val statement: CommonInst,
        ) : StartTraceEntry {
            override val edges: TraceEdges get() = TraceEdges.of(buildSet {
                sourcePrimaryAction?.let { addAll(it.sourceEdges) }
                sourceOtherActions.forEach { addAll(it.sourceEdges) }
            })
        }
    }

    internal class EntryManager(
        private val traceSummarizer: TraceSummarizer?,
    ) {
        val entries = arrayListOf<TraceEntry>()
        private val entryId = Object2IntOpenHashMap<TraceEntry>().apply { defaultReturnValue(NO_ENTRY) }

        fun entryId(entry: TraceEntry): Int {
            val currentId = entryId.getInt(entry)
            if (currentId != NO_ENTRY) return currentId

            val id = entries.size
            entries.add(entry)
            entryId.put(entry, id)
            traceSummarizer?.summarizeTraceEntry(entry)

            return id
        }

        fun entryById(id: Int): TraceEntry = entries[id]

        companion object {
            private const val NO_ENTRY = -1
        }
    }

    private class TraceBuilder(
        finalEntry: TraceEntry.Final,
        val cancellation: Cancellation,
        private val collectActionVariants: Boolean,
        traceSummarizer: TraceSummarizer?,
    ) {
        val entryManager = EntryManager(traceSummarizer)
        val finalEntryId: Int = entryManager.entryId(finalEntry)
        val finalHasAlternativePremises = finalEntry.edges.premisesByFinalFact.values.any { it.size > 1 }
        val startEntryIds = BitSet()
        var processedEntryIds = CompactIntSet().also { it.add(finalEntryId) }
        val unprocessedEntryIds = IntArrayList().also { it.add(finalEntryId) }
        val predecessors = Int2ObjectOpenHashMap<CompactIntSet>()
        val successors = Int2ObjectOpenHashMap<CompactIntSet>()

        var steps = 0
        var actionHardLimitReached = false

        fun addPredecessor(current: TraceEntry, predecessor: TraceEntry, enqueue: Boolean = true) {
            val currentId = entryManager.entryId(current)
            val predecessorId = entryManager.entryId(predecessor)

            var currentPredecessors = predecessors.get(currentId)
            if (currentPredecessors == null) {
                currentPredecessors = CompactIntSet().also { predecessors.put(currentId, it) }
            }
            currentPredecessors.add(predecessorId)

            var currentSuccessors = successors.get(predecessorId)
            if (currentSuccessors == null) {
                currentSuccessors = CompactIntSet().also { successors.put(predecessorId, it) }
            }
            currentSuccessors.add(currentId)

            if (!processedEntryIds.contains(predecessorId)) {
                processedEntryIds.add(predecessorId)

                if (enqueue) {
                    unprocessedEntryIds.add(predecessorId)
                }
            }
        }

        fun addStartEntry(entry: TraceEntry) {
            startEntryIds.add(entryManager.entryId(entry))
        }

        private val actionVariants = Int2ObjectOpenHashMap<MutableSet<ActionVariant>>()

        fun unsafeActionVariants() = actionVariants

        fun createAction(
            statement: CommonInst,
            edges: TraceEdges,
            variants: Set<ActionVariant>,
        ): TraceEntry {
            val action = TraceEntry.Action(edges, statement)

            if (!collectActionVariants) {
                return action
            }

            val actionId = entryManager.entryId(action)
            actionVariants.computeIfAbsent(actionId) { hashSetOf() }.addAll(variants)

            return action
        }

        fun actions(): Int = actionVariants.size
    }

    fun resolveIntraProceduralTrace(
        statement: CommonInst,
        facts: Set<InitialFactAp>,
        includeStatement: Boolean = false,
    ): List<SummaryTrace> {
        val edges = facts.map { resolveIntraProceduralTraceEdge(statement, it, includeStatement) }
        return edges.traceToFactSummaryEdges(statement, includeStatement)
    }

    fun resolveIntraProceduralTraceFromCall(
        statement: CommonInst,
        calleeEntry: TraceEntry.MethodEntry
    ): List<SummaryTrace> {
        val traceEdges = calleeEntry.facts.flatMap { fact ->
            val mappedFacts = methodCallFactMapper.mapMethodExitToReturnFlowFact(statement, fact)
            mappedFacts.map { resolveIntraProceduralTraceEdge(statement, it, includeStatement = false) }
        }

        return traceEdges.traceToFactSummaryEdges(statement, includeStatement = false)
    }

    private fun List<List<TraceEdge>>.traceToFactSummaryEdges(
        statement: CommonInst,
        includeStatement: Boolean
    ): List<SummaryTrace> {
        val traceKind = if (includeStatement) TraceKind.TraceToFactAfterStatement else TraceKind.TraceToFact
        if (any { it.isEmpty() }) return emptyList()

        if (apManager !is BaseOnlyApManager) {
            val result = mutableListOf<SummaryTrace>()
            cartesianProductMapTo { selectedPremises ->
                result += SummaryTrace(
                    methodEntryPoint,
                    TraceEntry.Final(selectedPremises.toHashSet(), statement),
                    traceKind,
                )
            }
            return result
        }

        val finalEntry = TraceEntry.Final(
            TraceEdges.conjoin(map { TraceEdges.of(it) }),
            statement,
        )
        return listOf(SummaryTrace(methodEntryPoint, finalEntry, traceKind))
    }

    private fun resolveIntraProceduralTraceEdge(
        statement: CommonInst,
        fact: InitialFactAp,
        includeStatement: Boolean
    ): List<TraceEdge> {
        val searcher = object : MethodAnalyzerEdgeSearcher(edges, apManager, analysisManager, analysisContext, graph) {
            override fun matchFact(factAtStatement: FinalFactAp, targetFactPattern: InitialFactAp): Boolean =
                factAtStatement.contains(targetFactPattern)
        }

        val universeFact = fact.replaceExclusions(ExclusionSet.Universe)
        val matchingInitialFacts = searcher.searchInitialFacts(statement, universeFact, includeStatement)

        return matchingInitialFacts.map { initialFacts ->
            val universeInitial = initialFacts.mapTo(hashSetOf()) { it.replaceExclusions(ExclusionSet.Universe) }

            when (universeInitial.size) {
                0 -> TraceEdge.SourceTraceEdge(universeFact)
                1 -> TraceEdge.MethodTraceEdge(universeInitial.first(), universeFact)
                else -> TraceEdge.MethodTraceNDEdge(universeInitial, universeFact)
            }
        }
    }

    private fun MethodAnalyzerEdgeSearcher.searchInitialFacts(
        statement: CommonInst,
        fact: InitialFactAp,
        includeStatement: Boolean,
    ): Set<Set<InitialFactAp>> {
        if (!includeStatement) {
            return findMatchingEdgesInitialFacts(statement, fact)
        }

        val statementCall = analysisManager.getCallExpr(statement)
        if (statementCall != null) {
            // todo
            return emptySet()
        } else {
            val preconditionFunction = analysisManager.getMethodSequentPrecondition(
                apManager, analysisContext, statement
            )
            val preconditions = preconditionFunction.factPrecondition(fact)
            val result = hashSetOf<Set<InitialFactAp>>()

            for (precondition in preconditions) {
                when (precondition) {
                    is SequentPrecondition.Unchanged -> {
                        result += findMatchingEdgesInitialFacts(statement, fact)
                    }

                    is MethodSequentPrecondition.SequentSource -> {
                        // todo
                    }

                    is MethodSequentPrecondition.PreconditionFactsForInitialFact -> {
                        precondition.preconditionFacts.forEach {
                            result += findMatchingEdgesInitialFacts(statement, it)
                        }
                    }
                }
            }

            return result
        }
    }

    /**
     * Resolves only the information needed to connect an inter-procedural summary to a method start.
     *
     * A summary with a non-Zero premise already carries its method-entry facts, so reconstructing the
     * intra-procedural path cannot add information to [Start2FinalTrace]. This also covers mixed
     * summaries: their Zero premises are produced inside the method while their non-Zero premises
     * determine the method start. For an all-Zero summary, the resolver walks the CFG forward and
     * stops each path at its first Z2F edge carrying the requested mark. Backward resolution then
     * starts at that frontier instead of at the summary final. The exact resolver remains the
     * completeness fallback for summaries for which the frontier cannot produce a source start.
     */
    fun resolveIntraProceduralOverApproximateStart2FinalTrace(
        summaryTrace: SummaryTrace,
        cancellation: Cancellation,
    ): List<Start2FinalTrace> {
        val st = summaryTrace.withUniverseExclusions()
        check(st.method == methodEntryPoint) { "Incorrect summary trace" }

        if (st.final.edges.premisesByFinalFact.values.any { it.size > 1 }) {
            return resolveIntraProceduralStart2FinalTrace(st, cancellation)
        }

        val premises = st.final.summaryPremises()
        if (premises.nonZeroFacts.isNotEmpty()) {
            val methodEntryFacts = premises.nonZeroFacts
            val start = TraceEntry.MethodEntry(methodEntryFacts, methodEntryPoint)
            return listOf(
                Start2FinalTrace(
                    methodEntryPoint,
                    start,
                    st.final,
                    st.traceKind,
                    isStartOverApproximation = true,
                )
            )
        }
        if (!premises.hasZero) {
            return resolveIntraProceduralStart2FinalTrace(st, cancellation)
        }

        val requestedFactsByMark = st.final.edges
            .filterIsInstance<TraceEdge.SourceTraceEdge>()
            .flatMap { edge -> edge.fact.taintMarks().map { mark -> mark to edge.fact } }
            .groupBy({ it.first }, { it.second })

        if (requestedFactsByMark.isEmpty()) {
            return resolveIntraProceduralStart2FinalTrace(st, cancellation)
        }

        val starts = hashSetOf<TraceEntry.SourceStartEntry>()
        for ((mark, requestedFacts) in requestedFactsByMark) {
            val origins = findFirstZeroFactOrigins(mark, cancellation)
            val originQueries = buildSet {
                for (origin in origins) {
                    origin.rebaseRequestedFacts(requestedFacts).forEach { pattern ->
                        add(origin.statement to pattern)
                    }
                }
            }
            for ((originStatement, originPattern) in originQueries) {
                val originTrace = SummaryTrace(
                    method = methodEntryPoint,
                    final = TraceEntry.Final(
                        edges = setOf(TraceEdge.SourceTraceEdge(originPattern)),
                        statement = originStatement,
                    ),
                    traceKind = TraceKind.TraceToFactAfterStatement,
                )

                val prefixTraces = resolveIntraProceduralStart2FinalTrace(originTrace, cancellation)
                prefixTraces.mapNotNullTo(starts) { it.startEntry as? TraceEntry.SourceStartEntry }
            }
        }

        if (starts.isEmpty()) {
            return resolveIntraProceduralStart2FinalTrace(st, cancellation)
        }

        return starts.map { start ->
            Start2FinalTrace(
                methodEntryPoint,
                start,
                st.final,
                st.traceKind,
                isStartOverApproximation = true,
            )
        }
    }

    private data class SummaryPremises(
        val hasZero: Boolean,
        val nonZeroFacts: Set<InitialFactAp>,
    )

    private fun TraceEntry.Final.summaryPremises(): SummaryPremises {
        var hasZero = false
        val nonZeroFacts = hashSetOf<InitialFactAp>()
        for (edge in edges) {
            when (edge) {
                is TraceEdge.SourceTraceEdge -> hasZero = true
                is TraceEdge.MethodTraceEdge -> nonZeroFacts += edge.initialFact
                is TraceEdge.MethodTraceNDEdge -> nonZeroFacts += edge.initialFacts
            }
        }
        return SummaryPremises(hasZero, nonZeroFacts)
    }

    private data class ZeroFactOrigin(
        val statement: CommonInst,
        val fact: FinalFactAp,
    )

    private fun findFirstZeroFactOrigins(
        mark: TaintMarkAccessor,
        cancellation: Cancellation,
    ): List<ZeroFactOrigin> {
        val result = arrayListOf<ZeroFactOrigin>()
        val visited = BitSet(graph.instructions.size)
        val unprocessed = IntArrayList()
        unprocessed.add(analysisManager.getInstIndex(methodEntryPoint.statement))

        while (unprocessed.isNotEmpty() && cancellation.isActive()) {
            val statementIdx = unprocessed.removeInt(unprocessed.lastIndex)
            if (!visited.add(statementIdx)) continue

            val statement = graph.instructions[statementIdx]
            val matchingFacts = edges.allZeroToFactFactsAtStatement(statement)
                .filter { mark in it.taintMarks() }
            if (matchingFacts.isNotEmpty()) {
                matchingFacts.forEach { result += ZeroFactOrigin(statement, it) }
                continue
            }

            graph.graph.forEachSuccessor(statementIdx) { successor ->
                if (!visited.get(successor)) unprocessed.add(successor)
            }
        }

        return result
    }

    private fun ZeroFactOrigin.rebaseRequestedFacts(
        requestedFacts: List<InitialFactAp>,
    ): Set<InitialFactAp> = requestedFacts.mapTo(hashSetOf()) { requested ->
        requested.rebase(fact.base).replaceExclusions(ExclusionSet.Universe)
    }

    private fun FactAp.taintMarks(): Set<TaintMarkAccessor> =
        getAllAccessors().filterIsInstanceTo(hashSetOf())

    fun resolveIntraProceduralStart2FinalTrace(
        summaryTrace: SummaryTrace,
        cancellation: Cancellation,
    ): List<Start2FinalTrace> {
        val st = summaryTrace.withUniverseExclusions()
        check(st.method == methodEntryPoint) { "Incorrect summary trace" }

        val builder = TraceBuilder(
            st.final,
            cancellation,
            collectActionVariants = false,
            traceSummarizer = traceSummarizer,
        )
        builder.resolveTrace(st.traceKind)
        stats.traceResolverSteps += builder.steps
        if (!cancellation.isActive()) return emptyList()

        if (builder.actionHardLimitReached && st.final.edges.hasAlternativePremises()) {
            return st.resolveExactCubes(cancellation::isActive) { cube ->
                resolveIntraProceduralStart2FinalTrace(cube, cancellation)
            }
        }

        val traces = mutableListOf<Start2FinalTrace>()
        builder.startEntryIds.forEach { startEntryId ->
            val startEntry = builder.entryManager.entryById(startEntryId) as TraceEntry.StartTraceEntry
            traces += Start2FinalTrace(methodEntryPoint, startEntry, st.final, st.traceKind)
        }
        return traces
    }

    fun resolveIntraProceduralFullStart2FinalTrace(
        summaryTrace: SummaryTrace,
        cancellation: Cancellation,
        collapseUnchangedNodes: Boolean
    ): List<FullStart2FinalTrace> {
        val st = summaryTrace.withUniverseExclusions()
        check(st.method == methodEntryPoint) { "Incorrect summary trace" }

        val builder = TraceBuilder(
            st.final,
            cancellation,
            collectActionVariants = true,
            traceSummarizer = traceSummarizer,
        )
        builder.resolveTrace(st.traceKind)
        stats.traceResolverSteps += builder.steps
        if (!cancellation.isActive()) return emptyList()

        if (builder.actionHardLimitReached && st.final.edges.hasAlternativePremises()) {
            return st.resolveExactCubes(cancellation::isActive) { cube ->
                resolveIntraProceduralFullStart2FinalTrace(
                    cube,
                    cancellation,
                    collapseUnchangedNodes,
                )
            }
        }

        builder.removeUnreachableNodes()
        if (!cancellation.isActive()) return emptyList()
        if (collapseUnchangedNodes) {
            builder.collapseUnchangedNodes()
        }
        if (!cancellation.isActive()) return emptyList()
        val fullTrace = builder.fullTrace(st.traceKind)
        return fullTrace
    }

    fun resolveIntraProceduralFullStart2FinalTrace(
        start2FinalTrace: Start2FinalTrace,
        cancellation: Cancellation,
        collapseUnchangedNodes: Boolean
    ): List<FullStart2FinalTrace> {
        check(start2FinalTrace.method == methodEntryPoint) { "Incorrect summary trace" }

        val builder = TraceBuilder(
            start2FinalTrace.final,
            cancellation,
            collectActionVariants = true,
            traceSummarizer = traceSummarizer,
        )
        builder.resolveTrace(start2FinalTrace.traceKind)
        stats.traceResolverSteps += builder.steps
        if (!cancellation.isActive()) return emptyList()

        if (builder.actionHardLimitReached && start2FinalTrace.final.edges.hasAlternativePremises()) {
            return start2FinalTrace.resolveExactFullCubes(
                cancellation,
                collapseUnchangedNodes,
            )
        }

        if (!start2FinalTrace.isStartOverApproximation) {
            val requiredStartId = builder.entryManager.entryId(start2FinalTrace.startEntry)
            if (!builder.startEntryIds.contains(requiredStartId)) {
                logger.warn("Trace start entry to found for: $methodEntryPoint")
                return emptyList()
            }

            builder.startEntryIds.clear()
            builder.startEntryIds.set(requiredStartId)
        }

        builder.removeUnreachableNodes()
        if (!cancellation.isActive()) return emptyList()
        if (collapseUnchangedNodes) {
            builder.collapseUnchangedNodes()
        }
        if (!cancellation.isActive()) return emptyList()
        val fullTrace = builder.fullTrace(start2FinalTrace.traceKind)
        return fullTrace
    }

    private fun Start2FinalTrace.resolveExactFullCubes(
        cancellation: Cancellation,
        collapseUnchangedNodes: Boolean,
    ): List<FullStart2FinalTrace> {
        val result = mutableListOf<FullStart2FinalTrace>()
        final.forEachExactCube { cube ->
            if (!cancellation.isActive()) return result
            val cubeTrace = SummaryTrace(method, cube, traceKind)
            val resolved = resolveIntraProceduralFullStart2FinalTrace(
                cubeTrace,
                cancellation,
                collapseUnchangedNodes,
            )
            if (isStartOverApproximation) {
                result += resolved
            } else {
                resolved.filterTo(result) { it.startEntry == startEntry }
            }
        }
        return result
    }

    private fun TraceEdges.hasAlternativePremises(): Boolean =
        premisesByFinalFact.values.any { it.size > 1 }

    private inline fun <T> SummaryTrace.resolveExactCubes(
        isActive: () -> Boolean,
        resolve: (SummaryTrace) -> List<T>,
    ): List<T> {
        val result = mutableListOf<T>()
        final.forEachExactCube {
            if (!isActive()) return result
            result += resolve(copy(final = it))
        }
        return result
    }

    private inline fun TraceEntry.Final.forEachExactCube(body: (TraceEntry.Final) -> Unit) {
        val clauses = edges.premisesByFinalFact.values.map { it.toList() }
        clauses.forEachCartesianProduct { selectedPremises ->
            body(copy(edges = TraceEdges.of(selectedPremises.asIterable())))
        }
    }

    private fun TraceBuilder.removeUnreachableNodes() {
        val reachableFromStart = BitSet()
        val reachableFromFinish = BitSet()

        traverseReachableNodes(reachableFromStart, startEntryIds) { successors.get(it) ?: CompactIntSet() }
        traverseReachableNodes(reachableFromFinish, bitSetOf(finalEntryId)) { predecessors.get(it) ?: CompactIntSet() }

        val reachableNodes = reachableFromStart
        reachableNodes.and(reachableFromFinish)

        val unreachableNodes = successors.keys.toBitSet()
        unreachableNodes.andNot(reachableNodes)

        unreachableNodes.forEach { unreachableEntry ->
            removeUnreachableEntry(unreachableEntry)
        }
    }

    private fun TraceBuilder.removeUnreachableEntry(entryId: Int) {
        val entryPredecessorIds = predecessors.remove(entryId) ?: CompactIntSet()
        val entrySuccessorIds = successors.remove(entryId) ?: CompactIntSet()
        entryPredecessorIds.remove(entryId)
        entrySuccessorIds.remove(entryId)

        entryPredecessorIds.forEach { predecessorId: Int ->
            successors.get(predecessorId)?.remove(entryId)
        }

        entrySuccessorIds.forEach { successorId: Int ->
            predecessors.get(successorId)?.remove(entryId)
        }
    }

    private inline fun TraceBuilder.traverseReachableNodes(reachable: BitSet, initial: BitSet, next: (Int) -> CompactIntSet) {
        initial.forEach { unprocessedEntryIds.add(it) }

        while (unprocessedEntryIds.isNotEmpty() && cancellation.isActive()) {
            steps++

            val entryId = unprocessedEntryIds.removeInt(unprocessedEntryIds.lastIndex)

            if (!reachable.add(entryId)) continue

            next(entryId).forEach { unprocessedEntryIds.add(it) }
        }
    }

    private fun TraceBuilder.collapseUnchangedNodes() {
        processedEntryIds = CompactIntSet()
        unprocessedEntryIds.add(finalEntryId)

        while (unprocessedEntryIds.isNotEmpty() && cancellation.isActive()) {
            val entryId = unprocessedEntryIds.removeInt(unprocessedEntryIds.lastIndex)

            if (processedEntryIds.contains(entryId)) continue
            processedEntryIds.add(entryId)

            if (startEntryIds.get(entryId)) continue

            val entryPredecessorIds = predecessors.get(entryId) ?: continue

            val entry = entryManager.entryById(entryId)
            if (entry is TraceEntry.Unchanged) {
                predecessors.remove(entryId)
                entryPredecessorIds.remove(entryId)

                val entrySuccessorIds = successors.remove(entryId) ?: CompactIntSet()
                entrySuccessorIds.remove(entryId)

                entryPredecessorIds.forEach { predecessorId: Int ->
                    val predSuccessors = successors.get(predecessorId)
                    predSuccessors?.remove(entryId)
                    predSuccessors?.addAll(entrySuccessorIds)
                }

                entrySuccessorIds.forEach { successorId: Int ->
                    val succPredecessors = predecessors.get(successorId)
                    succPredecessors?.remove(entryId)
                    succPredecessors?.addAll(entryPredecessorIds)
                }
            }

            entryPredecessorIds.forEach { predecessorId: Int ->
                unprocessedEntryIds.add(predecessorId)
            }
        }
    }

    private class EntryMapper(val manager: EntryManager) {
        val mapping = Int2IntOpenHashMap()
        val entries = mutableListOf<TraceEntry>()

        fun isTranslated(id: Int): Boolean = mapping.containsKey(id)

        fun translate(id: Int): Int = mapping.computeIfAbsent(id) {
            val entry = manager.entryById(id)
            val idx = entries.size
            entries.add(entry)
            idx
        }
    }

    private fun TraceBuilder.fullTrace(traceKind: TraceKind): List<FullStart2FinalTrace> {
        val allSuccessors = successors()
        if (!cancellation.isActive()) return emptyList()

        val result = mutableListOf<FullStart2FinalTrace>()
        startEntryIds.forEach { entryId: Int ->
            if (!cancellation.isActive()) return@forEach
            val mapper = EntryMapper(entryManager)
            val finalEntry = mapper.translate(finalEntryId)
            val startEntry = mapper.translate(entryId)
            val successors = mapper.translateSuccessors(entryId, allSuccessors, cancellation)
            if (!cancellation.isActive()) return@forEach
            val entries = mapper.entries.toTypedArray()

            val actionVariants = Int2ObjectOpenHashMap<List<ActionVariant>>()
            unsafeActionVariants().forEachIntEntry { key, value ->
                if (!cancellation.isActive()) return@forEachIntEntry
                if (!mapper.isTranslated(key)) return@forEachIntEntry

                val translatedId = mapper.translate(key)
                actionVariants.put(translatedId, value.toList())
            }

            result += FullStart2FinalTrace(
                methodEntryPoint, entries, actionVariants, startEntry, finalEntry, successors, traceKind
            )
        }

        return result.takeIf { cancellation.isActive() }.orEmpty()
    }

    private fun EntryMapper.translateSuccessors(
        start: Int,
        allSuccessors: Int2ObjectOpenHashMap<CompactIntSet>,
        cancellation: Cancellation,
    ): Int2ObjectOpenHashMap<CompactIntSet> {
        val result = Int2ObjectOpenHashMap<CompactIntSet>()

        val unprocessed = IntArrayList()
        unprocessed.add(start)
        while (unprocessed.isNotEmpty() && cancellation.isActive()) {
            val node = unprocessed.removeInt(unprocessed.lastIndex)

            val translatedNode = translate(node)
            if (result.containsKey(translatedNode)) continue

            val translatedSuccessors = CompactIntSet()
            allSuccessors.get(node)?.forEach {
                unprocessed.add(it)
                translatedSuccessors.add(translate(it))
            }

            result.put(translatedNode, translatedSuccessors)
        }

        return result
    }

    private fun TraceBuilder.successors(): Int2ObjectOpenHashMap<CompactIntSet> {
        val allSuccessors = Int2ObjectOpenHashMap<CompactIntSet>()
        for ((entryId, entryPredecessorIds) in predecessors) {
            if (!cancellation.isActive()) break
            entryPredecessorIds.forEach { predecessorId: Int ->
                allSuccessors.computeIfAbsent(predecessorId) { CompactIntSet() }.add(entryId)
            }
        }
        return allSuccessors
    }

    private fun TraceBuilder.resolveTrace(traceKind: TraceKind) {
        while (unprocessedEntryIds.isNotEmpty() && cancellation.isActive()) {
            if (
                actions() > traceResolutionActionHardLimit &&
                (finalHasAlternativePremises || !startEntryIds.isEmpty)
            ) {
                actionHardLimitReached = true
                logger.warn {
                    "Trace resolution stopped for $methodEntryPoint: action hard limit " +
                        traceResolutionActionHardLimit
                }
                return
            }

            val entryId = unprocessedEntryIds.removeInt(unprocessedEntryIds.lastIndex)
            val entry = entryManager.entryById(entryId)
            processTraceEntry(entry, traceKind)
        }
    }

    private fun TraceBuilder.processTraceEntry(entry: TraceEntry, traceKind: TraceKind) {
        if (entry is TraceEntry.StartTraceEntry) {
            addStartEntry(entry)
            return
        }

        if (entry is TraceEntry.Final) {
            when (traceKind) {
                TraceKind.TraceToFact -> {
                    // We have fact BEFORE entry.statement, no need to propagate
                }

                TraceKind.TraceToFactAfterStatement,
                TraceKind.SummaryTrace -> {
                    // We have fact AFTER entry.statement
                    propagateEntryNew(entry.statement, entry, skipFactCheck = true)
                    return
                }
            }
        }

        graph.forEachPredecessor(analysisManager, entry.statement) {
            propagateEntryNew(it, entry)
        }

        if (entry.statement == methodEntryPoint.statement) {
            propagateEntryToMethodEntryPoint(entry)
            return
        }
    }

    private fun TraceBuilder.propagateEntryToMethodEntryPoint(
        entry: TraceEntry
    ) {
        val applicablePremises = entry.edges.premisesByFinalFact.values.map { premises ->
            premises.filter { containsEntryEdgeCached(entry.statement, it) }
        }
        if (applicablePremises.any { it.isEmpty() }) return

        applicablePremises.forEachCartesianProduct { selectedPremises ->
            val entryEdges = hashSetOf<TraceEdge>()
            val sources = hashSetOf<SourceOtherAction>()

            for (edge in selectedPremises) {
                when (edge) {
                    is TraceEdge.MethodTraceEdge -> entryEdges.add(edge)
                    is TraceEdge.MethodTraceNDEdge -> entryEdges.add(edge)
                    is TraceEdge.SourceTraceEdge -> {
                        val preconditionFunction =
                            analysisManager.getMethodStartPrecondition(apManager, analysisContext)
                        preconditionFunction.factPrecondition(edge.fact).forEach {
                            sources += TraceEntryAction.EntryPointSourceRule(
                                setOf(edge), methodEntryPoint, it.rule, it.action
                            )
                        }
                    }
                }
            }

            if (entryEdges.isEmpty()) {
                if (sources.isNotEmpty()) {
                    addPredecessor(
                        entry,
                        TraceEntry.SourceStartEntry(null, sources, methodEntryPoint.statement)
                    )
                }
                return@forEachCartesianProduct
            }

            val preStartEntry = if (sources.isNotEmpty()) {
                val entryRequirements = TraceEdges.of(entryEdges)
                val actionVariant = ActionVariant(primaryAction = null, sources, entryRequirements)
                createAction(methodEntryPoint.statement, entryRequirements, setOf(actionVariant))
                    .also { addPredecessor(entry, it, enqueue = false) }
            } else {
                entry
            }

            val entryFacts = entryEdges.flatMapTo(hashSetOf()) {
                when (it) {
                    is TraceEdge.MethodTraceEdge -> listOf(it.initialFact)
                    is TraceEdge.MethodTraceNDEdge -> it.initialFacts
                    is TraceEdge.SourceTraceEdge -> error("impossible")
                }
            }

            addPredecessor(preStartEntry, TraceEntry.MethodEntry(entryFacts, methodEntryPoint))
        }
    }

    private sealed interface ActionOrUnchanged<T> {
        data class Unchanged<T>(val edges: TraceEdges) : ActionOrUnchanged<T>
        data class Action<T>(val action: T) : ActionOrUnchanged<T>
    }

    private fun TraceBuilder.propagateEntryNew(
        statement: CommonInst,
        entry: TraceEntry,
        skipFactCheck: Boolean = false,
    ) {
        val statementCall = analysisManager.getCallExpr(statement)
        if (statementCall != null) {
            val returnValue: CommonValue? = (statement as? CommonAssignInst)?.lhv

            val preconditionFunction = analysisManager.getMethodCallPrecondition(
                apManager, analysisContext, returnValue, statementCall, statement
            )
            val callees by lazy {
                runner.methodCallResolver.resolvedMethodCalls(analysisContext, statementCall, statement)
            }

            val callEdges = mutableListOf<List<ActionOrUnchanged<PartiallyResolvedCallAction>>>()

            for ((fact, currentEdges) in entry.edges.premisesByFinalFact) {
                val preconditions = callFactPrecondition(preconditionFunction, fact, callees)
                val callActions = mutableListOf<ActionOrUnchanged<PartiallyResolvedCallAction>>()

                for (precondition in preconditions) {
                    when (precondition) {
                        is CallPrecondition.Unchanged -> {
                            callActions += ActionOrUnchanged.Unchanged(TraceEdges.of(currentEdges))
                        }
                        is MethodCallPrecondition.PreconditionFactsForInitialFact -> {
                            val applicableEdges = if (skipFactCheck) {
                                currentEdges
                            } else {
                                currentEdges.filterTo(hashSetOf()) {
                                    containsEntryEdgeCached(entry.statement, it.replaceFact(precondition.initialFact))
                                }
                            }
                            if (applicableEdges.isEmpty()) continue

                            collectToListWithPostProcess(
                                callActions,
                                {
                                    it.propagateCall(
                                        TraceEdges.of(applicableEdges),
                                        precondition.preconditionFacts,
                                    )
                                },
                                { ActionOrUnchanged.Action(it) }
                            )
                        }
                    }
                }

                if (callActions.isEmpty()) {
                    // fact has no preconditions
                    return
                }

                callEdges.add(callActions)
            }
            val allUnchanged = callEdges.allUnchanged()
            if (allUnchanged != null) {
                addPredecessor(entry, TraceEntry.Unchanged(allUnchanged, statement))
                return
            }

            val resolvedMethodEntryPoints by lazy {
                cache.calleeEntryPoints(statement) {
                    callees.mapNotNull {
                        when (it) {
                            is MethodCallResolutionResult.ResolvedMethod -> it.method
                            MethodCallResolutionResult.ResolutionFailure -> null
                        }
                    }.flatMap(::methodEntryPoints)
                }
            }

            val resolvedCallActions = mutableListOf<ActionEdgeCombination>()
            forEachMergedCallActionsCombination(callEdges, { resolvedMethodEntryPoints }) { callAction ->
                resolvedCallActions.resolveCallAction(this, preconditionFunction, statement, callAction)
            }

            addPredecessorActions(resolvedCallActions, entry, statement)
        } else {
            val preconditionFunction = analysisManager.getMethodSequentPrecondition(
                apManager, analysisContext, statement
            )

            val sequentActions = mutableListOf<List<ActionOrUnchanged<SequentialAction>>>()

            for ((fact, currentEdges) in entry.edges.premisesByFinalFact) {
                val preconditions = preconditionFunction.factPrecondition(fact)
                val actions = mutableListOf<ActionOrUnchanged<SequentialAction>>()

                for (precondition in preconditions) {
                    when (precondition) {
                        is SequentPrecondition.Unchanged -> {
                            actions += ActionOrUnchanged.Unchanged(TraceEdges.of(currentEdges))
                        }
                        is MethodSequentPrecondition.SequentPreconditionFacts -> {
                            val applicableEdges = if (skipFactCheck) {
                                currentEdges
                            } else {
                                currentEdges.filterTo(hashSetOf()) {
                                    containsEntryEdgeCached(entry.statement, it.replaceFact(precondition.fact))
                                }
                            }
                            if (applicableEdges.isEmpty()) continue

                            when (precondition) {
                                is MethodSequentPrecondition.PreconditionFactsForInitialFact -> {
                                    precondition.preconditionFacts.mapTo(actions) { fact ->
                                        ActionOrUnchanged.Action(
                                            TraceEntryAction.Sequential(
                                                TraceEdges.of(applicableEdges.map { it.replaceFact(fact) }),
                                                TraceEdges.of(applicableEdges),
                                            )
                                        )
                                    }
                                }

                                is MethodSequentPrecondition.SequentSource -> {
                                    val sourceEdges = applicableEdges
                                        .filterIsInstanceTo<TraceEdge.SourceTraceEdge, _>(hashSetOf())
                                    if (sourceEdges.isNotEmpty()) {
                                        actions += ActionOrUnchanged.Action(
                                            TraceEntryAction.SequentialSourceRule(
                                                sourceEdges, precondition.rule.rule, precondition.rule.action
                                            )
                                        )
                                    }
                                }
                            }
                        }
                    }
                }

                if (actions.isEmpty()) {
                    // fact has no preconditions
                    return
                }

                sequentActions.add(actions)
            }

            val allUnchanged = sequentActions.allUnchanged()
            if (allUnchanged != null) {
                addPredecessor(entry, TraceEntry.Unchanged(allUnchanged, statement))
                return
            }

            val actionCombination = mergeSequentEdgeCombinations(sequentActions)
            addPredecessorActions(actionCombination, entry, statement)
        }
    }

    private fun callFactPrecondition(
        preconditionFunction: MethodCallPrecondition,
        fact: InitialFactAp,
        callees: List<MethodCallResolutionResult>,
    ): List<CallPrecondition> = buildList {
        val preconditions = preconditionFunction.factPrecondition(fact)

        preconditions.forEach { precondition ->
            when (precondition) {
                CallPrecondition.Unchanged -> {
                    this += precondition
                }

                is MethodCallPrecondition.PreconditionFactsForInitialFact -> {
                    this += processCallPreconditionFacts(preconditionFunction, precondition, callees)
                }
            }
        }
    }

    private fun processCallPreconditionFacts(
        preconditionFunction: MethodCallPrecondition,
        precondition: MethodCallPrecondition.PreconditionFactsForInitialFact,
        callees: List<MethodCallResolutionResult>,
    ): MethodCallPrecondition.PreconditionFactsForInitialFact {
        val resolutionFailure by lazy { callees.any { it is MethodCallResolutionResult.ResolutionFailure } }

        val processedPreconditions = precondition.preconditionFacts.flatMapTo(hashSetOf()) { preconditionFact ->
            when (preconditionFact) {
                is CallPreconditionFact.UnresolvedCallSkip -> listOf(preconditionFact)
                is CallPreconditionFact.CallToReturnTaintRule -> listOf(preconditionFact)

                is CallPreconditionFact.CallToStart -> {
                    if (resolutionFailure) {
                        preconditionFunction.factPreconditionResolutionFailure(
                            precondition.initialFact,
                            preconditionFact.startFactBase
                        ) + preconditionFact
                    } else {
                        listOf(preconditionFact)
                    }
                }
            }
        }.toList()

        return MethodCallPrecondition.PreconditionFactsForInitialFact(precondition.initialFact, processedPreconditions)
    }

    private fun TraceBuilder.addPredecessorActions(
        actionsCombination: List<ActionEdgeCombination>,
        entry: TraceEntry,
        statement: CommonInst,
    ) {
        val variantsByEdges = hashMapOf<TraceEdges, MutableSet<ActionVariant>>()

        for (sequent in actionsCombination) {
            if (sequent.other.isEmpty()) {
                if (sequent.primary == null) {
                    addPredecessor(entry, TraceEntry.Unchanged(sequent.unchanged, statement))
                    continue
                }

                val primaryUnchanged = sequent.primary.canBeTreatedAsUnchanged()
                if (primaryUnchanged != null) {
                    addPredecessor(
                        entry,
                        TraceEntry.Unchanged(sequent.unchanged.conjoin(primaryUnchanged), statement),
                    )
                    continue
                }
            }

            val variant = ActionVariant(sequent.primary, sequent.other, sequent.unchanged)
            val sourceStart = tryCreateSourceStart(variant, statement)
            if (sourceStart != null) {
                addPredecessor(entry, sourceStart)
            } else {
                variantsByEdges.getOrPut(variant.edges, ::hashSetOf).add(variant)
            }
        }

        for ((edges, variants) in variantsByEdges) {
            val action = createAction(statement, edges, variants)
            addPredecessor(entry, action)
        }
    }

    private fun PrimaryAction.canBeTreatedAsUnchanged(): TraceEdges? {
        if (this !is TraceEntryAction.PassAction) return null
        if (this !is CallSummary && this !is TraceEntryAction.Sequential) return null

        if (edges.size != 1) return null

        val edge = edges.first()

        // note: for now we drop calls only with single mark on a static field
        if (edge.fact.base !is AccessPathBase.ClassStatic) return null

        val after = edgesAfter.singleOrNull() ?: return null
        if (edge != after) return null

        return TraceEdges.of(setOf(edge))
    }

    private fun List<List<ActionOrUnchanged<*>>>.allUnchanged(): TraceEdges? {
        val unchanged = mutableListOf<TraceEdges>()
        for (aouGroup in this) {
            val aou = aouGroup.singleOrNull() ?: return null
            if (aou !is ActionOrUnchanged.Unchanged) return null
            unchanged += aou.edges
        }
        return TraceEdges.conjoin(unchanged)
    }

    private fun tryCreateSourceStart(
        variant: ActionVariant,
        statement: CommonInst,
    ): TraceEntry.SourceStartEntry? {
        if (variant.unchanged.isNotEmpty()) return null

        val primary = variant.primaryAction
        if (primary !is TraceEntryAction.SourcePrimaryAction?) return null

        val sourceOther = variant.otherActions.filterIsInstanceTo<SourceOtherAction, _>(hashSetOf())
        if (sourceOther.size != variant.otherActions.size) return null

        return TraceEntry.SourceStartEntry(primary, sourceOther, statement)
    }

    private data class ActionEdgeCombination(
        val unchanged: TraceEdges,
        val primary: PrimaryAction?,
        val other: Set<OtherAction>,
    )

    private fun mergeSequentEdgeCombinations(allActions: List<List<ActionOrUnchanged<SequentialAction>>>): List<ActionEdgeCombination> {
        val result = mutableListOf<ActionEdgeCombination>()
        allActions.cartesianProductMapTo { actionCombination ->
            val unchanged = mutableListOf<TraceEdges>()
            val sequential = mutableListOf<TraceEdges>()
            val sequentialAfter = mutableListOf<TraceEdges>()

            val rules = hashSetOf<TraceEntryAction.SequentialSourceRule>()

            for (aou in actionCombination) {
                when (aou) {
                    is ActionOrUnchanged.Unchanged -> {
                        unchanged += aou.edges
                    }

                    is ActionOrUnchanged.Action -> when (val action = aou.action) {
                        is TraceEntryAction.Sequential -> {
                            sequential += action.edges
                            sequentialAfter += action.edgesAfter
                        }

                        is TraceEntryAction.SequentialSourceRule -> rules.add(action)
                    }
                }
            }

            val primaryAction = sequential.takeIf { it.isNotEmpty() }?.let {
                TraceEntryAction.Sequential(
                    TraceEdges.conjoin(it),
                    TraceEdges.conjoin(sequentialAfter),
                )
            }
            result += ActionEdgeCombination(TraceEdges.conjoin(unchanged), primaryAction, rules)
        }
        return result
    }

    private data class PartialCallEdgeCombination(
        val unchanged: TraceEdges,
        val primary: PartiallyResolvedMergedPrimaryCallAction?,
        val rule: Set<MergedRuleAction>,
    )

    private inline fun forEachMergedCallActionsCombination(
        callActions: List<List<ActionOrUnchanged<PartiallyResolvedCallAction>>>,
        noinline calleeEntryPoints: () -> List<MethodEntryPoint>,
        body: (PartialCallEdgeCombination) -> Unit,
    ) {
        val seen = hashSetOf<PartialCallEdgeCombination>()
        callActions.forEachCartesianProduct { actions ->
            val mergedActions = mergeCallActions(actions, calleeEntryPoints)
            mergedActions.forEach { action ->
                if (seen.add(action)) body(action)
            }
        }
    }

    private fun mergeCallActions(
        aouGroup: Array<ActionOrUnchanged<PartiallyResolvedCallAction>>,
        resolveCalleeEntryPoints: () -> List<MethodEntryPoint>,
    ): List<PartialCallEdgeCombination> {
        val unchanged = mutableListOf<TraceEdges>()
        val rules = hashSetOf<PartiallyResolvedCallAction.CallRule>()
        val summary = hashSetOf<PartiallyResolvedCallAction.Call2Start>()
        val unresolvedSkips = hashSetOf<PartiallyResolvedCallAction.UnresolvedCallSkip>()

        for (aou in aouGroup) {
            when (aou) {
                is ActionOrUnchanged.Unchanged -> {
                    unchanged += aou.edges
                }

                is ActionOrUnchanged.Action -> when (val action = aou.action) {
                    is PartiallyResolvedCallAction.CallRule -> rules.add(action)
                    is PartiallyResolvedCallAction.Call2Start -> summary.add(action)
                    is PartiallyResolvedCallAction.UnresolvedCallSkip -> { unresolvedSkips.add(action) }
                }
            }
        }

        val mergedRules = mergeCallRules(rules)

        if (summary.isEmpty()) {
            if (unresolvedSkips.isEmpty()) {
                return listOf(
                    PartialCallEdgeCombination(TraceEdges.conjoin(unchanged), primary = null, mergedRules)
                )
            }

            val skippedEdges = TraceEdges.conjoin(unresolvedSkips.map { it.currentEdges })
            val primary = MergedPrimaryUnresolvedCallSkip(UnresolvedCallSkip(skippedEdges, skippedEdges))
            return listOf(PartialCallEdgeCombination(TraceEdges.conjoin(unchanged), primary, mergedRules))
        }

        if (unresolvedSkips.isNotEmpty()) {
            // note: we have a summary (i.e. call resolved) and an unresolved call
            return emptyList()
        }

        val result = mutableListOf<PartialCallEdgeCombination>()
        resolveCalleeEntryPoints().forEach { entryPoint ->
            val primary = MergedPrimaryCall2StartAction(entryPoint, summary)
            result += PartialCallEdgeCombination(TraceEdges.conjoin(unchanged), primary, mergedRules)
        }

        return result
    }

    private fun mergeCallRules(callRules: HashSet<PartiallyResolvedCallAction.CallRule>): Set<MergedRuleAction> {
        if (callRules.isEmpty()) return emptySet()

        val sourceRules = hashMapOf<CommonTaintConfigurationSource, MutableList<PartiallyResolvedCallAction.CallRule>>()
        val passRules = hashMapOf<CommonTaintConfigurationItem, MutableMap<PassRuleCondition, MutableList<PartiallyResolvedCallAction.CallRule>>>()

        for (unresolvedRule in callRules) {
            when (val rule = unresolvedRule.rule) {
                is TaintRulePrecondition.Pass -> passRules
                    .getOrPut(rule.rule, ::hashMapOf)
                    .getOrPut(rule.condition, ::mutableListOf)
                    .add(unresolvedRule)

                is TaintRulePrecondition.Source -> sourceRules
                    .getOrPut(rule.rule, ::mutableListOf)
                    .add(unresolvedRule)
            }
        }

        val result = hashSetOf<MergedRuleAction>()
        for ((rule, ruleActions) in sourceRules) {
            val action = ruleActions.flatMapTo(hashSetOf()) {
                (it.rule as TaintRulePrecondition.Source).action
            }
            val edges = TraceEdges.conjoin(ruleActions.map { it.currentEdges })
            result += MergedRuleAction(edges, TaintRulePrecondition.Source(rule, action))
        }

        for ((rule, conditionedActions) in passRules) {
            for ((condition, ruleActions) in conditionedActions) {
                val action = ruleActions.flatMapTo(hashSetOf()) {
                    (it.rule as TaintRulePrecondition.Pass).action
                }
                val edges = TraceEdges.conjoin(ruleActions.map { it.currentEdges })
                result += MergedRuleAction(edges, TaintRulePrecondition.Pass(rule, action, condition))
            }
        }

        return result
    }

    private sealed interface PartiallyResolvedCallAction {
        data class CallRule(
            val currentEdges: TraceEdges,
            val rule: TaintRulePrecondition
        ) : PartiallyResolvedCallAction

        data class Call2Start(
            val currentEdges: TraceEdges,
            val call2Start: CallPreconditionFact.CallToStart,
        ): PartiallyResolvedCallAction

        data class UnresolvedCallSkip(
            val currentEdges: TraceEdges,
        ): PartiallyResolvedCallAction
    }

    private sealed interface PartiallyResolvedMergedCallAction {
        sealed interface PartiallyResolvedMergedPrimaryCallAction: PartiallyResolvedMergedCallAction

        data class MergedPrimaryCall2StartAction(
            val calleeEntryPoint: MethodEntryPoint,
            val call2Start: Set<PartiallyResolvedCallAction.Call2Start>,
        ) : PartiallyResolvedMergedPrimaryCallAction

        data class MergedPrimaryUnresolvedCallSkip(
            val action: UnresolvedCallSkip
        ) : PartiallyResolvedMergedPrimaryCallAction

        data class MergedRuleAction(
            val currentEdges: TraceEdges,
            val rule: TaintRulePrecondition
        ) : PartiallyResolvedMergedCallAction
    }

    private fun MutableList<PartiallyResolvedCallAction>.propagateCall(
        currentEdges: TraceEdges,
        preconditionFacts: List<CallPreconditionFact>
    ) {
        for (fact in preconditionFacts) {
            when (fact) {
                is CallPreconditionFact.CallToReturnTaintRule -> {
                    val ruleEdges = if (fact.precondition is TaintRulePrecondition.Source) {
                        TraceEdges.of(currentEdges.filterIsInstance<TraceEdge.SourceTraceEdge>())
                    } else {
                        currentEdges
                    }
                    if (ruleEdges.isEmpty()) {
                        // We search for pass-rule, not source rule
                        continue
                    }

                    this += PartiallyResolvedCallAction.CallRule(ruleEdges, fact.precondition)
                }

                is CallPreconditionFact.CallToStart -> {
                    this += PartiallyResolvedCallAction.Call2Start(currentEdges, fact)
                }

                is CallPreconditionFact.UnresolvedCallSkip -> {
                    this += PartiallyResolvedCallAction.UnresolvedCallSkip(currentEdges)
                }
            }
        }
    }

    private fun MutableList<ActionEdgeCombination>.resolveCallAction(
        builder: TraceBuilder,
        preconditionFunction: MethodCallPrecondition,
        statement: CommonInst,
        callAction: PartialCallEdgeCombination,
    ) {
        fun addResolved(primaryActions: List<PrimaryAction>?, otherActions: Set<OtherAction>) {
            if (primaryActions == null) {
                this += ActionEdgeCombination(callAction.unchanged, primary = null, otherActions)
            } else {
                primaryActions.forEach {
                    this += ActionEdgeCombination(callAction.unchanged, it, otherActions)
                }
            }
        }

        val resolvedPrimaryAction = when (val primaryAction = callAction.primary) {
            null -> null
            is MergedPrimaryUnresolvedCallSkip -> listOf(primaryAction.action)
            is MergedPrimaryCall2StartAction -> {
                resolveCallSummary(builder, statement, primaryAction.calleeEntryPoint, primaryAction.call2Start)
            }
        }

        val ruleActions = callAction.rule
        if (ruleActions.isEmpty()) {
            addResolved(resolvedPrimaryAction, emptySet())
            return
        }

        val resolvedRuleActions = ruleActions.map {
            resolveCallRule(it.currentEdges, it.rule, preconditionFunction, statement)
        }

        resolvedRuleActions.forEachCartesianProduct { ruleActionGroup ->
            addResolved(resolvedPrimaryAction, ruleActionGroup.toHashSet())
        }
    }

    private fun resolveCallSummary(
        builder: TraceBuilder,
        statement: CommonInst,
        callee: MethodEntryPoint,
        call2Start: Set<PartiallyResolvedCallAction.Call2Start>,
    ): List<PrimaryAction> {
        val resultSummaries = mutableListOf<List<CallSummary>>()
        for (action in call2Start) {
            val edgeSummaries = mutableListOf<CallSummary>()

            for (currentEdge in action.currentEdges) {
                if (currentEdge is TraceEdge.SourceTraceEdge) {
                    edgeSummaries.resolveCallSourceSummary(currentEdge, callee, action.call2Start)
                }

                edgeSummaries.resolveCallPassSummary(currentEdge, callee, action.call2Start, statement)
            }

            if (edgeSummaries.isEmpty()) return emptyList()

            resultSummaries.add(edgeSummaries.mergeEquivalentCallSummaries())
        }

        val resultActions = linkedSetOf<PrimaryAction>()
        resultSummaries.forEachCartesianProduct { summaryGroup ->
            resultActions += mergeCallSummary(summaryGroup) ?: return@forEachCartesianProduct
        }
        return resultActions.toList()
    }

    private fun List<CallSummary>.mergeEquivalentCallSummaries(): List<CallSummary> = buildList {
        this@mergeEquivalentCallSummaries.groupBy { it.summaryTrace }.values.forEach { equivalent ->
            val edgeFacts = equivalent.mapNotNullTo(hashSetOf()) {
                it.edges.premisesByFinalFact.keys.singleOrNull()
            }
            val edgeAfterFacts = equivalent.mapNotNullTo(hashSetOf()) {
                it.edgesAfter.premisesByFinalFact.keys.singleOrNull()
            }
            val canMergeAsAlternatives =
                edgeFacts.size == 1 &&
                    edgeAfterFacts.size == 1 &&
                    equivalent.all {
                        it.edges.premisesByFinalFact.size == 1 &&
                            it.edgesAfter.premisesByFinalFact.size == 1
                    }

            if (!canMergeAsAlternatives) {
                addAll(equivalent)
                return@forEach
            }

            add(
                CallSummary(
                    summaryEdges = equivalent.flatMapTo(hashSetOf()) { it.summaryEdges },
                    summaryTrace = equivalent.first().summaryTrace,
                    edges = TraceEdges.of(equivalent.flatMap { it.edges }),
                    edgesAfter = TraceEdges.of(equivalent.flatMap { it.edgesAfter }),
                )
            )
        }
    }

    private fun mergeCallSummary(callSummaries: Array<CallSummary>): PrimaryAction? {
        check(callSummaries.all { it.summaryTrace.traceKind == TraceKind.SummaryTrace })

        val callee = callSummaries.first().summaryTrace.method

        val exitStatement = callSummaries.first().summaryTrace.final.statement
        if (callSummaries.any { it.summaryTrace.final.statement != exitStatement }) return null

        val summaryEdges = hashSetOf<TraceSummaryEdge>()

        for (summary in callSummaries) {
            summaryEdges += summary.summaryEdges
        }

        val summaryTraceFinal = TraceEntry.Final(
            TraceEdges.conjoin(callSummaries.map { it.summaryTrace.final.edges }),
            exitStatement,
        )
        val summaryTrace = SummaryTrace(callee, summaryTraceFinal, TraceKind.SummaryTrace)

        val sourceSummaryEdges = summaryEdges.filterIsInstanceTo<TraceSummaryEdge.SourceSummary, _>(hashSetOf())
        val summaryAction = if (sourceSummaryEdges.size == summaryEdges.size) {
            TraceEntryAction.CallSourceSummary(sourceSummaryEdges, summaryTrace)
        } else {
            CallSummary(
                summaryEdges,
                summaryTrace,
                TraceEdges.conjoin(callSummaries.map { it.edges }),
                TraceEdges.conjoin(callSummaries.map { it.edgesAfter }),
            )
        }

        return summaryAction
    }

    private fun resolveCallRule(
        currentEdges: TraceEdges,
        rule: TaintRulePrecondition,
        preconditionFunction: MethodCallPrecondition,
        statement: CommonInst,
    ): List<OtherAction> {
        when (rule) {
            is TaintRulePrecondition.Source -> {
                val sourceEdges = currentEdges.filterIsInstanceTo<TraceEdge.SourceTraceEdge, _>(hashSetOf())
                check(sourceEdges.size == currentEdges.size) {
                    "Unexpected non-source edge"
                }

                return listOf(TraceEntryAction.CallSourceRule(sourceEdges, rule.rule, rule.action))
            }

            is TaintRulePrecondition.Pass -> {
                val conditionFacts = preconditionFunction.resolvePassRuleCondition(rule.condition, edges)
                return conditionFacts.flatMap {
                    resolvePassCallRulePrecondition(currentEdges, statement, rule, it.facts)
                }
            }
        }
    }

    private fun resolvePassCallRulePrecondition(
        currentEdges: TraceEdges,
        statement: CommonInst,
        rule: TaintRulePrecondition.Pass,
        facts: List<InitialFactAp>,
    ): List<TraceEntryAction.CallRule> {
        when (facts.size) {
            0 -> error("impossible")
            1 -> {
                return listOf(
                    TraceEntryAction.CallRule(
                        currentEdges.collapseToFact(facts.first()),
                        currentEdges,
                        rule.rule,
                        rule.action,
                    )
                )
            }

            else -> {
                val result = linkedSetOf<TraceEntryAction.CallRule>()

                val allFactEdges = facts.map {
                    resolveIntraProceduralTraceEdge(statement, it, includeStatement = false)
                }

                val currentPremiseGroups = currentEdges.premisesByFinalFact.values.map { it.toList() }

                allFactEdges.cartesianProductMapTo { edgeGroup ->
                    currentPremiseGroups.forEachCartesianProduct { selectedCurrentPremises ->
                        if (!selectedCurrentPremises.asIterable().hasSameInitialFactsAs(edgeGroup.asIterable())) {
                            return@forEachCartesianProduct
                        }

                        result += TraceEntryAction.CallRule(
                            TraceEdges.of(edgeGroup.asIterable()),
                            TraceEdges.of(selectedCurrentPremises.asIterable()),
                            rule.rule,
                            rule.action,
                        )
                    }
                }

                return result.toList()
            }
        }
    }

    private fun Iterable<TraceEdge>.hasSameInitialFactsAs(otherEdges: Iterable<TraceEdge>): Boolean =
        flatMapTo(hashSetOf()) { it.normalizedInitialFacts() } ==
            otherEdges.flatMapTo(hashSetOf()) { it.normalizedInitialFacts() }

    private fun TraceEdge.normalizedInitialFacts(): Set<InitialFactAp> = when (this) {
        is TraceEdge.SourceTraceEdge -> emptySet()
        is TraceEdge.MethodTraceEdge -> setOf(initialFact.replaceExclusions(ExclusionSet.Universe))
        is TraceEdge.MethodTraceNDEdge -> initialFacts.mapTo(hashSetOf()) {
            it.replaceExclusions(ExclusionSet.Universe)
        }
    }

    private fun MutableList<CallSummary>.resolveCallPassSummary(
        currentEdge: TraceEdge,
        callee: MethodEntryPoint,
        startFact: CallPreconditionFact.CallToStart,
        statement: CommonInst
    ) {
        addAll(cache.callPassSummaries(currentEdge, callee, startFact, statement) {
            computeCallPassSummaries(currentEdge, callee, startFact, statement)
        })
    }

    private fun computeCallPassSummaries(
        currentEdge: TraceEdge,
        callee: MethodEntryPoint,
        startFact: CallPreconditionFact.CallToStart,
        statement: CommonInst,
    ): List<CallSummary> {
        val resolvedCallSummaries = mutableListOf<CallSummary>()

        val callerFact = startFact.callerFact
        val finalFactPattern = (callerFact as? BaseOnlyInitialFactAp)?.let {
            BaseOnlyFinalFactAp(
                manager = it.manager,
                base = startFact.startFactBase,
                access = it.access,
                exclusions = it.exclusions,
            )
        }
        val methodSummaries = if (finalFactPattern == null) {
            manager.findFactToFactSummaryEdges(callee, startFact.startFactBase)
        } else {
            manager.findFactToFactSummaryEdges(callee, finalFactPattern)
        }
        val applicableMethodSummaries = methodSummaries.filter { isApplicableExitToReturnEdge(it) }

        for (summaryEdge in applicableMethodSummaries) {
            val mappedSummaryFact = summaryEdge.factAp.rebase(callerFact.base)
            val deltas = callerFact.splitDelta(mappedSummaryFact)
            if (deltas.isEmpty()) continue

            // it is ok to map call arguments via exit2return
            val mappedSummaryInitial = methodCallFactMapper.mapMethodExitToReturnFlowFact(
                statement, summaryEdge.initialFactAp
            )

            for ((matchedEntryFact, delta) in deltas) {
                // todo: remove this check?
                if (!mappedSummaryFact.contains(matchedEntryFact)) continue

                for (mappedSummaryInitialFact in mappedSummaryInitial) {
                    val precondition = mappedSummaryInitialFact
                        .concat(delta)
                        .replaceExclusions(callerFact.exclusions)

                    resolvedCallSummaries.addCallSummaryEntry(
                        currentTraceEdge = currentEdge,
                        precondition = precondition,
                        preconditionDelta = delta,
                        callee = callee,
                        summaryFinalFact = matchedEntryFact,
                        summaryEdge = summaryEdge,
                    )
                }
            }
        }

        val result = selectWeakestEntries(resolvedCallSummaries).toMutableList()
        val methodNdSummaries = manager.findFactNDSummaryEdges(callee, startFact.startFactBase)
        val applicableNDSummaries = methodNdSummaries.filter { isApplicableExitToReturnEdge(it) }

        for (summaryEdge in applicableNDSummaries) {
            val mappedSummaryFact = summaryEdge.factAp.rebase(callerFact.base)
            if (!mappedSummaryFact.contains(callerFact)) continue

            val mappedSummaryInitialFacts = summaryEdge.initialFacts.map {
                methodCallFactMapper.mapMethodExitToReturnFlowFact(statement, it)
            }

            mappedSummaryInitialFacts.cartesianProductMapTo { mappedFactGroup ->
                val preconditions = mappedFactGroup.toHashSet()

                val mappedFinalFact = callerFact
                    .rebase(summaryEdge.factAp.base)
                    .replaceExclusions(summaryEdge.factAp.exclusions)

                val traceSummaryEdge = TraceEdge.MethodTraceNDEdge(summaryEdge.initialFacts, mappedFinalFact)
                val calleeTrace = SummaryTrace(
                    final = TraceEntry.Final(setOf(traceSummaryEdge), summaryEdge.statement),
                    method = callee,
                    traceKind = TraceKind.SummaryTrace,
                )

                val callSummaries = preconditions.mapTo(hashSetOf()) {
                    TraceSummaryEdge.MethodSummary(currentEdge.replaceFact(it), currentEdge, delta = null)
                }

                result += CallSummary(callSummaries, calleeTrace)
            }
        }

        return result
    }

    private fun MutableList<CallSummary>.resolveCallSourceSummary(
        currentEdge: TraceEdge.SourceTraceEdge,
        callee: MethodEntryPoint,
        startFact: CallPreconditionFact.CallToStart
    ) {
        val relevantSummaryEdges = manager.findZeroToFactSummaryEdges(callee, startFact.startFactBase)
        val applicableSummaryEdges = relevantSummaryEdges.filter { isApplicableExitToReturnEdge(it) }

        for (summaryEdge in applicableSummaryEdges) {
            val mappedSummaryFact = summaryEdge.factAp.rebase(startFact.callerFact.base)
            if (!mappedSummaryFact.contains(startFact.callerFact)) continue

            val summaryEdgeTrace = TraceEdge.SourceTraceEdge(startFact.callerFact.rebase(startFact.startFactBase))
            val summaryTrace = SummaryTrace(
                method = callee,
                final = TraceEntry.Final(setOf(summaryEdgeTrace), summaryEdge.statement),
                traceKind = TraceKind.SummaryTrace
            )

            val callSummary = TraceSummaryEdge.SourceSummary(currentEdge, currentEdge)
            this += CallSummary(setOf(callSummary), summaryTrace)
        }
    }

    private fun isApplicableExitToReturnEdge(edge: Edge): Boolean {
        return !analysisManager.producesExceptionalControlFlow(edge.statement)
    }

    private fun selectWeakestEntries(allSummaries: List<CallSummary>): List<CallSummary> {
        val result = mutableListOf<CallSummary>()
        allSummaries
            .groupBy { it.summaryTrace.final.statement }
            .values.forEach { entries ->
                val selectedEntries = LinkedList<CallSummary>()
                for (summary in entries.dropFieldEntriesCoveredByApplicableWildcard()) {
                    addWeakestEntry(summary, selectedEntries)
                }
                result += selectedEntries
            }
        return result
    }

    private fun List<CallSummary>.dropFieldEntriesCoveredByApplicableWildcard(): List<CallSummary> {
        val wildcardEntries = filter { it.hasApplicableBaseOnlyWildcardSummary() }
        if (wildcardEntries.isEmpty()) return this
        return filterNot { entry ->
            if (entry.hasApplicableBaseOnlyWildcardSummary()) return@filterNot false
            wildcardEntries.any { wildcard -> entry.isCoveredByApplicableWildcard(wildcard) }
        }
    }

    private fun CallSummary.hasApplicableBaseOnlyWildcardSummary(): Boolean {
        val summary = summaryEdges.singleOrNull() as? TraceSummaryEdge.MethodSummary ?: return false
        val initial = summary.delta?.initialFact as? BaseOnlyInitialFactAp ?: return false
        return initial.access == ABSTRACT_EMPTY_ACCESS
    }

    private fun CallSummary.isCoveredByApplicableWildcard(wildcard: CallSummary): Boolean {
        val summary = summaryEdges.singleOrNull() as? TraceSummaryEdge.MethodSummary ?: return false
        val wildcardSummary = wildcard.summaryEdges.singleOrNull() as? TraceSummaryEdge.MethodSummary ?: return false
        if (summary.edgeAfter != wildcardSummary.edgeAfter) return false

        val edge = summaryTrace.final.edges.singleOrNull() as? TraceEdge.MethodTraceEdge ?: return false
        val wildcardEdge = wildcard.summaryTrace.final.edges.singleOrNull() as? TraceEdge.MethodTraceEdge ?: return false
        if (summaryTrace.method != wildcard.summaryTrace.method) return false
        if (summaryTrace.traceKind != wildcard.summaryTrace.traceKind) return false
        if (summaryTrace.final.statement != wildcard.summaryTrace.final.statement) return false
        if (edge.fact != wildcardEdge.fact) return false

        val initial = summary.delta?.initialFact as? BaseOnlyInitialFactAp ?: return false
        val wildcardInitial = wildcardSummary.delta?.initialFact as? BaseOnlyInitialFactAp ?: return false
        if (initial.projectFieldToWildcard() != wildcardInitial) return false

        val callerFact = summary.edge.fact as? BaseOnlyInitialFactAp ?: return false
        val wildcardCallerFact = wildcardSummary.edge.fact as? BaseOnlyInitialFactAp ?: return false
        if (callerFact.projectFieldToWildcard() != wildcardCallerFact) return false
        return summary.edge.replaceFact(wildcardCallerFact) == wildcardSummary.edge
    }

    private fun BaseOnlyInitialFactAp.projectFieldToWildcard(): BaseOnlyInitialFactAp? {
        val generalizedAccess = access.eraseFieldForSummaryGeneralization() ?: return null
        return BaseOnlyInitialFactAp(manager, base, generalizedAccess, exclusions)
    }

    private fun addWeakestEntry(entry: CallSummary, selectedEntries: LinkedList<CallSummary>) {
        val entryFact = entry.edges.single().fact
        val iter = selectedEntries.listIterator()

        while (iter.hasNext()) {
            val selectedEntry = iter.next()
            val selectedFact = selectedEntry.edges.single().fact

            // Entry fact is stronger than already added selected fact
            if (entryFact.contains(selectedFact)) {
                return
            }

            // Selected fact is stronger
            if (selectedFact.contains(entryFact)) {
                iter.remove()
            }
        }

        selectedEntries.add(entry)
    }

    private fun MutableList<CallSummary>.addCallSummaryEntry(
        currentTraceEdge: TraceEdge,
        precondition: InitialFactAp,
        preconditionDelta: InitialFactAp.Delta,
        callee: MethodEntryPoint,
        summaryFinalFact: InitialFactAp,
        summaryEdge: FactToFact,
    ) {
        val mappedFinalFact = summaryFinalFact
            .rebase(summaryEdge.factAp.base)
            .replaceExclusions(summaryEdge.factAp.exclusions)

        val traceSummaryEdge = TraceEdge.MethodTraceEdge(summaryEdge.initialFactAp, mappedFinalFact)
        val calleeTrace = SummaryTrace(
            final = TraceEntry.Final(setOf(traceSummaryEdge), summaryEdge.statement),
            method = callee,
            traceKind = TraceKind.SummaryTrace,
        )

        val callSummary = TraceSummaryEdge.MethodSummary(
            currentTraceEdge.replaceFact(precondition),
            currentTraceEdge,
            TraceSummaryEdge.TraceSummaryDelta(summaryEdge.initialFactAp, preconditionDelta)
        )

        this += CallSummary(setOf(callSummary), calleeTrace)
    }

    private fun methodEntryPoints(method: MethodWithContext): Sequence<MethodEntryPoint> =
        runner.graph.methodGraph(method.method).entryPoints().map { MethodEntryPoint(method.ctx, it) }

    private fun TraceBuilder.containsEntryEdge(entryStatement: CommonInst, entryEdge: TraceEdge): Boolean {
        when (entryEdge) {
            is TraceEdge.SourceTraceEdge -> {
                val entryFacts = cache.zeroEntryFacts(entryStatement, entryEdge.fact.base) {
                    edges.allZeroToFactFactsAtStatement(entryStatement, entryEdge.fact)
                }
                return entryFacts.any { statementFact -> statementFact.contains(entryEdge.fact) }
            }

            is TraceEdge.MethodTraceEdge -> {
                val entryFacts = edges.allFactToFactFactsAtStatement(entryStatement, entryEdge.initialFact, entryEdge.fact)
                return entryFacts.any { statementFact -> statementFact.contains(entryEdge.fact) }
            }

            is TraceEdge.MethodTraceNDEdge -> {
                val entryFacts = edges.allNDFactToFactFactsAtStatement(entryStatement, entryEdge.initialFacts, entryEdge.fact)
                return entryFacts.any { statementFact -> statementFact.contains(entryEdge.fact) }
            }
        }
    }

    private fun TraceBuilder.containsEntryEdgeCached(
        entryStatement: CommonInst,
        entryEdge: TraceEdge,
    ): Boolean = cache.containsEntryEdge(entryStatement, entryEdge) {
        containsEntryEdge(entryStatement, entryEdge)
    }

    private fun TraceBuilder.debugTrace(): FullStart2FinalTrace {
        val successors = successors()
        val additionalSuccessors = Int2ObjectOpenHashMap<CompactIntSet>()

        val fakeStartEntry = TraceEntry.SourceStartEntry(null, emptySet(), methodEntryPoint.statement)
        val fakeStartId = entryManager.entryId(fakeStartEntry)
        val startSuccessors = CompactIntSet().also { additionalSuccessors.put(fakeStartId, it) }

        val allEntries = predecessors.keys.toBitSet { it }
        predecessors.values.forEach { pred ->
            pred.forEach { allEntries.set(it) }
        }

        allEntries.forEach { entryId ->
            if (predecessors[entryId]?.let { it.size == 0 } == false) return@forEach

            val entry = entryManager.entryById(entryId)
            graph.forEachPredecessor(analysisManager, entry.statement) { p ->
                val fakePredecessor = TraceEntry.SourceStartEntry(null, emptySet(), p)
                val fakePredId = entryManager.entryId(fakePredecessor)
                startSuccessors.add(fakePredId)
                additionalSuccessors.computeIfAbsent(fakePredId) { CompactIntSet() }.add(entryId)
            }
        }

        successors.putAll(additionalSuccessors)

        val actionVariants = Int2ObjectOpenHashMap<List<ActionVariant>>()
        unsafeActionVariants().forEachIntEntry { key, value ->
            actionVariants.put(key, value.toList())
        }

        return FullStart2FinalTrace(
            methodEntryPoint,
            entryManager.entries.toTypedArray(),
            actionVariants,
            fakeStartId, finalEntryId, successors, TraceKind.TraceToFact
        )
    }

    companion object {
        private val logger = object : KLogging() {}.logger
        private const val TRACE_RESOLUTION_ACTION_HARD_LIMIT = 10_000

    }
}

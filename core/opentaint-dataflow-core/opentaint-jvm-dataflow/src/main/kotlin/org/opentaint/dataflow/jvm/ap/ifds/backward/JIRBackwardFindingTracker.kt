package org.opentaint.dataflow.jvm.ap.ifds.backward

import org.opentaint.dataflow.ap.ifds.BackwardSinkOccurrence
import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.configuration.jvm.TaintConfigurationSink
import org.opentaint.dataflow.taint.TaintMarkAwareConditionExpr
import org.opentaint.ir.api.jvm.JIRMethod
import org.opentaint.ir.api.jvm.cfg.JIRInst
import java.util.concurrent.ConcurrentHashMap

class JIRBackwardFindingTracker {
    data class BackwardSeededSink(
        val methodEntryPoint: MethodEntryPoint,
        val statement: JIRInst,
        val rule: TaintConfigurationSink,
        val condition: TaintMarkAwareConditionExpr?,
        val endRequirement: JIRBackwardEndRequirement?,
    ) {
        val occurrence: BackwardSinkOccurrence get() = BackwardSinkOccurrence(rule, statement)

        fun demandedMarks(): Set<TaintMarkAccessor> {
            val marks = hashSetOf<TaintMarkAccessor>()
            condition?.collectMarks(marks)
            endRequirement?.let { marks += it.mark }
            return marks
        }
    }

    data class BackwardConditionalSource(
        val marks: Set<TaintMarkAccessor>,
        val condition: TaintMarkAwareConditionExpr,
    )

    data class BackwardEndRequirementReached(
        val statement: JIRInst,
        val rule: TaintConfigurationSink,
    )

    private val sourceMarks = ConcurrentHashMap.newKeySet<TaintMarkAccessor>()
    private val seededSinks = ConcurrentHashMap.newKeySet<BackwardSeededSink>()
    private val conditionalSources = ConcurrentHashMap.newKeySet<BackwardConditionalSource>()
    private val endRequirementsReached = ConcurrentHashMap.newKeySet<BackwardEndRequirementReached>()
    private val zeroEdgeOnlySinks = ConcurrentHashMap.newKeySet<BackwardSinkOccurrence>()

    @Volatile
    var restrictedTo: Set<BackwardSinkOccurrence>? = null
        private set

    @Volatile
    private var endRequirementTargets: Map<JIRInst, List<TaintConfigurationSink>> = emptyMap()

    private val zeroEdgeDemandsKept = ConcurrentHashMap<JIRMethod, Boolean>()

    fun configureRun(restrictedTo: Set<BackwardSinkOccurrence>?) {
        this.restrictedTo = restrictedTo
        endRequirementTargets = restrictedTo.orEmpty()
            .filter { (it.rule as TaintConfigurationSink).trackFactsReachAnalysisEnd.isNotEmpty() }
            .groupBy({ it.statement as JIRInst }, { it.rule as TaintConfigurationSink })
        zeroEdgeDemandsKept.clear()
    }

    fun keepsZeroEdgeDemands(method: JIRMethod, compute: () -> Boolean): Boolean =
        zeroEdgeDemandsKept.computeIfAbsent(method) { compute() }

    val hasEndRequirementTargets: Boolean get() = endRequirementTargets.isNotEmpty()

    fun endRequirementTargets(statement: JIRInst): List<TaintConfigurationSink> =
        endRequirementTargets[statement].orEmpty()

    fun acceptsSeed(statement: JIRInst, rule: TaintConfigurationSink): Boolean {
        val restricted = restrictedTo ?: return true
        return BackwardSinkOccurrence(rule, statement) in restricted
    }

    fun addSourceMarks(marks: Set<TaintMarkAccessor>) {
        sourceMarks.addAll(marks)
    }

    fun addSeededSink(sink: BackwardSeededSink) {
        seededSinks.add(sink)
    }

    fun addConditionalSource(source: BackwardConditionalSource) {
        conditionalSources.add(source)
    }

    fun addEndRequirementReached(reached: BackwardEndRequirementReached) {
        endRequirementsReached.add(reached)
    }

    fun addZeroEdgeOnlySink(occurrence: BackwardSinkOccurrence) {
        zeroEdgeOnlySinks.add(occurrence)
    }

    fun seededSinks(): List<BackwardSeededSink> = seededSinks.toList()

    val hasZeroEdgeOnlySinks: Boolean get() = zeroEdgeOnlySinks.isNotEmpty()

    private fun satisfiedMarks(): Set<TaintMarkAccessor> {
        val satisfied = sourceMarks.toHashSet()
        val pending = conditionalSources.toMutableList()

        var changed = true
        while (changed) {
            changed = false
            val iter = pending.iterator()
            while (iter.hasNext()) {
                val source = iter.next()
                if (!source.condition.holds(satisfied)) continue

                iter.remove()
                if (satisfied.addAll(source.marks)) changed = true
            }
        }

        return satisfied
    }

    fun vulnerableSinks(checkEndRequirements: Boolean): List<BackwardSeededSink> {
        val satisfied = satisfiedMarks()
        val reached = endRequirementsReached.mapTo(hashSetOf()) { it.rule to it.statement }
        return seededSinks.filter { sink ->
            val conditionHolds = sink.condition?.holds(satisfied) ?: true
            val requirementHolds = !checkEndRequirements || sink.endRequirement == null ||
                (sink.rule to sink.statement) in reached
            conditionHolds && requirementHolds
        }
    }

    fun reset() {
        sourceMarks.clear()
        seededSinks.clear()
        conditionalSources.clear()
        endRequirementsReached.clear()
        zeroEdgeOnlySinks.clear()
    }

    companion object {
        fun TaintMarkAwareConditionExpr.collectMarks(marks: MutableSet<TaintMarkAccessor>) {
            when (this) {
                is TaintMarkAwareConditionExpr.And -> args.forEach { it.collectMarks(marks) }
                is TaintMarkAwareConditionExpr.Or -> args.forEach { it.collectMarks(marks) }
                is TaintMarkAwareConditionExpr.ContainsMarkLiteral -> if (!negated) marks += mark
                is TaintMarkAwareConditionExpr.ContainsMarkOnAnyAccessorLiteral -> if (!negated) marks += mark
            }
        }

        fun TaintMarkAwareConditionExpr.holds(satisfied: Set<TaintMarkAccessor>): Boolean = when (this) {
            is TaintMarkAwareConditionExpr.And -> args.all { it.holds(satisfied) }
            is TaintMarkAwareConditionExpr.Or -> args.any { it.holds(satisfied) }
            is TaintMarkAwareConditionExpr.ContainsMarkLiteral -> negated || mark in satisfied
            is TaintMarkAwareConditionExpr.ContainsMarkOnAnyAccessorLiteral -> negated || mark in satisfied
        }
    }
}

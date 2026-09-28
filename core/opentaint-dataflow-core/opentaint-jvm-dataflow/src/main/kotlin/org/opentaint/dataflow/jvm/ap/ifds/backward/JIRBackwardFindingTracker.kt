package org.opentaint.dataflow.jvm.ap.ifds.backward

import org.opentaint.dataflow.ap.ifds.BackwardSinkOccurrence
import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.configuration.jvm.TaintConfigurationSink
import org.opentaint.dataflow.configuration.jvm.TaintConfigurationSource
import org.opentaint.dataflow.taint.TaintMarkAwareConditionExpr
import org.opentaint.ir.api.jvm.cfg.JIRInst
import java.util.concurrent.ConcurrentHashMap

class JIRBackwardFindingTracker(private val recordDemandSeeds: Boolean = false) {
    data class BackwardSourceFinding(
        val methodEntryPoint: MethodEntryPoint,
        val statement: JIRInst,
        val rule: TaintConfigurationSource,
        val mark: TaintMarkAccessor,
    )

    data class BackwardUnconditionalSink(
        val methodEntryPoint: MethodEntryPoint,
        val statement: JIRInst,
        val rule: TaintConfigurationSink,
    )

    data class BackwardDemandSeed(
        val methodEntryPoint: MethodEntryPoint,
        val statement: JIRInst,
        val rule: TaintConfigurationSink,
        val fact: FinalFactAp,
    )

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
        val methodEntryPoint: MethodEntryPoint,
        val statement: JIRInst,
        val rule: TaintConfigurationSource,
        val marks: Set<TaintMarkAccessor>,
        val condition: TaintMarkAwareConditionExpr,
    )

    data class BackwardEndRequirementReached(
        val statement: JIRInst,
        val rule: TaintConfigurationSink,
    )

    private val sourceFindings = ConcurrentHashMap.newKeySet<BackwardSourceFinding>()
    private val unconditionalSinks = ConcurrentHashMap.newKeySet<BackwardUnconditionalSink>()
    private val demandSeeds = ConcurrentHashMap.newKeySet<BackwardDemandSeed>()
    private val seededSinks = ConcurrentHashMap.newKeySet<BackwardSeededSink>()
    private val conditionalSources = ConcurrentHashMap.newKeySet<BackwardConditionalSource>()
    private val endRequirementsReached = ConcurrentHashMap.newKeySet<BackwardEndRequirementReached>()

    @Volatile
    var restrictedTo: Set<BackwardSinkOccurrence>? = null
        private set

    @Volatile
    private var endRequirementTargets: Map<JIRInst, List<TaintConfigurationSink>> = emptyMap()

    fun configureRun(restrictedTo: Set<BackwardSinkOccurrence>?) {
        this.restrictedTo = restrictedTo
        endRequirementTargets = restrictedTo.orEmpty()
            .filter { (it.rule as TaintConfigurationSink).trackFactsReachAnalysisEnd.isNotEmpty() }
            .groupBy({ it.statement as JIRInst }, { it.rule as TaintConfigurationSink })
    }

    val hasEndRequirementTargets: Boolean get() = endRequirementTargets.isNotEmpty()

    fun endRequirementTargets(statement: JIRInst): List<TaintConfigurationSink> =
        endRequirementTargets[statement].orEmpty()

    fun acceptsSeed(statement: JIRInst, rule: TaintConfigurationSink): Boolean {
        val restricted = restrictedTo ?: return true
        return BackwardSinkOccurrence(rule, statement) in restricted
    }

    fun addSourceFinding(finding: BackwardSourceFinding) {
        sourceFindings.add(finding)
    }

    fun addUnconditionalSink(finding: BackwardUnconditionalSink) {
        unconditionalSinks.add(finding)
    }

    fun addDemandSeed(seed: BackwardDemandSeed) {
        if (!recordDemandSeeds) return
        demandSeeds.add(seed)
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

    fun sourceFindings(): List<BackwardSourceFinding> = sourceFindings.toList()

    fun unconditionalSinks(): List<BackwardUnconditionalSink> = unconditionalSinks.toList()

    fun demandSeeds(): List<BackwardDemandSeed> = demandSeeds.toList()

    fun seededSinks(): List<BackwardSeededSink> = seededSinks.toList()

    fun conditionalSources(): List<BackwardConditionalSource> = conditionalSources.toList()

    fun endRequirementsReached(): List<BackwardEndRequirementReached> = endRequirementsReached.toList()

    fun satisfiedMarks(): Set<TaintMarkAccessor> {
        val satisfied = sourceFindings.mapTo(hashSetOf()) { it.mark }
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
        sourceFindings.clear()
        unconditionalSinks.clear()
        demandSeeds.clear()
        seededSinks.clear()
        conditionalSources.clear()
        endRequirementsReached.clear()
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

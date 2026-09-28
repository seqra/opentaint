package org.opentaint.dataflow.jvm.ap.ifds.backward

import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.taint.TaintSinkTracker
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
        val zeroEdgeOnly: Boolean,
        val sinkTracker: TaintSinkTracker,
    ) {
        val occurrence: Pair<JIRInst, TaintConfigurationSink> get() = statement to rule

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

    @Volatile
    var endRequirementTargets: Map<JIRInst, List<TaintConfigurationSink>> = emptyMap()
        private set

    @Volatile
    private var zeroEdgeDemandsDroppedAt: JIRMethod? = null

    fun configureRun(
        endRequirementTargets: Map<JIRInst, List<TaintConfigurationSink>>,
        zeroEdgeDemandsDroppedAt: JIRMethod?,
    ) {
        this.endRequirementTargets = endRequirementTargets
        this.zeroEdgeDemandsDroppedAt = zeroEdgeDemandsDroppedAt
        reset()
    }

    fun keepsZeroEdgeDemands(method: JIRMethod): Boolean = method != zeroEdgeDemandsDroppedAt

    fun endRequirementTargets(statement: JIRInst): List<TaintConfigurationSink> =
        endRequirementTargets[statement].orEmpty()

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

    fun seededSinks(): List<BackwardSeededSink> = seededSinks.toList()

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

    private fun reset() {
        sourceMarks.clear()
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

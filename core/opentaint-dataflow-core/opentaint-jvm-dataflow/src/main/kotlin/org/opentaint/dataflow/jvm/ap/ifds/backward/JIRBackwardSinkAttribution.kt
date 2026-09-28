package org.opentaint.dataflow.jvm.ap.ifds.backward

import mu.KLogging
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.configuration.jvm.TaintConfigurationSink
import org.opentaint.dataflow.jvm.ap.ifds.backward.JIRBackwardFindingTracker.BackwardSeededSink
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.jvm.cfg.JIRInst
import kotlin.time.Duration

private typealias SinkOccurrence = Pair<JIRInst, TaintConfigurationSink>

class JIRBackwardSinkAttribution(
    private val findings: JIRBackwardFindingTracker,
    private val sinkSelection: JIRBackwardSinkSelection,
) {
    private class RunResult(
        val seeded: Map<SinkOccurrence, Set<TaintMarkAccessor>>,
        val vulnerable: Map<SinkOccurrence, BackwardSeededSink>,
        val exact: Boolean,
    )

    private enum class Stage { START, DISCOVERY, GROUPS, CANDIDATES, DONE }

    private var stage = Stage.START
    private var restrictedTo: Set<SinkOccurrence>? = null
    private var index = 0

    private lateinit var discovery: RunResult
    private var zeroEdgeOnly: Set<SinkOccurrence> = emptySet()
    private var groups: List<List<SinkOccurrence>> = emptyList()
    private var groupShare = 1.0
    private val candidates = linkedMapOf<SinkOccurrence, BackwardSeededSink>()
    private var pending: List<Pair<SinkOccurrence, BackwardSeededSink>> = emptyList()
    private val reported = hashMapOf<SinkOccurrence, BackwardSeededSink>()

    fun nextRun(timeLeft: Duration): Duration? = when (stage) {
        Stage.START -> {
            stage = Stage.DISCOVERY
            select(null)
            timeLeft * 0.5
        }

        Stage.DISCOVERY -> {
            finishDiscovery(runResult())
            nextGroup(timeLeft)
        }

        Stage.GROUPS -> {
            val result = runResult()
            if (result.exact) reported += result.vulnerable else candidates += result.vulnerable
            index++
            nextGroup(timeLeft)
        }

        Stage.CANDIDATES -> {
            val candidate = pending[index].first
            runResult().vulnerable[candidate]?.let { reported[candidate] = it }
            index++
            nextCandidate(timeLeft)
        }

        Stage.DONE -> null
    }

    private fun finishDiscovery(result: RunResult) {
        discovery = result
        zeroEdgeOnly = findings.seededSinks().filter { it.zeroEdgeOnly }.mapTo(hashSetOf()) { it.occurrence }
        if (result.exact) reported += result.vulnerable
        groups = if (result.exact) emptyList() else groupByDisjointMarks(result.seeded)
        groupShare = if (groups.any { it.size > 1 }) 0.5 else 1.0
        stage = Stage.GROUPS
        index = 0
    }

    private fun nextGroup(timeLeft: Duration): Duration? {
        if (index < groups.size) {
            if (timeLeft.isPositive()) {
                select(groups[index].toSet())
                return timeLeft * groupShare / (groups.size - index)
            }
            groups.drop(index).flatten().forEach { o -> discovery.vulnerable[o]?.let { reported[o] = it } }
        }

        stage = Stage.CANDIDATES
        pending = candidates.toList()
        index = 0
        return nextCandidate(timeLeft)
    }

    private fun nextCandidate(timeLeft: Duration): Duration? {
        if (index < pending.size) {
            if (timeLeft.isPositive()) {
                select(setOf(pending[index].first))
                return timeLeft / (pending.size - index)
            }
            pending.drop(index).forEach { reported[it.first] = it.second }
        }

        stage = Stage.DONE
        logger.info { "Backward sink attribution: ${discovery.seeded.size} sinks, ${reported.size} vulnerable" }
        for (sink in reported.values) {
            sink.sinkTracker.addUnconditionalVulnerability(sink.methodEntryPoint, sink.statement, sink.rule)
        }
        return null
    }

    private fun select(occurrences: Set<SinkOccurrence>?) {
        restrictedTo = occurrences
        sinkSelection.selected = occurrences
            ?.groupBy<SinkOccurrence, CommonInst, TaintConfigurationSink>({ it.first }, { it.second })
            ?.mapValues { it.value.toSet() }

        val endRequirementTargets = occurrences.orEmpty()
            .filter { it.second.trackFactsReachAnalysisEnd.isNotEmpty() }
            .groupBy({ it.first }, { it.second })
        val zeroEdgeDemandsDroppedAt = occurrences
            ?.takeIf { it.isNotEmpty() && it.all { occurrence -> occurrence in zeroEdgeOnly } }
            ?.mapTo(hashSetOf()) { it.first.location.method }
            ?.singleOrNull()
        findings.configureRun(endRequirementTargets, zeroEdgeDemandsDroppedAt)
    }

    private fun runResult(): RunResult {
        val restricted = restrictedTo
        val seededSinks = findings.seededSinks()

        val seeded = hashMapOf<SinkOccurrence, MutableSet<TaintMarkAccessor>>()
        seededSinks.forEach { seeded.getOrPut(it.occurrence, ::hashSetOf).addAll(it.demandedMarks()) }

        val vulnerable = hashMapOf<SinkOccurrence, BackwardSeededSink>()
        findings.vulnerableSinks(checkEndRequirements = restricted != null).forEach {
            vulnerable.putIfAbsent(it.occurrence, it)
        }

        val exact = restricted?.let { it.size <= 1 }
            ?: (seeded.size <= 1 && seededSinks.all { it.endRequirement == null } && seededSinks.none { it.zeroEdgeOnly })
        return RunResult(seeded, vulnerable, exact)
    }

    private fun groupByDisjointMarks(
        occurrences: Map<SinkOccurrence, Set<TaintMarkAccessor>>,
    ): List<List<SinkOccurrence>> {
        val groups = mutableListOf<Pair<MutableList<SinkOccurrence>, MutableSet<TaintMarkAccessor>>>()
        val ordered = occurrences.entries.sortedBy { (occurrence, _) ->
            val (statement, rule) = occurrence
            "${statement.location.method}#${statement.location.index}#${rule.id}"
        }

        for ((occurrence, marks) in ordered) {
            val group = groups.firstOrNull { (_, used) -> marks.none { it in used } }
            if (group != null) {
                group.first += occurrence
                group.second += marks
            } else {
                groups += mutableListOf(occurrence) to marks.toHashSet()
            }
        }
        return groups.map { it.first }
    }

    companion object : KLogging()
}

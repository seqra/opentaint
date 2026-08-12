package org.opentaint.dataflow.ap.ifds

import org.opentaint.ir.api.common.CommonMethod
import java.util.BitSet
import kotlin.time.Duration.Companion.nanoseconds

data class UnitRunnerStats(val processed: Long, val enqueued: Long)

class MethodStats {
    val stats = hashMapOf<CommonMethod, Stats>()

    fun subtract(other: MethodStats): MethodStats {
        val result = MethodStats()
        for ((m, s) in stats) {
            val otherS = other.stats[m]
            val subS = otherS?.let { os -> s.copy().apply { subtract(os) } } ?: s
            result.stats[m] = subS
        }
        return result
    }

    fun stats(method: CommonMethod): Stats = stats.getOrPut(method) {
        Stats(
            method,
            steps = 0,
            unprocessedEdges = 0,
            handledSummaries = 0,
            sourceSummaries = 0,
            passSummaries = 0,
            traceResolverSteps = 0,
            ndSummaryAnchorDeliveries = 0,
            ndSummaryUniqueEmissions = 0,
            ndSummaryDuplicateEmissions = 0,
            transparentClosureQueries = 0,
            transparentClosureHits = 0,
            transparentClosureStatements = 0,
            transparentClosureMaxSupport = 0,
            transparentF2FGroups = 0,
            transparentF2FEdges = 0,
            transparentF2FMaxGroup = 0,
            baseOnlyF2FGroupKinds = BaseOnlyF2FGroupKindStats(),
            transparentGroupedStatements = 0,
            transparentGroupedEdges = 0,
            transparentGroupedInitials = 0,
            baseOnlyF2FTransferQueries = 0,
            baseOnlyF2FTransferHits = 0,
            baseOnlyF2FCallTransferGroups = 0,
            baseOnlyF2FCallTransferEdges = 0,
            analysisTime = 0,
            stepTime = 0,
            summaryTime = 0,
            callTime = 0,
            otherTime = 0,
        )
    }

    data class Stats(
        val method: CommonMethod,
        var steps: Long,
        var unprocessedEdges: Long,
        var handledSummaries: Long,
        var sourceSummaries: Long,
        var passSummaries: Long,
        var traceResolverSteps: Long,
        var ndSummaryAnchorDeliveries: Long,
        var ndSummaryUniqueEmissions: Long,
        var ndSummaryDuplicateEmissions: Long,
        var transparentClosureQueries: Long,
        var transparentClosureHits: Long,
        var transparentClosureStatements: Long,
        var transparentClosureMaxSupport: Int,
        var transparentF2FGroups: Long,
        var transparentF2FEdges: Long,
        var transparentF2FMaxGroup: Int,
        val baseOnlyF2FGroupKinds: BaseOnlyF2FGroupKindStats,
        var transparentGroupedStatements: Long,
        var transparentGroupedEdges: Long,
        var transparentGroupedInitials: Long,
        var baseOnlyF2FTransferQueries: Long,
        var baseOnlyF2FTransferHits: Long,
        var baseOnlyF2FCallTransferGroups: Long,
        var baseOnlyF2FCallTransferEdges: Long,
        var analysisTime: Long,
        var stepTime: Long,
        var summaryTime: Long,
        var callTime: Long,
        var otherTime: Long,
    ) {
        val stepsForTaintMark: MutableMap<String, Long> = hashMapOf()
        val coveredInstructions = BitSet()

        fun subtract(other: Stats) {
            steps -= other.steps
            unprocessedEdges -= other.unprocessedEdges
            handledSummaries -= other.handledSummaries
            sourceSummaries -= other.sourceSummaries
            passSummaries -= other.passSummaries
            traceResolverSteps -= other.traceResolverSteps
            ndSummaryAnchorDeliveries -= other.ndSummaryAnchorDeliveries
            ndSummaryUniqueEmissions -= other.ndSummaryUniqueEmissions
            ndSummaryDuplicateEmissions -= other.ndSummaryDuplicateEmissions
            transparentClosureQueries -= other.transparentClosureQueries
            transparentClosureHits -= other.transparentClosureHits
            transparentClosureStatements -= other.transparentClosureStatements
            transparentClosureMaxSupport = maxOf(transparentClosureMaxSupport, other.transparentClosureMaxSupport)
            transparentF2FGroups -= other.transparentF2FGroups
            transparentF2FEdges -= other.transparentF2FEdges
            transparentF2FMaxGroup = maxOf(transparentF2FMaxGroup, other.transparentF2FMaxGroup)
            baseOnlyF2FGroupKinds.subtract(other.baseOnlyF2FGroupKinds)
            transparentGroupedStatements -= other.transparentGroupedStatements
            transparentGroupedEdges -= other.transparentGroupedEdges
            transparentGroupedInitials -= other.transparentGroupedInitials
            baseOnlyF2FTransferQueries -= other.baseOnlyF2FTransferQueries
            baseOnlyF2FTransferHits -= other.baseOnlyF2FTransferHits
            baseOnlyF2FCallTransferGroups -= other.baseOnlyF2FCallTransferGroups
            baseOnlyF2FCallTransferEdges -= other.baseOnlyF2FCallTransferEdges
            analysisTime -= other.analysisTime
            stepTime -= other.stepTime
            summaryTime -= other.summaryTime
            callTime -= other.callTime
            otherTime -= other.otherTime
        }

        override fun toString(): String = buildString {
            append(method)
            append(" | ")
            append("steps: $steps")
            append(" | ")
            append("unp: $unprocessedEdges")
            append(" | ")
            append("sum: $handledSummaries")
            append(" | ")
            append("source: $sourceSummaries")
            append(" | ")
            append("pass: $passSummaries")

            if (analysisTime > 0) {
                append(" | ")
                append("AT: ${analysisTime.nanoseconds.inWholeMilliseconds}")
                append(" | ")
                append("StT: ${stepTime.nanoseconds.inWholeMilliseconds}")
                append(" | ")
                append("SuT: ${summaryTime.nanoseconds.inWholeMilliseconds}")
                append(" | ")
                append("CT: ${callTime.nanoseconds.inWholeMilliseconds}")
                append(" | ")
                append("OT: ${otherTime.nanoseconds.inWholeMilliseconds}")
            }

            if (traceResolverSteps > 0) {
                append(" | ")
                append("trace: $traceResolverSteps")
            }

            if (ndSummaryAnchorDeliveries > 0) {
                append(" | ")
                append("nd: $ndSummaryAnchorDeliveries/$ndSummaryUniqueEmissions/$ndSummaryDuplicateEmissions")
            }

            if (transparentClosureQueries > 0) {
                append(" | closure: $transparentClosureHits/$transparentClosureQueries/$transparentClosureStatements/$transparentClosureMaxSupport")
                append(" | F2F batch: $transparentF2FGroups/$transparentF2FEdges/$transparentF2FMaxGroup")
                append(" | F2F kinds: $baseOnlyF2FGroupKinds")
                append(" | transparent: $transparentGroupedStatements/$transparentGroupedEdges/$transparentGroupedInitials")
            }

            if (baseOnlyF2FTransferQueries > 0) {
                append(" | F2F transfer: $baseOnlyF2FTransferHits/$baseOnlyF2FTransferQueries")
            }
            if (baseOnlyF2FCallTransferGroups > 0) {
                append(" | F2F call identity: $baseOnlyF2FCallTransferGroups/$baseOnlyF2FCallTransferEdges")
            }
        }
    }
}

class BaseOnlyF2FGroupKindStats {
    private val rejected = GroupStats()
    private val call = GroupStats()
    private val sequential = GroupStats()

    fun recordRejected(size: Int) = rejected.record(size)

    fun recordCall(size: Int) = call.record(size)

    fun recordSequential(size: Int) = sequential.record(size)

    fun add(other: BaseOnlyF2FGroupKindStats) {
        rejected.add(other.rejected)
        call.add(other.call)
        sequential.add(other.sequential)
    }

    fun subtract(other: BaseOnlyF2FGroupKindStats) {
        rejected.subtract(other.rejected)
        call.subtract(other.call)
        sequential.subtract(other.sequential)
    }

    override fun toString(): String = "rejected=$rejected,call=$call,sequential=$sequential"

    private class GroupStats {
        private var groups = 0L
        private var edges = 0L
        private var maxGroup = 0
        private val buckets = LongArray(6)

        fun record(size: Int) {
            groups++
            edges += size
            maxGroup = maxOf(maxGroup, size)
            buckets[when (size) {
                1 -> 0
                2 -> 1
                in 3..4 -> 2
                in 5..8 -> 3
                in 9..16 -> 4
                else -> 5
            }]++
        }

        fun add(other: GroupStats) {
            groups += other.groups
            edges += other.edges
            maxGroup = maxOf(maxGroup, other.maxGroup)
            buckets.indices.forEach { buckets[it] += other.buckets[it] }
        }

        fun subtract(other: GroupStats) {
            groups -= other.groups
            edges -= other.edges
            maxGroup = maxOf(maxGroup, other.maxGroup)
            buckets.indices.forEach { buckets[it] -= other.buckets[it] }
        }

        override fun toString(): String = buildString {
            append(groups)
            append('/')
            append(edges)
            append('/')
            append(maxGroup)
            append('/')
            append(buckets.joinToString(","))
        }
    }
}

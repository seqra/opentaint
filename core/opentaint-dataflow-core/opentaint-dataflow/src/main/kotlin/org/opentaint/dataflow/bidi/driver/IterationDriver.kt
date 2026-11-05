package org.opentaint.dataflow.bidi.driver

import mu.KLogging
import org.opentaint.dataflow.bidi.ap.Direction
import org.opentaint.dataflow.bidi.ap.MethodKey
import org.opentaint.dataflow.bidi.ap.MarkMode
import org.opentaint.dataflow.bidi.ap.TaintMark
import org.opentaint.dataflow.bidi.engine.MethodCallServicesFactory
import org.opentaint.dataflow.bidi.engine.MethodLocalServicesFactory
import org.opentaint.dataflow.bidi.engine.RunConfig
import org.opentaint.dataflow.bidi.engine.RunManager
import org.opentaint.dataflow.bidi.engine.LoopPipelineTrace
import org.opentaint.dataflow.bidi.engine.RunMethodAnalyzer
import org.opentaint.dataflow.bidi.engine.RunMethodCallServices
import org.opentaint.dataflow.bidi.engine.RunMethodHandlers
import org.opentaint.dataflow.bidi.engine.RunMethodLocalServices
import org.opentaint.dataflow.bidi.engine.RunResult
import org.opentaint.dataflow.bidi.engine.RunStatus
import org.opentaint.dataflow.bidi.engine.SharedObjects
import org.opentaint.dataflow.bidi.engine.readRun1MarkMode
import org.opentaint.dataflow.bidi.store.RelationCensus
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.MemoryManager
import java.util.Collections
import kotlin.time.Duration
import kotlin.time.TimeSource

/** Runs fresh engines in sequence and reads their stores only after all runners join. */
class IterationDriver internal constructor(
    private val policy: IterationPolicy,
    private val shared: SharedObjects,
    private val budget: Duration,
    private val invokeRun: (RunConfig, SharedObjects, Duration) -> RunResult<RunMethodAnalyzer>,
    private val guardBarrier: (SharedObjects, () -> Next) -> Next,
) {
    constructor(policy: IterationPolicy, shared: SharedObjects, budget: Duration) :
        this(policy, shared, budget, ::runEngine, ::withBarrierGuard)

    private val run1MarkMode = readRun1MarkMode()
    private val fieldLimitSchedule = policy.fieldLimitSchedule
    private val frontierLog = ArrayList<Frontier>()
    val frontiers: List<Frontier> get() = Collections.unmodifiableList(ArrayList(frontierLog))

    fun analyze(roots: List<MethodKey>): Report {
        val start = TimeSource.Monotonic.markNow()
        val report = ReportBuilder()
        var index = 1
        fun end(status: RunStatus, reason: EndReason): Report {
            logger.info { "BIDI_ANALYSIS_END run=$index status=$status reason=$reason elapsed=${start.elapsedNow()}" }
            return report.build(AnalysisEnd(status, index,
                if (index % 2 == 1) Direction.FORWARD else Direction.BACKWARD, reason, run1MarkMode))
        }
        try {
            logger.info { "BIDI_FIELD_LIMIT_SCHEDULE schedule=$fieldLimitSchedule" }
            val firstLimit = policy.fieldLimit(1)
            require(firstLimit == 1) { "F78: selected run 1 needs field limit exactly 1" }
            var config = RunConfig(1, firstLimit, demand = null, records = shared.records.view(),
                seeds = SeedIndex.EMPTY, roots = roots, run1MarkMode = run1MarkMode,
                fieldLimitSchedule = fieldLimitSchedule)
            while (true) {
                index = config.index
                val selectedTimeout = policy.timeout(config, budget - start.elapsedNow())
                // The callback consumes this same budget and cannot extend it.
                val timeout = minOf(selectedTimeout, budget - start.elapsedNow())
                when (val next = runOnce(config, report, timeout)) {
                    is Next.Run -> config = next.config
                    is Next.End -> return end(next.status, next.reason)
                }
            }
        } catch (error: Throwable) {
            logger.error(error) { "Run $index failed; the analysis ends with the report so far" }
            return end(RunStatus.FAILED, EndReason.ABNORMAL)
        }
    }

    /** This frame releases its result before the next engine is created. */
    private fun runOnce(config: RunConfig, report: ReportBuilder, timeout: Duration): Next {
        val start = TimeSource.Monotonic.markNow()
        logger.info { "BIDI_RUN_START run=${config.index} direction=${config.direction} limit=${config.fieldLimit} timeout=$timeout markMode=${config.mode.markMode}" }
        logOptimizationStatistics(config, "START")
        val result = try {
            invokeRun(config, shared, timeout)
        } catch (error: Throwable) {
            logger.info { "BIDI_RUN_END run=${config.index} status=FAILED engineTime=${start.elapsedNow()}" }
            logOptimizationStatistics(config, "END")
            throw error
        } finally {
            // Diagnostic counters only. Engine workers have joined before this callback returns.
            LoopPipelineTrace.finishRun(config.index)
        }
        logger.info { "BIDI_JOINED_RELEASE run=${config.index} sealReleaseTime=${result.joinedSealReleaseTime} status=${result.status}" }
        val engineTime = (start.elapsedNow() - result.joinedStaticBindingTime).coerceAtLeast(Duration.ZERO)
        logger.info { "BIDI_RUN_END run=${config.index} status=${result.status} engineTime=$engineTime" }
        if (config.run1 && config.mode.markMode == MarkMode.FULL && result.status == RunStatus.COMPLETE) {
            logger.info { "BIDI_FLOW_BACKED_STATISTICS run=${config.index} neutralBatches=${result.analyzers.sumOf { it.neutralBatchApplications }} neutralMemberships=${result.analyzers.sumOf { it.neutralBatchMemberships }} bulkStorePackets=${result.analyzers.sumOf { it.neutralBulkStorePackets }} bulkStoreMemberships=${result.analyzers.sumOf { it.neutralBulkStoreMemberships }} scalarStoreFallbackMemberships=${result.analyzers.sumOf { it.neutralScalarFallbackMemberships }}" }
        }
        if (shared.n2Statistics != null && result.status == RunStatus.COMPLETE) {
            logger.info {
                "BIDI_CFG_DELIVERY_STATISTICS run=${config.index} hits=${result.analyzers.sumOf { it.cfgDeliveryHits }} " +
                    "searches=${result.analyzers.sumOf { it.cfgDeliverySearches }} " +
                    "visitedNodes=${result.analyzers.sumOf { it.cfgDeliveryVisitedNodes }} " +
                    "destinations=${result.analyzers.sumOf { it.cfgDeliveryDestinations }} " +
                    "maxWidth=${result.analyzers.maxOfOrNull { it.cfgDeliveryMaxWidth } ?: 0}"
            }
        }
        if (shared.n2Statistics != null) {
            val loopMethods = result.analyzers.mapNotNull { actor -> actor.blockDiagnostics()?.let { actor to it } }
            logger.info { "BIDI_LOOP_BLOCK_STATISTICS run=${config.index} methods=${loopMethods.size}" }
            for ((actor, summary) in loopMethods.sortedByDescending { it.first.steps }.take(24)) logger.info {
                "BIDI_LOOP_BLOCK_METHOD run=${config.index} method=${actor.key} $summary"
            }
            val measured = result.analyzers.mapNotNull { actor -> actor.bodyWorkSnapshot?.let { actor.key to it } }
            logger.info {
                "BIDI_BODY_WORK_STATISTICS run=${config.index} scope=packet-events " +
                    "snapshotActors=${measured.size} unavailableActors=${result.analyzers.size - measured.size} " +
                    "processed=${measured.sumOf { it.second.processedPackets }} " +
                    "freshPostS=${measured.sumOf { it.second.freshPackets }} " +
                    "candidateOffers=${measured.sumOf { it.second.candidatePackets }} " +
                    "methodCandidateOffers=${measured.sumOf { it.second.methodCandidatePackets }} " +
                    "blockCandidateOffers=${measured.sumOf { it.second.blockCandidatePackets }} " +
                    "cyclicProcessed=${measured.sumOf { it.second.cyclicProcessedPackets }} " +
                    "cyclicFreshPostS=${measured.sumOf { it.second.cyclicFreshPackets }} " +
                    "sampledPackets=${(0..2).map { stage -> measured.sumOf { it.second.sampledPackets[stage] } }} " +
                    "sampledMemberships=${(0..2).map { stage -> measured.sumOf { it.second.sampledMemberships[stage] } }} " +
                    "droppedSamples=${measured.sumOf { it.second.droppedSamples }}"
            }
            val hot = (measured.sortedByDescending { it.second.processedPackets }.take(12) +
                measured.sortedByDescending { it.second.candidatePackets }.take(12)).distinctBy { it.first }
            for ((method, snapshot) in hot) logger.info {
                "BIDI_BODY_WORK_METHOD run=${config.index} method=$method snapshot=$snapshot"
            }
            // Only copied IDs from bounded hot-method samples enter this read-only dictionary.
            val fieldIds = hot.asSequence().flatMap { it.second.samples.asSequence() }.flatMap { sample ->
                (sample.firstPath + sample.initials.flatMap { it.path }).asSequence()
            }.distinct().take(256).toList()
            val markIds = hot.asSequence().flatMap { it.second.samples.asSequence() }.flatMap { sample ->
                (sample.exampleMarkIds + sample.initials.mapNotNull { it.concreteMark }).asSequence()
            }.distinct().take(256).toList()
            for (id in fieldIds) logger.info {
                "BIDI_BODY_FIELD run=${config.index} id=$id accessor=${shared.ap.accessors.accessor(id)}"
            }
            for (id in markIds) logger.info {
                "BIDI_BODY_MARK run=${config.index} id=$id name=${shared.ap.marks.name(TaintMark(id))} key=${shared.ap.marks.key(TaintMark(id))}"
            }
            // These are scalar-store end-state gauges, not cumulative edge work.
            // Cancelled/live actors need a heap census; absent snapshots are not zero.
            val snapshots = result.analyzers.mapNotNull { it.scalarIdentityStatistics }
            val reasons = sortedMapOf<String, Long>()
            for (snapshot in snapshots) for ((reason, count) in snapshot.fallbackReasons)
                reasons[reason] = (reasons[reason] ?: 0L) + count
            logger.info {
                "BIDI_IDENTITY_STORAGE_STATISTICS run=${config.index} scope=frozen-scalar-stores " +
                    "snapshotActors=${snapshots.size} unavailableActors=${result.analyzers.size - snapshots.size} " +
                    "compactPoints=${snapshots.sumOf { it.compactPoints }} " +
                    "compactNormal=${snapshots.sumOf { it.compactNormal }} compactDemand=${snapshots.sumOf { it.compactDemand }} " +
                    "compactFlow=${snapshots.sumOf { it.compactFlow }} compactTaint=${snapshots.sumOf { it.compactTaint }} " +
                    "protectedNormal=${snapshots.sumOf { it.protectedNormal }} protectedDemand=${snapshots.sumOf { it.protectedDemand }} " +
                    "fullPoints=${snapshots.sumOf { it.fullPoints }} promotedPoints=${snapshots.sumOf { it.promotedPoints }} " +
                    "firstFullPoints=${snapshots.sumOf { it.firstFullPoints }} bitWords=${snapshots.sumOf { it.bitWords }} " +
                    "fullArrayCapacity=${snapshots.sumOf { it.fullArrayCapacity }} fallbackReasons=$reasons"
            }
        }
        logOptimizationStatistics(config, "END")
        config.demand?.staticCompletionStatistics()?.let {
            logger.info { "BIDI_STATIC_CLOSURE_LOOKUP run=${config.index} $it" }
        }
        config.demand?.diagnosticC5Samples()?.forEach { sample ->
            logger.info { "BIDI_C5_ROW_SAMPLE run=${config.index} $sample" }
        }
        if (result.status != RunStatus.COMPLETE) return Next.End(result.status)
        val barrierStart = TimeSource.Monotonic.markNow()
        val next = try {
            guardBarrier(shared) { barrier(config, result, report) }
        } catch (error: Cancellation.Cancelled) {
            Next.End(RunStatus.OOM)
        } finally {
            logger.info { "BIDI_BARRIER_END run=${config.index} barrierTime=${barrierStart.elapsedNow()} iterationTime=${start.elapsedNow()}" }
            if (config.run1) shared.releaseRun1CatalogCoverage()
        }
        if (shared.cancellation.isActive()) return next
        logger.error { "Run ${config.index}: the barrier memory guard fired; the analysis ends with the report so far" }
        return Next.End(RunStatus.OOM)
    }

    private fun logOptimizationStatistics(config: RunConfig, phase: String) {
        shared.abstractionStatistics?.let { statistics ->
            logger.info { "BIDI_ABSTRACTION_STATISTICS run=${config.index} direction=${config.direction} limit=${config.fieldLimit} phase=$phase totals=${statistics.snapshot()}" }
        }
        shared.n1Statistics?.let { statistics ->
            logger.info { "BIDI_N1_STATISTICS run=${config.index} direction=${config.direction} limit=${config.fieldLimit} phase=$phase totals=${statistics.snapshot()}" }
        }
        shared.n2Statistics?.let { statistics ->
            logger.info { "BIDI_N2_STATISTICS run=${config.index} direction=${config.direction} limit=${config.fieldLimit} phase=$phase totals=${statistics.snapshot()}" }
        }
        shared.requestBatchStatistics?.let { statistics ->
            logger.info { "BIDI_REQUEST_BATCH_STATISTICS run=${config.index} direction=${config.direction} limit=${config.fieldLimit} phase=$phase totals=${statistics.snapshot()}" }
        }
    }

    private fun barrier(config: RunConfig, result: RunResult<RunMethodAnalyzer>, report: ReportBuilder): Next {
        if (shared.n2Statistics != null) {
            val censusStart = TimeSource.Monotonic.markNow()
            val publicAdmitted = result.analyzers.fold(RelationCensus()) { counts, actor -> counts + actor.summaries.census() }
            val publicOutgoing = result.analyzers.fold(RelationCensus()) { counts, actor -> counts + actor.summaries.demandCensus(config.direction) }
            val blockAdmitted = result.analyzers.asSequence().flatMap { it.blockSummaries() }
                .fold(RelationCensus()) { counts, block -> counts + block.summaries.census() }
            val blockOutgoing = result.analyzers.asSequence().flatMap { it.blockSummaries() }
                .fold(RelationCensus()) { counts, block -> counts + block.summaries.demandCensus(config.direction) }
            val admitted = publicAdmitted + blockAdmitted
            val outgoing = publicOutgoing + blockOutgoing
            logger.info { "BIDI_FLOW_BACKED_CENSUS run=${config.index} admitted=$admitted outgoing=$outgoing blockAdmitted=$blockAdmitted blockOutgoing=$blockOutgoing scanTime=${censusStart.elapsedNow()}" }
        }
        val forward = config.direction == Direction.FORWARD
        val terminals = report.prepare(config, result, shared)
        shared.records.persistCompleted(config.direction, result.analyzers.asSequence().map { it.key to it.summaries },
            result.analyzers.asSequence().flatMap { it.blockSummaries() })
        val handOff = HandOff.of(config, result, shared)
        val frontier = frontierOf(config, result, handOff, terminals.entries.size)
        frontierLog += frontier
        frontier.log()
        val next = when {
            forward && handOff.demandEdges.isEmpty() -> Next.End(RunStatus.COMPLETE, EndReason.NO_DEMAND_EDGE)
            forward && !policy.continueAfter(config, result, frontiers) -> Next.End(RunStatus.COMPLETE, EndReason.POLICY)
            else -> Next.Run(nextConfig(config, handOff, terminals.normal))
        }
        logger.info { "BIDI_TARGET_STATISTICS run=${config.index} raw=${result.analyzers.sumOf { it.targets.size }} outgoing=${result.analyzers.sumOf { it.outgoingTargets.size }} reports=${terminals.entries.size} blockRaw=${result.analyzers.asSequence().flatMap { it.blockTargets() }.sumOf { it.rows.size }} blockOutgoing=${result.analyzers.asSequence().flatMap { it.blockOutgoingTargets() }.sumOf { it.rows.size }}" }
        // All fallible preparation precedes this single terminal/report commit.
        shared.cancellation.checkpoint()
        if (forward && config.mode.markMode == MarkMode.FULL) {
            shared.normalRuleContributors.publish(result.analyzers.asSequence()
                .flatMap { it.normalContributorRows() }.asIterable())
        }
        report.commit(terminals)
        return next
    }

    private fun nextConfig(config: RunConfig, handOff: HandOff, normalTargets: org.opentaint.dataflow.bidi.engine.NormalTargetView): RunConfig {
        val index = config.index + 1
        val limit = policy.fieldLimit(index)
        require(limit >= config.fieldLimit) { "ap.md W3: the field limit must not decrease" }
        return RunConfig(index, limit, handOff.demand, shared.records.view(), handOff.seeds, config.roots,
            run1MarkMode = run1MarkMode, fieldLimitSchedule = fieldLimitSchedule, normalTargets = normalTargets)
    }

    companion object : KLogging() {
        const val BARRIER_MEMORY_THRESHOLD = 0.99
    }
}

private fun runEngine(config: RunConfig, shared: SharedObjects, timeout: Duration): RunResult<RunMethodAnalyzer> =
    RunManager(config, shared, RunMethodHandlers(MethodLocalServicesFactory(::RunMethodLocalServices),
        MethodCallServicesFactory(::RunMethodCallServices))).run(timeout)

private fun withBarrierGuard(shared: SharedObjects, body: () -> Next): Next =
    MemoryManager(shared.refManager, IterationDriver.BARRIER_MEMORY_THRESHOLD) { shared.cancellation.cancel() }
        .runWithMemoryManager(body)

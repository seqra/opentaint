package org.opentaint.dataflow.bidi.engine

import kotlinx.coroutines.CompletableDeferred
import kotlinx.coroutines.CoroutineExceptionHandler
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.CoroutineStart
import kotlinx.coroutines.Job
import kotlinx.coroutines.NonCancellable
import kotlinx.coroutines.SupervisorJob
import kotlinx.coroutines.delay
import kotlinx.coroutines.isActive
import kotlinx.coroutines.joinAll
import kotlinx.coroutines.launch
import kotlinx.coroutines.runBlocking
import kotlinx.coroutines.withTimeoutOrNull
import mu.KLogging
import org.opentaint.dataflow.bidi.interp.DirectedForms
import org.opentaint.dataflow.bidi.interp.RuleView
import org.opentaint.dataflow.bidi.ap.MethodKey
import org.opentaint.dataflow.bidi.ap.MarkMode
import org.opentaint.dataflow.bidi.store.FrozenCompletion
import org.opentaint.dataflow.ifds.UnitType
import org.opentaint.dataflow.ifds.UnknownUnit
import org.opentaint.dataflow.util.MemoryManager
import java.util.concurrent.atomic.AtomicBoolean
import java.util.concurrent.atomic.AtomicReference
import java.util.concurrent.ConcurrentHashMap
import kotlin.time.Duration
import kotlin.time.Duration.Companion.seconds
import kotlin.time.TimeMark
import kotlin.time.TimeSource

/** Fresh routing, completion and coroutine ownership for exactly one run. */
class RunManager<A : RunActor>(
    val config: RunConfig,
    val shared: SharedObjects,
    private val factory: RunnerHandlerFactory<A>,
    val steps: ProtocolSteps = ProtocolSteps.Inline,
    private val quantum: Int = RUNNER_STEPS_QUANT,
) {
    init {
        require(quantum > 0) { "The runner quantum must be positive" }
        shared.cancellation.activate()
    }

    private val job = SupervisorJob()
    private val scope = CoroutineScope(shared.dispatcher + job)
    private val admission = Any()
    private val runners = LinkedHashMap<UnitType, UnitRunner<A>>()
    private val storages = ConcurrentHashMap<MethodKey, SummaryStorage>()
    private val runnerJobs = ArrayList<Job>()
    private val completion = CompletableDeferred<RunStatus>()
    private val status = AtomicReference<RunStatus?>(null)
    private val invoked = AtomicBoolean()
    /** Native lifecycle/failure control; production keeps this null. */
    internal var joinedPreparationObserver: ((JoinedPreparationPhase) -> Unit)? = null
    private class Deadline(private val start: TimeMark, private val timeout: Duration) {
        val remaining: Duration get() = timeout - start.elapsedNow()
    }
    @Volatile private var deadline: Deadline? = null
    @Volatile private var admitting = false
    val ended: Boolean get() = status.get() != null
    val terminalStatus: RunStatus? get() = status.get()
    val inFlight = InFlight {
        if (status.compareAndSet(null, RunStatus.COMPLETE)) completion.complete(RunStatus.COMPLETE)
    }
    val forms: DirectedForms = shared.contexts.directed(config.direction,
        if (config.mode.markMode == MarkMode.GROUP) RuleView.RUN1_GROUP else RuleView.FULL)
    val staticService: Run1StaticService? = if (config.run1) Run1StaticService(shared.ap, config.mode.markMode) else null
    private val memory = MemoryManager(shared.refManager, OOM_THRESHOLD) { fail(RunStatus.OOM) }

    /** All units in this run share one storage for the complete callee key. */
    fun summaryStorage(key: MethodKey): SummaryStorage = synchronized(admission) {
        check(!ended) { "The run has ended" }
        shared.cancellation.checkpoint()
        storages.computeIfAbsent(key) { SummaryStorage(it, shared.ap, shared.ops, steps,
            shared.abstractionStatistics, flowBacked = true) }
    }

    fun route(event: RunEvent): Boolean {
        if (!admitting || !withinDeadline()) return false
        val unit = shared.unitResolver.resolve(event.target().method)
        if (!withinDeadline() || unit == UnknownUnit) return false
        return synchronized(admission) {
            if (!admitting || !withinDeadline()) return@synchronized false
            val runner = runners[unit] ?: UnitRunner(unit, this, factory, quantum).also { r ->
                runners[unit] = r
                if (!withinDeadline()) return@synchronized false
                val exceptionHandler = CoroutineExceptionHandler { _, e ->
                    logger.error(e) { "Runner $unit failed in run ${config.index}" }
                    fail(RunStatus.FAILED)
                }
                val runnerJob = scope.launch(exceptionHandler, start = CoroutineStart.LAZY) { r.runLoop() }
                runnerJobs += runnerJob
                runnerJob.start()
            }
            if (!withinDeadline()) return@synchronized false
            runner.postEvent(event)
        }
    }

    /** The reservation and its visibility are one admission transition. */
    internal fun accept(send: () -> Boolean): Boolean = synchronized(admission) {
        if (!admitting || !withinDeadline()) return@synchronized false
        inFlight.beforeSend()
        val accepted = try { send() }
        catch (e: Throwable) {
            fail(RunStatus.FAILED)
            inFlight.rejectedSend()
            throw e
        }
        if (!accepted) inFlight.rejectedSend()
        accepted
    }

    internal fun afterHandler() = synchronized(admission) {
        withinDeadline()
        inFlight.afterHandler()
    }

    /** Routing and setup consume the same budget as the completion wait. */
    private fun withinDeadline(): Boolean {
        if (!ended && deadline?.remaining?.let { it <= Duration.ZERO } == true) fail(RunStatus.TIMEOUT)
        return !ended
    }

    /** Selection precedes cancellation; a later failure preserves the first terminal status. */
    fun fail(end: RunStatus) {
        require(end != RunStatus.COMPLETE) { "Only quiescence selects COMPLETE" }
        if (!status.compareAndSet(null, end)) return
        shared.cancellation.cancel()
        completion.complete(end)
    }

    fun run(timeout: Duration): RunResult<A> {
        check(invoked.compareAndSet(false, true)) { "A run manager can run only once" }
        logger.info { "BIDI_MARK_MODE run=${config.index} mode=${config.mode.markMode} configuredRun1Mode=${config.run1MarkMode}" }
        if (config.run1) logger.info {
            "Run 1: DIAGNOSTIC opentaint.bidi.disableRun1Statics=${config.disableRun1Statics}; " +
                "true disables static FIELD flows and can miss findings; exact global markers are kept"
        }
        deadline = Deadline(TimeSource.Monotonic.markNow(), timeout)
        var joinAttempted = false
        var joined = false
        fun joinRunners() {
            joinAttempted = true
            joined = try { runBlocking(NonCancellable) { stopAndJoin() } }
            catch (e: Throwable) {
                logger.error(e) { "Run ${config.index}: runner join failed" }
                false
            }
        }
        try {
            memory.runWithMemoryManager {
                try {
                    runBlocking {
                        val progress = launch {
                            var last = 0L
                            while (isActive) {
                                delay(PROGRESS_PERIOD)
                                last = logProgress(last)
                            }
                        }
                        try {
                            startRoots()
                            if (withinDeadline()) {
                                withTimeoutOrNull(checkNotNull(deadline).remaining) { completion.await() }
                                    ?: fail(RunStatus.TIMEOUT)
                            }
                        } finally { progress.cancel() }
                    }
                } catch (e: Throwable) {
                    logger.error(e) { "Run ${config.index}: caller failed" }
                    fail(RunStatus.FAILED)
                } finally { joinRunners() }
            }
        } catch (e: Throwable) {
            logger.error(e) { "Run ${config.index}: memory guard or caller failed" }
            fail(RunStatus.FAILED)
        } finally {
            if (!joinAttempted) joinRunners()
        }

        if (!joined) {
            // A failed join cannot export any runner-owned state.
            status.set(RunStatus.FAILED)
            shared.cancellation.cancel()
            completion.complete(RunStatus.FAILED)
        }
        val snapshot = synchronized(admission) { runners.values.toList() }
        val joinedActors = if (joined) snapshot.flatMap { it.analyzers() } else emptyList()
        var staticCompletion: FrozenCompletion? = null
        var joinedStaticBindingTime = Duration.ZERO
        var joinedSealReleaseTime = Duration.ZERO
        val methods = joinedActors.filterIsInstance<RunMethodAnalyzer>()
        val realMethods = methods.size == joinedActors.size
        var preparationStarted = false
        val lease = JoinedBindingLease()
        val releasedRunners = java.util.Collections.newSetFromMap(java.util.IdentityHashMap<UnitRunner<A>, Boolean>())
        var failure: Throwable? = null
        var preparationError: Throwable? = null
        fun release(action: () -> Unit) {
            try { action() } catch (error: Throwable) {
                val first = failure ?: preparationError
                if (first == null) failure = error else if (error !== first) first.addSuppressed(error)
            }
        }
        fun releaseRunner(runner: UnitRunner<A>) {
            if (releasedRunners.add(runner)) runner.release()
        }
        fun prepareJoined(checkpoint: () -> Unit): JoinedStaticGuidance? {
            var sources: List<JoinedStaticSource> = emptyList()
            var primary: Throwable? = null
            try {
                if (realMethods) {
                    preparationStarted = true
                    val sealStarted = TimeSource.Monotonic.markNow()
                    try {
                        check(inFlight.pending == 0L && !admitting) { "Joined preparation needs complete callback quiescence" }
                        for (method in methods) { checkpoint(); method.captureJoinedExports() }
                        joinedPreparationObserver?.invoke(JoinedPreparationPhase.CAPTURED)
                        if (config.run1) {
                            sources = methods.flatMap { checkpoint(); it.detachJoinedStaticSources() }
                            for (method in methods) { checkpoint(); lease.addLocal(method.key, method.detachJoinedLocalInputs()) }
                            for (storage in storages.values) { checkpoint(); lease.addCallers(storage) }
                        }
                        joinedPreparationObserver?.invoke(JoinedPreparationPhase.SEALED)
                        for (method in methods) {
                            checkpoint()
                            release { method.freeze() }
                        }
                        failure?.let { throw it }
                        for (runner in snapshot) release { releaseRunner(runner) }
                        failure?.let { throw it }
                        synchronized(admission) { runners.clear(); runnerJobs.clear(); storages.clear() }
                        joinedPreparationObserver?.invoke(JoinedPreparationPhase.RELEASED)
                    } finally { joinedSealReleaseTime += sealStarted.elapsedNow() }
                }
                if (!config.run1) return null
                checkpoint()
                joinedPreparationObserver?.invoke(JoinedPreparationPhase.BEFORE_BIND)
                val bindStarted = TimeSource.Monotonic.markNow()
                val result = try {
                    if (realMethods) completeJoinedStaticGuidance(config, shared, sources, lease, checkpoint)
                    else completeJoinedStaticGuidance(config, shared, methods, storage = { storages[it] }, checkpoint = checkpoint)
                } finally { joinedStaticBindingTime += bindStarted.elapsedNow() }
                checkpoint()
                joinedPreparationObserver?.invoke(JoinedPreparationPhase.BOUND)
                return result
            } catch (error: Throwable) {
                primary = error
                throw error
            } finally {
                val closeStarted = TimeSource.Monotonic.markNow()
                var cleanup: Throwable? = null
                fun close(action: () -> Unit) {
                    try { action() } catch (error: Throwable) {
                        val first = primary ?: cleanup
                        if (first == null) cleanup = error else if (first !== error) first.addSuppressed(error)
                    }
                }
                close { lease.close() }
                sources = emptyList() // Drop reader references, never shared native stores or keys.
                joinedSealReleaseTime += closeStarted.elapsedNow()
                if (realMethods) close { joinedPreparationObserver?.invoke(JoinedPreparationPhase.CLOSED) }
                if (primary == null) cleanup?.let { throw it }
            }
        }
        if (joined && status.get() == RunStatus.COMPLETE) {
            val resourceGate = Any()
            var resourceActive = true
            var guidance: JoinedStaticGuidance? = null
            fun rejectPreparation(reason: RunStatus) = synchronized(resourceGate) {
                check(reason != RunStatus.COMPLETE)
                if (resourceActive && status.compareAndSet(RunStatus.COMPLETE, reason)) shared.cancellation.cancel()
            }
            fun checkpoint() {
                if (checkNotNull(deadline).remaining <= Duration.ZERO) rejectPreparation(RunStatus.TIMEOUT)
                shared.cancellation.checkpoint()
            }
            try {
                if (config.run1) {
                    // Preserve the existing joined resource gate around the entire new lifetime phase.
                    withJoinedDeadline(remaining = { checkNotNull(deadline).remaining },
                        onTimeout = { rejectPreparation(RunStatus.TIMEOUT) }) {
                        MemoryManager(shared.refManager, OOM_THRESHOLD) { rejectPreparation(RunStatus.OOM) }
                            .runWithMemoryManager { checkpoint(); guidance = prepareJoined(::checkpoint); checkpoint() }
                    }
                } else {
                    // Later runs keep their old post-join guard coverage.
                    guidance = prepareJoined(shared.cancellation::checkpoint)
                }
            } catch (error: Throwable) {
                preparationError = error
                rejectPreparation(if (error is OutOfMemoryError) RunStatus.OOM else RunStatus.FAILED)
                logger.error(error) { "Run ${config.index}: joined preparation failed" }
            } finally { synchronized(resourceGate) { resourceActive = false } }
            if (status.get() == RunStatus.COMPLETE) staticCompletion = guidance?.completion
            if (config.run1) logger.info {
                "BIDI_STATIC_WRITER_BIND run=${config.index} bindingTime=$joinedStaticBindingTime status=${status.get()} " +
                    "observedCandidates=${guidance?.observedCandidates ?: 0} lostCandidates=${guidance?.lostCandidates ?: 0} " +
                    "peakCandidateMemberships=${guidance?.peakCandidates ?: 0} " +
                    "pruneTime=${guidance?.pruneTime ?: Duration.ZERO} writerTime=${guidance?.writerTime ?: Duration.ZERO} " +
                    "closureFreezeTime=${guidance?.closureFreezeTime ?: Duration.ZERO} ${guidance?.binding ?: "no-completed-binding"}"
            }
        }
        val end = checkNotNull(status.get())
        val analyzers = if (end == RunStatus.COMPLETE) joinedActors else emptyList()
        if (joined && end != RunStatus.COMPLETE && shared.n2Statistics != null) {
            // Failed runs export no actors. Read only stopped-owner diagnostics,
            // while the joined actors still exist, before releasing their runners.
            val measured = joinedActors.filterIsInstance<RunMethodAnalyzer>()
            logger.info {
                "BIDI_BODY_WORK_ABORTED run=${config.index} status=$end scope=joined-packet-events " +
                    "actors=${measured.size} steps=${measured.sumOf { it.steps }} " +
                    "candidateOffers=${measured.sumOf { it.diagnosticCandidateOffers }}"
            }
            // Copy bounded samples for the hot owners only, especially after an OOM.
            val hot = (measured.sortedByDescending { it.steps }.take(12) +
                measured.sortedByDescending { it.diagnosticCandidateOffers }.take(12)).distinctBy { it.key }
            for (actor in hot) logger.info {
                "BIDI_BODY_WORK_ABORTED_METHOD run=${config.index} status=$end method=${actor.key} snapshot=${actor.stoppedBodyWorkSnapshot()}"
            }
            for (actor in hot) actor.blockDiagnostics()?.let { summary -> logger.info {
                "BIDI_LOOP_BLOCK_ABORTED run=${config.index} status=$end method=${actor.key} $summary"
            } }
        }
        staticService?.let { logger.info { "BIDI_STATIC_STATISTICS run=${config.index} status=$end totals=${it.statistics()} requests=${it.requestStatistics()}" } }
        try {
            for (analyzer in analyzers) release { analyzer.freeze() }
            if (preparationStarted && end != RunStatus.COMPLETE)
                for (method in methods) release { method.freeze() }
        } finally {
            release { lease.close() }
            if (joined) for (runner in snapshot) release { releaseRunner(runner) }
            // A complete run's frozen state is still needed by the driver barrier.
            if (joined && config.run1 && end != RunStatus.COMPLETE) shared.releaseRun1CatalogCoverage()
            synchronized(admission) {
                runners.clear()
                runnerJobs.clear()
                if (joined) { storages.values.forEach { it.releaseStopped() }; storages.clear() }
            }
            if (joined) staticService?.clear()
        }
        failure?.let { throw it }
        return RunResult(end, analyzers, config.index, config.direction, config.mode.markMode,
            joinedStaticBindingTime, staticCompletion, joinedSealReleaseTime)
    }

    private fun startRoots() {
        val reserved = synchronized(admission) {
            if (!withinDeadline()) false
            else {
                inFlight.beforeSend()
                admitting = true
                true
            }
        }
        if (!reserved) return
        try {
            for (root in config.roots) {
                if (!withinDeadline()) break
                route(RunEvent.Start(root))
            }
        } catch (e: Throwable) {
            fail(RunStatus.FAILED)
            throw e
        } finally { afterHandler() }
    }

    private suspend fun stopAndJoin(): Boolean {
        val (snapshot, jobs) = synchronized(admission) {
            admitting = false
            runners.values.toList() to runnerJobs.toList()
        }
        snapshot.forEach { it.close() }
        job.cancel()
        return withTimeoutOrNull(shared.cancellationTimeout) { jobs.joinAll(); true } ?: false
    }

    private fun logProgress(last: Long): Long {
        val handled = inFlight.handled
        logger.info { "Run ${config.index}: $handled events (+${handled - last}), ${inFlight.pending} in flight" }
        logger.info { "Memory usage: ${MemoryManager.currentMemoryUsage()}/${Runtime.getRuntime().maxMemory()}" }
        return handled
    }

    companion object : KLogging() {
        const val RUNNER_STEPS_QUANT = 1000
        const val OOM_THRESHOLD = 0.90
        val PROGRESS_PERIOD = 10.seconds
    }
}

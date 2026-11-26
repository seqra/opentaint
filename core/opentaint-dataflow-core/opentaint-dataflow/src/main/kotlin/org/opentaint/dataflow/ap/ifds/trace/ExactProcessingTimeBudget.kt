package org.opentaint.dataflow.ap.ifds.trace

import org.opentaint.dataflow.util.Cancellation
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.atomic.AtomicLong
import kotlin.time.Duration
import kotlin.time.Duration.Companion.nanoseconds

class ExactProcessingTimeBudget<K>(
    val limit: Duration,
) {
    enum class Stage {
        TRACE_RESOLUTION,
        RULE_SEARCH,
    }

    data class Snapshot(
        val traceResolution: Duration,
        val ruleSearch: Duration,
        val limit: Duration,
    ) {
        val total: Duration get() = traceResolution + ruleSearch
        val exhausted: Boolean get() = total >= limit
    }

    data class Measurement<T>(
        val value: T,
        val snapshot: Snapshot,
    )

    private class Counters {
        val traceResolutionNanos = AtomicLong()
        val ruleSearchNanos = AtomicLong()

        fun totalNanos(): Long = traceResolutionNanos.get() + ruleSearchNanos.get()
    }

    private val limitNanos = limit.inWholeNanoseconds
    private val counters = ConcurrentHashMap<K, Counters>()

    init {
        require(limit.isPositive() && limit.isFinite()) { "A finite positive time limit is required" }
    }

    fun snapshot(key: K): Snapshot {
        val current = counters[key]
        return Snapshot(
            traceResolution = (current?.traceResolutionNanos?.get() ?: 0L).nanoseconds,
            ruleSearch = (current?.ruleSearchNanos?.get() ?: 0L).nanoseconds,
            limit = limit,
        )
    }

    fun isExhausted(key: K): Boolean = snapshot(key).exhausted

    fun <T> measure(
        key: K,
        stage: Stage,
        parentCancellation: Cancellation,
        block: (Cancellation) -> T,
    ): Measurement<T> {
        val counter = counters.computeIfAbsent(key) { Counters() }
        val consumedAtStart = counter.totalNanos()
        val startedAt = System.nanoTime()
        val operationCancellation = parentCancellation.derive {
            val currentOperationNanos = elapsedNanos(startedAt)
            consumedAtStart + currentOperationNanos < limitNanos
        }

        val value = try {
            block(operationCancellation)
        } finally {
            val elapsed = elapsedNanos(startedAt)
            when (stage) {
                Stage.TRACE_RESOLUTION -> counter.traceResolutionNanos.addAndGet(elapsed)
                Stage.RULE_SEARCH -> counter.ruleSearchNanos.addAndGet(elapsed)
            }
        }

        return Measurement(value, snapshot(key))
    }

    private fun elapsedNanos(startedAt: Long): Long =
        (System.nanoTime() - startedAt).coerceAtLeast(0L)
}

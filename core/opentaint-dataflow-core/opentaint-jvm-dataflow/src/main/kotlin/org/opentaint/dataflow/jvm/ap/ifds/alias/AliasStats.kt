package org.opentaint.dataflow.jvm.ap.ifds.alias

import mu.KLogging
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.Params
import java.util.concurrent.CancellationException
import java.util.concurrent.atomic.AtomicBoolean
import java.util.concurrent.atomic.AtomicLong
import java.util.concurrent.atomic.AtomicLongArray
import java.util.concurrent.atomic.LongAdder

/** The kind of an alias query (design §11.2, V1). */
enum class AliasQueryKind {
    /** `findAlias`: the state before the statement. */
    BEFORE,

    /** `findAliasAfterStatement`: the state after the statement. */
    AFTER,

    /** `findArrayElementAliases`: the elements of an array (IMPL §6.3). */
    ARRAY_ELEMENT,

    /** `findHeapAlias`: a heap path (tests only). */
    HEAP,
}

/** A backend of the alias analysis facade. */
enum class AliasBackend { DSU, DIRECTED }

/**
 * The statistics of the alias analysis (IMPL §8, design §11.2). One registry for the process. It is
 * thread safe. It is always on. Each counter is a [LongAdder], an atomic value or a [StatHistogram].
 * The statistics never change an answer.
 *
 * Groups:
 * - [backend]: for each backend, the number of method analyses, the time-outs, the failures and the
 *   alias time of each method ([AliasBackendStats]).
 * - [volume]: the answer volume of each backend ([AliasVolumeStats]).
 * - [shadow]: the comparison of the two answers of each query in `SHADOW` mode ([AliasShadowStats]).
 * - [directed]: the work counters of the directed analysis ([DirectedAliasStats]).
 *
 * The summary ([summaryLines]) has one line for each counter group. Each line starts with
 * `ALIAS-STATS group=<name>`. The other items of a line are `key=value` pairs. The keys are stable:
 *
 * `group=config`: `mode` (`DSU`, `SHADOW` or `DIRECTED`), `symDepth` (K), `maxAccessors` (D),
 * `maxCallClosure`, `depth` (the inlining depth `aliasAnalysisInterProcCallDepth`), `timeLimitMs`.
 *
 * `group=backend backend=<DSU|DIRECTED>`: `methods` (the method analyses that started), `timeouts`,
 * `failures` (analyses that stopped with an exception), `cancelled` (analyses that the parent
 * cancellation stopped), `aliasTimeMs` (the sum of the alias time of
 * all methods, in milliseconds), `aliasTimeUsP50`, `aliasTimeUsP99`, `aliasTimeUsMax` (the alias
 * time of one method, in microseconds). The alias time of a method is the time of the backend
 * computation: DSU `compute()`, directed `compute()` (CFG, fixpoint and freeze). Time-outs are
 * included.
 *
 * `group=volume backend=<DSU|DIRECTED> kind=<BEFORE|AFTER|ARRAY_ELEMENT|HEAP|ALL>`: see
 * [AliasVolumeStats]. `group=volumeMethods backend=<DSU|DIRECTED>`: the totals of each method.
 *
 * `group=shadow kind=<...|ALL>` and `group=shadowRun`: see [AliasShadowStats].
 *
 * `group=directed`, `group=directedCalls`, `group=directedOrigins`: see [DirectedAliasStats].
 *
 * A percentile (`P50`, `P99`) is approximate: exact below 64, else the lower bound of a bucket of
 * relative width 1/8 ([StatHistogram]). A `Max` and a `Sum` are exact.
 *
 * The taint analyzer logs the summary at INFO at the end of the analysis of a project
 * ([logSummary]), then it resets the counters. A JVM shutdown hook logs the summary if counters
 * were recorded after the last summary (a run that a time-out or the memory guard stops).
 */
object AliasStats {
    const val PREFIX = "ALIAS-STATS"

    private val logger = object : KLogging() {}.logger

    private val backends = AliasBackend.entries.associateWith { AliasBackendStats() }

    val volume = AliasVolumeStats()
    val shadow = AliasShadowStats()
    val directed = DirectedAliasStats()

    /** The parameters of the last facade. The shutdown hook prints them. */
    @Volatile
    private var config: Params? = null

    private val hookRegistered = AtomicBoolean(false)

    fun backend(b: AliasBackend): AliasBackendStats = backends.getValue(b)

    /** Notes the parameters of a facade. The first call registers the shutdown hook. */
    fun noteConfig(params: Params) {
        if (config !== params) config = params
        if (!hookRegistered.get() && hookRegistered.compareAndSet(false, true)) {
            Runtime.getRuntime().addShutdownHook(Thread({ logSummaryAtShutdown() }, "alias-stats-summary"))
        }
    }

    /** True if a counter was recorded after the last [reset]. */
    fun hasRecords(): Boolean =
        backends.values.any { it.methods.sum() > 0 } || volume.hasRecords()

    /** The summary lines (see the KDoc of [AliasStats]). [params] gives the configuration line. */
    fun summaryLines(params: Params? = config): List<String> = buildList {
        add(line("config") {
            if (params == null) {
                put("mode", "unknown")
            } else {
                put("mode", params.mode.name)
                put("symDepth", params.symDepth)
                put("maxAccessors", params.maxAccessors)
                put("maxCallClosure", params.maxCallClosure)
                put("depth", params.aliasAnalysisInterProcCallDepth)
                put("timeLimitMs", params.aliasAnalysisTimeLimit.inWholeMilliseconds)
            }
        })
        for (b in AliasBackend.entries) add(line("backend") { put("backend", b.name); backend(b).write(this) })
        volume.writeLines(this)
        shadow.writeLines(this)
        directed.writeLines(this)
    }

    /** Logs the summary at INFO, then resets the counters. [params]: the configuration of the run. */
    fun logSummary(params: Params? = null) {
        val lines = summaryLines(params ?: config)
        reset()
        for (l in lines) logger.info { l }
    }

    private fun logSummaryAtShutdown() {
        if (!hasRecords()) return
        logger.info { "$PREFIX summary at shutdown: the analysis did not end normally" }
        logSummary()
    }

    /** Sets all counters of the project to zero. The diff line count of the process stays. */
    fun reset() {
        backends.values.forEach { it.reset() }
        volume.reset()
        shadow.reset()
        directed.reset()
    }

    /** Parses a summary line into its `key=value` pairs. The `group` item is a pair too. */
    fun parseSummaryLine(line: String): Map<String, String> {
        require(line.startsWith("$PREFIX ")) { "Not a summary line: $line" }
        return line.removePrefix("$PREFIX ").split(' ').filter { it.isNotEmpty() }.associate { item ->
            val i = item.indexOf('=')
            require(i > 0) { "Not a key=value item: '$item' in $line" }
            item.substring(0, i) to item.substring(i + 1)
        }
    }

    /** One summary line: the prefix, `group=<group>`, then the items of [body]. */
    internal inline fun line(group: String, body: LineBuilder.() -> Unit): String {
        val b = LineBuilder(StringBuilder("$PREFIX group=$group"))
        b.body()
        return b.sb.toString()
    }

    class LineBuilder(val sb: StringBuilder) {
        fun put(key: String, value: Any) {
            sb.append(' ').append(key).append('=').append(value)
        }

        /** `<key>Sum`, `<key>P50`, `<key>P99`, `<key>Max` of [h]. */
        fun putDistribution(key: String, h: StatHistogram) {
            put("${key}Sum", h.sum())
            put("${key}P50", h.percentile(0.50))
            put("${key}P99", h.percentile(0.99))
            put("${key}Max", h.max())
        }
    }
}

/** The counters of one backend (`group=backend`). */
class AliasBackendStats {
    val methods = LongAdder()
    val timeouts = LongAdder()
    val failures = LongAdder()
    val cancelled = LongAdder()

    /** The alias time of each method, in microseconds. */
    val aliasTimeUs = StatHistogram()

    private val aliasTimeNs = LongAdder()

    /** Records one method analysis that took [nanos]. */
    fun record(nanos: Long, timeout: Boolean, failure: Boolean, cancel: Boolean = false) {
        methods.increment()
        if (timeout) timeouts.increment()
        if (failure) failures.increment()
        if (cancel) cancelled.increment()
        aliasTimeNs.add(nanos)
        aliasTimeUs.record(nanos / 1000)
    }

    /**
     * Runs [compute] and records its time. A `null` result is a time-out if [nullIsTimeout] gives
     * true. A [CancellationException] (the parent cancellation) is a cancel. Another exception is a
     * failure. The exception goes to the caller.
     */
    inline fun <T> measure(nullIsTimeout: () -> Boolean, compute: () -> T?): T? {
        val start = System.nanoTime()
        val result = try {
            compute()
        } catch (e: Throwable) {
            val cancel = e is CancellationException
            record(System.nanoTime() - start, timeout = false, failure = !cancel, cancel = cancel)
            throw e
        }
        record(System.nanoTime() - start, timeout = result == null && nullIsTimeout(), failure = false)
        return result
    }

    internal fun write(b: AliasStats.LineBuilder) {
        b.put("methods", methods.sum())
        b.put("timeouts", timeouts.sum())
        b.put("failures", failures.sum())
        b.put("cancelled", cancelled.sum())
        b.put("aliasTimeMs", aliasTimeNs.sum() / 1_000_000)
        b.put("aliasTimeUsP50", aliasTimeUs.percentile(0.50))
        b.put("aliasTimeUsP99", aliasTimeUs.percentile(0.99))
        b.put("aliasTimeUsMax", aliasTimeUs.max())
    }

    fun reset() {
        methods.reset()
        timeouts.reset()
        failures.reset()
        cancelled.reset()
        aliasTimeNs.reset()
        aliasTimeUs.reset()
    }
}

/**
 * A histogram with fixed buckets for values that are not negative. It is thread safe. A value below
 * 64 has its own bucket. A larger value goes into one of 8 buckets for each power of two. So a
 * percentile is the lower bound of a bucket of relative width 1/8. The sum, the count and the
 * maximum are exact. A negative value counts as 0.
 */
class StatHistogram {
    private val buckets = AtomicLongArray(BUCKETS)
    private val count = LongAdder()
    private val sum = LongAdder()
    private val max = AtomicLong(0)

    fun record(value: Long) {
        val v = if (value < 0) 0 else value
        buckets.incrementAndGet(bucket(v))
        count.increment()
        sum.add(v)
        if (v > max.get()) max.accumulateAndGet(v) { a, b -> maxOf(a, b) }
    }

    /** Adds the values of [other] to this histogram. */
    fun merge(other: StatHistogram) {
        for (i in 0 until BUCKETS) {
            val n = other.buckets.get(i)
            if (n != 0L) buckets.addAndGet(i, n)
        }
        count.add(other.count())
        sum.add(other.sum())
        val m = other.max()
        if (m > max.get()) max.accumulateAndGet(m) { a, b -> maxOf(a, b) }
    }

    fun count(): Long = count.sum()
    fun sum(): Long = sum.sum()
    fun max(): Long = max.get()

    /** The value at quantile [q] (0..1): the lower bound of its bucket. 0 if the histogram is empty. */
    fun percentile(q: Double): Long {
        val n = count()
        if (n == 0L) return 0
        val rank = maxOf(1L, kotlin.math.ceil(q * n).toLong())
        var acc = 0L
        for (i in 0 until BUCKETS) {
            acc += buckets.get(i)
            if (acc >= rank) return minOf(lowerBound(i), max())
        }
        return max()
    }

    fun reset() {
        for (i in 0 until BUCKETS) buckets.set(i, 0)
        count.reset()
        sum.reset()
        max.set(0)
    }

    companion object {
        private const val LINEAR = 64
        private const val SUB = 8
        private const val BUCKETS = LINEAR + (63 - 6) * SUB

        /** The bucket of [v]: `v` below 64; else 8 buckets for each power of two from 64. */
        fun bucket(v: Long): Int {
            if (v < LINEAR) return v.toInt()
            val e = 63 - java.lang.Long.numberOfLeadingZeros(v)
            val sub = ((v ushr (e - 3)) and (SUB - 1).toLong()).toInt()
            return LINEAR + (e - 6) * SUB + sub
        }

        /** The smallest value of bucket [i]. */
        fun lowerBound(i: Int): Long {
            if (i < LINEAR) return i.toLong()
            val e = (i - LINEAR) / SUB + 6
            val sub = (i - LINEAR) % SUB
            return (1L shl e) + (sub.toLong() shl (e - 3))
        }
    }
}

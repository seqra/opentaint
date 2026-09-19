package org.opentaint.dataflow.util

import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import java.io.File
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.atomic.LongAdder

/**
 * Diagnostic for [org.opentaint.dataflow.taint.TaintMarkFieldUnfoldRequest] traffic.
 *
 * Entirely gated behind `-Dopentaint.unfoldDiag=true`; every probe is a no-op (and allocation free)
 * when disabled. Output goes to `-Dopentaint.unfoldDiag.out=<path>` or to stdout with an
 * `UNFOLDDIAG` prefix on every line.
 */
object UnfoldRequestDiag {
    @JvmStatic
    val enabled: Boolean = System.getProperty("opentaint.unfoldDiag")?.toBoolean() ?: false

    private val outPath: String? = System.getProperty("opentaint.unfoldDiag.out")

    private const val MAX_KEYS = 200_000

    // ---------------------------------------------------------------- helpers

    private class CappedSet {
        val keys = ConcurrentHashMap<Any, Boolean>()
        val overflow = LongAdder()

        fun add(key: Any) {
            if (keys.containsKey(key)) return
            if (keys.size >= MAX_KEYS) {
                overflow.increment()
                return
            }
            keys.putIfAbsent(key, java.lang.Boolean.TRUE)
        }

        val size: Int get() = keys.size
    }

    private class CappedCounter {
        val map = ConcurrentHashMap<Any, LongAdder>()
        val overflow = LongAdder()

        fun inc(key: Any) {
            val existing = map[key]
            if (existing != null) {
                existing.increment()
                return
            }
            if (map.size >= MAX_KEYS) {
                overflow.increment()
                return
            }
            map.computeIfAbsent(key) { LongAdder() }.increment()
        }

        fun top(n: Int): List<Pair<Any, Long>> =
            map.entries.map { it.key to it.value.sum() }.sortedByDescending { it.second }.take(n)

        fun histogram(): LongArray {
            // buckets: 1, 2, 3-5, 6-10, 11-100, 101+
            val h = LongArray(6)
            for (e in map.values) {
                val c = e.sum()
                val idx = when {
                    c <= 1L -> 0
                    c == 2L -> 1
                    c <= 5L -> 2
                    c <= 10L -> 3
                    c <= 100L -> 4
                    else -> 5
                }
                h[idx]++
            }
            return h
        }
    }

    private fun adders(n: Int) = Array(n) { LongAdder() }

    private fun sum(a: Array<LongAdder>) = a.sumOf { it.sum() }

    // ------------------------------------------------------------- A. emission

    private val originResolve = LongAdder()
    private val originDistinct = CappedSet()

    private val edgeZ2f = LongAdder()
    private val edgeF2f = LongAdder()

    private val answered = LongAdder()
    private val unanswered = LongAdder()
    private val markMissing = LongAdder()

    private val repost = LongAdder()
    private val repostDistinct = CappedSet()
    private val repostCounter = CappedCounter()

    private val traverseTopCalls = LongAdder()
    private val traverseCalls = LongAdder()
    private val traverseNodesVisited = LongAdder()
    private val traverseRequestsEmitted = LongAdder()

    /** buckets 0, 1, 2, 3, 4, 5-8, 9-16, 17-32, 33+ */
    private val fanoutHist = adders(9)
    private val FANOUT_LABELS = arrayOf("0", "1", "2", "3", "4", "5-8", "9-16", "17-32", "33+")

    private fun fanoutBucket(n: Int) = when {
        n <= 0 -> 0
        n == 1 -> 1
        n == 2 -> 2
        n == 3 -> 3
        n == 4 -> 4
        n <= 8 -> 5
        n <= 16 -> 6
        n <= 32 -> 7
        else -> 8
    }

    private const val DEPTH_BUCKETS = 17 // 0..15, 16+
    private fun depthBucket(d: Int) = if (d < 0) 0 else if (d >= DEPTH_BUCKETS) DEPTH_BUCKETS - 1 else d

    /** emitted request depth histogram */
    private val emitDepthHist = adders(DEPTH_BUCKETS)
    private val emitDeepest = LongAdder()
    private val emitNotDeepest = LongAdder()

    // ---------------------------------------------------------- B. redundancy

    private class ReqKey(val method: MethodEntryPoint, val fact: InitialFactAp) {
        private val hash = 31 * method.hashCode() + fact.hashCode()
        override fun hashCode(): Int = hash
        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (other !is ReqKey) return false
            return hash == other.hash && method == other.method && fact == other.fact
        }

        override fun toString(): String = "$method | $fact"
    }

    private class ReqStat {
        val emitted = LongAdder()

        @Volatile
        var depth: Int = -1

        @Volatile
        var deepest: Boolean = false
    }

    private val crossUnitTotal = LongAdder()
    private val crossUnitStats = ConcurrentHashMap<ReqKey, ReqStat>()
    private val crossUnitOverflow = LongAdder()
    private val crossUnitStrippedDistinct = CappedSet()

    // --------------------------------------------------------- C. productivity

    // outcomes: 0 = noop, 1 = barren, 2 = parked, 3 = live
    private const val O_NOOP = 0
    private const val O_BARREN = 1
    private const val O_PARKED = 2
    private const val O_LIVE = 3
    private val OUTCOME_LABELS = arrayOf("noop", "barren", "parked", "live")

    private val outcome = adders(4)
    private val pairsProduced = LongAdder()
    private val edgesParked = LongAdder()
    private val edgesLive = LongAdder()
    private val edgesAbsorbed = LongAdder()
    private val edgesNew = LongAdder()
    private val registeredRequests = LongAdder()

    /** size of the list returned by registerNewInitialFact: 0,1,2,3,4,5-8,9-16,17-32,33-64,65-128,129-256,257+ */
    private val pairsHist = adders(12)
    private val PAIRS_LABELS = arrayOf(
        "0", "1", "2", "3", "4", "5-8", "9-16", "17-32", "33-64", "65-128", "129-256", "257+"
    )

    private fun pairsBucket(n: Long) = when {
        n <= 0L -> 0
        n == 1L -> 1
        n == 2L -> 2
        n == 3L -> 3
        n == 4L -> 4
        n <= 8L -> 5
        n <= 16L -> 6
        n <= 32L -> 7
        n <= 64L -> 8
        n <= 128L -> 9
        n <= 256L -> 10
        else -> 11
    }

    /** [depthBucket][outcome] */
    private val outcomeByDepth = Array(DEPTH_BUCKETS) { adders(4) }

    /** [0 = deepest, 1 = not deepest, 2 = unknown][outcome] */
    private val outcomeByDeepest = Array(3) { adders(4) }

    /** [limit 0..15, 16+][outcome] */
    private val outcomeByLimit = Array(DEPTH_BUCKETS) { adders(4) }

    private val depthOverLimit = LongAdder()
    private val depthWithinLimit = LongAdder()
    private val depthOverLimitByOutcome = adders(4)

    /** how far above the limit the emitted request was: 0 = within, 1, 2, 3, 4+ */
    private val overLimitBy = adders(5)

    private val barrenByMethod = CappedCounter()
    private val effectUnattributed = LongAdder()

    // ----------------------------------------------------------- D. cost, misc

    private val nanosHandleUnfold = LongAdder()
    private val nanosTraverse = LongAdder()
    private val nanosEffectRegister = LongAdder()

    private val unitMaxLimit = ConcurrentHashMap<String, Int>()

    // thread-local arming token: identifies the request currently being delivered
    private val armed = ThreadLocal<ReqKey?>()

    // ------------------------------------------------------------------ probes

    fun originResolve(method: MethodEntryPoint, fact: InitialFactAp, mark: Any) {
        originResolve.increment()
        originDistinct.add(Triple(method, fact, mark))
    }

    fun edgeZeroToFact() = edgeZ2f.increment()

    fun edgeFactToFact() = edgeF2f.increment()

    fun unfoldResult(answeredResult: Boolean, nanos: Long) {
        if (answeredResult) answered.increment() else unanswered.increment()
        nanosHandleUnfold.add(nanos)
    }

    fun markMissing() = markMissing.increment()

    fun repost(method: MethodEntryPoint, fact: InitialFactAp, mark: Any) {
        repost.increment()
        val key = Triple(method, fact, mark)
        repostDistinct.add(key)
        repostCounter.inc(key)
    }

    fun traverseTop(nanos: Long) {
        traverseTopCalls.increment()
        nanosTraverse.add(nanos)
    }

    fun traverseCall() = traverseCalls.increment()

    fun traverseNode() = traverseNodesVisited.increment()

    fun traverseEmit() = traverseRequestsEmitted.increment()

    fun fanout(n: Int) = fanoutHist[fanoutBucket(n)].increment()

    /** Records one `handleCrossUnitSideEffectReq(method, fact)` emission. */
    fun crossUnitEmit(method: MethodEntryPoint, fact: InitialFactAp, depth: Int, isDeepest: Boolean) {
        crossUnitTotal.increment()
        emitDepthHist[depthBucket(depth)].increment()
        if (isDeepest) emitDeepest.increment() else emitNotDeepest.increment()

        val key = ReqKey(method, fact)
        var stat = crossUnitStats[key]
        if (stat == null) {
            if (crossUnitStats.size >= MAX_KEYS) {
                crossUnitOverflow.increment()
            } else {
                stat = crossUnitStats.computeIfAbsent(key) { ReqStat() }
            }
        }
        if (stat != null) {
            stat.emitted.increment()
            stat.depth = depth
            // "deepest" is sticky: if the same key was ever emitted as the deepest of its traverse,
            // record that; otherwise it stays false.
            if (isDeepest) stat.deepest = true
        }

        val stripped = fact.replaceExclusions(ExclusionSet.Empty)
        crossUnitStrippedDistinct.add(ReqKey(method, stripped))
    }

    /** Arms the effect-site probe for the request about to be delivered to the method analyzer. */
    fun armEffect(method: MethodEntryPoint, fact: InitialFactAp) {
        armed.set(ReqKey(method, fact))
    }

    fun disarmEffect() {
        armed.set(null)
    }

    /**
     * Consumes the arming token. Returns true iff this `triggerSideEffectRequirement` call is the
     * unfold-originated one that was armed (nested calls therefore do not match).
     */
    fun consumeEffect(method: MethodEntryPoint, fact: InitialFactAp): Boolean {
        val token = armed.get() ?: return false
        if (token.method != method || token.fact != fact) return false
        armed.set(null)
        return true
    }

    /**
     * @param result -1 for the `original == new` early return, otherwise `(parked shl 32) or live`.
     */
    private const val F_MASK = 0x1FFFFFL

    /**
     * @param result -1 if the fact did not change, otherwise
     *   `parkedPairs or (absorbedPairs shl 21) or (newEdgePairs shl 42)`.
     * @param newEdges raw number of edges `edges.add` reported as new.
     */
    fun effectResult(
        method: MethodEntryPoint,
        fact: InitialFactAp,
        result: Long,
        factDepthLimit: Int,
        newEdges: Long,
        nanos: Long
    ) {
        nanosEffectRegister.add(nanos)
        val parked = if (result < 0) 0L else result and F_MASK
        val absorbed = if (result < 0) 0L else (result ushr 21) and F_MASK
        val livePairs = if (result < 0) 0L else (result ushr 42) and F_MASK
        val live = absorbed + livePairs
        val pairs = parked + live

        val o = when {
            result < 0L -> O_NOOP
            pairs == 0L -> O_BARREN
            live == 0L -> O_PARKED
            else -> O_LIVE
        }

        outcome[o].increment()
        pairsProduced.add(pairs)
        edgesParked.add(parked)
        edgesLive.add(live)
        edgesAbsorbed.add(absorbed)
        edgesNew.add(newEdges)
        if (result >= 0L) {
            registeredRequests.increment()
            pairsHist[pairsBucket(pairs)].increment()
        }

        val depth = fact.depth
        outcomeByDepth[depthBucket(depth)][o].increment()
        outcomeByLimit[depthBucket(factDepthLimit)][o].increment()

        val stat = crossUnitStats[ReqKey(method, fact)]
        val deepestIdx = when {
            stat == null -> 2
            stat.deepest -> 0
            else -> 1
        }
        if (stat == null) effectUnattributed.increment()
        outcomeByDeepest[deepestIdx][o].increment()

        if (depth > factDepthLimit) {
            depthOverLimit.increment()
            depthOverLimitByOutcome[o].increment()
            val over = depth - factDepthLimit
            overLimitBy[if (over >= 4) 4 else over].increment()
        } else {
            depthWithinLimit.increment()
            overLimitBy[0].increment()
        }

        if (o == O_BARREN) barrenByMethod.inc(method)
    }

    fun unitFactLimit(unit: String, limit: Int) {
        unitMaxLimit.merge(unit, limit) { a, b -> if (a >= b) a else b }
    }

    // ------------------------------------------------------------------- dump

    private val shutdownHookInstalled = java.util.concurrent.atomic.AtomicBoolean(false)

    init {
        if (enabled && shutdownHookInstalled.compareAndSet(false, true)) {
            Runtime.getRuntime().addShutdownHook(Thread { dump("shutdown") })
        }
    }

    @Volatile
    private var dumped = false

    @Synchronized
    fun dump(reason: String) {
        if (!enabled) return
        val text = report(reason)
        val path = outPath
        if (path == null) {
            text.lineSequence().forEach { println("UNFOLDDIAG $it") }
        } else {
            try {
                val f = File(path)
                f.parentFile?.mkdirs()
                f.writeText(text)
            } catch (t: Throwable) {
                text.lineSequence().forEach { println("UNFOLDDIAG $it") }
            }
        }
        dumped = true
    }

    private fun pct(a: Long, b: Long): String =
        if (b == 0L) "n/a" else String.format("%.2f%%", 100.0 * a / b)

    private fun ratio(a: Long, b: Long): String =
        if (b == 0L) "n/a" else String.format("%.3f", a.toDouble() / b.toDouble())

    fun report(reason: String): String = buildString {
        appendLine("=== UNFOLD REQUEST DIAGNOSTIC (reason=$reason) ===")
        appendLine("maxKeys=$MAX_KEYS")
        appendLine()

        appendLine("-- A. emission / shape --")
        appendLine("origin.resolve                = ${originResolve.sum()}")
        appendLine("origin.distinct               = ${originDistinct.size} (overflow ${originDistinct.overflow.sum()})")
        appendLine("edge.z2f                      = ${edgeZ2f.sum()}")
        appendLine("edge.f2f                      = ${edgeF2f.sum()}")
        appendLine("answered                      = ${answered.sum()}")
        appendLine("unanswered                    = ${unanswered.sum()}")
        appendLine("markMissing                   = ${markMissing.sum()}")
        appendLine("repost                        = ${repost.sum()}")
        appendLine("repost.distinct               = ${repostDistinct.size} (overflow ${repostDistinct.overflow.sum()})")
        appendLine("repost.dupRate                = ${ratio(repost.sum(), repostDistinct.size.toLong())} emissions/distinct")
        appendLine("traverse.topCalls             = ${traverseTopCalls.sum()}")
        appendLine("traverse.calls                = ${traverseCalls.sum()}")
        appendLine("traverse.nodesVisited         = ${traverseNodesVisited.sum()}")
        appendLine("traverse.requestsEmitted      = ${traverseRequestsEmitted.sum()}")
        appendLine()

        appendLine("-- A2. requests emitted per traverse call (top-level) --")
        val fanTotal = sum(fanoutHist)
        for (i in FANOUT_LABELS.indices) {
            val v = fanoutHist[i].sum()
            appendLine("  fanout[${FANOUT_LABELS[i]}]".padEnd(30) + "= $v (${pct(v, fanTotal)})")
        }
        appendLine()

        appendLine("-- A3. emitted request depth --")
        val emitTotal = sum(emitDepthHist)
        for (i in 0 until DEPTH_BUCKETS) {
            val v = emitDepthHist[i].sum()
            if (v == 0L) continue
            val label = if (i == DEPTH_BUCKETS - 1) "${DEPTH_BUCKETS - 1}+" else "$i"
            appendLine("  depth[$label]".padEnd(30) + "= $v (${pct(v, emitTotal)})")
        }
        appendLine("  emitted.deepestInTraverse   = ${emitDeepest.sum()} (${pct(emitDeepest.sum(), emitTotal)})")
        appendLine("  emitted.notDeepest          = ${emitNotDeepest.sum()} (${pct(emitNotDeepest.sum(), emitTotal)})")
        appendLine()

        appendLine("-- B. redundancy --")
        val cuTotal = crossUnitTotal.sum()
        val cuDistinct = crossUnitStats.size.toLong()
        appendLine("crossUnit.total               = $cuTotal")
        appendLine("crossUnit.distinct            = $cuDistinct (overflow ${crossUnitOverflow.sum()})")
        appendLine("crossUnit.distinctStripped    = ${crossUnitStrippedDistinct.size} (overflow ${crossUnitStrippedDistinct.overflow.sum()})")
        appendLine("crossUnit.repeatsPerDistinct  = ${ratio(cuTotal, cuDistinct)}")
        appendLine("crossUnit.redundantFraction   = ${pct(cuTotal - cuDistinct, cuTotal)} (emissions beyond the first per key)")
        appendLine()
        appendLine("  repeat-count histogram over distinct keys:")
        val repeatHist = LongArray(6)
        var maxRepeat = 0L
        for (s in crossUnitStats.values) {
            val c = s.emitted.sum()
            if (c > maxRepeat) maxRepeat = c
            val idx = when {
                c <= 1L -> 0
                c == 2L -> 1
                c <= 5L -> 2
                c <= 10L -> 3
                c <= 100L -> 4
                else -> 5
            }
            repeatHist[idx]++
        }
        val repeatLabels = arrayOf("1", "2", "3-5", "6-10", "11-100", "101+")
        for (i in repeatLabels.indices) {
            appendLine("    repeats[${repeatLabels[i]}]".padEnd(30) + "= ${repeatHist[i]} (${pct(repeatHist[i], cuDistinct)})")
        }
        appendLine("    maxRepeatsForOneKey       = $maxRepeat")
        appendLine()
        appendLine("  top 20 most-repeated (method | fact) keys:")
        crossUnitStats.entries
            .map { it.key to it.value }
            .sortedByDescending { it.second.emitted.sum() }
            .take(20)
            .forEachIndexed { i, (k, v) ->
                appendLine("    #${i + 1} count=${v.emitted.sum()} depth=${v.depth} deepest=${v.deepest} :: $k")
            }
        appendLine()
        appendLine("  top 20 most-repeated reposts (methodEntryPoint | fact | mark):")
        repostCounter.top(20).forEachIndexed { i, (k, c) ->
            appendLine("    #${i + 1} count=$c :: $k")
        }
        appendLine()

        appendLine("-- C. productivity (unfold-originated requirements only) --")
        val oTotal = sum(outcome)
        for (i in 0..3) {
            val v = outcome[i].sum()
            appendLine("  req.${OUTCOME_LABELS[i]}".padEnd(30) + "= $v (${pct(v, oTotal)})")
        }
        appendLine("  req.total".padEnd(30) + "= $oTotal")
        appendLine("  pairsProduced".padEnd(30) + "= ${pairsProduced.sum()}")
        appendLine("  edges.parked".padEnd(30) + "= ${edgesParked.sum()}")
        appendLine("  edges.live(reachedAddSeq)".padEnd(30) + "= ${edgesLive.sum()}")
        appendLine("  edges.absorbed(0 new)".padEnd(30) + "= ${edgesAbsorbed.sum()}")
        appendLine("  edges.new".padEnd(30) + "= ${edgesNew.sum()}")
        appendLine("  effect.unattributed(nostat)".padEnd(30) + "= ${effectUnattributed.sum()}")
        appendLine("  req.pairsReturned.total".padEnd(30) + "= ${pairsProduced.sum()}")
        appendLine("  req.pairsReturned.perCrossUnit".padEnd(30) + "= ${ratio(pairsProduced.sum(), crossUnitTotal.sum())}")
        appendLine("  req.pairsReturned.perRegistered".padEnd(30) + "= ${ratio(pairsProduced.sum(), registeredRequests.sum())}")
        appendLine()
        appendLine("  req.pairsReturned histogram (over requests that reached registerNewInitialFact):")
        val pairsTotal = sum(pairsHist)
        for (i in PAIRS_LABELS.indices) {
            val v = pairsHist[i].sum()
            if (v == 0L) continue
            appendLine("    pairs[${PAIRS_LABELS[i]}]".padEnd(30) + "= $v (${pct(v, pairsTotal)})")
        }
        appendLine()

        appendLine("  outcome by emitted-request depth:")
        appendLine("    depth  " + OUTCOME_LABELS.joinToString("  ") { it.padStart(9) } + "      total")
        for (d in 0 until DEPTH_BUCKETS) {
            val row = (0..3).map { outcomeByDepth[d][it].sum() }
            val t = row.sum()
            if (t == 0L) continue
            val label = if (d == DEPTH_BUCKETS - 1) "${DEPTH_BUCKETS - 1}+" else "$d"
            appendLine("    " + label.padStart(5) + "  " + row.joinToString("  ") { it.toString().padStart(9) } + "  " + t.toString().padStart(9))
        }
        appendLine()

        appendLine("  outcome by was-deepest-in-its-traverse:")
        appendLine("    group       " + OUTCOME_LABELS.joinToString("  ") { it.padStart(9) } + "      total")
        val deepestLabels = arrayOf("deepest", "notDeepest", "unknown")
        for (g in 0..2) {
            val row = (0..3).map { outcomeByDeepest[g][it].sum() }
            val t = row.sum()
            appendLine("    " + deepestLabels[g].padEnd(10) + "  " + row.joinToString("  ") { it.toString().padStart(9) } + "  " + t.toString().padStart(9))
        }
        appendLine()

        appendLine("  outcome by factDepthLimit in force:")
        appendLine("    limit  " + OUTCOME_LABELS.joinToString("  ") { it.padStart(9) } + "      total")
        for (d in 0 until DEPTH_BUCKETS) {
            val row = (0..3).map { outcomeByLimit[d][it].sum() }
            val t = row.sum()
            if (t == 0L) continue
            val label = if (d == DEPTH_BUCKETS - 1) "${DEPTH_BUCKETS - 1}+" else "$d"
            appendLine("    " + label.padStart(5) + "  " + row.joinToString("  ") { it.toString().padStart(9) } + "  " + t.toString().padStart(9))
        }
        appendLine()

        appendLine("  emitted depth vs limit:")
        appendLine("    depth <= limit            = ${depthWithinLimit.sum()} (${pct(depthWithinLimit.sum(), oTotal)})")
        appendLine("    depth >  limit            = ${depthOverLimit.sum()} (${pct(depthOverLimit.sum(), oTotal)})")
        for (i in 0..3) {
            appendLine("      over-limit & ${OUTCOME_LABELS[i]}".padEnd(30) + "= ${depthOverLimitByOutcome[i].sum()}")
        }
        val overLabels = arrayOf("within", "+1", "+2", "+3", "+4 or more")
        for (i in overLabels.indices) {
            appendLine("      overBy[${overLabels[i]}]".padEnd(30) + "= ${overLimitBy[i].sum()}")
        }
        appendLine()

        appendLine("  top 20 methods by barren-request count:")
        barrenByMethod.top(20).forEachIndexed { i, (k, c) ->
            appendLine("    #${i + 1} barren=$c :: $k")
        }
        appendLine("    barrenByMethod.overflow   = ${barrenByMethod.overflow.sum()}")
        appendLine()

        appendLine("-- D. cost --")
        val nu = nanosHandleUnfold.sum()
        val nt = nanosTraverse.sum()
        appendLine("  handleUnfoldRequest nanos   = $nu (${String.format("%.3f", nu / 1e9)} s)")
        appendLine("  traverse nanos (nested)     = $nt (${String.format("%.3f", nt / 1e9)} s)")
        val ne = nanosEffectRegister.sum()
        appendLine("  effect-site handleInputFactChange nanos (unfold only) = $ne (${String.format("%.3f", ne / 1e9)} s)")
        appendLine()

        appendLine("-- E. per-unit final factDepthLimit --")
        appendLine("  units with a raised limit   = ${unitMaxLimit.size}")
        val limitHist = sortedMapOf<Int, Int>()
        unitMaxLimit.values.forEach { limitHist.merge(it, 1) { a, b -> a + b } }
        limitHist.forEach { (limit, n) -> appendLine("    finalLimit=$limit  units=$n") }
        unitMaxLimit.entries.sortedByDescending { it.value }.take(20).forEach { (u, l) ->
            appendLine("    limit=$l :: $u")
        }
        appendLine("=== END UNFOLD REQUEST DIAGNOSTIC ===")
    }
}

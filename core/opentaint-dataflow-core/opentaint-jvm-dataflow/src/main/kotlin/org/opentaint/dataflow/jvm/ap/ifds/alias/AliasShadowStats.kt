package org.opentaint.dataflow.jvm.ap.ifds.alias

import mu.KLogging
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasApInfo
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasInfo
import java.util.concurrent.atomic.AtomicInteger
import java.util.concurrent.atomic.AtomicLong
import java.util.concurrent.atomic.LongAdder

/**
 * The comparison of the DSU answer and the directed answer of each query in `SHADOW` mode (IMPL §8;
 * design §11.2, V1). The facade records each query one time for each method analysis.
 *
 * The comparison uses the answers as sets. A `null` answer is the empty set (IMPL §1.5). For an
 * array element query, the DSU answer has the path `base[*]` itself; the comparison removes it (the
 * directed answer never has it).
 *
 * Summary line `group=shadow kind=<BEFORE|AFTER|ARRAY_ELEMENT|HEAP|ALL>`:
 * - `queries`: the compared queries.
 * - `equal`: both answers are not `null` and have the same set.
 * - `bothNull`: both answers are `null`. `oneNull`: one answer is `null`.
 * - `notSubset`: the directed set is not a subset of the DSU set. Each such query is logged.
 * - `precisionGain`: the DSU set is not a subset of the directed set.
 * - `skipped`: the queries that were not compared, because a backend had no result (time-out).
 * - `dsuAnswers`, `directedAnswers`: the sums of the answer sizes.
 * - `dsuAccessors`, `directedAccessors`: the sums of the accessors of the paths.
 * - `dsuLongestMax`, `directedLongestMax`: the longest path of all answers.
 *
 * Summary line `group=shadowRun`: `directedFailures` (directed analyses that stopped with an
 * exception; the DSU answers stay), `directedTimeouts`, `directedCancelled` (the parent
 * cancellation stopped the directed analysis), `diffLines` (the `ALIAS-SHADOW-DIFF` lines that the
 * process logged, at most [MAX_DIFF_LINES]).
 *
 * Diff line, at INFO, one for each `notSubset` query, at most [MAX_DIFF_LINES] for each process:
 * `ALIAS-SHADOW-DIFF method=<method> inst=<index> kind=<kind> var=local#<index> dsuSize=<n>
 * directedSize=<n> extraSize=<n> dsu=[...] directed=[...] extra=[...]`. `extra` is the directed set
 * minus the DSU set. The sizes are the full sizes. Each list shows at most [MAX_DIFF_ITEMS] items,
 * then `+<n> more`. A line has at most [MAX_DIFF_LINE_LENGTH] characters.
 */
class AliasShadowStats {
    class Counters {
        val queries = LongAdder()
        val equal = LongAdder()
        val bothNull = LongAdder()
        val oneNull = LongAdder()
        val notSubset = LongAdder()
        val precisionGain = LongAdder()
        val skipped = LongAdder()
        val dsuAnswers = LongAdder()
        val directedAnswers = LongAdder()
        val dsuAccessors = LongAdder()
        val directedAccessors = LongAdder()
        val dsuLongestMax = AtomicLong()
        val directedLongestMax = AtomicLong()

        internal fun reset() {
            listOf(
                queries, equal, bothNull, oneNull, notSubset, precisionGain, skipped,
                dsuAnswers, directedAnswers, dsuAccessors, directedAccessors,
            ).forEach { it.reset() }
            dsuLongestMax.set(0)
            directedLongestMax.set(0)
        }
    }

    private val counters = Array(AliasQueryKind.entries.size) { Counters() }

    val directedFailures = LongAdder()
    val directedTimeouts = LongAdder()
    val directedCancelled = LongAdder()

    /** The diff lines that the process logged. A reset does not change it. */
    val diffLines = AtomicInteger()

    private val failureLogs = AtomicInteger()

    fun of(kind: AliasQueryKind): Counters = counters[kind.ordinal]

    /** Counts a query that a backend without a result did not let compare. */
    fun skip(kind: AliasQueryKind) {
        of(kind).skipped.increment()
    }

    /**
     * Compares the answers of one query. [describe] gives the method, the instruction index and the
     * local of a diff line. [exclude] is a DSU item that the comparison removes (see the KDoc).
     */
    fun record(
        kind: AliasQueryKind,
        dsu: List<AliasInfo>?,
        directed: List<AliasInfo>?,
        exclude: AliasInfo?,
        describe: () -> Triple<String, Int, Int>,
    ) {
        val c = of(kind)
        c.queries.increment()
        dsu?.let {
            c.dsuAnswers.add(it.size.toLong())
            c.dsuAccessors.add(accessorSum(it))
            max(c.dsuLongestMax, longest(it))
        }
        directed?.let {
            c.directedAnswers.add(it.size.toLong())
            c.directedAccessors.add(accessorSum(it))
            max(c.directedLongestMax, longest(it))
        }
        when {
            dsu == null && directed == null -> c.bothNull.increment()
            dsu == null || directed == null -> c.oneNull.increment()
        }
        val dsuSet = dsu.orEmpty().toHashSet()
        if (exclude != null) dsuSet.remove(exclude)
        val directedSet = directed.orEmpty().toHashSet()
        if (dsu != null && directed != null && dsuSet == directedSet) c.equal.increment()
        if (!dsuSet.containsAll(directedSet)) {
            c.notSubset.increment()
            logDiff(kind, dsu.orEmpty(), directed.orEmpty(), directedSet - dsuSet, describe)
        }
        if (!directedSet.containsAll(dsuSet)) c.precisionGain.increment()
    }

    /** Counts a failure of the directed analysis. Logs the first [MAX_FAILURE_LOGS] at WARN. */
    fun failure(method: String, e: Throwable) {
        directedFailures.increment()
        if (failureLogs.incrementAndGet() <= MAX_FAILURE_LOGS) {
            logger.warn(e) { "Directed alias analysis failed in SHADOW mode for $method; the DSU answers stay" }
        }
    }

    private fun logDiff(
        kind: AliasQueryKind,
        dsu: List<AliasInfo>,
        directed: List<AliasInfo>,
        extra: Collection<AliasInfo>,
        describe: () -> Triple<String, Int, Int>,
    ) {
        while (true) {
            val n = diffLines.get()
            if (n >= MAX_DIFF_LINES) return
            if (diffLines.compareAndSet(n, n + 1)) break
        }
        val (method, inst, local) = describe()
        val line = diffLine(method, inst, kind, local, dsu, directed, extra)
        logger.info { line }
    }

    internal fun writeLines(out: MutableList<String>) {
        val all = Counters()
        for (k in AliasQueryKind.entries) {
            val c = of(k)
            out += line(k.name, c)
            for ((to, from) in listOf(
                all.queries to c.queries, all.equal to c.equal, all.bothNull to c.bothNull,
                all.oneNull to c.oneNull, all.notSubset to c.notSubset, all.precisionGain to c.precisionGain,
                all.skipped to c.skipped, all.dsuAnswers to c.dsuAnswers, all.directedAnswers to c.directedAnswers,
                all.dsuAccessors to c.dsuAccessors, all.directedAccessors to c.directedAccessors,
            )) {
                to.add(from.sum())
            }
            max(all.dsuLongestMax, c.dsuLongestMax.get().toInt())
            max(all.directedLongestMax, c.directedLongestMax.get().toInt())
        }
        out += line("ALL", all)
        out += AliasStats.line("shadowRun") {
            put("directedFailures", directedFailures.sum())
            put("directedTimeouts", directedTimeouts.sum())
            put("directedCancelled", directedCancelled.sum())
            put("diffLines", diffLines.get())
        }
    }

    private fun line(kind: String, c: Counters): String = AliasStats.line("shadow") {
        put("kind", kind)
        put("queries", c.queries.sum())
        put("equal", c.equal.sum())
        put("bothNull", c.bothNull.sum())
        put("oneNull", c.oneNull.sum())
        put("notSubset", c.notSubset.sum())
        put("precisionGain", c.precisionGain.sum())
        put("skipped", c.skipped.sum())
        put("dsuAnswers", c.dsuAnswers.sum())
        put("directedAnswers", c.directedAnswers.sum())
        put("dsuAccessors", c.dsuAccessors.sum())
        put("directedAccessors", c.directedAccessors.sum())
        put("dsuLongestMax", c.dsuLongestMax.get())
        put("directedLongestMax", c.directedLongestMax.get())
    }

    internal fun reset() {
        counters.forEach { it.reset() }
        directedFailures.reset()
        directedTimeouts.reset()
        directedCancelled.reset()
    }

    companion object {
        const val DIFF_PREFIX = "ALIAS-SHADOW-DIFF"
        const val MAX_DIFF_LINES = 300
        const val MAX_FAILURE_LOGS = 20

        /** The maximum number of items of each list of a diff line. */
        const val MAX_DIFF_ITEMS = 20

        /** The maximum length of a diff line. A longer line is cut and ends with [CUT_MARK]. */
        const val MAX_DIFF_LINE_LENGTH = 8_000

        private const val CUT_MARK = " ...(cut)"

        private val logger = object : KLogging() {}.logger

        /** The diff line of a `notSubset` query (see the KDoc of [AliasShadowStats]). */
        fun diffLine(
            method: String,
            inst: Int,
            kind: AliasQueryKind,
            local: Int,
            dsu: List<AliasInfo>,
            directed: List<AliasInfo>,
            extra: Collection<AliasInfo>,
        ): String {
            val line = "$DIFF_PREFIX method=$method inst=$inst kind=$kind var=local#$local " +
                "dsuSize=${dsu.size} directedSize=${directed.size} extraSize=${extra.size} " +
                "dsu=${items(dsu)} directed=${items(directed)} extra=${items(extra)}"
            if (line.length <= MAX_DIFF_LINE_LENGTH) return line
            return line.take(MAX_DIFF_LINE_LENGTH - CUT_MARK.length) + CUT_MARK
        }

        /** The first [MAX_DIFF_ITEMS] items of [items] in list form, then `+<n> more` if there are more. */
        private fun items(items: Collection<AliasInfo>): String {
            if (items.size <= MAX_DIFF_ITEMS) return items.toString()
            return items.take(MAX_DIFF_ITEMS).joinToString(", ", "[", ", +${items.size - MAX_DIFF_ITEMS} more]")
        }

        private fun accessorSum(answer: List<AliasInfo>): Long =
            answer.sumOf { if (it is AliasApInfo) it.accessors.size.toLong() else 0L }

        private fun longest(answer: List<AliasInfo>): Int =
            answer.maxOfOrNull { if (it is AliasApInfo) it.accessors.size else 0 } ?: 0

        private fun max(target: AtomicLong, value: Int) {
            if (value > target.get()) target.accumulateAndGet(value.toLong()) { a, b -> maxOf(a, b) }
        }
    }
}

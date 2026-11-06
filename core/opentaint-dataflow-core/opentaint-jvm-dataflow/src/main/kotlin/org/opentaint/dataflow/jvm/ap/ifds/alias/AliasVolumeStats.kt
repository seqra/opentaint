package org.opentaint.dataflow.jvm.ap.ifds.alias

import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasApInfo
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasInfo
import java.util.concurrent.ConcurrentLinkedQueue
import java.util.concurrent.atomic.AtomicLongArray
import java.util.concurrent.atomic.LongAdder

/**
 * The volume of the alias answers (IMPL §8; design §11.2, V1). Both backends record, in each mode
 * with the statistics on (`Params.recordsStatistics`). In `SHADOW` mode both answers of a query are
 * recorded.
 *
 * The facade records each query one time for each method analysis: a repeated query (the same
 * statement, local and query kind) is not recorded again. A heap-path query (tests) is recorded
 * each time.
 *
 * Summary line `group=volume backend=<DSU|DIRECTED> kind=<BEFORE|AFTER|ARRAY_ELEMENT|HEAP|ALL>`:
 * - `queries`: the recorded queries.
 * - `nullAnswers`: the queries with a `null` answer (no state, unknown local, time-out).
 * - `answers`: the sum of the answer sizes (all `AliasInfo` items, as the consumers get them).
 * - `paths`: the sum of the `AliasApInfo` items. `accessors`: the sum of their accessors.
 * - `answersP50`, `answersP99`, `answersMax`: the answer size of one query.
 * - `longestP50`, `longestP99`, `longestMax`: the longest path (accessors) of one answer.
 * - `nullOnlyPaths`: the reported paths that share with the query only null-valued origins (null
 *   constants and the default content of the fields of new objects, design R17). Directed only; the
 *   DSU line has `na`.
 *
 * Summary line `group=volumeMethods backend=<DSU|DIRECTED>`: the totals of each method analysis that
 * had a query: `methods`, then `queries`, `answers` and `accessors` as `<key>P50`, `<key>P99`,
 * `<key>Max` over the methods.
 */
class AliasVolumeStats {
    class Counters {
        val queries = LongAdder()
        val nullAnswers = LongAdder()
        val answers = LongAdder()
        val paths = LongAdder()
        val accessors = LongAdder()
        val nullOnlyPaths = LongAdder()
        val answerSizes = StatHistogram()
        val longest = StatHistogram()

        internal fun reset() {
            queries.reset()
            nullAnswers.reset()
            answers.reset()
            paths.reset()
            accessors.reset()
            nullOnlyPaths.reset()
            answerSizes.reset()
            longest.reset()
        }
    }

    /**
     * The totals of one method analysis (one facade). Index `3 * backend + i`, `i`: 0 queries,
     * 1 answers, 2 accessors.
     */
    class MethodVolume internal constructor() {
        internal val counts = AtomicLongArray(3 * AliasBackend.entries.size)
    }

    private val counters = Array(AliasBackend.entries.size) { Array(AliasQueryKind.entries.size) { Counters() } }
    private val methods = ConcurrentLinkedQueue<MethodVolume>()

    fun of(backend: AliasBackend, kind: AliasQueryKind): Counters = counters[backend.ordinal][kind.ordinal]

    /** A new record of the totals of one method analysis. The summary reads it. */
    fun newMethod(): MethodVolume = MethodVolume().also { methods.add(it) }

    /**
     * Records one answer. [nullOnlyPaths]: the count of null-only paths, or a negative value if the
     * backend does not know it.
     */
    fun record(
        backend: AliasBackend,
        kind: AliasQueryKind,
        answer: List<AliasInfo>?,
        method: MethodVolume?,
        nullOnlyPaths: Int = -1,
    ) {
        val c = of(backend, kind)
        c.queries.increment()
        val base = 3 * backend.ordinal
        method?.counts?.incrementAndGet(base)
        if (answer == null) {
            c.nullAnswers.increment()
            return
        }
        var paths = 0
        var accessors = 0L
        var longest = 0
        for (info in answer) {
            if (info !is AliasApInfo) continue
            paths++
            val n = info.accessors.size
            accessors += n
            if (n > longest) longest = n
        }
        c.answers.add(answer.size.toLong())
        c.paths.add(paths.toLong())
        c.accessors.add(accessors)
        c.answerSizes.record(answer.size.toLong())
        c.longest.record(longest.toLong())
        if (nullOnlyPaths > 0) c.nullOnlyPaths.add(nullOnlyPaths.toLong())
        if (method != null) {
            method.counts.addAndGet(base + 1, answer.size.toLong())
            method.counts.addAndGet(base + 2, accessors)
        }
    }

    internal fun hasRecords(): Boolean = methods.isNotEmpty()

    internal fun writeLines(out: MutableList<String>) {
        for (b in AliasBackend.entries) {
            val all = Counters()
            for (k in AliasQueryKind.entries) {
                val c = of(b, k)
                out += line(b, k.name, c, c.answerSizes, c.longest)
                all.queries.add(c.queries.sum())
                all.nullAnswers.add(c.nullAnswers.sum())
                all.answers.add(c.answers.sum())
                all.paths.add(c.paths.sum())
                all.accessors.add(c.accessors.sum())
                all.nullOnlyPaths.add(c.nullOnlyPaths.sum())
            }
            val sizes = StatHistogram()
            val longest = StatHistogram()
            for (k in AliasQueryKind.entries) {
                sizes.merge(of(b, k).answerSizes)
                longest.merge(of(b, k).longest)
            }
            out += line(b, "ALL", all, sizes, longest)
        }
        for (b in AliasBackend.entries) {
            val queries = StatHistogram()
            val answers = StatHistogram()
            val accessors = StatHistogram()
            val base = 3 * b.ordinal
            for (m in methods) {
                val q = m.counts.get(base)
                if (q == 0L) continue
                queries.record(q)
                answers.record(m.counts.get(base + 1))
                accessors.record(m.counts.get(base + 2))
            }
            out += AliasStats.line("volumeMethods") {
                put("backend", b.name)
                put("methods", queries.count())
                putPercentiles("queries", queries)
                putPercentiles("answers", answers)
                putPercentiles("accessors", accessors)
            }
        }
    }

    private fun line(b: AliasBackend, kind: String, c: Counters, sizes: StatHistogram, longest: StatHistogram): String =
        AliasStats.line("volume") {
            put("backend", b.name)
            put("kind", kind)
            put("queries", c.queries.sum())
            put("nullAnswers", c.nullAnswers.sum())
            put("answers", c.answers.sum())
            put("paths", c.paths.sum())
            put("accessors", c.accessors.sum())
            putPercentiles("answers", sizes)
            putPercentiles("longest", longest)
            put("nullOnlyPaths", if (b == AliasBackend.DIRECTED) c.nullOnlyPaths.sum() else "na")
        }

    private fun AliasStats.LineBuilder.putPercentiles(key: String, h: StatHistogram) {
        put("${key}P50", h.percentile(0.50))
        put("${key}P99", h.percentile(0.99))
        put("${key}Max", h.max())
    }

    internal fun reset() {
        counters.forEach { row -> row.forEach { it.reset() } }
        methods.clear()
    }
}

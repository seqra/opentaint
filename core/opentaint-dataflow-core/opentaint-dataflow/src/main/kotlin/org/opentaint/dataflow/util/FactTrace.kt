package org.opentaint.dataflow.util

import java.util.concurrent.atomic.AtomicLong

/**
 * A trace of how one taint fact EVOLVES, for a scoped run (one rule, one entry point).
 *
 * The point is observation, not measurement. Every earlier attempt in this investigation proposed
 * an operator and then measured whether it converged; none of them asked what the fact population
 * is actually made of. This answers that, at the four places a fact can change:
 *
 * * `ARRIVE` -- a fact reaches a method entry and the abstraction runs on it.
 * * `PAIR`   -- the (premise, fact) pairs that arrival produced. This is where the premise
 *               population comes from, so it is where "why do we have these premises" is answered.
 * * `SUMMARY`-- a callee summary is applied in a caller, which is the step that GROWS a fact.
 * * `SOURCE` -- the fact a taint source introduces, i.e. the root of every chain.
 *
 * Output is one line per event, tab separated, so it can be grouped with `sort`/`awk`. Off unless
 * `-Dopentaint.factTrace=<file>` is set; the check is a null test on a `val`, so a normal run pays
 * one predictable branch.
 */
object FactTrace {
    private val path: String? = System.getProperty("opentaint.factTrace")

    val enabled: Boolean = path != null

    /** Cap the file: a scoped run should be small, but an unscoped one must not fill the disk. */
    private val limit: Long =
        System.getProperty("opentaint.factTraceLimit")?.toLongOrNull() ?: 3_000_000L

    /** Per-field character cap. See [f]. */
    private val FIELD_CAP: Int =
        System.getProperty("opentaint.factTraceFieldCap")?.toIntOrNull() ?: 200

    /**
     * Which event kinds to record, comma separated; empty means all.
     *
     * SUMMARY is about 60% of the lines, so a run that only needs the fact population can capture
     * every ARRIVE within a small file. Measured the hard way: an uncapped full-ruleset trace hit a
     * 2.5M line cap after 2.5M of 4.5M events, and the distinct-shape counts taken from that prefix
     * were wrong.
     */
    private val kinds: Set<String> =
        System.getProperty("opentaint.factTraceEvents")?.split(',')?.map { it.trim() }
            ?.filter { it.isNotEmpty() }?.toSet() ?: emptySet()

    private fun wants(kind: String): Boolean = kinds.isEmpty() || kind in kinds

    private val seq = AtomicLong()
    private val dropped = AtomicLong()
    private val lock = Any()

    private val out: java.io.PrintWriter? =
        path?.let { java.io.PrintWriter(java.io.BufferedWriter(java.io.FileWriter(it), 1 shl 20)) }

    /**
     * One field, made safe for a line-oriented file.
     *
     * MEASURED the hard way: `SummaryEdge.toString()` is multi-line, so an unsanitised trace of
     * 1.8M events produced 120.9M physical lines and no field-based tool could read it. Newlines
     * and tabs become spaces, and runs of spaces collapse, so one event is always one line.
     */
    private fun f(v: Any?): String {
        val s = v?.toString() ?: "null"
        val sb = StringBuilder(s.length)
        var lastSpace = false
        for (c in s) {
            val space = c == '\n' || c == '\r' || c == '\t' || c == ' '
            if (space) { if (!lastSpace) sb.append(' '); lastSpace = true }
            else { sb.append(c); lastSpace = false }
        }
        // And CAP it. `SummaryEdge.toString()` runs to about 10 KB, which turned a 1.1M-event
        // scoped run into an 11 GB file. The head of an access path carries the shape; the tail is
        // repetition, so a cap loses nothing an analysis of the SHAPE needs.
        val t = sb.toString().trim()
        return if (t.length <= FIELD_CAP) t else t.take(FIELD_CAP) + "~" + t.length
    }

    private fun emit(line: String) {
        val w = out ?: return
        if (seq.incrementAndGet() > limit) { dropped.incrementAndGet(); return }
        synchronized(lock) { w.println(line) }
    }

    /**
     * The SHAPE of an arriving fact, as numbers. Exact where a text dump is not: at a 20,000
     * character field cap, 29% of arriving facts were still truncated.
     */
    fun shape(method: Any, paths: Long, markFree: Long, marks: Long, depth: Long, size: Long) {
        if (out == null || !wants("SHAPE")) return
        emit("SHAPE\t${f(method)}\t$paths\t$markFree\t$marks\t$depth\t$size")
    }

    /** A fact reaches a method entry point. */
    fun arrive(method: Any, fact: Any) {
        if (out == null || !wants("ARRIVE")) return
        emit("ARRIVE\t${f(method)}\t${f(fact)}")
    }

    /** The abstraction turned that arrival into a (premise, fact) pair. */
    fun pair(method: Any, premise: Any, fact: Any) {
        if (out == null || !wants("PAIR")) return
        emit("PAIR\t${f(method)}\t${f(premise)}\t${f(fact)}")
    }

    /**
     * A callee summary was applied at a call site: the step that GROWS a fact.
     *
     * Deliberately NOT the whole `SummaryEdge`. Its `toString()` runs to about 10 KB and turned one
     * scoped run into an 11 GB file. The call SITE plus the caller's fact is what answers "which
     * summaries do we have and what do they do to the fact"; the edge's interior is repetition.
     */
    fun summary(caller: Any, site: Any, fact: Any, edge: Any?) {
        if (out == null || !wants("SUMMARY")) return
        // The summary's IDENTITY, not its text. `SummaryEdge.toString()` is ~10 KB, but a stable
        // hash is enough to answer the question that matters: when the same (site, fact) is
        // re-applied 16 times, is it 16 DIFFERENT summaries (genuine incremental work as the callee
        // learns more) or the SAME one (pure waste)?
        val id = edge?.let { java.lang.Integer.toHexString(it.hashCode()) } ?: "-"
        emit("SUMMARY\t${f(caller)}\t${f(site)}\t${f(fact)}\t$id")
    }

    /** A taint source introduced a fact -- the root of a chain. */
    fun source(method: Any, rule: Any, fact: Any) {
        if (out == null || !wants("SOURCE")) return
        emit("SOURCE\t${f(method)}\t${f(rule)}\t${f(fact)}")
    }

    fun report(): String =
        if (out == null) "factTrace=off"
        else "factTrace=on lines=" + seq.get() + " dropped=" + dropped.get()

    fun flush() { out?.flush() }

    private val hook = Thread { out?.flush() }
        .also { if (out != null) Runtime.getRuntime().addShutdownHook(it) }
}

package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.ANY_ACCESSOR_IDX
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.atomic.AtomicInteger

/**
 * How many distinct SUMMARY PREMISES each method accumulates, and how many of them carry an `[any]`.
 *
 * A summary premise is an entry in [MethodInitialToFinalApSummaries]' storage: the initial fact a
 * summary edge is keyed on. It is a different quantity from the `sum:` column of the existing
 * per-method stats, which counts summary APPLICATIONS handled -- a method can apply one premise a
 * hundred thousand times, or hold a hundred thousand premises applied once each, and only the second
 * is a population problem.
 *
 * Counted at the point a premise node is first created, so nothing has to enumerate the storages at
 * the end of the run.
 *
 * `-Dopentaint.summaryPremiseDiag=true`.
 */
object SummaryPremiseDiagnostics {
    val enabled: Boolean = System.getProperty("opentaint.summaryPremiseDiag")?.trim().toBoolean()

    /** How many methods the end-of-run ranking lists. `-Dopentaint.summaryPremiseTop=N`. */
    val reportTopN: Int = System.getProperty("opentaint.summaryPremiseTop")?.trim()?.toIntOrNull() ?: 20

    /**
     * The TARGETED trace: a substring of the method signature.
     *
     * The ranking says WHICH method holds the premises; it cannot say what they spell or who made
     * them. For every method whose signature contains this, each premise is recorded verbatim as it
     * is created, with the call statement parked by [TifaDiagnostics] and -- for the first few -- the
     * stack that built it, which is the only thing that distinguishes the initial-fact walk from the
     * side-effect path.
     *
     * `-Dopentaint.summaryPremiseTrace=<substring of the method signature>`.
     */
    val traceKey: String? = System.getProperty("opentaint.summaryPremiseTrace")?.trim()?.takeIf { it.isNotEmpty() }

    /** Premises kept for a targeted method, and stacks captured. Both bounded. */
    const val TRACE_MAX_PREMISES = 4_000
    const val TRACE_MAX_STACKS = 16

    /** Longest premises kept for EVERY method, so the ranking rows carry a shape as well as a count. */
    const val SAMPLES_PER_METHOD = 6

    private val counters = ConcurrentHashMap<String, MethodSummaryPremises>()

    fun counterFor(method: String): MethodSummaryPremises =
        counters.computeIfAbsent(method) { MethodSummaryPremises(it) }

    fun report(topN: Int): String {
        val all = counters.values.sortedByDescending { it.total() }
        return buildString {
            appendLine("Summary premises: ${all.sumOf { it.total() }} over ${all.size} methods")
            all.take(topN).forEach { c ->
                appendLine("  $c")
                c.sampleLines().forEach { appendLine("      $it") }
            }
        }
    }

    /** Every premise of every method matching [traceKey], with the site and the builder's stack. */
    fun dumpTargeted(): String {
        val key = traceKey ?: return "no summary premise trace key set"
        val hits = counters.values.filter { it.matchesTraceKey }.sortedByDescending { it.total() }
        if (hits.isEmpty()) return "no method matched summary premise trace key '$key'"
        return buildString {
            appendLine("TARGETED PREMISE TRACE for '$key' -- ${hits.size} matching methods")
            hits.forEach { append(it.dumpTraced()) }
        }
    }
}

class MethodSummaryPremises(private val method: String) {
    /** Whether this method is the one [SummaryPremiseDiagnostics.traceKey] asked for. */
    @JvmField
    val matchesTraceKey: Boolean = SummaryPremiseDiagnostics.traceKey?.let { method.contains(it) } == true

    /** Identity summaries -- a premise that passes straight through. */
    @JvmField val idPremises = AtomicInteger()

    /** Real summaries -- a premise with an exit fact that is not just the premise itself. */
    @JvmField val apPremises = AtomicInteger()

    /** Of the above, how many carry an `[any]` link. */
    @JvmField val anyPremises = AtomicInteger()

    /** The longest premise chain this method was keyed on, in links. */
    @JvmField val maxPremiseLinks = AtomicInteger()

    fun total(): Int = idPremises.get() + apPremises.get()

    /** Premises by link count, so a long tail cannot hide behind [maxPremiseLinks]. */
    private val linkBuckets = java.util.concurrent.atomic.AtomicLongArray(LINK_BUCKETS)

    /** The longest premises seen, for the ranking rows. Small and bounded, kept for every method. */
    private val samples = java.util.Collections.synchronizedList(ArrayList<Pair<Int, String>>())

    /** Every premise, in creation order, for the targeted method only. */
    private val traced = java.util.Collections.synchronizedList(ArrayList<String>())
    private val stacks = java.util.Collections.synchronizedList(ArrayList<String>())

    fun record(access: AccessPath.AccessNode?, identity: Boolean) {
        if (identity) idPremises.incrementAndGet() else apPremises.incrementAndGet()

        var links = 0
        var carriesAny = false
        var node = access
        while (node != null) {
            links++
            if (node.accessor == ANY_ACCESSOR_IDX) carriesAny = true
            node = node.next
        }

        if (carriesAny) anyPremises.incrementAndGet()
        linkBuckets.incrementAndGet(links.coerceIn(0, LINK_BUCKETS - 1))

        var cur = maxPremiseLinks.get()
        while (links > cur && !maxPremiseLinks.compareAndSet(cur, links)) cur = maxPremiseLinks.get()

        if (matchesTraceKey) recordTraced(access, identity, links, carriesAny)
        recordSample(access, links)
    }

    /**
     * A premise is created once, so this runs at most [SummaryPremiseDiagnostics.TRACE_MAX_PREMISES]
     * times per traced method -- the rendering cost is paid on the rare side.
     */
    private fun recordTraced(access: AccessPath.AccessNode?, identity: Boolean, links: Int, any: Boolean) {
        if (traced.size < SummaryPremiseDiagnostics.TRACE_MAX_PREMISES) {
            traced.add(
                "#${traced.size} ${if (identity) "id" else "ap"} links=$links any=$any" +
                    " | at ${TifaDiagnostics.siteOf(TifaDiagnostics.callSite.get())}" +
                    " | ${access?.toString()?.take(320) ?: "<empty>"}"
            )
        }

        if (stacks.size < SummaryPremiseDiagnostics.TRACE_MAX_STACKS) {
            val frames = Thread.currentThread().stackTrace
                .map { it.toString() }
                .filter { it.startsWith("org.opentaint") }
                .filterNot { it.contains("SummaryPremiseDiagnostics") || it.contains("MethodSummaryPremises") }
                .take(20)
                .joinToString("\n        ")
            stacks.add("at premise #${traced.size}\n        $frames")
        }
    }

    private fun recordSample(access: AccessPath.AccessNode?, links: Int) {
        if (links < 2) return
        synchronized(samples) {
            if (samples.size >= SummaryPremiseDiagnostics.SAMPLES_PER_METHOD &&
                links <= samples.minOf { it.first }
            ) {
                return
            }
            samples.add(links to (access?.toString()?.take(220) ?: "<empty>"))
            if (samples.size > SummaryPremiseDiagnostics.SAMPLES_PER_METHOD) {
                val worst = samples.minByOrNull { it.first }
                samples.remove(worst)
            }
        }
    }

    fun sampleLines(): List<String> =
        synchronized(samples) { samples.sortedByDescending { it.first }.map { "links=${it.first} ${it.second}" } }

    fun dumpTraced(): String = buildString {
        appendLine("  --- $method")
        appendLine("    ${this@MethodSummaryPremises}")
        appendLine("    links=[${renderBuckets()}]")
        appendLine("    --- all ${traced.size} premises, in creation order ---")
        synchronized(traced) { traced.forEach { appendLine("      $it") } }
        appendLine("    --- who built them ---")
        synchronized(stacks) { stacks.forEach { appendLine("      $it") } }
    }

    private fun renderBuckets(): String =
        (0 until LINK_BUCKETS).map { linkBuckets.get(it) }.dropLastWhile { it == 0L }.joinToString(",")

    override fun toString(): String =
        "premises: ${total()} | id: ${idPremises.get()} | ap: ${apPremises.get()}" +
            " | any: ${anyPremises.get()} | maxLinks: ${maxPremiseLinks.get()}" +
            " | links=[${renderBuckets()}] | $method"

    private companion object {
        const val LINK_BUCKETS = 32
    }
}

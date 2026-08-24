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

    private val counters = ConcurrentHashMap<String, MethodSummaryPremises>()

    fun counterFor(method: String): MethodSummaryPremises =
        counters.computeIfAbsent(method) { MethodSummaryPremises(it) }

    fun report(topN: Int): String {
        val all = counters.values.sortedByDescending { it.total() }
        return buildString {
            appendLine("Summary premises: ${all.sumOf { it.total() }} over ${all.size} methods")
            all.take(topN).forEach { appendLine("  $it") }
        }
    }
}

class MethodSummaryPremises(private val method: String) {
    /** Identity summaries -- a premise that passes straight through. */
    @JvmField val idPremises = AtomicInteger()

    /** Real summaries -- a premise with an exit fact that is not just the premise itself. */
    @JvmField val apPremises = AtomicInteger()

    /** Of the above, how many carry an `[any]` link. */
    @JvmField val anyPremises = AtomicInteger()

    /** The longest premise chain this method was keyed on, in links. */
    @JvmField val maxPremiseLinks = AtomicInteger()

    fun total(): Int = idPremises.get() + apPremises.get()

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

        var cur = maxPremiseLinks.get()
        while (links > cur && !maxPremiseLinks.compareAndSet(cur, links)) cur = maxPremiseLinks.get()
    }

    override fun toString(): String =
        "premises: ${total()} | id: ${idPremises.get()} | ap: ${apPremises.get()}" +
            " | any: ${anyPremises.get()} | maxLinks: ${maxPremiseLinks.get()} | $method"
}

package org.opentaint.dataflow.ap.ifds.access.tree

import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.atomic.AtomicInteger
import java.util.concurrent.atomic.AtomicLong

/**
 * Where the initial-fact abstraction's premises come from.
 *
 * Premises are emitted by WALKING `MethodSameBaseInitialFact.added` -- the merged tree of every fact
 * that has arrived at this `(method entry point, access-path base)`. So the premise count is a
 * function of how big and how branchy that tree is, and the question "why so many premises" is
 * really "why is `added` so large".
 *
 * The counters split the answer three ways: how much is ARRIVING (facts merged in, and how many of
 * those actually grew the tree), how much the tree GREW to, and how much the walk EMITS per unit of
 * tree. A method with a small `added` and many emits has a branchy walk; a method with a huge
 * `added` has an arrival problem, and the arrivals come from summary application.
 *
 * `-Dopentaint.tifaDiag=true`.
 */
object TifaDiagnostics {
    val enabled: Boolean = System.getProperty("opentaint.tifaDiag")?.trim().toBoolean()

    /** Facts handed to the abstraction, and how many of them actually grew `added`. */
    val addCalls = AtomicLong()
    val addDeltas = AtomicLong()

    /** Walk cost: states popped, premises emitted, and how many states crossed an `[any]` edge. */
    val walkStates = AtomicLong()
    val emits = AtomicLong()
    val anyDescents = AtomicLong()

    /** The unroll, separated from every other refusal so the two are not confused again. */
    val unrollRequests = AtomicLong()
    val unrollAccessorsOffered = AtomicLong()
    val unrollMaterialised = AtomicLong()
    val unrollRefusedByBudget = AtomicLong()

    private val perBase = ConcurrentHashMap<String, BaseStats>()

    fun baseStats(key: String): BaseStats = perBase.computeIfAbsent(key) { BaseStats(it) }

    fun report(topN: Int): String {
        val all = perBase.values.sortedByDescending { it.maxAddedSize.get() }
        return buildString {
            append("tifa addCalls=").append(addCalls.get())
            append(" addDeltas=").append(addDeltas.get())
            append(" walkStates=").append(walkStates.get())
            append(" emits=").append(emits.get())
            append(" anyDescents=").append(anyDescents.get())
            append(" unrollRequests=").append(unrollRequests.get())
            append(" accessorsOffered=").append(unrollAccessorsOffered.get())
            append(" materialised=").append(unrollMaterialised.get())
            append(" refusedByBudget=").append(unrollRefusedByBudget.get())
            appendLine()
            appendLine("added trees: ${all.size} (method, base) pairs")
            all.take(topN).forEach { appendLine("  $it") }
        }
    }
}

class BaseStats(private val key: String) {
    /** Nodes in `added`, counted with multiplicity -- the precomputed subtree size. */
    @JvmField val maxAddedSize = AtomicLong()

    /** Its depth, which separates "wide" from "deep". */
    @JvmField val maxAddedDepth = AtomicInteger()

    /** Whether this base's `added` ever carried an `[any]` anywhere. */
    @JvmField val everCarriedAny = AtomicInteger()

    @JvmField val addCalls = AtomicLong()
    @JvmField val emits = AtomicLong()

    fun recordAdded(node: AccessTree.AccessNode) {
        var cur = maxAddedSize.get()
        while (node.size > cur && !maxAddedSize.compareAndSet(cur, node.size)) cur = maxAddedSize.get()

        var d = maxAddedDepth.get()
        while (node.maxDepth > d && !maxAddedDepth.compareAndSet(d, node.maxDepth)) d = maxAddedDepth.get()

        if (node.containsAnyInThisOrDeepNodes) everCarriedAny.set(1)
    }

    override fun toString(): String =
        "added: ${maxAddedSize.get()} | depth: ${maxAddedDepth.get()} | any: ${everCarriedAny.get()}" +
            " | adds: ${addCalls.get()} | emits: ${emits.get()} | $key"
}

package org.opentaint.dataflow.ap.ifds.access.tree

import java.util.concurrent.atomic.AtomicLong
import java.util.concurrent.atomic.AtomicLongArray

/**
 * Which OPERATION creates the nodes.
 *
 * [TifaDiagnostics] answers "which `(method, base)` accumulator grew, and which caller fed it". It
 * cannot answer "which operation manufactured the nodes that arrived", because by the time a fact
 * reaches the abstraction it is already built. There are only four operations in the engine that can
 * return more nodes than they were given, and this separates them so their contributions can be
 * compared rather than argued about:
 *
 *  - **A, the TIFA `[any]` unroll** (`TreeInitialFactAbstraction.unrollAnyAccessors`): re-roots the
 *    `[any]`-CARRYING node under `prefix.c` once per demanded accessor `c`.
 *  - **B, the `getChild` synthesis** (`AccessNode.getChild`, the `isCoveredByAny` arm): a READ
 *    returns the literal child merged with the whole `[any]` subtree, re-wrapped in a fresh `[any]`.
 *  - **C, the summary graft** (`AccessNode.concatToLeafAbstractNodes`): attaches the delta at EVERY
 *    abstract node of the receiver.
 *  - **D, `filterStartsWith`**: the summary-delivery read channel, which descends with B and
 *    re-prepends what it matched.
 *
 * Every counter is a NODE count (`AccessNode.size`, multiplicity), so the columns are commensurable
 * and "growth" means the same thing in each row.
 *
 * `-Dopentaint.apOpDiag=true`.
 */
object ApOpDiagnostics {
    val enabled: Boolean = System.getProperty("opentaint.apOpDiag")?.trim().toBoolean()

    private const val DEPTH_BUCKETS = 24

    // ---- A: the TIFA [any] unroll -------------------------------------------------------------

    /** Calls to `unrollAnyAccessors` that had at least one request. */
    val unrollCalls = AtomicLong()

    /** Requests seen, and accessors offered by the demand trie across them. */
    val unrollRequests = AtomicLong()
    val unrollOffered = AtomicLong()

    /** Accessors that survived every filter and produced a re-rooted copy. */
    val unrollMaterialised = AtomicLong()

    /**
     * Nodes in the object being re-rooted, summed over materialised accessors.
     *
     * Split deliberately: [unrollCarrierNodes] is the node that OWNS the `[any]` edge -- what the
     * unroll actually copies -- and [unrollAnyChildNodes] is the `[any]` subtree alone, which is what
     * "unrolling the `[any]`" sounds like it should copy. The gap between the two columns is the
     * whole question.
     */
    val unrollCarrierNodes = AtomicLong()
    val unrollAnyChildNodes = AtomicLong()

    /** Nodes in the merged round result, and the delta it actually added to `added`. */
    val unrollMergedNodes = AtomicLong()
    val unrollAddedDelta = AtomicLong()

    /** Whether the copy the unroll re-roots still carries an `[any]` of its own. */
    val unrollCopyCarriesAny = AtomicLong()
    val unrollCopyAnyFree = AtomicLong()

    /** Requests by prefix depth: round r of the fixed point produces prefixes of depth r. */
    val unrollPrefixDepth = AtomicLongArray(DEPTH_BUCKETS)

    /** Materialised accessors by prefix depth, so the fan-out per level is visible. */
    val unrollMaterialisedAtDepth = AtomicLongArray(DEPTH_BUCKETS)

    // ---- B: the getChild [any] synthesis -------------------------------------------------------

    val anyReadCalls = AtomicLong()

    /** Nodes the fact LITERALLY holds under the accessor (0 when it holds none). */
    val anyReadLiteralNodes = AtomicLong()

    /** Nodes the read RETURNS. */
    val anyReadResultNodes = AtomicLong()

    /** Reads that returned strictly more than the literal child, and by how much. */
    val anyReadGrew = AtomicLong()
    val anyReadGrowth = AtomicLong()

    /** Reads where the fact held no literal child at all -- the accessor is pure synthesis. */
    val anyReadFromNothing = AtomicLong()

    // ---- C: the summary graft ------------------------------------------------------------------

    val concatCalls = AtomicLong()
    val concatReceiverNodes = AtomicLong()
    val concatDeltaNodes = AtomicLong()
    val concatResultNodes = AtomicLong()
    val concatGrew = AtomicLong()
    val concatGrowth = AtomicLong()

    // ---- D: filterStartsWith -------------------------------------------------------------------

    val fswCalls = AtomicLong()
    val fswInNodes = AtomicLong()
    val fswOutNodes = AtomicLong()
    val fswGrew = AtomicLong()
    val fswGrowth = AtomicLong()

    // ---- worked examples -----------------------------------------------------------------------

    /**
     * The single biggest event of each kind, REPLACED as bigger ones arrive.
     *
     * The first version appended to a bounded list while separately tracking the max, so it kept the
     * first fourteen record-breakers -- all of them tiny, because a monotonically rising maximum
     * breaks its own record most often at the very start. Keeping one slot per kind and overwriting
     * it is the only shape that ends up holding the maximum.
     */
    private val biggest = java.util.concurrent.ConcurrentHashMap<String, Pair<Long, String>>()

    fun example(kind: String, growth: Long, render: () -> String) {
        if (!enabled) return
        biggest.compute(kind) { _, prev ->
            if (prev != null && growth <= prev.first) prev else growth to render().take(700)
        }
    }

    /**
     * Distinct unroll prefixes at depth >= [PREFIX_SAMPLE_MIN_DEPTH].
     *
     * The counters say the ladder reaches depth 7; these say what a rung actually spells, which is
     * what makes "every non-repeating sequence over the demand set" checkable against real data
     * rather than against the unit reproducer alone.
     */
    const val PREFIX_SAMPLE_MIN_DEPTH = 5
    private const val PREFIX_SAMPLES = 20
    private val prefixSamples = java.util.Collections.synchronizedSet(LinkedHashSet<String>())

    fun samplePrefix(depth: Int, render: () -> String) {
        if (!enabled || depth < PREFIX_SAMPLE_MIN_DEPTH) return
        if (prefixSamples.size >= PREFIX_SAMPLES) return
        prefixSamples.add("d$depth ${render().take(300)}")
    }

    fun recordUnrollRequest(prefixDepth: Int, offered: Int, carrier: Long, anyChild: Long) {
        unrollRequests.incrementAndGet()
        unrollOffered.addAndGet(offered.toLong())
        unrollCarrierNodes.addAndGet(carrier)
        unrollAnyChildNodes.addAndGet(anyChild)
        unrollPrefixDepth.incrementAndGet(prefixDepth.coerceIn(0, DEPTH_BUCKETS - 1))
    }

    fun recordUnrollMaterialised(prefixDepth: Int, copyCarriesAny: Boolean) {
        unrollMaterialised.incrementAndGet()
        unrollMaterialisedAtDepth.incrementAndGet(prefixDepth.coerceIn(0, DEPTH_BUCKETS - 1))
        if (copyCarriesAny) unrollCopyCarriesAny.incrementAndGet() else unrollCopyAnyFree.incrementAndGet()
    }

    private fun AtomicLongArray.render(): String =
        (0 until DEPTH_BUCKETS).map { get(it) }.dropLastWhile { it == 0L }.joinToString(",")

    private fun ratio(a: Long, b: Long): String = if (b == 0L) "-" else String.format("%.2f", a.toDouble() / b)

    fun report(): String = buildString {
        appendLine(
            "apop A-unroll calls=${unrollCalls.get()} requests=${unrollRequests.get()}" +
                " offered=${unrollOffered.get()} materialised=${unrollMaterialised.get()}" +
                " carrierNodes=${unrollCarrierNodes.get()} anyChildNodes=${unrollAnyChildNodes.get()}" +
                " mergedNodes=${unrollMergedNodes.get()} addedDelta=${unrollAddedDelta.get()}"
        )
        appendLine(
            "apop A-unroll copyCarriesAny=${unrollCopyCarriesAny.get()} copyAnyFree=${unrollCopyAnyFree.get()}" +
                " carrierPerRequest=${ratio(unrollCarrierNodes.get(), unrollRequests.get())}" +
                " nodesPerMaterialised=${ratio(unrollCarrierNodes.get(), unrollMaterialised.get())}"
        )
        appendLine("apop A-unroll requestsByPrefixDepth=[${unrollPrefixDepth.render()}]")
        appendLine("apop A-unroll materialisedByPrefixDepth=[${unrollMaterialisedAtDepth.render()}]")
        appendLine(
            "apop B-getChildAny calls=${anyReadCalls.get()} literalNodes=${anyReadLiteralNodes.get()}" +
                " resultNodes=${anyReadResultNodes.get()} grew=${anyReadGrew.get()}" +
                " growth=${anyReadGrowth.get()} fromNothing=${anyReadFromNothing.get()}" +
                " growthPerCall=${ratio(anyReadGrowth.get(), anyReadCalls.get())}"
        )
        appendLine(
            "apop C-concat calls=${concatCalls.get()} receiverNodes=${concatReceiverNodes.get()}" +
                " deltaNodes=${concatDeltaNodes.get()} resultNodes=${concatResultNodes.get()}" +
                " grew=${concatGrew.get()} growth=${concatGrowth.get()}" +
                " growthPerCall=${ratio(concatGrowth.get(), concatCalls.get())}"
        )
        appendLine(
            "apop D-filterStartsWith calls=${fswCalls.get()} inNodes=${fswInNodes.get()}" +
                " outNodes=${fswOutNodes.get()} grew=${fswGrew.get()} growth=${fswGrowth.get()}"
        )
        appendLine("apop --- biggest single event of each kind ---")
        biggest.forEach { (kind, e) -> appendLine("apop   [$kind +${e.first}] ${e.second}") }
        appendLine("apop --- unroll prefixes at depth >= $PREFIX_SAMPLE_MIN_DEPTH ---")
        prefixSamples.forEach { appendLine("apop   $it") }
    }
}

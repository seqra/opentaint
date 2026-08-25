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

    // ---- C, in detail: what the graft actually does --------------------------------------------

    /**
     * How many abstract nodes of the receiver the delta was actually attached at, per call.
     *
     * This is the multiplier in `|result| ~ |receiver| + k * |delta|`. Counted exactly rather than
     * sampled, because the whole question is whether the graft MULTIPLIES (k large) or merely
     * RELOCATES the caller's remainder to a new prefix (k = 1).
     */
    val concatGraftPoints = AtomicLong()
    val concatGraftPointsMax = AtomicLong()

    /** Calls by graft-point count, so a heavy tail cannot hide behind a mean of 1. */
    val concatGraftPointBuckets = AtomicLongArray(DEPTH_BUCKETS)

    /** Calls by log2 of growth: the shape of the distribution, not just its mean. */
    val concatGrowthBuckets = AtomicLongArray(DEPTH_BUCKETS)

    /**
     * Deep profile, sampled 1 call in [CONCAT_SAMPLE_RATE].
     *
     * `AccessNode.size` counts with MULTIPLICITY, and `FilteredNode.create` interns the delta before
     * grafting, so a graft can multiply `size` while allocating almost nothing. Distinct-node counts
     * are the only way to tell those two apart, and `countNodes()` is O(n) -- hence the sampling.
     */
    const val CONCAT_SAMPLE_RATE = 512
    val concatSamples = AtomicLong()
    val concatSampleRecvSize = AtomicLong()
    val concatSampleRecvDistinct = AtomicLong()
    val concatSampleDeltaSize = AtomicLong()
    val concatSampleDeltaDistinct = AtomicLong()
    val concatSampleResultSize = AtomicLong()
    val concatSampleResultDistinct = AtomicLong()
    val concatSampleRecvAbstract = AtomicLong()

    private val concatCallCounter = AtomicLong()

    /** Mutable per-thread box: the recursion is hot, so this must not allocate per call. */
    class IntBox { @JvmField var value: Int = 0 }

    val graftPointCounter: ThreadLocal<IntBox> = ThreadLocal.withInitial { IntBox() }

    fun concatShouldSample(): Boolean =
        enabled && concatCallCounter.incrementAndGet() % CONCAT_SAMPLE_RATE == 0L

    fun recordConcatShape(graftPoints: Int, growth: Long) {
        concatGraftPoints.addAndGet(graftPoints.toLong())
        concatGraftPointsMax.updateAndGet { maxOf(it, graftPoints.toLong()) }
        concatGraftPointBuckets.incrementAndGet(graftPoints.coerceIn(0, DEPTH_BUCKETS - 1))
        concatGrowthBuckets.incrementAndGet(log2Bucket(growth))
    }

    private fun log2Bucket(v: Long): Int {
        if (v <= 0) return 0
        var b = 0
        var x = v
        while (x > 1 && b < DEPTH_BUCKETS - 1) { x = x shr 1; b++ }
        return b
    }

    // ---- E: delta(), which produces what C grafts ----------------------------------------------

    /**
     * `AccessTree.delta(premise)` decides what a graft receives: it walks the caller's fact DOWN the
     * summary's premise and returns what is left hanging below it.
     *
     * The walk uses `getChildRecording`, and a step through an `[any]` CONSUMES NOTHING -- the
     * `isCoveredByAny` arm returns the node it read from, re-wrapped. So a premise carrying an
     * `[any]` leaves nearly the whole caller fact as the remainder, and `concat` then re-attaches
     * that whole fact under the conclusion instead of advancing past it. Splitting the counters by
     * whether the premise carries an `[any]` is the only way to see that.
     */
    val deltaCalls = AtomicLong()
    val deltaFactNodes = AtomicLong()
    val deltaResultNodes = AtomicLong()
    val deltaPremiseLinks = AtomicLong()

    val deltaAnyCalls = AtomicLong()
    val deltaAnyFactNodes = AtomicLong()
    val deltaAnyResultNodes = AtomicLong()
    val deltaAnyPremiseLinks = AtomicLong()

    /** Calls where the remainder is at least as large as the fact it was cut from. */
    val deltaNotSmaller = AtomicLong()
    val deltaAnyNotSmaller = AtomicLong()

    fun recordDelta(premiseCarriesAny: Boolean, factNodes: Long, premiseLinks: Int, resultNodes: Long) {
        if (premiseCarriesAny) {
            deltaAnyCalls.incrementAndGet()
            deltaAnyFactNodes.addAndGet(factNodes)
            deltaAnyResultNodes.addAndGet(resultNodes)
            deltaAnyPremiseLinks.addAndGet(premiseLinks.toLong())
            if (resultNodes >= factNodes) deltaAnyNotSmaller.incrementAndGet()
        } else {
            deltaCalls.incrementAndGet()
            deltaFactNodes.addAndGet(factNodes)
            deltaResultNodes.addAndGet(resultNodes)
            deltaPremiseLinks.addAndGet(premiseLinks.toLong())
            if (resultNodes >= factNodes) deltaNotSmaller.incrementAndGet()
        }
    }

    // ---- F: the hypothesis -- delta reads THROUGH an [any] and concat prepends in front of it ---

    /**
     * The round trip `arg0.[any].*` + premise `arg0.a` -> conclusion `ret.a.*` => `ret.a.[any].*`.
     *
     * `getChild`'s `isCoveredByAny` arm returns the node it read FROM, re-wrapped in a fresh `[any]`:
     * the read consumes nothing. So `delta()` against a concrete premise hands back a remainder that
     * still carries the `[any]`, and `concat` re-attaches it below the conclusion's concrete prefix.
     * Net effect of one summary application: the fact is one concrete link longer and still carries
     * an `[any]` — a fixed point with a ratchet.
     *
     * These counters isolate exactly that round trip. [deltaThroughAnyKept] is the load-bearing one:
     * a remainder that both crossed an `[any]` and still carries one is a step that made no progress.
     */
    val deltaThroughAny = AtomicLong()
    val deltaThroughAnyKept = AtomicLong()
    val deltaThroughAnyNotSmaller = AtomicLong()
    val deltaThroughAnyFactNodes = AtomicLong()
    val deltaThroughAnyRemainderNodes = AtomicLong()

    /** Result depth minus receiver depth, for grafts whose delta carries an `[any]`. */
    val concatAnyDeltaCalls = AtomicLong()
    val concatAnyDeltaDepthGain = AtomicLong()
    val concatAnyDeltaResultKeepsAny = AtomicLong()

    /** Verbatim round trips: premise, fact, remainder, conclusion, result. */
    private const val ROUNDTRIP_SAMPLES = 10
    private val roundTrips = java.util.Collections.synchronizedList(ArrayList<String>())

    fun sampleRoundTrip(render: () -> String) {
        if (!enabled || roundTrips.size >= ROUNDTRIP_SAMPLES) return
        roundTrips.add(render().take(520))
    }

    /** Set by `getChild`'s synthesis arm, read and cleared by `delta`. */
    val crossedAnyFlag: ThreadLocal<IntBox> = ThreadLocal.withInitial { IntBox() }

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

    // ---- I: can the type filter at a graft point reject anything at all? -----------------------

    /**
     * The shape of the accessor path the graft hands to `FactTypeChecker.accessPathFilter`.
     *
     * `JIRFactTypeChecker.accessorActualType` reads ONLY `accessPath.lastOrNull()`, and returns
     * `null` -- i.e. an always-accept filter -- for an empty path and for a path whose last step is
     * `[any]`. So at those graft points the delta is attached with no type test whatsoever, and the
     * `[any]` does not merely widen the fact: it switches the type system off for what comes next.
     *
     * Counting the three cases separately turns that from a code reading into a measurement.
     */
    val graftFilterEmptyPath = AtomicLong()
    val graftFilterAnyTail = AtomicLong()
    val graftFilterTyped = AtomicLong()
    val graftFilterEmptyPathDeltaNodes = AtomicLong()
    val graftFilterAnyTailDeltaNodes = AtomicLong()
    val graftFilterTypedDeltaNodes = AtomicLong()

    fun recordGraftFilterShape(pathEmpty: Boolean, pathEndsAny: Boolean, deltaNodes: Long) {
        when {
            pathEmpty -> {
                graftFilterEmptyPath.incrementAndGet()
                graftFilterEmptyPathDeltaNodes.addAndGet(deltaNodes)
            }
            pathEndsAny -> {
                graftFilterAnyTail.incrementAndGet()
                graftFilterAnyTailDeltaNodes.addAndGet(deltaNodes)
            }
            else -> {
                graftFilterTyped.incrementAndGet()
                graftFilterTypedDeltaNodes.addAndGet(deltaNodes)
            }
        }
    }

    // ---- G: which LINE OF THE ANALYSED PROGRAM the graft ran for -------------------------------

    /**
     * The graft, billed to the call statement whose summary application ran it.
     *
     * Every counter above says WHAT the engine did. None of them says WHERE in the analysed program
     * it was doing it, and "which code pattern explodes" is a question about the analysed program,
     * not about the engine. A summary is applied at a call statement; [MethodAnalyzer] parks that
     * statement in [TifaDiagnostics.callSite] around the application, so the graft can read it back
     * and attribute the nodes it manufactured to a `<caller method>:<line>`.
     *
     * Keyed by the statement's IDENTITY. Instructions are per-method singletons, so the map stays
     * the size of the reached call graph, and no IR `equals` runs on a path taken millions of times.
     * Formatting happens once, at report time.
     */
    class SiteStats {
        @JvmField val calls = java.util.concurrent.atomic.LongAdder()
        @JvmField val receiverNodes = java.util.concurrent.atomic.LongAdder()
        @JvmField val resultNodes = java.util.concurrent.atomic.LongAdder()
        @JvmField val growth = java.util.concurrent.atomic.LongAdder()
        @JvmField val graftPoints = java.util.concurrent.atomic.LongAdder()
        @JvmField val anyDeltaCalls = java.util.concurrent.atomic.LongAdder()
        @JvmField val maxResult = AtomicLong()

        /** The biggest single graft seen here, verbatim -- what the ratio cannot show. */
        @Volatile
        @JvmField
        var sample: String? = null
    }

    private class IdKey(@JvmField val statement: Any) {
        override fun hashCode(): Int = System.identityHashCode(statement)
        override fun equals(other: Any?): Boolean = other is IdKey && other.statement === statement
    }

    private val perSite = java.util.concurrent.ConcurrentHashMap<IdKey, SiteStats>()

    /** Grafts that ran with nothing parked -- billed to nobody rather than to a guess. */
    val concatNoSite = AtomicLong()
    val concatNoSiteResultNodes = AtomicLong()

    fun recordConcatSite(
        receiver: Long,
        result: Long,
        graftPoints: Int,
        deltaCarriesAny: Boolean,
        render: () -> String,
    ) {
        val statement = TifaDiagnostics.callSite.get()
        if (statement == null) {
            concatNoSite.incrementAndGet()
            concatNoSiteResultNodes.addAndGet(result)
            return
        }

        val stats = perSite.computeIfAbsent(IdKey(statement)) { SiteStats() }
        stats.calls.increment()
        stats.receiverNodes.add(receiver)
        stats.resultNodes.add(result)
        stats.growth.add(maxOf(0L, result - receiver))
        stats.graftPoints.add(graftPoints.toLong())
        if (deltaCarriesAny) stats.anyDeltaCalls.increment()

        var seen = stats.maxResult.get()
        while (result > seen && !stats.maxResult.compareAndSet(seen, result)) seen = stats.maxResult.get()
        if (result > seen) stats.sample = render().take(600)
    }

    /**
     * The same graft, split by the ROOT the receiver fact hangs off.
     *
     * The site attribution says which call statement ran the graft; this says which family of facts
     * it ran on. `<static>` is one global base for every static of every class
     * (`AccessPathBase.ClassStatic` is a `data object`), so a single row here covers a tree that is
     * delivered to every method -- a distinction the site rows cannot draw.
     */
    class BaseStats {
        @JvmField val calls = java.util.concurrent.atomic.LongAdder()
        @JvmField val receiverNodes = java.util.concurrent.atomic.LongAdder()
        @JvmField val resultNodes = java.util.concurrent.atomic.LongAdder()
        @JvmField val receiverCarriesAny = java.util.concurrent.atomic.LongAdder()
        @JvmField val maxResult = AtomicLong()
    }

    private val perBaseKind = java.util.concurrent.ConcurrentHashMap<String, BaseStats>()

    fun recordConcatBase(baseKind: String, receiver: Long, result: Long, receiverCarriesAny: Boolean) {
        val stats = perBaseKind.computeIfAbsent(baseKind) { BaseStats() }
        stats.calls.increment()
        stats.receiverNodes.add(receiver)
        stats.resultNodes.add(result)
        if (receiverCarriesAny) stats.receiverCarriesAny.increment()
        var seen = stats.maxResult.get()
        while (result > seen && !stats.maxResult.compareAndSet(seen, result)) seen = stats.maxResult.get()
    }

    private fun baseReport(): String = buildString {
        val all = perBaseKind.entries.sortedByDescending { it.value.resultNodes.sum() }
        val total = all.sumOf { it.value.resultNodes.sum() }
        appendLine("apop H-base total=$total")
        all.forEach { (kind, v) ->
            val calls = v.calls.sum()
            appendLine(
                "apop H-base $kind resultNodes=${v.resultNodes.sum()}" +
                    " (${if (total == 0L) "-" else String.format("%.1f%%", 100.0 * v.resultNodes.sum() / total)})" +
                    " calls=$calls nodesPerCall=${ratio(v.resultNodes.sum(), calls)}" +
                    " receiverNodes=${v.receiverNodes.sum()}" +
                    " receiverCarriesAny=${v.receiverCarriesAny.sum()} maxResult=${v.maxResult.get()}"
            )
        }
    }

    private const val SITE_TOP_N = 30

    private fun siteReport(): String = buildString {
        val all = perSite.entries.sortedByDescending { it.value.resultNodes.sum() }
        val total = all.sumOf { it.value.resultNodes.sum() }
        appendLine(
            "apop G-site sites=${all.size} attributedResultNodes=$total" +
                " noSite=${concatNoSite.get()} noSiteResultNodes=${concatNoSiteResultNodes.get()}"
        )

        // The per-line rows below are the top [SITE_TOP_N] only; this rollup is over ALL of them, so
        // "how much of the node mass is made inside one METHOD" is a total rather than a lower bound.
        val byMethod = HashMap<String, LongArray>()
        for ((key, v) in perSite.entries) {
            val method = TifaDiagnostics.siteOf(key.statement).substringBeforeLast(':')
            val row = byMethod.getOrPut(method) { LongArray(3) }
            row[0] += v.resultNodes.sum()
            row[1] += v.calls.sum()
            row[2] += 1
        }
        byMethod.entries.sortedByDescending { it.value[0] }.take(SITE_TOP_N).forEachIndexed { i, (m, r) ->
            appendLine(
                "apop G-method #$i resultNodes=${r[0]}" +
                    " (${if (total == 0L) "-" else String.format("%.1f%%", 100.0 * r[0] / total)})" +
                    " calls=${r[1]} sites=${r[2]} nodesPerCall=${ratio(r[0], r[1])} | $m"
            )
        }
        all.take(SITE_TOP_N).forEachIndexed { i, (key, v) ->
            val calls = v.calls.sum()
            appendLine(
                "apop G-site #$i resultNodes=${v.resultNodes.sum()}" +
                    " (${if (total == 0L) "-" else String.format("%.1f%%", 100.0 * v.resultNodes.sum() / total)})" +
                    " calls=$calls nodesPerCall=${ratio(v.resultNodes.sum(), calls)}" +
                    " growth=${v.growth.sum()} pointsPerCall=${ratio(v.graftPoints.sum(), calls)}" +
                    " anyDelta=${v.anyDeltaCalls.sum()} maxResult=${v.maxResult.get()}" +
                    " | ${TifaDiagnostics.siteOf(key.statement)}" +
                    " | ${key.statement.toString().replace('\n', ' ').take(200)}"
            )
            v.sample?.let { appendLine("apop G-site #$i biggest: ${it.replace('\n', ' ')}") }
        }
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
            "apop C-graft points=${concatGraftPoints.get()} max=${concatGraftPointsMax.get()}" +
                " pointsPerCall=${ratio(concatGraftPoints.get(), concatCalls.get())}" +
                " actualGrowth=${concatGrowth.get()}" +
                " deltaNodes=${concatDeltaNodes.get()}"
        )
        appendLine("apop C-graft pointsByCount=[${concatGraftPointBuckets.render()}]")
        appendLine("apop C-graft growthByLog2=[${concatGrowthBuckets.render()}]")
        appendLine(
            "apop C-sample n=${concatSamples.get()}" +
                " recv size/distinct/abstract=${concatSampleRecvSize.get()}/${concatSampleRecvDistinct.get()}/${concatSampleRecvAbstract.get()}" +
                " delta size/distinct=${concatSampleDeltaSize.get()}/${concatSampleDeltaDistinct.get()}" +
                " result size/distinct=${concatSampleResultSize.get()}/${concatSampleResultDistinct.get()}" +
                " distinctGrowthPerSample=${ratio(concatSampleResultDistinct.get() - concatSampleRecvDistinct.get(), concatSamples.get())}" +
                " sizeGrowthPerSample=${ratio(concatSampleResultSize.get() - concatSampleRecvSize.get(), concatSamples.get())}"
        )
        appendLine(
            "apop E-delta concretePremise calls=${deltaCalls.get()} factNodes=${deltaFactNodes.get()}" +
                " remainderNodes=${deltaResultNodes.get()} premiseLinks=${deltaPremiseLinks.get()}" +
                " remainderPerFact=${ratio(deltaResultNodes.get(), deltaFactNodes.get())}" +
                " notSmaller=${deltaNotSmaller.get()}"
        )
        appendLine(
            "apop E-delta anyPremise      calls=${deltaAnyCalls.get()} factNodes=${deltaAnyFactNodes.get()}" +
                " remainderNodes=${deltaAnyResultNodes.get()} premiseLinks=${deltaAnyPremiseLinks.get()}" +
                " remainderPerFact=${ratio(deltaAnyResultNodes.get(), deltaAnyFactNodes.get())}" +
                " notSmaller=${deltaAnyNotSmaller.get()}"
        )
        appendLine(
            "apop F-roundtrip deltaThroughAny=${deltaThroughAny.get()}" +
                " remainderKeepsAny=${deltaThroughAnyKept.get()}" +
                " remainderNotSmaller=${deltaThroughAnyNotSmaller.get()}" +
                " factNodes=${deltaThroughAnyFactNodes.get()}" +
                " remainderNodes=${deltaThroughAnyRemainderNodes.get()}" +
                " remainderPerFact=${ratio(deltaThroughAnyRemainderNodes.get(), deltaThroughAnyFactNodes.get())}"
        )
        appendLine(
            "apop F-roundtrip concatAnyDelta=${concatAnyDeltaCalls.get()}" +
                " resultKeepsAny=${concatAnyDeltaResultKeepsAny.get()}" +
                " depthGain=${concatAnyDeltaDepthGain.get()}" +
                " depthGainPerCall=${ratio(concatAnyDeltaDepthGain.get(), concatAnyDeltaCalls.get())}"
        )
        appendLine("apop F-roundtrip --- verbatim round trips ---")
        roundTrips.forEach { appendLine("apop   $it") }
        appendLine(
            "apop D-filterStartsWith calls=${fswCalls.get()} inNodes=${fswInNodes.get()}" +
                " outNodes=${fswOutNodes.get()} grew=${fswGrew.get()} growth=${fswGrowth.get()}"
        )
        appendLine("apop --- biggest single event of each kind ---")
        biggest.forEach { (kind, e) -> appendLine("apop   [$kind +${e.first}] ${e.second}") }
        appendLine(
            "apop I-filter emptyPath=${graftFilterEmptyPath.get()} anyTail=${graftFilterAnyTail.get()}" +
                " typed=${graftFilterTyped.get()}" +
                " deltaNodes empty/anyTail/typed=${graftFilterEmptyPathDeltaNodes.get()}" +
                "/${graftFilterAnyTailDeltaNodes.get()}/${graftFilterTypedDeltaNodes.get()}"
        )
        append(baseReport())
        append(siteReport())
        appendLine("apop --- unroll prefixes at depth >= $PREFIX_SAMPLE_MIN_DEPTH ---")
        prefixSamples.forEach { appendLine("apop   $it") }
    }
}

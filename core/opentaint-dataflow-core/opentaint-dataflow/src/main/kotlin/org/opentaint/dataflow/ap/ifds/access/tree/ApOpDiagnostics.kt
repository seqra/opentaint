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

    // ---- A: the TIFA [any] unroll -- REMOVED ---------------------------------------------------
    //
    // There is no unroll any more. `TreeInitialFactAbstraction` never materialises an accessor out
    // of an `[any]`, so `unrollCalls`, `unrollCarrierNodes`, `unrollCopyCarriesAny` and the two
    // by-prefix-depth histograms have no producer. They are deleted rather than left reading zero:
    // a counter that is zero by construction says nothing, and this file already carries the
    // measurements they were taken for (`carrierPerRequest = 10.72`, `copyCarriesAny` 99.4%).
    // The equivalent question is now `TIFA R3c` versus `R4` -- premises handed out versus walk
    // states entered by reading -- and both live in `TifaDiagnostics`.

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

    /**
     * The whole cost of the literal matching rule, counted at the exact point it is paid.
     *
     * Incremented by `AccessTree.AccessNode.getChildMatching` when a MATCHING read found neither a
     * literal child nor a zero-step child for an accessor the `[any]` covers -- precisely the
     * population the synthesising reader used to answer, and therefore precisely the set of premise
     * matches the rule gives up. Against [anyReadCalls] (the same synthesis on the DENOTATION
     * channels, which keep it) this says how much of the old traffic was matching and how much was
     * denotation.
     *
     * Design: `docs/superpowers/specs/2026-08-27-literal-any-matching-design.md`.
     */
    val matchRefusedAnySynthesis = AtomicLong()

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

    /**
     * Why `pointsPerCall` is large, split into the two mechanisms that produce it -- because they
     * have different fixes and only one of them has ever been measured.
     *
     * The receiver is a DAG, not a tree. `size` counts nodes WITH path multiplicity while
     * `countNodes()` counts distinct ones, and the sampled receiver holds 8.0 distinct nodes of
     * which 2.1 are abstract, against 15.7 graft points per call. So a graft point is mostly a
     * RE-VISIT of a node already grafted in this same call -- `manager.abstractNode` is a
     * process-wide singleton, so every `*` leaf of a receiver is literally the same object -- and
     * `concatToLeafAbstractNodes` memoises only the DELTA side, never its own result.
     *
     * - [graftPointsRevisited] counts points whose receiver node was already grafted in this call.
     *   It is the ceiling on a receiver-side memo.
     * - [graftPointsNested] counts points that sit strictly BELOW another graft point. It is the
     *   population a subsumption rule ("the deep graft is covered by the shallow one") could skip.
     *
     * They overlap, and separating them is the point: a re-visit is answered by remembering, a
     * nested point by not asking.
     */
    val graftPointsRevisited = AtomicLong()
    val graftPointsNested = AtomicLong()

    /**
     * Deltas whose ROOT owns an `[any]` edge, as opposed to merely containing one somewhere.
     *
     * [concatAnyDeltaCalls] tests `containsAnyInThisOrDeepNodes`, which is strictly weaker, and every
     * rule that wants to fold the receiver's spine into the delta's `[any]` -- the absorbing prepend
     * at the graft, and any deep-graft subsumption -- needs the ROOT predicate. Rendered deltas on
     * conductor show the common big shape carrying its `[any]` at depth 6-8 behind a concrete spine,
     * so the two predicates are expected to disagree by a lot. Nothing measured which.
     */
    val concatDeltaRootCarriesAny = AtomicLong()

    /** Per-thread identity set of receiver nodes already grafted in the current concat call. */
    val graftSeen: ThreadLocal<java.util.IdentityHashMap<Any, Any>> =
        ThreadLocal.withInitial { java.util.IdentityHashMap<Any, Any>() }

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

    // ---- J: the subsumption counterfactual -----------------------------------------------------

    /**
     * What the `[any]` subsumption trim WOULD remove from the initial-fact accumulator, which is the
     * one storage in the module that switches it off.
     *
     * `mergeAdd`'s `foldToAny` arm runs `AccessTreeAnySuffixMatcher` over each side's `[any]` subtree
     * and deletes from the other side every branch that suffix language already denotes -- a real
     * `⊑` test, wired into the merge, on every path-edge, summary and subscription channel.
     * `TreeInitialFactAbstraction` passes `foldToAny = false` at its two call sites, the only two in
     * the module, and its `added` tree is exactly where an `[any]` and the concrete enumerations it
     * denotes sit side by side.
     *
     * `keptFraction` is the reading. Near 1 means the accumulator's `[any]` does not cover what
     * arrives and the growth is genuinely new structure; well under 1 means it is storing an
     * enumeration of what it already says. **A root-level probe, so a LOWER BOUND** -- the real merge
     * trims recursively at every pair.
     */
    val tifaTrimCalls = AtomicLong()
    val tifaTrimNoAny = AtomicLong()
    val tifaTrimInNodes = AtomicLong()
    val tifaTrimKeptNodes = AtomicLong()
    val tifaTrimWouldDropAll = AtomicLong()

    /**
     * Branches the trim kept ONLY because the node was abstract -- the hole in the `⊑` test.
     *
     * `AccessTreeAnySuffixMatcher` cancels `isFinal` (`thisFinal = node.isFinal && !trie.isFinal`)
     * and has no mirror for `isAbstract`, so `[any].*` does not subsume a sibling `f.*` whose node is
     * abstract even though it denotes a superset. Abstract nodes are the graft points, and graft
     * points per concat call is the quantity that runs away.
     */
    val trimKeptForAbstract = AtomicLong()
    val trimKeptForAbstractNodes = AtomicLong()

    /**
     * The `(trie, node)` memo inside one `[any]`-trim walk. The hit rate is how much of the walk was
     * re-deriving a shared subtree it had already answered for -- a fact is a DAG, and the walk had
     * no memo until 2026-08-26.
     */
    val trimMemoHits = AtomicLong()
    val trimMemoMisses = AtomicLong()

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

    // ---- I: can the type filter at a graft point reject anything at all? -----------------------

    /**
     * The graft's type filter, counted where it actually costs.
     *
     * `filterTypes` memoises per (delta node, filter), and the filter's identity is the TYPE at the
     * graft position -- not the path -- so two positions of the same type share an entry. A HIT is
     * free. A MISS walks the whole delta subtree and calls `FactApFilter.check` once per accessor
     * edge, which is what the engine-wide `access R/T` counter sees. [filterTypesInNodes] is the
     * node mass those misses walked, and it is the number to compare against `concat resultNodes`:
     * if it is the larger of the two, the graft spends more time deciding what to graft than
     * grafting.
     */
    val filterTypesCalls = AtomicLong()
    val filterTypesHits = AtomicLong()
    val filterTypesRejectedHits = AtomicLong()
    val filterTypesMisses = AtomicLong()
    val filterTypesRejectedMisses = AtomicLong()
    val filterTypesInNodes = AtomicLong()
    val filterTypesOutNodes = AtomicLong()

    fun recordFilterTypes(hit: Boolean, rejected: Boolean, inNodes: Long, outNodes: Long) {
        filterTypesCalls.incrementAndGet()
        if (hit) {
            filterTypesHits.incrementAndGet()
            if (rejected) filterTypesRejectedHits.incrementAndGet()
            return
        }
        filterTypesMisses.incrementAndGet()
        filterTypesInNodes.addAndGet(inNodes)
        if (rejected) filterTypesRejectedMisses.incrementAndGet() else filterTypesOutNodes.addAndGet(outNodes)
    }

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
            "apop B-getChildAny calls=${anyReadCalls.get()} literalNodes=${anyReadLiteralNodes.get()}" +
                " resultNodes=${anyReadResultNodes.get()} grew=${anyReadGrew.get()}" +
                " growth=${anyReadGrowth.get()} fromNothing=${anyReadFromNothing.get()}" +
                " growthPerCall=${ratio(anyReadGrowth.get(), anyReadCalls.get())}" +
                " matchRefused=${matchRefusedAnySynthesis.get()}"
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
        appendLine(
            "apop C-graft revisited=${graftPointsRevisited.get()} nested=${graftPointsNested.get()}" +
                " revisitedShare=${ratio(graftPointsRevisited.get() * 100, concatGraftPoints.get())}%" +
                " nestedShare=${ratio(graftPointsNested.get() * 100, concatGraftPoints.get())}%" +
                " deltaRootCarriesAny=${concatDeltaRootCarriesAny.get()}"
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
            "apop J-trimCF tifaCalls=${tifaTrimCalls.get()} noAny=${tifaTrimNoAny.get()}" +
                " inNodes=${tifaTrimInNodes.get()} keptNodes=${tifaTrimKeptNodes.get()}" +
                " wouldDropAll=${tifaTrimWouldDropAll.get()}" +
                " keptFraction=${ratio(tifaTrimKeptNodes.get(), tifaTrimInNodes.get())}"
        )
        appendLine(
            "apop J-abstractHole keptForAbstract=${trimKeptForAbstract.get()}" +
                " nodesKept=${trimKeptForAbstractNodes.get()}"
        )
        appendLine(
            "apop J-trimMemo hits=${trimMemoHits.get()} misses=${trimMemoMisses.get()}" +
                " hitRate=${ratio(trimMemoHits.get() * 100, trimMemoHits.get() + trimMemoMisses.get())}%"
        )
        appendLine(
            "apop I-filterTypes calls=${filterTypesCalls.get()} hits=${filterTypesHits.get()}" +
                " hitRate=${ratio(filterTypesHits.get() * 100, filterTypesCalls.get())}%" +
                " misses=${filterTypesMisses.get()}" +
                " rejectedHits=${filterTypesRejectedHits.get()}" +
                " rejectedMisses=${filterTypesRejectedMisses.get()}" +
                " inNodes=${filterTypesInNodes.get()} outNodes=${filterTypesOutNodes.get()}" +
                " nodesPerMiss=${ratio(filterTypesInNodes.get(), filterTypesMisses.get())}"
        )
        appendLine(
            "apop I-filter emptyPath=${graftFilterEmptyPath.get()} anyTail=${graftFilterAnyTail.get()}" +
                " typed=${graftFilterTyped.get()}" +
                " deltaNodes empty/anyTail/typed=${graftFilterEmptyPathDeltaNodes.get()}" +
                "/${graftFilterAnyTailDeltaNodes.get()}/${graftFilterTypedDeltaNodes.get()}"
        )
        append(baseReport())
        append(siteReport())
    }
}

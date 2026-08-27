package org.opentaint.dataflow.ap.ifds

import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTreeAnySuffixMatcher
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.ANY_ACCESSOR_IDX
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.atomic.AtomicLong
import java.util.concurrent.atomic.AtomicLongArray

/**
 * Where stored facts come from, and what re-storing one costs.
 *
 * The per-statement fact store is not a SET of facts. `MethodEdgesFinalTreeApSet` and
 * `MethodEdgesInitialToFinalTreeApSet` hold ONE MERGED TREE per slot, and `add` hands back that
 * whole merged tree whenever the merge changed it. The returned edge -- not the edge that was
 * offered -- is what gets enqueued, propagated to every CFG successor and grafted through `concat`.
 * A slot that reaches S nodes over k growths therefore does not cost S; it costs the sum of its
 * intermediate sizes, and that sum is the quantity nothing in the engine reports.
 *
 * Three masses separate the question:
 *
 *  * [storeMass] -- what is HELD. Incremented by the growth of each merge, so it ends as the exact
 *    node total across every live slot.
 *  * [propagatedMass] -- what is HANDED BACK. The whole merged tree at every growth.
 *    `propagatedMass / storeMass` is the re-propagation factor, and it is the number this object
 *    exists to produce.
 *  * [offeredMass] -- what the producer BROUGHT. `storeMass / offeredMass` is how much of the
 *    incoming work was new.
 *
 * Node mass is [AccessTree.AccessNode.size] -- the precomputed subtree size, with path
 * multiplicity, an O(1) field read. `FinalFactAp.size` is `countNodes()` and walks the tree, so it
 * is never called here.
 *
 * `-Dopentaint.edgeCensus=true`; rows `-Dopentaint.edgeCensusTop=N`.
 */
object EdgeStoreDiagnostics {
    val enabled: Boolean = System.getProperty("opentaint.edgeCensus")?.trim().toBoolean()

    val reportTopN: Int = System.getProperty("opentaint.edgeCensusTop")?.trim()?.toIntOrNull() ?: 25

    /**
     * The producer that is currently running, parked per thread.
     *
     * `Edge` carries no provenance and the storage cannot see the frame that reached it, so the
     * producer travels the same way the call site does for [org.opentaint.dataflow.ap.ifds.access.tree.TifaDiagnostics].
     * Nesting is real and intended: a call step that seeds a callee re-tags for the duration of the
     * seed, so the callee's arrivals are billed to the seed and the caller's remaining adds are
     * still billed to the call.
     */
    enum class Producer {
        /** Method entry, zero fact. */
        START,

        /** A caller subscribed at a call site and the callee is seeded through the abstraction. */
        TIFA_SEED,

        /** An edge's initial fact was refined in place, so the abstraction re-registers it. */
        INPUT_REFINE,

        /** The fact-depth gate rose and delayed edges are replayed. */
        DELAY_REPLAY,

        /** Ordinary intra-procedural flow. */
        SEQUENT,

        /** Call-to-return, including the unresolved-call fallback. */
        CALL,

        /** A callee summary grafted onto a caller fact. */
        SUMMARY,

        /** A callee side-effect summary applied. */
        SIDE_EFFECT,

        /** A callee side-effect requirement propagated back. */
        SIDE_EFFECT_REQ,

        /** Anything that reached the store outside a tagged frame. */
        OTHER,
    }

    private val producers = Producer.values()

    private val producer: ThreadLocal<Producer> = ThreadLocal.withInitial { Producer.OTHER }

    inline fun <T> withProducer(kind: Producer, body: () -> T): T {
        if (!enabled) return body()
        val previous = currentProducer()
        setProducer(kind)
        try {
            return body()
        } finally {
            setProducer(previous)
        }
    }

    @PublishedApi
    internal fun currentProducer(): Producer = producer.get()

    @PublishedApi
    internal fun setProducer(kind: Producer) = producer.set(kind)

    /** Edge kinds, in the order [MethodAnalyzerEdges.addEdge] dispatches them. */
    enum class Kind { ZERO_TO_ZERO, ZERO_TO_FACT, FACT_TO_FACT, ND_FACT_TO_FACT }

    private val kinds = Kind.values()

    private val nKinds = kinds.size
    private val nProducers = producers.size

    /** `add` calls, and how each ended. Indexed `[producer * nKinds + kind]`. */
    private val calls = AtomicLongArray(nProducers * nKinds)
    private val firstInserts = AtomicLongArray(nProducers * nKinds)
    private val growths = AtomicLongArray(nProducers * nKinds)
    private val noops = AtomicLongArray(nProducers * nKinds)

    private val offeredMassBy = AtomicLongArray(nProducers * nKinds)
    private val storeMassBy = AtomicLongArray(nProducers * nKinds)
    private val propagatedMassBy = AtomicLongArray(nProducers * nKinds)

    val offeredMass = AtomicLong()
    val storeMass = AtomicLong()
    val propagatedMass = AtomicLong()

    /** Merged-tree size at a growth, bucketed by `log2`. The tail is what re-propagation costs. */
    private val growthSizeBuckets = AtomicLongArray(32)

    /** The largest single tree ever handed back, and where. */
    private val maxPropagated = AtomicLong()

    @Volatile
    private var maxPropagatedWhere: String? = null

    private val perMethod = ConcurrentHashMap<String, MethodEdgeStats>()

    private fun massOf(fact: FinalFactAp?): Long = when (fact) {
        null -> 0L
        is AccessTree -> fact.access.size
        else -> 0L
    }

    private fun kindOf(edge: Edge): Kind = when (edge) {
        is Edge.ZeroToZero -> Kind.ZERO_TO_ZERO
        is Edge.ZeroToFact -> Kind.ZERO_TO_FACT
        is Edge.FactToFact -> Kind.FACT_TO_FACT
        is Edge.NDFactToFact -> Kind.ND_FACT_TO_FACT
    }

    private fun factOf(edge: Edge): FinalFactAp? = when (edge) {
        is Edge.ZeroToZero -> null
        is Edge.ZeroToFact -> edge.factAp
        is Edge.FactToFact -> edge.factAp
        is Edge.NDFactToFact -> edge.factAp
    }

    /**
     * One `MethodAnalyzerEdges.add`.
     *
     * [produced] is what the storage handed back: empty means the merge changed nothing, a single
     * element identical to [offered] means the slot was empty and the fact went in as-is, and
     * anything else is a GROWTH whose element is the whole merged tree.
     */
    fun recordAdd(methodEntryPoint: MethodEntryPoint, offered: Edge, produced: List<Edge>) {
        val kind = kindOf(offered)
        val slot = currentProducer().ordinal * nKinds + kind.ordinal
        calls.incrementAndGet(slot)

        val offeredNodes = massOf(factOf(offered))
        offeredMassBy.addAndGet(slot, offeredNodes)
        offeredMass.addAndGet(offeredNodes)

        val stats = perMethod.computeIfAbsent(methodEntryPoint.method.toString()) { MethodEdgeStats(it) }
        stats.entryPoints.add(methodEntryPoint)
        stats.calls.incrementAndGet()
        stats.offeredMass.addAndGet(offeredNodes)

        val result = produced.firstOrNull()
        if (result == null) {
            noops.incrementAndGet(slot)
            stats.noops.incrementAndGet()
            return
        }

        if (result === offered) {
            firstInserts.incrementAndGet(slot)
            storeMassBy.addAndGet(slot, offeredNodes)
            propagatedMassBy.addAndGet(slot, offeredNodes)
            propagatedMass.addAndGet(offeredNodes)
            stats.firstInserts.incrementAndGet()
            stats.storeMass.addAndGet(offeredNodes)
            stats.propagatedMass.addAndGet(offeredNodes)
            recordGrowthSize(offeredNodes)
            return
        }

        val mergedNodes = massOf(factOf(result))
        // What the slot actually GAINED is not visible here -- the storage returns the merged tree,
        // not the tree it replaced -- so [recordMerge] supplies it from inside the merge. This site
        // owns the propagation cost, which is the whole merged tree every time.
        growths.incrementAndGet(slot)
        propagatedMassBy.addAndGet(slot, mergedNodes)
        propagatedMass.addAndGet(mergedNodes)
        stats.growths.incrementAndGet()
        stats.propagatedMass.addAndGet(mergedNodes)
        recordGrowthSize(mergedNodes)

        if (mergedNodes > stats.maxSlotMass.get()) stats.maxSlotMass.set(mergedNodes)

        var currentMax = maxPropagated.get()
        while (mergedNodes > currentMax) {
            if (maxPropagated.compareAndSet(currentMax, mergedNodes)) {
                maxPropagatedWhere = "${kind.name} in ${methodEntryPoint.method}"
                break
            }
            currentMax = maxPropagated.get()
        }
    }

    /**
     * The one number the [recordAdd] site cannot see: how much the slot GAINED.
     *
     * Called from inside the merge, where the tree that is being replaced is still in hand. Summed
     * over every merge it is the exact node total held across all slots, which is the denominator
     * of the re-propagation factor.
     */
    fun recordMerge(previousNodes: Long, mergedNodes: Long) {
        storeMass.addAndGet(mergedNodes - previousNodes)
        slotMerges.incrementAndGet()
        var currentMax = maxSlot.get()
        while (mergedNodes > currentMax) {
            if (maxSlot.compareAndSet(currentMax, mergedNodes)) break
            currentMax = maxSlot.get()
        }
    }

    /** New slots opened, i.e. distinct (base, premise, statement) keys the store ever held. */
    /**
     * Children-per-node at the ROOT of a stored fact, bucketed, plus the maximum.
     *
     * Breadth is the one dimension with NO bound anywhere in the tree backend -- depth has
     * `factDepthLimit`, the element cap and the field-repeat rule; width has nothing, and
     * `accessorCount()` is not compared against a threshold anywhere. The ROOT is the right place to
     * watch it because `limitFieldAccess` HOISTS every repeated field to the root, so the root is
     * where width actually accumulates. O(1) per call -- `accessors` is a sorted array.
     */
    private val rootBreadthBuckets = AtomicLongArray(64)
    val maxRootBreadth = AtomicLong()
    val rootBreadthTotal = AtomicLong()
    val rootBreadthSamples = AtomicLong()

    // ---- self-subsumption census ------------------------------------------------------------
    //
    // "Do we hold facts with a sibling branch the fact's OWN `[any]` already denotes?" -- e.g.
    // `a.b.c` beside `a.[any].c`.
    //
    // This is worth counting because the engine cannot answer it. `trimAnyCoveredAndPushChildren`
    // is a CROSS-trim between two merge OPERANDS: it matches one operand's `[any]` against the
    // other operand's branches. Nothing ever trims a node's own sibling against its own `[any]`, so
    // such a pair persists until some later merge partner happens to carry an `[any]` at exactly
    // that position. The census walks STORED facts and measures the residue directly.
    //
    // The matcher is built with `forceCancelAbstract = true` so the number is the FULL subsumption
    // residue -- what a complete self-normalisation could remove -- while the engine keeps running
    // its shipped, non-cancelling semantics. A fresh local matcher per point, never the cached
    // `anySuffixMatcher`: that one carries unsynchronised IdentityHashMap memos shared across
    // threads, and `manager.abstractNode` is a process-wide singleton, so reusing it would amplify
    // an existing race.
    private const val CENSUS_RATE = 512L
    private const val CENSUS_MIN_SIZE = 50L
    private const val CENSUS_VISIT_BUDGET = 20_000

    private val censusCounter = AtomicLong()
    val censusFacts = AtomicLong()
    val censusTruncated = AtomicLong()
    val censusNodesWithAny = AtomicLong()
    val censusSiblings = AtomicLong()
    /** Sibling branches the fact's own `[any]` fully denotes, and their node mass. */
    val censusFullySubsumed = AtomicLong()
    val censusFullySubsumedMass = AtomicLong()
    /** ... of which hold a mark/static/`[value]`/type-info, i.e. folding costs R3b a name. */
    val censusSubsumedNameCritical = AtomicLong()
    val censusSubsumedNameCriticalMass = AtomicLong()
    /** Partially subsumed: some paths denoted, some not. */
    val censusPartial = AtomicLong()
    val censusPartialDroppedMass = AtomicLong()
    val censusNotSubsumed = AtomicLong()
    val censusTotalSiblingMass = AtomicLong()

    /** Covered sibling branches folded into a node's own `[any]`, and the node mass folded. */
    val siblingsAbsorbed = AtomicLong()
    val siblingAbsorbedMass = AtomicLong()

    fun recordSiblingAbsorbed(mass: Long) {
        siblingsAbsorbed.incrementAndGet()
        siblingAbsorbedMass.addAndGet(mass)
    }

    /* ---------- why the fold does or does not fire, on the population it actually walks ---------- */

    /**
     * The fold's own census, counted at its decision point rather than by a sampler.
     *
     * `folded = 19` on one arm and `528,602` on another is not by itself a mechanism: it is
     * consistent with "no `[any]` ever reaches the store", with "`[any]` arrives but never beside a
     * covered edge", and with "the pass never walks those nodes". These five counters separate all
     * three, and they are counted where the decision is made, so they describe exactly the node
     * population the fold sees.
     */
    val foldCalls = AtomicLong()

    /** Of [foldCalls], how many were handed a fact carrying an `[any]` ANYWHERE in it. */
    val foldCallsWithAny = AtomicLong()

    val foldVisits = AtomicLong()

    /** Node visits where the node itself owns an `[any]` edge. Splits into the three below. */
    val foldNodesWithAny = AtomicLong()

    /** ... and holds at least one COVERED sibling: the shape the fold rewrites. */
    val foldAnyWithCovered = AtomicLong()

    /** ... and holds siblings, but every one of them is UNCOVERED (mark, static, type-info). */
    val foldAnyUncoveredOnly = AtomicLong()

    /** ... and the `[any]` is its only edge, so there is nothing beside it to absorb. */
    val foldAnyAlone = AtomicLong()

    fun recordFoldCall(containsAny: Boolean) {
        foldCalls.incrementAndGet()
        if (containsAny) foldCallsWithAny.incrementAndGet()
    }

    fun recordFoldVisit(hasAny: Boolean, hasCovered: Boolean, siblings: Int) {
        foldVisits.incrementAndGet()
        if (!hasAny) return
        foldNodesWithAny.incrementAndGet()
        when {
            hasCovered -> foldAnyWithCovered.incrementAndGet()
            siblings == 0 -> foldAnyAlone.incrementAndGet()
            else -> foldAnyUncoveredOnly.incrementAndGet()
        }
    }

    fun censusShouldSample(): Boolean =
        enabled && censusCounter.incrementAndGet() % CENSUS_RATE == 0L

    fun runSelfSubsumptionCensus(fact: FinalFactAp?) {
        val tree = fact as? AccessTree ?: return
        val root = tree.access
        if (root.size < CENSUS_MIN_SIZE) return
        censusFacts.incrementAndGet()

        val seen = java.util.IdentityHashMap<AccessTree.AccessNode, Unit>()
        val stack = ArrayDeque<AccessTree.AccessNode>()
        stack.addLast(root)
        var visits = 0

        while (stack.isNotEmpty()) {
            if (visits++ > CENSUS_VISIT_BUDGET) { censusTruncated.incrementAndGet(); return }
            val node = stack.removeLast()
            if (seen.put(node, Unit) != null) continue
            node.forEachAccessor { _, child -> stack.addLast(child) }
            if (!node.containsAnyAccessor()) continue

            var anyNode: AccessTree.AccessNode? = null
            node.forEachAccessor { a, c -> if (a == ANY_ACCESSOR_IDX) anyNode = c }
            val any = anyNode ?: continue
            val siblings = node.clearChild(ANY_ACCESSOR_IDX)
            if (siblings.isEmpty || siblings.accessors == null) continue

            censusNodesWithAny.incrementAndGet()
            val kept = AccessTreeAnySuffixMatcher(any, forceCancelAbstract = true)
                .getNonMatchingNode(siblings)

            val keptChildren = Int2ObjectOpenHashMap<AccessTree.AccessNode>()
            if (!kept.isEmpty) kept.forEachAccessor { a, c -> keptChildren.put(a, c) }

            siblings.forEachAccessor { accessor, child ->
                censusSiblings.incrementAndGet()
                censusTotalSiblingMass.addAndGet(child.size)
                val kc = keptChildren.get(accessor)
                when {
                    kc == null -> {
                        censusFullySubsumed.incrementAndGet()
                        censusFullySubsumedMass.addAndGet(child.size)
                        if (child.containsNameCriticalInThisOrDeepNodes) {
                            censusSubsumedNameCritical.incrementAndGet()
                            censusSubsumedNameCriticalMass.addAndGet(child.size)
                        }
                    }
                    kc === child -> censusNotSubsumed.incrementAndGet()
                    else -> {
                        censusPartial.incrementAndGet()
                        censusPartialDroppedMass.addAndGet(child.size - kc.size)
                    }
                }
            }
        }
    }

    fun recordRootBreadth(width: Int) {
        rootBreadthBuckets.incrementAndGet(width.coerceIn(0, 63))
        rootBreadthTotal.addAndGet(width.toLong())
        rootBreadthSamples.incrementAndGet()
        while (true) {
            val cur = maxRootBreadth.get()
            if (width <= cur || maxRootBreadth.compareAndSet(cur, width.toLong())) break
        }
    }

    /* ---------- what the store actually holds: premise trie nodes, and the biggest facts ---------- */

    /**
     * Nodes created in the PREMISE trie, i.e. how many distinct access paths the store keys on.
     *
     * The question this exists for is "is the explosion in the number of premises or in the size of
     * the facts hanging off them", which no existing counter answers: [slotsOpened] counts
     * (premise, statement) SLOTS and [storeMass] their fact mass, so both move when either half
     * grows.
     */
    val premiseTrieNodes = AtomicLong()

    private const val BIG_FACT_SLOTS = 6
    private const val BIG_FACT_MIN_PATHS = 512L

    private val bigFactLock = Any()
    private val bigFactPaths = LongArray(BIG_FACT_SLOTS)
    private val bigFactText = arrayOfNulls<String>(BIG_FACT_SLOTS)

    /**
     * A hall of fame of the largest stored facts, summarised STRUCTURALLY rather than printed.
     *
     * `AccessNode.print` emits one line per root-to-leaf PATH, so rendering a fact whose `size` is
     * seven figures would emit seven figures of lines. [summariseFact] instead reports the shape:
     * the per-level node and `[any]` census, the branching, and a bounded BFS sample of actual
     * paths -- which is what a reader needs to answer "what do these facts look like, and where is
     * the `[any]`".
     *
     * Summarising happens only when a fact displaces the smallest entry, so the cost is paid a few
     * dozen times per run rather than per merge.
     */
    fun recordBigFact(node: AccessTree.AccessNode) {
        val paths = node.size
        if (paths < BIG_FACT_MIN_PATHS) return
        synchronized(bigFactLock) {
            var victim = 0
            for (i in 0 until BIG_FACT_SLOTS) {
                if (bigFactText[i] == null) { victim = i; break }
                if (bigFactPaths[i] < bigFactPaths[victim]) victim = i
            }
            if (bigFactText[victim] != null && bigFactPaths[victim] >= paths) return
            bigFactPaths[victim] = paths
            bigFactText[victim] = summariseFact(node)
        }
    }

    private const val SUMMARY_MAX_LEVELS = 12
    private const val SUMMARY_MAX_VISITS = 200_000
    private const val SUMMARY_SAMPLE_PATHS = 10

    private fun summariseFact(root: AccessTree.AccessNode): String {
        val manager = root.manager
        val levelNodes = IntArray(SUMMARY_MAX_LEVELS)
        val levelWithAny = IntArray(SUMMARY_MAX_LEVELS)
        val levelAnyEdges = IntArray(SUMMARY_MAX_LEVELS)
        val levelCoveredEdges = IntArray(SUMMARY_MAX_LEVELS)
        val levelMarkEdges = IntArray(SUMMARY_MAX_LEVELS)
        val samples = ArrayList<String>()
        var visits = 0
        var truncated = false
        var deepest = ""
        var deepestLen = -1

        // BFS over DISTINCT nodes: the structure is a DAG and a path walk would re-enumerate the
        // shared subtrees that are the whole reason `size` and `countNodes` diverge.
        val seen = java.util.IdentityHashMap<AccessTree.AccessNode, Unit>()
        var frontier = ArrayList<Pair<AccessTree.AccessNode, String>>()
        frontier.add(root to "")
        var level = 0
        while (frontier.isNotEmpty() && level < SUMMARY_MAX_LEVELS) {
            val next = ArrayList<Pair<AccessTree.AccessNode, String>>()
            for ((node, path) in frontier) {
                if (visits++ > SUMMARY_MAX_VISITS) { truncated = true; break }
                if (seen.put(node, Unit) != null) continue
                levelNodes[level]++
                if (node.containsAnyAccessor()) levelWithAny[level]++
                if ((node.isAbstract || node.isFinal) && samples.size < SUMMARY_SAMPLE_PATHS) {
                    samples.add(path + if (node.isFinal) "$" else "/*")
                }
                if (path.length > deepestLen) { deepestLen = path.length; deepest = path }
                node.forEachAccessor { idx, child ->
                    when {
                        idx == ANY_ACCESSOR_IDX -> levelAnyEdges[level]++
                        manager.isCoveredByAny(idx) -> levelCoveredEdges[level]++
                        else -> levelMarkEdges[level]++
                    }
                    if (next.size < 20_000) next.add(child to (path + with(manager) { idx.accessor }.toSuffix()))
                }
            }
            frontier = next
            level++
        }

        return buildString {
            append("paths=").append(root.size)
            append(" nodes=").append(root.countNodes())
            append(" maxDepth=").append(root.maxDepth)
            append(" rootBreadth=").append(root.accessorCount())
            if (truncated) append(" TRUNCATED")
            appendLine()
            append("      levels (depth: nodes/withAny  edges any,covered,other): ")
            for (d in 0 until minOf(level, SUMMARY_MAX_LEVELS)) {
                if (levelNodes[d] == 0) continue
                append("d").append(d).append(":").append(levelNodes[d]).append("/").append(levelWithAny[d])
                append(" ").append(levelAnyEdges[d]).append(",").append(levelCoveredEdges[d])
                append(",").append(levelMarkEdges[d]).append("  ")
            }
            appendLine()
            append("      sample paths: ").append(samples.joinToString(" | "))
            appendLine()
            append("      deepest sampled prefix: ").append(deepest)
        }
    }

    fun recordSlotOpened(nodes: Long) {
        slotsOpened.incrementAndGet()
        storeMass.addAndGet(nodes)
    }

    val slotsOpened = AtomicLong()
    val slotMerges = AtomicLong()
    val maxSlot = AtomicLong()

    private fun recordGrowthSize(nodes: Long) {
        var bucket = 0
        var value = nodes
        while (value > 1 && bucket < 31) {
            value = value shr 1
            bucket++
        }
        growthSizeBuckets.incrementAndGet(bucket)
    }

    /** Edges a flow function reported unchanged: worklist cost that never reaches a store. */
    val unchangedEnqueued = AtomicLong()
    val unchangedSuppressed = AtomicLong()

    /**
     * The fact-depth gate, and what it parks.
     *
     * An entry edge deeper than the unit's current limit is put aside and replayed only when the
     * limit rises, and the limit rises only when the unit runs out of work. On a workload that
     * never runs out of work the limit freezes, and [delayedInitialEdges] minus [replayedEdges] is
     * the backlog that is then never processed at all -- a bound that is silently doing the work no
     * widening operator does, and doing it by dropping edges on the floor rather than by
     * approximating them.
     */
    val delayedInitialEdges = AtomicLong()
    val replayedEdges = AtomicLong()
    val limitRaises = AtomicLong()
    val maxLimit = AtomicLong()

    fun recordLimitRaise(newLimit: Int, replayed: Int) {
        limitRaises.incrementAndGet()
        replayedEdges.addAndGet(replayed.toLong())
        var current = maxLimit.get()
        while (newLimit > current) {
            if (maxLimit.compareAndSet(current, newLimit.toLong())) break
            current = maxLimit.get()
        }
    }

    private fun sum(a: AtomicLongArray): Long {
        var total = 0L
        for (i in 0 until a.length()) total += a.get(i)
        return total
    }

    private fun ratio(a: Long, b: Long): String =
        if (b == 0L) "-" else String.format("%.2f", a.toDouble() / b)

    /** One line per progress tick, so the store totals can be read as a curve. */
    fun liveReport(): String = buildString {
        append("edgeStoreLive slots=").append(slotsOpened.get())
        append(" merges=").append(slotMerges.get())
        append(" storeMass=").append(storeMass.get())
        append(" propagatedMass=").append(propagatedMass.get())
        append(" offeredMass=").append(offeredMass.get())
        append(" calls=").append(sum(calls))
        append(" growths=").append(sum(growths))
        append(" noops=").append(sum(noops))
        append(" maxSlot=").append(maxSlot.get())
    }

    fun report(topN: Int): String = buildString {
        val totalCalls = sum(calls)
        val totalGrowths = sum(growths)
        val totalFirst = sum(firstInserts)
        val totalNoops = sum(noops)

        append("edgeStore calls=").append(totalCalls)
        append(" firstInserts=").append(totalFirst)
        append(" growths=").append(totalGrowths)
        append(" noops=").append(totalNoops)
        append(" noopShare=").append(ratio(totalNoops * 100, totalCalls)).append('%')
        appendLine()

        append("edgeStore offeredMass=").append(offeredMass.get())
        append(" storeMass=").append(storeMass.get())
        append(" propagatedMass=").append(propagatedMass.get())
        append(" propagatedPerStored=").append(ratio(propagatedMass.get(), storeMass.get()))
        append(" propagatedPerGrowth=").append(ratio(propagatedMass.get(), totalFirst + totalGrowths))
        appendLine()

        append("edgeStore unchangedEnqueued=").append(unchangedEnqueued.get())
        append(" unchangedSuppressed=").append(unchangedSuppressed.get())
        append(" delayed=").append(delayedInitialEdges.get())
        append(" replayed=").append(replayedEdges.get())
        append(" stillParked=").append(delayedInitialEdges.get() - replayedEdges.get())
        append(" limitRaises=").append(limitRaises.get())
        append(" maxLimit=").append(maxLimit.get())
        append(" slotsOpened=").append(slotsOpened.get())
        append(" slotMerges=").append(slotMerges.get())
        append(" mergesPerSlot=").append(ratio(slotMerges.get(), slotsOpened.get()))
        append(" maxSlot=").append(maxSlot.get())
        append(" maxPropagated=").append(maxPropagated.get())
        append(" at ").append(maxPropagatedWhere ?: "-")
        appendLine()

        appendLine("edgeStore growthByLog2Size=" + (0 until 24).joinToString(",") { growthSizeBuckets.get(it).toString() })

        appendLine("edgeStore --- by producer ---")
        appendLine(
            "edgeStore rootBreadth mean=" + ratio(rootBreadthTotal.get(), rootBreadthSamples.get()) +
                " max=" + maxRootBreadth.get() +
                " buckets=" + (0..31).joinToString(",") { rootBreadthBuckets.get(it).toString() }
        )
        appendLine(
            "edgeStore siblingAbsorb folded=" + siblingsAbsorbed.get() +
                " mass=" + siblingAbsorbedMass.get()
        )
        appendLine("edgeStore premiseTrieNodes=" + premiseTrieNodes.get())
        synchronized(bigFactLock) {
            val order = (0 until BIG_FACT_SLOTS).filter { bigFactText[it] != null }
                .sortedByDescending { bigFactPaths[it] }
            for ((rank, i) in order.withIndex()) {
                appendLine("edgeStore bigFact #" + (rank + 1) + " " + bigFactText[i])
            }
        }
        appendLine(
            "edgeStore foldCensus calls=" + foldCalls.get() +
                " callsWithAny=" + foldCallsWithAny.get() +
                " share=" + ratio(foldCallsWithAny.get(), foldCalls.get()) +
                " | visits=" + foldVisits.get() +
                " nodesWithAny=" + foldNodesWithAny.get() +
                " share=" + ratio(foldNodesWithAny.get(), foldVisits.get()) +
                " | withCovered=" + foldAnyWithCovered.get() +
                " uncoveredOnly=" + foldAnyUncoveredOnly.get() +
                " alone=" + foldAnyAlone.get()
        )
        appendLine(
            "edgeStore selfSubsume facts=" + censusFacts.get() +
                " truncated=" + censusTruncated.get() +
                " nodesWithAny=" + censusNodesWithAny.get() +
                " siblings=" + censusSiblings.get() +
                " siblingMass=" + censusTotalSiblingMass.get() +
                " | fullySubsumed=" + censusFullySubsumed.get() +
                " mass=" + censusFullySubsumedMass.get() +
                " share=" + ratio(censusFullySubsumedMass.get(), censusTotalSiblingMass.get()) +
                " | ofWhichNameCritical=" + censusSubsumedNameCritical.get() +
                " mass=" + censusSubsumedNameCriticalMass.get() +
                " | partial=" + censusPartial.get() +
                " droppedMass=" + censusPartialDroppedMass.get() +
                " | notSubsumed=" + censusNotSubsumed.get()
        )
        for (p in producers) {
            var c = 0L; var f = 0L; var g = 0L; var n = 0L; var om = 0L; var pm = 0L
            for (k in kinds) {
                val i = p.ordinal * nKinds + k.ordinal
                c += calls.get(i); f += firstInserts.get(i); g += growths.get(i); n += noops.get(i)
                om += offeredMassBy.get(i); pm += propagatedMassBy.get(i)
            }
            if (c == 0L) continue
            append("edgeStore   ").append(p.name.padEnd(16))
            append(" calls=").append(c)
            append(" (").append(ratio(c * 100, totalCalls)).append("%)")
            append(" first=").append(f)
            append(" growth=").append(g)
            append(" noop=").append(n)
            append(" offered=").append(om)
            append(" propagated=").append(pm)
            append(" (").append(ratio(pm * 100, propagatedMass.get())).append("%)")
            appendLine()
        }

        appendLine("edgeStore --- by edge kind ---")
        for (k in kinds) {
            var c = 0L; var g = 0L; var pm = 0L
            for (p in producers) {
                val i = p.ordinal * nKinds + k.ordinal
                c += calls.get(i); g += growths.get(i); pm += propagatedMassBy.get(i)
            }
            if (c == 0L) continue
            append("edgeStore   ").append(k.name.padEnd(16))
            append(" calls=").append(c).append(" growth=").append(g).append(" propagated=").append(pm)
            appendLine()
        }

        val worst = perMethod.values.sortedByDescending { it.propagatedMass.get() }
        appendLine("edgeStore --- ${perMethod.size} methods, top $topN by propagated mass ---")
        worst.take(topN).forEach { appendLine("edgeStore   $it") }
    }
}

class MethodEdgeStats(private val method: String) {
    /** Distinct analyzers for this method: one per calling context. */
    @JvmField val entryPoints: MutableSet<MethodEntryPoint> = ConcurrentHashMap.newKeySet()

    @JvmField val calls = AtomicLong()
    @JvmField val firstInserts = AtomicLong()
    @JvmField val growths = AtomicLong()
    @JvmField val noops = AtomicLong()
    @JvmField val offeredMass = AtomicLong()
    @JvmField val storeMass = AtomicLong()
    @JvmField val propagatedMass = AtomicLong()
    @JvmField val maxSlotMass = AtomicLong()

    override fun toString(): String = buildString {
        append("propagated=").append(propagatedMass.get())
        append(" | calls=").append(calls.get())
        append(" | growths=").append(growths.get())
        append(" | noops=").append(noops.get())
        append(" | maxSlot=").append(maxSlotMass.get())
        append(" | eps=").append(entryPoints.size)
        append(" | ").append(method)
    }
}

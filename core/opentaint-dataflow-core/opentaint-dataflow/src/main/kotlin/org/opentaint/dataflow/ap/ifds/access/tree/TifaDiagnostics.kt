package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.ANY_ACCESSOR_IDX
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

    /**
     * Bases over this size get their arrivals traced and their final tree retained for an exact dump.
     * Everything below it is counted only.
     */
    const val TRACE_MIN_SIZE = 5_000L

    /** Arrivals recorded per traced base, and stack traces captured, both bounded. */
    const val TRACE_MAX_ARRIVALS = 80
    const val TRACE_MAX_STACKS = 12

    private val perBase = ConcurrentHashMap<String, BaseStats>()

    fun baseStats(key: String): BaseStats = perBase.computeIfAbsent(key) { BaseStats(it) }

    /** The exact shape and content of the single largest `added`, plus how it got there. */
    fun dumpLargest(): String {
        val worst = perBase.values.maxByOrNull { it.maxAddedSize.get() } ?: return "no bases"
        return worst.dumpTree()
    }

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

    /**
     * A structural profile of the largest `added` seen, recomputed only when the tree DOUBLES past
     * a threshold -- a handful of times per big base, never for a small one.
     */
    @Volatile
    @JvmField
    var profile: String? = null

    @Volatile
    private var profiledAt: Long = 0

    /** The final tree, retained only for bases big enough to be worth an exact dump. */
    @Volatile
    private var retained: AccessTree.AccessNode? = null

    /** What arrived, in order: `size-before -> size-after  <the incoming fact>`. */
    private val arrivals = java.util.Collections.synchronizedList(ArrayList<String>())
    private val stacks = java.util.Collections.synchronizedList(ArrayList<String>())

    fun recordArrival(before: AccessTree.AccessNode?, incoming: AccessTree.AccessNode, after: AccessTree.AccessNode) {
        if (after.size < TifaDiagnostics.TRACE_MIN_SIZE) return

        if (arrivals.size < TifaDiagnostics.TRACE_MAX_ARRIVALS) {
            arrivals.add(
                "${before?.size ?: 0} -> ${after.size} (+${after.size - (before?.size ?: 0)})" +
                    " incoming size=${incoming.size} depth=${incoming.maxDepth}: " +
                    incoming.toString().replace('\n', ' ').take(400)
            )
        }

        if (stacks.size < TifaDiagnostics.TRACE_MAX_STACKS) {
            val frames = Thread.currentThread().stackTrace
                .map { it.toString() }
                .filter { it.startsWith("org.opentaint") }
                .filterNot { it.contains("TifaDiagnostics") }
                .take(22)
                .joinToString("\n        ")
            stacks.add("at added.size=${after.size}\n        $frames")
        }
    }

    fun dumpTree(): String {
        val root = retained ?: return "no retained tree for $key"
        return buildString {
            appendLine("EXACT TREE for $key")
            appendLine("  size(multiplicity)=${root.size} distinct=${root.countNodes()} depth=${root.maxDepth}")
            appendLine("  --- DAG (shared nodes appear once; `=> nK` is a back-reference) ---")
            val ids = java.util.IdentityHashMap<AccessTree.AccessNode, Int>()
            val order = ArrayList<AccessTree.AccessNode>()
            fun assign(n: AccessTree.AccessNode) {
                if (ids.containsKey(n)) return
                ids[n] = ids.size
                order.add(n)
                n.forEachAccessor { _, c -> assign(c) }
            }
            assign(root)
            for (n in order) {
                val flags = buildString {
                    if (n.isAbstract) append("*")
                    if (n.isFinal) append("$")
                    if (n.deepAccessorExclusion != null) append("[excl]")
                }
                appendLine("  n${ids[n]}$flags")
                n.forEachAccessor { accessor, child ->
                    val name = with(n.manager) { accessor.accessor }.toSuffix()
                    appendLine("      $name => n${ids[child]}")
                }
            }
            appendLine("  --- how it grew: the first ${arrivals.size} arrivals that reached the threshold ---")
            arrivals.forEach { appendLine("    $it") }
            appendLine("  --- who added them ---")
            stacks.forEach { appendLine("    $it") }
        }
    }

    fun recordAdded(node: AccessTree.AccessNode) {
        var cur = maxAddedSize.get()
        while (node.size > cur && !maxAddedSize.compareAndSet(cur, node.size)) cur = maxAddedSize.get()

        var d = maxAddedDepth.get()
        while (node.maxDepth > d && !maxAddedDepth.compareAndSet(d, node.maxDepth)) d = maxAddedDepth.get()

        if (node.containsAnyInThisOrDeepNodes) everCarriedAny.set(1)

        if (node.size >= PROFILE_MIN_SIZE && node.size >= profiledAt * 2) {
            profiledAt = node.size
            profile = profileOf(node)
        }

        // Always the LATEST tree over the threshold, not a doubling snapshot: the previous instrument
        // caught this base at 20,601 and reported `anyEdges=0`, while its recorded max depth of 127
        // implies about eleven `[any]` edges stacked on one path in the version that actually mattered.
        if (node.size >= TifaDiagnostics.TRACE_MIN_SIZE) retained = node
    }

    private fun profileOf(root: AccessTree.AccessNode): String {
        // Distinct nodes vs `size`: `size` counts with multiplicity, so the ratio is how much
        // sharing the interner has already bought. A tree that is 32k by multiplicity and 300
        // distinct is a very different object from one that is 32k of both.
        val distinct = root.countNodes()

        val perLevel = HashMap<Int, MutableSet<AccessTree.AccessNode>>()
        val accessorCounts = HashMap<String, Int>()
        var anyEdges = 0
        val anyDepths = sortedSetOf<Int>()
        var deepest = ""

        val seen = java.util.IdentityHashMap<AccessTree.AccessNode, Int>()
        val stack = ArrayDeque<Triple<AccessTree.AccessNode, Int, String>>()
        stack.addLast(Triple(root, 0, ""))
        var visits = 0

        while (stack.isNotEmpty() && visits < PROFILE_VISIT_BUDGET) {
            val (node, depth, path) = stack.removeLast()
            visits++

            perLevel.getOrPut(depth) { java.util.Collections.newSetFromMap(java.util.IdentityHashMap()) }.add(node)
            if (path.length > deepest.length) deepest = path
            if (seen.put(node, depth) != null) continue

            node.forEachAccessor { accessor, child ->
                val name = with(node.manager) { accessor.accessor }.toSuffix()
                accessorCounts.merge(name, 1, Int::plus)
                if (accessor == ANY_ACCESSOR_IDX) {
                    anyEdges++
                    anyDepths.add(depth)
                }
                stack.addLast(Triple(child, depth + 1, path + name))
            }
        }

        val levels = (0..perLevel.keys.maxOrNull().orZeroInt())
            .joinToString(",") { perLevel[it]?.size?.toString() ?: "0" }
        val topAccessors = accessorCounts.entries.sortedByDescending { it.value }.take(8)
            .joinToString(", ") { "${it.key}:${it.value}" }

        return buildString {
            append("size=").append(root.size)
            append(" distinct=").append(distinct)
            append(" depth=").append(root.maxDepth)
            append(" anyEdges=").append(anyEdges)
            append(" anyDepths=").append(anyDepths.take(12))
            append(if (visits >= PROFILE_VISIT_BUDGET) " TRUNCATED" else "")
            append(" | levels=").append(levels.take(200))
            append(" | top=").append(topAccessors)
            append(" | deepest=").append(deepest.take(300))
        }
    }

    private fun Int?.orZeroInt(): Int = this ?: 0

    private companion object {
        const val PROFILE_MIN_SIZE = 5_000L
        const val PROFILE_VISIT_BUDGET = 400_000
    }

    override fun toString(): String = buildString {
        append("added: ").append(maxAddedSize.get())
        append(" | depth: ").append(maxAddedDepth.get())
        append(" | any: ").append(everCarriedAny.get())
        append(" | adds: ").append(addCalls.get())
        append(" | emits: ").append(emits.get())
        append(" | ").append(key)
        profile?.let { append("\n      PROFILE ").append(it) }
    }
}
